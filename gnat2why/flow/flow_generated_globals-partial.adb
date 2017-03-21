------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Hashed_Maps;
with Ada.Text_IO;                      use Ada.Text_IO;
with Common_Iterators;                 use Common_Iterators;
with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_1;   use Flow_Generated_Globals.Phase_1;
with Flow_Refinement;                  use Flow_Refinement;
with Flow.Slice;                       use Flow.Slice;
with Flow_Utility;                     use Flow_Utility;
with Flow_Types;                       use Flow_Types;
with Gnat2Why_Args;                    use Gnat2Why_Args;
with Gnat2Why.Annotate;                use Gnat2Why.Annotate;
with Graphs;
with Lib;                              use Lib;
with Namet;                            use Namet;
with Sem_Aux;                          use Sem_Aux;
with Sem_Util;                         use Sem_Util;
with Sinfo;                            use Sinfo;
with Snames;                           use Snames;
with SPARK_Definition;                 use SPARK_Definition;
with SPARK_Util;                       use SPARK_Util;
with SPARK_Frame_Conditions;           use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;           use SPARK_Util.Subprograms;
with SPARK_Xrefs;                      use SPARK_Xrefs;

package body Flow_Generated_Globals.Partial is

   ----------------------------------------------------------------------------
   --  Debugging
   ----------------------------------------------------------------------------

   Indent : constant String := "  ";

   ----------------------------------------------------------------------------
   --  Preliminaries
   ----------------------------------------------------------------------------

   function Disjoint (A, B, C : Node_Sets.Set) return Boolean;
   --  Returns True iff sets A, B, C are mutually disjoint

   function Is_Caller_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff E represent an entity that is might call other routines

   function Is_Global_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff E represent an entity that may acts as a global

   function Is_Heap_Entity (E : Entity_Id) return Boolean renames No;
   --  Returns True iff E represens heap (which is in turn represented by an
   --  empty entity id and __HEAP entity name).

   function Is_Proper_Callee (E : Entity_Id) return Boolean;
   --  Returns True iff E might be called

   function Is_Callee (E : Entity_Id) return Boolean;
   --  Returns True iff E might be called or is a package nested in an entity
   --  that might be called (and we treat its elaboration as a call).

   function Scope_Truly_Within_Or_Same
     (E, Analyzed : Entity_Id) return Boolean
   is
     (Is_In_Analyzed_Files (E)
      and then Scope_Within_Or_Same (E, Analyzed))
   with Pre => Is_In_Analyzed_Files (Analyzed);
   --  Similar to Scope_Within_Or_Same, but returns for entities in child units
   --  (which strictly speaking are "within" the scope of the parent packages).
   --  This routine is only intented to be called to detect entities belonging
   --  to scopes of the current compilation uni (hence the Pre).

   ----------------------
   -- Is_Caller_Entity --
   ----------------------

   function Is_Caller_Entity (E : Entity_Id) return Boolean is
     (Ekind (E) in Flow_Generated_Globals.Traversal.Container_Scope);
   --  ??? Container_Scope isn't the best name; rethink
   --  ??? not sure how Protected_Type fits here

   ----------------------
   -- Is_Global_Entity --
   ----------------------

   function Is_Global_Entity (E : Entity_Id) return Boolean is
     (Is_Heap_Entity (E) or else
      Ekind (E) in E_Abstract_State
                 | E_Constant
                 | E_Loop_Parameter
                 | E_Variable
                 | Formal_Kind
                 | E_Protected_Type
                 | E_Task_Type);

   ----------------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------------

   subtype Global_Set is Node_Sets.Set
   with Dynamic_Predicate =>
          (for all E of Global_Set => Is_Global_Entity (E));

   subtype Callee_Set is Node_Sets.Set
   with Dynamic_Predicate =>
          (for all E of Callee_Set => Is_Callee (E));

   type No_Colours is (Dummy_Color);
   --  Dummy type inhabited by only a single value (just like a unit type in
   --  OCaml); needed for graphs with colorless edges.

   type Global_Nodes is record
      Proof_Ins : Global_Set;
      Inputs    : Global_Set;
      Outputs   : Global_Set;
   end record
   with Dynamic_Predicate =>
          (for all G of Global_Nodes.Proof_Ins =>
              not Global_Nodes.Inputs.Contains (G) and then
              not Global_Nodes.Outputs.Contains (G));
   --  ??? should it be an array then we could remove some repeated code

   type Call_Nodes is record
      Proof_Calls       : Callee_Set;
      Conditional_Calls : Callee_Set;
      Definite_Calls    : Callee_Set;
   end record
   with Dynamic_Predicate => Disjoint (Call_Nodes.Proof_Calls,
                                       Call_Nodes.Conditional_Calls,
                                       Call_Nodes.Definite_Calls);

   type Flow_Nodes is record
      Proper  : Global_Nodes;
      Refined : Global_Nodes;

      Initializes : Global_Set;
      --  Only meaningful for packages

      Calls : Call_Nodes;
   end record;
   --  Information needed to synthesize the the Global contract

   type Contract is record
      Globals : Flow_Nodes;

      Direct_Calls      : Node_Sets.Set;  --   ??? Callee_Set
      --  For compatibility with old GG (e.g. assumptions)

      Local_Variables       : Global_Set;
      Local_Ghost_Variables : Global_Set;
      --  Only meaningful for packages

      Has_Terminate : Boolean;
      --  Only meaningful for subprograms and entries

      Nonreturning       : Boolean;
      Nonblocking        : Boolean;
      Entry_Calls        : Entry_Call_Sets.Set;
      Tasking            : Tasking_Info;
      Calls_Current_Task : Boolean;
      --  Only meaningfull only for entries, functions and procedures and
      --  initially for packages (nested in entries, functions or procedures).
      --
      --  Only recorded to the ALI files for entries, functions and procedures
   end record;

   package Entity_Contract_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Contract,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Containers with contracts generated based on the current compilation
   --  unit alone.

   type Global_Patch is record
      Entity  : Entity_Id;
      Globals : Flow_Nodes;
   end record;

   package Global_Patch_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Global_Patch);

   package Call_Graphs is new Graphs
     (Vertex_Key   => Entity_Id,
      Key_Hash     => Node_Hash,
      Edge_Colours => No_Colours,
      Null_Key     => Entity_Id'Last,
      Test_Key     => "=");

   Meaningless : constant Boolean := False;
   --  Meaningless value needed to silence checks for invalid data

   ----------------------------------------------------------------------------
   --  Specs
   ----------------------------------------------------------------------------

   function Preanalyze_Body (E : Entity_Id) return Contract;

   function Preanalyze_Spec (E : Entity_Id) return Contract
   with Pre => (if Entity_In_SPARK (E)
                then not Entity_Body_In_SPARK (E));

   function Categorize_Calls
     (E         : Entity_Id;
      Analyzed  : Entity_Id;
      Contracts : Entity_Contract_Maps.Map)
   return Call_Nodes
   with Pre => Is_Caller_Entity (E) and then
               Scope_Truly_Within_Or_Same (E, Analyzed);
   --  Categorize calls from E to entities nested within Analyzed into Proof,
   --  Conditional and Definite calls.

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure,
        Post => (for all Call of Contract_Calls'Result =>
                    Ekind (Call) = E_Function);
   --  Return direct calls in the contract of E, i.e. in its Pre, Post and
   --  Contract_Cases.

   function Contract_Globals
     (E       : Entity_Id;
      Refined : Boolean)
      return Global_Nodes;
   --  Return globals from the Global and Depends contracts of E (or from their
   --  refined variants iff Refined is True).

   procedure Debug (Label : String; E : Entity_Id);
   --  Display Label followed by the entity name of E

   procedure Do_Global
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
   with Pre => Is_Caller_Entity (Analyzed);

   procedure Do_Preanalysis
     (Contracts : in out Entity_Contract_Maps.Map);
   --  Collect contracts on the intraprocedural analysis alone

   procedure Dump (Contracts : Entity_Contract_Maps.Map; Analyzed : Entity_Id);
   --  Display contracts highlighing the analyzed entity

   procedure Filter_Local (E : Entity_Id; Nodes : in out Node_Sets.Set);
   procedure Filter_Local (E : Entity_Id; G : in out Global_Nodes);

   procedure Fold (Folded    :        Entity_Id;
                   Analyzed  :        Entity_Id;
                   Contracts :        Entity_Contract_Maps.Map;
                   Patches   : in out Global_Patch_Lists.List);
   --  Main workhorse for the partial generated globals

   function Frontend_Calls (E : Entity_Id) return Node_Sets.Set;
   --  Return direct calls using the frontend cross-references

   function Frontend_Globals (E : Entity_Id) return Global_Nodes;
   --  Return globals using the frontend cross-references

   function Is_Empty (G : Global_Nodes) return Boolean;
   --  Return True iff all components of the G are empty

   procedure To_Node_Set
     (Names :     Name_Sets.Set;
      Nodes : out Node_Sets.Set);
   --  Convert names to nodes

   function To_Names
     (Entries : Entry_Call_Sets.Set;
      Objects : Tasking_Info)
      return Name_Tasking_Info;
   --  Convert tasking info from nodes to names

   procedure Write_Contracts_To_ALI
     (E :        Entity_Id;
      C : in out Entity_Contract_Maps.Map)
   with Pre => Is_Caller_Entity (E);
   --  Moves information to the ALI writer (probably should write it directly)

   ----------------------------------------------------------------------------
   --  Bodies
   ----------------------------------------------------------------------------

   ------------------
   -- Analyze_Body --
   ------------------

   function Preanalyze_Body (E : Entity_Id) return Contract
   is
      FA : constant Flow_Analysis_Graphs :=
        Flow_Analyse_Entity
          ((if Ekind (E) = E_Package and then Entity_Body_In_SPARK (E)
            then Body_Entity (E)
            else E),
           Generating_Globals => True);

      Contr : Contract;

   begin
      --  ??? I do not understand what Is_Generative means
      if FA.Is_Generative then
         Compute_Globals
           (FA,
            Inputs_Proof          => Contr.Globals.Refined.Proof_Ins,
            Inputs                => Contr.Globals.Refined.Inputs,
            Outputs               => Contr.Globals.Refined.Outputs,
            Proof_Calls           => Contr.Globals.Calls.Proof_Calls,
            Definite_Calls        => Contr.Globals.Calls.Definite_Calls,
            Conditional_Calls     => Contr.Globals.Calls.Conditional_Calls,
            Local_Variables       => Contr.Local_Variables,
            Local_Ghost_Variables => Contr.Local_Ghost_Variables,
            Local_Definite_Writes => Contr.Globals.Initializes);

      else
         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Task_Type
            =>
               --  Use globals from spec, but calls and tasking info from body
               Contr.Globals.Proper  := Contract_Globals (E, Refined => False);
               Contr.Globals.Refined := Contract_Globals (E, Refined => True);

            when E_Package =>
               null;

            when E_Protected_Type =>
               null; --  ??? do nothing for now

            when others =>
               raise Program_Error;
         end case;
      end if;

      --  Register direct calls without splitting them into proof, definite and
      --  conditional; this is necessary because splitting still looses calls
      --  to protected subprograms, which are handled as accesses to global
      --  variables.
      --  ??? not sure about protected types
      if Ekind (E) /= E_Protected_Type then
         Contr.Direct_Calls := FA.Direct_Calls;
      end if;

      if Ekind (E) = E_Package then
         GG_Register_State_Refinement (FA.Spec_Entity);
      end if;

      --  We register the following:
      --  * subprograms which contain at least one loop that may not terminate
      --  * procedures annotated with No_Return
      --  * subprograms which call predefined procedures with No_Return.
      Contr.Nonreturning :=
        FA.Kind in Kind_Subprogram | Kind_Package_Body
          and then
        (FA.Has_Potentially_Nonterminating_Loops
           or else
         No_Return (E)
           or else
         (for some Callee of FA.Direct_Calls =>
             In_Predefined_Unit (Callee) and then No_Return (Callee)));

      --  Check for potentially blocking statements in bodies of callable
      --  entities, i.e. entries and subprograms. Specs never contain any
      --  statements.

      Contr.Nonblocking :=
        (if Is_Callee (E)
         then FA.Has_Only_Nonblocking_Statements
         else Meaningless);

      --  Deal with tasking-related stuff
      Contr.Tasking     := FA.Tasking;
      Contr.Entry_Calls := FA.Entries;

      return Contr;
   end Preanalyze_Body;

   ------------------
   -- Analyze_Spec --
   ------------------

   function Preanalyze_Spec (E : Entity_Id) return Contract is

      Contr : Contract;

      function Unsynchronized_Globals (G : Global_Nodes) return Node_Sets.Set;
      --  Returns unsynchronized globals from G

      function Has_No_Body_Yet (E : Entity_Id) return Boolean is
        (Ekind (E) in E_Function | E_Procedure
         and then No (Subprogram_Body_Entity (E)));
      --  Returns True if subprogram E does not have a body yet (no .adb)

      ----------------------------
      -- Unsynchronized_Globals --
      ----------------------------

      function Unsynchronized_Globals (G : Global_Nodes) return Node_Sets.Set
      is
         Unsynch : Node_Sets.Set;

         procedure Collect_Unsynchronized (Vars : Node_Sets.Set);

         ----------------------------
         -- Collect_Unsynchronized --
         ----------------------------

         procedure Collect_Unsynchronized (Vars : Node_Sets.Set) is
         begin
            for E of Vars loop
               if not (Is_Heap_Entity (E)
                       or else Is_Synchronized_Object (E)
                       or else Is_Synchronized_State (E)
                       or else Is_Part_Of_Concurrent_Object (E))
               then
                  Contr.Tasking (Unsynch_Accesses).Include (E);
               end if;
            end loop;
         end Collect_Unsynchronized;

      --  Start of processing for Unsynchronized_Globals

      begin
         Collect_Unsynchronized (G.Proof_Ins);
         Collect_Unsynchronized (G.Inputs);
         Collect_Unsynchronized (G.Outputs);

         return Unsynch;
      end Unsynchronized_Globals;

   --  Start of processing for Preanalyze_Spec

   begin
      if Ekind (E) in Entry_Kind
                    | E_Function
                    | E_Procedure
                    | E_Task_Type
      then
         if Has_User_Supplied_Globals (E) then

            --  ??? do nothing?
            Contr.Globals.Proper := Contract_Globals (E, Refined => False);

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Globals.Proper);

         --  Capture (Yannick's) "frontend globals"; once they will end up in
         --  the ALI file they should be indistinguishable from other globals.

         else
            Contr.Globals.Refined := Frontend_Globals (E);

            --  Frontend globals does not distinguish Proof_Ins from Inputs;
            --  conservatively assume that all reads belong to Inputs.
            pragma Assert (Contr.Globals.Refined.Proof_Ins.Is_Empty);

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Globals.Refined);
         end if;
      end if;

      Contr.Globals.Calls.Conditional_Calls := Frontend_Calls (E);

      pragma Assert
        (if Is_Proper_Callee (E)
         then Contract_Calls (E).Is_Subset
                (Of_Set => Contr.Globals.Calls.Conditional_Calls));

      if Entity_In_SPARK (E) then
         if Is_Proper_Callee (E) then
            Contr.Direct_Calls := Contract_Calls (E);
         end if;

         --  We register subprograms with body not in SPARK as nonreturning
         --  except when they are:
         --  * predefined (or are instances of predefined subprograms)
         --  * imported
         --  * intrinsic
         --  * have no body yet (no .adb) and are not procedures annotated with
         --    No_Return.

         Contr.Nonreturning := not
           (In_Predefined_Unit (E)
            or else
            Is_Imported (E)
            or else
            Is_Intrinsic (E)
            or else
              (Has_No_Body_Yet (E)
               and then not No_Return (E)));

         --  Register accesses to unsynchronized states and
         --  variables that occur in contract.
         --  Collect_Unsynchronized_Globals (Contr.Proof_Ins);
         --  Collect_Unsynchronized_Globals (Contr.Inputs);
         --  Collect_Unsynchronized_Globals (Contr.Outputs);

         Contr.Nonblocking :=
           (if Is_Callee (E)
            then False --  ??? first approximation
            else Meaningless);

         --  In a contract it is syntactically not allowed to suspend on a
         --  suspension object, call a protected procedure or entry, and it is
         --  semantically not allowed to externally call a protected function
         --  (because such calls are volatile and they would occur in an
         --  interfering context).
         pragma Assert (Contr.Tasking (Suspends_On).Is_Empty);
         pragma Assert (Contr.Tasking (Locks).Is_Empty);
         pragma Assert (Contr.Entry_Calls.Is_Empty);

      --  Otherwise, fill in dummy value

      else
         pragma Assert (Contr.Direct_Calls.Is_Empty);

         Contr.Nonreturning := Meaningless;
         Contr.Nonblocking  := Meaningless;
      end if;

      return Contr;
   end Preanalyze_Spec;

   ----------------------
   -- Categorize_Calls --
   ----------------------

   function Categorize_Calls
     (E         : Entity_Id;
      Analyzed  : Entity_Id;
      Contracts : Entity_Contract_Maps.Map)
      return Call_Nodes
   is
      use type Node_Sets.Set;

      Original : Call_Nodes renames Contracts (E).Globals.Calls;

      --  Categorization is done in two steps: first, we find subprograms
      --  called definitely, conditionally and in proof contexts and not care
      --  about overlapping (e.g a routine that is called both definitely and
      --  in proof will be found twice); then we handle overlapping, which is
      --  enforced by the Call_Nodes type predicate. The first step is
      --  difficult, then overlapping is simple.
      --
      --  The first step is relatively easy to specify inductively, but its
      --  imperative implementation is quite hard to follow. Verifying it would
      --  be very reassuring. So here is a spec, and verification is left as an
      --  exercise for the reader.
      --
      --  Notation
      --  ========
      --
      --  Def, Cond and Proof denote sets of subprograms called definitely,
      --  conditionally and in proof contexts (they might overlap),
      --  respectively. That's what we are looking for.
      --
      --  Def_i, Cond_i and Proof_i denote sets of subprograms called
      --  "immediately", e.g. those whose calls appear in the CFG of the
      --  caller. That's what we get in Contracts.
      --
      --  Both the prefixed and unprefixed sets are represented as relations
      --  and typed in the curried style typical to proof assistants, e.g.:
      --  "Def x y" reads as "x will definitely call y" (either immediately or
      --  as an effect of a call to some other subprogram, which we typically
      --  call "p" for proxy).
      --
      --  Logical symbols are typed in the style of HOL proof assistant, i.e.
      --  a \/ b  = "a or b"
      --  a /\ b  = "a and b"
      --  ?x. F x = "exists x such that F x"
      --
      --  Specification
      --  =============
      --
      --  Subprograms called definitely are inductively specified as:
      --
      --  Def x y =
      --    Def_i x y \/
      --    ?p. Def x p /\ Def_i p y,
      --
      --  i.e. they are either immediately (and definitely) called from x or
      --  immediately called from some of its definite callees. In other words,
      --  they are reachable from x through a chain of definitely called
      --  subprograms.
      --
      --  Subprograms called conditionally are more complicated:
      --
      --  Cond x y =
      --    Cond_i x y \/
      --    (?p. Cond x p /\ (Def_i p y \/ Cond_i p y)) \/
      --    (?p. Def x p /\ Cond_i p y),
      --
      --  i.e. they are either immediately (and conditionally) called from x,
      --  immediately called (conditionally or definitely) from one of its
      --  conditional callees, or immediately (but conditionally) called from
      --  one of its definite callees. Note: this definition uses Def from the
      --  previous one.
      --
      --  And those called in proof context are the most complicated:
      --
      --  Proof x y =
      --    Proof_i x y \/
      --    (?p. (Def x p \/ Cond x p) /\ Proof_i p y) \/
      --    (?p. Proof x p /\ (Def_i p y \/ Cond_i p y \/ Proof_i p y)),
      --
      --  i.e. they are either immediately called from x in a proof context, or
      --  are immediately called from a conditional or definitive callee of x
      --  in a proof context, or are immediately called no matter how from a
      --  proof callee of x. Note: this definitions uses Def and Cond from the
      --  previous ones.

      O_Proof, O_Conditional, O_Definite : Node_Sets.Set;
      --  Sets for intermediate results, i.e. overlapping sets of calls

   begin
      --  Definitive calls are the easiest to find and the implementation is
      --  fairly straightforward, as it ignores conditional and proof calls.
      --  Note: this could be done with a simple closure of a graph with only
      --  definitive calls, but we would still need a similar traversal to
      --  populate such a graph.
      --
      --  We maintain two sets: Todo, initialized according to the base case of
      --  the inductive specification; and Done, processed according to the
      --  inductive cases. For definitive calls those two sets are enough; for
      --  conditional and proof calls they are split into subsets for handling
      --  different inductive cases.

      Find_Definite_Calls : declare
         Todo : Node_Sets.Set := Original.Definite_Calls;
         Done : Node_Sets.Set;

      begin
         loop
            if not Todo.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.First_Element;

               begin
                  Done.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Todo.Union
                       (Contracts (Pick).Globals.Calls.Definite_Calls - Done);
                  end if;

                  Todo.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Original.Definite_Calls.Is_Subset (Of_Set => Done));

         Node_Sets.Move (Target => O_Definite,
                         Source => Done);
      end Find_Definite_Calls;

      --  Conditional calls are more difficult to find, but the implementation
      --  is still similar to the previous one. It maintains two sets of called
      --  subprograms: those called definitively and those called
      --  conditionally.

      Find_Conditional_Calls : declare
         type Calls is record
            Conditional, Definite : Node_Sets.Set;
         end record;

         Todo : Calls := (Conditional => Original.Conditional_Calls,
                          Definite    => Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Conditional.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Conditional.First_Element;

               begin
                  Done.Conditional.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then
                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

                     begin
                        Todo.Conditional.Union
                          ((Picked.Conditional_Calls or Picked.Definite_Calls)
                           - Done.Conditional);
                     end;
                  end if;

                  Todo.Conditional.Delete (Pick);
               end;
            elsif not Todo.Definite.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Definite.First_Element;

               begin
                  Done.Definite.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

                     begin
                        Todo.Conditional.Union
                          (Picked.Conditional_Calls - Done.Conditional);

                        Todo.Definite.Union
                          (Picked.Definite_Calls - Done.Definite);
                     end;
                  end if;

                  Todo.Definite.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert
           (Original.Conditional_Calls.Is_Subset (Of_Set => Done.Conditional));

         Node_Sets.Move (Target => O_Conditional,
                         Source => Done.Conditional);
      end Find_Conditional_Calls;

      --  Proof calls turns out to be not really harder than conditional calls;
      --  their implementation follows the very same pattern.

      Find_Proof_Calls : declare
         type Calls is record
            Proof, Other : Node_Sets.Set;
         end record;

         Todo : Calls := (Proof => Original.Proof_Calls,
                          Other => Original.Conditional_Calls or
                                   Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Proof.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Proof.First_Element;

               begin
                  Done.Proof.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

                     begin
                        Todo.Proof.Union
                          ((Picked.Proof_Calls or
                              Picked.Conditional_Calls or
                              Picked.Definite_Calls)
                             - Done.Proof);
                     end;
                  end if;

                  Todo.Proof.Delete (Pick);
               end;
            elsif not Todo.Other.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Other.First_Element;

               begin
                  Done.Other.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

                     begin
                        Todo.Proof.Union
                          (Picked.Proof_Calls - Done.Proof);

                        Todo.Other.Union
                          ((Picked.Conditional_Calls or
                              Picked.Definite_Calls)
                             - Done.Other);
                     end;
                  end if;

                  Todo.Other.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Original.Proof_Calls.Is_Subset (Of_Set => Done.Proof));

         Node_Sets.Move (Target => O_Proof,
                         Source => Done.Proof);
      end Find_Proof_Calls;

      --  Finally, overlapping. For proof calls it is just like in slicing.
      --  However, calls that are both conditional and definitive are resolved
      --  in slicing as definitive, but here as conditional.
      --
      --  It is because in slicing we are synthesizing contract for the sliced
      --  subprogram; if its callee is called definitely then its outputs will
      --  become outputs of the sliced subprogram (and it doesn't matter if it
      --  is also called conditionally). Here we categorize calls to use their
      --  contracts; if a callee is called conditionally then we must read its
      --  outputs (and it doesn't matter if it is also called definitively).

      return (Proof_Calls       => O_Proof - O_Conditional - O_Definite,
              Conditional_Calls => O_Conditional,
              Definite_Calls    => O_Definite - O_Conditional);
   end Categorize_Calls;

   ---------------------
   -- Contracts_Calls --
   ---------------------

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set is
      Calls : Node_Sets.Set;

      procedure Collect_Calls (Expr : Node_Id);
      --  Collect function calls in expression Expr and put them in Calls

      ------------------
      -- Collect_Calls --
      ------------------

      procedure Collect_Calls (Expr : Node_Id) is
      begin
         Calls.Union (Get_Functions (Expr, Include_Predicates => True));
      end Collect_Calls;

   --  Start of processing for Calls_In_Visible_Contracts

   begin
      for Expr of Get_Precondition_Expressions (E) loop
         Collect_Calls (Expr);
      end loop;

      for Expr of Get_Postcondition_Expressions (E, Refined => False)
      loop
         Collect_Calls (Expr);
      end loop;

      return Calls;
   end Contract_Calls;

   ----------------------
   -- Contract_Globals --
   ----------------------

   function Contract_Globals
     (E : Entity_Id;
      Refined : Boolean)
      return Global_Nodes
   is
      Proof_Ins_FS : Flow_Id_Sets.Set;
      Inputs_FS    : Flow_Id_Sets.Set;
      Outputs_FS   : Flow_Id_Sets.Set;

   begin
      Get_Globals
        (Subprogram          => E,
         Scope               => Get_Flow_Scope ((if Refined
                                                 then Get_Body (E)
                                                 else E)),
         Classwide           => False,
         Proof_Ins           => Proof_Ins_FS,
         Reads               => Inputs_FS,
         Writes              => Outputs_FS,
         Use_Deduced_Globals => False);

      return (Proof_Ins => To_Node_Set (Proof_Ins_FS),
              Inputs    => To_Node_Set (Inputs_FS),
              Outputs   => To_Node_Set (Outputs_FS));
   end Contract_Globals;

   --------------
   -- Disjoint --
   --------------

   function Disjoint (A, B, C : Node_Sets.Set) return Boolean is
   begin
      return not
        (for some E of A => B.Contains (E) or else C.Contains (E))
          or else
        (for some E of B => C.Contains (E));
   end Disjoint;

   -----------
   -- Debug --
   -----------

   procedure Debug (Label : String; E : Entity_Id) is
   begin
      if XXX then
         Ada.Text_IO.Put_Line (Label & " " & Full_Source_Name (E));
      end if;
   end Debug;

   ------------------------
   -- Do_Global_Contract --
   ------------------------

   procedure Do_Global
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
   is
      Has_Children : constant Boolean := not Is_Leaf (Analyzed);

   begin
      if Has_Children then
         for Child of Scope_Map (Analyzed) loop
            Do_Global (Child, Contracts);
         end loop;
      end if;

      if Analyzed = Root_Entity
        or else Has_Children
      then
         declare
            Patches : Global_Patch_Lists.List;

         begin
            Fold (Analyzed     => Analyzed,
                  Folded       => Analyzed,
                  Contracts    => Contracts,
                  Patches      => Patches);

            for Patch of Patches loop
               declare
                  Updated : Contract renames Contracts (Patch.Entity);

               begin
                  Updated.Globals := Patch.Globals;
               end;
            end loop;
         end;
      end if;

      --  ??? this is probably wrong place to filter locals
      if Ekind (Analyzed) in Entry_Kind
                           | E_Function
                           | E_Procedure
                           | E_Task_Type
      then
         declare
            C : Contract renames Contracts (Analyzed);

            S : constant Entity_Id := Scope (Analyzed);

         begin
            Filter_Local (Analyzed, C.Globals.Proper);
            Filter_Local (Analyzed, C.Globals.Refined);

            --  Protected type appear as an implicit parameter to protected
            --  subprograms and protected entries, and as a global to things
            --  nested in them. After resolving calls from protected
            --  subprograms and protected entries to their nested things the
            --  type will also appear as a global of the protected
            --  subprogram/entry. Here we strip it. ??? Conceptually this
            --  belongs to Filter_Local where Scope_Same_Or_Within does not
            --  capture this.

            if Ekind (S) = E_Protected_Type then
               C.Globals.Proper.Inputs.Exclude (S);
               C.Globals.Proper.Outputs.Exclude (S);
               C.Globals.Proper.Proof_Ins.Exclude (S);
               C.Globals.Refined.Inputs.Exclude (S);
               C.Globals.Refined.Outputs.Exclude (S);
               C.Globals.Refined.Proof_Ins.Exclude (S);
            end if;
         end;
      end if;
   end Do_Global;

   ----------
   -- Dump --
   ----------

   procedure Dump
     (Contracts : Entity_Contract_Maps.Map;
      Analyzed  : Entity_Id)
   is
      procedure Dump (E : Entity_Id);

      procedure Dump (Label : String; Vars : Node_Sets.Set);

      ----------
      -- Dump --
      ----------

      procedure Dump (E : Entity_Id) is

         procedure Dump (Label : String; G : Global_Nodes);
         --  Display globals, if any

         ----------
         -- Dump --
         ----------

         procedure Dump (Label : String; G : Global_Nodes) is
         begin
            if not Is_Empty (G) then
               Ada.Text_IO.Put_Line (Indent & Indent & Label & " =>");
               Dump (Indent & Indent & "Proof_Ins  ", G.Proof_Ins);
               Dump (Indent & Indent & "Inputs     ", G.Inputs);
               Dump (Indent & Indent & "Outputs    ", G.Outputs);
            end if;
         end Dump;

         --  Local constants

         C : constant Entity_Contract_Maps.Cursor := Contracts.Find (E);

      --  Start of processing for Dump

      begin
         for Child of Scope_Map (E) loop
            Dump (Child);
         end loop;

         if Entity_Contract_Maps.Has_Element (C) then
            declare
               Contr     : Contract renames Contracts (C);
               Highlight : constant Boolean := E = Analyzed;

            begin
               if Highlight then
                  Term_Info.Set_Style (Bright);
               end if;

               Ada.Text_IO.Put_Line (Indent &
                                       Ekind (E)'Image & ": " &
                                       Full_Source_Name (E));

               if Highlight then
                  Term_Info.Set_Style (Normal);
               end if;

               Dump ("Global",         Contr.Globals.Proper);
               Dump ("Refined_Global", Contr.Globals.Refined);

               if not Contr.Globals.Calls.Proof_Calls.Is_Empty
                 or else not Contr.Globals.Calls.Conditional_Calls.Is_Empty
                 or else not Contr.Globals.Calls.Definite_Calls.Is_Empty
--                   or else not Contr.Remote_Calls.Is_Empty
               then
                  Ada.Text_IO.Put_Line (Indent & Indent & "Calls:");
                  Dump (Indent & Indent & "Proof      ",
                        Contr.Globals.Calls.Proof_Calls);
                  Dump (Indent & Indent & "Conditional",
                        Contr.Globals.Calls.Conditional_Calls);
                  Dump (Indent & Indent & "Definite   ",
                        Contr.Globals.Calls.Definite_Calls);
--                    Dump (Indent & Indent & "Remote     ",
--                          Contr.Remote_Calls);
               end if;

               case Ekind (E) is
                  when E_Function | E_Procedure =>
                     --  Ada.Text_IO.Put_Line
                     --    (Indent & Indent & "Nonblocking  : " &
                     --     Boolean'Image (Contr.Nonblocking));
                     Ada.Text_IO.Put_Line
                       (Indent & Indent & "Nonreturning : " &
                        Boolean'Image (Contr.Nonreturning));

                  when E_Package =>
                     Dump (Indent & "Initializes  ",
                           Contr.Globals.Initializes);

                  when others =>
                     null;
               end case;

               for Kind in Contr.Tasking'Range loop
                  if not Contr.Tasking (Kind).Is_Empty then
                     Dump (Indent & Kind'Img, Contr.Tasking (Kind));
                  end if;
               end loop;
            end;
         end if;
      end Dump;

      procedure Dump (Label : String; Vars : Node_Sets.Set) is
      begin
         if not Vars.Is_Empty then
            Ada.Text_IO.Put (Indent & Label & ":");
            for C in Vars.Iterate loop
               declare
                  Var : Entity_Id renames Vars (C);
                  use type Node_Sets.Cursor;
               begin
                  Ada.Text_IO.Put (" ");

                  declare
                     Highlight : constant Boolean := Var = Analyzed;

                  begin
                     if Highlight then
                        Term_Info.Set_Style (Bright);
                     end if;

                     if Is_Heap_Entity (Var) then
                        Ada.Text_IO.Put (Name_Of_Heap_Variable);
                     else
                        Ada.Text_IO.Put (Full_Source_Name (Var));
                        Ada.Text_IO.Put
                          (" (" & Entity_Kind'Image (Ekind (Var)) & ")");
                     end if;

                     if Highlight then
                        Term_Info.Set_Style (Normal);
                     end if;
                  end;

                  if C /= Vars.Last then
                     Ada.Text_IO.Put (',');
                  end if;
               end;
            end loop;
            Ada.Text_IO.New_Line;
         end if;
      end Dump;

   --  Start of processing for Dump

   begin
      if Debug_Partial_Contracts then
         Dump (Root_Entity);
         Ada.Text_IO.New_Line;
      end if;
   end Dump;

   ------------------
   -- Filter_Local --
   ------------------

   procedure Filter_Local (E : Entity_Id; Nodes : in out Node_Sets.Set) is
      Remote : Node_Sets.Set;

   begin
      for N of Nodes loop
         --  Filter variables declared within E and the E itself (which occurs
         --  as a global when E is a single concurrent type). Heap is never a
         --  local variable, so it must be always kept while filtering.
         if Is_Heap_Entity (N)
           or else not (Is_In_Analyzed_Files (N)
                        and then Scope_Within_Or_Same (N, E))
         then
            Remote.Insert (N);
         end if;
      end loop;

      Node_Sets.Move (Target => Nodes,
                      Source => Remote);
   end Filter_Local;

   procedure Filter_Local (E : Entity_Id; G : in out Global_Nodes) is
   begin
      Filter_Local (E, G.Proof_Ins);
      Filter_Local (E, G.Inputs);
      Filter_Local (E, G.Outputs);
   end Filter_Local;

   ----------
   -- Fold --
   ----------

   procedure Fold (Folded    :        Entity_Id;
                   Analyzed  :        Entity_Id;
                   Contracts :        Entity_Contract_Maps.Map;
                   Patches   : in out Global_Patch_Lists.List)
   is
      Folded_Scope : constant Flow_Scope := Get_Flow_Scope (Folded);

      Full_Contract : Contract renames Contracts (Folded);

      use type Node_Sets.Set; --  to make "or" operator visible

      Original : Flow_Nodes renames Full_Contract.Globals;

      Local_Pkg_Variables : constant Node_Sets.Set :=
        Full_Contract.Local_Variables or Full_Contract.Local_Ghost_Variables;
      --  Only needed for packages, but safe for other entities

      function Callee_Globals (E : Entity_Id) return Global_Nodes
      with Pre => Is_Caller_Entity (E);

      function Collect (E : Entity_Id) return Flow_Nodes
      with Pre => Is_Caller_Entity (E),
           Post => Node_Sets.Is_Empty (Collect'Result.Initializes) and then
                   Is_Empty (Collect'Result.Proper);

      function Down_Project (G : Global_Nodes) return Global_Nodes;

      function Is_Fully_Written
        (State   : Entity_Id;
         Outputs : Node_Sets.Set)
            return Boolean
        with Pre => Ekind (State) = E_Abstract_State;
      --  Returns True iff all constituents of State are among Outputs

      procedure Up_Project
        (Vars      :     Node_Sets.Set;
         Projected : out Node_Sets.Set;
         Partial   : out Node_Sets.Set)
        with Post =>
          (for all E of Partial => Ekind (E) = E_Abstract_State);

      --------------------
      -- Callee_Globals --
      --------------------

      function Callee_Globals (E : Entity_Id) return Global_Nodes is
         Callee_Contr_Position : constant Entity_Contract_Maps.Cursor :=
           Contracts.Find (E);
         --  ??? check if E is within Analyzed

      begin
         if Entity_Contract_Maps.Has_Element (Callee_Contr_Position) then
            declare
               Callee_Globals : Flow_Nodes renames
                 Contracts (Callee_Contr_Position).Globals;
            begin
               if E = Analyzed
                 or else Parent_Scope (E) = Analyzed
               then
                  if (case Ekind (E) is
                         when E_Package =>
                            Present (Get_Pragma (E, Pragma_Initializes)),

                         when Entry_Kind
                            | E_Function
                            | E_Procedure
                            | E_Task_Type
                         =>
                         Entity_In_SPARK (E)
                           and then not Entity_Body_In_SPARK (E)
                           and then Has_User_Supplied_Globals (E),

                         when E_Protected_Type =>
                            Meaningless,

                         when others => raise Program_Error)
                  then
                     Debug ("Folding with down-projected globals:", E);
                     return Down_Project (Callee_Globals.Proper);
                  else
                     Debug ("Folding with refined globals:", E);
                     return Callee_Globals.Refined;
                  end if;
               else
                  Debug ("Folding with proper globals:", E);
                  return Down_Project (Callee_Globals.Proper);
               end if;
            end;
         else
            Debug ("Ignoring remote call to", E);
            return Global_Nodes'(others => <>);
         end if;
      end Callee_Globals;

      -------------
      -- Collect --
      -------------

      function Collect (E : Entity_Id) return Flow_Nodes is
         Result_Proof_Ins : Node_Sets.Set := Original.Refined.Proof_Ins;
         Result_Inputs    : Node_Sets.Set := Original.Refined.Inputs;
         Result_Outputs   : Node_Sets.Set := Original.Refined.Outputs;
         --  By keeping these sets separate we don't have to care about
         --  maintaing the Global_Nodes invariant; it will be only checked when
         --  returning from this routine.

         Result : Flow_Nodes;

      begin
         --  First collect callees
         Result.Calls := Categorize_Calls (E, Analyzed, Contracts);

         --  Now collect their globals

         for Callee of Result.Calls.Definite_Calls loop
            declare
               G : constant Global_Nodes := Callee_Globals (Callee);
            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Inputs.Union (G.Inputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         for Callee of Result.Calls.Proof_Calls loop
            declare
               G : constant Global_Nodes := Callee_Globals (Callee);
            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Proof_Ins.Union (G.Inputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         --  For conditional calls do as above, but also connect the caller's
         --  Inputs vertices to the callee's Outputs vertices. This models code
         --  like:
         --
         --     if Condition then
         --        Output := ...;
         --     end if;
         --
         --  as:
         --
         --     if Condition then
         --        Output := ...;
         --     else
         --        Output := Output;  <<< artificial read of Output
         --     end if;
         --
         --  which adds an dummy assignment.

         for Callee of Result.Calls.Conditional_Calls loop
            declare
               G : constant Global_Nodes := Callee_Globals (Callee);
            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Inputs.Union (G.Inputs);
               Result_Inputs.Union (G.Outputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         --  Post-processing
         Result_Proof_Ins.Difference (Result_Inputs);

         declare
            Proof_Ins_Outs : constant Node_Sets.Set :=
              Result_Proof_Ins and Result_Outputs;
         begin
            Result_Proof_Ins.Difference (Proof_Ins_Outs);
            Result_Inputs.Union (Proof_Ins_Outs);
         end;

         Result.Refined := (Proof_Ins => Result_Proof_Ins,
                            Inputs    => Result_Inputs,
                            Outputs   => Result_Outputs);

         return Result;
      end Collect;

      ------------------
      -- Down_Project --
      ------------------

      function Down_Project (G : Global_Nodes) return Global_Nodes is

         Analyzed_View : constant Flow_Scope :=
           (case Ekind (Analyzed) is
               when Entry_Kind
                  | E_Function
                  | E_Procedure
                  | E_Protected_Type
                  | E_Task_Type
               =>
                  Get_Flow_Scope (Get_Body (Analyzed)),

               when E_Package
               =>
                 (Analyzed, Body_Part),

               when others
               =>
                 raise Program_Error);

      begin
         return
           Global_Nodes'
             (Proof_Ins => Down_Project (G.Proof_Ins, Analyzed_View),
              Inputs    => Down_Project (G.Inputs,    Analyzed_View),
              Outputs   => Down_Project (G.Outputs,   Analyzed_View));
      end Down_Project;

      ----------------------
      -- Is_Fully_Written --
      ----------------------

      function Is_Fully_Written
        (State   : Entity_Id;
         Outputs : Node_Sets.Set)
         return Boolean
      is
        ((for all C of Iter (Refinement_Constituents (State)) =>
             Outputs.Contains (C))
           and then
         (for all C of Iter (Part_Of_Constituents (State)) =>
             Outputs.Contains (C)));

      ----------------
      -- Up_Project --
      ----------------

      procedure Up_Project
        (Vars      :     Node_Sets.Set;
         Projected : out Node_Sets.Set;
         Partial   : out Node_Sets.Set)
      is
      begin
         Projected.Clear;
         Partial.Clear;

         for Var of Vars loop
            if Is_Heap_Entity (Var)
              or else Is_Visible (Var, Folded_Scope)
            then
               Projected.Include (Var);
            else
               declare
                  State : constant Entity_Id := Parent_State (Var);
               begin
                  if Present (State) then
                     Partial.Include (State);
                  else
                     --  ??? implicit abstract state
                     --  Projected.Include
                     --    (Get_Flow_Scope (Var).Ent);
                     --  Old approach: pretend that variable is
                     --  public.
                     Projected.Include (Var);
                  end if;
               end;
            end if;
         end loop;
      end Up_Project;

      --  Local variables

      Update : Flow_Nodes;

   --  Start of processing for Fold

   begin
      Debug ("Folding", Folded);

      Update := Collect (Folded);

      declare
         Projected, Partial : Node_Sets.Set;
      begin
         Up_Project (Update.Refined.Inputs, Projected, Partial);
         Update.Proper.Inputs := Projected or Partial;

         Up_Project (Update.Refined.Outputs, Projected, Partial);
         for State of Partial loop
            if not Is_Fully_Written (State, Update.Refined.Outputs)
            then
               Update.Proper.Inputs.Include (State);
            end if;
         end loop;
         Update.Proper.Outputs := Projected or Partial;

         Up_Project (Update.Refined.Proof_Ins, Projected, Partial);
         Update.Proper.Proof_Ins :=
           (Projected or Partial) -
           (Update.Proper.Inputs or Update.Proper.Outputs);

         --  Handle package Initializes aspect
         if Ekind (Folded) = E_Package then
            Update.Initializes :=
              Original.Initializes or
              ((Update.Refined.Outputs - Update.Refined.Inputs)
                  and
               Local_Pkg_Variables);

            Up_Project (Update.Initializes, Projected, Partial);

            for State of Partial loop
               if Is_Fully_Written (State, Update.Initializes) then
                  Projected.Include (State);
               end if;
            end loop;
            Update.Initializes := Projected;
         end if;
      end;

      Filter_Local (Analyzed, Update.Calls.Proof_Calls);
      Filter_Local (Analyzed, Update.Calls.Definite_Calls);
      Filter_Local (Analyzed, Update.Calls.Conditional_Calls);

      --  Filter_Local (Analyzed, Update.Remote_Calls);

      Patches.Append (Global_Patch'(Entity  => Folded,
                                    Globals => Update));

      for Child of Scope_Map (Folded) loop
         Fold (Child, Analyzed, Contracts, Patches);
      end loop;
   end Fold;

   --------------------
   -- Frontend_Calls --
   --------------------

   function Frontend_Calls (E : Entity_Id) return Node_Sets.Set is
      Calls : Node_Sets.Set;

   begin
      To_Node_Set (Names => Computed_Calls (To_Entity_Name (E)),
                   Nodes => Calls);

      return Calls;
   end Frontend_Calls;

   ----------------------
   -- Frontend_Globals --
   ----------------------

   function Frontend_Globals (E : Entity_Id) return Global_Nodes is
      Input_Names  : Name_Sets.Set;
      Output_Names : Name_Sets.Set;

      G : Global_Nodes;

   begin
      --  Collect frontend globals using only info from the current compilation
      --  unit.
      --  ??? ignore calls, because they seem too over-aproximating
      Collect_Direct_Computed_Globals (E, Input_Names, Output_Names);

      To_Node_Set (Names => Input_Names,  Nodes => G.Inputs);
      To_Node_Set (Names => Output_Names, Nodes => G.Outputs);

      return G;
   end Frontend_Globals;

   ------------------------
   -- Generate_Contracts --
   ------------------------

   procedure Generate_Contracts (GNAT_Root : Node_Id) is
   begin
      Dump_Tree;

      --  GG section in ALI must be present, even if it is empty
      GG_Write_Initialize (GNAT_Root);

      if Present (Root_Entity) then
         declare
            Contracts : Entity_Contract_Maps.Map;
            --  Partial information collected by analysis of inner scopes
            --  needed for the summary of their outer scopes.
         begin

            Do_Preanalysis (Contracts);

            if Gnat2Why_Args.Flow_Generate_Contracts then
               Do_Global (Root_Entity, Contracts);
            end if;

            --  Recursive contract is used when generating the Nonreturning
            --  contract, so it must be done first.

            Write_Contracts_To_ALI (Root_Entity, Contracts);
         end;
      end if;

      GG_Write_Finalize;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Term_Info.Set_Fg (Yellow);
         Ada.Text_IO.Put_Line ("Global generation complete for current CU");
         Term_Info.Set_Fg (Reset);
      end if;
   end Generate_Contracts;

   ---------------
   -- Is_Callee --
   ---------------

   function Is_Callee (E : Entity_Id) return Boolean is
   begin
      if Is_Proper_Callee (E) then
         return True;
      else
         declare
            S : constant Entity_Id := Enclosing_Subprogram (E);

         begin
            return Present (S) and then Is_Proper_Callee (S);
         end;
      end if;
   end Is_Callee;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (G : Global_Nodes) return Boolean is
     (G.Proof_Ins.Is_Empty and then
      G.Inputs.Is_Empty and then
      G.Outputs.Is_Empty);

   ----------------------
   -- Is_Proper_Callee --
   ----------------------

   function Is_Proper_Callee (E : Entity_Id) return Boolean is
     (Ekind (E) in Entry_Kind | E_Function | E_Procedure);

   --------------------
   -- Do_Preanalysis --
   --------------------

   procedure Do_Preanalysis
     (Contracts : in out Entity_Contract_Maps.Map)
   is
      procedure Preanalyze (E : Entity_Id);

      ----------------
      -- Preanalyze --
      ----------------

      procedure Preanalyze (E : Entity_Id) is
         Contr : Contract;
         --  Contract for the analyzed entity

      begin
         --  This is first traversal of the current compilation unit, so it's
         --  a good place for some debug.
         Debug_Traversal (E);

         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Task_Type
               =>
               Contr := (if Entity_In_SPARK (E)
                           and then Entity_Body_In_SPARK (E)
                         then Preanalyze_Body (E)
                         else Preanalyze_Spec (E));

            when E_Package =>
               Contr := (if Entity_In_SPARK (E)
                         then Preanalyze_Body (E)
                         else Preanalyze_Spec (E));

            when E_Protected_Type =>
               --   ??? perhaps we should do something, but now we don't
               null;

            when others =>
               raise Program_Error;
         end case;

         --  Terminating stuff, picked no matter if body is in SPARK
         Contr.Has_Terminate :=
           (if Is_Proper_Callee (E)
            then Has_Terminate_Annotation (E)
            else Meaningless);

         Contr.Calls_Current_Task :=
           Includes_Current_Task (Contr.Direct_Calls);

         Contracts.Insert (E, Contr);
      end Preanalyze;

   begin
      Iterate_Main_Unit (Preanalyze'Access);

      --  Only debug output from now on

      Dump (Contracts, Root_Entity);
   end Do_Preanalysis;

   --------------
   -- To_Names --
   --------------

   function To_Names
     (Entries : Entry_Call_Sets.Set;
      Objects : Tasking_Info)
      return Name_Tasking_Info
   is
      Result : Name_Tasking_Info;

   begin
      for EC of Entries loop
         --  For entry calls pretend that we are accessing an object
         --  Package_Name.Object_Name.Entry_Name.
         Result (Entry_Calls).Insert
           (To_Entity_Name
              (To_String (EC.Obj) &
                 "__" &
               Get_Name_String (Chars (EC.Entr))));
      end loop;

      for Kind in Objects'Range loop
         for N of Objects (Kind) loop
            pragma Assert (Ekind (N) in E_Abstract_State | Object_Kind);
            Result (Kind).Insert (To_Entity_Name (N));
         end loop;
      end loop;

      return Result;
   end To_Names;

   -----------------
   -- To_Node_Set --
   -----------------

   procedure To_Node_Set
     (Names :     Name_Sets.Set;
      Nodes : out Node_Sets.Set)
   is
   begin
      Nodes := Node_Sets.Empty_Set;

      for Name of Names loop
         declare
            Node : constant Entity_Id := Find_Entity (Name);

            --  pragma Assert (if No (Node) then Is_Heap_Variable (Name));
            --  ??? temporarily replace pragma with an error message below

         begin
            if No (Node)
              and then not Is_Heap_Variable (Name)
            then
               Ada.Text_IO.Put_Line ("no Entity_Id for " &
                                     Common_Containers.To_String (Name));
               raise Program_Error;
            end if;
            Nodes.Insert (Node);
         end;
      end loop;
   end To_Node_Set;

   ----------------------------
   -- Write_Contracts_To_ALI --
   ----------------------------

   procedure Write_Contracts_To_ALI
     (E :        Entity_Id;
      C : in out Entity_Contract_Maps.Map)
   is
      Contr : Contract renames C (E);

   begin
      for Child of Scope_Map (E) loop
         Write_Contracts_To_ALI (Child, C);
      end loop;

      if Ekind (E) /= E_Protected_Type then
         GG_Register_Direct_Calls (E, Contr.Direct_Calls);

         GG_Register_Global_Info
           ((Name                  => To_Entity_Name (E),
             Local                 => not Is_Globally_Visible (E),
             Kind                  => Ekind (E),
             Origin                => Origin_Flow,      --  ??? dummy
             Globals               =>
               (Proper  =>
                  (Proof_Ins => To_Name_Set (Contr.Globals.Proper.Proof_Ins),
                   Inputs    => To_Name_Set (Contr.Globals.Proper.Inputs),
                   Outputs   => To_Name_Set (Contr.Globals.Proper.Outputs)),
                Refined =>
                  (Proof_Ins => To_Name_Set (Contr.Globals.Refined.Proof_Ins),
                   Inputs    => To_Name_Set (Contr.Globals.Refined.Inputs),
                   Outputs   => To_Name_Set (Contr.Globals.Refined.Outputs)),
                Initializes =>
                  To_Name_Set (Contr.Globals.Initializes),
                Calls   =>
                  (Proof_Calls       =>
                     To_Name_Set (Contr.Globals.Calls.Proof_Calls),
                   Definite_Calls    =>
                     To_Name_Set (Contr.Globals.Calls.Definite_Calls),
                   Conditional_Calls =>
                     To_Name_Set (Contr.Globals.Calls.Conditional_Calls))),

             Local_Variables       => To_Name_Set (Contr.Local_Variables),
             Local_Ghost_Variables => To_Name_Set
               (Contr.Local_Ghost_Variables),

             Has_Terminate         => Contr.Has_Terminate,
             Nonreturning          => Contr.Nonreturning,
             Nonblocking           => Contr.Nonblocking,
             Tasking               => To_Names (Contr.Entry_Calls,
                                                Contr.Tasking)));
      end if;

      --  Register abstract state components; if any then there
      --  should bea Refined_State aspect.
      --  ??? isn't this just checking if there are any
      --  abstract states?
      --  if FA.Kind = Kind_Package_Body
      --    and then Present (Get_Pragma (FA.Analyzed_Entity,
      --                      Pragma_Refined_State))
      --  then
      --     GG_Register_State_Refinement (FA.Analyzed_Entity);
      --  end if;
   end Write_Contracts_To_ALI;

end Flow_Generated_Globals.Partial;
