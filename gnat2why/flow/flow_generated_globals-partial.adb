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
with Ada.Strings.Unbounded;            use Ada.Strings.Unbounded;
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

   Debug_Global_Graph : constant Boolean := True and XXX;
   --  Display edges added to global graph

   ----------------------------------------------------------------------------
   --  Preliminaries
   ----------------------------------------------------------------------------

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

   ----------------------
   -- Is_Caller_Entity --
   ----------------------

   function Is_Caller_Entity (E : Entity_Id) return Boolean is
     (Ekind (E) in Entry_Kind
                 | E_Function
                 | E_Package
                 | E_Procedure
                 | E_Protected_Type
                 | E_Task_Type);

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
                 | E_Protected_Type | E_Task_Type); --  ??? not sure about this
   --  ??? it seems too risky to just use Assignable_Kind and Object_Kind

   ----------------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------------

   type Global_Kind is (Proof_Ins, Inputs, Outputs, Variable);
   pragma Ordered (Global_Kind);
   --  Kinds of vertices in the global graph; ordering matters because we use
   --  it as an array index.

   type Global_Id is record
      Entity : Entity_Id;
      Kind   : Global_Kind;
   end record with
     Dynamic_Predicate =>
       (case Kind is
           when Inputs | Outputs | Proof_Ins =>
              Is_Caller_Entity (Entity),
           when Variable =>
              Entity = Entity_Id'Last or else --  ??? for Empty_Global
              Is_Global_Entity (Entity));
   --  Vertex data for the global graph

   Empty_Global : constant Global_Id := (Entity => Entity_Id'Last,
                                         Kind   => Global_Kind'Last);
   --  Dummy value required by the Graphs package; otherwise unused

   type No_Colours is (Dummy_Color);
   --  Dummy type inhabited by only a single value (similar to unit type in
   --  OCaml); needed for graphs with colorless edges.

   function Global_Hash (G : Global_Id) return Ada.Containers.Hash_Type;
   --  Hash function needed to instantiate the Graphs package

   package Global_Graphs is new Graphs
     (Vertex_Key   => Global_Id,
      Key_Hash     => Global_Hash,
      Edge_Colours => No_Colours,
      Null_Key     => Empty_Global,
      Test_Key     => "=");

   type Global_Nodes is record
      Proof_Ins : Node_Sets.Set;
      Inputs    : Node_Sets.Set;
      Outputs   : Node_Sets.Set;
   end record
   with Dynamic_Predicate =>
          (for all G of Global_Nodes.Proof_Ins =>
              not Global_Nodes.Inputs.Contains (G) and then
              not Global_Nodes.Outputs.Contains (G));
   --  ??? should it be an array then we could remove some repeated code

   type Contract is record
      Proper  : Global_Nodes;
      Refined : Global_Nodes;
      --  Proper and refined globals

      Initializes : Node_Sets.Set;
      --  Only meaningful for packages

      Proof_Calls       : Node_Sets.Set;
      Conditional_Calls : Node_Sets.Set;
      Definite_Calls    : Node_Sets.Set;

      Direct_Calls      : Node_Sets.Set; -- ??? should be union of the above
      --  For compatibility with old GG (e.g. assumptions)

      Remote_Calls      : Node_Sets.Set;
      --  Calls to routines in other compilation units

      Local_Variables       : Node_Sets.Set;
      Local_Ghost_Variables : Node_Sets.Set;

      Has_Terminate : Boolean;
      --  Only meaningful for subprograms and entries

      Recursive          : Boolean;
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

   procedure Add (E            :        Entity_Id;
                  Analyzed     :        Entity_Id;
                  Contracts    :        Entity_Contract_Maps.Map;
                  Global_Graph : in out Global_Graphs.Graph)
   with Pre => Is_Caller_Entity (E);
   --  Add globals for entity E to Global_Graph

   procedure Add_Nonreturning (E          :        Entity_Id;
                               Contracts  :        Entity_Contract_Maps.Map;
                               Call_Graph : in out Call_Graphs.Graph);
   --  Add E to the call graph for detecting non-returning subprograms

   procedure Add_Recursive (E          :        Entity_Id;
                            Contracts  :        Entity_Contract_Maps.Map;
                            Call_Graph : in out Call_Graphs.Graph);
   --  Add E to the call graph for detecting recursive subprograms

   procedure Analyze
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
     with Pre => Is_Caller_Entity (Analyzed);
   --  Analyze E by first doing something when going top-down and then
   --  finishing when going back.

   function Analyze_Body (E : Entity_Id) return Contract;

   function Analyze_Spec (E : Entity_Id) return Contract
   with Pre => (if Entity_In_SPARK (E)
                then not Entity_Body_In_SPARK (E));

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure,
        Ghost;
   --  Return direct calls in the contract of E, i.e. in its Pre, Post and
   --  Contract_Cases.

   function Contract_Globals
     (E       : Entity_Id;
      Refined : Boolean)
      return Global_Nodes;
   --  Return globals from the Global and Depends contracts of E (or their
   --  refined variants iff Refined is True).

   procedure Debug (Label : String; E : Entity_Id);
   --  Display Label followed by the entity name of E

   procedure Dump (Contracts : Entity_Contract_Maps.Map; Analyzed : Entity_Id);
   --  Display contracts highlighing the analyzed entity

   procedure Filter_Local (E : Entity_Id; Nodes : in out Node_Sets.Set);
   procedure Filter_Local (E : Entity_Id; G : in out Global_Nodes);

   procedure Fold (Folded       :        Entity_Id;
                   Analyzed     :        Entity_Id;
                   Global_Graph :        Global_Graphs.Graph;
                   Contracts    : in out Entity_Contract_Maps.Map);
   --  Main workhorse for the partial generated globals

   procedure Fold_Nonreturning (Folded     :        Entity_Id;
                                Call_Graph :        Call_Graphs.Graph;
                                Contracts  : in out Entity_Contract_Maps.Map);
   --  Fold call graph for detecting non-returning subprograms

   procedure Fold_Recursive (Folded     :        Entity_Id;
                             Call_Graph :        Call_Graphs.Graph;
                             Contracts  : in out Entity_Contract_Maps.Map);
   --  Fold call graph for detecting recursive subprograms

   function Frontend_Calls (E : Entity_Id) return Node_Sets.Set;
   --  Return direct calls using the frontend cross-references

   function Frontend_Globals (E : Entity_Id) return Global_Nodes;
   --  Return globals using the frontend cross-references

   procedure Print_Partial_Graph (Prefix : String;
                                  G      : Global_Graphs.Graph);
   --  Debug output

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
   --  Moves information to ALI writer (probably should write it directly)

   ----------------------------------------------------------------------------
   --  Bodies
   ----------------------------------------------------------------------------

   ---------
   -- Add --
   ---------

   procedure Add (E            :        Entity_Id;
                  Analyzed     :        Entity_Id;
                  Contracts    :        Entity_Contract_Maps.Map;
                  Global_Graph : in out Global_Graphs.Graph)
   is
      Contr : Contract renames Contracts (E);

      procedure Add_Down_Projected_Globals (G : Global_Nodes);
      procedure Add_Globals                (G : Global_Nodes);
      --  Connect subprogram's vertices to the corresponding variables:
      --  proof inputs, inputs and outputs.

      type Edge_Kind is record
         Source, Target : Global_Kind;
      end record
        with Predicate => Edge_Kind.Source in Proof_Ins | Inputs | Outputs;
      --  Kind of edges in the global graphs: they are always from subprogram
      --  (represented as Proof_Ins, Inputs and Outputs) to either other
      --  subprogram (when it represents a call) or to variable (when it
      --  represents a direct access to global).

      type Edge_Kinds is array (Positive range <>) of Edge_Kind;
      --  Technical type for representing a bucket of edge kinds

      procedure Connect
        (Targets : Node_Sets.Set;
         Edges   : Edge_Kinds);
      --  Connect Targets using the given kinds of edges

      --------------------------------
      -- Add_Down_Projected_Globals --
      --------------------------------

      procedure Add_Down_Projected_Globals (G : Global_Nodes) is

         Analyzed_View : constant Flow_Scope :=
           (case Ekind (E) is
               when Entry_Kind
                  | E_Function
                  | E_Procedure
                  | E_Task_Type
                  | E_Protected_Type
               =>
                  Get_Flow_Scope (Get_Body (E)),

               when E_Package
               =>
                 (E, Body_Part),

               when others => raise Program_Error);

      begin
         Connect (Down_Project (G.Proof_Ins, Analyzed_View),
                  (1 => (Source => Proof_Ins,
                         Target => Variable)));
         Connect (Down_Project (G.Inputs, Analyzed_View),
                  (1 => (Source => Inputs,
                         Target => Variable)));
         Connect (Down_Project (G.Outputs, Analyzed_View),
                  (1 => (Source => Outputs,
                         Target => Variable)));
      end Add_Down_Projected_Globals;

      -----------------
      -- Add_Globals --
      -----------------

      procedure Add_Globals (G : Global_Nodes) is
      begin
         Connect (G.Proof_Ins, (1 => (Source => Proof_Ins,
                                      Target => Variable)));
         Connect (G.Inputs,    (1 => (Source => Inputs,
                                      Target => Variable)));
         Connect (G.Outputs,   (1 => (Source => Outputs,
                                      Target => Variable)));
      end Add_Globals;

      -------------
      -- Connect --
      -------------

      procedure Connect
        (Targets : Node_Sets.Set;
         Edges   : Edge_Kinds)
      is
         function Image (G : Global_Id) return String;
         --  Convert global G to string usable for debugging

         -----------
         -- Image --
         -----------

         function Image (G : Global_Id) return String is
         begin
            return
              (if Is_Heap_Entity (G.Entity)
               then Name_Of_Heap_Variable
               else Full_Source_Name (G.Entity)) &
              "'" & Global_Kind'Image (G.Kind);
         end Image;

      --  Start of processing for Connect

      begin
         for Target_Entity of Targets loop
            for Edge of Edges loop
               declare
                  Source : constant Global_Id :=
                    (Entity => E,
                     Kind   => Edge.Source);

                  Target : constant Global_Id :=
                    (Entity => Target_Entity,
                     Kind   => Edge.Target);

               begin
                  Global_Graph.Include_Vertex (Target);

                  Global_Graph.Add_Edge (Source, Target);
                  --  ??? Graphs API should provide Insert and we should
                  --  use Vertex_Ids here.

                  if Debug_Global_Graph then
                     Ada.Text_IO.Put_Line
                       ("  " &
                          Image (Source) & " -> " &
                          Image (Target));
                  end if;
               end;
            end loop;
         end loop;
      end Connect;

   --  Start of processing for Add

   begin
      for Kind in Proof_Ins .. Outputs loop
         Global_Graph.Include_Vertex ((Kind => Kind, Entity => E));
      end loop;

      if E = Analyzed
        or else Parent_Scope (E) = Analyzed
      then
         if (case Ekind (E) is
                when E_Package
                =>
                   Present (Get_Pragma (E, Pragma_Initializes)),

                when Entry_Kind
                   | E_Function
                   | E_Procedure
                   | E_Task_Type
                =>
                   Entity_In_SPARK (E)
                   and then not Entity_Body_In_SPARK (E)
                   and then Has_User_Supplied_Globals (E),

                when E_Protected_Type
                =>
                   Meaningless,

                when others => raise Program_Error)
         then
            Debug ("Adding to graph (down-projected):", E);
            Add_Down_Projected_Globals (Contr.Proper);
         else
            Debug ("Adding to graph (refined):", E);
            Add_Globals (Contr.Refined);
         end if;
      else
         Debug ("Adding to graph (proper):", E);
         Add_Down_Projected_Globals (Contr.Proper);
      end if;

      --  For proof calls connect the caller's Proof_Ins vertex to the callee's
      --  Proof_Ins and Inputs (because Inputs of the callee are now accessed
      --  as Proof_Ins). Do nothing for outputs, because they cannot be access
      --  from a proof context.
      Connect (Contr.Proof_Calls,
               (1 => (Source => Proof_Ins, Target => Proof_Ins),
                2 => (Source => Proof_Ins, Target => Inputs),
                3 => (Source => Outputs,   Target => Outputs)));

      --  For definite calls connect the caller's Proof_Ins, Inputs and Outputs
      --  vertices respectively to the callee's Proof_Ins, Inputs and Outputs
      --  vertices.
      Connect (Contr.Definite_Calls,
               (1 => (Source => Proof_Ins, Target => Proof_Ins),
                2 => (Source => Inputs,    Target => Inputs),
                3 => (Source => Outputs,   Target => Outputs)));

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

      Connect (Contr.Conditional_Calls,
               (1 => (Source => Proof_Ins, Target => Proof_Ins),
                2 => (Source => Inputs,    Target => Inputs),
                3 => (Source => Inputs,    Target => Outputs),
                4 => (Source => Outputs,   Target => Outputs)));

      for Child of Scope_Map (E) loop
         Add (Child, Analyzed, Contracts, Global_Graph);
      end loop;
   end Add;

   procedure Add_Nonreturning (E          :        Entity_Id;
                               Contracts  :        Entity_Contract_Maps.Map;
                               Call_Graph : in out Call_Graphs.Graph)
   is
   begin
      if Is_Callee (E) then
         Call_Graph.Include_Vertex (E);

         for Callee of Contracts (E).Direct_Calls loop
            if Is_In_Analyzed_Files (Callee) then
               if Ekind (Callee) in Entry_Kind
                                  | E_Function
                                  | E_Procedure
                 and then Contracts (Callee).Has_Terminate
               then
                  null;
               else
                  --  ??? cut graph at Nonreturning and Recursive subprograms
                  Call_Graph.Include_Vertex (Callee);

                  Call_Graph.Add_Edge (E, Callee);
               end if;
            end if;
         end loop;
      end if;

      for Child of Scope_Map (E) loop
         Add_Nonreturning (Child, Contracts, Call_Graph);
      end loop;
   end Add_Nonreturning;

   -------------------
   -- Add_Recursive --
   -------------------

   procedure Add_Recursive (E           :        Entity_Id;
                            Contracts   :        Entity_Contract_Maps.Map;
                            Call_Graph  : in out Call_Graphs.Graph)
   is
   begin
      if Is_Callee (E) then
         Call_Graph.Include_Vertex (E);

         for Callee of Contracts (E).Direct_Calls loop
            if Is_In_Analyzed_Files (Callee) then
               Call_Graph.Include_Vertex (Callee);

               Call_Graph.Add_Edge (E, Callee);
            end if;
         end loop;
      end if;

      for Child of Scope_Map (E) loop
         Add_Recursive (Child, Contracts, Call_Graph);
      end loop;
   end Add_Recursive;

   -------------
   -- Analyze --
   -------------

   procedure Analyze
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
   is
      Contr : Contract;
      --  Contract for the analyzed entity

   begin
      case Ekind (Analyzed) is
         when Entry_Kind
            | E_Function
            | E_Procedure
            | E_Task_Type
         =>
            Contr := (if Entity_In_SPARK (Analyzed)
                        and then Entity_Body_In_SPARK (Analyzed)
                      then Analyze_Body (Analyzed)
                      else Analyze_Spec (Analyzed));

         when E_Package =>
            Contr := (if Entity_In_SPARK (Analyzed)
                      then Analyze_Body (Analyzed)
                      else Analyze_Spec (Analyzed));

         when E_Protected_Type =>
            --   ??? perhaps we should do something, but now we don't
            null;

         when others =>
            raise Program_Error;
      end case;

      --  Terminating stuff, picked no matter if body is in SPARK
      Contr.Has_Terminate :=
        (if Is_Proper_Callee (Analyzed)
         then Has_Terminate_Annotation (Analyzed)
         else Meaningless);

      Contr.Calls_Current_Task := Includes_Current_Task (Contr.Direct_Calls);

      Contracts.Insert (Analyzed, Contr);

      if Analyzed = Root_Entity
        or else not Is_Leaf (Analyzed)
      then
         for Child of Scope_Map (Analyzed) loop
            Analyze (Child, Contracts);
         end loop;

         declare
            Global_Graph : Global_Graphs.Graph := Global_Graphs.Create;
            --  Graph with references from the analyzed entity and its nested
            --  entities.

         begin
            Add (Analyzed, Analyzed, Contracts, Global_Graph);

            Global_Graph.Close;

            Print_Partial_Graph
              (Prefix => Unique_Name (Analyzed),
               G      => Global_Graph);

            Fold (Analyzed     => Analyzed,
                  Folded       => Analyzed,
                  Global_Graph => Global_Graph,
                  Contracts    => Contracts);
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
            Filter_Local (Analyzed, C.Proper);
            Filter_Local (Analyzed, C.Refined);

            --  Protected type appear as an implicit parameter to protected
            --  subprograms and protected entries, and as a global to things
            --  nested in them. After resolving calls from protected
            --  subprograms and protected entries to their nested things the
            --  type will also appear as a global of the protected
            --  subprogram/entry. Here we strip it. ??? Conceptually this
            --  belongs to Filter_Local where Scope_Same_Or_Within does not
            --  capture this.

            if Ekind (S) = E_Protected_Type then
               C.Proper.Inputs.Exclude (S);
               C.Proper.Outputs.Exclude (S);
               C.Proper.Proof_Ins.Exclude (S);
               C.Refined.Inputs.Exclude (S);
               C.Refined.Outputs.Exclude (S);
               C.Refined.Proof_Ins.Exclude (S);
            end if;
         end;
      end if;

      --  Only debug output from now on
      Debug_Traversal (Analyzed);

      Dump (Contracts, Analyzed);
   end Analyze;

   ------------------
   -- Analyze_Body --
   ------------------

   function Analyze_Body (E : Entity_Id) return Contract
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
         declare
            Unused : Node_Sets.Set;
            --  ??? should be remove

         begin
            Compute_Globals
              (FA,
               Inputs_Proof          => Contr.Refined.Proof_Ins,
               Inputs                => Contr.Refined.Inputs,
               Outputs               => Contr.Refined.Outputs,
               Proof_Calls           => Contr.Proof_Calls,
               Definite_Calls        => Contr.Definite_Calls,
               Conditional_Calls     => Contr.Conditional_Calls,
               Local_Variables       => Contr.Local_Variables,
               Local_Ghost_Variables => Contr.Local_Ghost_Variables,
               Local_Subprograms     => Unused,
               Local_Definite_Writes => Contr.Initializes);
         end;

      else
         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Task_Type
            =>
               --  Use globals from spec, but calls and tasking info from body
               Contr.Proper  := Contract_Globals (E, Refined => False);
               Contr.Refined := Contract_Globals (E, Refined => True);

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

         --  We start with all calls being remote and filter local ones later
         Contr.Remote_Calls := FA.Direct_Calls;
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
   end Analyze_Body;

   ------------------
   -- Analyze_Spec --
   ------------------

   function Analyze_Spec (E : Entity_Id) return Contract is

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

         procedure Collect (Vars : Node_Sets.Set);

         -------------
         -- Collect --
         -------------

         procedure Collect (Vars : Node_Sets.Set) is
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
         end Collect;

      --  Start of processing for Unsynchronized_Globals

      begin
         Collect (G.Proof_Ins);
         Collect (G.Inputs);
         Collect (G.Outputs);

         return Unsynch;
      end Unsynchronized_Globals;

   --  Start of processing for Analyze_Spec

   begin
      if Ekind (E) in Entry_Kind
                    | E_Function
                    | E_Procedure
                    | E_Task_Type
      then
         if Has_User_Supplied_Globals (E) then

            --  Pretend that user supplied refined globals
            Contr.Proper := Contract_Globals (E, Refined => False);

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Proper);

         --  Capture (Yannick's) "frontend globals"; once they will end up in
         --  the ALI file they should be indistinguishable from other globals.

         else
            Contr.Refined := Frontend_Globals (E);

            --  Frontend globals does not distinguish Proof_Ins from Inputs;
            --  conservatively assume that all reads belong to Inputs.
            pragma Assert (Contr.Refined.Proof_Ins.Is_Empty);

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Refined);
         end if;
      end if;

      Contr.Direct_Calls      := Frontend_Calls (E);
      Contr.Conditional_Calls := Contr.Direct_Calls;

      pragma Assert
        (if Is_Proper_Callee (E)
         then Contract_Calls (E).Is_Subset (Contr.Conditional_Calls));

      --  We register subprograms with body not in SPARK as nonreturning except
      --  when they are:
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

      return Contr;
   end Analyze_Spec;

   ---------------------
   -- Contracts_Calls --
   ---------------------

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set is
      Calls : Node_Sets.Set;

      procedure Collect_Calls (Expr : Node_Id)
      with Global => Calls;
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

      G : Global_Nodes;

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

      G.Proof_Ins := To_Node_Set (Proof_Ins_FS);
      G.Inputs    := To_Node_Set (Inputs_FS);
      G.Outputs   := To_Node_Set (Outputs_FS);

      return G;
   end Contract_Globals;

   -----------
   -- Debug --
   -----------

   procedure Debug (Label : String; E : Entity_Id) is
   begin
      if XXX then
         Ada.Text_IO.Put_Line (Label & " " & Full_Source_Name (E));
      end if;
   end Debug;

   ----------
   -- Dump --
   ----------

   procedure Dump
     (Contracts : Entity_Contract_Maps.Map;
      Analyzed  : Entity_Id)
   is
      Indent : constant String := "  ";

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
            if not G.Proof_Ins.Is_Empty
              or else not G.Inputs.Is_Empty
              or else not G.Outputs.Is_Empty
            then
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

               Dump ("Global",         Contr.Proper);
               Dump ("Refined_Global", Contr.Refined);

               if not Contr.Proof_Calls.Is_Empty
                 or else not Contr.Conditional_Calls.Is_Empty
                 or else not Contr.Definite_Calls.Is_Empty
               then
                  Ada.Text_IO.Put_Line (Indent & Indent & "Calls:");
                  Dump (Indent & Indent & "Proof      ",
                        Contr.Proof_Calls);
                  Dump (Indent & Indent & "Conditional",
                        Contr.Conditional_Calls);
                  Dump (Indent & Indent & "Definite   ",
                        Contr.Definite_Calls);
               end if;

               if not Contr.Remote_Calls.Is_Empty then
                  Ada.Text_IO.Put_Line (Indent & Indent & "Calls:");
                  Dump (Indent & Indent & "Remote     ", Contr.Remote_Calls);
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
                     Dump (Indent & "Initializes  ", Contr.Initializes);

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
           or else not Scope_Within_Or_Same (N, E)
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

   procedure Fold (Folded       :        Entity_Id;
                   Analyzed     :        Entity_Id;
                   Global_Graph :        Global_Graphs.Graph;
                   Contracts    : in out Entity_Contract_Maps.Map)
   is
      Folded_Scope : constant Flow_Scope := Get_Flow_Scope (Folded);

      Contr : Contract renames Contracts (Folded);

      use Global_Graphs;

      function Collect
        (E            : Entity_Id;
         Global_Graph : Global_Graphs.Graph)
         return Global_Nodes
      with Pre => Is_Caller_Entity (E);

      function Is_Fully_Written
        (State   : Entity_Id;
         Outputs : Node_Sets.Set)
            return Boolean
        with Pre => Ekind (State) = E_Abstract_State;
      --  Returns True iff all constituents of State are among Outputs

      procedure Up_Project
        (Vars      : Node_Sets.Set;
         Projected : out Node_Sets.Set;
         Partial   : out Node_Sets.Set)
        with Post =>
          (for all E of Partial => Ekind (E) = E_Abstract_State);

      use type Node_Sets.Set; --  to make "or" operator visible

      -------------
      -- Collect --
      -------------

      function Collect
        (E            : Entity_Id;
         Global_Graph : Global_Graphs.Graph)
         return Global_Nodes
      is

         procedure Collect
           (Kind :     Global_Kind;
            Vars : out Node_Sets.Set);
         --  Collect variables referenced from the Folded'Kind vertex
         --  into Vars.

         -------------
         -- Collect --
         -------------

         procedure Collect
           (Kind :     Global_Kind;
            Vars : out Node_Sets.Set)
         is
            Calls : constant Global_Graphs.Vertex_Id :=
              Global_Graph.Get_Vertex (Global_Id'(Kind   => Kind,
                                                  Entity => E));

         begin
            Vars.Clear;

            for V of Global_Graph.Get_Collection (Calls, Out_Neighbours)
            loop
               declare
                  Global : Global_Id renames Global_Graph.Get_Key (V);
               begin
                  if Global.Kind = Variable then
                     Vars.Insert (Global.Entity);
                  end if;
               end;
            end loop;
         end Collect;

         --  Local variables

         Result : Global_Nodes;

      --  Start of processing for Collect

      begin
         Collect (Proof_Ins, Result.Proof_Ins);
         Collect (Inputs,    Result.Inputs);
         Collect (Outputs,   Result.Outputs);

         Result.Proof_Ins.Difference (Result.Inputs);

         declare
            Proof_Ins_Outs : constant Node_Sets.Set :=
              Result.Proof_Ins and Result.Outputs;
         begin
            Result.Proof_Ins.Difference (Proof_Ins_Outs);
            Result.Inputs.Union (Proof_Ins_Outs);
         end;

         return Result;
      end Collect;

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
        (Vars      : Node_Sets.Set;
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
      RProof, RConditional, RDefinite : Node_Sets.Set;

   --  Start of processing for Fold

   begin
      Debug ("Folding", Folded);

      Contr.Refined := Collect (Folded, Global_Graph);

      declare
         Projected, Partial : Node_Sets.Set;
      begin
         Up_Project (Contr.Refined.Inputs, Projected, Partial);
         Contr.Proper.Inputs := Projected or Partial;

         Up_Project (Contr.Refined.Outputs, Projected, Partial);
         for State of Partial loop
            if not Is_Fully_Written (State, Contr.Refined.Outputs)
            then
               Contr.Proper.Inputs.Include (State);
            end if;
         end loop;
         Contr.Proper.Outputs := Projected or Partial;

         Up_Project (Contr.Refined.Proof_Ins, Projected, Partial);
         Contr.Proper.Proof_Ins :=
           (Projected or Partial) -
           (Contr.Proper.Inputs or Contr.Proper.Outputs);

         --  Handle package Initializes aspect
         if Ekind (Folded) = E_Package then
            for Definite_Call of Contr.Definite_Calls loop
               declare
                  G : constant Global_Nodes :=
                    Collect (Definite_Call, Global_Graph);
               begin
                  Contr.Initializes.Union
                    ((G.Outputs - G.Inputs) and Contr.Local_Variables);
               end;
            end loop;

            Up_Project (Contr.Initializes, Projected, Partial);

            for State of Partial loop
               if Is_Fully_Written (State, Contr.Initializes) then
                  Projected.Include (State);
               end if;
            end loop;
            Contr.Initializes := Projected;
         end if;
      end;

      --  Categorize calls: PROOF CALLS

      declare
         type Calls is record
            Proof, Other : Node_Sets.Set;
         end record;

         Todo : Calls := (Proof => Contr.Proof_Calls,
                          Other => Contr.Conditional_Calls or
                                   Contr.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Proof.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Proof.First_Element;

                  Inserted : Boolean;
                  Unused   : Node_Sets.Cursor;
                  C        : Entity_Contract_Maps.Cursor;

               begin
                  Done.Proof.Insert (New_Item  => Pick,
                                     Position  => Unused,
                                     Inserted  => Inserted);

                  if Inserted then
                     C := Contracts.Find (Pick);
                     if Entity_Contract_Maps.Has_Element (C) then

                        Todo.Proof.Union
                          ((Contracts (C).Proof_Calls or
                            Contracts (C).Conditional_Calls or
                            Contracts (C).Definite_Calls)
                           - Done.Proof);
                     end if;
                  end if;

                  Todo.Proof.Delete (Pick);
               end;
            elsif not Todo.Other.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Other.First_Element;

                  C : constant Entity_Contract_Maps.Cursor :=
                    Contracts.Find (Pick);
               begin
                  Done.Other.Insert (Pick);

                  if Entity_Contract_Maps.Has_Element (C) then
                     Todo.Proof.Union (Contracts (C).Proof_Calls -
                                       Done.Proof);

                     Todo.Other.Union ((Contracts (C).Conditional_Calls or
                                        Contracts (C).Definite_Calls)
                                       - Done.Other);
                  end if;

                  Todo.Other.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Contr.Proof_Calls.Is_Subset (Of_Set => Done.Proof));

         RProof := Done.Proof;
      end;

      --  Categorize calls: CONDITIONAL CALLS

      declare
         type Calls is record
            Conditional, Definite : Node_Sets.Set;
         end record;

         Todo : Calls := (Contr.Conditional_Calls,
                          Contr.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Conditional.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Conditional.First_Element;

                  Inserted : Boolean;
                  Unused   : Node_Sets.Cursor;
                  C        : Entity_Contract_Maps.Cursor;

               begin
                  Done.Conditional.Insert (New_Item  => Pick,
                                           Position  => Unused,
                                           Inserted  => Inserted);

                  if Inserted then
                     C := Contracts.Find (Pick);
                     if Entity_Contract_Maps.Has_Element (C) then

                        Todo.Conditional.Union
                          ((Contracts (C).Conditional_Calls or
                            Contracts (C).Definite_Calls)
                           - Done.Conditional);
                     end if;
                  end if;

                  Todo.Conditional.Delete (Pick);
               end;
            elsif not Todo.Definite.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Definite.First_Element;

                  C : constant Entity_Contract_Maps.Cursor :=
                    Contracts.Find (Pick);
               begin
                  Done.Definite.Insert (Pick);

                  if Entity_Contract_Maps.Has_Element (C) then
                     Todo.Conditional.Union (Contracts (C).Conditional_Calls -
                                             Done.Conditional);

                     Todo.Definite.Union (Contracts (C).Definite_Calls -
                                          Done.Definite);
                  end if;

                  Todo.Definite.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert
           (Contr.Conditional_Calls.Is_Subset (Of_Set => Done.Conditional));

         RConditional := Done.Conditional;
      end;

      --  Categorize calls: Definite CALLS

      declare
         Todo : Node_Sets.Set := Contr.Definite_Calls;
         Done : Node_Sets.Set;

      begin
         loop
            if not Todo.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.First_Element;

                  Inserted : Boolean;
                  Unused   : Node_Sets.Cursor;
                  C        : Entity_Contract_Maps.Cursor;

               begin
                  Done.Insert (New_Item  => Pick,
                               Position  => Unused,
                               Inserted  => Inserted);

                  if Inserted then
                     C := Contracts.Find (Pick);
                     if Entity_Contract_Maps.Has_Element (C) then

                        Todo.Union (Contracts (C).Definite_Calls - Done);
                     end if;
                  end if;

                  Todo.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert
           (Contr.Definite_Calls.Is_Subset (Of_Set => Done));

         RDefinite := Done;
      end;

      RProof.Difference (RConditional);
      RProof.Difference (RDefinite);

      RConditional.Difference (RDefinite);

      --  ??? should be disjoint, enforce it
      pragma Assert (RProof.Intersection (RConditional).Is_Empty);
      pragma Assert (RConditional.Intersection (RDefinite).Is_Empty);
      pragma Assert (RProof.Intersection (RDefinite).Is_Empty);

      Contr.Proof_Calls       := RProof;
      Contr.Conditional_Calls := RConditional;
      Contr.Definite_Calls    := RDefinite;

      Filter_Local (Analyzed, Contr.Proof_Calls);
      Filter_Local (Analyzed, Contr.Definite_Calls);
      Filter_Local (Analyzed, Contr.Conditional_Calls);

      Filter_Local (Analyzed, Contr.Remote_Calls);

      for Child of Scope_Map (Folded) loop
         Fold (Child, Analyzed, Global_Graph, Contracts);
      end loop;
   end Fold;

   procedure Fold_Nonreturning (Folded     :        Entity_Id;
                                Call_Graph :        Call_Graphs.Graph;
                                Contracts  : in out Entity_Contract_Maps.Map)
   is
   begin
      if Is_Proper_Callee (Folded) then
--        Contracts (Folded).Nonreturning :=
--          (for some Callee of
--             Call_Graph.Get_Collection (Call_Graph.Get_Vertex (Folded),
--                                        Call_Graphs.Out_Neighbours) =>
--                Contracts (Call_Graph.Get_Key (Callee)).Nonreturning);

         for Callee of
           Call_Graph.Get_Collection (Call_Graph.Get_Vertex (Folded),
                                      Call_Graphs.Out_Neighbours)
         loop
            declare
               E : constant Entity_Id := Call_Graph.Get_Key (Callee);

            begin
               if Contracts (E).Nonreturning then
                  Contracts (Folded).Nonreturning := True;
                  exit;
               end if;
            end;
         end loop;

      --  For non-callee entities we still need a dummy value, otherwise we
      --  would access an invalid data.

      else
         Contracts (Folded).Nonreturning := Meaningless;
      end if;

      for Child of Scope_Map (Folded) loop
         Fold_Nonreturning (Child, Call_Graph, Contracts);
      end loop;
   end Fold_Nonreturning;

   procedure Fold_Recursive (Folded     :        Entity_Id;
                             Call_Graph :        Call_Graphs.Graph;
                             Contracts  : in out Entity_Contract_Maps.Map)
   is
   begin
      Contracts (Folded).Recursive :=
        (if Is_Proper_Callee (Folded)
         then Call_Graph.Edge_Exists (Folded, Folded)
         else Meaningless);

      for Child of Scope_Map (Folded) loop
         Fold_Recursive (Child, Call_Graph, Contracts);
      end loop;
   end Fold_Recursive;

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

   procedure Generate_Contracts (GNAT_Root : Node_Id)
   is
      Contracts : Entity_Contract_Maps.Map;
      --  Partial information collected by analysis of inner scopes needed for
      --  the summary of their outer scopes.

   --  Start of processing for Generate_Globals

   begin
      Dump_Tree;

      --  GG section in ALI must be present, even if it is empty
      GG_Write_Initialize (GNAT_Root);

      if Present (Root_Entity) then

         --  Generate Global contract

         Analyze (Root_Entity, Contracts);

         --  Recursive contract is used when generating the Nonreturning
         --  contract, so it must be done first.

         Generate_Recursive_Contract : declare
            Call_Graph : Call_Graphs.Graph := Call_Graphs.Create;

         begin
            Add_Recursive (Root_Entity, Contracts, Call_Graph);

            Call_Graph.Close;

            Fold_Recursive (Root_Entity, Call_Graph, Contracts);
         end Generate_Recursive_Contract;

         Generate_Nonreturning_Contract : declare
            Call_Graph : Call_Graphs.Graph := Call_Graphs.Create;

         begin
            Add_Nonreturning (Root_Entity, Contracts, Call_Graph);

            Call_Graph.Close;

            Fold_Nonreturning (Root_Entity, Call_Graph, Contracts);
         end Generate_Nonreturning_Contract;

         Write_Contracts_To_ALI (Root_Entity, Contracts);

      end if;

      GG_Write_Finalize;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Term_Info.Set_Fg (Yellow);
         Ada.Text_IO.Put_Line ("Global generation complete for current CU");
         Term_Info.Set_Fg (Reset);
      end if;
   end Generate_Contracts;

   -----------------
   -- Global_Hash --
   -----------------

   function Global_Hash (G : Global_Id) return Ada.Containers.Hash_Type
   is
      use type Ada.Containers.Hash_Type;
   begin
      return 13 * Ada.Containers.Hash_Type (G.Entity) +
             17 * Ada.Containers.Hash_Type (Global_Kind'Pos (G.Kind));
   end Global_Hash;

   ---------------
   -- Is_Callee --
   ---------------

   function Is_Callee (E : Entity_Id) return Boolean
   is

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

   ----------------------
   -- Is_Proper_Callee --
   ----------------------

   function Is_Proper_Callee (E : Entity_Id) return Boolean is
     (Ekind (E) in Entry_Kind | E_Function | E_Procedure);

   -------------------------
   -- Print_Partial_Graph --
   -------------------------

   procedure Print_Partial_Graph (Prefix : String;
                                  G      : Global_Graphs.Graph)
   is
      use Global_Graphs;

      Filename : constant String := Prefix & "_partial_graph";

      function NDI
        (G : Graph;
         V : Vertex_Id)
         return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours)
         return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output

      ---------
      -- NDI --
      ---------

      function NDI
        (G : Graph;
         V : Vertex_Id) return Node_Display_Info
      is
         G_Id  : constant Global_Id := G.Get_Key (V);

         Shape : constant Node_Shape_T := (if G_Id.Kind = Variable
                                           then Shape_Oval
                                           else Shape_Box);

         Label : constant String :=
           (if Is_Heap_Entity (G_Id.Entity)
            then "__HEAP"
            else Full_Source_Name (G_Id.Entity) &
                 (case G_Id.Kind is
                     when Proof_Ins      => "'Proof_Ins",
                     when Inputs         => "'Inputs",
                     when Outputs        => "'Outputs",
                     when Variable       => ""));

         Rv : constant Node_Display_Info := Node_Display_Info'
           (Show        => False
                           or else G.In_Neighbour_Count (V) > 0
                           or else G.Out_Neighbour_Count (V) > 0,
            Shape       => Shape,
            Colour      => Null_Unbounded_String,
            Fill_Colour => Null_Unbounded_String,
            Label       => To_Unbounded_String (Label));
      begin
         return Rv;
      end NDI;

      ---------
      -- EDI --
      ---------

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours)
         return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked, Colour);

         Rv : constant Edge_Display_Info :=
           Edge_Display_Info'(Show   => True,
                              Shape  => Edge_Normal,
                              Colour => Null_Unbounded_String,
                              Label  => Null_Unbounded_String);
      begin
         return Rv;
      end EDI;

   --  Start of processing for Print_Global_Graph

   begin
      if XXX then
         G.Write_Pdf_File
           (Filename  => Filename,
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);
      end if;
   end Print_Partial_Graph;

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
            --  ??? temporarily replace prama with an error message below

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
         GG_Register_Remote_Calls (E, Contr.Remote_Calls);

         GG_Register_Global_Info
           ((Name                  => To_Entity_Name (E),
             Local                 => not Is_Visible (E, Null_Flow_Scope),
             Kind                  => Ekind (E),
             Origin                => Origin_Flow,      --  ??? dummy
             Proper                =>
               (Proof_Ins => To_Name_Set (Contr.Proper.Proof_Ins),
                Inputs    => To_Name_Set (Contr.Proper.Inputs),
                Outputs   => To_Name_Set (Contr.Proper.Outputs)),
             Refined               =>
               (Proof_Ins => To_Name_Set (Contr.Refined.Proof_Ins),
                Inputs    => To_Name_Set (Contr.Refined.Inputs),
                Outputs   => To_Name_Set (Contr.Refined.Outputs)),
             Proof_Calls           => To_Name_Set (Contr.Proof_Calls),
             Definite_Calls        => To_Name_Set (Contr.Definite_Calls),
             Conditional_Calls     => To_Name_Set (Contr.Conditional_Calls),
             Local_Variables       => To_Name_Set (Contr.Local_Variables),
             Local_Ghost_Variables => To_Name_Set
                                        (Contr.Local_Ghost_Variables),
             Local_Subprograms     => <>,
             Local_Definite_Writes => To_Name_Set (Contr.Initializes),
             Has_Terminate         => Contr.Has_Terminate,
             Recursive             => Contr.Recursive,
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
