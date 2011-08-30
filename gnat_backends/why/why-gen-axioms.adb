------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       W H Y - G E N - A X I O M S                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Sinfo;          use Why.Sinfo;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;

package body Why.Gen.Axioms is

   -------------------------
   -- Define_Coerce_Axiom --
   -------------------------

   procedure Define_Coerce_Axiom
     (File           : W_File_Id;
      Type_Name      : W_Identifier_Id;
      Base_Type      : W_Primitive_Type_Id;
      From_Base_Type : W_Identifier_Id;
      To_Base_Type   : W_Identifier_Id)
   is
      Arg_S                : constant String := "x";
      X_To_Type_Op         : constant W_Term_Id :=
                               New_Call
                                 (Domain => EW_Term,
                                  Name   => From_Base_Type,
                                  Args   => (1 => +New_Term (Arg_S)));
      Back_To_Base_Type_Op : constant W_Term_Id :=
                               New_Call
                                 (Domain => EW_Term,
                                  Name   => To_Base_Type,
                                  Args   => (1 => +X_To_Type_Op));
      In_Range             : constant W_Pred_Id :=
                               New_Call
                                 (Domain => EW_Pred,
                                  Name   =>
                                    Range_Pred_Name.Id (Type_Name),
                                  Args   =>
                                    (1 => +New_Term (Arg_S)));
      In_Range_t          : constant W_Term_Id :=
                               New_Call
                                 (Domain => EW_Term,
                                  Name   =>
                                    Range_Pred_Name.Id (Type_Name),
                                  Args   =>
                                    (1 => +New_Term (Arg_S)));
      Formula              : constant W_Pred_Id :=
                               New_Connection
                                 (Domain => EW_Pred,
                                  Op     => EW_Imply,
                                  Left   => +In_Range,
                                  Right  =>
                                    New_Relation
                                      (Left  => +Back_To_Base_Type_Op,
                                       Op    => EW_Eq,
                                       Right => New_Prog (Arg_S)));
      Quantif_On_X         : constant W_Pred_Id :=
                               New_Universal_Quantif
                                 (Var_Type  => Base_Type,
                                  Variables => (1 => New_Identifier (EW_Term,
                                                                     Arg_S)),
                                  Triggers  => New_Triggers (
                                    Triggers =>
                                      (1 => New_Trigger (
                                         Terms => (1 => In_Range_t,
                                                   2 => X_To_Type_Op)),
                                       2 => New_Trigger (
                                         Terms => (1 =>
                                                     Back_To_Base_Type_Op)))),
                                  Pred      => Formula);
   begin
      Emit
        (File,
         New_Axiom
           (Name => Coerce_Axiom.Id (Type_Name),
            Def  => Quantif_On_X));
   end Define_Coerce_Axiom;

   -------------------------
   -- Define_Getter_Axiom --
   -------------------------

   procedure Define_Getter_Axiom
     (File      : W_File_Id;
      Type_Name : String;
      C_Name    : W_Identifier_Id;
      Binders   : Binder_Array)
   is
      Call_To_Builder : constant W_Term_Id :=
                          New_Call
                            (Domain  => EW_Term,
                             Name    => Record_Builder_Name.Id (Type_Name),
                             Binders => Binders);
      Call_To_Getter  : constant W_Term_Id :=
                          New_Call
                           (Domain => EW_Term,
                            Name   => Record_Getter_Name.Id (C_Name),
                            Args   => (1 => +Call_To_Builder));
      Context         : constant W_Pred_Id :=
                          New_Equal (Call_To_Getter,
                                     +C_Name);
      UPB             : constant W_Pred_Id :=
                          New_Universal_Quantif
                            (Binders => Binders,
                             Pred    => Context);
   begin
      Emit
        (File,
         New_Axiom
           (Name => Record_Getter_Axiom.Id (C_Name),
            Def  => UPB));
   end Define_Getter_Axiom;

   ------------------------
   -- Define_Range_Axiom --
   ------------------------

   procedure Define_Range_Axiom
     (File       : W_File_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      Arg_S              : constant String := "x";
      Call_To_Conversion : constant W_Term_Id :=
                             New_Call
                               (Domain => EW_Term,
                                Name   => Conversion,
                                Args   => (1 => +New_Term (Arg_S)));
      Formula            : constant W_Pred_Id :=
                             New_Call
                               (Domain => EW_Pred,
                                Name   => Range_Pred_Name.Id (Type_Name),
                                Args   => (1 => +Call_To_Conversion));
      Quantif_On_X       : constant W_Pred_Id :=
                             New_Universal_Quantif
                               (Var_Type =>
                                  New_Abstract_Type (Name => Type_Name),
                                Variables =>
                                  (1 => New_Identifier (Arg_S)),
                                Pred =>
                                  Formula);
   begin
      Emit
        (File,
         New_Axiom
           (Name => Range_Axiom.Id (Type_Name),
            Def  => Quantif_On_X));
   end Define_Range_Axiom;

   --------------------------
   -- Define_Unicity_Axiom --
   --------------------------

   procedure Define_Unicity_Axiom
     (File       : W_File_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      X_S               : constant String := "x";
      Y_S               : constant String := "y";
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Domain => EW_Term,
                               Name   => Conversion,
                               Args   => (1 => +New_Term (X_S)));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Domain => EW_Term,
                               Name   => Conversion,
                               Args   => (1 => +New_Term (Y_S)));
      Formula           : constant W_Pred_Id :=
                            New_Connection
                              (Domain => EW_Pred,
                               Op     => EW_Imply,
                               Left   =>
                                 New_Relation
                                   (Domain => EW_Pred,
                                    Left   => +X_To_Base_Type_Op,
                                    Op     => EW_Eq,
                                    Right  => +Y_To_Base_Type_Op),
                               Right =>
                                 New_Relation
                                   (Domain => EW_Pred,
                                    Left   => +New_Term (X_S),
                                    Op     => EW_Eq,
                                    Right  => +New_Term (Y_S)));
      Quantif_On_XY     : constant W_Pred_Id :=
                            New_Universal_Quantif
                              (Var_Type =>
                                 New_Abstract_Type (Name => Type_Name),
                               Variables =>
                                 (New_Identifier (X_S),
                                  New_Identifier (Y_S)),
                               Pred =>
                                 Formula);
   begin
      Emit
        (File,
         New_Axiom
           (Name => Unicity_Axiom.Id (Type_Name),
            Def  => Quantif_On_XY));
   end Define_Unicity_Axiom;

end Why.Gen.Axioms;
