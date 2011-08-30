------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 S p e c                                  --
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

with Types;     use Types;
with VC_Kinds;  use VC_Kinds;
with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Preds is

   --  This package provides facilities to manipulate Why predicates

   procedure Define_Range_Predicate
     (File      : W_File_Id;
      Name      : String;
      Base_Type : W_Primitive_Type_Id;
      First     : W_Term_Id;
      Last      : W_Term_Id);
   --  Generate the definition of the range predicate for an abstract type
   --  whose base type is given in parameters. This predicate is True when
   --  the argument is in range First .. Last.

   procedure Define_Eq_Predicate
     (File           : W_File_Id;
      Name           : String;
      Base_Type_Name : String);
   --  Generate the definition of the equality predicate for an abstract type
   --  whose base type is given in parameters. This predicate is True when
   --  conversions to base type are equal.

   function New_Equal
     (Left  : W_Term_Id;
      Right : W_Term_Id) return W_Pred_Id;
   --  Create the predicate "Left = Right"

   function New_NEqual
     (Left  : W_Term_Id;
      Right : W_Term_Id) return W_Pred_Id;
   --  Create the predicate "Left <> Right"

   function New_Equal_Bool
     (Left  : W_Term_Id;
      Right : W_Pred_Id) return W_Pred_Id;
   --  Create the formula "Left = true <-> Right".

   function New_Located_Expr
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;

end Why.Gen.Preds;
