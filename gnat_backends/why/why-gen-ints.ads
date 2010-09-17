------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         W H Y - G E N - I N T S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Types; use Types;

with Why.Ids; use Why.Ids;

package Why.Gen.Ints is
   --  This package provides an interface to generate declarations
   --  (types, subprograms, axioms) for integer types.

   procedure Declare_Abstract_Signed_Int
     (File : W_File_Id;
      Name : String;
      Size : Pos);
   --  Declare the whole theory for a signed int of the given size,
   --  i.e. whose range is -2 ** (Pos - 1) .. 2 ** (Pos - 1) -1.
   --  This creates an abstract type whose name is given in parameter
   --  along with a set of axioms and subprograms for int conversion.

   procedure Declare_Abstract_Signed_Int
     (File  : W_File_Id;
      Name  : String;
      First : Int;
      Last  : Int);
   --  Same as the previous function, except that the higher and lower
   --  bounds are specified explicitly.

end Why.Gen.Ints;
