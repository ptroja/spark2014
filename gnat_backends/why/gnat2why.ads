------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             G N A T 2 W H Y                              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

--  This subsystem is for transforming a GNAT tree into Why.

package Gnat2Why is
   pragma Pure;

   --  Gnat2why is a tool to generate Why3 programs from Ada programs.

   ------------------------------------
   -- Labels interpreted by gnatwhy3 --
   ------------------------------------

   --  In addition to the Why3 program, more information is sometimes needed,
   --  for example for error reporting, showing VCs in a format close to Ada
   --  syntax and so on. Why3 allows giving such extra information in the form
   --  of labels, which can annotate terms/program expressions and identifier
   --  declarations. This section is an exhaustive list of all labels that are
   --  generated by gnat2why, and interpreted by gnatwhy3. Note that labels
   --  should never influence the actual interpretation of the program, because
   --  we want to guarantee that the standard Why3 tools can read programs
   --  generated by gnatwhy3.

   --  In the following description, labels are enclosed in quotes, and parts
   --  of the labels that must be replaced by concrete strings are enclosed by
   --  < >.
   --
   --  ----------------------
   --  -- Labels for terms --
   --  ----------------------
   --
   --  "GP_Sloc:<file1:line1:col1:...:file_n:line_n:col_n>"
   --  the encoding of a GNAT Source location. It is a list of triples, where
   --  the elements of the list and the triples themselves are separated by a
   --  colon. The first Sloc is the most generic, the last one is the last
   --  instantiation.
   --
   --  "GP_Reason:<VC_Kind>"
   --     The reason for a VC. <VC_Kind> should be obtained by VC_Kind'Image.
   --     Required for all VC nodes.
   --
   --  "GP_Subp:<file:line>"
   --     For a VC, defines to which subprogram it belongs. The subprogram is
   --     defined by file and line. Required for all VC nodes.
   --
   --  "keep_on_simp"
   --     Disallows simplification of that node. Required for all VC nodes.

end Gnat2Why;
