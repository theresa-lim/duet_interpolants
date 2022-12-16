Test_Interpolants
====

This folder contains our test files for the Compositional SMT interpolate function. A description of each pair of files is below. To run, execute the following command:

./bigtop.exe -interpolate \[file\]A.smt2~\[file\]B.smt2

+ paperA/B.smt2 : the example in section 2 of the "Beautiful Interpolants" paper by Albarghouthi and McMillan.

+ linearA/B.smt2 : formulas with a linear seperating half-plane.

+ slopeA/B.smt2 : formulas requiring a steeper linear separating half-plane

+ tightA/B.smt2 : formulas that require multiple half-planes to separate.

+ slowA/B.smt2 : formulas that require multiple half planes to separate but have multiple options

+ bmcA/B.smt2 : formulas from the BMC model of the report, n = 1

+ bmcmedA/B.smt2 : formulas from the BMC model of the report, n = 4

+ bmcbigA/B.smt2 : formulas from the BMC model of the report, n = 10