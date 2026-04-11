# GoedelLogic

An extension of https://github.com/DafinaTrufas/Intuitionistic-Logic-Lean to Goedel logic.

The following files are minor modifications of work found in the above repository:
"Filters.lean",
"Formula.lean",
"GLSyntax.lean",
"LAlgebraSoundness.lean",
"LAlgebraCompleteness.lean".

The other files are my own original work, following the propositional part of Alfred Horn's paper "Logic with Truth Values in a Linearly Ordered Heyting Algebra" https://www.jstor.org/stable/2270905.

To install this project:
1. Install Lean 4 https://lean-lang.org/install/manual/
2. Download the zip file
3. Extract the contents of the zip file
4. Open command prompt (or equivalent), and navigate to the extracted folder
5. Note that you may have to enter a further subfolder, just make sure you are in the folder with files such as "Main.lean" and "GoedelLogic.lean"
6. Run "lake clean" and then "lake build" - this may take a while the first time because it compiles all of Mathlib. You may get a warning telling you to update the Mathlib version, but I advise against it because the code in this repository may break in newer versions
7. If it builds successfully, everything is working as it should
8. Optionally, open the project folder in an editor such as VSCode, make sure you open the folder that contains "Main.lean" and "GoedelLogic.lean", not anything higher or lower in the folder hierarchy.
