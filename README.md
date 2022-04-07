# CSC335-Lambda-Subst
Final Project for a Functional Programming course I took. Therefore, certain details have been omitted.\
The subst function performs lambda substitution on an expression without capturing. This is achieved by looking for any bound variables and renaming them starting from x0 and incrementing the digit by 1 for each instance of variable that gets renamed to avoid capturing. It takes three arguments in order:
1. The lambda expression to perform the substitution on.
2. The lambda expression that will replace the 3rd argument.
3. The variable that will be substituted.
<!-- -->
The function assumes that none of the variables in all three arguments are named x<i>[some positive integer]</i>.
