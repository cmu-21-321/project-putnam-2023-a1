# 2023 Putnam A1 in Lean

This project formalizes the solution to the Putnam 2023 exam's problem A1.

The problem is stated as follows: 
For positive integer $n$, let 
$f_n(x) = \cos(x)\cos(2x)\cdots\cos(nx)$. What is the problem asks for the smallest positive
integer $n$ such that the absolute value of $f_n''(0)$ exceeds 2023? 

The proof computes
$f_n''(0) = -\sum_{k=1}^n k^2$ using the product rule and induction. We may obtain an expression
for $f_n''(0)$ as a sum of squares. This sum is
1785 at $n = 17$ and 2109 at $n = 18$. Sums of squares increase so $n = 18$ is the smallest possible.

## Repository guide

- [Main formalization]Project_Files/putnam_2023_a1.lean contains the cosine product
  definition and the direct differentiation proof of the 2023 A1 result.
- [Taylor expansion]Project_Files/Putnam2023A1Taylor.lean proves some of the results leading 
up to an alternate approach to proving the problem result using Taylor expansions.
- [Putnam B1 exploration]Project_Files/putnam_2-23_b1.lean gives the initial definitions for a 
separate problem. 

