# 2023 Putnam A1 in Lean

This project formalizes the solution to the Putnam 2023 exam's problem A1.

The problem is stated as follows: 
For positive integer $n$, let 
$f_n(x) = \cos(x)\cos(2x)\cdots\cos(nx)$. What is the problem asks for the smallest positive
integer $n$ such that the absolute value of $f_n''(0)$ exceeds 2023? 

The proof computes
$f_n''(0) = -\sum_{k=1}^n k^2$ using the product rule and induction. The sum is
1785 at $n = 17$ and 2109 at $n = 18$, so monotonicity gives the minimum $n = 18$.

## Repository guide

- [Main formalization](Project_Files/putnam_2023_a1.lean) defines the cosine product as
  `f`. Start with `f_second_deriv_zero` for the derivative calculation, then see
  `eighteenSatisfies` and `eighteenIsSmallest` for the final result.
- [Project outline](Project_Files/Outline.md) records the initial proof plan.
- [Putnam B1 exploration](Project_Files/putnam_2-23_b1.lean) defines the initial
  coin configuration and legal moves for a separate problem.

## Checking the proof

With Lean installed via elan, run these commands from the repository root. Elan
selects the Lean version pinned in [lean-toolchain](lean-toolchain).

```sh
lake exe cache get
lake env lean Project_Files/putnam_2023_a1.lean
```
