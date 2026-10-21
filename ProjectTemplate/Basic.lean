import Mathlib
import Mathlib.Algebra.BigOperators.Finprod

def f {ℝ ℕ} (x : ℝ) (n : ℕ) (hn : n ≥ 1) :=
  | x 1 => Real.cos(x)
  | x n => Real.cos(n * x) * (f x (n-1))
