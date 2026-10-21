import Mathlib
import Mathlib.Algebra.BigOperators.Finprod

def f (x : ℝ) : ℕ →  ℝ
  | Nat.0 => -1
  | Nat.succ 0 => Real.cos(x)
  | Nat.succ n => Real.cos(n * x) * (f x (n))
