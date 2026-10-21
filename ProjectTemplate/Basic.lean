import Mathlib

noncomputable def f (x : ℝ) : ℕ →  ℝ
  | 0 => -1
  | 1 => Real.cos x
  | 2 => Real.cos x * Real.cos (2 * x)
  | n + 2 => Real.cos ((n + 2) * x) * (f x (n + 1))
