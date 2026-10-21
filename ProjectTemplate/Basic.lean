import Mathlib

/*
 Hi
*/


noncomputable def f (x : ℝ) : ℕ →  ℝ
  | 0 => -1
  | 1 => Real.cos x
  | 2 => Real.cos x * Real.cos (2 * x)
  | n + 2 => Real.cos ((n + 2) * x) * (f x (n + 1))


  theorem Smallest_Num sorry :(



- TODO for Friday:
- Formalize the actual problem.
- Set up a taylor series that was used in the solution.
