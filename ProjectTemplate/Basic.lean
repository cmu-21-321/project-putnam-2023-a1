import Mathlib

-- hello there this is really awesome and i hiope this is long enough?

-- sup
noncomputable def f (x : ℝ) : ℕ →  ℝ
  | 0 => 1
  | n + 1 => Real.cos ((n + 1 : ℕ) * x) * (f x n)

lemma f_zero (n : ℕ) : f 0 n = 1 := by
  induction n with
  | zero => simp [f]
  | succ n ih =>


def satisfiesTheProperty (n : ℕ) : Prop :=
  |deriv (deriv (fun x : ℝ => f x n)) 0| > 2023

theorem eighteenSatisfies : satisfiesTheProperty 18 := by
  sorry

theorem eighteenIsSmallest {n : ℕ} : satisfiesTheProperty (n : ℕ) → n ≥ 18 := by
  sorry

-- TODO for Friday:
-- Formalize the actual problem.
-- Set up a taylor series that was used in the solution.
