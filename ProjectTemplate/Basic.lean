/-
Copyright (c) 2026 CMU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiffany Darmawan, Daniela Bellido Rodriguez, Isaac Li
-/

import Mathlib

/-!
# STOP IT
HELP I'M TRAPPED IN A MODULE
-/
noncomputable def f (x : ℝ) : ℕ →  ℝ
  | 0 => 1
  | n + 1 => Real.cos ((n + 1 : ℕ) * x) * (f x n)

lemma f_zero (n : ℕ) : f 0 n = 1 := by
  induction n with
  | zero => simp [f]
  | succ n ih => rw [f, ih]; ring_nf; exact Real.cos_zero


def satisfiesTheProperty (n : ℕ) : Prop :=
  |deriv (deriv (fun x : ℝ => f x n)) 0| > 2023

theorem eighteenSatisfies : satisfiesTheProperty 18 := by
  sorry

theorem eighteenIsSmallest {n : ℕ} : satisfiesTheProperty (n : ℕ) → n ≥ 18 := by
  sorry

-- TODO for Friday:
-- Formalize the actual problem.
-- Set up a taylor series that was used in the solution.
