/-
Copyright (c) 2026 CMU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiffany Darmawan, Daniela Bellido Rodriguez, Isaac Li
-/

import Mathlib
/-!
# hey
ok bye
-/
open scoped BigOperators Topology
open Filter Asymptotics

/-!
# STOP IT
HELP I'M TRAPPED IN A MODULE
-/
noncomputable def f (x : ℝ) : ℕ →  ℝ
  | 0 => 1
  | n + 1 => Real.cos ((n + 1 : ℕ) * x) * (f x n)

lemma f_zero (n : ℕ) : f 0 n = 1 := by
  induction n with
  | zero => unfold f; rfl
  | succ n ih => rw [f, ih]; ring_nf; exact Real.cos_zero

lemma f_is_twice_continuously_differentiable (n : ℕ) : ContDiff ℝ 2 (fun x : ℝ => f x n) := by
  induction n with
  | zero =>
      change ContDiff ℝ 2 (fun x : ℝ => (1 : ℝ))
      exact contDiff_const
  | succ n ih =>
      change ContDiff ℝ 2 (fun x : ℝ => Real.cos ((n + 1 : ℕ) * x) * f x n)
      have h_first_part_cont_diff :
          ContDiff ℝ 2 (fun x : ℝ => ((n + 1 : ℕ) : ℝ) * x) :=
        ContDiff.mul contDiff_const contDiff_id
      have h_cosine_part_cont_diff :
          ContDiff ℝ 2 (fun x : ℝ => Real.cos ((n + 1 : ℕ) * x)) :=
        Real.contDiff_cos.comp h_first_part_cont_diff
      exact ContDiff.mul h_cosine_part_cont_diff ih

-- The first derivative of the deriv function is twice differentiable,
-- so its derivative is differentiable.
lemma f_deriv_differentiable (n : ℕ) :
    Differentiable ℝ (deriv (fun x : ℝ => f x n)) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).mp
    (f_is_twice_continuously_differentiable n)
  exact h.2.2.differentiable (by norm_num)

-- The product rule for the first derivative, valid everywhere.
lemma f_deriv_succ (n : ℕ) :
    deriv (fun x : ℝ => f x (n + 1)) =
      fun x : ℝ =>
        -(Real.sin (((n + 1 : ℕ) : ℝ) * x) * ((n + 1 : ℕ) : ℝ)) * f x n +
          Real.cos (((n + 1 : ℕ) : ℝ) * x) * deriv (fun y : ℝ => f y n) x := by
  funext x
  let a : ℝ := (n + 1 : ℕ)
  have hf : DifferentiableAt ℝ (fun y : ℝ => f y n) x :=
    ((f_is_twice_continuously_differentiable n).differentiable (by norm_num)) x
  have hc :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-Real.sin (a * x) * a) x := by
    simpa using ((hasDerivAt_id x).const_mul a).cos
  change deriv (fun y : ℝ => Real.cos (a * y) * f y n) x = _
  refine (hc.mul hf.hasDerivAt).deriv.trans ?_
  ring

-- The first derivative vanishes at zero.
lemma f_deriv_zero (n : ℕ) : deriv (fun x : ℝ => f x n) 0 = 0 := by
  induction n with
  | zero =>
      change deriv (fun _ : ℝ => (1 : ℝ)) 0 = 0
      exact deriv_const 0 1
  | succ n ih =>
      rw [f_deriv_succ]
      simp [ih]

-- The second derivative at zero is minus the sum of the squares.
lemma f_second_deriv_zero (n : ℕ) :
    deriv (deriv (fun x : ℝ => f x n)) 0 =
      -∑ k ∈ Finset.range (n + 1), (k : ℝ)^2 := by
  induction n with
  | zero =>
      change deriv (deriv (fun _ : ℝ => (1 : ℝ))) 0 = _
      simp
  | succ n ih =>
      let a : ℝ := (n + 1 : ℕ)
      rw [f_deriv_succ]
      -- Derivatives of each of the four factors at zero.
      have hs :
          HasDerivAt (fun x : ℝ => -(Real.sin (a * x) * a))
            (-(Real.cos (a * 0) * a * a)) 0 := by
        exact ((((hasDerivAt_id (0 : ℝ)).const_mul a).sin.mul_const a).neg).congr_deriv
          (by simp)
      have hc :
          HasDerivAt (fun x : ℝ => Real.cos (a * x))
            (-Real.sin (a * 0) * a) 0 := by
        exact (((hasDerivAt_id (0 : ℝ)).const_mul a).cos).congr_deriv
          (by simp)
      have hf :
          HasDerivAt (fun x : ℝ => f x n)
            (deriv (fun x : ℝ => f x n) 0) 0 :=
        ((f_is_twice_continuously_differentiable n).differentiable
          (by norm_num) 0).hasDerivAt
      have hg :
          HasDerivAt (deriv (fun x : ℝ => f x n))
            (deriv (deriv (fun x : ℝ => f x n)) 0) 0 :=
        (f_deriv_differentiable n 0).hasDerivAt
      change deriv (fun x : ℝ =>
        -(Real.sin (a * x) * a) * f x n +
          Real.cos (a * x) * deriv (fun y : ℝ => f y n) x) 0 = _
      refine ((hs.mul hf).add (hc.mul hg)).deriv.trans ?_
      rw [ih, f_zero, f_deriv_zero,
        Finset.sum_range_succ _ (n + 1)]
      simp only [a, mul_zero, Real.cos_zero, Real.sin_zero]
      push_cast
      ring

def satisfiesTheProperty (n : ℕ) : Prop :=
  |deriv (deriv (fun x : ℝ => f x n)) 0| > 2023

-- Rewrite the property as a condition on the sum of squares.
lemma satisfiesTheProperty_iff (n : ℕ) :
    satisfiesTheProperty n ↔
      ∑ k ∈ Finset.range (n + 1), k^2 > 2023 := by
  unfold satisfiesTheProperty
  rw [f_second_deriv_zero, abs_neg,
    abs_of_nonneg (Finset.sum_nonneg (f := fun k : ℕ => (k : ℝ)^2)
      (fun k _ => sq_nonneg (k : ℝ)))]
  exact_mod_cast Iff.rfl

theorem eighteenSatisfies : satisfiesTheProperty 18 := by
  rw [satisfiesTheProperty_iff]
  decide

theorem eighteenIsSmallest {n : ℕ} : satisfiesTheProperty (n : ℕ) → n ≥ 18 := by
  rw [satisfiesTheProperty_iff]
  intro h
  by_contra hn
  push Not at hn
  -- The sum of squares is monotone, so it is at most the value at 17.
  have hle :
      ∑ k ∈ Finset.range (n + 1), k^2 ≤
        ∑ k ∈ Finset.range (17 + 1), k^2 :=
    Finset.sum_le_sum_of_subset
      (Finset.range_subset_range.mpr (by omega))
  have h17 : ∑ k ∈ Finset.range (17 + 1), k^2 = 1785 := by decide
  omega
