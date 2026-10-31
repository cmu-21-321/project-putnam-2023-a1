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
  | zero => simp [f]
  | succ n ih => rw [f, ih]; ring_nf; exact Real.cos_zero

-- First establish the quadratic expansion of cos at zero.
lemma cos_taylor_zero :
    Asymptotics.IsLittleO (𝓝 (0 : ℝ))
      (fun x : ℝ => Real.cos x - (1 - x^2 / 2))
      (fun x : ℝ => x^2) := by
  have ht :=
    taylor_isLittleO_univ
      (n := 2) (x₀ := (0 : ℝ)) Real.contDiff_cos
  have hp (x : ℝ) :
      taylorWithinEval Real.cos 2 Set.univ 0 x =
        1 - x^2 / 2 := by
    norm_num [taylorWithinEval_succ,
      iteratedDerivWithin_univ, iteratedDeriv_succ,
      iteratedDeriv_zero, Real.deriv_cos',
      Real.deriv_sin, deriv_neg] ; ring
  simpa only [hp, sub_zero] using ht

-- Substitute a*x into the cosine expansion.
lemma cos_mul_taylor_zero (a : ℝ) :
    Asymptotics.IsLittleO (𝓝 (0 : ℝ))
      (fun x : ℝ =>
        Real.cos (a * x) - (1 - a^2 * x^2 / 2))
      (fun x : ℝ => x^2) := by
  have ha :
      Tendsto (fun x : ℝ => a * x)
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_id :
          Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)))
  have h := cos_taylor_zero.comp_tendsto ha
  simp only [Function.comp_def, mul_pow] at h
  exact h.of_const_mul_right

-- Now multiply the expansions inductively.
lemma f_taylor (n : ℕ) :
    Asymptotics.IsLittleO (𝓝 (0 : ℝ))
      (fun x : ℝ =>
        f x n -
          (1 -
            (∑ k ∈ Finset.range (n + 1), (k : ℝ)^2) *
              x^2 / 2))
      (fun x : ℝ => x^2) := by
  induction n with
  | zero =>
      simp [f]
  | succ n ih =>
      let a : ℝ := (n + 1 : ℕ)
      let S : ℝ :=
        ∑ k ∈ Finset.range (n + 1), (k : ℝ)^2
      have hcos := cos_mul_taylor_zero a
      -- Both multiplier functions are bounded near zero.
      have hc :
          ContinuousAt (fun x : ℝ => Real.cos (a * x)) 0 := by
        fun_prop
      have hp :
          ContinuousAt (fun x : ℝ => 1 - S * x^2 / 2) 0 := by
        fun_prop
      -- The old remainder multiplied by cosine.
      have h₁ :
          Asymptotics.IsLittleO (𝓝 (0 : ℝ))
            (fun x : ℝ =>
              Real.cos (a * x) *
                (f x n - (1 - S * x^2 / 2)))
            (fun x : ℝ => x^2) := by
        simpa only [one_mul] using
          (hc.tendsto.isBigO_one ℝ).mul_isLittleO ih
      -- The cosine remainder multiplied by the old polynomial.
      have h₂ :
          Asymptotics.IsLittleO (𝓝 (0 : ℝ))
            (fun x : ℝ =>
              (Real.cos (a * x) - (1 - a^2 * x^2 / 2)) *
                (1 - S * x^2 / 2))
            (fun x : ℝ => x^2) := by
        simpa only [mul_one] using
          hcos.mul_isBigO (hp.tendsto.isBigO_one ℝ)
      -- The product of the quadratic terms has order x^4.
      have h₃ :
          Asymptotics.IsLittleO (𝓝 (0 : ℝ))
            (fun x : ℝ => (a^2 * S / 4) * x^4)
            (fun x : ℝ => x^2) := by
        exact
          (Asymptotics.isLittleO_pow_pow
            (𝕜 := ℝ) (m := 2) (n := 4) (by norm_num)).const_mul_left
            (a^2 * S / 4)
      -- Add the three errors and simplify the algebra.
      refine ((h₁.add h₂).add h₃).congr ?_ (fun _ => rfl)
      intro x
      simp only [f, Finset.sum_range_succ, a, S] ; ring

def satisfiesTheProperty (n : ℕ) : Prop :=
  |deriv (deriv (fun x : ℝ => f x n)) 0| > 2023

theorem eighteenSatisfies : satisfiesTheProperty 18 := by
  sorry

theorem eighteenIsSmallest {n : ℕ} : satisfiesTheProperty (n : ℕ) → n ≥ 18 := by
  sorry

-- TODO for Friday:
-- Formalize the actual problem.
-- Set up a taylor series that was used in the solution.
