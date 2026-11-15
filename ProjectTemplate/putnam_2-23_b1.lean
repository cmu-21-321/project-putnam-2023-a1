import Mathlib

def initiallyContainsCoin (m n : ℕ)
  (coordinates : {i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n})

def initialConfiguration (m n : ℕ):
  Finset ({i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}) :=
