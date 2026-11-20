/-
Copyright (c) 2026 CMU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiffany Darmawan, Daniela Bellido Rodriguez, Isaac Li
-/

import Mathlib

/-!
# Putnam 2023 B1

Problem B1 on the 2023 Putnam exam is stated as follows. On an m by n
grid, coins are initially placed to fully occupy the upper-left
(m - 1) by (n - 1) rectangle. There is always at most coin per square.
A coin at i, j) can slide to (i + 1, j + 1) if that square and the two
squares (i + 1, j) and (i, j + 1) are on the board and empty.
How many distinct configurations can be reached after any number of
legal moves, including zero?

The definition initialConfiguration gives the starting set of occupied
squares, and legalMove describes a defines move and its effect.

The problem sheet for the 2023 Putnam exam is linked here: https://kskedlaya.org/putnam-archive/2023.pdf.
-/


-- Describes that the m-1 x n-1 grid initially contains the coins.
def initiallyContainsCoin (m n : ℕ)
  (coordinates : {i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}) : Prop :=
  coordinates.1.val < m ∧ coordinates.2.val < n

-- the initialConfiguration definition needs that it's decidable.
instance (m n : ℕ) : DecidablePred (initiallyContainsCoin m n) :=
  fun coordinates => by
    unfold initiallyContainsCoin
    infer_instance

-- Needed for decidability, apparently.
instance (m : ℕ) : Fintype {i : ℕ // 1 ≤ i ∧ i ≤ m} :=
  Fintype.subtype (Finset.Icc 1 m) (by intro i; simp)

-- Describes the initial configuration of the coins.
def initialConfiguration (m n : ℕ):
  Finset ({i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}) :=
  Finset.univ.filter (initiallyContainsCoin m n)

/-
Configuration is the locations of all the squares, origin is where it starts, destination is where
it goes.
-/
def moveIsAllowed {m n : ℕ}
  (configuration : Finset ({i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}))
  (origin destination : {i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n})
  : Prop :=
  destination.1.val = origin.1.val + 1
  ∧ destination.2.val = origin.2.val + 1
  ∧ origin ∈ configuration
  ∧ destination ∉ configuration
  ∧ (destination.1, origin.2) ∉ configuration
  ∧ (origin.1, destination.2) ∉ configuration

/-
Checks if the configuration matches after removing the coin from origin, then adding a coin to
the destination.
-/
def moveIsResultOfOther {m n : ℕ}
    (configuration nextConfiguration : Finset ({i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}))
    (origin destination : {i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n})
    : Prop :=
  nextConfiguration = insert destination (configuration.erase origin)

def legalMove {m n : ℕ}
    (configuration nextConfiguration : Finset ({i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n}))
    (origin destination : {i : ℕ // 1 ≤ i ∧ i ≤ m} × {j : ℕ // 1 ≤ j ∧ j ≤ n})
    : Prop :=
  moveIsAllowed configuration origin destination
  ∧ moveIsResultOfOther configuration nextConfiguration origin destination
