/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib

--public import Mathlib.Algebra.Order.Ring.Star
--public import Mathlib.Analysis.CStarAlgebra.Classes
--public import Mathlib.Dynamics.Ergodic.Function
--public import Mathlib.Order.BourbakiWitt

/-!
# Characterization of ergodicity

In this file we prove that ergodicity wrt a probability measure is eqivalent to convergence of the
Birkhoff Averages of `μ (A ∩ (preimage f^[n] B))` to `μ A * μ B` for all measurable Sets A and B.
We also prove that the convergence for all measurable sets is equivalent to the convergence on a
π-system that generates the `σ`-algebra. (In particular for product measures of σ-finite spaces it
is enough to know the convergence on measurable rectangles.)
-/

public section

open Function Set Filter MeasureTheory Topology

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α} {f : α → α}

section birkhoffAverage

theorem Function.const.birkhoffAverage_eq₀ (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) {n : ℕ} (hn : (n : R) ≠ 0)
    (x : α) : birkhoffAverage R f (fun _ ↦ a) n x = a := by
  rw [birkhoffAverage, birkhoffSum, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul R,
    inv_smul_smul₀ hn]

theorem Function.const.birkhoffAverage_eq₀' (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) {n : ℕ} (hn : (n : R) ≠ 0) :
    birkhoffAverage R f (fun _ ↦ a) n = fun _ ↦ a := by
  ext x; exact Function.const.birkhoffAverage_eq₀ R a hn x

open Classical in
theorem Function.const.birkhoffAverage_eq (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) (n : ℕ)
    (x : α) : birkhoffAverage R f (fun _ ↦ a) n x = if (n : R) = 0 then 0 else a := by
  by_cases h : (n : R) = 0
  · simp [h, birkhoffAverage]
  simpa [h] using Function.const.birkhoffAverage_eq₀ R a h x

open Classical in
@[simp]
theorem Function.const.birkhoffAverage_eq' (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) (n : ℕ) :
    birkhoffAverage R f (fun _ ↦ a) n = fun _ ↦ if (n : R) = 0 then 0 else a := by
  ext x; exact Function.const.birkhoffAverage_eq R a n x

theorem birkhoffSum_le_birkhoffSum {α : Type*} {M : Type*} [AddCommMonoid M] [Preorder M]
    [AddLeftMono M] {f : α → α} {g g' : α → M} (h : g ≤ g') : birkhoffSum f g ≤ birkhoffSum f g' :=
  fun _ _ ↦ Finset.sum_le_sum (fun _ _ ↦ h _)

theorem birkhoffAverage_le_birkhoffAverage (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Preorder M] [PartialOrder R] [IsOrderedRing R] [Module R M] [PosSMulMono R M]
    [PosMulReflectLT R] [AddLeftMono M] (f : α → α) {g g' : α → M} (h : g ≤ g') :
    birkhoffAverage R f g ≤ birkhoffAverage R f g' :=
  fun n x ↦ smul_le_smul_of_nonneg_left
    (birkhoffSum_le_birkhoffSum h n x) <|inv_nonneg_of_nonneg <|Nat.cast_nonneg' n

theorem abs_comp_birkhoffAverage_le_birkhoffAverage_comp_abs (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommGroup M] [Lattice M] [PartialOrder R] [IsOrderedRing R] [Module R M] [PosSMulMono R M]
    [PosMulReflectLT R] [AddLeftMono M] (f : α → α) {g : α → M} :
    abs ∘ (birkhoffAverage R f g) ≤ birkhoffAverage R f (abs ∘ g) := by
  apply abs_le'.mpr
  rw [← birkhoffAverage_neg]
  exact ⟨birkhoffAverage_le_birkhoffAverage _ _ <|le_abs_self _,
    birkhoffAverage_le_birkhoffAverage _ _ <|neg_le_abs _⟩
