/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib
public import WeakMixing.AEEqFunCompMeasurePreservingIterate

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

open Filter MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
  [NormedAddCommGroup E] {β : Type*} {mb : MeasurableSpace β} {μb : Measure β} {f : α → β}

namespace MeasureTheory
namespace Lp


@[simp]
theorem compMeasurePreserving_id :
    compMeasurePreserving (E := E) (p := p) id (.id μb) = AddMonoidHom.id _ := by
  ext
  simp

theorem compMeasurePreserving_id_apply (g : Lp E p μb) :
    compMeasurePreserving id (MeasurePreserving.id μb) g = g := by simp

theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    {f : β → γ} (hf : MeasurePreserving f μb μc) {f' : α → β} (hf' : MeasurePreserving f' μ μb) :
    compMeasurePreserving (E := E) (p := p) (f ∘ f') (hf.comp hf') =
    (compMeasurePreserving f' hf').comp (compMeasurePreserving f hf) := by
  ext g
  simp [AEEqFun.compMeasurePreserving_comp _ hf hf']

theorem compMeasurePreserving_comp_apply {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    (g : Lp E p μc) {f : β → γ} (hf : MeasurePreserving f μb μc) {f' : α → β}
    (hf' : MeasurePreserving f' μ μb) :
    (compMeasurePreserving (f ∘ f') (hf.comp hf')) g =
    (compMeasurePreserving f' hf') ((compMeasurePreserving f hf) g) := by
  simp [compMeasurePreserving_comp hf hf']

theorem compMeasurePreserving_iterate {f : α → α} (hf : MeasurePreserving f μ μ) (n : ℕ) :
    (compMeasurePreserving (E := E) (p := p) f hf)^[n] =
    compMeasurePreserving f^[n] (MeasurePreserving.iterate hf n) := by
  funext
  induction n with
  | zero => simp
  | succ n h =>
    nth_rewrite 1 [add_comm n 1]
    simp [Function.iterate_add, h, compMeasurePreserving_comp (hf.iterate n) hf]

end Lp
end MeasureTheory
