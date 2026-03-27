/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import WeakMixing.AEEqFunCompMeasurePreservingIterate

/-!
# Lp.compMeasurePreserving_iterate

In this file we prove that `Lp.compMeasurePreserving` plays well with composition. In particular
we prove that iterating `Lp.compMeasurePreserving` is the same as applying it to the iterated
composition. This is needed for the specialisation of the Von Neumann Mean Ergodic Theorem we want
to prove.
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
