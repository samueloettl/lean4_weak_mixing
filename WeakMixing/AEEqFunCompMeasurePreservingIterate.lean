/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# AEEqFun comp

In this file we prove that `compQuasiMeasurePreserving` plays well with composition. In particular
we prove that iterating `compQuasiMeasurePreserving` is the same as applying it to the iterated
composition. This is needed to prove similar results for the Koopman operator
`Lp.comMeasurePreserving`. We also state and prove the corresponding auxiliary for
`compMeasurePreserving`.
-/

public section

open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} [MeasurableSpace α] {μ ν : Measure α} [TopologicalSpace δ]

@[gcongr]
theorem Filter.EventuallyEq.fun_comp' {α : Type*} {β : Type*} {γ : Type*} {f g : α → β}
    {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) : h ∘ f =ᶠ[l] h ∘ g :=
  Filter.EventuallyEq.fun_comp H h

namespace MeasureTheory

namespace Measure
namespace QuasiMeasurePreserving
protected theorem congr {α β : Type*} {ma : MeasurableSpace α}
    {mb : MeasurableSpace β} {μa : Measure α} {μb : Measure β} {f f' : α → β}
    (hf : QuasiMeasurePreserving f μa μb) (hf' : Measurable f') (h : f =ᵐ[μa] f') :
    QuasiMeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.absolutelyContinuous

@[gcongr]
theorem ae_eq' {α : Type*} {β : Type*} {δ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure α} {μb : MeasureTheory.Measure β}
    {f : α → β} (h : MeasureTheory.Measure.QuasiMeasurePreserving f μa μb)
    {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) : g₁ ∘ f =ᵐ[μa] g₂ ∘ f := ae_eq h hg

end QuasiMeasurePreserving
end Measure

namespace MeasurePreserving

protected theorem congr {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}
    {μa : Measure α} {μb : Measure β} {f f' : α → β} (hf : MeasurePreserving f μa μb)
    (hf' : Measurable f') (h : f =ᵐ[μa] f') : MeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.map_eq

end MeasurePreserving

namespace AEEqFun

section compQuasiMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α → β}

open MeasureTheory.Measure (QuasiMeasurePreserving)

theorem compQuasiMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compQuasiMeasurePreserving g f hf = compQuasiMeasurePreserving g f' (hf.congr hf' h) := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]
theorem compQuasiMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compQuasiMeasurePreserving g id (.id ν) = g := by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _

theorem compQuasiMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : QuasiMeasurePreserving f ν ξ) {f' : α → β}
    (hf' : QuasiMeasurePreserving f' μ ν) :
    compQuasiMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compQuasiMeasurePreserving (compQuasiMeasurePreserving g f hf) f' hf' := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]
  assumption

theorem compQuasiMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : QuasiMeasurePreserving f μ μ) (n : ℕ) :
    (compQuasiMeasurePreserving · f hf)^[n] g =
    compQuasiMeasurePreserving g (f^[n]) (hf.iterate n) := by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

end compQuasiMeasurePreserving


section compMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β}
  {f : α → β} {g : β → γ}


theorem compMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compMeasurePreserving g f hf = compMeasurePreserving g f' (hf.congr hf' h) :=
  compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]
theorem compMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compMeasurePreserving g id (.id ν) = g :=
  compQuasiMeasurePreserving_id _

theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : MeasurePreserving f ν ξ) {f' : α → β}
    (hf' : MeasurePreserving f' μ ν) :
    compMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compMeasurePreserving (compMeasurePreserving g f hf) f' hf' :=
  compQuasiMeasurePreserving_comp _ _ _

theorem compMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : MeasurePreserving f μ μ) (n : ℕ) :
    (compMeasurePreserving · f hf)^[n] g = compMeasurePreserving g (f^[n]) (hf.iterate n) :=
  compQuasiMeasurePreserving_iterate _ _ _


end compMeasurePreserving

end AEEqFun

end MeasureTheory
