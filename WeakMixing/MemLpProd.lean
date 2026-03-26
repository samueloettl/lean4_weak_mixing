/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib

public section

open Set Filter Topology ComplexConjugate Function

namespace MeasureTheory

variable (R : Type*) [DivisionSemiring R] [Module R ℝ] {X : Type*} [MeasurableSpace X]
  {μ : Measure X} {T : X → X}

namespace Measure

lemma prod_eq_zero_left {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set α} (s_ae_empty : μ s = 0) :
    μ.prod ν (s ×ˢ Set.univ) = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
  _ ≤ _ := Measure.prod_prod_le _ _
  _ = _ := by simp [s_ae_empty]

lemma prod_eq_zero_right {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set β} (s_ae_empty : ν s = 0) :
    μ.prod ν (Set.univ ×ˢ s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
  _ ≤ _ := Measure.prod_prod_le _ _
  _ = _ := by simp [s_ae_empty]

end Measure

lemma essSup_prod_fst_le_essSup {α : Type*} {β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μ : Measure α} {ν : Measure β} (f : α → ENNReal) :
    essSup (f ·.1) (μ.prod ν) ≤ essSup f μ := by
  refine essSup_le_of_ae_le _ <|mem_ae_iff.mpr ?_
  rw [show {x:α×β | f x.1 ≤ essSup f μ}ᶜ = {a | f a > essSup f μ} ×ˢ Set.univ by ext; simp]
  exact Measure.prod_eq_zero_left <|meas_essSup_lt

lemma essSup_prod_snd_le_essSup {α : Type*} {β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μ : Measure α} {ν : Measure β} (g : β → ENNReal) :
    essSup (g ·.2) (μ.prod ν) ≤ essSup g ν := by
  refine essSup_le_of_ae_le _ <|mem_ae_iff.mpr ?_
  rw [show {x:α×β | g x.2 ≤ essSup g ν}ᶜ = Set.univ ×ˢ {b|g b > essSup g ν} by ext; simp]
  exact Measure.prod_eq_zero_right <| meas_essSup_lt

lemma memLp_conj {α : Type*} {mα : MeasurableSpace α}
{μ : Measure α} {f : α → ℂ} {p : ENNReal} (hf : MemLp f p μ)
: MemLp (conj f) p μ := by
  apply hf.congr_enorm
  · change AEStronglyMeasurable (conj ∘ f) μ
    exact AEStronglyMeasurable.comp_aemeasurable
      (Continuous.measurable Complex.continuous_conj|>.aestronglyMeasurable)
      hf.aemeasurable
  · simp

lemma memLp_conj' {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p : ENNReal}
    (f : Lp ℂ p μ) : MemLp (conj f) p μ :=
  MemLp.ae_eq
    (LipschitzWith.coeFn_compLp (Isometry.lipschitz Complex.isometry_conj) (map_zero _) f)
    (Lp.memLp <| LipschitzWith.compLp (Isometry.lipschitz Complex.isometry_conj) (map_zero _) f)

lemma memLp_prod_of_ne_top {α : Type*} {β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ} {p : NNReal}
    (hf : MemLp f p μ) (hg : MemLp g p ν) [SFinite ν] :
    MemLp (fun z ↦ f z.1 * g z.2) p (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd, ?_⟩
  unfold eLpNorm
  simp only [ENNReal.coe_eq_zero, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.coe_toReal]
  split
  · trivial
  · unfold eLpNorm'
    simp only [enorm_mul, one_div, NNReal.zero_le_coe, ENNReal.mul_rpow_of_nonneg]
    let f' := fun a : α ↦ ‖f a‖ₑ ^ (↑p:ℝ)
    let g' := fun b : β ↦ ‖g b‖ₑ ^ (↑p:ℝ)
    change (∫⁻ (a : α × β), f' a.1 * g' a.2 ∂μ.prod ν) ^ _ < _
    rw [lintegral_prod_mul]
    · have h1 := hf.eLpNorm_lt_top
      unfold eLpNorm at h1
      simp_all only [ENNReal.coe_eq_zero, ↓reduceIte, ENNReal.coe_ne_top, ENNReal.coe_toReal,
        gt_iff_lt]
      unfold eLpNorm' at h1
      change (∫⁻ (a : α), f' a ∂μ) ^ _ < _ at h1
      apply ENNReal.rpow_lt_top_iff_of_pos (by positivity)|>.mp at h1
      have h2 := hg.eLpNorm_lt_top
      unfold eLpNorm at h2
      simp_all only [ENNReal.coe_eq_zero, ↓reduceIte, ENNReal.coe_ne_top, ENNReal.coe_toReal,
        gt_iff_lt]
      unfold eLpNorm' at h2
      change (∫⁻ (a : β), g' a ∂ν) ^ _ < _ at h2
      apply ENNReal.rpow_lt_top_iff_of_pos (by positivity)|>.mp at h2
      apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
      exact ENNReal.mul_ne_top (ne_top_of_lt h1) (ne_top_of_lt h2)
    · apply AEMeasurable.pow_const
      apply AEStronglyMeasurable.enorm
      exact AEMeasurable.aestronglyMeasurable hf.aemeasurable
    · apply AEMeasurable.pow_const
      apply AEStronglyMeasurable.enorm
      exact AEMeasurable.aestronglyMeasurable hg.aemeasurable

lemma memLp_prod {α : Type*} {β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
{μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ} (p : ENNReal)
(hf : MemLp f p μ) (hg : MemLp g p ν)
[SFinite ν] : MemLp (fun z ↦ f z.1 * g z.2) p (μ.prod ν) := by
  by_cases hp : p = ⊤
  · refine ⟨AEStronglyMeasurable.mul hf.aestronglyMeasurable.comp_fst
      hg.aestronglyMeasurable.comp_snd, ?_⟩
    simp_all only [eLpNorm_exponent_top]
    unfold eLpNormEssSup
    simp only [enorm_mul]
    let f' := fun x:α × β ↦ ‖f x.1‖ₑ
    let g' := fun x:α × β ↦ ‖g x.2‖ₑ
    change essSup (f' * g') (μ.prod ν) < ⊤
    calc
    _ ≤ essSup (f') (μ.prod ν) * essSup (g') (μ.prod ν) := by exact ENNReal.essSup_mul_le f' g'
    _ ≤ essSup (fun x ↦ ‖f x‖ₑ) μ * essSup (fun y ↦ ‖g y‖ₑ) ν := by
      gcongr
      · exact essSup_prod_fst_le_essSup (fun a:α ↦ ‖f a‖ₑ)
      · exact essSup_prod_snd_le_essSup (fun b:β ↦ ‖g b‖ₑ)
    _ < _ := by
      change _ < ⊤ * (⊤:ENNReal)
      gcongr
      · have := hf.eLpNorm_lt_top
        unfold eLpNorm at this
        simp only [ENNReal.top_ne_zero, ↓reduceIte] at this
        exact this
      · have := hg.eLpNorm_lt_top
        unfold eLpNorm at this
        simp only [ENNReal.top_ne_zero, ↓reduceIte] at this
        exact this
  rw [← ENNReal.coe_toNNReal hp] at hf hg ⊢
  exact memLp_prod_of_ne_top hf hg

lemma ae_const_of_mul_conj_ae_const [SFinite μ] {f : X → ℂ} {a : ℂ}
    (h : (fun z ↦ f z.1 * conj f z.2) =ᶠ[ae (μ.prod μ)] const (X × X) a) :
    ∃ b, f =ᶠ[ae μ] const _ b := by
  by_cases h_zero : f =ᶠ[ae μ] const X 0
  · use 0
  rw [EventuallyEq, not_eventually] at h_zero
  have := Filter.Eventually.and_frequently (Measure.ae_ae_of_ae_prod h) h_zero
  obtain ⟨x, h⟩ := Filter.Frequently.exists this
  have (y : X) : f x * (starRingEnd ℂ) (f y) = a ↔ f y = conj a / conj f x := by
    have : (starRingEnd (X → ℂ)) f x ≠ 0 := by
      simp only [Pi.conj_apply, ne_eq, map_eq_zero]
      exact h.2
    rw [eq_div_iff this, ← EquivLike.apply_eq_iff_eq starRingAut, RingEquiv.map_mul, mul_comm]
    simp
  use conj a / conj f x
  simpa [this] using h.1


lemma eventuallyConst_prod_imp_eventuallyConst {A : Set X} {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] {B : Set Y} (h : EventuallyConst (A ×ˢ B) (ae (μ.prod ν))) :
    EventuallyConst A (ae μ) ∨ EventuallyConst B (ae ν) := by
  simp_all only [eventuallyConst_pred]
  cases h with
  | inl h =>
    change μ.prod ν (A ×ˢ B)ᶜ = _ at h
    rw [Set.compl_prod_eq_union] at h
    have := le_of_le_of_eq measure_le_measure_union_left h
    rw [nonpos_iff_eq_zero] at this
    simp only [measure_union_null_iff, Measure.prod_prod, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h
    cases h.1 with
    | inl h => exact Or.inl <|Or.inl h
    | inr h => simp [h]
  | inr h =>
    change μ.prod ν (A ×ˢ B)ᶜᶜ = _ at h
    simp only [compl_compl, Measure.prod_prod, mul_eq_zero] at h
    cases h with
    | inl h =>
      left; right
      simpa [ae_iff] using h
    | inr h =>
      right; right
      simpa [ae_iff] using h

lemma eventuallyConst_A_sq_imp_eventuallyConst_A [SFinite μ] {A : Set X}
    (h : EventuallyConst (A ×ˢ A) (ae (μ.prod μ))) : EventuallyConst A (ae μ) :=
  Or.elim (eventuallyConst_prod_imp_eventuallyConst h) id id

end MeasureTheory

lemma ENNReal.pow_eq_pow_iff_eq {a b : ENNReal} {p : ℝ} (hp : p ≠ 0) : a ^ p = b ^ p ↔ a = b := by
  constructor
  · intro h
    simpa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp] using congrArg (· ^ (p⁻¹)) h
  · intro h
    rw [h]
