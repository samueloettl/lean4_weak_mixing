/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Von Neumann Mean Ergodic Theorem

In this file we specialize `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` to
the Koopman operator of an ergodic map.
-/

public section

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {E : Type*}
  [NormedAddCommGroup E] (𝕜 : Type*) (g : Lp E 2 μ)

namespace Ergodic

lemma eqLocus_compMeasurePreserving_eq_range_const {p : ENNReal} [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)] [IsFiniteMeasure μ] (h : Ergodic f μ) :
    LinearMap.eqLocus (Lp.compMeasurePreservingₗᵢ 𝕜 f h.toMeasurePreserving).toContinuousLinearMap 1
    = LinearMap.range (Lp.constₗ (E:=E) p μ 𝕜) := by
  ext g
  simp only [Lp.compMeasurePreservingₗᵢ, LinearMap.mem_eqLocus,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.coe_mk,
    Lp.compMeasurePreservingₗ_apply, Lp.compMeasurePreserving, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk,
    ContinuousLinearMap.one_apply, LinearMap.mem_range, Lp.constₗ_apply]
  constructor
  · intro hg
    obtain ⟨y, h⟩ := eq_const_of_compMeasurePreserving_eq h (congrArg Subtype.val hg)
    use y
    exact Eq.symm <|SetLike.coe_eq_coe.mp h
  · intro ⟨y, hg⟩
    rw [← hg]
    ext
    grw [AEEqFun.coeFn_compMeasurePreserving]
    by_cases hZ : NeZero μ
    · apply Filter.EventuallyEq.of_eq
      ext x
      simp [AEEqFun.coeFn_const_eq]
    · simp only [not_neZero.mp hZ]
      rfl

lemma projection_const [IsProbabilityMeasure μ] [RCLike 𝕜] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E] :
    (Lp.constₗ 2 μ 𝕜).range.starProjection g = Lp.const 2 μ (∫ x, g x ∂ μ) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨∫ x, g x ∂μ, rfl⟩
  · intro g ⟨c,hg⟩
    rw [Lp.constₗ_apply, ← indicatorConstLp_univ] at hg
    rw [inner_sub_left, ← indicatorConstLp_univ, ← hg, L2.inner_indicatorConstLp_indicatorConstLp,
      ← inner_conj_symm, L2.inner_indicatorConstLp_eq_inner_setIntegral]
    simp [sub_self]

/-- A special case of the von Neumann Mean Ergodic Theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` for the Koopman Operator of an
ergodic map. -/
theorem tendsto_birkhoffAverage_const [IsProbabilityMeasure μ] [RCLike 𝕜] [InnerProductSpace 𝕜 E]
    [NormedSpace ℝ E] [FiniteDimensional 𝕜 E] [CompleteSpace E] (h : Ergodic f μ) :
    Tendsto (birkhoffAverage 𝕜 (Lp.compMeasurePreserving f h.toMeasurePreserving) id · g) atTop
    (𝓝 (Lp.const 2 μ (∫x,g x ∂ μ))) := by
  simpa [eqLocus_compMeasurePreserving_eq_range_const _ h, projection_const] using
    ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    (Lp.compMeasurePreservingₗᵢ (E:=E) (p:=2) 𝕜 _ h.toMeasurePreserving).toContinuousLinearMap
    (LinearIsometry.norm_toContinuousLinearMap_le _) g

end Ergodic
