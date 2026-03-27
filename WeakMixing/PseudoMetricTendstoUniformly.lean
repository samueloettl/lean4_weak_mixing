/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# PseudoMetricTendstoUiformly

In this file we prove some lemmas needed for OnAverageIndependent.lean. We apply these to get
uniform convergence of the Birkhoff averages such that we can exchange limits.
-/

public section

open Set Filter Topology

namespace Metric

theorem tendstoUniformlyOn_of_dist_le_tendsto_zero' {α β M : Type*} [PseudoMetricSpace M]
    {u : α → ℝ}
    {F : α → β → M} {f : β → M} {s : Set β} {l : Filter α}
    (hfu : ∀ᶠ n in l, ∀ x ∈ s, dist (f x) (F n x) ≤ u n) (h : Tendsto u l (𝓝 0)) :
    TendstoUniformlyOn F f l s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  rw [Metric.tendsto_nhds] at h
  specialize h ε εpos
  filter_upwards [hfu, h] with x hn hu n hs
  specialize hn n hs
  rw [Real.dist_0_eq_abs, abs_of_nonneg <|le_trans dist_nonneg hn] at hu
  exact lt_of_le_of_lt hn hu

theorem tendstoUniformlyOn_of_dist_le_tendsto_zero {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {s : Set β} {l : Filter α}
    (hfu : ∀ n x, x ∈ s → dist (f x) (F n x) ≤ u n) (h : Tendsto u l (𝓝 0)) :
    TendstoUniformlyOn F f l s :=
  tendstoUniformlyOn_of_dist_le_tendsto_zero' (Eventually.of_forall hfu) h

theorem tendstoUniformly_of_dist_le_tendsto_zero {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {l : Filter α} (hfu : ∀ n x, dist (f x) (F n x) ≤ u n)
    (h : Tendsto u l (𝓝 0)) : TendstoUniformly F f l :=
  tendstoUniformlyOn_univ.mp <|tendstoUniformlyOn_of_dist_le_tendsto_zero (fun n x _ ↦ hfu n x) h

theorem tendstoUniformly_of_dist_le_tendsto_zero' {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {l : Filter α} (hfu : ∀ᶠ n in l, ∀ x, dist (f x) (F n x) ≤ u n)
    (h : Tendsto u l (𝓝 0)) : TendstoUniformly F f l :=
  tendstoUniformlyOn_univ.mp <|tendstoUniformlyOn_of_dist_le_tendsto_zero'
    (Eventually.mono hfu (fun _ h x _ ↦ h x)) h

end Metric
