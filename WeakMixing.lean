import Mathlib
import WeakMixing.OnAverageIndependent
import WeakMixing.MemLpProd

open Filter Topology Function MeasureTheory ComplexConjugate

variable (R : Type*) [DivisionSemiring R] [Module R ℝ] {X : Type*} [MeasurableSpace X]
  {μ : Measure X} {T : X → X}

universe u

def WeakMixing {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) : Prop :=
  ∀ {Y : Type u} [MeasurableSpace Y], ∀ {ν : Measure Y} [IsFiniteMeasure ν],
  ∀ {S : Y → Y}, Ergodic S ν → Ergodic (Prod.map T S) (Measure.prod μ ν)

def WeakMixing' {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) : Prop :=
  ∀ {Y : Type u} [MeasurableSpace Y], ∀ {ν : Measure Y} [IsProbabilityMeasure ν],
  ∀ {S : Y → Y}, Ergodic S ν → Ergodic (Prod.map T S) (Measure.prod μ ν)

def TraditionalWeakMixing (T : X → X) (μ : Measure X) : Prop :=
  ∀ {A}, MeasurableSet A → ∀ {B}, MeasurableSet B →
  Tendsto (birkhoffAverage R (Set.preimage T) (fun S ↦ |μ.real (A ∩ S) - μ.real A * μ.real B|) · B)
  atTop (𝓝 0)

def DoublyErgodic (T : X → X) (μ : Measure X) : Prop :=
  Ergodic (Prod.map T T) (Measure.prod μ μ)

def DoublyWeakMixing (T : X → X) (μ : Measure X) : Prop :=
  TraditionalWeakMixing R (Prod.map T T) (μ.prod μ)

def SpectralWeakMixingL2Complex (h : MeasurePreserving T μ μ) : Prop :=
  ∀ {c:ℂ}, ∀{f : Lp ℂ 2 μ}, (Lp.compMeasurePreserving T h) f = c • f
  → ∃ (a : ℂ), f =ᶠ[ae μ] const X a

theorem traditionalWeakMixing_congr_ring (S : Type*) [DivisionSemiring S] [Module S ℝ] (T : X → X)
    (μ : Measure X) : TraditionalWeakMixing R T μ = TraditionalWeakMixing S T μ := by
  simp only [TraditionalWeakMixing, birkhoffAverage_congr_ring R S]

theorem traditionalWeakMixing_congr_ring' (S : Type*) [DivisionSemiring S] [Module S ℝ] :
    TraditionalWeakMixing (X := X) R = TraditionalWeakMixing S := by
  unfold TraditionalWeakMixing
  simp only [birkhoffAverage_congr_ring' R S]

theorem ergodic_of_traditionalWeakMixing [IsProbabilityMeasure μ] (hM : Measurable T) {R : Type*}
    [DivisionSemiring R] [Module R ℝ] (h : TraditionalWeakMixing R T μ) : Ergodic T μ := by
  rw [traditionalWeakMixing_congr_ring' R ℝ] at h
  refine Ergodic.of_onAverageIndependent hM (fun A hA B hB ↦ ?_)
  specialize h hA hB
  apply Filter.tendsto_sub_const_iff (μ.real A * μ.real B)|>.mp
  rw [sub_self, tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall <|fun _ ↦ abs_nonneg _) ?_ h
  simp only [eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  nth_rewrite 1 [← Function.const.birkhoffAverage_eq₀ ℝ (f := Set.preimage T)
    (μ.real A * μ.real B) (Nat.cast_ne_zero.mpr <|Nat.ne_zero_of_lt hn) B]
  rw [← Pi.sub_apply, ← Pi.sub_apply, ← birkhoffAverage_sub]
  exact abs_comp_birkhoffAverage_le_birkhoffAverage_comp_abs _ _ _ _

lemma measurable_of_measurable_prod_map_pUnit {f : PUnit → PUnit} (h : Measurable <| Prod.map T f) :
    Measurable T := by
  intro A hA
  specialize h <|hA.prod .univ
  simp only [Set.preimage_prod_map_prod, Set.preimage_univ] at h
  apply measurableSet_prod.mp at h
  cases h with
  | inl h => exact h.1
  | inr h => cases h with
  | inl h =>
    rw [h]
    exact MeasurableSet.empty
  | inr h => exact False.elim (IsEmpty.false (self:=Set.univ_eq_empty_iff.mp h) PUnit.unit)

lemma ergodic_of_ergodic_prod_pUnit {f : PUnit → PUnit}
    (h : Ergodic (Prod.map T f) (μ.prod (Measure.dirac PUnit.unit))) : Ergodic T μ :=
  MeasurePreserving.ergodic_of_ergodic_semiconj measurePreserving_fst h
    (measurable_of_measurable_prod_map_pUnit h.toMeasurePreserving.measurable)
    (congrFun rfl)

lemma ergodic_dirac_pUnit (f : PUnit → PUnit) : Ergodic f (.dirac PUnit.unit) :=
  ⟨.id (Measure.dirac _), ⟨fun _ _ _ ↦ EventuallyConst.of_subsingleton_left⟩⟩

theorem weakMixing_iff_weakMixing' (T : X → X) (μ : Measure X) :
    WeakMixing T μ ↔ WeakMixing' T μ := by
  refine ⟨fun h Y _ ν _ S hS ↦ h hS, fun h Y _ ν _ S hS ↦ ?_⟩
  by_cases hν : ν = 0
  · rw [hν, Measure.prod_zero]
    refine Ergodic.zero_measure <|Measurable.prodMap ?_ hS.measurable
    apply measurable_of_measurable_prod_map_pUnit
    exact h (ergodic_dirac_pUnit id)|>.measurable
  · have : NeZero ν := ⟨hν⟩
    specialize h <|Ergodic.smul_measure hS (ν Set.univ)⁻¹
    refine ⟨⟨h.measurable, ?_⟩, ⟨?_⟩⟩
    · ext A hA
      have := congrFun (congrArg DFunLike.coe h.map_eq) A
      simp only [Measure.prod_smul_right, Measure.map_smul, Measure.smul_apply, smul_eq_mul] at this
      have h := congrArg ENNReal.toReal this
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, mul_eq_mul_left_iff, inv_eq_zero] at h
      rw [ENNReal.toReal_eq_toReal_iff, ENNReal.toReal_eq_zero_iff] at h
      cases h with
      | inl h => cases h with
        | inl h => rw [h]
        | inr h => cases h with
          | _ h => simp [h.1, h.2] at this
      | inr h => cases h with
        | inl h =>
          rw [Measure.measure_univ_eq_zero] at h
          exact False.elim (hν h)
        | inr h =>
          exact False.elim ((measure_ne_top ν Set.univ) h)
    · intro A hA hAinv
      have := h.aeconst_set hA hAinv
      rw [Measure.prod_smul_right] at this
      simpa only [ne_eq, ENNReal.inv_eq_zero, measure_ne_top, not_false_eq_true,
        Measure.ae_ennreal_smul_measure_eq] using this

theorem traditionalWeakMixing_of_doublyWeakMixing [IsProbabilityMeasure μ]
    (h : DoublyWeakMixing R T μ) : TraditionalWeakMixing R T μ := by
  intro A hA B hB
  simpa [birkhoffAverage, birkhoffSum, ← Set.preimage_iterate_eq, Set.preimage_prod_map_prod,
    Set.prod_inter_prod] using h (MeasurableSet.prod hA MeasurableSet.univ)
      (MeasurableSet.prod hB MeasurableSet.univ)

theorem ergodic_of_weakMixing (h : WeakMixing T μ) : Ergodic T μ :=
  ergodic_of_ergodic_prod_pUnit <|h <|ergodic_dirac_pUnit id

theorem doublyErgodic_of_weakMixing [IsFiniteMeasure μ] (h : WeakMixing T μ) :
    DoublyErgodic T μ := h <|ergodic_of_weakMixing h

lemma measurePreserving_of_doublyErgodic [SFinite μ] (h : DoublyErgodic T μ) :
    MeasurePreserving T μ μ := by
  have h_T_meas : Measurable T := by
    by_cases h_empty : IsEmpty X
    · exact Measurable.of_discrete
    rw [not_isEmpty_iff, ← exists_true_iff_nonempty] at h_empty
    obtain ⟨x,_⟩ := h_empty
    exact measurable_snd.comp <|h.measurable.comp <|measurable_prodMk_left (x:=x)
  refine ⟨h_T_meas, ?_⟩
  ext A hA
  rw [Measure.map_apply h_T_meas hA]
  have := congrFun (congrArg DFunLike.coe h.map_eq) (A ×ˢ A)
  rw [Measure.map_apply (h_T_meas.prodMap h_T_meas) (hA.prod hA)] at this
  change (μ.prod μ) ((T ⁻¹' A) ×ˢ (T ⁻¹' A)) = (μ.prod μ) (A ×ˢ A) at this
  simp only [Measure.prod_prod] at this
  repeat rw [← pow_two, ← ENNReal.rpow_two] at this
  simpa only [ENNReal.pow_eq_pow_iff_eq <|NeZero.ne 2] using this

lemma ergodic_of_doublyErgodic [SFinite μ] (h : DoublyErgodic T μ) : Ergodic T μ := by
  refine ⟨measurePreserving_of_doublyErgodic h, ⟨fun A hAm hAi ↦ ?_⟩⟩
  have : Prod.map T T ⁻¹' A ×ˢ A = A ×ˢ A := by
    change (T ⁻¹' A) ×ˢ (T ⁻¹' A) = A ×ˢ A
    rw [hAi]
  have := h.toPreErgodic.aeconst_set (MeasurableSet.prod hAm hAm) this
  exact eventuallyConst_A_sq_imp_eventuallyConst_A this

theorem spectralWeakMixingL2Complex_of_doublyErgodic (h : DoublyErgodic T μ) [SFinite μ] :
    SpectralWeakMixingL2Complex (measurePreserving_of_doublyErgodic h) := by
  intro c f hf
  by_cases h_null : f = 0
  · use 0
    rw [h_null]
    exact ae_eq_trans (AEEqFun.ext_iff.mp rfl) (AEEqFun.coeFn_const _ (μ:=μ) (0:ℂ))
  let g := fun z:X×X ↦ f z.1 * conj (f:X→ℂ) z.2
  have : ∃ a:ℂ, g =ᶠ[ae (μ.prod μ)] const (X×X) a := by
    apply Ergodic.ae_eq_const_of_ae_eq_comp_ae h
    · exact memLp_prod 2 (Lp.memLp f) (memLp_conj' f)|>.aestronglyMeasurable
    · change (μ.prod μ) {x | (g ∘ Prod.map T T) x = g x}ᶜ = 0
      have hf' := hf
      apply Lp.ext_iff.mp at hf
      have hf := ae_eq_trans (ae_eq_trans (ae_eq_symm (Lp.coeFn_compMeasurePreserving f
        (measurePreserving_of_doublyErgodic h))) hf) (Lp.coeFn_smul c f)
      change μ {x | (f ∘ T) x = c • f x}ᶜ = 0 at hf
      simp only [comp_apply, smul_eq_mul] at hf
      unfold g
      simp only [Pi.conj_apply, comp_apply, Prod.map_fst, Prod.map_snd]
      have : {x:X | (f ∘ T) x = c * f x}×ˢ{x:X | (f ∘ T) x = c * f x} ⊆
        {x:X×X | f (T x.1) * (starRingEnd ℂ) (f (T x.2)) = f x.1 * (starRingEnd ℂ) (f x.2)} := by
        intro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [comp_apply, Set.mem_setOf_eq] at hx hy ⊢
        rw [hx, hy]
        simp only [map_mul]
        have : c * conj c = 1 := by
          have : ‖c‖ = 1 := by
            calc
            _ = ‖c‖*1 := by rw [mul_one]
            _ = ‖c‖*(‖f‖/‖f‖) := by
              congr
              rw [div_self]
              exact norm_ne_zero_iff.mpr h_null
            _ = _ := by rw[mul_div, ← norm_smul, ← hf', Lp.norm_compMeasurePreserving,
              div_self (norm_ne_zero_iff.mpr h_null)]
          rw [Complex.mul_conj', this, Complex.ofReal_one, one_pow]
        rw [mul_comm c, mul_assoc, ← mul_assoc c, this, one_mul]
      apply Measure.mono_null (Set.compl_subset_compl_of_subset this)
      exact Measure.measure_prod_compl_eq_zero hf hf
  obtain ⟨a, h⟩ := this
  exact ae_const_of_mul_conj_ae_const h

theorem weakMixing_of_traditionalWeakMixing [IsProbabilityMeasure μ] (hm : Measurable T)
    (h : TraditionalWeakMixing R T μ) : WeakMixing T μ := by
  apply weakMixing_iff_weakMixing' T μ|>.mpr
  intro Y _ ν _ S hS
  apply Ergodic.of_onAverageIndependent <| Measurable.prodMap hm hS.measurable
  intro A hA b hB
  apply Ergodic.onAverageIndependent_measurableSet_of_piSystem
    (Eq.symm <| generateFrom_prod (α := X) (β := Y))
  · exact isPiSystem_prod
  · exact ergodic_of_traditionalWeakMixing hm h|>.toMeasurePreserving.prod hS.toMeasurePreserving
  · simp only [Set.mem_image2, Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro A A₁ hA₁ A₂ hA₂ hA B B₁ hB₁ B₂ hB₂ hB
    unfold Ergodic.OnAverageIndependent birkhoffAverage birkhoffSum
    rw [← hA, ← hB]
    simp only [← Set.preimage_iterate_eq, Prod.map_iterate, Set.preimage_prod_map_prod,
      Set.prod_inter_prod, measureReal_prod_prod,
      show
          ∀ (x : ℕ),
            ∀ (a : ℝ),
              μ.real (A₁ ∩ T^[x] ⁻¹' B₁) * a =
                (μ.real (A₁) * μ.real (B₁) +
                    (μ.real (A₁ ∩ T^[x] ⁻¹' B₁) - μ.real (A₁) * μ.real (B₁))) *
                  a
          by intros; simp,
      add_mul, Finset.sum_add_distrib, smul_eq_mul, mul_add]
    rw [← add_zero (μ.real A₁ * ν.real A₂ * (μ.real B₁ * ν.real B₂))]
    apply Tendsto.add
    · have (x:ℕ) : (x:ℝ)⁻¹ * ∑ x ∈ Finset.range x,
            μ.real A₁ * μ.real B₁ * ν.real (A₂ ∩ S^[x] ⁻¹' B₂) =
          μ.real A₁ * μ.real B₁ * ((x:ℝ)⁻¹ * ∑ x ∈ Finset.range x,
            ν.real (A₂ ∩ S^[x] ⁻¹' B₂)) := by
        simp only [← Finset.mul_sum]
        ring
      simp only [this]
      rw [show μ.real A₁ * ν.real A₂ * (μ.real B₁ * ν.real B₂) =
        μ.real A₁ * μ.real B₁ * (ν.real A₂ * ν.real B₂) by ring]
      apply Tendsto.const_mul
      simp only [Set.preimage_iterate_eq]
      exact hS.onAverageIndependent A₂ hA₂ B₂ hB₂
    · rw [tendsto_zero_iff_abs_tendsto_zero]
      rw [traditionalWeakMixing_congr_ring' R ℝ] at h
      apply squeeze_zero (g := fun x:ℕ ↦
        (x:ℝ)⁻¹ • ∑ x ∈ Finset.range x, |μ.real (A₁ ∩ T^[x] ⁻¹' B₁) - μ.real A₁ * μ.real B₁|)
      · exact fun _ ↦ abs_nonneg _
      · intro n
        simp only [comp_apply, abs_mul, abs_inv, Nat.abs_cast]
        refine mul_le_mul_of_nonneg_left ?_ <|inv_nonneg_of_nonneg <| Nat.cast_nonneg' n
        calc
        _ ≤ ∑ x ∈ Finset.range n, |(μ.real (A₁ ∩ T^[x] ⁻¹' B₁) - μ.real A₁ * μ.real B₁) *
          ν.real (A₂ ∩ S^[x] ⁻¹' B₂)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro m _
          rw [abs_mul]
          apply mul_le_of_le_one_right (abs_nonneg _)
          rw [abs_of_nonneg measureReal_nonneg]
          exact measureReal_le_one
      · simp only [Set.preimage_iterate_eq]
        exact h hA₁ hB₁
  · exact hA
  · exact hB

--#min_imports
