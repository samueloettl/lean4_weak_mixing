import Mathlib
import WeakMixing.OnAverageIndependent

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

lemma Measure.prod_eq_zero_left {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set α} (s_ae_empty : μ s = 0) :
    μ.prod ν (s ×ˢ Set.univ) = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
  _ ≤ _ := Measure.prod_prod_le _ _
  _ = _ := by simp [s_ae_empty]

lemma Measure.prod_eq_zero_right {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set β} (s_ae_empty : ν s = 0) :
    μ.prod ν (Set.univ ×ˢ s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
  _ ≤ _ := Measure.prod_prod_le _ _
  _ = _ := by simp [s_ae_empty]

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

lemma memLp_prod_of_p_ne_top {α : Type*} {β : Type*} {mα : MeasurableSpace α}
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
  exact memLp_prod_of_p_ne_top hf hg

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

lemma ENNReal.pow_eq_pow_iff_eq {a b : ENNReal} {p : ℝ} (hp : p ≠ 0) : a ^ p = b ^ p ↔ a = b := by
  constructor
  · intro h
    simpa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp] using congrArg (· ^ (p⁻¹)) h
  · intro h
    rw [h]

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
