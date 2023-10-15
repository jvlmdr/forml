import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Basic

open MeasureTheory Real

/- Second mean value theorem for integrals.

Follows: https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization
-/
lemma exists_mul_eq_intervalIntegral {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b))
    (hgnn : ∀ x, x ∈ Set.Icc a b → 0 ≤ g x)
    : ∃ c, c ∈ Set.Icc a b ∧ ∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x := by
  rw [← Set.uIcc_of_lt hab] at *
  have hm := @IsCompact.exists_isMinOn ℝ _ _ _ _ _ _ isCompact_uIcc Set.nonempty_uIcc _ hfc
  have hM := @IsCompact.exists_isMaxOn ℝ _ _ _ _ _ _ isCompact_uIcc Set.nonempty_uIcc _ hfc
  rcases hm with ⟨m, ⟨hm_mem, hm⟩⟩
  rcases hM with ⟨M, ⟨hM_mem, hM⟩⟩
  simp [IsMinOn, IsMinFilter] at hm
  simp [IsMaxOn, IsMaxFilter] at hM
  replace hm : ∫ x in a..b, g x * f m ≤ ∫ x in a..b, g x * f x
  . apply intervalIntegral.integral_mono_on (le_of_lt hab)
    . apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.mul hgc continuousOn_const
    . apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.mul hgc hfc
    rw [← Set.uIcc_of_lt hab]
    intro u hu
    exact mul_le_mul_of_nonneg_left (hm u hu) (hgnn u hu)
  replace hM : ∫ x in a..b, g x * f x ≤ ∫ x in a..b, g x * f M
  . apply intervalIntegral.integral_mono_on (le_of_lt hab)
    . apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.mul hgc hfc
    . apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.mul hgc continuousOn_const
    rw [← Set.uIcc_of_lt hab]
    intro u hu
    exact mul_le_mul_of_nonneg_left (hM u hu) (hgnn u hu)
  simp at hm
  simp at hM
  -- Introduce `z` to denote integral for brevity.
  generalize hz : ∫ (x : ℝ) in a..b, g x = z at *
  have h : 0 ≤ z
  . rw [← hz]
    apply intervalIntegral.integral_nonneg (le_of_lt hab)
    rw [← Set.uIcc_of_lt hab]
    exact hgnn
  cases eq_or_gt_of_le h with
  | inl h =>
    -- Cannot divide by integral; show g is ae zero.
    simp [h]
    apply And.intro
    . exists a; simp
    rw [← hz] at h
    rw [intervalIntegral.integral_of_le (le_of_lt hab)] at h
    rw [MeasureTheory.set_integral_eq_zero_iff_of_nonneg_ae] at h
    rotate_left
    . simp
      -- There is no `Filter.eventuallyLe_inf_principal_iff`.
      -- Took this from definition of `Filter.eventuallyEq_inf_principal_iff`.
      rw [Filter.EventuallyLE, Filter.eventually_inf_principal]
      apply Filter.eventually_of_forall
      intro x hx
      simp
      apply hgnn
      rw [Set.uIcc_of_lt hab]
      exact Set.mem_Icc_of_Ioc hx
    . rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      rw [← Set.uIcc_of_lt hab]
      exact ContinuousOn.integrableOn_uIcc hgc
    replace h := Filter.EventuallyEq.mul (ae_eq_refl f) h
    conv at h => rhs; simp
    rw [intervalIntegral.integral_of_le (le_of_lt hab)]
    simp at h
    rw [Filter.eventuallyEq_inf_principal_iff] at h
    rw [set_integral_congr_ae measurableSet_Ioc h]
    simp
  | inr h =>
    -- Divide both sides by integral of `g`.
    rw [mul_comm z, ← div_le_iff h] at hM
    rw [mul_comm z, ← le_div_iff h] at hm
    simp_rw [eq_comm]
    simp_rw [← eq_div_iff (ne_of_gt h)]
    -- Obtain the constant using the mean value theorem for continuous functions.
    have hmM := Set.uIcc_subset_uIcc hm_mem hM_mem
    have h_subset := @intermediate_value_uIcc ℝ _ _ _ _ ℝ _ _ _ m M f (ContinuousOn.mono hfc hmM)
    have h_mem := Set.mem_of_mem_of_subset (Set.mem_uIcc_of_le hm hM) h_subset
    simp at h_mem
    rcases h_mem with ⟨c, hc⟩
    exists c
    apply And.intro
    . exact Set.mem_of_mem_of_subset hc.left hmM
    . simp_rw [mul_comm] at hc
      exact hc.right

-- For easy rewrite.
lemma and_left_imp {p q r : Prop} : (p ∧ q → p ∧ r) ↔ (p → q → r) := by
  simp
  apply Iff.intro
  . intro h hp hq
    exact (h hp hq).right
  . intro h hp hq
    exact ⟨hp, h hp hq⟩

/- Mean value theorem as a single integral equal to zero. -/
lemma exists_mul_eq_intervalIntegral' {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b))
    (hgnn : ∀ x, x ∈ Set.Icc a b → 0 ≤ g x)
    : ∃ c, c ∈ Set.Icc a b ∧ ∫ x in a..b, (f x - f c) * g x = 0 := by
  rcases exists_mul_eq_intervalIntegral hab hfc hgc hgnn with ⟨c, hc⟩
  exists c
  revert hc
  rw [and_left_imp]
  intro _
  simp [sub_mul]
  rw [intervalIntegral.integral_sub]
  rotate_left
  . apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_lt hab]
    exact ContinuousOn.mul hfc hgc
  . apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_lt hab]
    exact ContinuousOn.mul continuousOn_const hgc
  intro h
  simp [h]


-- Unused.
lemma IsFiniteMeasure_withDensity_of_integrableOn {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {μ : Measure ℝ}
    (h_int : IntegrableOn f s μ) (h_nonneg : ∀ x, x ∈ s → 0 ≤ f x)
    : IsFiniteMeasure ((μ.restrict s).withDensity (fun x => ENNReal.ofReal (f x))) where
  measure_univ_lt_top := by
    simp
    rcases h_int with ⟨_, ⟨z, hz⟩⟩
    simp at hz
    rw [@set_lintegral_congr_fun _ _ _ _ (fun x => ‖f x‖₊) _  hs]
    . simp [hz]
    . refine Filter.eventually_of_forall ?_
      intro x hx
      rw [ennnorm_eq_ofReal_abs]
      rw [abs_eq_self.mpr (h_nonneg x hx)]

-- Handle trivial case where g is ae zero.
lemma setIntegral_mul_eq_zero_of_setIntegral_eq_zero {f g : ℝ → ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) {μ : Measure ℝ}
    (hg_int : IntegrableOn g s μ)
    (hg_nonneg : ∀ x, x ∈ s → 0 ≤ g x)
    (h : ∫ x in s, g x ∂μ = 0)
    : ∫ x in s, f x * g x ∂μ = 0 := by
  rw [MeasureTheory.set_integral_eq_zero_iff_of_nonneg_ae] at h
  rotate_left
  . -- There is no `Filter.eventuallyLe_inf_principal_iff`.
    -- Took this from definition of `Filter.eventuallyEq_inf_principal_iff`.
    simp [Filter.EventuallyLE]
    rw [ae_restrict_iff' hs]
    exact Filter.eventually_of_forall hg_nonneg
  . exact hg_int
  replace h := Filter.EventuallyEq.mul (ae_eq_refl f) h
  simp at h
  simp [integral_congr_ae h]

-- Unused.
lemma setIntegral_eq_setIntegral_norm_of_nonneg
    {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → ℝ} (hf : ∀ x, x ∈ s → 0 ≤ f x)
    {μ : Measure ℝ}
    : ∫ x in s, f x ∂μ = ∫ x in s, ‖f x‖ ∂μ := by
  rw [set_integral_congr hs]
  rw [Set.EqOn]
  intro x hx
  simp
  symm
  rw [abs_eq_self]
  exact hf x hx

-- Unused.
lemma toReal_eq_iff_of_pos {a : ENNReal} {z : ℝ} (hz : 0 < z) : ENNReal.toReal a = z ↔ a = ENNReal.ofReal z := by
  cases a with
  | none => simp; linarith
  | some a =>
    simp [ENNReal.ofReal]
    rw [← NNReal.coe_eq]
    rw [Real.coe_toNNReal _ hz.le]


-- TODO: Extract this part.
-- lemma existsBounds {f g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) {μ : Measure ℝ}
--     (hf : ContinuousOn f s)
--     (hg : IntegrableOn g s μ)
--     (hz : 0 < ∫⁻ x in s, ‖g x‖₊ ∂μ)
--     (h : IntegrableOn (fun x => f x * |g x|) s μ)
--     : (∃ m, m ∈ s ∧ f m ≤ ∫ x in s, f x * |g x| ∂μ) ∧
--       (∃ M, M ∈ s ∧ ∫ x in s, f x * |g x| ∂μ ≤ f M) := by  
--   sorry


-- Second mean value theorem for improper integral.
-- https://math.stackexchange.com/questions/3712287/mean-value-theorem-for-improper-integrals
theorem exists_mul_eq_setInterval {f g : ℝ → ℝ} {s : Set ℝ} {μ : Measure ℝ}
    (hs_ne : Set.Nonempty s) {hs_meas : MeasurableSet s} (hs_conn : IsPreconnected s) {hs_closed : IsClosed s}
    (h_int : IntegrableOn (fun x => f x * g x) s μ)
    (hf_cont : ContinuousOn f s)
    (hg_int : IntegrableOn g s μ)
    (hg_nonneg : ∀ x, x ∈ s → 0 ≤ g x)
    : ∃ c, c ∈ s ∧ ∫ x in s, f x * g x ∂μ = f c * ∫ x in s, g x ∂μ := by
  -- We will normalize g to obtain `IsProbabilityMeasure`.
  -- First deal with case where g is (ae) zero.

  -- Rewrite as lintegral using fact that `g` is non-negative.
  have hz_int : ∫ x in s, g x ∂μ = ENNReal.toReal (∫⁻ (x : ℝ) in s, ↑‖g x‖₊ ∂μ)
  . rw [← integral_norm_eq_lintegral_nnnorm hg_int.aestronglyMeasurable]
    rw [set_integral_congr hs_meas]
    simp [Set.EqOn]
    intro x hx
    symm
    rw [abs_eq_self]
    exact hg_nonneg x hx
  -- Obtain NNReal to represent integral (can coerce to Real, ENNReal).
  rw [ENNReal.toReal] at hz_int
  generalize hz_lint : ENNReal.toNNReal (∫⁻ (x : ℝ) in s, ↑‖g x‖₊ ∂μ) = z at hz_int
  symm at hz_lint
  -- Simplify the goal expression to use `z`.
  simp_rw [hz_int]

  -- Deal with case where z = 0.
  -- rcases z with ⟨z, hz⟩
  -- simp at hz_int
  cases eq_or_gt_of_le (zero_le z) with
  | inl hz_zero =>
    rw [hz_zero] at hz_int ⊢
    simp
    rw [setIntegral_mul_eq_zero_of_setIntegral_eq_zero hs_meas hg_int hg_nonneg hz_int]
    simp
    exact hs_ne
  | inr hz_pos =>
    -- Integral of g is nonzero. Normalize to obtain `IsProbabilityMeasure`.
    -- Could use `exists_le_integral` with subtype `{x // x ∈ s}`,
    -- or use `exists_not_mem_null_le_integral` with `Measure.restrict`.
    -- TODO: Extract this to a lemma? Will it generalize to `MeasurableSet s` and `IsPreconnected s`?
    generalize hq : μ.withDensity (fun x => ‖g x‖₊) = q
    -- Use ENNReal here for `Measure.restrict_smul`, which is a simp lemma.
    generalize hp : (z : ENNReal)⁻¹ • q = p
    have hp_one : IsProbabilityMeasure (p.restrict s)
    . constructor
      rw [← hp]
      simp
      rw [← hq]
      rw [MeasureTheory.withDensity_apply _ hs_meas]
      rw [← ENNReal.div_eq_inv_mul]
      rw [ENNReal.div_eq_one_iff]
      rotate_left
      . simp; apply hz_pos.ne'
      . simp
      rw [hz_lint]
      rw [ENNReal.coe_toNNReal]
      rcases hg_int with ⟨_, ⟨w, hw⟩⟩
      simp at hw
      simp [hw]
    -- Useful for showing equivalence.
    have hq_eqOn : Set.EqOn (fun x => ‖g x‖₊ • f x) (fun x => f x * g x) s
    . simp [NNReal.smul_def]
      rw [Set.EqOn]
      intro x hx
      rw [mul_comm, abs_of_nonneg (hg_nonneg x hx)]
    have hq_eq : ∫ x in s, f x ∂q = ∫ x in s, f x * g x ∂μ
    . rw [← hq]
      rw [set_integral_withDensity_eq_set_integral_smul₀ _ _ hs_meas]
      . exact set_integral_congr hs_meas hq_eqOn
      . exact AEMeasurable.nnnorm hg_int.aemeasurable
    have hq_int : Integrable f (q.restrict s)
    . rw [← hq]
      rw [restrict_withDensity hs_meas]
      rw [integrable_withDensity_iff_integrable_smul₀]
      . exact IntegrableOn.congr_fun h_int hq_eqOn.symm hs_meas
      . exact AEMeasurable.nnnorm hg_int.aemeasurable
    have hp_eq : ∫ x in s, f x ∂p = (z : ℝ)⁻¹ * ∫ x in s, f x * g x ∂μ
    . rw [← hp, ← hq_eq]
      simp
      apply Or.inl
      simp [ENNReal.toReal_inv]
    have hp_int : Integrable f (p.restrict s)
    . rw [← hp]
      simp
      apply Integrable.smul_measure hq_int
      simp; apply hz_pos.ne'
    -- 🎉

    have hp_meas_compl : p.restrict s sᶜ = 0
    . simp [Measure.restrict_apply (MeasurableSet.compl hs_meas)]
    have h_lb := @exists_not_mem_null_le_integral _ _ _ _ _ hp_one hp_int hp_meas_compl
    have h_ub := @exists_not_mem_null_integral_le _ _ _ _ _ hp_one hp_int hp_meas_compl
    simp_rw [Set.not_mem_compl_iff] at h_lb
    simp_rw [Set.not_mem_compl_iff] at h_ub
    -- 🎉

    rcases h_lb with ⟨m, ⟨hm_mem, hm⟩⟩
    rcases h_ub with ⟨M, ⟨hM_mem, hM⟩⟩
    rw [hp_eq] at hm
    rw [hp_eq] at hM
    -- Funny! I didn't think we would be able to obtain this.
    -- I was just looking for `k ≤ ... ≤ K` rather than `f m ≤ ... ≤ f M`.
    clear hp hp_one hp_eq hp_int hp_meas_compl p
    clear hq hq_eqOn hq_eq hq_int q

    -- Multiply by z⁻¹ on either side.
    have hz_ne_zero : (z : ℝ) ≠ 0 := ne_of_gt hz_pos
    conv =>
      arg 1; intro c; rhs
      rw [mul_comm]
      rw [← inv_mul_eq_iff_eq_mul₀ hz_ne_zero]

    cases eq_or_gt_of_le hm with
    | inl hm => exists m
    | inr hm_lt =>
      cases eq_or_lt_of_le hM with
      | inl hM_eq => exists M
      | inr hM_lt =>
        simp_rw [eq_comm]
        rw [← Set.mem_image]
        refine @Set.mem_of_mem_of_subset _ _ (Set.Ioo (f m) (f M)) _ ?_ ?_
        . exact And.intro hm_lt hM_lt
        . refine @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _
            hs_conn (nhdsWithin m s) (nhdsWithin M s) ?_ ?_ ?_ ?_ _
            hf_cont _ _ ?_ ?_
          . rw [← mem_closure_iff_nhdsWithin_neBot]
            rw [IsClosed.closure_eq hs_closed]
            exact hm_mem
          . rw [← mem_closure_iff_nhdsWithin_neBot]
            rw [IsClosed.closure_eq hs_closed]
            exact hM_mem
          . simp; exact self_mem_nhdsWithin
          . simp; exact self_mem_nhdsWithin
          . exact hf_cont m hm_mem
          . exact hf_cont M hM_mem
