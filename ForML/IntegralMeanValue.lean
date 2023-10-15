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


-- For handling trivial case where g is ae zero.
lemma integral_mul_eq_zero_of_integral_eq_zero {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hg_int : Integrable g μ)
    (hg_nonneg : 0 ≤ᵐ[μ] g)
    (h : ∫ x, g x ∂μ = 0)
    : ∫ x, f x * g x ∂μ = 0 := by
  apply integral_eq_zero_of_ae
  rw [integral_eq_zero_iff_of_nonneg_ae hg_nonneg hg_int] at h
  apply Filter.Eventually.mp h
  simp
  apply Filter.eventually_of_forall
  intro x hx
  exact Or.inr hx


lemma existsBoundsOn_integral_measure {f : ℝ → ℝ} {q : Measure ℝ} {s : Set ℝ}
    (hs_meas : MeasurableSet s)
    (hq_fin : IsFiniteMeasure (q.restrict s))
    (hq_nonzero : q s ≠ 0)
    (h_int : IntegrableOn f s q)
    : (∃ m M, (m ∈ s ∧ M ∈ s) ∧ (∫ x in s, f x ∂q) / ENNReal.toReal (q s) ∈ Set.Icc (f m) (f M)) := by
  rw [ENNReal.toReal]
  generalize hz : ENNReal.toNNReal (q s) = z

  rcases hq_fin with ⟨hq_fin⟩
  simp at hq_fin
  have hz' : q s = z
  . rw [← hz]
    rw [ENNReal.coe_toNNReal hq_fin.ne]

  -- TODO: Avoid cases using assumption?
  cases eq_or_gt_of_le (zero_le z) with
  | inl hz_zero =>
    exfalso
    rw [hz_zero] at hz
    rw [ENNReal.toNNReal_eq_zero_iff] at hz
    cases hz with
    | inl _ => contradiction
    | inr h => exact ne_of_lt hq_fin h

  | inr hz_pos =>
    -- Use ENNReal here for `Measure.restrict_smul`, which is a simp lemma.
    generalize hp : (z : ENNReal)⁻¹ • q = p
    have hp_one : IsProbabilityMeasure (p.restrict s)
    . constructor
      rw [← hp]
      simp
      rw [hz']
      rw [← ENNReal.div_eq_inv_mul]
      rw [ENNReal.div_eq_one_iff]
      . simp; exact hz_pos.ne'
      . simp
    have hp_eq : ∫ x in s, f x ∂p = (∫ x in s, f x ∂q) / (z : ℝ)
    . rw [← hp]
      simp
      simp [ENNReal.toReal_inv]
      rw [inv_mul_eq_div]
    have hp_int : Integrable f (p.restrict s)
    . rw [← hp]
      simp  -- Invisible change (measure of `Integrable`).
      apply Integrable.smul_measure h_int
      simp
      apply hz_pos.ne'

    have hp_meas_compl : p.restrict s sᶜ = 0
    . rw [Measure.restrict_apply (MeasurableSet.compl hs_meas)]
      simp
    have h_lb := @exists_not_mem_null_le_integral _ _ _ _ _ hp_one hp_int hp_meas_compl
    have h_ub := @exists_not_mem_null_integral_le _ _ _ _ _ hp_one hp_int hp_meas_compl
    simp at h_lb
    simp at h_ub
    rcases h_lb with ⟨m, ⟨hm_mem, hm⟩⟩
    rcases h_ub with ⟨M, ⟨hM_mem, hM⟩⟩

    exists m
    exists M
    apply And.intro ⟨hm_mem, hM_mem⟩
    simp
    apply And.intro
    . rw [hp_eq] at hm
      exact hm
    . rw [hp_eq] at hM
      exact hM


lemma existsBoundsOn_integral_mul_nonneg {f g : ℝ → ℝ} {s : Set ℝ} {μ : Measure ℝ}
    (hs_meas : MeasurableSet s)
    (hg_int : IntegrableOn g s μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict s] g)
    (hg_nonzero : ∫ x in s, g x ∂μ ≠ 0)
    (h_int : IntegrableOn (fun x => f x * g x) s μ)
    : (∃ m M, (m ∈ s ∧ M ∈ s) ∧ (∫ x in s, f x * g x ∂μ) / (∫ x in s, g x ∂μ) ∈ Set.Icc (f m) (f M)) := by
  -- Useful to establish this for integral and integrable.
  have h_ae_eq : (fun x => f x * g x) =ᵐ[μ.restrict s] (fun x => ‖g x‖₊ • f x)
  . simp [NNReal.smul_def]
    apply Filter.Eventually.mp hg_nonneg
    simp
    apply Filter.eventually_of_forall
    intro x hx
    rw [mul_comm]
    rw [abs_eq_self.mpr hx]

  generalize hq : μ.withDensity (fun x => ‖g x‖₊) = q
  have hq_g : ENNReal.toReal (q s) = ∫ (x : ℝ) in s, g x ∂μ
  . simp [← hq, hs_meas]
    rw [← integral_norm_eq_lintegral_nnnorm hg_int.aestronglyMeasurable]
    apply integral_congr_ae
    apply Filter.Eventually.mp hg_nonneg
    simp
  have hq_fg : ∫ x in s, f x ∂q = ∫ (x : ℝ) in s, f x * g x ∂μ
  . rw [← hq]
    rw [set_integral_withDensity_eq_set_integral_smul₀ _ _ hs_meas]
    . exact integral_congr_ae h_ae_eq.symm
    . apply AEMeasurable.nnnorm
      exact hg_int.aemeasurable
  rw [← hq_g, ← hq_fg]

  refine existsBoundsOn_integral_measure hs_meas ?_ ?_ ?_
  . constructor
    simp [← hq, hs_meas]
    exact hg_int.right
  . intro h
    revert hq_g
    simp [h]
    rw [eq_comm]
    exact hg_nonzero
  . simp [← hq]
    rw [IntegrableOn]
    rw [restrict_withDensity hs_meas]
    rw [integrable_withDensity_iff_integrable_smul₀]
    . exact IntegrableOn.congr_fun_ae h_int h_ae_eq
    . exact AEMeasurable.nnnorm hg_int.aemeasurable


/- Second mean value theorem for improper integrals.

Follows: https://math.stackexchange.com/questions/3712287/mean-value-theorem-for-improper-integrals
-/
theorem exists_mul_eq_setInterval {f g : ℝ → ℝ} {s : Set ℝ} {μ : Measure ℝ}
    (hs_ne : Set.Nonempty s) {hs_meas : MeasurableSet s} (hs_conn : IsPreconnected s) {hs_closed : IsClosed s}
    (hf_cont : ContinuousOn f s)
    (hg_int : IntegrableOn g s μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict s] g)
    (h_int : IntegrableOn (fun x => f x * g x) s μ)
    : ∃ c, c ∈ s ∧ ∫ x in s, f x * g x ∂μ = f c * ∫ x in s, g x ∂μ := by

  -- TODO: Reduce duplication?
  have hz_integral : ∫ x in s, g x ∂μ = ENNReal.toReal (∫⁻ x in s, ↑‖g x‖₊ ∂μ)
  . rw [← integral_norm_eq_lintegral_nnnorm hg_int.aestronglyMeasurable]
    rw [integral_congr_ae]
    apply Filter.Eventually.mp hg_nonneg
    simp
    apply Filter.eventually_of_forall
    intro x hx
    symm
    rw [abs_eq_self]
    exact hx
  rw [ENNReal.toReal] at hz_integral
  generalize hz_lintegral : ENNReal.toNNReal (∫⁻ (x : ℝ) in s, ↑‖g x‖₊ ∂μ) = z
  rw [hz_lintegral] at hz_integral

  cases eq_or_gt_of_le (zero_le z) with
  | inl hz_zero =>
    simp [hz_zero] at hz_integral
    simp [hz_integral]
    refine And.intro hs_ne ?_
    exact integral_mul_eq_zero_of_integral_eq_zero hg_int hg_nonneg hz_integral
  | inr hz_pos =>
    have hmM := existsBoundsOn_integral_mul_nonneg hs_meas hg_int hg_nonneg ?_ h_int
    swap
    . intro h_zero
      simp [h_zero] at hz_integral
      rw [eq_comm] at hz_integral
      rw [NNReal.coe_eq_zero] at hz_integral
      simp [hz_integral] at hz_pos

    -- Use `z` for legibility.
    rw [hz_integral]
    rw [hz_integral] at hmM
    -- Divide by `z` in goal.
    have hz_ne_zero : (z : ℝ) ≠ 0 := ne_of_gt hz_pos
    conv => arg 1; intro c; rhs; rw [← div_eq_iff hz_ne_zero]

    rcases hmM with ⟨m, hmM⟩
    rcases hmM with ⟨M, hmM⟩
    rcases hmM with ⟨⟨hm_mem, hM_mem⟩, ⟨hm, hM⟩⟩

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
