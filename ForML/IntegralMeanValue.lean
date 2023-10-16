import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Basic

open MeasureTheory Real


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


/- Application of `exists_not_mem_null_le_integral` to obtain lower and upper bounds on set. -/
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
    {hs_ne : Set.Nonempty s} {hs_meas : MeasurableSet s} {hs_conn : IsPreconnected s} {hs_closed : IsClosed s}
    (hf_cont : ContinuousOn f s)
    (hg_int : IntegrableOn g s μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict s] g)
    (h_int : IntegrableOn (fun x => f x * g x) s μ)
    : ∃ c, c ∈ s ∧ ∫ x in s, f x * g x ∂μ = f c * ∫ x in s, g x ∂μ := by
  -- TODO: Is it possible to generalize to `s` that is open?
  -- Use `ContinuousOn f (closure s)` and `c ∈ closure s` instead?

  -- TODO: Generalize type to `f : ℝ → E` using `f x • g x`?

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


/- Utility for showing `0 ≤ᵐ[μ.restrict s] g` as required by most lemmas. -/
lemma Filter_eventuallyLe_restrict_of_forall_mem_imp {α E : Type*} [MeasurableSpace α] [LE E]
    {f g : α → E} {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    (h : ∀ x, x ∈ s → f x ≤ g x) : f ≤ᵐ[μ.restrict s] g := by
  rw [Filter.EventuallyLE]
  rw [ae_restrict_iff' hs]
  exact Filter.eventually_of_forall h


lemma exists_mul_eq_setInterval_Ici {a : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hf_cont : ContinuousOn f (Set.Ici a))
    (hg_int : IntegrableOn g (Set.Ici a) μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict (Set.Ici a)] g)
    (h_int : IntegrableOn (fun x => f x * g x) (Set.Ici a) μ)
    : ∃ c, c ∈ (Set.Ici a) ∧ ∫ x in Set.Ici a, f x * g x ∂μ = f c * ∫ x in Set.Ici a, g x ∂μ := by
  apply exists_mul_eq_setInterval hf_cont hg_int hg_nonneg h_int <;> try simp
  repeat simp [isClosed_Ici, isPreconnected_Ici]

lemma exists_mul_eq_setInterval_Iic {a : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hf_cont : ContinuousOn f (Set.Iic a))
    (hg_int : IntegrableOn g (Set.Iic a) μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict (Set.Iic a)] g)
    (h_int : IntegrableOn (fun x => f x * g x) (Set.Iic a) μ)
    : ∃ c, c ∈ (Set.Iic a) ∧ ∫ x in Set.Iic a, f x * g x ∂μ = f c * ∫ x in Set.Iic a, g x ∂μ := by
  apply exists_mul_eq_setInterval hf_cont hg_int hg_nonneg h_int <;> try simp
  repeat simp [isClosed_Iic, isPreconnected_Iic]

lemma exists_mul_eq_setInterval_Icc {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_int : IntegrableOn g (Set.Icc a b) μ)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict (Set.Icc a b)] g)
    (h_int : IntegrableOn (fun x => f x * g x) (Set.Icc a b) μ)
    : ∃ c, c ∈ (Set.Icc a b) ∧ ∫ x in Set.Icc a b, f x * g x ∂μ = f c * ∫ x in Set.Icc a b, g x ∂μ := by
  apply exists_mul_eq_setInterval hf_cont hg_int hg_nonneg h_int <;> try simp [hab]
  repeat simp [isClosed_Icc, isPreconnected_Icc, hab]


/- Obtain `IntegrableOn` from `ContinuousOn.mul`. -/
lemma exists_mul_eq_setInterval_Icc_of_continuousOn {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_nonneg : ∀ x, x ∈ Set.Icc a b → 0 ≤ g x)
    : ∃ c, c ∈ (Set.Icc a b) ∧ ∫ x in Set.Icc a b, f x * g x ∂μ = f c * ∫ x in Set.Icc a b, g x ∂μ := by
  apply exists_mul_eq_setInterval_Icc hab hf_cont ?_ ?_ ?_
  . exact ContinuousOn.integrableOn_Icc hg_cont
  . exact Filter_eventuallyLe_restrict_of_forall_mem_imp measurableSet_Icc hg_nonneg
  . exact ContinuousOn.integrableOn_Icc (ContinuousOn.mul hf_cont hg_cont)


-- TODO: Possible to remove `NoAtoms μ`?
-- Could remove assumption `IsClosed s` above to eliminate `integral_Icc_eq_integral_Ioc`?
lemma exists_mul_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    {μ : Measure ℝ} [NoAtoms μ] [IsLocallyFiniteMeasure μ]
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_int : IntervalIntegrable g μ a b)
    (hg_nonneg : 0 ≤ᵐ[μ.restrict (Set.Icc a b)] g)
    (h_int : IntervalIntegrable (fun x => f x * g x) μ a b)
    : ∃ c, c ∈ (Set.Icc a b) ∧ ∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral.integral_of_le hab]
  simp only [← integral_Icc_eq_integral_Ioc]
  refine exists_mul_eq_setInterval_Icc hab hf_cont ?_ hg_nonneg ?_
  . rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hg_int.left
  . rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact h_int.left

theorem exists_mul_eq_intervalIntegral_of_continuousOn {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    {μ : Measure ℝ} [NoAtoms μ] [IsLocallyFiniteMeasure μ]
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_nonneg : ∀ x, x ∈ Set.Icc a b → 0 ≤ g x)
    : ∃ c, c ∈ Set.Icc a b ∧ ∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral.integral_of_le hab]
  simp only [← integral_Icc_eq_integral_Ioc]
  exact exists_mul_eq_setInterval_Icc_of_continuousOn hab hf_cont hg_cont hg_nonneg
