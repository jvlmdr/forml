import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntervalIntegral
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
