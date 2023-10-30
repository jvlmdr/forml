import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.VectorMeasure

import ForML.SchwartzLp

open MeasureTheory SchwartzSpace

open scoped Real NNReal ENNReal

-- Plan is to define mapping from `L1` to `L1`,
-- then show continuous,
-- then transfer to `𝓢(E, F)` using `ContinuousLinearMap.comp`.
section L1

variable {α : Type*}
variable {E : Type*} [NormedAddCommGroup E]
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

lemma memL1_memℒp_top_smul [MeasurableSpace α] {g : α → 𝕜} {μ : Measure α}
    (hg : Memℒp g ⊤ μ) (f : Lp E 1 μ) :
    Memℒp (g • (f : α → E)) 1 μ := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.smul hg.aestronglyMeasurable (Lp.aestronglyMeasurable f)
  . have : snorm (g • (f : α → E)) 1 μ ≤ snorm g ∞ μ * snorm f 1 μ
    . refine snorm_smul_le_mul_snorm ?_ ?_ (by norm_num)
      . exact Lp.aestronglyMeasurable f
      . exact hg.aestronglyMeasurable
    refine lt_of_le_of_lt this ?_
    refine ENNReal.mul_lt_top ?_ ?_
    . exact Memℒp.snorm_ne_top hg
    . exact Lp.snorm_ne_top f

lemma memL1_aestronglyMeasurable_smul_of_ae_bound {g : α → 𝕜} [MeasurableSpace α]
    {μ : Measure α}
    (hg_meas : AEStronglyMeasurable g μ)
    {C : ℝ} (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp E 1 μ) :
    Memℒp (g • (f : α → E)) 1 μ := by
  refine memL1_memℒp_top_smul ?_ f
  exact memℒp_top_of_bound hg_meas C hg_bound

lemma memL1_continuous_smul_of_bound {g : α → 𝕜} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopologyEither α 𝕜]
    (hg_cont : Continuous g)
    {C : ℝ} (hg_bound : ∀ x, ‖g x‖ ≤ C)
    {μ : Measure α}
    (f : Lp E 1 μ) :
    Memℒp (g • (f : α → E)) 1 μ :=
  memL1_aestronglyMeasurable_smul_of_ae_bound
    hg_cont.aestronglyMeasurable (ae_of_all μ hg_bound) f

-- Can show that function is ae `< ∞`, but not `≤ C`.
lemma Memℒp_nnreal_ae_lt_top [MeasurableSpace α] {p : NNReal} (hp : p ≠ 0) {f : α → E}
    (μ : Measure α := by volume_tac)
    (hf : Memℒp f p μ) :
    ∀ᵐ x ∂μ, (‖f x‖₊ : ENNReal) < ⊤ := by
  suffices : ∀ᵐ x ∂μ, (‖f x‖₊ ^ (p : ℝ) : ENNReal) < ⊤
  . exact Filter.Eventually.congr this (by simp)
  refine ae_lt_top' ?_ ?_
  . refine AEMeasurable.coe_nnreal_ennreal (AEMeasurable.pow_const ?_ _)
    exact hf.aestronglyMeasurable.nnnorm.aemeasurable
  rw [← lt_top_iff_ne_top]
  rcases hf with ⟨_, hf⟩
  rw [snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top] at hf
  rotate_left
  . norm_cast
  . simp
  simp at hf
  simp_rw [ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg p)] at hf
  exact hf

-- TODO: Are there conditions under which we can obtain `Lp _ ∞` from `Lp _ p`?
-- Would it help to assume `continuous` or `volume`?
-- Mainly need to show that function doesn't go to infinity on a set of positive measure?
lemma memℒp_top_of_memℒp_volume [MeasureSpace α] {p : ENNReal} {g : α → 𝕜}
    (hg : Memℒp g p) (hp : 1 ≤ p) : Memℒp g ⊤ := by
  cases p with
  | none => exact hg
  | some p =>
    simp at hg hp
    have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    rcases hg with ⟨hg_meas, hg_bound⟩
    refine And.intro hg_meas ?_
    simp
    simp [snorm, hp_pos.ne', snorm'] at hg_bound
    suffices : ∃ C, ∀ᵐ (x : α) ∂volume, ‖g x‖ ≤ C
    . rcases this with ⟨C, hC⟩
      exact snormEssSup_lt_top_of_ae_bound hC
    sorry

-- lemma memL1_integralAgainst_memℒp_nnreal [TopologicalSpace α] [MeasureSpace α]
--     {p : NNReal} (hp : 1 ≤ p)
--     {g : α → 𝕜} (hg : Memℒp g p)
--     (f : Lp E 1) :
--     Memℒp (g • (f : α → E)) 1 := by
--   -- suffices : ∃ C, ∀ᵐ (x : α) ∂volume, ‖g x‖ ≤ C
--   -- . rcases this with ⟨C, hC⟩
--   --   exact memL1_integralAgainst_bound volume hg.aestronglyMeasurable hC f
--   refine memL1_integralAgainstMemℒp_top ?_ f
--   exact memℒp_top_of_memℒp_volume hg (by norm_cast)

end L1


namespace SchwartzMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- Define specifically for `𝓢(E, F)` since Schwartz maps are in `Lp` for any `p`.
-- TODO: Possible to generalize to `L1` using equivalence to functions on `[0, 1]`?
lemma memL1_memℒp_smul {p : ENNReal} (hp : 1 ≤ p)
    {g : E → 𝕜} (hg : Memℒp g p) (f : 𝓢(E, F)) :
    Memℒp (g • (f : E → F)) 1 := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.smul hg.aestronglyMeasurable f.continuous.aestronglyMeasurable
  . -- 1/p + 1/q = 1; q = p / (p-1) = 1 / (1 - 1/p)
    generalize hq : (1 - p⁻¹)⁻¹ = q
    -- have hq' : 1 ≤ q
    -- . simp [← hq]
    have hpq : 1/1 = 1/p + 1/q
    . simp [← hq, hp]
    have : snorm (g • (f : E → F)) 1 volume ≤ snorm g p volume * snorm f q volume
    . refine snorm_smul_le_mul_snorm ?_ ?_ hpq
      . exact f.continuous.aestronglyMeasurable
      . exact hg.aestronglyMeasurable
    refine lt_of_le_of_lt this ?_
    refine ENNReal.mul_lt_top ?_ ?_
    . exact Memℒp.snorm_ne_top hg
    . rw [← lt_top_iff_ne_top]
      exact snorm_lt_top f


noncomputable def integralAgainstMemℒpLM
    {p : ENNReal} (hp : 1 ≤ p) {g : E → 𝕜} (hg : Memℒp g p) :
    𝓢(E, F) →ₗ[𝕜] F where
  -- toFun φ := L1.integralCLM (Memℒp.toLp _ (memL1_memℒp_smul hp hg φ))
  toFun φ := L1.integral (Memℒp.toLp _ (memL1_memℒp_smul hp hg φ))
  map_add' φ φ' := by
    simp
    sorry
  map_smul' d φ := by
    simp
    sorry

lemma integralAgainstMemℒpLM_apply {p : ENNReal} (hp : 1 ≤ p)
    {g : E → 𝕜} (hg : Memℒp g p) (φ : 𝓢(E, F)) :
    integralAgainstMemℒpLM hp hg φ = ∫ (x : E), g x • φ x := by
  simp [integralAgainstMemℒpLM]
  -- rw [← integral_eq]
  -- simp [L1.integral_eq_integral]
  -- simp [Memℒp.coeFn_toLp]
  sorry


/- Helper for `integralAgainstContinuousCLM`. -/
noncomputable def integralAgainstContinuousLM [CompleteSpace F] {g : E → 𝕜}
    (hg_meas : MeasureTheory.AEStronglyMeasurable g volume)
    (hg_bdd : essSup (fun x => (‖g x‖₊ : ENNReal)) volume ≠ ⊤) :
    𝓢(E, F) →ₗ[𝕜] F where
  toFun φ := ∫ (x : E), g x • φ x
  map_add' φ φ' := by
    simp
    rw [integral_add]
    . refine Integrable.essSup_smul φ.integrable hg_meas hg_bdd
    . refine Integrable.essSup_smul φ'.integrable hg_meas hg_bdd
  map_smul' d φ := by
    simp
    rw [← integral_smul]
    simp_rw [smul_comm d]

/- Integration against a continuous function as a CLM. -/
noncomputable def integralAgainstContinuousCLM [CompleteSpace F] (g : E → 𝕜)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g volume)
    (hg_bdd : essSup (fun x => (‖g x‖₊ : ENNReal)) volume ≠ ⊤) :
    𝓢(E, F) →L[𝕜] F where
  toLinearMap := integralAgainstContinuousLM g hg_meas hg_bdd
  cont := by
    simp
    sorry
  -- cont := by
  --   simp
  --   refine Continuous.comp _ (toL1_CLM 𝕜)
  --   refine Continuous.comp _ (Lp.continuous_inner_left _)
  --   exact Continuous.comp _ (Continuous.prod_map Continuous.id Continuous.id)

/- Integration against a measure as a CLM. -/
noncomputable def integralAgainstMeasureLM [CompleteSpace F] (μ : Measure E) :
    𝓢(E, F) →ₗ[𝕜] F where
  toFun φ := ∫ (x : E), φ x ∂μ
  map_add' φ φ' := by
    simp
    rw [integral_add]
    . sorry
    . sorry
  map_smul' d φ := by
    simp
    rw [← integral_smul]
  -- cont := by
  --   simp
  --   refine Continuous.comp _ (toL1_CLM 𝕜)
  --   refine Continuous.comp _ (Lp.continuous_inner_left _)
  --   exact Continuous.comp _ (Continuous.prod_map Continuous.id Continuous.id)

-- TODO: Define a CLM by integration with a vector measure.
-- noncomputable def integral_vectorMeasure_CLM [CompleteSpace F] (μ : VectorMeasure E 𝕜) :
--     𝓢(E, F) →L[𝕜] F where

end SchwartzMap
