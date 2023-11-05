import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.VectorMeasure

import ForML.LpHoelder
import ForML.SchwartzLp

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace
open scoped BigOperators Real NNReal ENNReal

-- Plan is to define mapping from `L1` to `L1`,
-- then show continuous,
-- then transfer to `𝓢(E, F)` using `ContinuousLinearMap.comp`.

namespace SchwartzMap

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

section Lp

variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [CompleteSpace F]
variable [NontriviallyNormedField 𝕜]  -- Required by `MeasureTheory.integral_smul`.
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- TODO: Define using `g : Lp (α := E) 𝕜 p` or just `g : E → 𝕜`?
noncomputable def integral_Lp_smul {p : ENNReal}
    (g : Lp (α := E) 𝕜 p) (φ : 𝓢(E, F)) : F :=
  ∫ (x : E), g x • φ x

lemma integral_Lp_smul_def {p : ENNReal} {g : Lp (α := E) 𝕜 p} {φ : 𝓢(E, F)} :
    integral_Lp_smul g φ = ∫ (x : E), g x • φ x := by rfl

-- TODO: Define these as bilinear CLM? Although depends on topology of `g`?
lemma integral_Lp_smul_add {p : ENNReal} (hp : 1 ≤ p)
    (g : Lp (α := E) 𝕜 p) (φ θ : 𝓢(E, F)) :
    integral_Lp_smul g (φ + θ) = integral_Lp_smul g φ + integral_Lp_smul g θ := by
  simp [integral_Lp_smul]
  have hpq := ENNReal.conjugate_conjugateExponent hp
  generalize p.conjugateExponent = q at hpq
  rw [integral_add]
  . exact integrable_Lp_smul_Lq hpq (Lp.memℒp g) (φ.memℒp q)
  . exact integrable_Lp_smul_Lq hpq (Lp.memℒp g) (θ.memℒp q)

-- Note: Doesn't require `1 ≤ p`?
lemma integral_Lp_smul_smul {p : ENNReal}
    (g : Lp (α := E) 𝕜 p) (c : 𝕜) (φ : 𝓢(E, F)) :
    integral_Lp_smul g (c • φ) = c • integral_Lp_smul g φ := by
  simp [integral_Lp_smul]
  simp_rw [smul_comm _ c]
  rw [integral_smul]

/-- `L1.integral` of `L1_of_Lp_smul_Lq _ _ (SchwartzMap.toLp φ _)` as an integral. -/
lemma L1_integral_Lp_smul_Lq_eq_integral {p q : ENNReal} (hpq : p⁻¹ + q⁻¹ = 1) {g : Lp (α := E) 𝕜 p} {φ : 𝓢(E, F)} :
    L1.integral (L1_of_Lp_smul_Lq hpq g (φ.toLp q)) = ∫ (x : E), g x • φ x := by
  rw [L1.integral_eq_integral]
  rw [integral_congr_ae (coeFn_L1_of_Lp_smul_Lq hpq)]
  refine integral_congr_ae ?_
  simp
  refine Filter.EventuallyEq.smul (by rfl) ?_
  exact SchwartzMap.coeFn_toLp _


-- Want to define `φ ↦ ∫ x, f x • φ x` as a CLM `𝓢(E, F) →L[𝕜] F` where `f : Lp 𝕜 p`.
-- Two options for how to do this...
--
-- 1. Define `g ↦ f • g` as a CLM `Lp_smul_CLM g : Lp F q →L[𝕜] Lp F 1`,
-- then use `integralCLM ∘ Lp_smul_CLM g ∘ SchwartzMap.toLp_CLM`.
-- TODO: Implement `SchwartzMap.toLp_CLM` rather than `SchwartzMap.toL1_CLM`.
--
-- 2. Define `φ ↦ f ∘ φ` as a CLM `SchwartzMap.Lp_smul_CLM g : 𝓢(E, F) →L[𝕜] 𝓢(E, F)`,
-- then use `integralCLM ∘ SchwartzMap.toL1_CLM ∘ SchwartzMap.Lp_smul_CLM g`.
-- This requires that `g • φ` is a Schwartz map...
-- Which kind of functions
--
-- Option 1 is more broadly useful (for `Lp` rather than just `SchwartzMap`).
-- Option 2 is specific to `SchwartzMap`, but this may be advantageous.
-- For example, we can easily go from `SchwartzMap` to `Lp` but not vice versa.
-- Perhaps this could be remedied showing that `SchwartzMap` is dense in `Lp`?

-- Actually, multiplication by Lp is not general enough!
-- For example, polynomials are tempered distributions, but they are not in Lp for any p.
-- Instead consider multiplication by a function that `HasTemperateGrowth`.
-- Note that this is not general enough to capture all tempered distributions.
-- For example, `x ↦ sign x` or `x ↦ max 0 x`.

-- TODO: Eventually define as bilinear CLM `Lp 𝕜 p →L[𝕜] 𝓢(E, F) →L[𝕜] F`?
-- Check type classes.
#check fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => Lp (α := E) 𝕜 p →L[𝕜] 𝓢(E, F) →L[𝕜] F

-- Can we follow `SchwartzMap.evalCLM` and use `SchwartzMap E (E →L[ℝ] F)`?
-- Maybe it's better to propose notation `E →𝓢 F` and `E →ℒ[p] 𝕜`?
-- We have a function `smul g φ x : F`. Rewrite as `smul x g φ`?
-- This might have type... `SchwartzMap E (Lp {E} 𝕜 p →L[𝕜] F)`?
-- Check type classes.
-- #check fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => SchwartzMap E (Lp (α := E) 𝕜 p →L[𝕜] F)
-- This would require `NormedSpace ℝ (Lp {E} 𝕜 p →L[𝕜] F)`.
-- That is, linear functionals on `Lp` as a `NormedSpace`? What's missing? `SMul ℝ` etc.
-- Although, if we *can* this, can we still obtain the *integral* of `f • φ` as a CLM?

end Lp


section HasTemperateGrowth

variable [NormedField 𝕜]  -- Don't need `NontriviallyNormedField 𝕜`.
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Used to define `hasTemperateGrowth_smul_CLM`. -/
lemma exists_hasTemperateGrowth_smul_bound {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(E, F)) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x • f x) x‖ ≤
      C * s.sup (schwartzSeminormFamily 𝕜 E F) f := by
  rcases hg with ⟨hg_smooth, hg_bound⟩

  -- We need to show
  -- `∃ s C, ∀ f x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g • f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 E F) f`,
  -- for which it is sufficient to show
  -- `∃ s C, ∀ f x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (g • f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 E F) f`.
  -- In particular, we need to find `s, C` that hold for all `i`.

  -- From `one_add_le_sup_seminorm_apply`, with `k_f ≤ m.1` and `i ≤ m.2`, we have
  -- (1) `∀ f x, (1 + ‖x‖) ^ k_f * ‖iteratedFDeriv ℝ i f x‖ ≤ 2 ^ m.1 * (Finset.Iic m).sup (schwartzSeminormFamily 𝕜 E F) f`.
  -- From `HasTemperateGrowth g`, we have
  -- (2) `∀ n, ∃ k C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C * (1 + ‖x‖) ^ k`.
  -- From `norm_iteratedFDeriv_smul_le`, we have
  -- (3) `‖iteratedFDeriv ℝ n (f • g) x‖ ≤ ∑ i in Finset.range (n + 1), n.choose i * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖`.

  -- From (2), we can find `k_g, C_g` such that `‖iteratedFDeriv ℝ i g x‖ ≤ C_g * (1 + ‖x‖) ^ k_g` for all `i ≤ n`.
  -- We can then combine
  -- `(1 + ‖x‖) ^ k_f * ‖iteratedFDeriv ℝ i f x‖ ≤ 2 ^ m.1 * (Finset.Iic m).sup (schwartzSeminormFamily 𝕜 E F) f`
  -- `‖iteratedFDeriv ℝ (n - i) g x‖ ≤ C_g * (1 + ‖x‖) ^ k_g`
  -- `∑ i in Finset.range (n + 1), n.choose i = 2 ^ n`
  -- to obtain
  -- `2 ^ n * (1 + ‖x‖) ^ k_f * ‖iteratedFDeriv ℝ n f x‖`
  --   `≤ 2 ^ m.1 * C_g * (1 + ‖x‖) ^ k_g * (Finset.Iic m).sup (schwartzSeminormFamily 𝕜 E F) f`.
  -- We need `k_f - k_g ≥ k` to obtain an upper bound on `(1 + ‖x‖) ^ k_f * ...`.
  -- Therefore set `k_f = k + k_g`.
  -- For `m`, we require `m.1 ≥ k_f` and `m.2 ≥ n`.
  -- We could either set `m.1 = max k_f n` (`= max (k + k_g) n`) to have `2 ^ n ≤ 2 ^ m.1`,
  -- or just incorporate the `2 ^ n` factor into `C`.
  -- Therefore we set `s = Finset.Iic (k + k_g, max n k)` and `C = 2 ^ m.1 * C_g`.

  -- Take maximum `k` and maximum `C` to obtain bound on derivatives of `g` for all `i`.
  have (m) : ∃ k C, 0 ≤ C ∧ ∀ i ∈ Finset.range m, ∀ (x : E), ‖iteratedFDeriv ℝ i g x‖ ≤ C * (1 + ‖x‖) ^ k
  . induction m with
    | zero => simp; use 0
    | succ m h_ind =>
      specialize hg_bound m
      rcases hg_bound with ⟨k_m, C_m, hC_m⟩
      rcases h_ind with ⟨k_i, C_i, ⟨hC_i_nonneg, hC_i⟩⟩
      refine ⟨max k_i k_m, max C_i C_m, ?_⟩
      refine And.intro (le_trans hC_i_nonneg (by simp)) ?_
      intro i hi x
      simp [Nat.lt_succ] at hi
      simp at hC_i
      cases lt_or_eq_of_le hi with
      | inl hi =>
        specialize hC_i i hi x
        refine le_trans hC_i ?_
        refine mul_le_mul ?_ (pow_le_pow ?_ ?_) ?_ (le_trans hC_i_nonneg ?_) <;> simp
      | inr hi =>
        rw [hi]
        specialize hC_m x
        refine le_trans hC_m ?_
        refine mul_le_mul ?_ (pow_le_pow ?_ ?_) ?_ (le_trans hC_i_nonneg ?_) <;> simp
  specialize this (n + 1)
  rcases this with ⟨k_g, C_g, ⟨hC_g_nonneg, hC_g⟩⟩

  use Finset.Iic (k + k_g, n)
  use 2 ^ (k + k_g) * 2 ^ n * C_g
  norm_num
  simp [hC_g_nonneg]
  intro f x
  refine le_trans (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_smul_le hg_smooth (f.smooth ⊤) x (le_top : (n : ℕ∞) ≤ ⊤))
    (by simp : 0 ≤ ‖x‖ ^ k)) ?_

  -- Move `‖x‖ ^ k` inside sum and bound each summand.
  rw [Finset.mul_sum]
  suffices : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * (n.choose i * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
      2 ^ (k + k_g) * n.choose i * C_g * (Finset.Iic (k + k_g, n)).sup (schwartzSeminormFamily 𝕜 E F) f
  . refine le_trans (Finset.sum_le_sum this) ?_
    clear this
    simp [← Finset.sum_mul, ← Finset.mul_sum]
    norm_cast
    rw [Nat.sum_range_choose]

  intro i hi
  simp [Nat.lt_succ] at hi hC_g
  -- Eliminate `choose` term.
  rw [mul_comm (‖x‖ ^ k)]
  rw [mul_comm _ (n.choose i : ℝ)]
  simp [mul_assoc, Nat.choose_pos hi]
  -- Replace `‖x‖` with `1 + ‖x‖`.
  simp [← mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_left (?_ : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k) ?_) ?_
  . refine pow_le_pow_of_le_left ?_ ?_ k
    . exact norm_nonneg x
    . exact le_add_of_nonneg_left zero_le_one
  . refine mul_nonneg ?_ ?_ <;> exact norm_nonneg _
  -- Bound on `g`.
  simp [mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_right (hC_g i hi x) ?_) ?_
  . exact mul_nonneg (norm_nonneg _) (by simp)
  -- Eliminate `C_g`.
  simp [← mul_assoc]
  rw [mul_comm _ C_g]
  simp [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC_g_nonneg
  -- Merge terms.
  rw [mul_comm _ (_ ^ k)]
  simp [← mul_assoc]
  rw [← pow_add]
  rw [add_comm k_g k]
  -- Bound on `f`.
  have : (1 + ‖x‖) ^ (k + k_g) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ _ :=
    one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (k + k_g, n)) ?_ ?_ f x <;> simp
  simpa using this


section Def  -- Make 𝕜 explicit.
variable (𝕜)

-- TODO: Possible/useful to generalize to `→SL[σ]` with `𝕜` and `𝕜'`?
def hasTemperateGrowth_smul_CLM {g : E → ℝ} (hg : Function.HasTemperateGrowth g) :
    𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  mkCLM (fun φ x => (g • φ) x)
    (fun φ θ x => by simp)
    (fun a φ x => smul_comm (g x) a (φ x))
    (fun φ => ContDiff.smul hg.1 (φ.smooth ⊤))
    (fun m => exists_hasTemperateGrowth_smul_bound hg m.1 m.2)

end Def

lemma hasTemperateGrowth_smul_CLM_apply
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) {φ : 𝓢(E, F)} {x : E} :
    hasTemperateGrowth_smul_CLM 𝕜 hg φ x = g x • φ x := rfl

end HasTemperateGrowth

section Integral

variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜)

noncomputable def integral_hasTemperateGrowth_smul_CLM [CompleteSpace F]
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) : 𝓢(E, F) →L[𝕜] F :=
  ContinuousLinearMap.comp (integralCLM 𝕜) (hasTemperateGrowth_smul_CLM 𝕜 hg)

end Integral

end SchwartzMap


section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Function.hasTemperateGrowth_const {c : F} : Function.HasTemperateGrowth (fun (_ : E) => c) := by
  refine ⟨contDiff_const, ?_⟩
  intro n
  cases n with
  | zero => refine ⟨0, ‖c‖, ?_⟩; simp
  | succ n => refine ⟨0, 0, ?_⟩; simp [iteratedFDeriv_const_of_ne, Nat.succ_ne_zero]

end Const


-- TODO: Move to `LpHoelder`.
-- Easier to keep it here for planning; avoids need to rebuild dependency.
namespace Lp

variable {E : Type*} [MeasurableSpace E]
variable {μ : Measure E}

variable {𝕜 : Type*} [NormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F]
-- variable [SMulZeroClass 𝕜 F] [BoundedSMul 𝕜 F]

variable {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
variable {f : Lp 𝕜 p μ}

/-- Defines `g ↦ ∫ x, f x • g x` with `f : Lp` and `g : Lq` as a CLM.

TODO: Define as a bilinear CLM?
-/
noncomputable def Lp_smul_CLM {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp 𝕜 p μ) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ where
  toFun :=

    sorry
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

end Lp


-- -- Plan is to define mapping from `L1` to `L1`,
-- -- then show continuous,
-- -- then transfer to `𝓢(E, F)` using `ContinuousLinearMap.comp`.
-- section L1

-- variable {α : Type*}
-- variable {E : Type*} [NormedAddCommGroup E]
-- variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

-- lemma memL1_memℒp_top_smul [MeasurableSpace α] {g : α → 𝕜} {μ : Measure α}
--     (hg : Memℒp g ⊤ μ) (f : Lp E 1 μ) :
--     Memℒp (g • (f : α → E)) 1 μ := by
--   refine And.intro ?_ ?_
--   . exact AEStronglyMeasurable.smul hg.aestronglyMeasurable (Lp.aestronglyMeasurable f)
--   . have : snorm (g • (f : α → E)) 1 μ ≤ snorm g ∞ μ * snorm f 1 μ
--     . refine snorm_smul_le_mul_snorm ?_ ?_ (by norm_num)
--       . exact Lp.aestronglyMeasurable f
--       . exact hg.aestronglyMeasurable
--     refine lt_of_le_of_lt this ?_
--     refine ENNReal.mul_lt_top ?_ ?_
--     . exact Memℒp.snorm_ne_top hg
--     . exact Lp.snorm_ne_top f

-- lemma memL1_aestronglyMeasurable_smul_of_ae_bound {g : α → 𝕜} [MeasurableSpace α]
--     {μ : Measure α}
--     (hg_meas : AEStronglyMeasurable g μ)
--     {C : ℝ} (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
--     (f : Lp E 1 μ) :
--     Memℒp (g • (f : α → E)) 1 μ := by
--   refine memL1_memℒp_top_smul ?_ f
--   exact memℒp_top_of_bound hg_meas C hg_bound

-- lemma memL1_continuous_smul_of_bound {g : α → 𝕜} [MeasurableSpace α]
--     [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopologyEither α 𝕜]
--     (hg_cont : Continuous g)
--     {C : ℝ} (hg_bound : ∀ x, ‖g x‖ ≤ C)
--     {μ : Measure α}
--     (f : Lp E 1 μ) :
--     Memℒp (g • (f : α → E)) 1 μ :=
--   memL1_aestronglyMeasurable_smul_of_ae_bound
--     hg_cont.aestronglyMeasurable (ae_of_all μ hg_bound) f

-- -- Can show that function is ae `< ∞`, but not `≤ C`.
-- lemma Memℒp_nnreal_ae_lt_top [MeasurableSpace α] {p : NNReal} (hp : p ≠ 0) {f : α → E}
--     (μ : Measure α := by volume_tac)
--     (hf : Memℒp f p μ) :
--     ∀ᵐ x ∂μ, (‖f x‖₊ : ENNReal) < ⊤ := by
--   suffices : ∀ᵐ x ∂μ, (‖f x‖₊ ^ (p : ℝ) : ENNReal) < ⊤
--   . exact Filter.Eventually.congr this (by simp)
--   refine ae_lt_top' ?_ ?_
--   . refine AEMeasurable.coe_nnreal_ennreal (AEMeasurable.pow_const ?_ _)
--     exact hf.aestronglyMeasurable.nnnorm.aemeasurable
--   rw [← lt_top_iff_ne_top]
--   rcases hf with ⟨_, hf⟩
--   rw [snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top] at hf
--   rotate_left
--   . norm_cast
--   . simp
--   simp at hf
--   simp_rw [ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg p)] at hf
--   exact hf

-- -- TODO: Are there conditions under which we can obtain `Lp _ ∞` from `Lp _ p`?
-- -- Would it help to assume `continuous` or `volume`?
-- -- Mainly need to show that function doesn't go to infinity on a set of positive measure?
-- lemma memℒp_top_of_memℒp_volume [MeasureSpace α] {p : ENNReal} {g : α → 𝕜}
--     (hg : Memℒp g p) (hp : 1 ≤ p) : Memℒp g ⊤ := by
--   cases p with
--   | none => exact hg
--   | some p =>
--     simp at hg hp
--     have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
--     rcases hg with ⟨hg_meas, hg_bound⟩
--     refine And.intro hg_meas ?_
--     simp
--     simp [snorm, hp_pos.ne', snorm'] at hg_bound
--     suffices : ∃ C, ∀ᵐ (x : α) ∂volume, ‖g x‖ ≤ C
--     . rcases this with ⟨C, hC⟩
--       exact snormEssSup_lt_top_of_ae_bound hC
--     sorry

-- -- lemma memL1_integralAgainst_memℒp_nnreal [TopologicalSpace α] [MeasureSpace α]
-- --     {p : NNReal} (hp : 1 ≤ p)
-- --     {g : α → 𝕜} (hg : Memℒp g p)
-- --     (f : Lp E 1) :
-- --     Memℒp (g • (f : α → E)) 1 := by
-- --   -- suffices : ∃ C, ∀ᵐ (x : α) ∂volume, ‖g x‖ ≤ C
-- --   -- . rcases this with ⟨C, hC⟩
-- --   --   exact memL1_integralAgainst_bound volume hg.aestronglyMeasurable hC f
-- --   refine memL1_integralAgainstMemℒp_top ?_ f
-- --   exact memℒp_top_of_memℒp_volume hg (by norm_cast)

-- end L1


-- namespace SchwartzMap

-- variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
-- variable {E F : Type*}
-- variable [NormedAddCommGroup E] [NormedSpace ℝ E]
-- variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
-- variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
-- variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- -- Define specifically for `𝓢(E, F)` since Schwartz maps are in `Lp` for any `p`.
-- -- TODO: Possible to generalize to `L1` using equivalence to functions on `[0, 1]`?
-- lemma memL1_memℒp_smul {p : ENNReal} (hp : 1 ≤ p)
--     {g : E → 𝕜} (hg : Memℒp g p) (f : 𝓢(E, F)) :
--     Memℒp (g • (f : E → F)) 1 := by
--   refine And.intro ?_ ?_
--   . exact AEStronglyMeasurable.smul hg.aestronglyMeasurable f.continuous.aestronglyMeasurable
--   . -- 1/p + 1/q = 1; q = p / (p-1) = 1 / (1 - 1/p)
--     generalize hq : (1 - p⁻¹)⁻¹ = q
--     -- have hq' : 1 ≤ q
--     -- . simp [← hq]
--     have hpq : 1/1 = 1/p + 1/q
--     . simp [← hq, hp]
--     have : snorm (g • (f : E → F)) 1 volume ≤ snorm g p volume * snorm f q volume
--     . refine snorm_smul_le_mul_snorm ?_ ?_ hpq
--       . exact f.continuous.aestronglyMeasurable
--       . exact hg.aestronglyMeasurable
--     refine lt_of_le_of_lt this ?_
--     refine ENNReal.mul_lt_top ?_ ?_
--     . exact Memℒp.snorm_ne_top hg
--     . rw [← lt_top_iff_ne_top]
--       exact snorm_lt_top f


-- noncomputable def integralAgainstMemℒpLM
--     {p : ENNReal} (hp : 1 ≤ p) {g : E → 𝕜} (hg : Memℒp g p) :
--     𝓢(E, F) →ₗ[𝕜] F where
--   -- toFun φ := L1.integralCLM (Memℒp.toLp _ (memL1_memℒp_smul hp hg φ))
--   toFun φ := L1.integral (Memℒp.toLp _ (memL1_memℒp_smul hp hg φ))
--   map_add' φ φ' := by
--     simp
--     sorry
--   map_smul' d φ := by
--     simp
--     sorry

-- lemma integralAgainstMemℒpLM_apply {p : ENNReal} (hp : 1 ≤ p)
--     {g : E → 𝕜} (hg : Memℒp g p) (φ : 𝓢(E, F)) :
--     integralAgainstMemℒpLM hp hg φ = ∫ (x : E), g x • φ x := by
--   simp [integralAgainstMemℒpLM]
--   -- rw [← integral_eq]
--   -- simp [L1.integral_eq_integral]
--   -- simp [Memℒp.coeFn_toLp]
--   sorry


-- /- Helper for `integralAgainstContinuousCLM`. -/
-- noncomputable def integralAgainstContinuousLM [CompleteSpace F] {g : E → 𝕜}
--     (hg_meas : MeasureTheory.AEStronglyMeasurable g volume)
--     (hg_bdd : essSup (fun x => (‖g x‖₊ : ENNReal)) volume ≠ ⊤) :
--     𝓢(E, F) →ₗ[𝕜] F where
--   toFun φ := ∫ (x : E), g x • φ x
--   map_add' φ φ' := by
--     simp
--     rw [integral_add]
--     . refine Integrable.essSup_smul φ.integrable hg_meas hg_bdd
--     . refine Integrable.essSup_smul φ'.integrable hg_meas hg_bdd
--   map_smul' d φ := by
--     simp
--     rw [← integral_smul]
--     simp_rw [smul_comm d]

-- /- Integration against a continuous function as a CLM. -/
-- noncomputable def integralAgainstContinuousCLM [CompleteSpace F] (g : E → 𝕜)
--     (hg_meas : MeasureTheory.AEStronglyMeasurable g volume)
--     (hg_bdd : essSup (fun x => (‖g x‖₊ : ENNReal)) volume ≠ ⊤) :
--     𝓢(E, F) →L[𝕜] F where
--   toLinearMap := integralAgainstContinuousLM g hg_meas hg_bdd
--   cont := by
--     simp
--     sorry
--   -- cont := by
--   --   simp
--   --   refine Continuous.comp _ (toL1_CLM 𝕜)
--   --   refine Continuous.comp _ (Lp.continuous_inner_left _)
--   --   exact Continuous.comp _ (Continuous.prod_map Continuous.id Continuous.id)

-- /- Integration against a measure as a CLM. -/
-- noncomputable def integralAgainstMeasureLM [CompleteSpace F] (μ : Measure E) :
--     𝓢(E, F) →ₗ[𝕜] F where
--   toFun φ := ∫ (x : E), φ x ∂μ
--   map_add' φ φ' := by
--     simp
--     rw [integral_add]
--     . sorry
--     . sorry
--   map_smul' d φ := by
--     simp
--     rw [← integral_smul]
--   -- cont := by
--   --   simp
--   --   refine Continuous.comp _ (toL1_CLM 𝕜)
--   --   refine Continuous.comp _ (Lp.continuous_inner_left _)
--   --   exact Continuous.comp _ (Continuous.prod_map Continuous.id Continuous.id)

-- -- TODO: Define a CLM by integration with a vector measure.
-- -- noncomputable def integral_vectorMeasure_CLM [CompleteSpace F] (μ : VectorMeasure E 𝕜) :
-- --     𝓢(E, F) →L[𝕜] F where

-- end SchwartzMap
