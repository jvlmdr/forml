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
-- #check fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => Lp (α := E) 𝕜 p →L[𝕜] 𝓢(E, F) →L[𝕜] F

-- Can we follow `SchwartzMap.evalCLM` and use `SchwartzMap E (E →L[ℝ] F)`?
-- Maybe it's better to propose notation `E →𝓢 F` and `E →ℒ[p] 𝕜`?
-- We have a function `smul g φ x : F`. Rewrite as `smul x g φ`?
-- This might have type... `SchwartzMap E (Lp {E} 𝕜 p →L[𝕜] F)`?
-- Check type classes.
-- #check fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => SchwartzMap E (Lp (α := E) 𝕜 p →L[𝕜] F)
-- This would require `NormedSpace ℝ (Lp {E} 𝕜 p →L[𝕜] F)`.
-- That is, linear functionals on `Lp` as a `NormedSpace`? What's missing? `SMul ℝ` etc.
-- Although, if we *can* this, can we still obtain the *integral* of `f • φ` as a CLM?

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]


section Const  -- TODO: Move to a different file?

lemma Function.hasTemperateGrowth_const {c : F} : Function.HasTemperateGrowth (fun (_ : E) => c) := by
  refine ⟨contDiff_const, ?_⟩
  intro n
  cases n with
  | zero => refine ⟨0, ‖c‖, ?_⟩; simp
  | succ n => refine ⟨0, 0, ?_⟩; simp [iteratedFDeriv_const_of_ne, Nat.succ_ne_zero]

end Const


namespace SchwartzMap

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


namespace Distribution

variable [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable [CompleteSpace F]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]

section Def
variable (𝕜)
noncomputable def ofHasTemperateGrowth'
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) : 𝓢(E, F) →L[𝕜] F :=
  ContinuousLinearMap.comp (integralCLM' 𝕜) (hasTemperateGrowth_smul_CLM 𝕜 hg)
end Def

lemma ofHasTemperateGrowth'_apply
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) {φ : 𝓢(E, F)} :
    ofHasTemperateGrowth' 𝕜 hg φ = ∫ (x : E), g x • φ x := by
  rw [ofHasTemperateGrowth']
  rw [ContinuousLinearMap.comp_apply]
  rw [integralCLM'_apply]
  rfl

noncomputable def ofHasTemperateGrowth
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) : 𝓢(E, F) →L[ℝ] F :=
  ofHasTemperateGrowth' ℝ hg

lemma ofHasTemperateGrowth_apply
    {g : E → ℝ} (hg : Function.HasTemperateGrowth g) {φ : 𝓢(E, F)} :
    ofHasTemperateGrowth hg φ = ∫ (x : E), g x • φ x := by
  rw [ofHasTemperateGrowth]
  exact ofHasTemperateGrowth'_apply hg

-- TODO: Would this be better defined with a subtype?
lemma ofHasTemperateGrowth_const {c : ℝ} :
    ofHasTemperateGrowth
      (Function.hasTemperateGrowth_const :
        Function.HasTemperateGrowth (fun (_ : E) => c)) =
    SchwartzMap.Distribution.const E F c := by
  ext φ
  rw [ofHasTemperateGrowth_apply, const_apply]
  rw [integral_smul]

end Distribution  -- namespace
end SchwartzMap  -- namespace
