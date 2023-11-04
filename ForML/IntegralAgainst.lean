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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
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

lemma coeFn_apply {f : 𝓢(E, F)} {x : E} : f x = f.toFun x := rfl

lemma coeFn {f : 𝓢(E, F)} : f = f.toFun := rfl


/-- The product of a Schwartz function and a function with polynomial-bounded derivatives as a Schwartz function.

Requires `g : E → ℝ` rather than `g : E → 𝕜` in order to use `ContDiff.smul`.
TODO: May be possible to generalize to `g : E → 𝕜'`?
-/
def hasTemperateGrowth_smul {g : E → ℝ} (hg : Function.HasTemperateGrowth g)
    (f : 𝓢(E, F)) : 𝓢(E, F) where
  toFun := g • (f : E → F)
  smooth' := ContDiff.smul hg.1 (f.smooth ⊤)
  decay' := by
    refine decay_of_decay₁ ?_
    intro k n
    -- Change goal using bound on norm_iteratedFDeriv_smul.
    have h_deriv (x : E) (n : ℕ) := norm_iteratedFDeriv_smul_le hg.1 (f.smooth ⊤) x (le_top : (n : ENat) ≤ ⊤)
    -- TODO: Should be possible to avoid writing out long proposition?
    -- refine Exists.imp (fun C h x => le_trans (mul_le_mul_of_nonneg_left (h_deriv x n) (by simp)) (h x)) ?_
    have (C) :
        (∀ (x : E), (1 + ‖x‖) ^ k * (∑ i in Finset.range (n + 1),
          n.choose i * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ C) →
        (∀ (x : E), (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (g • (f : E → F)) x‖ ≤ C)
    . intro h x
      refine le_trans ?_ (h x)
      exact mul_le_mul_of_nonneg_left (h_deriv x n) (by simp)
    refine Exists.imp this ?_
    clear this h_deriv
    -- If we have an upper bound for each summand, then we have an upper bound for the sum.
    -- Easier to define in abstract terms. Could extract as a lemma?
    have (q : ℕ → E → ℝ) (m : ℕ) :
        (∀ i ∈ Finset.range m, ∃ C, ∀ x, q i x ≤ C) → (∃ C, ∀ x, ∑ i in Finset.range m, q i x ≤ C)
    . intro h
      have := Finset.sum_induction q (fun (qi : E → ℝ) => ∃ C, ∀ x, qi x ≤ C) ?_ ?_ h
      rotate_left
      . simp
        intro qi qi' C hi C' hi'
        use C + C'
        intro x
        exact add_le_add (hi x) (hi' x)
      . simp
        use 0
      simp at this
      exact this
    -- Move the multiplier inside the summation and then apply.
    simp [Finset.mul_sum]
    refine this _ _ ?_
    clear this
    intro i _
    have hg_temp := hg.2
    have hf_decay₁ := f.decay₁
    specialize hg_temp i
    rcases hg_temp with ⟨k_g, ⟨C_g, hC_g⟩⟩
    -- Want to choose `k_f` such that we can use
    -- `(1 + ‖x‖) ^ k_f * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ C_f`
    -- with the existing condition
    -- `‖iteratedFDeriv ℝ i g x‖ ≤ C_g * (1 + ‖x‖) ^ k_g`
    -- to obtain
    -- `(1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ C_g * C_f`.
    -- The two conditions together give us
    -- `(1 + ‖x‖) ^ k_f * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ C_g * C_f * (1 + ‖x‖) ^ k_g`
    -- `(1 + ‖x‖) ^ k_f * (1 + ‖x‖)⁻¹ ^ k_g * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ C_g * C_f`
    -- Therefore, use `k_f = k + k_g`.
    specialize hf_decay₁ (k + k_g) (n - i)
    rcases hf_decay₁ with ⟨C_f, hC_f⟩
    use n.choose i * C_g * C_f
    intro x
    specialize hC_g x
    specialize hC_f x
    simp [pow_add] at hC_f
    -- Eliminate the `choose` term.
    simp [← mul_assoc]
    rw [mul_comm _ (Nat.choose _ _ : ℝ)]
    simp [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    simp [← mul_assoc]
    -- Take product of two conditions, then just re-arrange.
    -- Eliminate the `(1 + ‖x‖) ^ k_g` term.
    rw [mul_comm] at hC_g
    rw [mul_comm (_ ^ _) (_ ^ _)] at hC_f
    have := mul_le_mul hC_g hC_f ?_ ?_
    rotate_left
    . refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp
    . exact le_trans (by simp) hC_g
    rw [mul_comm] at this
    simp [mul_assoc] at this
    rw [mul_comm ‖_‖ ‖_‖] at this
    simp [← mul_assoc] at this
    exact this


lemma hasTemperateGrowth_smul_apply {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (f : 𝓢(E, F)) :
    hasTemperateGrowth_smul hg f x = g x • f x := rfl

lemma coeFn_hasTemperateGrowth_smul {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (f : 𝓢(E, F)) :
    hasTemperateGrowth_smul hg f = fun x => g x • f x := rfl

lemma hasTemperateGrowth_smul_add {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (φ θ : 𝓢(E, F)) :
    hasTemperateGrowth_smul hg (φ + θ) = hasTemperateGrowth_smul hg φ + hasTemperateGrowth_smul hg θ := by
  ext x
  simp [hasTemperateGrowth_smul_apply]

lemma hasTemperateGrowth_smul_smul {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (c : 𝕜) (φ : 𝓢(E, F)) :
    hasTemperateGrowth_smul hg (c • φ) = c • hasTemperateGrowth_smul hg φ := by
  ext x
  simp [hasTemperateGrowth_smul_apply]
  rw [smul_comm]


-- TODO: Could it be easier to prove `cont` directly, rather than use `mkCLM`?

-- /-- Bound the seminorm of `g • f` by the seminorm of `f` for `mkCLM`. -/
-- lemma hasTemperateGrowth_smul_bound_le {g : E → ℝ} (hg : Function.HasTemperateGrowth g)
--     (k n : ℕ) (f : 𝓢(E, F)) (x : E) (C' : ℝ) :
--     ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x • f x) x‖ ≤
--       C' * (Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f := by
--   -- Already showed that `g • f` is a Schwartz function.
--   -- Do we have the required bound from that?
--   simp_rw [← coeFn_hasTemperateGrowth_smul hg]
--   have hgf := (hasTemperateGrowth_smul hg f).decay k n
--   rcases hgf with ⟨C_gf, hC_gf, hgf⟩
--   specialize hgf x
--   refine le_trans hgf ?_
--   have hf := f.decay k n
--   simp [schwartzSeminormFamily]
--   sorry


-- Not good enough for `mkCLM`; upper bound depends on `x`!
lemma hasTemperateGrowth_smul_bound' {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (k n : ℕ) :
    ∀ (f : 𝓢(E, F)) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x • f x) x‖ ≤
        (↑(2 ^ k : ℕ) * (∑ i in Finset.range (n + 1), (n.choose i) * ‖iteratedFDeriv ℝ i g x‖)) *
          (Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f := by
  intro f x
  -- Apply `norm_iteratedFDeriv_smul_le` to obtain sum.
  refine le_trans (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_smul_le hg.1 (f.smooth ⊤) x le_top)
    (pow_nonneg (norm_nonneg x) _)) ?_

  -- Move `‖x‖ ^ k` inside sum and bound each summand.
  rw [Finset.mul_sum]
  suffices : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i) * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
      ↑(2 ^ k : ℕ) * ((n.choose i) * ‖iteratedFDeriv ℝ i g x‖) * ((Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f)
  . refine le_trans (Finset.sum_le_sum this) ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]

  intro i hi
  -- Move common terms to the left.
  rw [mul_comm (‖x‖ ^ k)]
  rw [mul_assoc (↑(2 ^ k) : ℝ)]
  rw [mul_comm (↑(2 ^ k) : ℝ)]
  simp only [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  -- Now obtain bound for `f`.
  rw [mul_comm _ (‖x‖ ^ k)]
  rw [mul_comm _ (↑(2 ^ k) : ℝ)]
  simp_rw [schwartzSeminormFamily]
  -- Switch to `(1 + ‖x‖) ^ k`.
  refine le_trans (mul_le_mul_of_nonneg_right (?_ : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k) (norm_nonneg _)) ?_
  . refine pow_le_pow_of_le_left ?_ ?_ k
    . exact norm_nonneg x
    . exact le_add_of_nonneg_left zero_le_one
  -- Need to use pair.
  generalize hm : (k, n) = m
  have hk : k = m.1 := by rw [← hm]
  have hn : n = m.2 := by rw [← hm]
  rw [hk, hn]
  exact one_add_le_sup_seminorm_apply (Nat.le_refl m.1) (Nat.sub_le m.2 i) f x


lemma exists_hasTemperateGrowth_smul_bound {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(E, F)) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x • f x) x‖ ≤
      C * s.sup (schwartzSeminormFamily 𝕜 E F) f := by
  rcases hg with ⟨hg_smooth, hg_bound⟩

  -- Obtain upper bound that holds for all `0 ≤ i ≤ n`. Use maximum `k_g` and maximum `C_g`.
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

  -- Note: Could use `max k k_g` for tighter bound?
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
    one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (k + k_g, n)) ?_ ?_ f x
    <;> simp
  simp at this
  exact this


/-- Bound the seminorm of `g • f` by the seminorm of `f` for `mkCLM`. -/
lemma hasTemperateGrowth_smul_bound'' {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (k n : ℕ) {C : ℝ} :
    ∀ (f : 𝓢(E, F)) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x • f x) x‖ ≤
      (2 ^ k) * C * (Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f := by
  intro f x
  refine le_trans (mul_le_mul_of_nonneg_right (?_ : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k) (norm_nonneg _)) ?_
  . refine pow_le_pow_of_le_left ?_ ?_ k
    . exact norm_nonneg x
    . exact le_add_of_nonneg_left zero_le_one

  rw [← coeFn_hasTemperateGrowth_smul hg]
  have (k' n' : ℕ) (hk : k' ≤ k) (hn : n' ≤ n) :=
    one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (k, n)) hk hn (hasTemperateGrowth_smul hg f) x
  simp at this
  refine le_trans (this k n (by simp) (by simp)) ?_
  simp [mul_assoc]
  -- Is this useful? sup ≤ sup...
  -- Need to prove that seminorms of `g • f` are bounded by seminorms of `f`...
  sorry


/-- Bound the seminorm of `g • f` by the seminorm of `f` for `mkCLM`. -/
lemma exists_hasTemperateGrowth_smul_bound' {g : E → ℝ} (hg : Function.HasTemperateGrowth g) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(E, F)) (x : E),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g • (f : E → F)) x‖ ≤
          C * s.sup (schwartzSeminormFamily 𝕜 E F) f := by
  use Finset.Iic (k, n)
  -- use ↑(2 ^ k : ℕ) * (∑ i in Finset.range (n + 1), (n.choose i) * ‖iteratedFDeriv ℝ i g x‖)
  sorry


-- TODO: Possible/useful to generalize to `→SL[σ]` with `𝕜` and `𝕜'`?
def hasTemperateGrowth_smulCLM {g : E → ℝ} (hg : Function.HasTemperateGrowth g) :
    𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  mkCLM (fun φ x => (g • φ) x)
    (fun φ θ x => by simp)
    (fun a φ x => smul_comm (g x) a (φ x))
    (fun φ => ContDiff.smul hg.1 (φ.smooth ⊤))
    (fun m => exists_hasTemperateGrowth_smul_bound hg m.1 m.2)


-- TODO: Define CLMs for `Lp_smul` and `HasTemperateGrowth_smul`?

-- def smul_CLM {p : ENNReal} (hp : 1 ≤ p) {g : E → 𝕜} :
--     𝓢(E, F) →L[𝕜] 𝓢(E, F) where
--   toFun φ := fun x => g x • φ x
--   map_add' := integral_Lp_smul_add hp g
--   map_smul' := integral_Lp_smul_smul g
--   cont := by
--     refine Seminorm.cont_withSeminorms_normedSpace _ (schwartz_withSeminorms 𝕜 E F) _ ?_
--     simp [Seminorm.le_def]
--     conv => arg 1; intro s; arg 1; intro C; intro φ  -- Rename.
--     simp [NNReal.smul_def]
--     sorry


end SchwartzMap


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
