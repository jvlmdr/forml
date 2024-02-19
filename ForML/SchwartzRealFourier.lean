import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

import ForML.IntegralAgainst
import ForML.SchwartzLp
import ForML.Trigonometric
import ForML.Util

open MeasureTheory SchwartzSpace FourierTransform
open Complex (I)
open scoped BigOperators Real

attribute [-simp] Matrix.zero_empty
attribute [-simp] ofAdd_neg

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace Real

/-- The Fourier integrand as a Schwartz function. -/
theorem fourierIntegrand_eq_hasTemperateGrowth_smul {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    Real.fourierChar[-(x * ξ)] • f x =
      (hasTemperateGrowth_smul ((Function.hasTemperateGrowth_mul_const ξ).neg.realFourierChar) f)
        x := by
  simp [hasTemperateGrowth_smul_apply]

-- TODO: Redundant due to `fourier_integrand_integrable`?
/-- As a Schwartz function, the Fourier integrand is integrable. -/
theorem integrable_fourierIntegrand (f : 𝓢(ℝ, F)) (ξ : ℝ) :
    Integrable (fun x ↦ Real.fourierChar[-(x * ξ)] • f x) := by
  -- The Fourier integrand is itself a Schwartz function, and hence integrable.
  simp [fourierIntegrand_eq_hasTemperateGrowth_smul]

theorem fourierIntegral_add {f g : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ f x + g x) ξ = 𝓕 (fun x ↦ f x) ξ + 𝓕 (fun x ↦ g x) ξ := by
  simpa [Real.fourierIntegral_def] using
    integral_add (integrable_fourierIntegrand f ξ) (integrable_fourierIntegrand g ξ)

theorem fourierIntegral_smul {c : ℝ} {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ c • f x) ξ = c • 𝓕 (fun x ↦ f x) ξ := by
  simpa [Real.fourierIntegral_def, smul_comm _ c] using integral_smul c _

theorem fourierIntegral_neg {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ -f x) ξ = -𝓕 (fun x ↦ f x) ξ := by
  simpa [Real.fourierIntegral_def] using integral_neg _

theorem fourierIntegral_sub {f g : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ f x - g x) ξ = 𝓕 (fun x ↦ f x) ξ - 𝓕 (fun x ↦ g x) ξ := by
  simpa [Real.fourierIntegral_def, smul_sub] using
    integral_sub (integrable_fourierIntegrand f ξ) (integrable_fourierIntegrand g ξ)

theorem fourierIntegral_sum {s : Finset ι} {f : ι → 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ ∑ i in s, f i x) ξ = ∑ i in s, 𝓕 (fun x ↦ f i x) ξ := by
  simpa [Real.fourierIntegral_def, Finset.smul_sum] using
    integral_finset_sum s fun i _ ↦ Real.integrable_fourierIntegrand (f i) ξ

-- theorem hasFDerivAt_integral_vectorFourierIntegrand' {f : 𝓢(ℝ, F)} {ξ : ℝ} :
--     HasFDerivAt (fun ξ ↦ 𝓕 f ξ)
--       (-((2 * π * I) • 𝓕 (innerSL_smul f) ξ)) ξ := by
--   refine hasFDerivAt_integral_vectorFourierIntegrand.congr_fderiv ?_
--   simp only [fderiv_vectorFourierIntegrand]
--   rw [← neg_smul, ← integral_smul]
--   refine congrArg _ ?_
--   funext x
--   ext m
--   rw [fderivVectorFourierIntegrandCLM_apply, ContinuousLinearMap.smul_apply, ← neg_smul]
--   refine congrArg _ ?_
--   simp only [vectorFourierIntegrand_apply, ContinuousLinearMap.smul_apply, innerSL_smul_apply]
--   rw [smul_comm]

-- theorem hasDerivAt_fourierIntegral {f : 𝓢(ℝ, F)} {ξ : ℝ} :
--     HasDerivAt (fun ξ ↦ 𝓕 f ξ)
--       (-((2 * π * I) • 𝓕 (fun x ↦ x • f x) ξ)) ξ := by
--   sorry

/-- The derivative of the Fourier transform is the Fourier transform of multiplication. -/
theorem hasDerivAt_fourierIntegral {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    HasDerivAt (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) (-((2 * π * I) • 𝓕 (fun x ↦ x • f x) ξ)) ξ := by
  refine .congr_deriv (_root_.hasDerivAt_fourierIntegral f.integrable ?_ ξ) ?_
  · exact (hasTemperateGrowth_smul Function.hasTemperateGrowth_id f).integrable
  · simp [Real.fourierIntegral_def, integral_neg,
      ← smul_smul (2 * π * I), smul_comm _ (2 * π * I), integral_smul]

/-- The derivative of the Fourier transform is the Fourier transform of multiplication. -/
theorem deriv_fourierIntegral {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    deriv (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) ξ = -((2 * π * I) • 𝓕 (fun x ↦ x • f x) ξ) :=
  hasDerivAt_fourierIntegral.deriv

theorem differentiable_fourierIntegral (f : 𝓢(ℝ, F)) :
    Differentiable ℝ (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) :=
  fun _ ↦ hasDerivAt_fourierIntegral.differentiableAt

theorem continuous_fourierIntegral (f : 𝓢(ℝ, F)) :
    Continuous (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) :=
  (differentiable_fourierIntegral f).continuous

theorem contDiff_fourierIntegral (n : ℕ∞) (f : 𝓢(ℝ, F)) :
    ContDiff ℝ n (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) := by
  -- This `generalizing f` approach would require induction over type for `fderiv`.
  induction n using ENat.nat_induction generalizing f with
  | h0 => simpa [contDiff_zero] using continuous_fourierIntegral f
  | hsuc n IH =>
    rw [contDiff_succ_iff_deriv]
    refine And.intro (differentiable_fourierIntegral f) ?_
    conv => arg 3; intro ξ
    simp only [deriv_fourierIntegral]
    refine ContDiff.neg ?_
    refine ContDiff.const_smul _ ?_
    simp only [← hasTemperateGrowth_smul_apply (Function.hasTemperateGrowth_id')]
    exact IH _
  | htop IH => exact contDiff_top.mpr fun n ↦ IH n f

theorem iteratedDeriv_fourierIntegral {n : ℕ} {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    iteratedDeriv n (fun ξ ↦ 𝓕 (fun x ↦ f x) ξ) ξ =
      ((-(2 * π * I)) ^ n • 𝓕 (fun x ↦ x ^ n • f x) ξ) := by
  induction n generalizing ξ with
  | zero => simp
  | succ n IH =>
    rw [iteratedDeriv_succ]
    conv => lhs; arg 1; intro ζ
    simp only [IH, ← hasTemperateGrowth_smul_apply (Function.hasTemperateGrowth_pow n)]
    rw [deriv_const_smul _ (differentiable_fourierIntegral _ ξ), deriv_fourierIntegral]
    simp [hasTemperateGrowth_smul_apply, pow_succ', smul_smul, mul_comm (_ ^ n)]

/-- Integration by parts for the Fourier integral of the derivative of a Schwartz function on ℝ. -/
theorem intervalIntegral_fourierIntegrand_deriv_sub_smul_fourierIntegrand {f : 𝓢(ℝ, F)} {ξ : ℝ}
    {a b : ℝ} :
    ∫ (x : ℝ) in a..b, Real.fourierChar[-(x * ξ)] • deriv (fun y ↦ f y) x -
        (2 * π * I * ξ) • Real.fourierChar[-(x * ξ)] • f x =
      Real.fourierChar[-(b * ξ)] • f b - Real.fourierChar[-(a * ξ)] • f a := by
  have := intervalIntegral.integral_deriv_smul_eq_sub (a := a) (b := b)
    (u := fun x ↦ Real.fourierChar[-(x * ξ)])
    (v := fun x ↦ f x)
    (u' := fun x ↦ (-ξ) • (2 * π * I * Real.fourierChar[-(x * ξ)]))
    (v' := fun x ↦ deriv f x)
    (fun x _ ↦ .comp_of_tower x (Real.hasDerivAt_fourierChar _) (hasDerivAt_mul_const ξ).neg)
    (fun x _ ↦ f.differentiableAt.hasDerivAt)
    (Continuous.continuousOn <|
      .const_smul (.mul continuous_const (continuous_mul_right ξ).neg.realFourierChar) _)
    (by simpa [derivCLM_apply ℝ] using (derivCLM ℝ f).continuous.continuousOn)
  simp only at this
  rw [← this]
  refine intervalIntegral.integral_congr ?_
  intro x _
  simp only
  rw [sub_eq_neg_add, add_left_inj]
  simp only [neg_smul, neg_inj]
  rw [Complex.real_smul, smul_smul]
  exact congrArg₂ _ (by ring) rfl

/-- The Fourier integral of the derivative is multiplication by the Fourier transform. -/
theorem fourierIntegral_deriv {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ deriv (fun y ↦ f y) x) ξ = (2 * π * I * ξ) • 𝓕 (fun x ↦ f x) ξ := by
  -- simp only [← derivCLM_apply]
  -- Replace `fourierChar[_]` with `realFourierIntegrand`; easy to show integrable and differentiable.
  -- change ∫ x, realFourierIntegrand ξ (derivCLM ℝ f) x = (2 * π * I * ξ) • ∫ x : ℝ, realFourierIntegrand ξ f x
  rw [← sub_eq_zero]
  simp only [Real.fourierIntegral_def]
  rw [← integral_smul]
  simp only [← derivCLM_apply (𝕜 := ℝ)]
  rw [← integral_sub (integrable_fourierIntegrand _ ξ) ((integrable_fourierIntegrand f ξ).smul' _)]
  have h_cover : AECover volume Filter.atTop (fun i => Set.Ioc (-i) i : ℕ → Set ℝ)
  . refine aecover_Ioc ?_ ?_ <;> simp [Filter.tendsto_neg_atBot_iff, tendsto_nat_cast_atTop_atTop]
  refine AECover.integral_eq_of_tendsto h_cover _
    (.sub (integrable_fourierIntegrand _ ξ) ((integrable_fourierIntegrand f ξ).smul' _)) ?_
  simp only [← intervalIntegral.integral_of_le (neg_le_self_iff.mpr (Nat.cast_nonneg _))]
  simp only [derivCLM_apply]
  simp only [intervalIntegral_fourierIntegrand_deriv_sub_smul_fourierIntegrand]
  -- TODO: Why do we need to specify `f` here?
  rw [← Function.comp_def (g := (fun n : ℕ ↦ (n : ℝ)))
    (fun x : ℝ ↦ Real.fourierChar[-(x * ξ)] • f x - Real.fourierChar[-(-x * ξ)] • f (-x))]
  refine Filter.Tendsto.comp ?_ tendsto_nat_cast_atTop_atTop
  rw [← sub_zero 0]
  simp only [fourierIntegrand_eq_hasTemperateGrowth_smul]
  refine Filter.Tendsto.sub ?_ ?_
  . exact Filter.Tendsto.mono_left (zero_at_infty _) atTop_le_cocompact
  · refine Filter.Tendsto.comp ?_ Filter.tendsto_neg_atTop_atBot
    exact Filter.Tendsto.mono_left (zero_at_infty _) atBot_le_cocompact

theorem fourierIntegral_iteratedDeriv {n : ℕ} {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x ↦ iteratedDeriv n (fun y ↦ f y) x) ξ =
      (2 * π * I * ξ) ^ n • 𝓕 (fun x ↦ f x) ξ := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedDeriv_succ]
    conv => lhs; arg 1; intro x; arg 1; intro z
    simp only [iteratedDeriv_eq_iteratedPDeriv]
    rw [fourierIntegral_deriv]
    simp only [← iteratedDeriv_eq_iteratedPDeriv]
    rw [IH]
    simp [pow_succ, smul_smul]

-- theorem fourierIntegral_pow_smul {n : ℕ} {f : 𝓢(ℝ, F)} {ξ : ℝ} :
--     𝓕 (fun x ↦ x ^ n • f x) ξ =
--       (2 * π * I) ^ n • ξ ^ n • 𝓕 (fun x ↦ f x) ξ := by
--   sorry

-- -- TODO: Excessive definition.
-- theorem pow_smul_fourierIntegral {n : ℕ} {f : 𝓢(ℝ, F)} {ξ : ℝ} :
--     ξ ^ n • 𝓕 (fun x ↦ f x) ξ =
--       ((2 * π * I) ^ n)⁻¹ • 𝓕 (fun x ↦ iteratedDeriv n (fun y ↦ f y) x) ξ := by
--   sorry

theorem norm_fourierIntegral_le_integral_norm (f : 𝓢(ℝ, F)) (ξ : ℝ) :
    ‖Real.fourierIntegral (fun x ↦ f x) ξ‖ ≤ ∫ x, ‖f x‖ := by
  simpa [Real.fourierIntegral_def] using
    norm_integral_le_of_norm_le f.integrable.norm
      (Filter.eventually_of_forall (by simp [norm_smul]))

-- theorem norm_fourierIntegral_le_seminorm {f : 𝓢(ℝ, F)} :
--     ∀ ξ, ‖Real.fourierIntegral ⇑f ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
--   intro ξ
--   refine le_trans (norm_fourierIntegral_le_integral_norm f ξ) ?_
--   refine le_trans ?_ (le_seminorm ℝ 0 0 f ξ)
--   simp
--   -- `∫ (x : ℝ), ‖f x‖ ≤ ‖f ξ‖`
--   sorry

-- TODO: Generalize beyond Schwartz map and `ℝ`? Just `iteratedDeriv_smul`? Does norm not suffice?
theorem iteratedDeriv_pow_smul {n k : ℕ} {f : 𝓢(ℝ, F)} :
    iteratedDeriv n (fun y ↦ y ^ k • f y) = fun x ↦ ∑ i in .range n.succ,
      n.choose i • k.descFactorial i • x ^ (k - i) • iteratedDeriv (n - i) f x := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedDeriv_succ, IH]
    funext x
    simp only [smul_smul]
    -- have h₁ (i) := differentiable_pow (𝕜 := ℝ) i
    have hf (i) := (f.smooth ⊤).differentiable_iteratedDeriv i (WithTop.coe_lt_top _)
    rw [deriv_sum fun i _ ↦ ((differentiable_pow _).smul (hf _)).const_smul _ _]
    simp only [deriv_const_smul _ ((differentiable_pow _).smul (hf _) _)]
    simp only [deriv_smul (differentiable_pow _ _) (hf _ _)]
    simp only [smul_add, Finset.sum_add_distrib]
    simp only [← iteratedDeriv_succ, deriv_pow]
    simp only [← Nat.sub_succ']
    rw [Finset.sum_range_succ' _ n.succ]
    simp only [Nat.choose_succ_succ]
    simp only [add_mul, add_smul, Finset.sum_add_distrib]
    simp only [Nat.succ_sub_succ_eq_sub]
    rw [add_comm, add_assoc]
    refine congrArg₂ _ ?_ ?_
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [← nsmul_eq_mul, smul_assoc, smul_smul]
      -- Could use `ring` here but gives warning due to nats.
      rw [Nat.descFactorial_succ, mul_comm (k - i), mul_assoc]
    · -- Eliminate zero term arising from `Nat.choose n n.succ`.
      conv => rhs; rw [Finset.sum_range_succ]
      simp only [Nat.choose_succ_self, zero_mul, zero_smul, add_zero]
      -- Split the term `n = 0` from the sum.
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.descFactorial_zero, mul_one, Nat.sub_zero, one_smul]
      rw [add_left_inj]
      -- Equate the remaining terms.
      refine Finset.sum_congr rfl ?_
      intro i hi
      replace hi : i.succ ≤ n := by simpa [Finset.mem_range] using hi
      simp [Nat.add_one, ← Nat.succ_sub hi]


-- The bound `C` depends on `n, k, f`.
-- We need `C` that only depends on `f` through `SchwartzMap.seminorm`...
theorem norm_integral_pow_smul_iteratedDeriv_bound {f : 𝓢(ℝ, F)} :
    ∃ C, 0 ≤ C ∧ ‖∫ x, x ^ k • iteratedDeriv n f x‖ ≤ C := by
  -- TODO: Cleaner way?
  generalize hg : hasTemperateGrowth_smul (Function.hasTemperateGrowth_pow k)
      (iteratedPDeriv ℝ (fun _ ↦ 1 : Fin n → ℝ) f) = g
  have (x : ℝ) : x ^ k • iteratedDeriv n f x = g x := by
    simp [← hg, hasTemperateGrowth_smul_apply, iteratedPDeriv_eq_iteratedFDeriv,
      iteratedDeriv_eq_iteratedFDeriv]
  simp only [this]
  clear this
  -- TODO: More idiomatic way?
  have := g.integrable.hasFiniteIntegral
  rw [HasFiniteIntegral, lt_top_iff_ne_top, WithTop.ne_top_iff_exists] at this
  rcases this with ⟨C, hC⟩
  use C.val
  refine And.intro C.prop ?_
  -- TODO: More idiomatic way?
  refine le_trans (norm_integral_le_lintegral_norm _) ?_
  refine ENNReal.toReal_le_of_le_ofReal C.prop ?_
  refine le_trans (lintegral_ofReal_le_lintegral_nnnorm _) ?_
  simp [← hC]

-- TODO: Make symmetric and remove `div`?
theorem norm_iteratedDeriv_fourierIntegral_eq_norm_fourierIntegral_iteratedDeriv {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    (2 * π) ^ k * (|ξ| ^ k * ‖iteratedDeriv n (fun ζ ↦ 𝓕 ⇑f ζ) ξ‖) =
      (2 * π) ^ n * ‖𝓕 (fun x ↦ iteratedDeriv k (fun y ↦ y ^ n • f y) x) ξ‖ := by
  rw [iteratedDeriv_fourierIntegral]
  -- Eliminate `(2 * π) ^ n` from both sides
  rw [norm_smul, mul_rotate' _ ‖_ ^ n‖, mul_rotate' _ ‖_ ^ n‖]
  refine congrArg₂ _ (by simp [abs_of_nonneg Real.pi_pos.le]) ?_
  simp only [← hasTemperateGrowth_smul_apply (Function.hasTemperateGrowth_pow n)]
  rw [fourierIntegral_iteratedDeriv]
  simp only [hasTemperateGrowth_smul_apply, norm_smul]
  rw [mul_assoc, mul_comm]
  refine congrArg₂ _ ?_ rfl
  rw [mul_comm]
  simp [mul_pow, abs_of_nonneg Real.pi_pos.le]

/--
Convenient form of
`norm_iteratedDeriv_fourierIntegral_eq_norm_fourierIntegral_iteratedDeriv`.
-/
theorem pow_abs_mul_norm_iteratedDeriv_fourierIntegral {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    |ξ| ^ k * ‖iteratedDeriv n (fun ζ ↦ 𝓕 ⇑f ζ) ξ‖ =
      (2 * π) ^ n / (2 * π) ^ k * ‖𝓕 (fun x ↦ iteratedDeriv k (fun y ↦ y ^ n • f y) x) ξ‖ := by
  rw [div_mul_eq_mul_div]
  rw [← norm_iteratedDeriv_fourierIntegral_eq_norm_fourierIntegral_iteratedDeriv]
  rw [mul_div_cancel_left]
  simp [Real.pi_pos.ne']

/--
Convenient form of
`norm_iteratedDeriv_fourierIntegral_eq_norm_fourierIntegral_iteratedDeriv`.
-/
theorem norm_fourierIntegral_iteratedDeriv_pow_smul {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    ‖𝓕 (fun x ↦ iteratedDeriv k (fun y ↦ y ^ n • f y) x) ξ‖ =
      (2 * π) ^ k / (2 * π) ^ n * (|ξ| ^ k * ‖iteratedDeriv n (fun ζ ↦ 𝓕 ⇑f ζ) ξ‖) := by
  rw [div_mul_eq_mul_div]
  rw [norm_iteratedDeriv_fourierIntegral_eq_norm_fourierIntegral_iteratedDeriv]
  rw [mul_div_cancel_left]
  simp [Real.pi_pos.ne']

-- This definition is too simplistic; doesn't even show linear.
noncomputable def fourierIntegral (f : 𝓢(ℝ, F)) : 𝓢(ℝ, F) where
  toFun ξ := 𝓕 f ξ
  smooth' := contDiff_fourierIntegral ⊤ f
  decay' k n := by
    use (2 * π) ^ n / (2 * π) ^ k * ∫ (x : ℝ), ‖iteratedDeriv k (fun y ↦ y ^ n • f y) x‖
    intro ξ
    simp only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp only [pow_abs_mul_norm_iteratedDeriv_fourierIntegral]
    refine mul_le_mul_of_nonneg_left ?_ (by refine div_nonneg ?_ ?_ <;> simp [Real.pi_pos.le])
    simp only [← hasTemperateGrowth_smul_apply (Function.hasTemperateGrowth_pow n)]
    simp only [iteratedDeriv_eq_iteratedPDeriv]
    exact norm_fourierIntegral_le_integral_norm _ ξ

@[simp]
theorem fourierIntegral_apply {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    fourierIntegral f ξ = 𝓕 (fun x ↦ f x) ξ := rfl

noncomputable def fourierIntegralLM : 𝓢(ℝ, F) →ₗ[ℝ] 𝓢(ℝ, F) where
  toFun := fourierIntegral
  map_add' f g := by ext; simp [Real.fourierIntegral_add]
  map_smul' r f := by ext; simp [Real.fourierIntegral_smul]

noncomputable def fourierIntegralCLM : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) where
  toLinearMap := fourierIntegralLM
  cont := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    conv => arg 1; intro f
    -- rw [continuous_def]
    -- rw [continuous_iff_isClosed]
    refine Seminorm.continuous_from_bounded (schwartz_withSeminorms ℝ ℝ F)
      (schwartz_withSeminorms ℝ ℝ F) _ ?_
    intro m
    rcases m with ⟨a, b⟩
    have s : Finset (ℕ × ℕ) := sorry
    have C : NNReal := sorry
    use s
    use C
    intro f
    simp only [schwartzSeminormFamily_apply, Seminorm.comp_apply, Seminorm.smul_apply]
    -- `(SchwartzMap.seminorm ℝ a b) (fourierIntegralLM f) ≤`
    --   `C • (Finset.sup s (schwartzSeminormFamily ℝ ℝ F)) f`
    sorry

/-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
noncomputable def fourierIntegralCLM' : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) :=
  mkCLM (fun f ξ ↦ 𝓕 (fun x ↦ f x) ξ)
    -- (fun f ξ ↦ ∫ x, Real.fourierChar[-(x * ξ)] • f x)
    (fun φ θ ξ ↦ by
      simpa [Real.fourierIntegral_def] using
        integral_add (integrable_fourierIntegrand φ ξ) (integrable_fourierIntegrand θ ξ))
    (fun c φ ξ ↦ by
      simpa [Real.fourierIntegral_def, smul_comm c] using
        integral_smul c (fun x ↦ Real.fourierChar[-(x * ξ)] • φ x))
    (fun φ ↦ by
      simp only [Real.fourierIntegral_def]
      -- Need to show:
      -- `ContDiff ℝ ⊤ fun x => ∫ (v : ℝ), ↑(Real.fourierChar (Multiplicative.ofAdd (-(v * x)))) • φ v`
      -- Use that derivative of Fourier transform is Fourier transform of multiplication?
      -- Suffices
      sorry)
    (fun m ↦ by
      -- Need to show that `‖ξ‖ ^ m.1 * ‖iteratedFDeriv ℝ m.2 (𝓕 ⇑f) ξ‖` is bounded.
      have s : Finset (ℕ × ℕ) := sorry
      have C : ℝ := sorry
      have hC : 0 ≤ C := sorry
      use s
      use C
      refine And.intro hC ?_
      intro f ξ

      simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      simp only [pow_abs_mul_norm_iteratedDeriv_fourierIntegral]

      -- simp only [← norm_pow, ← norm_smul]
      -- simp only [iteratedDeriv_fourierIntegral]
      -- simp only [smul_neg, norm_neg]
      -- simp only [smul_comm (_ ^ m.1)]
      -- have (f : 𝓢(ℝ, F)) (x : ℝ) : x ^ m.2 • f x =
      --     hasTemperateGrowth_smul (Function.hasTemperateGrowth_pow m.2) f x := by
      --   simp [hasTemperateGrowth_smul_apply]
      -- simp only [this]
      -- clear this
      -- simp only [pow_smul_fourierIntegral]
      -- -- Need to use fact that Fourier transform of a function with moderate decay is bounded?
      -- -- Or, just show that iteratedDeriv of Schwartz function is Schwartz? (is that true?)
      -- simp only [norm_smul]
      -- simp only [hasTemperateGrowth_smul_apply]

      -- Need to bound `‖𝓕 (fun x ↦ iteratedDeriv m.1 (fun y ↦ y ^ m.2 • f y) x) ξ‖` above.
      simp only [iteratedDeriv_pow_smul]
      -- Need to bound `‖𝓕 (fun x ↦ x ^ (m.2 - i) • iteratedDeriv (m.1 - i) f x) ξ‖` above for all `i`.
      -- From `SchwartzMap.le_seminorm`, have
      -- `‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ (SchwartzMap.seminorm 𝕜 k n) f`

      -- use Finset.Iic m

      -- Try going back the other way...
      simp only [iteratedDeriv_eq_iteratedFDeriv, ← iteratedPDeriv_eq_iteratedFDeriv (𝕜 := ℝ)]
      simp only [← hasTemperateGrowth_smul_apply (hg := Function.hasTemperateGrowth_pow _)]
      simp only [smul_smul]
      simp only [nsmul_eq_smul_cast ℝ]
      simp only [← smul_apply]
      simp only [Real.fourierIntegral_sum]
      simp only [smul_apply]
      simp only [Real.fourierIntegral_smul]
      simp only [hasTemperateGrowth_smul_apply]
      simp only [iteratedPDeriv_eq_iteratedFDeriv, ← iteratedDeriv_eq_iteratedFDeriv]
      rw [← inv_div, inv_mul_le_iff sorry]
      refine le_trans (norm_sum_le _ _) ?_
      simp only [norm_smul, IsROrC.norm_natCast]


      -- -- have (f : 𝓢(ℝ, F)) := decay (hasTemperateGrowth_smul (Function.hasTemperateGrowth_pow m.2) f)
      -- -- simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this

      -- simp only [iteratedDeriv_eq_iteratedFDeriv]
      -- simp only [← iteratedPDeriv_eq_iteratedFDeriv (𝕜 := ℝ)]

      -- have k : ℕ := sorry
      -- have n : ℕ := sorry
      -- use Finset.Iic (k, n)
      -- have C : ℝ := sorry
      -- -- have hC : 0 ≤ C := sorry
      -- -- use (2 * π) ^ m.2 / (2 * π) ^ m.1
      -- use (2 * π) ^ m.2 * ((2 * π) ^ m.1)⁻¹ * C
      -- refine And.intro sorry ?_
      -- simp [abs_of_nonneg Real.pi_pos.le]
      -- intro f ξ
      -- rw [← mul_assoc]
      -- rw [mul_assoc _ C]
      -- refine mul_le_mul_of_nonneg_left ?_
      --   (by refine mul_nonneg ?_ ?_ <;> simp [pow_nonneg (mul_pos two_pos Real.pi_pos).le _])

      -- rw [Real.fourierIntegral_def]
      -- -- simp only [Real.fourierIntegrand_eq_hasTemperateGrowth_smul]
      -- -- simp only [← integralCLM_apply]
      -- -- have := ContinuousLinearMap.le_opNorm integralCLM f
      -- refine le_trans (ContinuousLinearMap.le_opNorm integralCLM _) ?_


      -- -- refine le_trans (norm_fourierIntegral_le_integral_norm _ _) ?_
      -- -- sorry

      sorry)

end Real

end SchwartzMap  -- namespace
