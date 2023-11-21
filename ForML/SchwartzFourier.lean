import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner

import ForML.HasTemperateGrowth
import ForML.IntegralAgainst
import ForML.SchwartzDeriv
import ForML.SchwartzLp
import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace Complex FourierTransform RealInnerProductSpace
open scoped BigOperators Real

variable {𝕜 𝕜' R D E F G : Type*}


section Continuous

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]

/-- Application of `VectorFourier.fourierIntegral_continuous`. -/
lemma Real.fourierIntegral_continuous {f : ℝ → F} (hf : Integrable f) :
    Continuous (Real.fourierIntegral f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_mul) hf

-- lemma ContDiff.ofReal {f : ℝ → ℝ} {n : ℕ∞} (hf : ContDiff ℝ n f) :
--     ContDiff ℝ n (fun x => (f x : ℂ)) :=
--   ofRealClm.contDiff.comp hf

end Continuous


section Integral

-- variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] -- [NormedSpace ℂ F]
-- variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]

lemma SchwartzMap.integralCLM_eq_L1_integral {f : 𝓢(E, F)} [CompleteSpace F] : integralCLM f = L1.integral f.toL1 := by
  rw [integralCLM_apply]
  rw [L1.integral_eq_integral]
  exact integral_congr_ae (coeFn_toL1 f).symm

end Integral


namespace SchwartzMap

section Fourier

variable [NormedAddCommGroup E] [hE : InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

instance : NormedSpace ℝ E := hE.toNormedSpace  -- Type system can't find this?

-- Prove that the Fourier transform of a Schwartz function is a Schwartz function
-- in order to define the Fourier transform of a tempered distribution.
-- https://math.mit.edu/~rbm/iml/Chapter1.pdf
-- https://math.stackexchange.com/questions/445089/fourier-transform-of-a-schwartz-space-function-and-norm
-- https://sites.math.washington.edu/~hart/m556/Lecture25.pdf

-- We already have that the Fourier transform of a Schwartz function is continuous
-- using `VectorFourier.fourierIntegral_continuous` and that Schwartz functions are integrable.

-- Next step is to obtain the derivative of the Fourier transform
-- and the Fourier transform of the derivative.


/-- The real Fourier integrand as a Schwartz function in one variable. -/
noncomputable def realFourierIntegrand (f : 𝓢(ℝ, F)) (ξ : ℝ) : 𝓢(ℝ, F) :=
  hasTemperateGrowth_smul (Real.hasTemperateGrowth_fourierChar_neg_mul_const ξ) f

lemma realFourierIntegrand_apply {f : 𝓢(ℝ, F)} {ξ x : ℝ} :
    realFourierIntegrand f ξ x = Real.fourierChar[-(x * ξ)] • f x := by
  rw [realFourierIntegrand, hasTemperateGrowth_smul_apply]

/-- The vector Fourier integrand as a Schwartz function in one variable. -/
noncomputable def vectorFourierIntegrand (ξ : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  hasTemperateGrowth_smul (Real.hasTemperateGrowth_inner_const ξ).neg.realFourierChar

lemma vectorFourierIntegrand_apply {f : 𝓢(E, F)} {ξ x : E} :
    vectorFourierIntegrand ξ f x = Real.fourierChar[-⟪x, ξ⟫] • f x := by
  rw [vectorFourierIntegrand, hasTemperateGrowth_smul_apply]

lemma contDiff_vectorFourierIntegrand_prod {f : 𝓢(E, F)} :
    ContDiff ℝ ⊤ fun m : (E × E) => vectorFourierIntegrand m.2 f m.1 := by
  -- Use "of_tower" variant in `ForML.Util`.
  exact ContDiff.smul_of_tower contDiff_inner.neg.realFourierChar (f.smooth'.comp contDiff_fst)

lemma contDiff_vectorFourierIntegrand {f : 𝓢(E, F)} {x : E} :
    ContDiff ℝ ⊤ (fun ξ => vectorFourierIntegrand ξ f x) := by
  change ContDiff ℝ ⊤ ((fun p : E × E => vectorFourierIntegrand p.2 f p.1) ∘ (fun ξ => (x, ξ)))
  exact ContDiff.comp contDiff_vectorFourierIntegrand_prod (contDiff_prod_mk_right x)

lemma differentiable_vectorFourierIntegrand {f : 𝓢(E, F)} {x : E} :
    Differentiable ℝ (fun ξ => vectorFourierIntegrand ξ f x) :=
  contDiff_vectorFourierIntegrand.differentiable le_top

lemma continuous_vectorFourierIntegrand {f : 𝓢(E, F)} {x : E} :
    Continuous (fun ξ => vectorFourierIntegrand ξ f x) :=
  contDiff_vectorFourierIntegrand.continuous

/--
The Fourier integrand commutes with pointwise smul by the inner product map.

TODO: There's likely a more general version of this lemma for `HasTemperateGrowth` functions
(the Fourier integrand commutes with a pointwise smul action).
-/
lemma innerSL_smul_vectorFourierIntegrand_comm {f : 𝓢(E, F)} {ξ : E} :
    innerSL_smul (vectorFourierIntegrand ξ f) =
    vectorFourierIntegrand ξ (innerSL_smul f) := by
  ext x m
  simp [innerSL_smul_apply, vectorFourierIntegrand_apply]
  rw [smul_comm]

-- Give hint to find instance for `(c : ℂ) • f` in `fderivCLM_vectorFourierIntegrand`.
-- noncomputable instance : Module ℂ (𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F)) := ContinuousLinearMap.module
instance {D E F G : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] :
    Module ℂ (𝓢(D, E) →L[ℝ] 𝓢(F, G)) := ContinuousLinearMap.module

/--
The Fréchet derivative of `vectorFourierIntegrand` with respect to `ξ`; Schwartz in `x`, linear in `dξ`.

The derivative with respect to `x` can be obtained using `SchwartzMap.fderivCLM`.
-/
noncomputable def fderivCLM_vectorFourierIntegrand (ξ : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F) :=
  -((2 * π * Complex.I) • (vectorFourierIntegrand ξ).comp (innerSL_smul (F := F)))

lemma fderivCLM_vectorFourierIntegrand_apply {f : 𝓢(E, F)} {x ξ dξ : E} :
    fderivCLM_vectorFourierIntegrand ξ f x dξ =
    -((2 * π * Complex.I * ⟪x, dξ⟫) • vectorFourierIntegrand ξ f x) := by
  rw [fderivCLM_vectorFourierIntegrand]
  simp [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply]
  rw [← innerSL_smul_vectorFourierIntegrand_comm]
  rw [innerSL_smul_apply]
  rw [smul_comm]
  rw [← smul_assoc]
  simp
  ring_nf

/-- The Fréchet derivative of `vectorFourierIntegrand` with respect to `ξ`. -/
lemma fderiv_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ x : E} :
    fderiv ℝ (fun ξ' => vectorFourierIntegrand ξ' f x) ξ =
    fderivCLM_vectorFourierIntegrand ξ f x := by
  change fderiv ℝ ((fun u : ℝ => Real.fourierChar[u] • f x) ∘ fun ξ' : E => -⟪x, ξ'⟫) ξ = _
  refine ContinuousLinearMap.ext ?_
  intro dξ
  rw [fderiv.comp]
  rotate_left
  . refine (ContDiff.differentiable ?_ le_top).differentiableAt
    exact ContDiff.smul_of_tower Real.contDiff_fourierChar contDiff_const
  . refine (ContDiff.differentiable ?_ le_top).differentiableAt
    exact (ContDiff.inner ℝ contDiff_const contDiff_id).neg
  rw [ContinuousLinearMap.comp_apply]
  simp
  rw [fderiv_inner_apply ℝ (differentiableAt_const x) differentiableAt_id']
  simp
  rw [fderiv_smul_const]
  swap
  . -- TODO: Avoid repetition?
    refine (ContDiff.differentiable ?_ le_top).differentiableAt
    exact Real.contDiff_fourierChar
  simp
  rw [Real.fderiv_fourierChar]
  simp
  rw [fderivCLM_vectorFourierIntegrand_apply]
  rw [vectorFourierIntegrand_apply]
  simp
  rw [smul_comm]
  simp [← smul_assoc]
  ring_nf

-- TODO: More idiomatic to define `HasFDerivAt` before `fderiv`?
lemma hasFDerivAt_vectorFourierIntegrand {f : 𝓢(E, F)} {x ξ₀ : E} :
    HasFDerivAt (fun ξ : E => vectorFourierIntegrand ξ f x) (fderivCLM_vectorFourierIntegrand ξ₀ f x) ξ₀ :=
  HasFDerivAt.congr_fderiv
    differentiable_vectorFourierIntegrand.differentiableAt.hasFDerivAt
    fderiv_vectorFourierIntegrand

-- Need to provide assistance?
-- noncomputable instance : SeminormedAddCommGroup (E →L[ℝ] ℂ) := ContinuousLinearMap.toSeminormedAddCommGroup
-- noncomputable instance : NormedSpace ℝ (E →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace

/-- Uses `‖cexp (_ • I)‖ = 1` to obtain norm independent of `ξ`. -/
lemma norm_fderivCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ x : E} :
    ‖fderivCLM_vectorFourierIntegrand ξ f x‖ = 2 * π * ‖innerSL_smul f x‖ := by
    -- ‖fderiv ℝ (fun ξ => vectorFourierIntegrand ξ f x) ξ‖ = 2 * π * ‖innerSL_smul f x‖ := by
  suffices : ‖fderivCLM_vectorFourierIntegrand ξ f x‖ = ‖innerSL_smul ((2 * π) • f) x‖
  . simpa [norm_smul, _root_.abs_of_nonneg Real.pi_pos.le] using this
  simp only [ContinuousLinearMap.norm_def]
  simp only [fderivCLM_vectorFourierIntegrand_apply, vectorFourierIntegrand_apply, innerSL_smul_apply]
  simp
  congr
  ext r
  simp
  intro _
  refine forall_congr' ?_
  intro u
  simp [norm_smul]
  ring_nf


section Integral

variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [CompleteSpace F]

/-- Leibniz integral rule for Fourier integrand. -/
lemma hasFDerivAt_integral_vectorFourierIntegrand_integral_fderiv {f : 𝓢(E, F)} {ξ₀ : E} :
    HasFDerivAt (fun ξ => ∫ x, vectorFourierIntegrand ξ f x)
      (∫ x, fderiv ℝ (fun ξ => vectorFourierIntegrand ξ f x) ξ₀) ξ₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun ξ x => fderiv ℝ (fun ξ => vectorFourierIntegrand ξ f x) ξ)
      -- (bound := fun x => 2 * π * ‖innerSL_smul f x‖)
      zero_lt_one ?_ (vectorFourierIntegrand ξ₀ f).integrable ?_ ?_
      ((innerSL_smul f).integrable.norm.const_mul (2 * π)) ?_
  . refine Filter.eventually_of_forall ?_
    intro ξ
    exact Continuous.aestronglyMeasurable (SchwartzMap.continuous _)
  . refine Continuous.aestronglyMeasurable ?_
    simp
    exact Continuous.fderiv contDiff_vectorFourierIntegrand_prod continuous_const le_top
  . refine Filter.eventually_of_forall ?_
    intro x ξ _
    simp
    rw [fderiv_vectorFourierIntegrand]
    rw [norm_fderivCLM_vectorFourierIntegrand]
  . refine Filter.eventually_of_forall ?_
    intro x ξ _
    simp
    exact differentiable_vectorFourierIntegrand.differentiableAt.hasFDerivAt

/-- Leibniz integral rule for Fourier integrand in terms of CLMs. -/
lemma hasFDerivAt_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ₀ : E} :
    HasFDerivAt (fun ξ => integralCLM (vectorFourierIntegrand ξ f))
      (integralCLM (fderivCLM_vectorFourierIntegrand ξ₀ f)) ξ₀ := by
  simp_rw [integralCLM_apply]
  simp_rw [← fderiv_vectorFourierIntegrand]
  exact hasFDerivAt_integral_vectorFourierIntegrand_integral_fderiv

lemma fderiv_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ =
    integralCLM (fderivCLM_vectorFourierIntegrand ξ f) :=
  hasFDerivAt_integralCLM_vectorFourierIntegrand.fderiv

lemma differentiable_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Differentiable ℝ fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  fun _ => hasFDerivAt_integralCLM_vectorFourierIntegrand.differentiableAt

lemma continuous_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Continuous fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  -- TODO: Is this an upside-down way to prove this?
  -- Could use `integralCLM.continuous.comp`; show that `hasTemperateGrowth_smul` is continuous with Schwartz topology?
  differentiable_integralCLM_vectorFourierIntegrand.continuous

section Induction

universe u
variable {E F : Type u}  -- Ensure that `E →L[ℝ] F` is in the same universe as `F`.

variable [NormedAddCommGroup E] [hE : InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [CompleteSpace F]

/-- The Fourier integral of a Schwartz map is smooth. -/
theorem contDiff_fourierIntegral {f : 𝓢(E, F)} : ContDiff ℝ ⊤ fun ξ => ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x := by
  simp_rw [← vectorFourierIntegrand_apply]
  simp_rw [← integralCLM_apply]
  rw [contDiff_top]
  intro n
  induction n generalizing F with
  | zero =>
    simp
    exact continuous_integralCLM_vectorFourierIntegrand
  | succ n h_ind =>
    rw [contDiff_succ_iff_fderiv]
    refine ⟨differentiable_integralCLM_vectorFourierIntegrand, ?_⟩
    simp_rw [fderiv_integralCLM_vectorFourierIntegrand]
    simp_rw [fderivCLM_vectorFourierIntegrand]
    simp [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply]
    simp [integralCLM_neg_apply, integralCLM_smul_apply]
    refine ContDiff.neg ?_
    refine ContDiff.const_smul (2 * π * I : ℂ) ?_
    -- Need `E →L[ℝ] F` to be in same universe as `F` to apply induction.
    exact h_ind

/-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
noncomputable def vectorFourierIntegralCLM : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  mkCLM (fun f ξ => ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x)
    (fun φ θ ξ => by
      simp_rw [← vectorFourierIntegrand_apply]
      change (∫ x, vectorFourierIntegrand ξ (φ + θ) x) = _
      simp
      rw [integral_add (integrable _) (integrable _)])
    (fun c φ ξ => by
      simp_rw [← vectorFourierIntegrand_apply]
      simp
      rw [integral_smul])
    (fun φ => contDiff_fourierIntegral)
    (fun m => by
      simp_rw [← vectorFourierIntegrand_apply]
      simp_rw [← integralCLM_apply]
      have k' := 5
      have n' := 7
      have C' := π
      use Finset.Iic (k', n')
      use C'
      refine ⟨sorry, ?_⟩
      intro φ ξ
      have hφ := φ.decay'
      rcases m with ⟨k, n⟩
      simp
      sorry)

end Induction
end Integral
end Fourier
end SchwartzMap  -- namespace
