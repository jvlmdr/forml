import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import ForML.HasTemperateGrowth
import ForML.IndexDerivBasic
import ForML.IndexIntegral
import ForML.IntegralAgainst
import ForML.SchwartzDeriv
import ForML.SchwartzEquiv
import ForML.SchwartzLp
import ForML.Trigonometric
import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace Complex FourierTransform RealInnerProductSpace
open scoped BigOperators Real

attribute [-simp] ofAdd_neg

section NoTypeInduction

variable {ι 𝕜 𝕜' R : Type*} {M : ι → Type*} {D E F G : Type*}

section Continuous

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Real version of `VectorFourier.fourierIntegral_continuous`. -/
lemma Real.fourierIntegral_continuous {f : ℝ → F} (hf : Integrable f) :
    Continuous (Real.fourierIntegral f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_mul) hf

-- lemma ContDiff.ofReal {f : ℝ → ℝ} {n : ℕ∞} (hf : ContDiff ℝ n f) :
--     ContDiff ℝ n (fun x => (f x : ℂ)) :=
--   ofRealClm.contDiff.comp hf

end Continuous


section VectorDef

variable [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
noncomputable instance mE : MeasureSpace E := measureSpaceOfInnerProductSpace  -- Might not be required?
variable [CompleteSpace F]

/-- Definition of l2 inner product for pi type. -/
noncomputable def l2innerₛₗ (𝕜 : Type*) [IsROrC 𝕜] {ι : Type*} [Fintype ι] :
    (ι → 𝕜) →ₗ⋆[𝕜] (ι → 𝕜) →ₗ[𝕜] 𝕜 := innerₛₗ 𝕜 (E := EuclideanSpace 𝕜 ι)

lemma l2innerₛₗ_apply {𝕜 : Type*} [IsROrC 𝕜] {ι : Type*} [Fintype ι] {x y : ι → 𝕜} :
    l2innerₛₗ 𝕜 x y = ∑ i, inner (x i) (y i) := rfl

-- noncomputable def RealVectorFourier.fourierIntegral
--     (f : EuclideanSpace ℝ ι → F) (ξ : EuclideanSpace ℝ ι) : F :=
--   VectorFourier.fourierIntegral Real.fourierChar volume (innerₛₗ ℝ (E := EuclideanSpace ℝ ι)) f ξ

-- /-- Definition of Fourier transform for finite-dimensional real vectors as Euclidean space. -/
-- noncomputable def RealVectorFourier.fourierIntegral (f : (ι → ℝ) → F) (ξ : ι → ℝ) : F :=
--   VectorFourier.fourierIntegral Real.fourierChar volume l2innerₛₗ f ξ

-- /-- Notation for Fourier transform for finite-dimensional real vectors as Euclidean space. -/
-- scoped[FourierTransform] notation "𝓕ₙ" => RealVectorFourier.fourierIntegral

-- lemma RealVectorFourier.fourierIntegral_apply {f : (ι → ℝ) → F} {ξ : ι → ℝ} :
--     -- 𝓕ₙ f ξ = ∫ x, Real.fourierChar[-⟪(x : EuclideanSpace ℝ ι), ξ⟫] • f x := by
--     𝓕ₙ f ξ = ∫ x : ι → ℝ, Real.fourierChar[-∑ i, x i * ξ i] • f x := by
--   rw [RealVectorFourier.fourierIntegral]
--   rw [VectorFourier.fourierIntegral]
--   change ∫ (x : EuclideanSpace ℝ ι), Real.fourierChar (Multiplicative.ofAdd (-innerₛₗ ℝ x ξ)) • f x = _
--   change _ = ∫ (x : ι → ℝ), Real.fourierChar (Multiplicative.ofAdd _) • f x
--   rw [← MeasurePreserving.integral_comp' (EuclideanSpace.volume_preserving_measurableEquiv ι)]
--   rfl

/-- Notation for Fourier transform for real `InnerProductSpace`. -/
scoped[FourierTransform] notation "𝓕ᵥ" => VectorFourier.fourierIntegral Real.fourierChar volume (innerₛₗ ℝ)
-- scoped[FourierTransform] notation "𝓕ᵥ[" V "]" => VectorFourier.fourierIntegral Real.fourierChar (volume : Measure V) (innerₛₗ ℝ)

/--
Notation for Fourier transform for real vectors using l2 inner product.
Useful for differentiating or integrating wrt one coordinate.
-/
scoped[FourierTransform] notation "𝓕ₙ" => VectorFourier.fourierIntegral Real.fourierChar volume (l2innerₛₗ ℝ)

namespace RealVectorFourier

lemma fourierIntegral_l2inner_apply {f : (ι → ℝ) → F} {ξ : ι → ℝ} :
    𝓕ₙ f ξ = ∫ x, Real.fourierChar[-∑ i, x i * ξ i] • f x := rfl

lemma fourierIntegral_euclidean_eq_fourierIntegral_l2inner {f : EuclideanSpace ℝ ι → F} {ξ : EuclideanSpace ℝ ι} :
    𝓕ᵥ f ξ = 𝓕ₙ f ξ := by
  rw [VectorFourier.fourierIntegral]
  rw [← MeasurePreserving.integral_comp' (EuclideanSpace.volume_preserving_measurableEquiv ι).symm]
  rfl

lemma fourierIntegral_l2inner_eq_fourierIntegral_euclidean {f : (ι → ℝ) → F} {ξ : ι → ℝ} :
    𝓕ₙ f ξ = 𝓕ᵥ (f ∘ ⇑(EuclideanSpace.equiv ι ℝ)) ξ := by
  rw [VectorFourier.fourierIntegral]
  rw [← MeasurePreserving.integral_comp' (EuclideanSpace.volume_preserving_measurableEquiv ι)]
  rfl

lemma fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis (v : OrthonormalBasis ι ℝ E) {f : E → F} {ξ : E} :
    𝓕ᵥ f ξ = 𝓕ᵥ (f ∘ ⇑v.repr.symm) (v.repr ξ) := by
  rw [VectorFourier.fourierIntegral]
  rw [VectorFourier.fourierIntegral]
  rw [← MeasurePreserving.integral_comp' (v.measurePreserving_measurableEquiv)]
  conv =>
    rhs; arg 2; intro x
    change Real.fourierChar[-innerₛₗ ℝ (v.repr x) (v.repr ξ)] • f (v.repr.symm (v.repr x))
    simp

lemma fourierIntegral_eq_fourierIntegral_euclidean_stdOrthonormalBasis {f : E → F} {ξ : E} :
    𝓕ᵥ f ξ = 𝓕ᵥ (f ∘ ⇑(stdOrthonormalBasis ℝ E).repr.symm) ((stdOrthonormalBasis ℝ E).repr ξ) :=
  fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis (stdOrthonormalBasis ℝ E)

lemma fourierIntegral_eq_fourierIntegral_l2inner_ofOrthonormalBasis (v : OrthonormalBasis ι ℝ E) {f : E → F} {ξ : E} :
    𝓕ᵥ f ξ = 𝓕ₙ (f ∘ ⇑v.repr.symm) (v.repr ξ) := by
  rw [fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis v]
  rw [fourierIntegral_euclidean_eq_fourierIntegral_l2inner]

lemma fourierIntegral_eq_fourierIntegral_l2inner_stdOrthonormalBasis {f : E → F} {ξ : E} :
    𝓕ᵥ f ξ = 𝓕ₙ (f ∘ ⇑(stdOrthonormalBasis ℝ E).repr.symm) ((stdOrthonormalBasis ℝ E).repr ξ) :=
  fourierIntegral_eq_fourierIntegral_l2inner_ofOrthonormalBasis (stdOrthonormalBasis ℝ E)

end RealVectorFourier  -- namespace

end VectorDef


section Tendsto

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

-- TODO: Generalize to vector space `E` using cocompact filter?
/-- A `SchwartzMap` on `ℝ` goes to zero at infinity. -/
theorem tendsto_atTop_zero_real (f : 𝓢(ℝ, F)) : Filter.Tendsto (fun x => f x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rcases f.decay₁ 1 0 with ⟨C, hC⟩
  simp at hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (h := fun x => C * (1 + |x|)⁻¹) tendsto_const_nhds ?_ ?_ ?_
  . rw [← mul_zero C]
    refine Filter.Tendsto.const_mul C ?_
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    refine Filter.tendsto_atTop_add_const_left _ 1 ?_
    exact Filter.tendsto_abs_atTop_atTop
  . intro x
    simp
  . intro x
    simp
    rw [← div_eq_mul_inv]
    rw [le_div_iff (lt_of_lt_of_le zero_lt_one (by simp))]
    rw [mul_comm]
    exact hC x

/-- Maps `f` to `x ↦ f (-x)`. -/
def compNegEquiv : 𝓢(E, F) ≃L[ℝ] 𝓢(E, F) := compEquiv (LinearIsometryEquiv.neg ℝ (E := E))

@[simp]
lemma compNegEquiv_apply {f : 𝓢(E, F)} {x : E} : compNegEquiv f x = f (-x) := rfl

/-- A `SchwartzMap` on `ℝ` goes to zero at negative infinity. -/
theorem tendsto_atBot_zero_real (f : 𝓢(ℝ, F)) : Filter.Tendsto (fun x => f x) Filter.atBot (nhds 0) := by
  conv => arg 1; intro x; rw [← neg_neg x]; rw [← compNegEquiv_apply]
  exact (tendsto_atTop_zero_real (compNegEquiv f)).comp Filter.tendsto_neg_atBot_atTop

end SchwartzMap  -- namespace

end Tendsto


section Fourier

variable [DecidableEq ι] [Fintype ι]
variable [NontriviallyNormedField 𝕜]
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]

variable [NormedAddCommGroup D] [NormedSpace ℝ D]
-- Note: `NormedSpace ℝ E` provided by `InnerProductSpace.Core.toNormedSpace`.
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
-- Note: `NormedSpace ℝ F` provided by `NormedSpace.complexToReal`.
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
-- Note: `MeasureSpace E` provided by `measureSpaceOfInnerProductSpace`.
variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
variable [MeasurableSpace E'] [FiniteDimensional ℝ E'] [BorelSpace E']
variable [CompleteSpace F]

section Explicit
variable (M)

lemma Function.hasTemperateGrowth_single (i : ι) :
    HasTemperateGrowth (fun u : M i => Pi.single i u) := by
  change HasTemperateGrowth (fun u : M i => ContinuousLinearMap.single (R := ℝ) i u)
  exact hasTemperateGrowth_clm _

end Explicit

namespace SchwartzMap

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
noncomputable def realFourierIntegrand (ξ : ℝ) : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) :=
  hasTemperateGrowth_smul (Real.hasTemperateGrowth_fourierChar_neg_mul_const ξ)

lemma realFourierIntegrand_apply {f : 𝓢(ℝ, F)} {ξ x : ℝ} :
    realFourierIntegrand ξ f x = Real.fourierChar[-(x * ξ)] • f x := rfl

lemma integral_realFourierIntegrand {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 f ξ = ∫ x, realFourierIntegrand ξ f x := rfl

/-- The vector Fourier integrand as a Schwartz function in one variable. -/
noncomputable def vectorFourierIntegrand (ξ : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  hasTemperateGrowth_smul (Real.hasTemperateGrowth_inner_const ξ).neg.realFourierChar

lemma vectorFourierIntegrand_apply {f : 𝓢(E, F)} {ξ x : E} :
    vectorFourierIntegrand ξ f x = Real.fourierChar[-⟪x, ξ⟫] • f x := rfl

-- TODO: Rename "realVectorFourier" to better reflect pi type with l2 inner product
-- ("vectorFourier" already assumes E is a real `InnerProductSpace`).
-- Ideas: l2fourier, l2piFourier, l2realFourier, realL2Fourier, l2vectorFourier, piRealFourier

/-- The real vector Fourier integrand (using pi type) as a Schwartz function in one variable. -/
noncomputable def realVectorFourierIntegrand (ξ : ι → ℝ) : 𝓢(ι → ℝ, F) →L[ℝ] 𝓢(ι → ℝ, F) :=
  hasTemperateGrowth_smul (Real.hasTemperateGrowth_l2inner_const ξ).neg.realFourierChar

lemma realVectorFourierIntegrand_apply {f : 𝓢(ι → ℝ, F)} {ξ x : ι → ℝ} :
    realVectorFourierIntegrand ξ f x = Real.fourierChar[-∑ i, x i * ξ i] • f x := rfl

lemma realVectorFourierIntegrand_eq_vectorFourierIntegrand_euclidean {f : 𝓢(ι → ℝ, F)} {ξ : ι → ℝ} :
    realVectorFourierIntegrand ξ f =
    compEquiv
      (EuclideanSpace.equiv ι ℝ).symm
      (vectorFourierIntegrand (E := EuclideanSpace ℝ ι) ξ (compEquiv (EuclideanSpace.equiv ι ℝ) f)) := rfl

lemma realVectorFourierIntegrand_apply_vectorFourierIntegrand_euclidean {f : 𝓢(ι → ℝ, F)} {ξ x : ι → ℝ} :
    realVectorFourierIntegrand ξ f x =
    vectorFourierIntegrand (E := EuclideanSpace ℝ ι) ξ (compEquiv (EuclideanSpace.equiv ι ℝ) f) x := rfl

lemma vectorFourierIntegrand_euclidean_eq_realVectorFourierIntegrand {f : 𝓢(EuclideanSpace ℝ ι, F)} {ξ : EuclideanSpace ℝ ι} :
    vectorFourierIntegrand ξ f =
    compEquiv (EuclideanSpace.equiv ι ℝ)
      (realVectorFourierIntegrand ξ (compEquiv (EuclideanSpace.equiv ι ℝ).symm f)) := rfl

lemma vectorFourierIntegrand_euclidean_apply_realVectorFourierIntegrand {f : 𝓢(EuclideanSpace ℝ ι, F)} {ξ x : EuclideanSpace ℝ ι} :
    vectorFourierIntegrand ξ f x =
    realVectorFourierIntegrand ξ (compEquiv (EuclideanSpace.equiv ι ℝ).symm f) x := rfl

lemma vectorFourierIntegrand_compEquiv_symm_apply (e : E ≃ₗᵢ[ℝ] E') {f : 𝓢(E, F)} {ξ x : E} :
    vectorFourierIntegrand ξ f x =
    vectorFourierIntegrand (e ξ) (compEquiv e.symm.toContinuousLinearEquiv f) (e x) := by
  simp [vectorFourierIntegrand_apply]

lemma vectorFourierIntegrand_compEquiv_symm (e : E ≃ₗᵢ[ℝ] E') {f : 𝓢(E, F)} {ξ : E} :
    vectorFourierIntegrand ξ f = compEquiv e.toContinuousLinearEquiv
      (vectorFourierIntegrand (e ξ) (compEquiv e.symm.toContinuousLinearEquiv f)) := by
  ext x
  simp
  exact vectorFourierIntegrand_compEquiv_symm_apply e

lemma vectorFourierIntegrand_compEquiv_apply (e : E' ≃ₗᵢ[ℝ] E) {f : 𝓢(E, F)} {ξ x : E} :
    vectorFourierIntegrand ξ f x =
    vectorFourierIntegrand (e.symm ξ) (compEquiv e.toContinuousLinearEquiv f) (e.symm x) := by
  simp [vectorFourierIntegrand_apply]

lemma vectorFourierIntegrand_compEquiv (e : E' ≃ₗᵢ[ℝ] E) {f : 𝓢(E, F)} {ξ : E} :
    vectorFourierIntegrand ξ f = compEquiv e.symm.toContinuousLinearEquiv
      (vectorFourierIntegrand (e.symm ξ) (compEquiv e.toContinuousLinearEquiv f)) := by
  ext x
  simp
  exact vectorFourierIntegrand_compEquiv_apply e


/-- Express the Fourier integrand for a real `InnerProductSpace` using pi type. -/
lemma vectorFourierIntegrand_apply_realVectorFourierIntegrand_ofOrthonormalBasis (v : OrthonormalBasis ι ℝ E)
    {f : 𝓢(E, F)} {ξ x : E} :
    vectorFourierIntegrand ξ f x =
    realVectorFourierIntegrand
      (v.repr ξ)
      (compEquiv (v.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv ι ℝ)).symm f)
      (v.repr x) := by
  simp [vectorFourierIntegrand_apply, realVectorFourierIntegrand_apply]
  congr
  . rw [← v.repr.inner_map_map]
    rfl
  . rw [ContinuousLinearEquiv.eq_symm_apply]
    rfl

/-- Express the Fourier integrand for a real `InnerProductSpace` using pi type. -/
lemma vectorFourierIntegrand_eq_realVectorFourierIntegrand_ofOrthonormalBasis (v : OrthonormalBasis ι ℝ E)
    {f : 𝓢(E, F)} {ξ : E} :
    vectorFourierIntegrand ξ f = compEquiv (v.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv ι ℝ))
      (realVectorFourierIntegrand
        (v.repr ξ)
        (compEquiv (v.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv ι ℝ)).symm f)) := by
  ext x
  simp
  rw [vectorFourierIntegrand_apply_realVectorFourierIntegrand_ofOrthonormalBasis v]
  rfl


lemma vectorFourierIntegrand_smul_apply {f : 𝓢(E, F)} {ξ x : E} {c : ℂ} :
    c • vectorFourierIntegrand ξ f x = Real.fourierChar[-⟪x, ξ⟫] • (c • f) x := by
  simp
  rw [smul_comm]
  rfl

lemma integral_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ : E} :
    𝓕ᵥ f ξ = ∫ x, vectorFourierIntegrand ξ f x := rfl

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

-- -- Give hint to find instance for `(c : ℂ) • f` in `fderivCLM_vectorFourierIntegrand`.
-- -- noncomputable instance : Module ℂ (𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F)) := ContinuousLinearMap.module
-- instance {D E F G : Type*}
--     [NormedAddCommGroup D] [NormedSpace ℝ D]
--     [NormedAddCommGroup E] [NormedSpace ℝ E]
--     [NormedAddCommGroup F] [NormedSpace ℝ F]
--     [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] :
--     Module ℂ (𝓢(D, E) →L[ℝ] 𝓢(F, G)) := ContinuousLinearMap.module

/--
The Fréchet derivative of `vectorFourierIntegrand` with respect to `ξ`; Schwartz in `x`, linear in `dξ`.

The derivative with respect to `x` can be obtained using `SchwartzMap.fderivCLM`.
-/
noncomputable def fderivCLM_vectorFourierIntegrand (ξ : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F) :=
  -((2 * π * I) • (vectorFourierIntegrand ξ).comp (innerSL_smul (F := F)))

lemma fderivCLM_vectorFourierIntegrand_apply {f : 𝓢(E, F)} {x ξ dξ : E} :
    fderivCLM_vectorFourierIntegrand ξ f x dξ =
    -((2 * π * I * ⟪x, dξ⟫) • vectorFourierIntegrand ξ f x) := by
  simp [fderivCLM_vectorFourierIntegrand]
  rw [neg_apply, smul_apply]  -- TODO: Can't use `simp` or `simp only` instead of `rw`?
  simp
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
  rw [fderivCLM_vectorFourierIntegrand_apply, vectorFourierIntegrand_apply]
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

-- Need help for `Continuous.aestronglyMeasurable` in `hasFDerivAt_integral_vectorFourierIntegrand`.
instance {α : Type*} [TopologicalSpace α] : SecondCountableTopologyEither E α := secondCountableTopologyEither_of_left E α

/-- The derivative of the Fourier integral. -/
lemma hasFDerivAt_integral_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ₀ : E} :
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

lemma fderiv_integral_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => ∫ x, vectorFourierIntegrand ξ f x) ξ =
    ∫ x, fderiv ℝ (fun ξ => vectorFourierIntegrand ξ f x) ξ :=
  hasFDerivAt_integral_vectorFourierIntegrand.fderiv

/-- Leibniz integral rule for Fourier integrand in terms of CLMs. -/
lemma hasFDerivAt_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ₀ : E} :
    HasFDerivAt (fun ξ => integralCLM (vectorFourierIntegrand ξ f))
      (integralCLM (fderivCLM_vectorFourierIntegrand ξ₀ f)) ξ₀ := by
  simp_rw [integralCLM_apply]
  simp_rw [← fderiv_vectorFourierIntegrand]
  exact hasFDerivAt_integral_vectorFourierIntegrand

lemma fderiv_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ =
    integralCLM (fderivCLM_vectorFourierIntegrand ξ f) :=
  hasFDerivAt_integralCLM_vectorFourierIntegrand.fderiv

lemma fderiv_integralCLM_eq_integralCLM_innerSL_smul {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ =
    -((2 * π * I) • integralCLM ((vectorFourierIntegrand ξ) (innerSL_smul f))) := by
  rw [fderiv_integralCLM_vectorFourierIntegrand]
  rw [fderivCLM_vectorFourierIntegrand]
  simp [integralCLM_neg_apply, integralCLM_smul_apply]

lemma differentiable_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Differentiable ℝ fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  fun _ => hasFDerivAt_integralCLM_vectorFourierIntegrand.differentiableAt

lemma continuous_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Continuous fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  -- TODO: Is this an upside-down way to prove this?
  -- Could use `integralCLM.continuous.comp`; show that `hasTemperateGrowth_smul` is continuous with Schwartz topology?
  differentiable_integralCLM_vectorFourierIntegrand.continuous

-- `d[exp(-2 π I ⟪x, ξ⟫)]`
-- `d[-2 π I ⟪x, ξ⟫] exp(-(2 π I ⟪x, ξ⟫))`
-- `-2 π I ⟪dx, ξ⟫ exp(-(2 π I ⟪x, ξ⟫))`

lemma fderiv_fourierChar_inner {x ξ dξ : E} :
    fderiv ℝ (fun ξ => Real.fourierChar[-⟪x, ξ⟫]) ξ dξ =
    -((2 * π * I) * ⟪x, dξ⟫ * Real.fourierChar[-⟪x, ξ⟫]) := by
  change fderiv ℝ ((fun u : ℝ => Real.fourierChar[u]) ∘ (fun ξ : E => -⟪x, ξ⟫)) ξ dξ = _
  rw [fderiv.comp]
  rotate_left
  . exact (Real.contDiff_fourierChar.differentiable le_top).differentiableAt
  . exact (DifferentiableAt.inner ℝ (differentiableAt_const x) differentiableAt_id).neg
  rw [ContinuousLinearMap.comp_apply]
  simp
  rw [fderiv_inner_apply ℝ (differentiableAt_const x) differentiableAt_id']
  simp [Real.fderiv_fourierChar]
  ring_nf

-- `d^n[ exp(-2 π I ⟪x, ξ⟫) ]`
-- `= -2 π I ⟪x, dξ_0⟫ d^(n-1)[ exp(-2 π I ⟪x, ξ⟫) ]`
-- `= (-2 π I)^2 ⟪x, dξ 0⟫ ⟪x, dξ 1⟫ d^(n-2)[ exp(-2 π I ⟪x, ξ⟫) ]`
-- `= (-2 π I)^n ⟪x, dξ 0⟫ ... ⟪x, dξ (n-1)⟫ exp(-2 π I ⟪x, ξ⟫)`

-- `‖d^n[exp(-2 π I ⟪x, ξ⟫)] • f x‖`
-- `= ‖(-2 π I)^n ⟪x, dξ 0⟫ ... ⟪x, dξ (n-1)⟫ exp(-2 π I ⟪x, ξ⟫) • f x‖`
-- `= (2 π)^n ‖⟪x, dξ 0⟫ ... ⟪x, dξ (n-1)⟫ exp(-2 π I ⟪x, ξ⟫) • f x‖`

-- `‖ ∫ x, exp(-2 π I ⟪x, ξ⟫) • f x ‖`
-- ...

-- Is this useful for proving bound?
lemma norm_integral_vectorFourierIntegrand_le {f : 𝓢(E, F)} {ξ : E} :
    ‖∫ x, vectorFourierIntegrand ξ f x‖ ≤ ∫ x, ‖f x‖ := by
  refine norm_integral_le_of_norm_le f.integrable.norm ?_
  refine Filter.eventually_of_forall ?_
  intro x
  simp [vectorFourierIntegrand_apply, norm_smul]

lemma norm_integralCLM_vectorFourierIntegrand_le {f : 𝓢(E, F)} {ξ : E} :
    ‖integralCLM (vectorFourierIntegrand ξ f)‖ ≤ ∫ x, ‖f x‖ := by
  rw [integralCLM_apply]
  exact norm_integral_vectorFourierIntegrand_le

/-- Integration by parts for the Fourier integral of the derivative of a Schwartz function on ℝ. -/
lemma intervalIntegral_integrand_deriv_sub_smul_integrand {f : 𝓢(ℝ, F)} {ξ : ℝ} {a b : ℝ} :
    (∫ (x : ℝ) in a..b, realFourierIntegrand ξ (derivCLM ℝ f) x - ((2 * π * I * ξ) • realFourierIntegrand ξ f x)) =
      realFourierIntegrand ξ f b - realFourierIntegrand ξ f a := by
  have := intervalIntegral.integral_deriv_smul_eq_sub (a := a) (b := b)
    (u := (fun x => Real.fourierChar[-(x * ξ)]))
    (v := (fun x => f x))
    (u' := (fun x => (-ξ) • (2 * π * I * Real.fourierChar[-(x * ξ)])))
    (v' := (fun x => deriv f x))
    (fun x _ => HasDerivAt.comp_of_tower x Real.hasDerivAt_fourierChar (hasDerivAt_mul_const ξ).neg)
    (fun x _ => f.differentiableAt.hasDerivAt) ?_ ?_
  rotate_left
  . refine Continuous.continuousOn ?_
    refine ((continuous_const).mul ?_).const_smul (-ξ)
    exact (continuous_mul_right ξ).neg.realFourierChar
  . refine Continuous.continuousOn ?_
    simp_rw [← derivCLM_apply ℝ]
    exact (derivCLM ℝ f).continuous
  simp at this
  conv => rhs; simp [realFourierIntegrand_apply]
  rw [← this]
  clear this
  congr
  funext x
  simp [realFourierIntegrand_apply, derivCLM_apply]
  simp [smul_smul, neg_add_eq_sub]
  ring_nf

-- TODO: Should be possible to obtain `Tendsto f atTop (nhds 0)` from `Integrable f` and `Continuous f`?
-- For now, prove it for the specific case that we have instead.

/-- The Fourier integral of the derivative of a Schwartz function on ℝ. -/
lemma realFourierIntegral_deriv {f : 𝓢(ℝ, F)} {ξ : ℝ} :
    𝓕 (fun x => deriv (fun y => f y) x) ξ = (2 * π * I * ξ) • 𝓕 (fun x => f x) ξ := by
  -- Replace `fourierChar[_]` with `realFourierIntegrand`; easy to show integrable and differentiable.
  change ∫ x, realFourierIntegrand ξ (derivCLM ℝ f) x = (2 * π * I * ξ) • ∫ x : ℝ, realFourierIntegrand ξ f x
  rw [← sub_eq_zero]
  rw [← integral_smul]
  rw [← integral_sub (integrable _)]
  swap
  . exact (integrable _).smul _  -- This can't be put inside the rewrite?

  have h_cover : AECover volume Filter.atTop (fun i => Set.Ioc (-i) i : ℕ → Set ℝ)
  . refine aecover_Ioc ?_ ?_ <;> simp [Filter.tendsto_neg_atBot_iff, tendsto_nat_cast_atTop_atTop]

  refine AECover.integral_eq_of_tendsto h_cover _ ?_ ?_
  . refine Integrable.sub ?_ ?_
    . have := integrable (realFourierIntegrand ξ (derivCLM ℝ f))
      simp only [realFourierIntegrand_apply, derivCLM_apply] at this
      exact this
    . have := integrable ((2 * π * I * ξ) • (realFourierIntegrand ξ f))
      simp only [smul_apply, smul_eq_mul, realFourierIntegrand_apply] at this
      exact this
  simp_rw [← intervalIntegral.integral_of_le (neg_le_self_iff.mpr (Nat.cast_nonneg _))]
  simp_rw [intervalIntegral_integrand_deriv_sub_smul_integrand]

  rw [← sub_zero 0]
  refine Filter.Tendsto.sub ?_ ?_
  . refine Filter.Tendsto.comp ?_ tendsto_nat_cast_atTop_atTop
    exact tendsto_atTop_zero_real (realFourierIntegrand ξ f)
  . change Filter.Tendsto ((fun x => realFourierIntegrand ξ f (-x)) ∘ (fun n => n : ℕ → ℝ)) Filter.atTop (nhds 0)
    refine Filter.Tendsto.comp ?_ tendsto_nat_cast_atTop_atTop
    simp_rw [← compNegEquiv_apply]
    exact tendsto_atTop_zero_real (compNegEquiv (realFourierIntegrand ξ f))


-- Define some compositions that may be useful for taking partial derivative.
section CompCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Simpler case than `compAddSingleCLM`; just translation.
def compConstAddCLM (b : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  compCLM ℝ (g := fun x => b + x)
    (Function.hasTemperateGrowth_id'.const_add b)
    (by
      refine ⟨1, 1 + ‖b‖, ?_⟩
      intro y
      simp [add_mul, mul_add, ← add_assoc]
      refine le_trans (norm_le_add_norm_add y b) ?_
      rw [add_comm y]
      rw [add_comm ‖b + y‖ ‖b‖]
      refine le_add_of_le_of_nonneg ?_ (mul_nonneg ?_ ?_) <;> simp)

lemma compConstAddCLM_apply {b u : ∀ i, M i} {f : 𝓢((i : ι) → M i, F)} :
    compConstAddCLM b f u = f (b + u) := rfl

-- def compSMulRightCLM {v : E} (hv : ‖v‖ ≠ 0) : 𝓢(E, F) →L[ℝ] 𝓢(ℝ, F) :=
--   compCLM ℝ (g := fun x => x • v)
--     (Function.hasTemperateGrowth_id'.smul_const v)
--     (by
--       refine ⟨1, ‖v‖⁻¹, ?_⟩
--       intro x
--       simp
--       rw [inv_mul_eq_div]
--       rw [le_div_iff (lt_of_le_of_ne' (norm_nonneg _) hv)]
--       simp [norm_smul])

-- lemma compSMulRightCLM_apply {v : E} (hv : ‖v‖ ≠ 0) {f : 𝓢(E, F)} {x : ℝ} :
--     compSMulRightCLM hv f x = f (x • v) := rfl

end CompCLM

def compSingleCLM (i : ι) : 𝓢((i : ι) → M i, F) →L[ℝ] 𝓢(M i, F) :=
  compCLM ℝ (g := fun x => Pi.single i x)
    (Function.hasTemperateGrowth_clm (ContinuousLinearMap.single (R := ℝ) (M := M) i))
    ⟨1, 1, fun x => by simp⟩

lemma compSingleCLM_apply {i : ι} {f : 𝓢((i : ι) → M i, F)} {u : M i} :
    compSingleCLM i f u = f (Pi.single i u) := rfl

-- TODO: Not sure whether it's useful to have f as a function of `EuclideanSpace`...
-- Note that it changes the definition of norm compared to pi.

lemma realVectorFourierIntegral_pderivCLM_single {i : ι} {f : 𝓢(ι → ℝ, F)} {ξ : ι → ℝ} :
    𝓕ₙ (pderivCLM ℝ (Pi.single i 1) f) ξ = (2 * π * I * ξ i) • 𝓕ₙ f ξ := by
  rw [RealVectorFourier.fourierIntegral_l2inner_apply]
  -- Break up the integral.
  rw [integral_piSplitAt_right i]
  swap
  . simp_rw [← realVectorFourierIntegrand_apply]  -- TODO: Extract to lemma without rw?
    exact integrable _
  -- Split the sum.
  have h_mem (j) : j ∈ Finset.univ \ {i} ↔ j ≠ i := by simp
  conv => lhs; simp only [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  simp only [dite_true, Finset.sum_subtype _ h_mem]
  simp [Finset.sum_ite]
  conv => lhs; arg 2; intro x; arg 2; intro u; lhs; rw [← smul_eq_mul]
  simp only [smul_assoc]
  simp only [integral_smul]

  simp only [← deriv_comp_update (f.differentiableAt)]
  simp only [Equiv.piSplitAt_symm_apply (j := i), dite_true]
  simp only [Function.update_piSplitAt_symm]
  conv =>
    lhs; arg 2; intro x; rhs
    -- Express as the derivative of a Schwartz function.
    conv =>
      arg 2; intro y; rhs; arg 1; intro u
      rw [← Equiv.piSplitAt_symm_zero_add_single]
      rw [← compConstAddCLM_apply]
      rw [← compSingleCLM_apply]
    -- Rewrite using theorem for scalar Fourier transform.
    rw [← Real.fourierIntegral_def]
    rw [realFourierIntegral_deriv]

  simp only [compConstAddCLM_apply, compSingleCLM_apply]
  conv => lhs; arg 2; intro x; rw [smul_comm]
  rw [integral_smul]
  refine congrArg _ ?_  -- More idiomatic way to do this?
  simp only [Real.fourierIntegral_def]
  simp only [← integral_smul]
  simp only [smul_smul]

  rw [RealVectorFourier.fourierIntegral_l2inner_apply]
  rw [integral_piSplitAt_right i]
  swap
  . simp only [← realVectorFourierIntegrand_apply]
    exact integrable _
  refine congrArg _ ?_
  ext x
  refine congrArg _ ?_
  ext u
  congr
  . rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
    simp only [Finset.sum_subtype _ h_mem]
    simp [Finset.sum_ite]
  . rw [Equiv.piSplitAt_symm_zero_add_single]


lemma vectorFourierIntegral_pderivCLM_single_euclidean {i : ι} {f : 𝓢(EuclideanSpace ℝ ι, F)} {ξ : EuclideanSpace ℝ ι} :
    𝓕ᵥ (pderivCLM ℝ (EuclideanSpace.single i 1) f) ξ = (2 * π * I * ξ i) • 𝓕ᵥ f ξ := by
  rw [RealVectorFourier.fourierIntegral_euclidean_eq_fourierIntegral_l2inner]
  rw [RealVectorFourier.fourierIntegral_euclidean_eq_fourierIntegral_l2inner]
  have := realVectorFourierIntegral_pderivCLM_single (i := i)
    (f := compEquiv (EuclideanSpace.equiv ι ℝ).symm f) (ξ := (EuclideanSpace.equiv ι ℝ) ξ)
  -- Use equivalence to modify derivative as well.
  conv at this =>
    lhs; arg 4; intro x
    simp
    conv => arg 1; arg 2; intro y; simp
    change fderiv ℝ (f ∘ ⇑(EuclideanSpace.equiv ι ℝ).symm) x (Pi.single i 1)
    rw [ContinuousLinearEquiv.comp_right_fderiv]
    rw [ContinuousLinearMap.comp_apply]
  exact this

lemma vectorFourierIntegral_pderivCLM_single_ofOrthonormalBasis (v : OrthonormalBasis ι ℝ E) {i : ι} {f : 𝓢(E, F)} {ξ : E} :
    𝓕ᵥ (pderivCLM ℝ (v.repr.symm (Pi.single i 1)) f) ξ = (2 * π * I * (v.repr ξ) i) • 𝓕ᵥ f ξ := by
  rw [RealVectorFourier.fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis v]
  rw [RealVectorFourier.fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis v]
  have := vectorFourierIntegral_pderivCLM_single_euclidean (i := i)
    (f := compEquiv v.repr.symm f) (ξ := v.repr ξ)
  conv at this =>
    lhs; arg 4; intro x
    simp
    conv => arg 1; arg 2; intro y; simp
    change fderiv ℝ (f ∘ ⇑v.repr.toContinuousLinearEquiv.symm) x (EuclideanSpace.single i 1)
    rw [ContinuousLinearEquiv.comp_right_fderiv]
    simp
  exact this

-- TODO: Implement directional derivative (not just canonical directions).
-- Use `proj` and `ker`?

end SchwartzMap  -- namespace

end Fourier

end NoTypeInduction


-- TODO: Rewrite avoiding induction over type.
section TypeInduction

universe u
variable {E F : Type u}  -- Ensure that `E →L[ℝ] F` is in the same universe as `F`.

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
variable [CompleteSpace F]

namespace SchwartzMap

/-- The Fourier integral of a Schwartz map is smooth. -/
theorem contDiff_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} : ContDiff ℝ ⊤ fun ξ => integralCLM (vectorFourierIntegrand ξ f) := by
  rw [contDiff_top]
  intro n
  induction n generalizing F with
  | zero =>
    simp
    exact continuous_integralCLM_vectorFourierIntegrand
  | succ n h_ind =>
    rw [contDiff_succ_iff_fderiv]
    refine ⟨differentiable_integralCLM_vectorFourierIntegrand, ?_⟩
    simp_rw [fderiv_integralCLM_eq_integralCLM_innerSL_smul]
    refine ContDiff.neg ?_
    refine ContDiff.const_smul (2 * π * I : ℂ) ?_
    -- Need `E →L[ℝ] F` to be in same universe as `F` to apply induction.
    exact h_ind

/-- The Fourier integral of a Schwartz map is smooth. -/
theorem contDiff_fourierIntegral {f : 𝓢(E, F)} : ContDiff ℝ ⊤ fun ξ => ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x := by
  simp_rw [← vectorFourierIntegrand_apply]
  simp_rw [← integralCLM_apply]
  exact contDiff_integralCLM_vectorFourierIntegrand

lemma norm_iteratedFDeriv_integralCLM_fourierIntegrand_le {n : ℕ} {f : 𝓢(E, F)} {ξ : E} :
    ‖iteratedFDeriv ℝ n (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ‖ ≤ (2 * π) ^ n * ∫ x, ‖x‖ ^ n * ‖f x‖ := by
  induction n generalizing F with
  | zero =>
    simp
    exact norm_integralCLM_vectorFourierIntegrand_le
  | succ n h_ind =>
    simp [iteratedFDeriv_succ_eq_comp_right]
    simp_rw [fderiv_integralCLM_eq_integralCLM_innerSL_smul]
    rw [iteratedFDeriv_neg_apply']
    rw [iteratedFDeriv_const_smul_apply']
    swap
    . exact contDiff_integralCLM_vectorFourierIntegrand.of_le le_top
    -- simp
    -- rw [norm_neg]  -- Assistance needed?
    rw [norm_neg (E := ContinuousMultilinearMap _ _ _)]
    rw [norm_smul]
    simp
    rw [abs_of_pos Real.pi_pos]
    rw [pow_succ]
    rw [mul_assoc (2 * π)]
    refine mul_le_mul_of_nonneg_left ?_ (by simp [Real.pi_pos.le])
    specialize h_ind (f := innerSL_smul f)
    refine le_trans h_ind ?_
    refine mul_le_mul_of_nonneg_left ?_ (by simp [Real.pi_pos.le])
    refine integral_mono integrable_norm_pow_mul_norm integrable_norm_pow_mul_norm ?_
    intro x
    simp
    rw [pow_succ']
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    rw [ContinuousLinearMap.op_norm_le_iff]
    swap
    . refine mul_nonneg ?_ ?_ <;> simp
    intro y
    rw [innerSL_smul_apply]
    simp_rw [norm_smul]
    repeat rw [mul_comm _ ‖f x‖]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    exact norm_inner_le_norm x y

/-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
noncomputable def realFourierIntegralCLM : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) :=
  mkCLM (fun f ξ => ∫ x, Real.fourierChar[-(x * ξ)] • f x)
    (fun φ θ ξ => by
      simp [← realFourierIntegrand_apply]
      rw [integral_add (integrable _) (integrable _)])
    (fun c φ ξ => by
      simp [smul_comm _ c]
      rw [integral_smul])
    (fun φ => sorry)
    (fun m => by
      simp only [← realFourierIntegrand_apply]
      -- simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      sorry)

/-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
noncomputable def vectorFourierIntegralCLM {r : ℕ} [hr : Fact (FiniteDimensional.finrank ℝ E < r)] : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  mkCLM (fun f ξ => ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x)
    (fun φ θ ξ => by
      simp [← vectorFourierIntegrand_apply]
      rw [integral_add (integrable _) (integrable _)])
    (fun c φ ξ => by
      simp [smul_comm _ c]
      rw [integral_smul])
    (fun φ => contDiff_fourierIntegral)
    (fun m => by
      simp [← vectorFourierIntegrand_apply, ← integralCLM_apply]
      -- simp_rw [integralCLM_eq_L1_integral]
      have k' := 5
      have n' := 7
      have C' := π
      use Finset.Iic (k', n')
      use C'
      refine ⟨sorry, ?_⟩
      intro φ ξ
      have := tendsto_integral_exp_inner_smul_cocompact φ
      -- Have that the integral tends to zero at infinity and is ContDiff.
      -- However, we still need to show that it decays faster than polynomial.
      -- Need to use the fact that the Fourier transform of the derivative has a 1/ξ^n term?
      have hφ := φ.decay'
      rcases m with ⟨k, n⟩
      simp
      refine le_trans (mul_le_mul_of_nonneg_left norm_iteratedFDeriv_integralCLM_fourierIntegrand_le (by simp)) ?_
      sorry)

end SchwartzMap  -- namespace

end TypeInduction
