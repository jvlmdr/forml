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
import ForML.ContinuousMultilinearMap
import ForML.MultilinearIntegral
import ForML.SchwartzDeriv
import ForML.SchwartzEquiv
import ForML.SchwartzLp
import ForML.Trigonometric
import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace Complex FourierTransform RealInnerProductSpace
open scoped BigOperators Real

attribute [-simp] Matrix.zero_empty
attribute [-simp] ofAdd_neg

variable {ι 𝕜 𝕜' R : Type*} {M : ι → Type*} {D E F G : Type*}

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [Fintype ι] {z : G} {x : 𝕜}

#check ContinuousMultilinearMap.mkPiField 𝕜 ι z

#check ContinuousMultilinearMap.mkPiField 𝕜 ι z (fun _ ↦ x)

-- theorem hasFTaylorSeriesUpTo_mkPiField {n : ℕ} {z : G} {x : E} :
--     HasFTaylorSeriesUpTo n (fun y ↦ ContinuousMultilinearMap.mkPiField 𝕜 (Fin n) z y)
--       (fun x n ↦ ContinuousMultilinearMap.mkPiField 𝕜 (Fin n) z) := by
--   sorry

-- theorem norm_iteratedFDeriv_mkPiField_le [Fintype ι] {f : E → G} {x : E} :
--     ‖iteratedFDeriv 𝕜 n (fun x ↦ ContinuousMultilinearMap.mkPiField 𝕜 ι (f x)) x‖ ≤
--       C := by
--   rw [ContinuousMultilinearMap.op_norm_le_iff _ sorry]
--   intro m
--   induction n generalizing f with
--   | zero =>
--     simp
--     -- `‖f x‖ ≤ C`
--     sorry
--   | succ n IH =>
--     -- rw [← norm_fderiv_iteratedFDeriv]
--     rw [iteratedFDeriv_succ_apply_left]
--     rw [← fderiv_continuousMultilinearMap_apply_comm]
--     swap
--     · sorry
--     rw [Fin.prod_univ_succ]
--     rw [mul_comm ‖m 0‖]
--     rw [← mul_assoc]
--     suffices :
--         ‖fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n (fun x ↦ ContinuousMultilinearMap.mkPiField 𝕜 ι (f x)) y (Fin.tail m)) x‖ ≤
--           C * ∏ i : Fin n, ‖m (Fin.succ i)‖
--     · rw [ContinuousLinearMap.op_norm_le_iff] at this
--       · exact this (m 0)
--       · refine mul_nonneg ?_ ?_
--         · sorry
--         · simp [Finset.prod_nonneg]
--     sorry

end

section Continuous

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Real version of `VectorFourier.fourierIntegral_continuous`. -/
lemma Real.fourierIntegral_continuous {f : ℝ → F} (hf : Integrable f) :
    Continuous (Real.fourierIntegral f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_mul) hf

-- lemma ContDiff.ofReal {f : ℝ → ℝ} {n : ℕ∞} (hf : ContDiff ℝ n f) :
--     ContDiff ℝ n (fun x => (f x : ℂ)) :=
--   ofRealCLM.contDiff.comp hf

end Continuous

-- section IteratedFDeriv

-- variable [NontriviallyNormedField 𝕜]
-- variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
-- variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- lemma iteratedFDeriv_iteratedFDeriv_apply {n m : ℕ} {f : E → F} {x : E} {u : Fin n → E} {v : Fin m → E} :
--     iteratedFDeriv 𝕜 n (iteratedFDeriv 𝕜 m f) x u v = iteratedFDeriv 𝕜 (n + m) f x (Fin.append u v) := by
--   induction n generalizing x with
--   | zero =>
--     simp
--     -- rw [zero_add]
--     sorry  -- Cannot rw/simp/conv; because type depends on `n`?
--   | succ n IH =>
--     rw [iteratedFDeriv_succ_apply_left]
--     rw [← fderiv_continuousMultilinearMap_apply_comm sorry]
--     rw [← fderiv_continuousMultilinearMap_apply_comm sorry]
--     -- conv => lhs; arg 1; arg 2; intro y; rw [IH]
--     -- rw [Nat.succ_add]
--     -- rw [iteratedFDeriv_succ_apply_left]
--     sorry

-- -- lemma norm_iteratedFDeriv_iteratedFDeriv {n m : ℕ} {f : E → F} {x : E} :
-- --     ‖iteratedFDeriv 𝕜 n (iteratedFDeriv 𝕜 m f) x‖ ≤ ‖iteratedFDeriv 𝕜 (n + m) f x‖ := by
-- --   induction n with
-- --   | zero =>
-- --     simp
-- --     rw [zero_add]
-- --   | succ n IH =>
-- --     -- I don't think induction will help with this...
-- --     sorry

-- end IteratedFDeriv

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

lemma Function.hasTemperateGrowth_prod_univ_inner_const [Fintype ι] (w : ι → E) :
    HasTemperateGrowth (∏ i, ⟪·, w i⟫) :=
  HasTemperateGrowth.prod Finset.univ fun i _ ↦
    hasTemperateGrowth_id.inner (hasTemperateGrowth_const (w i))

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

@[simp]
lemma norm_vectorFourierIntegrand_apply {f : 𝓢(E, F)} {ξ x : E} :
    ‖vectorFourierIntegrand ξ f x‖ = ‖f x‖ := by
  simp [vectorFourierIntegrand_apply, norm_smul]

-- For `HasFiniteIntegral`.
@[simp]
lemma nnnorm_vectorFourierIntegrand_apply {f : 𝓢(E, F)} {ξ x : E} :
    ‖vectorFourierIntegrand ξ f x‖₊ = ‖f x‖₊ :=
  NNReal.coe_injective (by simp)

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

-- -- Give hint to find instance for `(c : ℂ) • f` in `fderivVectorFourierIntegrandCLM`.
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
noncomputable def fderivVectorFourierIntegrandCLM (ξ : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F) :=
  -((2 * π * I) • (vectorFourierIntegrand ξ).comp (innerSL_smul (F := F)))

lemma fderivVectorFourierIntegrandCLM_apply {f : 𝓢(E, F)} {x ξ dξ : E} :
    fderivVectorFourierIntegrandCLM ξ f x dξ =
    -((2 * π * I) • ⟪x, dξ⟫ • vectorFourierIntegrand ξ f x) := by
  simp only [fderivVectorFourierIntegrandCLM]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    neg_apply (F := E →L[ℝ] F), smul_apply (F := E →L[ℝ] F)]
  refine congrArg _ (congrArg _ ?_)
  simp only [vectorFourierIntegrand_apply]
  rw [ContinuousLinearMap.smul_apply, innerSL_smul_apply, smul_comm]

/-- The Fréchet derivative of `vectorFourierIntegrand` with respect to `ξ`. -/
lemma fderiv_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ x : E} :
    fderiv ℝ (fun ξ' => vectorFourierIntegrand ξ' f x) ξ =
    fderivVectorFourierIntegrandCLM ξ f x := by
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
  rw [fderivVectorFourierIntegrandCLM_apply, vectorFourierIntegrand_apply]
  simp
  rw [smul_comm]
  simp [← smul_assoc]
  ring_nf

-- TODO: More idiomatic to define `HasFDerivAt` before `fderiv`?
lemma hasFDerivAt_vectorFourierIntegrand {f : 𝓢(E, F)} {x ξ₀ : E} :
    HasFDerivAt (fun ξ : E => vectorFourierIntegrand ξ f x) (fderivVectorFourierIntegrandCLM ξ₀ f x) ξ₀ :=
  HasFDerivAt.congr_fderiv
    differentiable_vectorFourierIntegrand.differentiableAt.hasFDerivAt
    fderiv_vectorFourierIntegrand

-- Need to provide assistance?
-- noncomputable instance : SeminormedAddCommGroup (E →L[ℝ] ℂ) := ContinuousLinearMap.toSeminormedAddCommGroup
-- noncomputable instance : NormedSpace ℝ (E →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace

/-- Uses `‖cexp (_ • I)‖ = 1` to obtain norm independent of `ξ`. -/
lemma norm_fderivVectorFourierIntegrandCLM {f : 𝓢(E, F)} {ξ x : E} :
    ‖fderivVectorFourierIntegrandCLM ξ f x‖ = 2 * π * ‖innerSL_smul f x‖ := by
    -- ‖fderiv ℝ (fun ξ => vectorFourierIntegrand ξ f x) ξ‖ = 2 * π * ‖innerSL_smul f x‖ := by
  suffices : ‖fderivVectorFourierIntegrandCLM ξ f x‖ = ‖innerSL_smul ((2 * π) • f) x‖
  . simpa [norm_smul, _root_.abs_of_nonneg Real.pi_pos.le] using this
  simp only [ContinuousLinearMap.norm_def]
  simp only [fderivVectorFourierIntegrandCLM_apply, vectorFourierIntegrand_apply, innerSL_smul_apply]
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
instance {α : Type*} [TopologicalSpace α] : SecondCountableTopologyEither E α :=
  secondCountableTopologyEither_of_left E α

-- TODO: Could be unidiomatic use of `HasFDerivAt` (uses `fderiv` rather than `f'`).
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
    rw [norm_fderivVectorFourierIntegrandCLM]
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
      (integralCLM (fderivVectorFourierIntegrandCLM ξ₀ f)) ξ₀ := by
  simp_rw [integralCLM_apply]
  simp_rw [← fderiv_vectorFourierIntegrand]
  exact hasFDerivAt_integral_vectorFourierIntegrand

lemma fderiv_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ =
    integralCLM (fderivVectorFourierIntegrandCLM ξ f) :=
  hasFDerivAt_integralCLM_vectorFourierIntegrand.fderiv

lemma fderiv_integralCLM_eq_integralCLM_innerSL_smul {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ => integralCLM (vectorFourierIntegrand ξ f)) ξ =
    -((2 * π * I) • integralCLM ((vectorFourierIntegrand ξ) (innerSL_smul f))) := by
  rw [fderiv_integralCLM_vectorFourierIntegrand]
  rw [fderivVectorFourierIntegrandCLM]
  simp [integralCLM_neg_apply, integralCLM_smul_apply]

lemma differentiable_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Differentiable ℝ fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  fun _ => hasFDerivAt_integralCLM_vectorFourierIntegrand.differentiableAt

lemma continuous_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Continuous fun ξ => integralCLM (vectorFourierIntegrand ξ f) :=
  -- TODO: Is this an upside-down way to prove this?
  -- Could use `integralCLM.continuous.comp`; show that `hasTemperateGrowth_smul` is continuous with Schwartz topology?
  differentiable_integralCLM_vectorFourierIntegrand.continuous

lemma hasFDerivAt_integral_vectorFourierIntegrand' {f : 𝓢(E, F)} {ξ₀ : E} :
    HasFDerivAt (fun ξ => ∫ x, vectorFourierIntegrand ξ f x)
      (-((2 * π * I) • ∫ x, vectorFourierIntegrand ξ₀ (innerSL_smul f) x)) ξ₀ := by
  refine hasFDerivAt_integral_vectorFourierIntegrand.congr_fderiv ?_
  simp only [fderiv_vectorFourierIntegrand]
  rw [← neg_smul, ← integral_smul]
  refine congrArg _ ?_
  funext x
  ext m
  rw [fderivVectorFourierIntegrandCLM_apply, ContinuousLinearMap.smul_apply, ← neg_smul]
  refine congrArg _ ?_
  simp only [vectorFourierIntegrand_apply, ContinuousLinearMap.smul_apply, innerSL_smul_apply]
  rw [smul_comm]

lemma fderiv_integral_vectorFourierIntegrand' {f : 𝓢(E, F)} {ξ : E} :
    fderiv ℝ (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) ξ =
      -((2 * π * I) • ∫ x, vectorFourierIntegrand ξ (innerSL_smul f) x) :=
  hasFDerivAt_integral_vectorFourierIntegrand'.fderiv

lemma differentiable_integral_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Differentiable ℝ fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x :=
  fun _ ↦ hasFDerivAt_integral_vectorFourierIntegrand'.differentiableAt

lemma continuous_integral_vectorFourierIntegrand {f : 𝓢(E, F)} :
    Continuous fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x :=
  -- TODO: Is this an upside-down way to prove this?
  -- Could use `integralCLM.continuous.comp`; show that `hasTemperateGrowth_smul` is continuous with Schwartz topology?
  differentiable_integral_vectorFourierIntegrand.continuous

-- theorem ContinuousMultilinearMap.smul_mkPiField [Fintype ι] (c : 𝕜) (z : F) (m : ι → 𝕜) :
--     ContinuousMultilinearMap.mkPiField 𝕜 ι z m =
--       ContinuousMultilinearMap.mkPiField 𝕜 ι (1 : 𝕜) m • z := by
--   sorry

-- Anything to gain from `FormalMultilinearSeries.compContinuousLinearMap`?
-- variable {f : 𝓢(E, F)} {ξ : E}


-- noncomputable def SchwartzMap.mkPiField (ι : Type*) [Fintype ι] (f : 𝓢(E, F)) :
--     𝓢(E, ContinuousMultilinearMap ℝ (fun _ : ι ↦ ℝ) F) where
--   toFun x := ContinuousMultilinearMap.mkPiField ℝ ι (f x)
--   smooth' := by
--     sorry
--   decay' := by
--     intro k n
--     -- have ⟨C, hC⟩ := f.decay' k n
--     induction n with
--     | zero =>
--       let ⟨C, hC⟩ := f.decay' k 0
--       use C
--       simpa using hC
--     | succ n IH =>
--       let ⟨C, hC⟩ := f.decay' k n.succ
--       have C' : ℝ := sorry
--       use C'
--       intro x
--       rw [iteratedFDeriv_succ_eq_comp_left]
--       sorry

-- theorem mkPiField_vectorFourierIntegrand {n : ℕ} {f : 𝓢(E, F)} {x ξ : E} :
--     ContinuousMultilinearMap.mkPiField ℝ (Fin n) (vectorFourierIntegrand ξ f x) =
--       (vectorFourierIntegrand ξ f x)


theorem hasFTaylorSeriesUpTo_integral_vectorFourierIntegrand {f : 𝓢(E, F)} :
    HasFTaylorSeriesUpTo ⊤ (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) fun ξ n ↦
      (-(2 * π * I)) ^ n • ∫ x, (ContinuousMultilinearMap.mkPiField ℝ (Fin n)
        (vectorFourierIntegrand ξ f x)).compContinuousLinearMap fun _ ↦ innerSL ℝ x := by
  rw [hasFTaylorSeriesUpTo_top_iff]
  intro n
  induction n with
  | zero =>
    rw [ENat.coe_zero, hasFTaylorSeriesUpTo_zero_iff]
    refine And.intro ?_ ?_
    · exact continuous_integral_vectorFourierIntegrand
    · intro ξ
      simp
      -- Requires integral of `ContinuousMultilinearMap` over `E`...
      sorry
  | succ n IH =>
    rw [← hasFTaylorSeriesUpToOn_univ_iff, Nat.cast_succ]
    rw [hasFTaylorSeriesUpToOn_succ_iff_left]
    refine And.intro ?_ ?_
    · rw [hasFTaylorSeriesUpToOn_univ_iff]
      exact IH
    · refine And.intro ?_ ?_
      · intro ξ _
        sorry
      · rw [← continuous_iff_continuousOn_univ]
        refine Continuous.const_smul ?_ _
        -- To prove this using `continuous_integral_vectorFourierIntegrand`,
        -- we need to have a Schwartz map with `ContinuousMultilinearMap` value.
        sorry

-- theorem contDiff_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} :
--     ContDiff ℝ ⊤ fun ξ ↦ integralCLM (vectorFourierIntegrand ξ f) := by
--   rw [contDiff_top]
--   intro n
--   induction n with
--   | zero =>
--     rw [ENat.coe_zero, contDiff_zero]
--     exact continuous_integralCLM_vectorFourierIntegrand
--   | succ n IH =>
--     rw [contDiff_succ_iff_fderiv]
--     refine And.intro differentiable_integralCLM_vectorFourierIntegrand ?_
--     -- simp only [fderiv_integralCLM_vectorFourierIntegrand]
--     simp only [fderiv_integralCLM_eq_integralCLM_innerSL_smul]
--     refine (ContDiff.const_smul (2 * π * I) ?_).neg
--     -- specialize @IH (f := innerSL_smul f)
--     sorry

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

-- Is this useful for proving bound?
lemma norm_integral_vectorFourierIntegrand_le {f : 𝓢(E, F)} {ξ : E} :
    ‖∫ x, vectorFourierIntegrand ξ f x‖ ≤ ∫ x, ‖f x‖ := by
  refine norm_integral_le_of_norm_le f.integrable.norm ?_
  refine Filter.eventually_of_forall ?_
  intro x
  simp

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

lemma realintegral_vectorFourierIntegrand_pderivCLM_single {i : ι} {f : 𝓢(ι → ℝ, F)} {ξ : ι → ℝ} :
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


lemma integral_vectorFourierIntegrand_pderivCLM_single_euclidean {i : ι}
    {f : 𝓢(EuclideanSpace ℝ ι, F)} {ξ : EuclideanSpace ℝ ι} :
    𝓕ᵥ (pderivCLM ℝ (EuclideanSpace.single i 1) f) ξ = (2 * π * I * ξ i) • 𝓕ᵥ f ξ := by
  rw [RealVectorFourier.fourierIntegral_euclidean_eq_fourierIntegral_l2inner]
  rw [RealVectorFourier.fourierIntegral_euclidean_eq_fourierIntegral_l2inner]
  have := realintegral_vectorFourierIntegrand_pderivCLM_single (i := i)
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

lemma integral_vectorFourierIntegrand_pderivCLM_single_ofOrthonormalBasis
    (v : OrthonormalBasis ι ℝ E) {i : ι} {f : 𝓢(E, F)} {ξ : E} :
    𝓕ᵥ (pderivCLM ℝ (v.repr.symm (Pi.single i 1)) f) ξ = (2 * π * I * (v.repr ξ) i) • 𝓕ᵥ f ξ := by
  rw [RealVectorFourier.fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis v]
  rw [RealVectorFourier.fourierIntegral_eq_fourierIntegral_euclidean_ofOrthonormalBasis v]
  have := integral_vectorFourierIntegrand_pderivCLM_single_euclidean (i := i)
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

theorem iteratedFDeriv_vectorFourierIntegrand_apply {n : ℕ} {f : 𝓢(E, F)} {x ξ : E}
    {dξ : Fin n → E} :
    iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ dξ =
      (-(2 * π * I)) ^ n • (∏ i : Fin n, ⟪x, dξ i⟫) • vectorFourierIntegrand ξ f x := by
  induction n generalizing ξ with
  | zero => simp
  | succ n IH =>
    rw [iteratedFDeriv_succ_apply_left]
    rw [← fderiv_continuousMultilinearMap_apply_comm
      (contDiff_vectorFourierIntegrand.differentiable_iteratedFDeriv (WithTop.coe_lt_top _) _)]
    simp_rw [IH]
    -- Bring the power outside.
    rw [fderiv_const_smul ((differentiable_vectorFourierIntegrand _).const_smul _)]
    simp
    rw [pow_succ']
    rw [← smul_smul]
    refine congrArg _ ?_
    rw [smul_comm]
    -- Bring the product outside.
    rw [fderiv_const_smul (differentiable_vectorFourierIntegrand _)]
    simp [-neg_smul, -smul_neg]
    rw [Fin.prod_univ_succ]
    simp only [Fin.tail]
    rw [mul_comm ⟪x, dξ 0⟫]
    rw [← smul_smul]
    refine congrArg _ ?_
    rw [fderiv_vectorFourierIntegrand]
    rw [fderivVectorFourierIntegrandCLM_apply]
    rw [smul_comm]
    simp [← smul_smul]

-- For `iteratedFDeriv_integral_vectorFourierIntegrand_apply`,
-- for `contDiff_integralCLM_vectorFourierIntegrand`.
theorem iteratedFDeriv_vectorFourierIntegrand {n : ℕ} {f : 𝓢(E, F)} {x ξ : E} :
    iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ =
    (-(2 * π * I)) ^ n • (ContinuousMultilinearMap.mkPiField ℝ (Fin n)
      (vectorFourierIntegrand ξ f x)).compContinuousLinearMap (fun _ ↦ innerSL ℝ x) := by
  ext; simp [iteratedFDeriv_vectorFourierIntegrand_apply]

theorem integral_iteratedFDeriv_vectorFourierIntegrand_apply {n : ℕ} {f : 𝓢(E, F)} {ξ : E} {m : Fin n → E} :
    (∫ x, iteratedFDeriv ℝ n (vectorFourierIntegrand · f x) ξ m) =
      (-(2 * π * I)) ^ n • ∫ x, (∏ i, ⟪x, m i⟫) • vectorFourierIntegrand ξ f x := by
  simp only [iteratedFDeriv_vectorFourierIntegrand]
  simp [integral_smul]

theorem integral_iteratedFDeriv_vectorFourierIntegrand_apply' {n : ℕ} {f : 𝓢(E, F)} {ξ : E} {m : Fin n → E} :
    (∫ x, iteratedFDeriv ℝ n (vectorFourierIntegrand · f x) ξ) m =
      (-(2 * π * I)) ^ n • ∫ x, (∏ i, ⟪x, m i⟫) • vectorFourierIntegrand ξ f x := by
  simp only [iteratedFDeriv_vectorFourierIntegrand]
  rw [integral_smul, ContinuousMultilinearMap.smul_apply]
  refine congrArg _ ?_
  rw [← ContinuousMultilinearMap.integral_apply]
  · simp
  · refine And.intro ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      -- TODO: Extract this as a lemma if needed elsewhere.
      simp only [← ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      refine .clm_apply ?_ ?_
      · refine .comp (ContinuousMultilinearMap.continuous_compContinuousLinearMapL F) ?_
        exact continuous_pi (fun i ↦ ContinuousLinearMap.continuous (innerSL ℝ))
      · simp only [← ContinuousMultilinearMap.mkPiFieldL_apply]
        -- TODO: Add lemma `Continuous.mkPiField`?
        exact .clm_apply continuous_const (vectorFourierIntegrand ξ f).continuous
    · refine .mono (integrable_norm_pow_mul_norm n f).hasFiniteIntegral ?_
      refine Filter.eventually_of_forall ?_
      intro x
      refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
      simp [mul_comm ‖f x‖]

theorem norm_iteratedFDeriv_vectorFourierIntegrand_apply_le {n : ℕ} {f : 𝓢(E, F)} {x ξ : E} {m : Fin n → E} :
    ‖iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ m‖ ≤
      (2 * π) ^ n * ‖x‖ ^ n * ‖vectorFourierIntegrand ξ f x‖ * ∏ j : Fin n, ‖m j‖ := by
  simp only [iteratedFDeriv_vectorFourierIntegrand_apply, norm_smul]
  rw [mul_assoc (c := ∏ j : Fin n, ‖m j‖), mul_comm (b := ∏ j : Fin n, ‖m j‖)]
  simp only [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by simp)
  simp only [norm_pow, norm_neg, norm_mul, IsROrC.norm_ofNat, norm_eq_abs, abs_ofReal,
    _root_.abs_of_nonneg Real.pi_pos.le, abs_I, mul_one, norm_prod, Real.norm_eq_abs]
  simp only [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by simp [Real.pi_pos.le])
  refine le_trans (Finset.prod_le_prod (by simp) (fun j _ ↦ abs_real_inner_le_norm x (m j))) ?_
  rw [Finset.prod_mul_distrib]
  simp

theorem norm_iteratedFDeriv_vectorFourierIntegrand_le {n : ℕ} {f : 𝓢(E, F)} {x ξ : E} :
    ‖iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ‖ ≤
      (2 * π) ^ n * ‖x‖ ^ n * ‖vectorFourierIntegrand ξ f x‖ :=
  ContinuousMultilinearMap.op_norm_le_bound _
    (by refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp [Real.pi_pos.le])
    fun _ ↦ norm_iteratedFDeriv_vectorFourierIntegrand_apply_le

-- Remember, need to show that
-- `‖ξ‖ ^ p * ‖iteratedFDeriv ℝ i (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ φ x) ξ‖`
-- is bounded above!

-- Suspect we can show that, `∀ ξ`,
-- `‖∫ x, iteratedFDeriv ℝ n (vectorFourierIntegrand · f x) ξ‖ ≤`
-- `(2 * π) ^ n • ∫ x, ‖x‖ ^ n • ‖vectorFourierIntegrand ξ f x‖`
-- Or more precisely,
-- `(∫ x, iteratedFDeriv ℝ n (vectorFourierIntegrand · f x) ξ) m =`
-- `  (-(2 * π * I)) ^ n • ∫ x, (∏ i, ⟪x, m i⟫) • vectorFourierIntegrand ξ f x`

-- Focus on what we need.
-- We need the *derivative of the Fourier integral*!

-- The classical results are..
-- 1. The Fourier transform of the derivative is scalar multiplication of the Fourier transform.
-- 2. The Fourier transform of scalar multiplication is the derivative of the Fourier transform.
-- So we need the latter?

-- For this, we need to obtain scalar multiplication as a Schwartz map?
-- Does this help? Mainly useful for showing integrable, smooth?

-- We already have `fderiv_integral_vectorFourierIntegrand`.
-- (Note that it only proves exchange of variables.)
-- Just need to make `iteratedFDeriv` version of this?
-- However, this might require integral of `ContinuousMultilinearMap`; maybe ok, maybe not.
-- Might be easier to prove extensionality and norm?
-- Or use `MeasurableEquiv`?

-- For `iteratedFDeriv_integral_vectorFourierIntegrand_apply`.
theorem contDiff_integral_vectorFourierIntegrand {f : 𝓢(E, F)} :
    ContDiff ℝ ⊤ fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x :=
  hasFTaylorSeriesUpTo_integral_vectorFourierIntegrand.contDiff  -- BIG TODO


-- TODO: Just define Fourier integrand using `hasTemperateGrowth_smul`?
/-- Scalar multiplication of the Fourier integrand can be moved inside. -/
theorem vectorFourierIntegrand_hasTemperateGrowth_smul {f : 𝓢(E, F)} {x ξ : E} {g : E → ℝ}
    (hg : g.HasTemperateGrowth) :
    vectorFourierIntegrand ξ (hasTemperateGrowth_smul hg f) x =
      g x • vectorFourierIntegrand ξ f x := by
  simp only [vectorFourierIntegrand_apply]
  simp only [hasTemperateGrowth_smul_apply]
  rw [smul_comm]

-- TODO: Depends on `contDiff_integral_vectorFourierIntegrand`.
theorem iteratedFDeriv_integral_vectorFourierIntegrand_apply {n : ℕ} {f : 𝓢(E, F)} {ξ : E}
    {m : Fin n → E} :
    iteratedFDeriv ℝ n (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) ξ m =
      -- ∫ x, iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ m := by
      (-(2 * π * I)) ^ n • ∫ x, (∏ i, ⟪x, m i⟫) • vectorFourierIntegrand ξ f x := by
  induction n generalizing f ξ with
  | zero => simp
  | succ n IH =>
    rw [iteratedFDeriv_succ_apply_left]
    rw [← fderiv_continuousMultilinearMap_apply_comm (ContDiff.differentiable_iteratedFDeriv
      (WithTop.coe_lt_top n) contDiff_integral_vectorFourierIntegrand ξ)]
    simp_rw [IH]
    simp only [Fin.tail]
    -- TODO: Avoid long notation that results here?
    simp_rw [← vectorFourierIntegrand_hasTemperateGrowth_smul
      (Function.hasTemperateGrowth_prod_univ_inner_const fun i : Fin n ↦ m i.succ)]
    rw [fderiv_const_smul (differentiable_integral_vectorFourierIntegrand _)]
    rw [ContinuousLinearMap.smul_apply, pow_succ', mul_smul]
    refine congrArg _ ?_
    -- TODO: Avoid long notation that results here?
    rw [fderiv_integral_vectorFourierIntegrand', ← neg_smul, ContinuousLinearMap.smul_apply]
    refine congrArg _ ?_
    rw [ContinuousLinearMap.integral_apply (by exact integrable _)]  -- TODO: Why `exact` needed?
    refine congrArg _ ?_
    funext x
    rw [Fin.prod_univ_succ]
    simp only [vectorFourierIntegrand_apply, ContinuousLinearMap.smul_apply, innerSL_smul_apply,
      hasTemperateGrowth_smul_apply]
    simp [smul_comm (_ : ℂ), smul_smul]

-- -- Similar to `innerSL_smul`, define a Schwartz map with `ContinuousMultilinearMap` value.
-- noncomputable def innerSL_smul
--     (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
--     (x : E) : F →L[ℝ] E →L[ℝ] F :=
--   ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ x)

-- Expresses derivative using `SchwartzMap.hasTemperateGrowth_smul`.
theorem iteratedFDeriv_integral_vectorFourierIntegrand_apply' {n : ℕ} {f : 𝓢(E, F)} {ξ : E}
    {m : Fin n → E} :
    iteratedFDeriv ℝ n (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) ξ m =
      (-(2 * π * I)) ^ n • ∫ x, vectorFourierIntegrand ξ
        (SchwartzMap.hasTemperateGrowth_smul
          (Function.hasTemperateGrowth_prod_univ_inner_const m) f) x := by
  induction n generalizing f ξ with
  | zero => simp [vectorFourierIntegrand_hasTemperateGrowth_smul]
  | succ n IH =>
    rw [iteratedFDeriv_succ_apply_left]
    rw [← fderiv_continuousMultilinearMap_apply_comm (ContDiff.differentiable_iteratedFDeriv
      (WithTop.coe_lt_top n) contDiff_integral_vectorFourierIntegrand ξ)]
    simp_rw [IH]
    simp only [Fin.tail]
    rw [fderiv_const_smul (differentiable_integral_vectorFourierIntegrand _)]
    rw [ContinuousLinearMap.smul_apply, pow_succ', mul_smul]
    refine congrArg _ ?_
    rw [fderiv_integral_vectorFourierIntegrand', ← neg_smul, ContinuousLinearMap.smul_apply]
    refine congrArg _ ?_
    rw [ContinuousLinearMap.integral_apply (by exact integrable _)]
    refine congrArg _ ?_
    funext x
    simp only [vectorFourierIntegrand_hasTemperateGrowth_smul]
    rw [Fin.prod_univ_succ]
    simp only [vectorFourierIntegrand_apply, ContinuousLinearMap.smul_apply, innerSL_smul_apply,
      hasTemperateGrowth_smul_apply]
    simp [smul_comm (_ : ℂ), smul_smul]

-- -- TODO: Is it cleaner/useful to prove this?
-- theorem iteratedFDeriv_integral_vectorFourierIntegrand_eq_integral_iteratedFDeriv {f : 𝓢(E, F)} {ξ : E} :
--     iteratedFDeriv ℝ n (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) ξ =
--       ∫ x, iteratedFDeriv ℝ n (fun ξ ↦ vectorFourierIntegrand ξ f x) ξ := by
--   induction n generalizing f ξ with
--   | zero =>
--     ext m
--     simp
--     -- Require `integral_continuousMultilinearMap_apply`.
--     sorry
--   | succ n IH =>
--     ext m
--     simp [iteratedFDeriv_succ_eq_comp_left]
--     conv => rhs; rw [← Fin.cons_self_tail m]
--     conv => lhs; arg 1; arg 1; arg 2; intro ξ; rw [IH]
--     sorry

-- TODO: In order to write `iteratedFDeriv_integral_vectorFourierIntegrand`,
-- we need `mkPiField` Schwartz map (to take `m` outside).
-- If we then take the norm, we will have something like `‖vectorFourierIntegrand ξ (prod_inner_smul f)‖`.
-- What can we do with that?

-- Can we avoid this by instead writing `norm_iteratedFDeriv_integral_vectorFourierIntegrand`?

-- After proving this, then what?
-- The applied `iteratedFDeriv` of `vectorFourierIntegrand` will give something like
-- `(-(2 * π * I)) ^ n • ∫ x, (∏ i, ⟪x, m i⟫) • vectorFourierIntegrand ξ f x`
-- The norm of this might be bounded by something like...
-- `(2 * π) ^ n • ∫ x, ‖x‖ ^ n • vectorFourierIntegrand ξ f x`
-- Then...
-- We need to prove that this is a Schwartz map to obtain an upper bound?
-- Would suffice to show that `fun x ↦ ‖x‖ ^ n • f x` is Schwartz?

theorem norm_iteratedFDeriv_integral_vectorFourierIntegrand_le {n : ℕ} {f : 𝓢(E, F)} {ξ : E}
    {C : ℝ} (hC : 0 ≤ C) :
    ‖iteratedFDeriv ℝ n (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ f x) ξ‖ ≤
      -- (2 * π) ^ n * ‖vectorFourierIntegrand ξ (SchwartzMap.hasTemperateGrowth_mul  f)‖ := by
      (2 * π) ^ n * C := by
  rw [ContinuousMultilinearMap.op_norm_le_iff _ (mul_nonneg (by simp [Real.pi_pos.le]) hC)]
  intro m
  rw [iteratedFDeriv_integral_vectorFourierIntegrand_apply']
  rw [norm_smul, mul_assoc _ C]
  refine mul_le_mul (by simp [_root_.abs_of_nonneg Real.pi_pos.le]) ?_
    (norm_nonneg _) (by simp [Real.pi_pos.le])
  refine le_trans norm_integral_vectorFourierIntegrand_le ?_
  simp [hasTemperateGrowth_smul_apply]
  -- Need `C` such that `∫ (x : E), ‖(∏ i : Fin n, ⟪x, m i⟫_ℝ) • f x‖ ≤ C * ∏ i : Fin n, ‖m i‖`.
  refine le_trans (integral_mono (g := fun x ↦ (∏ i : Fin n, ‖x‖ * ‖m i‖) • ‖f x‖) ?_ ?_ ?_) ?_
  · sorry
  · sorry
  · sorry
  -- Need `C` such that `∫ (a : E), (∏ i : Fin n, ‖a‖ * ‖m i‖) • ‖f a‖ ≤ C * ∏ i : Fin n, ‖m i‖`.
  -- Expect this to contain `‖ξ‖ ^ n`??
  -- Effectively need Plancherel's theorem?
  sorry

-- theorem fderiv_integral_vectorFourierIntegrand_apply_eq_integral_vectorFourierIntegrand_inner_smul_apply
--     {n : ℕ} {f : 𝓢(E, F)} {x ξ m : E} :
--     fderiv ℝ (fun ξ ↦ ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x) ξ m =
--       ∫ x, Real.fourierChar[-⟪x, ξ⟫] • (⟪x, m⟫ • f x) := by
--   -- Need to exchange integral and derivative.
--   -- Then we can use the derivative of the integrAND.
--   -- Shouldn't need integration by parts; that was for the Fourier transform of the derivative
--   -- (was particularly challenging for vector case).
--   simp only [← vectorFourierIntegrand_apply]
--   rw [fderiv_integral_vectorFourierIntegrand]
--   sorry

-- theorem integral_vectorFourierIntegrand_inner_smul_eq_fderiv_integral_vectorFourierIntegrand {n : ℕ} {f : 𝓢(E, F)} {x ξ m : E} :
--     ∫ x, Real.fourierChar[-⟪x, ξ⟫] • (⟪x, m⟫ • f x) =
--       fderiv ℝ (fun ξ ↦ ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x) ξ m := by
--   simp only [← vectorFourierIntegrand_apply]
--   sorry


-- /-- The Schwartz function `x ↦ ∏ ⟪x, m i⟫ • f x` -/
-- def prod_innerSL_smul (f : 𝓢(E, F)) : 𝓢(E, E[×n]→L[ℝ] F) :=
--   sorry

-- /-- The Schwartz function `x ↦ ∏ ⟪x, m i⟫ • f x` -/
-- def prod_innerSL_smulCLM : 𝓢(E, F) →L[ℝ] 𝓢(E, E[×n]→L[ℝ] F) :=
--   sorry

-- The elements in the power and product do not depend on `ξ`...
-- However, they do depend on `x`.
-- We need the derivative with respect to `ξ` as a Schwartz map in `x`!
-- `fun x => (-(2 * π * I)) ^ n • (∏ i : Fin n, ⟪x, dξ i⟫) • vectorFourierIntegrand ξ f x`

-- noncomputable def iteratedFDerivVectorFourierIntegrandCLM (n : ℕ) (x : E) : 𝓢(E, F) →L[ℝ] 𝓢(E, E[×n]→L[ℝ] F) :=
--   mkCLM (fun f ξ => (-2 * π * I) ^ n •
--       (ContinuousMultilinearMap.mkPiField ℝ (Fin n) (vectorFourierIntegrand ξ f x)).compContinuousLinearMap
--         (fun _ => innerSL ℝ x))
--     (fun f g x => iteratedFDeriv_add_apply (f.smooth n) (g.smooth n))
--     (fun r f x => iteratedFDeriv_const_smul_apply (f.smooth n))
--     (fun f => ContDiff.iteratedFDeriv_right f.smooth' le_top)
--     (fun m => by
--       sorry)

-- noncomputable def iteratedFDerivCLM (n : ℕ) : 𝓢(E, F) →L[ℝ] 𝓢(E, E[×n]→L[ℝ] F) :=
--   mkCLM (fun f x => iteratedFDeriv ℝ n f x)
--     (fun f g x => iteratedFDeriv_add_apply (f.smooth n) (g.smooth n))
--     (fun r f x => iteratedFDeriv_const_smul_apply (f.smooth n))
--     (fun f => ContDiff.iteratedFDeriv_right f.smooth' le_top)
--     (fun m => by
--       sorry)

-- /-- The Fourier integral of a Schwartz map is smooth. -/
-- theorem contDiff_integralCLM_vectorFourierIntegrand {f : 𝓢(E, F)} : ContDiff ℝ ⊤ fun ξ => integralCLM (vectorFourierIntegrand ξ f) := by
--   -- Cannot use `ContDiff.comp`; requires `NormedAddCommGroup 𝓢(E, F)`.
--   conv => arg 3; intro ξ; rw [integralCLM_apply]
--   sorry
--   -- rw [contDiff_top]
--   -- intro n
--   -- induction n with
--   -- | zero =>
--   --   simp
--   --   exact continuous_integralCLM_vectorFourierIntegrand
--   -- | succ n h_ind =>
--   --   rw [contDiff_succ_iff_fderiv]
--   --   refine ⟨differentiable_integralCLM_vectorFourierIntegrand, ?_⟩
--   --   simp_rw [fderiv_integralCLM_eq_integralCLM_innerSL_smul]
--   --   conv =>
--   --     arg 3; intro y; arg 1; rhs
--   --   sorry
--   --   -- refine ContDiff.neg ?_
--   --   -- refine ContDiff.const_smul (2 * π * I : ℂ) ?_
--   --   -- -- Need `E →L[ℝ] F` to be in same universe as `F` to apply induction.
--   --   -- exact h_ind

/-- The Fourier integral of a Schwartz map is smooth. -/
theorem contDiff_fourierIntegral {f : 𝓢(E, F)} :
    ContDiff ℝ ⊤ fun ξ ↦ ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x :=
  contDiff_integral_vectorFourierIntegrand

-- /-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
-- noncomputable def realFourierIntegralCLM : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) :=
--   mkCLM (fun f ξ ↦ ∫ x, Real.fourierChar[-(x * ξ)] • f x)
--     (fun φ θ ξ ↦ by simp [← realFourierIntegrand_apply, integral_add])
--     (fun c φ ξ ↦ by simp [smul_comm _ c, integral_smul])
--     (fun φ ↦ by
--       simp only
--       sorry)
--     (fun m ↦ by
--       simp only
--       simp only [← realFourierIntegrand_apply]
--       sorry
--       simp only [← iteratedFDeriv_vectorFourierIntegrand_apply]
--       -- simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
--       sorry)

/-- The Fourier integral of a Schwartz function as a ContinuousLinearMap. -/
noncomputable def integral_vectorFourierIntegrandCLM {r : ℕ} [hr : Fact (FiniteDimensional.finrank ℝ E < r)] : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  mkCLM (fun f ξ ↦ ∫ x, Real.fourierChar[-⟪x, ξ⟫] • f x)
    (fun φ θ ξ ↦ by simp [← vectorFourierIntegrand_apply, integral_add])
    (fun c φ ξ ↦ by simp [smul_comm _ c, integral_smul])
    (fun φ ↦ contDiff_fourierIntegral)
    (fun m ↦ by
      rcases m with ⟨p, i⟩
      simp only
      simp only [← vectorFourierIntegrand_apply]
      -- have C' : ℝ := sorry
      -- have hC' : 0 ≤ C := sorry
      -- have {f : 𝓢(E, F)} {x : E} := (iteratedFDeriv ℝ m.2 (fun ξ => ∫ (x : E), vectorFourierIntegrand ξ f x) x).op_norm_le_iff hC'

      have k' : ℕ := sorry
      have n' : ℕ := sorry
      have C' : ℝ := sorry
      use Finset.Iic (k', n')
      use C'
      refine ⟨sorry, ?_⟩
      intro φ ξ
      -- CURRENT GOAL 1
      -- `‖ξ‖ ^ p * ‖iteratedFDeriv ℝ i (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ φ x) ξ‖ ≤ _`
      -- Reduce to norm of application of `iteratedFDeriv`?
      have := (ContinuousMultilinearMap.op_norm_le_iff
          (iteratedFDeriv ℝ i (fun ξ => ∫ (x : E), ((vectorFourierIntegrand ξ) φ) x) ξ)
          (sorry : 0 ≤ C' * (Finset.Iic (k', n')).sup (schwartzSeminormFamily ℝ E F) φ)
        ).mpr

      suffices (m : Fin i → E) :
          ‖ξ‖ ^ p * ‖iteratedFDeriv ℝ i (fun ξ ↦ ∫ x, vectorFourierIntegrand ξ φ x) ξ m‖ ≤
            C' * (Finset.Iic (k', n')).sup (schwartzSeminormFamily ℝ E F) φ * ∏ j, ‖m j‖
      · sorry

      sorry
    )

end SchwartzMap  -- namespace

end Fourier
