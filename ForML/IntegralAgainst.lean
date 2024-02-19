import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Integral.Bochner

import ForML.HasTemperateGrowth
import ForML.SchwartzLp
import ForML.Util

open MeasureTheory SchwartzSpace RealInnerProductSpace
open scoped Real Complex

-- A tempered distribution is a linear functional on the Schwartz space.
-- A function `g : E → 𝕜'` with `HasTemperateGrowth g` corresponds to a tempered distribution
-- in the functional `fun (φ : 𝓢(E, F)) => ∫ x, g x • φ x`.
-- This linear functional has type `𝓢(E, F) →L[_] F` where `𝕜'` is a scalar multiplier for `F`.

-- TODO: Should this functional be `ℝ`-linear or `𝕜`-linear?
-- Note that `HasTemperateGrowth` uses `ContDiff ℝ` and `iteratedFDeriv ℝ`.
--
-- We will subsequently want to define the Fourier transform of such distributions
-- (distinct from the Fourier transform *of* a Schwartz function).
-- For simple purposes, this will always be for functions `g : ℝ → ℂ`,
-- although there will be frequent cases where
-- `g = ofReal ∘ r` with `r : ℝ → ℝ` or
-- `g = c ∘ ofReal` with `c : ℂ → ℂ`.
-- nLab defines Fourier transforms for distributions on `ℝ^n`.
-- Given this restriction, we only need consider Schwartz functions `𝓢(R^n, F)`.

-- What about `F`? And what kind of linearity should the Fourier transform have?
-- The Fourier transform of a tempered distribution is a tempered distribution (closure).
-- However, functions with `HasTemperateGrowth` are not closed under the Fourier transform
-- (e.g. the Fourier transform of `const` is `delta`).
-- The Fourier transform will be defined as a linear map from distributions to distributions
-- `(𝓢(R^n, F) →L[_] F) →L[_] 𝓢(R^n, F) →L[_] F`.
-- Usually we would only consider `F = ℂ` and denote
-- `𝓢(R^n, ℂ)` as `𝓢(R^n)` and
-- `𝓢(R^n, ℂ) →L[_] ℂ` as `𝓢'(R^n)`.
-- Should this be `ℝ`-linear or `ℂ`-linear?

-- The Fourier transform of a tempered distribution `u : 𝓢'(R^n)` is denoted `ℱ[u] : 𝓢'(R^n)`
-- and is defined as the linear functional `fun φ => inner u ℱ[φ] : 𝓢'(ℝ^n)`.
-- Here, we need an inner product of tempered distributions and
-- the Fourier transform of a Schwartz function `φ` as a tempered distribution.
-- The Fourier transform of a Schwartz function `ℱ[φ] : 𝓢'(ℝ^n)` is defined...
-- For `n = 1`:
-- `ℱ[φ] = fun w => Real.fourierIntegral φ w`
-- which is defined as
-- `∫ (v : ℝ), ↑(↑Real.fourierChar (↑Multiplicative.ofAdd (-(v * w)))) • f v`
-- `∫ (v : ℝ), cexp (↑(-2 * Real.pi * v * w) * Complex.I) • f v`
-- Note that we do not have Fourier integral as a CLM because
-- it is *not* continuous (for all functions) under the standard topology.
-- We do have `VectorFourier.fourierIntegral_add` which shows linearity, and
-- `VectorFourier.fourierIntegral_continuous` for functions with finite integral.


variable {𝕜 𝕜' D E F G : Type*}

-- First define CLMs that perform pointwise multiplication, then compose with integral.
section Pointwise

namespace SchwartzMap

section SMul

variable [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable  {g : E → 𝕜} (hg : Function.HasTemperateGrowth g)

/-- Pointwise multiplication by a scalar-valued `HasTemperateGrowth` function as a CLM. -/
noncomputable def hasTemperateGrowth_smul : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  bilinLeftCLM isBoundedBilinearMap_smul.toContinuousLinearMap.flip hg

lemma hasTemperateGrowth_smul_apply {φ : 𝓢(E, F)} {x : E} :
    hasTemperateGrowth_smul hg φ x = g x • φ x := rfl

noncomputable def id_smul (φ : 𝓢(𝕜, F)) : 𝓢(𝕜, F) :=
  hasTemperateGrowth_smul Function.hasTemperateGrowth_id φ

lemma id_smul_apply {φ : 𝓢(𝕜, F)} {x : 𝕜} : id_smul φ x = x • φ x := rfl

end SMul


section Mul

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

variable {g : E → 𝕜} (hg : Function.HasTemperateGrowth g)

-- /-- Pointwise multiplication by a `HasTemperateGrowth` function as a CLM. -/
-- noncomputable def hasTemperateGrowth_mul : 𝓢(E, 𝕜) →L[ℝ] 𝓢(E, 𝕜) :=
--   bilinLeftCLM (bilin_restrictScalars ℝ isBoundedBilinearMap_mul.toContinuousLinearMap.flip) hg

/-- Pointwise multiplication by a `HasTemperateGrowth` function as a CLM. -/
noncomputable def hasTemperateGrowth_mul : 𝓢(E, 𝕜) →L[ℝ] 𝓢(E, 𝕜) :=
  hasTemperateGrowth_smul hg

lemma hasTemperateGrowth_mul_apply {φ : 𝓢(E, 𝕜)} {x : E} :
    hasTemperateGrowth_mul hg φ x = g x * φ x := rfl

lemma hasTemperateGrowth_smul_eq_hasTemperateGrowth_mul {φ : 𝓢(E, 𝕜)} {x : E} :
    hasTemperateGrowth_smul hg φ x = hasTemperateGrowth_mul hg φ x := rfl

end Mul

end SchwartzMap  -- namespace



section Map

variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def SchwartzMap.hasTemperateGrowth_apply
    {g : D → E →L[ℝ] G} (hg : Function.HasTemperateGrowth g) : 𝓢(D, E) →L[ℝ] 𝓢(D, G) :=
  bilinLeftCLM (ContinuousLinearMap.apply ℝ G) hg

end Map


section InnerProduct

variable [NormedAddCommGroup E] [hE : InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
instance : NormedSpace ℝ E := hE.toNormedSpace  -- Type system doesn't find this?

-- Tried adding this as a simp lemma but it doesn't seem to help.
@[simp] lemma fderiv_const_innerSL : fderiv ℝ (fun _ : E => innerSL ℝ (E := E)) x = 0 := by
  rw [fderiv_const]
  rfl

lemma fderiv_innerSL_apply {x : E} : fderiv ℝ (fun x : E => innerSL ℝ x) x = innerSL ℝ := by
  refine ContinuousLinearMap.ext ?_
  intro u
  refine ContinuousLinearMap.ext ?_
  intro dx
  rw [fderiv_clm_apply (differentiableAt_const _) differentiableAt_id']
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.flip_apply]
  rw [fderiv_const]
  change _ + 0 = _  -- Needs help to resolve.
  simp
  rw [ContinuousLinearMap.comp_apply]
  rfl

-- The function `x ↦ (u ↦ ⟪x, u⟫)` is a `HasTemperateGrowth` function.
lemma Function.hasTemperateGrowth_innerSL : HasTemperateGrowth fun x : E => innerSL ℝ x := by
  refine ⟨contDiff_const.clm_apply contDiff_id, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  cases n with
  | zero => simp
  | succ n =>
    simp [iteratedFDeriv_succ_eq_comp_right]
    simp_rw [fderiv_innerSL_apply]
    cases n with
    | zero =>
      simp
      refine le_trans (norm_innerSL_le_one ℝ) (by simp)
    | succ n =>
      rw [iteratedFDeriv_const_of_ne]
      . change ‖0‖ ≤ _
        simp
      . simp

/-- CLM that represents `x ↦ ⟪x, u⟫ • c` as a CLM `F →L[ℝ] E →L[ℝ] F` (could make first map linear too?). -/
noncomputable def innerSL_smul (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (x : E) :
    F →L[ℝ] E →L[ℝ] F :=
  .smulRightL ℝ E F (innerSL ℝ x)

lemma innerSL_smul_apply {x u : E} {c : F} : (innerSL_smul F x) c u = ⟪x, u⟫ • c := rfl

lemma innerSL_smul_comm {x u : E} {c : F} : (innerSL_smul F x) c u = (innerSL_smul F u) c x := by
  simp [innerSL_smul_apply]
  rw [real_inner_comm]

-- TODO: Can we use `hasTemperateGrowth_smul` to reduce extra definitions?

lemma Function.hasTemperateGrowth_innerSL_smul
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    HasTemperateGrowth fun x : E => innerSL_smul F x :=
  HasTemperateGrowth.clm _ hasTemperateGrowth_innerSL

-- Schwartz CLM for `x ↦ ⟪x, u⟫ • f x`.
noncomputable def SchwartzMap.innerSL_smul : 𝓢(E, F) →L[ℝ] 𝓢(E, E →L[ℝ] F) :=
  bilinLeftCLM (ContinuousLinearMap.apply ℝ (E →L[ℝ] F)) (Function.hasTemperateGrowth_innerSL_smul F)

lemma SchwartzMap.innerSL_smul_apply {φ : 𝓢(E, F)} {x u : E} :
    SchwartzMap.innerSL_smul φ x u = ⟪x, u⟫ • φ x := rfl

lemma SchwartzMap.innerSL_smul_one_eq_id_smul {φ : 𝓢(ℝ, F)} {x : ℝ} :
    SchwartzMap.innerSL_smul φ x 1 = SchwartzMap.id_smul φ x := by
  simp [innerSL_smul_apply, id_smul_apply]

lemma SchwartzMap.norm_innerSL_smul_le {φ : 𝓢(E, F)} {x : E} :
    ‖SchwartzMap.innerSL_smul φ x‖ ≤ ‖x‖ * ‖φ x‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg (norm_nonneg x) (norm_nonneg (φ x)))]
  intro m
  rw [SchwartzMap.innerSL_smul_apply, norm_smul]
  rw [← mul_rotate]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (φ x))
  rw [mul_comm]
  exact norm_inner_le_norm x m

end InnerProduct

end Pointwise


-- Now define some distributions.

-- scoped[SchwartzSpace] notation "𝓢'(" E ", " F ")" => 𝓢(E, F) →L[ℝ] F
-- scoped[SchwartzSpace] notation "𝓢'[" 𝕜 "](" E ", " F ")" => SchwartzMap E F →L[𝕜] F

section IntegralAgainst

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Need `NontriviallyNormedField` rather than `NormedField` for `MeasureTheory.integral_smul`.
variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 F]

variable [CompleteSpace F]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]

namespace SchwartzMap

noncomputable def Distribution.ofHasTemperateGrowth
    {g : E → 𝕜} (hg : Function.HasTemperateGrowth g) : 𝓢(E, F) →L[ℝ] F :=
  integralCLM.comp (hasTemperateGrowth_smul hg)

lemma Distribution.ofHasTemperateGrowth_apply
    {g : E → 𝕜} (hg : Function.HasTemperateGrowth g) {φ : 𝓢(E, F)} :
    ofHasTemperateGrowth hg φ = ∫ (x : E), g x • φ x := by
  rw [ofHasTemperateGrowth, ContinuousLinearMap.comp_apply, integralCLM_apply]
  rfl

lemma Distribution.ofHasTemperateGrowth_const {c : 𝕜} :
    ofHasTemperateGrowth (Function.hasTemperateGrowth_const c) = SchwartzMap.Distribution.const E F c := by
  ext φ
  rw [ofHasTemperateGrowth_apply]
  rw [const_apply]
  rw [integral_smul]

noncomputable def toDistribution (φ : 𝓢(E, 𝕜)) : 𝓢(E, F) →L[ℝ] F :=
  Distribution.ofHasTemperateGrowth (SchwartzMap.hasTemperateGrowth φ)

end SchwartzMap  -- namespace

end IntegralAgainst
