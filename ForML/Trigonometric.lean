import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import ForML.HasTemperateGrowth
import ForML.Util

open Complex
open scoped BigOperators Real FourierTransform RealInnerProductSpace

section IteratedDeriv
-- Some useful lemmata for `iteratedDeriv` that avoid passing through `iteratedFDeriv`.
-- TODO: Is it overkill to declare these?
-- TODO: Typeclasses might not be perfect; some trial and error involved.

variable {𝕜 𝕜' F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma iteratedDeriv_neg_apply {n : ℕ} {f : 𝕜 → F} :
    iteratedDeriv n (fun x => -f x) x = -iteratedDeriv n f x := by
  change iteratedDeriv n (-f) x = _
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp [iteratedFDeriv_neg_apply]

lemma iteratedDeriv_const_mul_apply {n : ℕ} (a : 𝕜') {f : 𝕜 → 𝕜'} (hf : ContDiff 𝕜 n f) {x : 𝕜} :
    iteratedDeriv n (fun x => a * f x) x = a * iteratedDeriv n f x := by
  change iteratedDeriv n (a • f) x = _
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp [iteratedFDeriv_const_smul_apply hf]

lemma iteratedDeriv_mul_const_apply {n : ℕ} (a : 𝕜') {f : 𝕜 → 𝕜'} (hf : ContDiff 𝕜 n f) {x : 𝕜} :
    iteratedDeriv n (fun x => f x * a) x = iteratedDeriv n f x * a := by
  simp_rw [mul_comm _ a]
  exact iteratedDeriv_const_mul_apply a hf

end IteratedDeriv


section Complex

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma Complex.contDiff_exp_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (x • I) :=
  (contDiff_id.smul contDiff_const).cexp

lemma Complex.contDiff_exp_neg_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (-(x • I)) :=
  (contDiff_id.smul contDiff_const).neg.cexp

lemma ContDiff.cexp_real_smul_I {n : ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => cexp (f x • Complex.I) :=
  Complex.contDiff_exp_real_smul_I.comp hf

lemma ContDiff.realFourierChar {n : ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => Real.fourierChar[f x] :=
  ((contDiff_const.mul hf).smul contDiff_const).cexp

lemma Real.contDiff_fourierChar {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => fourierChar[x] :=
  ((contDiff_const.mul contDiff_id).smul contDiff_const).cexp

lemma Real.differentiable_fourierChar : Differentiable ℝ fun x : ℝ => fourierChar[x] :=
  contDiff_fourierChar.differentiable le_top

lemma Real.differentiableAt_fourierChar {x : ℝ} : DifferentiableAt ℝ (fun x : ℝ => fourierChar[x]) x :=
  differentiable_fourierChar.differentiableAt

lemma Complex.hasDerivAt_exp_real_smul_I {x : ℝ} :
    HasDerivAt (fun x : ℝ => exp (x • I)) (I * exp (x • I)) x := by
  -- rw [Complex.exp_eq_exp_ℂ]
  -- refine hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := ℂ) ?_ x  -- Gives `NormedSpace.exp ℝ`
  rw [mul_comm I]
  refine HasDerivAt.cexp ?_
  suffices : HasDerivAt (fun x => x • I) ((1 : ℝ) • I) x
  . simpa using this
  exact HasDerivAt.smul_const (hasDerivAt_id' x) I

lemma Complex.deriv_exp_real_smul_I {x : ℝ} :
    deriv (fun x : ℝ => exp (x • I)) x = I * exp (x • I) :=
  hasDerivAt_exp_real_smul_I.deriv

lemma Complex.iteratedDeriv_exp_real_smul_I {n : ℕ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp (x • I)) x = HPow.hPow I n * exp (x • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x; rw [deriv_exp_real_smul_I]
    rw [iteratedDeriv_const_mul_apply I contDiff_exp_real_smul_I]
    rw [hi, mul_assoc]

lemma Complex.hasTemperateGrowth_exp_real_smul_I :
    Function.HasTemperateGrowth fun x : ℝ => exp (x • I) := by
  refine ⟨contDiff_exp_real_smul_I, ?_⟩
  intro n
  refine ⟨n, 1, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedDeriv_exp_real_smul_I]
  simp
  exact one_le_pow_of_one_le (by simp) n

/-- `d(exp (2 π I x)) = (2 π I) exp (2 π I x) dx` -/
lemma Real.fderiv_fourierChar_apply {x dx : ℝ} :
    fderiv ℝ (fun x : ℝ => Real.fourierChar[x]) x dx =
    (2 * π * dx) • (Complex.I * Real.fourierChar[x]) := by
  simp [Real.fourierChar]
  norm_cast
  -- TODO: Re-order to avoid O(n^2) re-proving?
  rw [fderiv_cexp_real]
  swap
  . simp_rw [← Complex.real_smul]
    exact (differentiableAt_id.const_mul _).smul_const _
  simp
  rw [ContinuousLinearMap.smul_apply]
  simp
  norm_cast
  simp_rw [← Complex.real_smul]
  rw [fderiv_smul_const]
  swap
  . exact DifferentiableAt.const_mul differentiableAt_id _
  rw [ContinuousLinearMap.smulRight_apply]
  simp
  rw [fderiv_const_mul differentiableAt_id']
  simp
  ring_nf

lemma Real.fderiv_fourierChar {x : ℝ} :
    fderiv ℝ (fun x => Real.fourierChar[(x : ℝ)]) x =
    (2 * π * Complex.I * Real.fourierChar[x]) • Complex.ofRealCLM := by
  refine ContinuousLinearMap.ext ?_
  intro dx
  rw [fderiv_fourierChar_apply]
  simp
  ring_nf

/--
The imaginary exponential of a real-valued `HasTemperateGrowth` function is a `HasTemperateGrowth` function.

TODO: Prove for more general `g : E → ℂ` with `|(g x).re| ≤ 1`?
-/
lemma Function.HasTemperateGrowth.cexp_real_smul_I {f : E → ℝ} (hf : Function.HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => cexp (f x • Complex.I) :=
  Complex.hasTemperateGrowth_exp_real_smul_I.comp hf

end Complex


section RealFourier

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma Real.hasTemperateGrowth_cos : Function.HasTemperateGrowth (fun x : ℝ => cos x) := by
  simp_rw [cos, Complex.cos]
  refine ((Function.HasTemperateGrowth.add ?_ ?_).div_const 2).re
  . simp_rw [← Complex.real_smul]
    exact Complex.hasTemperateGrowth_exp_real_smul_I
  norm_cast
  simp_rw [← Complex.real_smul]
  exact Function.hasTemperateGrowth_neg.cexp_real_smul_I

lemma Real.hasTemperateGrowth_sin : Function.HasTemperateGrowth (fun x => sin x) := by
  simp_rw [sin, Complex.sin]
  refine (((Function.HasTemperateGrowth.sub ?_ ?_).mul_const Complex.I).div_const 2).re
  . norm_cast
    simp_rw [← Complex.real_smul]
    exact Function.hasTemperateGrowth_neg.cexp_real_smul_I
  simp_rw [← Complex.real_smul]
  exact Complex.hasTemperateGrowth_exp_real_smul_I

lemma Real.hasTemperateGrowth_fourierChar :
    Function.HasTemperateGrowth fun x : ℝ => fourierChar[x] := by
  simp [fourierChar_apply]
  norm_cast
  simp_rw [← Complex.real_smul]
  exact (Function.hasTemperateGrowth_const_mul (2 * π)).cexp_real_smul_I

lemma Function.HasTemperateGrowth.cos {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.cos (f x) := Real.hasTemperateGrowth_cos.comp hf

lemma Function.HasTemperateGrowth.sin {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.sin (f x) := Real.hasTemperateGrowth_sin.comp hf

lemma Function.HasTemperateGrowth.realFourierChar {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.fourierChar[f x] := Real.hasTemperateGrowth_fourierChar.comp hf

-- TODO: Too trivial to declare? May be useful for Fourier transform.

lemma Real.hasTemperateGrowth_fourierChar_mul_const (w : ℝ) : Function.HasTemperateGrowth fun v : ℝ => fourierChar[v * w] :=
  (Function.hasTemperateGrowth_mul_const w).realFourierChar

lemma Real.hasTemperateGrowth_fourierChar_neg_mul_const (w : ℝ) : Function.HasTemperateGrowth fun v : ℝ => fourierChar[-(v * w)] :=
  (Function.hasTemperateGrowth_mul_const w).neg.realFourierChar

end RealFourier


section VectorFourier

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

example {v w : F} : (innerSL ℝ v) w = ⟪v, w⟫ := rfl
example {v w : F} : ((innerSL ℝ).flip v) w = ⟪w, v⟫ := rfl

lemma Function.HasTemperateGrowth.inner {f g : E → F} (hf : HasTemperateGrowth f) (hg : HasTemperateGrowth g) :
    Function.HasTemperateGrowth fun x => ⟪f x, g x⟫ :=
  bilin (innerSL ℝ) hf hg

lemma Function.HasTemperateGrowth.inner_const {f : E → F} (hf : HasTemperateGrowth f) (w : F) :
    Function.HasTemperateGrowth fun x => ⟪f x, w⟫ :=
  inner hf (hasTemperateGrowth_const w)

lemma Function.HasTemperateGrowth.const_inner (v : F) {f : E → F} (hf : HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => ⟪v, f x⟫ :=
  inner (hasTemperateGrowth_const v) hf

-- TODO: Too trivial to declare? May be useful for Fourier transform.

lemma Real.hasTemperateGrowth_inner_const (w : F) :
    Function.HasTemperateGrowth fun v : F => ⟪v, w⟫ :=
  Function.HasTemperateGrowth.inner Function.hasTemperateGrowth_id (Function.hasTemperateGrowth_const w)

lemma Real.hasTemperateGrowth_l2inner_const {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    Function.HasTemperateGrowth fun v : ι → ℝ => ∑ i : ι, v i * w i := by
  change Function.HasTemperateGrowth ((fun v : EuclideanSpace ℝ ι => inner v w) ∘ ⇑(EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap)
  exact (Real.hasTemperateGrowth_inner_const _).comp (Function.hasTemperateGrowth_clm _)

lemma Real.hasTemperateGrowth_realFourierChar_inner_const (w : F) :
    Function.HasTemperateGrowth fun v : F => fourierChar[⟪v, w⟫] :=
  (hasTemperateGrowth_inner_const w).realFourierChar

lemma Real.hasTemperateGrowth_realFourierChar_neg_inner_const (w : F) :
    Function.HasTemperateGrowth fun v : F => fourierChar[-⟪v, w⟫] :=
  (hasTemperateGrowth_inner_const w).neg.realFourierChar

end VectorFourier


section RealFourier  -- TODO: Integrate with above.

variable {E : Type*}
variable [TopologicalSpace E]

-- lemma Continuous.cexp_real_smul_I {f : E → ℝ} (h : Continuous f) : Continuous (fun x => cexp (f x • I)) := by
--   exact (h.smul continuous_const).cexp

lemma Continuous.realFourierChar {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun x => Real.fourierChar[f x]) := by
  simp_rw [Real.fourierChar_apply]
  simp_rw [← Complex.real_smul]
  exact ((continuous_const.mul hf).smul continuous_const).cexp

lemma deriv.cexp_real_smul_I {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    deriv (fun x : ℝ => Complex.exp (f x • I)) x = (deriv f x) * I * Complex.exp (f x • I) := by
  rw [deriv_cexp (hf.smul_const I)]
  rw [deriv_smul hf (differentiableAt_const I)]
  simp
  ring_nf

-- `HasDerivAt.comp` only allows type to change in inner function.
lemma HasDerivAt.cexp_real_smul_I {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x : ℝ => Complex.exp (f x • I)) (f' * I * Complex.exp (f x • I)) x := by
  suffices : HasDerivAt (fun x : ℝ => Complex.exp (f x • I)) (f' • (I * Complex.exp (f x • I))) x
  . simpa [← mul_assoc] using this
  exact HasDerivAt.comp_of_tower x Complex.hasDerivAt_exp_real_smul_I hf

end RealFourier
