import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open scoped Real Complex

section Differentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' ℂ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
-- `NormedAlgebra` instead of `NormedSpace` for `Complex.differentiable_exp`
variable [NormedAlgebra 𝕜 ℂ] [IsScalarTower 𝕜 𝕜' ℂ]

lemma Differentiable.cexp_smul_I {f : E → 𝕜'} (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x • (I : ℂ)) :=
  Complex.differentiable_exp.comp (hf.smul_const I)

lemma Complex.differentiable_exp_real_smul_I : Differentiable ℝ (fun x : ℝ => exp (x • I)) :=
  Differentiable.cexp_smul_I differentiable_id

end Differentiable


section IteratedDeriv
-- Some useful lemmata for `iteratedDeriv` that avoid passing through `iteratedFDeriv`.
-- TODO: Typeclasses might not be perfect; some trial and error involved.

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' ℂ]
variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' ℂ]

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


namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]

lemma contDiff_exp_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (x • I) :=
  ContDiff.cexp (ContDiff.smul contDiff_id contDiff_const)

lemma _root_.ContDiff.cexp_const_mul_real_smul_I {n : ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x : ℝ => Complex.exp (f x • I) :=
  contDiff_exp_real_smul_I.comp hf

lemma deriv_exp_real_smul_I_apply {x : ℝ} :
    deriv (fun x : ℝ => exp (x • I)) x = I * exp (x • I) := by
  change deriv (exp ∘ fun x => (x • I)) x = I * cexp (x • I)
  rw [deriv.comp _ differentiableAt_exp (differentiableAt_id.smul_const I)]
  rw [Complex.deriv_exp]
  rw [mul_comm]
  congr
  rw [deriv_smul_const differentiableAt_id]
  simp

lemma iteratedDeriv_exp_real_smul_I_apply {n : ℕ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp (x • I)) x = HPow.hPow I n * exp (x • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_real_smul_I_apply]
    rw [iteratedDeriv_const_mul_apply I contDiff_exp_real_smul_I]
    rw [hi, mul_assoc]

lemma deriv_comp_exp_real_smul_I_apply {f : 𝕜 → ℝ} (hf : Differentiable 𝕜 f) {x : 𝕜} :
    deriv (fun x => exp (f x • I)) x = cexp (f x • I) * (deriv f x • I) := by
  change deriv (exp ∘ (fun x => f x • I)) x = _
  rw [deriv.comp _ differentiableAt_exp (hf.smul_const I).differentiableAt]
  rw [deriv_smul_const hf.differentiableAt]
  simp

-- Prove some convenience lemmata for `fun x : ℝ => exp ((a * x) • I)`.

lemma contDiff_exp_const_mul_real_smul_I {n : ℕ∞} {a : ℝ} :
    ContDiff ℝ n fun x : ℝ => exp ((a * x) • I) :=
  ContDiff.cexp_const_mul_real_smul_I (contDiff_const.mul contDiff_id)

-- TODO: Use comp with CLM?
lemma deriv_exp_const_mul_real_smul_I_apply {a : ℝ} {x : ℝ} :
    deriv (fun x : ℝ => exp ((a * x) • I)) x = (a • I) * exp ((a * x) • I) := by
  rw [deriv_comp_exp_real_smul_I_apply]
  swap
  . exact differentiable_id.const_mul a
  rw [mul_comm]
  congr
  rw [deriv_const_mul _ differentiableAt_id]
  simp

-- TODO: Use comp with CLM?
lemma iteratedDeriv_exp_const_mul_real_smul_I_apply {n : ℕ} {a : ℝ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp ((a * x) • I)) x = HPow.hPow (a • I) n * exp ((a * x) • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_const_mul_real_smul_I_apply]
    rw [iteratedDeriv_const_mul_apply _ contDiff_exp_const_mul_real_smul_I]
    rw [hi, mul_assoc]

lemma hasTemperateGrowth_exp_real_smul_I :
    Function.HasTemperateGrowth fun x : ℝ => exp (x • I) := by
  refine ⟨contDiff_exp_real_smul_I, ?_⟩
  intro n
  refine ⟨n, 1, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedDeriv_exp_real_smul_I_apply]
  simp
  exact one_le_pow_of_one_le (by simp) n

-- TODO: Generalize to `f x` with bound on growth?
-- Could there be a `HasTemperateGrowth.comp`? At least with a `ContinuousLinearMap`?
lemma hasTemperateGrowth_exp_const_mul_real_smul_I {a : ℝ} :
    Function.HasTemperateGrowth fun x : ℝ => exp ((a * x) • I) := by
  refine ⟨contDiff_exp_const_mul_real_smul_I, ?_⟩
  intro n
  refine ⟨n, HPow.hPow |a| n, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedDeriv_exp_const_mul_real_smul_I_apply]
  simp [abs_of_pos, Real.pi_pos]
  norm_cast
  rw [abs_exp_ofReal_mul_I]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg a) n)
  exact one_le_pow_of_one_le (by simp) n

-- /-- More general than `contDiff_sin`; matches `contDiff_exp`. -/
-- lemma contDiff_sin' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] :
--     ContDiff 𝕜 ⊤ sin := by
--   simp [sin]
--   refine ContDiff.div_const (ContDiff.mul ?_ contDiff_const) 2
--   refine ContDiff.sub ?_ ?_
--   . exact ContDiff.cexp (ContDiff.neg (ContDiff.mul contDiff_id contDiff_const))
--   . exact ContDiff.cexp (ContDiff.mul contDiff_id contDiff_const)

-- /-- More general than `contDiff_cos`; matches `contDiff_exp`. -/
-- lemma contDiff_cos' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] :
--     ContDiff 𝕜 ⊤ cos := by
--   simp [cos]
--   refine ContDiff.div_const ?_ 2
--   refine ContDiff.add ?_ ?_
--   . exact ContDiff.cexp (ContDiff.mul contDiff_id contDiff_const)
--   . exact ContDiff.cexp (ContDiff.neg (ContDiff.mul contDiff_id contDiff_const))

end Complex


namespace Real

-- Tried using `ContinuousLinearMap.norm_compContinuousMultilinearMap_le` with
-- `‖iteratedFDeriv ℝ n (Complex.reClm ∘ Complex.sin ∘ Complex.ofRealClm) x‖ ≤ 1`
-- and then using `LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` with
-- `‖iteratedFDeriv ℝ n ((Complex.sin ∘ Subtype.val) ∘ Complex.ofRealLi.equivRange) x‖ ≤ 1`
-- but it was difficult to use the last `Subtype.val`.
-- Easier to just prove `sin` and `cos` together by induction.
-- Could revisit and refer to `ContDiffAt.real_of_complex` as a guide.

/-- Auxiliary function for `abs_iteratedDeriv_{sin,cos}_le`. -/
lemma abs_iteratedDeriv_sin_cos_le {n : ℕ} {x : ℝ} :
    |iteratedDeriv n sin x| ≤ 1 ∧ |iteratedDeriv n cos x| ≤ 1 := by
  induction n with
  | zero => simp; exact ⟨abs_sin_le_one x, abs_cos_le_one x⟩
  | succ n hi =>
    simp [iteratedDeriv_succ']
    refine ⟨hi.right, ?_⟩
    simp [iteratedDeriv_neg_apply]
    exact hi.left

lemma abs_iteratedDeriv_sin_le {n : ℕ} {x : ℝ} : |iteratedDeriv n sin x| ≤ 1 :=
  abs_iteratedDeriv_sin_cos_le.left

lemma abs_iteratedDeriv_cos_le {n : ℕ} {x : ℝ} : |iteratedDeriv n cos x| ≤ 1 :=
  abs_iteratedDeriv_sin_cos_le.right

lemma hasTemperateGrowth_sin : Function.HasTemperateGrowth sin := by
  refine ⟨contDiff_sin, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact le_trans abs_iteratedDeriv_sin_le (le_add_of_nonneg_right (abs_nonneg x))

lemma hasTemperateGrowth_cos : Function.HasTemperateGrowth cos := by
  refine ⟨contDiff_cos, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact le_trans abs_iteratedDeriv_cos_le (le_add_of_nonneg_right (abs_nonneg x))

lemma hasTemperateGrowth_fourierChar :
    Function.HasTemperateGrowth fun x : ℝ => (Real.fourierChar (Multiplicative.ofAdd x) : ℂ) := by
  simp_rw [Real.fourierChar_apply]
  simp_rw [← Complex.real_smul]
  exact Complex.hasTemperateGrowth_exp_const_mul_real_smul_I

end Real
