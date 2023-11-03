import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Real Complex

section Differentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAlgebra 𝕜 ℂ]  -- `NormedAlgebra` instead of `NormedSpace` for `Complex.differentiable_exp`
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' ℂ]
variable [IsScalarTower 𝕜 𝕜' ℂ]

lemma Differentiable.cexp_smul_I {f : E → 𝕜'} (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x • (I : ℂ)) := by
  change Differentiable 𝕜 (Complex.exp ∘ (fun x => f x • I))
  refine Differentiable.comp Complex.differentiable_exp ?_
  exact Differentiable.smul_const hf I

lemma iteratedDeriv_const_smul_apply {n : ℕ} (a : 𝕜') {f : 𝕜 → 𝕜'} (hf : ContDiff 𝕜 n f) (x : 𝕜) :
    iteratedDeriv n (fun x => a • f x) x = a • iteratedDeriv n f x := by
  change iteratedDeriv n (a • f) x = _
  simp only [iteratedDeriv]
  simp [iteratedFDeriv_const_smul_apply hf]

end Differentiable


namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜']

lemma deriv_exp_smul_I_apply {f : 𝕜 → ℝ} (hf : Differentiable 𝕜 f) (x : 𝕜) :
    deriv (fun x => Complex.exp (f x • I)) x = cexp (f x • I) * (deriv f x • I) := by
  change deriv (Complex.exp ∘ (fun x => f x • I)) x = _
  rw [deriv.comp _ differentiableAt_exp]
  swap
  . refine Differentiable.differentiableAt ?_
    exact Differentiable.smul_const hf I
  rw [deriv_smul_const (Differentiable.differentiableAt hf)]
  simp

-- TODO: Could make more general than `ℝ`?
lemma deriv_exp_real_const_mul_smul_I_apply {a : ℝ} (x : ℝ) :
    deriv (fun (x : ℝ) => exp ((a * x) • I)) x =
    (a • I) * exp ((a * x) • I) := by
  rw [deriv_exp_smul_I_apply]
  swap
  . exact Differentiable.const_mul differentiable_id a
  rw [mul_comm]
  congr
  rw [deriv_const_mul _ differentiableAt_id]
  simp

lemma iteratedDeriv_exp_real_const_mul_smul_I_apply {n : ℕ} {a : ℝ} (x : ℝ) :
    iteratedDeriv n (fun (x : ℝ) => exp ((a * x) • I)) x =
    HPow.hPow (a • I) n * exp ((a * x) • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_real_const_mul_smul_I_apply]
    simp only [← smul_eq_mul]
    rw [iteratedDeriv_const_smul_apply] <;> simp only [smul_eq_mul]
    swap
    . -- TODO: Could extract this as `ContDiff.cexp_smul_I`?
      refine ContDiff.cexp ?_
      refine ContDiff.smul ?_ contDiff_const
      refine ContDiff.smul contDiff_const contDiff_id
    rw [hi]
    rw [mul_assoc]

-- TODO: Generalize to `a * x + b`, or `f x` with bound on growth?
lemma Complex.hasTemperateGrowth_exp_const_mul_real_smul_I {a : ℝ} : Function.HasTemperateGrowth
    fun (x : ℝ) => exp ((a * x) • I) := by
  refine And.intro ?_ ?_
  . refine ContDiff.cexp ?_
    refine ContDiff.smul ?_ contDiff_const
    exact ContDiff.mul contDiff_const contDiff_id
  . intro n
    refine Exists.intro n ?_
    refine Exists.intro (HPow.hPow |a| n) ?_
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [iteratedDeriv_exp_real_const_mul_smul_I_apply]
    simp [abs_of_pos, Real.pi_pos]
    norm_cast
    rw [abs_exp_ofReal_mul_I]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg a) n)
    exact one_le_pow_of_one_le (by simp) n

end Complex


namespace Real

lemma Real.hasTemperateGrowth_sin : Function.HasTemperateGrowth fun x => sin x := by
  refine ⟨contDiff_sin, ?_⟩
  simp
  intro n
  refine ⟨1, ⟨1, ?_⟩⟩
  simp
  intro x
  refine le_trans ?_ (le_add_of_nonneg_right (abs_nonneg x))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp [← Complex.sin_ofReal_re]
  sorry

  -- induction n with
  -- | zero => simp; exact abs_sin_le_one x
  -- | succ n hi =>
  --   simp at hi ⊢
  --   simp [iteratedDeriv_succ']
  --   sorry

  --   -- have : cos = fun x => sin (x + π / 2)
  --   -- . sorry
  --   -- simp [this]
  --   -- sorry

  --   -- cases n with
  --   -- | zero => simp; exact abs_cos_le_one x
  --   -- | succ n =>
  --   --   simp [iteratedDeriv_succ']
  --   --   sorry

end Real
