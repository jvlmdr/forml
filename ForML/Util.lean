import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open SchwartzSpace

-- Define some handy `simp` lemmas for `1 + ‖x‖`.
section OneAddNorm
variable {α : Type*} [SeminormedAddGroup α]

@[simp] lemma one_add_norm_pos (x : α) : 0 < 1 + ‖x‖ :=
  add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)

@[simp] lemma one_add_norm_nonneg (x : α) : 0 ≤ 1 + ‖x‖ :=
  le_of_lt (one_add_norm_pos x)

@[simp] lemma one_add_norm_ne_zero (x : α) : 1 + ‖x‖ ≠ 0 :=
  ne_of_gt (one_add_norm_pos x)

@[simp] lemma one_le_one_add_norm (x : α) : 1 ≤ 1 + ‖x‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

@[simp] lemma one_le_pow_one_add_norm (x : α) (k : ℕ) : 1 ≤ (1 + ‖x‖) ^ k :=
  one_le_pow_of_one_le (one_le_one_add_norm x) k

end OneAddNorm


namespace SchwartzMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
lemma neg_apply {f : 𝓢(E, F)} {x : E} : (-f) x = -f x := rfl

end SchwartzMap


section Exponential

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

-- TODO: Would it make sense to provide this for `𝕜`-linearity?
/-- Analogy of `fderiv_exp` for complex exponential. -/
lemma fderiv_cexp_real {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Complex.exp (f x)) x = Complex.exp (f x) • fderiv ℝ f x := by
  change fderiv ℝ (Complex.exp ∘ f) x = _
  rw [fderiv.comp x Complex.differentiable_exp.differentiableAt hf]
  rw [(Complex.hasStrictFDerivAt_exp_real (f x)).hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.one_def]

end Exponential


section ContDiff

variable {𝕜 𝕜' E F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

lemma contDiff_smul_of_tower {n : ℕ∞} : ContDiff 𝕜 n fun p : (𝕜' × F) => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff

lemma ContDiff.smul_of_tower {n : ℕ∞} {f : E → 𝕜'} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x • g x :=
  contDiff_smul_of_tower.comp (hf.prod hg)

end ContDiff


section IteratedFDeriv

variable {𝕜 𝕜' E F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [Semiring 𝕜'] [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [ContinuousConstSMul 𝕜' F]

-- Easier to use (issue with eta rewrite?).
lemma iteratedFDeriv_neg_apply' {x : E} {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (fun x => -f x) x = -iteratedFDeriv 𝕜 i f x := by
  rw [← iteratedFDeriv_neg_apply]
  rfl

-- Easier to use (issue with eta rewrite?).
lemma iteratedFDeriv_const_smul_apply' {i : ℕ} {a : 𝕜'} {f : E → F} {x : E} (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (fun x => a • f x) x = a • iteratedFDeriv 𝕜 i f x := by
  rw [← iteratedFDeriv_const_smul_apply hf]
  rfl

end IteratedFDeriv
