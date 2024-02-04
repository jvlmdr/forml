import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace

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

@[simp] lemma one_le_one_add_norm_pow_const (x : α) (k : ℕ) : 1 ≤ (1 + ‖x‖) ^ k :=
  one_le_pow_of_one_le (one_le_one_add_norm x) k

@[simp] lemma one_add_norm_rpow_const_pos (x : α) (r : ℝ) : 0 < (1 + ‖x‖) ^ r :=
  Real.rpow_pos_of_pos (one_add_norm_pos x) r

@[simp] lemma one_add_norm_rpow_const_nonneg (x : α) (r : ℝ) : 0 ≤ (1 + ‖x‖) ^ r :=
  (one_add_norm_rpow_const_pos x r).le

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


section DerivComp

variable {𝕜 𝕜' F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NontriviallyNormedField F] [NormedAlgebra 𝕜 F] [NormedAlgebra 𝕜' F]
variable [IsScalarTower 𝕜 𝕜' F]

lemma HasDerivAt.comp_of_tower (x : 𝕜) {g : 𝕜 → 𝕜'} {f : 𝕜' → F} {g' : 𝕜'} {f' : F}
    (hf : HasDerivAt f f' (g x))
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f (g x)) (g' • f') x := by
  rw [hasDerivAt_iff_hasFDerivAt] at hf hg ⊢
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.comp x (hf.restrictScalars 𝕜) hg) ?_
  refine ContinuousLinearMap.ext ?_
  intro m
  simp

lemma deriv.comp_of_tower (x : 𝕜) {g : 𝕜 → 𝕜'} {f : 𝕜' → F}
    (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun x => f (g x)) x = deriv g x • deriv f (g x) := by
  rw [← hasDerivAt_deriv_iff] at hf hg
  exact (HasDerivAt.comp_of_tower x hf hg).deriv

/-- Utility lemma as it can be easier to rewrite in `deriv` form. -/
lemma HasDerivAt.of_deriv (x : 𝕜) {f : 𝕜 → F} {f' : 𝕜 → F} (h : DifferentiableAt 𝕜 f x) (h' : _root_.deriv f x = f' x) :
    HasDerivAt f (f' x) x := by
  rw [← h']
  exact h.hasDerivAt

/-- Utility lemma as it can be easier to rewrite in `deriv` form. -/
lemma HasDerivAt.comp_of_deriv (x : 𝕜) {f : 𝕜' → F} {g : 𝕜 → 𝕜'} {fg' : 𝕜 → F}
    (hf : DifferentiableAt 𝕜 f (g x))
    (hg : DifferentiableAt 𝕜 g x)
    (hf' : _root_.deriv (fun x => f (g x)) x = fg' x) :
    HasDerivAt (fun x => f (g x)) (fg' x) x := by
  rw [← hf']
  refine DifferentiableAt.hasDerivAt ?_
  exact DifferentiableAt.comp x hf hg

/-- Utility lemma as it can be easier to rewrite in `deriv` form. -/
lemma HasDerivAt.comp_of_deriv' (x : 𝕜) {f : 𝕜' → F} {g : 𝕜 → 𝕜'} {fg' : 𝕜 → F}
    (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x)
    (hf' : _root_.deriv g x • _root_.deriv f (g x) = fg' x) :
    HasDerivAt (fun x => f (g x)) (fg' x) x := by
  rw [← hf']
  exact comp_of_tower x hf.hasDerivAt hg.hasDerivAt

end DerivComp


section Parts

variable {𝕜 S E F G : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
variable [NontriviallyNormedField S] [NormedSpace S G]
variable [NormedSpace ℝ S] [SMulCommClass ℝ S G] [IsScalarTower ℝ S G]
variable [NormedSpace 𝕜 S] [SMulCommClass 𝕜 S G] [IsScalarTower 𝕜 S G]

lemma HasDerivAt.bilin {u : 𝕜 → E} {u' : E} {v : 𝕜 → F} {v' : F} (B : E →L[𝕜] F →L[𝕜] G) {x : 𝕜}
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun x => B (u x) (v x)) (B u' (v x) + B (u x) v') x := by
  rw [hasDerivAt_iff_hasFDerivAt] at hu hv ⊢
  refine (ContinuousLinearMap.hasFDerivAt_of_bilinear B hu hv).congr_fderiv ?_
  refine ContinuousLinearMap.ext ?_
  intro dx
  simp [ContinuousLinearMap.precompL]
  rw [add_comm]

lemma ContinuousOn.bilin {u : 𝕜 → E} {v : 𝕜 → F} {B : E →L[𝕜] F →L[𝕜] G} {s : Set 𝕜}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun x => B (u x) (v x)) s :=
  B.isBoundedBilinearMap.continuous.comp_continuousOn (hu.prod hv)

lemma Continuous.bilin {u : 𝕜 → E} {v : 𝕜 → F} {B : E →L[𝕜] F →L[𝕜] G}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => B (u x) (v x)) :=
  B.isBoundedBilinearMap.continuous.comp (hu.prod_mk hv)

section Def
variable (𝕜 S G)

/-- Scalar multiplication for `IsScalarTower 𝕜 S G` as a `𝕜`-bilinear map. -/
noncomputable def ContinuousLinearMap.smulBilin : G →L[𝕜] S →L[𝕜] G :=
  LinearMap.mkContinuous₂
    { toFun := fun x => LinearMap.smulRight LinearMap.id x,
      map_add' := fun x y => by simp; ext m; simp,
      map_smul' := fun c x => by simp; ext m; simp; rw [← smul_comm]}
    1 (fun x c => by simp [norm_smul]; rw [mul_comm])

end Def

section Explicit
variable (𝕜)

@[simp]
lemma ContinuousLinearMap.smulBilin_apply {x : G} {c : S} : smulBilin 𝕜 S G x c = c • x := rfl

-- Can be used to rewrite scalar multiplication as application of a bilinear CLM.
lemma ContinuousLinearMap.flip_smulBilin_apply {x : G} {c : S} : (smulBilin 𝕜 S G).flip c x = c • x := rfl

end Explicit

/-- `smulBilin` with `S = k` is equal to `smulRightL id`. -/
lemma ContinuousLinearMap.smulRightL_id_eq_smulBilin :
    smulBilin 𝕜 𝕜 G = (smulRightL 𝕜 𝕜 G) (id 𝕜 𝕜) := rfl

/-- `smulRight` can be rewritten as composition with `smulBilin`. -/
lemma ContinuousLinearMap.smulRight_eq_smulBilin_comp {c : G →L[𝕜] S} {x : G} :
    smulRight c x = (smulBilin 𝕜 S G x).comp c := rfl

/-- Scalar multiplication of a `ContinuousLinearMap` can be rewritten as composition with `smulBilin`. -/
lemma ContinuousLinearMap.smul_clm_eq_smulBilin_flip_comp {c : S} {f : G →L[𝕜] G} :
    c • f = ((smulBilin 𝕜 S G).flip c).comp f := rfl

/--
Integration by parts for a general bilinear map.

TODO: Might be possible to relax `ContinuousOn` to `IntervalIntegrable` if there exists a lemma
which is analogous to `IntervalIntegrable.mul_continuousOn` for bilinear CLMs.
-/
theorem intervalIntegral.integral_deriv_bilin_eq_sub {u u' : ℝ → E} {v v' : ℝ → F} (B : E →L[ℝ] F →L[ℝ] G)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b))
    (hv' : ContinuousOn v' (Set.uIcc a b)) :
    ∫ x in a..b, B (u' x) (v x) + B (u x) (v' x) = B (u b) (v b) - B (u a) (v a) := by
  refine integral_eq_sub_of_hasDerivAt (fun x hx => HasDerivAt.bilin B (hu x hx) (hv x hx)) ?_
  refine (ContinuousOn.add ?_ ?_).intervalIntegrable
  . exact ContinuousOn.bilin hu' (HasDerivAt.continuousOn hv)
  . exact ContinuousOn.bilin (HasDerivAt.continuousOn hu) hv'

/--
Integration by parts for a general bilinear map.

This must use `ℝ`-linearity because `u` and `v` are differentiable functions on `ℝ`.
-/
theorem intervalIntegral.integral_bilin_deriv_eq_deriv_bilin {u u' : ℝ → E} {v v' : ℝ → F} (B : E →L[ℝ] F →L[ℝ] G)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b))
    (hv' : ContinuousOn v' (Set.uIcc a b)) :
    ∫ x in a..b, B (u x) (v' x) = B (u b) (v b) - B (u a) (v a) - ∫ x in a..b, B (u' x) (v x) := by
  rw [← integral_deriv_bilin_eq_sub B hu hv hu' hv']
  rw [← integral_sub]
  · simp
  . refine (ContinuousOn.add ?_ ?_).intervalIntegrable
    . exact ContinuousOn.bilin hu' (HasDerivAt.continuousOn hv)
    . exact ContinuousOn.bilin (HasDerivAt.continuousOn hu) hv'
  · exact (ContinuousOn.bilin hu' (HasDerivAt.continuousOn hv)).intervalIntegrable

/-- Integration by parts for smul. -/
lemma intervalIntegral.integral_deriv_smul_eq_sub {u u' : ℝ → S} {v v' : ℝ → G}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b))
    (hv' : ContinuousOn v' (Set.uIcc a b)) :
    ∫ x in a..b, u' x • v x + u x • v' x = u b • v b - u a • v a :=
  integral_deriv_bilin_eq_sub (ContinuousLinearMap.smulBilin ℝ S G).flip hu hv hu' hv'

/-- Integration by parts for smul. -/
theorem intervalIntegral.integral_smul_deriv_eq_deriv_smul {u u' : ℝ → S} {v v' : ℝ → G}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b))
    (hv' : ContinuousOn v' (Set.uIcc a b)) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_bilin_deriv_eq_deriv_bilin (ContinuousLinearMap.smulBilin ℝ S G).flip hu hv hu' hv'

end Parts


section LinearInner

variable {𝕜 : Type*} [IsROrC 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜)

theorem norm_innerSL_le_one : ‖innerSL 𝕜 (E := E)‖ ≤ 1 := by
  simp [ContinuousLinearMap.op_norm_le_iff]

end LinearInner
