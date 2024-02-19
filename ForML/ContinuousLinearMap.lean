import Mathlib.Analysis.Calculus.ContDiff.Bounds

open BigOperators


section Basic

variable {𝕜 α E F G : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup α] [NormedSpace 𝕜 α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- Help (sometimes?) needed for `ContinuousLinearMap.opNorm_comp_le` in `norm_iteratedFDeriv_clm_comp_const`.
noncomputable instance : NormedAddCommGroup (E →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

-- While this is a one-line proof, it has the convenience of not introducing the second term.
lemma HasFDerivAt.clm_apply_const {c : α → F →L[𝕜] G} {v : F} {c' : α →L[𝕜] F →L[𝕜] G} {x : α} (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y => (c y) v) (c'.flip v) x := by
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.clm_apply hc (hasFDerivAt_const v x)) ?_
  simp

-- -- While this is a one-line proof, it has the convenience of not introducing the second term.
-- -- Also, `HasFDerivAt.comp` often requires `change` to have specific form `f ∘ g`?
-- lemma HasFDerivAt.const_clm_apply {c : F →L[𝕜] G} {v : F} {c' : α →L[𝕜] F →L[𝕜] G} {x : α} (hc : HasFDerivAt c c' x) :
--     HasFDerivAt (fun y => (c y) v) (c'.flip v) x := by
--   refine HasFDerivAt.congr_fderiv (HasFDerivAt.clm_apply hc (hasFDerivAt_const v x)) ?_
--   simp

lemma fderiv_clm_apply_const {c : α → F →L[𝕜] G} {v : F} {x : α} (hc : DifferentiableAt 𝕜 c x) :
    fderiv 𝕜 (fun y => (c y) v) x = (fderiv 𝕜 c x).flip v := by
  simp [fderiv_clm_apply hc (differentiableAt_const v)]

lemma fderiv_clm_apply_comm {c : α → F →L[𝕜] G} {v : F} {x m : α} (hc : DifferentiableAt 𝕜 c x) :
    (fderiv 𝕜 (fun y => (c y) v) x) m = (fderiv 𝕜 c x) m v := by
  simp [fderiv_clm_apply_const hc]

lemma HasFDerivAt.clm_comp_const {c : α → F →L[𝕜] G} {u : E →L[𝕜] F} {c' : α →L[𝕜] F →L[𝕜] G} {x : α} (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y => (c y).comp u) (((ContinuousLinearMap.compL 𝕜 E F G).flip u).comp c') x := by
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.clm_comp hc (hasFDerivAt_const u x)) ?_
  rw [ContinuousLinearMap.comp_zero, zero_add]

lemma HasFDerivAt.const_clm_comp {c : F →L[𝕜] G} {u : α → E →L[𝕜] F} {u' : α →L[𝕜] E →L[𝕜] F} {x : α} (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c.comp (u y))) ((ContinuousLinearMap.compL 𝕜 E F G c).comp u') x := by
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.clm_comp (hasFDerivAt_const c x) hu) ?_
  rw [ContinuousLinearMap.comp_zero, add_zero]

lemma norm_iteratedFDeriv_clm_const_apply {n : ℕ} {c : F →L[𝕜] G} {u : α → F} {x : α} (hu : ContDiff 𝕜 n u) :
    ‖iteratedFDeriv 𝕜 n (fun y => c (u y)) x‖ ≤ ‖c‖ * ‖iteratedFDeriv 𝕜 n u x‖ := by
  refine le_trans (norm_iteratedFDeriv_clm_apply contDiff_const hu x (le_refl _)) ?_
  rw [Finset.sum_eq_single 0]
  . simp
  . intro b _ hb
    rw [iteratedFDeriv_const_of_ne hb]
    simp
  . simp

lemma ContinuousLinearMap.opNorm_apply_le {u : E} : ‖apply 𝕜 G u‖ ≤ ‖u‖ := by
  rw [opNorm_le_iff (norm_nonneg _)]
  intro c
  rw [apply_apply, mul_comm]
  exact le_opNorm c u

lemma norm_iteratedFDeriv_clm_comp_const {n : ℕ} {c : α → F →L[𝕜] G} {u : E →L[𝕜] F} {x : α} (hc : ContDiff 𝕜 n c) :
    ‖iteratedFDeriv 𝕜 n (fun y => (c y).comp u) x‖ ≤ ‖u‖ * ‖iteratedFDeriv 𝕜 n c x‖ := by
  -- Use `compL` and `apply` to obtain constant CLM applied to `c y`.
  conv => lhs; arg 1; arg 3; intro y; rw [← ContinuousLinearMap.compL_apply]
  change ‖iteratedFDeriv 𝕜 n (fun y => (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) u).comp (ContinuousLinearMap.compL 𝕜 E F G) (c y)) x‖ ≤ _
  -- Now use `norm_iteratedFDeriv_clm_const_apply` with `u := c`.
  refine le_trans (norm_iteratedFDeriv_clm_const_apply hc) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  rw [← mul_one ‖u‖]
  exact mul_le_mul ContinuousLinearMap.opNorm_apply_le (ContinuousLinearMap.norm_compL_le 𝕜 E F G) (norm_nonneg _) (norm_nonneg _)

end Basic


section Single

variable {ι R : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Semiring R]
variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
variable {φ : ι → Type*} [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)]
  [∀ i, Module R (φ i)]

namespace ContinuousLinearMap

/--
`ContinuousLinearMap` that constructs a one-hot vector; counterpart to `proj`.
Leave `R` implicit to match `ContinuousLinearMap.proj` and `LinearMap.single`.
-/
def single (i : ι) : φ i →L[R] ((i : ι) → φ i) where
  toLinearMap := LinearMap.single i
  cont := continuous_single i

@[simp]
theorem single_apply {i : ι} {x : φ i} : single (R := R) i x = Pi.single i x := rfl

@[simp]
theorem proj_single_apply {i : ι} {x : φ i} : proj (R := R) i (single (R := R) i x) = x := by
  simp

@[simp]
theorem proj_comp_single {i : ι} : (proj i).comp (single i) = id R (φ i) := by ext; simp

-- theorem norm_single_le_one {i : ι} : ‖single (R := R) (φ := φ) i‖ ≤ 1 := by
--   rw [opNorm_le_iff zero_le_one]
--   simp

end ContinuousLinearMap

end Single


section Pi

variable {𝕜 ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {M : Type*} [TopologicalSpace M] [AddCommGroup M]
variable {φ : ι → Type*} [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommGroup (φ i)]
  [∀ i, TopologicalAddGroup (φ i)]

variable [NormedField 𝕜] [Module 𝕜 M] [∀ i, Module 𝕜 (φ i)] [∀ i, ContinuousConstSMul 𝕜 (φ i)]

theorem ContinuousLinearMap.pi_apply'
    {f : (i : ι) → M →L[𝕜] φ i} :
    pi f = ∑ i, (single i).comp (f i) :=
  by ext; simp

end Pi

section PiL

variable {𝕜 ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {X : Type*} [TopologicalSpace X]
variable {M : Type*} [NormedAddCommGroup M]
variable {φ : ι → Type*} [∀ i, NormedAddCommGroup (φ i)]

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 M] [∀ i, NormedSpace 𝕜 (φ i)]
  -- [∀ i, ContinuousConstSMul 𝕜 (φ i)]

namespace ContinuousLinearMap

variable (𝕜 M φ)

theorem pi_eq_sum_single_proj :
    pi (R := 𝕜) (M := M) (φ := φ) =
      ∑ i, comp ((compL 𝕜 M (φ i) ((i : ι) → φ i)) (single i)) (proj i) := by ext; simp

def piL : ((i : ι) → M →L[𝕜] φ i) →L[𝕜] M →L[𝕜] (i : ι) → φ i where
  toFun := pi
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  cont := by
    change Continuous fun f ↦ pi f
    simp only [pi_eq_sum_single_proj, sum_apply]
    exact continuous_finset_sum _ fun i _ ↦ ContinuousLinearMap.continuous _

variable {𝕜 M φ}

theorem piL_apply (f : (i : ι) → M →L[𝕜] φ i) :
    piL 𝕜 M φ f = pi f := rfl

theorem continuous_pi {f : (i : ι) → X → M →L[𝕜] φ i} (hf : ∀ i, Continuous (fun x ↦ f i x)) :
    Continuous (fun x ↦ pi (fun i ↦ f i x)) := by
  simp only [← piL_apply]
  refine .clm_apply continuous_const (_root_.continuous_pi hf)

end ContinuousLinearMap

end PiL


section Map

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : Type*} [TopologicalSpace X]
variable {D : ι → Type*} [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace 𝕜 (D i)]
variable {D₁ : ι → Type*} [∀ i, NormedAddCommGroup (D₁ i)] [∀ i, NormedSpace 𝕜 (D₁ i)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

variable (ι)

def map (f : E →L[𝕜] F) :
    (ι → E) →L[𝕜] (ι → F) where
  toFun x i := f (x i)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

variable {ι}

@[simp]
theorem map_apply (f : E →L[𝕜] F) (x : ι → E) (i : ι) :
    ContinuousLinearMap.map ι f x i = f (x i) := rfl

variable (𝕜 ι E F)

def mapL : (E →L[𝕜] F) →L[𝕜] (ι → E) →L[𝕜] (ι → F) where
  toFun := map ι
  map_add' f g := rfl
  map_smul' c x := rfl
  cont := by
    -- TODO: Simpler proof?
    simp only [Metric.continuous_iff]
    intro g ε hε
    use ε
    refine ⟨hε, ?_⟩
    intro f
    simp only [dist_eq_norm_sub]
    intro h
    refine lt_of_le_of_lt ?_ h
    rw [opNorm_le_iff (opNorm_nonneg (f - g))]
    intro x
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (opNorm_nonneg (f - g)) (norm_nonneg x))]
    simp only [sub_apply, Pi.sub_apply, map_apply]
    simp only [← sub_apply]
    intro i
    refine le_trans (le_opNorm (f - g) (x i)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg (f - g))
    exact norm_le_pi_norm x i

variable {𝕜 ι E F}

-- @[simp]
-- theorem mapL_apply {f : E →L[𝕜] F} {x : ι → E} :
--     mapL 𝕜 ι E F f x = map ι f x := rfl


def piMap (f : (i : ι) → D i →L[𝕜] D₁ i) :
    ((i : ι) → D i) →L[𝕜] ((i : ι) → D₁ i) where
  toFun x i := (f i) (x i)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

theorem piMap_apply_apply {f : (i : ι) → D i →L[𝕜] D₁ i} {x : (i : ι) → D i} :
    piMap f x = fun i ↦ f i (x i) := rfl

theorem piMap_apply {f : (i : ι) → D i →L[𝕜] D₁ i} :
    piMap f = ContinuousLinearMap.pi (fun i ↦ (f i).comp (ContinuousLinearMap.proj i)) := rfl

variable (𝕜 D D₁)

def piMapL : ((i : ι) → D i →L[𝕜] D₁ i) →L[𝕜] ((i : ι) → D i) →L[𝕜] ((i : ι) → D₁ i) where
  toFun := piMap
  map_add' f g := rfl
  map_smul' c x := rfl
  cont := by
    simp only
    change Continuous fun f ↦ ContinuousLinearMap.piMap f
    simp only [piMap_apply]
    exact continuous_pi fun i ↦ .clm_comp (continuous_apply i) (continuous_const)

variable {𝕜 D D₁}

theorem piMapL_apply {f : (i : ι) → D i →L[𝕜] D₁ i} :
    piMapL 𝕜 D D₁ f = piMap f := rfl

theorem continuous_piMap {f : (i : ι) → X → E →L[𝕜] F} (hf : ∀ i, Continuous (fun x ↦ f i x)) :
    Continuous (fun x ↦ piMap (fun i ↦ f i x)) := by
  simp only [← piMapL_apply]
  exact .clm_apply continuous_const (_root_.continuous_pi hf)

end ContinuousLinearMap

end Map
