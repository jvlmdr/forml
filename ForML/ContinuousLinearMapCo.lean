import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi

import ForML.PiEquiv

open scoped BigOperators


variable {ι R : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NontriviallyNormedField R]
variable {M₁ M₂ : Type*}
variable [NormedAddCommGroup M₁] [NormedSpace R M₁]
variable [NormedAddCommGroup M₂] [NormedSpace R M₂]
variable {M : ι → Type*}
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace R (M i)]
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace R F]

-- Help sometimes needed to use `bilinearComp_apply` in `coprodL_apply`?
noncomputable instance : SeminormedAddCommGroup ((M₁ →L[R] F) × (M₂ →L[R] F)) := Prod.seminormedAddCommGroup
noncomputable instance : NormedSpace R ((M₁ →L[R] F) × (M₂ →L[R] F)) := Prod.normedSpace

lemma Function.update_eq_add_sum_filter_single {i : ι} {x : ∀ i, M i} {xi : M i} :
    Function.update x i xi = Pi.single i xi + ∑ k in Finset.univ.filter (fun k => k ≠ i), Pi.single k (x k) := by
  ext j
  simp
  by_cases h : j = i <;> simp [h]
  rw [Pi.single]
  simp [update, h]

lemma Function.update_eq_sum_single {i : ι} {x : ∀ i, M i} {xi : M i} :
    Function.update x i xi = ∑ j, if j = i then Pi.single i xi else Pi.single j (x j) := by
  ext j
  simp [ite_apply]
  rw [Finset.sum_eq_single j]
  . by_cases h : j = i <;> simp [h]
    rw [h]
    simp
  . simp
    intro k hkj
    simp [hkj]
    intro hki
    rw [hki] at hkj
    simp [hkj]
  . simp


lemma Pi.norm_single_le_norm {i : ι} {u : M i} : ‖Pi.single i u‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  by_cases h : j = i <;> simp [h]
  rw [h]
  simp

-- Uses `NormOneClass.norm_one`.
lemma Pi.norm_single_one_le_one {𝕜 : Type*} [NormedField 𝕜] {i : ι} : ‖Pi.single (f := fun _ : ι => 𝕜) i 1‖ ≤ 1 := by
  refine le_trans norm_single_le_norm ?_
  simp


namespace ContinuousLinearMap

/--
`ContinuousLinearMap` that constructs a one-hot vector; counterpart to `proj`.
Leave `R` implicit to match `ContinuousLinearMap.proj` and `LinearMap.single`.
-/
def single (i : ι) : M i →L[R] (∀ i, M i) where
  toLinearMap := LinearMap.single i
  cont := continuous_single i

@[simp] lemma single_apply {i : ι} {x : M i} : single (R := R) i x = Pi.single i x := rfl

@[simp] lemma proj_single_apply {i : ι} {x : M i} : proj (R := R) i (single (R := R) i x) = x := by simp

@[simp] lemma proj_comp_single {i : ι} : (proj i).comp (single i) = id R (M i) := by
  ext x
  simp

lemma norm_single_le_one {i : ι} : ‖single (R := R) (M := M) i‖ ≤ 1 := by
  rw [op_norm_le_iff zero_le_one]
  simp
  intro x
  exact Pi.norm_single_le_norm


/-- Analogy of `coprod` for pi types; same as the application of `LinearMap.lsum`. -/
def copi (f : ∀ i, M i →L[R] F) : (∀ i, M i) →L[R] F where
  toFun x := ∑ i, (f i) (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

-- Equivalent to application of `LinearMap.lsum`.
example {f : ∀ i, M i →L[R] F} {x : ∀ i, M i} : copi f x = LinearMap.lsum R M R (fun i => (f i).toLinearMap) x := by
  simp [copi, LinearMap.lsum_apply]

section Def
variable (R M F)

/-- `copi` as a bilinear `ContinuousLinearMap`. -/
noncomputable def copiL : (∀ i, M i →L[R] F) →L[R] (∀ i, M i) →L[R] F :=
  ∑ i, bilinearComp (apply R F).flip (proj i) (proj i)

end Def

@[simp]
lemma copiL_apply {f : ∀ i, M i →L[R] F} : copiL R M F f = copi f := by
  ext x
  rw [copiL]
  rw [sum_apply, sum_apply]
  rfl

lemma copiL_coe : ⇑(copiL R M F) = copi := by
  ext x
  simp

/-- The inverse of `copi`; same as the application of `LinearMap.lsum.symm`. -/
def invcopi (f : (∀ i, M i) →L[R] F) : ∀ i, (M i →L[R] F) :=
  fun i => f.comp (single i)

-- Equivalent to application of `LinearMap.lsum.symm`.
example {f : (∀ i, M i) →L[R] F} {x : ∀ i, M i} :
    (fun i => invcopi f i (x i)) = fun i => ((LinearMap.lsum R M R).symm f.toLinearMap i (x i)) :=
  rfl

section Def
variable (R M F)

/-- `invcopi` as a `ContinuousLinearMap`. -/
noncomputable def invcopiL : ((∀ i, M i) →L[R] F) →L[R] ∀ i, (M i →L[R] F) :=
  pi (fun i => (comp (apply R F) (single i)).flip)

end Def

@[simp]
lemma invcopiL_apply {f : (∀ i, M i) →L[R] F} : invcopiL R M F f = invcopi f := rfl

lemma invcopiL_coe : ⇑(invcopiL R M F) = invcopi := rfl


lemma copi_apply {f : ∀ i, M i →L[R] F} {x : ∀ i, M i} :
    copi f x = ∑ i, f i (x i) := rfl

@[simp]
lemma copi_empty [IsEmpty ι] {f : ∀ i, M i →L[R] F} {x : ∀ i, M i} : copi f x = 0 := by
  simp [copi_apply]

@[simp]
lemma copi_single {f : ∀ i, M i →L[R] F} {i : ι} {xi : M i} :
    copi f (Pi.single i xi) = (f i) xi := by
  simp [copi_apply]
  rw [Finset.sum_eq_single i]
  . simp
  . simp
    intro j hj
    simp [hj]
  . simp

@[simp]
lemma copi_add_apply {f g : ∀ i, M i →L[R] F} :
    copi (f + g) = copi f + copi g := by
  rw [← copiL_apply, map_add]
  simp

@[simp]
lemma copi_smul_apply {c : R} {f : ∀ i, M i →L[R] F} :
    copi (c • f) = c • copi f := by
  rw [← copiL_apply, map_smul]
  simp

lemma copi_eq_sum_comp_proj {f : ∀ i, M i →L[R] F} :
    copi f = ∑ i, (f i).comp (proj i) := by
  ext x
  simp [copi_apply]

lemma copi_eq_sum_compL_proj {f : ∀ i, M i →L[R] F} :
    copi f = ∑ i, ContinuousLinearMap.compL _ _ _ _ (f i) (proj i) := by
  ext x
  simp
  rw [ContinuousLinearMap.sum_apply]
  conv => rhs; arg 2; intro i; rw [comp_apply]


lemma invcopi_apply {f : (∀ i, M i) →L[R] F} {i : ι} {xi : M i} :
    invcopi f i xi = f (Pi.single i xi) := rfl

@[simp]
lemma sum_apply_single {f : (∀ i, M i) →L[R] F} {x : ∀ i, M i} :
    ∑ j : ι, f (Pi.single j (x j)) = f x := by
  rw [← _root_.map_sum]
  congr
  ext i
  simp

@[simp]
lemma sum_comp_single_apply {f : (∀ i, M i) →L[R] F} {x : ∀ i, M i} :
    ∑ j : ι, f.comp (single j) (x j) = f x := by
  simp

@[simp]
lemma copi_comp_single {f : (∀ i, M i) →L[R] F} :
    copi (fun j => (f.comp (single j))) = f := by
  ext x
  simp [copi_apply]

@[simp]
lemma sum_invcopi_apply {f : (∀ i, M i) →L[R] F} {x : ∀ i, M i} :
    ∑ j : ι, (invcopi f j) (x j) = f x := by
  simp [invcopi_apply]

@[simp]
lemma copi_invcopoi {f : (∀ i, M i) →L[R] F} :
    copi (fun j => invcopi f j) = f := by
  ext x
  simp [copi_apply]

/-
lemma fderiv_eq_copi_fderiv_comp_single {f : (∀ i, M i) → F} {x : (∀ i, M i)} :
    fderiv 𝕜 f x = ContinuousLinearMap.copi (fun i => (fderiv 𝕜 f x).comp (ContinuousLinearMap.single i)) := by
-/

@[simp]
lemma invcopi_copi_apply {f : ∀ i, (M i →L[R] F)} : invcopi (copi f) = f := by
  ext i xi
  rw [invcopi_apply]
  simp

@[simp]
lemma copi_invcopi_apply {f : (∀ i, M i) →L[R] F} : copi (invcopi f) = f := by
  ext i
  rw [copi_apply]
  simp

@[simp]
lemma invcopiL_comp_copiL : (invcopiL R M F).comp (copiL R M F) = ContinuousLinearMap.id R (∀ i, M i →L[R] F) := by
  ext f i xi
  simp [copiL_apply, invcopiL_apply]

@[simp]
lemma copiL_comp_invcopiL : (copiL R M F).comp (invcopiL R M F) = ContinuousLinearMap.id R ((∀ i, M i) →L[R] F) := by
  ext f x
  simp [copiL_apply, invcopiL_apply]

@[simp]
lemma leftInverse_copi : Function.LeftInverse invcopi (copi (R := R) (M := M) (F := F)) :=
  fun _ => invcopi_copi_apply

@[simp]
lemma rightInverse_copi : Function.RightInverse invcopi (copi (R := R) (M := M) (F := F)) :=
  fun _ => copi_invcopi_apply

lemma eq_invcopi_iff_copi_apply_eq {f : ∀ i, M i →L[R] F} {g : (∀ i, M i) →L[R] F} :
    copi f = g ↔ f = invcopi g := by
  refine Iff.intro ?_ ?_
  . intro h
    simp [← h]
  . intro h
    simp [h]


section Def

variable (R M F)

/-- `ContinuousLinearEquiv` version of `LinearMap.lsum`. -/
noncomputable def lsum : (∀ i, M i →L[R] F) ≃L[R] (∀ i, M i) →L[R] F where
  toFun := copiL R M F
  invFun := invcopiL R M F
  map_add' f g := ContinuousLinearMap.map_add _ f g
  map_smul' c f := ContinuousLinearMap.map_smul _ c f
  left_inv := by
    simp
    change Function.LeftInverse (fun f => invcopiL R M F f) (fun f => copiL R M F f)
    simp_rw [invcopiL_apply, copiL_apply]
    exact leftInverse_copi
  right_inv := by
    simp
    change Function.RightInverse (fun f => invcopiL R M F f) (fun f => copiL R M F f)
    simp_rw [invcopiL_apply, copiL_apply]
    exact rightInverse_copi

end Def

lemma lsum_apply_eq_copiL {f : ∀ i, M i →L[R] F} :
    lsum R M F f = copiL R M F f := rfl

lemma lsum_symm_apply_eq_invcopiL {f : (∀ i, M i) →L[R] F} :
    (lsum R M F).symm f = invcopiL R M F f := rfl

-- example {x y : F} {hx : ‖x‖ ≤ 1} {hy : ‖y‖ ≤ 1} (h : 1 ≤ ‖x‖ * ‖y‖) : ‖x‖ = 1 := by
--   suffices : 1 ≤ ‖x‖
--   . exact le_antisymm hx this
--   refine le_trans h ?_
--   refine mul_le_of_le_one_right (norm_nonneg _) ?_
--   exact hy

-- noncomputable def lsumₗᵢ : (∀ i, M i →L[R] F) ≃ₗᵢ[R] (∀ i, M i) →L[R] F where
--   toLinearEquiv := (lsum R M F).toLinearEquiv
--   norm_map' := fun f => by
--     simp
--     rw [lsum_apply_eq_copiL]
--     refine ContinuousLinearMap.op_norm_eq_of_bounds (norm_nonneg _) ?_ ?_
--     . intro x
--       simp [Pi.norm_def]
--       simp [copiL_apply, copi_apply]
--       refine le_trans (norm_sum_le _ _) ?_
--       sorry
--     sorry
--     -- suffices : ‖copiL R M F‖ = 1
--     -- .
--     --   sorry
--     -- simp

-- variable {f : (∀ i, M i) →L[R] F} {i : ι}
-- #check invcopi f i

-- lemma copi_comp_proj {f : (∀ i, M i) →L[R] F} {x : ∀ i, M i} :
--     copi (fun i => comp f (proj (φ := M) i)) x = sorry := by
--   simp [copi_apply]

section Coprod

lemma coprod_eq_comp_fst_add_comp_snd {f : M₁ →L[R] F} {g : M₂ →L[R] F} :
    coprod f g = f.comp (fst R M₁ M₂) + g.comp (snd R M₁ M₂) := by
  ext x <;> simp [coprod_apply, comp_apply]

section Def
variable (R M₁ M₂ F)

/-- `coprod` as a bilinear `ContinuousLinearMap`. -/
noncomputable def coprodL : (M₁ →L[R] F) × (M₂ →L[R] F) →L[R] M₁ × M₂ →L[R] F :=
  bilinearComp (apply R F).flip (fst R (M₁ →L[R] F) (M₂ →L[R] F)) (fst R M₁ M₂) +
  bilinearComp (apply R F).flip (snd R (M₁ →L[R] F) (M₂ →L[R] F)) (snd R M₁ M₂)

end Def

lemma coprodL_apply {f : (M₁ →L[R] F) × (M₂ →L[R] F)} :
    coprodL R M₁ M₂ F f = coprod f.1 f.2 := by
  refine ContinuousLinearMap.ext ?_
  intro x
  simp [coprodL]
  rw [add_apply, add_apply]
  rw [bilinearComp_apply, bilinearComp_apply]
  simp


def invcoprod (f : M₁ × M₂ →L[R] F) : (M₁ →L[R] F) × (M₂ →L[R] F) :=
  (f.comp (inl R M₁ M₂), f.comp (inr R M₁ M₂))

@[simp]
lemma invcoprod_fst_apply {f : M₁ × M₂ →L[R] F} {x : M₁} :
    (invcoprod f).1 x = f (x, 0) := by
  simp [invcoprod]

@[simp]
lemma invcoprod_snd_apply {f : M₁ × M₂ →L[R] F} {x : M₂} :
    (invcoprod f).2 x = f (0, x) := by
  simp [invcoprod]

@[simp]
lemma coprod_invcoprod_apply {f : M₁ × M₂ →L[R] F} : coprod (invcoprod f).1 (invcoprod f).2 = f := by
  ext x <;> simp

@[simp]
lemma invcoprod_coprod_apply {f : (M₁ →L[R] F) × (M₂ →L[R] F)} : invcoprod (coprod f.1 f.2) = f := by
  ext x <;> simp

section Def
variable (R M₁ M₂ F)

-- TODO: Review. Not sure if this is most natural, I just made the types work.
noncomputable def invcoprodL : (M₁ × M₂ →L[R] F) →L[R] (M₁ →L[R] F) × (M₂ →L[R] F) :=
  ContinuousLinearMap.prod
    ((compL R M₁ (M₁ × M₂) F).flip (inl R M₁ M₂))
    ((compL R M₂ (M₁ × M₂) F).flip (inr R M₁ M₂))

end Def

lemma invcoprodL_apply {f : M₁ × M₂ →L[R] F} : invcoprodL R M₁ M₂ F f = invcoprod f := by
  ext x <;> {
    simp [invcoprodL]
    rw [ContinuousLinearMap.comp_apply]
    simp
  }


section Def
variable (R M)

/-- `Function.update` as a `ContinuousLinearMap` on a pair. -/
def updateL (i : ι) : (∀ i, M i) × M i →L[R] (∀ i, M i) :=
    (single i).comp (snd R (∀ i, M i) (M i)) +
    pi (fun j => if j = i then 0 else (proj j).comp (fst R (∀ i, M i) (M i)))

end Def

lemma updateL_apply {i : ι} {x : ∀ i, M i} {xi : M i} :
    updateL R M i (x, xi) = Function.update x i xi := by
  ext j
  simp [updateL]
  by_cases h : j = i <;> simp [h]
  rw [h]
  simp

end Coprod

end ContinuousLinearMap  -- namespace
