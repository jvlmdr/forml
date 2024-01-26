import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import Mathlib.MeasureTheory.Integral.Bochner

import ForML.MultilinearDeriv  -- TODO: Extract or unify common bits.

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory

attribute [-simp] Matrix.zero_empty


variable {α : Type*} [MeasurableSpace α]

section Fintype

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {D : ι → Type*} [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [CompleteSpace F]

/--
Application of a `ContinuousMultilinearMap` can be moved outside the integral.
Multilinear version of `ContinuousLinearMap.integral_apply`.
-/
theorem ContinuousMultilinearMap.integral_apply {c : α → ContinuousMultilinearMap ℝ D F}
    {μ : Measure α} (hc : Integrable c μ) {m : ∀ i, D i} :
    ∫ x, (c x) m ∂μ = (∫ x, c x ∂μ) m := by
  change ∫ x, ContinuousMultilinearMap.apply _ _ _ m (c x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hc]
  rfl

theorem ContinuousMultilinearMap.integrable_of_integrable_apply {c : α → ContinuousMultilinearMap ℝ D F}
    {μ : Measure α} (hc : ∀ m, Integrable (fun x => c x m) μ) :
    Integrable c μ := by

  sorry

end Fintype


-- Originally attempted to prove `integral_apply_comm` with induction on `Fin n` and then equivalence.

-- section Fin

-- variable {n : ℕ}
-- variable {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
-- variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

-- theorem ContinuousMultilinearMap.integral_fin_apply_comm
--     {c : α → ContinuousMultilinearMap ℝ E F}
--     {μ : Measure α} (hc : Integrable c μ) {m : ∀ i, E i} :
--     ∫ x, (c x) m ∂μ = (∫ x, c x ∂μ) m := by
--   induction n with
--   | zero =>
--     rw [Subsingleton.elim m 0]
--     conv =>
--       rhs; arg 1; arg 2; intro x
--       rw [← (continuousMultilinearIsEmptyEquiv ℝ E F).left_inv (c x)]
--       change (continuousMultilinearIsEmptyEquiv ℝ E F).symm.toContinuousLinearEquiv
--           ((continuousMultilinearIsEmptyEquiv ℝ E F) (c x))
--     rw [ContinuousLinearEquiv.integral_comp_comm]
--     simp
--   | succ n ih =>
--     rw [← Fin.cons_self_tail m]
--     conv =>
--       lhs; arg 2; intro x
--       rw [← continuousMultilinearCurryLeftEquiv_symm_apply]
--     rw [ih]
--     swap
--     . refine Integrable.apply_continuousLinearMap ?_ _
--       -- TODO: Avoid repetition here?
--       change Integrable (μ := μ) fun x => (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap (c x)
--       exact ContinuousLinearMap.integrable_comp _ hc
--     rw [← ContinuousLinearMap.integral_apply]
--     swap
--     . change Integrable (μ := μ) fun x => (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap (c x)
--       exact ContinuousLinearMap.integrable_comp _ hc
--     conv =>
--       lhs; arg 1; arg 1; arg 2; intro x
--       change (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv (c x)
--     rw [ContinuousLinearEquiv.integral_comp_comm]
--     simp

-- end Fin


section PiCongr

section Equiv

variable {R : Type*} [Semiring R]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable (φ : ι → Type*) [∀ i, SeminormedAddGroup (φ i)]  -- for `Pi.norm_def`

@[simp]
theorem Equiv.norm_piCongrLeft (e : ι' ≃ ι) (x : ∀ i, φ (e i)) :
  ‖Equiv.piCongrLeft φ e x‖ = ‖x‖ := by
  rw [Pi.norm_def]
  rw [Pi.norm_def]
  norm_cast
  rw [← Finset.map_univ_equiv e]
  rw [Finset.sup_map]
  congr
  funext i
  simp [-Equiv.piCongrLeft_apply]
  congr
  exact piCongrLeft_apply_apply φ e x i

@[simp]
theorem Equiv.norm_piCongrLeft' (e : ι ≃ ι') (x : ∀ i, φ i) :
  ‖Equiv.piCongrLeft' φ e x‖ = ‖x‖ := by
  rw [Pi.norm_def]
  rw [Pi.norm_def]
  norm_cast
  simp
  rw [← Finset.map_univ_equiv e]
  rw [Finset.sup_map]
  congr
  funext i
  simp
  rw [symm_apply_apply]

end Equiv

section LinearIsometryEquiv

-- Typeclasses might not be perfect.
-- Based on `MultilinearMap.domDomCongrLinearEquiv'` but with norms.
variable {R : Type*} [NormedField R]
variable {S : Type*} [NormedField S]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {D : ι → Type*} [∀ i, SeminormedAddCommGroup (D i)] [∀ i, NormedSpace R (D i)]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace R F] [NormedSpace S F]
variable [SMulCommClass R S F]

section Def
variable (R D)

/-- Isometry version of `LinearEquiv.piCongrLeft`. -/
def LinearIsometryEquiv.piCongrLeft (e : ι' ≃ ι) : (∀ i', D (e i')) ≃ₗᵢ[R] (∀ i, D i) where
  toLinearEquiv := LinearEquiv.piCongrLeft R D e
  norm_map' := e.norm_piCongrLeft D

/-- Isometry version of `LinearEquiv.piCongrLeft'`. -/
def LinearIsometryEquiv.piCongrLeft' (e : ι ≃ ι') : (∀ i, D i) ≃ₗᵢ[R] (∀ i', D (e.symm i')) where
  toLinearEquiv := LinearEquiv.piCongrLeft' R D e
  norm_map' := e.norm_piCongrLeft' D

end Def

lemma LinearIsometryEquiv.piCongrLeft_apply {e : ι' ≃ ι} {x : ∀ i', D (e i')} :
  (LinearIsometryEquiv.piCongrLeft R D e) x = Equiv.piCongrLeft D e x := rfl

lemma LinearIsometryEquiv.piCongrLeft_symm_apply {e : ι' ≃ ι} {x : ∀ i, D i} :
  (LinearIsometryEquiv.piCongrLeft R D e).symm x = Equiv.piCongrLeft' D e.symm x := rfl

lemma LinearIsometryEquiv.piCongrLeft'_apply {e : ι ≃ ι'} {x : ∀ i, D i} :
  (LinearIsometryEquiv.piCongrLeft' R D e) x = Equiv.piCongrLeft' D e x := rfl

lemma LinearIsometryEquiv.piCongrLeft'_symm_apply {e : ι ≃ ι'} {x : ∀ i', D (e.symm i')} :
  (LinearIsometryEquiv.piCongrLeft' R D e).symm x = Equiv.piCongrLeft D e.symm x := rfl


section Def
variable (R S D F)

/--
Dependent version of `ContinuousMultilinearMap.domDomCongrLinearEquiv`;
continuous version of `MultilinearMap.domDomCongrLinearEquiv'`.
-/
def ContinuousMultilinearMap.domDomCongrLinearEquiv' (σ : ι ≃ ι') :
    ContinuousMultilinearMap R D F ≃ₗ[S] ContinuousMultilinearMap R (fun i => D (σ.symm i)) F where
  toFun f := {
    toMultilinearMap := MultilinearMap.domDomCongrLinearEquiv' R S D F σ f.toMultilinearMap
    cont := by
      change Continuous fun x => f ((LinearIsometryEquiv.piCongrLeft' R D σ).symm x)
      refine Continuous.comp (coe_continuous f) (LinearIsometryEquiv.continuous _)
  }
  invFun f := {
    toMultilinearMap := (MultilinearMap.domDomCongrLinearEquiv' R S D F σ).invFun f.toMultilinearMap
    cont := by
      change Continuous fun x => f ((LinearIsometryEquiv.piCongrLeft' R D σ) x)
      refine Continuous.comp (coe_continuous f) (LinearIsometryEquiv.continuous _)
  }
  map_add' x y := rfl
  map_smul' r x := rfl
  left_inv f := by
    ext x
    simp
    change (⇑f ∘ ⇑(Equiv.piCongrLeft' D σ).symm ∘ ⇑(Equiv.piCongrLeft' D σ)) x = f x
    simp
  right_inv f := by
    ext x
    simp
    change ((⇑f ∘ ⇑(Equiv.piCongrLeft' D σ)) ∘ ⇑(Equiv.piCongrLeft' D σ).symm) x = f x
    simp

end Def

lemma ContinuousMultilinearMap.domDomCongrLinearEquiv'_apply {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R D F} {x : ∀ i, D (σ.symm i)} :
    ContinuousMultilinearMap.domDomCongrLinearEquiv' R S D F σ f x = f ((Equiv.piCongrLeft' D σ).symm x) :=
  rfl

lemma ContinuousMultilinearMap.domDomCongrLinearEquiv'_symm_apply {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R (fun i => D (σ.symm i)) F} {x : ∀ i, D i} :
    (ContinuousMultilinearMap.domDomCongrLinearEquiv' R S D F σ).symm f x = f (Equiv.piCongrLeft' D σ x) :=
  rfl

lemma ContinuousMultilinearMap.domDomCongrLinearEquiv'_apply_piCongrLeft' {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R D F} {x : ∀ i, D i} :
    ContinuousMultilinearMap.domDomCongrLinearEquiv' R S D F σ f (Equiv.piCongrLeft' D σ x) = f x := by
  rw [ContinuousMultilinearMap.domDomCongrLinearEquiv'_apply]
  rw [Equiv.symm_apply_apply]

lemma ContinuousMultilinearMap.domDomCongrLinearEquiv'_symm_apply_piCongrLeft'_symm {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R (fun i => D (σ.symm i)) F} {x : ∀ i, D (σ.symm i)} :
    (ContinuousMultilinearMap.domDomCongrLinearEquiv' R S D F σ).symm f ((Equiv.piCongrLeft' D σ).symm x) = f x := by
  rw [ContinuousMultilinearMap.domDomCongrLinearEquiv'_symm_apply]
  rw [Equiv.apply_symm_apply]

end LinearIsometryEquiv

end PiCongr
