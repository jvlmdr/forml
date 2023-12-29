import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

import ForML.ContinuousLinearMapCo


section Simple

variable {𝕜 α E F G : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup α] [NormedSpace 𝕜 α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- -- Help (sometimes?) needed for `ContinuousLinearMap.op_norm_comp_le` in `norm_iteratedFDeriv_clm_comp_const`.
-- noncomputable instance : NormedAddCommGroup (E →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

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

lemma ContinuousLinearMap.op_norm_apply_le {u : E} : ‖apply 𝕜 G u‖ ≤ ‖u‖ := by
  rw [op_norm_le_iff (norm_nonneg _)]
  intro c
  rw [apply_apply, mul_comm]
  exact le_op_norm c u

lemma norm_iteratedFDeriv_clm_comp_const {n : ℕ} {c : α → F →L[𝕜] G} {u : E →L[𝕜] F} {x : α} (hc : ContDiff 𝕜 n c) :
    ‖iteratedFDeriv 𝕜 n (fun y => (c y).comp u) x‖ ≤ ‖u‖ * ‖iteratedFDeriv 𝕜 n c x‖ := by
  -- Use `compL` and `apply` to obtain constant CLM applied to `c y`.
  conv => lhs; arg 1; arg 3; intro y; rw [← ContinuousLinearMap.compL_apply]
  change ‖iteratedFDeriv 𝕜 n (fun y => (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) u).comp (ContinuousLinearMap.compL 𝕜 E F G) (c y)) x‖ ≤ _
  -- Now use `norm_iteratedFDeriv_clm_const_apply` with `u := c`.
  refine le_trans (norm_iteratedFDeriv_clm_const_apply hc) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (ContinuousLinearMap.op_norm_comp_le _ _) ?_
  rw [← mul_one ‖u‖]
  exact mul_le_mul ContinuousLinearMap.op_norm_apply_le (ContinuousLinearMap.norm_compL_le 𝕜 E F G) (norm_nonneg _) (norm_nonneg _)

end Simple


section Multilinear

variable {𝕜 α : Type*}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {D : ι → Type*}
variable {n : ℕ} {E : Fin n → Type*}
variable {F G : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup α] [NormedSpace 𝕜 α]
variable [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace 𝕜 (D i)]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

section Apply
namespace ContinuousMultilinearMap

section Def
variable (𝕜 D G)

/--
The application of a multilinear map as a `ContinuousLinearMap`.
(Not a bilinear map like `ContinuousLinearMap.apply` due to multilinearity with respect to `x`.)
-/
def apply (x : ∀ i, D i) : ContinuousMultilinearMap 𝕜 D G →L[𝕜] G where
  toFun c := c x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_left x

end Def

@[simp]
lemma apply_apply {x : ∀ i, D i} {c : ContinuousMultilinearMap 𝕜 D G} :
    (apply 𝕜 D G x) c = c x := rfl

end ContinuousMultilinearMap  -- namespace

theorem Continuous.continuousMultilinear_apply_const {c : α → ContinuousMultilinearMap 𝕜 D G} {u : ∀ i, D i} (hc : Continuous c) :
    Continuous (fun y => (c y) u) := by
  change Continuous (fun y => (ContinuousMultilinearMap.apply _ _ _ u) (c y))
  refine (ContinuousLinearMap.continuous _).comp hc

theorem Differentiable.continuousMultilinear_apply_const {c : α → ContinuousMultilinearMap 𝕜 D G} {u : ∀ i, D i} (hc : Differentiable 𝕜 c) :
    Differentiable 𝕜 (fun y => (c y) u) := by
  change Differentiable 𝕜 (fun y => (ContinuousMultilinearMap.apply _ _ _ u) (c y))
  exact (ContinuousLinearMap.differentiable _).comp hc

theorem ContDiff.continuousMultilinearMap_apply_const {n : ℕ∞} {c : α → ContinuousMultilinearMap 𝕜 D G} {u : ∀ i, D i} (hc : ContDiff 𝕜 n c) :
    ContDiff 𝕜 n (fun y => (c y) u) := by
  change ContDiff 𝕜 n (fun y => (ContinuousMultilinearMap.apply _ _ _ u) (c y))
  exact (ContinuousLinearMap.contDiff _).comp hc

-- lemma continuous_apply :
--     Continuous (fun c => apply 𝕜 D G c) := by
--   -- Don't have `UniformSpace` for `ContinuousMultilinearMap`;
--   -- can't use `Metric.continuous_iff` or `continuousAt_of_locally_lipschitz`.
--   -- Try looking at `ContDiff.iteratedFDeriv_right`?
--   sorry

end Apply


section Empty
variable [IsEmpty ι]

-- lemma Pi.empty_eq_zero {x : ∀ i, D i} : x = 0 := Subsingleton.elim x 0
-- lemma Pi.empty_refl (x y : ∀ i, D i) : x = y := Subsingleton.elim x y

namespace ContinuousMultilinearMap

lemma eq_empty (c : ContinuousMultilinearMap 𝕜 D G) :
    c = constOfIsEmpty 𝕜 D (c 0) := by
  ext m
  simp [Subsingleton.elim m 0]

lemma norm_empty (c : ContinuousMultilinearMap 𝕜 D G) {x : ∀ i, D i} :
    ‖c x‖ = ‖c‖ := by
  rw [c.eq_empty]
  rw [constOfIsEmpty_apply, norm_constOfIsEmpty]

lemma continuous_constOfIsEmpty : Continuous fun y : G => constOfIsEmpty 𝕜 D y := by
  rw [Metric.continuous_iff]
  intro y ε hε
  use ε
  refine And.intro hε ?_
  intro x h
  rw [dist_eq_norm] at h ⊢
  change ‖constOfIsEmpty 𝕜 D (x - y)‖ < ε
  rw [norm_constOfIsEmpty]
  exact h

section Def
variable (𝕜 D G)

-- def empty_apply : ContinuousMultilinearMap 𝕜 D G →L[𝕜] G := apply 𝕜 D G 0

def toConstOfIsEmpty : G →L[𝕜] ContinuousMultilinearMap 𝕜 D G where
  toFun y := constOfIsEmpty 𝕜 D y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    simp
    exact continuous_constOfIsEmpty

end Def

-- @[simp]
-- lemma empty_apply_apply {c : ContinuousMultilinearMap 𝕜 D G} :
--     (empty_apply 𝕜 D G) c = c 0 := rfl

@[simp]
lemma toConstOfIsEmpty_apply {y : G} {v : ∀ i, D i} :
    (toConstOfIsEmpty 𝕜 D G y) v = y := rfl

end ContinuousMultilinearMap  -- namespace

section Def
variable (𝕜 D G)

/-- Like `continuousMultilinearCurryFin0` but for any empty index (not just `Fin 0`). -/
def continuousMultilinearIsEmptyEquiv : (ContinuousMultilinearMap 𝕜 D G) ≃ₗᵢ[𝕜] G where
  -- Write `toFun` and `invFun` as application of CLM to help `ContinuousLinearEquiv.mk iso.toLinearEquiv`.
  -- toFun c := c 0
  -- invFun y := ContinuousMultilinearMap.constOfIsEmpty 𝕜 D y
  toFun c := ContinuousMultilinearMap.apply 𝕜 D G 0 c
  invFun y := ContinuousMultilinearMap.toConstOfIsEmpty 𝕜 D G y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := by
    simp
    intro c
    ext m
    simp [Subsingleton.elim m 0]
  right_inv := by
    simp
    intro y
    simp
  norm_map' c := by
    simp
    exact c.norm_empty

-- def continuousMultilinearIsEmptyEquiv_continuousLinearEquiv : (ContinuousMultilinearMap 𝕜 D G) ≃L[𝕜] G :=
--   ContinuousLinearEquiv.mk (continuousMultilinearIsEmptyEquiv 𝕜 D G).toLinearEquiv

-- -- Just defined this because aesop was having trouble with `ContinuousLinearEquiv.mk (continuousMultilinearIsEmptyEquiv 𝕜 D G).symm.toLinearEquiv`.
-- def continuousMultilinearIsEmptyEquiv_symm_continuousLinearEquiv : G ≃L[𝕜] (ContinuousMultilinearMap 𝕜 D G) :=
--   ContinuousLinearEquiv.mk (continuousMultilinearIsEmptyEquiv 𝕜 D G).symm.toLinearEquiv

example :
    (ContinuousLinearEquiv.mk (continuousMultilinearIsEmptyEquiv 𝕜 D G).symm.toLinearEquiv : G ≃L[𝕜] ContinuousMultilinearMap 𝕜 D G) =
    (continuousMultilinearIsEmptyEquiv 𝕜 D G).toContinuousLinearEquiv.symm :=
  rfl

end Def

@[simp]
lemma continuousMultilinearIsEmptyEquiv_apply (c : ContinuousMultilinearMap 𝕜 D G) :
  (continuousMultilinearIsEmptyEquiv 𝕜 D G) c = c 0 := rfl

@[simp]
lemma continuousMultilinearIsEmptyEquiv_symm_apply (y : G) :
  (continuousMultilinearIsEmptyEquiv 𝕜 D G).symm y 0 = y := rfl

end Empty


-- TODO: Move to `PiEquiv`?
lemma Equiv.piSplitAt_symm_apply_eq_update_zero (i : ι) (x : D i × ∀ j : {j // j ≠ i}, D j) :
    (Equiv.piSplitAt i D).symm x = Function.update ((Equiv.piSplitAt i D).symm (0, x.2)) i x.1 := by
  ext j
  simp [Equiv.piSplitAt_symm_apply]  -- TODO: Add `simp`?
  rw [Function.update]
  by_cases h : j = i <;> simp [h]

-- lemma Equiv.piSplitAt_symmm_update_eq_update_piSplitAt_symm (i : ι) (xi : D i) (xni : ∀ j : {j // j ≠ i}, D j) (k : ι) (hk : k ≠ i) (xk : D k) :
--     (Equiv.piSplitAt i D).symm (xi, Function.update xni ⟨k, hk⟩ xk) =
--     Function.update ((Equiv.piSplitAt i D).symm (xi, xni)) k xk := by
--   rw [Equiv.piSplitAt_symm_apply_eq_update_zero]
--   simp
--   ext j
--   rw [Function.update]
--   rw [Function.update]
--   by_cases hji : j = i
--   . simp [hji, hk.symm]
--   . simp [hji, Function.update]
--     by_cases hjk : j = k
--     . simp [hjk]
--       -- Need to show equivalence of types? Use some equivalence?
--       sorry
--     . simp [hji, hjk]


-- TODO: Possible/useful to define as `D i →L[𝕜] ContinuousMultilinearMap 𝕜 D G →L[𝕜] G` to be more like `ContinuousLinearMap.apply`?
-- TODO: Instead implement using `domDomCongr` with currying? Or show equivalent?

def ContinuousMultilinearMap.applyAt (i : ι) (xni : ∀ j : {j // j ≠ i}, D j) (f : ContinuousMultilinearMap 𝕜 D G) : D i →L[𝕜] G where
  -- TODO: More idiomatic to use `Equiv` here and `change` in `cont`?
  -- toFun xi := f ((Equiv.piSplitAt i D).symm (xi, xni))
  toFun xi := f ((ContinuousLinearEquiv.piSplitAt 𝕜 i D).symm (xi, xni))
  -- toFun xi := f ((ContinuousLinearEquiv.piSplitAt 𝕜 i D).symm (ContinuousLinearMap.inl 𝕜 _ _ xi + (0, xni)))
  -- toFun xi := ContinuousMultilinearMap.apply 𝕜 D G ((ContinuousLinearEquiv.piSplitAt 𝕜 i D).symm (ContinuousLinearMap.inl 𝕜 _ _ xi + (0, xni))) f
  map_add' xi yi := by
    simp
    simp [ContinuousLinearEquiv.piSplitAt_symm_apply]
    rw [Equiv.piSplitAt_symm_apply_eq_update_zero (x := (xi, _))]
    rw [Equiv.piSplitAt_symm_apply_eq_update_zero (x := (yi, _))]
    simp
    rw [← ContinuousMultilinearMap.map_add]
    rw [Equiv.piSplitAt_symm_apply_eq_update_zero (x := (xi + yi, _))]
  map_smul' c xi := by
    simp [ContinuousLinearEquiv.piSplitAt_symm_apply]
    rw [Equiv.piSplitAt_symm_apply_eq_update_zero (x := (xi, _))]
    simp
    rw [← ContinuousMultilinearMap.map_smul]
    rw [Equiv.piSplitAt_symm_apply_eq_update_zero (x := (c • xi, _))]
  cont := f.cont.comp ((ContinuousLinearEquiv.piSplitAt 𝕜 i D).symm.continuous.comp (Continuous.Prod.mk_left xni))

-- Might be convenient? Maybe remove?
def ContinuousMultilinearMap.applyUpdate (x : ∀ j, D j) (i : ι) (f : ContinuousMultilinearMap 𝕜 D G) : D i →L[𝕜] G :=
  f.applyAt i (fun j : {j // j ≠ i} => x j)


-- lemma ContinuousMultilinearMap.hasFDerivAt (c : ContinuousMultilinearMap 𝕜 E G) {x : ∀ i, E i} :
--     HasFDerivAt (fun x => c x) (ContinuousLinearMap.copi (fun i => c.applyAt i (fun j : {j // j ≠ i} => x j))) x := by
--   induction n with
--   | zero =>
--     conv => arg 1; intro x; rw [Subsingleton.elim x 0]
--     refine HasFDerivAt.congr_fderiv (hasFDerivAt_const _ _) ?_
--     ext m
--     simp
--     rw [ContinuousLinearMap.zero_apply]  -- No `simp`?
--   | succ n ih =>
--     -- Proof outline:
--     -- Curry on the left to obtain `D 0 →L[𝕜] ContinuousMultilinearMap 𝕜 D' G`.
--     -- Use result for HasFDerivAt of CLM.
--     -- Apply inductive hypothesis to `n` remaining variables.

--     -- Challenge:
--     -- Still have fderiv with respect to both variables mixed together.

--     have h_comp (y) : c y = ((continuousMultilinearCurryLeftEquiv 𝕜 E G).symm c) (y 0) (Fin.tail y) := by simp
--     simp_rw [h_comp]
--     change HasFDerivAt
--       ((fun p => ((continuousMultilinearCurryLeftEquiv 𝕜 E G).symm c) p.1 p.2) ∘
--         fun x => (x 0, Fin.tail x)) _ _
--     clear h_comp

--     have hf (f' : E 0 × ((i : Fin n) → E (Fin.succ i)) →L[𝕜] G) :
--         HasFDerivAt (fun p => ((continuousMultilinearCurryLeftEquiv 𝕜 E G).symm c) p.1 p.2) f' (x 0, Fin.tail x)
--     . sorry

--     have hg (g' : ((i : Fin (Nat.succ n)) → E i) →L[𝕜] E 0 × ((i : Fin n) → E (Fin.succ i))) :
--         HasFDerivAt (fun x => (x 0, Fin.tail x)) g' x
--     . sorry

--     sorry


lemma Differentiable.continuousMultilinearMap_apply_const
    {c : α → ContinuousMultilinearMap 𝕜 D G} {u : ∀ i, D i}
    (hc : Differentiable 𝕜 c) :
    Differentiable 𝕜 (fun y => (c y) u) :=
  comp (ContinuousMultilinearMap.apply 𝕜 D G u).differentiable hc

lemma DifferentiableAt.continuousMultilinearMap_apply_const
    {c : α → ContinuousMultilinearMap 𝕜 D G} {u : ∀ i, D i} {x : α}
    (hc : DifferentiableAt 𝕜 c x) :
    DifferentiableAt 𝕜 (fun y => (c y) u) x :=
  comp x (ContinuousMultilinearMap.apply 𝕜 D G u).differentiableAt hc


/-- The application of a `ContinuousMultilinearMap` can be moved outside `fderiv`. -/
theorem fderiv_continuousMultilinearMap_apply_comm {c : α → ContinuousMultilinearMap 𝕜 E G} {v : ∀ i, E i} {x m : α} (hc : DifferentiableAt 𝕜 c x) :
    (fderiv 𝕜 (fun y => (c y) v) x) m = (fderiv 𝕜 c x) m v := by
  change (fderiv 𝕜 (ContinuousMultilinearMap.apply 𝕜 E G v ∘ c) x) m = _
  rw [fderiv.comp x (ContinuousLinearMap.differentiableAt _) hc]
  simp

/-- The application of `iteratedFDeriv` can be moved outside of `fderiv`. -/
theorem fderiv_iteratedFDeriv_apply_comm {n : ℕ} {f : F → G} {m : Fin n → F} {x : F} {v : F} (hf : ContDiff 𝕜 n.succ f) :
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y m) x v =
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y) x v m :=
  fderiv_continuousMultilinearMap_apply_comm (hf.differentiable_iteratedFDeriv (by norm_cast; simp) x)


/-- The Fréchet derivative of the application of a `ContinuousMultilinearMap` indexed by `Fin n`. -/
theorem hasFDerivAt_continuousMultilinearMap_apply_const
    {c : α → ContinuousMultilinearMap 𝕜 E G} {v : ∀ i, E i} {x : α}
    {c' : α →L[𝕜] ContinuousMultilinearMap 𝕜 E G} (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y : α => (c y) v) (ContinuousLinearMap.flipMultilinear c' v) x := by
  change HasFDerivAt (ContinuousMultilinearMap.apply 𝕜 E G v ∘ c) _ _
  exact (HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt _) hc)


/-- The application of a `ContinuousLinearMap` can be moved outside of `iteratedFDeriv`. -/
theorem iteratedFDeriv_clm_apply_comm {n : ℕ} {c : α → F →L[𝕜] G} {v : F} {x : α} {m : Fin n → α} (hc : ContDiff 𝕜 n c) :
    iteratedFDeriv 𝕜 n (fun y => c y v) x m =
    iteratedFDeriv 𝕜 n (fun y => c y) x m v := by
  try simp  -- `ContinuousLinearMap.strongUniformity_topology_eq`
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have h_deriv_apply {v} : Differentiable 𝕜 (fun y => iteratedFDeriv 𝕜 n (fun y => (c y) v) y)
    . refine ContDiff.differentiable_iteratedFDeriv (n := n.succ) (by norm_cast; simp) ?_
      exact hc.clm_apply contDiff_const
    have h_deriv : Differentiable 𝕜 (iteratedFDeriv 𝕜 n (fun y => c y))
    . exact hc.differentiable_iteratedFDeriv (by norm_cast; simp)
    have h_apply_deriv {m} : Differentiable 𝕜 (fun y => (iteratedFDeriv 𝕜 n (fun y => c y) y) m)
    . exact Differentiable.continuousMultilinearMap_apply_const h_deriv

    rw [iteratedFDeriv_succ_apply_left]
    rw [iteratedFDeriv_succ_apply_left]
    rw [← fderiv_continuousMultilinearMap_apply_comm (h_deriv_apply _)]
    simp_rw [ih (ContDiff.of_succ hc)]
    rw [fderiv_clm_apply_comm (h_apply_deriv _)]
    rw [fderiv_continuousMultilinearMap_apply_comm (h_deriv _)]


/-- The application of `fderiv` can be moved outside of `iteratedFDeriv`. -/
theorem iteratedFDeriv_fderiv_apply_comm {n : ℕ} {f : F → G} {x : F} {m : Fin n → F} {v : F} (hf : ContDiff 𝕜 n.succ f) :
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y v) x m =
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x m v := by
  rw [contDiff_succ_iff_fderiv] at hf
  rw [iteratedFDeriv_clm_apply_comm hf.right]

-- TODO: `iteratedFDeriv_continuousMultilinearMap_apply_comm`

end Multilinear
