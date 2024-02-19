import Mathlib.Analysis.Calculus.ContDiff.Bounds

import ForML.ContinuousLinearMap
import ForML.ContinuousLinearMapCo
import ForML.ContinuousMultilinearMap


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


/-- The Fréchet derivative of the application of a `ContinuousMultilinearMap` indexed by `Fin n`. -/
theorem hasFDerivAt_continuousMultilinearMap_apply_const
    {c : α → ContinuousMultilinearMap 𝕜 E G} {v : ∀ i, E i} {x : α}
    {c' : α →L[𝕜] ContinuousMultilinearMap 𝕜 E G} (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y : α => (c y) v) (ContinuousLinearMap.flipMultilinear c' v) x := by
  change HasFDerivAt (ContinuousMultilinearMap.apply 𝕜 E G v ∘ c) _ _
  exact (HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt _) hc)

-- TODO: `iteratedFDeriv_continuousMultilinearMap_apply_comm`

end Multilinear
