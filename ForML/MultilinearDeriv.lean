import Mathlib.Analysis.Calculus.ContDiff.Basic

section Induction

-- Fix universes such that `E →L[ℝ] F` and `F` are in the same universe (for induction generalizing F).
universe u
variable {𝕜 : Type*} {α β G : Type u}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup α] [NormedSpace 𝕜 α]
variable [NormedAddCommGroup β] [NormedSpace 𝕜 β]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The application of a CLM can be moved outside of `iteratedFDeriv`. -/
theorem iteratedFDeriv_clm_apply_const {n : ℕ} {c : β → α →L[𝕜] G} {v : α} {x : β} {m : Fin n → β} (hc : ContDiff 𝕜 n c) :
    iteratedFDeriv 𝕜 n (fun y => c y v) x m =
    iteratedFDeriv 𝕜 n (fun y => c y) x m v := by
  symm
  induction n generalizing α G with
  | zero => simp
  | succ n h_ind =>
    simp [iteratedFDeriv_succ_apply_right]
    -- generalize m (Fin.last n) = m_last  -- For readability.
    -- generalize Fin.init m = m_init
    have hc_diff : Differentiable 𝕜 (fun y => c y) := hc.differentiable (by norm_num)
    have hc_fderiv : ContDiff 𝕜 n (fun y => fderiv 𝕜 c y) := hc.fderiv_right (by norm_cast)
    rw [h_ind hc_fderiv]
    rw [h_ind (hc_fderiv.clm_apply contDiff_const)]
    rw [h_ind]
    swap
    . conv => arg 3; intro y; rw [fderiv_clm_apply (hc_diff y) (differentiableAt_const v)]
      simp
      refine ContDiff.clm_apply ?_ contDiff_const
      change ContDiff 𝕜 n fun y => (ContinuousLinearMap.flipₗᵢ 𝕜 β α G).toContinuousLinearEquiv.toContinuousLinearMap (fderiv 𝕜 c y)
      exact ContDiff.continuousLinearMap_comp _ hc_fderiv
    congr
    funext z
    rw [fderiv_clm_apply (hc_diff z) (differentiableAt_const v)]
    simp

lemma iteratedFDeriv_fderiv_apply {n : ℕ} {f : α → G} {x : α} {m : Fin n → α} {v : α} (hf : ContDiff 𝕜 n.succ f) :
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y v) x m =
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x m v := by
  rw [contDiff_succ_iff_fderiv] at hf
  rw [iteratedFDeriv_clm_apply_const hf.right]

-- How to use `LinearIsometryEquiv` for multilinear maps.

example {y : α} {c : α → α[×0]→L[𝕜] G} : (c y) 0 = (continuousMultilinearCurryFin0 𝕜 α G) (c y) := rfl

example {y : α} {c : α → α[×(n + 1)]→L[𝕜] G} :
    ContinuousMultilinearMap.curryRight (c y) =
    (continuousMultilinearCurryRightEquiv' 𝕜 n α G).symm (c y) := rfl

example {y : α} {c : α → α[×(n + 1)]→L[𝕜] G} :
    ContinuousMultilinearMap.curryLeft (c y) =
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => α) G).symm (c y) := rfl

/-- The Fréchet derivative of the application of a `ContinuousMultilinearMap`.

TODO: Add version for multilinear map with pi type `(i : Fin n) → α i`.
-/
theorem hasFDerivAt_continuousMultilinearMap_apply_const' {n : ℕ} {c : β → α[×n]→L[𝕜] G} {v : Fin n → α} {x : β} {c' : β →L[𝕜] α[×n]→L[𝕜] G}
    (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y : β => (c y) v) (ContinuousLinearMap.flipMultilinear c' v) x := by
  induction n generalizing G with
  | zero =>
    rw [Matrix.empty_eq v, ← Matrix.empty_eq 0]  -- TODO: More idiomatic way?
    change HasFDerivAt (continuousMultilinearCurryFin0 𝕜 α G ∘ c) _ x
    -- have he : HasFDerivAt (continuousMultilinearCurryFin0 𝕜 α G) _ (c x) := LinearIsometryEquiv.hasFDerivAt _
    refine HasFDerivAt.congr_fderiv (HasFDerivAt.comp x (continuousMultilinearCurryFin0 𝕜 α G).hasFDerivAt hc) ?_
    ext a
    simp
  | succ n h_ind =>
    conv => arg 1; intro y; rw [← Fin.snoc_init_self v, ← ContinuousMultilinearMap.curryRight_apply]
    -- Need to find derivative of
    -- `(c y) v = ContinuousMultilinearMap.curryRight (c y) (Fin.init v) (v (Fin.last n))`
    -- where
    -- `c y : α[×(n + 1)]→L[𝕜] G`
    -- `ContinuousMultilinearMap.curryRight (c y) : α →L[𝕜] α[×n]→L[𝕜] G`  -- use `clm_apply`
    -- `ContinuousMultilinearMap.curryRight (c y) _ : α[×n]→L[𝕜] G`  -- use induction

    -- Find derivative of `fun y => ContinuousMultilinearMap.curryRight (c y)`.
    have he : HasFDerivAt (continuousMultilinearCurryRightEquiv' 𝕜 n α G).symm _ (c x) := LinearIsometryEquiv.hasFDerivAt _
    have := HasFDerivAt.comp x he hc
    conv at this => arg 1; intro y; change ContinuousMultilinearMap.curryRight (c y)
    -- Find derivative of `fun y => ContinuousMultilinearMap.curryRight (c y) (Fin.init v)`.
    replace : HasFDerivAt (fun y => (ContinuousMultilinearMap.curryRight (c y)) (Fin.init v)) _ x := h_ind this
    -- Find derivative of `fun y => ContinuousMultilinearMap.curryRight (c y) (Fin.init v) (v (Fin.last n))`.
    refine HasFDerivAt.congr_fderiv (HasFDerivAt.clm_apply this (hasFDerivAt_const _ x)) ?_
    clear this
    ext b
    simp

/-- The application of a `ContinuousMultilinearMap` can be moved outside `fderiv`. -/
theorem fderiv_continuousMultilinearMap_apply_const {n : ℕ} {c : β → α[×n]→L[𝕜] G} {v : Fin n → α} {x m : β} (hc : DifferentiableAt 𝕜 c x) :
    fderiv 𝕜 (fun y => c y v) x m =
    fderiv 𝕜 (fun y => c y) x m v := by
  rw [(hasFDerivAt_continuousMultilinearMap_apply_const' hc.hasFDerivAt).fderiv]
  simp

lemma fderiv_iteratedFDeriv_apply {n : ℕ} {f : α → G} {m : Fin n → α} {x : α} {v : α} (hf : ContDiff 𝕜 n.succ f) :
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y m) x v =
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y) x v m :=
  fderiv_continuousMultilinearMap_apply_const (hf.differentiable_iteratedFDeriv (by norm_cast; simp) x)

-- TODO: `iteratedFDeriv_continuousMultilinearMap_apply_const`

end Induction
