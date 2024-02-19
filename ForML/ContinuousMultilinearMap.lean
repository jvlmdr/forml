import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.NormedSpace.Multilinear.Curry

import ForML.ContinuousLinearMap
import ForML.PiEquiv
import ForML.Util

open BigOperators


section Basic

namespace ContinuousMultilinearMap

variable {R ι : Type*} {M₁ : ι → Type*} {M₂ : Type*} [Semiring R]
  [(i : ι) → AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [(i : ι) → Module R (M₁ i)] [Module R M₂]
  [(i : ι) → TopologicalSpace (M₁ i)] [TopologicalSpace M₂]

-- Added for `domDomCongrLinearEquiv'.{left,right}_inv`.
-- To access `toFun` of `ContinuousMultilinearMap` defined using `toMultilinearMap`.
theorem toFun_eq_coe {f : ContinuousMultilinearMap R M₁ M₂} : f.toFun = ⇑f := rfl

end ContinuousMultilinearMap

end Basic


section ContinuousLinear

section Apply

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {F : Type*}
variable {G : Type*}

-- namespace ContinuousMultilinearMap

-- variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

-- variable (𝕜 E G)

-- /--
-- The application of a multilinear map as a `ContinuousLinearMap`.
-- (Not a bilinear map like `ContinuousLinearMap.apply` due to multilinearity with respect to `x`.)
-- -/
-- def apply (x : ∀ i, E i) : ContinuousMultilinearMap 𝕜 E G →L[𝕜] G where
--   toFun c := c x
--   map_add' _ _ := rfl
--   map_smul' _ _ := rfl
--   cont := continuous_eval_left x

-- variable {𝕜 E G}

-- @[simp]
-- theorem apply_apply {x : ∀ i, E i} {c : ContinuousMultilinearMap 𝕜 E G} :
--     (apply 𝕜 E G x) c = c x := rfl

-- end ContinuousMultilinearMap

section ContDiff

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {α : Type*} [NormedAddCommGroup α] [NormedSpace 𝕜 α]

theorem Continuous.continuousMultilinear_apply_const
     {c : α → ContinuousMultilinearMap 𝕜 E G} {u : ∀ i, E i}
     (hc : Continuous c) :
    Continuous fun y ↦ (c y) u :=
  comp (ContinuousMultilinearMap.apply 𝕜 E G u).continuous hc

-- theorem Differentiable.continuousMultilinear_apply_const
--      {c : α → ContinuousMultilinearMap 𝕜 E G} {u : ∀ i, E i}
--      (hc : Differentiable 𝕜 c) :
--     Differentiable 𝕜 fun y ↦ (c y) u :=
--   comp (ContinuousMultilinearMap.apply 𝕜 E G u).differentiable hc

theorem ContDiff.continuousMultilinear_apply_const
    {c : α → ContinuousMultilinearMap 𝕜 E G} {u : ∀ i, E i}
    {n : ℕ∞} (hc : ContDiff 𝕜 n c) :
    ContDiff 𝕜 n (fun y ↦ (c y) u) :=
  comp (ContinuousMultilinearMap.apply 𝕜 E G u).contDiff hc

-- /-- The application of a `ContinuousMultilinearMap` can be moved outside `fderiv`. -/
-- theorem fderiv_continuousMultilinear_apply_const_apply
--     {c : α → ContinuousMultilinearMap 𝕜 E G} {v : ∀ i, E i} {x m : α}
--     (hc : DifferentiableAt 𝕜 c x) :
--     (fderiv 𝕜 (fun y => (c y) v) x) m = (fderiv 𝕜 c x) m v := by
--   change (fderiv 𝕜 (ContinuousMultilinearMap.apply 𝕜 E G v ∘ c) x) m = _
--   rw [fderiv.comp x (ContinuousLinearMap.differentiableAt _) hc]
--   simp

/-- The application of `iteratedFDeriv` can be moved outside of `fderiv`. -/
theorem fderiv_iteratedFDeriv_apply_comm {n : ℕ} {f : F → G} {m : Fin n → F} {x : F} {v : F}
    (hf : ContDiff 𝕜 n.succ f) :
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y m) x v =
      fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y) x v m :=
  fderiv_continuousMultilinear_apply_const_apply
    (hf.differentiable_iteratedFDeriv (by norm_cast; simp) x) m v

-- /-- The Fréchet derivative of the application of a `ContinuousMultilinearMap` indexed by `Fin n`. -/
-- theorem hasFDerivAt_continuousMultilinear_apply_const
--     {c : α → ContinuousMultilinearMap 𝕜 E G} {v : ∀ i, E i} {x : α}
--     {c' : α →L[𝕜] ContinuousMultilinearMap 𝕜 E G} (hc : HasFDerivAt c c' x) :
--     HasFDerivAt (fun y : α => (c y) v) (ContinuousLinearMap.flipMultilinear c' v) x := by
--   change HasFDerivAt (ContinuousMultilinearMap.apply 𝕜 E G v ∘ c) _ _
--   exact (HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt _) hc)

-- /-- The application of a `ContinuousLinearMap` can be moved outside of `iteratedFDeriv`. -/
-- theorem iteratedFDeriv_clm_apply_comm {n : ℕ} {c : α → F →L[𝕜] G} {v : F} {x : α} {m : Fin n → α} (hc : ContDiff 𝕜 n c) :
--     iteratedFDeriv 𝕜 n (fun y => c y v) x m =
--       iteratedFDeriv 𝕜 n (fun y => c y) x m v := by
--   try simp  -- `ContinuousLinearMap.strongUniformity_topology_eq`
--   induction n generalizing x with
--   | zero => simp
--   | succ n ih =>
--     have h_deriv_apply {v} : Differentiable 𝕜 (fun y => iteratedFDeriv 𝕜 n (fun y => (c y) v) y)
--     . refine ContDiff.differentiable_iteratedFDeriv (n := n.succ) (by norm_cast; simp) ?_
--       exact hc.clm_apply contDiff_const
--     have h_deriv : Differentiable 𝕜 (iteratedFDeriv 𝕜 n (fun y => c y))
--     . exact hc.differentiable_iteratedFDeriv (by norm_cast; simp)
--     have h_apply_deriv {m} : Differentiable 𝕜 (fun y => (iteratedFDeriv 𝕜 n (fun y => c y) y) m)
--     . exact Differentiable.continuousMultilinear_apply_const h_deriv m

--     rw [iteratedFDeriv_succ_apply_left]
--     rw [iteratedFDeriv_succ_apply_left]
--     rw [← fderiv_continuousMultilinear_apply_const_apply (h_deriv_apply _)]
--     simp_rw [ih (ContDiff.of_succ hc)]
--     rw [fderiv_clm_apply_comm (h_apply_deriv _)]
--     rw [fderiv_continuousMultilinear_apply_const_apply (h_deriv _)]

/-- The application of `fderiv` can be moved outside of `iteratedFDeriv`. -/
theorem iteratedFDeriv_fderiv_apply_comm {n : ℕ} {f : F → G} {x : F} {m : Fin n → F} {v : F} (hf : ContDiff 𝕜 n.succ f) :
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y v) x m =
    iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x m v := by
  rw [contDiff_succ_iff_fderiv] at hf
  rw [iteratedFDeriv_clm_apply_const_apply hf.right (le_refl _)]

-- TODO: `iteratedFDeriv_continuousMultilinear_apply_comm`

end ContDiff

end Apply


section Empty

variable {ι : Type*} [Fintype ι] [IsEmpty ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

-- theorem Pi.empty_eq_zero {x : ∀ i, E i} : x = 0 := Subsingleton.elim x 0
-- theorem Pi.empty_refl (x y : ∀ i, E i) : x = y := Subsingleton.elim x y

namespace ContinuousMultilinearMap

theorem eq_empty (c : ContinuousMultilinearMap 𝕜 E G) :
    c = constOfIsEmpty 𝕜 E (c 0) := by
  ext m
  simp [Subsingleton.elim m 0]

theorem norm_empty (c : ContinuousMultilinearMap 𝕜 E G) {x : ∀ i, E i} :
    ‖c x‖ = ‖c‖ := by
  rw [c.eq_empty]
  rw [constOfIsEmpty_apply, norm_constOfIsEmpty]

theorem continuous_constOfIsEmpty : Continuous fun y : G => constOfIsEmpty 𝕜 E y := by
  rw [Metric.continuous_iff]
  intro y ε hε
  use ε
  refine And.intro hε ?_
  intro x h
  rw [dist_eq_norm] at h ⊢
  change ‖constOfIsEmpty 𝕜 E (x - y)‖ < ε
  rw [norm_constOfIsEmpty]
  exact h

variable (𝕜 E G)

def toConstOfIsEmpty : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G where
  toFun y := constOfIsEmpty 𝕜 E y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    simp
    exact continuous_constOfIsEmpty

variable {𝕜 E G}

-- @[simp]
-- theorem empty_apply_apply {c : ContinuousMultilinearMap 𝕜 E G} :
--     (empty_apply 𝕜 E G) c = c 0 := rfl

@[simp]
theorem toConstOfIsEmpty_apply {y : G} {v : ∀ i, E i} :
    (toConstOfIsEmpty 𝕜 E G y) v = y := rfl

end ContinuousMultilinearMap

variable (𝕜 E G)

/-- Like `continuousMultilinearCurryFin0` but for any empty index (not just `Fin 0`). -/
noncomputable def continuousMultilinearIsEmptyEquiv : (ContinuousMultilinearMap 𝕜 E G) ≃ₗᵢ[𝕜] G where
  -- Write `toFun` and `invFun` as application of CLM to help `ContinuousLinearEquiv.mk iso.toLinearEquiv`.
  -- toFun c := c 0
  -- invFun y := ContinuousMultilinearMap.constOfIsEmpty 𝕜 E y
  toFun c := ContinuousMultilinearMap.apply 𝕜 E G 0 c
  invFun y := ContinuousMultilinearMap.toConstOfIsEmpty 𝕜 E G y
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

variable {𝕜 E G}

example :
    (ContinuousLinearEquiv.mk (continuousMultilinearIsEmptyEquiv 𝕜 E G).symm.toLinearEquiv : G ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G) =
    (continuousMultilinearIsEmptyEquiv 𝕜 E G).toContinuousLinearEquiv.symm :=
  rfl

@[simp]
theorem continuousMultilinearIsEmptyEquiv_apply (c : ContinuousMultilinearMap 𝕜 E G) :
    (continuousMultilinearIsEmptyEquiv 𝕜 E G) c = c 0 := rfl

@[simp]
theorem continuousMultilinearIsEmptyEquiv_symm_apply (y : G) :
    (continuousMultilinearIsEmptyEquiv 𝕜 E G).symm y 0 = y := rfl

end Empty


section MkPiRing

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousMultilinearMap

variable (𝕜 G)

noncomputable def mkPiRingL :
    G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ 𝕜) G where
  toFun := ContinuousMultilinearMap.mkPiRing 𝕜 ι
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp [smul_comm c]
  cont := by
    simp only
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε
    refine And.intro hε ?_
    intro a hab
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ((opNorm_le_iff _ dist_nonneg).mpr ?_) hab
    intro m
    refine le_of_eq ?_
    rw [mul_comm, dist_eq_norm]
    simp [← smul_sub, norm_smul]

variable {𝕜 G}

@[simp]
theorem mkPiRingL_apply {z : G} :
    mkPiRingL 𝕜 G z = ContinuousMultilinearMap.mkPiRing 𝕜 ι z := rfl

theorem mkPiRing_continuous :
    Continuous fun z : G ↦ ContinuousMultilinearMap.mkPiRing 𝕜 ι z :=
  (mkPiRingL 𝕜 G).continuous

-- theorem Continuous.continuousMultilinear_mkPiRing
--     {α : Type*} [TopologicalSpace α] {f : α → G} (hf : Continuous f) :
--     Continuous (fun x ↦ ContinuousMultilinearMap.mkPiRing 𝕜 ι (f x)) :=
--   .comp ContinuousMultilinearMap.mkPiRing_continuous hf

end ContinuousMultilinearMap

end MkPiRing

end ContinuousLinear


section PiCongr

-- section Equiv

-- variable {R : Type*} [Semiring R]
-- variable {ι : Type*} [Fintype ι]
-- variable {ι' : Type*} [Fintype ι']
-- variable (φ : ι → Type*) [∀ i, SeminormedAddGroup (φ i)]  -- for `Pi.norm_def`

-- @[simp]
-- theorem Equiv.norm_piCongrLeft (e : ι' ≃ ι) (x : ∀ i, φ (e i)) :
--     ‖Equiv.piCongrLeft φ e x‖ = ‖x‖ := by
--   rw [Pi.norm_def]
--   rw [Pi.norm_def]
--   norm_cast
--   rw [← Finset.map_univ_equiv e]
--   rw [Finset.sup_map]
--   congr
--   funext i
--   simp [-Equiv.piCongrLeft_apply]
--   congr
--   exact piCongrLeft_apply_apply φ e x i

-- @[simp]
-- theorem Equiv.norm_piCongrLeft' (e : ι ≃ ι') (x : ∀ i, φ i) :
--   ‖Equiv.piCongrLeft' φ e x‖ = ‖x‖ := by
--   rw [Pi.norm_def]
--   rw [Pi.norm_def]
--   norm_cast
--   simp
--   rw [← Finset.map_univ_equiv e]
--   rw [Finset.sup_map]
--   congr
--   funext i
--   simp
--   rw [symm_apply_apply]

-- end Equiv

namespace ContinuousMultilinearMap

section LinearEquiv

variable {R : Type*} [Semiring R]
variable {S : Type*} [Semiring S]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {D : ι → Type*} [∀ i, SeminormedAddCommGroup (D i)] [∀ i, Module R (D i)]
variable {F : Type*} [SeminormedAddCommGroup F] [Module R F] [Module S F] [ContinuousConstSMul S F]
variable [SMulCommClass R S F]

-- variable (S)

-- def domDomCongr' (σ : ι ≃ ι') (f : ContinuousMultilinearMap R D F) :
--     ContinuousMultilinearMap R (fun i' ↦ D (σ.symm i')) F where
--   toMultilinearMap := MultilinearMap.domDomCongrLinearEquiv' R S D F σ f.toMultilinearMap
--   cont := f.coe_continuous.comp (LinearIsometryEquiv.continuous (.symm (.piCongrLeft' R D σ)))

-- -- TODO: Should this follow e.g. `piCongrLeft` and use `σ : ι' = ι`?
-- -- Although, we only have `MultilinearMap.domDomCongrLinearEquiv'`...
-- -- The problem is that we end up with the type `fun i ↦ D (σ.symm.symm i)`.
-- -- Maybe the best thing would be to define `MultilinearMap.domDomCongrLinearEquiv''`?
-- def domDomCongrSymm' (σ : ι ≃ ι') (f : ContinuousMultilinearMap R (fun i' ↦ D (σ.symm i')) F) :
--     ContinuousMultilinearMap R D F where
--   toMultilinearMap := (MultilinearMap.domDomCongrLinearEquiv' R S D F σ).symm f.toMultilinearMap
--   cont := f.coe_continuous.comp (LinearIsometryEquiv.continuous (.piCongrLeft' R D σ))

-- theorem domDomCongr'_apply {σ : ι ≃ ι'} {f : ContinuousMultilinearMap R D F}
--     {x : (i' : ι') → D (σ.symm i')} :
--     domDomCongr' S σ f x = f ((Equiv.piCongrLeft' D σ).symm x) := rfl

-- theorem domDomCongrSymm'_apply {σ : ι ≃ ι'}
--     {f : ContinuousMultilinearMap R (fun i' ↦ D (σ.symm i')) F} {x : (i : ι) → D i} :
--     domDomCongrSymm' S σ f x = f ((Equiv.piCongrLeft' D σ) x) := rfl

-- variable {S}

variable (R S D F)

-- TODO: Add `domDomCongrLinearEquiv` (`LinearEquiv` for `domDomCongrEquiv`) for completeness?

/--
Continuous version of `MultilinearMap.domDomCongrLinearEquiv'`.
Dependent, linear version of `ContinuousMultilinearMap.domDomCongrEquiv`.
-/
def domDomCongrLinearEquiv' (σ : ι ≃ ι') :
    ContinuousMultilinearMap R D F ≃ₗ[S]
      ContinuousMultilinearMap R (fun i' : ι' ↦ D (σ.symm i')) F where
  -- toFun := domDomCongr' S σ
  -- invFun := domDomCongrSymm' S σ
  toFun f := {
    MultilinearMap.domDomCongrLinearEquiv' R S D F σ f.toMultilinearMap with
    cont := f.coe_continuous.comp (LinearIsometryEquiv.continuous (.symm (.piCongrLeft' R D σ)))
  }
  invFun f := {
    (MultilinearMap.domDomCongrLinearEquiv' R S D F σ).symm f.toMultilinearMap with
    cont := f.coe_continuous.comp (LinearIsometryEquiv.continuous (.piCongrLeft' R D σ))
  }
  map_add' x y := rfl
  map_smul' r x := rfl
  left_inv f := ContinuousMultilinearMap.ext fun x ↦ by
    -- Add `toFun_eq_coe` to access `(toFun f).toMultilinearMap.toFun`.
    simp only [← toFun_eq_coe, MultilinearMap.toFun_eq_coe]
    simp
  right_inv f := ContinuousMultilinearMap.ext fun x ↦ by
    simp only [← toFun_eq_coe, MultilinearMap.toFun_eq_coe]
    simp

variable {R S D F}

-- theorem coe_domDomCongrLinearEquiv' (σ : ι ≃ ι') :
--   ⇑(domDomCongrLinearEquiv' R S D F σ) = domDomCongr' S σ := rfl

-- theorem coe_domDomCongrLinearEquiv'_symm (σ : ι ≃ ι') :
--   ⇑(domDomCongrLinearEquiv' R S D F σ).symm = domDomCongrSymm' S σ := rfl

@[simp]
theorem domDomCongrLinearEquiv'_apply {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R D F} {x : (i' : ι') → D (σ.symm i')} :
    domDomCongrLinearEquiv' R S D F σ f x = f ((Equiv.piCongrLeft' D σ).symm x) :=
  rfl

@[simp]
theorem domDomCongrLinearEquiv'_symm_apply {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R (fun i' : ι' ↦ D (σ.symm i')) F} {x : (i : ι) → D i} :
    (domDomCongrLinearEquiv' R S D F σ).symm f x = f (Equiv.piCongrLeft' D σ x) :=
  rfl

@[simp]
theorem domDomCongrLinearEquiv'_apply_piCongrLeft' {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R D F} {x : (i : ι) → D i} :
    domDomCongrLinearEquiv' R S D F σ f (Equiv.piCongrLeft' D σ x) = f x := by
  rw [domDomCongrLinearEquiv'_apply, Equiv.symm_apply_apply]

@[simp]
theorem domDomCongrLinearEquiv'_symm_apply_piCongrLeft'_symm {σ : ι ≃ ι'}
    {f : ContinuousMultilinearMap R (fun i ↦ D (σ.symm i)) F} {x : (i' : ι') → D (σ.symm i')} :
    (domDomCongrLinearEquiv' R S D F σ).symm f ((Equiv.piCongrLeft' D σ).symm x) = f x := by
  rw [domDomCongrLinearEquiv'_symm_apply, Equiv.apply_symm_apply]

end LinearEquiv

section Isometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {D : ι → Type*} [∀ i, SeminormedAddCommGroup (D i)] [∀ i, NormedSpace 𝕜 (D i)]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_domDomCongrLinearEquiv' (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 D F) :
    ‖(domDomCongrLinearEquiv' 𝕜 𝕜 D F σ) f‖ = ‖f‖ := by
  simp only [ContinuousMultilinearMap.norm_def, domDomCongrLinearEquiv'_apply]
  refine congrArg _ ?_
  ext c
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [Equiv.forall_congr_left' (Equiv.piCongrLeft' D σ).symm]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.piCongrLeft'_apply]
  rw [forall_congr]
  intro x
  rw [eq_iff_iff]
  rw [← Finset.univ_map_equiv_to_embedding σ, Finset.prod_map]
  -- simp [σ.symm_apply_apply]  -- TODO: Why doesn't this work?
  simp only [Equiv.coe_toEmbedding]
  rw [Finset.prod_congr rfl fun (i : ι) _ ↦ congrArg (‖x ·‖) (σ.symm_apply_apply i)]

variable (𝕜 D F)

/--
Dependent version of `ContinuousMultilinearMap.domDomCongrLinearEquiv`;
continuous version of `MultilinearMap.domDomCongrLinearEquiv'`;
isometric version of `ContinuousMultilinearMap.domDomCongrEquiv`.
-/
def domDomCongrₗᵢ' (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 D F ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i' : ι' ↦ D (σ.symm i')) F where
  toLinearEquiv := domDomCongrLinearEquiv' 𝕜 𝕜 D F σ
  norm_map' := norm_domDomCongrLinearEquiv' σ

variable {𝕜 D F}

theorem domDomCongrₗᵢ'_toLinearEquiv {σ : ι ≃ ι'} :
  (domDomCongrₗᵢ' 𝕜 D F σ).toLinearEquiv = domDomCongrLinearEquiv' 𝕜 𝕜 D F σ := rfl

theorem coe_domDomCongrₗᵢ' {σ : ι ≃ ι'} :
  ⇑(domDomCongrₗᵢ' 𝕜 D F σ) = ⇑(domDomCongrLinearEquiv' 𝕜 𝕜 D F σ) := rfl

theorem coe_domDomCongrₗᵢ'_symm {σ : ι ≃ ι'} :
  ⇑(domDomCongrₗᵢ' 𝕜 D F σ).symm = ⇑(domDomCongrLinearEquiv' 𝕜 𝕜 D F σ).symm := rfl

end Isometry

end ContinuousMultilinearMap

end PiCongr


section CompContinuousLinearMap

section Continuous

section Fin

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {n : ℕ}
variable {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : Fin n → Type*} [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem Fin.map_cons' {α δ₁ : Type*} {n : ℕ} {f : Fin n.succ → α → δ₁} {x : α} {p : Fin n → α} :
    (fun i ↦ f i (Fin.cons (α := fun _ : Fin n.succ ↦ α) x p i)) =
      Fin.cons (f 0 x) (fun i : Fin n ↦ f i.succ (p i)) := by
  ext i
  cases i using Fin.cases <;> simp

theorem Fin.map_cons {n : ℕ} {α δ₁ : Fin n.succ → Type*} {f : (i : Fin n.succ) → α i → δ₁ i}
    {x : α 0} {p : (i : Fin n) → α i.succ} :
    (fun i ↦ (f i) (Fin.cons x p i)) =
      Fin.cons ((f 0) x) (fun i ↦ (f i.succ) (p i)) := by
  ext i
  cases i using Fin.cases <;> simp

theorem Fin.cons.nnnorm {α : Fin n.succ → Type*} [∀ i, SeminormedAddGroup (α i)]
    (a : α 0) (b : (i : Fin n) → α i.succ) :
    ‖Fin.cons a b‖₊ = ‖a‖₊ ⊔ ‖b‖₊ := by
  simp [Pi.nnnorm_def, Fin.univ_succ, Function.comp_def]

theorem Fin.cons.norm {α : Fin n.succ → Type*} [∀ i, SeminormedAddGroup (α i)]
    {a : α 0} {b : (i : Fin n) → α i.succ} :
    ‖Fin.cons a b‖ = ‖a‖ ⊔ ‖b‖ := by
  rw [← Real.toNNReal_eq_toNNReal_iff]
  · rw [Real.toNNReal_mono.map_sup]
    simpa [norm_toNNReal] using nnnorm a b
  · exact norm_nonneg (cons a b)
  · exact le_trans (norm_nonneg a) le_sup_left

-- TODO: Copy all ops for `AddGroup` somehow?
theorem Fin.cons.map_sub {α : Fin n.succ → Type*} [∀ i, AddGroup (α i)]
    {a c : α 0} {b d : (i : Fin n) → α i.succ} :
    Fin.cons a b - Fin.cons c d = Fin.cons (a - c) (b - d) := by
  ext i
  cases i using Fin.cases <;> simp

-- Helps with speed of e.g. `norm_zero` in `continuous_compContinuousLinearMapL_fin`
noncomputable instance :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable instance :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  ContinuousLinearMap.toNormedSpace

variable (G)

/-- Auxiliary lemma for `continuous_compContinuousLinearMapL`. -/
theorem ContinuousMultilinearMap.continuous_compContinuousLinearMapL_fin :
    Continuous (compContinuousLinearMapL (𝕜 := 𝕜) (E := E) (E₁ := E₁) (G := G)) := by
  rw [Metric.continuous_iff
    (β := ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G)]
  simp only [dist_eq_norm_sub]
  intro f
  induction n with
  | zero => exact fun ε hε ↦ ⟨1, ⟨zero_lt_one, fun g _ ↦ by simp [Subsingleton.elim f g, hε]⟩⟩
  | succ n IH =>
    intro ε hε_pos
    /-
    Need to choose `0 < ε₁`, `0 < δ ≤ δ₁` to satisfy:
      `ε₁ * (‖f 0‖ + δ) < C₁`
      `δ * ∏ i, ‖f (Fin.succ i)‖ < C₂`
      `C₁ + C₂ ≤ ε`
    where `δ₁` depends on `ε₁`.
    Together, this gives:
      `ε₁ * (‖f 0‖ + δ) + δ * ∏ i, ‖f (Fin.succ i)‖ < ε`
      `ε₁ < (ε - δ * ∏ i, ‖f (Fin.succ i)‖) / (‖f 0‖ + δ)`
    However, we can't set `δ = δ₁` here because `δ₁` is determined by `ε₁`.
    Let us set `C₁ = C₂ = r * ε` and choose `r = 1/2`.
    The contraints on `δ > 0` are:
      `δ ≤ δ₁`
      `δ < rε / ∏ i, ‖f (Fin.succ i)‖`
      `δ < rε / ε₁ - ‖f 0‖`
    The last condition requires `ε₁ < rε / ‖f 0‖` to have `0 < δ`.
    If we choose `ε₁ = rε / (a + ‖f 0‖)` with `a > 0`, this is equivalent to `δ < a`.
    Therefore set..
      `ε₁ = rε / (2 + ‖f 0‖)`
      `δ = 1 ⊓ δ₁ ⊓ rε / (1 + ∏ i, ‖f (Fin.succ i)‖)`
    -/
    generalize hε₁_def : (ε / 2) / (2 + ‖f 0‖) = ε₁
    have hε₁_pos : 0 < ε₁ := by
      rw [← hε₁_def]
      exact div_pos (half_pos hε_pos) <| add_pos_of_pos_of_nonneg zero_lt_two (norm_nonneg _)
    specialize IH (fun i : Fin n ↦ f (i.succ)) ε₁ hε₁_pos
    rcases IH with ⟨δ₁, hδ₁_pos, IH⟩
    generalize hδ_def : 1 ⊓ δ₁ ⊓ (ε / 2) / (1 + ∏ i, ‖f (Fin.succ i)‖) = δ
    have hδ : δ ≤ δ₁ := by rw [← hδ_def]; exact le_trans inf_le_left inf_le_right
    have hδ_pos : 0 < δ := by
      simp only [← hδ_def, lt_inf_iff]
      refine And.intro (And.intro zero_lt_one hδ₁_pos) ?_
      refine div_pos (half_pos hε_pos) ?_
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    generalize hC₁_def : ε₁ * (δ + ‖f 0‖) = C₁
    generalize hC₂_def : δ * ∏ i, ‖f (Fin.succ i)‖ = C₂
    have hC₁ : C₁ < ε / 2 := by
      simp only [← hC₁_def, ← hε₁_def]
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff <| add_pos_of_pos_of_nonneg zero_lt_two (norm_nonneg _)]
      refine mul_lt_mul_of_pos_left (add_lt_add_right ?_ _) (half_pos hε_pos)
      rw [← hδ_def]
      exact inf_lt_of_left_lt <| inf_lt_of_left_lt one_lt_two
    have hC₂ : C₂ < ε / 2 := by
      simp only [← hC₂_def, ← hε₁_def, ← hδ_def]
      simp only [inf_eq_min]
      rw [min_mul_of_nonneg _ _ (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)]
      refine min_lt_of_right_lt ?_
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff]
      · exact mul_lt_mul_of_pos_left (lt_one_add _) (half_pos hε_pos)
      · exact add_pos_of_pos_of_nonneg zero_lt_one <| Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
    have hC : C₁ + C₂ < ε := by simpa [add_halves] using add_lt_add hC₁ hC₂
    have hC₁_nonneg : 0 ≤ C₁ := by
      rw [← hC₁_def]
      exact mul_nonneg hε₁_pos.le <| add_nonneg hδ_pos.le (norm_nonneg _)
    have hC₂_nonneg : 0 ≤ C₂ := by
      rw [← hC₂_def]
      exact mul_nonneg hδ_pos.le <| Finset.prod_nonneg fun _ _ ↦ norm_nonneg _

    use δ
    refine And.intro hδ_pos ?_
    intro g
    intro hgf
    rw [← Fin.cons_self_tail (g - f)] at hgf
    rw [Fin.cons.norm, sup_lt_iff] at hgf
    refine lt_of_le_of_lt ?_ hC
    rw [ContinuousLinearMap.opNorm_le_iff (add_nonneg hC₁_nonneg hC₂_nonneg)]
    intro q
    rw [opNorm_le_iff _ (mul_nonneg (add_nonneg hC₁_nonneg hC₂_nonneg) (norm_nonneg q))]
    intro x
    simp only [ContinuousLinearMap.sub_apply, compContinuousLinearMapL_apply]
    simp only [sub_apply, compContinuousLinearMap_apply]
    -- TODO: Add identity for `ContinuousMultilinearMap` that captures this step?
    refine le_trans (norm_sub_le_norm_sub_add_norm_sub
      _ (q (Fin.cons (g 0 (x 0)) fun i ↦ f i.succ (x i.succ))) _) ?_
    simp only [add_mul]
    refine add_le_add ?_ ?_
    · rw [← Fin.cons_self_tail (fun i ↦ (g i) (x i)), Fin.tail_def]
      specialize IH (fun i : Fin n ↦ g i.succ) (lt_of_lt_of_le hgf.2 hδ)
      replace IH := le_of_lt IH
      -- TODO: Apply inverse operations to goal instead?
      rw [ContinuousLinearMap.opNorm_le_iff hε₁_pos.le] at IH
      have he_q := continuousMultilinearCurryLeftEquiv_symm_apply q
      generalize (continuousMultilinearCurryLeftEquiv 𝕜 E₁ G).symm = e at he_q
      specialize IH ((e q) (g 0 (x 0)))
      rw [opNorm_le_iff _ (mul_nonneg hε₁_pos.le (norm_nonneg _))] at IH
      specialize IH (fun i : Fin n ↦ x i.succ)
      simp only [ContinuousLinearMap.sub_apply, compContinuousLinearMapL_apply, sub_apply,
        compContinuousLinearMap_apply, he_q] at IH
      refine le_trans IH ?_
      rw [← hC₁_def]
      simp only [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hε₁_pos.le
      simp only [Fin.prod_univ_succ]
      suffices : ‖(e q) (g 0 (x 0))‖ ≤ ‖q‖ * ((δ + ‖f 0‖) * ‖x 0‖)
      · exact le_trans
          (mul_le_mul_of_nonneg_right this (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
          (le_of_eq (by ring))
      refine le_trans (ContinuousLinearMap.le_opNorm (e q) _) ?_
      rw [LinearIsometryEquiv.norm_map]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg q)
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_le_norm_add_norm_sub (f 0) (g 0)) ?_
      rw [add_comm, norm_sub_rev]
      exact add_le_add_right hgf.1.le _

    · rw [← Fin.cons_self_tail (fun i ↦ (f i) (x i)), Fin.tail_def]
      simp (config := {singlePass := true}) only [← Fin.update_cons_zero 0]
      rw [← map_sub]
      refine le_trans (le_opNorm _ _) ?_
      rw [mul_comm _ ‖q‖]
      simp only [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg q)
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [← ContinuousLinearMap.sub_apply, ← hC₂_def]
      suffices : ‖(g 0 - f 0) (x 0)‖ ≤ δ * ‖x 0‖ ∧
          ∏ i : Fin n, ‖f i.succ (x i.succ)‖ ≤ (∏ i : Fin n, ‖f i.succ‖) * ∏ i : Fin n, ‖x i.succ‖
      · exact le_trans
          (mul_le_mul this.1 this.2 (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
            (mul_nonneg hδ_pos.le (norm_nonneg _)))
          (le_of_eq (by ring))
      refine And.intro ?_ ?_
      · exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          <| mul_le_mul_of_nonneg_right hgf.1.le (norm_nonneg _)
      · rw [← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun _ _ ↦
          ContinuousLinearMap.le_opNorm _ _

end Fin

section Fintype

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (G)

theorem ContinuousMultilinearMap.compContinuousLinearMapL_domDomCongr (e : ι ≃ ι')
    (f : (i : ι) → E i →L[𝕜] E₁ i) :
    compContinuousLinearMapL (G := G) f =
      ContinuousLinearMap.comp
        (domDomCongrₗᵢ' 𝕜 E G e).symm.toContinuousLinearEquiv.toContinuousLinearMap
        (ContinuousLinearMap.comp
          (compContinuousLinearMapL (G := G)
            ((LinearIsometryEquiv.piCongrLeft' 𝕜 (fun i : ι ↦ E i →L[𝕜] E₁ i) e) f))
          (domDomCongrₗᵢ' 𝕜 E₁ G e).toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext φ x
  suffices : (e.piCongrLeft' E₁).symm (fun i' ↦ f (e.symm i') (x (e.symm i'))) = fun i ↦ f i (x i)
  · simp [coe_domDomCongrₗᵢ', coe_domDomCongrₗᵢ'_symm, this, -Equiv.piCongrLeft'_symm_apply]
  refine funext ?_
  rw [Equiv.forall_congr_left' e]
  intro i'
  simp only [Equiv.piCongrLeft'_symm_apply_apply]

theorem ContinuousMultilinearMap.continuous_compContinuousLinearMapL :
    Continuous (fun (f : (i : ι) → E i →L[𝕜] E₁ i) ↦ compContinuousLinearMapL (G := G) f) := by
  have e := Fintype.equivFin ι
  rw [continuous_congr (compContinuousLinearMapL_domDomCongr G e)]
  refine .clm_comp continuous_const (.clm_comp ?_ continuous_const)
  exact .comp (continuous_compContinuousLinearMapL_fin G) (LinearIsometryEquiv.continuous _)

variable {G}

theorem ContinuousMultilinearMap.continuous_compContinuousLinearMap_right
    (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    Continuous (fun (f : (i : ι) → E i →L[𝕜] E₁ i) ↦ compContinuousLinearMap g f) := by
  simp only [← compContinuousLinearMapL_apply]
  exact .clm_apply (continuous_compContinuousLinearMapL G) continuous_const

-- theorem Continuous.continuousMultilinear_compContinuousLinearMapL
--     {α : Type*} [TopologicalSpace α]
--     {f : α → (i : ι) → E i →L[𝕜] E₁ i}
--     (hf : Continuous f) :
--     Continuous (fun x ↦ ContinuousMultilinearMap.compContinuousLinearMapL (G := G) (f x)) :=
--   .comp (ContinuousMultilinearMap.continuous_compContinuousLinearMapL G) hf

end Fintype

end Continuous


section Deriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {α : Type*} [NormedAddCommGroup α] [NormedSpace 𝕜 α]
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']


namespace ContinuousMultilinearMap

-- theorem hasFDerivAt (f : ContinuousMultilinearMap 𝕜 E G) (x : (i : ι) → E i)
--     {f' : ((i : ι) → E i) →L[𝕜] G} :
--     HasFDerivAt (𝕜 := 𝕜) (fun x ↦ f x)
--       (∑ i : ι, f x • (ContinuousLinearMap.proj (R := 𝕜) (φ := E) i)) x := by
--   sorry

noncomputable instance :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable instance :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  ContinuousLinearMap.toNormedSpace



-- theorem hasFDerivAt_compContinuousLinearMap
--     {g : ContinuousMultilinearMap 𝕜 E₁ G}
--     {f : (i : ι) → E i →L[𝕜] E₁ i} :
--     HasFDerivAt (𝕜 := 𝕜) (fun f ↦ compContinuousLinearMap g f) q f := by

--   sorry

noncomputable def flipLinear (f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) :
    G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' where
  toFun x := ContinuousLinearMap.compContinuousMultilinearMap (ContinuousLinearMap.apply 𝕜 G' x) f
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp
  cont := by
    -- TODO: Add `ContinuousLinearMap.compContinuousMultilinearMapL_apply[_apply]`?
    change Continuous fun x ↦
      ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 E (G →L[𝕜] G') G' (.apply 𝕜 G' x) f
    refine .clm_apply (.clm_apply continuous_const ?_) continuous_const
    exact (ContinuousLinearMap.apply 𝕜 G').continuous

@[simp]
theorem flipLinear_apply_apply (f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G'))
    (m : G) (x : (i : ι) → E i) :
  flipLinear f m x = (f x) m := rfl

@[simp]
theorem flipMultilinear_flipLinear_apply {f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')} :
    ContinuousLinearMap.flipMultilinear (flipLinear f) = f := rfl

variable (𝕜 E G G')

def leftInverse_flipLinear :
    Function.LeftInverse ContinuousLinearMap.flipMultilinear
      (flipLinear (𝕜 := 𝕜) (E := E) (G := G) (G' := G')) := fun _ ↦ rfl

def rightInverse_flipLinear :
    Function.RightInverse ContinuousLinearMap.flipMultilinear
      (flipLinear (𝕜 := 𝕜) (E := E) (G := G) (G' := G')) := fun _ ↦ rfl

example (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') (m : (i : ι) → E i) (x : G) :
    ContinuousLinearMap.flipMultilinear f m x = y ↔
      (ContinuousLinearMap.flipMultilinear (flipLinear (ContinuousLinearMap.flipMultilinear f))) m x = y := by
  rw [ContinuousLinearMap.flipMultilinear_apply_apply]
  sorry

variable {𝕜 E G G'}

@[simp]
theorem flipLinear_flipMultilinear_apply {f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'} :
    flipLinear (ContinuousLinearMap.flipMultilinear f) = f := rfl



theorem compContinuousLinearMap_apply_eq_piMap (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : (i : ι) → E i →L[𝕜] E₁ i) (x : (i : ι) → E i) :
    compContinuousLinearMap g f x = g (ContinuousLinearMap.piMap f x) := rfl
    -- compContinuousLinearMap g f x = apply 𝕜 E₁ G (ContinuousLinearMap.piMap f x) g := rfl


section

variable {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i}

#check ContinuousLinearMap.flipMultilinear (compContinuousLinearMapL (G := G) f)

end

lemma fderiv_compContinuousLinearMap_apply
    {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i}
    -- TODO: Prove `HasFDerivAt`
    (h : DifferentiableAt 𝕜 (fun f ↦ compContinuousLinearMap g f) f) :
    (fderiv 𝕜 (fun f ↦ compContinuousLinearMap g f) f) df =
      ∑ j : ι, compContinuousLinearMap g (Function.update f j (df j)) := by
    -- (fderiv 𝕜 (fun f ↦ compContinuousLinearMap g f x) f) df =
    --   (∑ j : ι, compContinuousLinearMap g fun i ↦ ite (i = j) df f i) x := by
  ext x
  rw [← fderiv_continuousMultilinear_apply_const_apply h]
  simp only [sum_apply, compContinuousLinearMap_apply]

  have : HasFDerivAt (𝕜 := 𝕜) (fun (f : (i : ι) → E i →L[𝕜] E₁ i) (i : ι) ↦ f i (x i))
      (.pi fun i ↦ .comp (.apply 𝕜 (E₁ i) (x i)) (.proj i)) f :=
    hasFDerivAt_pi.mpr fun i ↦ by
      simp only [← ContinuousLinearMap.proj_apply (R := 𝕜) (φ := fun i ↦ E i →L[𝕜] E₁ i) i]
      simp only [← ContinuousLinearMap.apply_apply (x i)]
      simp only [← ContinuousLinearMap.comp_apply]
      exact ContinuousLinearMap.hasFDerivAt _
  rw [← Function.comp_def g]
  rw [((ContinuousMultilinearMap.hasFDerivAt g _).comp f this).fderiv]

  simp only [ContinuousLinearMap.strongUniformity_topology_eq, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_pi', Function.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.apply_apply]
  rw [linearDeriv_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine congrArg g ?_
  rw [Function.update_eq_iff]
  refine And.intro ?_ ?_
  · simp
  · intro j hji
    simp [hji]


lemma clm_update_apply {f : (i : ι) → E i →L[𝕜] E₁ i} {j : ι} {b : E j →L[𝕜] E₁ j}
    {x : (i : ι) → E i} :
    (fun i ↦ (Function.update f j b i) (x i)) =
      Function.update (fun i ↦ f i (x i)) j (b (x j)) := by
  rw [Function.eq_update_iff]
  refine And.intro ?_ ?_
  · simp
  · intro i h; simp [h]

theorem compContinuousLinearMapContinuousMultilinear_apply {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i} {x : (i : ι) → E i} :
    compContinuousLinearMapContinuousMultilinear 𝕜 E E₁ G f g x = g (fun i ↦ f i (x i)) := rfl

-- TODO: Is there a more fundamental way to express this?
-- Use `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`!
-- And then use `toContinuousLinearMap`?
-- Note: `compContinuousLinearMapContinuousMultilinear` is `MultilinearMap` not `Continuous...`.

/-- Composition with a `ContinuousLinearMap`  -/
def compContinuousLinearMapUpdate (g : ContinuousMultilinearMap 𝕜 E₁ G) (j : ι)
    (f : (i : ι) → E i →L[𝕜] E₁ i) :
    (E j →L[𝕜] E₁ j) →L[𝕜] ContinuousMultilinearMap 𝕜 E G where
  -- toFun := g.compContinuousLinearMap ∘ Function.update f j
  toFun b := g.compContinuousLinearMap (Function.update f j b)
  map_add' a b := by ext; simp [clm_update_apply]
  map_smul' c a := by ext; simp [clm_update_apply]
  cont := by
    simp only
    exact .comp (continuous_compContinuousLinearMap_right g)
      (.update continuous_const j continuous_id)

@[simp]
theorem compContinuousLinearMapUpdate_apply {g : ContinuousMultilinearMap 𝕜 E₁ G} {j : ι}
    {f : (i : ι) → E i →L[𝕜] E₁ i} {b : E j →L[𝕜] E₁ j} :
    compContinuousLinearMapUpdate g j f b = g.compContinuousLinearMap (Function.update f j b) :=
  rfl


theorem compContinuousLinearMap_update
    {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i}
    {j : ι}
    {b : E j →L[𝕜] E₁ j}
    {q : (E j →L[𝕜] E₁ j) →L[𝕜] ContinuousMultilinearMap 𝕜 E G} :
    compContinuousLinearMap g (Function.update f j b) = q b := by
  refine ContinuousMultilinearMap.ext ?_
  intro x
  rw [compContinuousLinearMap_apply, ← compContinuousLinearMapContinuousMultilinear_apply]

  sorry

--   ext x
--   rw [compContinuousLinearMap_apply]

--   -- have h₁ (f : (i : ι) → E i →L[𝕜] E₁ i) (i) :
--   --     f i (x i) = ContinuousLinearMap.apply 𝕜 (E₁ i) (x i) (f i) := by simp
--   -- have h₂ (f : (i : ι) → E i →L[𝕜] E₁ i) (i) :
--   --     f i (x i) = (ContinuousLinearMap.apply 𝕜 (E₁ i)).flip (f i) (x i) := by simp
--   -- simp only [h₂]

--   have : (fun i ↦ (Function.update f j b i) (x i)) =
--       Function.update (fun i ↦ f i (x i)) j (b (x j)) := by
--     rw [Function.eq_update_iff]
--     refine And.intro ?_ ?_
--     · simp
--     · intro i h; simp [h]
--   rw [this]
--   clear this

--   -- Split into two `ContinuousMultilinearMap`s applied to `x` where one is independent of `b`?
--   -- No.. that would not be linear in `b`?


--   -- `∑ j : ι, g (Function.update (fun i => (f i) (x i)) j ((b j) (x j))) = (q b) x`
--   simp only [← toContinuousLinearMap_apply]
--   -- `∑ j : ι, (toContinuousLinearMap g (fun i => (f i) (x i)) j) ((b j) (x j)) = (q b) x`
--   -- Problem: Have `x` inside `toContinuousLinearMap`.

--   simp only [← ContinuousLinearMap.apply_apply (x _) b]
--   simp only [← ContinuousLinearMap.flip_apply (ContinuousLinearMap.apply 𝕜 (E₁ _))]
--   simp only [← ContinuousLinearMap.proj_apply (R := 𝕜) _ x]

--   -- simp only [← ContinuousLinearMap.proj_apply (R := 𝕜) _ b]
--   -- have (j : ι) : Function.update f j (b j) = Function.update f j (ContinuousLinearMap.proj (R := 𝕜) j b) := sorry
--   -- have (j : ι) : Function.update f j (b j) = Function.update f j 0 + Function.update (fun _ ↦ 0) j (b j) := sorry
--   -- have (j : ι) : Function.update f j (b j) = (fun i ↦ ite (i = j) (f i) 0) + (fun i ↦ ite (i = j) 0 (b i)) := sorry

--   have (j : ι) : Function.update f j (b j) =
--     (fun i ↦ ite (i = j) (f i) 0) +
--       (fun i ↦ ite (i = j) 0 (ContinuousLinearMap.proj (R := 𝕜) i b)) := sorry

--   have (j : ι) : Function.update f j (b j) =
--       (fun i ↦ ite (i = j) (f i) 0) +
--       ContinuousLinearMap.pi (R := 𝕜) (φ := fun i ↦ E i →L[𝕜] E₁ i) (fun i ↦ ite (i = j) 0 (.proj i)) b := sorry

--   have (j : ι) : Function.update f j (b j) =
--       Function.update f j 0 +
--       ContinuousLinearMap.pi (R := 𝕜) (φ := fun i ↦ E i →L[𝕜] E₁ i) (Function.update (fun _ ↦ 0) j (.proj j)) b := sorry

--   sorry


theorem hasFDerivAt_compContinuousLinearMap_fin {n : ℕ}
    {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {E₁ : Fin n → Type*} [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
    {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : Fin n) → E i →L[𝕜] E₁ i} :
    HasFDerivAt (fun f ↦ compContinuousLinearMap g f)
      (∑ i, ContinuousLinearMap.comp (compContinuousLinearMapUpdate g i f) (.proj i)) f := by
  induction n with
  | zero =>
    simp [Subsingleton.elim _ (0 : (i : Fin 0) → E i →L[𝕜] E₁ i), hasFDerivAt_const]
  | succ n =>

    sorry


theorem hasFDerivAt_compContinuousLinearMap {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i} :
    HasFDerivAt (fun f ↦ compContinuousLinearMap g f)
      (∑ i, ContinuousLinearMap.comp (compContinuousLinearMapUpdate g i f) (.proj i)) f := by
  -- Not sure how to proceed...
  -- Can't rewrite as product...
  -- Need to use `linearDeriv`?
  have (x : (i : ι) → E i) := (g.hasFDerivAt (fun i ↦ f i (x i))).hasFDerivAtFilter (le_refl _)

  refine HasFDerivAtFilter.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  simp

  sorry


theorem fderiv_compContinuousLinearMap
    {g : ContinuousMultilinearMap 𝕜 E₁ G}
    {f : (i : ι) → E i →L[𝕜] E₁ i} :
    fderiv 𝕜 (fun f ↦ compContinuousLinearMap g f) f =
      ∑ i, ContinuousLinearMap.comp (compContinuousLinearMapUpdate g i f) (.proj i) := by
  refine ContinuousLinearMap.ext ?_
  intro df
  rw [fderiv_compContinuousLinearMap_apply]
  · simp
  · sorry


theorem hasFDerivAt_compContinuousLinearMapL
    {f : (i : ι) → E i →L[𝕜] E₁ i}
    {q : ((i : ι) → E i →L[𝕜] E₁ i) →L[𝕜]
      ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G} :
    HasFDerivAt (𝕜 := 𝕜) (fun f ↦ compContinuousLinearMapL (G := G) f) q f := by
  sorry

theorem fderiv_compContinuousLinearMapL
    {f : (i : ι) → E i →L[𝕜] E₁ i}
    {q : ((i : ι) → E i →L[𝕜] E₁ i) → ((i : ι) → E i →L[𝕜] E₁ i) →L[𝕜]
      ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G} :
    fderiv 𝕜 (fun f ↦ compContinuousLinearMapL (G := G) f) f = q f := by
  refine ContinuousLinearMap.ext ?_
  intro df
  refine ContinuousLinearMap.ext ?_
  intro m
  rw [← fderiv_clm_apply_comm]
  swap
  · sorry
  simp only [compContinuousLinearMapL_apply]
  refine ContinuousMultilinearMap.ext ?_
  intro x
  rw [← fderiv_continuousMultilinear_apply_const_apply]
  swap
  · sorry
  rw [fderiv_continuousMultilinear_apply_const]
  swap
  · sorry

  sorry

  -- ext df g x
  -- -- `(((fderiv 𝕜 (fun f => compContinuousLinearMapL f) f) df) g) x = ((q df) g) x`
  -- rw [← fderiv_clm_apply_comm sorry]
  -- -- `((fderiv 𝕜 (fun y => (compContinuousLinearMapL y) g) f) df) x = ((q df) g) x`
  -- rw [← fderiv_continuousMultilinear_apply_const_apply sorry]
  -- -- `(fderiv 𝕜 (fun y => ((compContinuousLinearMapL y) g) x) f) df = ((q df) g) x`
  -- simp only [compContinuousLinearMapL_apply, compContinuousLinearMap_apply]
  -- -- `(fderiv 𝕜 (fun y => g fun i => (y i) (x i)) f) df = ((q df) g) x`
  -- conv =>
  --   lhs; arg 1; arg 2; intro f
  --   -- TODO: Can't rewrite?
  --   change g fun i ↦ (ContinuousLinearMap.proj (R := 𝕜) i f) (x i)
  --   change g fun i ↦ ContinuousLinearMap.comp (.proj (R := 𝕜) i f) (.proj (R := 𝕜) i) x
  --   simp only [← ContinuousLinearMap.apply_apply]
  --   simp only [← ContinuousLinearMap.compL_apply]
  --   -- simp only [← ]
  --   -- change g (ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj i f) (x i) i f) (x i)
  --   -- simp only [← ContinuousLinearMap.pi_apply f ]
  -- sorry

-- theorem fderiv_compContinuousLinearMapL
--     {f : D → (i : ι) → E i →L[𝕜] E₁ i} (x : D)
--     {q : D →L[𝕜] ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G} :
--     fderiv 𝕜 (fun x ↦ compContinuousLinearMapL (G := G) (f x)) x = q := by
--   refine ContinuousLinearMap.ext ?_
--   intro m
--   refine ContinuousLinearMap.ext ?_
--   intro g
--   rw [← fderiv_clm_apply_comm]
--   swap
--   · sorry
--   simp only [compContinuousLinearMapL_apply]
--   -- `(fderiv 𝕜 (fun y => compContinuousLinearMap g (f y)) x) m = (q m) g`
--   -- Need to express this as x CLM in `m` then `g`; arbitrary function of `x`.
--   refine ContinuousMultilinearMap.ext ?_
--   intro t
--   rw [← fderiv_continuousMultilinear_apply_const_apply]
--   swap
--   · sorry
--   simp only [compContinuousLinearMap_apply]
--   conv => lhs; simp only [← apply_apply]
--   -- `(fderiv 𝕜 (fun y => (apply 𝕜 (fun i => E₁ i) G fun i => (f y i) (t i)) g) x) m = ((q m) g) t`
--   rw [fderiv_clm_apply]
--   rotate_left
--   · sorry
--   · sorry
--   simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
--     ContinuousLinearMap.flip_apply]
--   rw [← fderiv_clm_apply_comm]
--   swap
--   · sorry
--   simp only [apply_apply]
--   -- `(fderiv 𝕜 (fun y => g fun i => (f y i) (t i)) x) m = ((q m) g) t`
--   sorry

-- theorem hasFDerivAt_compContinuousLinearMap (g : D → ContinuousMultilinearMap 𝕜 E₁ G)
--     (f : D → (i : ι) → E i →L[𝕜] E₁ i) (x : D) :
--     HasFDerivAt (𝕜 := 𝕜) (fun x ↦ compContinuousLinearMap (g x) (f x))
--       sorry x := by
--   simp only [← compContinuousLinearMapL_apply]
--   sorry

end ContinuousMultilinearMap

end Deriv
