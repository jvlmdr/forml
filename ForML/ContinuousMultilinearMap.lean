import Mathlib.Analysis.NormedSpace.Multilinear.Curry

import ForML.PiEquiv

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

namespace ContinuousMultilinearMap

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E₁ : ι → Type*} [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

section Apply

variable (𝕜 E G)

/--
The application of a multilinear map as a `ContinuousLinearMap`.
(Not a bilinear map like `ContinuousLinearMap.apply` due to multilinearity with respect to `x`.)
-/
def apply (x : ∀ i, E i) : ContinuousMultilinearMap 𝕜 E G →L[𝕜] G where
  toFun c := c x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_left x

variable {𝕜 E G}

@[simp]
lemma apply_apply {x : ∀ i, E i} {c : ContinuousMultilinearMap 𝕜 E G} :
    (apply 𝕜 E G x) c = c x := rfl

end Apply

section MkPiField

variable (𝕜 G)

noncomputable def mkPiFieldL :
    G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ 𝕜) G where
  toFun := ContinuousMultilinearMap.mkPiField 𝕜 ι
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
    refine lt_of_le_of_lt ((op_norm_le_iff _ dist_nonneg).mpr ?_) hab
    intro m
    refine le_of_eq ?_
    rw [mul_comm, dist_eq_norm]
    simp [← smul_sub, norm_smul]

variable {𝕜 G}

@[simp]
theorem mkPiFieldL_apply {z : G} :
    mkPiFieldL 𝕜 G z = ContinuousMultilinearMap.mkPiField 𝕜 ι z := rfl

end MkPiField

end ContinuousMultilinearMap

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
  rw [Finset.prod_congr rfl (fun (i : ι) _ ↦ congrArg (‖x ·‖) (σ.symm_apply_apply i))]

variable (𝕜 D F)

/--
Dependent version of `ContinuousMultilinearMap.domDomCongrLinearEquiv`;
continuous version of `MultilinearMap.domDomCongrLinearEquiv'`;
isometric version of `ContinuousMultilinearMap.domDomCongrEquiv`.
-/
def domDomCongrₗᵢ' (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 D F ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun i' : ι' ↦ D (σ.symm i')) F where
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
  | zero =>
    intro ε hε
    use 1
    refine And.intro zero_lt_one ?_
    intro g _
    simp [Subsingleton.elim f g, hε]
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
    rw [ContinuousLinearMap.op_norm_le_iff (add_nonneg hC₁_nonneg hC₂_nonneg)]
    intro q
    rw [op_norm_le_iff _ (mul_nonneg (add_nonneg hC₁_nonneg hC₂_nonneg) (norm_nonneg q))]
    intro m
    simp only [ContinuousLinearMap.sub_apply, compContinuousLinearMapL_apply]
    simp only [sub_apply, compContinuousLinearMap_apply]
    -- TODO: Add identity for `ContinuousMultilinearMap` that captures this step?
    refine le_trans (norm_sub_le_norm_sub_add_norm_sub
      _ (q (Fin.cons (g 0 (m 0)) fun i ↦ f i.succ (m i.succ))) _) ?_
    simp only [add_mul]
    refine add_le_add ?_ ?_
    · rw [← Fin.cons_self_tail (fun i ↦ (g i) (m i))]
      specialize IH (fun i : Fin n ↦ g i.succ) (lt_of_lt_of_le hgf.2 hδ)
      replace IH := le_of_lt IH
      -- TODO: Apply inverse operations to goal instead?
      rw [ContinuousLinearMap.op_norm_le_iff hε₁_pos.le] at IH
      have he_q := continuousMultilinearCurryLeftEquiv_symm_apply q
      generalize (continuousMultilinearCurryLeftEquiv 𝕜 E₁ G).symm = e at he_q
      specialize IH ((e q) (g 0 (m 0)))
      rw [op_norm_le_iff _ (mul_nonneg hε₁_pos.le (norm_nonneg _))] at IH
      specialize IH (fun i : Fin n ↦ m i.succ)
      simp only [ContinuousLinearMap.sub_apply, compContinuousLinearMapL_apply, sub_apply,
        compContinuousLinearMap_apply, he_q] at IH
      refine le_trans IH ?_
      rw [← hC₁_def]
      simp only [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hε₁_pos.le
      simp only [Fin.prod_univ_succ]
      suffices : ‖(e q) (g 0 (m 0))‖ ≤ ‖q‖ * ((δ + ‖f 0‖) * ‖m 0‖)
      · exact le_trans
          (mul_le_mul_of_nonneg_right this (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
          (le_of_eq (by ring))
      refine le_trans (ContinuousLinearMap.le_op_norm (e q) _) ?_
      rw [LinearIsometryEquiv.norm_map]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg q)
      refine le_trans (ContinuousLinearMap.le_op_norm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_le_norm_add_norm_sub (f 0) (g 0)) ?_
      rw [add_comm, norm_sub_rev]
      exact add_le_add_right hgf.1.le _

    · -- TODO: Ugly to specify unused value (0) here. Nicer way to obtain this result?
      have := map_sub q (Fin.cons 0 fun i ↦ f i.succ (m i.succ)) 0 (g 0 (m 0)) (f 0 (m 0))
      simp only [Fin.update_cons_zero] at this
      rw [← Fin.cons_self_tail (fun i ↦ (f i) (m i)), Fin.tail_def, ← this]
      refine le_trans (le_op_norm _ _) ?_
      rw [mul_comm _ ‖q‖]
      simp only [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg q)
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [← ContinuousLinearMap.sub_apply, ← hC₂_def]
      suffices : ‖(g 0 - f 0) (m 0)‖ ≤ δ * ‖m 0‖ ∧
          ∏ i : Fin n, ‖f i.succ (m i.succ)‖ ≤ (∏ i : Fin n, ‖f i.succ‖) * ∏ i : Fin n, ‖m i.succ‖
      · exact le_trans
          (mul_le_mul this.1 this.2 (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
            (mul_nonneg hδ_pos.le (norm_nonneg _)))
          (le_of_eq (by ring))
      refine And.intro ?_ ?_
      · exact le_trans (ContinuousLinearMap.le_op_norm _ _)
          <| mul_le_mul_of_nonneg_right hgf.1.le (norm_nonneg _)
      · rw [← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun _ _ ↦
          ContinuousLinearMap.le_op_norm _ _

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
    Continuous (compContinuousLinearMapL (𝕜 := 𝕜) (E := E) (E₁ := E₁) (G := G)) := by
  have e := Fintype.equivFin ι
  rw [continuous_congr (compContinuousLinearMapL_domDomCongr G e)]
  refine .clm_comp continuous_const (.clm_comp ?_ continuous_const)
  exact .comp (continuous_compContinuousLinearMapL_fin G) (LinearIsometryEquiv.continuous _)

end Fintype
