import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral

open MeasureTheory


-- Written for `ContinuousMultilinearMap.piCongrLeft`.
-- No longer needed; used `LinearIsometryEquiv.coe_piCongrLeft_symm'` instead.
section PiCongr

namespace LinearEquiv

variable {R : Type*} [Semiring R]
variable {ι ι' : Type*}
variable {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

variable (R φ)  -- Follow e.g. `LinearEquiv.piCongrLeft'_apply`

-- Complements to existing `LinearEquiv.piCongrLeft'_apply`

@[simp]
theorem piCongrLeft'_symm_apply_apply {e : ι ≃ ι'} {x : (i : ι') → φ (e.symm i)} {i' : ι'} :
    (piCongrLeft' R φ e).symm x (e.symm i') = x i' :=
  Equiv.piCongrLeft'_symm_apply_apply φ e x i'

@[simp]
theorem piCongrLeft_apply_apply {e : ι' ≃ ι} {x : (i' : ι') → φ (e i')} {i' : ι'} :
    (piCongrLeft R φ e) x (e i') = x i' :=
  Equiv.piCongrLeft_apply_apply φ e x i'

@[simp]
theorem piCongrLeft_symm_apply {e : ι' ≃ ι} {x : (i : ι) → φ i} {i' : ι'} :
    (piCongrLeft R φ e).symm x i' = x (e i') :=
  Equiv.piCongrLeft_symm_apply φ e x i'

-- These rewrites are useful for using `Function.piCongrLeft'_symm_update`.

theorem coe_piCongrLeft' (e : ι ≃ ι') :
    ⇑(piCongrLeft' R φ e) = ⇑(Equiv.piCongrLeft' φ e) := rfl

theorem coe_piCongrLeft'_symm (e : ι ≃ ι') :
    ⇑(piCongrLeft' R φ e).symm = ⇑(Equiv.piCongrLeft' φ e).symm := rfl

theorem coe_piCongrLeft (e : ι' ≃ ι) :
    ⇑(piCongrLeft R φ e) = ⇑(Equiv.piCongrLeft φ e) := rfl

theorem coe_piCongrLeft_symm (e : ι' ≃ ι) :
    ⇑(piCongrLeft R φ e).symm = ⇑(Equiv.piCongrLeft φ e).symm := rfl

theorem piCongrLeft'_toEquiv (e : ι ≃ ι') :
    (piCongrLeft' R φ e).toEquiv = Equiv.piCongrLeft' φ e := rfl


end LinearEquiv

namespace LinearIsometryEquiv

variable {R : Type*} [Semiring R]
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']
variable {φ : ι → Type*} [∀ i, SeminormedAddCommGroup (φ i)] [∀ i, Module R (φ i)]

-- def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗᵢ[R] (i : ι) → φ i where
--   toLinearEquiv := LinearEquiv.piCongrLeft R φ e
--   norm_map' x := by
--     simp [Pi.norm_def]
--     rw [← Finset.univ_map_equiv_to_embedding e.symm]
--     rw [Finset.sup_map]
--     simp [Function.comp_def]
--     sorry

variable (R φ)

def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗᵢ[R] (i : ι') → φ (e.symm i) where
  toLinearEquiv := LinearEquiv.piCongrLeft' R φ e
  norm_map' x := by
    simp only [Pi.norm_def]
    rw [← Finset.univ_map_equiv_to_embedding e.symm, Finset.sup_map]
    simp [Function.comp_def]

def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗᵢ[R] (i : ι) → φ i := (piCongrLeft' R φ e.symm).symm

-- theorem piCongrLeft_eq {e : ι' ≃ ι} :
--     piCongrLeft R φ e = (piCongrLeft' R φ e.symm).symm := rfl

-- theorem piCongrLeft_symm_eq {e : ι' ≃ ι} :
--     (piCongrLeft R φ e).symm = (piCongrLeft' R φ e.symm) := rfl

-- -- rhs has `e.symm.symm`!
-- theorem piCongrLeft_symm_eq {e : ι' ≃ ι} :
--     (piCongrLeft R φ e).symm = piCongrLeft' R φ e.symm := rfl

-- theorem piCongrLeft_symm_eq' {e : ι' ≃ ι} :
--     (piCongrLeft R φ e.symm) = (piCongrLeft' R φ e).symm := rfl

-- theorem piCongrLeft_symm_eq'' {e : ι' ≃ ι} :
--     (piCongrLeft R φ e.symm).symm = (piCongrLeft' R φ e) := rfl

-- def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗᵢ[R] (i : ι) → φ i where
--   toLinearEquiv := LinearEquiv.piCongrLeft R φ e
--   norm_map' x := by
--     simp only [Pi.norm_def]
--     rw [← Finset.univ_map_equiv_to_embedding e, Finset.sup_map]
--     simp [Function.comp_def, LinearEquiv.piCongrLeft_apply_apply]

@[simp]
theorem piCongrLeft'_apply {e : ι ≃ ι'} {x : (i : ι) → φ i} {i' : ι'} :
    (piCongrLeft' R φ e) x i' = x (e.symm i') :=
  Equiv.piCongrLeft'_apply φ e x i'

@[simp]
theorem piCongrLeft'_symm_apply_apply {e : ι ≃ ι'} {x : (i' : ι') → φ (e.symm i')} {i' : ι'} :
    (piCongrLeft' R φ e).symm x (e.symm i') = x i' :=
  Equiv.piCongrLeft'_symm_apply_apply φ e x i'

@[simp]
theorem piCongrLeft_apply_apply {e : ι' ≃ ι} {x : (i' : ι') → φ (e i')} {i' : ι'} :
    (piCongrLeft R φ e) x (e i') = x i' :=
  Equiv.piCongrLeft_apply_apply φ e x i'

@[simp]
theorem piCongrLeft_symm_apply {e : ι' ≃ ι} {x : (i : ι) → φ i} {i' : ι'} :
    (piCongrLeft R φ e).symm x i' = x (e i') :=
  Equiv.piCongrLeft_symm_apply φ e x i'

end LinearIsometryEquiv

end PiCongr


section ContinuousLinear

variable {ι 𝕜 : Type*}
variable [NormedField 𝕜]
variable [DecidableEq ι]
variable {i : ι}
variable {p : ι → Prop} [DecidablePred p]

variable {α : ι → Type*}
variable [∀ j, NormedAddCommGroup (α j)] [∀ j, NormedSpace 𝕜 (α j)]


/-- Utility lemma for application of `Finset.sup_attach`, `Finset.subtype`, `Finset.subtype_univ`. -/
lemma Finset.sup_filter_eq_sup_univ_subtype_coe [Fintype ι]
    {R : Type*} [SemilatticeSup R] [OrderBot R] {f : ι → R} :
    sup (filter p univ) (fun i => f i) = sup univ (fun i : {j // p j} => f (i : ι)) := by
  rw [← Finset.subtype_univ]
  rw [Finset.subtype]
  simp
  conv => rhs; arg 2; intro x; simp
  rw [sup_attach]


section PiSplitAt

lemma Equiv.piSplitAt_const {E : Type*} (i : ι) :
    Equiv.piSplitAt i (fun _ => E) = Equiv.funSplitAt i E := rfl

lemma Function.update_piSplitAt_symm {i : ι} {a u : α i} {x : ∀ j : {j // j ≠ i}, α j} :
    Function.update ((Equiv.piSplitAt i α).symm (a, x)) i u = (Equiv.piSplitAt i α).symm (u, x) := by
  ext j
  by_cases h : j = i
  . rw [h]; simp
  . simp [h]

-- lemma Function.update_eq_piSplitAt_add_single {i : ι} {x : ∀ i, α i} {u : α i} :
--     Function.update x i u = (Equiv.piSplitAt i α).symm (0, (Equiv.piSplitAt i α x).2) + Pi.single i u := by
--   funext j
--   by_cases h : j = i
--   . rw [h]; simp
--   . simp [h]

lemma Equiv.piSplitAt_symm_zero_add_single {i : ι} {u : α i} {x : ∀ j : {j // j ≠ i}, α j} :
    (Equiv.piSplitAt i α).symm (0, x) + Pi.single i u =
    (Equiv.piSplitAt i α).symm (u, x) := by
  ext j
  by_cases h : j = i
  . rw [h]; simp
  . simp [h]

section Def
variable (𝕜 i α)

/-- Extension of `Equiv.piSplitAt` to `LinearEquiv`. -/
def LinearEquiv.piSplitAt : (∀ j, α j) ≃ₗ[𝕜] α i × (∀ j : {j // j ≠ i }, α j) :=
  (Equiv.piSplitAt i α).toLinearEquiv
    { map_add := fun _ _ => rfl,
      map_smul := fun _ _ => rfl }

/-- Extension of `Equiv.piSplitAt` to `LinearIsometryEquiv`. Requires `Fintype ι` for norm. -/
def LinearIsometryEquiv.piSplitAt [Fintype ι] : (∀ j, α j) ≃ₗᵢ[𝕜] α i × (∀ j : {j // j ≠ i }, α j) where
  toLinearEquiv := LinearEquiv.piSplitAt 𝕜 i α
  norm_map' := fun x => by
    change ‖Equiv.piSplitAt i α x‖ = ‖x‖
    simp [Prod.norm_def, Pi.norm_def]
    rw [← Finset.union_compl (Finset.filter (fun j => j = i) Finset.univ)]
    rw [Finset.compl_filter, Finset.filter_eq']
    rw [Finset.sup_union, sup_eq_max]
    simp
    rw [Finset.sup_filter_eq_sup_univ_subtype_coe]

/--
Extension of `Equiv.piSplitAt` to `ContinuousLinearEquiv`.
Unlike `LinearIsometryEquiv.toContinuousLinearEquiv`, does not require `Fintype ι`.
-/
def ContinuousLinearEquiv.piSplitAt : (∀ j, α j) ≃L[𝕜] α i × (∀ j : {j // j ≠ i }, α j) where
  toLinearEquiv := LinearEquiv.piSplitAt 𝕜 i α
  continuous_toFun := by
    change Continuous (fun x => Equiv.piSplitAt i α x)
    simp
    refine And.intro (continuous_apply i) (Pi.continuous_precomp' _)
  continuous_invFun := by
    change Continuous (fun x => (Equiv.piSplitAt i α).symm x)
    refine continuous_pi ?_
    intro j
    cases Decidable.em (j = i) with
    | inl h =>
      refine Eq.subst (motive := fun k => Continuous fun a => (Equiv.piSplitAt k α).symm a j) h ?_
      simp
      exact continuous_fst
    | inr h =>
      simp [h]
      refine Continuous.comp (continuous_apply _) continuous_snd

end Def

section Apply
variable (𝕜)

lemma LinearEquiv.piSplitAt_apply {x : ∀ j, α j} :
    LinearEquiv.piSplitAt 𝕜 i α x = Equiv.piSplitAt i α x := rfl

lemma LinearIsometryEquiv.piSplitAt_apply [Fintype ι] {x : ∀ j, α j} :
    LinearIsometryEquiv.piSplitAt 𝕜 i α x = Equiv.piSplitAt i α x := rfl

lemma ContinuousLinearEquiv.piSplitAt_apply {x : ∀ j, α j} :
    ContinuousLinearEquiv.piSplitAt 𝕜 i α x = Equiv.piSplitAt i α x := rfl

lemma LinearEquiv.piSplitAt_symm_apply {x : α i × (∀ j : {j // j ≠ i }, α j)} :
    (LinearEquiv.piSplitAt 𝕜 i α).symm x = (Equiv.piSplitAt i α).symm x := rfl

lemma LinearIsometryEquiv.piSplitAt_symm_apply [Fintype ι] {x : α i × (∀ j : {j // j ≠ i }, α j)} :
    (LinearIsometryEquiv.piSplitAt 𝕜 i α).symm x = (Equiv.piSplitAt i α).symm x := rfl

lemma ContinuousLinearEquiv.piSplitAt_symm_apply {x : α i × (∀ j : {j // j ≠ i }, α j)} :
    (ContinuousLinearEquiv.piSplitAt 𝕜 i α).symm x = (Equiv.piSplitAt i α).symm x := rfl

end Apply

end PiSplitAt


section PiEquivPiSubtypeProd

section Def
variable (𝕜 p α)

/-- Extension of `Equiv.piEquivPiSubtypeProd` to `LinearEquiv`. -/
def LinearEquiv.piEquivPiSubtypeProd : (∀ j, α j) ≃ₗ[𝕜] ((∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)) :=
  (Equiv.piEquivPiSubtypeProd p α).toLinearEquiv
    { map_add := fun _ _ => rfl,
      map_smul := fun c x => by
        simp only [Equiv.piEquivPiSubtypeProd_apply, Pi.smul_apply]
        rfl }

/-- Extension of `Equiv.piEquivPiSubtypeProd` to `LinearIsometryEquiv`. -/
def LinearIsometryEquiv.piEquivPiSubtypeProd [Fintype ι] : (∀ j, α j) ≃ₗᵢ[𝕜] ((∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)) where
  toLinearEquiv := LinearEquiv.piEquivPiSubtypeProd 𝕜 p α
  norm_map' := fun x => by
    change ‖Equiv.piEquivPiSubtypeProd p α x‖ = ‖x‖
    simp [Prod.norm_def, Pi.norm_def]
    rw [← Finset.union_compl (Finset.filter p Finset.univ)]
    rw [Finset.sup_union]
    simp [sup_eq_max]
    rw [Finset.sup_filter_eq_sup_univ_subtype_coe]
    rw [Finset.sup_filter_eq_sup_univ_subtype_coe]

/--
Extension of `Equiv.piEquivPiSubtypeProd` to `ContinuousLinearEquiv`.
Unlike `LinearIsometryEquiv.toContinuousLinearEquiv`, does not require `Fintype ι`.
-/
def ContinuousLinearEquiv.piEquivPiSubtypeProd : (∀ j, α j) ≃L[𝕜] ((∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)) where
  toLinearEquiv := LinearEquiv.piEquivPiSubtypeProd 𝕜 p α
  continuous_toFun := by
    change Continuous (fun x => Equiv.piEquivPiSubtypeProd p α x)
    simp
    refine And.intro ?_ ?_ <;> exact Pi.continuous_precomp' _
  continuous_invFun := by
    change Continuous (fun x => (Equiv.piEquivPiSubtypeProd p α).symm x)
    refine continuous_pi ?_
    intro j
    simp
    cases Decidable.em (p j) with
    | inl h => simp [h]; exact (continuous_apply _).comp continuous_fst
    | inr h => simp [h]; exact (continuous_apply _).comp continuous_snd

-- TODO: Move MeasurableEquiv here?

end Def

section Apply
variable (𝕜)

lemma LinearEquiv.piEquivPiSubtypeProd_apply {x : ∀ j, α j} :
    LinearEquiv.piEquivPiSubtypeProd 𝕜 p α x = Equiv.piEquivPiSubtypeProd p α x := rfl

lemma LinearIsometryEquiv.piEquivPiSubtypeProd_apply [Fintype ι] {x : ∀ j, α j} :
    LinearIsometryEquiv.piEquivPiSubtypeProd 𝕜 p α x = Equiv.piEquivPiSubtypeProd p α x := rfl

lemma ContinuousLinearEquiv.piEquivPiSubtypeProd_apply {x : ∀ j, α j} :
    ContinuousLinearEquiv.piEquivPiSubtypeProd 𝕜 p α x = Equiv.piEquivPiSubtypeProd p α x := rfl

lemma LinearEquiv.piEquivPiSubtypeProd_symm_apply {x : (∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)} :
    (LinearEquiv.piEquivPiSubtypeProd 𝕜 p α).symm x = (Equiv.piEquivPiSubtypeProd p α).symm x := rfl

lemma LinearIsometryEquiv.piEquivPiSubtypeProd_symm_apply [Fintype ι] {x : (∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)} :
    (LinearIsometryEquiv.piEquivPiSubtypeProd 𝕜 p α).symm x = (Equiv.piEquivPiSubtypeProd p α).symm x := rfl

lemma ContinuousLinearEquiv.piEquivPiSubtypeProd_symm_apply {x : (∀ j : {j // p j}, α j) × (∀ j : {j // ¬p j}, α j)} :
    (ContinuousLinearEquiv.piEquivPiSubtypeProd 𝕜 p α).symm x = (Equiv.piEquivPiSubtypeProd p α).symm x := rfl

end Apply

end PiEquivPiSubtypeProd

end ContinuousLinear


section Measure

variable {ι : Type*} [DecidableEq ι]
variable {α : ι → Type*}
variable {i : ι}  -- Follow argument order of `MeasurableEquiv.piEquivPiSubtypeProd` rather than `Equiv.SplitAt`.
-- Don't declare `MeasurableSpace` here; instance can interfere with `MeasureSpace`.

lemma Subtype.fintype_subtypeEq [Fintype ι] : (Subtype.fintype fun x => x = i) = Fintype.subtypeEq i := by
  rw [fintype, Fintype.subtypeEq]
  simp [Finset.filter_eq']

lemma Subtype.fintype_subtypeEq' [Fintype ι] : (Subtype.fintype fun x => i = x) = Fintype.subtypeEq' i := by
  rw [fintype, Fintype.subtypeEq']
  simp [Finset.filter_eq]

namespace MeasurableEquiv

section PiSplitAt

section Def
variable (α i)

/-- Applies `MeasurableEquiv.piEquivPiSubtypeProd` to obtain measure-preserving equivalence for `Equiv.piSplitAt`. -/
def piSplitAt [∀ j, MeasurableSpace (α j)] : (∀ j, α j) ≃ᵐ α i × (∀ j : { j // j ≠ i }, α j) :=
  trans (piEquivPiSubtypeProd (fun i => α i) (fun j => j = i)) (prodCongr (piUnique _) (refl _))

-- TODO: Is there a more idiomatic way to define the above?
-- Would be nice to have definitional equality for application of symm?
example [∀ j, MeasurableSpace (α j)] {x : ∀ j, α j} : piSplitAt α i x = Equiv.piSplitAt i α x := rfl
-- example [∀ j, MeasurableSpace (α j)] {x : α i × (∀ j : {j // j ≠ i }, α j)} :
--     (piSplitAt α i).symm x = (Equiv.piSplitAt i α).symm x := rfl

end Def

lemma piSplitAt_eq_trans [∀ j, MeasurableSpace (α j)] :
    piSplitAt α i = trans (piEquivPiSubtypeProd (fun j => α j) (fun j => j = i)) (prodCongr (piUnique _) (refl _)) :=
  rfl

-- Provide this since the definition uses `MeasurableEquiv.trans`.
lemma piSplitAt_toEquiv [∀ j, MeasurableSpace (α j)] : (piSplitAt α i).toEquiv = Equiv.piSplitAt i α :=
  Equiv.ext (fun _ => rfl)

@[simp]
lemma piSplitAt_apply [∀ j, MeasurableSpace (α j)] {x : ∀ j, α j} :
    piSplitAt α i x = Equiv.piSplitAt i α x := rfl

@[simp]
lemma piSplitAt_symm_apply [∀ j, MeasurableSpace (α j)] {x : α i × (∀ j : {j // j ≠ i }, α j)} :
    (piSplitAt α i).symm x = (Equiv.piSplitAt i α).symm x := by
  change (piSplitAt α i).toEquiv.symm x = (Equiv.piSplitAt i α).symm x
  rw [piSplitAt_toEquiv]

section Preserving
variable [Fintype ι]
variable (i α)

lemma measurePreserving_piSplitAt [∀ j, MeasurableSpace (α j)] (μ : ∀ j, Measure (α j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (piSplitAt α i) (Measure.pi μ) (Measure.prod (μ i) (Measure.pi (fun j => μ j))) := by
  rw [piSplitAt_eq_trans]
  refine MeasurePreserving.trans (measurePreserving_piEquivPiSubtypeProd _ _) ?_
  simp [prodCongr]
  refine MeasurePreserving.prod ?_ (MeasurePreserving.id _)
  rw [Subtype.fintype_subtypeEq]
  exact measurePreserving_piUnique _

lemma volume_preserving_piSplitAt [∀ j, MeasureSpace (α j)] [∀ j, SigmaFinite (volume : Measure (α j))] :
    MeasurePreserving (piSplitAt α i) :=
  measurePreserving_piSplitAt α i (fun _ => volume)

end Preserving

end PiSplitAt

end MeasurableEquiv  -- namespace

end Measure
