import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral

open MeasureTheory


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

/-- Applies `MeasurableEquiv.piEquivPiSubtypeProd` to obtain measure-preserving equivalence for `piSplitAt`. -/
def piSplitAt [∀ j, MeasurableSpace (α j)] : (∀ j, α j) ≃ᵐ α i × (∀ j : { j // j ≠ i }, α j) :=
  trans (piEquivPiSubtypeProd (fun i => α i) (fun j => j = i)) (prodCongr (piUnique _) (refl _))

end Def

lemma piSplitAt_eq_trans [∀ j, MeasurableSpace (α j)] :
    piSplitAt α i = trans (piEquivPiSubtypeProd (fun j => α j) (fun j => j = i)) (prodCongr (piUnique _) (refl _)) :=
  rfl

-- Provide this since the definition uses `MeasurableEquiv.trans`.
lemma piSplitAt_toEquiv [∀ j, MeasurableSpace (α j)] : (piSplitAt α i).toEquiv = Equiv.piSplitAt i α :=
  Equiv.ext (fun _ => rfl)

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
