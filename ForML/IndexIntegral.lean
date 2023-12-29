import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import ForML.PiEquiv

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [mE : MeasureSpace E] [SigmaFinite (volume : Measure E)]
variable {D : ι → Type*}
variable [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
variable [mD : ∀ i, MeasureSpace (D i)] [∀ i, SigmaFinite (mD i).volume]
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Split an integral over a pi type into an integral over a product of one element and a pi type. -/
theorem integral_piSplitAt (i : ι) {f : (∀ i, D i) → F} :
    ∫ x, f x = ∫ p : (D i) × (∀ j : {j // j ≠ i}, D j), f ((Equiv.piSplitAt i D).symm p) := by
  have he := (MeasurableEquiv.volume_preserving_piSplitAt D i).symm
  rw [← he.map_eq]
  rw [integral_map_equiv]
  rw [Measure.volume_eq_prod]
  simp only [MeasurableEquiv.piSplitAt_symm_apply]

/--
Split an integral over a pi type into an integral over a product of one element and a pi type.
See `integral_piSplitAt` for the dependent version.
-/
lemma integral_funSplitAt (i : ι) {f : (ι → E) → F} :
    ∫ x, f x = ∫ p : E × ({j // j ≠ i} → E), f ((Equiv.funSplitAt i E).symm p) := by
  rw [integral_piSplitAt i]
  rfl

/-- A function that is integrable on a pi type is integrable on the split product. -/
theorem MeasureTheory.Integrable.piSplitAt (i : ι) {f : (∀ i, D i) → F} (hf : Integrable f) :
    Integrable fun p : (D i) × (∀ j : {j // j ≠ i}, D j) => f ((Equiv.piSplitAt i D).symm p) := by
  simp_rw [← MeasurableEquiv.piSplitAt_symm_apply]
  change Integrable (f ∘ ((MeasurableEquiv.piSplitAt D i).symm)) _
  rw [← integrable_map_equiv]
  -- Like `integral_piSplitAt` in reverse. TODO: Cleaner way that avoids this?
  have he := (MeasurableEquiv.volume_preserving_piSplitAt D i).symm
  rw [he.map_eq]
  exact hf

/--
A function that is integrable on a pi type is integrable on the split product.
See `MeasureTheory.Integrable.piSplitAt` for the dependent version.
-/
lemma MeasureTheory.Integrable.funSplitAt (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    Integrable fun p : E × ({j // j ≠ i} → E) => f ((Equiv.funSplitAt i E).symm p) :=
  hf.piSplitAt i

/-- Combines `integral_piSplitAt` and `Integrable.piSplitAt` for convenience. -/
lemma integral_piSplitAt_left (i : ι) {f : (∀ i, D i) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (u : D i) (x : ∀ j : {j // j ≠ i}, D j), f ((Equiv.piSplitAt i D).symm (u, x)) := by
  rw [integral_piSplitAt i]
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ (hf.piSplitAt i)]

/-- Combines `integral_funSplitAt` and `Integrable.funSplitAt` for convenience. -/
lemma integral_funSplitAt_left (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (u : E) (x : {j // j ≠ i} → E), f ((Equiv.funSplitAt i E).symm (u, x)) :=
  integral_piSplitAt_left i hf

/-- Combines `integral_piSplitAt` and `Integrable.piSplitAt` for convenience. -/
lemma integral_piSplitAt_right (i : ι) {f : (∀ i, D i) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (x : ∀ j : {j // j ≠ i}, D j) (u : D i), f ((Equiv.piSplitAt i D).symm (u, x)) := by
  rw [integral_piSplitAt_left i hf]
  rw [integral_integral_swap]
  rw [Function.uncurry_def]
  exact hf.piSplitAt i

/-- Combines `integral_funSplitAt` and `Integrable.funSplitAt` for convenience. -/
lemma integral_funSplitAt_right (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (x : {j // j ≠ i} → E) (u : E), f ((Equiv.funSplitAt i E).symm (u, x)) := by
  exact integral_piSplitAt_right i hf


-- lemma Equiv.piSplitAt_symm_inl_eq_single {i : ι} {u : D i} :
--     (Equiv.piSplitAt i D).symm (u, 0) = Pi.single i u := by
--   funext j
--   simp
--   by_cases hj : j = i
--   . rw [hj]; simp
--   . simp [hj]

-- lemma Equiv.piSplitAt_symm_inl_add_inr {i : ι} {u : D i} {v : ∀ j : { j // j ≠ i }, D j} :
--     (Equiv.piSplitAt i D).symm (u, 0) + (Equiv.piSplitAt i D).symm (0, v) = (Equiv.piSplitAt i D).symm (u, v) := by
--   funext j
--   simp
--   by_cases hj : j = i
--   . rw [hj]; simp
--   . simp [hj]

-- lemma Equiv.piSplitAt_symm_eq_single_add {i : ι} {p : D i × (∀ j : { j // j ≠ i }, D j)} :
--     (Equiv.piSplitAt i D).symm p = Pi.single i p.1 + (Equiv.piSplitAt i D).symm (0, p.2) := by
--   funext j
--   simp
--   by_cases hj : j = i
--   . rw [hj]; simp
--   . simp [hj]

-- lemma Equiv.piSplitAt_symm_apply_add_single {i : ι} {a b : D i} {p : D i × (∀ j : { j // j ≠ i }, D j)} :
--     (Equiv.piSplitAt i D).symm p + Pi.single i b = (Equiv.piSplitAt i D).symm (p.1 + b, p.2) := by
--   funext j
--   simp
--   by_cases hj : j = i
--   . rw [hj]; simp
--   . simp [hj]

-- lemma Equiv.splitAt_symm_apply_sub_single {i : ι} {x : { j // j ≠ i } → ℝ} {a b : ℝ} :
--     (Equiv.funSplitAt i ℝ).symm (a, x) - b • Pi.single i 1 = (Equiv.funSplitAt i ℝ).symm (a - b, x) := by
--   funext j
--   simp
--   by_cases hj : j = i
--   . rw [hj]; simp
--   . simp [hj]
