import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import ForML.PiEquiv

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [mE : MeasureSpace E] [SigmaFinite mE.volume]

-- TODO: Generalize to `(j : ι) → E j`? Rename this version to "const" or "vector"?
lemma integral_piSplitAt (i : ι) {f : (ι → E) → F} :
    ∫ x, f x = ∫ p : E × ({j // j ≠ i} → E), f (fun j => if h : j = i then p.1 else p.2 ⟨j, h⟩) := by
  have he := (MeasurableEquiv.volume_preserving_piSplitAt (fun _ => E) i).symm
  rw [← he.map_eq]
  rw [integral_map_equiv]
  rw [Measure.volume_eq_prod]
  rfl

lemma integrable_piSplitAt (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    Integrable fun p : E × ({j // j ≠ i} → E) => f (fun j => if h : j = i then p.1 else p.2 ⟨j, h⟩) := by
  change Integrable (f ∘ ((MeasurableEquiv.piSplitAt (fun _ => E) i).symm)) _
  rw [← integrable_map_equiv]
  -- TODO: Cleaner way that avoids applying same steps in reverse?
  have he := (MeasurableEquiv.volume_preserving_piSplitAt (fun _ => E) i).symm
  rw [he.map_eq]
  exact hf

lemma integral_piSplitAt_left (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (u : E) (x : {j // j ≠ i} → E), f (fun j : ι => if h : j = i then u else x ⟨j, h⟩) := by
  rw [integral_piSplitAt i]
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ (integrable_piSplitAt i hf)]

lemma integral_piSplitAt_right (i : ι) {f : (ι → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (x : {j // j ≠ i} → E) (u : E), f (fun j : ι => if h : j = i then u else x ⟨j, h⟩) := by
  rw [integral_piSplitAt_left i hf]
  rw [integral_integral_swap]
  rw [Function.uncurry_def]
  exact integrable_piSplitAt i hf
