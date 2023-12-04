import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Integral.Bochner

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [mE : MeasureSpace E] [SigmaFinite mE.volume]

/-- If a function is integrable on `ℝ^(n+1)`, then it is integrable on `ℝ × ℝ^n`. -/
lemma integrable_comp_insertNth {i : Fin (n + 1)} {f : (Fin (n + 1) → E) → F} (hf : Integrable f) :
    Integrable fun p : E × (Fin n → E) => f (Fin.insertNth i p.1 p.2) := by
  change Integrable (f ∘ (MeasurableEquiv.piFinSuccAboveEquiv (fun _ => E) i).symm) _
  rw [← integrable_map_equiv]
  have h := (volume_preserving_piFinSuccAboveEquiv (fun _ => E) i).symm
  rw [h.map_eq]
  exact hf

/-- Rewrite an integral over `E^(n+1)` as an integral over `E` of an integral over `E^n`. -/
theorem integral_pi_left (i : Fin (n + 1)) {f : (Fin (n + 1) → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (xi : E) (x : Fin n → E), f (Fin.insertNth i xi x) := by
  have h := (volume_preserving_piFinSuccAboveEquiv (fun _ => E) i).symm
  rw [← h.map_eq]
  rw [integral_map_equiv]
  simp
  rw [Measure.volume_eq_prod]
  rw [integral_prod]
  rw [← Measure.volume_eq_prod]
  exact integrable_comp_insertNth hf

/-- Rewrite an integral over `E^(n+1)` as an integral over `E^n` of an integral over `E`. -/
theorem integral_pi_right (i : Fin (n + 1)) {f : (Fin (n + 1) → E) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ (x : Fin n → E) (xi : E), f (Fin.insertNth i xi x) := by
  rw [integral_pi_left i hf]
  rw [integral_integral_swap]
  rw [Function.uncurry_def]
  rw [← Measure.volume_eq_prod]
  exact integrable_comp_insertNth hf
