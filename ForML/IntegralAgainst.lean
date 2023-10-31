import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.VectorMeasure

import ForML.LpHoelder
import ForML.SchwartzLp

open MeasureTheory SchwartzSpace
open scoped Real NNReal ENNReal

-- Plan is to define mapping from `L1` to `L1`,
-- then show continuous,
-- then transfer to `𝓢(E, F)` using `ContinuousLinearMap.comp`.

namespace SchwartzMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]


-- TODO: Define using `g : Lp (α := E) 𝕜 p` or just `g : E → 𝕜`?
noncomputable def integral_Lp_smul {p : ENNReal}
    (g : Lp (α := E) 𝕜 p) (φ : 𝓢(E, F)) : F :=
  ∫ (x : E), g x • φ x

lemma integral_Lp_smul_def {p : ENNReal} {g : Lp (α := E) 𝕜 p} {φ : 𝓢(E, F)} :
    integral_Lp_smul g φ = ∫ (x : E), g x • φ x := by rfl

-- TODO: Define these as bilinear CLM? Although depends on topology of `g`?
lemma integral_Lp_smul_add {p : ENNReal} (hp : 1 ≤ p)
    (g : Lp (α := E) 𝕜 p) (φ θ : 𝓢(E, F)) :
    integral_Lp_smul g (φ + θ) = integral_Lp_smul g φ + integral_Lp_smul g θ := by
  simp [integral_Lp_smul]
  have hpq := ENNReal.conjugate_conjugateExponent hp
  generalize p.conjugateExponent = q at hpq
  rw [integral_add]
  . exact integrable_Lp_smul_Lq hpq (Lp.memℒp g) (φ.memℒp q)
  . exact integrable_Lp_smul_Lq hpq (Lp.memℒp g) (θ.memℒp q)

-- Note: Doesn't require `1 ≤ p`?
lemma integral_Lp_smul_smul {p : ENNReal}
    (g : Lp (α := E) 𝕜 p) (c : 𝕜) (φ : 𝓢(E, F)) :
    integral_Lp_smul g (c • φ) = c • integral_Lp_smul g φ := by
  simp [integral_Lp_smul]
  simp_rw [smul_comm _ c]
  rw [integral_smul]

lemma L1_integral_Lp_smul {p q : ENNReal} (hpq : p⁻¹ + q⁻¹ = 1) {g : Lp (α := E) 𝕜 p} {φ : 𝓢(E, F)} :
    L1.integral (L1_of_Lp_smul_Lq hpq g (φ.toLp q)) = integral_Lp_smul g φ := by
  rw [L1.integral_eq_integral, integral_Lp_smul]
  rw [integral_congr_ae (coeFn_L1_of_Lp_smul_Lq hpq)]
  refine integral_congr_ae ?_
  simp
  refine Filter.EventuallyEq.smul (by rfl) ?_
  exact SchwartzMap.coeFn_toLp _

end SchwartzMap
