import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner

import ForML.ContinuousMultilinearMap

open MeasureTheory


variable {α : Type*} [MeasurableSpace α]
variable [TopologicalSpace α]
variable [OpensMeasurableSpace α]
variable [SecondCountableTopology α]

section Fintype

namespace ContinuousMultilinearMap

variable {ι : Type*} [Fintype ι]
variable {ι' : Type*} [Fintype ι']
variable {D : ι → Type*} [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [CompleteSpace F]

/--
Application of a `ContinuousMultilinearMap` can be moved outside the integral.
Multilinear version of `ContinuousLinearMap.integral_apply`.
-/
theorem integral_apply {c : α → ContinuousMultilinearMap ℝ D F}
    {μ : Measure α} (hc : Integrable c μ) {m : ∀ i, D i} :
    ∫ x, (c x) m ∂μ = (∫ x, c x ∂μ) m := by
  simpa using ContinuousLinearMap.integral_comp_comm (apply ℝ D F m) hc

end ContinuousMultilinearMap

end Fintype


-- Originally attempted to prove `integral_apply_comm` with induction on `Fin n` and then equivalence.

-- section Fin

-- variable {n : ℕ}
-- variable {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
-- variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

-- theorem ContinuousMultilinearMap.integral_fin_apply_comm
--     {c : α → ContinuousMultilinearMap ℝ E F}
--     {μ : Measure α} (hc : Integrable c μ) {m : ∀ i, E i} :
--     ∫ x, (c x) m ∂μ = (∫ x, c x ∂μ) m := by
--   induction n with
--   | zero =>
--     rw [Subsingleton.elim m 0]
--     conv =>
--       rhs; arg 1; arg 2; intro x
--       rw [← (continuousMultilinearIsEmptyEquiv ℝ E F).left_inv (c x)]
--       change (continuousMultilinearIsEmptyEquiv ℝ E F).symm.toContinuousLinearEquiv
--           ((continuousMultilinearIsEmptyEquiv ℝ E F) (c x))
--     rw [ContinuousLinearEquiv.integral_comp_comm]
--     simp
--   | succ n ih =>
--     rw [← Fin.cons_self_tail m]
--     conv =>
--       lhs; arg 2; intro x
--       rw [← continuousMultilinearCurryLeftEquiv_symm_apply]
--     rw [ih]
--     swap
--     . refine Integrable.apply_continuousLinearMap ?_ _
--       -- TODO: Avoid repetition here?
--       change Integrable (μ := μ) fun x => (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap (c x)
--       exact ContinuousLinearMap.integrable_comp _ hc
--     rw [← ContinuousLinearMap.integral_apply]
--     swap
--     . change Integrable (μ := μ) fun x => (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap (c x)
--       exact ContinuousLinearMap.integrable_comp _ hc
--     conv =>
--       lhs; arg 1; arg 1; arg 2; intro x
--       change (continuousMultilinearCurryLeftEquiv ℝ E F).symm.toContinuousLinearEquiv (c x)
--     rw [ContinuousLinearEquiv.integral_comp_comm]
--     simp

-- end Fin
