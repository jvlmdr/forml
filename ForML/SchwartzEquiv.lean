import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace

import ForML.HasTemperateGrowth
import ForML.MultilinearDeriv
import ForML.PiEquiv

open SchwartzSpace

namespace SchwartzMap

variable {𝕜 D E F : Type*}
variable [IsROrC 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace 𝕜 D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

lemma ContinuousLinearEquiv.norm_le_norm_symm_mul_norm_apply (e : E ≃L[𝕜] D) {x : E} :
    ‖x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := by
  suffices : ‖e.symm.toContinuousLinearMap (e x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖
  . simpa
  refine le_trans (ContinuousLinearMap.le_op_norm _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp [le_add_iff_nonneg_left]

section Def

variable (𝕜)

lemma compCLM_apply {g : D → E} {hg : Function.HasTemperateGrowth g}
    {hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : D), ‖x‖ ≤ C * (1 + ‖g x‖) ^ k}
    {f : 𝓢(E, F)} {x : D} :
    (compCLM 𝕜 hg hg_upper f) x = f (g x) := rfl

-- TODO: Generalize to `≃L[𝕜]`? Requires modification of `hasTemperateGrowth_clm` and its dependencies.
/-- ContinuousLinearEquiv between Schwartz spaces defined by composition on the right with an equivalence. -/
def compEquiv (e : E ≃L[ℝ] D) : 𝓢(D, F) ≃L[ℝ] 𝓢(E, F) where
  toLinearMap := ContinuousLinearMap.toLinearMap (compCLM ℝ (Function.hasTemperateGrowth_clm e.toContinuousLinearMap)
    (by
      refine ⟨1, ‖e.symm.toContinuousLinearMap‖, ?_⟩
      simp
      intro x
      refine le_trans (ContinuousLinearEquiv.norm_le_norm_symm_mul_norm_apply e) ?_
      exact mul_le_mul_of_nonneg_left (by simp) (norm_nonneg _)))
  invFun := compCLM ℝ (Function.hasTemperateGrowth_clm e.symm.toContinuousLinearMap)
    (by
      refine ⟨1, ‖e.toContinuousLinearMap‖, ?_⟩
      simp
      intro x
      refine le_trans (ContinuousLinearEquiv.norm_le_norm_symm_mul_norm_apply e.symm) ?_
      simp
      exact mul_le_mul_of_nonneg_left (by simp) (norm_nonneg _))
  left_inv := fun f => by ext x; simp [compCLM_apply]
  right_inv := fun f => by ext x; simp [compCLM_apply]
  continuous_toFun := by
    simp
    exact ContinuousLinearMap.continuous _
  continuous_invFun := by
    simp
    exact ContinuousLinearMap.continuous _

end Def

end SchwartzMap
