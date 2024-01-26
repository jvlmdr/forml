-- https://github.com/leanprover-community/mathlib4/pull/9576

import Mathlib.Analysis.Distribution.SchwartzSpace

import ForML.MultilinearDeriv

open SchwartzSpace

section IteratedPDeriv

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

lemma SchwartzMap.iteratedPDeriv_eq_iteratedFDeriv {n : ℕ} {m : Fin n → E} {f : 𝓢(E, F)} {x : E} :
    iteratedPDeriv 𝕜 m f x = iteratedFDeriv ℝ n f x m := by
  induction n generalizing f with
  | zero => simp
  | succ n h_ind =>
    rw [iteratedPDeriv_succ_right]
    rw [h_ind]
    rw [iteratedFDeriv_succ_apply_right]
    conv => lhs; arg 1; arg 3; intro y; rw [pderivCLM_apply]
    exact iteratedFDeriv_fderiv_apply_comm (f.smooth n.succ)

end IteratedPDeriv
