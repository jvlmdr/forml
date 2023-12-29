import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For example.

import ForML.HasTemperateGrowth
import ForML.MultilinearDeriv
import ForML.PiEquiv

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

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


-- -- Couldn't prove "apply" lemma. Can just use `compEquiv.toContinuousLinearMap`.
-- lemma compEquivCLM (e : D ≃L[ℝ] E) : 𝓢(E, F) →L[ℝ] 𝓢(D, F) :=
--   compCLM ℝ (g := e) (Function.hasTemperateGrowth_clm e.toContinuousLinearMap)
--     (by
--       refine ⟨1, ‖e.symm.toContinuousLinearMap‖, ?_⟩
--       intro x
--       simp
--       rw [← ContinuousLinearEquiv.apply_symm_apply e.symm x]
--       refine le_trans (e.symm.toContinuousLinearMap.le_op_norm _) ?_
--       simp
--       exact mul_le_mul_of_nonneg_left (by simp) (norm_nonneg _))

-- lemma compEquivCLM_apply {e : D ≃L[ℝ] E} {f : 𝓢(E, F)} {x : D} :
--     compEquivCLM e f x = f (⇑e x) := by
--   -- rfl
--   sorry


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

@[simp]
lemma compEquiv_apply {e : E ≃L[ℝ] D} {f : 𝓢(D, F)} {x : E} :
    (compEquiv e f) x = f (e x) := rfl

-- How to split the input of a Schwartz function:
noncomputable example {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (f : 𝓢(ι → E, F)) : 𝓢(E × ({ j // j ≠ i } → E), F) :=
  compEquiv (ContinuousLinearEquiv.piSplitAt ℝ i (fun _ => E)).symm f

-- How to convert between EuclideanSpace and pi type:
noncomputable example {ι : Type*} [Fintype ι] [DecidableEq ι] (f : 𝓢(ι → ℝ, F)) : 𝓢(EuclideanSpace ℝ ι, F) :=
  compEquiv (EuclideanSpace.equiv ι ℝ) f

-- How to convert between finite-dimensional vector space and pi type:
noncomputable example [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : FiniteDimensional.finrank ℝ E = n)
    (f : 𝓢(E, F)) : 𝓢(Fin n → ℝ, F) :=
  compEquiv (FiniteDimensional.finBasisOfFinrankEq ℝ E hn).equivFun.toContinuousLinearEquiv.symm f

-- How to convert between finite-dimensional vector space and pi type:
noncomputable example [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : FiniteDimensional.finrank ℝ E = n)
    (f : 𝓢(E, F)) : 𝓢(Fin n → ℝ, F) :=
  compEquiv (FiniteDimensional.finBasisOfFinrankEq ℝ E hn).equivFun.toContinuousLinearEquiv.symm f


-- No longer needed.
-- Ended up using `compConstAddCLM` and `compSingleCLM` instead in order to
-- curry one dimension of a Schwartz map in the derivative.


-- def curryLeftCLM (x : D) : 𝓢(D × E, F) →L[𝕜] 𝓢(E, F) :=
--   mkCLM (fun f y => f (x, y))
--     (by simp)
--     (by simp)
--     (fun f => (f.smooth ⊤).comp (contDiff_prod_mk_right x))
--     (fun m => by
--       refine ⟨Finset.Iic m, 2 ^ m.1, ?_⟩
--       simp
--       refine ⟨(by norm_num), ?_⟩
--       intro f y
--       refine le_trans ?_ (SchwartzMap.one_add_le_sup_seminorm_apply (le_refl m.1) (le_refl m.2) f (x, y))
--       refine mul_le_mul ?_ ?_ (norm_nonneg _) (by simp)
--       . refine pow_le_pow_of_le_left (norm_nonneg y) ?_ m.1
--         refine le_trans ?_ (by simp : ‖(x, y)‖ ≤ 1 + ‖(x, y)‖)
--         simp [Prod.norm_def]
--       . rcases m with ⟨k, n⟩
--         simp
--         cases n with
--         | zero => simp
--         | succ n =>
--           rw [← norm_iteratedFDeriv_fderiv]
--           -- conv =>
--           --   lhs; arg 1; arg 3
--           --   intro u
--           --   change fderiv ℝ (f ∘ (fun y => (x, y))) u
--           --   rw [fderiv.comp _ f.differentiableAt ((differentiableAt_const _).prod differentiableAt_id')]
--           -- simp
--           sorry)

-- section Def

-- variable (𝕜 : Type*) [IsROrC 𝕜]
-- variable {ι M F : Type*}
-- variable [Fintype ι] [DecidableEq ι]
-- variable [NormedRing M]
-- variable [NormedAddCommGroup F]
-- variable [NormedSpace ℝ M] [NormedSpace 𝕜 M]
-- variable [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F ]

-- variable (p : ι → Prop) [DecidablePred p]

-- noncomputable def piSubtype_curryLeft (x : {j // p j} → M) : 𝓢(ι → M, F) →L[ℝ] 𝓢({j // ¬p j} → M, F) :=
--   mkCLM (fun f y => f (ContinuousLinearMap.piSubtype_coprod ℝ p (x, y)))
--     (by simp)
--     (by simp)
--     (fun f => by
--       simp
--       refine ContDiff.comp f.smooth' ?_
--       simp_rw [ContinuousLinearMap.piSubtype_coprod_eq_inl_add_inr]
--       exact ContDiff.add contDiff_const (ContinuousLinearMap.contDiff _))
--     (fun m => by
--       simp
--       refine ⟨Finset.Iic m, 1, ?_⟩
--       simp
--       intro f y
--       have hf := f.decay'
--       rcases m with ⟨k, n⟩
--       simp
--       specialize hf k n
--       -- simp_rw [ContinuousLinearMap.piSubtype_coprod_eq_inl_add_inr]
--       -- simp_rw [iteratedFDeriv_add_apply']
--       sorry)

-- end Def

end SchwartzMap
