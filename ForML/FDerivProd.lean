import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.Series
import Mathlib.Topology.Algebra.Module.Basic

import ForML.MultilinearDeriv

open scoped BigOperators


variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {A : Type*}
-- `[CommMonoid A]` for `Finset.prod`
-- `[NormedRing A] [NormedAlgebra 𝕜 A]` for `Finnorm_iteratedFDeriv_mul_le`
variable [NormedCommRing A] [NormedAlgebra 𝕜 A]

variable {ι : Type*} [DecidableEq ι]

/-- The Fréchet derivative of a product. Auxiliary lemma for `HasFDerivAt.finset_prod_univ`. -/
theorem HasFDerivAt.finset_prod_univ_fin {k : ℕ} {f : Fin k → E → A} {f' : Fin k → E →L[𝕜] A} {x : E}
    (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun x => ∏ i, f i x) (∑ i, (∏ j in {i}ᶜ, f j x) • f' i) x := by
  induction k with
  | zero => exact hasFDerivAt_const 1 x
  | succ k ih =>
    specialize ih (fun i => hf (Fin.succ i))
    simp_rw [Fin.prod_univ_succ]
    rw [Fin.sum_univ_succ]
    refine (HasFDerivAt.mul (hf 0) ih).congr_fderiv ?_
    rw [add_comm]
    refine congrArg₂ _ ?_ ?_
    . refine congrArg₂ _ ?_ rfl
      change ∏ i : Fin k, f ((Fin.succEmbedding k).toEmbedding i) x = _
      rw [← Finset.prod_map Finset.univ (Fin.succEmbedding k).toEmbedding (f := fun i => f i x)]
      congr
      ext i
      simp
    . rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      simp
      intro i
      rw [smul_smul]
      refine congrArg₂ _ ?_ rfl
      have : {Fin.succ i}ᶜ = {0} ∪ Finset.map (Fin.succEmbedding k).toEmbedding {i}ᶜ
      . -- Better `simp` lemmas for `Finset.erase`.
        simp only [Finset.compl_eq_univ_sdiff, ← Finset.erase_eq]
        ext j
        simp
        by_cases h : j = 0
        . simp [h]; exact ne_of_lt (Fin.succ_pos i)
        . simp [h]
      rw [this]
      rw [Finset.prod_union (by simp [Finset.compl_eq_univ_sdiff, ← Finset.erase_eq])]
      rw [Finset.prod_map]
      simp


-- TODO: Cleaner to prove `HasFDerivAt.finset_prod_univ_fin` using `HasFDerivAt.finset_prod_range`?

-- lemma Finset.erase_range_succ {n : ℕ} : Finset.erase (Finset.range (n + 1)) n = Finset.range n := by
--   ext i
--   rw [mem_erase, mem_range, mem_range]
--   rw [lt_iff_le_and_ne (b := n)]
--   rw [Nat.lt_succ, and_comm]

-- theorem HasFDerivAt.finset_prod_range {k : ℕ} {f : ℕ → E → A} {f' : ℕ → E →L[𝕜] A} {x : E}
--     (hf : ∀ i < k, HasFDerivAt (f i) (f' i) x) :
--     HasFDerivAt (fun x => ∏ i in Finset.range k, f i x) (∑ i in Finset.range k, (∏ i in Finset.erase (Finset.range k) i, f i x) • f' i) x := by
--   induction k with
--   | zero => exact hasFDerivAt_const 1 x
--   | succ k ih =>
--     specialize ih (fun i hi => hf i (Nat.lt.step hi))
--     simp_rw [Finset.prod_range_succ]
--     rw [Finset.sum_range_succ]
--     rw [Finset.erase_range_succ]
--     refine (HasFDerivAt.mul ih (hf k (Nat.lt_succ_self k))).congr_fderiv ?_
--     rw [add_comm]
--     rw [add_left_inj]
--     rw [Finset.smul_sum]
--     refine Finset.sum_congr rfl ?_
--     intro i hi
--     simp at hi
--     rw [smul_smul]
--     congr
--     rw [← Finset.prod_insert (f := fun i => f i x) (by simp)]
--     congr
--     ext j
--     simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_range]
--     by_cases hj : j = k
--     . simp [hj, Nat.ne_of_gt hi]
--     . simp [hj]
--       intro _
--       rw [Nat.lt_succ_iff]
--       refine Iff.intro Nat.le_of_lt ?_
--       intro h
--       exact Nat.lt_of_le_of_ne h hj


/-- The Fréchet derivative of a product over a `Fintype`. Auxiliary lemma for `HasFDerivAt.finset_prod`. -/
theorem HasFDerivAt.finset_prod_univ [Fintype ι] {f : ι → E → A}
    {f' : ι → E →L[𝕜] A} {x : E} (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun x => ∏ i, f i x) (∑ i, (∏ j in {i}ᶜ, f j x) • f' i) x := by
  have e := Fintype.equivFin ι
  simp_rw [← e.symm.prod_comp]
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.finset_prod_univ_fin (fun i => hf (e.symm i))) ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr
  symm
  refine Finset.prod_equiv e ?_ ?_
  . simp [Equiv.eq_symm_apply]
  . simp


/-- The Fréchet derivative of a product. -/
theorem HasFDerivAt.finset_prod {s : Finset ι} {f : ι → E → A} {f' : ι → E →L[𝕜] A} {x : E}
    (hf : ∀ i ∈ s, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun x => ∏ i in s, f i x) (∑ i in s, (∏ j in Finset.erase s i, f j x) • f' i) x := by
  conv => arg 1; intro x; rw [← Finset.prod_finset_coe]
  refine HasFDerivAt.congr_fderiv (HasFDerivAt.finset_prod_univ (fun i => hf i.val i.prop)) ?_
  -- TODO: Is there an easier way to do this conversion?
  have (i : (s : Set ι)) : ∏ j in {i}ᶜ, f j x = ∏ j in Finset.erase s i, f j x
  . simp
    refine Finset.prod_nbij (fun i => i) ?_ ?_ ?_ ?_
    . intro j hj
      simp at hj
      simp [Subtype.val_inj]
      exact hj
    . intro _ _ _ _
      simp
      exact Subtype.val_inj.mp
    . intro j hj
      simp
      simp at hj
      use hj.1
      rw [Subtype.ext_iff]
      simp
      exact hj.2
    . simp
  simp_rw [this]
  rw [Finset.sum_finset_coe (f := fun i => (∏ j in Finset.erase s i, f j x) • f' i)]


variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a product. -/
theorem HasDerivAt.finset_prod {s : Finset ι} {f : ι → 𝕜 → A} {f' : ι → A} {x : 𝕜}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun x => ∏ i in s, f i x) (∑ i in s, (∏ j in Finset.erase s i, f j x) * f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    using (HasFDerivAt.finset_prod (fun i hi => (hf i hi).hasFDerivAt)).hasDerivAt

/-- The derivative of a product. -/
theorem HasDerivAt.finset_prod_univ [Fintype ι] {f : ι → 𝕜 → A} {f' : ι → A} {x : 𝕜}
    (hf : ∀ i, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun x => ∏ i, f i x) (∑ i, (∏ j in {i}ᶜ, f j x) * f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    using (HasFDerivAt.finset_prod_univ (fun i => (hf i).hasFDerivAt)).hasDerivAt

-- /-- The derivative of a product using `Function.update`. -/
-- theorem HasDerivAt.finset_prod_univ' [Fintype ι] {f : ι → 𝕜 → A} {f' : ι → A} {x : 𝕜}
--     (hf : ∀ i, HasDerivAt (f i) (f' i) x) :
--     HasDerivAt (fun x => ∏ i, f i x) (∑ i, (∏ j, Function.update (fun j => f j x) i (f' i) j)) x := by
--   simp_rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
--   simp_rw [mul_comm (f' _)]
--   exact HasDerivAt.finset_prod_univ hf


theorem fderiv_finset_prod {s : Finset ι} {f : ι → E → A} {x : E}
    (hf : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    fderiv 𝕜 (fun x => ∏ i in s, f i x) x = ∑ i in s, (∏ j in Finset.erase s i, f j x) • fderiv 𝕜 (f i) x :=
  (HasFDerivAt.finset_prod (fun i hi => (hf i hi).hasFDerivAt)).fderiv

theorem deriv_finset_prod {s : Finset ι} {f : ι → 𝕜 → A} {x : 𝕜}
    (hf : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    deriv (fun x => ∏ i in s, f i x) x = ∑ i in s, (∏ j in Finset.erase s i, f j x) * deriv (f i) x :=
  (HasDerivAt.finset_prod (fun i hi => (hf i hi).hasDerivAt)).deriv


-- TODO: Use something like `Finset.powerset` to write general version?

-- for `HasTemperateGrowth.prod`
-- for `prod_innerSL_smul`
-- for `iteratedFDerivVectorFourierIntegrand`
lemma iteratedFDeriv_prod_succ_apply {s : Finset ι}
    {f : ι → E → A} (hf : ∀ i, ContDiff 𝕜 N (f i))
    {n : ℕ} (hn : n < N) {x : E} {m : Fin (n + 1) → E} :
    iteratedFDeriv 𝕜 (n + 1) (fun x => ∏ i in s, f i x) x m =
    ∑ i in s, (∏ i in Finset.erase s i, f i x) • iteratedFDeriv 𝕜 n (f i) x (Fin.tail m) := by
  rw [iteratedFDeriv_succ_apply_right]

  sorry


-- for `HasTemperateGrowth.prod`
-- for `prod_innerSL_smul`
-- for `iteratedFDerivVectorFourierIntegrand`
lemma iteratedFDeriv_prod_range_succ_apply {k : ℕ}
    {f : ℕ → E → A} (hf : ∀ i, ContDiff 𝕜 N (f i))
    {n : ℕ} (hn : n < N) {x : E} {dx : Fin (n + 1) → E} :
    iteratedFDeriv 𝕜 (n + 1) (fun x => ∏ i in Finset.range k, f i x) x dx =
    ∑ i in Finset.range k, (∏ i in Finset.erase (Finset.range k) i, f i x) • iteratedFDeriv 𝕜 n (f i) x (Fin.tail dx) := by
  -- cases n with
  -- | zero =>
  --   sorry
  -- | succ n =>
  --   sorry
  rw [iteratedFDeriv_succ_apply_left]
  induction k with
  | zero =>
    simp
    cases n with
    | zero =>
      rw [← fderiv_continuousMultilinearMap_apply_comm]
      . simp
      . exact contDiff_const.differentiable_iteratedFDeriv zero_lt_one _
    | succ n =>
      simp [iteratedFDeriv_succ_const]
      -- rw?
      sorry
  | succ k ih => sorry
