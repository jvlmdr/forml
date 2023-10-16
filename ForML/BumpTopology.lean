/-
Defines topology for bump functions.
Only considers one dimension (and real) for now.

https://ncatlab.org/nlab/show/distribution#TraditionalDefinition

TODO: Compare to SchwartzSpace.
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Real.ENNReal
import Mathlib.Topology.Algebra.UniformFilterBasis

import ForML.Bump

namespace Bump₁

-- TODO: Maybe there's a way to obtain these identities using Nat.iterate?
lemma iteratedDeriv_zero {n : ℕ} : iteratedDeriv n (0 : ℝ → ℝ) = 0 := by
  induction n with
  | zero => simp
  | succ n h =>
    simp [iteratedDeriv_succ, h]
    ext x
    apply deriv_const

lemma iteratedDeriv_add {n : ℕ} {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    : iteratedDeriv n (f + g) = iteratedDeriv n f + iteratedDeriv n g := by
  induction n with
  | zero => simp
  | succ n h =>
    simp [iteratedDeriv_succ, h]
    ext x
    apply deriv_add
    . apply Differentiable.differentiableAt
      exact ContDiff.differentiable_iteratedDeriv _ hf (WithTop.coe_lt_top _)
    . apply Differentiable.differentiableAt
      exact ContDiff.differentiable_iteratedDeriv _ hg (WithTop.coe_lt_top _)

lemma iteratedDeriv_neg {n : ℕ} {f : ℝ → ℝ} : iteratedDeriv n (-f) = -iteratedDeriv n f := by
  induction n with
  | zero => simp
  | succ n h =>
    conv => rhs; rw [iteratedDeriv_succ]
    rw [iteratedDeriv_succ]
    rw [h]
    ext x
    conv => lhs; arg 1; intro x
    simp [deriv.neg']

lemma iteratedDeriv_const_smul {n : ℕ} {r : ℝ} {f : ℝ → ℝ} : iteratedDeriv n (r • f) = r • iteratedDeriv n f := by
  induction n with
  | zero => simp
  | succ n h =>
    conv => rhs; rw [iteratedDeriv_succ]
    rw [iteratedDeriv_succ]
    rw [h]
    ext x
    conv => lhs; arg 1; intro x
    simp

-- It would be convenient to use `ENNReal` here because
-- it's easier to manipulate `iSup` expressions via `CompleteLattice`.
-- However, `Seminorm` requires `SeminormedRing`.
noncomputable def absNthDeriv (n : ℕ) (f : Bump ℝ) (x : ℝ) : NNReal := ↑‖iteratedDeriv n f.val x‖₊

lemma absNthDeriv_nonneg {n : ℕ} {f : Bump ℝ} (x : ℝ) : 0 ≤ absNthDeriv n f x := by
  simp [absNthDeriv]

lemma absNthDeriv_continuous {n : ℕ} {f : Bump ℝ} : Continuous (absNthDeriv n f) := by
  simp [absNthDeriv]
  apply Continuous.nnnorm
  exact ContDiff.continuous_iteratedDeriv _ f.contDiff (by norm_num)

lemma absNthDeriv_bddAbove_image {n : ℕ} {f : Bump ℝ} {K : Set ℝ} (hK : IsCompact K)
    : BddAbove (absNthDeriv n f '' K) := by
  apply IsCompact.bddAbove_image hK
  exact Continuous.continuousOn absNthDeriv_continuous

lemma iSup₂_coe_eq_coe_sSup {n : ℕ} {f : Bump ℝ} {K : Set ℝ} (hK : IsCompact K)
    : (⨆ (x : ℝ) (_ : x ∈ K), (absNthDeriv n f x : ENNReal))
      = ↑(sSup (absNthDeriv n f '' K)) := by
  rw [ENNReal.coe_sSup (absNthDeriv_bddAbove_image hK)]
  repeat rw [← sSup_image]
  congr
  ext x
  simp

lemma iSup_absNthDeriv_ne_top {n : ℕ} {f : Bump ℝ} {K : Set ℝ} (hK : IsCompact K)
    : (⨆ (x : ℝ) (_ : x ∈ K), (absNthDeriv n f x : ENNReal)) ≠ ⊤ := by
  rw [iSup₂_coe_eq_coe_sSup hK]
  simp

-- Should we make this an instance?
noncomputable def seminorm (K : {s : Set ℝ // IsCompact s}) (n : ℕ) : Seminorm ℝ (Bump ℝ) where
  -- val f := ⨆ (x : ↑K), norm (iteratedDeriv n f.val x)
  -- val f := sSup ((fun x => norm (iteratedDeriv n f.val x)) '' K)
  -- val f := ⨆ (x : ℝ) (_ : x ∈ K), absNthDeriv n f x
  -- val f := sSup (absNthDeriv n f '' K)
  toFun f := ENNReal.toReal (⨆ (x : ℝ) (_ : x ∈ K.val), (absNthDeriv n f x : ENNReal))
  map_zero' := by
    simp [absNthDeriv]
    simp [iteratedDeriv_zero]  -- TODO
  add_le' f g := by
    simp
    -- Obtain ENNReal on both sides to use `iSup₂_le`.
    rw [← ENNReal.toReal_add] <;> try exact iSup_absNthDeriv_ne_top K.property
    rw [ENNReal.toReal_le_toReal]
    rotate_left
    . exact iSup_absNthDeriv_ne_top K.property
    . rw [WithTop.add_ne_top]
      apply And.intro <;> exact iSup_absNthDeriv_ne_top K.property
    apply iSup₂_le
    intro x hx
    -- Split the sum of bumps into a sum of functions.
    simp [absNthDeriv]
    simp [iteratedDeriv_add f.contDiff g.contDiff]
    apply le_trans (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _))
    push_cast
    apply add_le_add <;> apply le_iSup₂ x hx
  neg' f := by
    simp [absNthDeriv]
    simp [iteratedDeriv_neg]
  smul' r f := by
    simp [absNthDeriv]
    simp [iteratedDeriv_const_smul]
    simp [← ENNReal.mul_iSup]

-- instance instMetricSpace : MetricSpace (Bump ℝ) := by
--   apply MetricSpace.induced seminorm.val

noncomputable def seminormFamily : SeminormFamily ℝ (Bump ℝ) ((@Subtype (Set ℝ) IsCompact) × ℕ) :=
  fun m => seminorm m.1 m.2

instance instInhabited : Inhabited (Subtype (IsCompact : Set ℝ → Prop) × ℕ) where
  default := ⟨⟨{0}, isCompact_singleton⟩, 0⟩

-- Follow `SchwartzSpace` definition.
noncomputable instance instTopologicalSpace : TopologicalSpace (Bump ℝ) :=
  seminormFamily.moduleFilterBasis.topology'

lemma withSeminorms : WithSeminorms seminormFamily := by
  exact { topology_eq_withSeminorms := rfl }

instance instContinuousSMul : ContinuousSMul ℝ (Bump ℝ) := by
  rw [withSeminorms.withSeminorms_eq]
  exact seminormFamily.moduleFilterBasis.continuousSMul

instance instTopologicalAddGroup : TopologicalAddGroup (Bump ℝ) :=
  seminormFamily.addGroupFilterBasis.isTopologicalAddGroup

instance instUniformSpace : UniformSpace (Bump ℝ) :=
  seminormFamily.addGroupFilterBasis.uniformSpace

instance instUniformAddGroup : UniformAddGroup (Bump ℝ) :=
  seminormFamily.addGroupFilterBasis.uniformAddGroup

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (Bump ℝ) :=
  withSeminorms.toLocallyConvexSpace

end Bump₁
