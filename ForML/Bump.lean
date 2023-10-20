/-
Defines smooth, compact bump functions.

https://ncatlab.org/nlab/show/bump+function
https://proofwiki.org/wiki/Definition:Test_Function
-/

import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Topology UniformConvergence

def IsBump {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] (f : α → ℝ) : Prop :=
  HasCompactSupport f ∧ ContDiff ℝ ⊤ f

namespace IsBump
variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]

-- `Mul` cannot be obtained from `Submodule` (unlike `Add`, `SMul`, `Neg`).
lemma mul {f g : α → ℝ} (hf : IsBump f) (hg : IsBump g) : IsBump (f * g) := by
  simp [IsBump]
  apply And.intro
  . apply HasCompactSupport.mul_right hf.left
  . exact ContDiff.mul hf.right hg.right

lemma continuous {f : α → ℝ} (hf : IsBump f) : Continuous f :=
  ContDiff.continuous hf.right

lemma differentiable {f : α → ℝ} (hf : IsBump f) : Differentiable ℝ f :=
  ContDiff.differentiable hf.right (by norm_num)

lemma bounded {f : α → ℝ} (hf : IsBump f) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  Continuous.bounded_above_of_compact_support hf.continuous hf.left

lemma comp_neg {f : α → ℝ} (hf : IsBump f) : IsBump (fun (x : α) => f (-x)) := by
  constructor
  . have h_neg {x : α} : -x = (Homeomorph.neg α) x := by simp [Homeomorph.neg]
    simp [h_neg]
    exact HasCompactSupport.comp_homeomorph hf.left _
  . exact ContDiff.comp hf.right contDiff_neg

section Measurable
variable [MeasurableSpace α] [OpensMeasurableSpace α]
variable {f : α → ℝ} (hf : IsBump f)

lemma stronglyMeasurable : StronglyMeasurable f :=
  Continuous.stronglyMeasurable (continuous hf)

lemma aestronglyMeasurable (μ : Measure α := by volume_tac)
    : AEStronglyMeasurable f μ :=
  Continuous.aestronglyMeasurable (continuous hf)

lemma integrable (μ : Measure α := by volume_tac) [IsLocallyFiniteMeasure μ] : Integrable f μ := by
  apply Continuous.integrable_of_hasCompactSupport
  . exact ContDiff.continuous hf.right
  . exact hf.left

lemma memL1 (μ : Measure α := by volume_tac) [IsLocallyFiniteMeasure μ] : Memℒp f 1 μ := by
  simp [Memℒp]
  apply And.intro
  . exact aestronglyMeasurable hf μ
  . simp [snorm, snorm']
    exact (integrable hf μ).right

lemma integrable_mul_continuous {f g : α → ℝ} (hf : IsBump f) (hg : Continuous g)
    (μ : Measure α := by volume_tac) [IsLocallyFiniteMeasure μ]
    : Integrable (f * g) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  . exact Continuous.mul hf.continuous hg
  . apply HasCompactSupport.mul_right hf.left

lemma integrable_continuous_mul {f g : α → ℝ} (hf : Continuous f) (hg : IsBump g)
    (μ : Measure α := by volume_tac) [IsLocallyFiniteMeasure μ]
    : Integrable (f * g) μ := by
  rw [mul_comm]
  apply integrable_mul_continuous <;> assumption

end Measurable
end IsBump


instance Bump.Submodule (α : Type*) [NormedAddCommGroup α] [NormedSpace ℝ α]
    : Submodule ℝ (α → ℝ) where
  carrier := {f | IsBump f}
  add_mem' := by
    intro f g hf hg
    simp [IsBump] at *
    refine And.intro ?_ ?_
    . exact HasCompactSupport.add hf.left hg.left
    . exact ContDiff.add hf.right hg.right
  zero_mem' := by
    simp [IsBump]
    apply And.intro
    . simp [HasCompactSupport, tsupport]
    . exact contDiff_const
  smul_mem' := by
    simp [IsBump]
    intro c f hf_support hf_smooth
    apply And.intro
    . apply @HasCompactSupport.smul_left _ _ _ _ _ _ _ (fun _ => c)
      exact hf_support
    . apply ContDiff.smul contDiff_const hf_smooth


-- Follows example of `Pi.Lp`.
abbrev Bump (α : Type*) [NormedAddCommGroup α] [NormedSpace ℝ α]
  [MeasurableSpace α] [OpensMeasurableSpace α] : Type _ := Bump.Submodule α


namespace Bump
variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
variable [mα : MeasureSpace α] [OpensMeasurableSpace α] [IsLocallyFiniteMeasure mα.volume]

instance funLike : FunLike (Bump α) α (fun _ => ℝ) where
  coe f := f.val
  coe_injective' f g := by simp

-- `Module ℝ` provides addition and scalar multiplication by ℝ.

-- `Module` requires `AddCommMonoid` (`AddCommGroup` extends `AddCommMonoid`).
instance instAddCommGroup : AddCommGroup (Bump α) := Submodule.addCommGroup _
noncomputable instance instModule : Module ℝ (Bump α) := Submodule.module _

-- `NonUnitalCommSemiring` provides (commutative) pointwise multiplication.
-- `NonUnital` and `Semiring` because there is no multiplicative identity (one).

-- Obtain via `Submodule.toNonUnitalSubalgebra`.
def nonUnitalSubalgebra := (Bump.Submodule α).toNonUnitalSubalgebra (by apply IsBump.mul)

noncomputable instance instNonUnitalCommSemiring : NonUnitalCommSemiring (Bump α) :=
  nonUnitalSubalgebra.toNonUnitalCommSemiring

-- No longer need these?
-- @[simp] lemma coeFnAdd (f g : Bump α) : (f + g).val = f.val + g.val := rfl
-- @[simp] lemma coeFnSub (f g : Bump α) : (f - g).val = f.val - g.val := rfl
-- @[simp] lemma coeFnNeg (f : Bump α) : (-f).val = -f.val := rfl
-- @[simp] lemma coeFnMul (f g : Bump α) : (f * g).val = f.val * g.val := rfl
-- @[simp] lemma coeFnSMul (r : ℝ) (f : Bump α) : (r • f).val = r • f.val := rfl

@[simp] lemma add_apply {f g : Bump α} {x : α} : (f + g) x = f x + g x := rfl
@[simp] lemma smul_apply {c : ℝ} {f : Bump α} {x : α} : (c • f) x = c • f x := rfl

lemma hasCompactSupport (f : Bump α) : HasCompactSupport f.val := f.property.left
lemma contDiff (f : Bump α) : ContDiff ℝ ⊤ f.val := f.property.right
lemma continuous (f : Bump α) : Continuous f.val := IsBump.continuous f.property
lemma differentiable {f : Bump α} : Differentiable ℝ f := IsBump.differentiable f.property
lemma stronglyMeasurable (f : Bump α) : StronglyMeasurable f.val :=
  IsBump.stronglyMeasurable f.property
lemma aestronglyMeasurable (f : Bump α) : AEStronglyMeasurable f.val mα.volume :=
  IsBump.aestronglyMeasurable f.property

lemma integrable (f : Bump α) : Integrable f.val := IsBump.integrable f.property
lemma memL1 (f : Bump α) : Memℒp f.val 1 := IsBump.memL1 f.property

def toL1 (f : Bump α) : Lp ℝ 1 mα.volume := (memL1 f).toLp
lemma toL1_def (f : Bump ℝ) : toL1 f = (memL1 f).toLp := rfl

-- No longer need `AddMonoidHom`?
-- Have `AddCommGroup`, `Module`, `NonUnitalCommSemiring` from `Submodule`.
-- noncomputable instance addMonoidHomLp : Bump α →+ Lp ℝ 1 mα.volume where
--   toFun := toL1
--   map_zero' := rfl
--   map_add' _ _ := rfl

end Bump
