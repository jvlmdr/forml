/-
Proves that `∫ x, φ x * gaussian b x` converges to `phi 0` as `b → ∞`.
Follows: https://proofwiki.org/wiki/Gaussian_Delta_Sequence/Proof_2
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

import ForML.Bump
import ForML.IntegralMeanValue

open Filter MeasureTheory Real


-- Sequence of Gaussian functions that converges to Diract delta; with integral one (for 0 < b).
noncomputable def DiracSeq (b x : ℝ) : ℝ := b / sqrt π * rexp (-(b * x)^2)

-- Can be handy for converting `HPow ℝ ℝ ℝ` to `HPow ℝ ℕ ℝ`.
lemma rpow_to_npow {r : ℝ} (n : ℕ) (h : r = ↑n) (x : ℝ) : x ^ r = HPow.hPow x n := by simp [h]
-- lemma npow_to_rpow {n : ℕ} (x : ℝ) : HPow.hPow x n = x ^ (n : ℝ) := by simp

lemma sqrt_pi_pos : 0 < sqrt π := sqrt_pos_of_pos pi_pos

-- lemma DiracSeq.def {b x : ℝ} : DiracSeq b x = b / sqrt π * rexp (-(b * x)^2) := rfl
lemma DiracSeq.one {x : ℝ} : DiracSeq 1 x = (sqrt π)⁻¹ * rexp (-x^2) := by simp [DiracSeq]
lemma DiracSeq.expNegSq {x : ℝ} : sqrt π * DiracSeq 1 x = rexp (-x^2) := by
  simp [DiracSeq]
  rw [← mul_assoc]
  rw [mul_inv_cancel sqrt_pi_pos.ne']
  simp

lemma DiracSeq.rpow_def {b x : ℝ} : DiracSeq b x = b / sqrt π * rexp (-rpow (b * x) 2) := by simp [DiracSeq]
-- lemma DiracSeq.npow_def {b x : ℝ} : DiracSeq b x = b / sqrt π * rexp (-HPow.hPow (b * x) (2:ℕ)) := by simp [DiracSeq]
lemma DiracSeq.npow_one {x : ℝ} : DiracSeq 1 x = (sqrt π)⁻¹ * rexp (-HPow.hPow x (2:ℕ)) := by simp [DiracSeq]

lemma DiracSeq.continuous {b : ℝ} : Continuous (DiracSeq b) := by
  refine Continuous.mul continuous_const ?_
  refine Continuous.exp ?_
  refine Continuous.neg ?_
  simp [rpow_to_npow 2]
  refine Continuous.pow ?_ 2
  refine Continuous.mul continuous_const continuous_id

lemma DiracSeq.nonneg {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : 0 ≤ DiracSeq b x := by
  simp [DiracSeq]
  refine mul_nonneg ?_ ?_
  . exact div_nonneg hb (sqrt_nonneg π)
  . exact le_of_lt (exp_pos _)

lemma DiracSeq.nonneg_nat {b : ℕ} (x : ℝ) : 0 ≤ DiracSeq b x :=
  DiracSeq.nonneg (Nat.cast_nonneg _) x

lemma DiracSeq.integral {b : ℝ} (hb : 0 < b) : ∫ x, DiracSeq b x = 1 := by
  simp [DiracSeq]
  simp [integral_mul_left]
  simp [mul_pow]
  have h := integral_gaussian
  simp at h
  simp [h]
  clear h
  rw [sqrt_div pi_pos.le]
  rw [sqrt_sq hb.le]
  rw [div_mul_div_comm]
  rw [mul_comm]
  rw [div_self]
  apply ne_of_gt
  exact mul_pos sqrt_pi_pos hb

lemma DiracSeq.integrable {b : ℝ} (hb : 0 < b) : Integrable (fun x => DiracSeq b x) := by
  exact integrable_of_integral_eq_one (DiracSeq.integral hb)

lemma integral_symm {f : ℝ → ℝ} (hf : Integrable f) (h_symm : ∀ x, f (-x) = f x) :
    2 * ∫ x in Set.Ioi 0, f x = ∫ x, f x := by
  -- Split the integral in two.
  have hs : MeasurableSet (Set.Ioi 0 : Set ℝ) := measurableSet_Ioi
  rw [← integral_add_compl hs hf]
  simp
  simp only [@two_mul ℝ]  -- Sometimes slow without `only`
  simp
  have h0 : (0 : ℝ) = -0 := by norm_num
  rw [h0]
  rw [← integral_comp_neg_Ioi]
  simp
  congr
  ext x
  rw [h_symm]

lemma DiracSeq.symm (b x : ℝ) : DiracSeq b (-x) = DiracSeq b x := by simp [DiracSeq]

lemma DiracSeq.eq_comp_mul (b x : ℝ) : DiracSeq b x = b * DiracSeq 1 (b * x) := by
  simp [DiracSeq]
  rw [← mul_assoc]
  rfl

lemma DiracSeq.integral_Ioi {b : ℝ} (hb : 0 < b) : ∫ x in Set.Ioi 0, DiracSeq b x = 1/2 := by
  rw [eq_div_iff (by norm_num)]
  rw [mul_comm]
  rw [integral_symm (DiracSeq.integrable hb) (DiracSeq.symm b)]
  exact DiracSeq.integral hb


lemma DiracSeq.intervalIntegral_comp_mul (s a b : ℝ) -- (hs : 0 < s) (ha : 0 < a) (hb : a ≤ b)
    : ∫ x in a..b, DiracSeq s x =
      ∫ x in s*a..s*b, DiracSeq 1 x := by
  simp [DiracSeq]
  rw [div_eq_inv_mul]
  rw [mul_assoc]
  rw [← intervalIntegral.mul_integral_comp_mul_left]

lemma DiracSeq.setIntegral_comp_mul {k : ℝ} (hk : 0 < k) {s : Set ℝ} (hs : MeasurableSet s)
    : ∫ x in s, DiracSeq k x =
      ∫ x in (fun u => k * u) '' s, DiracSeq 1 x := by
  rw [@integral_image_eq_integral_abs_deriv_smul _ _ _ _ _ (fun _ => k : ℝ → ℝ) _ hs]
  rotate_left
  . intro x _
    simp [mul_comm k]
    exact HasDerivAt.hasDerivWithinAt (hasDerivAt_mul_const k)
  . apply Function.Injective.injOn
    simp [Function.Injective]
    intro u v
    intro h
    cases h with
    | inl h => exact h
    | inr h => exfalso; exact hk.ne' h
  simp
  rw [abs_of_pos hk]
  simp [DiracSeq]
  simp [← mul_assoc]
  rfl


/- Prove that action of Gaussian on bump approaches Dirac delta. -/

-- Couldn't find a convenient function like this in mathlib.
lemma tendsto_zero_of_forall_abs_le {α : Type*} [Nonempty α] [SemilatticeSup α] {f g : α → ℝ}
    (hfg : ∀ x, |f x| ≤ g x) (h : Tendsto g atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  simp [Metric.tendsto_atTop]
  intro ε hε
  simp [Metric.tendsto_atTop] at h
  specialize h ε hε
  rcases h with ⟨a, ha⟩
  exists a
  intro x hx
  exact lt_of_le_of_lt (hfg x) (lt_of_abs_lt (ha x hx))



-- Coercion from ℕ+ to ℕ.
lemma tendsto_coe_pnat_atTop : Tendsto (fun (n : ℕ+) => (n : ℕ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro a
  exists Nat.toPNat' a
  intro x hx
  exact Nat.le_of_pred_lt hx

-- Coercion from ℕ+ to ℝ.
lemma tendsto_coe_coe_pnat_atTop : Tendsto (fun (n : ℕ+) => (n : ℝ)) atTop atTop :=
  Tendsto.comp tendsto_nat_cast_atTop_atTop tendsto_coe_pnat_atTop


lemma DiracSeq.tendsto_setIntegral_Ioi_zero {a : ℝ} (ha : 0 < a)
    : Tendsto (fun (n : ℕ+) => ∫ x in Set.Ioi a, DiracSeq n x) atTop (nhds 0) := by
  -- Rewrite integral as difference of integrals.
  have {n : ℕ+} : ∫ (x : ℝ) in Set.Ioi a, DiracSeq n x
    = (∫ (x : ℝ) in Set.Ioi 0, DiracSeq n x) - (∫ x in (0:ℝ)..a, DiracSeq n x)
  . rw [eq_sub_iff_add_eq']
    simp [intervalIntegral.integral_of_le ha.le]
    rw [← integral_union]
    . simp [Set.Ioc_union_Ioi_eq_Ioi ha.le]
    . simp [disjoint_iff]
    . exact measurableSet_Ioi
    . apply Integrable.integrableOn
      exact DiracSeq.integrable (by simp)
    . apply Integrable.integrableOn
      exact DiracSeq.integrable (by simp)
  simp [this]
  clear this
  conv => rhs; rw [← sub_self (1/2)]
  apply Tendsto.sub
  . -- Use existing result for integral on [0, ∞).
    simp [DiracSeq.integral_Ioi]
  . -- Move scaling from integrand to interval.
    conv => arg 1; intro b; arg 1; intro x; rw [DiracSeq.eq_comp_mul]
    simp
    simp [intervalIntegral.integral_comp_mul_left]
    -- Replace (1/2) in rhs with integral.
    rw [inv_eq_one_div, ← DiracSeq.integral_Ioi zero_lt_one]
    -- Integral on [0, c) tends to integral on [0, ∞) as c tends to ∞.
    apply intervalIntegral_tendsto_integral_Ioi
    . apply Integrable.integrableOn
      exact DiracSeq.integrable zero_lt_one
    . exact Tendsto.atTop_mul_const ha tendsto_coe_coe_pnat_atTop


lemma bounded_bump_sub_const {φ : ℝ → ℝ} (hφ : IsBump φ) (y : ℝ) : ∃ M, ∀ x, ‖φ x - y‖ ≤ M := by
  rcases hφ.bounded with ⟨C, hC⟩
  exists C + ‖y‖
  intro x
  refine le_trans (norm_sub_le _ _) ?_
  simp
  exact hC x

lemma integrable_bump_sub_const_mul_diracSeq {φ : ℝ → ℝ} (hφ : IsBump φ) (y : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => (φ x - y) * DiracSeq b x) := by
  refine Integrable.bdd_mul ?_ ?_ ?_
  . exact DiracSeq.integrable hb
  . refine Continuous.aestronglyMeasurable ?_
    exact Continuous.sub hφ.continuous continuous_const
  . exact bounded_bump_sub_const hφ y

lemma tendsto_integral_Ioi_bump_sub_const_mul {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsBump φ) (y : ℝ) :
    Tendsto (fun (n : ℕ+) => ∫ x in Set.Ioi a, (φ x - y) * DiracSeq n x) atTop (nhds 0) := by
  rcases bounded_bump_sub_const hφ y with ⟨M, hM⟩  -- Get explicit bound.
  suffices (n : ℕ+) : |∫ x in Set.Ioi a, (φ x - y) * DiracSeq n x| ≤ M * ∫ x in Set.Ioi a, DiracSeq n x
  . apply tendsto_zero_of_forall_abs_le this
    conv => arg 3; rw [← mul_zero M]
    exact Tendsto.const_mul _ (DiracSeq.tendsto_setIntegral_Ioi_zero ha)
  rw [← norm_eq_abs]
  rw [← integral_mul_left]
  refine norm_integral_le_of_norm_le ?_ ?_
  . refine Integrable.integrableOn ?_
    exact Integrable.const_mul (DiracSeq.integrable (by simp)) _
  . refine Filter.eventually_of_forall ?_
    intro x
    simp
    rw [abs_of_nonneg (DiracSeq.nonneg_nat _)]
    refine mul_le_mul_of_nonneg_right (hM x) (DiracSeq.nonneg_nat x)

lemma tendsto_integral_Iic_bump_sub_const_mul {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsBump φ) (y : ℝ) :
    Tendsto (fun (n : ℕ+) => ∫ x in Set.Iic (-a), (φ x - y) * DiracSeq n x) atTop (nhds 0) := by
  simp only [← integral_comp_neg_Ioi]
  simp only [DiracSeq.symm]
  exact tendsto_integral_Ioi_bump_sub_const_mul ha (IsBump.comp_neg hφ) y

lemma integral_eq_add_Iic_Ioc_Ioi {f : ℝ → ℝ} (hf : Integrable f) {a b : ℝ} (hab : a ≤ b) :
    ∫ x, f x = (∫ x in Set.Iic a, f x) + (∫ x in Set.Ioc a b, f x) + (∫ x in Set.Ioi b, f x) := by
  simp [← integral_union, hab, Integrable.integrableOn, hf]


theorem tendsto_integral_bump_mul_deltaSeq (φ : ℝ → ℝ) (hφ : IsBump φ)
    : Tendsto (fun (n : ℕ+) => ∫ x, φ x * DiracSeq n x) atTop (nhds (φ 0)) := by
  -- Instead show that `φ x - φ 0` tends to 0.
  suffices h_tendsto : Tendsto (fun (n : ℕ+) => ∫ x, (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
  . -- No re-write version of `Tendsto.sub_const`?
    conv => arg 1; intro n; rw [← sub_add_cancel (∫ x, _) (φ 0)]
    conv => arg 3; rw [← sub_add_cancel (φ 0) (φ 0)]
    refine Tendsto.add_const _ ?_
    simp
    refine Filter.Tendsto.congr ?_ h_tendsto
    intro n
    simp [sub_mul]
    rw [integral_sub]
    rotate_left
    . exact IsBump.integrable_mul_continuous hφ DiracSeq.continuous
    . refine Integrable.const_mul ?_ _
      exact DiracSeq.integrable (by simp)
    simp [integral_mul_left, DiracSeq.integral]

  -- Product has finite integral (even though `φ x - φ 0` does not have compact support).
  have h_integrable {n : ℕ+} := @integrable_bump_sub_const_mul_diracSeq _ hφ (φ 0) n (by simp)

  -- Eliminate the left and right parts in the limit.
  -- The challenge here is that we need `δ`, which depends on `ε`.
  -- Obtain `0 < δ` such that `|x| < δ` implies `|g x| < ε`.
  have hδ : Tendsto (fun (x : ℝ) => |φ x - φ 0|) (nhds 0) (nhds 0)
  . refine Continuous.tendsto' ?_ _ _ (by simp)
    refine Continuous.abs ?_
    exact Continuous.sub hφ.continuous continuous_const
  rw [Metric.tendsto_nhds_nhds] at hδ
  simp at hδ
  simp [Metric.tendsto_atTop]
  intro ε hε
  -- Use `ε/2` to obtain a `δ` while leaving room for the other limit.
  specialize hδ (ε/2) (half_pos hε)
  rcases hδ with ⟨δ, ⟨hδ, hδε⟩⟩

  -- Separate center from left and right using `δ`.
  -- Use specific `ε` for center and arbitrary `ε` for sides.
  suffices : (∃ N, ∀ (n : ℕ+), N ≤ n → |∫ x in Set.Ioc (-δ) δ, (φ x - φ 0) * DiracSeq (↑↑n) x| < ε/2) ∧
      Tendsto (fun (n : ℕ+) => ∫ x in Set.Iic (-δ) ∪ Set.Ioi δ, (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
  . rcases this with ⟨h_center, h_sides⟩
    simp [Metric.tendsto_atTop] at h_sides
    specialize h_sides (ε/2) (half_pos hε)
    rcases h_center with ⟨N_center, h_center⟩
    rcases h_sides with ⟨N_sides, h_sides⟩
    -- Take the max of the two filters.
    exists max N_center N_sides
    intro n hn
    specialize h_center n (le_of_max_le_left hn)
    specialize h_sides n (le_of_max_le_right hn)
    rw [← add_halves' ε]
    refine lt_of_le_of_lt ?_ (add_lt_add h_center h_sides)
    clear h_center h_sides hn N_center N_sides  -- For readability.
    have hδδ : -δ ≤ δ := by simp [hδ.le]
    simp [integral_eq_add_Iic_Ioc_Ioi h_integrable hδδ]
    conv =>
      lhs; arg 1
      conv => lhs; rw [add_comm]
      rw [add_assoc]
    refine le_trans (abs_add _ _) ?_
    simp
    refine le_of_eq ?_
    congr
    simp [integral_union, Set.Iic_disjoint_Ioi hδδ, h_integrable.integrableOn]

  apply And.intro
  -- Deal with center interval.
  . sorry  -- Looks provable.

  -- Deal with sides.
  . -- Consider the integral on `(a, ∞)`.
    have hI₂ {a} (ha : 0 < a) : Tendsto (fun (n : ℕ+) => ∫ x in Set.Ioi a, (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
    . exact tendsto_integral_Ioi_bump_sub_const_mul ha hφ (φ 0)
    -- Same for integral on `(-∞, a)`.
    have hI₁ {a} (ha : 0 < a) : Tendsto (fun (n : ℕ+) => ∫ x in Set.Iic (-a), (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
    . exact tendsto_integral_Iic_bump_sub_const_mul ha hφ (φ 0)
    clear hδε hε ε  -- No longer needed.
    simp [integral_union, hδ.le, h_integrable.integrableOn]
    conv => rhs; rw [← add_zero 0]
    exact Tendsto.add (hI₁ hδ) (hI₂ hδ)
