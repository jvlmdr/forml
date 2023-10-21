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

lemma DiracSeq.nonneg {b : ℝ} (hb : 0 ≤ b) : ∀ x, 0 ≤ DiracSeq b x := by
  intro x
  simp [DiracSeq]
  refine mul_nonneg ?_ ?_
  . exact div_nonneg hb (sqrt_nonneg π)
  . exact le_of_lt (Real.exp_pos _)

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

theorem tendsto_integral_deltaSeq (φ : ℝ → ℝ) (hφ : IsBump φ)
    : Tendsto (fun (n : ℕ+) => ∫ x, φ x * DiracSeq n x) atTop (nhds (φ 0)) := by
  -- Instead show that `φ x - φ 0` tends to 0.
  suffices : Tendsto (fun (n : ℕ+) => ∫ x, (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
  . sorry

  -- Have that `φ x - φ 0` is bounded since `φ x` is bounded.
  have h_bdd : ∃ M, ∀ x, ‖φ x - φ 0‖ ≤ M
  . rcases hφ.bounded with ⟨C, hC⟩
    exists C + ‖φ 0‖
    intro x
    refine le_trans (norm_sub_le _ _) ?_
    simp
    exact hC x
  -- Product has finite integral (even though `φ x - φ 0` does not have compact support).
  have h_integrable {n : ℕ+} : Integrable (fun x => (φ x - φ 0) * DiracSeq n x)
  . refine Integrable.bdd_mul ?_ ?_ h_bdd
    . refine DiracSeq.integrable ?_
      simp
    . refine Continuous.aestronglyMeasurable ?_
      exact Continuous.sub hφ.continuous continuous_const

  -- Consider the integral on `(a, ∞)`.
  -- This is only true for large enough `N`.
  have hI₂ {a} (ha : 0 < a) : Tendsto (fun (n : ℕ+) => ∫ x in Set.Ioi a, (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
  . -- rcases h_bdd with ⟨M, hM⟩  -- Get explicit bound.
    sorry

  -- Same for integral on `(-∞, a)`.
  have hI₁ {a} (ha : 0 < a) : Tendsto (fun (n : ℕ+) => ∫ x in Set.Iic (-a), (φ x - φ 0) * DiracSeq n x) atTop (nhds 0)
  . sorry

  -- Eliminate the left and right parts in the limit.
  -- The challenge here is that we need `δ`, which depends on `ε`.
  -- Obtain `0 < δ` such that `|x| < δ` implies `|g x| < ε`.
  have hg : Tendsto (fun (x : ℝ) => |φ x - φ 0|) (nhds 0) (nhds 0)
  . sorry
  rw [Metric.tendsto_nhds_nhds] at hg
  simp at hg
  simp [Metric.tendsto_atTop]
  intro ε hε
  -- Use `ε/2` to obtain a `δ` while leaving room for the other limit.
  specialize hg (ε/2) (half_pos hε)
  rcases hg with ⟨δ, ⟨hδ, hδε⟩⟩

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
    sorry  -- Looks provable.

  apply And.intro
  -- Deal with center interval.
  . sorry  -- Looks provable.

  -- Deal with sides.
  . clear hδε hε ε  -- No longer needed.
    simp [integral_union, hδ.le, h_integrable.integrableOn]
    conv => rhs; rw [← add_zero 0]
    exact Tendsto.add (hI₁ hδ) (hI₂ hδ)
