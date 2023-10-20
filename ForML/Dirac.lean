/-
Proves that `∫ x, φ x * gaussian b x` converges to `phi 0` as `b → ∞`.
Follows: https://proofwiki.org/wiki/Gaussian_Delta_Sequence/Proof_1
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


lemma integralIic_add_intervalIntegral {f : ℝ → ℝ} (hf : Integrable f) (a b : ℝ)
    : ∫ x in Set.Iic b, f x = (∫ x in Set.Iic a, f x) + ∫ x in a..b, f x := by
  rw [← @sub_eq_iff_eq_add']
  apply intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn

-- Need `IsCountablyGenerated` for `intervalIntegral_tendsto_integral_Ioi`!
lemma DiracSeq.tendsto_intervalIntegral_zero {a b : ℝ} (ha : 0 < a) (hb : a < b)
    : Tendsto (fun (s : ℕ) => ∫ x in a..b, DiracSeq ↑s x) atTop (nhds 0) := by
  simp [DiracSeq.intervalIntegral_comp_mul]
  have hi := integrable_exp_neg_mul_sq zero_lt_one
  simp at hi
  simp [DiracSeq.one]
  simp [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  conv =>
    arg 1; intro s
    conv => arg 2; arg 1; rw [integralIic_add_intervalIntegral hi 0 _]
    conv => arg 2; arg 2; rw [integralIic_add_intervalIntegral hi 0 _]
  simp
  simp [mul_sub]
  simp only [← intervalIntegral.integral_const_mul]
  simp only [← DiracSeq.npow_one]
  conv => rhs; rw [← sub_self (1/2 : ℝ)]
  rw [← DiracSeq.integral_Ioi zero_lt_one]
  apply Tendsto.sub
  . apply intervalIntegral_tendsto_integral_Ioi
    . exact (DiracSeq.integrable zero_lt_one).integrableOn
    . rw [tendsto_mul_const_atTop_of_pos (ha.trans hb)]
      exact tendsto_nat_cast_atTop_atTop
  . apply intervalIntegral_tendsto_integral_Ioi
    . exact (DiracSeq.integrable zero_lt_one).integrableOn
    . rw [tendsto_mul_const_atTop_of_pos ha]
      exact tendsto_nat_cast_atTop_atTop

-- lemma DiracSeq.tendsto_setIntegral_zero {s : Set ℝ} (hs_meas : MeasurableSet s)
--     (hs_pos : ∀ x, x ∈ s → 0 < x)
--     : Tendsto (fun (n : ℕ) => ∫ x in s, DiracSeq n.succ x) atTop (nhds 0) := by
--   simp
--   conv => arg 1; intro n; rw [DiracSeq.setIntegral_comp_mul (Nat.cast_add_one_pos n) hs_meas]

-- TODO: mathlib probably contains something to achieve this?
-- The closest is `Real.tendsto_comp_exp_atTop`?
-- Under the hood, this uses `OrderIso`. There are a few defined for ℕ.
-- TODO: Can probably formulate a more general version using `StrictMonoOn`?
-- `tendsto_iff_tendsto_subseq_of_monotone` requires `Monotone f` (not `Monotone φ`).
lemma tendsto_atTop_of_tendsto_atTop_comp_max
    {α : Type*} {β : Type*} [Nonempty α] [LinearOrder α] [TopologicalSpace β]
    {f : α → β} (x₀ : α) {y : β}
    (h : Tendsto (fun (x : α) => f (max x₀ x)) atTop (nhds y))
    : Tendsto f atTop (nhds y) := by
  simp [tendsto_def]
  simp [tendsto_def] at h
  intro s hs
  specialize h s hs
  rcases h with ⟨a, ha⟩
  exists max x₀ a
  intro b hb
  simp at hb
  have hb' : max x₀ b = b
  . exact max_eq_right hb.left
  specialize ha b
  simp [hb'] at ha
  exact ha hb.right

-- lemma forall_le_mem_iff {α β : Type*} {f : α → β} {s : Set β} {a : α}
--     [Nonempty α] [LinearOrder α] [NoMaxOrder α] [PseudoMetricSpace β]
--     : (∀ (x : α), a ≤ x → f x ∈ s) ↔ Set.Ici a ⊆ f ⁻¹' s := by
--   conv => lhs; intro x; rw [← Set.mem_Ici]

-- lemma tendsto_atTop_of_tendsto_atTop_comp_strictMono
--     {α : Type*} {β : Type*} [Nonempty α] [LinearOrder α] [PseudoMetricSpace β]
--     {f : α → β} {y : β} {φ : α → α}
--     (hφ : Filter.map φ atTop = atTop)  -- How to obtain this?
--     (hf : Tendsto (f ∘ φ) atTop (nhds y))
--     : Tendsto f atTop (nhds y) := by
--   -- Follow `Real.tendsto_comp_exp_atTop`.
--   rw [← tendsto_map'_iff] at hf
--   rw [hφ] at hf
--   exact hf

-- -- Should be some way to generalize this?
-- lemma tendsto_atTop_of_tendsto_atTop_comp_strictMono
--     {α : Type*} {β : Type*} [Nonempty α] [LinearOrder α] [PseudoMetricSpace β]
--     {f : α → β} {y : β} {φ : α → α}
--     (hφ : Filter.map φ atTop = atTop)  -- How to obtain this?
--     (hf : Tendsto (f ∘ φ) atTop (nhds y))
--     : Tendsto f atTop (nhds y) := by
--   -- Follow `Real.tendsto_comp_exp_atTop`.
--   rw [← tendsto_map'_iff] at hf
--   rw [hφ] at hf
--   exact hf

-- example {α : Type*}
--     [Nonempty α] [LinearOrder α] [TopologicalSpace β] {u : α}
--     : Filter.map (fun (x : α) => max u x) atTop = atTop := by
--   ext s
--   simp
--   refine exists_congr ?_
--   intro a
--   refine ball_congr ?_
--   intro b hb
--   -- Not true...
--   sorry

-- example
--     {α : Type*} {β : Type*} [Nonempty α] [LinearOrder α] [PseudoMetricSpace β]
--     {f : α → β} {u : α} {y : β} {φ φ' : α → α}
--     (hφ : Set.LeftInvOn φ φ' (Set.Ici u))
--     (hφ_surj : Function.Surjective φ)
--     (hφ_mono : Monotone φ)
--     (hf : Tendsto (f ∘ φ) atTop (nhds y))
--     : Tendsto f atTop (nhds y) := by
--   simp [tendsto_def]
--   simp [tendsto_def] at hf
--   intro s hs
--   specialize hf s hs
--   rcases hf with ⟨a, ha⟩
--   -- specialize ha (φ' a)
--   existsi (φ a)
--   intro b hb
--   specialize ha (φ' b)
--   -- rw [Function.Surjective.forall hφ_surj]
--   -- intro x hx
--   -- apply ha
--   sorry


-- Can convert to countably generated if required.
-- `tendsto_iff_tendsto_subseq_of_monotone` requires `Monotone f`.
lemma tendsto_atTop_nat_of_tendsto_atTop_real {β : Type*} [TopologicalSpace β]
    {f : ℝ → β} {l : Filter β} (h : Tendsto f atTop l)
    : Tendsto (fun (n : ℕ) => f n) atTop l := by
  simp [tendsto_def]
  simp [tendsto_def] at h
  intro s hs
  specialize h s hs
  rcases h with ⟨a, ha⟩
  exists ⌈a⌉₊
  intro b hb
  simp at hb
  exact ha b hb

-- Can convert to countably generated if required.
-- `tendsto_iff_tendsto_subseq_of_monotone` requires `Monotone f`.
lemma tendsto_atTop_pnat_of_tendsto_atTop_real {β : Type*} [TopologicalSpace β]
    {f : ℝ → β} {l : Filter β} (h : Tendsto f atTop l)
    : Tendsto (fun (n : ℕ+) => f n) atTop l := by
  simp [tendsto_def]
  simp [tendsto_def] at h
  intro s hs
  specialize h s hs
  rcases h with ⟨a, ha⟩
  exists ⟨⌈max 1 a⌉₊, by simp⟩
  intro b hb
  simp [← PNat.coe_le_coe] at hb
  exact ha b hb.right


-- -- Useful to eliminate a constant in `Tendsto .. (nhds zero)`.
-- lemma tendsto_const_mul_atTop_nhds_zero
--     {α : Type*} {β : Type*} [Nonempty α] [LinearOrder α] [TopologicalSpace β]
--     [NonUnitalNonAssocSemiring β] [ContinuousMul β]
--     {f : α → β} {c : β}
--     (h : Tendsto f atTop (nhds 0))
--     : Tendsto (fun x => c * f x) atTop (nhds 0) := by
--   have h := Tendsto.const_mul c h
--   simp at h
--   exact h


lemma DiracSeq.tendsto_setIntegral_Ioi_zero {a : ℝ} (ha : 0 < a)
    : Tendsto (fun (b : ℝ) => ∫ x in Set.Ioi a, DiracSeq b x) atTop (nhds 0) := by
  -- Apply exp to restrict to positive reals.
  rw [← Real.tendsto_comp_exp_atTop]
  -- Rewrite integral as difference of integrals.
  have {b : ℝ} : ∫ (x : ℝ) in Set.Ioi a, DiracSeq (rexp b) x
    = (∫ (x : ℝ) in Set.Ioi 0, DiracSeq (rexp b) x) - (∫ x in (0:ℝ)..a, DiracSeq (rexp b) x)
  . rw [eq_sub_iff_add_eq']
    simp [intervalIntegral.integral_of_le ha.le]
    rw [← integral_union]
    . simp [Set.Ioc_union_Ioi_eq_Ioi ha.le]
    . simp [disjoint_iff]
    . exact measurableSet_Ioi
    . apply Integrable.integrableOn
      exact DiracSeq.integrable (Real.exp_pos _)
    . apply Integrable.integrableOn
      exact DiracSeq.integrable (Real.exp_pos _)
  simp [this]
  clear this
  conv => rhs; rw [← sub_self (1/2)]
  apply Tendsto.sub
  . -- Use existing result for integral on [0, ∞).
    simp [DiracSeq.integral_Ioi (Real.exp_pos _)]
  . -- Move scaling from integrand to interval.
    conv => arg 1; intro b; arg 1; intro x; rw [DiracSeq.eq_comp_mul]
    simp
    simp [intervalIntegral.integral_comp_mul_left, Real.exp_ne_zero]
    -- Replace (1/2) in rhs with integral.
    rw [inv_eq_one_div, ← DiracSeq.integral_Ioi zero_lt_one]
    -- Integral on [0, c) tends to integral on [0, ∞) as c tends to ∞.
    apply intervalIntegral_tendsto_integral_Ioi
    . apply Integrable.integrableOn
      exact DiracSeq.integrable zero_lt_one
    . exact Tendsto.atTop_mul_const ha tendsto_exp_atTop

lemma DiracSeq.tendsto_intervalIntegral_one {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    : Tendsto (fun (b : ℝ) => ∫ x in a..b, DiracSeq b x) atTop (nhds 1) := by
  -- Should be easy to prove if we need it.
  sorry

lemma DiracSeq.tendsto_setIntegral_Ioi_bump_mul_zero {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsBump φ)
    : Tendsto (fun (b : ℝ) => ∫ x in Set.Ioi a, φ x * DiracSeq b x) atTop (nhds 0) := by
  -- Apply mean value theorem.
  -- How to apply it within limit?
  sorry


-- -- -- Causing timeout...
-- -- lemma DiracSeq.tendsto_setIntegral_Ioi_iff {a : ℝ} (ha : 0 < a)
-- --     : Tendsto (fun b => ∫ x in Set.Ioi a, DiracSeq b x) atTop (nhds y)
-- --       ↔ Tendsto (fun b => ∫ x in Set.Ioi (b*a), DiracSeq 1 x) atTop (nhds y) := by
-- --   conv => lhs; arg 1; intro n; arg 2; intro x; rw [DiracSeq.eq_comp_mul]
-- --   -- simp [integral_mul_left]
-- --   -- -- Restrict limit to positive part.
-- --   -- rw [← Real.tendsto_comp_exp_atTop]
-- --   -- simp [integral_comp_mul_left_Ioi, Real.exp_pos]
-- --   -- simp [← mul_assoc, abs_inv, Real.exp_ne_zero]
-- --   -- rw [@Real.tendsto_comp_exp_atTop _ _ (fun b => ∫ (x : ℝ) in Set.Ioi (b * a), DiracSeq 1 x)]
-- --   -- -- This seems good; integrand is independent of limit parameter.
-- --   -- -- How to proceed? Function is integrable;
-- --   -- -- integral on [b, ∞) is integral on (-∞, ∞) minus integral on (-∞, b].
-- --   -- -- These tend to the same thing. That should do it.
-- --   -- -- Is there no easier way to do it?
-- --   -- -- conv => lhs; arg 2; intro x; rw [DiracSeq.eq_comp_mul]
-- --   sorry

-- lemma DiracSeq.setIntegral_Ioi_eq {a : ℝ} (ha : 0 < a)
--     : ∫ x in Set.Ioi a, DiracSeq b x = b * ∫ x in Set.Ioi a, DiracSeq 1 (b * x) := by
--   conv => lhs; arg 2; intro x; rw [DiracSeq.eq_comp_mul]
--   simp [integral_mul_left]

-- lemma DiracSeq.tendsto_setIntegral_Ioi_zero {a : ℝ} (ha : 0 < a)
--     : Tendsto (fun (b : ℝ) => ∫ x in Set.Ioi a, DiracSeq b x) atTop (nhds 0) := by
--   conv => arg 1; intro n; arg 2; intro x; rw [DiracSeq.eq_comp_mul]
--   simp [integral_mul_left]
--   -- Restrict limit to positive part.
--   rw [← Real.tendsto_comp_exp_atTop]
--   simp [integral_comp_mul_left_Ioi, Real.exp_pos]
--   simp [← mul_assoc, abs_inv, Real.exp_ne_zero]
--   rw [@Real.tendsto_comp_exp_atTop _ _ (fun b => ∫ (x : ℝ) in Set.Ioi (b * a), DiracSeq 1 x)]
--   -- This seems good; integrand is independent of limit parameter.
--   -- How to proceed? Function is integrable;
--   -- integral on [b, ∞) is integral on (-∞, ∞) minus integral on (-∞, b].
--   -- These tend to the same thing. That should do it.
--   -- Is there no easier way to do it?
--   have {b} : ∫ (x : ℝ) in Set.Ioi (b*a), DiracSeq 1 x =
--     (∫ (x : ℝ) in Set.Ioi 0, DiracSeq 1 x) - (∫ (x : ℝ) in (0:ℝ)..(b*a), DiracSeq 1 x)
--   . sorry
--   simp [this]
--   clear this
  

--   simp [DiracSeq]
--   simp [integral_mul_left]


--   -- apply tendsto_const_mul_atTop_nhds_zero
--   -- Restrict limit to positive part.
--   -- apply tendsto_atTop_of_tendsto_atTop_comp_max 1
--   simp [integral_comp_mul_left_Ioi]
--   -- TODO: Easier way to cancel scalar?
--   simp [← mul_assoc, abs_inv]
  

--   -- have {b : ℝ} (hb : b) : ∫ x in Set.Ioi a, DiracSeq b x = |b⁻¹| * ∫ x in Set.Ioi (b * a), DiracSeq 1 x
--   -- . rw [← integral_comp_mul_left_Ioi (DiracSeq 1) a ha]


--   conv => arg 1; intro n; arg 2; intro x; rw [DiracSeq.eq_comp_mul]
--   simp [integral_mul_left]
--   -- conv => arg 1; intro n; rw [integral_comp_mul_left_Ioi _ _ (Nat.cast_add_one_pos n)]
--   -- Need to provide proof that 
--   simp [integral_comp_mul_left_Ioi, Nat.cast_add_one_pos]

  
--   -- simp [DiracSeq.intervalIntegral_comp_mul]
--   have hi := integrable_exp_neg_mul_sq zero_lt_one
--   simp at hi
--   simp [DiracSeq.one]
--   simp [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
--   conv =>
--     arg 1; intro s
--     conv => arg 2; arg 1; rw [integralIic_add_intervalIntegral hi 0 _]
--     conv => arg 2; arg 2; rw [integralIic_add_intervalIntegral hi 0 _]
--   simp
--   simp [mul_sub]
--   simp only [← intervalIntegral.integral_const_mul]
--   simp only [← DiracSeq.npow_one]
--   conv => rhs; rw [← sub_self (1/2 : ℝ)]
--   rw [← DiracSeq.integral_Ioi 1 zero_lt_one]
--   apply Tendsto.sub
--   . apply intervalIntegral_tendsto_integral_Ioi
--     . exact (DiracSeq.integrable zero_lt_one).integrableOn
--     . rw [tendsto_mul_const_atTop_of_pos (ha.trans hb)]
--       exact tendsto_nat_cast_atTop_atTop
--   . apply intervalIntegral_tendsto_integral_Ioi
--     . exact (DiracSeq.integrable zero_lt_one).integrableOn
--     . rw [tendsto_mul_const_atTop_of_pos ha]
--       exact tendsto_nat_cast_atTop_atTop

--   -- simp [Measure.integral_comp_mul_left (fun x => ↑n / sqrt π * rexp (-x^2))]
--   -- simp [integral_mul_left]
--   sorry


--   -- have hi := integrable_exp_neg_mul_sq zero_lt_one
--   -- simp at hi

--   -- simp [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
--   -- conv =>
--   --   arg 1; intro s
--   --   conv => arg 2; arg 1; rw [integralIic_add_intervalIntegral hi 0 _]
--   --   conv => arg 2; arg 2; rw [integralIic_add_intervalIntegral hi 0 _]
--   -- simp
--   -- simp [mul_sub]
--   -- simp only [← intervalIntegral.integral_const_mul]
--   -- simp only [← DiracSeq.npow_one]
--   -- conv => rhs; rw [← sub_self (1/2 : ℝ)]
--   -- rw [← DiracSeq.integral_Ioi 1 zero_lt_one]
--   -- apply Tendsto.sub
--   -- . apply intervalIntegral_tendsto_integral_Ioi
--   --   . exact (DiracSeq.integrable zero_lt_one).integrableOn
--   --   . rw [tendsto_mul_const_atTop_of_pos (ha.trans hb)]
--   --     exact tendsto_nat_cast_atTop_atTop
--   -- . apply intervalIntegral_tendsto_integral_Ioi
--   --   . exact (DiracSeq.integrable zero_lt_one).integrableOn
--   --   . rw [tendsto_mul_const_atTop_of_pos ha]
--   --     exact tendsto_nat_cast_atTop_atTop
  
--   -- sorry


lemma DiracSeq.tendsto_intervalIntegral_zero_neg (a b : ℝ) (ha : a < b) (hb : b < 0)
    : Tendsto (fun (s : ℕ) => ∫ x in a..b, DiracSeq ↑s x) atTop (nhds 0) := by
  conv =>
    arg 1; intro k
    conv => arg 1; intro x; arg 2; rw [← neg_neg x]
    rw [intervalIntegral.integral_comp_neg (fun x => DiracSeq (↑k) (-x))]
  simp [DiracSeq.symm]
  apply tendsto_intervalIntegral_zero <;> linarith

lemma integrable_bump_mul_diracSeq {φ : ℝ → ℝ} (hφ : IsBump φ) {b : ℝ}
    : Integrable (fun x => φ x * DiracSeq b x) := by
  exact IsBump.integrable_mul_continuous hφ DiracSeq.continuous


lemma DiracSeq.tendsto_integral_Ioi_bump_mul_zero {φ : ℝ → ℝ} (hφ : IsBump φ) {ε : ℝ} (hε : 0 < ε)
    : Tendsto (fun (n : ℕ+) => ∫ x in Set.Ioi ε, φ x * DiracSeq n x) atTop (nhds 0) := by
  -- simp [← integral_Ici_eq_integral_Ioi]
  -- have hξn (n : ℕ+) := @exists_mul_eq_setInterval_Ici (ε : ℝ) φ (DiracSeq (n : ℝ)) volume ?_ ?_ ?_ ?_
  -- rotate_left
  -- . exact Continuous.continuousOn hφ.continuous
  -- . exact Integrable.integrableOn (DiracSeq.integrable (by simp))
  -- . apply eventually_of_forall; simp
  --   apply DiracSeq.nonneg; simp
  -- . apply Integrable.integrableOn
  --   apply Continuous.integrable_of_hasCompactSupport
  --   . exact Continuous.mul hφ.continuous (DiracSeq.continuous _)
  --   . exact HasCompactSupport.mul_right hφ.left
  -- simp [integral_Ici_eq_integral_Ioi] at hξn
  -- simp [integral_Ici_eq_integral_Ioi]

  -- Didn't even use mean value theorem?!
  have hz := DiracSeq.tendsto_setIntegral_Ioi_zero hε
  replace hz := tendsto_atTop_pnat_of_tendsto_atTop_real hz

  -- Can't set integral to zero in goal; only true in limit.
  -- Use boundedness of bump function to show that it is close to zero.
  rw [Metric.tendsto_atTop]
  intro r hr
  simp at hr ⊢
  rcases hφ.bounded with ⟨C, hC⟩
  simp at hC
  rw [Metric.tendsto_atTop] at hz
  simp at hz
  have hC_nonneg : 0 ≤ C
  . exact le_trans (by simp) (hC 0)
  cases eq_or_gt_of_le hC_nonneg with
  | inl hC_zero =>
    simp [hC_zero] at hC
    simp [hC, hr]
  | inr hC_pos =>
    specialize hz (r / C)
    specialize hz (div_pos hr hC_pos)
    rcases hz with ⟨N, hN⟩
    exists N
    intro n hn
    specialize hN n hn
    rw [lt_div_iff hC_pos] at hN
    apply lt_of_le_of_lt ?_ hN
    -- Should be able to show this?
    rw [mul_comm _ C]
    -- TODO: Make a lemma from here?
    rw [← norm_eq_abs]
    rw [abs_of_nonneg]; swap
    . apply integral_nonneg
      intro x; simp
      apply DiracSeq.nonneg (by simp)
    rw [← integral_mul_left]
    apply norm_integral_le_of_norm_le
    . refine Integrable.integrableOn (Integrable.const_mul ?_ _)
      exact DiracSeq.integrable (by simp)
    apply eventually_of_forall
    intro x
    simp
    rw [abs_of_nonneg (DiracSeq.nonneg (by simp) _)]
    exact mul_le_mul_of_nonneg_right (hC x) (DiracSeq.nonneg (by simp) x)


lemma elim_exists_imp_and_left {α : Type*} {p q r : α → Prop}
    (h_forall : ∀ a, r a → p a → q a)
    (h_exists : ∃ a, r a ∧ p a)
    : ∃ a, r a ∧ q a := by
  rcases h_exists with ⟨a, ⟨hra, hpa⟩⟩
  exists a
  exact ⟨hra, h_forall a hra hpa⟩


lemma DiracSeq.exists_tendsto_integral_Icc_bump_mul {φ : ℝ → ℝ} (hφ : IsBump φ) (ε : ℝ) (hε : 0 < ε) {y : ℝ}
    : ∃ ξ, ξ ∈ Set.Icc (-ε) ε ∧
      Tendsto (fun (n : ℕ+) => ∫ x in (-ε)..ε, φ x * DiracSeq n x) atTop (nhds (φ ξ)) := by
  -- Apply mean value theorem.
  have hξn (n : ℕ+) := @exists_mul_eq_intervalIntegral (-ε) ε ?_ φ (DiracSeq n) volume _ _ ?_ ?_ ?_ ?_
  rotate_left
  . simp [hε.le]
  . exact Continuous.continuousOn hφ.continuous
  . exact Integrable.intervalIntegrable (DiracSeq.integrable (by simp))
  . exact eventually_of_forall  (DiracSeq.nonneg (by simp))
  . exact Integrable.intervalIntegrable (integrable_bump_mul_diracSeq hφ)

  have h1 : Tendsto (fun (n : ℕ+) => ∫ (x : ℝ) in -ε..ε, DiracSeq n x) atTop (nhds 1)
  . sorry

  -- Maybe this is actually impossible to show?
  -- Need `ξ` as a function of `n` (temperature of DiracSeq) to converge too?
  -- Which is exactly what we are trying to show?

  -- Maybe a better strategy is to show that the integral goes to zero for any `0 < ε`?
  -- However, the integral on the whole domain does not go to zero?


  -- What about if we modify the goal to include `n`?
  simp [Metric.tendsto_atTop]

  -- apply @Exists.imp ℝ (fun ξ => ξ ∈ Set.Icc (-ε) ε ∧
  --   Tendsto (fun n => φ ξ * ∫ (x : ℝ) in -ε..ε, DiracSeq (↑↑n) x) atTop (nhds (φ ξ)))
  -- . -- Wrong: Can't show this for all ξ.
  --   sorry
  -- . sorry

  -- apply @Exists.imp ℝ (fun ξ => ξ ∈ Set.Icc (-ε) ε ∧
  --   Tendsto (fun n => φ ξ * ∫ (x : ℝ) in -ε..ε, DiracSeq (↑↑n) x) atTop (nhds (φ ξ)))
  -- . -- Wrong: Can't show this for all ξ.
  --   sorry
  -- . sorry

  -- -- Can't rewrite with `hξn` because we need `n`.
  -- -- How can we get `n`?!
  -- -- As `n` increases, the integral of `DiracSeq n` on `[-ε, ε]` will get closer to 1.
  -- -- From `h1`, we can get `n` for a certain `r`.
  -- simp [Metric.tendsto_atTop] at h1
  -- -- How to get `r`? What about if we modify goal to contain `∀ r`?
  -- simp [Metric.tendsto_atTop]


  -- -- Can we just use `ξ = 0`?
  -- -- Will this hold as `n → ∞`, regardless of `ε`?
  -- -- Yes, but hard to show from mere existence of `ξ`?
  -- exists 0
  -- simp [hε.le]


  -- by_contra h
  -- simp [Metric.tendsto_atTop] at h

  -- have (ξ : ℝ) : ξ ∈ Set.Icc (-ε) ε
  --   → Tendsto (fun n => φ ξ * ∫ (x : ℝ) in -ε..ε, DiracSeq (↑↑n) x) atTop (nhds (φ ξ))
  --   → Tendsto (fun n => ∫ (x : ℝ) in -ε..ε, φ x * DiracSeq (↑↑n) x) atTop (nhds (φ ξ))
  -- . sorry

  -- have : ∃ ξ, ξ ∈ Set.Icc (-ε) ε ∧ Tendsto (fun n => φ ξ * ∫ (x : ℝ) in -ε..ε, DiracSeq (↑↑n) x) atTop (nhds (φ ξ))
  -- . sorry



  -- Need to get a ξ in order to specialize `h1`...
  -- Could use 0? But then we may as well just prove it directly?
  


  -- rw [Metric.tendsto_atTop] at h1
  -- exists 0
  -- simp [hε.le]
  -- rw [Metric.tendsto_atTop]
  -- intro r hr
  -- specialize h1 r hr
  -- rcases h1 with ⟨N, hN⟩



  -- rw [Metric.tendsto_atTop]
  -- intro r hr
  -- simp at hr ⊢
  -- rcases hφ.bounded with ⟨C, hC⟩
  -- simp at hC
  -- rw [Metric.tendsto_atTop] at hz

  sorry

  -- simp [← integral_Ici_eq_integral_Ioi]
  -- have hξn (n : ℕ+) := @exists_mul_eq_setInterval_Ici (ε : ℝ) φ (DiracSeq (n : ℝ)) volume ?_ ?_ ?_ ?_
  -- rotate_left
  -- . exact Continuous.continuousOn hφ.continuous
  -- . exact Integrable.integrableOn (DiracSeq.integrable (by simp))
  -- . apply eventually_of_forall; simp
  --   apply DiracSeq.nonneg; simp
  -- . apply Integrable.integrableOn
  --   apply Continuous.integrable_of_hasCompactSupport
  --   . exact Continuous.mul hφ.continuous (DiracSeq.continuous _)
  --   . exact HasCompactSupport.mul_right hφ.left

  -- simp [integral_Ici_eq_integral_Ioi] at hξn ⊢
  -- have hz := DiracSeq.tendsto_setIntegral_Ioi_zero hε
  -- replace hz := tendsto_atTop_pnat_of_tendsto_atTop_real hz

  -- -- Can't set integral to zero in goal; only true in limit.
  -- -- Use boundedness of bump function to show that it is close to zero.
  -- rw [Metric.tendsto_atTop]
  -- intro r hr
  -- simp at hr ⊢
  -- rcases hφ.bounded with ⟨C, hC⟩
  -- simp at hC
  -- rw [Metric.tendsto_atTop] at hz
  -- simp at hz
  -- have hC_nonneg : 0 ≤ C
  -- . exact le_trans (by simp) (hC 0)
  -- cases eq_or_gt_of_le hC_nonneg with
  -- | inl hC_zero =>
  --   simp [hC_zero] at hC
  --   simp [hC, hr]
  -- | inr hC_pos =>
  --   specialize hz (r / C)
  --   specialize hz (div_pos hr hC_pos)
  --   rcases hz with ⟨N, hN⟩
  --   exists N
  --   intro n hn
  --   specialize hN n hn
  --   rw [lt_div_iff hC_pos] at hN
  --   apply lt_of_le_of_lt ?_ hN
  --   -- Should be able to show this?
  --   rw [mul_comm _ C]
  --   -- TODO: Make a lemma from here?
  --   rw [← norm_eq_abs]
  --   rw [abs_of_nonneg]; swap
  --   . apply integral_nonneg
  --     intro x; simp
  --     apply DiracSeq.nonneg (by simp)
  --   rw [← integral_mul_left]
  --   apply norm_integral_le_of_norm_le
  --   . refine Integrable.integrableOn (Integrable.const_mul ?_ _)
  --     exact DiracSeq.integrable (by simp)
  --   apply eventually_of_forall
  --   intro x
  --   simp
  --   rw [abs_of_nonneg (DiracSeq.nonneg (by simp) _)]
  --   exact mul_le_mul_of_nonneg_right (hC x) (DiracSeq.nonneg (by simp) x)


lemma DiracSeq.exists_eq {φ : ℝ → ℝ} (hφ : IsBump φ) {ε : ℝ} (hε : 0 < ε)
    : ∃ (ξ : ℝ), ξ ∈ Set.Icc (-ε : ℝ) ε ∧
      (Tendsto (fun (n : ℕ+) => ∫ x, φ x * DiracSeq n x) atTop (nhds (φ ξ))) := by
  -- Split the integral into three parts.
  have {n : ℕ+} : ∫ x, φ x * DiracSeq n x =
      (∫ x in Set.Iio (-ε : ℝ), φ x * DiracSeq n x) +
      (∫ x in Set.Icc (-ε : ℝ) ε, φ x * DiracSeq n x) +
      (∫ x in Set.Ioi (ε : ℝ), φ x * DiracSeq n x)
  . rw [← integral_union _ measurableSet_Icc]
    rotate_left
    . exact Integrable.integrableOn (integrable_bump_mul_diracSeq hφ)
    . exact Integrable.integrableOn (integrable_bump_mul_diracSeq hφ)
    . rw [Set.disjoint_right]
      simp
      intro x h _
      exact h
    simp [hε.le]
    rw [← integral_union _ measurableSet_Ioi]
    rotate_left
    . exact Integrable.integrableOn (integrable_bump_mul_diracSeq hφ)
    . exact Integrable.integrableOn (integrable_bump_mul_diracSeq hφ)
    . simp
    simp
  simp [this]; clear this

  -- Could try to eliminate the zero terms using `Exists.imp`,
  -- but it's probably easier to find the `ξ` first and then proceed.
  have hξ : ∃ ξ, (-ε ≤ ξ ∧ ξ ≤ ε) ∧
    Tendsto (fun (n : ℕ+) => ∫ (x : ℝ) in Set.Icc (-ε) ε, φ x * DiracSeq n x) atTop (nhds (φ ξ))
  . 
    sorry

  rcases hξ with ⟨ξ, hξ⟩
  exists ξ
  refine And.intro hξ.left ?_
  conv => rhs; rw [← add_zero (φ ξ)]; rw [← zero_add (φ ξ)]
  refine Tendsto.add (Tendsto.add ?_ hξ.right) ?_
  . simp [← integral_Iic_eq_integral_Iio]
    simp [← integral_comp_neg_Ioi, DiracSeq.symm]
    exact DiracSeq.tendsto_integral_Ioi_bump_mul_zero hφ.comp_neg hε
  . exact DiracSeq.tendsto_integral_Ioi_bump_mul_zero hφ hε


  -- -- Before we can do `Tendsto.add`, we need to introduce the `ξ`?

  -- -- Switch to positive domain (and rename).
  -- conv => arg 1; intro ξ; rhs; rw [← Real.tendsto_comp_exp_atTop]; arg 1; intro b
  -- -- Obtain ξ for central interval and introduce it.
  -- have hξb {b} := @exists_mul_eq_intervalIntegral_of_continuousOn (-ε : ℝ) ε (by simp [hε.le])
  --   φ (DiracSeq (rexp b)) volume _ _ ?_ ?_ ?_
  -- rotate_left
  -- . exact Continuous.continuousOn hφ.continuous
  -- . exact Continuous.continuousOn (DiracSeq.continuous _)
  -- . intro x _
  --   exact DiracSeq.nonneg (le_of_lt (Real.exp_pos _)) x

  -- have hξ : ∃ ξ, ξ ∈ Set.Icc (-ε : ℝ) ε ∧
  --   Tendsto (fun b => ∫ (x : ℝ) in Set.Icc (-↑ε) ↑ε, φ x * DiracSeq (rexp b) x) atTop (nhds (φ ξ))
  -- . -- How to obtain this?
  --   -- Need to show that there exists a stable `ξ` (or at least, stable `φ ξ`) as `b → ∞`?
  --   --
  --   -- Maybe `IsSeqCompact.exists_tendsto`?
  --   -- This would need to be applied to the `f c` in the mean value theorem?
  --   --
  --   -- Maybe `TendstoUniformly` with `b` as an index (for the integral).
  --   sorry

  -- rcases hξ with ⟨ξ, hξ⟩
  -- exists ξ

  -- -- How to transform this?
  -- -- Need to show that there exists a stable `ξ` (or at least, stable `φ ξ`) as `b → ∞`?
  -- -- 

  -- -- ∫ (x : ℝ) in Set.Icc (-↑ε) ↑ε, φ x * DiracSeq b x

  -- conv => arg 1; intro ξ; rhs; arg 3; arg 1; rw [← add_zero (φ ξ)]; rw [← zero_add (φ ξ)]
  -- -- apply Tendsto.add

  -- -- have {ξ} : φ ξ = 0 + φ ξ + 0 := by simp
  -- -- simp only [this]

  -- -- have h_right : 
  -- -- have h_left : Tendsto (fun (n : ℝ) => ∫ x in Set.Iic (-ε : ℝ), φ x * DiracSeq n x) atTop (nhds 0)
  -- -- . apply @Tendsto.congr' ℝ ℝ 0
  -- --   . -- Apply mean value theorem.
  -- --     have hξ_left (n) := @exists_mul_eq_setInterval_Iic (-ε : ℝ) (DiracSeq n) φ volume ?_ ?_ ?_ ?_
  -- --     rotate_left
  -- --     . sorry
  -- --     . sorry
  -- --     . sorry
  -- --     . sorry
  -- --   . exact tendsto_const_nhds
  -- --   sorry
  


  -- simp only [MeasureTheory.integral_union]
  -- --  [← integral_univ]
  -- sorry
  
-- lemma existsTendsToIntegralMulGaussian (g : ℝ → ℝ) (hg : Continuous g)
--     : ∀ (ε : ℝ), 0 < ε → ∃ ξ, ξ ∈ Set.Icc (-ε) ε ∧
--         Tendsto (fun s => ∫ x, g x * (s / (Real.sqrt Real.pi) * Real.exp (-HPow.hPow (s * x) 2)))
--           atTop (nhds (g ξ)) := by

theorem DiracSeq.tendsto_integral_gaussian (φ : ℝ → ℝ) (hφ : Continuous φ)
    : Tendsto (fun (s : ℕ) => ∫ x, φ x * DiracSeq s x) atTop (nhds (φ 0)) := by
  -- Proof by contradiction.
  sorry
