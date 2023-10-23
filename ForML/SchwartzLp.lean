import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

open ENNReal MeasureTheory SchwartzSpace

-- Eventual goal: Prove that Fourier transform of Dirac is const and vice versa.

-- Want to define tempered distribution for constant function.
-- This corresponds to the integral of the function multiplied by a constant.
-- Therefore, need to prove that `SchartzMap` is integrable.
--
-- Use equivalent definition of Schwartz functions as described in:
-- https://math.stackexchange.com/questions/1505921/schwartz-functions-have-finite-lp-norm

-- Couldn't find this in mathlib.
lemma ENNReal_rpow_ne_top {a : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : a ≠ ⊤) : a ^ p ≠ ⊤ := by
  rw [← ofReal_toReal_eq_iff] at h
  rw [← h]
  simp
  intros
  exact hp.le

lemma ENNReal_rpow_lt_top {a : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : a < ⊤) : a ^ p < ⊤ := by
  rw [lt_top_iff_ne_top] at h ⊢
  exact ENNReal_rpow_ne_top hp h

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

-- -- Follows Folland (Real Analysis), Proposition 8.3.
-- lemma schwartz_decay_iff {f : E → F} :  -- add ContDiff?
--     (∀ (i j : ℕ), ∃ C, ∀ x, HPow.hPow ‖x‖ i * ‖iteratedFDeriv ℝ j f x‖ ≤ C) ↔
--     (∀ (n k : ℕ), ∃ C, ∀ x, HPow.hPow (1 + ‖x‖) (k + n) * ‖iteratedFDeriv ℝ k f x‖ ≤ C) := by
--   apply Iff.intro
--   . intro h n k
--     specialize h n k
--     rcases h with ⟨C, hC⟩
--     sorry
--   . intro h i j
--     -- specialize h i j
--     cases le_or_lt i j with
--     | inl hij =>
--       rcases h i j with ⟨C, hC⟩
--       use C
--       intro x
--       specialize hC x
--       refine le_trans ?_ hC
--       specialize h j (j - i)  -- TODO: Use `sub_le_self_iff`?
--       simp at h
--       sorry
--     | inr hij => sorry
--     sorry

-- lemma rpow_neg_one_add_abs_mem_Lp {p : ℝ≥0∞} (hp : 0 < p) {k : NNReal} (hN : 1/p < N) :
--     Memℒp (fun x => (1 + |x|) ^ (-(k : ℝ))) p := by
--   -- What's the strategy?
--   -- Know that `(1 + |x|) ^ -2` is integrable.
--   refine And.intro ?_ ?_
--   . sorry
--   . cases p with
--     | none => sorry
--     | some p =>
--       simp at hp hN ⊢
--       simp [snorm, snorm', hp.ne']
--       refine ENNReal_rpow_lt_top (inv_pos_of_pos hp) ?_
--       have : 
--       have {x : NNReal} : 0 < ‖1 + |x|‖₊
--       . exact lt_add_of_pos_of_le zero_lt_one (abs_nonneg _)
--       sorry

section Lp

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- Nothing new, just gives easy access to alternative bound.
-- This bound can be combined with `integrable_one_add_norm` from JapaneseBracket.
-- This bound resembles that of `Function.HasTemperateGrowth`.
lemma SchwartzMap.decay_one_add (f : 𝓢(E, F)) :
    ∀ (k n : ℕ), ∃ C, ∀ x, HPow.hPow (1 + ‖x‖) k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  have := @SchwartzMap.one_add_le_sup_seminorm_apply 𝕜 E F _ _ _ _ _ _ _ ⟨k, n⟩ k n (by simp) (by simp) f
  simp at this
  use HPow.hPow (2 : ℝ) k * Finset.sup (Finset.Iic (k, n)) (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f

lemma SchwartzMap.decay_one_add' (f : 𝓢(E, F)) (p : ℝ) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ (-p) := by
  intro n
  -- Use any integer `k` such that `p ≤ k`.
  generalize hk : ⌈p⌉₊ = k
  rcases SchwartzMap.decay_one_add 𝕜 f k n with ⟨C, hC⟩
  use C
  refine And.intro ?_ ?_
  . specialize hC 0  -- Use any `E`.
    simp at hC
    exact le_trans (norm_nonneg _) hC
  . intro x
    specialize hC x
    have h_pos : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
    rw [Real.rpow_neg h_pos.le]
    rw [mul_comm, inv_mul_eq_div]
    rw [le_div_iff' (Real.rpow_pos_of_pos h_pos _)]
    refine le_trans ?_ hC
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [← Real.rpow_nat_cast]
    refine Real.rpow_le_rpow_of_exponent_le (by simp) ?_
    simp [← hk]
    exact Nat.le_ceil _

-- Maybe it's more convenient to use this form?
lemma SchwartzMap.decay_one_add'' (f : 𝓢(E, F)) (p : NNReal) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ^ p ≤ C * (1 + ‖x‖) := by
  intro n
  -- Use any integer `k` such that `p ≤ k`.
  generalize hk : ⌈p⌉₊ = k
  rcases SchwartzMap.decay_one_add 𝕜 f k n with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C
  . specialize hC 0  -- Use any `E`.
    simp at hC
    exact le_trans (norm_nonneg _) hC
  have hCp_nonneg : 0 ≤ C ^ p := Real.rpow_nonneg_of_nonneg hC_nonneg p
  use C ^ p
  refine And.intro hCp_nonneg ?_
  intro x
  specialize hC x
  -- Put lhs and rhs to power of `p`.
  have h_pos : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  -- have h_lhs_nonneg : 0 ≤ HPow.hPow (1 + ‖x‖) k * ‖iteratedFDeriv ℝ n f x‖
  -- . exact mul_nonneg (pow_nonneg h_pos.le k) (norm_nonneg _)
  have : (HPow.hPow (1 + ‖x‖) k * ‖iteratedFDeriv ℝ n f x‖) ^ p ≤ C ^ p
  . refine Real.rpow_le_rpow ?_ hC (NNReal.coe_nonneg p)
    exact mul_nonneg (pow_nonneg h_pos.le k) (norm_nonneg _)
  rw [Real.mul_rpow (pow_nonneg h_pos.le k) (norm_nonneg _)] at this
  rw [← le_div_iff' (Real.rpow_pos_of_pos (pow_pos h_pos k) p)] at this
  refine le_trans this ?_
  rw [← Real.rpow_nat_cast]
  rw [← Real.rpow_mul h_pos.le]
  rw [div_eq_inv_mul]
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hCp_nonneg
  rw [← Real.rpow_neg h_pos.le]
  sorry

-- TODO: Generalize to `Memℒp _ ⊤`.
-- TODO: Generalise from `𝓢(ℝ, F)` to `𝓢(E, F)` using `iteratedFDeriv` form
-- (`iteratedFDeriv` returns `ContinuousLinearMap`).
-- TODO: Generalize to differential multi-index.
theorem SchwartzMap.iteratedDeriv_mem_Lp (f : 𝓢(ℝ, F)) {p : NNReal} (hp : 1 ≤ p) :
    ∀ (n : ℕ), Memℒp (fun x => iteratedDeriv n f.toFun x) p := by
  intro n
  have hf_decay' (k) := SchwartzMap.decay_one_add' 𝕜 f k n
  rcases f with ⟨f, hf_smooth, hf_decay⟩
  simp [FunLike.coe] at hf_decay' ⊢
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hf_decay
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hf_decay'
  apply And.intro
  . refine Continuous.aestronglyMeasurable ?_
    exact ContDiff.continuous_iteratedDeriv _ hf_smooth (by simp)
  . -- Choose `k` such that:
    -- `FiniteDimensional.finrank ℝ E < p * k` for `integrable_one_add_norm`
    generalize hd : FiniteDimensional.finrank ℝ ℝ = d
    generalize hN : ⌈(d / p : ℝ)⌉₊ + 1 = N
    specialize hf_decay' N  -- Any N > n / p will suffice; have p ≥ 1.
    have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    simp [snorm, hp_pos.ne']
    simp [snorm']
    refine ENNReal_rpow_lt_top (inv_pos_of_pos hp_pos) ?_
    rcases hf_decay' with ⟨C, ⟨hC_nonneg, hC⟩⟩
    suffices : ∫⁻ (x : ℝ), (‖iteratedDeriv n f x‖₊ : ENNReal) ^ (p : ℝ) ≤
        (ENNReal.ofReal C) * ∫⁻ (x : ℝ), ENNReal.ofReal ((1 + ‖x‖) ^ (-(p * N) : ℝ))
    . apply lt_of_le_of_lt this
      refine ENNReal.mul_lt_top ofReal_ne_top ?_
      rw [← lt_top_iff_ne_top]
      refine finite_integral_one_add_norm ?_  -- "JapaneseBracket"
      rw [hd]
      simp [← hN]
      simp [mul_add]
      refine lt_add_of_le_of_pos ?_ hp_pos
      sorry  -- Looks good.
    rw [← MeasureTheory.lintegral_const_mul]
    swap
    . refine Measurable.ennreal_ofReal ?_
      exact Measurable.pow_const (Measurable.const_add measurable_norm _) _
    simp_rw [← ENNReal.ofReal_mul hC_nonneg]
    have hp_coe_pos : 0 < (p : ℝ) := hp_pos
    simp_rw [ENNReal.coe_rpow_of_nonneg _ hp_coe_pos.le]
    simp [ENNReal.ofReal]
    refine lintegral_mono_nnreal ?_
    intro x
    simp
    rw [← norm_toNNReal]
    rw [← Real.toNNReal_rpow_of_nonneg (norm_nonneg _)]
    refine Real.toNNReal_le_toNNReal ?_
    sorry

lemma SchwartzMap.aestronglyMeasurable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]
    (f : 𝓢(E, F)) (μ : Measure E) : AEStronglyMeasurable f μ :=
  Continuous.aestronglyMeasurable f.continuous

-- TODO: Is there a way to define this from `StronglyMeasurable` instead of `AEStronglyMeasurable`?
-- Would that make things easier later?
def SchwartzMap.toAEEqFun [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]
    (f : 𝓢(E, F)) (μ : Measure E) : AEEqFun E F μ := AEEqFun.mk f.toFun (f.aestronglyMeasurable μ)

def SchwartzMap.toLp (f : 𝓢(ℝ, F)) {p : NNReal} (hp : 1 ≤ p) : Lp F p (volume : Measure ℝ) where
  val := f.toAEEqFun volume
  property := by
    simp [SchwartzMap.toAEEqFun]
    sorry

end Lp  -- [SMulCommClass ℝ 𝕜 F]


-- TODO: Generalize to `𝒮(E, F)`.
-- lemma SchwartzMap.integrable [MeasureSpace E] {f : 𝓢(E, F)} : Integrable f := sorry

-- Use `Memℒp f 1` to provide `Integrable`.
-- Cannot use `BoundedContinuousFunction.integrable` as it requires `IsFiniteMeasure μ`.
lemma SchwartzMap.integrable {f : 𝓢(ℝ, F)} : Integrable f := by
  have hp : (1 : NNReal) ≤ 1 := by simp
  have := L1.integrable_coeFn (f.toLp hp)
  -- Need to show equivalent.
  sorry

-- Is it correct to use `c : 𝕜`?
-- TODO: Why do we need to define `cont` here?
-- TODO: Generalize to `𝓢(ℝ, E)`.
lemma SchwartzMap.const (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (c : 𝕜) : 𝓢(ℝ, F) →L[𝕜] F where
  toFun f := c • ∫ x, f x
  map_add' := sorry
  map_smul' := sorry
  cont := sorry
