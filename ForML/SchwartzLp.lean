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


namespace SchwartzMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/- Exposes alternative form of Schwartz decay condition.

Can be obtained from `one_add_le_sup_seminorm_apply`.
Useful for combining with "Japanese bracket" in `integrable_one_add_norm`.

TODO: Add proof of equivalence of conditions?
-/
lemma decay₁ (f : 𝓢(E, F)) :
    ∀ (k n : ℕ), ∃ C, ∀ x, HPow.hPow (1 + ‖x‖) k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  have := @one_add_le_sup_seminorm_apply 𝕜 E F _ _ _ _ _ _ _ ⟨k, n⟩ k n (by simp) (by simp) f
  simp at this
  use HPow.hPow (2 : ℝ) k * Finset.sup (Finset.Iic (k, n)) (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f

/- Re-arranged version of `decay₁`. -/
lemma norm_iteratedFDeriv_le_pow_one_add_norm (f : 𝓢(E, F)) (r : ℝ) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ (-r) := by
  -- TODO: Better to remove the negative in the power?
  -- Most interesting for non-negative powers.
  intro n
  -- Use any integer `k` such that `r ≤ k`.
  generalize hk : ⌈r⌉₊ = k
  rcases decay₁ 𝕜 f k n with ⟨C, hC⟩
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

/- Useful form for proving that derivatives are in `Lp`. -/
lemma pow_norm_iteratedFDeriv_le_pow_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ^ p ≤ C * (1 + ‖x‖) ^ (-q) := by
  -- Seems wild that we can choose arbitrary `q`?
  intro n
  generalize hr : q / p = r
  rcases norm_iteratedFDeriv_le_pow_one_add_norm 𝕜 f r n with ⟨C, ⟨hC_nonneg, hC⟩⟩
  use C ^ p
  have hC_pow : 0 ≤ C ^ p := Real.rpow_nonneg_of_nonneg hC_nonneg _
  refine And.intro hC_pow ?_
  intro x
  specialize hC x
  have hq : q = p * r := by rw [← hr, mul_div, mul_div_cancel_left _ hp.ne']
  rw [hq]
  have hb_pos : 0 < 1 + ‖x‖
  . exact add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  rw [mul_comm p r, ← neg_mul, Real.rpow_mul hb_pos.le]
  rw [← Real.mul_rpow hC_nonneg (Real.rpow_nonneg_of_nonneg hb_pos.le _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hC hp.le

/- Simple version of `pow_norm_iteratedFDeriv_le_pow_one_add_norm` with `q = -1`. -/
lemma pow_norm_iteratedFDeriv_le_inv_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ^ p ≤ C * (1 + ‖x‖)⁻¹ := by
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm 𝕜 f hp 1
  simpa [Real.rpow_neg_one]

-- Rewrite for `norm` (`iteratedFDeriv` with `n = 0`).

/- Convenient form of `pow_norm_iteratedFDeriv_le_pow_one_add_norm`. -/
lemma pow_norm_le_pow_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ^ p ≤ C * (1 + ‖x‖) ^ (-q) := by
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm 𝕜 f hp q 0
  simpa

/- Schwartz map is bounded by `C_q * (1 + ‖x‖) ^ (-q)` for all `q`. -/
lemma norm_le_pow_one_add_norm (f : 𝓢(E, F)) (q : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q) := by
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm 𝕜 f zero_lt_one q 0
  simpa

/- Convenient form of `pow_norm_iteratedFDeriv_le_pow_one_add_norm`. -/
lemma pow_norm_le_inv_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ^ p ≤ C * (1 + ‖x‖)⁻¹ := by
  have := pow_norm_iteratedFDeriv_le_inv_one_add_norm 𝕜 f hp 0
  simpa

/- Schwartz map is bounded by `C * (1 + ‖x‖)⁻¹`. -/
lemma norm_le_inv_one_add_norm (f : 𝓢(E, F)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)⁻¹ := by
  have := pow_norm_iteratedFDeriv_le_inv_one_add_norm 𝕜 f zero_lt_one 0
  simpa


section Integral

variable [MeasureSpace E] [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]
variable [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/- Schwartz maps in `𝓢(E, F)` are in `Lp` for `p ∈ (0, ∞)` and finite-dimensional `E`.

Only holds for `Lp .. volume` (inherited from `integrable_one_add_norm`).

TODO: Generalize to `Memℒp f ⊤`?

TODO: Show that Schwartz maps are dense in `Lp`?
Might be achieved by showing that smooth, compact functions are dense in `Lp`.

Could also show that derivatives are in `Lp`, but this is trivial since
the derivative of a Schwartz map is a Schwartz map.
-/
lemma mem_Lp (f : 𝓢(E, F)) (p : NNReal) [hp : Fact (0 < p)] : Memℒp f p := by
  -- TODO: Just use `iteratedDeriv_mem_Lp` once generalized to `𝓢(E, F)`?
  refine And.intro f.continuous.aestronglyMeasurable ?_
  simp [snorm, hp.out.ne', snorm']
  refine ENNReal_rpow_lt_top (inv_pos_of_pos hp.out) ?_
  generalize hr : (FiniteDimensional.finrank ℝ E + 1 : ℝ) = r
  -- Need to get `C` for condition.
  rcases pow_norm_le_pow_one_add_norm 𝕜 f hp.out r with ⟨C, ⟨hC_nonneg, hC⟩⟩
  simp at hC
  suffices : ∫⁻ (x : E), (‖f x‖₊ : ENNReal) ^ (p : ℝ) ≤ ∫⁻ (x : E), ENNReal.ofReal (C * (1 + ‖x‖) ^ (-r))
  . refine lt_of_le_of_lt this ?_
    -- Remove the `C` from the condition.
    simp_rw [ENNReal.ofReal_mul hC_nonneg]
    rw [lintegral_const_mul]
    swap
    . refine Measurable.ennreal_ofReal ?_
      exact Measurable.pow_const (Measurable.const_add measurable_norm _) _
    refine ENNReal.mul_lt_top (by simp) ?_
    -- Use the "Japanese bracket".
    rw [← lt_top_iff_ne_top]
    refine finite_integral_one_add_norm ?_
    simp [← hr]
  refine lintegral_mono ?_
  intro x
  -- Get to NNReal.
  simp
  rw [ENNReal.ofReal]
  have hp_coe_pos : 0 < (p : ℝ) := hp.out
  rw [ENNReal.coe_rpow_of_nonneg _ hp_coe_pos.le]
  norm_cast
  -- Get to ℝ.
  rw [← norm_toNNReal]
  rw [← Real.toNNReal_rpow_of_nonneg (norm_nonneg _)]
  refine Real.toNNReal_le_toNNReal ?_
  exact hC x

-- Didn't need this to define `toLp`; just use `Memℒp.toLp`.
-- Could use `toContinuousMap.toAEEqFun`; it needs `[BorelSpace E]` (and `noncomputable`).
def toAEEqFun (f : 𝓢(E, F)) (μ : Measure E) : E →ₘ[μ] F :=
  AEEqFun.mk f.toFun f.continuous.aestronglyMeasurable

lemma coeFn_toAEEqFun (f : 𝓢(E, F)) (μ : Measure E) : f.toAEEqFun μ =ᵐ[μ] f.toFun :=
  AEEqFun.coeFn_mk _ _

-- TODO: May be better to write this as a continuous linear map, like `ContinuousMap.toLp`?
-- Or use `SchwartzMap.toContinuousMap.toAEEqFun`?
def toLp (p : NNReal) [Fact (0 < p)] (f : 𝓢(E, F)) :
    Lp F p (by volume_tac : Measure E) :=
  Memℒp.toLp f.toFun (mem_Lp 𝕜 f p)

lemma coeFn_toLp {p : NNReal} [Fact (0 < p)] (f : 𝓢(E, F)) : f.toLp 𝕜 p =ᵐ[volume] f :=
  Memℒp.coeFn_toLp _

-- Use `Memℒp f 1` to provide `Integrable`.
-- Cannot use `BoundedContinuousFunction.integrable` as it requires `IsFiniteMeasure μ`.
lemma integrable {f : 𝓢(E, F)} : Integrable f := by
  have hp : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  refine Integrable.congr (L1.integrable_coeFn (f.toLp 𝕜 1)) ?_
  exact coeFn_toLp 𝕜 f


end Integral  -- [MeasureSpace E] [SecondCountableTopologyEither E F]

-- end Lp  -- [SMulCommClass ℝ 𝕜 F]

end SchwartzMap
