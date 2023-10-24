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

/- Exposes alternative form of Schwartz decay condition.

Can be obtained from `one_add_le_sup_seminorm_apply`.
Useful for combining with "Japanese bracket" in `integrable_one_add_norm`.

TODO: Add proof of equivalence of conditions?
-/
lemma decay₁ (f : 𝓢(E, F)) :
    ∀ (k n : ℕ), ∃ C, ∀ x, HPow.hPow (1 + ‖x‖) k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  have := @one_add_le_sup_seminorm_apply ℝ E F _ _ _ _ _ _ _ ⟨k, n⟩ k n (by simp) (by simp) f
  simp at this
  use HPow.hPow (2 : ℝ) k * Finset.sup (Finset.Iic (k, n)) (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

/- Re-arranged version of `decay₁`. -/
lemma norm_iteratedFDeriv_le_pow_one_add_norm (f : 𝓢(E, F)) (r : ℝ) :
    ∀ (n : ℕ), ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ (-r) := by
  -- TODO: Better to remove the negative in the power?
  -- Most interesting for non-negative powers.
  intro n
  -- Use any integer `k` such that `r ≤ k`.
  generalize hk : ⌈r⌉₊ = k
  rcases decay₁ f k n with ⟨C, hC⟩
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
  rcases norm_iteratedFDeriv_le_pow_one_add_norm f r n with ⟨C, ⟨hC_nonneg, hC⟩⟩
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
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm f hp 1
  simpa [Real.rpow_neg_one]

-- Rewrite for `norm` (`iteratedFDeriv` with `n = 0`).

/- Convenient form of `pow_norm_iteratedFDeriv_le_pow_one_add_norm`. -/
lemma pow_norm_le_pow_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ^ p ≤ C * (1 + ‖x‖) ^ (-q) := by
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm f hp q 0
  simpa

/- Schwartz map is bounded by `C_q * (1 + ‖x‖) ^ (-q)` for all `q`. -/
lemma norm_le_pow_one_add_norm (f : 𝓢(E, F)) (q : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q) := by
  have := pow_norm_iteratedFDeriv_le_pow_one_add_norm f zero_lt_one q 0
  simpa

/- Convenient form of `pow_norm_iteratedFDeriv_le_pow_one_add_norm`. -/
lemma pow_norm_le_inv_one_add_norm (f : 𝓢(E, F)) {p : ℝ} (hp : 0 < p) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ^ p ≤ C * (1 + ‖x‖)⁻¹ := by
  have := pow_norm_iteratedFDeriv_le_inv_one_add_norm f hp 0
  simpa

/- Schwartz map is bounded by `C * (1 + ‖x‖)⁻¹`. -/
lemma norm_le_inv_one_add_norm (f : 𝓢(E, F)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)⁻¹ := by
  have := pow_norm_iteratedFDeriv_le_inv_one_add_norm f zero_lt_one 0
  simpa


section Integral

variable [MeasureSpace E]
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
  rcases pow_norm_le_pow_one_add_norm f hp.out r with ⟨C, ⟨hC_nonneg, hC⟩⟩
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
  Memℒp.toLp f.toFun (mem_Lp f p)

lemma coeFn_toLp {p : NNReal} [Fact (0 < p)] (f : 𝓢(E, F)) : f.toLp p =ᵐ[volume] f :=
  Memℒp.coeFn_toLp _

lemma mem_L1 (f : 𝓢(E, F)) : Memℒp f 1 := by
  have _ : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  exact mem_Lp f 1

def toL1 (f : 𝓢(E, F)) : Lp F 1 (by volume_tac : Measure E) :=
  Memℒp.toLp f.toFun (mem_L1 f)

lemma coeFn_toL1 (f : 𝓢(E, F)) : f.toL1 =ᵐ[volume] f :=
  Memℒp.coeFn_toLp (mem_L1 f)

-- -- Define integral using `L1.integral`.
-- -- TODO: Defining manually eliminates `CompleteSpace`?
-- noncomputable def integral [CompleteSpace F] (f : 𝓢(E, F)) : F := L1.integral f.toL1

-- -- TODO: Generalize to `𝕜` in `integralCLM'`.
-- def integralCLM [CompleteSpace F] : 𝓢(E, F) →L[ℝ] F where
--   toFun := integral
--   map_add' := sorry
--   map_smul' := sorry
--   cont := by
--     simp
--     simp [integral]
--     sorry

-- def toL1CLM : 𝓢(E, F) →L[ℝ] Lp F 1 (by volume_tac : Measure E) :=
--   mkCLM (fun f)

-- def toL1CLM' (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
--     𝓢(E, F) →L[𝕜] Lp F 1 (by volume_tac : Measure E) where
--   toFun := toL1
--   map_add' f g := by rfl
--   map_smul' d f := by rfl
--   cont := by
--     simp [toL1]
--     sorry

-- Use `Memℒp f 1` to provide `Integrable`.
-- Cannot use `BoundedContinuousFunction.integrable` as it requires `IsFiniteMeasure μ`.
lemma integrable {f : 𝓢(E, F)} : Integrable f :=
  Integrable.congr (L1.integrable_coeFn f.toL1) (coeFn_toL1 f)

-- Helper for `integralCLM`. Need `CompleteSpace F` to use `L1.integral`?
lemma integralLM [CompleteSpace F] : 𝓢(E, F) →ₗ[ℝ] F where
  -- toFun f := ∫ (x : E), f x
  -- map_add' f g := by simp [integral_add f.integrable g.integrable]
  -- map_smul' d f := by simp [integral_smul]
  toFun f := L1.integral f.toL1
  -- toFun f := L1.integralCLM f.toL1
  map_add' f g := sorry
  map_smul' d f := sorry

-- Can we prove that any linear map from `𝓢(E, F)` to `F` is continuous? Need bound...
example : Continuous (lm : 𝓢(E, F) →ₗ[ℝ] F) := by
  -- refine Seminorm.continuous_from_bounded
  --   (schwartz_withSeminorms ℝ E F) (norm_withSeminorms ℝ F) _ ?_
  -- rw [Seminorm.isBounded_const]
  refine Seminorm.cont_withSeminorms_normedSpace F (schwartz_withSeminorms ℝ E F) _ ?_
  sorry

-- Look for `(C, s)` that give a bound on `integralLM` in terms of `schwartzSeminormFamily`.
example [CompleteSpace F] (s : Finset (ℕ × ℕ)) (C : NNReal) :
    Seminorm.comp (normSeminorm ℝ F) integralLM ≤ C • Finset.sup s (schwartzSeminormFamily ℝ E F) := by
  intro f
  simp
  have : integralLM f = L1.integral f.toL1
  . sorry  -- Could define/show?
  rw [this]
  refine le_trans (L1.norm_integral_le _) ?_
  rw [toL1]
  simp  -- `Lp.norm_toLp`
  rw [snorm_one_eq_lintegral_nnnorm]
  simp [schwartzSeminormFamily]
  rw?
  sorry

-- lemma integral_isBounded : ∃ (s : Finset (ℕ × ℕ)) (C : NNReal),
--     Seminorm.comp (normSeminorm ℝ F) integralLM ≤
--     C • Finset.sup s (schwartzSeminormFamily ℝ E F) := by
--   -- Use `L1.norm_Integral_le_one` for `‖L1.integralCLM‖ ≤ 1`? Wrong norm...
--   simp [schwartzSeminormFamily]
--   -- simp [SchwartzMap.seminormAux, Seminorm.ofSMulLE, Seminorm.of]
--   sorry

/- Integral of a Schwartz map as a `ContinuousLinearMap`.

Based on `SchwartzMap.mkCLM`, which is for `𝓢(E, F) →L[𝕜] 𝓢(E, F)`.

TODO: Generalize to `𝕜` in `integralCLM'`.
-/
lemma integralCLM [CompleteSpace F] : 𝓢(E, F) →L[ℝ] F where
  toLinearMap := integralLM
  cont := by
    simp
    -- change Continuous (integralLM : 𝓢(E, F) →ₗ[ℝ] F)
    -- -- Use `norm_withSeminorms ℝ 𝔽` to obtain `WithSeminorm _` for `F`.
    -- refine Seminorm.continuous_from_bounded
    --   (schwartz_withSeminorms ℝ E F) (norm_withSeminorms ℝ F) _ ?_
    -- rw [Seminorm.isBounded_const]
    refine Seminorm.cont_withSeminorms_normedSpace F (schwartz_withSeminorms ℝ E F) _ ?_
    sorry

-- /- Integral of a Schwartz map as a `ContinuousLinearMap`. -/
-- lemma integralCLM' [CompleteSpace F]
--     (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
--     𝓢(E, F) →L[𝕜] F where
--   toFun f := L1.integralCLM' 𝕜 f.toL1
--   map_add' f g := by
--     simp
--     sorry
--   map_smul' d f := by
--     simp
--     sorry
--   cont := by
--     simp
--     refine Continuous.comp ?_ ?_
--     . exact ContinuousLinearMap.continuous _
--     . sorry

-- section SMul
-- variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- lemma integrable_smul
--     {f : E → 𝕜}
--     (hf_meas : MeasureTheory.AEStronglyMeasurable f (volume : Measure E))
--     (hf_ess_sup : essSup (fun x => (‖f x‖₊ : ENNReal)) (volume : Measure E) ≠ ⊤)
--     (φ : 𝓢(E, F)) :
--     Integrable (fun x => f x • φ x) :=
--   Integrable.essSup_smul SchwartzMap.integrable hf_meas hf_ess_sup

-- end SMul

end Integral
end SchwartzMap


namespace TemperedDistribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [MeasureSpace E] [CompleteSpace F]
-- variable [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]
variable [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
-- variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

section SMul

-- `integral_smul` requires `NontriviallyNormedField` rather than `NormedField`.
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- TODO: Is it useful to define `const_smul` using `𝕜` and `const_mul` using `F`?
lemma const_smul (c : 𝕜) : 𝓢(E, F) →L[𝕜] F where
  toFun f := c • ∫ (x : E), f x
  map_add' f g := by
    simp [integral_add f.integrable g.integrable]
  map_smul' d f := by
    simp [integral_smul]
    rw [smul_comm]
  cont := by
    simp
    refine Continuous.const_smul ?_ c
    sorry

/- Define a distribution from a bounded measurable function by integration. -/
-- TODO: Why do we need to define `cont` here?
noncomputable def integral_essSup_smul (f : E → 𝕜)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f (volume : Measure E))
    (hf_ess_sup : essSup (fun x => (‖f x‖₊ : ENNReal)) (volume : Measure E) ≠ ⊤) :
    𝓢(E, F) →L[𝕜] F where
  toFun φ := ∫ (x : E), f x • φ x
  map_add' φ φ' := by sorry
  map_smul' := by sorry
  cont := by sorry

-- noncomputable def integral_bdd_smul (f : E → 𝕜)
--     (hf_meas : MeasureTheory.AEStronglyMeasurable f (volume : Measure E))
--     (hf_ess_sup : essSup (fun x => (‖f x‖₊ : ENNReal)) (volume : Measure E) ≠ ⊤) :
--     𝓢(E, F) →L[𝕜] F where
--   toFun φ := ∫ (x : E), f x • φ x
--   map_add' φ φ' := by sorry
--   map_smul' := by sorry
--   cont := by sorry

end SMul

-- TODO: Should this whole thing be a CLM?
-- Maybe provide `asCLM` instead for readabilty?
def RealFourier (f : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := sorry

noncomputable def RealFourier.asCLM : (𝓢(ℝ, ℂ) →L[ℂ] ℂ) →L[ℂ] 𝓢(ℝ, ℂ) →L[ℂ] ℂ where
  toFun := RealFourier
  map_add' f g := sorry
  map_smul' f g := sorry
  cont := sorry

end TemperedDistribution
