-- First prove that Schwartz maps have finite integral.
-- This can be achieved by proving that Schwartz maps are in `Lp`.

-- Then prove that integral is a continuous linear map `𝓢(E, F) →L[𝕜] F`.
-- To achieve this, define conversion from `𝓢(E, F)` to `Lp F 1` as CLM.
-- This lets us use `ContinuousLinearMap.comp` to convert
-- a CLMs on `Lp F 1` to a CLM on `𝓢(E, F)`, including `L1.integralCLM`.

-- TODO: Prove that Schwartz maps are dense in Lp.

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.Bochner

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace

-- Eventual goal: Prove that Fourier transform of Dirac is const and vice versa.

-- Want to define tempered distribution for constant function.
-- This corresponds to the integral of the function multiplied by a constant.
-- Therefore, need to prove that `SchartzMap` is integrable.
--
-- Use equivalent definition of Schwartz functions as described in:
-- https://math.stackexchange.com/questions/1505921/schwartz-functions-have-finite-lp-norm

-- Couldn't find this in mathlib.
lemma ENNReal_rpow_ne_top {a : ENNReal} {p : ℝ} (hp : 0 < p) (h : a ≠ ⊤) : a ^ p ≠ ⊤ := by
  rw [← ENNReal.ofReal_toReal_eq_iff] at h
  rw [← h]
  simp
  intros
  exact hp.le

lemma ENNReal_rpow_lt_top {a : ENNReal} {p : ℝ} (hp : 0 < p) (h : a < ⊤) : a ^ p < ⊤ := by
  rw [lt_top_iff_ne_top] at h ⊢
  exact ENNReal_rpow_ne_top hp h


namespace SchwartzMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma coeFn_add {f g : 𝓢(E, F)} : (↑(f + g) : E → F) = ↑f + ↑g := by
  ext x
  simp

/- Exposes alternative form of Schwartz decay condition.

Can be obtained from `one_add_le_sup_seminorm_apply`.
Useful for combining with "Japanese bracket" in `integrable_one_add_norm`.

TODO: Add proof of equivalence of conditions?
TODO: Check if this is more simply obtained with
`le_rpow_one_add_norm_iff_norm_le` and `SchwartzMap.norm_pow_mul_le_seminorm`?
-/
lemma decay₁ (f : 𝓢(E, F)) :
    ∀ (k n : ℕ), ∃ C, ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  have := @one_add_le_sup_seminorm_apply ℝ E F _ _ _ _ _ _ _ ⟨k, n⟩ k n (by simp) (by simp) f
  simp at this
  use ((2 : ℝ) ^ k) * Finset.sup (Finset.Iic (k, n)) (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f


-- Trivial but may be useful for definitions.
lemma decay_of_decay₁ {f : E → F}
    (h : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  specialize h k n
  rcases h with ⟨C, hC⟩
  use C
  intro x
  specialize hC x
  refine le_trans ?_ hC
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simp [pow_le_pow_of_le_left]

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


-- Define some handy `simp` lemmas for `1 + ‖x‖`.
section OneAddNorm
variable {α : Type*} [SeminormedAddGroup α]

@[simp] lemma one_add_norm_pos (x : α) : 0 < 1 + ‖x‖ :=
  add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)

@[simp] lemma one_add_norm_nonneg (x : α) : 0 ≤ 1 + ‖x‖ :=
  le_of_lt (one_add_norm_pos x)

@[simp] lemma one_add_norm_ne_zero (x : α) : 1 + ‖x‖ ≠ 0 :=
  ne_of_gt (one_add_norm_pos x)

end OneAddNorm


-- section Measurable
-- variable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]

-- lemma aestronglyMeasurable (f : 𝓢(E, F)) (μ : Measure E := by volume_tac) :
--     AEStronglyMeasurable f μ := by
--   exact f.continuous.aestronglyMeasurable

-- end Measurable


section Integrable

variable [mE : MeasureSpace E]
variable [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]

-- Simple to prove `L∞` case.
lemma snorm_top_lt_top (f : 𝓢(E, F)) : snorm f ⊤ volume < ⊤ := by
  rcases f.decay 0 0 with ⟨C, hC⟩
  simp at hC
  exact snormEssSup_lt_top_of_ae_bound (Filter.eventually_of_forall hC.right)

/- Schwartz maps in `𝓢(E, F)` are in `Lp` for `p ∈ (0, ∞)` and finite-dimensional `E`.

Only holds for `volume` (inherited from `integrable_one_add_norm`).
-/
lemma snorm_nnreal_lt_top (f : 𝓢(E, F)) {p : NNReal} (hp : 0 < p) : snorm f p volume < ⊤ := by
  simp [snorm, hp.ne', snorm']
  refine ENNReal_rpow_lt_top (inv_pos_of_pos hp) ?_
  generalize hr : (FiniteDimensional.finrank ℝ E + 1 : ℝ) = r
  -- Need to get `C` for condition.
  rcases pow_norm_le_pow_one_add_norm f hp r with ⟨C, ⟨hC_nonneg, hC⟩⟩
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
  have hp_coe_pos : 0 < (p : ℝ) := hp
  rw [ENNReal.coe_rpow_of_nonneg _ hp_coe_pos.le]
  norm_cast
  -- Get to ℝ.
  rw [← norm_toNNReal]
  rw [← Real.toNNReal_rpow_of_nonneg (norm_nonneg _)]
  refine Real.toNNReal_le_toNNReal ?_
  exact hC x

lemma snorm_lt_top (f : 𝓢(E, F)) {p : ENNReal} : snorm f p volume < ⊤ := by
  cases p with
  | none => exact snorm_top_lt_top f
  | some p =>
    simp
    cases eq_or_lt_of_le (zero_le p) with
    | inl hp => simp [← hp]
    | inr hp => exact snorm_nnreal_lt_top f hp

/- Schwartz maps in `𝓢(E, F)` are in `Lp` for finite-dimensional `E`.

TODO: Show that Schwartz maps are dense in `Lp`?
Might be achieved by showing that smooth, compact functions are dense in `Lp`.
-/
lemma memℒp (f : 𝓢(E, F)) (p : ENNReal) : Memℒp f p :=
  ⟨f.continuous.aestronglyMeasurable, (snorm_lt_top f)⟩

def toLp (p : ENNReal) (f : 𝓢(E, F)) : Lp (α := E) F p :=
  Memℒp.toLp f (memℒp f p)

lemma coeFn_toLp {p : ENNReal} (f : 𝓢(E, F)) : f.toLp p =ᵐ[volume] f :=
  Memℒp.coeFn_toLp _

-- `L1` is useful for `L1.integralCLM`.
-- Also, any function in `L1` is also in `Lp` with `1 < p`.
noncomputable def toL1 : 𝓢(E, F) → Lp (α := E) F 1 := toLp 1

lemma coeFn_toL1 (f : 𝓢(E, F)) : f.toL1 =ᵐ[volume] f := by simp [toL1, coeFn_toLp]

lemma norm_toL1_eq_integral (f : 𝓢(E, F)) : ‖toL1 f‖ = ∫ x, ‖f x‖ := by
  simp [toL1, toLp]
  rw [snorm_one_eq_lintegral_nnnorm]
  rw [integral_norm_eq_lintegral_nnnorm f.continuous.aestronglyMeasurable]

-- TODO: Would it be useful to have this? Or no point?
-- lemma addHomL1 : 𝓢(E, F) →+ Lp F 1 mE.volume where
--   toFun := toLp 1
--   map_zero' := by rfl
--   map_add' f g := by rfl

-- Use `Memℒp f 1` to provide `Integrable`.
lemma integrable {f : 𝓢(E, F)} : Integrable f := by
  rw [← memℒp_one_iff_integrable]
  exact memℒp f 1


section Continuous

variable {𝕜 : Type*} [NormedField 𝕜] -- [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- Write a short version of the supremem of the seminorm over `Finset.Iic (k, n)`.
-- `k` is the power, `n` is the derivative number.
-- TODO: Avoid notation of `𝕜 k`?
section Def
variable (𝕜)
noncomputable def sup_Iic_seminorm (k n : ℕ) : 𝓢(E, F) → ℝ :=
  fun f => (Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f
end Def

lemma sup_Iic_seminorm_apply {k n : ℕ} {f : 𝓢(E, F)} :
  sup_Iic_seminorm 𝕜 k n f = (Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 E F) f := rfl

-- Now we need to obtain an upper bound of the form:
-- `∃ C, ∫ x, ‖f x‖ ≤ C * sup_Iic_seminorm 𝕜 k n f`
-- for some `k` and `n` that we choose.

-- Obtain inequality relating `‖f x‖` and `sup_Iic_seminorm 𝕜 k 0 f` (i.e. 0-th derivative).
lemma pow_one_add_norm_mul_norm_le_two_pow_sup_Iic_seminorm (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖f x‖ ≤ 2 ^ k * sup_Iic_seminorm 𝕜 k 0 f := by
  have := @one_add_le_sup_seminorm_apply 𝕜 E F _ _ _ _ _ _ _ (k, 0) k 0
  simp at this
  specialize this f x
  simpa [Real.rpow_nat_cast]

-- Re-arrange as upper bound of a function by a function.
-- TODO: Eliminate this lemma? It's trivial and not that useful.
lemma norm_le_sup_Iic_seminorm_mul_one_add_norm_pow_neg (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖f x‖ ≤ 2 ^ k * sup_Iic_seminorm 𝕜 k 0 f * (1 + ‖x‖) ^ (-k : ℝ) := by
  simp
  simp [Real.rpow_neg]
  rw [mul_comm, inv_mul_eq_div]
  simp [le_div_iff']
  have : (1 + ‖x‖) ^ k * ‖f x‖ ≤ 2 ^ k * sup_Iic_seminorm 𝕜 k 0 f
  . refine pow_one_add_norm_mul_norm_le_two_pow_sup_Iic_seminorm k f x
  simpa

-- Prove that bound exists for any finite-dimensional `E`.
-- TODO: Remove dependence on `SchwartzMap.integrable`?
lemma integral_norm_le_const_mul_sup_Iic_seminorm
    {r : ℕ} (hr : FiniteDimensional.finrank ℝ E < r) (f : 𝓢(E, F)) :
    ∫ x, ‖f x‖ ≤ (2 ^ r * ∫ (x : E), (1 + ‖x‖) ^ (-r)) * sup_Iic_seminorm 𝕜 r 0 f := by
  simp
  have h_int : Integrable (fun (x : E) => (1 + ‖x‖) ^ (-r : ℝ))
  . refine integrable_one_add_norm ?_
    norm_cast
  conv => rhs; rw [mul_assoc]; rhs; rw [mul_comm]
  rw [← mul_assoc]
  rw [← integral_mul_left]
  refine integral_mono integrable.norm (h_int.const_mul _) ?_
  intro x
  simp
  rw [← Real.rpow_nat_cast]
  exact norm_le_sup_Iic_seminorm_mul_one_add_norm_pow_neg r f x

lemma toL1_add (φ θ : 𝓢(E, F)) : (φ + θ).toL1 = φ.toL1 + θ.toL1 := by rfl
lemma toL1_smul (c : 𝕜) (φ : 𝓢(E, F)) : (c • φ).toL1 = c • φ.toL1 := by rfl

-- Prove that map from `𝓢(E, F)` to `Lp F p` is continuous.
-- TODO: Generalize to Lp?
-- TODO: Extract (and generalize?) the proof of continuity?
section Def
variable (𝕜)
noncomputable def toL1_CLM' : 𝓢(E, F) →L[𝕜] Lp (α := E) F 1 where
  toLinearMap := ⟨⟨toL1, toL1_add⟩, toL1_smul⟩
  cont := by
    refine Seminorm.cont_withSeminorms_normedSpace _ (schwartz_withSeminorms 𝕜 E F) _ ?_
    simp [Seminorm.le_def]
    conv => arg 1; intro s; arg 1; intro C; intro φ  -- Rename.
    simp [NNReal.smul_def]
    generalize hk : FiniteDimensional.finrank ℝ E + 1 = k
    use Finset.Iic ⟨k, 0⟩
    have hC : 0 ≤ 2 ^ k * ∫ (x : E), (1 + ‖x‖) ^ (-k)
    . simp
      refine integral_nonneg ?_
      intro x
      simp [Real.rpow_neg]
    use ⟨_, hC⟩
    simp
    intro f
    rw [norm_toL1_eq_integral]
    rw [← sup_Iic_seminorm]
    rw [← Real.rpow_nat_cast]
    refine integral_norm_le_const_mul_sup_Iic_seminorm ?_ _
    simp [← hk]
end Def

noncomputable def toL1_CLM : 𝓢(E, F) →L[ℝ] Lp (α := E) F 1 := toL1_CLM' ℝ

/- The integral of a Schwartz map as a continuous linear map. -/
noncomputable def integralCLM' [CompleteSpace F] : 𝓢(E, F) →L[ℝ] F :=
  ContinuousLinearMap.comp L1.integralCLM toL1_CLM

section Nontrivial
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/- The integral of a Schwartz map as a continuous linear map. -/
noncomputable def integralCLM [CompleteSpace F] : 𝓢(E, F) →L[𝕜] F :=
  ContinuousLinearMap.comp (L1.integralCLM' 𝕜) (toL1_CLM' 𝕜)

end Nontrivial
end Continuous
end Integrable
end SchwartzMap


namespace TemperedDistribution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [mE : MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mE.volume.IsAddHaarMeasure]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

section Def
variable (𝕜)
-- TODO: Is this useful or will it get in the way? Should 𝕜 not be included?
abbrev _root_.TemperedDistribution := 𝓢(E, F) →L[𝕜] F
end Def

noncomputable instance instOne : One (𝓢(E, F) →L[𝕜] F) where
  one := SchwartzMap.integralCLM 𝕜

noncomputable def const (c : 𝕜) : 𝓢(E, F) →L[𝕜] F := c • (1 : 𝓢(E, F) →L[𝕜] F)

lemma const_zero : const (0 : 𝕜) = (0 : 𝓢(E, F) →L[𝕜] F) := by simp [const]
lemma const_one : const (1 : 𝕜) = (1 : 𝓢(E, F) →L[𝕜] F) := by simp [const]
lemma const_neg_one : const (-1 : 𝕜) = (-1 : 𝓢(E, F) →L[𝕜] F) := by simp [const]

-- TODO: Should we use `(n : ℝ)` with an alternative definition of `const` here?
noncomputable instance instNatCast : NatCast (𝓢(E, F) →L[𝕜] F) where
  natCast n := const (n : 𝕜)

noncomputable instance instIntCast : IntCast (𝓢(E, F) →L[𝕜] F) where
  intCast n := const (n : 𝕜)

end TemperedDistribution
