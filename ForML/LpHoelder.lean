import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory

open scoped Real NNReal ENNReal

namespace ENNReal

-- def IsConjExponent (p q : ℝ≥0∞) : Prop := p⁻¹ + q⁻¹ = 1

-- Use `(1 - p⁻¹)⁻¹` rather than `p / (p - 1)` to avoid `∞ / (∞ - 1)`.
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

variable {p q : ℝ≥0∞}

lemma one_le_conjExponent : 1 ≤ conjExponent p := by
  simp [conjExponent]

instance one_le_conjExponent' : Fact (1 ≤ conjExponent p) :=
  ⟨one_le_conjExponent⟩

@[simp]
lemma sub_right_eq_self {a b : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) : a - b = a ↔ b = 0 := by
  refine Iff.intro ?_ ?_
  . intro h
    suffices hba : b ≤ a
    . simpa [← ENNReal.sub_right_inj ha' hba]
    have hba : 0 < a - b
    . simpa [h, zero_lt_iff]
    simp at hba
    exact hba.le
  . intro h
    simp [h]

-- Uses `sub_right_eq_self` with `a = 1`.
lemma conjExponent_eq_one : conjExponent p = 1 ↔ p = ⊤ := by
  simp [conjExponent, inv_eq_iff_eq_inv]

lemma conjExponent_eq_top (hp : 1 ≤ p) : conjExponent p = ⊤ ↔ p = 1 := by
  rw [conjExponent, inv_eq_top, tsub_eq_zero_iff_le, ENNReal.one_le_inv]
  exact LE.le.le_iff_eq hp

lemma one_le_of_conjugate (hpq : p⁻¹ + q⁻¹ = 1) : 1 ≤ p := by
  rw [← ENNReal.inv_le_inv, inv_one]
  simp [← hpq]

lemma one_le_of_conjugate' (hpq : p⁻¹ + q⁻¹ = 1) : 1 ≤ q := by
  rw [add_comm] at hpq
  exact one_le_of_conjugate hpq

/-- Like `Real.IsConjExponent.toReal` for `ℝ≥0∞`.

Note that it is not necessary to include `1 ≤ p` in the definition `p⁻¹ + q⁻¹ = 1`.
-/
lemma conjugate_iff : (1 ≤ p ∧ q = conjExponent p) ↔ p⁻¹ + q⁻¹ = 1 := by
  rw [conjExponent]
  rw [← inv_eq_iff_eq_inv]
  refine Iff.intro ?_ ?_
  . simp
    intro hp h
    rw [h]
    rw [add_tsub_cancel_iff_le]
    simp
    exact hp
  . intro h
    have hp : 1 ≤ p := one_le_of_conjugate h
    refine And.intro hp ?_
    rw [← h]
    rw [ENNReal.add_sub_cancel_left]
    rw [← lt_top_iff_ne_top]
    simp
    exact lt_of_lt_of_le zero_lt_one hp

lemma conjugate_conjExponent (hp : 1 ≤ p) : p⁻¹ + (conjExponent p)⁻¹ = 1 := by
  simp [conjExponent]
  simp [add_tsub_cancel_iff_le]
  exact hp

/-- Lighter version of `conjugate_cases`. -/
lemma conjugate_cases' (h : p⁻¹ + q⁻¹ = 1) :
    (p ≠ ⊤ ∧ q ≠ ⊤) ∨ (p = 1 ∧ q = ⊤) ∨ (p = ⊤ ∧ q = 1) := by
  cases p with
  | none =>
    simpa [inv_eq_iff_eq_inv] using h
  | some p =>
    cases q with
    | none =>
      simpa [inv_eq_iff_eq_inv] using h
    | some q =>
      simp

/-- Possible pairs are `(1, ⊤)`, `(⊤, 1)`, or `(p, q)` with `1 < p, q < ⊤`. -/
lemma conjugate_cases (h : p⁻¹ + q⁻¹ = 1) :
    ((1 < p ∧ p ≠ ⊤) ∧ (1 < q ∧ q ≠ ⊤)) ∨ (p = 1 ∧ q = ⊤) ∨ (p = ⊤ ∧ q = 1) := by
  cases eq_or_lt_of_le (le_top : p ≤ ⊤) with
  | inl hp =>
    simp [hp] at h ⊢
    simpa [inv_eq_iff_eq_inv] using h
  | inr hp =>
    cases eq_or_lt_of_le (le_top : q ≤ ⊤) with
    | inl hq =>
      simp [hq] at h ⊢
      simpa [inv_eq_iff_eq_inv] using h
    | inr hq =>
      refine Or.inl ?_
      simp [← lt_top_iff_ne_top, hp, hq]
      simp_rw [← ENNReal.inv_lt_one]
      rw [← h]
      rw [lt_top_iff_ne_top] at hp hq
      refine And.intro ?_ ?_
      . refine ENNReal.lt_add_right ?_ ?_
        . rw [← lt_top_iff_ne_top]
          simp
          exact lt_of_lt_of_le zero_lt_one (one_le_of_conjugate h)
        . rwa [ENNReal.inv_ne_zero]
      . rw [add_comm]
        refine ENNReal.lt_add_right ?_ ?_
        . rw [← lt_top_iff_ne_top]
          simp
          exact lt_of_lt_of_le zero_lt_one (one_le_of_conjugate' h)
        . rwa [ENNReal.inv_ne_zero]

/-- Obtain `Real.IsConjExponent` when both `p` and `q` are finite. -/
lemma isConjugateExponent_toReal (hpq : p⁻¹ + q⁻¹ = 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    Real.IsConjExponent (p.toNNReal) (q.toNNReal) := by
  cases conjugate_cases hpq with
  | inr hpq =>
    simp at *
    cases hpq with
    | inl hpq => rcases hpq with ⟨_, hq'⟩; contradiction
    | inr hpq => rcases hpq with ⟨hp', _⟩; contradiction
  | inl hpq =>
    rcases hpq with ⟨hp, hq⟩
    have hp' : p ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact one_le_of_conjugate hpq
    have hq' : q ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact one_le_of_conjugate' hpq
    -- Move to NNReal for coercion to ℝ.
    cases p with | none => contradiction | some p =>
    cases q with | none => contradiction | some q =>
    simp at *
    constructor
    . norm_cast
    . rw [← ENNReal.coe_inv hp', ← ENNReal.coe_inv hq'] at hpq
      norm_cast at hpq

end ENNReal


variable {E : Type*} [MeasurableSpace E]
variable {μ : Measure E}
variable {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1)

-- TODO: Think of a namespace? Follow e.g. `NNReal.lintegral_mul_le_Lp_mul_Lq`?
section Mul

variable {𝕜 : Type*} [NormedRing 𝕜]
-- Use `NormedRing` because we need `NormedAddCommGroup` for `Memℒp` and
-- `NonUnitalSeminormedRing` for `norm_mul_le`.

section Measurable
variable {f : E → 𝕜} (hf : AEStronglyMeasurable f μ)
variable {g : E → 𝕜} (hg : AEStronglyMeasurable g μ)

/-- **Hölder's inequality** for functions.

Compared to `NNReal.lintegral_mul_le_Lp_mul_Lq`, this theorem supports
`p, q ∈ [1, ∞]` inclusive, and `NormedRing` rather than `NNReal`.
-/
theorem snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq :
    snorm (f * g) 1 μ ≤ snorm f p μ * snorm g q μ := by
  cases ENNReal.conjugate_cases hpq with
  | inl hpq =>
    rcases hpq with ⟨hp, hq⟩
    have hp' : p ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal.one_le_of_conjugate hpq
    have hq' : q ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal.one_le_of_conjugate' hpq
    rw [snorm_eq_lintegral_rpow_nnnorm hp' hp.right]
    rw [snorm_eq_lintegral_rpow_nnnorm hq' hq.right]
    rw [snorm_one_eq_lintegral_nnnorm]
    simp [-one_div]
    refine le_trans ?_ (NNReal.lintegral_mul_le_Lp_mul_Lq ?_ ?_ ?_)
    rotate_left
    . exact ENNReal.isConjugateExponent_toReal hpq hp.right hq.right
    . exact hf.nnnorm.aemeasurable
    . exact hg.nnnorm.aemeasurable
    simp
    refine lintegral_mono ?_
    intro x
    simp
    norm_cast
    exact nnnorm_mul_le (f x) (g x)

  | inr hpq =>
    cases hpq with
    | inl hpq =>
      simp [hpq.left, hpq.right, -snorm_exponent_top] at *
      refine snorm_le_snorm_mul_snorm_top 1 hf g (fun u v => u * v) ?_
      refine Filter.eventually_of_forall ?_
      intro x
      simp
      exact nnnorm_mul_le (f x) (g x)
    | inr hpq =>
      simp [hpq.left, hpq.right, -snorm_exponent_top] at *
      refine snorm_le_snorm_top_mul_snorm 1 f hg (fun u v => u * v) ?_
      refine Filter.eventually_of_forall ?_
      intro x
      simp
      exact nnnorm_mul_le (f x) (g x)

end Measurable

end Mul


-- TODO: Think of a namespace? Follow e.g. `NNReal.lintegral_mul_le_Lp_mul_Lq`?
section SMul

variable {𝕜 : Type*} [NormedAddCommGroup 𝕜]
variable {F : Type*} [NormedAddCommGroup F]
-- TODO: Replace these with something more general that includes above?
-- `NormedSpace 𝕜 F` with `NormedField 𝕜` could work, but it seems less general
-- as it requires that `‖c • x‖ ≤ ‖c‖ * ‖x‖` holds with equality.
variable [SMulZeroClass 𝕜 F] [BoundedSMul 𝕜 F]

section Measurable
variable {f : E → 𝕜} (hf : AEStronglyMeasurable f μ)
variable {g : E → F} (hg : AEStronglyMeasurable g μ)

/-- **Hölder's inequality** for `f • g`. -/
theorem snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq :
    snorm (f • g) 1 μ ≤ snorm f p μ * snorm g q μ := by
  -- Convert to multiplication of norms and use `snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq`.
  suffices : snorm (fun x => ‖f x • g x‖) 1 μ ≤ snorm (fun x => ‖f x‖ * ‖g x‖) 1 μ
  . rw [← snorm_norm (f • g), ← snorm_norm f, ← snorm_norm g]
    refine le_trans this ?_
    exact snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq hpq hf.norm hg.norm
  simp
  refine snorm_mono ?_
  simp
  intro x
  exact norm_smul_le (f x) (g x)

end Measurable

section Memℒp
variable {f : E → 𝕜} (hf : Memℒp f p μ)
variable {g : E → F} (hg : Memℒp g q μ)

/-- Uses Hölder's inequality to show that `f • g` is in `L1`. -/
theorem memL1_Lp_smul_Lq  : Memℒp (f • g) 1 μ := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.smul hf.aestronglyMeasurable hg.aestronglyMeasurable
  . refine lt_of_le_of_lt (snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_) ?_
    . exact hf.aestronglyMeasurable
    . exact hg.aestronglyMeasurable
    exact ENNReal.mul_lt_top hf.snorm_ne_top hg.snorm_ne_top

lemma integrable_Lp_smul_Lq  : Integrable (f • g) μ := by
  rw [← memℒp_one_iff_integrable]
  exact memL1_Lp_smul_Lq hpq hf hg

end Memℒp

section Lp
variable {f : Lp 𝕜 p μ}
variable {g : Lp F q μ}

section Def
variable (f g)

/-- Constructs an element of `L1` from `f • g` using Hölder's inequality for functions. -/
noncomputable def L1_of_Lp_smul_Lq : Lp F 1 μ :=
  Memℒp.toLp ((f : E → 𝕜) • (g : E → F)) (memL1_Lp_smul_Lq hpq (Lp.memℒp f) (Lp.memℒp g))

end Def

lemma coeFn_L1_of_Lp_smul_Lq :
    L1_of_Lp_smul_Lq hpq f g =ᵐ[μ] (f : E → 𝕜) • (g : E → F) := by
  simp [L1_of_Lp_smul_Lq, Memℒp.coeFn_toLp]

/-- **Hölder's inequality** for `f • g`, expressed using `Lp` norms. -/
theorem norm_L1_of_smul_le_norm_Lp_mul_norm_Lq :
    ‖L1_of_Lp_smul_Lq hpq f g‖ ≤ ‖f‖ * ‖g‖ := by
  -- Combine finiteness and boundedness.
  generalize hξ : L1_of_Lp_smul_Lq hpq f g = ξ
  simp [Lp.norm_def]
  rw [← ENNReal.toReal_mul]
  rw [ENNReal.toReal_le_toReal]
  rotate_left
  . exact Lp.snorm_ne_top _
  . exact ENNReal.mul_ne_top (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)
  -- Need to propagate through the `AEEqFun` of `Memℒp.toLp`; use `snorm_congr_ae`.
  rw [← hξ]
  rw [snorm_congr_ae (coeFn_L1_of_Lp_smul_Lq hpq)]
  refine snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_
  . exact (Lp.memℒp f).aestronglyMeasurable
  . exact (Lp.memℒp g).aestronglyMeasurable

end Lp

end SMul


-- TODO: Could reduce duplication by defining a general version of the above.
-- However, it might be easier to just copy it for now.
section Mul

variable {𝕜 : Type*} [NormedRing 𝕜]

section Memℒp
variable {f : E → 𝕜} (hf : Memℒp f p μ)
variable {g : E → 𝕜} (hg : Memℒp g q μ)

/-- Uses Hölder's inequality for functions to show that `f * g` is in `L1`. -/
theorem memL1_Lp_mul_Lq  : Memℒp (f * g) 1 μ := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.mul hf.aestronglyMeasurable hg.aestronglyMeasurable
  . refine lt_of_le_of_lt (snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_) ?_
    . exact hf.aestronglyMeasurable
    . exact hg.aestronglyMeasurable
    exact ENNReal.mul_lt_top hf.snorm_ne_top hg.snorm_ne_top

lemma integrable_Lp_mul_Lq  : Integrable (f * g) μ := by
  rw [← memℒp_one_iff_integrable]
  exact memL1_Lp_mul_Lq hpq hf hg

end Memℒp

section Lp
variable {f : Lp 𝕜 p μ}
variable {g : Lp 𝕜 q μ}

section Def
variable (f g)

/-- Constructs an element of `L1` from `f * g` using Hölder's inequality for functions. -/
noncomputable def L1_of_mul : Lp 𝕜 1 μ :=
  Memℒp.toLp (f * g) (memL1_Lp_mul_Lq hpq (Lp.memℒp f) (Lp.memℒp g))

end Def

lemma coeFn_L1_of_mul :
    L1_of_mul hpq f g =ᵐ[μ] f * g := by
  simp [L1_of_mul, Memℒp.coeFn_toLp]

/-- **Hölder's inequality** for `f * g`, expressed using `Lp` norms. -/
theorem norm_L1_of_mul_le_norm_Lp_mul_norm_Lq :
    ‖L1_of_mul hpq f g‖ ≤ ‖f‖ * ‖g‖ := by
  -- Combine finiteness and boundedness.
  generalize hξ : L1_of_mul hpq f g = ξ
  simp [Lp.norm_def]
  rw [← ENNReal.toReal_mul]
  rw [ENNReal.toReal_le_toReal]
  rotate_left
  . exact Lp.snorm_ne_top _
  . exact ENNReal.mul_ne_top (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)
  -- Need to propagate through the `AEEqFun` of `Memℒp.toLp`; use `snorm_congr_ae`.
  rw [← hξ]
  rw [snorm_congr_ae (coeFn_L1_of_mul hpq)]
  refine snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_
  . exact (Lp.memℒp f).aestronglyMeasurable
  . exact (Lp.memℒp g).aestronglyMeasurable

end Lp

end Mul
