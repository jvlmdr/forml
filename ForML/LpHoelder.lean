import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory

open scoped Real NNReal ENNReal

section ENNReal

-- def IsConjugateExponent (p q : ℝ≥0∞) : Prop := p⁻¹ + q⁻¹ = 1

noncomputable def conjugateExponent (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

variable {p q : ℝ≥0∞}

lemma ENNReal_one_le_conjugateExponent : 1 ≤ conjugateExponent p := by
  simp [conjugateExponent]

lemma ENNReal_one_le_of_conjugate (hpq : p⁻¹ + q⁻¹ = 1) : 1 ≤ p := by
  rw [← ENNReal.inv_le_inv, inv_one]
  simp [← hpq]

lemma ENNReal_one_le_of_conjugate' (hpq : p⁻¹ + q⁻¹ = 1) : 1 ≤ q := by
  rw [add_comm] at hpq
  exact ENNReal_one_le_of_conjugate hpq

/- Like `Real.IsConjugateExponent.toReal` for `ℝ≥0∞`.

It is not necessary to include `1 ≤ p` in the definition.
-/
lemma ENNReal_conjugate_iff : p⁻¹ + q⁻¹ = 1 ↔ (1 ≤ p ∧ q = conjugateExponent p) := by
  rw [conjugateExponent]
  rw [← inv_eq_iff_eq_inv]
  refine Iff.intro ?_ ?_
  . intro h
    have hp : 1 ≤ p := ENNReal_one_le_of_conjugate h
    refine And.intro hp ?_
    rw [← h]
    rw [ENNReal.add_sub_cancel_left]
    rw [← lt_top_iff_ne_top]
    simp
    exact lt_of_lt_of_le zero_lt_one hp
  . simp
    intro hp h
    rw [h]
    rw [add_tsub_cancel_iff_le]
    simp
    exact hp

/- Either one of `p`, `q` is `⊤`, or neither are.
Lighter version of `ENNReal_conjugate_cases`.
-/
lemma ENNReal_conjugate_cases' (h : p⁻¹ + q⁻¹ = 1) :
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

/- Possible pairs are `(1, ⊤)`, `(⊤, 1)`, or `(p, q)` with `1 < p, q < ⊤`. -/
lemma ENNReal_conjugate_cases (h : p⁻¹ + q⁻¹ = 1) :
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
          exact lt_of_lt_of_le zero_lt_one (ENNReal_one_le_of_conjugate h)
        . rwa [ENNReal.inv_ne_zero]
      . rw [add_comm]
        refine ENNReal.lt_add_right ?_ ?_
        . rw [← lt_top_iff_ne_top]
          simp
          exact lt_of_lt_of_le zero_lt_one (ENNReal_one_le_of_conjugate' h)
        . rwa [ENNReal.inv_ne_zero]

lemma ENNReal_isConjugateExponent_toReal (hpq : p⁻¹ + q⁻¹ = 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    Real.IsConjugateExponent (p.toNNReal) (q.toNNReal) := by
  cases ENNReal_conjugate_cases hpq with
  | inr hpq =>
    simp at *
    cases hpq with
    | inl hpq => rcases hpq with ⟨_, hq'⟩; contradiction
    | inr hpq => rcases hpq with ⟨hp', _⟩; contradiction
  | inl hpq =>
    rcases hpq with ⟨hp, hq⟩
    have hp' : p ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal_one_le_of_conjugate hpq
    have hq' : q ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal_one_le_of_conjugate' hpq
    -- Move to NNReal for coercion to ℝ.
    cases p with | none => contradiction | some p =>
    cases q with | none => contradiction | some q =>
    simp at *
    refine Real.IsConjugateExponent.mk ?_ ?_
    . norm_cast
    . rw [← ENNReal.coe_inv hp', ← ENNReal.coe_inv hq'] at hpq
      norm_cast at hpq
      simp
      norm_cast

end ENNReal


variable {E : Type*} [MeasurableSpace E]
variable {μ : Measure E}
variable {p q : ℝ≥0∞} {hpq : p⁻¹ + q⁻¹ = 1}

-- TODO: Think of a namespace? Follow e.g. `NNReal.lintegral_mul_le_Lp_mul_Lq`?
section Mul

variable {𝕜 : Type*} [NormedRing 𝕜]
-- Use `NormedRing` because we need `NormedAddCommGroup` for `Memℒp` and
-- `NonUnitalSeminormedRing` for `norm_mul_le`.

section Measurable
variable {f : E → 𝕜} (hf : AEStronglyMeasurable f μ)
variable {g : E → 𝕜} (hg : AEStronglyMeasurable g μ)
variable (hpq)

/- Hölder's inequality for functions.
Compared to `NNReal.lintegral_mul_le_Lp_mul_Lq`, it supports `p, q ∈ [1, ∞]`
and `NormedRing` rather than `NNReal`.

Depends on `NNReal.lintegral_mul_le_Lp_mul_Lq`.
-/
lemma snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq :
    snorm (f * g) 1 μ ≤ snorm f p μ * snorm g q μ := by
  cases ENNReal_conjugate_cases hpq with
  | inl hpq =>
    rcases hpq with ⟨hp, hq⟩
    have hp' : p ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal_one_le_of_conjugate hpq
    have hq' : q ≠ 0
    . refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
      exact ENNReal_one_le_of_conjugate' hpq
    rw [snorm_eq_lintegral_rpow_nnnorm hp' hp.right]
    rw [snorm_eq_lintegral_rpow_nnnorm hq' hq.right]
    rw [snorm_one_eq_lintegral_nnnorm]
    simp [-one_div]
    refine le_trans ?_ (NNReal.lintegral_mul_le_Lp_mul_Lq ?_ ?_ ?_)
    rotate_left
    . exact ENNReal_isConjugateExponent_toReal hpq hp.right hq.right
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

section Memℒp
variable {f : E → 𝕜} (hf : Memℒp f p μ)
variable {g : E → 𝕜} (hg : Memℒp g q μ)
variable (hpq)

/- Use Hölder's inequality for functions to show that `f * g` is in `L1`. -/
lemma memL1_Lp_mul_Lq  : Memℒp (f * g) 1 μ := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.mul hf.aestronglyMeasurable hg.aestronglyMeasurable
  . refine lt_of_le_of_lt (snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_) ?_
    . exact hf.aestronglyMeasurable
    . exact hg.aestronglyMeasurable
    exact ENNReal.mul_lt_top hf.snorm_ne_top hg.snorm_ne_top

end Memℒp

section Lp
variable {f : Lp (α := E) 𝕜 p μ}
variable {g : Lp (α := E) 𝕜 q μ}

section Def
variable (hpq f g)

/- Constructs an element of `L1` from `f * g` using Hölder's inequality for functions. -/
noncomputable def L1_of_mul : Lp (α := E) 𝕜 1 μ :=
  Memℒp.toLp (f * g) (memL1_Lp_mul_Lq hpq (Lp.memℒp f) (Lp.memℒp g))

end Def

lemma coeFn_L1_of_mul :
    L1_of_mul hpq f g =ᵐ[μ] f * g := by
  simp [L1_of_mul, Memℒp.coeFn_toLp]

/- Hölder's inequality for `f * g` expressed using `Lp` norms. -/
lemma norm_L1_of_mul_le_norm_Lp_mul_norm_Lq :
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
  rw [snorm_congr_ae coeFn_L1_of_mul]
  refine snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_
  . exact (Lp.memℒp f).aestronglyMeasurable
  . exact (Lp.memℒp g).aestronglyMeasurable

end Lp

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
variable (hpq)

/- Hölder's inequality for functions.
Depends on `snorm_mul_L1_le_snorm_Lp_mul_snorm_Lq`.
-/
lemma snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq :
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
variable (hpq)

/- Use Hölder's inequality for functions to show that `f • g` is in `L1`. -/
lemma memL1_Lp_smul_Lq  : Memℒp (f • g) 1 μ := by
  refine And.intro ?_ ?_
  . exact AEStronglyMeasurable.smul hf.aestronglyMeasurable hg.aestronglyMeasurable
  . refine lt_of_le_of_lt (snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_) ?_
    . exact hf.aestronglyMeasurable
    . exact hg.aestronglyMeasurable
    exact ENNReal.mul_lt_top hf.snorm_ne_top hg.snorm_ne_top

end Memℒp

section Lp
variable {f : Lp (α := E) 𝕜 p μ}
variable {g : Lp (α := E) F q μ}

section Def
variable (hpq f g)

/- Constructs an element of `L1` from `f • g` using Hölder's inequality for functions. -/
noncomputable def L1_of_Lp_smul_Lq : Lp (α := E) F 1 μ :=
  Memℒp.toLp ((f : E → 𝕜) • (g : E → F)) (memL1_Lp_smul_Lq hpq (Lp.memℒp f) (Lp.memℒp g))

end Def

lemma coeFn_L1_of_Lp_smul_Lq :
    L1_of_Lp_smul_Lq hpq f g =ᵐ[μ] (f : E → 𝕜) • (g : E → F) := by
  simp [L1_of_Lp_smul_Lq, Memℒp.coeFn_toLp]

/- Hölder's inequality for `f • g` expressed using `Lp` norms. -/
lemma norm_L1_of_smul_le_norm_Lp_mul_norm_Lq :
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
  rw [snorm_congr_ae coeFn_L1_of_Lp_smul_Lq]
  refine snorm_smul_L1_le_snorm_Lp_mul_snorm_Lq hpq ?_ ?_
  . exact (Lp.memℒp f).aestronglyMeasurable
  . exact (Lp.memℒp g).aestronglyMeasurable

end Lp

end SMul
