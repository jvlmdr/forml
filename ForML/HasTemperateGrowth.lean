import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped Real Complex SchwartzSpace BigOperators FourierTransform

section Basic

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Convenience lemma.
lemma Function.HasTemperateGrowth.differentiable {g : E → F} (hg : Function.HasTemperateGrowth g) :
    Differentiable ℝ g :=  hg.1.differentiable le_top

/-- Any constant function is a trivial example of `HasTemperateGrowth`. -/
lemma Function.hasTemperateGrowth_const (c : F) : Function.HasTemperateGrowth (fun _ : E => c) := by
  refine ⟨contDiff_const, ?_⟩
  intro n
  cases n with
  | zero => refine ⟨0, ‖c‖, ?_⟩; simp
  | succ n => refine ⟨0, 0, ?_⟩; simp [iteratedFDeriv_const_of_ne, Nat.succ_ne_zero]

/-- Any Schwartz function is a trivial example of `HasTemperateGrowth`. -/
lemma SchwartzMap.hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f := by
  refine ⟨f.smooth', ?_⟩
  intro n
  have hf_decay := f.decay' 0 n
  rcases hf_decay with ⟨C, hC⟩
  simp at hC
  refine ⟨0, C, ?_⟩
  simpa

end Basic


section Util

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Convenient lemma for bounding `choose` sums. -/
lemma Finset.sum_range_choose_smul_le_pow_two_smul {R : Type*} [OrderedAddCommMonoid R] [OrderedSMul ℕ R]
    {n : ℕ} {f : ℕ → R} {B : R} (h : ∀ i ∈ Finset.range (n + 1), f i ≤ B) :
    ∑ i in Finset.range (n + 1), n.choose i • f i ≤ 2 ^ n • B := by
  rw [← Nat.sum_range_choose]
  rw [Finset.sum_smul]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact smul_le_smul_of_nonneg (h i hi) (Nat.zero_le _)

/-- Convenient lemma for bounding `choose` sums.

TODO: Possible to define for general `LinearOrdered[Cancel]AddCommMonoid R`, e.g. `ℕ` and `ℤ`?
-/
lemma Finset.sum_range_choose_mul_le_pow_two_mul_real
    {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (h : ∀ i ∈ Finset.range (n + 1), f i ≤ B) :
    ∑ i in Finset.range (n + 1), n.choose i * f i ≤ 2 ^ n * B := by
  simp only [← nsmul_eq_mul]
  exact Finset.sum_range_choose_smul_le_pow_two_smul h

-- TODO: Rename/move this?
-- TODO: Maybe there is machinery in BigO to do this?
/-- Take maximum `k` and maximum `C` to obtain bounding monomial for all `i < n`. -/
lemma bound_forall_range (n : ℕ) {f : ℕ → E → ℝ}
    (h : ∀ i, i < n → ∃ (k : ℕ) (C : ℝ), ∀ x, f i x ≤ C * (1 + ‖x‖) ^ k) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i, i < n → ∀ x, f i x ≤ C * (1 + ‖x‖) ^ k := by
  induction n with
  | zero => simp; use 0
  | succ n h_ind =>
    specialize h_ind ?_  -- Feels like we shouldn't have to do this?
    . intro i hi
      refine h _ ?_
      exact lt_trans hi (Nat.lt_succ_self _)
    specialize h n (Nat.lt_succ_self _)
    rcases h with ⟨k_m, C_m, hC_m⟩
    rcases h_ind with ⟨k_i, C_i, ⟨hC_i_nonneg, hC_i⟩⟩
    refine ⟨max k_i k_m, max C_i C_m, ?_⟩
    refine And.intro (le_trans hC_i_nonneg (by simp)) ?_
    intro i hi x
    simp [Nat.lt_succ] at hi
    cases lt_or_eq_of_le hi with
    | inl hi =>
      specialize hC_i i hi x
      refine le_trans hC_i ?_
      refine mul_le_mul ?_ (pow_le_pow ?_ ?_) ?_ (le_trans hC_i_nonneg ?_) <;> simp
    | inr hi =>
      rw [hi]
      specialize hC_m x
      refine le_trans hC_m ?_
      refine mul_le_mul ?_ (pow_le_pow ?_ ?_) ?_ (le_trans hC_i_nonneg ?_) <;> simp

/-- Take maximum `k` and maximum `C` to obtain bound on derivatives of `g` for all `i < n`. -/
lemma Function.HasTemperateGrowth.bound_forall_range (n : ℕ) {f : E → F} (hf : HasTemperateGrowth f) :
    ∃ k C, 0 ≤ C ∧ ∀ i ∈ Finset.range n, ∀ (x : E), ‖iteratedFDeriv ℝ i f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  simp
  refine _root_.bound_forall_range n ?_
  intro i _
  exact hf.2 i

/-- The Fréchet derivative of a `HasTemperateGrowth` function is a `HasTemperateGrowth` function. -/
lemma Function.HasTemperateGrowth.fderiv {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth (fun x => fderiv ℝ f x) := by
  refine ⟨hf.1.fderiv_right le_top, ?_⟩
  intro n
  rcases bound_forall_range (n + 2) hf with ⟨k, C, ⟨_, hC⟩⟩
  refine ⟨k, C, ?_⟩
  intro x
  suffices : ‖iteratedFDeriv ℝ (n + 1) (fun x => f x) x‖ ≤ C * (1 + ‖x‖) ^ k
  . simpa [iteratedFDeriv_succ_eq_comp_right] using this
  refine hC (n + 1) ?_ x
  exact Finset.self_mem_range_succ (n + 1)

end Util


namespace Function

section Compose

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

-- TODO: Could this be more easily proved using BigO?
/-- The composition of two `HasTemperateGrowth` functions is a `HasTemperateGrowth` function. -/
theorem HasTemperateGrowth.comp
      {g : F → G} (hg : HasTemperateGrowth g)
      {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => g (f x) := by
  refine ⟨ContDiff.comp hg.1 hf.1, ?_⟩
  intro n
  -- Obtain `k, C` for derivatives of `g` and `f`.
  have hg_bound := hg.bound_forall_range (n + 1)
  have hf_bound := hf.bound_forall_range (n + 1)
  simp [Nat.lt_succ] at hg_bound hf_bound
  rcases hg_bound with ⟨k_g, C_g, ⟨hC_g_nonneg, hC_g⟩⟩
  rcases hf_bound with ⟨k_f, C_f, ⟨_, hC_f⟩⟩
  -- Also obtain `k, C` for f itself to bound `(1 + ‖f x‖) ^ k_g` by a power of `1 + ‖x‖`.
  have hf0 := hf.2 0
  simp at hf0
  rcases hf0 with ⟨k_f0, C_f0, hC_f0⟩

  -- Eventually need to show:
  -- `n.factorial * (C_g * (2 * max 1 C_f0 * (1 + ‖x‖) ^ k_f0) ^ k_g) * (max 1 C_f * (1 + ‖x‖) ^ k_f) ^ n ≤ C * (1 + ‖x‖) ^ k`
  -- Therefore:
  use k_f0 * k_g + k_f * n
  use n.factorial * C_g * (2 * max 1 C_f0) ^ k_g * (max 1 C_f) ^ n
  intro x

  -- Establish bounds required for `norm_iteratedFDeriv_comp_le`.
  -- First obtain a bound for `1 + ‖f x‖` to avoid a `(1 + ‖f x‖) ^ k_g` term on the left.
  have hf0 : (1 + ‖f x‖) ≤ 2 * max 1 C_f0 * (1 + ‖x‖) ^ k_f0
  . rw [mul_assoc, two_mul]
    refine add_le_add ?_ ?_
    . simp [one_le_mul_of_one_le_of_one_le]
    . exact le_trans (hC_f0 x) (by simp)
  -- Bound derivatives of `g` at `f x` by a constant `C`.
  have hC : ∀ (i : ℕ), i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C_g * (2 * max 1 C_f0 * (1 + ‖x‖) ^ k_f0) ^ k_g
  . intro i hi
    refine le_trans (hC_g i hi (f x)) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC_g_nonneg
    exact pow_le_pow_of_le_left (by simp) hf0 k_g
  -- Bound derivatives of `f` at `x` by non-zero powers of `D`.
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ (max 1 C_f * (1 + ‖x‖) ^ k_f) ^ i
  . intro i _ hi
    refine le_trans (hC_f i hi x) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (le_max_right 1 C_f) (by simp)) ?_
    refine le_self_pow ?_ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (le_max_left 1 C_f) (by simp)
  refine le_trans (norm_iteratedFDeriv_comp_le hg.1 hf.1 le_top x hC hD) ?_
  refine le_of_eq ?_
  ring_nf

end Compose


section Linear

variable {E F G 𝔸 : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Any `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
lemma hasTemperateGrowth_clm (a : E →L[ℝ] F) : HasTemperateGrowth fun x => a x := by
  refine ⟨contDiff_const.clm_apply contDiff_id, ?_⟩
  intro n
  refine ⟨1, ‖a‖, ?_⟩
  intro x
  refine le_trans (norm_iteratedFDeriv_clm_apply contDiff_const contDiff_id _ le_top) ?_
  -- Only need to consider first term.
  rw [add_comm n 1]
  rw [Finset.sum_range_add]
  simp
  rw [Finset.sum_eq_zero ?_]
  swap
  . intro i _
    rw [iteratedFDeriv_const_of_ne] <;> simp
  simp
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  cases n with
  | zero => simp
  | succ n =>
    rw [iteratedFDeriv_succ_eq_comp_right]
    cases n with
    | zero => simp; refine le_trans ContinuousLinearMap.norm_id_le (by simp)
    | succ n => simp; rw [iteratedFDeriv_const_of_ne] <;> simp

lemma HasTemperateGrowth.clm (g : F →L[ℝ] G) {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => g (f x) :=
  comp (hasTemperateGrowth_clm _) hf

section Explicit
variable (E)
lemma hasTemperateGrowth_id : HasTemperateGrowth (id : E → E) :=
  hasTemperateGrowth_clm (ContinuousLinearMap.id ℝ E)
end Explicit

lemma hasTemperateGrowth_neg : HasTemperateGrowth fun x : E => (-x) := hasTemperateGrowth_clm (-ContinuousLinearMap.id ℝ E)
lemma hasTemperateGrowth_re : HasTemperateGrowth fun x : ℂ => x.re := hasTemperateGrowth_clm Complex.reClm
lemma hasTemperateGrowth_im : HasTemperateGrowth fun x : ℂ => x.im := hasTemperateGrowth_clm Complex.imClm

lemma HasTemperateGrowth.re {f : E → ℂ} (hf : HasTemperateGrowth f) : HasTemperateGrowth fun x => (f x).re := clm Complex.reClm hf
lemma HasTemperateGrowth.im {f : E → ℂ} (hf : HasTemperateGrowth f) : HasTemperateGrowth fun x => (f x).im := clm Complex.imClm hf
lemma HasTemperateGrowth.neg {f : E → F} (hf : HasTemperateGrowth f) : HasTemperateGrowth fun x => (-f x) := clm (-ContinuousLinearMap.id ℝ F) hf

section Mul

variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

lemma hasTemperateGrowth_const_mul (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 => a * x := hasTemperateGrowth_clm (ContinuousLinearMap.mul ℝ 𝔸 a)
lemma hasTemperateGrowth_mul_const (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 => x * a := hasTemperateGrowth_clm ((ContinuousLinearMap.mul ℝ 𝔸).flip a)

lemma HasTemperateGrowth.const_mul (a : 𝔸) {f : E → 𝔸} (hf : HasTemperateGrowth f) : HasTemperateGrowth fun x => a * f x := clm (ContinuousLinearMap.mul ℝ 𝔸 a) hf
lemma HasTemperateGrowth.mul_const {f : E → 𝔸} (hf : HasTemperateGrowth f) (a : 𝔸) : HasTemperateGrowth fun x => f x * a := clm ((ContinuousLinearMap.mul ℝ 𝔸).flip a) hf

end Mul

section Div

variable [NormedDivisionRing 𝔸] [NormedAlgebra ℝ 𝔸]

lemma hasTemperateGrowth_div_const (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 => x / a := by
  simp_rw [div_eq_mul_inv]
  exact hasTemperateGrowth_mul_const a⁻¹

lemma HasTemperateGrowth.div_const {f : E → 𝔸} (hf : HasTemperateGrowth f) (a : 𝔸) : HasTemperateGrowth fun x => f x / a :=
  comp (hasTemperateGrowth_div_const a) hf

end Div

end Linear


section ParametricLinear

variable {D E F G 𝔸 : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Application of a parametric `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
lemma HasTemperateGrowth.clm_apply
    {f : D → E →L[ℝ] F} (hf : HasTemperateGrowth f)
    {g : D → E} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => (f x) (g x) := by
  refine ⟨hf.1.clm_apply hg.1, ?_⟩
  sorry

end ParametricLinear


section Add

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The addition of two `HasTemperateGrowth` functions is a `HasTemperateGrowth` function. -/
theorem HasTemperateGrowth.add
      {f : E → F} (hf : HasTemperateGrowth f)
      {g : E → F} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => f x + g x := by
  refine ⟨ContDiff.add hf.1 hg.1, ?_⟩
  intro n
  -- Obtain coefficients for each function.
  rcases hf.2 n with ⟨k_f, C_f, hC_f⟩
  rcases hg.2 n with ⟨k_g, C_g, hC_g⟩
  have hC_f_nonneg : 0 ≤ C_f
  . have := le_trans (norm_nonneg _) (hC_f 0)
    simpa using this
  have hC_g_nonneg : 0 ≤ C_g
  . have := le_trans (norm_nonneg _) (hC_g 0)
    simpa using this
  use max k_f k_g
  use C_f + C_g
  intro x
  change ‖iteratedFDeriv ℝ n (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.1.of_le le_top) (hg.1.of_le le_top)]
  refine le_trans (norm_add_le _ _) ?_
  simp [add_mul]
  refine add_le_add ?_ ?_
  . refine le_trans (hC_f x) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC_f_nonneg
    exact pow_le_pow (by simp) (by simp)
  . refine le_trans (hC_g x) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC_g_nonneg
    exact pow_le_pow (by simp) (by simp)

lemma HasTemperateGrowth.sub
      {f : E → F} (hf : HasTemperateGrowth f)
      {g : E → F} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => f x - g x := by
  simp_rw [sub_eq_add_neg]
  refine add hf hg.neg

lemma HasTemperateGrowth.add_const {f : E → F} (hf : HasTemperateGrowth f) (c : F) :
    HasTemperateGrowth fun x => f x + c :=
  add hf (hasTemperateGrowth_const c)

lemma HasTemperateGrowth.const_add (c : F) {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => c + f x :=
  add (hasTemperateGrowth_const c) hf

end Add


section ConstSMul

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

example (c : 𝕜) (x : F) : c • x = (c • ContinuousLinearMap.id ℝ F) x := rfl

lemma HasTemperateGrowth.const_smul (c : 𝕜) {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => c • f x :=
  comp (hasTemperateGrowth_clm (c • ContinuousLinearMap.id ℝ F)) hf

end ConstSMul

section SMulConst

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
-- TODO: Check types; some fumbling involved.
variable [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
variable [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F] [ContinuousSMul 𝕜 F]

example (x : 𝕜) (c : F) : x • c = (ContinuousLinearMap.id ℝ 𝕜).smulRight c x := rfl

lemma HasTemperateGrowth.smul_const {f : E → 𝕜} (hf : HasTemperateGrowth f) (c : F) :
    HasTemperateGrowth fun x => f x • c :=
  comp (hasTemperateGrowth_clm ((ContinuousLinearMap.id ℝ 𝕜).smulRight c)) hf

end SMulConst


section Bilinear

variable {E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma HasTemperateGrowth.bilin
    (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} (hf : HasTemperateGrowth f)
    {g : E → G} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => B (f x) (g x) :=
  clm_apply (clm B hf) hg

end Bilinear


section SMul

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

example (x : ℝ) (y : F) : x • y = ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ) y x := rfl

-- TODO: Add `mul`.
-- TODO: Add `smulRightL` that generalizes beyond `ℝ` with `S →[ℝ] ℝ` applied to lhs?
lemma HasTemperateGrowth.smul
    {f : E → ℝ} (hf : HasTemperateGrowth f)
    {g : E → F} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => f x • g x :=
  bilin (ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)) hg hf

end SMul

end Function  -- namespace


section IteratedDeriv
-- Some useful lemmata for `iteratedDeriv` that avoid passing through `iteratedFDeriv`.
-- TODO: Is it overkill to declare these?
-- TODO: Typeclasses might not be perfect; some trial and error involved.

variable {𝕜 𝕜' F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma iteratedDeriv_neg_apply {n : ℕ} {f : 𝕜 → F} :
    iteratedDeriv n (fun x => -f x) x = -iteratedDeriv n f x := by
  change iteratedDeriv n (-f) x = _
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp [iteratedFDeriv_neg_apply]

lemma iteratedDeriv_const_mul_apply {n : ℕ} (a : 𝕜') {f : 𝕜 → 𝕜'} (hf : ContDiff 𝕜 n f) {x : 𝕜} :
    iteratedDeriv n (fun x => a * f x) x = a * iteratedDeriv n f x := by
  change iteratedDeriv n (a • f) x = _
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp [iteratedFDeriv_const_smul_apply hf]

lemma iteratedDeriv_mul_const_apply {n : ℕ} (a : 𝕜') {f : 𝕜 → 𝕜'} (hf : ContDiff 𝕜 n f) {x : 𝕜} :
    iteratedDeriv n (fun x => f x * a) x = iteratedDeriv n f x * a := by
  simp_rw [mul_comm _ a]
  exact iteratedDeriv_const_mul_apply a hf

end IteratedDeriv


section Complex

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma Complex.contDiff_exp_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (x • I) :=
  (contDiff_id.smul contDiff_const).cexp

lemma Complex.contDiff_exp_neg_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (-(x • I)) :=
  (contDiff_id.smul contDiff_const).neg.cexp

lemma ContDiff.cexp_real_smul_I {n : ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => cexp (f x • Complex.I) :=
  Complex.contDiff_exp_real_smul_I.comp hf

lemma Complex.deriv_exp_real_smul_I {x : ℝ} :
    deriv (fun x : ℝ => exp (x • I)) x = I * exp (x • I) := by
  change deriv (exp ∘ fun x => (x • I)) x = I * exp (x • I)
  rw [deriv.comp _ differentiableAt_exp (differentiableAt_id.smul_const I)]
  rw [Complex.deriv_exp]
  rw [mul_comm]
  congr
  rw [deriv_smul_const differentiableAt_id]
  simp

lemma Complex.iteratedDeriv_exp_real_smul_I {n : ℕ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp (x • I)) x = HPow.hPow I n * exp (x • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_real_smul_I]
    rw [iteratedDeriv_const_mul_apply I contDiff_exp_real_smul_I]
    rw [hi, mul_assoc]

lemma Differentiable.deriv_cexp_real_smul_I {f : 𝕜 → ℝ} (hf : Differentiable 𝕜 f) {x : 𝕜} :
    deriv (fun x => cexp (f x • Complex.I)) x = cexp (f x • Complex.I) * (deriv f x • Complex.I) := by
  change deriv (cexp ∘ (fun x => f x • Complex.I)) x = _
  rw [deriv.comp _ Complex.differentiableAt_exp (hf.smul_const Complex.I).differentiableAt]
  rw [deriv_smul_const hf.differentiableAt]
  simp

-- TODO: Remove? No longer needed.
-- TODO: Would it make sense to provide this for `𝕜`-linearity?
/-- Analogy of `fderiv_exp` for complex exponential. -/
lemma fderiv_cexp_real {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => cexp (f x)) x = cexp (f x) • fderiv ℝ f x := by
  change fderiv ℝ (cexp ∘ f) x = _
  rw [fderiv.comp x Complex.differentiable_exp.differentiableAt hf]
  rw [(Complex.hasStrictFDerivAt_exp_real (f x)).hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.one_def]

lemma Complex.hasTemperateGrowth_exp_real_smul_I :
    Function.HasTemperateGrowth fun x : ℝ => exp (x • I) := by
  refine ⟨contDiff_exp_real_smul_I, ?_⟩
  intro n
  refine ⟨n, 1, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedDeriv_exp_real_smul_I]
  simp
  exact one_le_pow_of_one_le (by simp) n

/--
The imaginary exponential of a real-valued `HasTemperateGrowth` function is a `HasTemperateGrowth` function.

TODO: Prove for more general `g : E → ℂ` with `|(g x).re| ≤ 1`?
-/
lemma Function.HasTemperateGrowth.cexp_real_smul_I {f : E → ℝ} (hf : Function.HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => cexp (f x • Complex.I) :=
  Complex.hasTemperateGrowth_exp_real_smul_I.comp hf

end Complex


section RealFourier

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma Real.hasTemperateGrowth_cos : Function.HasTemperateGrowth cos := by
  simp_rw [cos, Complex.cos]
  refine ((Function.HasTemperateGrowth.add ?_ ?_).div_const 2).re
  . simp_rw [← Complex.real_smul]
    exact Complex.hasTemperateGrowth_exp_real_smul_I
  norm_cast
  simp_rw [← Complex.real_smul]
  exact Function.hasTemperateGrowth_neg.cexp_real_smul_I

lemma Real.hasTemperateGrowth_sin : Function.HasTemperateGrowth sin := by
  simp_rw [sin, Complex.sin]
  refine (((Function.HasTemperateGrowth.sub ?_ ?_).mul_const Complex.I).div_const 2).re
  . norm_cast
    simp_rw [← Complex.real_smul]
    exact Function.hasTemperateGrowth_neg.cexp_real_smul_I
  simp_rw [← Complex.real_smul]
  exact Complex.hasTemperateGrowth_exp_real_smul_I

lemma Real.hasTemperateGrowth_fourierChar :
    Function.HasTemperateGrowth fun x : ℝ => fourierChar[x] := by
  simp [fourierChar_apply]
  norm_cast
  simp_rw [← Complex.real_smul]
  exact (Function.hasTemperateGrowth_const_mul (2 * π)).cexp_real_smul_I

lemma Function.HasTemperateGrowth.cos {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.cos (f x) := Real.hasTemperateGrowth_cos.comp hf

lemma Function.HasTemperateGrowth.sin {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.sin (f x) := Real.hasTemperateGrowth_sin.comp hf

lemma Function.HasTemperateGrowth.realFourierChar {f : E → ℝ} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => Real.fourierChar[f x] := Real.hasTemperateGrowth_fourierChar.comp hf

-- TODO: Too trivial to declare? May be useful for Fourier transform.

lemma Real.hasTemperateGrowth_fourierChar_mul_const (w : ℝ) : Function.HasTemperateGrowth fun v : ℝ => fourierChar[v * w] :=
  (Function.hasTemperateGrowth_mul_const w).realFourierChar

lemma Real.hasTemperateGrowth_fourierChar_neg_mul_const (w : ℝ) : Function.HasTemperateGrowth fun v : ℝ => fourierChar[-(v * w)] :=
  (Function.hasTemperateGrowth_mul_const w).neg.realFourierChar

end RealFourier


section VectorFourier

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def Real.innerL (v : E) : E →L[ℝ] ℝ := isBoundedBilinearMap_inner.toContinuousLinearMap v
noncomputable def Real.innerR (w : E) : E →L[ℝ] ℝ := isBoundedBilinearMap_inner.toContinuousLinearMap.flip w

lemma innerL_apply {v w : E} : Real.innerL v w = inner v w := rfl
lemma innerR_apply {v w : E} : Real.innerR w v = inner v w := rfl

-- TODO: Too trivial to declare? May be useful for Fourier transform.

lemma Real.hasTemperateGrowth_inner_const (w : E) :
    Function.HasTemperateGrowth fun v : E => (inner v w : ℝ) :=
  Function.hasTemperateGrowth_clm (innerR w)

lemma Real.hasTemperateGrowth_vectorFourierChar_inner_const (w : E) :
    Function.HasTemperateGrowth fun v : E => fourierChar[(inner v w : ℝ)] :=
  (hasTemperateGrowth_inner_const w).realFourierChar

lemma Real.hasTemperateGrowth_vectorFourierChar_neg_inner_const (w : E) :
    Function.HasTemperateGrowth fun v : E => fourierChar[(-inner v w : ℝ)] :=
  (hasTemperateGrowth_inner_const w).neg.realFourierChar

end VectorFourier
