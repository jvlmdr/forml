import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped Real Complex SchwartzSpace BigOperators

section Basic

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Function.HasTemperateGrowth.differentiable {g : E → F} (hg : Function.HasTemperateGrowth g) :
    Differentiable ℝ g :=  hg.1.differentiable le_top

/-- Any constant function is a trivial example of `HasTemperateGrowth`. -/
lemma Function.hasTemperateGrowth_const {c : F} : Function.HasTemperateGrowth (fun (_ : E) => c) := by
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

-- Require `Nontrivial` for `ContinuousLinearMap.norm_id`.
section Explicit
variable (E)
lemma Function.hasTemperateGrowth_id [Nontrivial E] : Function.HasTemperateGrowth (id : E → E) := by
  refine ⟨contDiff_id, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  cases n with
  | zero => simp
  | succ n =>
    cases n <;> simp [iteratedFDeriv_succ_eq_comp_right]
end Explicit

/-- Any `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
lemma Function.HasTemperateGrowth.clm [Nontrivial E] {a : E →L[ℝ] F} : Function.HasTemperateGrowth fun x => a x := by
  constructor
  . exact ContDiff.clm_apply contDiff_const contDiff_id
  . intro n
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
    -- TODO: Could re-use result of `hasTemperateGrowth_id`?
    cases n with
    | zero => simp
    | succ n =>
      simp [iteratedFDeriv_succ_eq_comp_right]
      cases n with
      | zero => simp
      | succ n =>
        rw [iteratedFDeriv_const_of_ne] <;> simp

lemma Real.hasTemperateGrowth_mul_left {a : ℝ} : Function.HasTemperateGrowth fun x : ℝ => a * x := by
  constructor
  . refine ContDiff.mul contDiff_const contDiff_id
  . intro n
    refine ⟨1, |a|, ?_⟩
    intro x
    simp
    cases n with
    | zero => simp [mul_add]
    | succ n =>
      simp [iteratedFDeriv_succ_eq_comp_right]
      simp_rw [fderiv_const_mul differentiableAt_id']
      simp
      cases n with
      | zero =>
        simp
        refine le_trans (norm_smul_le _ _) ?_
        simp [mul_add]
        refine mul_nonneg (by simp) (by simp)
      | succ n =>
        rw [iteratedFDeriv_const_of_ne (by simp)]
        simp
        refine mul_nonneg (by simp) ?_
        exact add_nonneg (by simp) (by simp)

end Basic


section Differentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' ℂ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
-- `NormedAlgebra` instead of `NormedSpace` for `Complex.differentiable_exp`
variable [NormedAlgebra 𝕜 ℂ] [IsScalarTower 𝕜 𝕜' ℂ]

lemma Differentiable.cexp_smul_I {f : E → 𝕜'} (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x • (I : ℂ)) :=
  Complex.differentiable_exp.comp (hf.smul_const I)

lemma Complex.differentiable_exp_real_smul_I : Differentiable ℝ (fun x : ℝ => exp (x • I)) :=
  Differentiable.cexp_smul_I differentiable_id

end Differentiable


section IteratedDeriv
-- Some useful lemmata for `iteratedDeriv` that avoid passing through `iteratedFDeriv`.
-- TODO: Typeclasses might not be perfect; some trial and error involved.

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' ℂ]
variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' ℂ]

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


section Util

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Convenient lemma for bounding `choose` sums. -/
lemma Finset.sum_range_choose_smul_le_pow_two_smul {α : Type*} [OrderedAddCommMonoid α] [OrderedSMul ℕ α]
    {n : ℕ} {f : ℕ → α} {B : α} (h : ∀ i ∈ Finset.range (n + 1), f i ≤ B) :
    ∑ i in Finset.range (n + 1), n.choose i • f i ≤ 2 ^ n • B := by
  rw [← Nat.sum_range_choose]
  rw [Finset.sum_smul]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact smul_le_smul_of_nonneg (h i hi) (Nat.zero_le _)

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


section Compose

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

-- TODO: Could this be more easily proved using BigO?
/-- The composition of two `HasTemperateGrowth` functions is a `HasTemperateGrowth` function. -/
theorem Function.HasTemperateGrowth.comp
      {g : F → G} (hg : HasTemperateGrowth g)
      {f : E → F} (hf : HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => g (f x) := by
  refine ⟨ContDiff.comp hg.1 hf.1, ?_⟩
  intro n
  -- Obtain `k, C` for derivatives of `g` and `f`.
  have hg_bound := hg.bound_forall_range (n + 1)
  have hf_bound := hf.bound_forall_range (n + 1)
  simp [Nat.lt_succ] at hg_bound
  simp [Nat.lt_succ] at hf_bound
  rcases hg_bound with ⟨k_g, C_g, ⟨hC_g_nonneg, hC_g⟩⟩
  rcases hf_bound with ⟨k_f, C_f, ⟨_, hC_f⟩⟩
  -- Also obtain `k, C` for f itself to bound `(1 + ‖f x‖) ^ k_g` by a power of `1 + ‖x‖`.
  have hf0 := hf.2 0
  simp at hf0
  rcases hf0 with ⟨k_f0, C_f0, hC_f0⟩

  -- Eventually need to show:
  -- `n.factorial * (C_g * (2 * max 1 C_f0 * (1 + ‖x‖) ^ k_f0) ^ k_g) * (max 1 C_f * (1 + ‖x‖) ^ k_f) ^ n ≤ C * (1 + ‖x‖) ^ k`
  -- Choose `k, C` accordingly.
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


lemma Function.HasTemperateGrowth.comp_clm [Nontrivial E]
    {g : F → G} (hg : HasTemperateGrowth g) (f : E →L[ℝ] F) :
    Function.HasTemperateGrowth fun x => g (f x) :=
  comp hg clm

lemma Function.HasTemperateGrowth.clm_comp [Nontrivial F]
    (g : F →L[ℝ] G) {f : E → F} (hf : HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => g (f x) :=
  comp clm hf

end Compose


namespace Complex

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiff_exp_real_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (x • I) :=
  ContDiff.cexp (ContDiff.smul contDiff_id contDiff_const)

lemma contDiff_exp_real_neg_smul_I {n : ℕ∞} : ContDiff ℝ n fun x : ℝ => exp (-x • I) :=
  ContDiff.cexp (ContDiff.smul contDiff_neg contDiff_const)

lemma _root_.ContDiff.cexp_real_smul_I {n : ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => Complex.exp (f x • I) :=
  contDiff_exp_real_smul_I.comp hf

lemma deriv_exp_real_smul_I_apply {x : ℝ} :
    deriv (fun x : ℝ => exp (x • I)) x = I * exp (x • I) := by
  change deriv (exp ∘ fun x => (x • I)) x = I * cexp (x • I)
  rw [deriv.comp _ differentiableAt_exp (differentiableAt_id.smul_const I)]
  rw [Complex.deriv_exp]
  rw [mul_comm]
  congr
  rw [deriv_smul_const differentiableAt_id]
  simp

lemma iteratedDeriv_exp_real_smul_I_apply {n : ℕ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp (x • I)) x = HPow.hPow I n * exp (x • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_real_smul_I_apply]
    rw [iteratedDeriv_const_mul_apply I contDiff_exp_real_smul_I]
    rw [hi, mul_assoc]

lemma deriv_comp_exp_real_smul_I_apply {f : 𝕜 → ℝ} (hf : Differentiable 𝕜 f) {x : 𝕜} :
    deriv (fun x => exp (f x • I)) x = cexp (f x • I) * (deriv f x • I) := by
  change deriv (exp ∘ (fun x => f x • I)) x = _
  rw [deriv.comp _ differentiableAt_exp (hf.smul_const I).differentiableAt]
  rw [deriv_smul_const hf.differentiableAt]
  simp

-- Prove some convenience lemmata for `fun x : ℝ => exp ((a * x) • I)`.

lemma contDiff_exp_const_mul_real_smul_I {n : ℕ∞} {a : ℝ} :
    ContDiff ℝ n fun x : ℝ => exp ((a * x) • I) :=
  ContDiff.cexp_real_smul_I (contDiff_const.mul contDiff_id)

-- TODO: Use comp with CLM?
lemma deriv_exp_const_mul_real_smul_I_apply {a : ℝ} {x : ℝ} :
    deriv (fun x : ℝ => exp ((a * x) • I)) x = (a • I) * exp ((a * x) • I) := by
  rw [deriv_comp_exp_real_smul_I_apply]
  swap
  . exact differentiable_id.const_mul a
  rw [mul_comm]
  congr
  rw [deriv_const_mul _ differentiableAt_id]
  simp

-- TODO: Use comp with CLM?
lemma iteratedDeriv_exp_const_mul_real_smul_I_apply {n : ℕ} {a : ℝ} {x : ℝ} :
    iteratedDeriv n (fun x : ℝ => exp ((a * x) • I)) x = HPow.hPow (a • I) n * exp ((a * x) • I) := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [iteratedDeriv_succ', pow_succ]
    conv => lhs; arg 2; intro x
    simp only [deriv_exp_const_mul_real_smul_I_apply]
    rw [iteratedDeriv_const_mul_apply _ contDiff_exp_const_mul_real_smul_I]
    rw [hi, mul_assoc]

-- TODO: Would it make sense to provide this for `𝕜`-linearity?
/-- Analogy of `fderiv_exp` for complex exponential. -/
lemma _root_.fderiv_cexp_real {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => exp (f x)) x = cexp (f x) • fderiv ℝ f x := by
  change fderiv ℝ (exp ∘ f) x = _
  rw [fderiv.comp x differentiable_exp.differentiableAt hf]
  rw [(hasStrictFDerivAt_exp_real (f x)).hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.one_def]


-- How to write smul as application of a CLM.
example {a : ℝ} : a • I = a • (ContinuousLinearMap.id ℝ ℂ) I := rfl

-- TODO: Proof is long but should be trivial?
-- TODO: Should this hold with equality?
lemma _root_.norm_iteratedFDeriv_smul_I_le {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) {x : E} :
    ‖iteratedFDeriv ℝ n (fun x => f x • I) x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  -- Tried using `norm_iteratedFDeriv_clm_apply_const` with `norm_iteratedFDeriv_smul_le`.
  -- However, it was no easier than before; just replaced `I` with `ContinuousLinearMap.id`
  -- change ‖iteratedFDeriv ℝ n (fun x => (f x • ContinuousLinearMap.id ℝ ℂ) I) x‖ ≤ ‖iteratedFDeriv ℝ n f x‖
  -- refine le_trans (norm_iteratedFDeriv_clm_apply_const ?_ le_top) ?_
  -- . exact ContDiff.smul hf contDiff_const
  -- simp

  refine le_trans (norm_iteratedFDeriv_smul_le hf contDiff_const _ le_top) ?_
  -- All terms are zero except `i = 0`.
  -- Non-trivial due to `Fin (n - n) ≠ Fin 0`.
  -- Rewrite and flip the order of the sum to eliminate.
  rw [Finset.sum_congr rfl (g := fun i =>
      n.choose (n - i) * ‖iteratedFDeriv ℝ (n - (n - i)) f x‖ * ‖iteratedFDeriv ℝ (n - i) (fun _ => I) x‖)]
  swap
  . intro i hi
    simp at hi
    rw [Nat.choose_symm (Nat.le_of_lt_succ hi)]
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ hi)]
  rw [Finset.sum_flip (fun u =>
      n.choose u * ‖iteratedFDeriv ℝ (n - u) f x‖ * ‖iteratedFDeriv ℝ u (fun _ => I) x‖)]
  rw [add_comm n 1]
  rw [Finset.sum_range_add]
  simp  -- Yay!
  refine le_of_eq ?_
  refine Finset.sum_eq_zero ?_
  intro i _
  simp
  right
  rw [iteratedFDeriv_const_of_ne] <;> simp

/--
The imaginary exponential of a real-valued `HasTemperateGrowth` function is a `HasTemperateGrowth` function.

TODO: Prove for more general `g : E → ℂ` with `|(g x).re| ≤ 1`?
-/
theorem _root_.Function.HasTemperateGrowth.exp_real_smul_I {f : E → ℝ} (hf : Function.HasTemperateGrowth f) :
    Function.HasTemperateGrowth fun x => exp (f x • I) := by
  refine ⟨?_, ?_⟩
  . exact ContDiff.cexp_real_smul_I hf.1
  . intro n
    induction n using Nat.caseStrongInductionOn with
    | zero =>
      refine ⟨0, 1, ?_⟩
      simp
    | ind n h_ind =>
      simp [iteratedFDeriv_succ_eq_comp_right, -real_smul]
      have hf_diff := hf.1.differentiable le_top
      simp_rw [fderiv_cexp_real (hf_diff.smul_const I).differentiableAt]
      clear hf_diff

      -- Find bounding monomials for both terms for all `i`.
      have h₁ : ∃ k₁ C₁, 0 ≤ C₁ ∧ ∀ i, i < n + 1 → ∀ x, ‖iteratedFDeriv ℝ i (fun y => cexp (f y • I)) x‖ ≤ C₁ * (1 + ‖x‖) ^ k₁
      . refine _root_.bound_forall_range (n + 1) ?_
        intro i hi
        exact h_ind i (Nat.le_of_lt_succ hi)

      -- Note: Technically don't need to include case `i = 0` here.
      have h₂ : ∃ k₂ C₂, 0 ≤ C₂ ∧ ∀ i, i < n + 2 → ∀ x, ‖iteratedFDeriv ℝ i (fun y => f y • I) x‖ ≤ C₂ * (1 + ‖x‖) ^ k₂
      . refine _root_.bound_forall_range (n + 2) ?_
        intro i _
        rcases hf.2 i with ⟨k, C, hC⟩
        refine ⟨k, C, ?_⟩
        intro x
        specialize hC x
        refine le_trans ?_ hC
        exact norm_iteratedFDeriv_smul_I_le hf.1

      rcases h₁ with ⟨k₁, C₁, ⟨hC₁_nonneg, hC₁⟩⟩
      rcases h₂ with ⟨k₂, C₂, ⟨_, hC₂⟩⟩
      refine ⟨k₁ + k₂, 2 ^ n * C₁ * C₂, ?_⟩
      intro x
      refine le_trans (norm_iteratedFDeriv_smul_le ?_ ?_ _ le_top) ?_
      . exact ContDiff.cexp_real_smul_I hf.1
      . refine ContDiff.fderiv_right ?_ le_top
        exact ContDiff.smul hf.1 contDiff_const
      simp_rw [norm_iteratedFDeriv_fderiv]

      -- Now use the two bounds above.
      simp only [mul_assoc]
      simp only [← nsmul_eq_mul]
      refine Finset.sum_range_choose_smul_le_pow_two_smul ?_
      intro i hi
      simp at hi
      specialize hC₁ i hi x
      specialize hC₂ (n - i + 1) ?_ x
      . refine Nat.succ_le_succ ?_
        refine Nat.succ_le_succ ?_
        exact Nat.sub_le n i
      refine le_of_le_of_eq (mul_le_mul hC₁ hC₂ ?_ ?_) ?_
      . exact norm_nonneg _
      . exact mul_nonneg hC₁_nonneg (by simp)
      ring_nf

-- TODO: Implement in terms of more general method applied to `id`.
lemma hasTemperateGrowth_exp_real_smul_I :
    Function.HasTemperateGrowth fun x : ℝ => exp (x • I) :=
  Function.HasTemperateGrowth.exp_real_smul_I (Function.hasTemperateGrowth_id ℝ)

-- TODO: Generalize to `f x` with bound on growth?
-- Could there be a `HasTemperateGrowth.comp`? At least with a `ContinuousLinearMap`?
lemma hasTemperateGrowth_exp_const_mul_real_smul_I {a : ℝ} :
    Function.HasTemperateGrowth fun x : ℝ => exp ((a * x) • I) :=
  Function.HasTemperateGrowth.exp_real_smul_I Real.hasTemperateGrowth_mul_left

-- /-- More general than `contDiff_sin`; matches `contDiff_exp`. -/
-- lemma contDiff_sin' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] :
--     ContDiff 𝕜 ⊤ sin := by
--   simp [sin]
--   refine ContDiff.div_const (ContDiff.mul ?_ contDiff_const) 2
--   refine ContDiff.sub ?_ ?_
--   . exact ContDiff.cexp (ContDiff.neg (ContDiff.mul contDiff_id contDiff_const))
--   . exact ContDiff.cexp (ContDiff.mul contDiff_id contDiff_const)

-- /-- More general than `contDiff_cos`; matches `contDiff_exp`. -/
-- lemma contDiff_cos' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] :
--     ContDiff 𝕜 ⊤ cos := by
--   simp [cos]
--   refine ContDiff.div_const ?_ 2
--   refine ContDiff.add ?_ ?_
--   . exact ContDiff.cexp (ContDiff.mul contDiff_id contDiff_const)
--   . exact ContDiff.cexp (ContDiff.neg (ContDiff.mul contDiff_id contDiff_const))

end Complex


namespace Real

-- Tried using `ContinuousLinearMap.norm_compContinuousMultilinearMap_le` with
-- `‖iteratedFDeriv ℝ n (Complex.reClm ∘ Complex.sin ∘ Complex.ofRealClm) x‖ ≤ 1`
-- and then using `LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` with
-- `‖iteratedFDeriv ℝ n ((Complex.sin ∘ Subtype.val) ∘ Complex.ofRealLi.equivRange) x‖ ≤ 1`
-- but it was difficult to use the last `Subtype.val`.
-- Easier to just prove `sin` and `cos` together by induction.
-- Could revisit and refer to `ContDiffAt.real_of_complex` as a guide.

/-- Auxiliary function for `abs_iteratedDeriv_{sin,cos}_le`. -/
lemma abs_iteratedDeriv_sin_cos_le {n : ℕ} {x : ℝ} :
    |iteratedDeriv n sin x| ≤ 1 ∧ |iteratedDeriv n cos x| ≤ 1 := by
  induction n with
  | zero => simp; exact ⟨abs_sin_le_one x, abs_cos_le_one x⟩
  | succ n hi =>
    simp [iteratedDeriv_succ']
    refine ⟨hi.right, ?_⟩
    simp [iteratedDeriv_neg_apply]
    exact hi.left

lemma abs_iteratedDeriv_sin_le {n : ℕ} {x : ℝ} : |iteratedDeriv n sin x| ≤ 1 :=
  abs_iteratedDeriv_sin_cos_le.left

lemma abs_iteratedDeriv_cos_le {n : ℕ} {x : ℝ} : |iteratedDeriv n cos x| ≤ 1 :=
  abs_iteratedDeriv_sin_cos_le.right

lemma hasTemperateGrowth_sin : Function.HasTemperateGrowth sin := by
  refine ⟨contDiff_sin, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact le_trans abs_iteratedDeriv_sin_le (le_add_of_nonneg_right (abs_nonneg x))

lemma hasTemperateGrowth_cos : Function.HasTemperateGrowth cos := by
  refine ⟨contDiff_cos, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact le_trans abs_iteratedDeriv_cos_le (le_add_of_nonneg_right (abs_nonneg x))

lemma hasTemperateGrowth_fourierChar_mul' (w : ℝ) :
    Function.HasTemperateGrowth fun v : ℝ => Complex.exp (↑(-(2 * π * v * w)) * Complex.I) := by
  simp_rw [← Complex.real_smul]
  simp_rw [mul_assoc _ _ w, mul_comm _ w, ← mul_assoc _ w]
  simp_rw [← neg_mul]
  exact Complex.hasTemperateGrowth_exp_const_mul_real_smul_I

lemma hasTemperateGrowth_fourierChar_mul (w : ℝ) :
    Function.HasTemperateGrowth fun v : ℝ => (fourierChar (Multiplicative.ofAdd (-(v * w))) : ℂ) := by
  simp_rw [fourierChar_apply]
  simp_rw [mul_neg]
  simp_rw [← mul_assoc]
  exact hasTemperateGrowth_fourierChar_mul' w

end Real


-- section Vector

-- variable {E : Type*}
-- variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- lemma hasTemperateGrowth_fourierChar_mul (w : E) :
--     Function.HasTemperateGrowth fun v : E => Complex.exp (↑(-(2 * π * inner v w)) * Complex.I) := by
--   simp
--   sorry
--   -- simp_rw [← Complex.real_smul]
--   -- simp_rw [mul_assoc _ _ w, mul_comm _ w, ← mul_assoc _ w]
--   -- simp_rw [← neg_mul]
--   -- exact Complex.hasTemperateGrowth_exp_const_mul_real_smul_I

-- end Vector
