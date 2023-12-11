import Mathlib.Analysis.Distribution.SchwartzSpace

import ForML.Util

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped Real Complex SchwartzSpace BigOperators

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
  refine ⟨0, ‖c‖, ?_⟩
  cases n <;> simp [iteratedFDeriv_const_of_ne]

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


section ParametricLinear

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Application of a parametric `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
lemma HasTemperateGrowth.clm_apply
    {f : D → E →L[ℝ] F} (hf : HasTemperateGrowth f)
    {g : D → E} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => (f x) (g x) := by
  refine ⟨hf.1.clm_apply hg.1, ?_⟩
  intro n
  -- Obtain `k, C` for derivatives of `g` and `f`.
  have hf_bound := hf.bound_forall_range (n + 1)
  have hg_bound := hg.bound_forall_range (n + 1)
  rcases hf_bound with ⟨k_f, C_f, ⟨hC_f_nonneg, hC_f⟩⟩
  rcases hg_bound with ⟨k_g, C_g, ⟨_, hC_g⟩⟩
  use k_f + k_g
  use 2 ^ n * C_f * C_g
  intro x
  refine le_trans (norm_iteratedFDeriv_clm_apply hf.1 hg.1 _ le_top) ?_
  simp [mul_assoc]
  norm_cast
  refine Finset.sum_range_choose_mul_le_pow_two_mul_real ?_
  intro i hi
  refine le_trans (mul_le_mul (hC_f i hi x) (hC_g (n - i) ?_ x) (norm_nonneg _) ?_) ?_
  . simp
    exact Nat.sub_lt_succ n i
  . simp [hC_f_nonneg]
  refine le_of_eq ?_
  ring_nf

-- TODO: Generalize to CLMs with `𝕜`-linearity.

-- variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
-- variable [NormedSpace 𝕜 D] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
-- variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- /-- Application of a parametric `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
-- lemma HasTemperateGrowth.clm_apply'
--     {f : D → E →L[𝕜] F} (hf : HasTemperateGrowth f)
--     {g : D → E} (hg : HasTemperateGrowth g) :
--     HasTemperateGrowth fun x => (f x) (g x) := by
--   refine ⟨?_, ?_⟩
--   . have := ContDiff.clm_apply (𝕜 := ℝ) (E := D) (F := E) (G := F) (?_ : ContDiff ℝ ⊤ (fun x => (f x).restrictScalars ℝ)) hg.1
--     . exact this
--     . change ContDiff ℝ ⊤ fun x => ContinuousLinearMap.restrictScalarsIsometry 𝕜 E F ℝ ℝ (f x)
--       refine ContDiff.comp ?_ ?_
--       . exact LinearIsometry.contDiff _
--       . exact hf.1
--   -- refine ⟨hf.1.clm_apply hg.1, ?_⟩
--   intro n
--   -- Obtain `k, C` for derivatives of `g` and `f`.
--   have hf_bound := hf.bound_forall_range (n + 1)
--   have hg_bound := hg.bound_forall_range (n + 1)
--   rcases hf_bound with ⟨k_f, C_f, ⟨hC_f_nonneg, hC_f⟩⟩
--   rcases hg_bound with ⟨k_g, C_g, ⟨_, hC_g⟩⟩
--   use k_f + k_g
--   use 2 ^ n * C_f * C_g
--   intro x
--   refine le_trans (norm_iteratedFDeriv_clm_apply hf.1 hg.1 _ le_top) ?_
--   simp [mul_assoc]
--   norm_cast
--   refine Finset.sum_range_choose_mul_le_pow_two_mul_real ?_
--   intro i hi
--   refine le_trans (mul_le_mul (hC_f i hi x) (hC_g (n - i) ?_ x) (norm_nonneg _) ?_) ?_
--   . simp
--     exact Nat.sub_lt_succ n i
--   . simp [hC_f_nonneg]
--   refine le_of_eq ?_
--   ring_nf

end ParametricLinear


section Linear

variable {E F G 𝔸 : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 G] [SMulCommClass ℝ 𝕜 G]

lemma HasTemperateGrowth.clm' (g : F →L[𝕜] G) {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => g (f x) := by
  change HasTemperateGrowth fun x => g.restrictScalars ℝ (f x)
  exact clm_apply (hasTemperateGrowth_const g) hf

lemma HasTemperateGrowth.clm (g : F →L[ℝ] G) {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth fun x => g (f x) :=
  clm_apply (hasTemperateGrowth_const g) hf

-- TODO: Can't use `HasTemperateGrowth.const_clm` with `ContinuousLinearMap.id` due to circular dependency?
lemma hasTemperateGrowth_id : Function.HasTemperateGrowth (id : E → E) := by
  refine ⟨contDiff_id, ?_⟩
  intro n
  refine ⟨1, 1, ?_⟩
  intro x
  simp
  cases n with
  | zero => simp
  | succ n =>
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
    cases n with
    | zero => simp; refine le_trans ContinuousLinearMap.norm_id_le (by simp)
    | succ n => simp [iteratedFDeriv_const_of_ne]

lemma hasTemperateGrowth_id' : Function.HasTemperateGrowth (fun x : E => x) := hasTemperateGrowth_id

/-- Any `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
lemma hasTemperateGrowth_clm (a : E →L[ℝ] F) : HasTemperateGrowth fun x => a x :=
  hasTemperateGrowth_id.clm a

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

lemma HasTemperateGrowth.bilin (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} (hf : HasTemperateGrowth f)
    {g : E → G} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => B (f x) (g x) :=
  clm_apply (clm B hf) hg

end Bilinear

section SMul

variable {E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasTemperateGrowth.smul
    {f : E → ℝ} (hf : HasTemperateGrowth f)
    {g : E → F} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => f x • g x :=
  bilin (ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)) hg hf

end SMul

section Mul

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NonUnitalNormedRing F] [NormedSpace ℝ F]
variable [IsScalarTower ℝ F F] [SMulCommClass ℝ F F]

lemma HasTemperateGrowth.mul
    {f : E → F} (hf : HasTemperateGrowth f)
    {g : E → F} (hg : HasTemperateGrowth g) :
    HasTemperateGrowth fun x => f x * g x :=
  bilin (ContinuousLinearMap.mul ℝ F) hf hg

end Mul

end Function  -- namespace
