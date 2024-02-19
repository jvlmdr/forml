import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace

import ForML.ContinuousLinearMapCo
import ForML.ContinuousMultilinearMap
import ForML.MultilinearDeriv
import ForML.PiEquiv

open BigOperators

attribute [-simp] Matrix.zero_empty


-- Next define `pideriv` and use pi/copi to give some useful lemmata.

section Derivative

variable {ι 𝕜 : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Def
variable (𝕜)

/--
The Fréchet derivative with respect to one index of a pi type.
Supports `𝕜`-linearity for maps on `(∀ i,) M i` with `NormedSpace 𝕜 (M i)`.
-/
noncomputable def fpideriv (i : ι) (f : (∀ i, M i) → F) (x : (∀ i, M i)) : (M i) →L[𝕜] F :=
  fderiv 𝕜 (fun y => f (Function.update x i y)) (x i)

end Def

/-- The derivative with respect to one index of a pi type. -/
noncomputable def pideriv (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) : F :=
  deriv (fun y => f (Function.update x i y)) (x i)

lemma fpideriv_apply {i : ι} {f : (∀ i, M i) → F} {x : (∀ i, M i)} {m : M i} :
    fpideriv 𝕜 i f x m = fderiv 𝕜 (fun y => f (Function.update x i y)) (x i) m := rfl

lemma fpideriv_def {i : ι} {f : (∀ i, M i) → F} :
    fpideriv 𝕜 i f = fun x => fderiv 𝕜 (fun y => f (Function.update x i y)) (x i) := rfl

lemma pideriv_def {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} :
    pideriv i f x = deriv (fun y => f (Function.update x i y)) (x i) := rfl


/-- The function `f` has Fréchet derivative `f'` at `x` along  -/
def HasFPiDerivAt (i : ι) (f : (∀ i, M i) → F) (f' : M i →L[𝕜] F) (x : (∀ i, M i)) :=
  HasFDerivAt (fun y => f (Function.update x i y)) f' (x i)

def HasPiDerivAt (i : ι) (f : (ι → 𝕜) → F) (f' : F) (x : ι → 𝕜) :=
  HasDerivAt (fun y => f (Function.update x i y)) f' (x i)

theorem hasFPiDerivAt_iff_hasPiDerivAt {i : ι} {f : (ι → 𝕜) → F} {f' : 𝕜 →L[𝕜] F} {x : ι → 𝕜} :
    HasFPiDerivAt i f f' x ↔ HasPiDerivAt i f (f' 1) x :=
  hasFDerivAt_iff_hasDerivAt

lemma HasFDerivAt.hasFPiDerivAt {i : ι} {f : (∀ i, M i) → F} {f' : (∀ i, M i) →L[𝕜] F} {x : (∀ i, M i)}
    (hf : HasFDerivAt f f' x) :
    HasFPiDerivAt i f (f'.comp (ContinuousLinearMap.single i)) x := by
  rw [HasFPiDerivAt]
  refine HasFDerivAt.comp _ (by simpa) ?_
  refine HasFDerivAt.congr_fderiv (hasFDerivAt_update _ _) ?_
  ext m j
  simp
  simp [Pi.single]
  by_cases h : j = i
  . rw [h]
    simp
  . simp [h]

lemma HasFDerivAt.hasPiDerivAt {i : ι} {f : (ι → 𝕜) → F} {f' : (ι → 𝕜) →L[𝕜] F} {x : ι → 𝕜}
    (hf : HasFDerivAt f f' x) :
    HasPiDerivAt i f (f' (Pi.single i 1)) x := by
  change HasPiDerivAt i f (f'.comp (ContinuousLinearMap.single i) 1) x
  rw [← hasFPiDerivAt_iff_hasPiDerivAt]
  exact hasFPiDerivAt hf

lemma DifferentiableAt.hasFPiDerivAt {i : ι} {f : (∀ i, M i) → F} {x : (∀ i, M i)}
    (hf : DifferentiableAt 𝕜 f x) :
    HasFPiDerivAt i f ((fderiv 𝕜 f x).comp (ContinuousLinearMap.single i)) x :=
  hf.hasFDerivAt.hasFPiDerivAt

lemma DifferentiableAt.hasPiDerivAt {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    HasPiDerivAt i f ((fderiv 𝕜 f x) (Pi.single i 1)) x :=
  hf.hasFDerivAt.hasPiDerivAt

lemma HasFPiDerivAt.fpideriv {i : ι} {f : (∀ i, M i) → F} {f' : (M i) →L[𝕜] F} {x : (∀ i, M i)} (hf : HasFPiDerivAt i f f' x) :
    fpideriv 𝕜 i f x = f' :=
  hf.fderiv

lemma HasPiDerivAt.pideriv {i : ι} {f : (ι → 𝕜) → F} {f' : F} {x : ι → 𝕜} (hf : HasPiDerivAt i f f' x) :
    pideriv i f x = f' :=
  hf.deriv

-- The partial derivative can be expressed as a projection of `fderiv` onto a canonical basis vector.

lemma fpideriv_eq_fderiv_comp_single {i : ι} {f : (∀ i, M i) → F} {x : (∀ i, M i)}
    (hf : DifferentiableAt 𝕜 f x) :
    fpideriv 𝕜 i f x = (fderiv 𝕜 f x).comp (ContinuousLinearMap.single i) :=
  hf.hasFPiDerivAt.fpideriv

lemma pideriv_eq_fderiv_apply_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    pideriv i f x = fderiv 𝕜 f x (Pi.single i 1) :=
  hf.hasPiDerivAt.pideriv

lemma fpideriv_apply_eq_fderiv_apply_single {i : ι} {f : (∀ i, M i) → F} {x : (∀ i, M i)} {m : M i}
    (hf : DifferentiableAt 𝕜 f x) :
    fpideriv 𝕜 i f x m = fderiv 𝕜 f x (Pi.single i m) := by
  rw [fpideriv_eq_fderiv_comp_single hf]
  rfl

/-- Analogy of `fderiv_deriv`. -/
lemma fpideriv_pideriv {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} :
    fpideriv 𝕜 i f x 1 = pideriv i f x :=
  fderiv_deriv

/-- Analogy of `deriv_fderiv`. -/
lemma pideriv_fpideriv {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} :
    ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (pideriv i f x) = fpideriv 𝕜 i f x :=
  deriv_fderiv

lemma fpideriv_apply_eq_smul_pideriv {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} {m : 𝕜} :
    fpideriv 𝕜 i f x m = m • pideriv i f x := by
  rw [← pideriv_fpideriv]
  simp

/--
The Fréchet derivative can be rewritten as a `ContinuousLinearMap.copi`.

Compared to `fderiv_eq_copi_fpideriv`, this variant doesn't require `DifferentiableAt`
because it doesn't take individual derivatives.
-/
lemma fderiv_eq_copi_fderiv_comp_single {f : (∀ i, M i) → F} {x : (∀ i, M i)} :
    fderiv 𝕜 f x = ContinuousLinearMap.copi (fun i => (fderiv 𝕜 f x).comp (ContinuousLinearMap.single i)) := by
  rw [ContinuousLinearMap.copi_comp_single]

/-- The Fréchet derivative can be rewritten as a `ContinuousLinearMap.copi` of partial derivatives. -/
lemma fderiv_eq_copi_fpideriv {f : (∀ i, M i) → F} {x : (∀ i, M i)}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x = ContinuousLinearMap.copi (fun i => fpideriv 𝕜 i f x) := by
  rw [fderiv_eq_copi_fderiv_comp_single]
  -- conv => lhs; rw [← ContinuousLinearMap.copi_comp_single (f := fderiv 𝕜 f x)]
  congr
  ext i m
  simp
  exact (fpideriv_apply_eq_fderiv_apply_single hf).symm

-- This can be rewritten using `smul_pideriv`, `fderiv_apply_single`.
/-- The Fréchet derivative can be rewritten as a sum of partial derivatives. -/
lemma fderiv_apply_eq_sum_fpideriv {f : (∀ i, M i) → F} {x m : (∀ i, M i)}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x m = ∑ i : ι, fpideriv 𝕜 i f x (m i) := by
  rw [fderiv_eq_copi_fpideriv hf]
  rfl

lemma fderiv_apply_eq_sum_fderiv_apply_single {f : (∀ i, M i) → F} {x m : ∀ i, M i} :
    fderiv 𝕜 f x m = ∑ i : ι, fderiv 𝕜 f x (Pi.single i (m i)) := by
  conv => lhs; rw [fderiv_eq_copi_fderiv_comp_single]


-- /-- The Fréchet derivative can be written as a sum of partial derivatives over coordinates. -/
-- lemma fderiv_apply_eq_sum_smul_ideriv {f : (ι → 𝕜) → F} {x dx : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
--     fderiv 𝕜 f x dx = ∑ i, dx i • pideriv i f x := by
--   change (fderiv 𝕜 f x).toLinearMap dx = _
--   rw [LinearMap.pi_apply_eq_sum_univ]
--   congr
--   ext i
--   rw [ideriv_eq_fderiv_single hf]
--   simp_rw [← Pi.single_apply]
--   simp_rw [Pi.single_comm]
--   rfl


-- TODO: `hasFDerivAt_iff_hasPiDerivAt_forall`

-- lemma hasFDerivAt_copi_iff_hasFPiDerivAt_forall {f : (∀ i, M i) → F} {f' : ∀ i, M i →L[𝕜] F} {x : ∀ i, M i} :
--     HasFDerivAt f (ContinuousLinearMap.copi f') x ↔ ∀ i, HasFPiDerivAt i f (f' i) x := by
--   simp [HasFPiDerivAt]
--   sorry

--   -- rw [HasFDerivAt]
--   -- rw [HasFDerivAtFilter]

--   -- simp [HasFPiDerivAt]
--   -- refine Iff.intro ?_ ?_
--   -- . sorry
--   -- intro h
--   -- sorry

--   -- rw [hasFDerivAt_iff_hasPiDerivAt]
--   -- simp [Pi.single_comm]

-- lemma hasFDerivAt_copi_iff_hasPiDerivAt_forall {f : (ι → 𝕜) → F} {f' : ι → 𝕜 →L[𝕜] F} {x : ι → 𝕜} :
--     HasFDerivAt f (ContinuousLinearMap.copi f') x ↔ ∀ i, HasPiDerivAt i f (f' i) (x i) := by
--   sorry
--   rw [hasFDerivAt_iff_hasPiDerivAt]
--   simp [Pi.single_comm]


-- lemma differentiableAt_comp_update {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
--     (hf : DifferentiableAt 𝕜 f x) :
--     DifferentiableAt 𝕜 (fun xi => f (Function.update x i xi)) (x i) := by
--   change DifferentiableAt 𝕜 (f ∘ Function.update x i) (x i)
--   refine DifferentiableAt.comp _ ?_ (hasFDerivAt_update x _).differentiableAt
--   simp
--   exact hf


-- -- TODO: Is there some lemma for the norm of an lsum?
-- -- TODO: Upgrade to a CLM?
-- lemma fderiv_toLinearMap_eq_lsum_fpideriv {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
--     (fderiv 𝕜 f x).toLinearMap = LinearMap.lsum 𝕜 (fun _ : ι => 𝕜) 𝕜 (fun i => (fpideriv 𝕜 i f x).toLinearMap) := by
--   refine LinearMap.ext ?_
--   intro dx
--   simp
--   change fderiv 𝕜 f x dx = _
--   rw [fderiv_pi_apply_eq_sum]
--   congr
--   ext i
--   rw [← ideriv_eq_fderiv_single hf]
--   rw [fpideriv_eq_smul_ideriv]


/--
The norm of the fderiv map is bounded by norms of the coordinate derivatives.

TODO: Establish an equality?
TODO: Could eliminate `DifferentiableAt` using `Or.elim`.
-/
lemma norm_fderiv_le_sum_norm_fpideriv {f : (∀ i, M i) → F} {x : ∀ i, M i} (hf : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 f x‖ ≤ ∑ i, ‖fpideriv 𝕜 i f x‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
  intro u
  rw [fderiv_apply_eq_sum_fpideriv hf]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  simp
  intro i
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (norm_nonneg _)

/-- The norm of the fderiv map is bounded by norms of the coordinate derivatives. -/
lemma norm_fderiv_le_sum_norm_pideriv {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 f x‖ ≤ ∑ i, ‖pideriv i f x‖ := by
  refine le_trans (norm_fderiv_le_sum_norm_fpideriv hf) ?_
  refine Finset.sum_le_sum ?_
  simp
  intro i
  rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg _)]
  intro m
  refine le_of_eq ?_
  rw [fpideriv_apply_eq_smul_pideriv]
  rw [norm_smul]
  ring_nf


lemma norm_fpideriv_le_norm_fderiv {i : ι} {f : (∀ i, M i) → F} {x : ∀ i, M i} (hf : DifferentiableAt 𝕜 f x) :
    ‖fpideriv 𝕜 i f x‖ ≤ ‖fderiv 𝕜 f x‖ := by
  simp_rw [fpideriv_eq_fderiv_comp_single hf]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_single_le_one

lemma norm_pideriv_le_norm_fderiv {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    ‖pideriv i f x‖ ≤ ‖fderiv 𝕜 f x‖ := by
  simp_rw [pideriv_eq_fderiv_apply_single hf]
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  simp

lemma norm_iteratedFDeriv_fpideriv_le_norm_iteratedFDeriv_succ {n : ℕ} {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ContDiff 𝕜 (n + 1) f) :
    ‖iteratedFDeriv 𝕜 n (fpideriv 𝕜 i f) x‖ ≤ ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  change ‖iteratedFDeriv 𝕜 n (fun y => fpideriv 𝕜 i f y) x‖ ≤ _
  have hf_diff {y} : DifferentiableAt 𝕜 f y := hf.differentiable (by norm_num) _
  simp_rw [fpideriv_eq_fderiv_comp_single hf_diff]
  refine le_trans (norm_iteratedFDeriv_clm_comp_const (hf.fderiv_right (le_refl _))) ?_
  rw [norm_iteratedFDeriv_fderiv]
  simp
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact ContinuousLinearMap.norm_single_le_one

-- TODO: Could use `norm_iteratedFDeriv_fpideriv_le_norm_iteratedFDeriv_succ`.

lemma norm_iteratedFDeriv_pideriv_le_norm_iteratedFDeriv_succ {n : ℕ} {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ContDiff 𝕜 (n + 1) f) :
    ‖iteratedFDeriv 𝕜 n (pideriv i f) x‖ ≤ ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  change ‖iteratedFDeriv 𝕜 n (fun y => pideriv i f y) x‖ ≤ _
  have hf_diff {y} : DifferentiableAt 𝕜 f y := hf.differentiable (by norm_num) _
  simp_rw [pideriv_eq_fderiv_apply_single hf_diff]
  refine le_trans (norm_iteratedFDeriv_clm_apply_const (hf.fderiv_right (le_refl _)) (le_refl _)) ?_
  simp
  rw [norm_iteratedFDeriv_fderiv]


-- /-- Second derivative is symmetric; that is, `u' H v = v' H u`. -/
-- lemma fderiv_fderiv_symm {f : (∀ i, M i) → F} {x : ∀ i, M i} {u v : ∀ i, M i}
--     (hf : DifferentiableAt 𝕜 f x) (hf' : DifferentiableAt 𝕜 (fderiv 𝕜 f) x) :
--     fderiv 𝕜 (fderiv 𝕜 f) x u v = fderiv 𝕜 (fderiv 𝕜 f) x v u := by
--   change fderiv 𝕜 (fun y => fderiv 𝕜 f y) x u v = fderiv 𝕜 (fun y => fderiv 𝕜 f y) x v u
--   rw [← fderiv_clm_apply_comm hf']
--   rw [← fderiv_clm_apply_comm hf']
--   rw [fderiv_apply_eq_sum_fderiv_apply_single]
--   rw [fderiv_apply_eq_sum_fderiv_apply_single]
--   simp_rw [fderiv_apply_eq_sum_fderiv_apply_single (m := v)]
--   simp_rw [fderiv_apply_eq_sum_fderiv_apply_single (m := u)]
--   rw [fderiv_sum (fun i _ => DifferentiableAt.clm_apply hf' (differentiableAt_const _))]
--   rw [fderiv_sum (fun i _ => DifferentiableAt.clm_apply hf' (differentiableAt_const _))]
--   conv => lhs; arg 2; intro i; rw [ContinuousLinearMap.sum_apply]
--   conv => rhs; arg 2; intro i; rw [ContinuousLinearMap.sum_apply]
--   rw [Finset.sum_comm]
--   conv => lhs; arg 2; intro j; arg 2; intro i
--   conv => rhs; arg 2; intro j; arg 2; intro i
--   refine Finset.sum_congr rfl ?_
--   intro i _
--   refine Finset.sum_congr rfl ?_
--   intro j _
--   -- This just reduced to the partial derivative problem.
--   sorry


-- /-- Partial derivatives commute. -/
-- lemma fpideriv_comm {i₁ i₂ : ι} {f : (∀ j, M j) → F} {x : (∀ j, M j)} {m₁ : M i₁} {m₂ : M i₂}
--     (hf : Differentiable 𝕜 f)
--     (hf' : Differentiable 𝕜 (fun x => fderiv 𝕜 f x)) :
--     fpideriv 𝕜 i₁ (fun x => fpideriv 𝕜 i₂ f x m₂) x m₁ =
--     fpideriv 𝕜 i₂ (fun x => fpideriv 𝕜 i₁ f x m₁) x m₂ := by
--   have (i₁ i₂ m₁ m₂) : fpideriv 𝕜 i₁ (fun x => fpideriv 𝕜 i₂ f x m₂) x m₁ =
--       fpideriv 𝕜 i₁ (fun x => fderiv 𝕜 f x (Pi.single i₂ m₂)) x m₁
--   . congr
--     ext y
--     rw [fpideriv_eq_fderiv_comp_single (hf y)]
--     rw [ContinuousLinearMap.comp_apply]
--     simp
--   simp [this]
--   clear this

--   have (i₁ i₂ m₁ m₂) : fpideriv 𝕜 i₁ (fun x => fderiv 𝕜 f x (Pi.single i₂ m₂)) x m₁ =
--       fderiv 𝕜 (fun x => fderiv 𝕜 f x) x (Pi.single i₁ m₁) (Pi.single i₂ m₂)
--   . rw [fpideriv_eq_fderiv_comp_single ((hf' x).clm_apply (differentiableAt_const _))]
--     rw [ContinuousLinearMap.comp_apply]
--     simp
--     rw [fderiv_clm_apply_const (hf' x)]
--     simp
--   simp [this]
--   clear this

--   -- rw [fpideriv_eq_fderiv_comp_single ((hf' x).clm_apply (differentiableAt_const _))]
--   -- rw [ContinuousLinearMap.comp_apply]
--   -- simp
--   -- rw [fderiv_clm_apply_const (hf' x)]
--   -- simp

--   sorry


noncomputable def orderedIteratedPiDerivAux {n : ℕ} (f : (ι → 𝕜) → F) : (Fin n → ι) → (ι → 𝕜) → F :=
  Nat.recOn n
    (fun _ x => f x)
    (fun _n rec js x => pideriv (js 0) (fun y => rec (Fin.tail js) y) x)

noncomputable def orderedIteratedPiDeriv {n : ℕ} (js : Fin n → ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) : F :=
  orderedIteratedPiDerivAux f js x

section Def
variable (𝕜)

noncomputable def orderedIteratedFPiDerivAux {n : ℕ} (f : (∀ i, M i) → F) :
    (js : Fin n → ι) → (∀ i, M i) → ContinuousMultilinearMap 𝕜 (fun i : Fin n => M (js i)) F :=
  Nat.recOn n
    (fun js x => ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun i : Fin 0 => M (js i)) (f x))
    (fun _n rec js x => ContinuousLinearMap.uncurryLeft (fpideriv 𝕜 (js 0) (fun y => rec (Fin.tail js) y) x))

noncomputable def orderedIteratedFPiDeriv {n : ℕ} (js : Fin n → ι) (f : (∀ i, M i) → F) (x : ∀ i, M i) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => M (js i)) F :=
  orderedIteratedFPiDerivAux 𝕜 f js x

end Def

@[simp]
lemma orderedIteratedPiDeriv_zero {f : (ι → 𝕜) → F} {js : Fin 0 → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = f x := rfl

@[simp]
lemma orderedIteratedPiDeriv_one {f : (ι → 𝕜) → F} {js : Fin 1 → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = pideriv (js 0) f x := rfl

lemma orderedIteratedPiDeriv_succ_left {n : ℕ} {f : (ι → 𝕜) → F} {js : Fin (n + 1) → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = pideriv (js 0) (orderedIteratedPiDeriv (Fin.tail js) f) x := rfl

lemma orderedIteratedPiDeriv_succ_right {n : ℕ} {f : (ι → 𝕜) → F} {js : Fin (n + 1) → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = orderedIteratedPiDeriv (Fin.init js) (pideriv (js (Fin.last n)) f) x := by
  induction n generalizing f x with
  | zero => rfl
  | succ n ih =>
    -- Apply inductive hypothesis to elements `1 .. n + 2`.
    have A (y) : orderedIteratedPiDeriv (Fin.tail js) f y =
        orderedIteratedPiDeriv (Fin.init (Fin.tail js)) (pideriv (js (Fin.last (n + 1))) f) y
    . rw [ih]
      rfl
    rw [orderedIteratedPiDeriv_succ_left]
    change pideriv (js 0) (fun y => orderedIteratedPiDeriv (Fin.tail js) f y) x = _
    simp_rw [A]
    rfl


lemma orderedIteratedFPiDeriv_zero_apply {f : (∀ i, M i) → F} {js : Fin 0 → ι} {x : ∀ i, M i} {m : ∀ i, M (js i)} :
    orderedIteratedFPiDeriv 𝕜 js f x m = f x := rfl

theorem orderedIteratedFPiDeriv_zero_eq_comp {f : (∀ i, M i) → F} {js : Fin 0 → ι} :
    orderedIteratedFPiDeriv 𝕜 js f = (continuousMultilinearIsEmptyEquiv 𝕜 (fun i : Fin 0 => M (js i)) F).symm ∘ f := rfl

theorem orderedIteratedFPiDeriv_succ_eq_comp_left {f : (∀ i, M i) → F} {js : Fin (n + 1) → ι} :
    orderedIteratedFPiDeriv 𝕜 js f =
    ⇑(continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Fin (n + 1) => M (js i)) F) ∘
      (fpideriv 𝕜 (js 0) (orderedIteratedFPiDeriv 𝕜 (Fin.tail js) f)) := rfl

theorem orderedIteratedFPiDeriv_succ_apply_left {n : ℕ} {f : (∀ i, M i) → F} {js : Fin (n + 1) → ι} {x : ∀ i, M i}
    {m : (i : Fin (n + 1)) → M (js i)} :
    orderedIteratedFPiDeriv 𝕜 js f x m =
    fpideriv 𝕜 (js 0) (orderedIteratedFPiDeriv 𝕜 (Fin.tail js) f) x (m 0) (Fin.tail m) := rfl

theorem orderedIteratedFPiDeriv_succ_apply_right {n : ℕ} {f : (∀ i, M i) → F} {js : Fin (n + 1) → ι} {x : ∀ i, M i}
    {m : (i : Fin (n + 1)) → M (js i)} :
    orderedIteratedFPiDeriv 𝕜 js f x m =
    orderedIteratedFPiDeriv 𝕜 (Fin.init js) (fpideriv 𝕜 (js (Fin.last n)) f) x (Fin.init m) (m (Fin.last n)) := by
  simp  -- `ContinuousLinearMap.strongUniformity_topology_eq`?
  -- Follows `iteratedFDerivWithin_succ_apply_right`.
  induction n generalizing x with
  | zero =>
    rw [orderedIteratedFPiDeriv_succ_eq_comp_left]
    rw [fpideriv_def, orderedIteratedFPiDeriv_zero_eq_comp]
    rw [Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
    change fderiv 𝕜 (⇑(LinearIsometryEquiv.symm (continuousMultilinearIsEmptyEquiv 𝕜 (fun i => M (Fin.tail js i)) F)) ∘
      f ∘ (Function.update x (js 0))) _ _ _ = _
    rw [LinearIsometryEquiv.comp_fderiv]
    rw [ContinuousLinearMap.comp_apply]
    -- simp
    rfl
  | succ n ih =>
    -- Apply inductive hypothesis to `n + 1` elements `1 .. n + 2` and introduce equiv.
    -- Then expand on the left, where things are definitionally equal.
    have A (y) : orderedIteratedFPiDeriv 𝕜 (Fin.tail js) f y =
        (continuousMultilinearCurryRightEquiv 𝕜 (fun i : Fin (n + 1) => M (js (Fin.succ i))) F ∘
          orderedIteratedFPiDeriv 𝕜 (Fin.init (Fin.tail js)) (fpideriv 𝕜 (js (Fin.last (n + 1))) f)) y
    . ext m
      rw [ih]
      rfl
    rw [orderedIteratedFPiDeriv_succ_eq_comp_left]
    rw [Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
    rw [fpideriv_def]
    simp
    simp_rw [A]
    change fderiv 𝕜 (
      ⇑(continuousMultilinearCurryRightEquiv 𝕜 (fun i => M (js (Fin.succ i))) F) ∘
      (orderedIteratedFPiDeriv 𝕜 (Fin.init (Fin.tail js)) (fpideriv 𝕜 (js (Fin.last (n + 1))) f) ∘ Function.update x (js 0)))
      _ _ _ = _
    rw [LinearIsometryEquiv.comp_fderiv]
    -- simp
    -- rw [continuousMultilinearCurryRightEquiv_apply]  -- `Fin.castSucc` vs `Fin.succ`
    rfl

theorem orderedIteratedFPiDeriv_succ_eq_comp_right {f : (∀ i, M i) → F} {js : Fin (n + 1) → ι} :
    orderedIteratedFPiDeriv 𝕜 js f =
      ⇑(continuousMultilinearCurryRightEquiv 𝕜 (fun i : Fin (n + 1) => M (js i)) F) ∘
      (orderedIteratedFPiDeriv 𝕜 (Fin.init js) (fpideriv 𝕜 (js (Fin.last n)) f)) := by
  ext x m
  rw [orderedIteratedFPiDeriv_succ_apply_right]
  rfl

theorem orderedIteratedFPiDeriv_one_apply {f : (∀ i, M i) → F} {js : Fin 1 → ι} {x : ∀ i, M i} {m : ∀ i, M (js i)} :
    orderedIteratedFPiDeriv 𝕜 js f x m = fpideriv 𝕜 (js 0) f x (m 0) := by
  rw [orderedIteratedFPiDeriv_succ_apply_right]
  rw [orderedIteratedFPiDeriv_zero_apply]
  rfl


-- noncomputable instance {n : ℕ} {js : Fin (n + 2) → ι} :
--     NormedAddCommGroup (M (Fin.tail js 0) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => (i : ι) → M i) F) :=
--   ContinuousLinearMap.toNormedAddCommGroup

-- noncomputable instance {n : ℕ} {js : Fin (n + 2) → ι} :
--     NormedSpace 𝕜 (M (Fin.tail js 0) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => (i : ι) → M i) F) :=
--   ContinuousLinearMap.toNormedSpace

-- noncomputable instance {n : ℕ} :
--     NormedAddCommGroup (((i : ι) → M i) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => (i : ι) → M i) F) :=
--   ContinuousLinearMap.toNormedAddCommGroup

-- noncomputable instance {n : ℕ} :
--     NormedSpace 𝕜 (((i : ι) → M i) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => (i : ι) → M i) F) :=
--   ContinuousLinearMap.toNormedSpace


lemma ContinuousMultilinearMap.curryLeft_compContinuousLinearMap
    {M₁ : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace 𝕜 (M₁ i)]
    {M₁' : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (M₁' i)] [∀ i, NormedSpace 𝕜 (M₁' i)]
    (g : ContinuousMultilinearMap 𝕜 M₁' F)
    (f : ∀ i, M₁ i →L[𝕜] M₁' i) :
    (ContinuousMultilinearMap.compContinuousLinearMap g f).curryLeft =
    -- ((ContinuousMultilinearMap.compContinuousLinearMapL (fun i => f (Fin.succ i))).comp g.curryLeft).comp (f 0) := by
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun i => f (Fin.succ i))).comp (g.curryLeft.comp (f 0)) := by
  ext u m
  simp
  congr
  ext i
  refine Fin.cases ?_ ?_ i <;> simp


@[simp]
lemma continuousMultilinearCurryLeftEquiv_curryLeft
    {M₁ : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace 𝕜 (M₁ i)]
    (g : ContinuousMultilinearMap 𝕜 M₁ F) :
    (continuousMultilinearCurryLeftEquiv 𝕜 M₁ F) (g.curryLeft) = g := by
  ext x
  simp


section FormalMultilinearSeries

variable {f : (∀ i, M i) → F} {f' : ((i : ι) → M i) → FormalMultilinearSeries 𝕜 ((i : ι) → M i) F}

theorem HasFTaylorSeriesUpTo.hasFDerivAt_orderedIteratedFPiDeriv' {n : ℕ} (hf : HasFTaylorSeriesUpTo (n + 1) f f')
    {js : Fin n → ι} {x : ∀ i, M i} :
    HasFDerivAt (orderedIteratedFPiDeriv 𝕜 js f)
      ((ContinuousMultilinearMap.compContinuousLinearMapL (fun i => ContinuousLinearMap.single (js i))).comp
        (f' x (n + 1)).curryLeft) x := by
  induction n generalizing x with
  | zero =>
    rw [orderedIteratedFPiDeriv_zero_eq_comp]
    rw [LinearIsometryEquiv.comp_hasFDerivAt_iff']
    refine HasFDerivAt.congr_fderiv (hf.hasFDerivAt (by simp) x) ?_
    ext m
    simp only [continuousMultilinearCurryFin1_apply, Nat.zero_eq, LinearIsometryEquiv.symm_symm,
      ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
      Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      continuousMultilinearIsEmptyEquiv_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, Pi.zero_apply, map_zero,
      ContinuousMultilinearMap.curryLeft_apply]
    congr
    funext i
    rw [Fin.eq_zero i]
    simp only [Fin.cons_zero]
    have : (0 : Fin 1) = Fin.last 0 := rfl
    simp [this]
  | succ n ih =>
    rw [← hasFTaylorSeriesUpToOn_univ_iff] at hf
    rw [hasFTaylorSeriesUpToOn_succ_iff_left] at hf
    rcases hf with ⟨hf_pred, hf_diff, _⟩
    rw [hasFTaylorSeriesUpToOn_univ_iff] at hf_pred
    simp at hf_diff
    specialize @ih hf_pred
    rw [orderedIteratedFPiDeriv_succ_eq_comp_left]
    -- Use inductive hypothesis to rewrite `fpideriv`.
    conv =>
      arg 1; intro y; arg 2; intro x
      rw [fpideriv_eq_fderiv_comp_single ih.differentiableAt]
      rw [ih.fderiv]
      rw [ContinuousLinearMap.comp_assoc]
      simp [Fin.tail]
      rw [← ContinuousMultilinearMap.curryLeft_compContinuousLinearMap (f' x (n + 1)) (fun i => ContinuousLinearMap.single (js i))]
    simp
    simp_rw [← ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    refine ((ContinuousLinearMap.hasFDerivAt _).comp _ (hf_diff _)).congr_fderiv ?_
    ext m v
    simp


theorem HasFTaylorSeriesUpTo.hasFDerivAt_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} {x : ∀ i, M i} :
    HasFDerivAt (orderedIteratedFPiDeriv 𝕜 js f)
      ((ContinuousMultilinearMap.compContinuousLinearMapL (fun i => ContinuousLinearMap.single (js i))).comp
        (f' x (n + 1)).curryLeft) x :=
  hasFDerivAt_orderedIteratedFPiDeriv' (hf.ofLe (ENat.add_one_le_of_lt hn))


theorem HasFTaylorSeriesUpTo.fderiv_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} {x : ∀ i, M i} :
    _root_.fderiv 𝕜 (orderedIteratedFPiDeriv 𝕜 js f) x =
    ((ContinuousMultilinearMap.compContinuousLinearMapL (fun i => ContinuousLinearMap.single (js i))).comp (f' x (n + 1)).curryLeft) :=
  (hasFDerivAt_orderedIteratedFPiDeriv hn hf).fderiv

theorem HasFTaylorSeriesUpTo.differentiableAt_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} {x : ∀ i, M i} :
    DifferentiableAt 𝕜 (orderedIteratedFPiDeriv 𝕜 js f) x :=
  (hasFDerivAt_orderedIteratedFPiDeriv hn hf).differentiableAt

theorem HasFTaylorSeriesUpTo.differentiable_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} :
    Differentiable 𝕜 (orderedIteratedFPiDeriv 𝕜 js f) :=
  fun _ => (hasFDerivAt_orderedIteratedFPiDeriv hn hf).differentiableAt


theorem HasFTaylorSeriesUpTo.orderedIteratedFPiDeriv_apply {n : ℕ} {N : ℕ∞} (hn : n ≤ N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} {x : ∀ i, M i} {m : (i : Fin n) → M (js i)} :
    (orderedIteratedFPiDeriv 𝕜 js f x) m = (f' x n) (fun i => Pi.single (js i) (m i)) := by
  cases n with
  | zero =>
    simp
    rw [orderedIteratedFPiDeriv_zero_apply]
    rw [Subsingleton.elim (fun i => Pi.single (js i) _) 0]
    rw [← ContinuousMultilinearMap.uncurry0_apply]
    rw [hf.zero_eq]
  | succ n =>
    -- TODO: Induction not required; can this be further simplified?
    replace hn : n < N
    . refine lt_of_lt_of_le ?_ hn
      norm_cast
      exact Nat.lt_succ_self n
    rw [orderedIteratedFPiDeriv_succ_apply_left]
    rw [fpideriv_apply_eq_fderiv_apply_single (differentiableAt_orderedIteratedFPiDeriv hn hf)]
    rw [HasFTaylorSeriesUpTo.fderiv_orderedIteratedFPiDeriv hn hf]
    rw [ContinuousLinearMap.comp_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.single_apply,
      ContinuousMultilinearMap.curryLeft_apply]
    congr
    simp only [Fin.tail]
    funext i
    refine Fin.cases ?_ ?_ i <;> simp


theorem HasFTaylorSeriesUpTo.orderedIteratedFPiDeriv_eq_compContinuousLinearMap {n : ℕ} {N : ℕ∞} (hn : n ≤ N)
    (hf : HasFTaylorSeriesUpTo N f f') {js : Fin n → ι} {x : ∀ i, M i} :
    orderedIteratedFPiDeriv 𝕜 js f x = (f' x n).compContinuousLinearMap (fun i => ContinuousLinearMap.single (js i)) := by
  ext m
  rw [orderedIteratedFPiDeriv_apply hn hf]
  rfl


lemma ContDiff.differentiable_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N) (hf : ContDiff 𝕜 N f)
    {js : Fin n → ι} :
    Differentiable 𝕜 (orderedIteratedFPiDeriv 𝕜 js f) := by
  rcases hf with ⟨f', hf⟩
  exact hf.differentiable_orderedIteratedFPiDeriv hn

lemma ContDiff.differentiableAt_orderedIteratedFPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N) (hf : ContDiff 𝕜 N f)
    {js : Fin n → ι} {x : ∀ i, M i} :
    DifferentiableAt 𝕜 (orderedIteratedFPiDeriv 𝕜 js f) x := by
  rcases hf with ⟨f', hf⟩
  exact hf.differentiableAt_orderedIteratedFPiDeriv hn


/-- The iterated partial derivative is equal to the iterated derivative applied to one-hot vectors. -/
theorem ContDiff.orderedIteratedFPiDeriv_apply_eq_iteratedFDeriv_apply_single {n : ℕ} {N : ℕ∞} (hn : n ≤ N) (hf : ContDiff 𝕜 N f)
    {js : Fin n → ι} {x : ∀ i, M i} {m : ∀ k, M (js k)} :
    orderedIteratedFPiDeriv 𝕜 js f x m = iteratedFDeriv 𝕜 n f x (fun k => Pi.single (js k) (m k)) := by
  rw [contDiff_iff_ftaylorSeries] at hf
  rw [hf.orderedIteratedFPiDeriv_apply hn]
  rfl

theorem ContDiff.orderedIteratedFPiDeriv_eq_iteratedFDeriv_comp_single {n : ℕ} {N : ℕ∞} (hn : n ≤ N) (hf : ContDiff 𝕜 N f)
    {js : Fin n → ι} {x : ∀ i, M i} :
    orderedIteratedFPiDeriv 𝕜 js f x = (iteratedFDeriv 𝕜 n f x).compContinuousLinearMap (fun i => ContinuousLinearMap.single (js i)) := by
  ext m
  rw [orderedIteratedFPiDeriv_apply_eq_iteratedFDeriv_apply_single hn hf]
  rfl

-- Proof follows `ContDiffWithinAt.iteratedFderivWithin_right`.
-- TODO: Is there an easier way to write this, like `ContDiff.orderedIteratedPiDeriv_right`?
/-- The iterated partial derivative is continuous differentiable. -/
theorem ContDiff.orderedIteratedFPiDeriv_right {m N : ℕ∞} {n : ℕ} (hn : m + n ≤ N) (hf : ContDiff 𝕜 N f) {js : Fin n → ι} :
    ContDiff 𝕜 m (_root_.orderedIteratedFPiDeriv 𝕜 js f) := by
  induction n generalizing m with
  | zero =>
    rw [orderedIteratedFPiDeriv_zero_eq_comp]
    simp at hn
    exact (LinearIsometryEquiv.contDiff _).comp (hf.of_le hn)
  | succ n ih =>
    rw [orderedIteratedFPiDeriv_succ_eq_comp_left]
    refine ContDiff.comp ?_ ?_
    . exact LinearIsometryEquiv.contDiff _  -- Can't put inline for some reason?
    have hn' : n < N  -- TODO: Is there a simpler way to obtain this?
    . simp at hn
      rw [← add_assoc] at hn
      refine lt_of_lt_of_le ?_ hn
      rw [← ENat.add_one_le_iff (ENat.coe_ne_top n)]
      rw [add_assoc]
      exact le_add_self
    conv =>
      arg 3; intro x
      rw [fpideriv_eq_fderiv_comp_single (hf.differentiable_orderedIteratedFPiDeriv hn' _)]
    refine ContDiff.clm_comp ?_ contDiff_const
    specialize @ih (m + 1) ?_
    . rw [add_assoc]
      rw [add_comm 1]
      exact hn
    exact ContDiff.fderiv_right ih (le_refl _)

end FormalMultilinearSeries


section FormalMultilinearSeriesField

variable {f : (ι → 𝕜) → F} {f' : (ι → 𝕜) → FormalMultilinearSeries 𝕜 (ι → 𝕜) F}

/-- Unlike `contDiff_update`, does not use `Classical.propDecidable` (caused problems with typeclasses). -/
lemma contDiff_update' (n : ℕ∞) (x : ∀ i, M i) (i : ι) : ContDiff 𝕜 n (Function.update x i) := by
  conv => arg 3; intro u; rw [← ContinuousLinearMap.updateL_apply (R := 𝕜)]
  exact (ContinuousLinearMap.contDiff _).comp (contDiff_prod_mk_right x)

-- Just for convenience.
lemma differentiable_update' (x : ∀ i, M i) (i : ι) : Differentiable 𝕜 (Function.update x i) :=
  (contDiff_update' 1 x i).differentiable (le_refl 1)


theorem ContDiff.orderedIteratedPiDeriv_eq_orderedIteratedFPiDeriv {n : ℕ} (hf : ContDiff 𝕜 n f) {js : Fin n → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = orderedIteratedFPiDeriv 𝕜 js f x 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    specialize @ih hf.of_succ
    rw [orderedIteratedPiDeriv_succ_left, orderedIteratedFPiDeriv_succ_apply_left]
    rw [← fpideriv_pideriv]
    simp
    change _ = ((fpideriv 𝕜 (js 0) (orderedIteratedFPiDeriv 𝕜 (Fin.tail js) f) x) 1) 1
    rw [fpideriv_apply, fpideriv_apply]
    simp_rw [ih]
    rw [fderiv_continuousMultilinear_apply_const_apply]
    change DifferentiableAt 𝕜 (orderedIteratedFPiDeriv 𝕜 (Fin.tail js) f ∘ Function.update x (js 0)) _
    refine DifferentiableAt.comp _ ?_ ?_
    . refine hf.differentiableAt_orderedIteratedFPiDeriv ?_
      norm_cast
      exact Nat.lt_succ_self n
    . exact differentiable_update' x (js 0) _


theorem ContDiff.orderedIteratedPiDeriv_eq_iteratedFDeriv_apply {n : ℕ} (hf : ContDiff 𝕜 n f) {js : Fin n → ι} {x : ι → 𝕜} :
    orderedIteratedPiDeriv js f x = iteratedFDeriv 𝕜 n f x (fun i => Pi.single (js i) 1) := by
  rw [hf.orderedIteratedPiDeriv_eq_orderedIteratedFPiDeriv]
  rw [hf.orderedIteratedFPiDeriv_apply_eq_iteratedFDeriv_apply_single (le_refl _)]
  rfl


lemma ContDiff.differentiable_orderedIteratedPiDeriv {n : ℕ} {N : ℕ∞} (hn : n < N) (hf : ContDiff 𝕜 N f) {js : Fin n → ι} :
    Differentiable 𝕜 (orderedIteratedPiDeriv js f) := by
  conv =>
    arg 2; intro x
    rw [(hf.of_le (le_of_lt hn)).orderedIteratedPiDeriv_eq_orderedIteratedFPiDeriv]
  change Differentiable 𝕜 fun x => ContinuousMultilinearMap.apply 𝕜 _ _ 1 (orderedIteratedFPiDeriv 𝕜 js f x)
  exact (differentiable_const _).clm_apply (hf.differentiable_orderedIteratedFPiDeriv hn)


/-- The iterated partial derivative is continuous differentiable. -/
theorem ContDiff.orderedIteratedPiDeriv_right {m N : ℕ∞} {n : ℕ} (hn : m + n ≤ N) (hf : ContDiff 𝕜 N f) {js : Fin n → ι} :
    ContDiff 𝕜 m (_root_.orderedIteratedPiDeriv js f) := by
  have hfn : ContDiff 𝕜 n f := hf.of_le (le_trans (by simp) hn)
  conv => arg 3; intro x; rw [ContDiff.orderedIteratedPiDeriv_eq_iteratedFDeriv_apply hfn]
  exact continuousMultilinear_apply_const (hf.iteratedFDeriv_right hn)

end FormalMultilinearSeriesField

end Derivative
