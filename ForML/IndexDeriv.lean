import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory SchwartzSpace Complex FourierTransform RealInnerProductSpace
open scoped BigOperators Real

section Derivative

universe u
variable {ι 𝕜 F : Type u}
variable [DecidableEq ι] [Fintype ι]
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma fderiv_comp_update_eq_fderiv_apply_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun xi => f (Function.update x i xi)) (x i) 1 = fderiv 𝕜 f x (Pi.single i 1) := by
  change fderiv 𝕜 (f ∘ Function.update x i) (x i) 1 = _
  rw [fderiv.comp _ (by simpa using hf) (hasFDerivAt_update _ _).differentiableAt]
  simp
  rw [ContinuousLinearMap.comp_apply]
  simp
  rw [fderiv_update]
  congr
  ext j
  simp
  simp [Pi.single_apply]
  by_cases h : j = i <;> simp [h]

lemma fderiv_comp_update_apply_eq_smul_fderiv_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} {m : 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun xi => f (Function.update x i xi)) (x i) m = m • fderiv 𝕜 f x (Pi.single i 1) := by
  suffices : fderiv 𝕜 (fun xi => f (Function.update x i xi)) (x i) (m • 1) = m • fderiv 𝕜 f x (Pi.single i 1)
  . simpa using this
  rw [ContinuousLinearMap.map_smul]
  rw [fderiv_comp_update_eq_fderiv_apply_single hf]

/-- The derivative with respect to one coordinate is the Fréchet derivative applied to its basis vector. -/
lemma deriv_comp_update_eq_fderiv_apply_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun xi => f (Function.update x i xi)) (x i) = fderiv 𝕜 f x (Pi.single i 1) := by
  rw [← fderiv_comp_update_eq_fderiv_apply_single hf, fderiv_deriv]

/-- The derivative with respect to one index of a pi type. -/
noncomputable def ideriv (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) : F :=
  deriv (f ∘ Function.update x i) (x i)

lemma ideriv_apply (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) :
    ideriv i f x = deriv (fun xi => f (Function.update x i xi)) (x i) := rfl

/-- The derivative with respect to one coordinate is equal to the Fréchet derivative applied to its basis vector. -/
lemma ideriv_eq_fderiv_apply_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    ideriv i f x = fderiv 𝕜 f x (Pi.single i 1) := deriv_comp_update_eq_fderiv_apply_single hf

noncomputable def ifderiv (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) : 𝕜 →L[𝕜] F :=
  fderiv 𝕜 (f ∘ Function.update x i) (x i)

lemma ifderiv_def {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} :
    ifderiv i f x = fderiv 𝕜 (fun xi => f (Function.update x i xi)) (x i) := rfl

lemma ifderiv_apply_one_eq_fderiv_apply_single {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    ifderiv i f x 1 = fderiv 𝕜 f x (Pi.single i 1) := by
  rw [ifderiv_def, fderiv_comp_update_eq_fderiv_apply_single hf]

lemma ifderiv_apply {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) {m : 𝕜} :
    ifderiv i f x m = m • fderiv 𝕜 f x (Pi.single i 1) := by
  rw [ifderiv_def]
  rw [fderiv_comp_update_apply_eq_smul_fderiv_single hf]

-- TODO: Is there some lemma for the norm of an lsum?
-- TODO: Upgrade to a CLM?
lemma fderiv_toLinearMap_eq_lsum_ifderiv {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    ↑(fderiv 𝕜 f x) = LinearMap.lsum 𝕜 (fun _ : ι => 𝕜) 𝕜 (fun i => (ifderiv i f x).toLinearMap) := by
  refine LinearMap.ext ?_
  intro dx
  simp
  rw [LinearMap.pi_apply_eq_sum_univ]
  congr
  ext i
  rw [ifderiv_apply hf]
  simp_rw [← Pi.single_apply]
  simp_rw [Pi.single_comm]
  rfl

/-- The Fréchet derivative can be written as a sum of partial derivatives over coordinates. -/
lemma fderiv_apply_eq_sum_smul_ideriv {f : (ι → 𝕜) → F} {x dx : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x dx = ∑ i, dx i • ideriv i f x := by
  change (fderiv 𝕜 f x).toLinearMap dx = _
  rw [LinearMap.pi_apply_eq_sum_univ]
  congr
  ext i
  rw [ideriv_eq_fderiv_apply_single hf]
  simp_rw [← Pi.single_apply]
  simp_rw [Pi.single_comm]
  rfl

lemma fderiv_apply_eq_sum_smul_ideriv' {f : (ι → 𝕜) → F} {x dx : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x dx = (∑ i, dx i • ideriv i f) x := by
  simp
  exact fderiv_apply_eq_sum_smul_ideriv hf

/--
A bound on canonical partial derivatives gives a bound on the operator norm of the Fréchet derivative.

TODO: Can the `Fintype.card` factor be eliminated?
-/
lemma norm_fderiv_le_of_norm_ideriv_le {f : (ι → 𝕜) → F} {x : ι → 𝕜} {M : ℝ}
    (hf : DifferentiableAt 𝕜 f x)
    (hM : 0 ≤ M)
    (hM_bound : ∀ i, ‖ideriv i f x‖ ≤ M) :
    ‖fderiv 𝕜 f x‖ ≤ (Fintype.card ι) • M := by
  rw [ContinuousLinearMap.op_norm_le_iff (nsmul_nonneg hM _)]
  intro u
  rw [fderiv_apply_eq_sum_smul_ideriv hf]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Pi.norm_def]
  rw [smul_mul_assoc]
  refine Finset.sum_le_card_nsmul _ _ _ ?_
  intro i _
  rw [norm_smul]
  rw [mul_comm]
  refine mul_le_mul (hM_bound i) ?_ (norm_nonneg _) hM
  exact norm_le_pi_norm u i

end Derivative
