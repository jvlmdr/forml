import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pi

attribute [-simp] Matrix.zero_empty

section Derivative

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
-- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
-- variable {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]


lemma HasFDerivAt.hasDerivAt_comp_update {i : ι} {f : (ι → 𝕜) → F} {f' : (ι → 𝕜) →L[𝕜] F} {x : ι → 𝕜}
    (hf : HasFDerivAt f f' x) :
    HasDerivAt (fun u => f (Function.update x i u)) (f' (Pi.single i 1)) (x i) := by
  change HasDerivAt (f ∘ Function.update x i) _ _
  have : HasFDerivAt (f ∘ Function.update x i) (f'.comp (.pi (Pi.single i (.id 𝕜 𝕜)))) (x i)
  . refine HasFDerivAt.comp _ (by simpa using hf) (hasFDerivAt_update x _)
  refine HasDerivAt.congr_deriv this.hasDerivAt ?_
  simp
  refine congrArg _ ?_
  ext j
  by_cases h : j = i
  . rw [h]; simp
  . simp [h]

lemma deriv_comp_update {i : ι} {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun u => f (Function.update x i u)) (x i) = fderiv 𝕜 f x (Pi.single i 1) :=
  hf.hasFDerivAt.hasDerivAt_comp_update.deriv

-- TODO: Add `HasFDerivAt.hasFDerivAt_comp_update`?
-- (Only needed `hasDerivAt_comp_update` to apply integration by parts to partial derivative.)
