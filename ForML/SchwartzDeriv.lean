import Mathlib.Analysis.Distribution.SchwartzSpace

open SchwartzSpace


namespace SchwartzMap

section Deriv

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fderiv of a Schwartz function is a differentiable map `E → E →L[ℝ] F`. -/
lemma differentiable_fderiv {f : 𝓢(E, F)} : Differentiable ℝ (fun x : E => fderiv ℝ f x) := by
  simp_rw [← SchwartzMap.fderivCLM_apply (𝕜 := ℝ)]
  exact SchwartzMap.differentiable _

/-- Any Schwartz-CLM is trivially differentiable. --/
lemma differentiable_clm {c : 𝓢(D, E →L[ℝ] F)} : Differentiable ℝ fun x => c x := SchwartzMap.differentiable c

/-- The application of a Schwartz-CLM commutes with fderiv. -/
lemma fderiv_clm_apply_const {c : 𝓢(D, E →L[ℝ] F)} :
    fderiv ℝ (fun y => c y u) x w =
    fderiv ℝ (fun y => c y) x w u := by
  rw [_root_.fderiv_clm_apply]
  . simp
  . exact differentiable_clm.differentiableAt
  . exact differentiableAt_const u

/-- Evaluating differential commutes with taking differential. -/
lemma fderiv_fderiv_apply {f : 𝓢(E, F)} : fderiv ℝ (fun y => fderiv ℝ f y u) x w = fderiv ℝ (fderiv ℝ f) x w u := by
  change fderiv ℝ (fun y => fderivCLM ℝ f y u) x w = _
  rw [fderiv_clm_apply_const]
  simp

end Deriv


section Iterated

-- Fix universes such that `E →L[ℝ] F` and `F` are in the same universe (for induction generalizing F).
universe i
variable {E F : Type i}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {c : 𝓢(E, E →L[ℝ] F)}  -- Consider any Schwartz-CLM `c`.
variable {x u w : E}

-- Prove that application of linear map commutes with taking repeated derivative.
-- That is, prove
-- `(iteratedFDeriv ℝ n (fun y => c y) x v) u = iteratedFDeriv ℝ n (fun y => (c y) u) x v`
-- Prove by induction, therefore need to prove
-- `(iteratedFDeriv ℝ (n + 1) (fun y => c y) x vw) u = iteratedFDeriv ℝ (n + 1) (fun y => (c y) u) x vw`.
-- Expanding both `iteratedFDeriv` expressions on the right gives:
-- lhs: `((iteratedFDeriv ℝ n (fun z => fderiv ℝ (fun y => c y) z) x v) w) u`
-- rhs: `(iteratedFDeriv ℝ n (fun z => fderiv ℝ (fun y => (c y) u) z) x v) w`

-- rhs:
-- We can apply the inductive hypothesis on the right
-- Rewrite as application of Schwartz-CLM using `evalCLM`.
-- `(iteratedFDeriv ℝ n (fun z => fderiv ℝ (fun y => (c y) u) z) x v) w`
-- `(iteratedFDeriv ℝ n (fun z => fderivCLM ℝ (evalCLM u c) z) x v) w`
-- `iteratedFDeriv ℝ n (fun z => fderivCLM ℝ (evalCLM u c) z w) x v`
-- Now we have `u` and `w` in the inner function.
-- We can eliminate the CLMs.
-- `iteratedFDeriv ℝ n (fun z => fderiv ℝ (fun y => c y u) w) x v`

example {z : E} : fderiv ℝ (fun y => (c y) u) z = fderivCLM ℝ (SchwartzMap.evalCLM (𝕜 := ℝ) u c) z := rfl

-- lhs:
-- We can apply the inductive hypothesis before application to `u`.
-- `((iteratedFDeriv ℝ n (fun z => fderiv ℝ c z) x v) w) u`
-- `((iteratedFDeriv ℝ n (fun z => fderivCLM ℝ c z) x v) w) u`
-- `(iteratedFDeriv ℝ n (fun z => fderivCLM ℝ c z w) x v) u`
-- We can apply the inductive hypothesis again to bring `u` inside.
-- Rewrite using `pderivCLM` to have application of SchwartzCLM to `z`.
-- `(iteratedFDeriv ℝ n (fun z => pderivCLM ℝ w c z) x v) u`
-- `(iteratedFDeriv ℝ n (fun z => (pderivCLM ℝ w c z) u) x v)`
-- We can eliminate the CLMs.
-- `iteratedFDeriv ℝ n (fun z => (fderiv ℝ c z w) u) x v`
-- Now we have `u` and `w` in the inner function.

example {z : E} : fderivCLM ℝ c z w = pderivCLM ℝ w c z := rfl
example {z : E} : (pderivCLM ℝ w c z) u = (fderiv ℝ c z w) u := rfl

-- Then it just remains to show that:
-- `(fderiv ℝ c z w) u = (fderiv ℝ (fun x => c x u) z) w`
-- This can be obtained using `fderiv_clm_apply_const`.


/- The application of a Schwartz-CLM can be moved outside iteratedFDeriv. -/
lemma iteratedFDeriv_clm_apply {n : ℕ} {m : Fin n → E} :
    iteratedFDeriv ℝ n (fun y => c y u) x m =
    iteratedFDeriv ℝ n (fun y => c y) x m u := by
  -- We will apply the inductive hypothesis in the other direction.
  symm
  -- Generalize over `F` to use inductive hypothesis with `𝓢(E, E →L[ℝ] (E →L[ℝ] F))`.
  induction n generalizing F u with
  | zero => rfl
  | succ n h_ind =>
    simp [iteratedFDeriv_succ_apply_right]
    -- Rename `m = Fin.snoc v w` for clarity.
    generalize (Fin.init m) = v
    generalize (m (Fin.last n)) = w
    -- Apply induction on right.
    -- Use `fderivCLM ℝ (evalCLM ..) ..` to have application of Schwartz function.
    change _ = iteratedFDeriv ℝ n (fun y => fderivCLM ℝ (SchwartzMap.evalCLM (𝕜 := ℝ) u c) y) x v w
    rw [h_ind]
    -- Remove `evalCLM`.
    change _ = iteratedFDeriv ℝ n (fun y => fderiv ℝ (fun x => c x u) y w) x v
    -- Apply induction on left.
    -- Use `fderivCLM ℝ ..` to have application of Schwartz function.
    change iteratedFDeriv ℝ n (fun y => fderivCLM ℝ c y) x v w u = _
    -- Apply induction with `c : 𝓢(E, E →L[ℝ] E →L[ℝ] F)` and therefore `F := E →L[ℝ] F`.
    -- This requires that `F` and `E →L[ℝ] F` are in the same universe.
    rw [h_ind]
    -- Use `pderivCLM ℝ ..` to have application of Schwartz function.
    change (iteratedFDeriv ℝ n (fun y => pderivCLM ℝ w c y) x) v u = _
    rw [h_ind]
    congr
    ext z
    simp
    exact fderiv_clm_apply_const.symm


section Equal

variable {𝕜 : Type*} [IsROrC 𝕜]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable {n : ℕ} {m : Fin n → E} {f : 𝓢(E, F)}

lemma iteratedPDeriv_eq_iteratedFDeriv :
    iteratedPDeriv 𝕜 m f x = iteratedFDeriv ℝ n f x m := by
  induction n generalizing f with
  | zero => simp
  | succ n h_ind =>
    rw [iteratedPDeriv_succ_right]
    rw [h_ind]
    rw [iteratedFDeriv_succ_apply_right]
    simp
    generalize (Fin.init m) = v
    generalize (m (Fin.last n)) = w
    change iteratedFDeriv ℝ n (fun y => (fderivCLM ℝ f) y w) x v = iteratedFDeriv ℝ n (fun y => (fderivCLM ℝ f) y) x v w
    rw [iteratedFDeriv_clm_apply]

end Equal

end Iterated

end SchwartzMap  -- namespace
