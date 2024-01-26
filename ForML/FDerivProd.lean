-- https://github.com/leanprover-community/mathlib4/pull/10022

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Multinomial

open scoped BigOperators


namespace Finset  -- Mathlib/Algebra/BigOperators/Basic.lean

variable {ι : Type*} {β : Type u} {α : Type v}

section
variable [CommMonoid β]

@[to_additive]
theorem prod_update_one_of_mem [DecidableEq α] {s : Finset α} {i : α} (hi : i ∈ s) (f : α → β) :
    ∏ j in s, Function.update f i 1 j = ∏ j in s \ singleton i, f j := by
  simp [prod_update_of_mem hi]

end

section
variable [Fintype ι] [CommMonoid α]

@[to_additive]
theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι → α) (i : ↑s) :
    ∏ j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f j := by
  simp only [erase_eq]
  rw [← prod_update_one_of_mem i.prop, ← prod_update_one_of_mem (mem_attach s i)]
  rw [← prod_coe_sort s]
  refine prod_congr rfl ?_
  intro j _
  simp only [← Function.comp_apply (g := Subtype.val) (x := j)]
  rw [Function.update_comp_eq_of_injective _ Subtype.val_injective]
  rfl

end

end Finset


section  -- Mathlib/Analysis/Calculus/ContDiff/Basic.lean

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {D : Type uD} [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s s₁ t u : Set E} {f f₁ : E → F}
  {g : F → G} {x x₀ : E} {c : F} {b : E × F → G} {m n : ℕ∞} {p : E → FormalMultilinearSeries 𝕜 E F}

@[simp]
theorem iteratedFDerivWithin_zero_fun (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} :
    iteratedFDerivWithin 𝕜 i (fun _ : E ↦ (0 : F)) s x = 0 := by
  induction i generalizing x with
  | zero => ext; simp
  | succ i IH =>
    ext m
    rw [iteratedFDerivWithin_succ_apply_left, fderivWithin_congr (fun _ ↦ IH) (IH hx)]
    rw [fderivWithin_const_apply _ (hs x hx)]
    rfl

theorem iteratedFDerivWithin_succ_const (n : ℕ) (c : F) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E ↦ c) s x = 0 := by
  ext m
  rw [iteratedFDerivWithin_succ_apply_right hs hx]
  rw [iteratedFDerivWithin_congr (fun y hy ↦ fderivWithin_const_apply c (hs y hy)) hx]
  rw [iteratedFDerivWithin_zero_fun hs hx]
  simp [ContinuousMultilinearMap.zero_apply (R := 𝕜)]

theorem iteratedFDerivWithin_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 n (fun _ : E ↦ c) s x = 0 := by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const _ _ hs hx

section

variable {ι : Type*} [DecidableEq ι]

theorem iteratedFDerivWithin_sum_apply {f : ι → E → F} {u : Finset ι} {i : ℕ} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : ∀ j ∈ u, ContDiffOn 𝕜 i (f j) s) :
    iteratedFDerivWithin 𝕜 i (∑ j in u, f j ·) s x =
      ∑ j in u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  induction u using Finset.induction with
  | empty => ext; simp [hs, hx]
  | @insert a u ha IH =>
    simp only [Finset.mem_insert] at h
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    simp only [Finset.sum_insert ha]
    rw [iteratedFDerivWithin_add_apply' h.1 (ContDiffOn.sum h.2) hs hx, IH h.2]

theorem iteratedFDeriv_sum {f : ι → E → F} {u : Finset ι} {i : ℕ}
    (h : ∀ j ∈ u, ContDiff 𝕜 i (f j)) :
    iteratedFDeriv 𝕜 i (∑ j in u, f j ·) = ∑ j in u, iteratedFDeriv 𝕜 i (f j) := by
  simp only [← iteratedFDerivWithin_univ]
  funext x
  rw [Finset.sum_apply]
  exact iteratedFDerivWithin_sum_apply uniqueDiffOn_univ trivial fun j hj ↦ (h j hj).contDiffOn

end


section  -- Mathlib/Analysis/Calculus/FDeriv/Mul.lean

open ContinuousLinearMap

section Prod

open BigOperators

/-! ### Derivative of a finite product of functions -/

variable {ι : Type*} [DecidableEq ι] {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → E → 𝔸'} {f' : ι → E →L[𝕜] 𝔸'}

section Fintype

variable [Fintype ι]

theorem hasStrictFDerivAt_finset_prod_univ {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (∏ i, · i) (∑ i, (∏ j in Finset.univ.erase i, x j) • proj i) x := by
  generalize (Finset.univ : Finset ι) = u
  induction u using Finset.induction with
  | empty => simp [hasStrictFDerivAt_const]
  | @insert i u hi IH =>
    simp only [Finset.prod_insert hi]
    refine ((proj i).hasStrictFDerivAt.mul' IH).congr_fderiv ?_
    simp only [Finset.sum_insert hi, Finset.erase_insert hi]
    rw [add_comm]
    refine congrArg₂ _ ?_ ?_
    · ext m
      simp only [smulRight_apply (R := 𝕜), smul_apply, smul_eq_mul]
      exact mul_comm _ _
    · ext m
      simp only [smul_apply (R₁ := 𝕜), sum_apply (R₁ := 𝕜), Finset.smul_sum, smul_smul, proj_apply]
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [Finset.erase_insert_of_ne fun hik ↦ hi <| by simpa [hik]]
      rw [Finset.prod_insert <| by simp [hi]]

theorem hasFDerivAt_finset_prod_univ {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (∏ i, · i) (∑ i, (∏ j in Finset.univ.erase i, x j) • proj i) x :=
  hasStrictFDerivAt_finset_prod_univ.hasFDerivAt

theorem ContinuousMultilinearMap.hasStrictFDerivAt_mkPiAlgebra {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝔸')
      (∑ i, (∏ j in Finset.univ.erase i, x j) • proj i) x :=
  hasStrictFDerivAt_finset_prod_univ

theorem ContinuousMultilinearMap.hasFDerivAt_mkPiAlgebra {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝔸')
      (∑ i, (∏ j in Finset.univ.erase i, x j) • proj i) x :=
  hasStrictFDerivAt_mkPiAlgebra.hasFDerivAt

theorem HasFDerivAt.finset_prod_univ {x : E} (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (∏ i, f i ·) (∑ i, (∏ j in Finset.univ.erase i, f j x) • f' i) x := by
  refine (hasFDerivAt_finset_prod_univ.comp x <| hasFDerivAt_pi.mpr hf).congr_fderiv ?_
  ext m
  simp [comp_apply (R₁ := 𝕜), sum_apply (R₁ := 𝕜), smul_apply]

theorem HasStrictFDerivAt.finset_prod_univ {x : E} (hf : ∀ i, HasStrictFDerivAt (f i) (f' i) x) :
    HasStrictFDerivAt (∏ i, f i ·) (∑ i, (∏ j in Finset.univ.erase i, f j x) • f' i) x := by
  refine (hasStrictFDerivAt_finset_prod_univ.comp x <| hasStrictFDerivAt_pi.mpr hf).congr_fderiv ?_
  ext m
  simp [comp_apply (R₁ := 𝕜), sum_apply (R₁ := 𝕜), smul_apply]

theorem HasFDerivWithinAt.finset_prod_univ {x : E} (hf : ∀ i, HasFDerivWithinAt (f i) (f' i) s x) :
    HasFDerivWithinAt (∏ i, f i ·) (∑ i, (∏ j in Finset.univ.erase i, f j x) • f' i) s x := by
  refine HasFDerivWithinAt.congr_fderiv
    (hasFDerivAt_finset_prod_univ.comp_hasFDerivWithinAt x <| hasFDerivWithinAt_pi.mpr hf) ?_
  ext m
  simp [comp_apply (R₁ := 𝕜), sum_apply (R₁ := 𝕜), smul_apply]

end Fintype

section Comp

theorem HasFDerivAt.finset_prod {x : E} (hf : ∀ i ∈ u, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, (f j x)) • f' i) x := by
  simp only [← Finset.prod_coe_sort u]
  refine (finset_prod_univ fun i : u ↦ hf i i.prop).congr_fderiv ?_
  rw [← Finset.sum_attach u, Finset.univ_eq_attach]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg₂ _ (Finset.prod_erase_attach (f · x) i) rfl

theorem HasFDerivWithinAt.finset_prod {x : E} (hf : ∀ i ∈ u, HasFDerivWithinAt (f i) (f' i) s x) :
    HasFDerivWithinAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, (f j x)) • f' i) s x := by
  simp only [← Finset.prod_coe_sort u]
  refine (finset_prod_univ fun i : u ↦ hf i i.prop).congr_fderiv ?_
  rw [← Finset.sum_attach u, Finset.univ_eq_attach]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg₂ _ (Finset.prod_erase_attach (f · x) i) rfl

theorem HasStrictFDerivAt.finset_prod {x : E} (hf : ∀ i ∈ u, HasStrictFDerivAt (f i) (f' i) x) :
    HasStrictFDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, (f j x)) • f' i) x := by
  simp only [← Finset.prod_coe_sort u]
  refine (finset_prod_univ fun i : u ↦ hf i i.prop).congr_fderiv ?_
  rw [← Finset.sum_attach u, Finset.univ_eq_attach]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg₂ _ (Finset.prod_erase_attach (f · x) i) rfl

theorem fderiv_finset_prod {x : E} (hf : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    fderiv 𝕜 (∏ i in u, f i ·) x = ∑ i in u, (∏ j in u.erase i, (f j x)) • fderiv 𝕜 (f i) x :=
  (HasFDerivAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivAt)).fderiv

theorem fderivWithin_finset_prod {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hf : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    fderivWithin 𝕜 (∏ i in u, f i ·) s x =
      ∑ i in u, (∏ j in u.erase i, (f j x)) • fderivWithin 𝕜 (f i) s x :=
  (HasFDerivWithinAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivWithinAt)).fderivWithin hxs

end Comp

end Prod

end


section  -- Mathlib/Analysis/Calculus/Deriv/Mul.lean

variable {x : 𝕜}
variable {s t : Set 𝕜}

section Prod

variable {ι : Type*} [DecidableEq ι] {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → 𝕜 → 𝔸'} {f' : ι → 𝔸'}

theorem HasDerivAt.finset_prod (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasFDerivAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivAt)).hasDerivAt

theorem HasDerivWithinAt.finset_prod (hf : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) s x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasFDerivWithinAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivWithinAt)).hasDerivWithinAt

theorem HasStrictDerivAt.finset_prod (hf : ∀ i ∈ u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasStrictFDerivAt.finset_prod (fun i hi ↦ (hf i hi).hasStrictFDerivAt)).hasStrictDerivAt

theorem deriv_finset_prod (hf : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i in u, f i ·) x = ∑ i in u, (∏ j in u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.finset_prod fun i hi ↦ (hf i hi).hasDerivAt).deriv

theorem derivWithin_finset_prod (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hf : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i in u, f i ·) s x =
      ∑ i in u, (∏ j in u.erase i, f j x) • derivWithin (f i) s x :=
  (HasDerivWithinAt.finset_prod fun i hi ↦ (hf i hi).hasDerivWithinAt).derivWithin hxs

end Prod

end


namespace Sym  -- Mathlib/Data/Sym/Basic.lean

open Multiset

variable {α β : Type*} {n n' m : ℕ} {s : Sym α n} {a b : α}

@[simp]
theorem card_coe : Multiset.card (s : Multiset α) = n := s.prop

theorem count_coe_fill_self_of_not_mem [DecidableEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : a ∉ s) :
    count a (fill a i s : Multiset α) = i := by
  simp [coe_fill, coe_replicate, hx]

theorem count_coe_fill_of_ne [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : x ≠ a) :
    count x (fill a i s : Multiset α) = count x s := by
  suffices : x ∉ Multiset.replicate i a
  · simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

end Sym


section  -- Mathlib/Data/Nat/Choose/Multinomial.lean

namespace Multiset

variable {α : Type*}

@[simp]
theorem multinomial_zero [DecidableEq α] : multinomial (0 : Multiset α) = 1 := rfl

end Multiset

namespace Sym

variable {n : ℕ} {α : Type*} [DecidableEq α]

theorem multinomial_coe_fill_of_not_mem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s) :
    (fill x m s : Multiset α).multinomial = n.choose m * (s : Multiset α).multinomial := by
  rw [Multiset.multinomial_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_not_mem hx]
  · refine congrArg _ ?_
    rw [coe_fill, coe_replicate, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_right_eq_self]
      rw [Multiset.filter_eq_nil]
      exact fun j hj ↦ by simp [Multiset.mem_replicate.mp hj]
    · exact fun j hj h ↦ hx <| by simpa [h] using hj

end Sym

end


section  -- Mathlib/Analysis/Calculus/ContDiff/Bounds.lean

open Function

variable {A' : Type*} [NormedCommRing A'] [NormedAlgebra 𝕜 A']
variable {ι : Type*} [DecidableEq ι]

theorem norm_iteratedFDerivWithin_prod_le [NormOneClass A'] {u : Finset ι} {f : ι → E → A'}
    {N : ℕ∞} (hf : ∀ i ∈ u, ContDiffOn 𝕜 N (f i) s) (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (∏ j in u, f j ·) s x‖ ≤
      ∑ p in u.sym n, (p : Multiset ι).multinomial *
        ∏ j in u, ‖iteratedFDerivWithin 𝕜 ((p : Multiset ι).count j) (f j) s x‖ := by
  induction u using Finset.induction generalizing n with
  | empty =>
    cases n with
    | zero => simp [Sym.eq_nil_of_card_zero]
    | succ n => simp [iteratedFDerivWithin_succ_const _ _ hs hx]
  | @insert i u hi IH =>
    conv => lhs; simp only [Finset.prod_insert hi]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    refine le_trans (norm_iteratedFDerivWithin_mul_le hf.1 (contDiffOn_prod hf.2) hs hx hn) ?_
    rw [← Finset.sum_coe_sort (Finset.sym _ _)]
    rw [Finset.sum_equiv (Finset.symInsertEquiv hi) (t := Finset.univ)
      (g := (fun v ↦ v.multinomial *
          ∏ j in insert i u, ‖iteratedFDerivWithin 𝕜 (v.count j) (f j) s x‖) ∘
        Sym.toMultiset ∘ Subtype.val ∘ (Finset.symInsertEquiv hi).symm)
      (by simp) (by simp only [← comp_apply (g := Finset.symInsertEquiv hi), comp.assoc]; simp)]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_range]
    simp only [comp_apply, Finset.symInsertEquiv_symm_apply_coe]
    refine Finset.sum_le_sum ?_
    simp only [Finset.mem_univ, forall_true_left]
    intro m
    specialize IH hf.2 (n := n - m) (le_trans (WithTop.coe_le_coe.mpr (n.sub_le m)) hn)
    refine le_trans (mul_le_mul_of_nonneg_left IH (by simp [mul_nonneg])) ?_
    rw [Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_le_sum ?_
    simp only [Finset.mem_univ, forall_true_left, Subtype.forall, Finset.mem_sym_iff]
    intro p hp
    refine le_of_eq ?_
    rw [Finset.prod_insert hi]
    have hip : i ∉ p := fun h ↦ hi <| hp i h
    rw [Sym.count_coe_fill_self_of_not_mem hip, Sym.multinomial_coe_fill_of_not_mem hip]
    suffices : ∏ j in u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j p) (f j) s x‖ =
        ∏ j in u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j (Sym.fill i m p)) (f j) s x‖
    · rw [this, Nat.cast_mul]
      ring
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := fun h ↦ hi <| by simpa [h] using hj
    rw [Sym.count_coe_fill_of_ne hji]

theorem norm_iteratedFDeriv_prod_le [NormOneClass A'] {u : Finset ι} {f : ι → E → A'}
    {N : ℕ∞} (hf : ∀ i ∈ u, ContDiff 𝕜 N (f i)) {x : E} {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDeriv 𝕜 n (∏ j in u, f j ·) x‖ ≤
      ∑ p in u.sym n, (p : Multiset ι).multinomial *
        ∏ j in u, ‖iteratedFDeriv 𝕜 ((p : Multiset ι).count j) (f j) x‖ := by
  simpa [iteratedFDerivWithin_univ] using
    norm_iteratedFDerivWithin_prod_le (fun i hi ↦ (hf i hi).contDiffOn) uniqueDiffOn_univ trivial hn

end
