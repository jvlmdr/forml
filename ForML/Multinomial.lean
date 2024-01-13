import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Choose.Multinomial

import ForML.Multichoose

open scoped BigOperators

namespace Finset

variable {ι κ : Type*}

-- TODO: Is this the most natural choice? Better to use `MapsTo` and... inverse?
-- TODO: Add product and sum together?
/-- Convenient form of `Finset.sum_nbij` using composition with the inverse. -/
lemma sum_bijOn_comp_leftInvOn {E : Type*} [AddCommMonoid E]
    {s : Finset ι} {t : Finset κ} {f : ι → E} {e : ι → κ} {e' : κ → ι}
    (he : Set.BijOn e s t) (he' : Set.LeftInvOn e' e s) :
    ∑ i in s, f i = ∑ i in t, f (e' i) :=
  sum_nbij (i := e) (fun _ hx ↦ he.1 hx) he.2.1 he.2.2 (fun _ hx ↦ congrArg f (he' hx).symm)

end Finset

variable {α : Type*} [DecidableEq α]
variable {β : Type*} [DecidableEq β]

namespace Multiset

@[simp]
lemma multinomial_zero : multinomial (0 : Multiset α) = 1 := rfl

theorem card_filter_ne (a : α) (s : Multiset α) :
    card (s.filter (fun x => x ≠ a)) = card s - s.count a := by
  conv => rhs; lhs; rw [← Multiset.filter_add_not (fun x => x = a) s]
  simp only [_root_.map_add, count_eq_card_filter_eq, ne_eq, eq_comm (a := a)]
  rw [Nat.add_sub_cancel_left]

end Multiset

namespace Prod

def mkFstEmbedding (b : β) : α ↪ α × β := ⟨fun x ↦ (x, b), by simp [Function.Injective]⟩
def mkSndEmbedding (a : α) : β ↪ α × β := ⟨fun x ↦ (a, x), by simp [Function.Injective]⟩

@[simp] lemma mkFstEmbedding_apply (b : β) (x : α) : mkFstEmbedding b x = (x, b) := rfl
@[simp] lemma mkSndEmbedding_apply (a : α) (x : β) : mkSndEmbedding a x = (a, x) := rfl

end Prod

-- lemma Multiset.multinomial_eq {m : Multiset α} : m.multinomial = Nat.multinomial m.toFinset m.count := by
--   simp [Multiset.multinomial, Finsupp.multinomial_eq]
--   rfl

variable {E : Type*}  -- TODO: Rename/remove?

-- `[CommMonoid A]` for `Finset.prod`
-- `[NormedRing A] [NormedAlgebra 𝕜 A]` to be like `norm_iteratedFDeriv_mul_le`
variable {A : Type*} [CommSemiring A]  -- CommMonoid?


section Split

namespace Finset

-- TODO: Would it be better to use `Fin k.succ × Multiset α`?
/--
Image of count-remove on `Finset.multichoose k s`, defined as a `Finset`.
Equivalent to `{q : ℕ × Multiset (Fin n) | q.1 ≤ k ∧ q.2 ∈ Finset.multichoose (k - q.1) Finset.univ}`.
-/
def multichooseSplit (k : ℕ) (s : Finset α) (x : α) : Finset (ℕ × Multiset α) :=
  (range k.succ).biUnion fun m ↦ (multichoose (k - m) (s.erase x)).map (Prod.mkSndEmbedding m)

theorem mem_multichooseSplit_iff {k : ℕ} {s : Finset α} {x : α} {q : ℕ × Multiset α} :
    q ∈ multichooseSplit k s x ↔ q.1 ≤ k ∧ q.2 ∈ multichoose (k - q.1) (s.erase x) := by
  rcases q with ⟨m, t⟩
  simp [multichooseSplit, Nat.lt_succ]

/-- Helper lemma for `multichooseSplitEquiv`. -/
theorem prodCountFilterNe_mem_multichooseSplit {k : ℕ} {s : Finset α} {x : α}
    {t : Multiset α} (ht : t ∈ multichoose k s) :
    (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t) ∈ multichooseSplit k s x := by
  rw [mem_multichoose_iff] at ht
  rcases ht with ⟨ht_card, ht_mem⟩
  simp only [← ht_card]
  refine mem_multichooseSplit_iff.mpr (And.intro ?_ ?_)
  · exact Multiset.count_le_card x t
  · refine mem_multichoose_iff.mpr (And.intro ?_ ?_)
    · rw [← Multiset.card_filter_ne]
    · simp only [Multiset.mem_filter, mem_erase, and_imp]
      intro a ha
      simp [ht_mem a ha]

/-- Helper lemma for `multichooseSplitEquiv`. -/
theorem replicateAdd_mem_multichoose {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s)
    {q : ℕ × Multiset α} (hq : q ∈ multichooseSplit k s x) :
    Multiset.replicate q.1 x + q.2 ∈ multichoose k s := by
  rcases q with ⟨m, t⟩
  simp only [mem_multichooseSplit_iff, mem_multichoose_iff] at hq
  rcases hq with ⟨hm, ht_card, ht_mem⟩
  refine mem_multichoose_iff.mpr (And.intro ?_ ?_)
  · simp [ht_card, hm]
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    cases ha with
    | inl ha => rw [ha.2]; exact hx
    | inr ha => exact mem_of_mem_erase (ht_mem a ha)

theorem replicateAdd_countConsFilterNe_eq_self {x : α} {t : Multiset α} :
    Multiset.replicate (t.count x) x + Multiset.filter (fun a => a ≠ x) t = t := by
  simp [Set.LeftInvOn, ← Multiset.filter_eq', Multiset.filter_add_not]

theorem countConsFilterNe_replicateAdd_eq_self {k : ℕ} {s : Finset α} {x : α} :
    ∀ q ∈ Finset.multichooseSplit k s x,
    ⟨(Multiset.replicate q.1 x + q.2).count x,
      (Multiset.replicate q.1 x + q.2).filter (fun a => a ≠ x)⟩ = q := by
  intro q
  rcases q with ⟨m, t⟩
  simp only [mem_coe, mem_multichooseSplit_iff, mem_multichoose_iff, and_imp]
  intro _ _ ht_mem
  refine Prod.mk.inj_iff.mpr (And.intro ?_ ?_)
  · rw [Multiset.count_add, Multiset.count_replicate_self]
    rw [add_right_eq_self, Multiset.count_eq_zero]
    intro hxt
    exact not_mem_erase x s (ht_mem x hxt)
  · rw [Multiset.filter_add]
    rw [Multiset.filter_eq_nil.mpr (by simp [Multiset.mem_replicate])]
    rw [Multiset.filter_eq_self.mpr (fun a ha ↦ ne_of_mem_erase (ht_mem a ha))]
    simp

theorem mapsTo_prodCountFilterNe_multichoose {k : ℕ} {s : Finset α} {x : α} :
    Set.MapsTo (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t))
      (multichoose k s) (multichooseSplit k s x) :=
  fun _ ht ↦ prodCountFilterNe_mem_multichooseSplit ht

theorem mapsTo_replicateAdd_multichooseSplit {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    Set.MapsTo (fun q : ℕ × Multiset α ↦ Multiset.replicate q.1 x + q.2)
      (multichooseSplit k s x) (multichoose k s) :=
  fun _ hq ↦ replicateAdd_mem_multichoose hx hq

theorem image_replicateAdd_multichooseSplit {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    (multichooseSplit k s x).image (fun q ↦ Multiset.replicate q.1 x + q.2) = multichoose k s := by
  ext t
  simp only [mem_image]
  refine Iff.intro ?_ ?_
  . simp only [forall_exists_index, and_imp]
    intro q hq ht
    rw [← ht]
    exact replicateAdd_mem_multichoose hx hq
  . intro ht
    use (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t)
    refine And.intro ?_ ?_
    . exact prodCountFilterNe_mem_multichooseSplit ht
    . simp [replicateAdd_countConsFilterNe_eq_self]

theorem image_prodCountFilterNe_multichoose {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    (multichoose k s).image (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t)) =
      multichooseSplit k s x := by
  ext q
  simp only [mem_image]
  refine Iff.intro ?_ ?_
  . simp only [forall_exists_index, and_imp]
    intro t ht hq
    rw [← hq]
    exact prodCountFilterNe_mem_multichooseSplit ht
  . intro hq
    use Multiset.replicate q.1 x + q.2
    refine And.intro ?_ ?_
    . refine replicateAdd_mem_multichoose hx hq
    . exact countConsFilterNe_replicateAdd_eq_self q hq


theorem leftInverse_prodCountFilterNe_multichoose {x : α} :
    Function.LeftInverse (fun q ↦ Multiset.replicate q.1 x + q.2)
      (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t)) :=
  fun _ ↦ replicateAdd_countConsFilterNe_eq_self

theorem leftInvOn_replicateAdd_multichooseSplit {k : ℕ} {s : Finset α} {x : α} :
    Set.LeftInvOn (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t))
      (fun q ↦ Multiset.replicate q.1 x + q.2)
      (multichooseSplit k s x) :=
  fun q hq ↦ countConsFilterNe_replicateAdd_eq_self q hq

theorem invOn_prodCountFilterNe_multichoose {k : ℕ} {s : Finset α} {x : α} :
    Set.InvOn
      (fun q ↦ Multiset.replicate q.1 x + q.2)
      (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t))
      (multichoose k s)
      (multichooseSplit k s x) :=
  ⟨leftInverse_prodCountFilterNe_multichoose.leftInvOn _,
    leftInvOn_replicateAdd_multichooseSplit⟩

-- Combine `inv` and `mapsTo` to obtain `inj`, `surj`, `bij`.

theorem injective_prodCountFilterNe_multichoose {x : α} :
    Function.Injective (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t)) :=
  leftInverse_prodCountFilterNe_multichoose.injective

theorem surjective_replicateAdd_multichooseSplit {x : α} :
    Function.Surjective (fun q : ℕ × Multiset α ↦ Multiset.replicate q.1 x + q.2) :=
  leftInverse_prodCountFilterNe_multichoose.surjective

theorem injOn_replicateAdd_multichooseSplit {k : ℕ} {s : Finset α} {x : α} :
    Set.InjOn (fun q : ℕ × Multiset α ↦ Multiset.replicate q.1 x + q.2)
      (multichooseSplit k s x) :=
  leftInvOn_replicateAdd_multichooseSplit.injOn

theorem surjOn_prodCountFilterNe_multichoose {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    Set.SurjOn (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t))
      (multichoose k s) (multichooseSplit k s x) :=
  leftInvOn_replicateAdd_multichooseSplit.surjOn (mapsTo_replicateAdd_multichooseSplit hx)

theorem bijOn_prodCountFilterNe_multichoose {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    Set.BijOn (fun t ↦ (Multiset.count x t, Multiset.filter (fun a => a ≠ x) t))
      (multichoose k s) (multichooseSplit k s x) :=
  invOn_prodCountFilterNe_multichoose.bijOn
    mapsTo_prodCountFilterNe_multichoose
    (mapsTo_replicateAdd_multichooseSplit hx)

theorem bijOn_addReplicate_multichooseSplit {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    Set.BijOn (fun q : ℕ × Multiset α ↦ Multiset.replicate q.1 x + q.2)
      (multichooseSplit k s x) (multichoose k s) :=
  (bijOn_prodCountFilterNe_multichoose hx).symm
    invOn_prodCountFilterNe_multichoose.symm

lemma pairwiseDisjoint_multichooseSplit (k : ℕ) (s : Finset α) (x : α) :
    Set.PairwiseDisjoint ↑(range (Nat.succ k))
      fun m ↦ ((s.erase x).multichoose (k - m)).map (Prod.mkSndEmbedding m) := by
  intro i _ j _ hij
  simp [disjoint_iff_ne, hij]

-- TODO: `multichoose_eq_biUnion_multichoose_erase`

def multichooseSplitEquiv (k : ℕ) {s : Finset α} {x : α} (hx : x ∈ s) :
    ↑(multichoose k s) ≃ ↑(multichooseSplit k s x) where
  toFun
    | ⟨t, ht⟩ => ⟨⟨t.count x, t.filter (fun a ↦ a ≠ x)⟩, prodCountFilterNe_mem_multichooseSplit ht⟩
  invFun
    | ⟨q, hq⟩ => ⟨Multiset.replicate q.1 x + q.2, replicateAdd_mem_multichoose hx hq⟩
  left_inv := by
    simp only [Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    exact fun t _ ↦ replicateAdd_countConsFilterNe_eq_self
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    exact fun q hq ↦ countConsFilterNe_replicateAdd_eq_self q hq

@[simp]
lemma apply_multichooseSplitEquiv (k : ℕ) {s : Finset α} {x : α} (hx : x ∈ s)
    (t : multichoose k s) :
    (multichooseSplitEquiv k hx t).val = (t.val.count x, t.val.filter (fun a ↦ a ≠ x)) := rfl

@[simp]
lemma apply_multichooseSplitEquiv_symm (k : ℕ) {s : Finset α} {x : α} (hx : x ∈ s)
    (q : multichooseSplit k s x) :
    ((multichooseSplitEquiv k hx).symm q).val = Multiset.replicate q.val.1 x + q.val.2 := rfl

end Finset  -- namespace

end Split

namespace Finset

theorem pow_sum {p : ℕ} {s : Finset α} {f : α → A} :
    (∑ i in s, f i) ^ p = ∑ k in s.multichoose p, k.multinomial * ∏ i in s, f i ^ k.count i := by
  induction s using Finset.induction generalizing p with
  | empty => cases p <;> simp
  | @insert a s ha ih =>
    -- Apply binomial theorem on left.
    rw [Finset.sum_insert ha, add_pow]
    -- Re-index sum on right.
    rw [sum_bijOn_comp_leftInvOn (bijOn_prodCountFilterNe_multichoose (mem_insert_self a s))
      (leftInverse_prodCountFilterNe_multichoose.leftInvOn _)]
    rw [multichooseSplit]
    rw [sum_biUnion (pairwiseDisjoint_multichooseSplit p _ a)]
    refine Finset.sum_congr rfl ?_
    simp only [mem_range, Nat.lt_succ]
    intro m hmp
    -- Apply inductive hypothesis on left.
    simp only [ih, Finset.mul_sum, Finset.sum_mul]
    -- Simplify inner sum on right.
    simp only [sum_map, erase_insert ha, Prod.mkSndEmbedding_apply]
    refine Finset.sum_congr rfl ?_
    intro t ht
    -- Separate the multinomial and product terms.
    suffices : (Multiset.replicate m a + t).multinomial = p.choose m * t.multinomial ∧
        ∏ i in insert a s, f i ^ (Multiset.replicate m a + t).count i = f a ^ m * ∏ i in s, f i ^ t.count i
    · rw [this.1, this.2, Nat.cast_mul]
      ring_nf
    rw [Finset.mem_multichoose_iff] at ht
    -- `s` is a disjoint union of `t` and `{a}`.
    have hat : a ∉ t := fun h ↦ ha (ht.2 a h)
    have hs_ne : ∀ i ∈ s, i ≠ a := fun i his hia ↦ by rw [hia] at his; exact ha his
    refine And.intro ?_ ?_
    · -- Split the multinomial term.
      rw [Multiset.multinomial_filter_ne a]
      refine congrArg₂ _ ?_ ?_
      · simp [ht.1, hmp, hat]
      · rw [Multiset.filter_add]
        simp only [ne_comm (a := a), Multiset.filter_add]
        rw [Multiset.filter_eq_nil.mpr (by simp [Multiset.mem_replicate])]
        rw [Multiset.filter_eq_self.mpr (fun u hu ↦ ne_of_mem_of_not_mem hu hat)]
        rw [zero_add]
    · -- Split the product.
      rw [Finset.prod_insert ha]
      refine congrArg₂ _ ?_ (Finset.prod_congr rfl ?_)
      · simp [hat]
      · intro i hi
        simp [Multiset.count_replicate, hs_ne i hi]

end Finset
