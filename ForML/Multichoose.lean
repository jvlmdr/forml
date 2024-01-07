import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Multiset.Basic

open scoped BigOperators List


theorem Nat.multichoose_zero_eq_zero_iff {k : ℕ} : multichoose 0 k = 0 ↔ k ≠ 0 := by
  simp [multichoose_eq, Nat.choose_eq_zero_iff]
  exact ⟨not_eq_zero_of_lt, pred_lt⟩

theorem Nat.multichoose_eq_zero_iff {n k : ℕ} (h : k ≤ n) : multichoose n k = 0 ↔ n = 0 ∧ k ≠ 0 := by
  simp [multichoose_eq, Nat.choose_eq_zero_iff, -ne_eq]
  cases k with
  | zero => simp
  | succ k =>
    simp
    rw [succ_eq_one_add]
    rw [add_lt_add_iff_right]
    rw [lt_one_iff]


namespace List

variable {α : Type*}

/--
Finds all lists of length `n` formed using the elements of `l` in order.
Like `List.sublists` but with replacement and a fixed output length.
Like `Multiset.powersetCard` but without duplicates (when the input has no duplicates).
-/
def multichoose : ℕ → List α → List (List α)
  | Nat.zero, _ => [[]]
  | Nat.succ _, [] => []
  | Nat.succ n, x :: xs => List.append
      (multichoose (n + 1) xs)
      (map (cons x) (multichoose n (x :: xs)))  -- Order these to match `List.sublists`.

@[simp]
lemma multichoose_zero {l : List α} : multichoose 0 l = [[]] := by rw [multichoose]

@[simp]
lemma multichoose_succ_nil {n : ℕ} : multichoose n.succ ([] : List α) = [] := rfl

lemma multichoose_succ_cons {n : ℕ} {x : α} {xs : List α} :
    multichoose n.succ (x :: xs) = List.append
      (multichoose (n + 1) xs)
      (map (cons x) (multichoose n (x :: xs))) := by
  rw [multichoose]

@[simp]
lemma multichoose_nil {n : ℕ} (hn : n ≠ 0) :
    multichoose n ([] : List α) = [] := by
  cases n with
  | zero => contradiction
  | succ n => rfl

@[simp]
lemma mem_multichoose_nil {n : ℕ} {t : List α} :
    t ∈ multichoose n ([] : List α) ↔ n = 0 ∧ t = [] := by
  cases n <;> simp

@[simp]
lemma multichoose_singleton {n : ℕ} {x : α} : multichoose n [x] = [replicate n x] := by
  induction n with
  | zero => simp
  | succ n ih => simp [multichoose_succ_cons, ih]

/-- Multichoose is empty iff `n` is non-zero and the list is empty. -/
@[simp]
theorem multichoose_eq_empty {n : ℕ} {l : List α} :
    multichoose n l = [] ↔ n ≠ 0 ∧ l = [] := by
  induction n with
  | zero => simp
  | succ n ihn =>
    simp
    cases l with
    | nil => simp
    | cons x xs => simp [multichoose_succ_cons, ihn]

/-- The number of elements in multichoose is equal to `Nat.multichoose`. -/
theorem length_multichoose {n : ℕ} {l : List α} :
    length (multichoose n l) = Nat.multichoose l.length n := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      simp [multichoose_succ_cons, Nat.multichoose_succ_succ]
      simp [ihn, ihl]

-- TODO: Add monotone lemma?

lemma mem_multichoose_succ_cons {n : ℕ} {x : α} {xs : List α} {t : List α} :
    t ∈ multichoose n.succ (x :: xs) ↔ t ∈ multichoose n.succ xs ∨ (∃ s ∈ multichoose n (x :: xs), t = x :: s) := by
  simp [multichoose_succ_cons]
  simp [eq_comm]

lemma cons_mem_multichoose_succ_cons {n : ℕ} {x y : α} {xs ys : List α} :
    y :: ys ∈ multichoose n.succ (x :: xs) ↔ y :: ys ∈ multichoose n.succ xs ∨ (y = x ∧ ys ∈ multichoose n (x :: xs)) := by
  simp [multichoose_succ_cons]
  simp [and_comm, eq_comm]

-- lemma mem_of_cons_mem_multichoose {n : ℕ} {l : List α} {y : α} {ys : List α} (ht : (y :: ys) ∈ multichoose n l) :
--     y ∈ l := by
--   cases n with
--   | zero => rw [multichoose] at ht; contradiction
--   | succ n =>
--     induction l with
--     | nil => contradiction
--     | cons x xs ih =>
--       rw [mem_cons]
--       simp [multichoose] at ht
--       cases ht with
--       | inl ht => exact Or.inl ht.2.symm
--       | inr ht => exact Or.inr (ih ht)

/-- All lists in `multichoose` are composed of elements from the original list. -/
theorem mem_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    ∀ u ∈ t, u ∈ l := by
  induction n generalizing t l with
  | zero => simp at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons y ys ihl =>
      -- Could use `cons_mem_multichoose_succ_cons` here to avoid `∃`; could be messier though.
      rw [mem_multichoose_succ_cons] at ht
      intro u hu
      cases ht with
      | inl ht => simpa using Or.inr (ihl ht u hu)
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        simp [ht] at hu
        cases hu with
        | inl hu => simpa using Or.inl hu
        | inr hu => simpa using ihn hs u hu

/-- All lists in `multichoose` have length `n`. -/
theorem length_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    t.length = n := by
  induction n generalizing t l with
  | zero => simp at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons x xs ihl =>
      simp [mem_multichoose_succ_cons] at ht
      cases ht with
      | inl ht => exact ihl ht
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        simp [ht]
        exact ihn hs

-- TODO: Add more general monotonicity using Sublist `<+`.

lemma mem_multichoose_of_cons {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) (x : α) :
    t ∈ multichoose n (x :: l) := by
  cases n with
  | zero => simpa using ht
  | succ n => simp [mem_multichoose_succ_cons, ht]

-- TODO: Generalize and move? Or eliminate?
/-- If a property holds for all elements in one list and none in the other list, they are disjoint. -/
theorem disjoint_of_forall_left {p : α → Prop} {l₁ l₂ : List α} (hl₁ : ∀ x ∈ l₁, p x) (hl₂ : ∀ x ∈ l₂, ¬p x) :
    Disjoint l₁ l₂ := fun x hx₁ hx₂ => hl₂ x hx₂ (hl₁ x hx₁)

/-- If a property holds for all elements in one list and none in the other list, they are disjoint. -/
theorem disjoint_of_forall_right {p : α → Prop} {l₁ l₂ : List α} (h₁ : ∀ x ∈ l₁, ¬p x) (h₂ : ∀ x ∈ l₂, p x) :
    Disjoint l₁ l₂ := (disjoint_of_forall_left h₂ h₁).symm

/-- If the list of elements contains no duplicates, then `multichoose` contains no duplicates. -/
theorem nodup_multichoose {n : ℕ} {l : List α} (hl : Nodup l) : Nodup (multichoose n l) := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      specialize ihn hl
      simp at hl
      specialize ihl hl.2
      simp [multichoose_succ_cons]
      refine Nodup.append ihl (ihn.map cons_injective) ?_
      refine disjoint_of_forall_right (p := fun l => x ∈ l) ?_ (by simp)
      simp
      intro y hy hx
      refine hl.1 ?_
      exact mem_of_mem_multichoose hy x hx

/-- If a list has no duplicates, then two elements of `multichoose` are permutations iff they are equal. -/
theorem perm_mem_multichoose [DecidableEq α] {n : ℕ} {l : List α} (hl : Nodup l)
    {t s : List α} (ht : t ∈ multichoose n l) (hs : s ∈ multichoose n l) :
    t ~ s ↔ t = s := by
  induction n generalizing s t l with
  | zero => simp at ht hs; simp [ht, hs]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons x xs ihl =>
      specialize @ihn _ hl
      simp at hl
      specialize ihl hl.2
      cases t with
      | nil => simp [eq_comm]
      | cons b bs =>
        cases s with
        | nil => simp [eq_comm]
        | cons c cs =>
          -- Must consider four cases:
          -- (1) `t` and `s` both use `x` (induction on `n`)
          -- (2) `t` and `s` both use only `xs` (induction on `l`)
          -- (3,4) only one of `t` and `s` uses `x` (not equal)
          simp [cons_mem_multichoose_succ_cons] at ht hs
          cases ht with
          | inr ht =>
            cases hs with
            | inr hs =>
              -- (1) `t` and `s` both use `x` (induction on `n`)
              simpa [ht.1, hs.1] using ihn ht.2 hs.2
            | inl hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [ht.1]
              replace hs := mem_of_mem_multichoose hs
              simp at hs
              have hc : x ≠ c := fun hx => by rw [← hx] at hs; exact hl.1 hs.1
              have hcs : x ∉ cs := fun hx => hl.1 (hs.2 x hx)
              simp [cons_perm_iff_perm_erase, hc, hcs]
          | inl ht =>
            cases hs with
            | inl hs =>
              -- (2) `t` and `s` both use only `xs` (induction on `l`)
              exact ihl ht hs
            | inr hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [hs.1]
              replace ht := mem_of_mem_multichoose ht
              simp at ht
              have hb : x ≠ b := fun hx => by rw [← hx] at ht; exact hl.1 ht.1
              have hbs : x ∉ bs := fun hx => hl.1 (ht.2 x hx)
              rw [perm_comm, eq_comm]
              simp [cons_perm_iff_perm_erase, hb, hbs]

/-- Any `Multiset` containing `n` elements in a list `l` has a corresponding list in `multichoose`. -/
theorem exists_mem_multichoose_eq_multiset [DecidableEq α] {n : ℕ} {l : List α}
    {t : Multiset α} (ht_len : Multiset.card t = n) (ht_mem : ∀ x ∈ t, x ∈ l) :
    ∃ s ∈ multichoose n l, Multiset.ofList s = t := by
  induction n generalizing t l with
  | zero =>
    simp [Multiset.card_eq_zero] at ht_len
    simp [ht_len]
  | succ n ihn =>
    induction l with
    | nil =>
      exfalso
      simp at ht_mem
      replace ht_len : 0 < Multiset.card t := Nat.lt_of_sub_eq_succ ht_len
      rw [Multiset.card_pos_iff_exists_mem] at ht_len
      rcases ht_len with ⟨x, hx⟩
      exact ht_mem x hx
    | cons x xs ihl =>
      cases Decidable.em (x ∈ t) with
      | inl hx =>
        -- Set `s = x :: _`; apply induction on `n` to obtain the rest of `s`.
        specialize ihn (l := x :: xs) (t := t.erase x) ?_ ?_
        . simp [hx, ht_len]
        . exact fun u hu => ht_mem u (Multiset.mem_of_mem_erase hu)
        rcases ihn with ⟨rs, hrs_mem, hrs_perm⟩
        use x :: rs
        refine And.intro ?_ ?_
        . simp [cons_mem_multichoose_succ_cons, hrs_mem]
        . rw [← Multiset.cons_coe]
          rw [hrs_perm]
          rw [Multiset.cons_erase hx]
      | inr hx =>
        -- Apply induction on `l` to obtain `s`.
        specialize ihl ?_
        . intro u hu
          have hux : u ≠ x := fun h => by rw [h] at hu; exact hx hu
          simpa [hux] using ht_mem u hu
        rcases ihl with ⟨rs, hrs_mem, hrs_perm⟩
        use rs
        exact And.intro (mem_multichoose_of_cons hrs_mem x) hrs_perm

/-- Any list containing `n` elements in a list `l` has its permutation contained in `multichoose`. -/
theorem exists_mem_multichoose_perm [DecidableEq α] {n : ℕ} {l : List α}
    {t : List α} (ht_len : t.length = n) (ht_mem : ∀ x ∈ t, x ∈ l) :
    ∃ s ∈ multichoose n l, s ~ t := by
  simpa using exists_mem_multichoose_eq_multiset (t := Multiset.ofList t) ht_len ht_mem


theorem exists_mem_multichoose_eq_multiset_iff [DecidableEq α] {n : ℕ} {l : List α} {t : Multiset α} :
    (∃ s ∈ multichoose n l, ↑s = t) ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ l := by
  refine Iff.intro ?_ ?_
  . intro h
    rcases h with ⟨s, hs, ht⟩
    simp [← ht]
    refine And.intro ?_ ?_
    . exact length_of_mem_multichoose hs
    . intro x hx
      exact mem_of_mem_multichoose hs x hx
  . simp
    intro h_card h_mem
    exact exists_mem_multichoose_eq_multiset h_card h_mem

theorem exists_mem_multichoose_perm_iff [DecidableEq α] {n : ℕ} {l t : List α} :
    (∃ s ∈ multichoose n l, s ~ t) ↔ t.length = n ∧ ∀ x ∈ t, x ∈ l := by
  refine Iff.intro ?_ ?_
  . intro h
    rcases h with ⟨s, hs, hst⟩
    refine And.intro ?_ ?_
    . rw [← List.Perm.length_eq hst]
      exact length_of_mem_multichoose hs
    . intro x hx
      refine mem_of_mem_multichoose hs x ?_
      simpa [List.Perm.mem_iff hst] using hx
  . simp
    intro h_len h_mem
    exact exists_mem_multichoose_perm h_len h_mem

theorem sublistsLen_map {f : α → β} {n : ℕ} (l : List α) :
    sublistsLen n (map f l) = map (map f) (sublistsLen n l) := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl => simp [ihl, ihn]; rfl

theorem Sublist.join_of_forall_sublist {s l : List (List α)} (h_len : s.length ≤ l.length)
    (h_sub : ∀ p ∈ List.zip s l, p.1 <+ p.2) : List.join s <+ List.join l := by
  induction s generalizing l with
  | nil => simp
  | cons x s ih =>
    cases l with
    | nil => contradiction
    | cons y l =>
      simp [Nat.succ_le_succ_iff] at h_sub h_len ⊢
      refine List.Sublist.append h_sub.1 ?_
      exact ih h_len (fun p => h_sub.2 p.1 p.2)

theorem Sublist.join_map_of_forall_sublist {β : Type*} {f g : β → List α} {l : List β}
    (h_sub : ∀ t, f t <+ g t) : List.join (l.map f) <+ List.join (l.map g) := by
  refine join_of_forall_sublist (by simp) ?_
  simp [zip_map']
  intro t _
  exact h_sub t

/-- The `multichoose` list is a sublist of `sublistsLen n` with all elements repeated `n` times. -/
theorem multichoose_sublist_sublistsLen_join_map_replicate {n : ℕ} {l : List α} :
    multichoose n l <+ sublistsLen n (l.map (replicate n)).join := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      simp [multichoose_succ_cons]
      refine Sublist.append ?_ ?_
      . refine Sublist.trans ihl ?_
        exact sublistsLen_sublist_of_sublist n.succ (by simp)
      . refine Sublist.map (cons x) ?_
        refine Sublist.trans ihn ?_
        refine sublistsLen_sublist_of_sublist n ?_
        simp
        exact Sublist.join_map_of_forall_sublist (by simp)

end List  -- namespace


namespace Multiset

variable {α : Type*} [DecidableEq α]

lemma cons_injective_right {α : Type*} {x : α} : Function.Injective (Multiset.cons x) := by simp [Function.Injective]

lemma cons_injective_left {α : Type*} {s : Multiset α} : Function.Injective s.cons := by simp [Function.Injective]

theorem count_toList {x : α} {t : Multiset α} : t.toList.count x = t.count x := by
  rw [← coe_count]
  refine Quotient.inductionOn t ?_
  simp


section Aux

/-- Helper for `multichoose` that maps a list to a list. -/
def multichooseAux (n : ℕ) (l : List α) : List (Multiset α) := (l.multichoose n).map (↑)

lemma multichooseAux_eq_map_coe {n : ℕ} {l : List α} :
    multichooseAux n l = (l.multichoose n).map (↑) := rfl

@[simp]
lemma multichooseAux_zero {l : List α} : multichooseAux 0 l = [{}] := by simp [multichooseAux]

@[simp]
lemma multichooseAux_succ_nil {n : ℕ} : multichooseAux n.succ ([] : List α) = [] := rfl

lemma multichooseAux_succ_cons {n : ℕ} {x : α} {xs : List α} :
    multichooseAux n.succ (x :: xs) = List.append
      (multichooseAux (n + 1) xs)
      (List.map (cons x) (multichooseAux n (x :: xs))) := by
  simp [multichooseAux, List.multichoose_succ_cons]
  rfl

theorem mem_multichooseAux_iff {n : ℕ} {l : List α} {t : Multiset α} :
    t ∈ multichooseAux n l ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ l := by
  simp [multichooseAux]
  simp [List.exists_mem_multichoose_eq_multiset_iff]

theorem nodup_multichooseAux {n : ℕ} {l : List α} (hl : List.Nodup l) :
    List.Nodup (multichooseAux n l) := by
  rw [multichooseAux]
  rw [List.nodup_map_iff_inj_on]
  . simp
    intro x hx y hy
    exact (List.perm_mem_multichoose hl hx hy).mp
  . exact List.nodup_multichoose hl

lemma count_cons_multichooseAux_of_not_mem {n : ℕ} {l : List α} {x : α} {t : List α} (hx : x ∉ l) :
    List.count ↑(x :: t) (multichooseAux (n + 1) l) = 0 := by
  induction l with
  | nil => simp
  | cons y l ihl =>
    simp [multichooseAux_succ_cons]
    refine And.intro ?_ ?_
    . exact ihl (List.not_mem_of_not_mem_cons hx)
    . simp [List.count_eq_zero]
      simp [mem_multichooseAux_iff]
      intro s _ hs_mem h
      rw [← cons_coe] at h
      rw [Multiset.cons_eq_cons] at h
      refine hx ?_
      simp
      cases h with
      | inl h => exact Or.inl h.1.symm
      | inr h =>
        refine hs_mem x ?_
        rcases h with ⟨_, ⟨r, hr⟩⟩
        simp [hr.1]

theorem count_multichooseAux_succ_cons {n : ℕ} {y : α} {l : List α} {t : Multiset α} :
    List.count ↑t (multichooseAux n.succ (y :: l)) =
    List.count ↑t (multichooseAux n.succ l) + (if y ∈ t then List.count (t.erase y) (multichooseAux n (y :: l)) else 0) := by
  simp [multichooseAux_succ_cons]
  by_cases h_mem : y ∈ t <;> simp [h_mem]
  . conv => lhs; rw [← Multiset.cons_erase h_mem]
    exact List.count_map_of_injective _ _ cons_injective_right _
  . simp [List.count_eq_zero]
    intro r _ ht
    simp [← ht] at h_mem  -- contradiction

theorem count_multichooseAux_of_card_eq {n : ℕ} {l : List α} {t : Multiset α} (htn : card t = n) :
    (multichooseAux n l).count t = ∏ x in toFinset t, Nat.multichoose (l.count x) (t.count x) := by
  induction n generalizing t l with
  | zero => simp at htn; simp [htn]
  | succ n ihn =>
    induction l with
    | nil =>
      simp
      symm
      rw [Finset.prod_eq_zero_iff]
      simp [Nat.multichoose_zero_eq_zero_iff]
      rw [← card_pos_iff_exists_mem]
      rw [htn]
      exact Nat.succ_pos n
    | cons y l ihl =>
      rw [count_multichooseAux_succ_cons]
      by_cases h_mem : y ∈ t <;> simp [h_mem]
      . -- Split the `y` term from the product.
        -- Use `Nat.multichoose_succ_succ` to split into two terms.
        rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
        rw [List.count_cons_self]
        conv => rhs; rhs; rw [← cons_erase h_mem, count_cons_self]
        rw [Nat.multichoose_succ_succ]
        rw [mul_add]
        refine congrArg₂ _ ?_ ?_
        . -- Apply induction over `l` for first term.
          rw [ihl]
          simp
          rw [Nat.sub_add_cancel (one_le_count_iff_mem.mpr h_mem)]
          rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
          refine congrArg₂ _ ?_ rfl
          refine Finset.prod_congr rfl ?_
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [List.count_cons_of_ne hx.1]
        . -- Apply induction over `n` for second term.
          rw [ihn (by simp [htn, h_mem])]
          by_cases h_mem' : y ∈ erase t y
          . -- `y ∉ erase t y`; the element for `y` persists in the product
            rw [← Finset.prod_erase_mul (a := y) _ _ (mem_toFinset.mpr h_mem')]
            rw [List.count_cons_self]
            refine congrArg₂ _ ?_ rfl
            refine Finset.prod_congr ?_ ?_
            . ext x
              simp
              intro hx
              exact mem_erase_of_ne hx
            . intro x hx
              refine congrArg₂ _ rfl ?_
              rw [Finset.mem_erase] at hx
              rw [count_erase_of_ne hx.1]
          . -- `y ∉ erase t y`; the element for `y` disappears from the product
            simp [h_mem']
            refine Finset.prod_congr ?_ ?_
            . ext x
              simp
              by_cases hx : x = y <;> simp [hx]
              . exact h_mem'
              . exact mem_erase_of_ne hx
            . intro x hx
              refine congrArg₂ _ rfl ?_
              rw [Finset.mem_erase] at hx
              rw [count_erase_of_ne hx.1]
      . -- `y ∉ t`; count within `y :: l` is same as count within `l`
        rw [ihl]
        refine Finset.prod_congr rfl ?_
        simp
        intro x hx
        rw [List.count_cons_of_ne]
        intro hxy
        rw [hxy] at hx
        exact h_mem hx

theorem count_multichooseAux {n : ℕ} {l : List α} {t : Multiset α} :
    (multichooseAux n l).count t = if card t = n then ∏ x in toFinset t, Nat.multichoose (l.count x) (t.count x) else 0 := by
  by_cases h : card t = n <;> simp [h]
  . exact count_multichooseAux_of_card_eq h
  . rw [List.count_eq_zero]
    intro ht
    rw [mem_multichooseAux_iff] at ht
    exact h ht.1  -- contradiction

-- For use with `Quot.liftOn` in `multichoose`.
theorem multichooseAux_perm {n : ℕ} {l₁ l₂ : List α} (hl : l₁ ~ l₂) : multichooseAux n l₁ ~ multichooseAux n l₂ := by
  rw [List.perm_iff_count]
  simp [count_multichooseAux, hl.count_eq]

theorem length_multichooseAux {n : ℕ} {l : List α} : (multichooseAux n l).length = Nat.multichoose (l.length) n := by
  rw [multichooseAux_eq_map_coe]
  rw [List.length_map]
  exact List.length_multichoose

end Aux


/-- The multisets obtained by choosing `n` elements from a multiset with replacement. -/
def multichoose (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => multichooseAux n l)
    (fun _ _ h => Quot.sound (multichooseAux_perm h))

theorem multichoose_coe' (n : ℕ) (l : List α) : multichoose n (↑l : Multiset α) = ↑(multichooseAux n l) := rfl

theorem multichoose_coe (n : ℕ) (l : List α) :
    multichoose n (↑l : Multiset α) = ↑(List.map (↑) (List.multichoose n l) : List (Multiset α)) := rfl

@[simp]
theorem multichoose_zero {s : Multiset α} : multichoose 0 s = {∅} :=
  Quotient.inductionOn s fun l => by simp [multichoose_coe']

@[simp]
theorem multichoose_succ_nil {n : ℕ} : multichoose n.succ (∅ : Multiset α) = ∅ := by
  generalize hs : (∅ : Multiset α) = s
  rw [eq_comm] at hs
  revert hs
  refine Quotient.inductionOn s ?_
  simp [multichoose_coe']

theorem multichoose_succ_cons {n : ℕ} {x : α} {s : Multiset α} :
    multichoose n.succ (x ::ₘ s) = multichoose n.succ s + (multichoose n (x ::ₘ s)).map (cons x) := by
  refine Quotient.inductionOn s ?_
  intro l
  simp [multichoose_coe']
  simp [multichooseAux_succ_cons]

theorem mem_multichoose_iff {n : ℕ} {s : Multiset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ s :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact mem_multichooseAux_iff

theorem count_multichoose {n : ℕ} {s : Multiset α} {t : Multiset α} :
    (multichoose n s).count t = if card t = n then ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) else 0 :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact count_multichooseAux

theorem count_multichoose_of_card_eq {n : ℕ} {s : Multiset α} {t : Multiset α} (ht : card t = n) :
    (multichoose n s).count t = ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) := by
  simp [count_multichoose, ht]

theorem count_multichoose_of_card_ne {n : ℕ} {s : Multiset α} {t : Multiset α} (ht : card t ≠ n) :
    (multichoose n s).count t = 0 := by
  simp [count_multichoose, ht]

theorem nodup_multichoose {n : ℕ} {s : Multiset α} : Nodup s → Nodup (multichoose n s) :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact nodup_multichooseAux

theorem card_multichoose {n : ℕ} {s : Multiset α} :
    card (multichoose n s) = Nat.multichoose (card s) n :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact length_multichooseAux

-- def consEmbedding (x : α) : Multiset α ↪ Multiset α := ⟨cons x, cons_injective_right⟩

end Multiset  -- namespace


namespace Finset

variable {α : Type*} [DecidableEq α]

-- -- TODO: Is there a way to make this computable?
-- -- `compiler IR check failed at 'Finset.multichoose._rarg', error: unknown declaration 'Finset.toList'`
-- -- Could require that `α` has an order and use `Finset.sort` instead of `Finset.list`?
-- /--
-- Finds all multisets of cardinality `n` formed using the elements of `s`.
-- Like `Multiset.powersetCard` but without duplicates.
-- -/
-- noncomputable def multichoose (n : ℕ) (s : Finset α) : Finset (Multiset α) where
--   val := ↑(List.map Multiset.ofList (List.multichoose n s.toList))
--   nodup := by
--     rw [Multiset.coe_nodup]
--     rw [List.nodup_map_iff_inj_on]
--     . simp
--       intro x hx y hy
--       exact (List.perm_mem_multichoose s.nodup_toList hx hy).mp
--     . exact List.nodup_multichoose s.nodup_toList

/-- Finds all unique multisets of cardinality `n` formed using the elements of `s`. -/
def multichoose (n : ℕ) (s : Finset α) : Finset (Multiset α) :=
  ⟨Multiset.multichoose n s.1, Multiset.nodup_multichoose s.nodup⟩

lemma multichoose_val {n : ℕ} {s : Finset α} : (multichoose n s).val = Multiset.multichoose n s.val := rfl

@[simp]
lemma multichoose_zero {s : Finset α} : multichoose 0 s = {∅} := by
  simp [multichoose]
  rfl

@[simp]
lemma multichoose_succ_nil {n : ℕ} : multichoose n.succ (∅ : Finset α) = ∅ := by
  simp [multichoose]
  rfl

-- lemma multichoose_succ_insert {n : ℕ} {x : α} {s : Finset α} (hx : x ∉ s) :
--     multichoose n.succ (insert x s) = multichoose n.succ s ∪ Finset.map (Multiset.consEmbedding x) (multichoose n (insert x s)) := by
--   simp [multichoose, Multiset.multichoose_succ_cons, hx]
--   congr
--   sorry

theorem card_multichoose (n : ℕ) (s : Finset α) :
    (multichoose n s).card = Nat.multichoose (s.card) n := by
  simp [multichoose]
  rw [Multiset.card_multichoose]
  simp

/-- Necessary and sufficient condition for a `Multiset` to be a member of `multichoose`. -/
theorem mem_multichoose_iff {n : ℕ} {s : Finset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ s := by
  simp [multichoose]
  rw [Multiset.mem_multichoose_iff]
  simp

end Finset  -- namespace
