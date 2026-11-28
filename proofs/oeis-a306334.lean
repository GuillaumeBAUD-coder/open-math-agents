import OMAStatements.S_oeis_a306334
import Mathlib

/-!
Proof of Kotesovec's conjectures for A306334. Valid bond lists are enumerated by explicit
finsets W (all lists, by first element) and Q (palindromes, peeled from both ends); their
cardinalities f and q satisfy the transfer-matrix recursions, and the number of classes under
reversal is (f + q) / 2.
-/

namespace A306334
open OMA.S_oeis_a306334

/-- The allowed bonds next to a bond of order c. -/
def allowed (c : ℕ) : Finset ℕ := (Finset.range 4).filter (fun x => 1 ≤ x ∧ c + x ≤ 4)

theorem mem_allowed (c x : ℕ) : x ∈ allowed c ↔ (x = 1 ∨ x = 2 ∨ x = 3) ∧ c + x ≤ 4 := by
  simp only [allowed, Finset.mem_filter, Finset.mem_range]
  omega

theorem allowed1 : allowed 1 = {1, 2, 3} := by decide
theorem allowed2 : allowed 2 = {1, 2} := by decide
theorem allowed3 : allowed 3 = {1} := by decide

def Ent (l : List ℕ) : Prop := ∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3

/-- Lists of length m with allowed entries such that c :: l is a chain. -/
def W : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | m + 1, c => (allowed c).biUnion (fun x => (W m x).image (List.cons x))

theorem mem_W (m : ℕ) : ∀ (c : ℕ) (l : List ℕ),
    l ∈ W m c ↔ l.length = m ∧ Ent l ∧ (c :: l).IsChain (fun x y => x + y ≤ 4) := by
  induction m with
  | zero =>
    intro c l
    simp only [W, Finset.mem_singleton]
    constructor
    · rintro rfl
      simp [Ent]
    · rintro ⟨h, -⟩
      exact List.length_eq_zero_iff.mp h
  | succ m ih =>
    intro c l
    simp only [W, Finset.mem_biUnion, Finset.mem_image, ih, mem_allowed]
    constructor
    · rintro ⟨x, hx, l', ⟨hl, he, hc⟩, rfl⟩
      refine ⟨by simp [hl], ?_, List.isChain_cons_cons.2 ⟨hx.2, hc⟩⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx.1
      · exact he y hy
    · rintro ⟨hl, he, hc⟩
      cases l with
      | nil => simp at hl
      | cons x l' =>
        rw [List.isChain_cons_cons] at hc
        exact ⟨x, ⟨he x List.mem_cons_self, hc.1⟩, l', ⟨by simpa using hl,
          fun y hy => he y (List.mem_cons_of_mem _ hy), hc.2⟩, rfl⟩

def f : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, c => ∑ x ∈ allowed c, f m x

theorem card_W (m : ℕ) : ∀ c : ℕ, (W m c).card = f m c := by
  induction m with
  | zero => intro c; simp [W, f]
  | succ m ih =>
    intro c
    rw [W, f, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_image_of_injective _ (List.cons_injective), ih]
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro l h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨l1, -, rfl⟩ := h1
      obtain ⟨l2, -, h⟩ := h2
      exact hxy (List.cons.inj h).1.symm

/-- Palindromic lists l of length m with allowed entries such that c :: l ++ [c] is a chain. -/
def Q : ℕ → ℕ → Finset (List ℕ)
  | 0, c => if c + c ≤ 4 then {[]} else ∅
  | 1, c => (allowed c).image (fun x => [x])
  | m + 2, c => (allowed c).biUnion (fun x => (Q m x).image (fun l => x :: (l ++ [x])))

theorem mem_Q (m : ℕ) : ∀ (c : ℕ) (l : List ℕ),
    l ∈ Q m c ↔ l.length = m ∧ Ent l ∧ l.reverse = l ∧
      (c :: (l ++ [c])).IsChain (fun x y => x + y ≤ 4) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    intro c l
    constructor
    · intro h
      by_cases hc : c + c ≤ 4
      · simp only [Q, hc, if_true, Finset.mem_singleton] at h
        subst h
        simp [Ent, hc]
      · simp [Q, hc] at h
    · rintro ⟨hl, -, -, hc⟩
      obtain rfl := List.length_eq_zero_iff.1 hl
      have hc' : c + c ≤ 4 := by simpa using hc
      simp [Q, hc']
  | one =>
    intro c l
    simp only [Q, Finset.mem_image, mem_allowed]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨rfl, ?_, rfl, ?_⟩
      · intro y hy
        obtain rfl := List.mem_singleton.1 hy
        exact hx.1
      · simp only [List.singleton_append, List.isChain_cons_cons, List.isChain_singleton,
          and_true]
        omega
    · rintro ⟨hl, he, -, hc⟩
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hl
      simp only [List.singleton_append, List.isChain_cons_cons] at hc
      exact ⟨x, ⟨he x List.mem_cons_self, hc.1⟩, rfl⟩
  | more m ih _ =>
    intro c l
    simp only [Q, Finset.mem_biUnion, Finset.mem_image, ih, mem_allowed]
    constructor
    · rintro ⟨x, hx, l', ⟨hl, he, hr, hc⟩, rfl⟩
      refine ⟨by simp [hl], ?_, by simp [hr], ?_⟩
      · intro y hy
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | hy | rfl
        · exact hx.1
        · exact he y hy
        · exact hx.1
      · have : c :: (x :: (l' ++ [x]) ++ [c]) = c :: x :: (l' ++ x :: [c]) := by simp
        rw [this, List.isChain_cons_cons, List.isChain_cons_split]
        refine ⟨hx.2, hc, ?_⟩
        simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        omega
    · rintro ⟨hl, he, hr, hc⟩
      cases l with
      | nil => simp at hl
      | cons x t =>
        rcases List.eq_nil_or_concat t with rfl | ⟨l', y, rfl⟩
        · simp at hl
        · rw [List.concat_eq_append] at hl he hr hc
          have hr' : y :: (l'.reverse ++ [x]) = x :: (l' ++ [y]) := by simpa using hr
          obtain ⟨rfl, hr''⟩ := List.cons.inj hr'
          have hrev : l'.reverse = l' := List.append_cancel_right hr''
          have : c :: (y :: (l' ++ [y]) ++ [c]) = c :: y :: (l' ++ y :: [c]) := by simp
          rw [this, List.isChain_cons_cons, List.isChain_cons_split] at hc
          refine ⟨y, ⟨he y List.mem_cons_self, hc.1⟩, l', ⟨by simpa using hl, ?_, hrev, hc.2.1⟩, by simp⟩
          intro z hz
          exact he z (by simp [hz])

def q : ℕ → ℕ → ℕ
  | 0, c => if c + c ≤ 4 then 1 else 0
  | 1, c => (allowed c).card
  | m + 2, c => ∑ x ∈ allowed c, q m x

theorem card_Q (m : ℕ) : ∀ c : ℕ, (Q m c).card = q m c := by
  induction m using Nat.twoStepInduction with
  | zero =>
    intro c
    by_cases hc : c + c ≤ 4 <;> simp [Q, q, hc]
  | one =>
    intro c
    rw [Q, q, Finset.card_image_of_injective]
    intro x y h
    simpa using h
  | more m ih _ =>
    intro c
    rw [Q, q, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_image_of_injective, ih]
      intro l1 l2 h
      simpa using h
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro l h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨l1, -, rfl⟩ := h1
      obtain ⟨l2, -, h⟩ := h2
      exact hxy (List.cons.inj h).1.symm

theorem chain_one (l : List ℕ) (he : Ent l) :
    (1 :: l).IsChain (fun x y => x + y ≤ 4) ↔ l.IsChain (fun x y => x + y ≤ 4) := by
  rw [List.isChain_cons]
  refine ⟨fun h => h.2, fun h => ⟨fun y hy => ?_, h⟩⟩
  have := he y (List.mem_of_mem_head? hy)
  omega

theorem chain_one' (l : List ℕ) (he : Ent l) :
    (1 :: (l ++ [1])).IsChain (fun x y => x + y ≤ 4) ↔ l.IsChain (fun x y => x + y ≤ 4) := by
  rw [List.isChain_cons, List.isChain_append]
  constructor
  · intro h
    exact h.2.1
  · intro h
    refine ⟨fun y hy => ?_, h, List.isChain_singleton _, fun x hx y hy => ?_⟩
    · have hy' := List.mem_of_mem_head? hy
      rcases List.mem_append.1 hy' with hy' | hy'
      · have := he y hy'
        omega
      · have := List.mem_singleton.1 hy'
        omega
    · have := he x (List.mem_of_mem_getLast? hx)
      have hy' : y = 1 := by simpa using hy.symm
      omega

theorem mem_V (m : ℕ) (l : List ℕ) : l ∈ W m 1 ↔ l.length = m ∧ Valid l := by
  rw [mem_W, Valid]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (chain_one l h2).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (chain_one l h2).2 h3⟩

theorem mem_P (m : ℕ) (l : List ℕ) : l ∈ Q m 1 ↔ l ∈ W m 1 ∧ l.reverse = l := by
  rw [mem_Q, mem_W]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, (chain_one l h2).2 ((chain_one' l h2).1 h4)⟩, h3⟩
  · rintro ⟨⟨h1, h2, h4⟩, h3⟩
    exact ⟨h1, h2, h3, (chain_one' l h2).2 ((chain_one l h2).1 h4)⟩

theorem valid_reverse (l : List ℕ) (h : Valid l) : Valid l.reverse := by
  refine ⟨fun x hx => h.1 x (List.mem_reverse.1 hx), ?_⟩
  rw [List.isChain_reverse]
  exact h.2.imp (fun a b hab => by omega)

theorem mem_V_reverse (m : ℕ) (l : List ℕ) (h : l ∈ W m 1) : l.reverse ∈ W m 1 := by
  rw [mem_V] at h ⊢
  exact ⟨by simp [h.1], valid_reverse l h.2⟩

theorem same_equiv (n : ℕ) : Equivalence (Same n) := by
  refine ⟨fun l => Or.inl rfl, ?_, ?_⟩
  · rintro l l' (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, List.reverse_reverse])
  · rintro x y z (h1 | h1) (h2 | h2)
    · exact Or.inl (h2.trans h1)
    · exact Or.inr (by rw [h2, h1])
    · exact Or.inr (by rw [h2, h1])
    · exact Or.inl (by rw [h2, h1, List.reverse_reverse])

theorem card_quot (n : ℕ) :
    a n = ((W (n - 1) 1).filter (fun l => l ≤ l.reverse)).card := by
  classical
  set L := (W (n - 1) 1).filter (fun l => l ≤ l.reverse) with hL
  have hmem : ∀ l : L, l.1.length = n - 1 ∧ Valid l.1 := fun l =>
    (mem_V _ _).1 (Finset.mem_filter.1 l.2).1
  let g : L → Quot (Same n) := fun l => Quot.mk _ ⟨l.1, hmem l⟩
  have hg : Function.Bijective g := by
    constructor
    · intro l l' h
      have h' : Same n ⟨l.1, hmem l⟩ ⟨l'.1, hmem l'⟩ :=
        (same_equiv n).eqvGen_iff.1 (Quot.eqvGen_exact h)
      apply Subtype.ext
      rcases h' with h' | h'
      · exact h'.symm
      · have h1 := (Finset.mem_filter.1 l.2).2
        have h2 := (Finset.mem_filter.1 l'.2).2
        have h3 : l'.1 = l.1.reverse := h'
        rw [h3, List.reverse_reverse] at h2
        rw [h3]
        exact le_antisymm h1 h2
    · intro x
      induction x using Quot.ind with
      | mk l =>
        obtain ⟨l, hl⟩ := l
        have hV : l ∈ W (n - 1) 1 := (mem_V _ _).2 hl
        rcases le_total l l.reverse with h | h
        · exact ⟨⟨l, Finset.mem_filter.2 ⟨hV, h⟩⟩, rfl⟩
        · refine ⟨⟨l.reverse, Finset.mem_filter.2 ⟨mem_V_reverse _ _ hV, ?_⟩⟩, ?_⟩
          · rw [List.reverse_reverse]; exact h
          · exact Quot.sound (Or.inr (by simp))
  rw [a, ← Nat.card_eq_finsetCard L]
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem two_mul_card (m : ℕ) :
    2 * ((W m 1).filter (fun l => l ≤ l.reverse)).card = (W m 1).card + (Q m 1).card := by
  classical
  set L := (W m 1).filter (fun l => l ≤ l.reverse) with hL
  set L' := (W m 1).filter (fun l => l.reverse ≤ l) with hL'
  have h1 : L.card = L'.card := by
    refine Finset.card_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_
    · intro l hl
      rw [Finset.mem_coe, hL, Finset.mem_filter] at hl
      rw [Finset.mem_coe, hL', Finset.mem_filter, List.reverse_reverse]
      exact ⟨mem_V_reverse _ _ hl.1, hl.2⟩
    · intro l hl
      rw [Finset.mem_coe, hL', Finset.mem_filter] at hl
      rw [Finset.mem_coe, hL, Finset.mem_filter, List.reverse_reverse]
      exact ⟨mem_V_reverse _ _ hl.1, hl.2⟩
    · intro l _; exact List.reverse_reverse l
    · intro l _; exact List.reverse_reverse l
  have h2 : L ∪ L' = W m 1 := by
    ext l
    simp only [hL, hL', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total l l.reverse with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have h3 : L ∩ L' = Q m 1 := by
    ext l
    simp only [hL, hL', Finset.mem_inter, Finset.mem_filter, mem_P]
    constructor
    · rintro ⟨⟨h, h'⟩, -, h''⟩
      exact ⟨h, le_antisymm h'' h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, h'.symm.le⟩, h, h'.le⟩
  have h4 := Finset.card_union_add_card_inter L L'
  rw [h2, h3] at h4
  omega

theorem two_a (k : ℕ) : 2 * a (k + 1) = f k 1 + q k 1 := by
  rw [card_quot, Nat.add_sub_cancel, two_mul_card, card_W, card_Q]

theorem f1 (m : ℕ) : f (m + 1) 1 = f m 1 + f m 2 + f m 3 := by
  rw [f, allowed1]; simp [Finset.sum_insert]; ring
theorem f2 (m : ℕ) : f (m + 1) 2 = f m 1 + f m 2 := by
  rw [f, allowed2]; simp [Finset.sum_insert]
theorem f3 (m : ℕ) : f (m + 1) 3 = f m 1 := by
  rw [f, allowed3]; simp
theorem q1 (m : ℕ) : q (m + 2) 1 = q m 1 + q m 2 + q m 3 := by
  rw [q, allowed1]; simp [Finset.sum_insert]; ring
theorem q2 (m : ℕ) : q (m + 2) 2 = q m 1 + q m 2 := by
  rw [q, allowed2]; simp [Finset.sum_insert]
theorem q3 (m : ℕ) : q (m + 2) 3 = q m 1 := by
  rw [q, allowed3]; simp

theorem ft (m : ℕ) : f (m + 3) 1 + f m 1 = 2 * f (m + 2) 1 + f (m + 1) 1 := by
  have e1 : f (m + 3) 1 = f (m + 2) 1 + f (m + 2) 2 + f (m + 2) 3 := f1 (m + 2)
  have e2 : f (m + 2) 2 = f (m + 1) 1 + f (m + 1) 2 := f2 (m + 1)
  have e3 : f (m + 2) 3 = f (m + 1) 1 := f3 (m + 1)
  have e4 : f (m + 2) 1 = f (m + 1) 1 + f (m + 1) 2 + f (m + 1) 3 := f1 (m + 1)
  have e5 := f1 m
  have e6 := f2 m
  have e7 := f3 m
  omega

theorem qt (m : ℕ) : q (m + 6) 1 + q m 1 = 2 * q (m + 4) 1 + q (m + 2) 1 := by
  have e1 : q (m + 6) 1 = q (m + 4) 1 + q (m + 4) 2 + q (m + 4) 3 := q1 (m + 4)
  have e2 : q (m + 4) 2 = q (m + 2) 1 + q (m + 2) 2 := q2 (m + 2)
  have e3 : q (m + 4) 3 = q (m + 2) 1 := q3 (m + 2)
  have e4 : q (m + 4) 1 = q (m + 2) 1 + q (m + 2) 2 + q (m + 2) 3 := q1 (m + 2)
  have e5 := q1 m
  have e6 := q2 m
  have e7 := q3 m
  omega

theorem rec (k : ℕ) : a (k + 10) + 5 * a (k + 7) + a (k + 6) + 2 * a (k + 4) + a (k + 1) =
    2 * a (k + 9) + 3 * a (k + 8) + 3 * a (k + 3) + a (k + 2) := by
  have a1 : 2 * a (k + 1) = f k 1 + q k 1 := two_a k
  have a2 : 2 * a (k + 2) = f (k + 1) 1 + q (k + 1) 1 := two_a (k + 1)
  have a3 : 2 * a (k + 3) = f (k + 2) 1 + q (k + 2) 1 := two_a (k + 2)
  have a4 : 2 * a (k + 4) = f (k + 3) 1 + q (k + 3) 1 := two_a (k + 3)
  have a6 : 2 * a (k + 6) = f (k + 5) 1 + q (k + 5) 1 := two_a (k + 5)
  have a7 : 2 * a (k + 7) = f (k + 6) 1 + q (k + 6) 1 := two_a (k + 6)
  have a8 : 2 * a (k + 8) = f (k + 7) 1 + q (k + 7) 1 := two_a (k + 7)
  have a9 : 2 * a (k + 9) = f (k + 8) 1 + q (k + 8) 1 := two_a (k + 8)
  have a10 : 2 * a (k + 10) = f (k + 9) 1 + q (k + 9) 1 := two_a (k + 9)
  have t0 : f (k + 3) 1 + f k 1 = 2 * f (k + 2) 1 + f (k + 1) 1 := ft k
  have t2 : f (k + 5) 1 + f (k + 2) 1 = 2 * f (k + 4) 1 + f (k + 3) 1 := ft (k + 2)
  have t4 : f (k + 7) 1 + f (k + 4) 1 = 2 * f (k + 6) 1 + f (k + 5) 1 := ft (k + 4)
  have t6 : f (k + 9) 1 + f (k + 6) 1 = 2 * f (k + 8) 1 + f (k + 7) 1 := ft (k + 6)
  have p0 : q (k + 6) 1 + q k 1 = 2 * q (k + 4) 1 + q (k + 2) 1 := qt k
  have p1 : q (k + 7) 1 + q (k + 1) 1 = 2 * q (k + 5) 1 + q (k + 3) 1 := qt (k + 1)
  have p2 : q (k + 8) 1 + q (k + 2) 1 = 2 * q (k + 6) 1 + q (k + 4) 1 := qt (k + 2)
  have p3 : q (k + 9) 1 + q (k + 3) 1 = 2 * q (k + 7) 1 + q (k + 5) 1 := qt (k + 3)
  omega

theorem vals : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 4 ∧ a 4 = 10 ∧ a 5 = 18 ∧ a 6 = 42 ∧ a 7 = 84 ∧
    a 8 = 192 ∧ a 9 = 409 := by
  have h0 : f 0 1 + q 0 1 = 2 * 1 := by decide
  have h1 : f 1 1 + q 1 1 = 2 * 3 := by decide
  have h2 : f 2 1 + q 2 1 = 2 * 4 := by decide
  have h3 : f 3 1 + q 3 1 = 2 * 10 := by decide
  have h4 : f 4 1 + q 4 1 = 2 * 18 := by decide
  have h5 : f 5 1 + q 5 1 = 2 * 42 := by decide
  have h6 : f 6 1 + q 6 1 = 2 * 84 := by decide
  have h7 : f 7 1 + q 7 1 = 2 * 192 := by decide
  have h8 : f 8 1 + q 8 1 = 2 * 409 := by decide
  have g0 : 2 * a 1 = f 0 1 + q 0 1 := two_a 0
  have g1 : 2 * a 2 = f 1 1 + q 1 1 := two_a 1
  have g2 : 2 * a 3 = f 2 1 + q 2 1 := two_a 2
  have g3 : 2 * a 4 = f 3 1 + q 3 1 := two_a 3
  have g4 : 2 * a 5 = f 4 1 + q 4 1 := two_a 4
  have g5 : 2 * a 6 = f 5 1 + q 5 1 := two_a 5
  have g6 : 2 * a 7 = f 6 1 + q 6 1 := two_a 6
  have g7 : 2 * a 8 = f 7 1 + q 7 1 := two_a 7
  have g8 : 2 * a 9 = f 8 1 + q 8 1 := two_a 8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end A306334

open OMA.S_oeis_a306334 in
theorem OMA.solution : type_of% @OMA.S_oeis_a306334.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := A306334.rec k
    simp only [show k + 10 - 1 = k + 9 from rfl, show k + 10 - 2 = k + 8 from rfl,
      show k + 10 - 3 = k + 7 from rfl, show k + 10 - 4 = k + 6 from rfl,
      show k + 10 - 6 = k + 4 from rfl, show k + 10 - 7 = k + 3 from rfl,
      show k + 10 - 8 = k + 2 from rfl, show k + 10 - 9 = k + 1 from rfl]
    omega
  · obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := A306334.vals
    have hA : (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) + 1) =
        PowerSeries.mk (fun n => if n = 0 then (1 : ℚ) else (a n : ℚ)) := by
      ext n
      rcases n with _ | n <;> simp
    rw [hA]
    set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (1 : ℚ) else (a n : ℚ)) with hAdef
    have c2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat PowerSeries.C 2
    have c3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat PowerSeries.C 3
    have c5 : (PowerSeries.C (5 : ℚ) : PowerSeries ℚ) = 5 := map_ofNat PowerSeries.C 5
    have hD : A * ((1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
          (1 - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4 + PowerSeries.X ^ 6)) =
        A - PowerSeries.C (2 : ℚ) * (A * PowerSeries.X ^ 1)
          - PowerSeries.C (3 : ℚ) * (A * PowerSeries.X ^ 2)
          + PowerSeries.C (5 : ℚ) * (A * PowerSeries.X ^ 3) + A * PowerSeries.X ^ 4
          + PowerSeries.C (2 : ℚ) * (A * PowerSeries.X ^ 6)
          - PowerSeries.C (3 : ℚ) * (A * PowerSeries.X ^ 7) - A * PowerSeries.X ^ 8
          + A * PowerSeries.X ^ 9 := by
      rw [c2, c3, c5]; ring
    have hN : (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4
          + 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 - PowerSeries.X ^ 7 : PowerSeries ℚ) =
        PowerSeries.X ^ 0 - PowerSeries.X ^ 1 - (PowerSeries.X ^ 2 + PowerSeries.X ^ 2)
          - PowerSeries.X ^ 4 + (PowerSeries.X ^ 5 + PowerSeries.X ^ 5) + PowerSeries.X ^ 6
          - PowerSeries.X ^ 7 := by
      ring
    rw [hD, hN]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow, hAdef, PowerSeries.coeff_mk]
    rcases lt_or_ge n 10 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have h := A306334.rec k
      have h' : ((a (k + 10) : ℚ) + 5 * a (k + 7) + a (k + 6) + 2 * a (k + 4) + a (k + 1) =
          2 * a (k + 9) + 3 * a (k + 8) + 3 * a (k + 3) + a (k + 2)) := by exact_mod_cast h
      simp only [show k + 10 - 1 = k + 9 from rfl, show k + 10 - 2 = k + 8 from rfl,
        show k + 10 - 3 = k + 7 from rfl, show k + 10 - 4 = k + 6 from rfl,
        show k + 10 - 6 = k + 4 from rfl, show k + 10 - 7 = k + 3 from rfl,
        show k + 10 - 8 = k + 2 from rfl, show k + 10 - 9 = k + 1 from rfl,
        show ¬ (k + 10 = 0) by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega,
        show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 4 = 0) by omega,
        show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega,
        show ¬ (k + 10 = 1) by omega, show ¬ (k + 10 = 2) by omega, show ¬ (k + 10 = 4) by omega,
        show ¬ (k + 10 = 5) by omega, show ¬ (k + 10 = 6) by omega, show ¬ (k + 10 = 7) by omega,
        show (1 ≤ k + 10) by omega, show (2 ≤ k + 10) by omega, show (3 ≤ k + 10) by omega,
        show (4 ≤ k + 10) by omega, show (6 ≤ k + 10) by omega, show (7 ≤ k + 10) by omega,
        show (8 ≤ k + 10) by omega, show (9 ≤ k + 10) by omega, if_true, if_false]
      linarith
