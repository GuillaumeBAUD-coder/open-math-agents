import OMAStatements.S_mo_247107
import Mathlib.Data.Finset.Union

namespace OMA.Count247107

open Finset OMA.S_mo_247107

variable {n : ℕ}

def prepend (i : Fin n) : List (Fin n) ↪ List (Fin n) :=
  ⟨List.cons i, fun _ _ h => (List.cons.inj h).2⟩

def words : ℕ → Inventory n → (Fin n → Bool) → Bool → Finset (List (Fin n))
  | 0, r, _, _ => if ∀ j, r j = 0 then {[]} else ∅
  | k + 1, r, allowed, up =>
      (heads r allowed).biUnion fun i =>
        (words k (consume r i) (compareNext up i) (!up)).map (prepend i)

theorem count_cons_iff (r : Inventory n) (i : Fin n) (w : List (Fin n)) :
    (∀ j, (i :: w).count j = r j) ↔ 0 < r i ∧ (∀ j, w.count j = consume r i j) := by
  constructor
  · intro h
    have hi := h i
    rw [List.count_cons_self] at hi
    refine ⟨by omega, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp [consume]
      omega
    · have hij : i ≠ j := fun hij => hji hij.symm
      simpa [consume, hji, List.count_cons_of_ne hij] using h j
  · rintro ⟨hi, h⟩ j
    by_cases hji : j = i
    · subst j
      have hc := h i
      simp [consume] at hc
      rw [List.count_cons_self]
      omega
    · have hij : i ≠ j := fun hij => hji hij.symm
      simpa [consume, hji, List.count_cons_of_ne hij] using h j

theorem mem_words (k : ℕ) (r : Inventory n) (allowed : Fin n → Bool)
    (up : Bool) (w : List (Fin n)) :
    w ∈ words k r allowed up ↔
      w.length = k ∧ (∀ i, w.count i = r i) ∧ alternating allowed up w = true := by
  induction k generalizing r allowed up w with
  | zero =>
    cases w with
    | nil =>
      by_cases h : ∀ j, r j = 0
      · simp [words, h, alternating]
      · simp [words, h, alternating, eq_comm (a := 0)]
    | cons i w =>
      by_cases h : ∀ j, r j = 0 <;> simp [words, h]
  | succ k ih =>
    cases w with
    | nil => simp [words, mem_biUnion, mem_map, prepend]
    | cons i w =>
      simp only [words, mem_biUnion, mem_map, List.length_cons, Nat.succ.injEq,
        count_cons_iff, alternating, Bool.and_eq_true]
      constructor
      · rintro ⟨j, hj, v, hv, hcons⟩
        change j :: v = i :: w at hcons
        rcases List.cons.inj hcons with ⟨rfl, rfl⟩
        rcases (mem_filter.mp hj).2 with ⟨hpos, hall⟩
        rcases (ih _ _ _ _).mp hv with ⟨hlen, hcount, halt⟩
        exact ⟨hlen, ⟨hpos, hcount⟩, hall, halt⟩
      · rintro ⟨hlen, ⟨hpos, hcount⟩, hall, halt⟩
        have hi : i ∈ heads r allowed := mem_filter.mpr ⟨mem_univ _, hpos, hall⟩
        exact ⟨i, hi, w, (ih _ _ _ _).mpr ⟨hlen, hcount, halt⟩, rfl⟩

theorem card_words (k : ℕ) (r : Inventory n) (allowed : Fin n → Bool) (up : Bool) :
    (words k r allowed up).card = count k r allowed up := by
  induction k generalizing r allowed up with
  | zero =>
    simp only [words, count]
    split <;> simp
  | succ k ih =>
    rw [words, count]
    have disjoint_tails : (↑(heads r allowed) : Set (Fin n)).PairwiseDisjoint
        (fun i => (words k (consume r i) (compareNext up i) (!up)).map (prepend i)) := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro w hwi hwj
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hwi
      obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hwj
      exact hij ((List.cons.inj hv).1.symm)
    rw [Finset.card_biUnion disjoint_tails]
    exact sum_congr rfl (fun i _ => (Finset.card_map (prepend i)).trans (ih _ _ _))

end OMA.Count247107

open OMA.Count247107

theorem OMA.solution : type_of% @OMA.S_mo_247107.main := by
  intro n
  refine ⟨words (2 * n) (fun _ => 2) (fun _ => true) true, ?_, ?_⟩
  · intro w
    exact mem_words _ _ _ _ w
  · exact card_words _ _ _ _
