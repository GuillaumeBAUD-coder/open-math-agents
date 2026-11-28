import OMAStatements.S_oeis_a285076
import Mathlib

-- Problem: A285076: 1-limiting word of the morphism 0->10, 1-> 010.
-- Upstream: formal-conjectures statements/oeis-a285076.lean:0 (declaration OMA.S_oeis_a285076.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a285076

def OMA.vv : ℕ → List ℕ
  | 0 => []
  | k + 1 => [0, 1, 0] ++ (OMA.vv k).flatMap morph

theorem OMA.iter_eq (k : ℕ) :
    iter (k + 1) = (if k % 2 = 0 then [1, 0] else [0, 1]) ++ OMA.vv k := by
  induction k with
  | zero => simp [iter, morph, OMA.vv]
  | succ k ih =>
    show (iter (k + 1)).flatMap morph = _
    rw [ih, List.flatMap_append]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      simp [h, h', OMA.vv, morph]
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h', OMA.vv, morph]

theorem OMA.vv_prefix (k : ℕ) : ∃ t, OMA.vv (k + 1) = OMA.vv k ++ t := by
  induction k with
  | zero => exact ⟨_, (List.nil_append _).symm⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap morph, ?_⟩
    show [0, 1, 0] ++ (OMA.vv (k + 1)).flatMap morph
      = ([0, 1, 0] ++ (OMA.vv k).flatMap morph) ++ t.flatMap morph
    rw [ht, List.flatMap_append, List.append_assoc]

theorem OMA.len_flat (l : List ℕ) : l.length ≤ (l.flatMap morph).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : 1 ≤ (morph x).length := by cases x <;> simp [morph]
    omega

theorem OMA.vv_len (k : ℕ) : k ≤ (OMA.vv k).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    show k + 1 ≤ ([0, 1, 0] ++ (OMA.vv k).flatMap morph).length
    rw [List.length_append]
    have h1 := OMA.len_flat (OMA.vv k)
    have h2 : ([0, 1, 0] : List ℕ).length = 3 := rfl
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a285076.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  unfold a A285073
  have e1 : 2 * (m + 3) + 1 = (2 * m + 6) + 1 := by ring
  have e2 : 2 * (m + 3) = (2 * m + 5) + 1 := by ring
  rw [e1, e2, OMA.iter_eq, OMA.iter_eq]
  obtain ⟨t, ht⟩ := OMA.vv_prefix (2 * m + 5)
  have hlen := OMA.vv_len (2 * m + 5)
  have i1 : (2 * m + 6) % 2 = 0 := by omega
  have i2 : ¬ (2 * m + 5) % 2 = 0 := by omega
  rw [if_pos i1, if_neg i2]
  have idx : m + 3 - 1 = m + 2 := by omega
  rw [idx, ht]
  simp only [List.getD_eq_getElem?_getD]
  have g1 : ([1, 0] ++ (OMA.vv (2 * m + 5) ++ t))[m + 2]? = (OMA.vv (2 * m + 5))[m]? := by
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel]
    rw [List.getElem?_append_left (by omega)]
  have g2 : ([0, 1] ++ OMA.vv (2 * m + 5))[m + 2]? = (OMA.vv (2 * m + 5))[m]? := by
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel]
  rw [g1, g2]
