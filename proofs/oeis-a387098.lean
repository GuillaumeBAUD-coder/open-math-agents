import OMAStatements.S_oeis_a387098
import Mathlib

/-!
For `n ≥ 2` and `k ≥ 1`, column `1` holds a king `p0` in some row `r`; pick an adjacent row `r'`.
The `2k` kings of rows `r, r'` never sit in column `0` (they would attack `p0`), and
`q ↦ (q.2 - 1) / 2` is injective on them (equal values force adjacent squares), landing in
`range (n / 2)`. Hence `2k ≤ n / 2`, i.e. `4k ≤ n`. For `n = 1` a row holds at most one king.
-/

namespace R387098
open OMA.S_oeis_a387098

theorem attack {n : ℕ} (p q : Fin n × Fin n)
    (h : 1 < Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ)) ∨ 1 < Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ)))
    (h1 : p.1.val ≤ q.1.val + 1) (h2 : q.1.val ≤ p.1.val + 1)
    (h3 : p.2.val ≤ q.2.val + 1) (h4 : q.2.val ≤ p.2.val + 1) : False := by
  have e1 := Int.natAbs_eq ((p.1 : ℤ) - (q.1 : ℤ))
  have e2 := Int.natAbs_eq ((p.2 : ℤ) - (q.2 : ℤ))
  omega

theorem no_valid_ge2 (n k : ℕ) (hn : 2 ≤ n) (hnk : n < 4 * k) (S : Finset (Fin n × Fin n))
    (hS : IsValidKingPlacement n k S) : False := by
  obtain ⟨hrow, hcol, hna⟩ := hS
  have c1 : 1 < n := by omega
  have hne : (S.filter fun p => p.2 = (⟨1, c1⟩ : Fin n)).Nonempty := by
    rw [← Finset.card_pos, hcol]
    omega
  obtain ⟨p0, hp0⟩ := hne
  rw [Finset.mem_filter] at hp0
  obtain ⟨hp0S, hp0c⟩ := hp0
  have hp0c' : p0.2.val = 1 := by rw [hp0c]
  obtain ⟨r', hr'ne, hr'1, hr'2⟩ : ∃ r' : Fin n, r'.val ≠ p0.1.val ∧
      r'.val ≤ p0.1.val + 1 ∧ p0.1.val ≤ r'.val + 1 := by
    by_cases h : p0.1.val + 1 < n
    · refine ⟨⟨p0.1.val + 1, h⟩, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨⟨p0.1.val - 1, by omega⟩, ?_, ?_, ?_⟩ <;> simp <;> omega
  have hdisj : Disjoint (S.filter fun p => p.1 = p0.1) (S.filter fun p => p.1 = r') := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    apply hr'ne
    rw [← h1, ← h2]
  have hcardA : ((S.filter fun p => p.1 = p0.1) ∪ (S.filter fun p => p.1 = r')).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hdisj, hrow, hrow]
    omega
  have hmem : ∀ q ∈ ((S.filter fun p => p.1 = p0.1) ∪ (S.filter fun p => p.1 = r')),
      q ∈ S ∧ q.1.val ≤ p0.1.val + 1 ∧ p0.1.val ≤ q.1.val + 1 ∧
        (q.1.val = p0.1.val ∨ q.1.val = r'.val) := by
    intro q hq
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hq
    rcases hq with ⟨hqS, hq1⟩ | ⟨hqS, hq1⟩
    · have : q.1.val = p0.1.val := by rw [hq1]
      exact ⟨hqS, by omega, by omega, Or.inl this⟩
    · have : q.1.val = r'.val := by rw [hq1]
      exact ⟨hqS, by omega, by omega, Or.inr this⟩
  have hpos : ∀ q ∈ ((S.filter fun p => p.1 = p0.1) ∪ (S.filter fun p => p.1 = r')),
      1 ≤ q.2.val := by
    intro q hq
    obtain ⟨hqS, hq1, hq2, -⟩ := hmem q hq
    by_contra hlt
    have hq0 : q.2.val = 0 := by omega
    have hpq : p0 ≠ q := by
      intro e
      rw [← e] at hq0
      omega
    exact attack p0 q (hna p0 hp0S q hqS hpq) (by omega) (by omega) (by omega) (by omega)
  have hle := Finset.card_le_card_of_injOn (t := Finset.range (n / 2))
    (fun q : Fin n × Fin n => (q.2.val - 1) / 2) (s := ((S.filter fun p => p.1 = p0.1) ∪
      (S.filter fun p => p.1 = r'))) ?_ ?_
  · rw [hcardA, Finset.card_range] at hle
    omega
  · intro q hq
    have h1 := hpos q hq
    have h2 := q.2.isLt
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro p hp q hq hpq
    simp only at hpq
    have hp1 := hpos p hp
    have hq1 := hpos q hq
    obtain ⟨hpS, -, -, hpr⟩ := hmem p hp
    obtain ⟨hqS, -, -, hqr⟩ := hmem q hq
    by_contra hne
    exact attack p q (hna p hpS q hqS hne) (by omega) (by omega) (by omega) (by omega)

theorem no_valid (n k : ℕ) (hn : 1 ≤ n) (hnk : n < 4 * k) (hne : ¬ (n = 1 ∧ k = 1))
    (S : Finset (Fin n × Fin n)) (hS : IsValidKingPlacement n k S) : False := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have hk : k ≠ 1 := fun e => hne ⟨rfl, e⟩
    have hr := hS.1 0
    have hc := Finset.card_le_univ (S.filter fun p => p.1 = 0)
    rw [hr] at hc
    simp at hc
    omega
  · exact no_valid_ge2 n k h hnk S hS

theorem pt_eq (p : Fin 1 × Fin 1) : p = (0, 0) :=
  Prod.ext (Fin.fin_one_eq_zero _) (Fin.fin_one_eq_zero _)

theorem valid11 (S : Finset (Fin 1 × Fin 1)) : IsValidKingPlacement 1 1 S ↔ S = {(0, 0)} := by
  constructor
  · rintro ⟨hrow, -, -⟩
    have h := hrow 0
    have hf : (S.filter fun p => p.1 = 0) = S := by
      apply Finset.filter_true_of_mem
      intro p _
      exact Fin.fin_one_eq_zero _
    rw [hf] at h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    rw [pt_eq a]
  · rintro rfl
    refine ⟨fun r => ?_, fun c => ?_, ?_⟩
    · rw [Finset.filter_true_of_mem]
      · rfl
      · intro p _
        rw [Fin.fin_one_eq_zero p.1, Fin.fin_one_eq_zero r]
    · rw [Finset.filter_true_of_mem]
      · rfl
      · intro p _
        rw [Fin.fin_one_eq_zero p.2, Fin.fin_one_eq_zero c]
    · intro p hp q hq hpq
      rw [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq

theorem card_filter_zero {α : Type*} [Fintype α] (P : α → Prop) (inst : DecidablePred P)
    (h : ∀ x, ¬ P x) : (@Finset.filter α P inst Finset.univ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  exact h x

theorem card_filter_one {α : Type*} [Fintype α] (P : α → Prop) (inst : DecidablePred P) (a : α)
    (h : ∀ x, P x ↔ x = a) : (@Finset.filter α P inst Finset.univ).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext x
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hx => (h x).1 hx.2, fun hx => ⟨Finset.mem_univ x, (h x).2 hx⟩⟩

theorem T11 : T 1 1 = 1 := by
  unfold T
  exact card_filter_one _ _ _ valid11

end R387098

open R387098 in
theorem OMA.solution : type_of% @OMA.S_oeis_a387098.main := by
  refine ⟨T11, ?_⟩
  intro n k hn hnk hne
  unfold OMA.S_oeis_a387098.T
  exact card_filter_zero _ _ (fun S hS => no_valid n k hn hnk hne S hS)
