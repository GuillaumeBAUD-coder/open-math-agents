import OMAStatements.S_oeis_a129149
import Mathlib

/-!
Proof sketch. Grouping permutations by their fixed-point set S (a 7-subset), each fiber is in
bijection with the derangements of the complement of S (`derangements.subtypeEquiv`), so
a n = C(n, 7) * D(n - 7). With n = k + 9, the recurrence D(k + 2) = (k + 1)(D k + D(k + 1)) and
the binomial shifts C(N, 7) * (N + 1) = C(N + 1, 7) * (N - 6) give the identity by
`linear_combination`.
-/

namespace R129149
open OMA.S_oeis_a129149

theorem card_compl (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {a : Fin n // a ∉ S} = n - S.card := by
  simp only [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

theorem fiber (n : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter fun i : Fin n => σ i = i) = S).card = numDerangements (n - S.card) := by
  classical
  have h1 := Fintype.card_congr (derangements.subtypeEquiv (fun a : Fin n => a ∉ S))
  rw [card_derangements_eq_numDerangements, card_compl,
    Fintype.card_of_subtype (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter fun i : Fin n => σ i = i) = S)] at h1
  · exact h1.symm
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.ext_iff, not_not,
      Function.mem_fixedPoints, Function.IsFixedPt]
    exact forall_congr' fun a => iff_comm

theorem a_eq (n : ℕ) : a n = n.choose 7 * numDerangements (n - 7) := by
  unfold a
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin n) => Finset.univ.filter fun i : Fin n => σ i = i)
    (t := Finset.powersetCard 7 Finset.univ)]
  · rw [Finset.sum_congr rfl (g := fun _ => numDerangements (n - 7))]
    · simp [Finset.card_powersetCard]
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [Finset.filter_filter, show n - 7 = n - S.card by rw [hS.2], ← fiber n S]
      congr 1
      apply Finset.filter_congr
      intro σ _
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [h, hS.2], h⟩
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ
    simp [Finset.mem_powersetCard, hσ]

end R129149

theorem OMA.solution : type_of% @OMA.S_oeis_a129149.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, R129149.a_eq,
    R129149.a_eq, R129149.a_eq, show k + 9 - 7 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega,
    show k + 7 - 7 = k by omega, numDerangements_add_two]
  have h1 := Nat.choose_mul_succ_eq (k + 8) 7
  have h2 := Nat.choose_mul_succ_eq (k + 7) 7
  rw [show k + 8 + 1 - 7 = k + 2 by omega, show k + 8 + 1 = k + 9 by omega] at h1
  rw [show k + 7 + 1 - 7 = k + 1 by omega, show k + 7 + 1 = k + 8 by omega] at h2
  have h1' : ((k + 8).choose 7 : ℤ) * ((k : ℤ) + 9) = ((k + 9).choose 7 : ℤ) * ((k : ℤ) + 2) := by
    exact_mod_cast h1
  have h2' : ((k + 7).choose 7 : ℤ) * ((k : ℤ) + 8) = ((k + 8).choose 7 : ℤ) * ((k : ℤ) + 1) := by
    exact_mod_cast h2
  push_cast
  linear_combination ((k : ℤ) + 1) * ((numDerangements k : ℤ) + (numDerangements (k + 1) : ℤ)) * h1'
    + ((k : ℤ) + 9) * (numDerangements k : ℤ) * h2'
