import OMAReductions.R_oeis_a293483_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- For the moduli 1, 2, 4, 8 and 1, 3, 9 every unit u satisfies u^6 = 1 (decide, and ZMod.pow_totient for 9),
-- so the set of sixth powers is the singleton of 1 and its cardinality is 1.

namespace OMA.R_oeis_a293483_R1_Proof

open OMA.S_oeis_a293483 OMA.R_oeis_a293483_R1

lemma card_one_of_pow (m : ℕ) (h : ∀ u : (ZMod m)ˣ, u ^ 6 = 1) : a293483 m = 1 := by
  unfold a293483
  have hs : Set.range (fun u : (ZMod m)ˣ => u ^ 6) = {1} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      exact h u
    · rintro rfl
      exact ⟨1, one_pow _⟩
  rw [hs]
  simp

lemma p1 : ∀ u : (ZMod 1)ˣ, u ^ 6 = 1 := by decide
lemma p2 : ∀ u : (ZMod 2)ˣ, u ^ 6 = 1 := by decide
lemma p4 : ∀ u : (ZMod 4)ˣ, u ^ 6 = 1 := by decide
lemma p8 : ∀ u : (ZMod 8)ˣ, u ^ 6 = 1 := by decide
lemma p3 : ∀ u : (ZMod 3)ˣ, u ^ 6 = 1 := by decide
lemma p9 : ∀ u : (ZMod 9)ˣ, u ^ 6 = 1 := by
  intro u
  have h := ZMod.pow_totient u
  have h9 : Nat.totient 9 = 6 := by decide
  rwa [h9] at h

theorem h1 : OMA.R_oeis_a293483_R1.H1 := by
  intro e he
  interval_cases e
  · exact card_one_of_pow _ p1
  · exact card_one_of_pow _ p2
  · exact card_one_of_pow _ p4
  · exact card_one_of_pow _ p8

theorem h3 : OMA.R_oeis_a293483_R1.H3 := by
  intro e he
  interval_cases e
  · exact card_one_of_pow _ p1
  · exact card_one_of_pow _ p3
  · exact card_one_of_pow _ p9

end OMA.R_oeis_a293483_R1_Proof

theorem OMA.solution : OMA.R_oeis_a293483_R1.H1 := OMA.R_oeis_a293483_R1_Proof.h1
