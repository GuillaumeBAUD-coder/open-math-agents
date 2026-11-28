import OMAStatements.S_oeis_a341522
import Mathlib

open OMA.S_oeis_a341522

theorem OMA.solution : type_of% @OMA.S_oeis_a341522.main := by
  intro ps d inv _ h2 _ de dodd hinv n
  have hpow : ∀ v x, x ≠ 0 → d (2 ^ v * x) = 2 ^ v * d x := fun v x hx => by
    induction v <;> simp_all [pow_succ', mul_assoc, Nat.one_le_iff_ne_zero]
  have := @pow_succ_padicValNat_not_dvd 2 (n + 1) _ (by omega)
  obtain ⟨o, ho⟩ := @pow_padicValNat_dvd 2 (n + 1)
  generalize padicValNat 2 (n + 1) = v at *
  rcases Nat.even_or_odd' o with ⟨i, rfl | rfl⟩
  · exact absurd ⟨i, by rw [ho]; ring⟩ this
  rw [← show d (2 ^ v * (2 * (2 * i + 1) + 1)) = 3 * d (n + 1) by
    rw [ho, hpow _ _ (by omega), hpow _ _ (by omega), dodd, dodd, mul_left_comm, ← h2, ← de _ (by omega)]; rfl, hinv _ (Nat.pos_of_ne_zero (by simp))]
  ring_nf at *
  omega
