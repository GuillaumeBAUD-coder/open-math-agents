import OMAReductions.R_SternPrime_isSternPrime_iff_R1
import Mathlib.Tactic

/-!
# Verification of the eight known Stern primes
-/

private lemma stern_of_bound (q B : ℕ) (hq : q.Prime) (hB : q < 2 * B ^ 2)
    (hno : ∀ b : ℕ, 1 ≤ b → b < B → ¬ (q - 2 * b ^ 2).Prime) :
    SternPrime.IsSternPrime q := by
  refine ⟨hq, ?_⟩
  rintro ⟨p, b, hp, hb1, heq⟩
  have hbB : b < B := by
    by_contra hge
    have hle : B ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (Nat.le_of_not_lt hge) 2
    omega
  have hp_eq : q - 2 * b ^ 2 = p := by omega
  exact hno b hb1 hbB (hp_eq ▸ hp)

private lemma stern_2 : SternPrime.IsSternPrime 2 := by
  refine stern_of_bound 2 2 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_3 : SternPrime.IsSternPrime 3 := by
  refine stern_of_bound 3 2 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_17 : SternPrime.IsSternPrime 17 := by
  refine stern_of_bound 17 3 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_137 : SternPrime.IsSternPrime 137 := by
  refine stern_of_bound 137 9 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_227 : SternPrime.IsSternPrime 227 := by
  refine stern_of_bound 227 11 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_977 : SternPrime.IsSternPrime 977 := by
  refine stern_of_bound 977 23 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_1187 : SternPrime.IsSternPrime 1187 := by
  refine stern_of_bound 1187 25 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private lemma stern_1493 : SternPrime.IsSternPrime 1493 := by
  refine stern_of_bound 1493 28 (by norm_num) (by norm_num) ?_
  intro b hb1 hbB
  interval_cases b <;> norm_num

private theorem prove_SternPrime_H2 :
    ∀ q : ℕ, q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) →
      SternPrime.IsSternPrime q := by
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stern_2
  · exact stern_3
  · exact stern_17
  · exact stern_137
  · exact stern_227
  · exact stern_977
  · exact stern_1187
  · exact stern_1493

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 :=
  prove_SternPrime_H2
