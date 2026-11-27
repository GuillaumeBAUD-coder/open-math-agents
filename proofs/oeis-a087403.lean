import OMAStatements.S_oeis_a087403
import Mathlib

/-!
# Disproof of the nonvanishing conjecture for OEIS A087403: a(100) = 0

For n = 100 and c copies, 10 * K + 1 = V = 1 + 1000 + ... + 1000^c, a sum of N = c + 1 >= 2
powers of 1000. With R = 1 + 10 + ... + 10^(N-1) and W = 10^(2N) + 10^N + 1 one has
999 V = 1000^N - 1 = (10^N - 1) W = 9 R W, so 111 V = R W. If V were prime it would divide
R (impossible, 0 < R < V) or W; in the latter case R divides 111, which forces N = 3, and
then V = 1001001 = 3 * 333667. The case N = 2 gives V = 1001 = 7 * 11 * 13.
So no candidate is prime and a(100) = sInf of the empty set = 0. This is in line with
Farideh Firoozbakht's refutation recorded in OEIS A087403 (Jan 07 2015: a(10^m) = 0).
-/

namespace OMA.P_oeis_a087403

open OMA.S_oeis_a087403 Finset

lemma geom10 (N : ℕ) : 9 * (∑ j ∈ range N, 10 ^ j) + 1 = 10 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, pow_succ]; omega

lemma geom1000 (N : ℕ) : 999 * (∑ j ∈ range N, 1000 ^ j) + 1 = 1000 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, pow_succ]; omega

lemma value_eq (c : ℕ) : 10 * repeatDecimal 100 c + 1 = ∑ j ∈ range (c + 1), 1000 ^ j := by
  have hd : (Nat.digits 10 100).length = 3 := by norm_num
  unfold repeatDecimal
  rw [hd, sum_range_succ', mul_sum]
  simp only [pow_zero]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show (10 : ℕ) ^ 3 = 1000 by norm_num, pow_succ]
  ring

lemma not_prime_value (N : ℕ) (hN : 2 ≤ N) : ¬ (∑ j ∈ range N, 1000 ^ j).Prime := by
  set V := ∑ j ∈ range N, 1000 ^ j with hV
  set R := ∑ j ∈ range N, 10 ^ j with hR
  set W := 10 ^ (2 * N) + 10 ^ N + 1 with hW
  have g1 := geom10 N
  have g2 := geom1000 N
  rw [← hR] at g1
  rw [← hV] at g2
  have e1 : (1000 : ℕ) ^ N = (10 ^ N) ^ 3 := by
    rw [← pow_mul, show (1000 : ℕ) = 10 ^ 3 by norm_num, ← pow_mul, mul_comm]
  have e2 : (10 : ℕ) ^ (2 * N) = (10 ^ N) ^ 2 := by rw [← pow_mul, mul_comm]
  have key : 9 * (111 * V) = 9 * (R * W) := by
    have h3 : (9 * R + 1) ^ 3 = 9 * R * ((9 * R + 1) ^ 2 + (9 * R + 1) + 1) + 1 := by ring
    rw [hW, e2, ← g1]
    rw [e1, ← g1, h3] at g2
    nlinarith [g2]
  have key' : 111 * V = R * W := Nat.eq_of_mul_eq_mul_left (by norm_num) key
  have hpow : 100 ≤ 10 ^ N := by
    calc (100 : ℕ) = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hRpos : 11 ≤ R := by omega
  have hWbig : 112 ≤ W := by
    have : 10000 ≤ 10 ^ (2 * N) := by rw [e2]; nlinarith
    rw [hW]; omega
  intro hp
  have hdvd : V ∣ R * W := ⟨111, by rw [← key']; ring⟩
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · have hle : V ≤ R := Nat.le_of_dvd (by omega) h
    have : 111 * V < R * W := by
      calc 111 * V ≤ 111 * R := by omega
        _ < R * W := by nlinarith
    omega
  · obtain ⟨t, ht⟩ := h
    have hVpos : 0 < V := hp.pos
    have h111 : 111 = R * t := by
      have : V * 111 = V * (R * t) := by rw [mul_comm V 111, key', ht]; ring
      exact Nat.eq_of_mul_eq_mul_left hVpos this
    have hRle : R ≤ 111 := Nat.le_of_dvd (by norm_num) ⟨t, h111⟩
    by_cases hN4 : 4 ≤ N
    · have : 10000 ≤ 10 ^ N := by
        calc (10000 : ℕ) = 10 ^ 4 := by norm_num
          _ ≤ 10 ^ N := Nat.pow_le_pow_right (by norm_num) hN4
      omega
    · have hN' : N = 2 ∨ N = 3 := by omega
      rcases hN' with rfl | rfl
      · rw [hV] at hp; norm_num [sum_range_succ] at hp
      · rw [hV] at hp; norm_num [sum_range_succ] at hp

lemma a100 : a 100 = 0 := by
  unfold a
  have hempty : {p : ℕ | p.Prime ∧ ∃ copies : ℕ, 0 < copies ∧
      p = 10 * repeatDecimal 100 copies + 1} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hp ⟨c, hc, rfl⟩
    rw [value_eq] at hp
    exact not_prime_value (c + 1) (by omega) hp
  rw [hempty, Nat.sInf_empty]

end OMA.P_oeis_a087403

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087403.main) := by
  intro h
  exact h 100 (by norm_num) OMA.P_oeis_a087403.a100
