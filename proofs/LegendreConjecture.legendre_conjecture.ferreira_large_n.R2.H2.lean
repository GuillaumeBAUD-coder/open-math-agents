import OMAReductions.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R2
import Mathlib

-- Step LegendreConjecture.legendre_conjecture.ferreira_large_n.R2.H2: hypothesis H2 of reduction LegendreConjecture.legendre_conjecture.ferreira_large_n.R2
-- Credit: @Raimo33

namespace OMAE_Leg
open Finset

lemma big (n : ℕ) (hn : 10 ≤ n) : (2 * n + 1) ^ 3 < n ^ 4 := by
  have h1 : (10 * (2 * n + 1)) ^ 3 ≤ (21 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : 10 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
  have h3 : 0 < n ^ 3 := by positivity
  rw [mul_pow, mul_pow] at h1
  have : n * n ^ 3 = n ^ 4 := by ring
  nlinarith

lemma key (n p q k : ℕ) (hn : 10 ≤ n) (hk : 2 ≤ k) (hpq : p < q)
    (h1 : n ^ 2 < p ^ k) (h2 : q ^ k < (n + 1) ^ 2) : False := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    have : n < p := by
      by_contra hc; push Not at hc
      have := Nat.pow_le_pow_left hc 2; omega
    have : (n + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · have hq : 1 ≤ q := by omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hp : p ^ (j + 1) ≤ (q - 1) ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
    have hq1 : (q - 1) ^ (j + 1) ≤ (q - 1) * q ^ j := by
      rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hqq : (q - 1) * q ^ j + q ^ j = q ^ (j + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; ring
    have hdiff : q ^ j < 2 * n + 1 := by
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hsq : (q ^ (j + 1)) ^ 2 ≤ (q ^ j) ^ 3 := by
      rw [← pow_mul, ← pow_mul]; exact Nat.pow_le_pow_right hq (by omega)
    have hA : (n ^ 2) ^ 2 < (q ^ (j + 1)) ^ 2 := by
      have : p ^ (j + 1) < q ^ (j + 1) := Nat.pow_lt_pow_left hpq (by omega)
      exact Nat.pow_lt_pow_left (by omega) (by omega)
    have hB : (q ^ j) ^ 3 < (2 * n + 1) ^ 3 := Nat.pow_lt_pow_left hdiff (by omega)
    have := big n hn
    rw [← pow_mul, show 2 * 2 = 4 from rfl] at hA
    omega

theorem main (n : ℕ) : (((Ioo (n^2) ((n+1)^2)).filter (fun m => IsPrimePow m ∧ ¬m.Prime)).card) ≤
    Nat.log 2 ((n+1)^2) := by
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> decide +kernel
  · have fval : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → (p ^ k).factorization (p ^ k).minFac = k := by
      intro p k hp hk
      rw [Nat.pow_minFac hk, hp.minFac_eq, hp.factorization_pow]; simp
    have dest : ∀ m ∈ (Ioo (n^2) ((n+1)^2)).filter (fun m => IsPrimePow m ∧ ¬m.Prime),
        ∃ p k, p.Prime ∧ 2 ≤ k ∧ p ^ k = m ∧ n ^ 2 < m ∧ m < (n + 1) ^ 2 := by
      intro m hm
      simp only [mem_filter, mem_Ioo] at hm
      obtain ⟨⟨h1, h2⟩, hpp, hnp⟩ := hm
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      refine ⟨p, k, hp, ?_, rfl, h1, h2⟩
      by_contra hc
      obtain rfl : k = 1 := by omega
      exact hnp (by simpa using hp)
    calc _ ≤ (Icc 2 (Nat.log 2 ((n+1)^2))).card := by
          apply Finset.card_le_card_of_injOn (fun m => m.factorization m.minFac)
          · intro m hm
            obtain ⟨p, k, hp, hk, rfl, h1, h2⟩ := dest m hm
            show (p ^ k).factorization (p ^ k).minFac ∈ Icc 2 _
            rw [Finset.mem_Icc, fval hp (by omega)]
            refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
            calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le _
              _ ≤ _ := h2.le
          · intro m1 hm1 m2 hm2 he
            obtain ⟨p, k, hp, hk, rfl, h1, h2⟩ := dest m1 hm1
            obtain ⟨q, l, hq, hl, rfl, h3, h4⟩ := dest m2 hm2
            simp only at he
            rw [fval hp (by omega), fval hq (by omega)] at he
            subst he
            rcases lt_trichotomy p q with hpq | rfl | hpq
            · exact (key n p q k hn hk hpq h1 h4).elim
            · rfl
            · exact (key n q p k hn hk hpq h3 h2).elim
      _ ≤ _ := by simp

end OMAE_Leg

theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R2.H2 :=
  OMAE_Leg.main
