import OMAStatements.S_oeis_a226890
import Mathlib

open OMA.S_oeis_a226890

namespace P226890

lemma fpow (k : ℕ) : ∀ m, (k.factorial) ^ m ∣ (k * m).factorial
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, show k * (m + 1) = k * m + k by ring]
    exact (mul_dvd_mul_right (fpow k m) _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

lemma W0 (K : ℕ) (hK : 2 ≤ K) : K ^ (K - 2) * ((K - 1).factorial) ^ K ∣ (K ^ 2 - 1).factorial := by
  have h := fpow K K
  have hK2 : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [show K * K = (K ^ 2 - 1) + 1 by rw [← sq]; omega, Nat.factorial_succ,
    show K ^ 2 - 1 + 1 = K ^ 2 by omega, ← Nat.mul_factorial_pred (show K ≠ 0 by omega), mul_pow,
    show K ^ K = K ^ 2 * K ^ (K - 2) by rw [← pow_add]; congr 1; omega, mul_assoc] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h

lemma W (K : ℕ) (hK : 2 ≤ K) : 6 * K ^ (K - 2) ∣ (K ^ 2 - 1).factorial := by
  rcases Nat.lt_or_ge K 4 with h | h
  · interval_cases K <;> decide
  · have h6 : 6 ∣ ((K - 1).factorial) ^ K :=
      (show 6 ∣ (K - 1).factorial from
        (Nat.factorial_dvd_factorial (show 3 ≤ K - 1 by omega))).trans (dvd_pow_self _ (by omega))
    rw [mul_comm]
    exact (mul_dvd_mul_left _ h6).trans (W0 K (by omega))

lemma W30 (K : ℕ) (hK : 3 ≤ K) : 30 * K ^ (K - 2) ∣ (K ^ 2 - 1).factorial := by
  rcases Nat.lt_or_ge K 6 with h | h
  · interval_cases K <;> decide +kernel
  · have h6 : 30 ∣ ((K - 1).factorial) ^ K :=
      (show 30 ∣ (K - 1).factorial from
        (show 30 ∣ (5 : ℕ).factorial by decide).trans
          (Nat.factorial_dvd_factorial (show 5 ≤ K - 1 by omega))).trans (dvd_pow_self _ (by omega))
    rw [mul_comm]
    exact (mul_dvd_mul_left _ h6).trans (W0 K (by omega))

lemma termG (n k d : ℕ) (h : (k + 1) ^ 2 ≤ n + 1)
    (hW : d * (k + 1) ^ (k + 1 - 2) ∣ ((k + 1) ^ 2 - 1).factorial) :
    d ∣ n.factorial / ((n + 1 - (k + 1) ^ 2).factorial * (k + 1) ^ (k + 1 - 2)) := by
  apply Nat.dvd_div_of_mul_dvd
  have hK1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add (n + 1 - (k + 1) ^ 2) ((k + 1) ^ 2 - 1)
  rw [show n + 1 - (k + 1) ^ 2 + ((k + 1) ^ 2 - 1) = n by omega] at h1
  rw [mul_assoc]
  exact (mul_dvd_mul_left _ ((mul_comm d _) ▸ hW)).trans h1

lemma term (n k : ℕ) (hk : 1 ≤ k) (h : (k + 1) ^ 2 ≤ n + 1) :
    6 ∣ n.factorial / ((n + 1 - (k + 1) ^ 2).factorial * (k + 1) ^ (k + 1 - 2)) :=
  termG n k 6 h (W (k + 1) (by omega))

lemma term30 (n k : ℕ) (hk : 2 ≤ k) (h : (k + 1) ^ 2 ≤ n + 1) :
    30 ∣ n.factorial / ((n + 1 - (k + 1) ^ 2).factorial * (k + 1) ^ (k + 1 - 2)) :=
  termG n k 30 h (W30 (k + 1) (by omega))

lemma sig2 : sigmaSelf 2 = 5 := by decide

lemma step (n : ℕ) : a (n + 1) ≡ a n [MOD 30] := by
  rw [a, Fin.sum_univ_succ]
  have hd : 30 ∣ ∑ i : Fin n, (if ((i.succ : Fin (n + 1)).1 + 1) ^ 2 ≤ n + 1 then
      sigmaSelf ((i.succ : Fin (n + 1)).1 + 1) *
      (n.factorial / ((n + 1 - ((i.succ : Fin (n + 1)).1 + 1) ^ 2).factorial *
        ((i.succ : Fin (n + 1)).1 + 1) ^ ((i.succ : Fin (n + 1)).1 + 1 - 2))) *
        a (n + 1 - ((i.succ : Fin (n + 1)).1 + 1) ^ 2) else 0) := by
    apply Finset.dvd_sum
    intro i _
    split_ifs with h
    · apply dvd_mul_of_dvd_left
      rcases Nat.lt_or_ge (i.succ : Fin (n + 1)).1 2 with h2 | h2
      · have hi : (i.succ : Fin (n + 1)).1 = 1 := by simp at h2 ⊢; omega
        rw [hi, sig2]
        rw [hi] at h
        have := term n 1 le_rfl h
        exact (show 30 = 5 * 6 by rfl) ▸ mul_dvd_mul_left 5 this
      · exact dvd_mul_of_dvd_right (term30 n _ h2 h) _
    · exact dvd_zero _
  obtain ⟨c, hc⟩ := hd
  rw [hc]
  simp only [Fin.val_zero, zero_add, one_pow, show 1 ≤ n + 1 by omega, if_true,
    show n + 1 - 1 = n by omega, show 0 + 1 - 2 = 0 by rfl, pow_zero, mul_one,
    Nat.div_self (Nat.factorial_pos n), one_mul]
  have s1 : sigmaSelf 1 = 1 := by decide
  rw [s1, one_mul]
  unfold Nat.ModEq
  omega

end P226890

theorem OMA.solution : type_of% @OMA.S_oeis_a226890.main := by
  intro n
  induction n with
  | zero => rw [a]
  | succ n ih => exact (P226890.step n).trans ih
