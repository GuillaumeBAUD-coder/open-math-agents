import OMAStatements.S_oeis_a226838
import Mathlib

open OMA.S_oeis_a226838

namespace P226838

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

lemma term (n k : ℕ) (hk : 1 ≤ k) (h : (k + 1) ^ 2 ≤ n + 1) :
    6 ∣ n.factorial / ((n + 1 - (k + 1) ^ 2).factorial * (k + 1) ^ (k + 1 - 2)) := by
  apply Nat.dvd_div_of_mul_dvd
  have hK1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add (n + 1 - (k + 1) ^ 2) ((k + 1) ^ 2 - 1)
  rw [show n + 1 - (k + 1) ^ 2 + ((k + 1) ^ 2 - 1) = n by omega] at h1
  calc (n + 1 - (k + 1) ^ 2).factorial * (k + 1) ^ (k + 1 - 2) * 6
        = (n + 1 - (k + 1) ^ 2).factorial * (6 * (k + 1) ^ (k + 1 - 2)) := by ring
    _ ∣ (n + 1 - (k + 1) ^ 2).factorial * ((k + 1) ^ 2 - 1).factorial :=
        mul_dvd_mul_left _ (W (k + 1) (by omega))
    _ ∣ n.factorial := h1

lemma step (n : ℕ) : a (n + 1) ≡ a n [MOD 6] := by
  rw [a, Fin.sum_univ_succ]
  have hd : 6 ∣ ∑ i : Fin n, (if ((i.succ : Fin (n + 1)).1 + 1) ^ 2 ≤ n + 1 then
      (n.factorial / ((n + 1 - ((i.succ : Fin (n + 1)).1 + 1) ^ 2).factorial *
        ((i.succ : Fin (n + 1)).1 + 1) ^ ((i.succ : Fin (n + 1)).1 + 1 - 2))) *
        a (n + 1 - ((i.succ : Fin (n + 1)).1 + 1) ^ 2) else 0) := by
    apply Finset.dvd_sum
    intro i _
    split_ifs with h
    · exact dvd_mul_of_dvd_left (term n _ (by simp) h) _
    · exact dvd_zero _
  obtain ⟨c, hc⟩ := hd
  rw [hc]
  simp only [Fin.val_zero, zero_add, one_pow, show 1 ≤ n + 1 by omega, if_true,
    show n + 1 - 1 = n by omega, show 0 + 1 - 2 = 0 by rfl, pow_zero, mul_one,
    Nat.div_self (Nat.factorial_pos n), one_mul]
  unfold Nat.ModEq
  omega

end P226838

theorem OMA.solution : type_of% @OMA.S_oeis_a226838.main := by
  intro n
  induction n with
  | zero => rw [a]
  | succ n ih => exact (P226838.step n).trans ih
