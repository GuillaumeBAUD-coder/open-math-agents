import OMAReductions.R_Erdos384_erdos_384_R1
import Mathlib

-- Step Erdos384.erdos_384.R1.H1: hypothesis H1 of reduction Erdos384.erdos_384.R1
-- Credit: @NickLeko

/-!
Ecklund's first case: if `4 ≤ k` and `k² < n`, then `C(n, k)` has a prime factor `p` with
`2p ≤ n`.

Suppose not, and let `C = C(n, k)`.
* Every prime factor `p` of `C` has `2p > n`. It divides `n (n - 1) ⋯ (n - k + 1) = k! C`, hence
  some `n - i` with `i < k`, and `n - i < 2p` forces `n - i = p`. So the prime factors of `C` lie
  in `(n - k, n]`, and (being `> n/2 > 3`) they are prime to `6`.
* Since `p ^ v_p(C) ≤ n` for every prime `p`, `C ≤ n ^ t` where `t` is the number of prime
  factors of `C`.
* `n ^ k ≤ k ^ k C`, comparing `n (k - i) ≤ k (n - i)` factor by factor.
* Numbers prime to `6` in a window of length `k` number at most `2` when `k ≤ 6` (they have
  distinct residues `1, 5 mod 6`), and at most `(k + 1) / 3 + 1` in general (`m ↦ m / 3` is
  injective on them). So `t ≤ 2` for `k = 4, 5` and `2t ≤ k` for `k ≥ 6`.
* Then `n ^ k ≤ k ^ k n ^ t < n ^ k` because `k² < n`: contradiction.
-/

namespace OMA384H1

open Finset

/-- `n ^ k ≤ k ^ k * C(n, k)` for `k ≤ n`. -/
lemma pow_le_pow_mul_choose {n k : ℕ} (hkn : k ≤ n) : n ^ k ≤ k ^ k * n.choose k := by
  have hfac : k.factorial = ∏ i ∈ range k, (k - i) := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range]
  have hdesc : k.factorial * n.choose k = ∏ i ∈ range k, (n - i) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have hle : ∏ i ∈ range k, (n * (k - i)) ≤ ∏ i ∈ range k, (k * (n - i)) := by
    apply Finset.prod_le_prod'
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have h1 : i ≤ k := hik.le
    have h2 : i ≤ n := by omega
    zify [h1, h2]
    nlinarith
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, ← hfac, ← hdesc] at hle
  have hpos : 0 < k.factorial := Nat.factorial_pos k
  have : n ^ k * k.factorial ≤ k ^ k * n.choose k * k.factorial := by
    calc n ^ k * k.factorial ≤ k ^ k * (k.factorial * n.choose k) := hle
      _ = k ^ k * n.choose k * k.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-- `C(n, k) ≤ n ^ t` where `t` is the number of prime factors of `C(n, k)`. -/
lemma choose_le_pow_card {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    n.choose k ≤ n ^ (n.choose k).primeFactors.card := by
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hC]
  rw [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_le_pow_card
  intro p _
  exact Nat.pow_factorization_choose_le hn

/-- Numbers prime to `6` in a window of length at most `6` number at most `2`. -/
lemma card_window_le_two {S : Finset ℕ} {a k : ℕ} (hk : k ≤ 6)
    (hS : ∀ m ∈ S, a < m ∧ m ≤ a + k ∧ (m % 6 = 1 ∨ m % 6 = 5)) : S.card ≤ 2 := by
  have h : S.card ≤ ({1, 5} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (fun m => m % 6)
    · intro m hm
      rcases (hS m hm).2.2 with h | h <;> simp [h]
    · intro x hx y hy hxy
      have hx' := hS x hx
      have hy' := hS y hy
      simp only at hxy
      omega
  simpa using h

/-- Numbers prime to `6` in a window of length `k` number at most `(k + 1) / 3 + 1`. -/
lemma card_window_le {S : Finset ℕ} {a k : ℕ}
    (hS : ∀ m ∈ S, a < m ∧ m ≤ a + k ∧ (m % 6 = 1 ∨ m % 6 = 5)) :
    S.card ≤ (k + 1) / 3 + 1 := by
  have h : S.card ≤ (Finset.Icc ((a + 1) / 3) ((a + k) / 3)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / 3)
    · intro m hm
      have := hS m hm
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor <;> omega
    · intro x hx y hy hxy
      have hx' := hS x hx
      have hy' := hS y hy
      simp only at hxy
      omega
  rw [Nat.card_Icc] at h
  omega

/-- Under the contrary hypothesis, each prime factor of `C(n, k)` lies in `(n - k, n]` and is
prime to `6`. -/
lemma primeFactor_mem {n k p : ℕ} (hk : 4 ≤ k) (hkn : k * k < n)
    (hno : ∀ p : ℕ, p.Prime → p ∣ n.choose k → ¬ 2 * p ≤ n)
    (hp : p ∈ (n.choose k).primeFactors) :
    n - k < p ∧ p ≤ n - k + k ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ n.choose k := Nat.dvd_of_mem_primeFactors hp
  have h2p : n < 2 * p := by have := hno p hpp hpd; omega
  have hk2 : k ≤ n := by nlinarith
  have hdesc : p ∣ ∏ i ∈ range k, (n - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left hpd _
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdesc
  have hik : i < k := Finset.mem_range.mp hi
  have hni : n - i = p := by
    obtain ⟨c, hc⟩ := hpi
    have hpos : 0 < n - i := by omega
    rcases c with _ | _ | c
    · simp at hc; omega
    · simpa using hc
    · have : p * (c + 1 + 1) ≥ 2 * p := by nlinarith
      omega
  have hp8 : 8 < p := by nlinarith
  have h2 : p % 2 = 1 := by
    rcases Nat.even_or_odd p with he | ho
    · have := (Nat.Prime.even_iff hpp).mp he; omega
    · exact Nat.odd_iff.mp ho
  have h3 : p % 3 ≠ 0 := by
    intro h
    have h3d : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h3d
    omega
  refine ⟨by omega, by omega, by omega⟩

theorem main_H1 : OMA.R_Erdos384_erdos_384_R1.H1 := by
  intro n k hk hkn
  by_contra hcon
  have hno : ∀ p : ℕ, p.Prime → p ∣ n.choose k → ¬ 2 * p ≤ n := by
    intro p hp hpd h2
    exact hcon ⟨p, hp, hpd, h2⟩
  have hkn' : k ≤ n := by nlinarith
  have hn : 0 < n := by omega
  set t := (n.choose k).primeFactors.card with ht
  have hup : n.choose k ≤ n ^ t := choose_le_pow_card hn hkn'
  have hlow : n ^ k ≤ k ^ k * n.choose k := pow_le_pow_mul_choose hkn'
  have hmem : ∀ m ∈ (n.choose k).primeFactors,
      n - k < m ∧ m ≤ n - k + k ∧ (m % 6 = 1 ∨ m % 6 = 5) :=
    fun m hm => primeFactor_mem hk hkn hno hm
  have hchain : n ^ k ≤ k ^ k * n ^ t := hlow.trans (Nat.mul_le_mul_left _ hup)
  by_cases hk6 : k ≤ 5
  · -- `t ≤ 2`
    have ht2 : t ≤ 2 := card_window_le_two (by omega) hmem
    have hnt : n ^ t ≤ n ^ 2 := Nat.pow_le_pow_right hn ht2
    have hc : n ^ k ≤ k ^ k * n ^ 2 := hchain.trans (Nat.mul_le_mul_left _ hnt)
    have : k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl
    · have h17 : 17 ≤ n := by omega
      have : 256 * n ^ 2 < n ^ 4 := by
        have h2 : 289 ≤ n ^ 2 := by
          calc 289 = 17 ^ 2 := by norm_num
            _ ≤ n ^ 2 := Nat.pow_le_pow_left h17 2
        have hn2 : 0 < n ^ 2 := by positivity
        calc 256 * n ^ 2 < n ^ 2 * n ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) hn2
          _ = n ^ 4 := by ring
      norm_num at hc
      omega
    · have h26 : 26 ≤ n := by omega
      have : 3125 * n ^ 2 < n ^ 5 := by
        have h3 : 17576 ≤ n ^ 3 := by
          calc 17576 = 26 ^ 3 := by norm_num
            _ ≤ n ^ 3 := Nat.pow_le_pow_left h26 3
        have hn2 : 0 < n ^ 2 := by positivity
        calc 3125 * n ^ 2 < n ^ 3 * n ^ 2 := by
              exact Nat.mul_lt_mul_of_pos_right (by omega) hn2
          _ = n ^ 5 := by ring
      norm_num at hc
      omega
  · -- `2t ≤ k`
    have htk : t ≤ (k + 1) / 3 + 1 := card_window_le hmem
    have h2t : 2 * t ≤ k := by omega
    have hsq : (k ^ k * n ^ t) ^ 2 < (n ^ k) ^ 2 := by
      have e1 : (k ^ k * n ^ t) ^ 2 = (k * k) ^ k * n ^ (2 * t) := by ring
      have e2 : (n ^ k) ^ 2 = n ^ k * n ^ k := by ring
      rw [e1, e2]
      have hlt : (k * k) ^ k < n ^ k := Nat.pow_lt_pow_left hkn (by omega)
      have hle : n ^ (2 * t) ≤ n ^ k := Nat.pow_le_pow_right hn h2t
      have hpos : 0 < n ^ (2 * t) := by positivity
      calc (k * k) ^ k * n ^ (2 * t) < n ^ k * n ^ (2 * t) :=
            Nat.mul_lt_mul_of_pos_right hlt hpos
        _ ≤ n ^ k * n ^ k := Nat.mul_le_mul_left _ hle
    have : k ^ k * n ^ t < n ^ k := by
      by_contra h
      rw [not_lt] at h
      have := Nat.pow_le_pow_left h 2
      omega
    omega

end OMA384H1

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H1 := OMA384H1.main_H1
