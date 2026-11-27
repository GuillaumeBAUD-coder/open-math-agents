import OMAStatements.S_oeis_a326691
import Mathlib

namespace OMA.A326691Proof

open Finset OMA.S_oeis_a326691

lemma p_dvd_div {n p q : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n) (hq : q ∈ n.primeFactors) :
    p ∣ n / q := by
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hqn := Nat.dvd_of_mem_primeFactors hq
  by_cases h : q = p
  · subst h
    exact Nat.dvd_div_of_mul_dvd (by simpa [pow_two] using hpn)
  · have : p ∣ q * (n / q) := by
      rw [Nat.mul_div_cancel' hqn]; exact (dvd_pow_self p two_ne_zero).trans hpn
    rcases (Nat.Prime.dvd_mul hp).1 this with h1 | h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq').1 h1).symm h
    · exact h1

lemma key {n g : ℕ} (hgn : g ∣ n) (X Y : ℤ) (c : ℕ → ℤ) (hgX : (g : ℤ) ∣ X)
    (hXY : X - Y = ∑ q ∈ n.primeFactors, c q * ((n / q : ℕ) : ℤ))
    (hc : ∀ q ∈ n.primeFactors, n.factorization q = 1 → c q = 0)
    (hX : ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → ¬ (p : ℤ) ∣ X) : (g : ℤ) ∣ Y := by
  have hsum : (g : ℤ) ∣ X - Y := by
    rw [hXY]
    apply Finset.dvd_sum
    intro q hq
    by_cases h1 : n.factorization q = 1
    · simp [hc q hq h1]
    · apply Dvd.dvd.mul_left
      have hq' := Nat.prime_of_mem_primeFactors hq
      have hqn := Nat.dvd_of_mem_primeFactors hq
      have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hq).2.2
      have hne : n.factorization q ≠ 0 := by
        rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hq
      have h2 : q ^ 2 ∣ n := (hq'.pow_dvd_iff_le_factorization hn0).2 (by omega)
      have hng : ¬ q ∣ g := by
        intro hd
        exact hX q hq' h2 ((Int.natCast_dvd_natCast.2 hd).trans hgX)
      have hcop : Nat.Coprime q g := (Nat.Prime.coprime_iff_not_dvd hq').2 hng
      have : g ∣ n / q := hcop.symm.dvd_of_dvd_mul_left (by rwa [Nat.mul_div_cancel' hqn])
      exact Int.natCast_dvd_natCast.2 this
  have := dvd_sub hgX hsum
  simpa using this

theorem sol : ∀ n : ℕ, 0 < n →
    sequence n = Nat.gcd n (1 + (n - 1) * arithmeticDerivative n) := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  set T : ℤ := ∑ q ∈ n.primeFactors, ((n / q : ℕ) : ℤ) with hT
  set D : ℤ := ∑ q ∈ n.primeFactors, ((n.factorization q : ℕ) : ℤ) * ((n / q : ℕ) : ℤ) with hD
  have hDdef : ((arithmeticDerivative n : ℕ) : ℤ) = D := by
    simp [arithmeticDerivative, hD]
  have step1 : (∑ p ∈ n.primeFactors, (1 : ℚ) / p) - 1 / (n : ℚ)
      = (((T - 1 : ℤ)) : ℚ) / (((n : ℤ)) : ℚ) := by
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have : ∀ p ∈ n.primeFactors, (1 : ℚ) / p = (((n / p : ℕ) : ℤ) : ℚ) / n := by
      intro p hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [Int.cast_natCast, Nat.cast_div hpn hp0]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, hT]
    push_cast
    field_simp
  have hp_T : ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → (p : ℤ) ∣ T := by
    intro p hp h2
    apply Finset.dvd_sum
    intro q hq
    exact Int.natCast_dvd_natCast.2 (p_dvd_div hp h2 hq)
  have hp_D : ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → (p : ℤ) ∣ D := by
    intro p hp h2
    apply Finset.dvd_sum
    intro q hq
    exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (p_dvd_div hp h2 hq)) _
  have hXA : ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → ¬ (p : ℤ) ∣ (T - 1) := by
    intro p hp h2 hd
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (hp_T p hp h2) hd
      simpa using this
    have := Int.natCast_dvd_natCast.1 (by simpa using h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hXD : ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → ¬ (p : ℤ) ∣ (D - 1) := by
    intro p hp h2 hd
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (hp_D p hp h2) hd
      simpa using this
    have := Int.natCast_dvd_natCast.1 (by simpa using h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have gdvd : ∀ X : ℤ, Int.gcd (n : ℤ) X ∣ n := by
    intro X
    have := Int.gcd_dvd_left (a := (n : ℤ)) (b := X)
    exact_mod_cast this
  have step3 : Int.gcd (n : ℤ) (T - 1) = Int.gcd (n : ℤ) (D - 1) := by
    apply Nat.dvd_antisymm
    · have h := key (gdvd (T - 1)) (T - 1) (D - 1)
        (fun q => 1 - ((n.factorization q : ℕ) : ℤ)) (Int.gcd_dvd_right _ _)
        (by rw [hT, hD]; simp only [Finset.sum_sub_distrib, sub_mul, one_mul]; ring)
        (by intro q _ h; simp [h]) hXA
      have := Int.dvd_coe_gcd (Int.gcd_dvd_left (a := (n : ℤ)) (b := T - 1)) h
      exact_mod_cast this
    · have h := key (gdvd (D - 1)) (D - 1) (T - 1)
        (fun q => ((n.factorization q : ℕ) : ℤ) - 1) (Int.gcd_dvd_right _ _)
        (by rw [hT, hD]; simp only [Finset.sum_sub_distrib, sub_mul, one_mul]; ring)
        (by intro q _ h; simp [h]) hXD
      have := Int.dvd_coe_gcd (Int.gcd_dvd_left (a := (n : ℤ)) (b := D - 1)) h
      exact_mod_cast this
  have step4 : Nat.gcd n (1 + (n - 1) * arithmeticDerivative n) = Int.gcd (n : ℤ) (D - 1) := by
    rw [← Int.gcd_natCast_natCast]
    have : (((1 + (n - 1) * arithmeticDerivative n : ℕ)) : ℤ) = -(D - 1) + (n : ℤ) * D := by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega), hDdef]
      ring
    rw [this, Int.gcd_add_mul_left_right, Int.gcd_neg]
  rw [step4, ← step3, S_oeis_a326691.sequence, step1, ← Rat.divInt_eq_div, Rat.den_divInt, if_neg (by exact_mod_cast hn0),
    Int.natAbs_natCast]
  exact Nat.div_div_self (gdvd _) hn0

end OMA.A326691Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a326691.main := by
  exact OMA.A326691Proof.sol
