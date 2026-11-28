import OMAStatements.S_oeis_a064415
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a064415

/-- The completely additive extension of the values of A064415 on primes. -/
noncomputable def phiHeight (n : ℕ) : ℕ := n.factorization.sum (fun p e => e * a064415 p)

theorem phiHeight_one : phiHeight 1 = 0 := by simp [phiHeight]

theorem phiHeight_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    phiHeight (x * y) = phiHeight x + phiHeight y := by
  unfold phiHeight
  rw [Nat.factorization_mul hx hy, Finsupp.sum_add_index']
  · intro i; simp
  · intro i b1 b2; ring

theorem phiHeight_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    phiHeight (p ^ k) = k * a064415 p := by
  unfold phiHeight
  rw [hp.factorization_pow, Finsupp.sum_single_index]
  simp

theorem phiHeight_prime {p : ℕ} (hp : p.Prime) : phiHeight p = a064415 p := by
  have := phiHeight_prime_pow hp 1
  simpa using this

theorem phiHeight_prod (S : Finset ℕ) (g : ℕ → ℕ) (hg : ∀ x ∈ S, g x ≠ 0) :
    phiHeight (∏ x ∈ S, g x) = ∑ x ∈ S, phiHeight (g x) := by
  induction S using Finset.induction_on with
  | empty => simp [phiHeight_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
    have h2 : ∀ x ∈ s, g x ≠ 0 := fun x hx => hg x (Finset.mem_insert_of_mem hx)
    rw [phiHeight_mul h1 (Finset.prod_ne_zero_iff.mpr h2), ih h2]

theorem iterPhi_one : iterPhi 1 = 0 := by simp [iterPhi]

theorem iterPhi_step {n : ℕ} (hn : 2 ≤ n) : iterPhi n = 1 + iterPhi (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [iterPhi]

theorem a_one : a064415 1 = 0 := by simp [a064415, iterPhi_one]

theorem a_two : a064415 2 = 1 := by
  simp [a064415, iterPhi_step (le_refl 2), Nat.totient_two, iterPhi_one]

theorem a_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : a064415 p = a064415 (p - 1) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  unfold a064415
  rw [iterPhi_step hp.two_le, Nat.totient_prime hp]
  have : (p - 1) % 2 = 0 := by omega
  simp [hodd, this]

theorem phiHeight_totient {n : ℕ} (hn : n ≠ 0)
    (H : ∀ k, 1 ≤ k → k < n → a064415 k = phiHeight k) :
    phiHeight (Nat.totient n) + (if 2 ∣ n then 1 else 0) = phiHeight n := by
  rw [Nat.totient_eq_prod_factorization hn]
  unfold Finsupp.prod
  rw [phiHeight_prod]
  · conv_rhs => unfold phiHeight
    unfold Finsupp.sum
    rw [Nat.support_factorization]
    have hif : (if 2 ∣ n then 1 else 0) = ∑ p ∈ n.primeFactors, (if p = 2 then 1 else 0) := by
      rw [Finset.sum_ite_eq']
      simp [Nat.mem_primeFactors_of_ne_zero hn, Nat.prime_two]
    rw [hif, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ≤ n := Nat.le_of_mem_primeFactors hp
    have hk : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
    obtain ⟨j, hj⟩ : ∃ j, n.factorization p = j + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [hj]
    have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
    rw [phiHeight_mul (pow_ne_zero _ hpp.ne_zero) hp1, phiHeight_prime_pow hpp]
    by_cases h2 : p = 2
    · subst h2
      simp [phiHeight_one, a_two]
    · have hp1' : phiHeight (p - 1) = a064415 p := by
        rw [← H (p - 1) (by have := hpp.two_le; omega) (by have := hpp.two_le; omega),
          a_odd_prime hpp h2]
      rw [hp1']
      simp [h2]
      ring
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    exact Nat.mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (by have := hpp.two_le; omega)

theorem a_eq_phiHeight : ∀ n, 1 ≤ n → a064415 n = phiHeight n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · rw [a_one, phiHeight_one]
    · rw [phiHeight_prime Nat.prime_two]
    · have hm := Nat.totient_even (show 2 < n by omega)
      have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
      have hlt : Nat.totient n < n := Nat.totient_lt n (by omega)
      have hm2 : (Nat.totient n) % 2 = 0 := Nat.even_iff.mp hm
      have hIH := ih (Nat.totient n) hlt hpos
      have hiter : a064415 (Nat.totient n) = iterPhi (Nat.totient n) := by
        simp [a064415, hm2]
      have key := phiHeight_totient (show n ≠ 0 by omega) (fun k hk hkn => ih k hkn hk)
      have hstep := iterPhi_step (show 2 ≤ n by omega)
      unfold a064415
      by_cases hev : n % 2 = 0
      · have h2n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hev
        simp only [h2n, if_true] at key
        simp only [hev, if_true]
        omega
      · have h2n : ¬ 2 ∣ n := fun h => hev (Nat.mod_eq_zero_of_dvd h)
        simp only [h2n, if_false] at key
        simp only [hev, if_false]
        omega

theorem a_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : a064415 (m * n) = a064415 m + a064415 n := by
  rw [a_eq_phiHeight _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))),
    a_eq_phiHeight m hm, a_eq_phiHeight n hn, phiHeight_mul (by omega) (by omega)]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a064415.main := by
  refine ⟨⟨a_one, a_two⟩, a_mul, ?_, ?_⟩
  · intro p hp h3
    have h2 : p ≠ 2 := by omega
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    rw [a_odd_prime hp h2]
    have : p - 1 = 2 * ((p - 1) / 2) := by omega
    rw [this, a_mul 2 _ (by norm_num) (by omega), a_two]
    congr 2
    omega
  · intro k
    have h3 : OMA.S_oeis_a064415.a064415 3 = 1 := by
      rw [a_odd_prime Nat.prime_three (by norm_num)]
      exact a_two
    induction k with
    | zero => simp [a_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, a_mul _ _ (Nat.one_le_two_pow) (by norm_num),
        a_mul _ _ (Nat.one_le_pow _ _ (by norm_num)) (by norm_num), ih.1, ih.2, a_two, h3]
      exact ⟨rfl, rfl⟩
