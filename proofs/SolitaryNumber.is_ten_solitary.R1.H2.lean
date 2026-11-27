import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1

-- An odd number with abundancy 9/5 is a perfect square.
-- Original Lean proof of a classical observation: 10 sigma(m) = 18 m with m odd makes sigma(m) odd, and for
-- an odd m the divisor sum is odd only if m is a square (sigma is multiplicative, and for an odd prime p the
-- sum 1 + p + ... + p^k has the parity of k + 1).
-- A classical first step, not progress on the question whether 10 is solitary.

namespace OMA.Solitary2

open ArithmeticFunction Finset

lemma geom_parity (p : ℕ) (hp : p % 2 = 1) : ∀ m : ℕ, (∑ i ∈ range m, p ^ i) % 2 = m % 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 : p ^ m % 2 = 1 := by
      rw [Nat.pow_mod, hp]
      simp
    omega

lemma square_of_odd_sigma (n : ℕ) : n % 2 = 1 → sigma 1 n % 2 = 1 → IsSquare n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd hs
    have hp2 : p % 2 = 1 := by
      by_contra hne
      have hpe : p % 2 = 0 := by omega
      have h0 : p ^ k % 2 = 0 := by
        rw [Nat.pow_mod, hpe]
        simp [Nat.zero_pow hk]
      omega
    rw [sigma_one_apply_prime_pow hp, geom_parity p hp2] at hs
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    exact ⟨p ^ j, by rw [← pow_add]; congr 1; omega⟩
  | zero => intro h; omega
  | one => intro _ _; exact ⟨1, rfl⟩
  | coprime a b ha hb hab iha ihb =>
    intro hodd hs
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hs
    have ha2 : a % 2 = 1 := by
      by_contra hne
      have hae : a % 2 = 0 := by omega
      have : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hae]; simp
      omega
    have hb2 : b % 2 = 1 := by
      by_contra hne
      have hbe : b % 2 = 0 := by omega
      have : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hbe]; simp
      omega
    have hsa : sigma 1 a % 2 = 1 := by
      by_contra hne
      have hse : sigma 1 a % 2 = 0 := by omega
      have : (sigma 1 a * sigma 1 b) % 2 = 0 := by rw [Nat.mul_mod, hse]; simp
      omega
    have hsb : sigma 1 b % 2 = 1 := by
      by_contra hne
      have hse : sigma 1 b % 2 = 0 := by omega
      have : (sigma 1 a * sigma 1 b) % 2 = 0 := by rw [Nat.mul_mod, hse]; simp
      omega
    exact (iha ha2 hsa).mul (ihb hb2 hsb)

theorem odd_friend_square (m : ℕ) (ho : Odd m) (h : sigma 1 m * 10 = 18 * m) : IsSquare m := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp ho
  exact square_of_odd_sigma m hm2 (by omega)

end OMA.Solitary2

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H2 := by
  intro m ho h
  exact OMA.Solitary2.odd_friend_square m ho h
