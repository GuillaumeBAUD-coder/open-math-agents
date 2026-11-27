import FormalConjectures.OEIS.«182126»

-- Reduction OeisA182126.conjecture3.R1 of Product of two consecutive primes modulo the next prime — conjecture3
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! Reduction: for large n the residue equals a product of two prime gaps, so it is composite.
Write p_k for Nat.nth Nat.Prime k (0-indexed, so p_0 = 2). Since p_k = r - b and p_(k+1) = r - c
modulo r = p_(k+2), the residue is b * c whenever b * c < r. For k at least 1 both gaps are
at least 2, so b * c is not prime. H1 is the open prime-gap inequality (checked numerically
far beyond the threshold); H2 is the finite check of the first 61 terms. -/

namespace OMA.R_OeisA182126_conjecture3_R1

/-- For every 0-indexed k > 60 (that is, upstream index n = k + 1 > 61), the product of the two
gaps ending at the prime p_(k+2) is smaller than p_(k+2). -/
def H1 : Prop :=
  ∀ k : ℕ, 60 < k →
    (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime k) *
      (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) < Nat.nth Nat.Prime (k + 2)

/-- The finite part: among a(1), ..., a(61) the only primes are 2, 7, 11, 13, 29. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime →
    OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ)

theorem main : H1 → H2 → type_of% @OeisA182126.conjecture3 := by
  intro h1 h2 n hn
  constructor
  · intro hp
    by_cases hle : n ≤ 61
    · exact h2 n hn hle hp
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm : 60 < m := by omega
      have ha : OeisA182126.a (m + 1) =
          (Nat.nth Nat.Prime m * Nat.nth Nat.Prime (m + 1)) % Nat.nth Nat.Prime (m + 2) := by
        unfold OeisA182126.a OeisA182126.prime
        simp
      rw [ha] at hp
      have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
      have hpq : Nat.nth Nat.Prime m < Nat.nth Nat.Prime (m + 1) := hmono (by omega)
      have hqr : Nat.nth Nat.Prime (m + 1) < Nat.nth Nat.Prime (m + 2) := hmono (by omega)
      have hp2 : 2 ≤ Nat.nth Nat.Prime m := (Nat.prime_nth_prime m).two_le
      have hqo : Odd (Nat.nth Nat.Prime (m + 1)) :=
        (Nat.prime_nth_prime (m + 1)).odd_of_ne_two (by omega)
      have hro : Odd (Nat.nth Nat.Prime (m + 2)) :=
        (Nat.prime_nth_prime (m + 2)).odd_of_ne_two (by omega)
      have hlt := h1 m hm
      generalize Nat.nth Nat.Prime m = p at *
      generalize Nat.nth Nat.Prime (m + 1) = q at *
      generalize Nat.nth Nat.Prime (m + 2) = r at *
      obtain ⟨j, hj⟩ := hqo
      obtain ⟨i, hi⟩ := hro
      have hpr : p ≤ r := by omega
      have hqr' : q ≤ r := by omega
      have hid : p * q + r * ((r - p) + (r - q)) = (r - p) * (r - q) + r * r := by
        zify [hpr, hqr']
        ring
      have hmod : (p * q) % r = (r - p) * (r - q) := by
        rw [← Nat.add_mul_mod_self_left (p * q) r ((r - p) + (r - q)), hid,
          Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hlt
      rw [hmod] at hp
      exact Nat.not_prime_mul (by omega) (by omega) hp
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> rw [h] <;> norm_num

end OMA.R_OeisA182126_conjecture3_R1
