import FormalConjectures.ErdosProblems.«694»

/-!
# Reduction of Erdős 694 (inf_unique)

If `φ(x) = n` has the unique solution `x = m`, then for a prime `p > n + 1` the solutions of
`φ(x) = n (p - 1)` divisible by `p` are exactly `x = p m`. So it suffices to find arbitrarily large
primes `p` for which `n (p - 1)` has no totient preimage coprime to `p`.
- `H1` (sieve core, Erdős 1935 via Brun's sieve): arbitrarily large primes `p = 2 t + 1` with
  `t > 1`, every prime factor of `t` larger than `2 n + 1`, and `d u + 1` composite for all
  `d ∣ 2 n`, `u ∣ t`, `1 < u`, `d u ≠ 2 t`.
- `H2` (elementary bridge): for such `p`, no `x` coprime to `p` has `φ x = n (p - 1)`.
  `H2` is proved below as `bridge_holds`; the only genuine input is `H1`.
-/

namespace OMA.R_Erdos694_erdos_694_variants_inf_unique_R1

def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ N : ℕ, ∃ p t : ℕ, p.Prime ∧ N < p ∧ p = 2 * t + 1 ∧ 1 < t ∧
    (∀ q : ℕ, q.Prime → q ∣ t → 2 * n + 1 < q) ∧
    ∀ d u : ℕ, d ∣ 2 * n → u ∣ t → 1 < u → d * u ≠ 2 * t → ¬ (d * u + 1).Prime

def H2 : Prop :=
  ∀ n p t : ℕ, 0 < n → p.Prime → p = 2 * t + 1 → 1 < t →
    (∀ q : ℕ, q.Prime → q ∣ t → 2 * n + 1 < q) →
    (∀ d u : ℕ, d ∣ 2 * n → u ∣ t → 1 < u → d * u ≠ 2 * t → ¬ (d * u + 1).Prime) →
    ∀ x : ℕ, ¬ p ∣ x → Nat.totient x ≠ n * (p - 1)

lemma prime_dvd_totient {x q : ℕ} (hx : x ≠ 0) (hq : q.Prime) (h : q ∣ Nat.totient x) :
    ∃ r, r.Prime ∧ r ∣ x ∧ (q = r ∨ q ∣ r - 1) := by
  rw [Nat.totient_eq_prod_factorization hx] at h
  obtain ⟨r, hr, hd⟩ := (Prime.dvd_finsuppProd_iff hq.prime).1 h
  rw [Nat.support_factorization] at hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  refine ⟨r, hrp, Nat.dvd_of_mem_primeFactors hr, ?_⟩
  rcases (Nat.Prime.dvd_mul hq).1 hd with h1 | h1
  · left
    exact (Nat.prime_dvd_prime_iff_eq hq hrp).1 (hq.dvd_of_dvd_pow h1)
  · right; exact h1

lemma bridge_holds : H2 := by
  intro n p t hn hp hpt ht hq hcomp x hpx hφ
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hpx
  have hp1 : p - 1 = 2 * t := by omega
  rw [hp1] at hφ
  obtain ⟨q, hqp, hqt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  have hqbig := hq q hqp hqt
  have hqφ : q ∣ Nat.totient x := by
    rw [hφ]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hqt 2) n
  obtain ⟨r, hr, hrx, hqr⟩ := prime_dvd_totient hx hqp hqφ
  have hcop : Nat.Coprime (2 * n) t := by
    apply Nat.coprime_of_dvd
    intro k hk h1 h2
    have := hq k hk h2
    have := Nat.le_of_dvd (by omega) h1
    omega
  have he : r - 1 ∣ 2 * n * t := by
    have := Nat.totient_dvd_of_dvd hrx
    rw [Nat.totient_prime hr, hφ] at this
    rw [show 2 * n * t = n * (2 * t) by ring]; exact this
  have hr2 := hr.two_le
  have hsplit : r - 1 = Nat.gcd (r - 1) (2 * n) * Nat.gcd (r - 1) t := by
    rw [← Nat.Coprime.gcd_mul (r - 1) hcop]
    exact (Nat.gcd_eq_left he).symm
  have hu : Nat.gcd (r - 1) t = 1 := by
    by_contra hne
    have hpos : 0 < Nat.gcd (r - 1) t := Nat.gcd_pos_of_pos_right _ (by omega)
    have h1 : 1 < Nat.gcd (r - 1) t := by omega
    have hne2 : Nat.gcd (r - 1) (2 * n) * Nat.gcd (r - 1) t ≠ 2 * t := by
      intro heq
      rw [← hsplit] at heq
      have : r = p := by omega
      exact hpx (this ▸ hrx)
    apply hcomp _ _ (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _) h1 hne2
    rw [← hsplit, show r - 1 + 1 = r by omega]
    exact hr
  rw [hu, mul_one] at hsplit
  have hle : r - 1 ≤ 2 * n := by
    rw [hsplit]; exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  rcases hqr with h | h
  · omega
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem main : H1 → H2 → type_of% @Erdos694.erdos_694.variants.inf_unique := by
  intro h1 h2 h
  obtain ⟨n, hn, m, hm, huniq⟩ := h
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, t, hp, hpN, hpt, ht, hq, hcomp⟩ := h1 n hn (a + n + 1)
  have hpm : ¬ p ∣ m := by
    intro hdvd
    have := Nat.totient_dvd_of_dvd hdvd
    rw [Nat.totient_prime hp, hm] at this
    have := Nat.le_of_dvd hn this
    omega
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  refine ⟨n * (p - 1), ⟨p * m, ?_, ?_⟩, ?_⟩
  · show Nat.totient (p * m) = n * (p - 1)
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, hm, mul_comm]
  · intro x hx
    have hx' : Nat.totient x = n * (p - 1) := hx
    by_cases hpx : p ∣ x
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx'
        rcases hx' with h | h <;> omega
      obtain ⟨k, y, hy, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx0 p hp.one_lt.ne'
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hpx
        exact hy hpx
      have hcopy : Nat.Coprime (p ^ k) y :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hy)
      rw [Nat.totient_mul hcopy, Nat.totient_prime_pow hp (by omega)] at hx'
      have hp1 : 0 < p - 1 := by have := hp.two_le; omega
      have hx'' : p ^ (k - 1) * Nat.totient y = n := by
        have : p ^ (k - 1) * Nat.totient y * (p - 1) = n * (p - 1) := by
          rw [← hx']; ring
        exact Nat.eq_of_mul_eq_mul_right hp1 this
      have hk1 : k = 1 := by
        by_contra hk1
        have hd : p ∣ n := by
          rw [← hx'']
          apply Dvd.dvd.mul_right
          exact dvd_pow_self p (by omega)
        have := Nat.le_of_dvd hn hd
        omega
      subst hk1
      simp at hx''
      rw [huniq y hx'']
      ring
    · exact absurd hx' (h2 n p t hn hp hpt ht hq hcomp x hpx)
  · have : p - 1 ≤ n * (p - 1) := Nat.le_mul_of_pos_left _ hn
    omega

end OMA.R_Erdos694_erdos_694_variants_inf_unique_R1
