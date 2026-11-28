import OMAReductions.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1

-- Step AgrawalConjecture.agrawal_conjecture.variants.popovych.R1.H1: hypothesis H1 of reduction AgrawalConjecture.agrawal_conjecture.variants.popovych.R1
-- Credit: @marcusbuffett
--
-- Evaluation at X = 1 kills X^r - 1, so (X + 2)^n = X^n + 2 modulo (n, X^r - 1) gives
-- 3^n = 3 in ZMod n. If p^2 divides n, reduce to ZMod p^2. For p = 3, 3^n = 0 there (n is at
-- least 9), a contradiction. Otherwise 3 is a unit u with u^(n - 1) = 1 and, by Euler,
-- u^(p (p - 1)) = 1; p does not divide n - 1, so the order of u is prime to p and divides
-- p - 1. Written for this step.

open Polynomial

namespace OMA.S_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1_H1

/-- Evaluating at `X = 1`: the second Popovych congruence gives `3 ^ n = 3` in `ZMod n`. -/
theorem three_pow_eq (n r : ℕ)
    (hc : Ideal.Quotient.mk (Ideal.span ({(X : (ZMod n)[X]) ^ r - 1} : Set (ZMod n)[X]))
        ((X + 2) ^ n) =
      Ideal.Quotient.mk (Ideal.span ({(X : (ZMod n)[X]) ^ r - 1} : Set (ZMod n)[X]))
        (X ^ n + 2)) :
    (3 : ZMod n) ^ n = 3 := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨g, hg⟩ := hc
  have := congrArg (eval 1) hg
  simp only [eval_sub, eval_pow, eval_add, eval_X, eval_ofNat, eval_one, eval_mul, one_pow, sub_self,
    zero_mul] at this
  have h3 : (1 : ZMod n) + 2 = 3 := by norm_num
  rw [h3, sub_eq_zero] at this
  exact this

/-- A square prime factor `p ^ 2` of `n` with `3 ^ n ≡ 3 (mod n)` forces `p ≠ 3` and
`3 ^ (p - 1) ≡ 1 (mod p ^ 2)`: `p` is a base-3 Wieferich prime. -/
theorem wieferich (n p : ℕ) (hn : 1 < n) (hp : p.Prime) (hpn : p ^ 2 ∣ n)
    (h : (3 : ZMod n) ^ n = 3) : p ≠ 3 ∧ (3 : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
  have h' : (3 : ZMod (p ^ 2)) ^ n = 3 := by
    have := congrArg (ZMod.castHom hpn (ZMod (p ^ 2))) h
    rwa [map_pow, map_ofNat] at this
  have hp2 := hp.two_le
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h9 : (3 : ZMod (3 ^ 2)) ^ n = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by
        have := Nat.le_of_dvd (by omega) hpn; omega⟩
      rw [hk, pow_add]
      have : (3 : ZMod (3 ^ 2)) ^ 2 = 0 := by decide
      rw [this, mul_zero]
    rw [h9] at h'
    exact absurd h' (by decide)
  · have hcop : Nat.Coprime 3 (p ^ 2) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_primes Nat.prime_three hp]
      rintro rfl
      -- p = 3 case: same computation as above
      have h9 : (3 : ZMod (3 ^ 2)) ^ n = 0 := by
        obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by
          have := Nat.le_of_dvd (by omega) hpn; omega⟩
        rw [hk, pow_add]
        have : (3 : ZMod (3 ^ 2)) ^ 2 = 0 := by decide
        rw [this, mul_zero]
      rw [h9] at h'
      exact absurd h' (by decide)
    set u := ZMod.unitOfCoprime 3 hcop with hu
    have hu3 : (u : ZMod (p ^ 2)) = 3 := by simp [hu]
    -- `u ^ (n - 1) = 1`
    have h1 : u ^ (n - 1) = 1 := by
      apply Units.ext
      have hn1 : n = (n - 1) + 1 := by omega
      have : (3 : ZMod (p ^ 2)) ^ (n - 1) * 3 = 1 * 3 := by
        rw [← pow_succ, ← hn1, h', one_mul]
      have h3u : IsUnit (3 : ZMod (p ^ 2)) := hu3 ▸ u.isUnit
      have := h3u.mul_right_cancel this
      simpa [hu3] using this
    -- `u ^ (p (p - 1)) = 1` by Euler
    have h2 : u ^ (p * (p - 1)) = 1 := by
      have ht : Nat.totient (p ^ 2) = p * (p - 1) := by
        rw [Nat.totient_prime_pow hp (by norm_num)]; simp
      have := ZMod.pow_totient u
      rwa [ht] at this
    have ho1 : orderOf u ∣ n - 1 := orderOf_dvd_of_pow_eq_one h1
    have ho2 : orderOf u ∣ p * (p - 1) := orderOf_dvd_of_pow_eq_one h2
    have hpn1 : ¬ p ∣ n - 1 := by
      intro hd
      have hpn' : p ∣ n := (dvd_pow_self p (by norm_num)).trans hpn
      have h1' := Nat.dvd_sub hpn' hd
      rw [show n - (n - 1) = 1 by omega] at h1'
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1')
    have hcop2 : Nat.Coprime (orderOf u) p := by
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      exact fun hd => hpn1 (hd.trans ho1)
    have ho3 : orderOf u ∣ p - 1 := hcop2.dvd_of_dvd_mul_left ho2
    have h4 : u ^ (p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp ho3
    have := congrArg Units.val h4
    simpa [hu3] using this

end OMA.S_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1_H1

open OMA.S_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1_H1 in
theorem OMA.solution : OMA.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1.H1 := by
  intro n r hn
  dsimp only
  intro hc p hp hpn
  exact wieferich n p hn hp hpn (three_pow_eq n r hc)
