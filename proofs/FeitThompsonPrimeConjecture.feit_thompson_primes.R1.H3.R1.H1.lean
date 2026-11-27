import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1
import Mathlib

/-! Class S: if r is a prime factor of N and r divides M, then p ^ q = 1 in ZMod r. The order of p is 1 or q.
Order 1 gives r = q, but N = 1 mod q. Order q gives q | r - 1. -/

namespace OMA.FeitThompsonClassS

/-- Class S: if N has a prime factor r with q not dividing r - 1, then N does not divide M. -/
theorem classS : ∀ (p q : ℕ), p.Prime → q.Prime → p < q →
    ∀ r : ℕ, r.Prime → r ∣ (q ^ p - 1) / (q - 1) → ¬ q ∣ r - 1 →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1) := by
  intro p q hp hq hpq r hr hrN hqr hdvd
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  rw [← Nat.geomSum_eq hq.two_le] at hrN
  have hrM := hrN.trans hdvd
  have := Fact.mk hr
  have hM0 : ∑ i ∈ Finset.range q, (p : ZMod r) ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hrM
    push_cast at this; exact this
  have hx : (p : ZMod r) ^ q = 1 := by
    have h := geom_sum_mul (p : ZMod r) q
    rw [hM0, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  rcases hq.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hx) with h1 | hqo
  · have hx1 : (p : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
    rw [hx1] at hM0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hM0
    have hrq : r ∣ q := (ZMod.natCast_eq_zero_iff _ _).mp hM0
    have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
    subst hrq'
    have hN1 : ((∑ k ∈ Finset.range p, r ^ k : ℕ) : ZMod r) = 1 := by
      obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      push_cast
      rw [Finset.sum_range_succ']
      simp
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hrN] at hN1
    exact zero_ne_one hN1
  · have hx0 : (p : ZMod r) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hq.ne_zero] at hx
      exact zero_ne_one hx
    exact hqr (hqo ▸ ZMod.orderOf_dvd_card_sub_one hx0)

end OMA.FeitThompsonClassS

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1 := by
  intro p q hp hq hpq _ _ hs
  obtain ⟨r, hr, hrN, hqr⟩ := hs
  exact OMA.FeitThompsonClassS.classS p q hp hq hpq r hr hrN hqr
