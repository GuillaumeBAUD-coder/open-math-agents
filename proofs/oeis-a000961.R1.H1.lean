import OMAReductions.R_oeis_a000961_R1

-- Step oeis-a000961.R1.H1: hypothesis H1 of reduction oeis-a000961.R1
-- Credit: @GarnetCullet
-- Each k coprime to p contributes 1 modulo p^(e+1) (Euler), each multiple of p contributes 0
-- (the exponent phi(m) is at least e+1). Counting the non-multiples of p below p*s gives
-- (p-1)*s, so both sides carry the factor p^e*(p-1), which cancels.

namespace OMA.P_oeis_a000961_R1_H1

/-- Indicator of not being divisible by `p`. -/
def g (p k : ℕ) : ℕ := if p ∣ k then 0 else 1

theorem sum_g_block (p : ℕ) (hp : p.Prime) (a : ℕ) :
    (∑ j ∈ Finset.range p, g p (p * a + j)) = p - 1 := by
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have hdiv : ∀ j, p ∣ p * a + j ↔ p ∣ j := fun j =>
    Nat.dvd_add_right (dvd_mul_right p a)
  rw [hr, Finset.sum_range_succ']
  have h0 : g (r + 1) ((r + 1) * a + 0) = 0 := by simp [g]
  rw [h0, add_zero]
  have : ∀ j ∈ Finset.range r, g (r + 1) ((r + 1) * a + (j + 1)) = 1 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hnd : ¬ (r + 1) ∣ j + 1 := fun h =>
      absurd (Nat.le_of_dvd (by omega) h) (by omega)
    have := (hdiv (j + 1))
    rw [hr] at this
    simp [g, this, hnd]
  rw [Finset.sum_congr rfl this]
  simp

theorem sum_g (p : ℕ) (hp : p.Prime) (s : ℕ) :
    (∑ k ∈ Finset.range (p * s), g p k) = (p - 1) * s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, sum_g_block p hp s]
    ring

theorem pow_mod (p e t k : ℕ) (hp : p.Prime) (ht : 0 < t) (hc : p.Coprime t) :
    ((k ^ (p ^ (e + 1) * t).totient : ℕ) : ZMod (p ^ (e + 1))) = (g p k : ZMod (p ^ (e + 1))) := by
  have hq : (p ^ (e + 1)).Coprime t := Nat.Coprime.pow_left _ hc
  rw [Nat.totient_mul hq]
  by_cases hk : p ∣ k
  · simp only [g, hk, if_true, Nat.cast_zero]
    rw [ZMod.natCast_eq_zero_iff]
    have hφt : 0 < t.totient := Nat.totient_pos.mpr ht
    have hle : e + 1 ≤ (p ^ (e + 1)).totient * t.totient := by
      rw [Nat.totient_prime_pow_succ hp]
      have h1 : e < 2 ^ e := Nat.lt_two_pow_self
      have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
      have h3 : 1 ≤ p - 1 := by have := hp.two_le; omega
      calc e + 1 ≤ p ^ e := by omega
        _ = p ^ e * 1 * 1 := by ring
        _ ≤ p ^ e * (p - 1) * t.totient := by gcongr; omega
    exact (pow_dvd_pow_of_dvd hk (e + 1)).trans (pow_dvd_pow k hle)
  · simp only [g, hk, if_false, Nat.cast_one]
    have hkq : k.Coprime (p ^ (e + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)))
    have := (Nat.ModEq.pow_totient hkq).pow t.totient
    rw [← pow_mul, one_pow] at this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr this |>.trans (by simp)

end OMA.P_oeis_a000961_R1_H1

open OMA.P_oeis_a000961_R1_H1 in
theorem OMA.solution : OMA.R_oeis_a000961_R1.H1 := by
  intro p e t hp ht hc
  simp only
  have hq : (p ^ (e + 1)).Coprime t := Nat.Coprime.pow_left _ hc
  -- The power sum is congruent to the number of non-multiples of p.
  have hsum : (∑ k ∈ Finset.range (p ^ (e + 1) * t), k ^ (p ^ (e + 1) * t).totient)
      ≡ p ^ e * ((p - 1) * t) [MOD p ^ (e + 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
    rw [Finset.sum_congr rfl (fun k _ => pow_mod p e t k hp ht hc), ← Nat.cast_sum]
    congr 1
    rw [show p ^ (e + 1) * t = p * (p ^ e * t) by ring, sum_g p hp]
    ring
  have htot : (p ^ (e + 1) * t).totient = p ^ e * ((p - 1) * t.totient) := by
    rw [Nat.totient_mul hq, Nat.totient_prime_pow_succ hp]; ring
  have hp0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hcop : Nat.gcd p (p - 1) = 1 := by
    have : ¬ p ∣ p - 1 := fun h =>
      absurd (Nat.le_of_dvd (by have := hp.two_le; omega) h) (by have := hp.two_le; omega)
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  rw [htot] at hsum ⊢
  constructor
  · intro h
    have h2 := hsum.symm.trans h
    rw [pow_succ] at h2
    have h3 := Nat.ModEq.mul_left_cancel' hp0 h2
    exact Nat.ModEq.cancel_left_of_coprime hcop h3
  · intro h
    refine hsum.trans ?_
    rw [pow_succ]
    exact Nat.ModEq.mul_left' _ (Nat.ModEq.mul_left _ h)
