import FormalConjectures.OEIS.«358684»

/-! Single-factor Pocklington certificates (via q-th roots of unity d + 1 mod p) for F_7.
Each prime in the chain has a single prime factor q ∣ p - 1 with q^2 > p.
Original proof credited to @RhizomeSlopGenerator. -/

namespace OMA

def pm (a e p : ℕ) : ℕ :=
  if e = 0 then 1 % p else Nat.pow (pm a (e / 16) p) 16 * Nat.pow a (e % 16) % p
termination_by e
decreasing_by omega

lemma pm_eq (a e p : ℕ) : pm a e p = a ^ e % p := by
  fun_induction pm a e p with
  | case1 => simp
  | case2 e _ ih =>
    simp [ih, ← ZMod.natCast_eq_natCast_iff', ← pow_mul, ← pow_add, Nat.div_add_mod']

theorem pock (p q d : ℕ) (hq : q.Prime)
    (h : 1 < p ∧ p < q * q ∧ pm (d + 1) q p = 1 ∧ Nat.gcd d p = 1 := by decide +kernel) :
    p.Prime := by
  obtain ⟨hp, hqq, hpm, hg⟩ := h
  by_contra hnp
  set r := p.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrp : r ∣ p := Nat.minFac_dvd p
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  have hm : ((d + 1 : ℕ) : ZMod r) ^ q = 1 := by
    rw [← Nat.cast_pow, ← Nat.div_add_mod ((d + 1) ^ q) p]
    simp [(ZMod.natCast_eq_zero_iff p r).mpr hrp, ← pm_eq, hpm]
  have hne : ((d + 1 : ℕ) : ZMod r) ≠ 1 := fun hb =>
    hr.not_dvd_one (hg ▸ Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff d r).mp (by simpa using hb)) hrp)
  have ho := orderOf_eq_prime hm hne ▸
    ZMod.orderOf_dvd_card_sub_one fun h0 => by rw [h0, zero_pow hq.ne_zero] at hm; exact zero_ne_one hm
  have hr2 := hr.two_le
  have hqr : q < r := by have := Nat.le_of_dvd (by omega) ho; omega
  have hsq : r * r ≤ p := by simpa only [sq] using Nat.minFac_sq_le_self (by omega) hnp
  have := Nat.mul_lt_mul'' hqr hqr
  omega

end OMA

open OMA in
theorem OMA.solution : type_of% @OeisA358684.a_7 := by
  let n := Nat.fermatNumber 7
  have hp1 : Nat.Prime 59649589127497217 :=
    pock _ 116503103764643 55 (pock _ 18533742247 2235 (pock _ 1896229 478 (by norm_num)))
  have hp2 : Nat.Prime 5704689200685129054721 :=
    pock _ 733803839347 2500924644267550558591 (pock _ 55515497 1146 (by norm_num))
  have hprod : n = 59649589127497217 * 5704689200685129054721 := by decide
  have hmf : n.minFac = 59649589127497217 := by
    have hmp : n.minFac.Prime := Nat.minFac_prime (by rw [hprod]; decide)
    have hle : n.minFac ≤ 59649589127497217 :=
      Nat.minFac_le_of_dvd (by decide) (by rw [hprod]; exact dvd_mul_right _ _)
    have hd : n.minFac ∣ 59649589127497217 * 5704689200685129054721 := by
      rw [← hprod]; exact Nat.minFac_dvd _
    rcases hmp.dvd_mul.mp hd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hmp hp1).mp h
    · have := (Nat.prime_dvd_prime_iff_eq hmp hp2).mp h; omega
  change 2 ^ 7 - Nat.log2 n.minFac = 73
  rw [hmf]
  decide
