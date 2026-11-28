import OMAReductions.R_OeisA2326_conjecture2_R2
import Mathlib

-- Step OeisA2326.conjecture2.R2.H1: hypothesis H1 of reduction OeisA2326.conjecture2.R2
-- Credit: @sebastianbachmaier
-- H1 := ∀ k : ℕ, 2 ≤ k → k ≤ 1000 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ 1000 →     OeisA2326.a ((p ^ (k + 1) - 1) / 2) = p * OeisA2326.a ((p ^ k - 1) / 2)

/-!
# The tested square of OEIS A002326 conjecture2

For an odd prime p at most 1000 and k at least one, the order of 2 modulo p^(k+1) is p times
the order of 2 modulo p^k.

* A kernel computation shows that no p with 2 <= p <= 1000 has p^2 dividing 2^(p-1) - 1
  (there is no Wieferich prime in this range).
* For such p, lifting the exponent (Mathlib `padicValNat.pow_sub_pow`) gives the order identity
  for every k at least one; this is the argument of the merged step OeisA2326.conjecture2.R1.H1,
  restated here as `lift`.
* For odd p, `a ((p ^ j - 1) / 2)` is the order of 2 modulo p^j.

The bound on k is not used.
-/

namespace OMA.A2326R2H1

/-- In `ZMod N`, a power of two is one exactly when `N` divides that power of two minus one. -/
theorem zmod_two_pow_eq_one_iff (N n : ℕ) : (2 : ZMod N) ^ n = 1 ↔ N ∣ 2 ^ n - 1 := by
  have h : ((2 ^ n : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) ↔ N ∣ 2 ^ n - 1 := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' Nat.one_le_two_pow]
  rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
  exact h

/-- The order of two in `ZMod N` divides `n` exactly when `N` divides `2 ^ n - 1`. -/
theorem orderOf_two_zmod_dvd_iff (N n : ℕ) : orderOf (2 : ZMod N) ∣ n ↔ N ∣ 2 ^ n - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, zmod_two_pow_eq_one_iff]

/-- Lifting the exponent for `2 ^ (a * m) - 1` at an odd prime `p` dividing `2 ^ a - 1`
(a specialisation of Mathlib's `padicValNat.pow_sub_pow`). -/
theorem padicValNat_two_pow_mul_sub_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) {a m : ℕ}
    (ha : a ≠ 0) (hm : m ≠ 0) (hpa : p ∣ 2 ^ a - 1) :
    padicValNat p (2 ^ (a * m) - 1) = padicValNat p (2 ^ a - 1) + padicValNat p m := by
  have hp : p.Prime := Fact.out
  have h2 : ¬ p ∣ 2 ^ a := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow h)
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have h := padicValNat.pow_sub_pow (x := 2 ^ a) (y := 1) hodd (Nat.one_lt_two_pow ha) hpa h2 hm
  rwa [one_pow, ← pow_mul] at h

/-- Order lifting for an odd prime that is not a Wieferich prime. -/
theorem lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hW : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    (k : ℕ) (hk : 1 ≤ k) :
    orderOf (2 : ZMod (p ^ (k + 1))) = p * orderOf (2 : ZMod (p ^ k)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have hp1 : p - 1 ≠ 0 := by omega
  have hne : ∀ n : ℕ, n ≠ 0 → 2 ^ n - 1 ≠ 0 := fun n hn =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow hn)
  -- Fermat's little theorem for the base two
  have hferm : p ∣ 2 ^ (p - 1) - 1 := by
    rw [← zmod_two_pow_eq_one_iff]
    apply ZMod.pow_card_sub_one_eq_one
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'
    omega
  -- p is not a Wieferich prime: the exponent of p in 2^(p-1) - 1 is exactly one
  have hv1 : padicValNat p (2 ^ (p - 1) - 1) = 1 := by
    have h1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
      (padicValNat_dvd_iff_le (hne _ hp1)).mp (by rwa [pow_one])
    have h2 : ¬ 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := fun h =>
      hW ((padicValNat_dvd_iff_le (hne _ hp1)).mpr h)
    omega
  -- N = (p - 1) p^(k-1) has exponent exactly k
  have hpk1 : p ^ (k - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hN0 : (p - 1) * p ^ (k - 1) ≠ 0 := Nat.mul_ne_zero hp1 hpk1
  have hvN : padicValNat p (2 ^ ((p - 1) * p ^ (k - 1)) - 1) = k := by
    rw [padicValNat_two_pow_mul_sub_one hodd hp1 hpk1 hferm, hv1, padicValNat.prime_pow]
    omega
  -- the two orders
  obtain ⟨d, hd⟩ : ∃ d, orderOf (2 : ZMod (p ^ k)) = d := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, orderOf (2 : ZMod (p ^ (k + 1))) = D := ⟨_, rfl⟩
  rw [hd, hD]
  have hdi : ∀ n, d ∣ n ↔ p ^ k ∣ 2 ^ n - 1 := by
    intro n
    rw [← hd]
    exact orderOf_two_zmod_dvd_iff _ _
  have hDi : ∀ n, D ∣ n ↔ p ^ (k + 1) ∣ 2 ^ n - 1 := by
    intro n
    rw [← hD]
    exact orderOf_two_zmod_dvd_iff _ _
  -- d divides N, so d is nonzero
  have hdN : d ∣ (p - 1) * p ^ (k - 1) := by
    rw [hdi, padicValNat_dvd_iff_le (hne _ hN0), hvN]
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hN0 (Nat.eq_zero_of_zero_dvd hdN)
  have hpkd : p ^ k ∣ 2 ^ d - 1 := (hdi d).mp dvd_rfl
  have hpd : p ∣ 2 ^ d - 1 := (dvd_pow_self p (by omega : k ≠ 0)).trans hpkd
  -- p^(k+1) does not divide 2^d - 1, since 2^d - 1 divides 2^N - 1
  have hnot : ¬ p ^ (k + 1) ∣ 2 ^ d - 1 := by
    intro h
    obtain ⟨m, hm⟩ := hdN
    have hdiv : 2 ^ d - 1 ∣ 2 ^ ((p - 1) * p ^ (k - 1)) - 1 := by
      rw [hm, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 m
    have := (padicValNat_dvd_iff_le (hne _ hN0)).mp (h.trans hdiv)
    omega
  have hvd : padicValNat p (2 ^ d - 1) = k := by
    have h1 := (padicValNat_dvd_iff_le (hne _ hd0)).mp hpkd
    have h2 : ¬ k + 1 ≤ padicValNat p (2 ^ d - 1) := fun h =>
      hnot ((padicValNat_dvd_iff_le (hne _ hd0)).mpr h)
    omega
  -- D divides d p
  have hDdp : D ∣ d * p := by
    rw [hDi, padicValNat_dvd_iff_le (hne _ (Nat.mul_ne_zero hd0 hp.ne_zero)),
      padicValNat_two_pow_mul_sub_one hodd hd0 hp.ne_zero hpd, hvd, padicValNat_self]
  -- d divides D
  have hdD : d ∣ D := by
    rw [hdi]
    exact (pow_dvd_pow p (Nat.le_succ k)).trans ((hDi D).mp dvd_rfl)
  obtain ⟨m, hm⟩ := hdD
  have hmp : m ∣ p := by
    rw [hm] at hDdp
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hd0) hDdp
  rcases hp.eq_one_or_self_of_dvd m hmp with h1 | h1
  · exfalso
    apply hnot
    have h := (hDi D).mp dvd_rfl
    rwa [hm, h1, mul_one] at h
  · rw [hm, h1, mul_comm]

/-- For `p = b, ..., b + f - 1`: `2^(p-1)` is not `1` modulo `p^2`. -/
def wf : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, b => (2 ^ (b + f - 1) % (b + f) ^ 2 != 1) && wf f b

lemma wf_spec : ∀ (f b : ℕ), wf f b = true → ∀ p, b ≤ p → p < b + f → 2 ^ (p - 1) % p ^ 2 ≠ 1 := by
  intro f
  induction f with
  | zero => intro b _ p h1 h2; omega
  | succ f ih =>
    intro b h p h1 h2
    rw [wf, Bool.and_eq_true, bne_iff_ne] at h
    by_cases hp : p = b + f
    · subst hp; exact h.1
    · exact ih b h.2 p h1 (by omega)

lemma mod_eq_one {p : ℕ} (hp : 2 ≤ p) (h : p ^ 2 ∣ 2 ^ (p - 1) - 1) : 2 ^ (p - 1) % p ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (p - 1) = p ^ 2 * k + 1 := by omega
  have h3 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h3]

set_option maxRecDepth 100000 in
theorem c0 : wf 999 2 = true := by decide +kernel

/-- No `p` with `2 ≤ p ≤ 1000` has `p ^ 2` dividing `2 ^ (p - 1) - 1`. -/
lemma not_wieferich (p : ℕ) (h2 : 2 ≤ p) (hN : p ≤ 1000) : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1 :=
  fun h => wf_spec _ _ c0 p h2 (by omega) (mod_eq_one h2 h)

/-- For odd `p`, the term `a ((p ^ j - 1) / 2)` is the order of `2` modulo `p ^ j`. -/
lemma a_eq_orderOf {p : ℕ} (hodd : Odd p) (j : ℕ) :
    OeisA2326.a ((p ^ j - 1) / 2) = orderOf (2 : ZMod (p ^ j)) := by
  have h : 2 * ((p ^ j - 1) / 2) + 1 = p ^ j := by
    obtain ⟨t, ht⟩ := hodd.pow (n := j)
    omega
  unfold OeisA2326.a
  rw [h]

end OMA.A2326R2H1

theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R2.H1 := by
  intro k hk _ p hp hp2 hp1000
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [OMA.A2326R2H1.a_eq_orderOf hodd, OMA.A2326R2H1.a_eq_orderOf hodd]
  exact OMA.A2326R2H1.lift p hp hp2 (OMA.A2326R2H1.not_wieferich p hp.two_le hp1000) k (by omega)
