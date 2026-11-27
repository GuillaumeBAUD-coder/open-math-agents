import OMAReductions.R_OeisA2326_conjecture2_R1
import Mathlib

-- Step OeisA2326.conjecture2.R1.H1: hypothesis H1 of reduction OeisA2326.conjecture2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Order lifting for non-Wieferich primes: if `p` is an odd prime with `p ^ 2 ∤ 2 ^ (p - 1) - 1`,
then the order of `2` modulo `p ^ (k + 1)` is `p` times its order modulo `p ^ k` for every `k ≥ 1`.

Let `v` be the exponent of `p` in `2 ^ (p - 1) - 1`; Fermat gives `v ≥ 1`. For `k ≥ v`, lifting the
exponent shows that the exponent `(p - 1) * p ^ (k - v)` has valuation exactly `k`, so the order
`d` modulo `p ^ k` divides it and the valuation of `2 ^ d - 1` is exactly `k`. A second use of
lifting the exponent then shows that `p ^ (k + 1) ∣ 2 ^ (d * m) - 1` exactly when `p ∣ m`, so the
order modulo `p ^ (k + 1)` is `d * p`. The non-Wieferich hypothesis is `v = 1`.
-/

namespace OeisA2326Step

/-- `2 ^ n = 1` in `ZMod N` exactly when `N` divides `2 ^ n - 1`. -/
lemma two_pow_eq_one_iff (N n : ℕ) : (2 : ZMod N) ^ n = 1 ↔ N ∣ 2 ^ n - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  exact sub_eq_zero.symm

/-- The order of `2` modulo `N` divides `n` exactly when `N` divides `2 ^ n - 1`. -/
lemma orderOf_two_dvd_iff (N n : ℕ) : orderOf (2 : ZMod N) ∣ n ↔ N ∣ 2 ^ n - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, two_pow_eq_one_iff]

lemma two_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) : 2 ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_two_pow hn
  omega

lemma not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) (n : ℕ) : ¬ p ∣ 2 ^ n := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst h3
  exact absurd hodd (by decide)

/-- Lifting the exponent for `2 ^ n - 1` at an odd prime `p` dividing it. -/
lemma val_two_pow_mul {p : ℕ} [Fact p.Prime] (hodd : Odd p) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hdvd : p ∣ 2 ^ n - 1) :
    padicValNat p (2 ^ (n * m) - 1) = padicValNat p (2 ^ n - 1) + padicValNat p m := by
  have h := padicValNat.pow_sub_pow hodd (Nat.one_lt_two_pow hn) hdvd
    (not_dvd_two_pow Fact.out hodd n) hm
  rwa [one_pow, ← pow_mul] at h

/-- Fermat's little theorem for the base `2`. -/
lemma dvd_two_pow_pred_sub_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) : p ∣ 2 ^ (p - 1) - 1 := by
  rw [← two_pow_eq_one_iff]
  apply ZMod.pow_card_sub_one_eq_one
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact not_dvd_two_pow Fact.out hodd 1 (by simpa using h2)

/-- Order lifting in abstract form: if `d` and `D` are the orders of `2` modulo `p ^ k` and
`p ^ (k + 1)`, and `k` is at least the exponent of `p` in `2 ^ (p - 1) - 1`, then `D = p * d`. -/
lemma lift_core {p : ℕ} [Fact p.Prime] (hodd : Odd p) {k d D : ℕ}
    (hk : padicValNat p (2 ^ (p - 1) - 1) ≤ k)
    (hd : ∀ n : ℕ, d ∣ n ↔ p ^ k ∣ 2 ^ n - 1)
    (hD : ∀ n : ℕ, D ∣ n ↔ p ^ (k + 1) ∣ 2 ^ n - 1) : D = p * d := by
  have hp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hferm : p ∣ 2 ^ (p - 1) - 1 := dvd_two_pow_pred_sub_one hodd
  have hv1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
    one_le_padicValNat_of_dvd (two_pow_sub_one_ne_zero hp1) hferm
  have hppow : p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hn0 : (p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) ≠ 0 := Nat.mul_ne_zero hp1 hppow
  -- the exponent `(p - 1) * p ^ (k - v)` has valuation exactly `k`
  have hVn : padicValNat p (2 ^ ((p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1))) - 1) = k := by
    rw [val_two_pow_mul hodd hp1 hppow hferm, padicValNat.prime_pow]
    omega
  have hdn : d ∣ (p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) := by
    rw [hd, padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hn0), hVn]
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn0 (Nat.eq_zero_of_zero_dvd hdn)
  have hpk : p ^ k ∣ 2 ^ d - 1 := (hd d).mp dvd_rfl
  have hpd : p ∣ 2 ^ d - 1 := dvd_trans (dvd_pow_self p (by omega)) hpk
  have hVd_ge : k ≤ padicValNat p (2 ^ d - 1) :=
    (padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hd0)).mp hpk
  -- the valuation at the order `d` is exactly `k`
  have hVd : padicValNat p (2 ^ d - 1) = k := by
    obtain ⟨m, hm⟩ := hdn
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hn0 (by simpa using hm)
    have h := val_two_pow_mul hodd hd0 hm0 hpd
    rw [← hm, hVn] at h
    omega
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp.ne_zero
  have hDdp : D ∣ d * p := by
    rw [hD, padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hdp0),
      val_two_pow_mul hodd hd0 hp.ne_zero hpd, hVd, padicValNat_self]
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hdp0 (Nat.eq_zero_of_zero_dvd hDdp)
  have hpkD : p ^ (k + 1) ∣ 2 ^ D - 1 := (hD D).mp dvd_rfl
  have hdD : d ∣ D := by
    rw [hd]
    exact dvd_trans (pow_dvd_pow p (Nat.le_succ k)) hpkD
  obtain ⟨m, hm⟩ := hdD
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hD0 (by simpa using hm)
  have hVD : k + 1 ≤ padicValNat p (2 ^ D - 1) :=
    (padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hD0)).mp hpkD
  have hval := val_two_pow_mul hodd hd0 hm0 hpd
  rw [← hm, hVd] at hval
  have hpm : p ∣ m := dvd_of_one_le_padicValNat (by omega)
  have hdpD : d * p ∣ D := by
    rw [hm]
    exact Nat.mul_dvd_mul_left d hpm
  rw [mul_comm p d]
  exact Nat.dvd_antisymm hDdp hdpD

/-- Order lifting for the order of `2` modulo powers of an odd prime. -/
theorem orderOf_two_lift {p : ℕ} [Fact p.Prime] (hodd : Odd p) {k : ℕ}
    (hk : padicValNat p (2 ^ (p - 1) - 1) ≤ k) :
    orderOf (2 : ZMod (p ^ (k + 1))) = p * orderOf (2 : ZMod (p ^ k)) :=
  lift_core hodd hk (orderOf_two_dvd_iff _) (orderOf_two_dvd_iff _)

end OeisA2326Step

theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R1.H1 := by
  intro p hp hp2 hW k hk
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  rw [padicValNat_dvd_iff_le (OeisA2326Step.two_pow_sub_one_ne_zero hp1)] at hW
  exact OeisA2326Step.orderOf_two_lift hodd (by omega)
