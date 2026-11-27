import OMAReductions.R_BealConjecture_beal_conjecture_R2
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

-- Reduction BealConjecture.beal_conjecture.R2.H1.R1 of step BealConjecture.beal_conjecture.R2.H1
-- Credit: @Hennyrick

namespace OMA.R_BealConjecture_beal_conjecture_R2_H1_R1

/-- A primitive Beal equation whose right-hand base has two distinct prime divisors. -/
def H1 : Prop :=
  ∀ {a b c x y z p q : Nat}, 0 < a → 0 < b → 0 < c →
    2 < x → 2 < y → 2 < z → Nat.Coprime a b →
    (¬ ∃ j : Nat, 0 < j ∧ a = 2 ^ j) → (¬ ∃ j : Nat, 0 < j ∧ b = 2 ^ j) →
    p.Prime → q.Prime → p ≠ q → p ∣ c → q ∣ c → a ^ x + b ^ y ≠ c ^ z

/-- The odd prime-power right side when the two exponents on the left
have greatest common divisor a power of two, including one. -/
def H2 : Prop :=
  ∀ {a b x y p k t : Nat}, 0 < a → 0 < b → 2 < x → 2 < y → 2 < k →
    Nat.Coprime a b → (¬ ∃ j : Nat, 0 < j ∧ a = 2 ^ j) →
    (¬ ∃ j : Nat, 0 < j ∧ b = 2 ^ j) → 2 < p → p.Prime →
    Nat.gcd x y = 2 ^ t → a ^ x + b ^ y ≠ p ^ k

namespace BealPrimeGrowth

private theorem extend_power_bound {w n : Nat} (hw : 2 ≤ w)
    (h : 2 * (n + 1) ≤ w ^ n) :
    ∀ t : Nat, 2 * (n + t + 1) ≤ w ^ (n + t) := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
    change 2 * ((n+t).succ + 1) ≤ w ^ (n+t).succ
    rw [Nat.pow_succ]
    have hg := Nat.mul_le_mul ih hw
    omega

private theorem larger_power {w r : Nat} (hr : 3 ≤ r)
    (h : 3 ≤ w ∨ (2 ≤ w ∧ 3 < r)) : (2 * r) * w ≤ w ^ r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hr' : 2 * (3 + r) ≤ w ^ (2 + r) := by
    rcases h with h | ⟨hw, hr⟩
    · have h9 := Nat.pow_le_pow_left h 2
      have := extend_power_bound (by omega : 2 ≤ w)
        (by omega : 2 * (2 + 1) ≤ w ^ 2) r
      omega
    · cases r with
      | zero => omega
      | succ t =>
        have h8 := Nat.pow_le_pow_left hw 3
        have he := extend_power_bound hw (by omega : 2 * (3 + 1) ≤ w ^ 3) t
        have hn : 2 + (t + 1) = 3 + t := by omega
        rw [hn]
        omega
  have hh := Nat.mul_le_mul_right w hr'
  have hE : 3 + r = (2 + r).succ := by omega
  rw [hE, Nat.pow_succ]
  rwa [hE] at hh

private theorem sum_gt_of_le {u v r : Nat} (hu : 0 < u) (huv : u ≤ v)
    (hr : 3 ≤ r) (h : 3 ≤ v ∨ (2 ≤ v ∧ 3 < r)) :
    r * (u + v) < u ^ r + v ^ r := by
  have hv := larger_power hr h
  have hsum := Nat.mul_le_mul_left r (show u + v ≤ 2 * v by omega)
  have he : r * (2 * v) = (2 * r) * v := by
    rw [← Nat.mul_assoc, Nat.mul_comm r 2]
  rw [he] at hsum
  have hup := Nat.pow_pos (n := r) hu
  omega

theorem sum_gt {u v r : Nat} (hu : 0 < u) (hv : 0 < v) (hr : 3 ≤ r)
    (h : 3 ≤ max u v ∨ (2 ≤ max u v ∧ 3 < r)) :
    r * (u + v) < u ^ r + v ^ r := by
  by_cases huv : u ≤ v
  · rw [Nat.max_eq_right huv] at h
    exact sum_gt_of_le hu huv hr h
  · have hvu : v ≤ u := by omega
    rw [Nat.max_eq_left hvu] at h
    rw [Nat.add_comm u v, Nat.add_comm (u ^ r) (v ^ r)]
    exact sum_gt_of_le hv hvu hr h

end BealPrimeGrowth

namespace BealPrimeLTE

/-- The cofactor in the sum of two coprime odd powers has the same
valuation at an odd prime dividing the base sum as the exponent has. -/
theorem cofactor_valuation {p u v r : Nat} (hp : p.Prime) (hop : Odd p)
    (hr : Odd r) (hc : Nat.Coprime u v) (hd : p ∣ u + v) :
    padicValNat p ((u ^ r + v ^ r) / (u + v)) = padicValNat p r := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpu : ¬ p ∣ u := by
    intro h
    have hdvd := Nat.dvd_gcd h ((Nat.dvd_add_right h).mp hd)
    change Nat.gcd u v = 1 at hc
    rw [hc] at hdvd
    exact hp.ne_one (Nat.dvd_one.mp hdvd)
  rw [padicValNat.div_of_dvd (hr.nat_add_dvd_pow_add_pow u v),
    padicValNat.pow_add_pow hop hd hpu hr, Nat.add_sub_cancel_left]

/-- If the whole sum is a power of the same prime, its cofactor divides the
exponent. -/
theorem cofactor_dvd {p u v r k : Nat} (hp : p.Prime) (hop : Odd p)
    (hr : Odd r) (hc : Nat.Coprime u v) (hd : p ∣ u + v) (he : u ^ r + v ^ r = p ^ k) :
    (u ^ r + v ^ r) / (u + v) ∣ r := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hden : u + v ∣ u ^ r + v ^ r := hr.nat_add_dvd_pow_add_pow u v
  have hq := Nat.div_dvd_of_dvd hden
  rw [he] at hq
  obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow hp).mp hq
  have hval := cofactor_valuation hp hop hr hc hd
  rw [he, hs, padicValNat.prime_pow] at hval
  rw [he, hs, hval]
  exact pow_padicValNat_dvd

theorem sum_le_linear {p u v r k : Nat} (hp : p.Prime) (hop : Odd p)
    (hr : Odd r) (hc : Nat.Coprime u v) (hd : p ∣ u + v) (he : u ^ r + v ^ r = p ^ k) :
    u ^ r + v ^ r ≤ (u + v) * r := by
  have hden : u + v ∣ u ^ r + v ^ r := hr.nat_add_dvd_pow_add_pow u v
  have hq := Nat.le_of_dvd hr.pos (cofactor_dvd hp hop hr hc hd he)
  calc
    u ^ r + v ^ r = (u + v) * ((u ^ r + v ^ r) / (u + v)) := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hden]
    _ ≤ (u + v) * r := Nat.mul_le_mul_left _ hq

end BealPrimeLTE


private theorem rule_out_small {p u v r k : Nat} (hp : 3 ≤ p)
    (hu : 0 < u) (hv : 0 < v) (hk : 3 ≤ k) (hr : 3 ≤ r)
    (h : ¬(3 ≤ max u v ∨ (2 ≤ max u v ∧ 3 < r))) : u ^ r + v ^ r ≠ p ^ k := by
  have hlp : 3 ^ 3 ≤ p ^ k :=
    Nat.le_trans (Nat.pow_le_pow_left hp 3) (Nat.pow_le_pow_right (by omega) hk)
  have hu' := Nat.le_max_left u v
  have hv' := Nat.le_max_right u v
  by_cases hmax : 2 ≤ max u v
  · have hr' : r = 3 := by omega
    subst r
    have hu2 : u ^ 3 ≤ 2 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hv2 : v ^ 3 ≤ 2 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  · have h1 : u = 1 := by omega
    have h2 : v = 1 := by omega
    rw [h1, h2, Nat.one_pow]
    omega

/-- Two positive coprime bases raised to the same odd exponent of at least three
cannot sum to an odd prime power with exponent at least three. -/
theorem no_odd_prime_power_sum {p u v r k : Nat} (hp : p.Prime) (hopp : Odd p) (hu : 0 < u) (hv : 0 < v)
    (hc : Nat.Coprime u v) (hr : 3 ≤ r) (ho : Odd r) (hk : 3 ≤ k) :
    u ^ r + v ^ r ≠ p ^ k := by
  intro he
  have hd : u+v ∣ p^k := he ▸ ho.nat_add_dvd_pow_add_pow u v
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hps : p ∣ u+v := by
    cases j with
    | zero => simp at hj; omega
    | succ j => exact ⟨p^j, by rw [hj, Nat.pow_succ, Nat.mul_comm]⟩
  have hp' := hp.two_le
  have hpo := Nat.odd_iff.mp hopp
  by_cases h : 3 ≤ max u v ∨ (2 ≤ max u v ∧ 3 < r)
  · have hgt := BealPrimeGrowth.sum_gt hu hv hr h
    have hle := BealPrimeLTE.sum_le_linear hp hopp ho hc hps he
    rw [Nat.mul_comm (u+v) r] at hle
    omega
  · exact rule_out_small (by omega) hu hv hk hr h he


private theorem shared_prime_yields_gcd {a b c x y z : Nat}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (hn : ¬ Nat.Coprime a b) (he : a ^ x + b ^ y = c ^ z) :
    1 < Nat.gcd a (Nat.gcd b c) := by
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hax : a ∣ a ^ x := by simpa only [Nat.pow_one] using Nat.pow_dvd_pow a hx
  have hby : b ∣ b ^ y := by simpa only [Nat.pow_one] using Nat.pow_dvd_pow b hy
  have hpc : p ∣ c := hp.dvd_of_dvd_pow (he ▸ Nat.dvd_add (hpa.trans hax) (hpb.trans hby))
  exact hp.one_lt.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ ha)
    (Nat.dvd_gcd hpa (Nat.dvd_gcd hpb hpc)))

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R2.H1 := by
  intro h1 h2 a b c x y z ha hb hc hx hy hz hna hnb hnc he
  apply shared_prime_yields_gcd (by omega) (by omega) (by omega) _ he
  intro hab
  have hcn : c ≠ 1 := by
    intro h
    rw [h, Nat.one_pow] at he
    have := Nat.pow_pos (n := x) (by omega : 0 < a)
    have := Nat.pow_pos (n := y) (by omega : 0 < b)
    omega
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hcn
  obtain ⟨s, m, hpm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc p hp.ne_one
  by_cases hm : m = 1
  · subst m
    rw [Nat.mul_one] at hfac
    have hs : 0 < s := by
      by_contra! h
      rw [show s = 0 by omega, Nat.pow_zero] at hfac
      exact hcn hfac
    have hpne : p ≠ 2 := by
      rintro rfl
      exact hnc ⟨s, hs, hfac⟩
    have hop := hp.eq_two_or_odd'.resolve_left hpne
    have hple := hp.two_le
    obtain ⟨t, r, hro, hd⟩ := Nat.exists_eq_two_pow_mul_odd
      (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left y (by omega : 0 < x)))
    have hs' := Nat.mul_le_mul_right z (show 1 ≤ s by omega)
    have hk : 2 < s*z := by omega
    rw [hfac, ← Nat.pow_mul] at he
    by_cases hr : r = 1
    · subst r
      exact h2 (by omega) (by omega) hx hy hk hab hna hnb (by omega) hp
        (by simpa only [Nat.mul_one] using hd) he
    · have hmod := Nat.odd_iff.mp hro
      have hdvd : r ∣ Nat.gcd x y := by rw [hd]; exact Nat.dvd_mul_left _ _
      obtain ⟨i, hi⟩ := hdvd.trans (Nat.gcd_dvd_left x y)
      obtain ⟨j, hj⟩ := hdvd.trans (Nat.gcd_dvd_right x y)
      rw [hi, hj, Nat.mul_comm r i, Nat.mul_comm r j, Nat.pow_mul, Nat.pow_mul] at he
      exact no_odd_prime_power_sum hp hop (Nat.pow_pos (by omega : 0 < a))
        (Nat.pow_pos (by omega : 0 < b)) (hab.pow i j) (by omega) hro (by omega) he
  · obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm
    have hneq : p ≠ q := fun h => hpm (h ▸ hqm)
    have hqc : q ∣ c := by rw [hfac]; exact hqm.trans (Nat.dvd_mul_left _ _)
    exact h1 (by omega) (by omega) (by omega) hx hy hz hab hna hnb hp hq hneq hpc hqc he

end OMA.R_BealConjecture_beal_conjecture_R2_H1_R1
