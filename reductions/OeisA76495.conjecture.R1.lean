import FormalConjectures.OEIS.«76495»
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.ZMod.Basic

/-! A restriction on even solutions of the divisor-sum congruence with remainder five. -/

open Finset ArithmeticFunction

namespace SigmaFive

private theorem two_prime_pow_of_two_le {a e q : ℕ} (ha : 1 ≤ a) (he : 2 ≤ e)
    (hq : q.Prime) (hq3 : 3 ≤ q) :
    sigma 1 (2 ^ a * q ^ e) % (2 ^ a * q ^ e) ≠ 5 := by
  intro h
  let P : ℕ := 2 ^ a
  let Q : ℕ := q ^ e
  let S : ℕ := ∑ i ∈ range e, q ^ i
  have hP : 2 ≤ P := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) ha
  have hQ : 9 ≤ Q := calc
    9 = 3 ^ 2 := by decide
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 _
    _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
  have hS : 1 + q ≤ S := by
    dsimp [S]
    have hel := sum_le_sum_of_subset_of_nonneg (range_mono he)
      (fun i _ _ => Nat.zero_le (q ^ i))
    simpa [sum_range_succ] using hel
  have hgeom : S * (q-1) + 1 = Q := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by omega), S, Q] using
      (geom_sum_mul_add (q-1) e)
  have hS2 : 2*S ≤ Q := by
    have hh := Nat.mul_le_mul_left S (show 2 ≤ q-1 by omega)
    omega
  have hc : Nat.Coprime P Q := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes Nat.prime_two hq).2 (by omega)
  have htwo : (∑ i ∈ range (a+1), 2 ^ i) = 2*P-1 := by
    have hh := geom_sum_mul_add (1 : ℕ) (a+1)
    norm_num [pow_succ, P] at hh ⊢
    omega
  have hs : sigma 1 (P*Q) = (2*P-1)*(S+Q) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc]
    change sigma 1 (2^a) * sigma 1 (q^e) = _
    rw [sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow hq,
      htwo, sum_range_succ]
  change sigma 1 (P*Q) % (P*Q) = 5 at h
  let k := ((2*P-1)*(S+Q)) / (P*Q)
  have heq := Nat.mod_add_div (sigma 1 (P*Q)) (P*Q)
  rw [h, hs] at heq
  change 5 + P*Q*k = (2*P-1)*(S+Q) at heq
  have hklo : 2 ≤ k := by
    by_contra! hr
    have hkmul := Nat.mul_le_mul_left (P*Q) (show k ≤ 1 by omega)
    have hlow : (P+1)*Q ≤ (2*P-1)*(S+Q) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [← heq] at hlow
    simp only [mul_one] at hkmul
    nlinarith
  have hkhi : k ≤ 2 := by
    by_contra! hr
    have hkprod := Nat.mul_le_mul_left (P*Q) hr
    have hsum : 2*(S+Q) ≤ 3*Q := by omega
    have hprod := Nat.mul_le_mul_left P hsum
    have hstrict : (2*P-1)*(S+Q) < (2*P)*(S+Q) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    nlinarith
  have hk : k = 2 := by omega
  rw [hk] at heq
  have key : 2*P*S = q*S+6 := by
    have hm : (q-1)+1=q := Nat.sub_add_cancel (by omega)
    have hp : (2*P-1)+1=2*P := Nat.sub_add_cancel (by omega)
    nlinarith only [heq, hgeom, congrArg (S * ·) hm, congrArg (· * (S+Q)) hp]
  have hgreater : q < 2*P := by
    by_contra! hh
    have := Nat.mul_le_mul_right S hh
    omega
  have hd : (2*P-q)*S = 6 := by
    rw [Nat.sub_mul, key, Nat.add_sub_cancel_left]
  have hle : S ≤ 6 := by
    have hp := Nat.mul_le_mul_right S (show 1 ≤ 2*P-q by omega)
    simpa [hd] using hp
  have hsmall : e = 2 := by
    by_contra hn
    have hem : 3 ≤ e := by omega
    have hc : 1+q+q^2 ≤ S := by
      dsimp [S]
      simpa [sum_range_succ] using (sum_le_sum_of_subset_of_nonneg (range_mono hem)
        (fun i _ _ => Nat.zero_le (q ^ i)))
    nlinarith
  have heval : S = 1+q := by simp [S,hsmall,sum_range_succ]
  have hqmax : q ≤ 5 := by omega
  interval_cases q
  · rw [heval] at hd
    omega
  · exact (by decide : ¬ Nat.Prime 4) hq
  · rw [heval] at hd
    have hp3 : P = 3 := by omega
    have : 2 ∣ P := by
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
      simp [P,pow_succ]
    omega

theorem two_prime_pow {a e q : ℕ} (ha : 1 ≤ a) (he : 1 ≤ e)
    (hq : q.Prime) (hq3 : 3 ≤ q) :
    sigma 1 (2 ^ a * q ^ e) % (2 ^ a * q ^ e) ≠ 5 := by
  by_cases hb : 2 ≤ e
  · exact two_prime_pow_of_two_le ha hb hq hq3
  have he1 : e = 1 := by omega
  subst e
  simp only [pow_one]
  intro h
  have hc : Nat.Coprime (2^a) q :=
    ((Nat.coprime_primes Nat.prime_two hq).2 (by omega)).pow_left a
  have hqeven : 2 ∣ q+1 := by
    obtain ⟨j,hj⟩ := hq.odd_of_ne_two (by omega)
    exact ⟨j+1, by omega⟩
  have hse : 2 ∣ sigma 1 (2^a*q) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, ← pow_one q,
      sigma_one_apply_prime_pow hq]
    simp only [show (1 : ℕ)+1=2 by decide, sum_range_succ, sum_range_zero, pow_zero,
      pow_one, zero_add]
    exact dvd_mul_of_dvd_right (by simpa [Nat.add_comm] using hqeven : 2 ∣ 1 + q) _
  have hne : 2 ∣ 2^a*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  have hm := Nat.mod_mod_of_dvd (sigma 1 (2^a*q)) hne
  rw [h, Nat.mod_eq_zero_of_dvd hse] at hm
  exact (by decide : 5 % 2 ≠ 0) hm

theorem prime_pow {q : ℕ} (hq : q.Prime) (e : ℕ) :
    sigma 1 (q^e) % (q^e) ≠ 5 := by
  let S := ∑ i ∈ range e, q^i
  have hg : S*(q-1)+1 = q^e := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by have := hq.two_le; omega), S] using
      (geom_sum_mul_add (q-1) e)
  have hl : S < q^e := by
    have := Nat.mul_le_mul_left S (show 1 ≤ q-1 by have := hq.two_le; omega)
    omega
  rw [sigma_one_apply_prime_pow hq, sum_range_succ, Nat.add_mod_right, Nat.mod_eq_of_lt hl]
  intro heq
  by_cases hlarge : 3 ≤ e
  · have hsum : 1+q+q^2 ≤ S := by
      dsimp [S]
      simpa [sum_range_succ] using (sum_le_sum_of_subset_of_nonneg (range_mono hlarge)
        (fun i _ _ => Nat.zero_le (q ^ i)))
    have hq2 := hq.two_le
    change S = 5 at heq
    nlinarith
  · have cases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · simp [S] at heq
    · simp [S, sum_range_succ] at heq
    · simp [S, sum_range_succ] at heq
      have hq4 : q = 4 := by omega
      exact (by decide : ¬ Nat.Prime 4) (hq4 ▸ hq)

private theorem sigma_bound {p d : ℕ} (hp : p.Prime) (e : ℕ) (hd : d ≤ p-1) :
    d * sigma 1 (p ^ e) ≤ (d+1)*p^e := by
  let S := ∑ i ∈ range e, p^i
  have hg : S*(p-1)+1 = p^e := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ p by have := hp.two_le; omega), S] using
      (geom_sum_mul_add (p-1) e)
  have hdS := Nat.mul_le_mul_left S hd
  rw [sigma_one_apply_prime_pow hp, sum_range_succ]
  change d*(S+p^e) ≤ _
  nlinarith

private theorem pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    p^e < sigma 1 (p^e) := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ]
  have hb : 1 ≤ ∑ i ∈ range e, p^i := by
    simpa using (single_le_sum (f := fun i => p^i) (fun i _ => Nat.zero_le _)
      (mem_range.mpr (show 0 < e by omega)))
  omega

theorem odd_two_prime_pow {p q a e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) (ha : 1 ≤ a) (he : 1 ≤ e) :
    sigma 1 (p^a*q^e) % (p^a*q^e) ≠ 5 := by
  let P := p^a
  let Q := q^e
  have hP : 3 ≤ P := hp3.trans (by
    simpa [P] using Nat.pow_le_pow_right hp.pos ha)
  have hQ : 5 ≤ Q := hq5.trans (by
    simpa [Q] using Nat.pow_le_pow_right hq.pos he)
  have hc : P.Coprime Q := ((Nat.coprime_primes hp hq).2 hne).pow _ _
  have hmul : sigma 1 (P*Q) = sigma 1 P * sigma 1 Q :=
    isMultiplicative_sigma.map_mul_of_coprime hc
  have high : sigma 1 (P*Q) < 2*(P*Q) := by
    rw [hmul]
    have h := Nat.mul_le_mul (sigma_bound hp a (d := 2) (by omega))
      (sigma_bound hq e (d := 4) (by omega))
    change (2*sigma 1 P)*(4*sigma 1 Q) ≤ (2+1)*P*((4+1)*Q) at h
    have hpos : 0 < P*Q := Nat.mul_pos (by omega) (by omega)
    nlinarith only [h, hpos]
  have low : P*Q+5 < sigma 1 (P*Q) := by
    rw [hmul]
    have hl := Nat.mul_le_mul (pow_lt_sigma hp ha) (pow_lt_sigma hq he)
    change (P+1)*(Q+1) ≤ sigma 1 P * sigma 1 Q at hl
    nlinarith only [hl, hP, hQ]
  change sigma 1 (P*Q) % (P*Q) ≠ 5
  intro h
  have hx := Nat.mod_add_div (sigma 1 (P*Q)) (P*Q)
  rw [h] at hx
  let k := sigma 1 (P*Q) / (P*Q)
  change 5 + (P*Q)*k = _ at hx
  by_cases hk : k ≤ 1
  · have hb := Nat.mul_le_mul_left (P*Q) hk
    omega
  · have hb := Nat.mul_le_mul_left (P*Q) (show 2 ≤ k by omega)
    omega

private theorem ordered_pair {p q a e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (ha : 1 ≤ a) (he : 1 ≤ e) :
    sigma 1 (p^a*q^e) % (p^a*q^e) ≠ 5 := by
  have hp2 := hp.two_le
  by_cases hp' : p = 2
  · subst p
    exact two_prime_pow ha he hq (by omega)
  have hq5 : 5 ≤ q := by
    by_contra! hh
    have hq4 : q = 4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (hq4 ▸ hq)
  exact odd_two_prime_pow hp hq (by omega) hq5 (by omega) ha he

theorem three_le_primeFactors_card {n : ℕ} (hn : 0 < n)
    (h : sigma 1 n % n = 5) : 3 ≤ n.primeFactors.card := by
  have hn0 := Nat.ne_of_gt hn
  have fac := Nat.prod_primeFactors_pow_factorization hn0
  by_contra! hs
  have cases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 := by omega
  rcases cases with hzero | hone | htwo
  · rw [Finset.card_eq_zero.mp hzero, Finset.prod_empty] at fac
    rw [fac] at h
    simp at h
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hone
    have hprime := (Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hp])).1
    rw [hp,Finset.prod_singleton] at fac
    exact (prime_pow hprime (n.factorization p)) (by simpa only [← fac] using h)
  · obtain ⟨p,q,hne,hpq⟩ := Finset.card_eq_two.mp htwo
    have hp := Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hpq])
    have hq := Nat.mem_primeFactors.mp (show q ∈ n.primeFactors by simp [hpq])
    have ha := hp.1.factorization_pos_of_dvd hn0 hp.2.1
    have he := hq.1.factorization_pos_of_dvd hn0 hq.2.1
    rw [hpq,Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at fac
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ordered_pair hp.1 hq.1 hlt ha he) (by simpa only [← fac] using h)
    · rw [mul_comm] at fac
      exact (ordered_pair hq.1 hp.1 hlt he ha) (by simpa only [← fac] using h)


end SigmaFive
open Finset ArithmeticFunction

namespace SigmaFive.Modular

private theorem sum_five_powers_mod_five (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, 5 ^ i) % 5 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hterm : 5 ^ n % 5 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_pow_self 5 (by omega)
      rw [Nat.add_mod, ih (by omega), hterm]


private theorem sum_three_powers_mod_three (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, 3 ^ i) % 3 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hterm : 3 ^ n % 3 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_pow_self 3 (by omega)
      rw [Nat.add_mod, ih (by omega), hterm]

/-- Sigma of any power of 3 is one modulo 3. -/
theorem sigma_three_pow_mod_three (a : ℕ) :
    sigma 1 (3 ^ a) % 3 = 1 := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3), sum_range_succ]
  by_cases ha : a = 0
  · simp [ha]
  · have hs := sum_three_powers_mod_three a (by omega)
    have hp : 3 ^ a % 3 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self 3 (by omega)
    rw [Nat.add_mod, hs, hp]

private theorem pow_even_mod_three {p b : ℕ} (hp : p % 3 = 2) :
    p ^ (2*b) % 3 = 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show 2*(b+1) = 2*b+2 by omega, pow_add, Nat.mul_mod, Nat.mul_mod, ih]
    rw [Nat.pow_mod, hp]

private theorem sigma_prime_power_even_mod_three {p b : ℕ}
    (hp : p.Prime) (hpm : p % 3 = 2) (hpd : (p-1) % 3 = 1) :
    sigma 1 (p ^ (2*b)) % 3 = 1 := by
  rw [sigma_one_apply_prime_pow hp]
  rw [sum_range_succ]
  let S := ∑ i ∈ range (2*b), p ^ i
  have hm : p-1+1 = p := Nat.sub_add_cancel (by have := hp.two_le; omega)
  have hg : S * (p-1) + 1 = p ^ (2*b) := by
    convert geom_sum_mul_add (p-1) (2*b) using 1 <;> simp [S, hm]
  have hr := congrArg (fun x : ℕ => x % 3) hg
  rw [Nat.add_mod, Nat.mul_mod] at hr
  have hpow := @pow_even_mod_three p b hpm
  rw [hpow, hpd] at hr
  have hsum : S % 3 = 0 := by omega
  rw [Nat.add_mod, hsum, hpow]

/-- Sigma of a power of 5 with even exponent is one modulo 3. -/
theorem sigma_five_pow_mod_three (b : ℕ) :
    sigma 1 (5 ^ (2*b)) % 3 = 1 :=
  sigma_prime_power_even_mod_three (p := 5) (by decide) (by norm_num) (by norm_num)

/-- Sigma of a power of 11 with even exponent is one modulo 3. -/
theorem sigma_eleven_pow_mod_three (b : ℕ) :
    sigma 1 (11 ^ (2*b)) % 3 = 1 :=
  sigma_prime_power_even_mod_three (p := 11) (by decide) (by norm_num) (by norm_num)


/-- The geometric factor for every nonnegative even exponent of 5 is one modulo 5. -/
theorem sigma_five_pow_mod_five (b : ℕ) :
    sigma 1 (5 ^ (2*b)) % 5 = 1 := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  rw [sum_range_succ]
  by_cases he : 2*b = 0
  · simp [he]
  · have hs := sum_five_powers_mod_five (2*b) (by omega)
    have hp : 5 ^ (2*b) % 5 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self 5 (by omega)
    rw [Nat.add_mod, hs, hp]

end SigmaFive.Modular

namespace SigmaFive

private theorem triple_sigma {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) :
    sigma 1 (p^a*q^b*r^c) = sigma 1 (p^a)*sigma 1 (q^b)*sigma 1 (r^c) := by
  have h1 : (p^a).Coprime (q^b) := ((Nat.coprime_primes hp hq).2 (by omega)).pow _ _
  have h2 : (p^a).Coprime (r^c) := ((Nat.coprime_primes hp hr).2 (by omega)).pow _ _
  have h3 : (q^b).Coprime (r^c) := ((Nat.coprime_primes hq hr).2 (by omega)).pow _ _
  rw [isMultiplicative_sigma.map_mul_of_coprime (h2.mul_left h3),
    isMultiplicative_sigma.map_mul_of_coprime h1]

private theorem triple_bound {p q r a b c d f g : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (hd : d ≤ p-1) (hf : f ≤ q-1) (hg : g ≤ r-1) :
    d*f*g*sigma 1 (p^a*q^b*r^c) ≤ (d+1)*(f+1)*(g+1)*(p^a*q^b*r^c) := by
  rw [triple_sigma hp hq hr hpq hqr]
  calc
    _ = (d*sigma 1 (p^a))*(f*sigma 1 (q^b))*(g*sigma 1 (r^c)) := by ring
    _ ≤ ((d+1)*p^a)*((f+1)*q^b)*((g+1)*r^c) := Nat.mul_le_mul
      (Nat.mul_le_mul (sigma_bound hp a hd) (sigma_bound hq b hf)) (sigma_bound hr c hg)
    _ = _ := by ring

private theorem sum_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ i ∈ range e, p^i) % 2 = e % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

private theorem even_exp_of_odd_sigma {p e : ℕ} (hp : p.Prime)
    (hpodd : p % 2 = 1) (hs : Odd (sigma 1 (p^e))) : Even e := by
  rw [sigma_one_apply_prime_pow hp] at hs
  have hs' := Nat.odd_iff.mp hs
  rw [sum_pow_mod_two hpodd] at hs'
  exact Nat.even_iff.mpr (by omega)

theorem odd_triple_shape {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : sigma 1 (p^a*q^b*r^c) % (p^a*q^b*r^c) = 5) :
    p = 3 ∧ q = 5 ∧ (r = 7 ∨ r = 11 ∨ r = 13) ∧
      Even a ∧ Even b ∧ Even c ∧
      sigma 1 (p^a*q^b*r^c) = 2*(p^a*q^b*r^c)+5 := by
  have q5 : 5 ≤ q := by
    by_contra! hq'
    have : q = 4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (this ▸ hq)
  have r7 : 7 ≤ r := by
    by_contra! hr'
    have : r = 6 := by omega
    exact (by decide : ¬ Nat.Prime 6) (this ▸ hr)
  let P := p^a
  let Q := q^b
  let R := r^c
  let N := P*Q*R
  let F := sigma 1 N
  have P3 : 3 ≤ P := hp3.trans (by simpa [P] using Nat.pow_le_pow_right hp.pos ha)
  have Q5 : 5 ≤ Q := q5.trans (by simpa [Q] using Nat.pow_le_pow_right hq.pos hb)
  have R7 : 7 ≤ R := r7.trans (by simpa [R] using Nat.pow_le_pow_right hr.pos hc)
  have hn : 0 < N := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hbound := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
    (d := 2) (f := 4) (g := 6) (by omega) (by omega) (by omega)
  change 48*F ≤ 105*N at hbound
  have hl : N+5 < F := by
    have L : (P+1)*Q*R ≤ F := by
      dsimp only [F,N,P,Q,R]
      rw [triple_sigma hp hq hr hpq hqr]
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (pow_lt_sigma hp ha) (pow_lt_sigma hq hb).le)
        (pow_lt_sigma hr hc).le
    have hqr' : 5*7 ≤ Q*R := Nat.mul_le_mul Q5 R7
    dsimp only [N]
    nlinarith only [L, hqr']
  change F % N = 5 at h
  have heq := Nat.mod_add_div F N
  rw [h] at heq
  have hklo : 2 ≤ F/N := by
    by_contra! hh
    have := Nat.mul_le_mul_left N (show F/N ≤ 1 by omega)
    omega
  have hkhi : F/N ≤ 2 := by
    by_contra! hh
    have := Nat.mul_le_mul_left N hh
    omega
  have hk : F/N = 2 := by omega
  rw [hk] at heq
  have heq' : F = 2*N+5 := by omega
  have hp' : p = 3 := by
    by_contra hne
    have p5 : 5 ≤ p := by
      by_contra! hh
      have : p = 4 := by omega
      exact (by decide : ¬ Nat.Prime 4) (this ▸ hp)
    have q7 : 7 ≤ q := by
      by_contra! hh
      have : q = 6 := by omega
      exact (by decide : ¬ Nat.Prime 6) (this ▸ hq)
    have r11 : 11 ≤ r := by
      have r8 : 8 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> revert hr <;> decide
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 4) (f := 6) (g := 10) (by omega) (by omega) (by omega)
    change 240*F ≤ 385*N at H
    omega
  have hq' : q = 5 := by
    by_contra hne
    have q7 : 7 ≤ q := by
      by_contra! hh
      have : q = 6 := by omega
      exact (by decide : ¬ Nat.Prime 6) (this ▸ hq)
    have r11 : 11 ≤ r := by
      have r8 : 8 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> revert hr <;> decide
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 2) (f := 6) (g := 10) (by omega) (by omega) (by omega)
    change 120*F ≤ 231*N at H
    omega
  have r16 : r ≤ 16 := by
    by_contra! hh
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 2) (f := 4) (g := 16) (by omega) (by omega) (by omega)
    change 128*F ≤ 255*N at H
    omega
  have hrc : r = 7 ∨ r = 11 ∨ r = 13 := by
    interval_cases r <;> revert hr <;> decide
  have oddF : Odd F := ⟨N+2, by omega⟩
  change Odd (sigma 1 (p^a*q^b*r^c)) at oddF
  rw [triple_sigma hp hq hr hpq hqr, Nat.odd_mul, Nat.odd_mul] at oddF
  refine ⟨hp', hq', hrc, ?_, ?_, ?_, heq'⟩
  · exact even_exp_of_odd_sigma hp (by omega) oddF.1.1
  · exact even_exp_of_odd_sigma hq (by omega) oddF.1.2
  · exact even_exp_of_odd_sigma hr (by
      exact Nat.odd_iff.mp (hr.odd_of_ne_two (by omega))) oddF.2

end SigmaFive

namespace SigmaFive

private theorem sorted_card_three (S : Finset ℕ) (h : S.card = 3) :
    ∃ p q r, p < q ∧ q < r ∧ S = {p,q,r} := by
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hxy with hxy' | hyx
  · rcases lt_or_gt_of_ne hyz with hyz' | hzy
    · exact ⟨x,y,z,hxy',hyz',rfl⟩
    · rcases lt_or_gt_of_ne hxz with hxz' | hzx
      · refine ⟨x,z,y,hxz',hzy,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
      · refine ⟨z,x,y,hzx,hxy',?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
  · rcases lt_or_gt_of_ne hxz with hxz' | hzx
    · refine ⟨y,x,z,hyx,hxz',?_⟩
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
    · rcases lt_or_gt_of_ne hyz with hyz' | hzy
      · refine ⟨y,z,x,hyz',hzx,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
      · refine ⟨z,y,x,hzy,hyx,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto

theorem odd_four_support_of_modular
    (hexcl : ∀ a b c r : ℕ, 0 < a → 0 < b → Even a → Even b → Even c →
      (r = 7 ∨ r = 11 ∨ r = 13) →
      sigma 1 (3^a*5^b*r^c) ≠ 2*(3^a*5^b*r^c)+5)
    {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    4 ≤ n.primeFactors.card := by
  have hn' : 0 < n := by obtain ⟨j,hj⟩ := hn; omega
  have hge := three_le_primeFactors_card hn' h
  by_contra! hh
  obtain ⟨p,q,r,hpq,hqr,hset⟩ := sorted_card_three _ (by omega : n.primeFactors.card = 3)
  have hp := Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hset])
  have hq := Nat.mem_primeFactors.mp (show q ∈ n.primeFactors by simp [hset])
  have hr := Nat.mem_primeFactors.mp (show r ∈ n.primeFactors by simp [hset])
  have hp3 : 3 ≤ p := by
    have := hp.1.two_le
    by_contra! hl
    have he : p = 2 := by omega
    exact (hn.not_two_dvd_nat) (he ▸ hp.2.1)
  have ha := hp.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hp.2.1
  have hb := hq.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hq.2.1
  have hc := hr.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hr.2.1
  have hnfac := Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn')
  rw [hset, prod_insert (by simp; omega), prod_insert (by simp; omega), prod_singleton] at hnfac
  rw [← mul_assoc] at hnfac
  obtain ⟨hp',hq',hR,ha',hb',hc',heq⟩ :=
    odd_triple_shape hp.1 hq.1 hr.1 hp3 hpq hqr ha hb hc (by simpa only [← hnfac] using h)
  subst p
  subst q
  exact hexcl _ _ _ _ ha hb ha' hb' hc' hR heq

end SigmaFive

namespace SigmaFive

theorem exclude_triple_from_residues
    (three_mod_three : ∀ a : ℕ, sigma 1 (3^a) % 3 = 1)
    (five_mod_three : ∀ b : ℕ, Even b → sigma 1 (5^b) % 3 = 1)
    (eleven_mod_three : ∀ c : ℕ, Even c → sigma 1 (11^c) % 3 = 1)
    (five_mod_five : ∀ b : ℕ, Even b → sigma 1 (5^b) % 5 = 1)
    (other_mod_five : ∀ p e : ℕ, (p = 3 ∨ p = 7 ∨ p = 13) → Even e →
      sigma 1 (p^e) % 5 ≠ 0)
    (a b c r : ℕ) (ha : 0<a) (hb : 0<b) (ha' : Even a) (hb' : Even b) (hc' : Even c)
    (hr : r=7 ∨ r=11 ∨ r=13) :
    sigma 1 (3^a*5^b*r^c) ≠ 2*(3^a*5^b*r^c)+5 := by
  intro heq
  have hp : Nat.Prime r := by rcases hr with rfl | rfl | rfl <;> decide
  have hgt : 5 < r := by omega
  rw [triple_sigma (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) hp (by decide) hgt] at heq
  by_cases hr11 : r = 11
  · subst r
    have hn0 : (2*(3^a*5^b*11^c)) % 3 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_pow_self 3 (by omega : a ≠ 0)) _) _) _
    have hh := congrArg (fun x : ℕ => x % 3) heq
    rw [Nat.add_mod, hn0, Nat.mul_mod, Nat.mul_mod (sigma 1 (3^a)) (sigma 1 (5^b)) 3, three_mod_three,
      five_mod_three b hb', eleven_mod_three c hc'] at hh
    norm_num at hh
  · have hn : 5 ∣ 2*(3^a*5^b*r^c)+5 := by
      apply dvd_add _ (dvd_refl _)
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega : b ≠ 0)) _) _) _
    rw [← heq] at hn
    have prime5 : Nat.Prime 5 := by decide
    rcases prime5.dvd_mul.mp hn with h | h
    · rcases prime5.dvd_mul.mp h with h3 | h5
      · exact (other_mod_five 3 a (Or.inl rfl) ha') (Nat.mod_eq_zero_of_dvd h3)
      · have hz := Nat.mod_eq_zero_of_dvd h5
        rw [five_mod_five b hb'] at hz
        omega
    · exact (other_mod_five r c (by omega) hc') (Nat.mod_eq_zero_of_dvd h)

end SigmaFive

namespace SigmaFive.Modular

private theorem geom_odd_ne_zero (x : ZMod 5) (hx : x ^ 2 = -1) (j : ℕ) :
    (∑ i ∈ range (2 * j + 1), x ^ i) ≠ 0 := by
  intro h
  have he := geom_sum_mul x (2 * j + 1)
  rw [h, zero_mul, eq_comm, sub_eq_zero] at he
  have hh := congrArg (fun y : ZMod 5 => y ^ 2) he
  rw [← pow_mul, mul_comm (2*j+1) 2, pow_mul, hx, one_pow] at hh
  have hodd : Odd (2*j+1) := ⟨j, rfl⟩
  rw [hodd.neg_pow, one_pow] at hh
  exact (by decide : (-1 : ZMod 5) ≠ 1) hh

theorem sigma_other_mod_five (p j : ℕ) (hp : p = 3 ∨ p = 7 ∨ p = 13) :
    sigma 1 (p ^ (2*j)) % 5 ≠ 0 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have hx : (p : ZMod 5) ^ 2 = -1 := by rcases hp with rfl | rfl | rfl <;> decide
  intro h
  have hc : ((sigma 1 (p ^ (2*j)) : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero h)
  rw [sigma_one_apply_prime_pow hprime, Nat.cast_sum] at hc
  push_cast at hc
  exact geom_odd_ne_zero p hx j hc

end SigmaFive.Modular

namespace SigmaFive

theorem odd_four_support {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    4 ≤ n.primeFactors.card := by
  apply odd_four_support_of_modular _ hn h
  apply exclude_triple_from_residues Modular.sigma_three_pow_mod_three
  · intro b hb
    obtain ⟨j, rfl⟩ := hb
    simpa [two_mul] using Modular.sigma_five_pow_mod_three j
  · intro c hc
    obtain ⟨j, rfl⟩ := hc
    simpa [two_mul] using Modular.sigma_eleven_pow_mod_three j
  · intro b hb
    obtain ⟨j, rfl⟩ := hb
    simpa [two_mul] using Modular.sigma_five_pow_mod_five j
  · intro p e hp he
    obtain ⟨j, rfl⟩ := he
    simpa [two_mul] using Modular.sigma_other_mod_five p j hp

end SigmaFive

namespace OMA.R_OeisA76495_conjecture_R1

open ArithmeticFunction

/-- The remaining odd case has at least four distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 4 ≤ n.primeFactors.card → sigma 1 n % n ≠ 5

/-- The remaining even case has at least three distinct prime factors and odd divisor sum. -/
def H2 : Prop :=
  ∀ n : ℕ, Even n → 3 ≤ n.primeFactors.card → Odd (sigma 1 n) → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → type_of% @OeisA76495.conjecture := by
  classical
  intro odd_case even_case
  unfold OeisA76495.a
  split_ifs with h
  · obtain ⟨n, hn, hmod⟩ := h
    have hcard := SigmaFive.three_le_primeFactors_card hn hmod
    exfalso
    rcases Nat.even_or_odd n with he | ho
    · have hodd : Odd (sigma 1 n) := by
        obtain ⟨v, hv⟩ := he
        have heq := Nat.mod_add_div (sigma 1 n) n
        rw [hmod, hv] at heq
        rw [hv]
        refine ⟨v * (sigma 1 (v+v) / (v+v)) + 2, ?_⟩
        nlinarith only [heq]
      exact even_case n he hcard hodd hmod
    · exact odd_case n ho (SigmaFive.odd_four_support ho hmod) hmod
  · rfl

end OMA.R_OeisA76495_conjecture_R1
