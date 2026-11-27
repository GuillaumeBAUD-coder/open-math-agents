import FormalConjectures.OEIS.«76495»
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases

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

namespace OMA.R_OeisA76495_conjecture_R1

open ArithmeticFunction

/-- The remaining odd case has at least three distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n.primeFactors.card → sigma 1 n % n ≠ 5

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
    · exact odd_case n ho hcard hmod
  · rfl

end OMA.R_OeisA76495_conjecture_R1
