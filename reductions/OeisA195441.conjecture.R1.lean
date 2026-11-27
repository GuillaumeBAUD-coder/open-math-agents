import FormalConjectures.OEIS.«195441»

/-! # Digit-sum reductions for the radical of the Bernoulli coefficient denominator

The required direction of Kellner and Sondow's digit-sum formula follows
from Lucas's theorem and von Staudt--Clausen (arXiv:1705.03857, Theorem 2). The finite checks, the classification of even solutions, and
the exclusions for powers of three and five are unconditional.
-/

namespace OMA.R_OeisA195441_conjecture_R1

private theorem digit_sum_split (p n : ℕ) (hp : 1 < p) :
    (p.digits n).sum = n%p + (p.digits (n/p)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hl
  · simp
  · rw [Nat.digits_eq_cons_digits_div hp hl.ne', List.sum_cons]

/-- Select exactly s units of digit mass from n, without a borrow.
Lucas's theorem keeps the resulting binomial coefficient prime to p. -/
theorem choose_digit_mass {p : ℕ} (hp : p.Prime) (n s : ℕ)
    (hs : s ≤ (p.digits n).sum) :
    ∃ m ≤ n, (p.digits m).sum = s ∧ ¬ p ∣ n.choose m := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hs
      exact ⟨0, by simp [hs, hp.not_dvd_one]⟩
    let a := min s (n%p)
    have ha : a ≤ n%p := min_le_right ..
    have ha' : a ≤ s := min_le_left ..
    have hap : a < p := ha.trans_lt (Nat.mod_lt _ hp.pos)
    rw [digit_sum_split p n hp.one_lt] at hs
    obtain ⟨b,hb,hbs,hbc⟩ := ih (n/p) (Nat.div_lt_self hn hp.one_lt) (s-a) (by dsimp [a]; omega)
    let m := a+p*b
    have hm : m%p = a := by simp [m, Nat.mod_eq_of_lt hap]
    have hdiv : m/p = b := by simp [m, Nat.add_mul_div_left, hp.pos, Nat.div_eq_of_lt hap]
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨m, ?_, ?_, ?_⟩
    · exact (Nat.add_le_add ha (Nat.mul_le_mul_left p hb)).trans_eq (Nat.mod_add_div n p)
    · rw [digit_sum_split p m hp.one_lt, hm, hdiv, hbs]
      omega
    · have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := m)
      rw [hm,hdiv] at hl
      intro hd
      have hmul := (hl.dvd_iff (dvd_refl p)).mp hd
      exact (hp.dvd_mul.mp hmul).elim
        ((hp.coprime_iff_not_dvd).mp (hp.coprime_choose_of_lt (Nat.mod_lt _ hp.pos) ha)) hbc

/-- In the von Staudt--Clausen sum all reciprocal primes other than p
have a common denominator coprime to p. -/
theorem prime_dvd_bernoulli_den {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hd : p-1 ∣ 2*k) : p ∣ (bernoulli (2*k)).den := by
  classical
  let S := (Finset.range (2*k+2)).filter (fun q : ℕ => q.Prime ∧ q-1 ∣ 2*k)
  have mem : p ∈ S := by
    have hle := Nat.le_of_dvd (show 0 < 2*k by omega) hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hd⟩
  let rest := ∑ q ∈ S.erase p, (1:ℚ)/q
  have hc : rest.den.Coprime p := by
    apply Nat.Coprime.of_dvd_left (Finset.Rat.den_sum_dvd_prod_den _ _)
    apply Nat.Coprime.prod_left
    intro q hq
    obtain ⟨hne,hq'⟩ := Finset.mem_erase.mp hq
    change q ∈ (Finset.range (2*k+2)).filter (fun q : ℕ => q.Prime ∧ q-1 ∣ 2*k) at hq'
    have hprime : q.Prime := (Finset.mem_filter.mp hq').2.1
    rw [show ((1:ℚ)/q).den = q by simp [hprime.ne_zero]]
    exact (Nat.coprime_primes hprime hp).mpr hne
  obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen k
  change (z:ℚ) = bernoulli (2*k) + ∑ q ∈ S, (1:ℚ)/q at hz
  rw [← Finset.sum_erase_add _ _ mem] at hz
  have hrat : (1:ℚ)/p = z - (bernoulli (2*k) + rest) := by dsimp [rest]; linarith
  have hdvd := Rat.add_den_dvd (bernoulli (2*k)) rest
  have hden := congrArg Rat.den hrat
  simp [hp.ne_zero] at hden
  rw [← hden] at hdvd
  exact (hp.dvd_mul.mp hdvd).resolve_right (hp.coprime_iff_not_dvd.mp hc.symm)

private theorem prime_dvd_scaled_den {c p : ℕ} (q : ℚ) (hp : p.Prime)
    (hc : ¬p ∣ c) (hd : p ∣ q.den) : p ∣ ((c:ℚ)*q).den := by
  have hc0 : c ≠ 0 := fun he => hc (he ▸ dvd_zero _)
  have hh := Rat.mul_den_dvd ((c:ℚ)*q) (1/(c:ℚ))
  have hx : (c:ℚ)*q*(1/(c:ℚ)) = q := by field_simp
  rw [hx, show ((1:ℚ)/(c:ℚ)).den = c by simp [hc0]] at hh
  exact (hp.dvd_mul.mp (hd.trans hh)).resolve_right hc

/-- A prime detected by the digit sum occurs in a nonconstant coefficient. -/
theorem digit_sum_dvd_denominator {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hs : p ≤ (p.digits n).sum) : p ∣ OeisA195441.a (n-1) := by
  have hp2 := hp.two_le
  obtain ⟨m,hm,hmass,hunit⟩ := choose_digit_mass hp n (p-1) (by omega)
  have hlt : m < n := by
    by_contra! hh
    have eqn : m = n := by omega
    rw [eqn] at hmass
    omega
  have hmpos : 0 < m := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hmass
    omega
  have hden : p ∣ (bernoulli m).den := by
    by_cases htwo : p = 2
    · subst p
      by_cases hm1 : m = 1
      · subst m
        decide +kernel
      · have hme : 2 ∣ m := by
          by_contra hh
          have hmod : m % 2 = 1 := by omega
          rw [digit_sum_split 2 m (by decide), hmod] at hmass
          have hz : (Nat.digits 2 (m/2)).sum = 0 := by omega
          by_cases hq : m/2 = 0
          · omega
          · have he := Nat.getLast_digit_ne_zero 2 hq
            have hall := List.sum_eq_zero_iff.mp hz
            exact he (hall _ (List.getLast_mem _))
        obtain ⟨k,hk⟩ := hme
        rw [hk]
        exact prime_dvd_bernoulli_den hp (by omega) (by simp)
    · have h3 : 2 < p := by omega
      have hbase : p % (p-1) = 1 := by
        conv_lhs => lhs; rw [show p = 1+(p-1) by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hc := Nat.modEq_digits_sum (p-1) p hbase m
      rw [hmass] at hc
      have hd : p-1 ∣ m := Nat.dvd_of_mod_eq_zero (Eq.trans hc (Nat.mod_self _))
      have hpar := hp.eq_two_or_odd.resolve_left htwo
      have heven : 2 ∣ m := dvd_trans (show 2 ∣ p-1 by omega) hd
      obtain ⟨k,hk⟩ := heven
      rw [hk] at hd ⊢
      exact prime_dvd_bernoulli_den hp (by omega) hd
  rw [OeisA195441.a, show n-1+1 = n by omega]
  have hcoeff := Finset.dvd_lcm (f := fun k =>
    ((n.choose k : ℚ) * bernoulli (n-k)).den) (Finset.mem_Icc.mpr
      (show 1 ≤ n-m ∧ n-m ≤ n by omega))
  apply Dvd.dvd.trans _ hcoeff
  rw [Nat.choose_symm hm, show n-(n-m) = m by omega]
  exact prime_dvd_scaled_den _ hp hunit hden

private theorem ofDigits_zero_sum {b : ℕ} (L : List ℕ) (h : L.sum = 0) :
    Nat.ofDigits b L = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.sum_cons, Nat.add_eq_zero_iff] at h
    simp [Nat.ofDigits_cons, h.1, ih h.2]

private theorem power_of_one_digit_sum {b n : ℕ} (h : (b.digits n).sum = 1) :
    ∃ e : ℕ, n = b ^ e := by
  suffices aux : ∀ L : List ℕ, L.sum = 1 → ∃ e : ℕ, Nat.ofDigits b L = b ^ e by
    simpa only [Nat.ofDigits_digits] using aux (b.digits n) h
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.sum_cons, Nat.ofDigits_cons]
    intro hx
    by_cases h0 : x = 0
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨e + 1, by simp [h0, he, pow_succ']⟩
    · exact ⟨0, by rw [ofDigits_zero_sum L (by omega)]; simp; omega⟩

/-- With digit sum at most two and a nonzero units digit, a multi-digit
number is one more than a power of the base. -/
private theorem one_add_power {p n : ℕ} (hp : 1 < p) (hn : p ≤ n)
    (hu : n % p ≠ 0) (hs : (p.digits n).sum ≤ 2) :
    ∃ j : ℕ, n = 1 + p ^ j := by
  rw [Nat.digits_eq_cons_digits_div hp (by omega), List.sum_cons] at hs
  have hq : 0 < n / p := Nat.div_pos hn (by omega)
  have nz : (p.digits (n / p)).sum ≠ 0 := by
    intro hz
    have hh := ofDigits_zero_sum (b := p) _ hz
    rw [Nat.ofDigits_digits] at hh
    omega
  obtain ⟨e, he⟩ := power_of_one_digit_sum (show (p.digits (n/p)).sum = 1 by omega)
  refine ⟨e+1, ?_⟩
  have hh := Nat.mod_add_div n p
  rw [pow_succ', ← he]
  omega

private theorem two_pow_mod_seven (e : ℕ) :
    2 ^ e % 7 = 1 ∨ 2 ^ e % 7 = 2 ∨ 2 ^ e % 7 = 4 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> decide

private theorem three_pow_mod_eight (e : ℕ) :
    3 ^ e % 8 = 1 ∨ 3 ^ e % 8 = 3 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

private theorem seven_pow_mod_sixteen (e : ℕ) :
    7 ^ e % 16 = 1 ∨ 7 ^ e % 16 = 7 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

/-- No even integer above eight can pass the three prime tests. -/
theorem exclude_even {n : ℕ} (hn : 8 < n) (he : 2 ∣ n)
    (h : ∀ p : ℕ, p.Prime → p ≤ (p.digits n).sum → p ∣ n+1) : False := by
  have h2 : (Nat.digits 2 n).sum < 2 := by
    by_contra! hge
    have := h 2 (by decide) hge
    omega
  have hpos : (Nat.digits 2 n).sum ≠ 0 := by
    intro hz
    have hh := ofDigits_zero_sum (b := 2) _ hz
    rw [Nat.ofDigits_digits] at hh
    omega
  obtain ⟨e, rfl⟩ := power_of_one_digit_sum (show (Nat.digits 2 n).sum = 1 by omega)
  have ee : 4 ≤ e := by
    by_contra! hsmall
    interval_cases e <;> contradiction
  have h16 : 16 ∣ 2 ^ e := by exact pow_dvd_pow 2 ee
  by_cases h3 : 3 ∣ 2 ^ e + 1
  · have hm := two_pow_mod_seven e
    have h7 : (Nat.digits 7 (2 ^ e)).sum < 7 := by
      by_contra! hh
      have hd := h 7 (by decide) hh
      omega
    have hc := Nat.modEq_digits_sum 6 7 (by decide) (2 ^ e)
    change 2 ^ e % 6 = _ at hc
    obtain ⟨j, hj⟩ := one_add_power (p := 7) (n := 2^e) (by decide) (by omega)
      (by omega) (by omega)
    have := seven_pow_mod_sixteen j
    omega
  · have hsmall : (Nat.digits 3 (2^e)).sum < 3 := by
      by_contra! hh
      exact h3 (h 3 (by decide) hh)
    have hu : 2 ^ e % 3 ≠ 0 := by
      exact fun hh => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hh))
    obtain ⟨j, hj⟩ := one_add_power (p := 3) (n := 2^e) (by decide) (by omega) hu (by omega)
    have := three_pow_mod_eight j
    omega


private theorem digit_sum_pos {b n : ℕ} (hn : 0 < n) : 0 < (b.digits n).sum := by
  by_contra! hz
  have hh := ofDigits_zero_sum (b := b) _ (Nat.eq_zero_of_le_zero hz)
  rw [Nat.ofDigits_digits] at hh
  omega

/-- A modular period starting at exponent b persists after every further
multiplication by a. This allows prime and digit-base congruences to be
tested on a finite table of exponents. -/
private theorem power_period {a b T M : ℕ} (step : a^(b+T) ≡ a^b [MOD M]) (r t : ℕ) :
    a^(b+r+T*t) ≡ a^(b+r) [MOD M] := by
  induction t with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; rfl
  | succ t ih =>
    have hs := step.mul_right (a^(r+T*t))
    rw [← pow_add, ← pow_add, ← Nat.add_assoc b r (T*t)] at hs
    simpa only [show b+r+T*(t+1) = b+T+(r+T*t) by ring] using hs.trans ih

/-- If n has more than one base-p digit, its digit sum strictly exceeds
the units digit. Its residue modulo p-1 can then force the sum past p-1. -/
private theorem units_witness {p n : ℕ} (hp : 2 < p) (hn : p ≤ n)
    (hpos : 0 < n % (p-1)) (hle : n % (p-1) ≤ n % p) : p ≤ (p.digits n).sum := by
  have hc : n % (p-1) = (p.digits n).sum % (p-1) := by
    apply Nat.modEq_digits_sum
    conv_lhs => lhs; rw [show p = 1 + (p-1) by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hu : n % p < (p.digits n).sum := by
    rw [Nat.digits_eq_cons_digits_div (by omega : 1 < p) (by omega), List.sum_cons]
    exact Nat.lt_add_of_pos_right (digit_sum_pos (b := p) (Nat.div_pos hn (by omega)))
  by_contra! hsmall
  have hs : (p.digits n).sum < p-1 := by
    by_contra! hh
    have hh' : (p.digits n).sum = p-1 := by omega
    rw [hh', Nat.mod_self] at hc
    omega
  rw [Nat.mod_eq_of_lt hs] at hc
  omega

private theorem power_witness_of_table {a b T M P e : ℕ} (ha : 0 < a) (hT : 0 < T)
    (step : a^(b+T) ≡ a^b [MOD M])
    (table : ∀ r : Fin T, ∃ i : Fin P, let p := i.val
      p.Prime ∧ 2 < p ∧ p ≤ a^b ∧ p ∣ M ∧ (p-1) ∣ M ∧ ¬p ∣ a^(b+r.val)+1 ∧
      0 < a^(b+r.val) % (p-1) ∧ a^(b+r.val) % (p-1) ≤ a^(b+r.val) % p)
    (he : b ≤ e) : ∃ p : ℕ, p.Prime ∧ ¬p ∣ a^e+1 ∧ p ≤ (p.digits (a^e)).sum := by
  let r : Fin T := ⟨(e-b)%T, Nat.mod_lt _ hT⟩
  have ee : b+r.val+T*((e-b)/T) = e := by
    have hh := Nat.mod_add_div (e-b) T
    dsimp [r]
    omega
  have heq := power_period step r.val ((e-b)/T)
  rw [ee] at heq
  obtain ⟨i,hp,hp2,hpb,hd,hd',hno,hpos,hle⟩ := table r
  have hu : a^e % i.val = a^(b+r.val) % i.val := Nat.ModEq.of_dvd hd heq
  have hv : a^e % (i.val-1) = a^(b+r.val) % (i.val-1) := Nat.ModEq.of_dvd hd' heq
  exact ⟨i.val,hp, fun h => hno (((heq.add_right 1).dvd_iff hd).mp h),
    units_witness hp2 (hpb.trans (Nat.pow_le_pow_right ha he)) (hv ▸ hpos) (hv ▸ hu ▸ hle)⟩

/-- The five bases 5, 7, 13, 41, 73 cover exponents modulo 24. -/
theorem three_power_witness {e : ℕ} (he : 4 ≤ e) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ 3^e+1 ∧ p ≤ (p.digits (3^e)).sum :=
  power_witness_of_table (b := 4) (T := 24) (M := 98050680) (P := 74)
    (by decide) (by decide) (by decide) (by decide +kernel) he

/-- The two bases 7 and 13 cover powers of five modulo period 12. -/
theorem five_power_witness {e : ℕ} (he : 2 ≤ e) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ 5^e+1 ∧ p ≤ (p.digits (5^e)).sum :=
  power_witness_of_table (b := 2) (T := 12) (M := 1092) (P := 14)
    (by decide) (by decide) (by decide) (by decide +kernel) he

/-- A numeral with digit sum three is a sum of three powers of the base,
allowing repetitions of exponents. -/
private theorem three_powers {b n : ℕ} (hs : (b.digits n).sum = 3) :
    ∃ i j k : ℕ, n = b^i + b^j + b^k := by
  have expand (L : List ℕ) : ∃ E : List ℕ, E.length = L.sum ∧
      (E.map (fun i => b^i)).sum = Nat.ofDigits b L := by
    induction L with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons d L ih =>
      obtain ⟨E,hlen,hval⟩ := ih
      refine ⟨List.replicate d 0 ++ E.map (· + 1), by simp [hlen], ?_⟩
      simp only [List.map_append, List.map_replicate, pow_zero, List.sum_append,
        List.sum_replicate, smul_eq_mul, Nat.mul_one, Nat.ofDigits_cons, List.map_map]
      congr 1
      rw [← hval]
      clear hlen hval
      induction E with
      | nil => simp
      | cons i E ih => simp_all [pow_succ', Nat.mul_add, Function.comp_def]
  obtain ⟨E,hlen,hval⟩ := expand (b.digits n)
  rw [hs] at hlen
  rw [Nat.ofDigits_digits] at hval
  obtain ⟨i,j,k,rfl⟩ : ∃ i j k, E = [i,j,k] := by
    rcases E with _|⟨i,E⟩ <;> simp_all
    rcases E with _|⟨j,E⟩ <;> simp_all
    rcases E with _|⟨k,E⟩ <;> simp_all
  exact ⟨i,j,k,by simpa [Nat.add_assoc] using hval.symm⟩

/-- If an odd n has composite n+2, a prime factor of n+2 is a witness:
the units digit is p-2 and the remaining positive even quotient has
positive even digit sum in this odd base. -/
theorem prime_neighbor {n : ℕ} (hn : 1 ≤ n) (ho : n % 2 = 1)
    (h : ∀ p : ℕ, p.Prime → p ≤ (p.digits n).sum → p ∣ n+1) : (n+2).Prime := by
  by_contra hnp
  let p := (n+2).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ n+2 := Nat.minFac_dvd _
  have hl : p < n+2 := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  obtain ⟨t,ht⟩ := hd
  have hodd : p % 2 = 1 ∧ t % 2 = 1 := by
    have hm := congrArg (· % 2) ht
    rw [Nat.mul_mod] at hm
    rcases Nat.mod_two_eq_zero_or_one p with h0|h1 <;>
      rcases Nat.mod_two_eq_zero_or_one t with ht0|ht1 <;> simp_all <;> omega
  have ht2 : 1 < t := by
    by_contra! hh
    interval_cases t <;> simp_all
  have hp2 := hp.two_le
  have hn' : n = (p-2) + p*(t-1) := by
    have ht' : t = (t-1)+1 := by omega
    nth_rw 1 [ht'] at ht
    rw [Nat.mul_add, Nat.mul_one] at ht
    omega
  have hs : p ≤ (p.digits n).sum := by
    rw [hn', Nat.digits_add p hp.one_lt _ _ (by omega) (Or.inr (by omega)), List.sum_cons]
    have hpos := digit_sum_pos (b := p) (n := t-1) (by omega)
    have hc := Nat.modEq_digits_sum 2 p hodd.1 (t-1)
    change (t-1)%2 = (p.digits (t-1)).sum%2 at hc
    omega
  have hd1 := h p hp hs
  have hd2 : p ∣ n+1+1 := ht ▸ dvd_mul_right p t
  have hone : p ∣ 1 := (Nat.dvd_add_right hd1).mp hd2
  exact hp.not_dvd_one hone

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Compute the bounded classification with the pinned coefficient LCM. The
lookup table uses the positive B₁ convention of bernoulli'. The kernel checks
its recurrence before the table is used for any coefficient. -/
theorem finite_cases (n : ℕ) (hn : n ≤ 59) :
    (1 ≤ n ∧ OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1)) ↔
      n ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ) := by
  let B : ℕ → ℚ := fun j => ([1, 1/2, 1/6, 0, -1/30, 0,
    1/42, 0, -1/30, 0, 5/66, 0,
    -691/2730, 0, 7/6, 0, -3617/510, 0,
    43867/798, 0, -174611/330, 0, 854513/138, 0,
    -236364091/2730, 0, 8553103/6, 0, -23749461029/870, 0,
    8615841276005/14322, 0, -7709321041217/510, 0, 2577687858367/6, 0,
    -26315271553053477373/1919190, 0, 2929993913841559/6, 0, -261082718496449122051/13530, 0,
    1520097643918070802691/1806, 0, -27833269579301024235023/690, 0, 596451111593912163277961/282, 0,
    -5609403368997817686249127547/46410, 0, 495057205241079648212477525/66, 0, -801165718135489957347924991853/1590, 0,
    29149963634884862421418123812691/798, 0, -2479392929313226753685415739663229/870, 0, 84483613348880041862046775994036021/354] : List ℚ).getD j 0
  have recurrence : ∀ j : Fin 59, B j = 1 - ∑ k : Fin j.val,
      (Nat.fast_choose j k : ℚ) / (j.val - k.val + 1) * B k := by
    dsimp only [B]
    decide +kernel
  have correct (j : ℕ) (hj : j < 59) : bernoulli' j = B j := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rw [bernoulli'_def', recurrence ⟨j,hj⟩]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.choose_eq_fast_choose, ih k k.isLt (by omega)]
  have tableCheck : ∀ i : Fin 60,
      (1 ≤ i.val ∧ (Finset.Icc 1 i.val).lcm (fun k =>
        ((Nat.fast_choose i k : ℚ) * ((-1)^(i.val-k) * B (i.val-k))).den) =
          ∏ p ∈ (i.val+1).primeFactors, p) ↔
      i.val ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ) := by
    dsimp only [B]
    decide +kernel
  by_cases hn0 : n = 0
  · subst n
    simp
  have hh : n-1+1 = n := by omega
  rw [OeisA195441.a, hh, Nat.radical_eq_prod_primeFactors]
  have hlcm : (Finset.Icc 1 n).lcm (fun k => ((n.choose k : ℚ) * bernoulli (n-k)).den) =
      (Finset.Icc 1 n).lcm (fun k =>
        ((Nat.fast_choose n k : ℚ) * ((-1)^(n-k) * B (n-k))).den) := by
    apply Finset.lcm_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simp only [Nat.choose_eq_fast_choose, bernoulli, correct (n-k) (by omega)]
  rw [hlcm]
  exact tableCheck ⟨n,by omega⟩

theorem solution_forces_prime_divisors {n : ℕ} (hn : 0 < n)
    (eqn : OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1))
    {p : ℕ} (hp : p.Prime) (hs : p ≤ (p.digits n).sum) : p ∣ n+1 := by
  have hd := digit_sum_dvd_denominator hn hp hs
  rw [eqn] at hd
  exact hd.trans UniqueFactorizationMonoid.radical_dvd_self

/-- Eight is the only positive even solution of the original coefficient equation. -/
theorem even_solution_iff {n : ℕ} (hn : 0 < n) (he : 2 ∣ n) :
    OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1) ↔ n = 8 := by
  constructor
  · intro eqn
    by_cases hs : n ≤ 59
    · have hm := (finite_cases n hs).mp ⟨hn,eqn⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    · exact (exclude_even (by omega) he (fun _ => solution_forces_prime_divisors hn eqn)).elim
  · rintro rfl
    exact ((finite_cases 8 (by decide)).mpr (by decide)).2

/-- Sparse case. Find a digit-sum witness for a sum of three powers of five
lying two below a prime, on the remaining residue class modulo three. -/
def H1 : Prop := ∀ i j k : ℕ, let n := 5^i + 5^j + 5^k
  59 < n → n % 3 = 2 → (n+2).Prime →
  ∃ p : ℕ, p.Prime ∧ ¬p ∣ n+1 ∧ p ≤ (p.digits n).sum

/-- Progression case. Find a digit-sum witness two below a prime that is
one modulo thirty. -/
def H2 : Prop := ∀ q : ℕ, q.Prime → 61 < q → q % 30 = 1 →
  ∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum

theorem main : H1 → H2 → type_of% @OeisA195441.conjecture := by
  intro sparse progression
  ext n
  change (1 ≤ n ∧ OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1)) ↔
    n ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ)
  by_cases hs : n ≤ 59
  · exact finite_cases n hs
  constructor
  · rintro ⟨hn,eqn⟩
    exfalso
    have h (p : ℕ) := @solution_forces_prime_divisors n hn eqn p
    have ho : n % 2 = 1 := by
      by_contra hh
      have := (even_solution_iff hn (by omega)).mp eqn
      omega
    have neighbor := prime_neighbor hn ho h
    have h3 : 3 ∣ n+1 := by
      by_contra hnd
      have hd : (Nat.digits 3 n).sum < 3 := by
        by_contra! hh
        exact hnd (h 3 (by decide) hh)
      have hm := Nat.modEq_digits_sum 2 3 (by decide) n
      change n % 2 = (Nat.digits 3 n).sum % 2 at hm
      obtain ⟨e,he⟩ := power_of_one_digit_sum (show (Nat.digits 3 n).sum = 1 by omega)
      subst n
      have he4 : 4 ≤ e := by
        by_contra! hh
        interval_cases e <;> contradiction
      obtain ⟨p,hp,hnd',hds⟩ := three_power_witness he4
      exact hnd' (h p hp hds)
    by_cases h5 : 5 ∣ n+1
    · obtain ⟨p,hp,hnp,hds⟩ := progression (n+2) neighbor (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hds
      exact hnp (by simpa using h p hp hds)
    · have hd : (Nat.digits 5 n).sum < 5 := by
        by_contra! hh
        exact h5 (h 5 (by decide) hh)
      have hm := Nat.modEq_digits_sum 2 5 (by decide) n
      change n % 2 = (Nat.digits 5 n).sum % 2 at hm
      rcases (show (Nat.digits 5 n).sum = 1 ∨ (Nat.digits 5 n).sum = 3 by omega) with h1|hthree
      · obtain ⟨e,he⟩ := power_of_one_digit_sum h1
        subst n
        have he2 : 2 ≤ e := by
          by_contra! hh
          interval_cases e <;> contradiction
        obtain ⟨p,hp,hnp,hds⟩ := five_power_witness he2
        exact hnp (h p hp hds)
      · obtain ⟨i,j,k,rfl⟩ := three_powers hthree
        obtain ⟨p,hp,hnp,hds⟩ := sparse i j k (by omega) (by omega) neighbor
        exact hnp (h p hp hds)
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega

end OMA.R_OeisA195441_conjecture_R1
