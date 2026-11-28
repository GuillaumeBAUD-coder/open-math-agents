import OMAStatements.S_oeis_a076481

namespace OMA.R_oeis_a076481_R1

private theorem a076481_geometric (q e : ℕ) (hq : q.Prime) :
    ArithmeticFunction.sigma 1 (q ^ e) * (q - 1) + 1 = q ^ (e + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
  simpa only [Nat.sub_add_cancel hq.one_lt.le] using geom_sum_mul_add (q - 1) (e + 1)

private theorem a076481_forward (p : ℕ) (h : ∃ e : ℕ, 2 * p + 1 = 3 ^ e) :
    ArithmeticFunction.sigma 1 (2 * p + 1) = 3 * p + 1 := by
  obtain ⟨e, he⟩ := h
  have hσ := a076481_geometric 3 e (by decide)
  rw [pow_succ, ← he] at hσ
  norm_num only [Nat.reduceSub] at hσ
  omega

private theorem a076481_three_and_prime (q a b : ℕ) (hq : q.Prime) (hq3 : q ≠ 3)
    (_ha : 0 < a) (hb : 0 < b) :
    2 * ArithmeticFunction.sigma 1 (3 ^ a * q ^ b) + 1 ≠ 3 * (3 ^ a * q ^ b) := by
  let S := ∑ i ∈ Finset.range (a + 1), (3 : ℕ) ^ i
  let T := ∑ i ∈ Finset.range b, q ^ i
  have h3q : Nat.Coprime 3 q := Nat.prime_three.coprime_iff_not_dvd.mpr fun hd ↦
    hq3 ((Nat.dvd_prime_two_le hq (by decide : 2 ≤ 3)).mp hd).symm
  have hcop : Nat.Coprime (3 ^ a) (q ^ b) := (h3q.pow_left a).pow_right b
  have hS : 2 * S + 1 = 3 * 3 ^ a := by
    simpa [S, pow_succ', Nat.mul_comm] using (geom_sum_mul_add (2 : ℕ) (a + 1))
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hT : T * (q - 1) + 1 = q ^ b := by
    simpa only [T, Nat.sub_add_cancel hq1] using geom_sum_mul_add (q - 1) b
  have hTpos : 0 < T := by
    have hle : q ^ (0 : ℕ) ≤ T :=
      Finset.single_le_sum (fun i _ ↦ Nat.zero_le (q ^ i)) (Finset.mem_range.mpr hb)
    simp only [pow_zero] at hle
    omega
  have hSsig : ArithmeticFunction.sigma 1 (3 ^ a) = S :=
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three
  have hTsig : ArithmeticFunction.sigma 1 (q ^ b) = T + q ^ b := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
  intro h
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hSsig, hTsig] at h
  have he : 2 * S * (T + q ^ b) + 1 = (3 * 3 ^ a) * q ^ b := by
    simpa only [S, T, Nat.mul_assoc] using h
  rw [← hS, Nat.mul_add, Nat.add_mul, Nat.one_mul] at he
  have heq : (2 * S) * T = (q - 1) * T := by
    rw [Nat.mul_comm (q - 1) T]
    omega
  have hcancel := Nat.eq_of_mul_eq_mul_right hTpos heq
  have hqeq : q = 3 * 3 ^ a := by omega
  exact hq3 ((Nat.dvd_prime_two_le hq (by decide : 2 ≤ 3)).mp ⟨3 ^ a, hqeq⟩).symm

private theorem a076481_two_factorization (n : ℕ) (hn : n ≠ 0) (hc : n.primeFactors.card = 2) :
    ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 0 < a ∧ 0 < b ∧ n = p ^ a * q ^ b := by
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
  have hpMem : p ∈ n.primeFactors := by simp [hset]
  have hqMem : q ∈ n.primeFactors := by simp [hset]
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hq := Nat.prime_of_mem_primeFactors hqMem
  have ha := hp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hpMem)
  have hb := hq.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hqMem)
  have hprod : n = p ^ n.factorization p * q ^ n.factorization q := by
    calc
      n = ∏ r ∈ n.primeFactors, r ^ n.factorization r := Nat.prod_primeFactors_pow_factorization hn
      _ = _ := by simp [hset, hpq]
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact ⟨p, q, n.factorization p, n.factorization q, hp, hq, hlt, ha, hb, hprod⟩
  · exact ⟨q, p, n.factorization q, n.factorization p, hq, hp, hgt, hb, ha,
      hprod.trans (Nat.mul_comm _ _)⟩

private theorem a076481_three_dvd_sigma_of_mod_two (n : ℕ) (htwo : n % 3 = 2) :
    3 ∣ ArithmeticFunction.sigma 1 n := by
  have residues (x y : ℕ) (hx : x < 3) (hy : y < 3) (hxy : (x * y) % 3 = 2) :
      (x + y) % 3 = 0 := by
    interval_cases x <;> interval_cases y <;> norm_num at *
  have hAdd (d : ℕ) (hd : d ∈ n.divisors) : 3 ∣ d + n / d := by
    have hDiv := (Nat.mem_divisors.mp hd).1
    have hProd : ((d % 3) * ((n / d) % 3)) % 3 = 2 := by
      rw [← Nat.mul_mod, Nat.mul_div_cancel' hDiv, htwo]
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod]
    exact residues _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hProd
  have hSum : 3 ∣ ∑ d ∈ n.divisors, (d + n / d) := Finset.dvd_sum hAdd
  have hSwap : (∑ d ∈ n.divisors, n / d) = ∑ d ∈ n.divisors, d :=
    Nat.sum_div_divisors n id
  rw [Finset.sum_add_distrib, hSwap, ← ArithmeticFunction.sigma_one_apply] at hSum
  omega

private theorem a076481_three_dvd (p : ℕ) (hp : Nat.Prime p)
    (h : ArithmeticFunction.sigma 1 (2 * p + 1) = 3 * p + 1) :
    3 ∣ 2 * p + 1 := by
  rcases (show (2 * p + 1) % 3 = 0 ∨ (2 * p + 1) % 3 = 1 ∨
      (2 * p + 1) % 3 = 2 by omega) with hzero | hone | htwo
  · exact Nat.dvd_of_mod_eq_zero hzero
  · have hpDiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    have hpEq : 3 = p := (Nat.dvd_prime_two_le hp (by decide)).mp hpDiv
    subst p
    have hSigma7 : ArithmeticFunction.sigma 1 7 = 8 := by
      rw [ArithmeticFunction.sigma_one_apply, (show Nat.Prime 7 by decide).divisors]
      norm_num
    change ArithmeticFunction.sigma 1 7 = 10 at h
    omega
  · have hdiv := a076481_three_dvd_sigma_of_mod_two _ htwo
    rw [h] at hdiv
    omega

private theorem a076481_cofactor_identity (a m : ℕ) (hm : 0 < m)
    (h : (3 ^ (a + 1) - 1) * ArithmeticFunction.sigma 1 m + 1 = 3 ^ (a + 1) * m) :
    (3 ^ (a + 1) - 1) * (ArithmeticFunction.sigma 1 m - m) + 1 = m := by
  let c := 3 ^ (a + 1) - 1
  have hx : 0 < (3 : ℕ) ^ (a + 1) := pow_pos (by decide) _
  have hc : c + 1 = 3 ^ (a + 1) := by dsimp [c]; omega
  have hs : m ≤ ArithmeticFunction.sigma 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d) (Nat.mem_divisors_self _ hm.ne')
  change c * ArithmeticFunction.sigma 1 m + 1 = 3 ^ (a + 1) * m at h
  change c * (ArithmeticFunction.sigma 1 m - m) + 1 = m
  have he :
      c * (ArithmeticFunction.sigma 1 m - m) + 1 + c * m = m + c * m := calc
    _ = c * ((ArithmeticFunction.sigma 1 m - m) + m) + 1 := by ring
    _ = c * ArithmeticFunction.sigma 1 m + 1 := by rw [Nat.sub_add_cancel hs]
    _ = 3 ^ (a + 1) * m := h
    _ = m + c * m := by rw [← hc]; ring
  omega

private theorem a076481_cofactor_divisor_bound (a m q : ℕ) (hm : 0 < m)
    (h : (3 ^ (a + 1) - 1) * ArithmeticFunction.sigma 1 m + 1 = 3 ^ (a + 1) * m)
    (hq : 1 < q) (hd : q ∣ m) : 3 ^ (a + 1) - 1 < q := by
  have he := a076481_cofactor_identity a m hm h
  obtain ⟨t, ht⟩ := hd
  have htpos : 0 < t := by
    by_contra hg
    have ht0 : t = 0 := by omega
    simp [ht, ht0] at hm
  have htlt : t < m := by
    rw [ht]
    have hmul : 2 * t ≤ q * t := Nat.mul_le_mul_right t (by omega)
    omega
  have ht_div : t ∣ m := ⟨q, by rw [ht, mul_comm q t]⟩
  have hsub : ({m, t} : Finset ℕ) ⊆ m.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.mem_divisors_self _ hm.ne'
    · exact Nat.mem_divisors.mpr ⟨ht_div, hm.ne'⟩
  have hsum : m + t ≤ ArithmeticFunction.sigma 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    calc
      _ = ∑ d ∈ ({m, t} : Finset ℕ), d := by simp [ne_of_gt htlt]
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have ht_le : t ≤ ArithmeticFunction.sigma 1 m - m := by omega
  by_contra! hq_le
  have hmul := Nat.mul_le_mul hq_le ht_le
  omega

private theorem a076481_cofactor_residue (a m : ℕ) (hc : Nat.Coprime 3 m)
    (h : (3 ^ (a + 1) - 1) * ArithmeticFunction.sigma 1 m + 1 = 3 ^ (a + 1) * m) :
    m % 3 = 1 := by
  have hNotDvd : ¬ 3 ∣ m := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp hc
  have hNotZero : m % 3 ≠ 0 := fun hz => hNotDvd (Nat.dvd_of_mod_eq_zero hz)
  by_contra hNotOne
  have hTwo : m % 3 = 2 := by omega
  have hSigma := a076481_three_dvd_sigma_of_mod_two m hTwo
  have hPower : 3 ∣ (3 : ℕ) ^ (a + 1) := dvd_pow_self _ (Nat.succ_ne_zero a)
  have hLeft := dvd_mul_of_dvd_right hSigma (3 ^ (a + 1) - 1)
  have hRight := dvd_mul_of_dvd_left hPower m
  rw [← h] at hRight
  omega

private theorem a076481_split_three (n : ℕ) (hn : 0 < n) (hd : 3 ∣ n) :
    ∃ a m : ℕ, 0 < a ∧ 0 < m ∧ Nat.Coprime 3 m ∧ n = 3 ^ a * m :=
  ⟨n.factorization 3, ordCompl[3] n,
    Nat.prime_three.factorization_pos_of_dvd hn.ne' hd, Nat.ordCompl_pos 3 hn.ne',
    Nat.coprime_ordCompl Nat.prime_three hn.ne',
    (Nat.ordProj_mul_ordCompl_eq_self n 3).symm⟩

private theorem a076481_cofactor_pair_bound (x q r b c : ℕ) (hx : 1 < x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r) (hqx : x < q) (hb : 0 < b)
    (hc : 0 < c)
    (h : (x - 1) * ArithmeticFunction.sigma 1 (q ^ b * r ^ c) + 1 = x * (q ^ b * r ^ c)) :
    r < x ^ 2 := by
  let A := ∑ i ∈ Finset.range b, (q : ℤ) ^ i
  let B := ∑ i ∈ Finset.range c, (r : ℤ) ^ i
  have hcop : Nat.Coprime (q ^ b) (r ^ c) := by
    have hbase : Nat.Coprime q r := hq.coprime_iff_not_dvd.mpr fun hd ↦
      (Nat.ne_of_lt hqr) ((Nat.dvd_prime_two_le hr hq.two_le).mp hd)
    exact (hbase.pow_left b).pow_right c
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply_prime_pow hq,
    ArithmeticFunction.sigma_one_apply_prime_pow hr] at h
  have hInt := congrArg (fun n : ℕ ↦ (n : ℤ)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hx.le, Nat.cast_one,
    Nat.cast_pow, Nat.cast_sum] at hInt
  have hqpow : (q : ℤ) ^ b = 1 + ((q : ℤ) - 1) * A := by
    have hgeom : A * ((q : ℤ) - 1) = (q : ℤ) ^ b - 1 := geom_sum_mul (q : ℤ) b
    nlinarith only [hgeom]
  have hrpow : (r : ℤ) ^ c = 1 + ((r : ℤ) - 1) * B := by
    have hgeom : B * ((r : ℤ) - 1) = (r : ℤ) ^ c - 1 := geom_sum_mul (r : ℤ) c
    nlinarith only [hgeom]
  have hsumq : (∑ i ∈ Finset.range (b + 1), (q : ℤ) ^ i) = 1 + (q : ℤ) * A := by
    rw [Finset.sum_range_succ]
    change A + (q : ℤ) ^ b = _
    rw [hqpow]
    ring
  have hsumr : (∑ i ∈ Finset.range (c + 1), (r : ℤ) ^ i) = 1 + (r : ℤ) * B := by
    rw [Finset.sum_range_succ]
    change B + (r : ℤ) ^ c = _
    rw [hrpow]
    ring
  rw [hsumq, hsumr, hqpow, hrpow] at hInt
  have hnormalized :
      ((x : ℤ) * ((x : ℤ) - 1) - ((q : ℤ) - x) * ((r : ℤ) - x)) * A * B =
        ((q : ℤ) - x) * A + ((r : ℤ) - x) * B := by
    nlinarith only [hInt]
  have hsumPos (p n : ℕ) (hn : 0 < n) : 0 < ∑ i ∈ Finset.range n, (p : ℤ) ^ i := by
    have hle : (p : ℤ) ^ (0 : ℕ) ≤ ∑ i ∈ Finset.range n, (p : ℤ) ^ i :=
      Finset.single_le_sum (fun i _ ↦ pow_nonneg (Nat.cast_nonneg p) i)
        (Finset.mem_range.mpr hn)
    simp only [pow_zero] at hle
    omega
  have hApos : 0 < A := hsumPos q b hb
  have hBpos : 0 < B := hsumPos r c hc
  have hqpos : 0 < (q : ℤ) - x := by omega
  have hrpos : 0 < (r : ℤ) - x := by omega
  have hcoef : 0 < (x : ℤ) * ((x : ℤ) - 1) - ((q : ℤ) - x) * ((r : ℤ) - x) := by
    by_contra! hnonpos
    have hprod : ((x : ℤ) * ((x : ℤ) - 1) - ((q : ℤ) - x) * ((r : ℤ) - x)) * A * B ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hnonpos hApos.le) hBpos.le
    rw [hnormalized] at hprod
    exact (add_pos (mul_pos hqpos hApos) (mul_pos hrpos hBpos)).not_ge hprod
  have hstep : (r : ℤ) - x ≤ ((q : ℤ) - x) * ((r : ℤ) - x) := by
    have hqone : (1 : ℤ) ≤ (q : ℤ) - x := by omega
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hqone hrpos.le
  have hcast : (r : ℤ) < (x : ℤ) ^ 2 := by nlinarith only [hcoef, hstep]
  exact_mod_cast hcast

private theorem a076481_normalized_identity (a m : ℕ) (hc : Nat.Coprime 3 m)
    (h : 2 * ArithmeticFunction.sigma 1 (3 ^ a * m) + 1 = 3 * (3 ^ a * m)) :
    (3 ^ (a + 1) - 1) * ArithmeticFunction.sigma 1 m + 1 = 3 ^ (a + 1) * m := by
  have hthree : 2 * ArithmeticFunction.sigma 1 (3 ^ a) + 1 = 3 ^ (a + 1) := by
    simpa [Nat.mul_comm] using a076481_geometric 3 a (by decide)
  have hsub : 3 ^ (a + 1) - 1 = 2 * ArithmeticFunction.sigma 1 (3 ^ a) := by omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left a)] at h
  calc
    _ = 2 * (ArithmeticFunction.sigma 1 (3 ^ a) * ArithmeticFunction.sigma 1 m) + 1 := by
      rw [hsub]
      ring
    _ = 3 * (3 ^ a * m) := h
    _ = _ := by rw [pow_succ]; ring

/-- Two distinct cofactor primes. For each positive a, both primes lie
strictly between x and x², where x = 3^(a+1). -/
def H1 : Prop :=
  ∀ a q r b c : ℕ,
    0 < a → q.Prime → r.Prime → q < r → 0 < b → 0 < c →
    let x := 3 ^ (a + 1)
    let m := q ^ b * r ^ c
    x < q → r < x ^ 2 → m % 3 = 1 → (x - 1) ∣ m - 1 →
    ((3 ^ a * m - 1) / 2).Prime →
    (x - 1) *
        ((∑ i ∈ Finset.range (b + 1), q ^ i) * (∑ i ∈ Finset.range (c + 1), r ^ i))
      + 1 ≠ x * m

/-- Cofactors with at least three distinct prime divisors, in the forced
congruence classes and with every prime divisor exceeding x. -/
def H2 : Prop :=
  ∀ a m : ℕ, 0 < a → 3 ≤ m.primeFactors.card →
    let x := 3 ^ (a + 1)
    m % 3 = 1 → (x - 1) ∣ m - 1 →
    (∀ q ∈ m.primeFactors, x < q) →
    ((3 ^ a * m - 1) / 2).Prime →
    (x - 1) * (∏ q ∈ m.primeFactors, ∑ i ∈ Finset.range (m.factorization q + 1), q ^ i)
      + 1 ≠ x * m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a076481.main := by
  intro hpair hmany p hp
  refine ⟨a076481_forward p, ?_⟩
  intro hs
  obtain ⟨a, m, ha, hm, hcop, hsplit⟩ :=
    a076481_split_three (2 * p + 1) (by omega) (a076481_three_dvd p hp hs)
  by_cases hm_one : m = 1
  · exact ⟨a, by simpa [hm_one] using hsplit⟩
  have he : 2 * ArithmeticFunction.sigma 1 (3 ^ a * m) + 1 = 3 * (3 ^ a * m) := by
    rw [← hsplit, hs]
    omega
  have hnot_dvd : ¬ 3 ∣ m := Nat.prime_three.coprime_iff_not_dvd.mp hcop
  by_cases hone : m.primeFactors.card = 1
  · obtain ⟨q, hqset⟩ := Finset.card_eq_one.mp hone
    have hqmem : q ∈ m.primeFactors := by simp [hqset]
    have hq := Nat.prime_of_mem_primeFactors hqmem
    have hqd := Nat.dvd_of_mem_primeFactors hqmem
    have hq3 : q ≠ 3 := fun h => hnot_dvd (h ▸ hqd)
    have hb := hq.factorization_pos_of_dvd hm.ne' hqd
    have hmeq : m = q ^ m.factorization q := calc
      m = ∏ t ∈ m.primeFactors, t ^ m.factorization t := Nat.prod_primeFactors_pow_factorization hm.ne'
      _ = _ := by rw [hqset, Finset.prod_singleton]
    rw [hmeq] at he
    exact (a076481_three_and_prime q a _ hq hq3 ha hb he).elim
  have hcard_lower : 2 ≤ m.primeFactors.card := by
    have hpos := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega : 1 < m))
    omega
  have hnorm := a076481_normalized_identity a m hcop he
  have hmod := a076481_cofactor_residue a m hcop hnorm
  have hcong : 3 ^ (a + 1) - 1 ∣ m - 1 := by
    use ArithmeticFunction.sigma 1 m - m
    have h := a076481_cofactor_identity a m hm hnorm
    omega
  have hprime : ((3 ^ a * m - 1) / 2).Prime := by
    rw [← hsplit, show (2 * p + 1 - 1) / 2 = p by omega]
    exact hp
  have hlarge : ∀ q ∈ m.primeFactors, 3 ^ (a + 1) < q := by
    intro q hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hqlt := a076481_cofactor_divisor_bound a m q hm hnorm
      (Nat.prime_of_mem_primeFactors hq).one_lt hqd
    have hne : q ≠ 3 ^ (a + 1) := by
      intro hqpow
      have h3q : 3 ∣ q := hqpow ▸ dvd_pow_self 3 (Nat.succ_ne_zero a)
      exact hnot_dvd (h3q.trans hqd)
    have hx : 0 < (3 : ℕ) ^ (a + 1) := pow_pos (by decide) _
    omega
  by_cases htwo : m.primeFactors.card = 2
  · obtain ⟨q, r, b, c, hq, hr, hqr, hb, hc, hm_eq⟩ := a076481_two_factorization m hm.ne' htwo
    have hqd : q ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_left (dvd_pow_self q hb.ne') _
    have hqM : q ∈ m.primeFactors := hq.mem_primeFactors hqd hm.ne'
    have hq_gt := hlarge q hqM
    have hnorm' : (3 ^ (a + 1) - 1) * ArithmeticFunction.sigma 1 (q ^ b * r ^ c) + 1 =
        3 ^ (a + 1) * (q ^ b * r ^ c) := by simpa only [hm_eq] using hnorm
    have hx : 1 < (3 : ℕ) ^ (a + 1) := one_lt_pow₀ (by decide) (Nat.succ_ne_zero a)
    have hr_lt : r < (3 ^ (a + 1)) ^ 2 :=
      a076481_cofactor_pair_bound _ q r b c hx hq hr hqr hq_gt hb hc hnorm'
    have hcopQR : Nat.Coprime (q ^ b) (r ^ c) :=
      (hq.coprime_iff_not_dvd.mpr (fun hd => hqr.ne ((Nat.dvd_prime_two_le hr hq.two_le).mp hd))).pow b c
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopQR,
      ArithmeticFunction.sigma_one_apply_prime_pow hq, ArithmeticFunction.sigma_one_apply_prime_pow hr] at hnorm'
    exact False.elim ((hpair a q r b c ha hq hr hqr hb hc hq_gt hr_lt
      (by simpa only [hm_eq] using hmod) (by simpa only [hm_eq] using hcong)
      (by simpa only [hm_eq] using hprime)) hnorm')
  · have hprod : ArithmeticFunction.sigma 1 m =
        ∏ q ∈ m.primeFactors, ∑ i ∈ Finset.range (m.factorization q + 1), q ^ i := by
      simpa only [mul_one] using
        ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hm.ne'
    exact False.elim ((hmany a m ha (by omega) hmod hcong hlarge hprime)
      (by simpa only [hprod] using hnorm))

end OMA.R_oeis_a076481_R1
