import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1

-- Step Erdos977.erdos_977.variants.stewart.R1.H2: hypothesis H2 of reduction Erdos977.erdos_977.variants.stewart.R1
-- Credit: @ptc-prover-bot

/-! `2^φ(n) ≤ 4n · ∏_{p | 2^n - 1, p ≡ 1 (mod n)} p^{v_p(2^n - 1)}` for `n ≥ 2`, via `Φ = Φ_n(2)`:
* `2^φ(n) ≤ 4Φ`: Möbius inversion of `∑_{d|n} (log Φ_d(2) - φ(d) log 2) = log(1 - 2^{-n})` gives
  `log Φ - φ(n) log 2 ≥ ∑_{d|n} log(1 - 2^{-d}) ≥ -log 4` (as `μ(n/d) g(d) ≥ g(d)` for `g ≤ 0`, and
  `∑_{d≥1} -log(1 - 2^{-d}) ≤ log 2 + log(4/3) + 2/7 ≤ log 4`).
* a prime `q ∣ Φ` with `q ∤ n` has order `n` modulo `q`, so `q ≡ 1 (mod n)`, and `v_q(Φ) ≤ v_q(2^n - 1)`;
* for `q ∣ n`: `Φ ∣ 1 + x + ⋯ + x^{q-1}` (`x = 2^{n/q}`), whose `q`-adic valuation is at most `1`
  (lifting the exponent), so `v_q(Φ) ≤ v_q(n)` and that part of `Φ` divides `n`. -/

open Polynomial Real Finset

namespace OMA.Stewart977

/-- `-log(1 - 2^{-d})` summed over `d = 1..N` is at most `log(8/3) + 2/7 - (8/7) 2^{-N}` (`N ≥ 2`). -/
lemma neg_log_term (d : ℕ) (hd : 3 ≤ d) :
    -log (1 - (2:ℝ)⁻¹ ^ d) ≤ 8 / 7 * (2:ℝ)⁻¹ ^ d := by
  set t : ℝ := (2:ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have ht8 : t ≤ 1 / 8 := by
    rw [ht]
    calc (2:ℝ)⁻¹ ^ d ≤ (2:ℝ)⁻¹ ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
      _ = 1 / 8 := by norm_num
  have h1 : 0 < 1 - t := by linarith
  -- log x ≥ 1 - 1/x
  have hlog : 1 - 1 / (1 - t) ≤ log (1 - t) := by
    have := Real.add_one_le_exp (-log (1 - t))
    rw [Real.exp_neg, Real.exp_log h1] at this
    have e : 1 / (1 - t) = (1 - t)⁻¹ := one_div _
    rw [e]; linarith
  have h2 : 1 / (1 - t) - 1 ≤ 8 / 7 * t := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

lemma sum_neg_log (N : ℕ) (hN : 2 ≤ N) :
    ∑ d ∈ Icc 1 N, -log (1 - (2:ℝ)⁻¹ ^ d) ≤ log (8 / 3) + 2 / 7 - 8 / 7 * (2:ℝ)⁻¹ ^ N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show Icc 1 2 = {1, 2} by decide, sum_pair (by norm_num)]
    have e : log (8 / 3) = -log (1 - (2:ℝ)⁻¹ ^ 1) + -log (1 - (2:ℝ)⁻¹ ^ 2) := by
      rw [← log_inv, ← log_inv, ← log_mul (by norm_num) (by norm_num)]; norm_num
    rw [e]; norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have := neg_log_term (N + 1) (by omega)
    have e : (2:ℝ)⁻¹ ^ (N + 1) = (2:ℝ)⁻¹ ^ N / 2 := by rw [pow_succ]; ring
    rw [e] at this ⊢
    linarith

lemma log_three_halves : 2 / 7 ≤ log (3 / 2) := by
  have := Real.add_one_le_exp (-log (3 / 2))
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
  norm_num at this; linarith

lemma sum_neg_log_le (N : ℕ) : ∑ d ∈ Icc 1 N, -log (1 - (2:ℝ)⁻¹ ^ d) ≤ log 4 := by
  have h83 : log (8 / 3) + 2 / 7 ≤ log 4 := by
    have : log 4 = log (8 / 3) + log (3 / 2) := by
      rw [← log_mul (by norm_num) (by norm_num)]; norm_num
    linarith [log_three_halves]
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases N
    · simp; positivity
    · simp
      have : -log (1 - (2:ℝ)⁻¹) = log 2 := by rw [show (1:ℝ) - 2⁻¹ = 2⁻¹ by norm_num, log_inv, neg_neg]
      rw [this]
      exact log_le_log (by norm_num) (by norm_num)
  · have := sum_neg_log N h
    have : 0 ≤ 8 / 7 * (2:ℝ)⁻¹ ^ N := by positivity
    linarith

/-- `log Φ_n(2) - φ(n) log 2`. -/
noncomputable def a (n : ℕ) : ℝ := log (eval 2 (cyclotomic n ℝ)) - (n.totient : ℝ) * log 2

noncomputable def g (n : ℕ) : ℝ := log (1 - (2:ℝ)⁻¹ ^ n)

lemma sum_a (n : ℕ) (hn : 0 < n) : ∑ d ∈ n.divisors, a d = g n := by
  have hprod := prod_cyclotomic_eq_X_pow_sub_one hn ℝ
  have hev := congrArg (eval (2:ℝ)) hprod
  rw [eval_prod] at hev
  simp only [eval_sub, eval_pow, eval_X, eval_one] at hev
  have hpos : ∀ d ∈ n.divisors, 0 < eval 2 (cyclotomic d ℝ) :=
    fun d _ => cyclotomic_pos' d (by norm_num)
  have hlog : ∑ d ∈ n.divisors, log (eval 2 (cyclotomic d ℝ)) = log ((2:ℝ) ^ n - 1) := by
    rw [← log_prod (fun d hd => (hpos d hd).ne'), hev]
  have htot : ∑ d ∈ n.divisors, (d.totient : ℝ) = n := by exact_mod_cast Nat.sum_totient n
  unfold a g
  rw [sum_sub_distrib, hlog, ← sum_mul, htot]
  have h2n : (2:ℝ) ^ n - 1 = 2 ^ n * (1 - (2:ℝ)⁻¹ ^ n) := by
    rw [mul_sub, mul_one, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow]
  have h1 : 0 < 1 - (2:ℝ)⁻¹ ^ n := by
    have : (2:ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
    linarith
  rw [h2n, log_mul (by positivity) h1.ne', log_pow]; ring

lemma g_nonpos (n : ℕ) : g n ≤ 0 := by
  unfold g
  apply log_nonpos
  · have : (2:ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · have : 0 ≤ (2:ℝ)⁻¹ ^ n := by positivity
    linarith

theorem lower (n : ℕ) (hn : 0 < n) : (2:ℝ) ^ n.totient ≤ 4 * eval 2 (cyclotomic n ℝ) := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := a) (g := g)).mp (fun m hm => sum_a m hm) n hn
  -- a n ≥ Σ_{d | n} g d ≥ -log 4
  have hge : ∑ d ∈ n.divisors, g d ≤ a n := by
    rw [← hinv, Nat.sum_divisorsAntidiagonal' (f := fun x y => (ArithmeticFunction.moebius x : ℝ) * g y)]
    apply sum_le_sum
    intro x _
    have hg := g_nonpos x
    rcases ArithmeticFunction.moebius_eq_or (n / x) with h | h | h <;> rw [h] <;> push_cast <;> linarith
  have hdiv : ∑ d ∈ n.divisors, g d ≥ -log 4 := by
    have hsub : n.divisors ⊆ Icc 1 n := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 hn, Nat.le_of_dvd hn hd.1⟩
    have : ∑ d ∈ n.divisors, -g d ≤ ∑ d ∈ Icc 1 n, -g d :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by linarith [g_nonpos d])
    have h4 := sum_neg_log_le n
    simp only [g] at this h4 ⊢
    rw [sum_neg_distrib, sum_neg_distrib] at this
    rw [sum_neg_distrib] at h4
    linarith
  have hpos := cyclotomic_pos' n (R := ℝ) (by norm_num : (1:ℝ) < 2)
  have hlog : (n.totient : ℝ) * log 2 - log 4 ≤ log (eval 2 (cyclotomic n ℝ)) := by
    unfold a at hge; linarith
  have := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos, Real.exp_sub, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity),
    Real.exp_log (by norm_num), Real.rpow_natCast] at this
  rw [div_le_iff₀ (by norm_num)] at this
  linarith

end OMA.Stewart977


open Polynomial Finset

namespace OMA.Stewart977b

/-- `Φ_n(2)` as a natural number. -/
noncomputable def Φ (n : ℕ) : ℕ := ((cyclotomic n ℤ).eval 2).natAbs

lemma eval_pos (n : ℕ) : 0 < (cyclotomic n ℤ).eval 2 := cyclotomic_pos' n (by norm_num)

lemma Φ_cast (n : ℕ) : ((Φ n : ℕ) : ℤ) = (cyclotomic n ℤ).eval 2 := by
  unfold Φ; rw [Int.natCast_natAbs, abs_of_pos (eval_pos n)]

lemma Φ_real (n : ℕ) : ((Φ n : ℕ) : ℝ) = eval 2 (cyclotomic n ℝ) := by
  have h := eval_intCast_map (Int.castRingHom ℝ) (cyclotomic n ℤ) 2
  rw [map_cyclotomic] at h
  have : ((Φ n : ℕ) : ℝ) = (((Φ n : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [this, Φ_cast]; push_cast at h ⊢; rw [h]; rfl

lemma Φ_pos (n : ℕ) : 0 < Φ n := by
  unfold Φ; exact Int.natAbs_pos.mpr (eval_pos n).ne'

lemma Φ_dvd (n : ℕ) : Φ n ∣ 2 ^ n - 1 := by
  have h := eval_dvd (x := (2:ℤ)) (cyclotomic.dvd_X_pow_sub_one n ℤ)
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h
  have h' : ((Φ n : ℕ) : ℤ) ∣ ((2 ^ n - 1 : ℕ) : ℤ) := by
    rw [Φ_cast]; have : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
    rw [this]; exact h
  exact_mod_cast h'

lemma odd_of_dvd {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- A prime factor of `Φ_n(2)` not dividing `n` is `≡ 1 (mod n)`. -/
lemma mod_eq_one {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hpΦ : p ∣ Φ n) (hpn : ¬ p ∣ n) :
    p % n = 1 := by
  haveI := Fact.mk hp
  have hroot : IsRoot (cyclotomic n (ZMod p)) ((2 : ℤ) : ZMod p) := by
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), eval_map,
      show ((2:ℤ) : ZMod p) = Int.castRingHom (ZMod p) 2 from rfl, eval₂_hom, Int.coe_castRingHom,
      ZMod.intCast_zmod_eq_zero_iff_dvd, ← Φ_cast]
    exact_mod_cast hpΦ
  have hne : NeZero ((n : ℕ) : ZMod p) :=
    NeZero.of_not_dvd (ZMod p) (p := p) hpn
  have hprim := isRoot_cyclotomic_iff.mp hroot
  have hord : orderOf (((2:ℤ) : ZMod p)) = n := hprim.eq_orderOf.symm
  have h2 : ((2:ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have : p ∣ 2 := by exact_mod_cast h
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact odd_of_dvd (by omega) (hpΦ.trans (Φ_dvd n)) hp2
  have hdvd := ZMod.orderOf_dvd_card_sub_one h2
  rw [hord] at hdvd
  have hp1 := hp.one_lt
  obtain ⟨k, hk⟩ := hdvd
  have : p = n * k + 1 := by omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- For `n = m p`, `Φ_n ∣ 1 + X^m + ⋯ + X^{m(p-1)}`. -/
lemma cyc_dvd_S {n m p : ℕ} (hm : 0 < m) (hp : 1 < p) (hnm : n = m * p) :
    cyclotomic n ℤ ∣ ∑ i ∈ range p, (X ^ m : ℤ[X]) ^ i := by
  have hn : 0 < n := by rw [hnm]; positivity
  have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn.ne' ⟨p, hnm⟩
  have hmem : n ∈ n.divisors \ m.divisors := by
    rw [mem_sdiff, Nat.mem_divisors, Nat.mem_divisors]
    refine ⟨⟨dvd_rfl, hn.ne'⟩, fun h => ?_⟩
    have := Nat.le_of_dvd hm h.1
    rw [hnm] at this; nlinarith
  have h1 : (X ^ m - 1 : ℤ[X]) * ∑ i ∈ range p, (X ^ m) ^ i = X ^ n - 1 := by
    rw [mul_comm, geom_sum_mul, ← pow_mul, hnm]
  have h2 : (X ^ n - 1 : ℤ[X]) =
      (X ^ m - 1) * ∏ d ∈ n.divisors \ m.divisors, cyclotomic d ℤ := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn, ← prod_cyclotomic_eq_X_pow_sub_one hm,
      ← prod_sdiff hsub, mul_comm]
  have hne : (X ^ m - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) hm.ne').ne_zero; simpa using this
  have hS : ∑ i ∈ range p, (X ^ m : ℤ[X]) ^ i = ∏ d ∈ n.divisors \ m.divisors, cyclotomic d ℤ :=
    mul_left_cancel₀ hne (h1.trans h2)
  rw [hS]; exact dvd_prod_of_mem _ hmem

lemma Φ_dvd_S {n m p : ℕ} (hm : 0 < m) (hp : 1 < p) (hnm : n = m * p) :
    Φ n ∣ ∑ i ∈ range p, (2 ^ m) ^ i := by
  have h := eval_dvd (x := (2:ℤ)) (cyc_dvd_S hm hp hnm)
  simp only [eval_finsetSum, eval_pow, eval_X] at h
  rw [← Φ_cast] at h
  exact_mod_cast h

/-- `v_p(1 + x + ⋯ + x^{p-1}) ≤ 1` for `x = 2^m`, `m ≥ 1`. -/
lemma padic_S_le {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    padicValNat p (∑ i ∈ range p, (2 ^ m) ^ i) ≤ 1 := by
  haveI := Fact.mk hp
  set x : ℕ := 2 ^ m with hx
  have hx1 : 1 < x := Nat.one_lt_two_pow hm.ne'
  set S : ℕ := ∑ i ∈ range p, x ^ i with hS
  have hSpos : 0 < S := by
    rw [hS]; exact sum_pos (fun i _ => by positivity) ⟨0, mem_range.mpr hp.pos⟩
  have hgeom : (x - 1) * S = x ^ p - 1 := by
    have h : ((x : ℤ) - 1) * ∑ i ∈ range p, (x : ℤ) ^ i = (x : ℤ) ^ p - 1 := by
      rw [mul_comm, geom_sum_mul]
    have hxp : 1 ≤ x ^ p := Nat.one_le_pow _ _ (by omega)
    zify [hx1.le, hxp]; rw [hS]; push_cast; exact h
  by_cases hdvd : p ∣ x - 1
  · have hodd : Odd p := by
      refine hp.odd_of_ne_two ?_
      rintro rfl
      have : 2 ∣ x := by rw [hx]; exact dvd_pow_self 2 hm.ne'
      omega
    have hnx : ¬ p ∣ x := by
      intro h
      have := Nat.dvd_sub h hdvd
      rw [Nat.sub_sub_self hx1.le] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := padicValNat.pow_sub_pow (p := p) (x := x) (y := 1) (hp1 := hodd)
      hx1 (by simpa using hdvd) hnx (n := p) hp.ne_zero
    rw [one_pow, ← hgeom, padicValNat.mul (by omega) hSpos.ne', padicValNat_self] at hlte
    simp at hlte
    omega
  · have : ¬ p ∣ S := by
      intro hpS
      have hz : ((x : ℕ) : ZMod p) - 1 ≠ 0 := by
        intro h
        apply hdvd
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx1.le]; simpa using h
      have hS0 : ((S : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff S p).mpr hpS
      have hg : (((x - 1) * S : ℕ) : ZMod p) = ((x ^ p - 1 : ℕ) : ZMod p) := by rw [hgeom]
      rw [Nat.cast_mul, Nat.cast_sub hx1.le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
        hS0, mul_zero] at hg
      push_cast at hg
      rw [ZMod.pow_card] at hg
      exact hz (by rw [← hg])
    rw [padicValNat.eq_zero_of_not_dvd this]; omega

/-- For `p ∣ n`: `v_p(Φ_n(2)) ≤ v_p(n)`. -/
lemma padic_Φ_le {n p : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : p ∣ n) :
    padicValNat p (Φ n) ≤ padicValNat p n := by
  haveI := Fact.mk hp
  obtain ⟨m, hnm⟩ := hpn
  have hm : 0 < m := by rcases Nat.eq_zero_or_pos m with rfl | h; · simp at hnm; omega
                        · exact h
  have hd := Φ_dvd_S (n := n) hm hp.one_lt (by rw [hnm, mul_comm])
  have hSpos : 0 < ∑ i ∈ range p, (2 ^ m) ^ i :=
    sum_pos (fun i _ => by positivity) ⟨0, mem_range.mpr hp.pos⟩
  have h1 : padicValNat p (Φ n) ≤ padicValNat p (∑ i ∈ range p, (2 ^ m) ^ i) :=
    (padicValNat_dvd_iff_le hSpos.ne').mp (dvd_trans pow_padicValNat_dvd hd)
  have h2 := padic_S_le hp hm
  have h3 : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn.ne' ⟨m, hnm⟩
  omega

end OMA.Stewart977b

namespace OMA.Stewart977b

theorem H2_main (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n.totient ≤ 4 * n * ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1),
      p ^ padicValNat p (2 ^ n - 1) := by
  classical
  have hn0 : 0 < n := by omega
  set N : ℕ := 2 ^ n - 1 with hN
  have hN0 : N ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
    omega
  have hΦ0 : Φ n ≠ 0 := (Φ_pos n).ne'
  have hΦN : Φ n ∣ N := Φ_dvd n
  -- lower bound 2^φ ≤ 4 Φ
  have hlow : 2 ^ n.totient ≤ 4 * Φ n := by
    have h := OMA.Stewart977.lower n hn0
    rw [← Φ_real] at h
    exact_mod_cast h
  -- split Φ
  set A := (Φ n).primeFactors.filter (· ∣ n) with hA
  set B := (Φ n).primeFactors.filter (fun q => ¬ q ∣ n) with hB
  have hsplit : Φ n = (∏ q ∈ A, q ^ (Φ n).factorization q) * ∏ q ∈ B, q ^ (Φ n).factorization q := by
    rw [hA, hB, prod_filter_mul_prod_filter_not]
    exact Nat.prod_primeFactors_pow_factorization hΦ0
  -- the part dividing n
  have hD : (∏ q ∈ A, q ^ (Φ n).factorization q) ∣ n := by
    have h1 : (∏ q ∈ A, q ^ (Φ n).factorization q) ∣ ∏ q ∈ A, q ^ n.factorization q := by
      apply prod_dvd_prod_of_dvd
      intro q hq
      rw [hA, mem_filter, Nat.mem_primeFactors] at hq
      apply pow_dvd_pow
      rw [Nat.factorization_def _ hq.1.1, Nat.factorization_def _ hq.1.1]
      exact padic_Φ_le hq.1.1 hn0 hq.2
    have h2 : (∏ q ∈ A, q ^ n.factorization q) ∣ ∏ q ∈ n.primeFactors, q ^ n.factorization q := by
      apply prod_dvd_prod_of_subset
      intro q hq
      rw [hA, mem_filter, Nat.mem_primeFactors] at hq
      exact Nat.mem_primeFactors.mpr ⟨hq.1.1, hq.2, hn0.ne'⟩
    rw [← Nat.prod_primeFactors_pow_factorization hn0.ne'] at h2
    exact h1.trans h2
  -- the part ≡ 1 mod n
  have hG : (∏ q ∈ B, q ^ (Φ n).factorization q) ∣
      ∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p N := by
    have h1 : (∏ q ∈ B, q ^ (Φ n).factorization q) ∣ ∏ q ∈ B, q ^ N.factorization q := by
      apply prod_dvd_prod_of_dvd
      intro q _
      exact pow_dvd_pow _ ((Nat.factorization_le_iff_dvd hΦ0 hN0).mpr hΦN q)
    have h2 : (∏ q ∈ B, q ^ N.factorization q) ∣
        ∏ q ∈ N.primeFactors.filter (fun p => p % n = 1), q ^ N.factorization q := by
      apply prod_dvd_prod_of_subset
      intro q hq
      rw [hB, mem_filter, Nat.mem_primeFactors] at hq
      rw [mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hq.1.1, hq.1.2.1.trans hΦN, hN0⟩, mod_eq_one hn hq.1.1 hq.1.2.1 hq.2⟩
    have h3 : (∏ q ∈ N.primeFactors.filter (fun p => p % n = 1), q ^ N.factorization q) =
        ∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p N := by
      apply prod_congr rfl
      intro q hq
      rw [mem_filter] at hq
      rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hq.1)]
    rw [← h3]; exact h1.trans h2
  have hGpos : 0 < ∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p N :=
    prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _
  have hDle := Nat.le_of_dvd hn0 hD
  have hGle := Nat.le_of_dvd hGpos hG
  calc 2 ^ n.totient ≤ 4 * Φ n := hlow
    _ = 4 * ((∏ q ∈ A, q ^ (Φ n).factorization q) * ∏ q ∈ B, q ^ (Φ n).factorization q) := by
        rw [← hsplit]
    _ ≤ 4 * (n * ∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p N) := by
        gcongr
    _ = _ := by ring

end OMA.Stewart977b

theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H2 := OMA.Stewart977b.H2_main
