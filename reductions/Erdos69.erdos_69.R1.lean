import FormalConjectures.ErdosProblems.«69»

-- Reduction Erdos69.erdos_69.R1 of Erdős Problem 69
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős Problem 69: isolating the deep input of the Tao–Teräväinen proof

The irrationality of the sum of `ω n / 2 ^ n` was proved by Tao and Teräväinen in
*Quantitative correlations and some problems on prime factors of consecutive integers*
(arXiv:2512.01739, Section 9). This file splits that proof at its natural seam.

Write `T m` for the tail sum of `ω (m + h + 1) / 2 ^ (h + 1)` over `h`. If the series is rational
with denominator `q`, then `q * T m` is an integer for every `m` (lemma `int_of_rational`).
For a real threshold `y` let `g k` be the number of primes `p > y` dividing the integer `k`.

* `H1` is the elementary part of the argument (Gowers-type differencing over a cube of primes,
  Mertens and sieve bounds for small and medium primes, the moment method). It produces, at every
  large scale `x`, an arithmetic progression `n ≡ b mod Q` in `[x / 2, x]`, a short list `J` of
  shifts with small signed weights `w` summing to zero, and an integer combination `Z n` of the
  tails `T m`, such that `q * (Z n - ∑ r ∈ J, w r * g (n + r))` stays away from the integers on a
  positive proportion of the progression. In the paper `Z n` is the alternating sum of
  `T ((n - s_ε) / p_ε)` over the cube, `J` is the set of shifts `r_{ε, h + K}` with `h ≤ H` and
  `w` is `(-1) ^ |ε| / 2 ^ (h + K)`; the difference is then the contribution of the primes up to
  `y` at the near shifts plus the far shifts plus the square-divisibility terms, whose
  characteristic function is shown to be small (Sections 9.1 to 9.11).

* `H2` is the deep part: along a sequence of scales `x`, the numbers of large prime factors of
  `n + r` and `n + s` are asymptotically uncorrelated for distinct small shifts `r`, `s`,
  uniformly over progressions of small modulus. This is the estimate for very large primes in
  Section 9.12 of the paper, which rests on the quantitative two-point correlation theorem
  (Theorem 1.6 there, built on work of Pilatte). The scale `x` may be restricted to a sequence
  because that theorem has an exceptional set of scales, and the threshold `y` is only pinned
  to the range `x ^ (1/200) ≤ y ≤ x ^ (1/50)` for the same reason.

`main` combines them: expanding the second moment of `∑ r ∈ J, w r * (g (n + r) - m)` over the
progression, the diagonal is small because the weights have small square sum and `g ≤ 400`, the
off-diagonal is small by `H2`, so the weighted sum is small for most `n`; but rationality and
`H1` force it to be at least `c / q` in absolute value on a positive proportion.
-/

namespace OMA.R_Erdos69_erdos_69_R1

/-- The elementary part: at every large scale there is a progression, a list of shifts with
small alternating weights, and an integer combination `Z` of tails of the series, such that
after removing the weighted count of large prime factors the quantity `q * Z n` is at distance
at least `c` from every integer on a proportion at least `c` of the progression. -/
def H1 : Prop :=
  ∀ q : ℕ, 0 < q → ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → ∀ y : ℝ,
    (x : ℝ) ^ (1 / 200 : ℝ) ≤ y → y ≤ (x : ℝ) ^ (1 / 50 : ℝ) →
    ∃ (Q b : ℕ) (J : Finset ℤ) (w : ℤ → ℝ) (Z : ℕ → ℝ),
      0 < Q ∧ (Q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) ∧
      (∀ r ∈ J, |(r : ℝ)| ≤ Real.exp (Real.sqrt (Real.log (Real.log x)))) ∧
      ∑ r ∈ J, w r = 0 ∧ ∑ r ∈ J, |w r| ≤ 1 ∧ ∑ r ∈ J, w r ^ 2 ≤ η ∧
      (∀ n : ℕ, ∃ (M : Finset ℕ) (a : ℕ → ℤ), Z n = ∑ m ∈ M, (a m : ℝ) *
        ∑' h : ℕ, (ArithmeticFunction.cardDistinctFactors (m + h + 1) : ℝ) / 2 ^ (h + 1)) ∧
      ∃ A : Finset ℕ, A.Nonempty ∧
        A ⊆ (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q) ∧
        c * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card ≤ A.card ∧
        ∀ n ∈ A, ∀ z : ℤ, c ≤ |(q : ℝ) * (Z n - ∑ r ∈ J, w r *
          ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ)) - z|

/-- The deep part: along a sequence of scales, the counts of prime factors exceeding `y` of
`n + r` and `n + s` are uncorrelated (after centring at a bounded constant `m`), uniformly over
progressions of modulus at most `exp (sqrt (log (log x)))` and distinct shifts of that size. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ X : ℕ, ∃ x : ℕ, X ≤ x ∧ ∃ y m : ℝ,
    (x : ℝ) ^ (1 / 200 : ℝ) ≤ y ∧ y ≤ (x : ℝ) ^ (1 / 50 : ℝ) ∧ 0 ≤ m ∧ m ≤ 100 ∧
    ∀ (Q b : ℕ) (r s : ℤ), 0 < Q →
      (Q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) →
      |(r : ℝ)| ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) →
      |(s : ℝ)| ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) → r ≠ s →
      |∑ n ∈ (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q),
        ((((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m) *
         (((((n : ℤ) + s).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m))|
      ≤ η * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card

/-- If the series is rational with denominator `d`, then `d` times every shifted and
rescaled tail of the series is an integer. -/
lemma int_of_rational
    (hS : ¬ Irrational (∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2))) :
    ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ, ∃ z : ℤ, (d : ℝ) *
      ∑' h : ℕ, (ArithmeticFunction.cardDistinctFactors (m + h + 1) : ℝ) / 2 ^ (h + 1) = z := by
  have hs := ArithmeticFunction.summable_cardDistinctFactors_div_two_pow
  rw [Irrational, not_not] at hS
  obtain ⟨r, hr⟩ := hS
  have h2 := hs.sum_add_tsum_nat_add 2
  have hS0 : ∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors n : ℝ) / 2 ^ n = r := by
    rw [← h2, hr]
    simp [Finset.sum_range_succ]
  refine ⟨r.den, r.den_pos, fun m => ?_⟩
  have hm := hs.sum_add_tsum_nat_add (m + 1)
  have hT : ∑' h : ℕ, (ArithmeticFunction.cardDistinctFactors (m + h + 1) : ℝ) / 2 ^ (h + 1)
      = 2 ^ m * ∑' i : ℕ, (ArithmeticFunction.cardDistinctFactors (i + (m + 1)) : ℝ)
        / 2 ^ (i + (m + 1)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun h => ?_
    rw [show m + h + 1 = h + (m + 1) by ring, show h + (m + 1) = (h + 1) + m by ring,
      pow_add (2 : ℝ) (h + 1) m]
    field_simp
  have hden : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
  refine ⟨2 ^ m * r.num - r.den * ∑ i ∈ Finset.range (m + 1),
    (ArithmeticFunction.cardDistinctFactors i : ℤ) * 2 ^ (m - i), ?_⟩
  have hfin : (2 : ℝ) ^ m * ∑ i ∈ Finset.range (m + 1),
      (ArithmeticFunction.cardDistinctFactors i : ℝ) / 2 ^ i
      = ∑ i ∈ Finset.range (m + 1), (ArithmeticFunction.cardDistinctFactors i : ℝ) * 2 ^ (m - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : (2 : ℝ) ^ m = 2 ^ (m - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel him]
    rw [this]
    field_simp
  have htail : ∑' i : ℕ, (ArithmeticFunction.cardDistinctFactors (i + (m + 1)) : ℝ)
      / 2 ^ (i + (m + 1)) = r - ∑ i ∈ Finset.range (m + 1),
      (ArithmeticFunction.cardDistinctFactors i : ℝ) / 2 ^ i := by
    rw [← hS0, ← hm]; ring
  rw [hT, htail]
  push_cast
  rw [← hfin, ← hden]
  ring

/-- Expanding the square of a weighted sum and bounding diagonal and off-diagonal terms. -/
lemma second_moment (N : Finset ℕ) (J : Finset ℤ) (w : ℤ → ℝ) (G : ℕ → ℤ → ℝ) (C η₁ η₂ : ℝ)
    (hη₂ : 0 ≤ η₂) (hw1 : ∑ r ∈ J, |w r| ≤ 1) (hw2 : ∑ r ∈ J, w r ^ 2 ≤ η₁)
    (hG : ∀ n ∈ N, ∀ r ∈ J, |G n r| ≤ C)
    (hcov : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → |∑ n ∈ N, G n r * G n s| ≤ η₂ * N.card) :
    ∑ n ∈ N, (∑ r ∈ J, w r * G n r) ^ 2 ≤ (C ^ 2 * η₁ + η₂) * N.card := by
  have hexp : ∑ n ∈ N, (∑ r ∈ J, w r * G n r) ^ 2
      = ∑ r ∈ J, ∑ s ∈ J, w r * w s * ∑ n ∈ N, G n r * G n s := by
    have : ∀ n ∈ N, (∑ r ∈ J, w r * G n r) ^ 2
        = ∑ r ∈ J, ∑ s ∈ J, w r * w s * (G n r * G n s) := by
      intro n _
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
  have hNn : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  have hterm : ∀ r ∈ J, ∀ s ∈ J, w r * w s * ∑ n ∈ N, G n r * G n s
      ≤ (if r = s then w r ^ 2 * (C ^ 2 * N.card) else 0) + |w r| * |w s| * (η₂ * N.card) := by
    intro r hr s hs
    by_cases hrs : r = s
    · subst hrs
      rw [if_pos rfl]
      have h1 : ∑ n ∈ N, G n r * G n r ≤ C ^ 2 * N.card := by
        have : ∀ n ∈ N, G n r * G n r ≤ C ^ 2 := by
          intro n hn
          have := hG n hn r hr
          rw [← sq, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        calc ∑ n ∈ N, G n r * G n r ≤ ∑ _n ∈ N, C ^ 2 := Finset.sum_le_sum this
          _ = C ^ 2 * N.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      have h2 : w r * w r * ∑ n ∈ N, G n r * G n r ≤ w r ^ 2 * (C ^ 2 * N.card) := by
        rw [← sq]
        exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      have h3 : 0 ≤ |w r| * |w r| * (η₂ * N.card) := by positivity
      linarith
    · rw [if_neg hrs, zero_add]
      calc w r * w s * ∑ n ∈ N, G n r * G n s
          ≤ |w r * w s * ∑ n ∈ N, G n r * G n s| := le_abs_self _
        _ = |w r| * |w s| * |∑ n ∈ N, G n r * G n s| := by rw [abs_mul, abs_mul]
        _ ≤ |w r| * |w s| * (η₂ * N.card) :=
          mul_le_mul_of_nonneg_left (hcov r hr s hs hrs) (by positivity)
  rw [hexp]
  calc ∑ r ∈ J, ∑ s ∈ J, w r * w s * ∑ n ∈ N, G n r * G n s
      ≤ ∑ r ∈ J, ∑ s ∈ J, ((if r = s then w r ^ 2 * (C ^ 2 * N.card) else 0)
          + |w r| * |w s| * (η₂ * N.card)) :=
        Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs => hterm r hr s hs
    _ = (∑ r ∈ J, w r ^ 2) * (C ^ 2 * N.card)
          + (∑ r ∈ J, |w r|) * (∑ s ∈ J, |w s|) * (η₂ * N.card) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.sum_ite_eq J r, if_pos hr]
        · rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
    _ ≤ η₁ * (C ^ 2 * N.card) + 1 * 1 * (η₂ * N.card) := by
        have hsum_nn : 0 ≤ ∑ r ∈ J, |w r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        gcongr
    _ = (C ^ 2 * η₁ + η₂) * N.card := by ring

/-- A natural number at most `x ^ 2` has at most 400 prime factors exceeding `x ^ (1/200)`. -/
lemma large_pf_card_le (x : ℕ) (hx : 2 ≤ x) (y : ℝ) (hy : (x : ℝ) ^ (1 / 200 : ℝ) ≤ y) (k : ℕ)
    (hk : k ≤ x ^ 2) : ((k.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) ≤ 400 := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have h1 : 1 < y := lt_of_lt_of_le (Real.one_lt_rpow hx1 (by norm_num)) hy
  have hprod : (∏ p ∈ k.primeFactors.filter (fun p : ℕ => y < p), p) ∣ k :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd k)
  have hle : ∏ p ∈ k.primeFactors.filter (fun p : ℕ => y < p), p ≤ k := Nat.le_of_dvd hkpos hprod
  have hpow : y ^ (k.primeFactors.filter (fun p : ℕ => y < p)).card
      ≤ ∏ p ∈ k.primeFactors.filter (fun p : ℕ => y < p), (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by positivity)
      (fun p hp => (Finset.mem_filter.mp hp).2.le)
  have hx2 : y ^ (k.primeFactors.filter (fun p : ℕ => y < p)).card ≤ (x : ℝ) ^ 2 := by
    refine hpow.trans ?_
    have : ((∏ p ∈ k.primeFactors.filter (fun p : ℕ => y < p), p : ℕ) : ℝ) ≤ ((x ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (hle.trans hk)
    push_cast at this
    exact this
  have hy400 : (x : ℝ) ^ 2 ≤ y ^ 400 := by
    have : ((x : ℝ) ^ (1 / 200 : ℝ)) ^ 400 = (x : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← this]
    exact pow_le_pow_left₀ (by positivity) hy 400
  by_contra hcon
  rw [not_le] at hcon
  have hcard : 401 ≤ (k.primeFactors.filter (fun p : ℕ => y < p)).card := by
    have : (400 : ℝ) < ((k.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) := hcon
    exact_mod_cast this
  have h401 : y ^ 401 ≤ y ^ (k.primeFactors.filter (fun p : ℕ => y < p)).card :=
    pow_le_pow_right₀ h1.le hcard
  have hlt : y ^ 400 < y ^ 401 := pow_lt_pow_right₀ h1 (by norm_num)
  linarith

/-- The range of moduli and shifts allowed in the hypotheses is at most `x`. -/
lemma exp_sqrt_log_log_le (x : ℕ) (hx : 3 ≤ x) :
    Real.exp (Real.sqrt (Real.log (Real.log x))) ≤ x := by
  have hx0 : (0 : ℝ) < x := by positivity
  have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have h1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : Real.log (Real.log x) ≤ Real.log x - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h3 : Real.sqrt (Real.log (Real.log x)) ≤ Real.log x := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith
  calc Real.exp (Real.sqrt (Real.log (Real.log x))) ≤ Real.exp (Real.log x) :=
        Real.exp_le_exp.mpr h3
    _ = x := Real.exp_log hx0

theorem main : H1 → H2 → type_of% @Erdos69.erdos_69 := by
  intro h1 h2
  show Irrational _
  by_contra hirr
  obtain ⟨d, hd, hint⟩ := int_of_rational hirr
  obtain ⟨c, hc, h1c⟩ := h1 d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨X, hX⟩ := h1c (c ^ 3 / (d ^ 2 * 640000)) (by positivity)
  obtain ⟨x, hx, y, m, hy1, hy2, hm0, hm1, hcov⟩ :=
    h2 (c ^ 3 / (d ^ 2 * 4)) (by positivity) (max X 3)
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨Q, b, J, w, Z, hQ, hQB, hJB, hw0, hw1, hw2, hZ, A, hAne, hAsub, hAcard, hAfar⟩ :=
    hX x hxX y hy1 hy2
  have hB := exp_sqrt_log_log_le x hx3
  -- the count of large prime factors is bounded
  have hg : ∀ n ∈ (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q), ∀ r ∈ J,
      |((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m| ≤ 400 := by
    intro n hn r hr
    have hnx : n ≤ x := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hr' : r.natAbs ≤ x := by
      have : ((r.natAbs : ℕ) : ℝ) ≤ x := by
        rw [Nat.cast_natAbs]
        push_cast
        exact (hJB r hr).trans hB
      exact_mod_cast this
    have hk : ((n : ℤ) + r).natAbs ≤ x ^ 2 := by
      have := Int.natAbs_add_le (n : ℤ) r
      rw [Int.natAbs_natCast] at this
      nlinarith
    have h400 := large_pf_card_le x (by omega) y hy1 _ hk
    have h0 : (0 : ℝ) ≤ ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) :=
      Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hmom := second_moment ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)) J w
    (fun n r => ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m)
    400 (c ^ 3 / (d ^ 2 * 640000)) (c ^ 3 / (d ^ 2 * 4)) (by positivity) hw1 hw2 hg
    (fun r hr s hs hrs => hcov Q b r s hQ hQB (hJB r hr) (hJB s hs) hrs)
  -- on the set A the weighted sum is bounded below
  have hlow : ∀ n ∈ A, (c / d) ^ 2 ≤ (∑ r ∈ J, w r *
      (((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m)) ^ 2 := by
    intro n hn
    obtain ⟨M, a, hZn⟩ := hZ n
    choose zf hzf using hint
    have hdZ : (d : ℝ) * Z n = ((∑ k ∈ M, a k * zf k : ℤ) : ℝ) := by
      rw [hZn, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hzf k]
      ring
    have hfar := hAfar n hn (∑ k ∈ M, a k * zf k)
    have hY : ∑ r ∈ J, w r *
        (((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m)
        = ∑ r ∈ J, w r *
        ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw0, zero_mul, sub_zero]
    rw [hY]
    rw [mul_sub, hdZ] at hfar
    have habs : c ≤ d * |∑ r ∈ J, w r *
        ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ)| := by
      have : |((∑ k ∈ M, a k * zf k : ℤ) : ℝ) - (d : ℝ) * (∑ r ∈ J, w r *
          ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ))
          - ((∑ k ∈ M, a k * zf k : ℤ) : ℝ)| = d * |∑ r ∈ J, w r *
          ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ)| := by
        rw [show ∀ u v : ℝ, u - v - u = -v by intros; ring, abs_neg, abs_mul, abs_of_pos hdR]
      rw [this] at hfar
      exact hfar
    have hcd : c / d ≤ |∑ r ∈ J, w r *
        ((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ)| := by
      rw [div_le_iff₀ hdR]
      linarith
    rw [← sq_abs (∑ r ∈ J, w r * _)]
    exact pow_le_pow_left₀ (by positivity) hcd 2
  have hNpos : (0 : ℝ) < ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card := by
    have := Finset.card_pos.mpr (hAne.mono hAsub)
    exact_mod_cast this
  have hchain : (A.card : ℝ) * (c / d) ^ 2 ≤ ∑ n ∈ (Finset.Icc (x / 2) x).filter
      (fun n => n % Q = b % Q), (∑ r ∈ J, w r *
      (((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m)) ^ 2 := by
    calc (A.card : ℝ) * (c / d) ^ 2 = ∑ _n ∈ A, (c / d) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ A, (∑ r ∈ J, w r *
          (((((n : ℤ) + r).natAbs.primeFactors.filter (fun p : ℕ => y < p)).card : ℝ) - m)) ^ 2 :=
          Finset.sum_le_sum hlow
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => sq_nonneg _)
  have hfinal : c * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card * (c / d) ^ 2
      ≤ ((400 : ℝ) ^ 2 * (c ^ 3 / (d ^ 2 * 640000)) + c ^ 3 / (d ^ 2 * 4))
        * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card :=
    (mul_le_mul_of_nonneg_right hAcard (sq_nonneg _)).trans (hchain.trans hmom)
  have hval : (400 : ℝ) ^ 2 * (c ^ 3 / (d ^ 2 * 640000)) + c ^ 3 / (d ^ 2 * 4)
      = c ^ 3 / d ^ 2 / 2 := by
    field_simp
    ring
  have hval2 : c * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card * (c / d) ^ 2
      = c ^ 3 / d ^ 2 * ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card := by
    field_simp
  rw [hval, hval2] at hfinal
  have hpos : 0 < c ^ 3 / d ^ 2 *
      ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card := by positivity
  nlinarith

end OMA.R_Erdos69_erdos_69_R1
