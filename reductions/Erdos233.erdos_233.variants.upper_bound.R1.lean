import FormalConjectures.ErdosProblems.«233»

-- Reduction Erdos233.erdos_233.variants.upper_bound.R1 of Erdős Problem 233, upper bound
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route (Selberg 1943, with a second difference of psi1 in place of theta(y + h) - theta(y)).
-- Write psi1(t) = sum over n at most t of Lambda(n) (t - n), and
-- D2(d, y) = psi1(y(1+2d)) - 2 psi1(y(1+d)) + psi1(y). For a gap p_n < p_(n+1) with
-- x at most p_n < 2x and d_n at least 16h, every y in (p_n, p_(n+1)/(1+2d)), d = h/x,
-- has a prime-free window (y, y(1+2d)), so D2(d, y) is at most d y times the proper prime
-- powers in the window, which is small; hence d^2 y^2 - D2(d, y) is at least h^2/2 + 6
-- on a set of measure at least d_n/2. H1 and H2 then bound the sum of the large gaps in a
-- dyadic block by C x log^2 x / h. A dyadic summation over gap sizes gives
-- sum over x at most p_n < 2x of d_n^2 at most C x log^3 x, and summing blocks with
-- Chebyshev's p_N at most 18 N log N gives the target.
--
-- H1: the explicit formula for the second difference of psi1 (unconditional; Landau,
--     Ingham): D2(d, y) - d^2 y^2 equals minus the sum over the nontrivial zeros of
--     m_rho c_rho(d) y^(rho+1), up to an error of absolute value at most 6, where
--     c_rho(d) = ((1+2d)^(rho+1) - 2(1+d)^(rho+1) + 1) / (rho(rho+1)) and m_rho is the
--     multiplicity of rho as a zero of zeta.
-- H2: under RH, Selberg's mean square of that zero sum:
--     the integral over [x, 4x] of its squared modulus is at most C x^4 d^3 log^2(2/d).

namespace OMA.R_Erdos233_erdos_233_variants_upper_bound_R1


/-- The explicit formula for the second difference of `psi1`, over the nontrivial zeros of `ζ`
counted with multiplicity. -/
def H1 : Prop :=
  ∀ δ y : ℝ, 0 < δ → 1 ≤ y →
    ‖((((∑ n ∈ Finset.range (⌊y * (1 + 2 * δ)⌋₊ + 1),
            (ArithmeticFunction.vonMangoldt n : ℝ) * (y * (1 + 2 * δ) - n))
        - 2 * (∑ n ∈ Finset.range (⌊y * (1 + δ)⌋₊ + 1),
            (ArithmeticFunction.vonMangoldt n : ℝ) * (y * (1 + δ) - n))
        + (∑ n ∈ Finset.range (⌊y⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (y - n)))
        - δ ^ 2 * y ^ 2 : ℝ) : ℂ)
      + ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) *
            ((((1 + 2 * δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) + 1)
              / ((ρ : ℂ) * ((ρ : ℂ) + 1))))‖ ≤ 6

/-- Under RH, the mean square over `[x, 4x]` of the zero sum of `H1` is
`≪ x⁴ δ³ log²(2/δ)`. -/
def H2 : Prop :=
  RiemannHypothesis → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
    IntervalIntegrable (fun y : ℝ =>
      ‖∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) *
            ((((1 + 2 * δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) + 1)
              / ((ρ : ℂ) * ((ρ : ℂ) + 1))))‖ ^ 2) MeasureTheory.volume x (4 * x) ∧
    ∫ y in x..4 * x,
      ‖∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) *
            ((((1 + 2 * δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) + 1)
              / ((ρ : ℂ) * ((ρ : ℂ) + 1))))‖ ^ 2
      ≤ C * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2

-- ===== Primes.lean
section

open Nat

lemma nth_lt_of_lt_idx {n m : ℕ} (h : n < Nat.primeCounting' m) : nth Nat.Prime n < m :=
  Nat.nth_lt_of_lt_count h

lemma le_nth_of_idx_le {n m : ℕ} (h : Nat.primeCounting' m ≤ n) : m ≤ nth Nat.Prime n :=
  (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).1 h

lemma mem_block {x n : ℕ} (h : n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x)))) :
    x ≤ nth Nat.Prime n ∧ nth Nat.Prime n < 2 * x := by
  rw [Finset.mem_Ico] at h
  exact ⟨le_nth_of_idx_le h.1, nth_lt_of_lt_idx h.2⟩

lemma not_prime_between {n m : ℕ} (h1 : nth Nat.Prime n < m) (h2 : m < nth Nat.Prime (n + 1)) :
    ¬ m.Prime := by
  intro hm
  have e := Nat.nth_count hm
  rw [← e] at h1 h2
  rw [Nat.nth_lt_nth Nat.infinite_setOfPred_prime] at h1 h2
  omega

lemma nth_succ_le_two_mul (n : ℕ) : nth Nat.Prime (n + 1) ≤ 2 * nth Nat.Prime n := by
  have h0 : nth Nat.Prime n ≠ 0 := (Nat.prime_nth_prime n).ne_zero
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  have e := Nat.nth_count hq
  rw [← e] at hlt hle
  rw [Nat.nth_lt_nth Nat.infinite_setOfPred_prime] at hlt
  exact le_trans ((Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt) hle

lemma nth_le_nth_succ (n : ℕ) : nth Nat.Prime n ≤ nth Nat.Prime (n + 1) :=
  (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (Nat.le_succ n)

lemma primeGap_cast (n : ℕ) :
    (primeGap n : ℝ) = (nth Nat.Prime (n + 1) : ℝ) - nth Nat.Prime n := by
  unfold primeGap
  rw [Nat.cast_sub (nth_le_nth_succ n)]

lemma sum_Ico_primeGap (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (primeGap n : ℝ) = (nth Nat.Prime b : ℝ) - nth Nat.Prime a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Finset.sum_Ico_eq_sum_range, show a + k - a = k by omega]
  simp_rw [primeGap_cast, show ∀ i, a + i + 1 = a + (i + 1) from fun i => by ring]
  exact Finset.sum_range_sub (fun i => (nth Nat.Prime (a + i) : ℝ)) k

lemma sum_block_primeGap_le (x : ℕ) :
    ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ≤ 4 * x := by
  by_cases hab : Nat.primeCounting' x < Nat.primeCounting' (2 * x)
  · rw [sum_Ico_primeGap _ _ hab.le]
    have hb : Nat.primeCounting' (2 * x) - 1 ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))) := by
      rw [Finset.mem_Ico]; omega
    have h1 := (mem_block hb).2
    have h2 := nth_succ_le_two_mul (Nat.primeCounting' (2 * x) - 1)
    rw [show Nat.primeCounting' (2 * x) - 1 + 1 = Nat.primeCounting' (2 * x) by omega] at h2
    have h3 : (nth Nat.Prime (Nat.primeCounting' (2 * x)) : ℝ) ≤ 4 * x := by
      exact_mod_cast (by omega : nth Nat.Prime (Nat.primeCounting' (2 * x)) ≤ 4 * x)
    have h4 : (0 : ℝ) ≤ nth Nat.Prime (Nat.primeCounting' x) := Nat.cast_nonneg _
    linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity


end

-- ===== PrimePowers.lean
section

open Real Chebyshev Finset

lemma theta_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    θ b - θ a ≤ Real.log b * (b - a + 1) := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : θ b = θ a + ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, Real.log p := by
    simp only [theta, sum_filter]
    rw [sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  rw [hsplit, add_sub_cancel_left]
  have hb1 : 1 ≤ b := ha.trans hab
  calc ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, Real.log p
      ≤ ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Real.log b := by
        rw [sum_filter]
        refine sum_le_sum fun p hp => ?_
        split_ifs with h
        · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.one_lt.le
          have hpb : (p : ℝ) ≤ b := by
            have := (mem_Ioc.1 hp).2
            exact (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
          exact Real.log_le_log (by linarith) hpb
        · exact Real.log_nonneg hb1
    _ = ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) * Real.log b := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (b - a + 1) * Real.log b := by
        gcongr
        · exact Real.log_nonneg hb1
        · rw [Nat.cast_sub hfl]
          have h1 := Nat.floor_le (show 0 ≤ b by linarith)
          have h2 := Nat.lt_floor_add_one a
          linarith
    _ = Real.log b * (b - a + 1) := by ring

lemma rpow_sub_rpow_le_sqrt {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) {k : ℕ} (hk : 2 ≤ k) :
    B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) ≤ (B - A) / Real.sqrt A := by
  have hA0 : 0 < A := by linarith
  have hk' : (1 : ℝ) / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    exact_mod_cast (by omega : 1 * 2 ≤ 1 * k)
  have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hq : 1 ≤ B / A := by rw [le_div_iff₀ hA0]; linarith
  have e1 : B ^ ((1 : ℝ) / k) = A ^ ((1 : ℝ) / k) * (B / A) ^ ((1 : ℝ) / k) := by
    rw [Real.div_rpow (by linarith) hA0.le, mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos hA0 _).ne'
  have h1 : A ^ ((1 : ℝ) / k) ≤ A ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hA hk'
  have h2 : (B / A) ^ ((1 : ℝ) / k) ≤ (B / A) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq hk'
  have h3 : 1 ≤ (B / A) ^ ((1 : ℝ) / k) := Real.one_le_rpow hq hk0
  have hsA : A ^ ((1 : ℝ) / 2) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
  have hsq : (B / A) ^ ((1 : ℝ) / 2) = Real.sqrt B / Real.sqrt A := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hA0.le]
  have hsA0 : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  have key : B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) ≤ Real.sqrt B - Real.sqrt A := by
    rw [e1]
    have : A ^ ((1 : ℝ) / k) * ((B / A) ^ ((1 : ℝ) / k) - 1)
        ≤ A ^ ((1 : ℝ) / 2) * ((B / A) ^ ((1 : ℝ) / 2) - 1) :=
      mul_le_mul h1 (by linarith) (by linarith) (Real.rpow_nonneg hA0.le _)
    rw [hsA, hsq, mul_sub, mul_sub, mul_div_cancel₀ _ hsA0.ne', mul_one, mul_one] at this
    linarith
  have hsB : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
  have : Real.sqrt B - Real.sqrt A ≤ (B - A) / Real.sqrt A := by
    rw [le_div_iff₀ hsA0]
    have hA' := Real.mul_self_sqrt hA0.le
    have hB' := Real.mul_self_sqrt (show 0 ≤ B by linarith)
    nlinarith
  linarith

/-- The proper prime powers in `(A, B]` carry `Λ`-mass at most
`(log B / log 2) · log B · ((B − A)/√A + 1)`. -/
theorem psi_sub_theta_window {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    (ψ B - θ B) - (ψ A - θ A)
      ≤ (Real.log B / Real.log 2) * Real.log B * ((B - A) / Real.sqrt A + 1) := by
  set N := ⌊Real.log B / Real.log 2⌋₊ with hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNA : ⌊Real.log A / Real.log 2⌋₊ ≤ N :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith) hAB) hl2.le)
  rw [psi_eq_theta_add_sum_theta' (hA.trans hAB) le_rfl,
    psi_eq_theta_add_sum_theta' hA hNA, ← hN]
  simp only [add_sub_cancel_left]
  rw [← sum_sub_distrib]
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hterm : ∀ k ∈ Icc 2 N, θ (B ^ ((1 : ℝ) / k)) - θ (A ^ ((1 : ℝ) / k))
      ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
    have ha1 : 1 ≤ A ^ ((1 : ℝ) / k) := Real.one_le_rpow (by linarith) hk0
    have hab : A ^ ((1 : ℝ) / k) ≤ B ^ ((1 : ℝ) / k) :=
      Real.rpow_le_rpow (by linarith) hAB hk0
    refine (theta_sub_le ha1 hab).trans ?_
    have hlog : Real.log (B ^ ((1 : ℝ) / k)) ≤ Real.log B := by
      rw [Real.log_rpow (by linarith)]
      have : (1 : ℝ) / k ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    have hd := rpow_sub_rpow_le_sqrt (by linarith) hAB hk2
    have hpos : 0 ≤ B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1 := by linarith
    calc Real.log (B ^ ((1 : ℝ) / k)) * (B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1)
        ≤ Real.log B * (B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1) :=
          mul_le_mul_of_nonneg_right hlog hpos
      _ ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hcard : ((N + 1 - 2 : ℕ) : ℝ) ≤ Real.log B / Real.log 2 := by
    have : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    exact this.trans (Nat.floor_le (div_nonneg hlB hl2.le))
  have hnn : 0 ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by
    have : 0 ≤ (B - A) / Real.sqrt A := div_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  calc ((N + 1 - 2 : ℕ) : ℝ) * (Real.log B * ((B - A) / Real.sqrt A + 1))
      ≤ Real.log B / Real.log 2 * (Real.log B * ((B - A) / Real.sqrt A + 1)) :=
        mul_le_mul_of_nonneg_right hcard hnn
    _ = _ := by ring


end

-- ===== Gaps.lean
section

open Complex MeasureTheory intervalIntegral Chebyshev ArithmeticFunction

lemma psi1_eq_sum_pos (f : ℝ → ℝ) (hf : ∀ t, f t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n)) {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : ⌊t⌋₊ + 1 ≤ M) :
    f t = ∑ n ∈ Finset.range M, (Λ n : ℝ) * max (t - n) 0 := by
  rw [hf]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hn
    have : (n : ℝ) ≤ t := (Nat.cast_le.2 hn).trans (Nat.floor_le ht)
    rw [max_eq_left (by linarith)]
  · intro n _ hn
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hn
    have : t < n := (Nat.floor_lt ht).1 hn
    rw [max_eq_right (by linarith), mul_zero]

lemma tent_le (y H a : ℝ) (hH : 0 < H) :
    max (y + 2 * H - a) 0 - 2 * max (y + H - a) 0 + max (y - a) 0
      ≤ if y < a ∧ a < y + 2 * H then H else 0 := by
  rcases le_or_gt a y with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
      if_neg (show ¬(y < a ∧ a < y + 2 * H) by intro h; linarith [h.1])]
    linarith
  rcases lt_or_ge a (y + H) with h2 | h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
      if_pos ⟨h1, by linarith⟩]
    linarith
  rcases lt_or_ge a (y + 2 * H) with h3 | h3
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
      if_pos ⟨h1, h3⟩]
    linarith
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  split_ifs <;> linarith

/-- The Λ-side of `D2` when the window `(y, y(1+2δ))` contains no prime. -/
lemma D2_le (f : ℝ → ℝ) (hf : ∀ t, f t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n)) {δ y : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hnp : ∀ n : ℕ, y < n → (n : ℝ) < y * (1 + 2 * δ) → ¬ n.Prime) :
    (f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) ≤ δ * y * ((ψ (y * (1 + 2 * δ)) - θ (y * (1 + 2 * δ))) - (ψ y - θ y)) := by
  set B := y * (1 + 2 * δ) with hB
  set H := δ * y with hH
  have hH0 : 0 < H := mul_pos hδ hy
  set M := ⌊B⌋₊ + 1 with hM
  have hyB : y ≤ B := by rw [hB]; nlinarith
  have hyM : y * (1 + δ) ≤ B := by rw [hB]; nlinarith
  have e1 := psi1_eq_sum_pos f hf (t := B) (by linarith) (M := M) le_rfl
  have e2 := psi1_eq_sum_pos f hf (t := y * (1 + δ)) (by nlinarith) (M := M)
    (by have := Nat.floor_le_floor hyM; omega)
  have e3 := psi1_eq_sum_pos f hf (t := y) hy.le (M := M)
    (by have := Nat.floor_le_floor hyB; omega)
  have hD : (f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) = ∑ n ∈ Finset.range M, (Λ n : ℝ) *
      (max (y + 2 * H - n) 0 - 2 * max (y + H - n) 0 + max (y - n) 0) := by
    rw [← hB, e1, e2, e3, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show y + 2 * H = B by rw [hB, hH]; ring, show y + H = y * (1 + δ) by rw [hH]; ring]
    ring
  set P : ℕ → Prop := fun n => ⌊y⌋₊ < n ∧ n ≤ ⌊B⌋₊ ∧ ¬ n.Prime with hP
  have hstep : (f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) ≤ ∑ n ∈ Finset.range M, (Λ n : ℝ) * (if P n then H else 0) := by
    rw [hD]
    refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    refine (tent_le y H n hH0).trans ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      apply h2
      refine ⟨(Nat.floor_lt hy.le).2 h1.1, Nat.le_floor ?_, hnp n h1.1 ?_⟩
      · have : y + 2 * H = B := by rw [hB, hH]; ring
        linarith [h1.2]
      · have : y + 2 * H = B := by rw [hB, hH]; ring
        linarith [h1.2]
    · exact hH0.le
    · exact le_rfl
  have hsum : ∑ n ∈ Finset.range M, (Λ n : ℝ) * (if P n then H else 0)
      = H * ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊B⌋₊ with ¬ n.Prime, (Λ n : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    rw [← Finset.sum_subset (s₁ := Finset.Ioc ⌊y⌋₊ ⌊B⌋₊) (s₂ := Finset.range M)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      by_cases hp : n.Prime
      · simp [hP, hp]
      · simp [hP, hp, hn.1, hn.2, mul_comm]
    · intro n hn; rw [Finset.mem_Ioc] at hn; rw [Finset.mem_range]; omega
    · intro n _ hn
      rw [Finset.mem_Ioc] at hn
      have : ¬ P n := fun h => hn ⟨h.1, h.2.1⟩
      simp [this]
  have hpt : (ψ B - θ B) - (ψ y - θ y) = ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊B⌋₊ with ¬ n.Prime, (Λ n : ℝ) := by
    rw [psi_sub_theta_eq_sum_not_prime, psi_sub_theta_eq_sum_not_prime, Finset.sum_filter,
      Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hyB)]
    ring
  rw [hpt]
  exact hstep.trans hsum.le

/-- Eventually `16 log²(5x)/log 2 ≤ √x`. -/
lemma eventually_log_sq_le_sqrt :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 16 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ Real.sqrt X := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show 0 < Real.log 2 / 64 by positivity)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 ho
  refine ⟨max X₁ 5, fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have h := hX₁ X (le_of_max_le_left hX)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlX _),
    abs_of_nonneg (Real.rpow_nonneg hX0.le _), Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have h5 : Real.log (5 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 5 ≤ Real.log X := Real.log_le_log (by norm_num) hX5
    linarith
  have h5' : 0 ≤ Real.log (5 * X) := Real.log_nonneg (by linarith)
  have hsq : Real.log (5 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  rw [div_eq_mul_inv]
  have : 16 * (Real.log (5 * X) ^ 2 * (Real.log 2)⁻¹) ≤ 64 * Real.log X ^ 2 / Real.log 2 := by
    rw [mul_comm (Real.log (5 * X) ^ 2), ← mul_assoc, le_div_iff₀ hl2]
    field_simp
    nlinarith
  refine this.trans ?_
  rw [div_le_iff₀ hl2]
  nlinarith

lemma gap_arith {Sg Cm X h δ : ℝ} (hCm : 0 < Cm) (hX5 : 5 ≤ X) (hh0 : 0 < h) (hh1 : 1 ≤ h)
    (hhx : h ≤ X / 8) (hδdef : δ = h / X) (_hSnn : 0 ≤ Sg)
    (htot : Sg * (h ^ 4 / 4 / 2) ≤ Cm * X ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2) :
    Sg ≤ 32 * Cm * X * Real.log X ^ 2 / h := by
  have hX0 : 0 < X := by linarith
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hlog2δ : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0, one_mul, hδdef, div_le_iff₀ hX0]; linarith)
  have hlog2δ' : Real.log (2 / δ) ≤ 2 * Real.log X := by
    have : 2 / δ ≤ X ^ 2 := by
      rw [div_le_iff₀ hδ0, hδdef]
      field_simp
      nlinarith
    calc Real.log (2 / δ) ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  have hL2 : Real.log (2 / δ) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have hX4 : X ^ 4 * δ ^ 3 = X * h ^ 3 := by rw [hδdef]; field_simp
  rw [mul_assoc Cm, mul_assoc Cm, hX4] at htot
  rw [le_div_iff₀ hh0]
  have hh3 : 0 < h ^ 3 := by positivity
  have key : Sg * h * (h ^ 3 / 8) ≤ (32 * Cm * X * Real.log X ^ 2) * (h ^ 3 / 8) := by
    have e : Sg * h * (h ^ 3 / 8) = Sg * (h ^ 4 / 4 / 2) := by ring
    rw [e]
    refine htot.trans ?_
    have : Cm * (X * h ^ 3 * Real.log (2 / δ) ^ 2) ≤ Cm * (X * h ^ 3 * (4 * Real.log X ^ 2)) := by
      gcongr
    nlinarith
  have := le_of_mul_le_mul_right key (by positivity)
  linarith

theorem gap_sum (f : ℝ → ℝ) (hf : ∀ t, f t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n)) (G : ℝ → ℝ → ℝ)
    (hD : ∀ δ y : ℝ, 0 < δ → 1 ≤ y → |(f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) - δ ^ 2 * y ^ 2| ≤ 6 + G δ y)
    (hms : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun y => G δ y ^ 2) volume x (4 * x) ∧
      ∫ y in x..4 * x, G δ y ^ 2 ≤ C * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∀ h : ℝ, 16 * (Real.log (5 * x) ^ 2 / Real.log 2) ≤ h → h ≤ x / 8 →
    ∑ n ∈ ((Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x)))).filter (fun n => 16 * h ≤ primeGap n), (primeGap n : ℝ)
      ≤ C * x * Real.log x ^ 2 / h := by
  obtain ⟨Cm, hCm, hms⟩ := hms
  obtain ⟨X₁, hX₁⟩ := eventually_log_sq_le_sqrt
  refine ⟨32 * Cm, max X₁ 5, by positivity, fun x hx h hh hhx => ?_⟩
  set X : ℝ := (x : ℝ) with hXdef
  have hX5 : 5 ≤ X := le_of_max_le_right hx
  have hX0 : 0 < X := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set Lx := Real.log (5 * X) ^ 2 / Real.log 2 with hLx
  have hl5 : 1 ≤ Real.log (5 * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hLx1 : 1 ≤ Lx := by
    rw [hLx, le_div_iff₀ hl2]; nlinarith
  have hsqrt : 16 * Lx ≤ Real.sqrt X := hX₁ X (le_of_max_le_left hx)
  have hh16 : 16 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  set δ := h / X with hδdef
  have hδ0 : 0 < δ := div_pos hh0 hX0
  have hδ8 : δ ≤ 1 / 8 := by rw [hδdef, div_le_iff₀ hX0]; linarith
  have hδX : δ * X = h := by rw [hδdef]; field_simp
  obtain ⟨hII, hMS⟩ := hms X (by linarith) δ hδ0 (by linarith)
  set W : ℝ → ℝ := fun y => G δ y ^ 2 with hW
  set S := ((Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x)))).filter (fun n => 16 * h ≤ primeGap n) with hS
  set a : ℕ → ℝ := fun n => (Nat.nth Nat.Prime n : ℝ) with ha
  set b : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n + 1) : ℝ) / (1 + 2 * δ) with hb
  set c : ℝ := h ^ 4 / 4 with hc
  have hc0 : 0 ≤ c := by positivity
  have han : ∀ k, a k = (Nat.nth Nat.Prime k : ℝ) := fun k => by rw [ha]
  have hbn : ∀ k, b k = (Nat.nth Nat.Prime (k + 1) : ℝ) / (1 + 2 * δ) := fun k => by rw [hb]
  clear_value W S a b c
  -- facts about one gap
  have hgap : ∀ n ∈ S, X ≤ a n ∧ a n ≤ b n ∧ b n ≤ 4 * X ∧
      (primeGap n : ℝ) / 2 ≤ b n - a n ∧ (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 4 * X := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hn1, hn2⟩ := mem_block hn.1
    have hd := hn.2
    have h2 := nth_succ_le_two_mul n
    have hq4 : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 4 * X := by
      rw [hXdef]; exact_mod_cast (by omega : Nat.nth Nat.Prime (n + 1) ≤ 4 * x)
    have hxa : X ≤ a n := by rw [han, hXdef]; exact_mod_cast hn1
    have hpg := primeGap_cast n
    have hq0 : (0 : ℝ) ≤ Nat.nth Nat.Prime (n + 1) := Nat.cast_nonneg _
    have hbq : b n ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by
      rw [hbn, div_le_iff₀ (by linarith)]; nlinarith
    have hbl : (Nat.nth Nat.Prime (n + 1) : ℝ) * (1 - 2 * δ) ≤ b n := by
      rw [hbn, le_div_iff₀ (by linarith)]
      have e : (Nat.nth Nat.Prime (n + 1) : ℝ) * (1 - 2 * δ) * (1 + 2 * δ)
          = (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime (n + 1) : ℝ) * (4 * δ ^ 2) := by ring
      rw [e]
      have : 0 ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) * (4 * δ ^ 2) := by positivity
      linarith
    have hlen : (primeGap n : ℝ) / 2 ≤ b n - a n := by
      have : (Nat.nth Nat.Prime (n + 1) : ℝ) * (2 * δ) ≤ 8 * h := by
        have : (Nat.nth Nat.Prime (n + 1) : ℝ) * δ ≤ 4 * X * δ :=
          mul_le_mul_of_nonneg_right hq4 hδ0.le
        nlinarith
      have hd' : 16 * h ≤ (primeGap n : ℝ) := by exact_mod_cast hd
      rw [han]
      linarith
    have hpg0 : (0 : ℝ) ≤ primeGap n := Nat.cast_nonneg _
    exact ⟨hxa, by linarith, by linarith, hlen, hq4⟩
  -- on `G_n` the zero contribution is large
  have hbig : ∀ n ∈ S, ∀ y ∈ Set.Ioo (a n) (b n), c ≤ W y := by
    intro n hn y hy
    obtain ⟨hxa, -, hb4, -, hq4⟩ := hgap n hn
    have hyX : X ≤ y := by linarith [hy.1]
    have hy0 : 0 < y := by linarith
    set B := y * (1 + 2 * δ) with hBdef
    have hBq : B < (Nat.nth Nat.Prime (n + 1) : ℝ) := by
      have := hy.2; rw [hbn, lt_div_iff₀ (by linarith)] at this; rw [hBdef]; linarith
    have hnp : ∀ m : ℕ, y < m → (m : ℝ) < B → ¬ m.Prime := by
      intro m h1 h2
      refine not_prime_between (n := n) ?_ ?_
      · have : (Nat.nth Nat.Prime n : ℝ) < m := by
          have := hy.1; rw [han] at this; linarith
        exact_mod_cast this
      · exact_mod_cast h2.trans hBq
    have hD2 : (f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) ≤ δ * y * ((ψ B - θ B) - (ψ y - θ y)) := D2_le f hf hy0 hδ0 hnp
    have hyB : y ≤ B := by rw [hBdef]; nlinarith
    have hwin := psi_sub_theta_window (A := y) (B := B) (by linarith) hyB
    have hDb := hD δ y hδ0 (show 1 ≤ y by linarith)
    set H := δ * y with hHdef
    clear_value H B
    have hHh : h ≤ H := by rw [hHdef, ← hδX]; exact mul_le_mul_of_nonneg_left hyX hδ0.le
    have hB5 : B ≤ 5 * X := by linarith
    have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hlB5 : Real.log B ≤ Real.log (5 * X) := Real.log_le_log (by linarith) hB5
    have hLw : Real.log B / Real.log 2 * Real.log B ≤ Lx := by
      rw [hLx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2, sq]
      exact mul_le_mul hlB5 hlB5 hlB (hlB.trans hlB5)
    have hsy : Real.sqrt X ≤ Real.sqrt y := Real.sqrt_le_sqrt hyX
    have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have hT : (B - y) / Real.sqrt y = 2 * H / Real.sqrt y := by
      congr 1; rw [hBdef, hHdef]; ring
    set T := 2 * H / Real.sqrt y with hTdef
    have hT0 : 0 ≤ T := div_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hHT : H * Lx * T ≤ H ^ 2 / 8 := by
      rw [hTdef]
      have : H * Lx * (2 * H / Real.sqrt y) = 2 * Lx * H ^ 2 / Real.sqrt y := by ring
      rw [this, div_le_iff₀ hsy0]
      have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
      have := mul_le_mul_of_nonneg_left (hsqrt.trans hsy) hH2
      linarith
    have hP : (ψ B - θ B) - (ψ y - θ y) ≤ Lx * (T + 1) := by
      rw [← hT]
      refine hwin.trans ?_
      have : 0 ≤ (B - y) / Real.sqrt y + 1 := by
        have : 0 ≤ (B - y) / Real.sqrt y := div_nonneg (by linarith) (Real.sqrt_nonneg _)
        linarith
      exact mul_le_mul_of_nonneg_right hLw this
    have hH0 : 0 < H := by linarith
    have hDle : (f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) ≤ H * (Lx * (T + 1)) := hD2.trans (mul_le_mul_of_nonneg_left hP hH0.le)
    have hHL : H * Lx ≤ H ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_left (show 8 * Lx ≤ H by linarith) hH0.le
      have hsq : H ^ 2 = H * H := sq H
      linarith
    have hab := (abs_le.1 hDb).1
    have hWy : H ^ 2 / 2 ≤ G δ y := by
      have e : δ ^ 2 * y ^ 2 = H ^ 2 := by rw [hHdef]; ring
      rw [e] at hab
      have e2 : H * (Lx * (T + 1)) = H * Lx * T + H * Lx := by ring
      have h16 : 16 ≤ H := by linarith
      have h256 : 256 ≤ H ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num) h16 2; norm_num at this; linarith
      linarith
    have hh2 : h ^ 2 / 2 ≤ H ^ 2 / 2 := by
      have := pow_le_pow_left₀ hh0.le hHh 2; linarith
    rw [hW, hc]
    have h3 : h ^ 2 / 2 ≤ G δ y := hh2.trans hWy
    have h4 := pow_le_pow_left₀ (by positivity) h3 2
    have e3 : (h ^ 2 / 2) ^ 2 = h ^ 4 / 4 := by ring
    linarith
  -- disjointness
  have hdisj : ∀ n ∈ S, ∀ n' ∈ S, ∀ y, y ∈ Set.Ioo (a n) (b n) →
      y ∈ Set.Ioo (a n') (b n') → n = n' := by
    intro n hn n' hn' y hy hy'
    by_contra hne
    have hbq : ∀ k ∈ S, b k ≤ (Nat.nth Nat.Prime (k + 1) : ℝ) := by
      intro k hk
      obtain ⟨hxa, hab, -, -, hq4⟩ := hgap k hk
      rw [hbn, div_le_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ Nat.nth Nat.Prime (k + 1) := Nat.cast_nonneg _
      nlinarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Nat.nth Nat.Prime n' := by
        exact_mod_cast (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt
      have := hbq n hn
      have h1 := hy.2; have h2 := hy'.1; rw [han] at h2; linarith
    · have : (Nat.nth Nat.Prime (n' + 1) : ℝ) ≤ Nat.nth Nat.Prime n := by
        exact_mod_cast (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt
      have := hbq n' hn'
      have h1 := hy'.2; have h2 := hy.1; rw [han] at h2; linarith
  -- the lower function
  set g : ℝ → ℝ := fun y => ∑ n ∈ S, (Set.Ioo (a n) (b n)).indicator (fun _ => c) y with hg
  have hind_int : ∀ n, IntervalIntegrable ((Set.Ioo (a n) (b n)).indicator fun _ => c)
      volume X (4 * X) := by
    intro n
    refine Integrable.intervalIntegrable ?_
    exact (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
  have hgI : IntervalIntegrable g volume X (4 * X) := by
    have := IntervalIntegrable.sum S fun n _ => hind_int n
    have e : g = ∑ i ∈ S, (Set.Ioo (a i) (b i)).indicator fun _ => c := by
      funext y; simp [hg, Finset.sum_apply]
    rw [e]; exact this
  have hgW : ∀ y ∈ Set.Icc X (4 * X), g y ≤ W y := by
    intro y _
    have hW0 : 0 ≤ W y := by rw [hW]; positivity
    rw [hg]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    set K := S.filter (fun n => y ∈ Set.Ioo (a n) (b n)) with hK
    have hK1 : K.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro n hn n' hn'
      rw [hK, Finset.mem_filter] at hn hn'
      exact hdisj n hn.1 n' hn'.1 y hn.2 hn'.2
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · rw [h0]; simp [hW0]
    · obtain ⟨n, hn⟩ := Finset.card_pos.1 h0
      rw [hK, Finset.mem_filter] at hn
      have := hbig n hn.1 y hn.2
      have hK1' : (K.card : ℝ) ≤ 1 := by exact_mod_cast hK1
      nlinarith
  have hint_ind : ∀ n ∈ S, ∫ y in X..4 * X, (Set.Ioo (a n) (b n)).indicator (fun _ => c) y
      = c * (b n - a n) := by
    intro n hn
    obtain ⟨hxa, hab, hb4, -, -⟩ := hgap n hn
    rw [integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioo]
    have hset : Set.Ioc X (4 * X) ∩ Set.Ioo (a n) (b n) = Set.Ioo (a n) (b n) := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨by linarith [h.1], by linarith [h.2]⟩, h⟩
    rw [hset, setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul, mul_comm]
  have hint_g : ∫ y in X..4 * X, g y = ∑ n ∈ S, c * (b n - a n) := by
    rw [hg, intervalIntegral.integral_finsetSum fun n _ => hind_int n]
    exact Finset.sum_congr rfl hint_ind
  have hmono : ∫ y in X..4 * X, g y ≤ ∫ y in X..4 * X, W y :=
    integral_mono_on (by linarith) hgI hII hgW
  have hlow : (∑ n ∈ S, (primeGap n : ℝ)) * (c / 2) ≤ ∑ n ∈ S, c * (b n - a n) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    have h1 := mul_le_mul_of_nonneg_left (hgap n hn).2.2.2.1 hc0
    have e : (primeGap n : ℝ) * (c / 2) = c * ((primeGap n : ℝ) / 2) := by ring
    rw [e]; exact h1
  have htot : (∑ n ∈ S, (primeGap n : ℝ)) * (c / 2)
      ≤ Cm * X ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
    calc _ ≤ ∑ n ∈ S, c * (b n - a n) := hlow
      _ = ∫ y in X..4 * X, g y := hint_g.symm
      _ ≤ ∫ y in X..4 * X, W y := hmono
      _ ≤ _ := hMS
  have hSnn : 0 ≤ ∑ n ∈ S, (primeGap n : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [hc] at htot
  exact gap_arith hCm hX5 hh0 (by linarith) hhx hδdef hSnn htot


end

-- ===== Dyadic.lean
section

open Real

lemma sq_le_dyadic {d h0 : ℝ} (hh0 : 0 < h0) (hd0 : 0 ≤ d) (I : ℕ)
    (hI : d < 16 * h0 * 2 ^ (I + 1)) :
    d ^ 2 ≤ 16 * h0 * d + 32 * ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) := by
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  by_cases hsmall : d < 16 * h0
  · have : d ^ 2 ≤ 16 * h0 * d := by nlinarith
    linarith
  push Not at hsmall
  have h16 : 0 < 16 * h0 := by positivity
  set q := d / (16 * h0) with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ h16]; linarith
  set m := ⌊q⌋₊ with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.le_floor (by exact_mod_cast hq1)
  set j := Nat.log 2 m with hj
  have hjm : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hmj : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hmq : (m : ℝ) ≤ q := Nat.floor_le (by linarith)
  have hqm : q < m + 1 := Nat.lt_floor_add_one q
  have h2j : (2 : ℝ) ^ j ≤ q := by
    have : ((2 ^ j : ℕ) : ℝ) ≤ m := by exact_mod_cast hjm
    push_cast at this; linarith
  have hq2 : q < (2 : ℝ) ^ (j + 1) := by
    have : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hmj
    push_cast at this; linarith
  have hjI : j < I + 1 := by
    have hqI : q < (2 : ℝ) ^ (I + 1) := by
      rw [hq, div_lt_iff₀ h16]; linarith
    have : (2 : ℝ) ^ j < 2 ^ (I + 1) := lt_of_le_of_lt h2j hqI
    exact (pow_lt_pow_iff_right₀ (by norm_num)).1 this
  have hlow : 16 * (2 ^ j * h0) ≤ d := by
    have := mul_le_mul_of_nonneg_left h2j h16.le
    rw [hq, mul_div_cancel₀ _ h16.ne'] at this; linarith
  have hup : d < 32 * (2 ^ j * h0) := by
    have := mul_lt_mul_of_pos_left hq2 h16
    rw [hq, mul_div_cancel₀ _ h16.ne', pow_succ] at this; linarith
  have hterm : 2 ^ j * h0 * d ≤ ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) := by
    have := Finset.single_le_sum (f := fun i =>
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0))
      (fun i _ => by split_ifs <;> positivity) (Finset.mem_range.2 hjI)
    simp only [hlow, ↓reduceIte] at this
    exact this
  have : d ^ 2 ≤ 32 * (2 ^ j * h0 * d) := by nlinarith
  nlinarith

theorem block_sq (f : ℝ → ℝ) (hf : ∀ t, f t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n))
    (G : ℝ → ℝ → ℝ)
    (hD : ∀ δ y : ℝ, 0 < δ → 1 ≤ y → |(f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) - δ ^ 2 * y ^ 2| ≤ 6 + G δ y)
    (hms : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun y => G δ y ^ 2) MeasureTheory.volume x (4 * x) ∧
      ∫ y in x..4 * x, G δ y ^ 2 ≤ C * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ^ 2 ≤ C * x * Real.log x ^ 3 := by
  obtain ⟨Cg, Xg, hCg, hgap⟩ := gap_sum f hf G hD hms
  refine ⟨6000 + 96 * Cg, max Xg 5, by positivity, fun x hx => ?_⟩
  have hX5 : (5 : ℝ) ≤ x := le_of_max_le_right hx
  have hX0 : (0 : ℝ) < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlX : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  set h0 := 16 * (Real.log (5 * x) ^ 2 / Real.log 2) with hh0
  have hl5 : Real.log (5 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 5 ≤ Real.log x := Real.log_le_log (by norm_num) hX5
    linarith
  have hl5' : 1 ≤ Real.log (5 * x) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; have := Real.exp_one_lt_d9; linarith
  have hh0pos : 16 ≤ h0 := by
    rw [hh0]
    have : 1 ≤ Real.log (5 * x) ^ 2 / Real.log 2 := by
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      rw [le_div_iff₀ hl2]; nlinarith
    linarith
  have hh0le : h0 ≤ 93 * Real.log x ^ 2 := by
    rw [hh0, mul_div_assoc', div_le_iff₀ hl2]
    have : Real.log (5 * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
    nlinarith
  set I := Nat.log 2 x with hI
  have hxI : x < 2 ^ (I + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  -- pointwise
  have hpt : ∀ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ^ 2 ≤ 16 * h0 * primeGap n + 32 *
      ∑ i ∈ Finset.range (I + 1),
        (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0) := by
    intro n hn
    refine sq_le_dyadic (by linarith) (Nat.cast_nonneg _) I ?_
    have h1 := (mem_block hn).2
    have h2 := nth_succ_le_two_mul n
    have hd : (primeGap n : ℝ) < 2 * x := by
      rw [primeGap_cast]
      have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 2 * Nat.nth Nat.Prime n := by exact_mod_cast h2
      have : (Nat.nth Nat.Prime n : ℝ) < 2 * x := by exact_mod_cast h1
      linarith
    have : (x : ℝ) < 2 ^ (I + 1) := by exact_mod_cast hxI
    nlinarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hsum
  -- level bounds
  have hlevel : ∀ i ∈ Finset.range (I + 1), ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))),
      (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0)
      ≤ Cg * x * Real.log x ^ 2 := by
    intro i _
    have hhi : 0 < 2 ^ i * h0 := by positivity
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    by_cases hbig : 2 ^ i * h0 ≤ x / 8
    · have := hgap x (le_of_max_le_left hx) (2 ^ i * h0) (by
        have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        rw [← hh0]; nlinarith) hbig
      rw [le_div_iff₀ hhi] at this
      linarith
    · push Not at hbig
      have hempty : ((Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x)))).filter (fun n => 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        have h1 := (mem_block hn).2
        have h2 := nth_succ_le_two_mul n
        rw [primeGap_cast, not_le]
        have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 2 * Nat.nth Nat.Prime n := by exact_mod_cast h2
        have : (Nat.nth Nat.Prime n : ℝ) < 2 * x := by exact_mod_cast h1
        linarith
      rw [hempty, Finset.sum_empty, mul_zero]
      positivity
  have hlev := Finset.sum_le_sum hlevel
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlev
  have hIl : ((I + 1 : ℕ) : ℝ) ≤ 3 * Real.log x := by
    have hI' : (2 : ℝ) ^ I ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by
      have : (5 : ℝ) ≤ x := hX5; exact_mod_cast (show x ≠ 0 by rintro rfl; norm_num at this))
    have : (I : ℝ) * Real.log 2 ≤ Real.log x := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hI'
    push_cast
    have : (I : ℝ) ≤ Real.log x / 0.69 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith [(Nat.cast_nonneg I : (0 : ℝ) ≤ I)]
    have : Real.log x / 0.69 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hgsum := sum_block_primeGap_le x
  have hgsum0 : 0 ≤ ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hA : 16 * h0 * ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ≤ 6000 * x * Real.log x ^ 3 := by
    have : 16 * h0 * ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ≤ 16 * (93 * Real.log x ^ 2) * (4 * x) := by
      gcongr
    have : Real.log x ^ 2 ≤ Real.log x ^ 3 := by
      have := pow_le_pow_right₀ hlX (show 2 ≤ 3 by norm_num); exact this
    nlinarith
  have hB : 32 * (((I + 1 : ℕ) : ℝ) * (Cg * x * Real.log x ^ 2))
      ≤ 96 * Cg * x * Real.log x ^ 3 := by
    have h1 : 0 ≤ Cg * x * Real.log x ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hIl h1
    nlinarith
  have hB' : 32 * ∑ i ∈ Finset.range (I + 1), ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))),
      (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0)
      ≤ 32 * (((I + 1 : ℕ) : ℝ) * (Cg * x * Real.log x ^ 2)) := by
    have := hlev; push_cast at this ⊢; linarith
  nlinarith


end

-- ===== Main.lean
section

open Real Filter Asymptotics

lemma sum_Ico_blocks (f : ℕ → ℝ) (x₀ J : ℕ) :
    ∑ n ∈ Finset.Ico (Nat.primeCounting' x₀) (Nat.primeCounting' (2 ^ J * x₀)), f n
      = ∑ j ∈ Finset.range J, ∑ n ∈ (Finset.Ico (Nat.primeCounting' (2 ^ j * x₀)) (Nat.primeCounting' (2 * (2 ^ j * x₀)))), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * (2 ^ J * x₀) = 2 ^ (J + 1) * x₀ by ring]
    refine (Finset.sum_Ico_consecutive _ ?_ ?_).symm
    · exact Nat.monotone_primeCounting' (by
        have : 1 ≤ 2 ^ J := Nat.one_le_two_pow; nlinarith)
    · exact Nat.monotone_primeCounting' (by
        rw [pow_succ, mul_comm (2 ^ J) 2, mul_assoc]
        exact Nat.le_mul_of_pos_left _ (by norm_num))

/-- `p_N ≤ 18 N log N` for `N ≥ 3`. -/
lemma nth_prime_le (N : ℕ) (hN : 3 ≤ N) :
    (Nat.nth Nat.Prime N : ℝ) ≤ 18 * N * Real.log N := by
  set X := Nat.nth Nat.Prime N with hX
  have hX4 : 4 ≤ X := by have := Nat.add_two_le_nth_prime N; omega
  have hpi : Nat.primeCounting X = N + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime N
  have hcheb := Chebyshev.pi_ge X
  rw [hpi] at hcheb
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX4r : (4 : ℝ) ≤ X := by exact_mod_cast hX4
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlX0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (X : ℝ) * Real.log 2 - Real.log (X + 1) ≤ (N + 1) * Real.log X := by
    rw [div_le_iff₀ hlX0] at hcheb; push_cast at hcheb; linarith
  have hl1 : Real.log ((X : ℝ) + 1) ≤ 2 * Real.log X := by
    have : (X : ℝ) + 1 ≤ (X : ℝ) ^ 2 := by nlinarith
    calc Real.log ((X : ℝ) + 1) ≤ Real.log ((X : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  have h1 : (X : ℝ) * Real.log 2 ≤ 2 * N * Real.log X := by nlinarith
  -- `log X ≤ 2√X`
  have hsX : Real.log X ≤ 2 * Real.sqrt X := by
    have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hX0.le] at this
    linarith
  have hsq : Real.sqrt X ≤ 6 * N := by
    have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hXs : (X : ℝ) = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0.le).symm
    have : Real.sqrt X * Real.sqrt X * 0.69 ≤ 2 * N * (2 * Real.sqrt X) := by
      rw [← hXs]
      calc (X : ℝ) * 0.69 ≤ X * Real.log 2 := by gcongr
        _ ≤ 2 * N * Real.log X := h1
        _ ≤ 2 * N * (2 * Real.sqrt X) := by gcongr
    nlinarith
  have hXN : (X : ℝ) ≤ 36 * (N : ℝ) ^ 2 := by
    have := Real.mul_self_sqrt hX0.le
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  have hlN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]; have := Real.exp_one_lt_d9; linarith
  have hlogX : Real.log X ≤ 6 * Real.log N := by
    have hNN : (36 : ℝ) * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 6 := by
      have h3 : (81 : ℝ) ≤ (N : ℝ) ^ 4 := by
        have : (9 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        nlinarith
      have : (N : ℝ) ^ 6 = (N : ℝ) ^ 4 * (N : ℝ) ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg (N : ℝ)]
    calc Real.log X ≤ Real.log ((N : ℝ) ^ 6) := Real.log_le_log hX0 (hXN.trans hNN)
      _ = 6 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have : (X : ℝ) * 0.69 ≤ 2 * N * (6 * Real.log N) := by
    calc (X : ℝ) * 0.69 ≤ X * Real.log 2 := by gcongr
      _ ≤ 2 * N * Real.log X := h1
      _ ≤ 2 * N * (6 * Real.log N) := by gcongr
  nlinarith

theorem upper_bound_of (f : ℝ → ℝ) (hf : ∀ t, f t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n))
    (G : ℝ → ℝ → ℝ)
    (hD : ∀ δ y : ℝ, 0 < δ → 1 ≤ y → |(f (y * (1 + 2 * δ)) - 2 * f (y * (1 + δ)) + f y) - δ ^ 2 * y ^ 2| ≤ 6 + G δ y)
    (hms : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun y => G δ y ^ 2) MeasureTheory.volume x (4 * x) ∧
      ∫ y in x..4 * x, G δ y ^ 2 ≤ C * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2) :
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop] fun N => N * (Real.log N)^4 := by
  obtain ⟨Cb, Xb, hCb, hblock⟩ := block_sq f hf G hD hms
  set x₀ : ℕ := ⌈max Xb 5⌉₊ with hx₀
  have hx₀X : max Xb 5 ≤ (x₀ : ℝ) := Nat.le_ceil _
  have hx₀5 : (5 : ℝ) ≤ x₀ := le_trans (le_max_right _ _) hx₀X
  have hx₀pos : 0 < x₀ := by exact_mod_cast (show (0 : ℝ) < x₀ by linarith)
  set K₀ := ∑ n ∈ Finset.range (Nat.primeCounting' x₀), (primeGap n : ℝ) ^ 2 with hK₀
  set a := Real.log (2 * x₀) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  set C₁ := 36 * Cb * x₀ * (a + 6) ^ 3 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hK0 : 0 ≤ K₀ := Finset.sum_nonneg fun _ _ => by positivity
  refine IsBigO.of_bound (C₁ + 1) ?_
  rw [eventually_atTop]
  refine ⟨max 3 ⌈K₀⌉₊, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_left hN
  have hNK : K₀ ≤ N := (Nat.le_ceil K₀).trans (by exact_mod_cast le_of_max_le_right hN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  set X := Nat.nth Nat.Prime N with hX
  set J := Nat.log 2 X + 1 with hJ
  have hXJ : X < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) X
  have hJX : 2 ^ J ≤ 2 * X := by
    rw [hJ, pow_succ]
    have := Nat.pow_log_le_self 2 (show X ≠ 0 from (Nat.prime_nth_prime N).ne_zero)
    omega
  have hNidx : N ≤ Nat.primeCounting' (2 ^ J * x₀) := by
    have : X < 2 ^ J * x₀ := by nlinarith
    exact ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 this).le
  have hidx : Nat.primeCounting' x₀ ≤ Nat.primeCounting' (2 ^ J * x₀) :=
    Nat.monotone_primeCounting' (by have : 1 ≤ 2 ^ J := Nat.one_le_two_pow; nlinarith)
  -- the sum up to `N`
  have hsplit : ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2
      ≤ K₀ + ∑ j ∈ Finset.range J, ∑ n ∈ (Finset.Ico (Nat.primeCounting' (2 ^ j * x₀)) (Nat.primeCounting' (2 * (2 ^ j * x₀)))), (primeGap n : ℝ) ^ 2 := by
    rw [← sum_Ico_blocks, hK₀, Finset.sum_range_add_sum_Ico _ hidx]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNidx)
      fun _ _ _ => by positivity
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (Nat.prime_nth_prime N).pos
  have hlog0 : 0 ≤ Real.log (2 * x₀ * X) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ X := by exact_mod_cast (Nat.prime_nth_prime N).one_lt.le
    nlinarith)
  have hblocks : ∑ j ∈ Finset.range J, ∑ n ∈ (Finset.Ico (Nat.primeCounting' (2 ^ j * x₀)) (Nat.primeCounting' (2 * (2 ^ j * x₀)))), (primeGap n : ℝ) ^ 2
      ≤ Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J := by
    have hL : ∀ j ∈ Finset.range J, Real.log ((2 ^ j * x₀ : ℕ) : ℝ) ≤ Real.log (2 * x₀ * X) := by
      intro j hj
      refine Real.log_le_log (by positivity) ?_
      have : 2 ^ j * x₀ ≤ 2 * x₀ * X := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.1 hj).le
        nlinarith
      exact_mod_cast this
    calc ∑ j ∈ Finset.range J, ∑ n ∈ (Finset.Ico (Nat.primeCounting' (2 ^ j * x₀)) (Nat.primeCounting' (2 * (2 ^ j * x₀)))), (primeGap n : ℝ) ^ 2
        ≤ ∑ j ∈ Finset.range J, Cb * ((2 ^ j * x₀ : ℕ) : ℝ) * Real.log ((2 ^ j * x₀ : ℕ) : ℝ) ^ 3 :=
          Finset.sum_le_sum fun j _ => hblock _ (by
            refine le_trans (le_trans (le_max_left _ _) hx₀X) ?_
            have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
            exact_mod_cast (show x₀ ≤ 2 ^ j * x₀ by nlinarith))
      _ ≤ ∑ j ∈ Finset.range J, Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hl0 : 0 ≤ Real.log ((2 ^ j * x₀ : ℕ) : ℝ) := Real.log_nonneg (by
            have : 1 ≤ 2 ^ j * x₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
            exact_mod_cast this)
          have h3 := pow_le_pow_left₀ hl0 (hL j hj) 3
          push_cast at h3 ⊢
          have h := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Cb * ((2 : ℝ) ^ j * x₀) by positivity)
          linarith
      _ = Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J := by
          have hgeom : ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ 2 ^ J := by
            have := geom_sum_mul_of_one_le (show (1 : ℝ) ≤ 2 by norm_num) J
            norm_num at this; linarith [this, (pow_pos (show (0 : ℝ) < 2 by norm_num) J)]
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  -- sizes
  have hpN := nth_prime_le N hN3
  have hlog : Real.log (2 * x₀ * X) ≤ (a + 6) * Real.log N := by
    rw [Real.log_mul (by positivity) hX0.ne', ← ha]
    have hlX : Real.log X ≤ 6 * Real.log N := by
      have hXN : (X : ℝ) ≤ (N : ℝ) ^ 6 := by
        have h1 : 18 * (N : ℝ) * Real.log N ≤ 18 * N * N := by
          have := Real.log_le_sub_one_of_pos hN0
          gcongr; linarith
        have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
        have h2 : 18 * (N : ℝ) * N ≤ N ^ 6 := by
          have : (27 : ℝ) ≤ N ^ 3 := by nlinarith
          nlinarith
        linarith
      calc Real.log X ≤ Real.log ((N : ℝ) ^ 6) := Real.log_le_log hX0 hXN
        _ = 6 * Real.log N := by rw [Real.log_pow]; push_cast; ring
    nlinarith
  have h2J : ((2 : ℝ) ^ J) ≤ 2 * X := by exact_mod_cast hJX
  have hmain : Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J ≤ C₁ * (N * Real.log N ^ 4) := by
    have e1 := pow_le_pow_left₀ hlog0 hlog 3
    have : Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J
        ≤ Cb * x₀ * ((a + 6) * Real.log N) ^ 3 * (2 * (18 * N * Real.log N)) := by
      have h3 : (2 : ℝ) ^ J ≤ 2 * (18 * N * Real.log N) := by linarith
      gcongr
    rw [hC₁]
    calc _ ≤ Cb * x₀ * ((a + 6) * Real.log N) ^ 3 * (2 * (18 * N * Real.log N)) := this
      _ = 36 * Cb * x₀ * (a + 6) ^ 3 * (N * Real.log N ^ 4) := by ring
  have hg0 : 0 ≤ (N : ℝ) * Real.log N ^ 4 := by positivity
  have hK : K₀ ≤ 1 * ((N : ℝ) * Real.log N ^ 4) := by
    have : (1 : ℝ) ≤ Real.log N ^ 4 := one_le_pow₀ hlN
    nlinarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg0]
  rw [abs_of_nonneg hS0]
  nlinarith


end

/-! ### Assembly -/

lemma abs_le_of_norm_add_le (a : ℝ) (W : ℂ) (h : ‖(a : ℂ) + W‖ ≤ 6) : |a| ≤ 6 + ‖W‖ := by
  have e : (a : ℂ) = ((a : ℂ) + W) - W := by ring
  have h2 : ‖(a : ℂ)‖ ≤ ‖(a : ℂ) + W‖ + ‖W‖ := by
    calc ‖(a : ℂ)‖ = ‖((a : ℂ) + W) - W‖ := by rw [← e]
      _ ≤ ‖(a : ℂ) + W‖ + ‖W‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  linarith

theorem main : H1 → H2 → type_of% @Erdos233.erdos_233.variants.upper_bound := by
  intro h1 h2 hRH
  refine upper_bound_of
    (fun t => ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * (t - n))
    (fun t => rfl)
    (fun δ y => ‖∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) *
            ((((1 + 2 * δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) + 1)
              / ((ρ : ℂ) * ((ρ : ℂ) + 1))))‖) ?_ (h2 hRH)
  intro δ y hδ hy
  exact abs_le_of_norm_add_le _ _ (h1 δ y hδ hy)

end OMA.R_Erdos233_erdos_233_variants_upper_bound_R1
