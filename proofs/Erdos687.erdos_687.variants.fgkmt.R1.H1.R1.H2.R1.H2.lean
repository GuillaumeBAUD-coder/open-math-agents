import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1
import Mathlib

-- Step Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1
-- Credit: @carterleffen. The Mertens first-theorem and Abel-summation invariant setup below
-- adapts the unconditional `OMALib.Mertens` lemmas from `proofs/Erdos16.erdos_16.variant.romanoff.R1.H1.lean`.

/-!
# Elementary Mertens and Chebyshev density bounds on the sieve band `S` and target primes `V`

Proves `OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1.H2`:
for every `c > 0` and all sufficiently large `x`, with `X = x`, `U = log (log X)`,
`y = c * X * log X * log U / U`, `z = X ^ (log U / (4 * U))`,
`S = {p ≤ z : p prime, p ∉ (x/2, x], log X ^ 20 < p}`, `V = {q ∈ (x, y] : q prime}`,
and `σ = ∏_{p ∈ S} (1 - 1 / p)`, we have:

* `40 * U ^ 2 / (log X * log U) ≤ σ ≤ 120 * U ^ 2 / (log X * log U)`, and
* `|V| * σ ≤ 400 * c * X * U / log X`.

The `σ` bounds follow by telescoping Mertens' second-theorem invariant between `A = floor (log X ^ 20)`
and `B = floor z`, where the Mertens constant cancels identically and the ratio `log A / log B`
evaluates asymptotically to `80 * U ^ 2 / (log X * log U)`. The upper bound on `|V| * σ` follows
directly from Mathlib's `Chebyshev.eventually_primeCounting_le`.
-/

namespace Erdos687H2R1H2

open Real Finset Filter

private lemma log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _; simp

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

private lemma real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

private lemma log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

private lemma log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith

private lemma summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

private noncomputable def primePowerConst : ℝ :=
  ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

private lemma sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)

private lemma primePowerConst_nonneg : 0 ≤ primePowerConst := by
  simpa using sum_log_div_mul_sub_one_le ∅

private lemma sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private lemma sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := primePowerConst_nonneg; simp; linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp; ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

private lemma mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

private lemma abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

private lemma sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

private lemma recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp; ring
  · simp

private lemma abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

private noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

private lemma mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N
  set b := Real.log ((N + 1 : ℕ) : ℝ)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast; rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]; ring
    rw [e, hstep]; field_simp; ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]; gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

private lemma abs_mertensG_sub_le_interval {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    |mertensG B - mertensG A| ≤ (mertens1Const + 1) * (1 / Real.log A - 1 / Real.log B) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n (hA.trans hn)
    calc |mertensG (n + 1) - mertensG A|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG A)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG A| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring

private lemma sum_inv_sdiff_bound {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    |(∑ p ∈ Nat.primesLE B \ Nat.primesLE A, (1 : ℝ) / p) -
        (Real.log (Real.log B) - Real.log (Real.log A))| ≤
      (3 * mertens1Const + 1) / Real.log A := by
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hAB, hp.2⟩
  have hsum_eq : (∑ p ∈ Nat.primesLE B \ Nat.primesLE A, (1 : ℝ) / p) =
      (∑ p ∈ Nat.primesLE B, (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE A, (1 : ℝ) / p := by
    have := Finset.sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
    linarith
  have hA2 : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hlA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlAB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith) hABr
  have hlB : 0 < Real.log B := lt_of_lt_of_le hlA hlAB
  have hC : 0 ≤ mertens1Const := mertens1Const_nonneg
  have hG := abs_mertensG_sub_le_interval hA hAB
  have hRA := abs_sum_log_div_sub_log_le_nat A
  have hRB := abs_sum_log_div_sub_log_le_nat B
  have hident : (∑ p ∈ Nat.primesLE B \ Nat.primesLE A, (1 : ℝ) / p) -
      (Real.log (Real.log B) - Real.log (Real.log A)) =
      (mertensG B - mertensG A) +
      ((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B -
      ((∑ p ∈ Nat.primesLE A, Real.log p / p) - Real.log A) / Real.log A := by
    rw [hsum_eq]; unfold mertensG; ring
  rw [hident]
  have h1 : |mertensG B - mertensG A| ≤ (mertens1Const + 1) / Real.log A := by
    refine hG.trans ?_
    have h0 : 0 ≤ 1 / Real.log B := by positivity
    have : (mertens1Const + 1) * (1 / Real.log A - 1 / Real.log B) ≤
        (mertens1Const + 1) * (1 / Real.log A) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact this.trans_eq (by ring)
  have h2 : |((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B| ≤
      mertens1Const / Real.log A := by
    rw [abs_div, abs_of_pos hlB]
    exact (div_le_div_of_nonneg_right hRB hlB.le).trans (div_le_div_of_nonneg_left hC hlA hlAB)
  have h3 : |((∑ p ∈ Nat.primesLE A, Real.log p / p) - Real.log A) / Real.log A| ≤
      mertens1Const / Real.log A := by
    rw [abs_div, abs_of_pos hlA]
    exact div_le_div_of_nonneg_right hRA hlA.le
  have htri : |(mertensG B - mertensG A) +
      ((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B -
      ((∑ p ∈ Nat.primesLE A, Real.log p / p) - Real.log A) / Real.log A| ≤
      |mertensG B - mertensG A| +
      |((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B| +
      |((∑ p ∈ Nat.primesLE A, Real.log p / p) - Real.log A) / Real.log A| := by
    have e1 := abs_add_le
      ((mertensG B - mertensG A) +
        ((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B)
      (-(((∑ p ∈ Nat.primesLE A, Real.log p / p) - Real.log A) / Real.log A))
    have e2 := abs_add_le (mertensG B - mertensG A)
      (((∑ p ∈ Nat.primesLE B, Real.log p / p) - Real.log B) / Real.log B)
    rw [← sub_eq_add_neg, abs_neg] at e1
    linarith
  have hcomb : (mertens1Const + 1) / Real.log A + mertens1Const / Real.log A +
      mertens1Const / Real.log A = (3 * mertens1Const + 1) / Real.log A := by ring
  linarith

private lemma sum_Ioc_inv_mul_pred {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 / (A : ℝ) := by
  have heq : ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) =
      1 / (A : ℝ) - 1 / (B : ℝ) := by
    induction B, hAB using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hsub : Finset.Ioc A (n + 1) = insert (n + 1) (Finset.Ioc A n) := by
        ext k; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : n + 1 ∉ Finset.Ioc A n := by simp
      rw [hsub, Finset.sum_insert hnot, ih]
      have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hA.trans hn
      have hterm : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) =
          1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [show (n : ℝ) ≠ 0 by linarith, show (n : ℝ) + 1 ≠ 0 by linarith]; ring
      rw [hterm]; ring
  rw [heq]
  have : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
  linarith

private lemma log_prod_sdiff_bound {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    |Real.log (∏ p ∈ Nat.primesLE B \ Nat.primesLE A, (1 - 1 / (p : ℝ))) +
        (Real.log (Real.log B) - Real.log (Real.log A))| ≤
      (3 * mertens1Const + 2) / Real.log A := by
  let S := Nat.primesLE B \ Nat.primesLE A
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hS_ne : ∀ p ∈ S, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS_prime p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP : Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) = ∑ p ∈ S, Real.log (1 - 1 / (p : ℝ)) :=
    Real.log_prod hS_ne
  have hterm_le : ∀ p ∈ S, -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      Real.log (1 - 1 / (p : ℝ)) ∧ Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS_prime p hp).two_le
    have hpos : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    constructor
    · have h := Real.one_sub_inv_le_log_of_pos hpos
      have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        have : (p : ℝ) ≠ 0 := by linarith
        field_simp; ring
      linarith
    · linarith [Real.log_le_sub_one_of_pos hpos]
  have hS_sub_Ioc : S ⊆ Finset.Ioc A B := by
    intro p hp
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    have hB' := (Nat.mem_primesLE.mp hpB).1
    have hpr := (Nat.mem_primesLE.mp hpB).2
    have hA' : A < p := by
      by_contra! hle
      exact hpA (Nat.mem_primesLE.mpr ⟨hle, hpr⟩)
    exact Finset.mem_Ioc.mpr ⟨hA', hB'⟩
  have htail : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / (A : ℝ) := by
    have h1 : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hS_sub_Ioc (fun k hk _ => ?_)
      have hkA := (Finset.mem_Ioc.mp hk).1
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
    exact h1.trans (sum_Ioc_inv_mul_pred hA hAB)
  have hA2 : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hlA_pos : 0 < Real.log A := Real.log_pos (by linarith)
  have hinvA_le : 1 / (A : ℝ) ≤ 1 / Real.log A := by
    apply one_div_le_one_div_of_le hlA_pos
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < A by linarith)
    linarith
  have hdiff_sum : |Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + ∑ p ∈ S, (1 : ℝ) / p| ≤
      1 / Real.log A := by
    rw [hlogP]
    have hlo : -∑ p ∈ S, (1 : ℝ) / p - ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        ∑ p ∈ S, Real.log (1 - 1 / (p : ℝ)) := by
      have hs := Finset.sum_le_sum (fun p hp => (hterm_le p hp).1)
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
      exact hs
    have hhi : ∑ p ∈ S, Real.log (1 - 1 / (p : ℝ)) ≤ -∑ p ∈ S, (1 : ℝ) / p := by
      have hs := Finset.sum_le_sum (fun p hp => (hterm_le p hp).2)
      rwa [Finset.sum_neg_distrib] at hs
    rw [abs_le]
    constructor <;> linarith
  have hM := sum_inv_sdiff_bound hA hAB
  have htri : |Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + (Real.log (Real.log B) - Real.log (Real.log A))| ≤
      |Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + ∑ p ∈ S, (1 : ℝ) / p| +
      |(∑ p ∈ S, (1 : ℝ) / p) - (Real.log (Real.log B) - Real.log (Real.log A))| := by
    have heq : Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + (Real.log (Real.log B) - Real.log (Real.log A)) =
        (Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + ∑ p ∈ S, (1 : ℝ) / p) +
        -((∑ p ∈ S, (1 : ℝ) / p) - (Real.log (Real.log B) - Real.log (Real.log A))) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  have hcomb : 1 / Real.log A + (3 * mertens1Const + 1) / Real.log A =
      (3 * mertens1Const + 2) / Real.log A := by ring
  linarith

private lemma log_log_floor_close {t : ℝ} (ht : 4 ≤ t) :
    Real.log (Real.log ⌊t⌋₊) ≤ Real.log (Real.log t) ∧
      Real.log (Real.log t) ≤ Real.log (Real.log ⌊t⌋₊) + Real.log 2 / Real.log ⌊t⌋₊ := by
  have hfl2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hflR : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl2
  have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hl_fl : 0 < Real.log ⌊t⌋₊ := Real.log_pos (by linarith)
  have hl_le : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log (by linarith) hle
  have hl_t : 0 < Real.log t := lt_of_lt_of_le hl_fl hl_le
  have hl_hi : Real.log t ≤ Real.log ⌊t⌋₊ + Real.log 2 := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  constructor
  · exact Real.log_le_log hl_fl hl_le
  · have hq := Real.log_le_sub_one_of_pos (div_pos hl_t hl_fl)
    rw [Real.log_div hl_t.ne' hl_fl.ne'] at hq
    have hdiv : Real.log t / Real.log ⌊t⌋₊ - 1 ≤ Real.log 2 / Real.log ⌊t⌋₊ := by
      rw [div_sub_one hl_fl.ne']
      exact div_le_div_of_nonneg_right (by linarith) hl_fl.le
    linarith

end Erdos687H2R1H2

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1.H2 := by
  open Real Finset Filter in
  intro c hc
  have hL_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hU_top : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_top
  have hlogU_top : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hU_top
  have hy_top : Tendsto (fun x : ℕ =>
      c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
        Real.log (Real.log (x : ℝ))) atTop atTop := by
    have hge : ∀ᶠ x : ℕ in atTop,
        (x : ℝ) ≤ c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
          Real.log (Real.log (x : ℝ)) := by
      filter_upwards [hL_top.eventually_ge_atTop (max 4 ((2 / c) ^ 2)),
        hlogU_top.eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ)]
        with x hL hlogU hx1
      have hL4 : 4 ≤ Real.log (x : ℝ) := (le_max_left _ _).trans hL
      have hLc : (2 / c) ^ 2 ≤ Real.log (x : ℝ) := (le_max_right _ _).trans hL
      have hLpos : 0 < Real.log (x : ℝ) := by linarith
      have hUpos : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos (by linarith)
      have hU_le : Real.log (Real.log (x : ℝ)) ≤ 2 * √(Real.log (x : ℝ)) := by
        have := Real.log_le_rpow_div hLpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
        rw [← Real.sqrt_eq_rpow] at this; linarith
      have hsqrt_ge : 2 / c ≤ √(Real.log (x : ℝ)) := Real.le_sqrt_of_sq_le hLc
      have hcL : Real.log (Real.log (x : ℝ)) ≤ c * Real.log (x : ℝ) := by
        have h1 : 2 ≤ c * √(Real.log (x : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hsqrt_ge hc.le
          rwa [mul_div_cancel₀ _ hc.ne'] at this
        have h2 : 2 * √(Real.log (x : ℝ)) ≤ c * √(Real.log (x : ℝ)) * √(Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        rw [mul_assoc, Real.mul_self_sqrt hLpos.le] at h2
        linarith
      rw [le_div_iff₀ hUpos]
      have hmul1 : (x : ℝ) * Real.log (Real.log (x : ℝ)) ≤ (x : ℝ) * (c * Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hcL (by linarith)
      have hmul2 : c * (x : ℝ) * Real.log (x : ℝ) * 1 ≤
          c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogU (by positivity)
      linarith
    exact tendsto_atTop_mono' atTop hge tendsto_natCast_atTop_atTop
  have hCheb : ∀ᶠ x : ℕ in atTop,
      let y := c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
        Real.log (Real.log (x : ℝ))
      (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ (Real.log 4 + 1) * y / Real.log y :=
    hy_top.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  set C_err : ℝ := 3 * Erdos687H2R1H2.mertens1Const + 4
  have hCerr_pos : 0 < C_err := by
    have := Erdos687H2R1H2.mertens1Const_nonneg; dsimp [C_err]; linarith
  have hlog32_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [hCheb, hL_top.eventually_ge_atTop (max 16 ((2 / c) ^ 2)),
    hU_top.eventually_ge_atTop (max 4 (C_err / Real.log (3 / 2 : ℝ) + 2)),
    hlogU_top.eventually_ge_atTop 400,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 : ℝ)] with x hxCheb hLbig hUbig hlogU400 hx4
  set X : ℝ := (x : ℝ)
  set L : ℝ := Real.log X
  set U : ℝ := Real.log L
  set y : ℝ := c * X * L * Real.log U / U
  set z : ℝ := X ^ (Real.log U / (4 * U))
  let P : Finset ℕ := (Finset.Ioc (x / 2) x).filter Nat.Prime
  let S : Finset ℕ := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ L ^ 20 < p)
  let V : Finset ℕ := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
  let σ : ℝ := ∏ p ∈ S, (1 - 1 / (p : ℝ))
  have hXpos : 0 < X := by linarith
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hLbig
  have hLc : (2 / c) ^ 2 ≤ L := (le_max_right _ _).trans hLbig
  have hLpos : 0 < L := by linarith
  have hU4 : 4 ≤ U := (le_max_left _ _).trans hUbig
  have hUerr : C_err / Real.log (3 / 2 : ℝ) + 2 ≤ U := (le_max_right _ _).trans hUbig
  have hUpos : 0 < U := by linarith
  have hlogU_pos : 0 < Real.log U := by linarith
  have hlogU_lt_U : Real.log U < U := by
    have := Real.log_le_sub_one_of_pos hUpos; linarith
  -- Show z < X / 2 so every prime p ≤ z satisfies p ∉ P
  have hz_pos : 0 < z := Real.rpow_pos_of_pos hXpos _
  have hlog_z : Real.log z = (Real.log U / (4 * U)) * L := by
    dsimp [z]; rw [Real.log_rpow hXpos]
  have hz_lt_half : z < X / 2 := by
    have hlog_half : Real.log (X / 2) = L - Real.log 2 := by
      rw [Real.log_div hXpos.ne' (by norm_num)]
    have hlt : Real.log z < Real.log (X / 2) := by
      rw [hlog_z, hlog_half]
      have hfrac : Real.log U / (4 * U) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
        linarith
      have h1 : (Real.log U / (4 * U)) * L ≤ (1 / 4) * L :=
        mul_le_mul_of_nonneg_right hfrac hLpos.le
      have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    exact (Real.log_lt_log_iff hz_pos (by linarith)).mp hlt
  -- Identify S = Nat.primesLE B \ Nat.primesLE A
  set A : ℕ := ⌊L ^ 20⌋₊
  set B : ℕ := ⌊z⌋₊
  have hL20_ge4 : 4 ≤ L ^ 20 := by
    have : (16 : ℝ) ^ 20 ≤ L ^ 20 := pow_le_pow_left₀ (by norm_num) hL16 20
    norm_num at this; linarith
  have hL20_le_z : L ^ 20 ≤ z := by
    rw [← Real.log_le_log_iff (by positivity) hz_pos, hlog_z, Real.log_pow]
    push_cast
    have hU_le_sqrt : U ≤ 2 * √L := by
      have := Real.log_le_rpow_div hLpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [← Real.sqrt_eq_rpow] at this; linarith
    have hU2 : U ^ 2 ≤ 4 * L := by
      have := pow_le_pow_left₀ hUpos.le hU_le_sqrt 2
      rw [mul_pow, Real.sq_sqrt hLpos.le] at this; linarith
    rw [show Real.log L = U from rfl, div_mul_eq_mul_div, le_div_iff₀ (show 0 < 4 * U by positivity)]
    have h1 : 20 * U * (4 * U) = 80 * U ^ 2 := by ring
    have h2 : 80 * U ^ 2 ≤ 320 * L := by linarith
    have h3 : 320 * L ≤ Real.log U * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
    linarith
  have hz_ge4 : 4 ≤ z := hL20_ge4.trans hL20_le_z
  have hA2 : 2 ≤ A := Nat.le_floor (by norm_num; linarith)
  have hAB : A ≤ B := Nat.floor_mono hL20_le_z
  have hS_eq : S = Nat.primesLE B \ Nat.primesLE A := by
    ext p
    simp only [S, P, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Nat.mem_primesLE,
      Nat.lt_succ_iff, Finset.mem_Ioc]
    have hfl : L ^ 20 < (p : ℝ) ↔ A < p := (Nat.floor_lt (by positivity)).symm
    constructor
    · rintro ⟨hpB, hpPr, _, hpgt⟩
      have hAp : A < p := hfl.mp hpgt
      exact ⟨⟨hpB, hpPr⟩, fun h => by omega⟩
    · rintro ⟨⟨hpB, hpPr⟩, hnotA⟩
      have hAp : A < p := by
        by_contra! hle
        exact hnotA ⟨hle, hpPr⟩
      have hp_notP : ¬ ((x / 2 < p ∧ p ≤ x) ∧ p.Prime) := by
        rintro ⟨⟨hgt, _⟩, _⟩
        have h1 : (p : ℝ) ≤ z := (Nat.le_floor_iff hz_pos.le).mp hpB
        have h2 : x < 2 * p := by omega
        have h3 : (x : ℝ) < 2 * (p : ℝ) := by exact_mod_cast h2
        linarith
      exact ⟨hpB, hpPr, hp_notP, hfl.mpr hAp⟩
  -- Compute log σ via log_prod_sdiff_bound and floor approximations
  have hprod_pos : 0 < σ := by
    dsimp [σ]
    apply Finset.prod_pos
    intro p hp
    have hpPr : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPr.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hM := Erdos687H2R1H2.log_prod_sdiff_bound hA2 hAB
  rw [← hS_eq] at hM
  obtain ⟨hflA_lo, hflA_hi⟩ := Erdos687H2R1H2.log_log_floor_close hL20_ge4
  obtain ⟨hflB_lo, hflB_hi⟩ := Erdos687H2R1H2.log_log_floor_close hz_ge4
  have hA2R : (2 : ℝ) ≤ A := by exact_mod_cast hA2
  have hlA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by linarith)
  have hlA_le_hlB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hAB)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hdiffB : |Real.log (Real.log (B : ℝ)) - Real.log (Real.log z)| ≤
      Real.log 2 / Real.log (A : ℝ) := by
    have h1 : Real.log 2 / Real.log (B : ℝ) ≤ Real.log 2 / Real.log (A : ℝ) :=
      div_le_div_of_nonneg_left hlog2_pos.le hlA_pos hlA_le_hlB
    rw [abs_le]; constructor <;> linarith
  have hdiffA : |Real.log (Real.log (A : ℝ)) - Real.log (Real.log (L ^ 20))| ≤
      Real.log 2 / Real.log (A : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hlog_ratio : -(Real.log (Real.log z) - Real.log (Real.log (L ^ 20))) =
      Real.log (80 * U ^ 2 / (L * Real.log U)) := by
    rw [hlog_z, Real.log_pow]
    push_cast
    have hlogL : Real.log L = U := rfl
    rw [hlogL]
    have hnum_pos : 0 < 20 * U := by positivity
    have hden_pos : 0 < Real.log U / (4 * U) * L := by positivity
    rw [neg_sub, ← Real.log_div hnum_pos.ne' hden_pos.ne']
    congr 1
    field_simp [hUpos.ne', hLpos.ne', hlogU_pos.ne']; ring
  -- Lower bound log A ≥ 20 * U - log 2 ≥ U ≥ C_err / log (3/2)
  have hlA_ge : C_err / Real.log (3 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have h1 : L ^ 20 < 2 * (A : ℝ) := by
      have hlt : L ^ 20 < (A : ℝ) + 1 := Nat.lt_floor_add_one (L ^ 20)
      linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h2
    push_cast at h2
    have hlogL : Real.log L = U := rfl
    rw [hlogL] at h2
    linarith
  have hlog_err : |Real.log σ - Real.log (80 * U ^ 2 / (L * Real.log U))| ≤
      Real.log (3 / 2 : ℝ) := by
    have h1 : |Real.log σ - Real.log (80 * U ^ 2 / (L * Real.log U))| ≤
        C_err / Real.log (A : ℝ) := by
      rw [← hlog_ratio, sub_neg_eq_add]
      have hsplit : Real.log σ + (Real.log (Real.log z) - Real.log (Real.log (L ^ 20))) =
          (Real.log σ + (Real.log (Real.log (B : ℝ)) - Real.log (Real.log (A : ℝ)))) +
          (Real.log (Real.log z) - Real.log (Real.log (B : ℝ))) +
          (Real.log (Real.log (A : ℝ)) - Real.log (Real.log (L ^ 20))) := by ring
      rw [hsplit]
      have htri1 := abs_add_le
        ((Real.log σ + (Real.log (Real.log (B : ℝ)) - Real.log (Real.log (A : ℝ)))) +
          (Real.log (Real.log z) - Real.log (Real.log (B : ℝ))))
        (Real.log (Real.log (A : ℝ)) - Real.log (Real.log (L ^ 20)))
      have htri2 := abs_add_le
        (Real.log σ + (Real.log (Real.log (B : ℝ)) - Real.log (Real.log (A : ℝ))))
        (Real.log (Real.log z) - Real.log (Real.log (B : ℝ)))
      have hdiffB' : |Real.log (Real.log z) - Real.log (Real.log (B : ℝ))| ≤
          Real.log 2 / Real.log (A : ℝ) := by
        rw [abs_sub_comm]; exact hdiffB
      have h2div : 2 * Real.log 2 / Real.log (A : ℝ) ≤ 2 / Real.log (A : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hlA_pos.le
      have hcomb : (3 * Erdos687H2R1H2.mertens1Const + 2) / Real.log (A : ℝ) +
          Real.log 2 / Real.log (A : ℝ) + Real.log 2 / Real.log (A : ℝ) =
          (3 * Erdos687H2R1H2.mertens1Const + 2) / Real.log (A : ℝ) +
            2 * Real.log 2 / Real.log (A : ℝ) := by ring
      have hcomb2 : (3 * Erdos687H2R1H2.mertens1Const + 2) / Real.log (A : ℝ) +
          2 / Real.log (A : ℝ) = C_err / Real.log (A : ℝ) := by dsimp [C_err]; ring
      linarith
    have h2 : C_err / Real.log (A : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
      rw [div_le_iff₀ hlA_pos]
      have := mul_le_mul_of_nonneg_left hlA_ge hlog32_pos.le
      rwa [mul_div_cancel₀ _ hlog32_pos.ne'] at this
    exact h1.trans h2
  -- Exponentiate to get 40 ≤ σ / (U^2 / (L log U)) ≤ 120
  have htarget_pos : 0 < 80 * U ^ 2 / (L * Real.log U) := by positivity
  have hσ_lo : 40 * U ^ 2 / (L * Real.log U) ≤ σ := by
    have h1 := (abs_le.mp hlog_err).1
    have h2 : Real.log (40 * U ^ 2 / (L * Real.log U)) ≤ Real.log σ := by
      have h40_le : 40 * U ^ 2 / (L * Real.log U) ≤ (2 / 3 : ℝ) * (80 * U ^ 2 / (L * Real.log U)) := by
        have : (0 : ℝ) ≤ U ^ 2 / (L * Real.log U) := by positivity
        have e1 : 40 * U ^ 2 / (L * Real.log U) = 40 * (U ^ 2 / (L * Real.log U)) := by ring
        have e2 : (2 / 3 : ℝ) * (80 * U ^ 2 / (L * Real.log U)) = (160 / 3 : ℝ) * (U ^ 2 / (L * Real.log U)) := by ring
        linarith
      have hlog40 : Real.log (40 * U ^ 2 / (L * Real.log U)) ≤
          Real.log ((2 / 3 : ℝ) * (80 * U ^ 2 / (L * Real.log U))) :=
        Real.log_le_log (by positivity) h40_le
      rw [Real.log_mul (by norm_num) htarget_pos.ne'] at hlog40
      have hlog23 : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
        rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith
    exact (Real.log_le_log_iff (by positivity) hprod_pos).mp h2
  have hσ_hi : σ ≤ 120 * U ^ 2 / (L * Real.log U) := by
    have h1 := (abs_le.mp hlog_err).2
    have h2 : Real.log σ ≤ Real.log (120 * U ^ 2 / (L * Real.log U)) := by
      have heq : 120 * U ^ 2 / (L * Real.log U) = (3 / 2 : ℝ) * (80 * U ^ 2 / (L * Real.log U)) := by ring
      rw [heq, Real.log_mul (by norm_num) htarget_pos.ne']
      linarith
    exact (Real.log_le_log_iff hprod_pos (by positivity)).mp h2
  -- Chebyshev bound on V.card * σ
  have hV_le : (V.card : ℝ) ≤ 2.4 * c * X * Real.log U / U := by
    have hV_sub : V ⊆ Nat.primesLE ⌊y⌋₊ := by
      intro q hq
      obtain ⟨hqIoc, hqPr⟩ := Finset.mem_filter.mp hq
      exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp hqIoc).2, hqPr⟩
    have hV_card : (V.card : ℝ) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      exact_mod_cast Finset.card_le_card hV_sub
    have hX_le_y : X ≤ y := by
      have hU_le : U ≤ 2 * √L := by
        have := Real.log_le_rpow_div hLpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
        rw [← Real.sqrt_eq_rpow] at this; linarith
      have hsqrt_ge : 2 / c ≤ √L := Real.le_sqrt_of_sq_le hLc
      have hcL : U ≤ c * L := by
        have h1 : 2 ≤ c * √L := by
          have := mul_le_mul_of_nonneg_left hsqrt_ge hc.le
          rwa [mul_div_cancel₀ _ hc.ne'] at this
        have h2 : 2 * √L ≤ c * √L * √L := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        rw [mul_assoc, Real.mul_self_sqrt hLpos.le] at h2
        linarith
      dsimp [y]
      rw [le_div_iff₀ hUpos]
      have h1 : X * U ≤ X * (c * L) := mul_le_mul_of_nonneg_left hcL hXpos.le
      have h2 : c * X * L * 1 ≤ c * X * L * Real.log U :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hy_pos : 0 < y := lt_of_lt_of_le hXpos hX_le_y
    have hL_le_logy : L ≤ Real.log y := Real.log_le_log hXpos hX_le_y
    have hlog4 : Real.log 4 + 1 ≤ 2.4 := by
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    have hCheb' : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ (Real.log 4 + 1) * y / Real.log y := hxCheb
    calc (V.card : ℝ)
        ≤ (Real.log 4 + 1) * y / Real.log y := hV_card.trans hCheb'
      _ ≤ (Real.log 4 + 1) * y / L :=
          div_le_div_of_nonneg_left (by positivity) hLpos hL_le_logy
      _ ≤ 2.4 * y / L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlog4 hy_pos.le) hLpos.le
      _ = 2.4 * c * X * Real.log U / U := by dsimp [y]; field_simp [hLpos.ne', hUpos.ne']
  have hVσ : (V.card : ℝ) * σ ≤ 400 * c * X * U / L := by
    calc (V.card : ℝ) * σ
        ≤ (2.4 * c * X * Real.log U / U) * (120 * U ^ 2 / (L * Real.log U)) :=
          mul_le_mul hV_le hσ_hi hprod_pos.le (by positivity)
      _ = 288 * c * X * U / L := by field_simp [hUpos.ne', hLpos.ne', hlogU_pos.ne']; ring
      _ ≤ 400 * c * X * U / L := by
          have : (0 : ℝ) ≤ c * X * U / L := by positivity
          have e1 : 288 * c * X * U / L = 288 * (c * X * U / L) := by ring
          have e2 : 400 * c * X * U / L = 400 * (c * X * U / L) := by ring
          linarith
  exact ⟨hσ_lo, hσ_hi, hVσ⟩
