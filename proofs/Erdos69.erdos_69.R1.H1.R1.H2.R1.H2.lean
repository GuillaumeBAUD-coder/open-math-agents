import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H2_R1
import Mathlib

/-! Decay of the independent Euler product for the near shifts in Erdős 69.
At each height the signs among the subsets cancel the sine terms exactly.
The first height gives a loss at least 1/2^K, and the square-angle estimate
summed over all heights bounds the loss by 1. Mertens' reciprocal-prime sum
dominates the primes excluded by the modulus.
The Mertens estimates below are adapted from the merged Erdős 16 Romanoff
step by @senamakel. The prime-divisor count is from the merged far-shift
step for Erdős 69 by @marcusbuffett. -/

open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
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

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
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
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
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
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
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

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
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
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring


/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]


end OMALib.Mertens

open Finset Real
open OMA.R_Erdos69_erdos_69_R1_H1_R1 (geom_two sign_sum)
namespace Decay69
noncomputable def loss (K H : ℕ) (q : ℝ) : ℝ :=
  ∑ h ∈ Ico (K+1) (K+H+1), 2^K * (1-cos (2*π*q/2^h))
lemma cube (K H : ℕ) (hk : 0<K) (q : ℝ) :
    ∑ a ∈ (range K).powerset ×ˢ Ico (K+1) (K+H+1),
      (Complex.exp ((2*π*(q*((-1:ℝ)^a.1.card/2^a.2)):ℝ)*Complex.I)-1) =
      ((-loss K H q : ℝ):ℂ) := by
  classical
  let θ (h : ℕ) := 2*π*q/2^h
  have hphase (E : Finset ℕ) (h : ℕ) :
      Complex.exp ((2*π*(q*((-1:ℝ)^E.card/2^h)):ℝ)*Complex.I)-1 =
      ((cos (θ h)-1:ℝ):ℂ) + (↑((-1:ℝ)^E.card):ℂ) * ((sin (θ h):ℂ)*Complex.I) := by
    rw [show 2*π*(q*((-1:ℝ)^E.card/2^h)) = (-1:ℝ)^E.card * θ h by dsimp [θ]; ring]
    rw [Complex.exp_mul_I]
    rcases neg_one_pow_eq_or ℝ E.card with he | he <;> rw [he] <;> simp <;> ring
  simp only [sum_product,hphase]
  rw [sum_comm]
  unfold loss
  push_cast
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro h _
  have hs : (∑ i ∈ (range K).powerset, (-1:ℂ)^i.card) = 0 := by exact_mod_cast sign_sum K hk
  rw [sum_add_distrib,← sum_mul,hs]
  simp [θ]
  ring

lemma loss_bounds (K H : ℕ) (hH : 0<H) (q : ℝ) (hq : 1≤q)
    (hsmall : q ≤ (2:ℝ)^K) (hbig : (2*π*q)^2 ≤ (2:ℝ)^K) :
    1/(2:ℝ)^K ≤ loss K H q ∧ loss K H q ≤ 1 := by
  let B := (2:ℝ)^K
  have hB : 0<B := by positivity
  have hq0 : 0<q := by linarith
  constructor
  · have hθ : |π*q/B| ≤ π := by
      rw [abs_of_pos (by positivity),div_le_iff₀ hB]
      exact mul_le_mul_of_nonneg_left hsmall pi_pos.le
    have hcos := Real.cos_le_one_sub_mul_cos_sq hθ
    have hl : 2*q^2/B^2 ≤ 1-cos (π*q/B) := by
      convert (le_sub_comm.mp hcos) using 1 <;> field_simp
    have hb : 1/B ≤ B*(1-cos (π*q/B)) := calc
      1/B ≤ B*(2*q^2/B^2) := by
        field_simp
        nlinarith [sq_nonneg (q-1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hB.le
    have ht : 2*π*q/(2:ℝ)^(K+1) = π*q/B := by dsimp [B]; rw [pow_succ]; ring
    unfold loss
    refine le_trans ?_ (single_le_sum (f := fun h : ℕ => (2:ℝ)^K*(1-cos (2*π*q/2^h)))
      (fun i _ => mul_nonneg hB.le (sub_nonneg.mpr (cos_le_one _)))
      (show K+1 ∈ Ico (K+1) (K+H+1) by simp; omega))
    simpa only [ht] using hb
  · calc
      loss K H q ≤ ∑ h ∈ Ico (K+1) (K+H+1), (2*π*q)^2 * ((2:ℝ)^K/(2^h)^2) := by
        apply sum_le_sum
        intro h _
        have hh := Real.one_sub_sq_div_two_le_cos (x := 2*π*q/2^h)
        calc
          _ ≤ (2:ℝ)^K * (2*π*q/2^h)^2 := by
            apply mul_le_mul_of_nonneg_left _ hB.le
            linarith [sq_nonneg (2*π*q/2^h)]
          _ = _ := by ring
      _ = (2*π*q)^2 * ((1-1/((2:ℝ)^H)^2)/(3*B)) := by rw [←mul_sum,geom_two]
      _ ≤ (2*π*q)^2 * (1/(3*B)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [show 0≤1/((2:ℝ)^H)^2 by positivity]
      _ ≤ 1 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
end Decay69

open Finset Real
open OMALib.Mertens
namespace Decay69
noncomputable def good (R : ℝ) (Q : ℕ) := (range (⌊R⌋₊+1)).filter fun p : ℕ => p.Prime ∧ ¬ p ∣ Q ∧ (p:ℝ)≤R

lemma countQ (Q : ℕ) (hQ : 0<Q) : (Q.primeFactors.card:ℝ) ≤ 2 * log Q := by
  have hh : 2^Q.primeFactors.card ≤ Q := calc
    _ = ∏ _p ∈ Q.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ Q.primeFactors, p := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ _ := Nat.le_of_dvd hQ (Nat.prod_primeFactors_dvd _)
  have h := log_le_log (by positivity) (show (2:ℝ)^Q.primeFactors.card ≤ Q by exact_mod_cast hh)
  rw [log_pow] at h
  have hj := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ log 2 by linarith [log_two_gt_d9])
    (show 0 ≤ (Q.primeFactors.card:ℝ) by positivity)
  linarith only [h,hj]

lemma mass (R : ℝ) (hR : 2≤R) (Q : ℕ) (hQ : 0<Q) :
    log (log R) - mertens2Const - 2*log Q ≤ ∑ p ∈ good R Q, (1:ℝ)/p := by
  classical
  let P := Nat.primesLE ⌊R⌋₊
  let B := P.filter (fun p => p ∣ Q)
  have hb : B ⊆ Q.primeFactors := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp hp1).2,hp2,hQ.ne'⟩
  have hgood : P.filter (fun p => ¬p∣Q) = good R Q := by
    ext p
    simp only [P,good,mem_filter,Nat.mem_primesLE,mem_range,Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨hp,hpr⟩,hd⟩
      exact ⟨hp,hpr,hd,(Nat.le_floor_iff (by linarith : 0≤R)).mp hp⟩
    · tauto
  have hsplit := sum_filter_add_sum_filter_not P (fun p => p∣Q) (fun p => (1:ℝ)/p)
  rw [hgood] at hsplit
  have hsum : (∑ p ∈ B,(1:ℝ)/p) ≤ Q.primeFactors.card := calc
    _ ≤ ∑ _ ∈ B,(1:ℝ) := sum_le_sum fun p hp => by
      have hpr := Nat.prime_of_mem_primeFactors (hb hp)
      have hp2 : (2:ℝ)≤p := by exact_mod_cast hpr.two_le
      apply (div_le_iff₀ (by linarith)).2
      linarith
    _ ≤ _ := by simpa using (show (B.card:ℝ) ≤ Q.primeFactors.card by exact_mod_cast card_le_card hb)
  have hc := countQ Q hQ
  have hm := (abs_le.mp (abs_sum_inv_sub_log_log_le R hR)).1
  change (∑ p ∈ B,(1:ℝ)/p) + _ = ∑ p ∈ P, (1:ℝ)/p at hsplit
  change _ ≤ (∑ p ∈ P,(1:ℝ)/p) - _ at hm
  linarith

lemma prod_bound (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (d : ℝ) (hd : 0≤d) (hd1 : d≤1)
    (hlarge : 3 ≤ d * ∑ p ∈ P, (1:ℝ)/p) :
    ‖∏ p ∈ P, (1+ ((-d:ℝ):ℂ)/(p:ℂ))‖ ≤ 1/8 := calc
  _ = ∏ p ∈ P, ‖1+ ((-d:ℝ):ℂ)/(p:ℂ)‖ := norm_prod _ _
  _ ≤ ∏ p ∈ P, exp (-d/p) := by
    apply prod_le_prod (fun _ _ => norm_nonneg _)
    intro p h
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    have hpos : 0 ≤ 1 + -d / (p:ℝ) := by
      have hh : d/(p:ℝ) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      rw [neg_div]; linarith
    rw [show 1+ ((-d:ℝ):ℂ)/(p:ℂ) = ((1 + -d/(p:ℝ):ℝ):ℂ) by push_cast; ring,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos]
    linarith [Real.add_one_le_exp (-d/p)]
  _ = exp (-(d*∑ p ∈ P, (1:ℝ)/p)) := by rw [← Real.exp_sum,mul_sum,←sum_neg_distrib]; congr 1; apply sum_congr rfl; intros; ring
  _ ≤ exp (-3) := exp_le_exp.mpr (by linarith)
  _ ≤ _ := by
    rw [exp_neg,show (3:ℝ) = (3:ℕ)*1 by norm_num,exp_nat_mul]
    rw [← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    exact (show (8:ℝ) = 2^3 by norm_num).le.trans (pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _)
end Decay69

open Finset Filter Real OMALib.Mertens Decay69
theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1.H2 := by
  intro q hq
  have hlt := tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  have he := (tendsto_exp_div_pow_atTop 11).comp hlt
  let A := max mertens2Const (2*(2*π*q)^2 + 2*q + 10)
  filter_upwards [Numeric69.growth A,he.eventually_ge_atTop 20] with x hx hexp
  let w := log (log (x:ℝ))
  let l := log w
  let K := ⌊2*log l/log 2⌋₊
  let H := ⌊l^2⌋₊
  let R := (x:ℝ)^(1/w^2)
  obtain ⟨hx,hA,hl,_,_,_,hR,_,heq⟩ := hx
  change A ≤ l at hA
  change 100 ≤ l at hl
  change A ≤ R at hR
  change log (log R) = w - 2*l at heq
  change 20 ≤ exp l / l^11 at hexp
  have hlpos : 0<l := by linarith
  have hwpos : 0<w := by
    apply log_pos
    apply (lt_log_iff_exp_lt (by exact_mod_cast (show 0<x by omega) : 0<(x:ℝ))).mpr
    have hx' : (256:ℝ)≤x := by exact_mod_cast hx
    linarith [exp_one_lt_d9]
  have hwbig : 20*l^11 ≤ w := by
    have hh := (le_div_iff₀ (by positivity : 0<l^11)).mp hexp
    rwa [show exp l=w from exp_log hwpos] at hh
  have hC : mertens2Const≤l := (le_max_left ..).trans hA
  have hA2 : 2*(2*π*q)^2 + 2*q + 10 ≤ l := (le_max_right ..).trans hA
  have hR2 : 2≤R := by have hh := (le_max_right mertens2Const (2*(2*π*q)^2 + 2*q + 10)).trans hR; nlinarith [sq_nonneg (2*π*q),show 0≤(q:ℝ) by positivity]
  have hq1 : 1≤(q:ℝ) := by exact_mod_cast hq
  obtain ⟨hk,hK1,hK2⟩ := Numeric69.floor_power l hl
  change 0<K at hk
  change (2:ℝ)^K ≤ l^2 at hK1
  change l^2 ≤ 2*(2:ℝ)^K at hK2
  have hll : l≤l^2 := by nlinarith [sq_nonneg (l-1)]
  have hH : 1≤H := Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ)≤l^2 by linarith))
  obtain ⟨hd,hd1⟩ := loss_bounds K H hH q hq1 (by linarith [sq_nonneg (2*π*q)]) (by linarith)
  have hl11 : l^2≤l^11 := pow_le_pow_right₀ (by linarith : 1≤l) (by decide : 2≤11)
  dsimp only
  intro Q hQ hQmax
  change (Q:ℝ) ≤ exp (4*l^11) at hQmax
  have hlogQ := log_le_log (by exact_mod_cast hQ : 0<(Q:ℝ)) hQmax
  rw [log_exp] at hlogQ
  have hm := mass R hR2 Q hQ
  rw [heq] at hm
  have hm3 : 3*(2:ℝ)^K ≤ ∑ p ∈ good R Q, (1:ℝ)/p := by linarith
  have hpos : 0<(2:ℝ)^K := by positivity
  have hdpos : 0 ≤ loss K H q := (by positivity : (0:ℝ)≤1/2^K).trans hd
  have hlarge : 3 ≤ loss K H q * ∑ p ∈ good R Q, (1:ℝ)/p := calc
    3 = 1/(2:ℝ)^K * (3*2^K) := by field_simp
    _ ≤ _ := mul_le_mul hd hm3 (by positivity) hdpos
  have hb := prod_bound (good R Q) (fun p hp => (mem_filter.mp hp).2.1) _ hdpos hd1 hlarge
  change ‖∏ p ∈ good R Q, (1 + (∑ a ∈ (range K).powerset ×ˢ Ico (K+1) (K+H+1),
    (Complex.exp ((2*π*((q:ℝ)*((-1:ℝ)^a.1.card/2^a.2)):ℝ)*Complex.I)-1))/(p:ℂ))‖ ≤ 1/8
  rw [cube K H hk]; exact hb 
