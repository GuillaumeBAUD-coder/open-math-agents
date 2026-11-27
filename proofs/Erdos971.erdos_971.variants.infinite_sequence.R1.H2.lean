import OMAReductions.R_Erdos971_erdos_971_variants_infinite_sequence_R1
import Mathlib

/-! Upper bound for the third moment of primes in residue classes at phi(d) log d.
The finite Selberg sieve and Mertens estimates are adapted from the merged
Romanoff step by @senamakel (Erdos16.erdos_16.variant.romanoff.R1.H1).

A triple of distinct primes in one class is p, p + i d, p + j d, with i < j.
For primes outside the divisors of 6 d i j (j-i) this removes three residues.
A first moment of the logarithm of a squarefree divisor bounds the truncation
of the Selberg normalizer. The singular factor for the exceptional primes
has bounded average in the two shifts, by the Euler product for its third
moment and convergence of the reciprocal-square sum. -/


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

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩

theorem log_one_sub_inv_bounds {p : ℕ} (hp : p.Prime) :
    -(1 / (p : ℝ)) - Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        Real.log (1 - 1 / (p : ℝ)) ∧
      Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 := by
      rw [div_div, div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

/-- **Mertens' third theorem**, explicit form. For real `z ≥ 2`,
`exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp (mertens2Const) / log z`
with `c = mertens2Const + primePowerConst / log 2`. -/
theorem prod_one_sub_inv_bounds (z : ℝ) (hz : 2 ≤ z) :
    Real.exp (-(mertens2Const + primePowerConst / Real.log 2)) / Real.log z ≤
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ Real.exp mertens2Const / Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    intro h; linarith
  have hPpos : 0 < ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP := Real.log_prod (s := Nat.primesLE ⌊z⌋₊) (f := fun p => (1 - 1 / (p : ℝ))) hne
  have hup : Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) ≤
      -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p := by
    rw [hlogP, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).2
  have hlo : -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p - primePowerConst / Real.log 2 ≤
      Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) := by
    rw [hlogP]
    have hK := sum_log_div_mul_sub_one_le (Nat.primesLE ⌊z⌋₊)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK' : ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        primePowerConst / Real.log 2 := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hK hl2.le
    have hs := Finset.sum_le_sum (s := Nat.primesLE ⌊z⌋₊) fun p hp =>
      (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).1
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    linarith
  have hM := abs_sum_inv_sub_log_log_le z hz
  rw [abs_le] at hM
  have hexp : ∀ t : ℝ, Real.exp t / Real.log z = Real.exp (t - Real.log (Real.log z)) := by
    intro t
    rw [Real.exp_sub, Real.exp_log hlz]
  rw [hexp, hexp, ← Real.exp_log hPpos]
  constructor
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]

/-- **Mertens' third theorem**, existential form: there are constants `0 < c₁` and `c₂` with
`c₁ / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ c₂ / log z` for all real `z ≥ 2`. -/
theorem mertens3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℝ, 2 ≤ z →
    c₁ / Real.log z ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ c₂ / Real.log z :=
  ⟨_, _, Real.exp_pos _, Real.exp_pos _, prod_one_sub_inv_bounds⟩


/-- Upper half of Mertens' second theorem for any subset of the primes, for instance the primes
in a residue class: `∑_{p ≤ x, P p} 1 / p ≤ log log x + mertens2Const` for real `x ≥ 2`. -/
theorem sum_inv_filter_le (P : ℕ → Prop) [DecidablePred P] (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      Real.log (Real.log x) + mertens2Const := by
  have h := abs_sum_inv_sub_log_log_le x hx
  rw [abs_le] at h
  have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith [h.2]

end OMALib.Mertens


open scoped Classical
open Finset

namespace OMALib.Sieve

variable {ι : Type*} [DecidableEq ι]

/-- The Selberg function `h(p) = g(p)/(1 - g(p))` attached to a local density `g`. -/
noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

/-- Selberg's normaliser `G = Σ_{S ∈ D} Π_{p ∈ S} h(p)` for a support family `D`. -/
noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

/-- The optimal Selberg weights
`λ_S = (-1)^{|S|} (Π_{p∈S} g(p)⁻¹) G⁻¹ Σ_{T ∈ D, S ⊆ T} Π_{p∈T} h(p)`. -/
noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

/-- Inclusion-exclusion over an interval `[U, T]` of the subset lattice. -/
theorem sum_interval_neg_one_pow {U T : Finset ι} (hUT : U ⊆ T) :
    ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card = if T = U then (-1) ^ U.card else 0 := by
  have h1 : ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card
      = ∑ V ∈ (T \ U).powerset, (-1 : ℝ) ^ U.card * (-1) ^ V.card := by
    refine Finset.sum_nbij' (fun S => S \ U) (fun V => U ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS ⊢
      exact sdiff_subset_sdiff hS.1 le_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hV ⊢
      refine ⟨union_subset hUT (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset, mem_coe] at hV
      have : Disjoint U V := by
        rw [disjoint_iff_ne]; intro a ha b hb hab; subst hab
        have := hV hb; simp at this; exact this.2 ha
      exact union_sdiff_cancel_left this
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      rw [← pow_add, add_comm, card_sdiff_add_card_eq_card hS.2]
  have h2 : ∑ V ∈ (T \ U).powerset, ((-1 : ℝ)) ^ V.card = if T \ U = ∅ then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := T \ U))
    push_cast at this
    rw [this]
  rw [h1, ← mul_sum, h2]
  have : T \ U = ∅ ↔ T = U := by
    constructor
    · intro h; exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h) hUT
    · intro h; subst h; simp
  by_cases hT : T = U
  · simp [hT]
  · rw [if_neg (by rwa [this]), if_neg hT, mul_zero]

section Abstract

variable {Q : Finset ι} {g : ι → ℝ} {D : Finset (Finset ι)}

theorem hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {p : ι} (hp : p ∈ Q) :
    0 < hFun g p := div_pos (hg0 p hp) (by linarith [hg1 p hp])

theorem prod_hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S : Finset ι}
    (hS : S ⊆ Q) : 0 < ∏ p ∈ S, hFun g p :=
  prod_pos fun p hp => hFun_pos hg0 hg1 (hS hp)

/-- `G ≥ 1`, since the empty set contributes `1`. -/
theorem one_le_selbergG (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : 1 ≤ selbergG g D := by
  unfold selbergG
  have := single_le_sum (f := fun S => ∏ p ∈ S, hFun g p)
    (fun S hS => (prod_hFun_pos hg0 hg1 (hDQ S hS)).le) hemp
  simpa using this

theorem selbergWeight_mul_prod (hg0 : ∀ p ∈ Q, 0 < g p) {S : Finset ι} (hS : S ⊆ Q) :
    selbergWeight g D S * ∏ p ∈ S, g p
      = (-1) ^ S.card / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p := by
  unfold selbergWeight
  have h : (∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp => inv_mul_cancel₀ (hg0 p (hS hp)).ne'
  calc _ = (-1) ^ S.card / selbergG g D * (∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p) *
        ((∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p) := by ring
    _ = _ := by rw [h, mul_one]

/-- The diagonalising variables `y_U = Σ_{S ∈ D, U ⊆ S} λ_S g(S)` of the Selberg weights. -/
theorem selbergY (hg0 : ∀ p ∈ Q, 0 < g p) (hDQ : ∀ S ∈ D, S ⊆ Q)
    (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (U : Finset ι) :
    ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / selbergG g D else 0 := by
  set G := selbergG g D
  set hS : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have e1 : ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = ∑ S ∈ D, ∑ T ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun S hSD => ?_
    by_cases hU : U ⊆ S
    · rw [if_pos hU, selbergWeight_mul_prod hg0 (hDQ S hSD), mul_sum, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      by_cases hST : S ⊆ T <;> simp [hU, hST, hS, G]
    · rw [if_neg hU]; symm
      exact sum_eq_zero fun T _ => by simp [hU]
  rw [e1, sum_comm]
  have e2 : ∀ T ∈ D, (∑ S ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0)
      = if T = U then (-1) ^ U.card / G * hS U else 0 := by
    intro T hT
    rw [← sum_filter]
    by_cases hUT : U ⊆ T
    · have hf : D.filter (fun S => U ⊆ S ∧ S ⊆ T) = T.powerset.filter (fun S => U ⊆ S) := by
        ext S; simp only [mem_filter, mem_powerset]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩; exact ⟨hdown T hT S h2, h1, h2⟩
      rw [hf, ← sum_mul, ← sum_div, sum_interval_neg_one_pow hUT]
      by_cases hTU : T = U
      · subst hTU; simp
      · simp [hTU]
    · have hTU : T ≠ U := by rintro rfl; exact hUT le_rfl
      rw [if_neg hTU]
      refine sum_eq_zero fun S hS' => ?_
      simp only [mem_filter] at hS'
      exact absurd (hS'.2.1.trans hS'.2.2) hUT
  rw [sum_congr rfl e2, sum_ite_eq']
  split_ifs <;> ring

theorem prod_union_eq (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S₁ S₂ : Finset ι}
    (h₁ : S₁ ⊆ Q) (h₂ : S₂ ⊆ Q) :
    ∏ p ∈ S₁ ∪ S₂, g p = (∏ p ∈ S₁, g p) * (∏ p ∈ S₂, g p) *
      ∑ U ∈ Q.powerset, if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0 := by
  have hinv : (∏ p ∈ S₁ ∩ S₂, g p)⁻¹ = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← prod_inv_distrib]
    have : ∀ p ∈ S₁ ∩ S₂, (g p)⁻¹ = 1 + (hFun g p)⁻¹ := by
      intro p hp
      have hp' : p ∈ Q := h₁ (mem_inter.mp hp).1
      have a := hg0 p hp'; have b := hg1 p hp'
      unfold hFun; rw [inv_div]; field_simp; ring
    rw [prod_congr rfl this, prod_one_add]
    exact sum_congr rfl fun U _ => by rw [prod_inv_distrib]
  have hsum : ∑ U ∈ Q.powerset, (if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0)
      = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_filter, mem_powerset, subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans h₁, h⟩
  have hne : (∏ p ∈ S₁ ∩ S₂, g p) ≠ 0 :=
    (prod_pos fun p hp => hg0 p (h₁ (mem_inter.mp hp).1)).ne'
  rw [hsum, ← hinv, ← prod_union_inter (s₁ := S₁) (s₂ := S₂)]
  field_simp

/-- The Selberg quadratic form evaluated at the optimal weights equals `1 / G`. -/
theorem selberg_mainTerm (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D) :
    ∑ S₁ ∈ D, ∑ S₂ ∈ D, selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
      = 1 / selbergG g D := by
  set G := selbergG g D with hG
  set a : Finset ι → ℝ := fun S => selbergWeight g D S * ∏ p ∈ S, g p
  set w : Finset ι → ℝ := fun U => (∏ p ∈ U, hFun g p)⁻¹
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have e1 : ∀ S₁ ∈ D, ∀ S₂ ∈ D,
      selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
        = ∑ U ∈ Q.powerset, w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0)) := by
    intro S₁ h₁ S₂ h₂
    rw [prod_union_eq hg0 hg1 (hDQ _ h₁) (hDQ _ h₂), mul_sum, mul_sum]
    refine sum_congr rfl fun U _ => ?_
    by_cases u1 : U ⊆ S₁ <;> by_cases u2 : U ⊆ S₂ <;> simp [u1, u2, a, w] <;> ring
  rw [sum_congr rfl fun S₁ h₁ => sum_congr rfl fun S₂ h₂ => e1 S₁ h₁ S₂ h₂]
  have eswap : ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∑ U ∈ Q.powerset,
      w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0))
      = ∑ U ∈ Q.powerset, w U * ((∑ S ∈ D with U ⊆ S, a S) * (∑ S ∈ D with U ⊆ S, a S)) := by
    simp_rw [sum_filter, sum_mul_sum, mul_sum]
    conv_lhs => arg 2; ext S₁; rw [sum_comm]
    rw [sum_comm]
  rw [eswap]
  have hy : ∀ U, ∑ S ∈ D with U ⊆ S, a S
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0 :=
    selbergY hg0 hDQ hdown
  simp_rw [hy]
  have e3 : ∀ U ∈ Q.powerset, w U * ((if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0) *
      (if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0))
      = if U ∈ D then (∏ p ∈ U, hFun g p) / G ^ 2 else 0 := by
    intro U hU
    split_ifs with hUD
    · have hpos := prod_hFun_pos hg0 hg1 (hDQ U hUD)
      simp only [w]
      field_simp
      rw [← pow_mul, mul_comm (U.card) 2, pow_mul]; simp
    · simp
  rw [sum_congr rfl e3, ← sum_filter]
  have : Q.powerset.filter (fun U => U ∈ D) = D := by
    ext U; simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hDQ U h, h⟩⟩
  rw [this, ← sum_div]
  change G / G ^ 2 = 1 / G
  field_simp

/-- The optimal Selberg weights satisfy `|λ_S| ≤ 1`. -/
theorem abs_selbergWeight_le (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    {S : Finset ι} (hS : S ∈ D) : |selbergWeight g D S| ≤ 1 := by
  set G := selbergG g D with hG
  set hp : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have hSQ := hDQ S hS
  have hnn : ∀ T ⊆ Q, 0 ≤ hp T := fun T hT => (prod_hFun_pos hg0 hg1 hT).le
  have hginv : 0 < ∏ p ∈ S, (g p)⁻¹ := prod_pos fun p h => inv_pos.mpr (hg0 p (hSQ h))
  have habs : |selbergWeight g D S|
      = (∏ p ∈ S, (g p)⁻¹) * (∑ T ∈ D with S ⊆ T, hp T) / G := by
    unfold selbergWeight
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hginv, abs_of_pos (by linarith : (0:ℝ) < G),
      abs_of_nonneg (sum_nonneg fun T hT => hnn T (hDQ T (mem_filter.mp hT).1))]
    ring
  rw [habs, div_le_one (by linarith)]
  have key : ∀ T ∈ D.filter (fun T => S ⊆ T),
      (∏ p ∈ S, (g p)⁻¹) * hp T = ∑ W ∈ S.powerset, hp (W ∪ (T \ S)) := by
    intro T hT
    have hST := (mem_filter.mp hT).2
    have h1 : hp T = hp S * hp (T \ S) := by
      simp only [hp]; rw [mul_comm, prod_sdiff hST]
    have h2 : (∏ p ∈ S, (g p)⁻¹) * hp S = ∏ p ∈ S, (1 + hFun g p) := by
      simp only [hp]; rw [← prod_mul_distrib]
      refine prod_congr rfl fun p h => ?_
      have a := hg0 p (hSQ h); have b := hg1 p (hSQ h)
      have c : 1 - g p ≠ 0 := by linarith
      unfold hFun; field_simp; ring
    rw [h1, ← mul_assoc, h2, prod_one_add, sum_mul]
    refine sum_congr rfl fun W hW => ?_
    simp only [hp]
    rw [prod_union]
    exact disjoint_of_subset_left (mem_powerset.mp hW) disjoint_sdiff
  rw [mul_sum, sum_congr rfl key, sum_comm, ← sum_product']
  rw [← sum_image (s := S.powerset ×ˢ D.filter (fun T => S ⊆ T)) (g := fun x => x.1 ∪ (x.2 \ S))
    (f := hp)]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      simp only [mem_image, mem_product, mem_powerset, mem_filter] at hU
      obtain ⟨⟨W, T⟩, ⟨hW, hT, _⟩, rfl⟩ := hU
      exact hdown T hT _ (union_subset (hW.trans (by assumption)) sdiff_subset)
    · intro U hU _
      exact hnn U (hDQ U hU)
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powerset, mem_filter] at hx hy
    simp only at hxy
    have e1 : x.1 = (x.1 ∪ (x.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hx.1]
    have e2 : y.1 = (y.1 ∪ (y.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hy.1]
    have f1 : x.2 = S ∪ (x.1 ∪ (x.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hx.1, union_sdiff_of_subset hx.2.2]
    have f2 : y.2 = S ∪ (y.1 ∪ (y.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hy.1, union_sdiff_of_subset hy.2.2]
    exact Prod.ext (by rw [e1, e2, hxy]) (by rw [f1, f2, hxy])

theorem selbergWeight_empty (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : selbergWeight g D ∅ = 1 := by
  have hG1 : 1 ≤ selbergG g D := one_le_selbergG hg0 hg1 hDQ hemp
  unfold selbergWeight
  simp only [card_empty, pow_zero, prod_empty, one_mul, empty_subset, filter_true_of_mem,
    implies_true]
  change 1 / selbergG g D * selbergG g D = 1
  field_simp

/-- **Selberg's upper-bound sieve, abstract form.**

`A` is a finite family of objects, `E a` is the set of primes dividing `a`, `Q` is the finite
set of sieving primes, and `D` is any down-closed family of subsets of `Q` containing `∅` (the
support of the Selberg weights; for the classical sieve, the sets of primes with product `< z`).
If for every `S ⊆ Q` the number of `a` divisible by all of `S` is `X * Π_{p∈S} g p + r S`, with
`0 < g p < 1`, then the number of `a` free of all primes of `Q` is at most
`X / G + Σ_{S₁, S₂ ∈ D} |r (S₁ ∪ S₂)|`, where `G = selbergG g D`. -/
theorem selberg_sieve_abstract {α : Type*} (A : Finset α) (E : α → Finset ι)
    (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    (X : ℝ) (r : Finset ι → ℝ)
    (hr : ∀ S ⊆ Q, ((A.filter (fun a => S ⊆ E a)).card : ℝ) = X * ∏ p ∈ S, g p + r S) :
    ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
  set lam := selbergWeight g D
  have step1 : ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2 := by
    rw [card_filter]; push_cast
    refine sum_le_sum fun a _ => ?_
    split_ifs with hd
    · have : (∑ S ∈ D, if S ⊆ E a then lam S else 0) = lam ∅ := by
        have e := sum_ite_eq' D ∅ lam
        rw [if_pos hemp] at e
        rw [← e]
        refine sum_congr rfl fun S hS => ?_
        by_cases hS0 : S = ∅
        · subst hS0; simp
        · have : ¬ S ⊆ E a := by
            intro h
            apply hS0
            exact subset_empty.mp fun x hx =>
              (disjoint_left.mp hd (hDQ S hS hx) (h hx)).elim
          simp [this, hS0, Ne.symm hS0]
      have e1 : lam ∅ = 1 := selbergWeight_empty hg0 hg1 hDQ hemp
      rw [this, e1]; norm_num
    · positivity
  have step2 : ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2
      = ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ) := by
    simp_rw [sq, sum_mul_sum, card_filter]
    push_cast
    rw [sum_comm]
    refine sum_congr rfl fun S₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : S₁ ⊆ E a <;> by_cases h2 : S₂ ⊆ E a <;> simp [h1, h2, union_subset_iff]
  have step3 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ)
      = X * (∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * ∏ p ∈ S₁ ∪ S₂, g p)
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₁ h₁ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₂ h₂ => ?_
    rw [hr _ (union_subset (hDQ _ h₁) (hDQ _ h₂))]; ring
  have step4 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂)
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have a1 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₁
    have a2 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₂
    calc lam S₁ * lam S₂ * r (S₁ ∪ S₂) ≤ |lam S₁ * lam S₂ * r (S₁ ∪ S₂)| := le_abs_self _
      _ = |lam S₁| * |lam S₂| * |r (S₁ ∪ S₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |r (S₁ ∪ S₂)| := by gcongr
      _ = _ := by ring
  rw [selberg_mainTerm hg0 hg1 hDQ hdown hemp] at step3
  calc _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
      rw [mul_one_div]; linarith

end Abstract

/-! ## Counting residue conditions -/


theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2 <;> (ext; simp)
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/-! ## Selberg's sieve for residue conditions -/

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

/-- The classical Selberg support: sets of primes from `Q` whose product is `< z`. -/
noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

/-- **Selberg's sieve for residue conditions.** For each prime `p ∈ Q` let `C p` be a
`p`-periodic condition on `ℕ` holding for `ω(p)` residues, with `0 < ω(p) < p`. Then the number
of `n < N` satisfying no condition `C p`, `p ∈ Q`, is at most
`N / G + Σ_{S₁,S₂ ∈ D} Π_{p ∈ S₁ ∪ S₂} ω(p)`, with `G = selbergG (ω/p) D`, for any down-closed
support family `D ∋ ∅` of subsets of `Q`. -/
theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast (hQ p hp).pos)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    simp only [g]; rw [div_lt_one this]; exact_mod_cast hω1 p hp
  set E : ℕ → Finset ℕ := fun n => Q.filter (fun p => C p n)
  set r : Finset ℕ → ℝ := fun S =>
    (((range N).filter (fun n => S ⊆ E n)).card : ℝ) - N * ∏ p ∈ S, g p
  have key := selberg_sieve_abstract (range N) E hg0 hg1 hDQ hdown hemp (N : ℝ) r
    (fun S _ => by simp only [r]; rw [add_sub_cancel])
  have hrem : ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)|
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset (hDQ _ h₁) (hDQ _ h₂)
    have hc : ((range N).filter (fun n => S₁ ∪ S₂ ⊆ E n)).card
        = ((range N).filter (fun n => ∀ p ∈ S₁ ∪ S₂, C p n)).card := by
      congr 1; ext n
      simp only [E, mem_filter, subset_iff]
      exact ⟨fun h => ⟨h.1, fun p hp => (h.2 hp).2⟩, fun h => ⟨h.1, fun p hp => ⟨hSQ hp, h.2 p hp⟩⟩⟩
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp)) N
    simp only [r]; rw [hc]
    exact this
  have k2 := key.trans (add_le_add le_rfl hrem)
  have hc : ((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card
      = ((range N).filter (fun n => Disjoint Q (E n))).card := by
    congr 1; ext n
    simp only [E, disjoint_left, mem_filter, not_and]
    exact ⟨fun h => ⟨h.1, fun p hp _ => h.2 p hp⟩, fun h => ⟨h.1, fun p hp => h.2 hp hp⟩⟩
  have hc' : (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      = (((range N).filter (fun n => Disjoint Q (E n))).card : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  exact k2

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => (hQ p (hS.1 hp)).one_lt.le

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

/-- **Selberg's sieve at level `z`, with a crude explicit remainder.** With the classical support
`levelFamily Q z` (products of primes `< z`), the number of `n < N` meeting no condition `C p`,
`p ∈ Q`, is at most `N / G + z ^ 4`. -/
theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have key := selberg_residue N Q hQ C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
    (levelFamily_down hQ) (empty_mem_levelFamily hz)
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ S₁ ∈ levelFamily Q z, ∀ S₂ ∈ levelFamily Q z,
      ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ (z : ℝ) ^ 2 := by
    intro S₁ h₁ S₂ h₂
    have h₁' := h₁; have h₂' := h₂
    simp only [levelFamily, mem_filter, mem_powerset] at h₁' h₂'
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset h₁'.1 h₂'.1
    have a : ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ ∏ p ∈ S₁ ∪ S₂, (p : ℝ) :=
      prod_le_prod (fun p _ => by positivity)
        (fun p hp => by exact_mod_cast (hω1 p (hSQ hp)).le)
    have b : ∏ p ∈ S₁ ∪ S₂, p ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
      rw [← prod_union_inter]
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hQ p (h₁'.1 (mem_inter.mp hp).1)).pos)
    have c : (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ≤ z * z :=
      Nat.mul_le_mul h₁'.2.le h₂'.2.le
    have : ((∏ p ∈ S₁ ∪ S₂, p : ℕ) : ℝ) ≤ (z : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast b.trans c
    push_cast at this
    linarith
  calc ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ)
      ≤ ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, (z : ℝ) ^ 2 :=
        sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => hterm S₁ h₁ S₂ h₂
    _ = ((levelFamily Q z).card : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

/-- `selbergG` only depends on `g` on the primes of `Q`. -/
theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]


end OMALib.Sieve


open Finset
open scoped Classical
namespace Third971

lemma cube_le (h : ℕ) : h^3 ≤ 27*h+27*h.choose 3 := by
  obtain hsmall | hbig := lt_or_ge h 3
  · interval_cases h <;> decide
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hbig
  have hc := Nat.descFactorial_eq_factorial_mul_choose (3+m) 3
  simp [Nat.descFactorial_succ,Nat.factorial] at hc
  rw [show 3+m-2 = m+1 by omega] at hc
  nlinarith only [hc, Nat.zero_le m, Nat.zero_le (m^2), Nat.zero_le (m^3)]

lemma sorted_three {T : Finset ℕ} (hc : T.card=3) :
    ∃ p q r : ℕ, p<q ∧ q<r ∧ T={p,q,r} := by
  let f := T.orderEmbOfFin hc
  refine ⟨f 0,f 1,f 2,f.strictMono (by decide),f.strictMono (by decide),?_⟩
  have h : (univ : Finset (Fin 3)) = {0,1,2} := by decide
  have hh := T.image_orderEmbOfFin_univ hc
  change image f univ = T at hh
  simpa [h] using hh.symm

lemma finite_moment (X d J : ℕ) (hd : 0<d) (hX : X < (J+1)*d)
    (A : Finset ℕ) :
    let P := Nat.primesLE X
    let H (a : ℕ) := P.filter fun p => p%d=a
    let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
    let T (v : ℕ×ℕ) := P.filter fun p => (p+v.1*d).Prime ∧ (p+v.2*d).Prime
    ∑ a ∈ A, (H a).card^3 ≤ 27*P.card + 27*∑ v ∈ U, (T v).card := by
  classical
  intro P H U T
  have hone : ∑ a ∈ A, (H a).card ≤ P.card := by
    dsimp only [H]
    rw [sum_card_fiberwise_eq_card_filter]
    exact card_filter_le _ _
  let f (z : (v : ℕ×ℕ) × ℕ) : (a : ℕ) × Finset ℕ :=
    ⟨z.2%d,{z.2,z.2+z.1.1*d,z.2+z.1.2*d}⟩
  have hsub : (A.sigma (fun a => (H a).powersetCard 3)) ⊆ (U.sigma T).image f := by
    rintro ⟨a,E⟩ ha
    obtain ⟨_,hE,hcard⟩ := (mem_sigma.mp ha).1, (mem_powersetCard.mp (mem_sigma.mp ha).2)
    change E ⊆ H a at hE
    change E.card = 3 at hcard
    obtain ⟨p,q,r,hpq,hqr,hset⟩ := sorted_three hcard
    have hp : p ∈ H a := hE (by simp [hset])
    have hq : q ∈ H a := hE (by simp [hset])
    have hr : r ∈ H a := hE (by simp [hset])
    have hpd := (mem_filter.mp hp).2
    have hqd := (mem_filter.mp hq).2
    have hrd := (mem_filter.mp hr).2
    have hPp : p ∈ P := (mem_filter.mp hp).1
    have hQp : q.Prime := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).2
    have hRp := Nat.mem_primesLE.mp (mem_filter.mp hr).1
    obtain ⟨i,hi⟩ := (Nat.modEq_iff_dvd' hpq.le).mp (hpd.trans hqd.symm)
    obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' (hpq.trans hqr).le).mp (hpd.trans hrd.symm)
    have qi : q=p+i*d := by rw [mul_comm] at hi; omega
    have rj : r=p+j*d := by rw [mul_comm] at hj; omega
    have ip : 0 < i := by
      by_contra! hh
      have hz : i=0 := by omega
      simp [hz] at qi
      omega
    have ij : i<j := by
      by_contra! hh
      have := Nat.mul_le_mul_right d hh
      omega
    have jb : j≤J := by
      by_contra! hh
      have hb := Nat.mul_le_mul_right d (show J+1 ≤ j by omega)
      have hrX := hRp.1
      omega
    refine mem_image.mpr ⟨⟨(i,j),p⟩,mem_sigma.mpr ⟨mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ip,ij.le.trans jb⟩,mem_Icc.mpr ⟨ip.trans ij,jb⟩⟩,ij⟩,
      mem_filter.mpr ⟨hPp,by simpa [← qi,← rj] using And.intro hQp hRp.2⟩⟩,?_⟩
    simp only [f,hpd,← qi,← rj,hset]
  have htwo := (card_le_card hsub).trans card_image_le
  simp only [card_sigma,card_powersetCard] at htwo
  calc
    _ ≤ ∑ a ∈ A, (27*(H a).card + 27*((H a).card.choose 3)) :=
      sum_le_sum fun a _ => cube_le _
    _ = 27*(∑ a ∈ A, (H a).card) + 27*(∑ a ∈ A, (H a).card.choose 3) := by
      rw [sum_add_distrib,mul_sum,mul_sum]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hone) (Nat.mul_le_mul_left _ htwo)

end Third971


namespace Third971
open Finset Real
open scoped Classical

noncomputable def loss (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, ((p:ℝ)/(p-1:ℝ))^3

lemma loss_pos (n : ℕ) : 0 < loss n := by
  apply prod_pos
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact pow_pos (div_pos (by linarith) (by linarith)) _

lemma recip_sq (J : ℕ) :
    (∑ n ∈ Ioc 0 J, (1:ℝ)/(n:ℝ)^2) ≤ 2-2/(J+1:ℝ) := by
  induction J with
  | zero => norm_num
  | succ j ih =>
    rw [sum_Ioc_succ_top (by omega)]
    push_cast
    have e : (1:ℝ)/((j:ℝ)+1)^2 ≤ 2/((j:ℝ)+1)-2/((j:ℝ)+1+1) := by
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) j]
    linarith

lemma mean_product (J : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ n ∈ Ioc 0 J, (∏ p ∈ n.primeFactors, (1+c/(p:ℝ))) ≤ J * exp (2*c) := by
  classical
  let P := Nat.primesLE J
  let w (T : Finset ℕ) := ∏ p ∈ T, (c/(p:ℝ))
  let v (T : Finset ℕ) := ∏ p ∈ T, p
  have hw (T : Finset ℕ) : 0 ≤ w T := prod_nonneg fun p _ => div_nonneg hc (Nat.cast_nonneg p)
  have hsub (n) (hn : n ∈ Ioc 0 J) : n.primeFactors ⊆ P := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Ioc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans
      (mem_Ioc.mp hn).2,Nat.prime_of_mem_primeFactors hp⟩
  have hcard (T : Finset ℕ) : ((Ioc 0 J).filter (fun n => T ⊆ n.primeFactors)).card ≤ J / v T := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    apply card_le_card
    intro n hn
    refine mem_filter.mpr ⟨(mem_filter.mp hn).1,?_⟩
    exact (prod_dvd_prod_of_subset T n.primeFactors (fun p => p) (mem_filter.mp hn).2).trans
      (Nat.prod_primeFactors_dvd n)
  have hloc (n) (hn : n ∈ Ioc 0 J) :
      (∏ p ∈ n.primeFactors, (1+c/(p:ℝ))) =
      ∑ T ∈ P.powerset, (if T ⊆ n.primeFactors then w T else 0) := by
    rw [prod_one_add,← sum_filter]
    have h : P.powerset.filter (fun T => T ⊆ n.primeFactors) = n.primeFactors.powerset := by
      ext T
      simp only [mem_filter,mem_powerset]
      exact ⟨And.right,fun h => ⟨h.trans (hsub n hn),h⟩⟩
    rw [h]
  have hsum : (∑ p ∈ P, (1:ℝ)/(p:ℝ)^2) ≤ 2 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (t:=Ioc 0 J) (fun p hp =>
      mem_Ioc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,(Nat.mem_primesLE.mp hp).1⟩)
      (fun p _ _ => by positivity))
    exact (recip_sq J).trans (sub_le_self _ (by positivity))
  calc
    _ = ∑ T ∈ P.powerset, ∑ n ∈ Ioc 0 J, (if T ⊆ n.primeFactors then w T else 0) := by
      rw [sum_congr rfl hloc,sum_comm]
    _ ≤ ∑ T ∈ P.powerset, ((J:ℝ)/(v T:ℝ))*w T := by
      apply sum_le_sum
      intro T hT
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hw T)
      exact (show ((((Ioc 0 J).filter (fun n => T ⊆ n.primeFactors)).card : ℕ):ℝ) ≤
        (J/v T:ℕ) by exact_mod_cast hcard T).trans Nat.cast_div_le
    _ = (J:ℝ) * ∏ p ∈ P, (1+c/(p:ℝ)^2) := by
      rw [prod_one_add,mul_sum]
      apply sum_congr rfl
      intro T _
      dsimp only [w,v]
      push_cast
      rw [show (∏ i ∈ T, c/(i:ℝ)^2) = (∏ i ∈ T, c/(i:ℝ)) / (∏ i ∈ T, (i:ℝ)) by
        rw [← prod_div_distrib]; exact prod_congr rfl fun i _ => by ring]
      ring
    _ ≤ (J:ℝ)*exp (∑ p ∈ P, c/(p:ℝ)^2) := by
      rw [Real.exp_sum]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
      exact prod_le_prod (fun p _ => by positivity) (fun p _ => by linarith [Real.add_one_le_exp (c/(p:ℝ)^2)])
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum hc
      rw [mul_sum] at hh
      simpa only [mul_one_div,mul_comm 2 c] using hh

lemma local_ninth (t : ℝ) (ht : 2 ≤ t) : (t/(t-1))^9 ≤ 1+4608/t := by
  let v := t/(t-1)
  have hden : 0 < t-1 := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : 1 ≤ v := (le_div_iff₀ hden).mpr (by linarith)
  have h2 : v ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have hv : v-1 ≤ 2/t := by
    dsimp [v]
    field_simp
    nlinarith
  have hsum : ∑ i ∈ range 9, v^i ≤ 2304 := by
    calc
      _ ≤ ∑ _i ∈ range 9, (2:ℝ)^8 := sum_le_sum fun i hi =>
        (pow_le_pow_left₀ (by linarith) h2 i).trans
          (pow_le_pow_right₀ (by norm_num) (show i ≤ 8 by have := mem_range.mp hi; omega))
      _ = _ := by norm_num
  have he := mul_le_mul hsum hv (sub_nonneg.mpr h1) (by norm_num)
  rw [geom_sum_mul] at he
  change v^9 ≤ _
  rw [show 2304 * (2/t) = 4608/t by ring] at he
  linarith

lemma mean_loss_cube (J : ℕ) : ∑ n ∈ Ioc 0 J, (loss n)^3 ≤ J*exp (2*4608) := by
  apply le_trans _ (mean_product J 4608 (by norm_num))
  refine sum_le_sum fun n _ => ?_
  unfold loss
  rw [← prod_pow]
  apply prod_le_prod
  · intro p hp
    have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    positivity
  · intro p hp
    rw [← pow_mul]
    exact local_ninth p (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)

end Third971


open Finset Real OMALib.Sieve
open scoped Classical
namespace Third971

lemma weighted_log (Q : Finset ℕ) (h v : ℕ → ℝ) (hh : ∀ p ∈ Q, 0 ≤ h p) :
    ∑ T ∈ Q.powerset, (∏ p ∈ T, h p)*(∑ p ∈ T, v p) =
      (∏ p ∈ Q, (1+h p))*(∑ p ∈ Q, (h p/(1+h p))*v p) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert a Q ha ih =>
    have hQ (p) (hp : p ∈ Q) := hh p (mem_insert_of_mem hp)
    have hab : 0 < 1+h a := by linarith [hh a (mem_insert_self _ _)]
    rw [sum_powerset_insert ha,prod_insert ha,sum_insert ha]
    have hstep : (∑ T ∈ Q.powerset, (∏ p ∈ insert a T, h p)*(∑ p ∈ insert a T, v p)) =
      h a * v a * (∑ T ∈ Q.powerset, ∏ p ∈ T, h p) +
      h a * (∑ T ∈ Q.powerset, (∏ p ∈ T, h p)*(∑ p ∈ T, v p)) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro T hT
      have hnot : a ∉ T := fun hm => ha (mem_powerset.mp hT hm)
      rw [prod_insert hnot,sum_insert hnot]; ring
    rw [hstep,← prod_one_add,ih hQ]
    field_simp
    ring

lemma normalizer_half (Q : Finset ℕ) (z : ℕ) (hz : 1<z) (g : ℕ → ℝ)
    (hp : ∀ p ∈ Q, p.Prime) (hg : ∀ p ∈ Q, 0 < g p ∧ g p < 1)
    (hsmall : ∑ p ∈ Q, g p * log p ≤ log z / 2) :
    (∏ p ∈ Q, (1+hFun g p)) / 2 ≤ selbergG g (levelFamily Q z) := by
  classical
  let h := hFun g
  let w (T : Finset ℕ) := ∏ p ∈ T, h p
  let E := ∏ p ∈ Q, (1+h p)
  let A := levelFamily Q z
  let B := Q.powerset \ A
  have hpos (p) (hq : p ∈ Q) : 0 < h p := div_pos (hg p hq).1 (sub_pos.mpr (hg p hq).2)
  have hE : 0 ≤ E := prod_nonneg fun p hq => by linarith [hpos p hq]
  have hA : A ⊆ Q.powerset := filter_subset _ _
  have hw (T) (hT : T ∈ Q.powerset) : 0 ≤ w T := prod_nonneg fun p hp' => (hpos p (mem_powerset.mp hT hp')).le
  have hl (T) (hT : T ∈ Q.powerset) :
      log ((∏ p ∈ T, p : ℕ):ℝ) = (∑ p ∈ T, log (p:ℝ)) := by
    push_cast
    rw [Real.log_prod]
    intro p hh
    exact_mod_cast (hp p (mem_powerset.mp hT hh)).ne_zero
  have heq (p) (hq : p ∈ Q) : h p / (1+h p) = g p := by
    change (g p/(1-g p)) / (1+g p/(1-g p)) = g p
    have hd : 0 < 1-g p := sub_pos.mpr (hg p hq).2
    have hden : 0 < 1+g p/(1-g p) := by positivity [ (hg p hq).1, hd ]
    apply (div_eq_iff hden.ne').mpr
    field_simp [hd.ne']
    ring
  have hweight : (∑ T ∈ Q.powerset, w T*(∑ p ∈ T, log (p:ℝ))) ≤ E*(log z/2) := by
    rw [show (∑ T ∈ Q.powerset, w T*(∑ p ∈ T, log (p:ℝ))) =
      E*(∑ p ∈ Q, (h p/(1+h p))*log p) from weighted_log Q h (fun p => log p)
        (fun p hq => (hpos p hq).le)]
    rw [sum_congr rfl (fun p hq => by rw [heq p hq])]
    exact mul_le_mul_of_nonneg_left hsmall hE
  have hzR : 1<(z:ℝ) := by exact_mod_cast hz
  have hb : (∑ T ∈ B, w T)*log z ≤ E*(log z/2) := by
    rw [sum_mul]
    apply le_trans _ hweight
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=B) (t:=Q.powerset) (sdiff_subset) ?_)
    · apply sum_le_sum
      intro T ht
      obtain ⟨htQ,htA⟩ := mem_sdiff.mp ht
      have hn : z ≤ ∏ p ∈ T, p := by
        by_contra! h'
        exact htA (mem_filter.mpr ⟨htQ,h'⟩)
      apply mul_le_mul_of_nonneg_left _ (hw T htQ)
      rw [← hl T htQ]
      exact log_le_log (by linarith) (by exact_mod_cast hn)
    · intro T hT _
      exact mul_nonneg (hw T hT) (sum_nonneg fun p hh => log_nonneg
        (by exact_mod_cast (hp p (mem_powerset.mp hT hh)).one_lt.le))
  have hlz := Real.log_pos hzR
  have hb' : (∑ T ∈ B, w T) ≤ E / 2 := by
    apply (le_of_mul_le_mul_right (a := log z) ?_ hlz)
    linarith only [hb]
  have htotal : (∑ T ∈ B, w T)+(∑ T ∈ A, w T)=E := by
    rw [sum_sdiff hA]
    exact (prod_one_add Q).symm
  change E/2 ≤ ∑ T ∈ A, w T
  linarith

end Third971


open Finset Real OMALib.Sieve
open scoped Classical
namespace Third971

def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (n + d)

theorem pairCond_periodic (d p n : ℕ) : pairCond d p n ↔ pairCond d p (n % p) := by
  unfold pairCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem pairCond_iff_of_lt {d p r : ℕ} (hp : p.Prime) (hr : r < p) :
    pairCond d p r ↔ r = 0 ∨ r + d % p = p := by
  unfold pairCond
  rw [hp.dvd_mul]
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  have e1 : p ∣ r ↔ r = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero p⟩
  have e2 : p ∣ r + d ↔ p ∣ r + d % p := by
    have : r + d = (r + d % p) + p * (d / p) := by
      have := Nat.mod_add_div d p; omega
    rw [this, Nat.dvd_add_left (dvd_mul_right p _)]
  have e3 : p ∣ r + d % p ↔ r + d % p = 0 ∨ r + d % p = p := by
    constructor
    · rintro ⟨m, hm⟩
      have : m < 2 := by
        by_contra h; push_neg at h
        have : p * 2 ≤ p * m := Nat.mul_le_mul_left _ h
        omega
      interval_cases m <;> simp_all
    · rintro (h | h) <;> rw [h]
      · exact dvd_zero p
  rw [e1, e2, e3]
  omega



def badResidue (a b q n : ℕ) : Prop := pairCond a q n ∨ pairCond b q n

lemma bad_periodic (a b q n : ℕ) : badResidue a b q n ↔ badResidue a b q (n%q) := by
  unfold badResidue; rw [pairCond_periodic a q n,pairCond_periodic b q n]

lemma bad_omega (a b q : ℕ) (hq : q.Prime) (ha : ¬q ∣ a) (hb : ¬q ∣ b)
    (hdiff : a%q ≠ b%q) : OMALib.Sieve.omega (badResidue a b) q = 3 := by
  classical
  have ha' : a%q ≠ 0 := fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hb' : b%q ≠ 0 := fun h => hb (Nat.dvd_of_mod_eq_zero h)
  have haq := Nat.mod_lt a hq.pos
  have hbq := Nat.mod_lt b hq.pos
  have hs : (range q).filter (badResidue a b q) = {0,q-a%q,q-b%q} := by
    ext n
    simp only [mem_filter,mem_range,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hn,h⟩
      simp only [badResidue,pairCond_iff_of_lt hq hn] at h
      omega
    · intro h
      have hn : n<q := by omega
      refine ⟨hn,?_⟩
      simp only [badResidue,pairCond_iff_of_lt hq hn]
      omega
  unfold OMALib.Sieve.omega
  rw [hs,card_insert_of_notMem (by simp; omega),card_insert_of_notMem (by simp; omega),card_singleton]

lemma shift_sieve (X Y z a b : ℕ) (Q : Finset ℕ) (hz : 2≤z)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 3<q ∧ q≤Y ∧ ¬q ∣ a ∧ ¬q ∣ b ∧ a%q≠b%q) :
    (((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime).card:ℝ) ≤
    (Y+1:ℝ)+(X+1:ℝ)/selbergG (fun q : ℕ => 3/(q:ℝ)) (levelFamily Q z)+(z:ℝ)^4 := by
  classical
  have hω (q) (hq : q ∈ Q) : OMALib.Sieve.omega (badResidue a b) q = 3 :=
    bad_omega a b q (hQ q hq).1 (hQ q hq).2.2.2.1 (hQ q hq).2.2.2.2.1 (hQ q hq).2.2.2.2.2
  have hs := selberg_residue_level (X+1) z hz Q (fun q hq => (hQ q hq).1)
    (badResidue a b) (bad_periodic a b)
    (fun q hq => by rw [hω q hq]; decide)
    (fun q hq => by rw [hω q hq]; exact (hQ q hq).2.1)
  rw [selbergG_congr levelFamily_subset (fun q hq => show
    (OMALib.Sieve.omega (badResidue a b) q:ℝ)/q = 3/(q:ℝ) by rw [hω q hq]; norm_num)] at hs
  let F := (range (X+1)).filter fun n => ∀ q ∈ Q, ¬badResidue a b q n
  have hsub : ((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime) ⊆ range (Y+1) ∪ F := by
    intro n hn
    obtain ⟨hnp,hna,hnb⟩ := mem_filter.mp hn
    obtain ⟨hnX,hprime⟩ := Nat.mem_primesLE.mp hnp
    by_cases hnY : n≤Y
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),?_⟩
      intro q hq hd
      obtain ⟨hqp,_,hqY,_⟩ := hQ q hq
      have hne (r : ℕ) (hr : r.Prime) (hnr : n≤r) : ¬ q ∣ r := by
        intro hdiv
        have := (Nat.prime_dvd_prime_iff_eq hqp hr).mp hdiv
        omega
      rcases hd with hh | hh
      · rcases hqp.dvd_mul.mp hh with hh | hh
        · exact hne _ hprime le_rfl hh
        · exact hne _ hna (by omega) hh
      · rcases hqp.dvd_mul.mp hh with hh | hh
        · exact hne _ hprime le_rfl hh
        · exact hne _ hnb (by omega) hh
  have hl := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at hl
  have hh : (((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime).card:ℝ)
      ≤ (Y+1:ℝ)+(F.card:ℝ) := by exact_mod_cast hl
  change (F.card:ℝ) ≤ _ at hs
  push_cast at hs
  linarith

end Third971


open Finset Real OMALib.Sieve OMALib.Mertens
open scoped Classical
namespace Third971

lemma local_one {p : ℕ} (hp : p.Prime) : 1 ≤ ((p:ℝ)/(p-1:ℝ))^3 := by
  have h : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  apply one_le_pow₀
  exact (le_div_iff₀ (sub_pos.mpr h)).mpr (by linarith)

lemma loss_ge (n : ℕ) : 1 ≤ loss n :=
  Finset.one_le_prod fun p hp => local_one (Nat.prime_of_mem_primeFactors hp)

lemma loss_mul (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    loss (a*b) ≤ loss a * loss b := by
  let w (p : ℕ) := ((p:ℝ)/(p-1:ℝ))^3
  have h := prod_union_inter (s₁:=a.primeFactors) (s₂:=b.primeFactors) (f:=w)
  have h1 : 1 ≤ ∏ p ∈ a.primeFactors ∩ b.primeFactors, w p :=
    Finset.one_le_prod fun p hp => local_one (Nat.prime_of_mem_primeFactors (mem_inter.mp hp).1)
  unfold loss
  rw [Nat.primeFactors_mul ha.ne' hb.ne']
  change (∏ p ∈ a.primeFactors ∪ b.primeFactors, w p) ≤ _
  rw [← h]
  apply le_mul_of_one_le_right _ h1
  apply prod_nonneg
  intro p hp
  have pr : p.Prime := (mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  exact zero_le_one.trans (local_one pr)

lemma loss_eq_ratio (n : ℕ) (hn : 0<n) : loss n = ((n:ℝ)/n.totient)^3 := by
  unfold loss
  rw [prod_pow,prod_div_distrib]
  congr 1
  have hp : ∀ p ∈ n.primeFactors, 1 < (p:ℝ) := fun p h => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
  have hp0 : 0 < ∏ p ∈ n.primeFactors, ((p:ℝ)-1) := prod_pos fun p h => sub_pos.mpr (hp p h)
  have hφ : 0 < (n.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  apply (div_eq_div_iff hp0.ne' hφ.ne').mpr
  have hh := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors n)
  push_cast at hh
  rw [mul_comm]
  convert hh using 2
  apply prod_congr rfl
  intro p h
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors h).one_lt.le,Nat.cast_one]

lemma product_bound (Y D : ℕ) (hY : 4≤Y) (P : Finset ℕ) (hP : P=Nat.primesLE Y)
    (Q : Finset ℕ) (hq : Q=P \ D.primeFactors) (hgood : ∀ p ∈ Q, 3<p) :
    (∏ p ∈ Q, (1-3/(p:ℝ))) ≤ (exp mertens2Const/log Y)^3 * loss D := by
  classical
  let b (p : ℕ) := (1-1/(p:ℝ))^3
  have hprime {p} (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp (hP ▸ hp)).2
  have hlocal (p) (hp : p ∈ P) : 0 < 1-1/(p:ℝ) := by
    have h1 : 1 < (p:ℝ) := by exact_mod_cast (hprime hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr h1)
  have hQ : Q ⊆ P := hq ▸ sdiff_subset
  have hprod : (∏ p ∈ Q, b p) =
      (∏ p ∈ P, b p) * (∏ p ∈ P \ Q, ((p:ℝ)/(p-1:ℝ))^3) := by
    rw [← prod_sdiff hQ, mul_right_comm,← prod_mul_distrib]
    have hh : (∏ p ∈ P \ Q, b p * ((p:ℝ)/(p-1:ℝ))^3) = 1 := by
      apply prod_eq_one
      intro p hp
      have h1 : 1<(p:ℝ) := by exact_mod_cast (hprime (mem_sdiff.mp hp).1).one_lt
      dsimp [b]
      have hcalc : (1-1/(p:ℝ))*((p:ℝ)/(p-1))=1 := by
        field_simp [sub_ne_zero.mpr h1.ne',show (p:ℝ) ≠ 0 by linarith]
      rw [← mul_pow,hcalc,one_pow]
    rw [hh,one_mul]
  have hn : P \ Q ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    by_contra h
    exact h2 (hq ▸ mem_sdiff.mpr ⟨h1,h⟩)
  have hM := (prod_one_sub_inv_bounds (Y:ℝ) (by exact_mod_cast (show 2≤Y by omega))).2
  rw [Nat.floor_natCast,← hP] at hM
  calc
    _ ≤ ∏ p ∈ Q, b p := by
      apply prod_le_prod
      · intro p hp
        have h3 : 3<(p:ℝ) := by exact_mod_cast hgood p hp
        exact (sub_nonneg.mpr ((div_le_one (by linarith)).mpr h3.le))
      · intro p hp
        have h1 := hlocal p (hQ hp)
        have hv : 0≤(1:ℝ)/p := by positivity
        dsimp [b]
        nlinarith only [mul_nonneg (sq_nonneg ((1:ℝ)/p)) (show 0≤3-1/(p:ℝ) by linarith),
          show 3/(p:ℝ) = 3*(1/p) by ring]
    _ = _ := hprod
    _ ≤ _ := by
      apply mul_le_mul _ _ (prod_nonneg fun p hp =>
        zero_le_one.trans (local_one (hprime (mem_sdiff.mp hp).1))) (by positivity)
      · dsimp [b]; rw [prod_pow]
        exact pow_le_pow_left₀ (prod_nonneg fun p hp => (hlocal p hp).le) hM _
      · exact prod_le_prod_of_subset_of_one_le hn (fun p hp => zero_le_one.trans (local_one (Nat.prime_of_mem_primeFactors (hn hp)))) (fun p hp _ => local_one (Nat.prime_of_mem_primeFactors hp))

lemma sieve_main (Y D : ℕ) (hY : 4≤Y) (Q : Finset ℕ)
    (hq : Q=Nat.primesLE Y \ D.primeFactors) (hgood : ∀ p ∈ Q, 3<p) :
    let g (p : ℕ) := 3/(p:ℝ)
    let G := selbergG g (levelFamily Q (Y^12))
    0 < G ∧ 1/G ≤ 2*(exp mertens2Const/log Y)^3*loss D := by
  classical
  intro g G
  have sub : Q ⊆ Nat.primesLE Y := hq ▸ sdiff_subset
  have pr (p) (hp : p ∈ Q) := (Nat.mem_primesLE.mp (sub hp)).2
  have hg (p) (hp : p ∈ Q) : 0< g p ∧ g p<1 := by
    have h3 : 3<(p:ℝ) := by exact_mod_cast hgood p hp
    exact ⟨div_pos (by norm_num) (by linarith),(div_lt_one (by linarith)).mpr h3⟩
  have hsm : ∑ p ∈ Q, g p*log p ≤ log (Y^12:ℕ)/2 := by
    have hu := (sum_le_sum_of_subset_of_nonneg sub (f:=fun p : ℕ => log p / p)
      (fun p hp _ => div_nonneg (log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
        (Nat.cast_nonneg p))).trans (sum_log_div_le_nat Y)
    have h4 : log 4 ≤ log Y := log_le_log (by norm_num) (by exact_mod_cast hY)
    rw [show (∑ p ∈ Q, g p*log p) = 3*∑ p ∈ Q, log p/p by
      rw [mul_sum]; exact sum_congr rfl fun p _ => by dsimp [g]; ring]
    push_cast
    rw [Real.log_pow]
    linarith
  have hz : 1<Y^12 := one_lt_pow₀ (by omega) (by decide)
  have hh := normalizer_half Q (Y^12) hz g pr hg hsm
  let V := ∏ p ∈ Q, (1-g p)
  have hV : 0<V := prod_pos fun p hp => sub_pos.mpr (hg p hp).2
  have he : (∏ p ∈ Q, (1+hFun g p))=1/V := by
    change _ = 1/(∏ p ∈ Q, (1-g p))
    rw [one_div,← prod_inv_distrib]
    apply prod_congr rfl
    intro p hp
    unfold hFun
    have hd := sub_pos.mpr (hg p hp).2
    field_simp [hd.ne']
    ring
  rw [he] at hh
  change (1/V)/2 ≤ G at hh
  have hG : 0<G := lt_of_lt_of_le (by positivity) hh
  have hv := product_bound Y D hY (Nat.primesLE Y) rfl Q hq hgood
  change V ≤ _ at hv
  refine ⟨hG,le_trans ?_ (show 2*V ≤ _ by linarith only [hv])⟩
  apply (div_le_iff₀ hG).2
  have := (div_le_iff₀ hV).mp (show 1/V ≤ 2*G by linarith)
  linarith only [this,show 2*V*G = 2*G*V by ring]

end Third971


open Finset Real
open scoped Classical
namespace Third971

lemma triple_average (J : ℕ) :
    let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
    ∑ v ∈ U, loss v.1*loss v.2*loss (v.2-v.1) ≤ 3*(J:ℝ)^2*exp (2*4608) := by
  classical
  intro U
  let I := Ioc 0 J
  let V := I ×ˢ I
  let w (i : ℕ) := (loss i)^3
  have wp (i) : 0 ≤ w i := pow_nonneg (loss_pos i).le _
  have hI : Icc 1 J = I := by ext; simp [I]; omega
  have hU : U ⊆ V := by simpa only [U,V,hI] using
    (filter_subset (fun v : ℕ×ℕ => v.1<v.2) ((Icc 1 J) ×ˢ Icc 1 J))
  have hl (v) (hv : v ∈ U) : v.1 < v.2 := (mem_filter.mp hv).2
  let f (v : ℕ×ℕ) := (v.1,v.2-v.1)
  have hf : Set.InjOn f U := by
    rintro ⟨i,j⟩ h ⟨i',j'⟩ h' e
    have h1 : i=i' := congrArg Prod.fst e
    have h2 : j-i=j'-i' := congrArg Prod.snd e
    have a : i<j := hl _ h
    have b : i'<j' := hl _ h'
    congr 1 <;> omega
  have hV : U.image f ⊆ V := by
    rintro _ ht
    obtain ⟨⟨i,j⟩,hm,rfl⟩ := mem_image.mp ht
    obtain ⟨hi,hj⟩ := mem_product.mp (hU hm)
    obtain ⟨_,hjb⟩ := mem_Ioc.mp hj
    have hij : i<j := hl _ hm
    exact mem_product.mpr ⟨hi,mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hij,(Nat.sub_le j i).trans hjb⟩⟩
  let L := (J:ℝ)^2 * exp (2*4608)
  have hb : (J:ℝ)*(∑ n ∈ I,w n) ≤ L := by
    have := mul_le_mul_of_nonneg_left (mean_loss_cube J) (Nat.cast_nonneg (α:=ℝ) J)
    dsimp only [L,w,I]
    linarith only [this,show (J:ℝ)*(J*exp (2*4608)) = (J:ℝ)^2*exp (2*4608) by ring]
  have hcard : I.card=J := by simp [I]
  have hfst : (∑ v ∈ V, w v.1) ≤ L := by
    dsimp only [V]
    simp only [sum_product,sum_const,hcard,nsmul_eq_mul,← mul_sum]; exact hb
  have hsnd : (∑ v ∈ V, w v.2) ≤ L := by
    dsimp only [V]
    simp only [sum_product,sum_const,hcard,nsmul_eq_mul]; exact hb
  have hdf : (∑ v ∈ U, w (v.2-v.1)) ≤ L := by
    have hh := (sum_le_sum_of_subset_of_nonneg hV (f:=fun v : ℕ×ℕ => w v.2)
      (fun v _ _ => wp v.2)).trans hsnd
    rwa [sum_image (fun _ a _ b e => hf a b e)] at hh
  have h1 := (sum_le_sum_of_subset_of_nonneg hU (f:=fun v : ℕ×ℕ => w v.1)
    (fun v _ _ => wp v.1)).trans hfst
  have h2 := (sum_le_sum_of_subset_of_nonneg hU (f:=fun v : ℕ×ℕ => w v.2)
    (fun v _ _ => wp v.2)).trans hsnd
  have ham (a b c : ℕ) : loss a*loss b*loss c ≤ w a+w b+w c := by
    let u := max (loss a) (max (loss b) (loss c))
    have hA : loss a ≤ u := le_max_left .. 
    have hB : loss b ≤ u := (le_max_left ..).trans (le_max_right ..)
    have hC : loss c ≤ u := (le_max_right ..).trans (le_max_right ..)
    have hprod : loss a*loss b*loss c ≤ u*u*u :=
      mul_le_mul (mul_le_mul hA hB (loss_pos b).le ((loss_pos a).le.trans hA)) hC (loss_pos c).le
        (mul_nonneg ((loss_pos a).le.trans hA) ((loss_pos a).le.trans hA))
    rcases le_total (loss a) (max (loss b) (loss c)) with h | h
    · rw [show u=max (loss b) (loss c) from max_eq_right h] at hprod
      rcases le_total (loss b) (loss c) with h | h
      · rw [max_eq_right h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp a,wp b]
      · rw [max_eq_left h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp a,wp c]
    · rw [show u=loss a from max_eq_left h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp b,wp c]
  apply (sum_le_sum fun v (_ : v ∈ U) => ham v.1 v.2 (v.2-v.1)).trans
  rw [sum_add_distrib,sum_add_distrib]
  change _ ≤ 3*(J:ℝ)^2*exp (2*4608)
  dsimp only [L] at hdf h1 h2
  linarith

end Third971


open Finset Filter Real
namespace Third971

lemma scales : ∀ᶠ d : ℕ in atTop,
    let t := log (d:ℝ)
    let Y := ⌊exp (t/100)⌋₊
    let J := ⌊t⌋₊+1
    let X := ⌊(d.totient:ℝ)*t⌋₊
    0<d ∧ 1≤t ∧ 4≤Y ∧ t ≤ 200*log Y ∧ (J:ℝ) ≤ 2*t ∧ X<(J+1)*d ∧
      (X+1:ℝ) ≤ 2*d*t ∧ ((Y+1:ℝ)+(Y:ℝ)^48)*t^2 ≤ 3*d ∧
      ((Nat.primesLE X).card:ℝ) ≤ (log 4+1)*d := by
  have htend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hyend : Tendsto (fun d : ℕ => (d:ℝ)*log d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ htend
  have hpi := hyend.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 2,htend.eventually_ge_atTop 1000,hpi] with d hd hlg hp
  let t := log (d:ℝ)
  let Y := ⌊exp (t/100)⌋₊
  let J := ⌊t⌋₊+1
  let X := ⌊(d.totient:ℝ)*t⌋₊
  have ht : 1000 ≤ t := hlg
  have hdR : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdn : 0<d := by omega
  have hpos : 0<t := by linarith
  have hex := Real.exp_log (show 0<(d:ℝ) by positivity)
  change exp t = d at hex
  have hu : 6 ≤ exp (t/200) := by linarith [Real.add_one_le_exp (t/200)]
  have hsq : exp (t/200)*exp (t/200)=exp (t/100) := by rw [← Real.exp_add]; congr 1; ring
  have hfloor := Nat.lt_floor_add_one (exp (t/100))
  change exp (t/100)<(Y:ℝ)+1 at hfloor
  have hYlo : exp (t/200) ≤ (Y:ℝ) := by nlinarith [hsq,hu,hfloor]
  have hY : 4≤Y := by exact_mod_cast (show (4:ℝ) ≤ Y by linarith)
  have hlogY := Real.log_le_log (Real.exp_pos _) hYlo
  rw [Real.log_exp] at hlogY
  have hYhi : (Y:ℝ) ≤ exp (t/100) := Nat.floor_le (Real.exp_pos _).le
  have hhalf : (Y:ℝ)^48 ≤ exp (t/2) := by
    calc
      _ ≤ exp (t/100)^48 := pow_le_pow_left₀ (Nat.cast_nonneg Y) hYhi _
      _ = exp ((48:ℕ)*(t/100)) := (Real.exp_nat_mul _ _).symm
      _ ≤ exp (t/2) := Real.exp_le_exp.mpr (by norm_num; linarith)
  have hlin : (Y:ℝ) ≤ exp (t/2) := hYhi.trans (Real.exp_le_exp.mpr (by linarith))
  have he1 : 1≤exp (t/2) := Real.one_le_exp (by linarith)
  have he2 := Real.pow_div_factorial_le_exp (t/2) (by linarith) 3
  norm_num at he2
  have ht2 : t^2 ≤ exp (t/2) := by
    nlinarith only [he2,mul_nonneg (show 0≤t-48 by linarith) (sq_nonneg t)]
  have herr := mul_le_mul (show (Y+1:ℝ)+(Y:ℝ)^48 ≤ 3*exp (t/2) by linarith) ht2
    (sq_nonneg t) (by positivity)
  rw [mul_assoc,← Real.exp_add,show t/2+t/2=t by ring,hex] at herr
  have hjhi : (J:ℝ) ≤ t+1 := by dsimp [J]; push_cast; linarith [Nat.floor_le hpos.le]
  have hjlo : t < (J:ℝ) := by simpa [J] using Nat.lt_floor_add_one t
  have hXhi : (X:ℝ) ≤ (d:ℝ)*t := (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hpos.le)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le d) hpos.le)
  have hXn : X<(J+1)*d := by
    have hJ := mul_lt_mul_of_pos_left hjlo (show 0<(d:ℝ) by positivity)
    exact_mod_cast (show (X:ℝ)<((J:ℝ)+1)*(d:ℝ) by nlinarith only [hXhi,hJ,hdR])
  have hpi' : (Nat.primeCounting X:ℝ) ≤ (log 4+1)*((d:ℝ)*t)/log ((d:ℝ)*t) := by
    apply le_trans _ hp
    exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hXhi)
  have hdle : (d:ℝ) ≤ (d:ℝ)*t := le_mul_of_one_le_right (by positivity) (by linarith)
  have hlog := Real.log_le_log (show 0<(d:ℝ) by positivity) hdle
  change t ≤ _ at hlog
  have hscale : ((Nat.primesLE X).card:ℝ) ≤ (log 4+1)*d := by
    rw [Nat.primesLE_card_eq_primeCounting]
    apply hpi'.trans
    apply (div_le_iff₀ (hpos.trans_le hlog)).mpr
    calc
      _ = ((log 4+1)*(d:ℝ))*t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity [Real.log_nonneg (by norm_num : 1≤(4:ℝ))])
  refine ⟨hdn,by linarith,hY,by linarith,by linarith,hXn,?_,herr,hscale⟩
  nlinarith only [hXhi,hdle,hdR]

end Third971


open Finset OMALib.Sieve OMALib.Mertens Real
open scoped Classical
namespace Third971

lemma sieve_triple (X Y d i j : ℕ) (hY : 4≤Y) (hd : 0<d) (hi : 0 < i) (hij : i<j) :
    (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤
    (Y+1:ℝ)+(X+1:ℝ)*(2*(exp mertens2Const/log Y)^3*
      (loss 6*loss d*loss i*loss j*loss (j-i)))+(Y:ℝ)^48 := by
  classical
  let D := 6*d*i*j*(j-i)
  have hj : 0 < j := hi.trans hij
  have hg : 0 < j-i := Nat.sub_pos_of_lt hij
  have hD : 0 < D := by dsimp [D]; positivity
  let Q := Nat.primesLE Y \ D.primeFactors
  have info (q) (hq : q ∈ Q) : q.Prime ∧ 3<q ∧ q≤Y ∧ ¬q ∣ i*d ∧ ¬q ∣ j*d ∧ (i*d)%q≠(j*d)%q := by
    obtain ⟨hmem,hn⟩ := mem_sdiff.mp hq
    obtain ⟨hqY,hpr⟩ := Nat.mem_primesLE.mp hmem
    have hnd : ¬ q ∣ D := fun h => hn (Nat.mem_primeFactors.mpr ⟨hpr,h,hD.ne'⟩)
    have h6 : ¬q ∣ 6 := fun h => hnd (h.trans (show 6 ∣ D from ⟨d*i*j*(j-i),by dsimp [D]; ring⟩))
    have hq3 : 3<q := by
      by_contra! hq3
      interval_cases q <;> norm_num at *
    have hai : i*d ∣ D := ⟨6*j*(j-i),by dsimp [D]; ring⟩
    have haj : j*d ∣ D := ⟨6*i*(j-i),by dsimp [D]; ring⟩
    refine ⟨hpr,hq3,hqY,fun h => hnd (h.trans hai),fun h => hnd (h.trans haj),?_⟩
    intro hh
    have hh' := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right d hij.le)).mp hh
    rw [← Nat.sub_mul] at hh'
    exact hnd (hh'.trans ⟨6*i*j,by dsimp [D]; ring⟩)
  have hz : 2 ≤ Y^12 := one_lt_pow₀ (show 1<Y by omega) (show (12:ℕ) ≠ 0 by decide)
  have hs := shift_sieve X Y (Y^12) (i*d) (j*d) Q hz info
  obtain ⟨_,hmain⟩ := sieve_main Y D hY Q rfl (fun q hq => (info q hq).2.1)
  have hloss : loss D ≤ loss 6*loss d*loss i*loss j*loss (j-i) := by
    have hG0 := (loss_pos (j-i)).le
    have hJ0 := (loss_pos j).le
    have hI0 := (loss_pos i).le
    dsimp only [D]
    calc
      _ ≤ loss (6*d*i*j)*loss (j-i) := loss_mul _ _ (by positivity) hg
      _ ≤ loss (6*d*i)*loss j*loss (j-i) := by
        exact mul_le_mul_of_nonneg_right (loss_mul (6*d*i) j (by positivity) hj) hG0
      _ ≤ loss (6*d)*loss i*loss j*loss (j-i) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (loss_mul (6*d) i (by positivity) hi) hJ0) hG0
      _ ≤ _ := by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (loss_mul 6 d (by decide) hd) hI0) hJ0) hG0
  have hlog : 0 < log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have h1 := hmain.trans (mul_le_mul_of_nonneg_left hloss (by positivity))
  apply hs.trans
  push_cast
  rw [← pow_mul,show 12*4=48 by decide]
  gcongr 2
  rw [div_eq_mul_inv,← one_div]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Third971


open Filter Finset Real OMALib.Mertens
open scoped Classical
namespace Third971

lemma triple_bound (M t : ℝ) (hM : 0<M) (ht : 1≤t) (X Y d i j : ℕ) (hY : 4≤Y)
    (hd : 0<d) (hi : 0 < i) (hij : i<j) (hr : (d:ℝ) ≤ M*d.totient)
    (hlY : t ≤ 200*log Y) (hX : (X+1:ℝ) ≤ 2*d*t)
    (hE : ((Y+1:ℝ)+(Y:ℝ)^48)*t^2 ≤ 3*d) :
    let K := 3+4*(200*exp mertens2Const)^3*loss 6*M^3
    (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤
      K*d/t^2 * (loss i*loss j*loss (j-i)) := by
  intro K
  let W := loss i*loss j*loss (j-i)
  let C := exp mertens2Const
  have hW : 1≤W := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (loss_ge i) (loss_ge j)) (loss_ge _)
  have hW0 : 0≤W := zero_le_one.trans hW
  have hC : 0<C := exp_pos _
  have hlog : 0<log (Y:ℝ) := log_pos (by exact_mod_cast (show 1<Y by omega))
  have ht0 : 0<t := by linarith
  have hφ : 0<(d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hloss : loss d ≤ M^3 := by
    rw [loss_eq_ratio d hd]
    exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hφ).mpr hr) _
  have hsmall : (C*t/log Y)^3 ≤ (200*C)^3 := by
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hlog).mpr
    linarith only [mul_le_mul_of_nonneg_left hlY hC.le]
  have hd0 := (loss_pos d).le
  have h6 := (loss_pos 6).le
  have hs := sieve_triple X Y d i j hY hd hi hij
  have hm : ((X+1:ℝ)*(2*(C/log Y)^3*(loss 6*loss d*loss i*loss j*loss (j-i))))*t^2 ≤
      4*(200*C)^3*loss 6*M^3*d*W := by
    calc
      _ ≤ (2*d*t)*(2*(C/log Y)^3*(loss 6*loss d*W))*t^2 := by
        rw [show loss 6*loss d*loss i*loss j*loss (j-i) = loss 6*loss d*W by dsimp [W]; ring]
        gcongr <;> positivity
      _ = 4*(C*t/log Y)^3*loss 6*loss d*d*W := by ring
      _ ≤ _ := by
        have hl := (loss_pos d).le
        gcongr
  have he := mul_le_mul_of_nonneg_left hW (show 0≤3*(d:ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  change (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤ K*d/t^2*W
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos ht0)]
  dsimp only [K]
  change _ ≤ (3+4*(200*C)^3*loss 6*M^3)*d*W
  change _ ≤ ((Y+1:ℝ)+(X+1:ℝ)*(2*(C/log Y)^3*(loss 6*loss d*loss i*loss j*loss (j-i)))+
    (Y:ℝ)^48)*t^2 at hb
  linarith only [hb,hE,hm,he]

theorem third_moment : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H2 := by
  classical
  intro M hM
  let K := 3+4*(200*exp mertens2Const)^3*loss 6*M^3
  let B := exp (2*4608 : ℝ)
  let V := 27*(log 4+1)+27*12*K*B
  have hK : 0<K := by dsimp [K]; positivity [loss_pos 6]
  have hB : 0<B := exp_pos _
  have hV : 0<V := by dsimp [V]; positivity [log_nonneg (by norm_num : 1≤(4:ℝ))]
  refine ⟨V*M,mul_pos hV hM,?_⟩
  filter_upwards [scales] with d hs
  intro hr
  let t := log (d:ℝ)
  let X := ⌊(d.totient:ℝ)*t⌋₊
  let Y := ⌊exp (t/100)⌋₊
  let J := ⌊t⌋₊+1
  let A := (range d).filter fun a => a.Coprime d
  let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
  let T (v : ℕ×ℕ) := (Nat.primesLE X).filter fun p => (p+v.1*d).Prime ∧ (p+v.2*d).Prime
  let w (v : ℕ×ℕ) := loss v.1*loss v.2*loss (v.2-v.1)
  obtain ⟨hd,ht,hY,hlY,hJ,hXd,hX,hE,hP⟩ := hs
  have ht0 : 0<t := by change 1≤t at ht; linarith
  have main := finite_moment X d J hd hXd A
  have htr (v : ℕ×ℕ) (hv : v ∈ U) : ((T v).card:ℝ) ≤ K*d/t^2*w v := by
    obtain ⟨hh,hij⟩ := mem_filter.mp hv
    exact triple_bound M t hM ht X Y d v.1 v.2 hY hd
      (mem_Icc.mp (mem_product.mp hh).1).1 hij hr hlY hX hE
  have hs1 := sum_le_sum htr
  rw [← mul_sum] at hs1
  have hs2 : (∑ v ∈ U, w v) ≤ 3*(J:ℝ)^2*B := triple_average J
  have hj2 : (J:ℝ)^2 ≤ (2*t)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ _
  have hs3 : (∑ v ∈ U, ((T v).card:ℝ)) ≤ 12*K*B*d := by
    calc
      _ ≤ (K*d/t^2)*(3*(J:ℝ)^2*B) := hs1.trans (mul_le_mul_of_nonneg_left hs2 (by positivity))
      _ ≤ (K*d/t^2)*(3*(2*t)^2*B) := by gcongr
      _ = _ := by field_simp; ring
  have he : (↑(∑ a ∈ A, (((Nat.primesLE X).filter fun p => p%d=a).card)^3):ℝ) ≤
    27*((Nat.primesLE X).card:ℝ)+27*∑ v ∈ U, ((T v).card:ℝ) := by exact_mod_cast main
  apply he.trans
  apply le_trans _ (show V*(d:ℝ) ≤ (V*M)*d.totient by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr hV.le)
  change 27*((Nat.primesLE X).card:ℝ)+27*∑ v ∈ U, ((T v).card:ℝ) ≤
    (27*(log 4+1)+27*12*K*B)*d
  linarith only [hP,hs3]

end Third971


theorem OMA.solution : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H2 := by
  exact Third971.third_moment
