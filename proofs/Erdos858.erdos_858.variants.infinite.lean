import FormalConjectures.ErdosProblems.«858»
import Mathlib

/-! The Mertens estimates are from @senamakel’s checked proof of Erdős 851.
Multiples of each admissible element with sufficiently rough cofactor form
pairwise disjoint sets. Their densities bound a logarithmically weighted
series, giving the desired limit by dominated convergence. -/

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


end OMALib.Mertens

namespace E858
open Filter Real Finset Asymptotics
open scoped Classical Topology

private def period (a : ℕ) := (max 2 a).factorial

private theorem exclusive {A : Set ℕ}
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a)
    {a b u v : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hap : 0 < a) (hab : a < b)
    (hu : (period a).Coprime u) (hv : (period b).Coprime v) (he : a*u = b*v) : False := by
  have hcop : a.Coprime v := hv.coprime_dvd_left (Nat.dvd_factorial hap (hab.le.trans (le_max_right ..)))
  have hd : a ∣ b := hcop.dvd_of_dvd_mul_right (he ▸ Nat.dvd_mul_right a u)
  obtain ⟨t,ht⟩ := hd
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht; omega
  have htu : t ∣ u := ⟨v, Nat.eq_of_mul_eq_mul_left hap (by simpa [ht,Nat.mul_assoc] using he)⟩
  have hp := Nat.minFac_prime ht1
  have hsmall := hadm a ha b hb t ht.symm
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hu
    (Nat.dvd_factorial hp.pos (hsmall.trans (le_max_right ..))) ((Nat.minFac_dvd _).trans htu))

private def box (L m : ℕ) := range L ×ˢ ((range m).filter m.Coprime)
private def value (a m : ℕ) (p : ℕ × ℕ) := a*(p.2+p.1*m)

private theorem box_inj {a m L : ℕ} (ha : 0 < a) (hm : 0 < m) :
    Set.InjOn (value a m) (box L m) := by
  rintro ⟨i,r⟩ hp ⟨j,t⟩ hq he
  have hr := mem_range.mp (mem_filter.mp (mem_product.mp hp).2).1
  have ht := mem_range.mp (mem_filter.mp (mem_product.mp hq).2).1
  have he' := Nat.eq_of_mul_eq_mul_left ha he
  change r+i*m = t+j*m at he'
  have hrs := congrArg (· % m) he'
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht] at hrs
  subst t
  exact Prod.ext (Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel he')) rfl

private theorem packing {A : Set ℕ} (h0 : 0 ∉ A)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a*t=b → t.minFac ≤ a)
    (s : Finset ℕ) (hs : (s : Set ℕ) ⊆ A) :
    ∑ a ∈ s, ((period a).totient : ℝ) / ((a:ℝ)*period a) ≤ 1 := by
  classical
  let M := ∏ a ∈ s, a * period a
  have pos (a) (ha : a ∈ s) : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hs ha))
  have mp : 0 < M := Finset.prod_pos (fun a ha => Nat.mul_pos (pos a ha) (Nat.factorial_pos _))
  let L (a : ℕ) := M/(a*period a)
  have units (a) (ha : a ∈ s) : L a*(a*period a) = M :=
    Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ ha)
  let part (a : ℕ) := (box (L a) (period a)).image (value a (period a))
  have sz (a) (ha : a ∈ s) : (part a).card = L a*(period a).totient := by
    dsimp only [part]
    rw [card_image_of_injOn (box_inj (L := L a) (m := period a) (pos a ha) (Nat.factorial_pos _)),box,card_product,card_range]
    rfl
  have sub (a) (ha : a ∈ s) : part a ⊆ range M := by
    rintro x hx
    obtain ⟨⟨i,r⟩,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨hi,hr⟩ := mem_product.mp hp
    have hil := mem_range.mp hi
    have hrm := mem_range.mp (mem_filter.mp hr).1
    apply mem_range.mpr
    rw [← units a ha]
    change a*(r+i*period a) < _
    have hh : r+i*period a < L a*period a := calc
      _ < (i+1)*period a := by rw [Nat.add_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hil
    simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hh (pos a ha)
  have dis (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) : Disjoint (part a) (part b) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨⟨i,r⟩,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨⟨j,t⟩,hq,he⟩ := mem_image.mp hy
    have hr := (mem_filter.mp (mem_product.mp hp).2).2
    have ht := (mem_filter.mp (mem_product.mp hq).2).2
    exact exclusive hadm (hs ha) (hs hb) (pos a ha) hab
      ((Nat.coprime_add_mul_right_right _ _ _).mpr hr) ((Nat.coprime_add_mul_right_right _ _ _).mpr ht) he.symm
  have hh : ∑ a ∈ s, L a * (period a).totient ≤ M := by
    calc
      _ = ∑ a ∈ s, (part a).card := sum_congr rfl fun a ha => (sz a ha).symm
      _ = (s.biUnion part).card := (card_biUnion (fun a ha b hb hab =>
        (lt_or_gt_of_ne hab).elim (dis a b ha hb) (fun h => (dis b a hb ha h).symm))).symm
      _ ≤ (range M).card := card_le_card (biUnion_subset.mpr sub)
      _ = M := card_range _
  apply (le_of_mul_le_mul_right (a := (M:ℝ)) ?_ (by exact_mod_cast mp))
  rw [Finset.sum_mul,one_mul]
  calc
    _ = ∑ a ∈ s, (L a:ℝ) * (period a).totient := by
      apply Finset.sum_congr rfl
      intro a ha
      have h := congrArg (fun k : ℕ => (k:ℝ)) (units a ha).symm
      push_cast at h
      rw [h]
      have hden : (a:ℝ)*(period a) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos (pos a ha) (Nat.factorial_pos _)).ne'
      rw [mul_comm (L a : ℝ), ← mul_assoc, div_mul_cancel₀ _ hden, mul_comm]
    _ ≤ M := by exact_mod_cast hh

private noncomputable def weight (n : ℕ) : ℝ := (1/(n:ℝ))/Real.log (max 2 n : ℕ)
private theorem logpos (n : ℕ) : 0 < Real.log (max 2 n : ℕ) := by
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 n))
private theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := div_nonneg (by positivity) (logpos n).le

private theorem weights {A : Set ℕ} (h0 : 0 ∉ A)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a*t=b → t.minFac ≤ a) :
    Summable (A.indicator weight) := by
  classical
  obtain ⟨c,_,hc,_,h⟩ := OMALib.Mertens.mertens3
  apply summable_of_sum_le (c := 1/c)
  · intro n
    by_cases hn : n ∈ A <;> simp [Set.indicator,hn,weight_nonneg]
  · intro s
    change (∑ n ∈ s, if n ∈ A then weight n else 0) ≤ _
    rw [← Finset.sum_filter]
    let T := s.filter (· ∈ A)
    have hT : (T:Set ℕ) ⊆ A := fun _ hx => (mem_filter.mp hx).2
    apply (le_div_iff₀ hc).mpr
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum (g := fun n => ((period n).totient:ℝ) / ((n:ℝ)*period n)) ?_)
      (packing h0 hadm T hT)
    intro n hn
    have hnp : 0 < n := Nat.pos_of_ne_zero (fun he => h0 (he ▸ hT hn))
    let z := max 2 n
    have hmn : 2 ≤ z := le_max_left .. 
    have hb := (h (z:ℝ) (by exact_mod_cast hmn)).1
    rw [Nat.floor_natCast] at hb
    have hpr : (period n).primeFactors = Nat.primesLE z := by
      ext p
      simp only [period,Nat.mem_primeFactors,Nat.mem_primesLE]
      constructor
      · rintro ⟨hp,hd,_⟩
        exact ⟨hp.dvd_factorial.mp hd,hp⟩
      · rintro ⟨hle,hp⟩
        exact ⟨hp,hp.dvd_factorial.mpr hle,Nat.factorial_ne_zero _⟩
    have he := congrArg (fun q : ℚ => (q:ℝ)) (Nat.totient_eq_mul_prod_factors (period n))
    push_cast at he
    rw [hpr] at he
    simp only [one_div] at hb
    have hnp' : 0 < (n:ℝ) := by exact_mod_cast hnp
    have hper : 0 < (period n:ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hl : 0 < Real.log (z:ℝ) := logpos n
    rw [he]
    change (1/(n:ℝ)/Real.log (z:ℝ))*c ≤ _
    calc
      _ = (c / Real.log (z:ℝ)) / n := by ring
      _ ≤ _ / (n:ℝ) := div_le_div_of_nonneg_right hb hnp'.le
      _ = _ := by field_simp

end E858

open E858 Real Filter Finset Asymptotics
open scoped Topology Classical

theorem OMA.solution : type_of% @Erdos858.erdos_858.variants.infinite := by
  classical
  intro A _ h0 hadm
  let term (N n : ℕ) : ℝ := if n ∈ (Icc 1 N).filter (· ∈ A) then (1/(n:ℝ))/Real.log N else 0
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have limit := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := term) (g := fun _ => (0:ℝ))
    (weights h0 hadm) (fun n => ?_) ?_
  · apply (isLittleO_iff_tendsto' ?_).mpr
    · apply (show Tendsto (fun N => ∑' n, term N n) atTop (𝓝 0) by simpa using limit).congr'
      apply Eventually.of_forall
      intro N
      change (∑' n, term N n) = (∑ n ∈ (Icc 1 N).filter (· ∈ A), (1:ℝ)/n) / Real.log N
      rw [tsum_eq_sum (f := term N) (s := (Icc 1 N).filter (· ∈ A)) (fun n hn => by simp only [term,if_neg hn]),Finset.sum_div]
      exact sum_congr rfl fun n hn => by simp only [term,if_pos hn]
    · filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
      exact fun he => False.elim ((Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne' he)
  · by_cases hn : n ∈ A
    · have hp : 1 ≤ n := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hn))
      apply ((tendsto_const_nhds (x := 1/(n:ℝ))).div_atTop hlog).congr'
      filter_upwards [eventually_ge_atTop n] with N hN
      simp [term,hn,hp,hN]
    · simpa [term,hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN n
    by_cases h : n ∈ (Icc 1 N).filter (· ∈ A)
    · obtain ⟨hb,ha⟩ := mem_filter.mp h
      have hn := (mem_Icc.mp hb).2
      have hl : Real.log (max 2 n : ℕ) ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast max_le hN hn)
      have hlN := (logpos n).trans_le hl
      simp only [term,if_pos h,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by positivity : 0 ≤ 1/(n:ℝ)) hlN.le),
        Set.indicator_of_mem ha,weight]
      exact div_le_div_of_nonneg_left (by positivity) (logpos n) hl
    · simp only [term,if_neg h,norm_zero]
      by_cases hn : n ∈ A <;> simp [Set.indicator,hn,weight_nonneg]
