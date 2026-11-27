import FormalConjectures.ErdosProblems.«962»

-- Problem: Erdős Problem 962 — tang lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/962.lean:73 (declaration Erdos962.erdos_962.variants.tang_lower_bound)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


/-!
Mertens' theorems.

Elementary proofs, over the reals, of the three theorems of Mertens (1874):

* `OMALib.Mertens.abs_sum_log_div_sub_log_le` (first theorem):
  `|∑_{p ≤ x} log p / p - log x| ≤ mertens1Const + log 2` for `x ≥ 1`;
* `OMALib.Mertens.abs_sum_inv_sub_log_log_le` (second theorem):
  `|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const` for `x ≥ 2`;
* `OMALib.Mertens.prod_one_sub_inv_bounds` (third theorem, product form):
  `exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp mertens2Const / log z` for `z ≥ 2`;

with existential forms `mertens1`, `mertens2`, `mertens3`. Sums over primes `p ≤ x` are written
`∑ p ∈ Nat.primesLE ⌊x⌋₊`, as in `Mathlib.NumberTheory.Chebyshev`.

The first theorem follows from Legendre's formula for `log N!`, the bounds
`N log N - N ≤ log N! ≤ N log N` and Chebyshev's bound `θ(N) ≤ N log 4`. The second follows
from the first by discrete partial summation, run as an induction on `N`. The third follows from
the second and `-t / (1 - t) ≤ log (1 - t) ≤ -t`.
-/

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

open Filter Real
namespace E962
open Erdos962
theorem prod_bound (K : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ∏ p ∈ Nat.primesBelow (K + 1), (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      Real.exp (4 * ∑ p ∈ Nat.primesBelow (K + 1), (p : ℝ) ^ (-σ)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have h1 : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro p hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    set t := (p : ℝ) ^ (-σ) with ht
    have t0 : 0 ≤ t := Real.rpow_nonneg (by linarith) _
    have t1 : t ≤ 3 / 4 := by
      have a1 : t ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have a2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      have a3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hpos : 0 < 1 - t := by linarith
    calc (1 - t)⁻¹ ≤ 4 * t + 1 := by
          rw [inv_le_iff_one_le_mul₀ hpos]
          nlinarith
      _ ≤ Real.exp (4 * t) := Real.add_one_le_exp _

theorem sum_split (K : ℕ) (a B D E : ℝ) (ha0 : 0 < a) (hz2 : 2 ≤ Real.exp (1 / a))
    (hzK : Real.exp (1 / a) ≤ K) (hKa : (K : ℝ) ^ a ≤ B) (hD : a * Real.log K ≤ D)
    (hE : ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ E) :
    ∑ p ∈ Nat.primesBelow (K + 1), (p : ℝ) ^ (-(1 - a)) ≤
      Real.exp 1 * (1 / a + E) + B * (D + 2 * E) := by
  have hB : 0 ≤ B := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hKa
  set z := Real.exp (1 / a) with hz
  set Z := ⌊z⌋₊ with hZ
  have hZK : Z ≤ K := Nat.floor_le_of_le hzK
  have hK2 : (2 : ℝ) ≤ K := le_trans hz2 hzK
  have hsub : Nat.primesLE Z ⊆ Nat.primesLE K := by
    intro p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hPB : Nat.primesBelow (K + 1) = Nat.primesLE K := rfl
  rw [hPB, ← Finset.sum_sdiff hsub]
  have hterm : ∀ p : ℕ, 0 < p → (p : ℝ) ^ (-(1 - a)) = (p : ℝ) ^ a * (1 / p) := by
    intro p hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    rw [show -(1 - a) = a + -1 by ring, Real.rpow_add hp', Real.rpow_neg_one, one_div]
  have hmemp : ∀ {N p : ℕ}, p ∈ Nat.primesLE N → p.Prime ∧ p ≤ N := by
    intro N p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
    exact ⟨hp.2, by omega⟩
  -- small primes
  have hsmall : ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-(1 - a)) ≤
      Real.exp 1 * ∑ p ∈ Nat.primesLE Z, (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨pp, hpZ⟩ := hmemp hp
    rw [hterm p pp.pos]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hpz : (p : ℝ) ≤ z := by
      have := (Nat.le_floor_iff (Real.exp_pos _).le).mp hpZ
      exact this
    calc (p : ℝ) ^ a ≤ z ^ a := Real.rpow_le_rpow (Nat.cast_nonneg _) hpz ha0.le
      _ = Real.exp 1 := by
        rw [hz, ← Real.exp_mul]; congr 1; field_simp
  have hlarge : ∑ p ∈ Nat.primesLE K \ Nat.primesLE Z, (p : ℝ) ^ (-(1 - a)) ≤
      B * ∑ p ∈ Nat.primesLE K \ Nat.primesLE Z, (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨pp, hpK⟩ := hmemp (Finset.mem_sdiff.mp hp).1
    rw [hterm p pp.pos]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (p : ℝ) ^ a ≤ (K : ℝ) ^ a :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hpK) ha0.le
      _ ≤ B := hKa
  have hMZ := hE z hz2
  have hMK := hE (K : ℝ) hK2
  rw [Nat.floor_natCast] at hMK
  rw [← hZ] at hMZ
  have hdiff : ∑ p ∈ Nat.primesLE K \ Nat.primesLE Z, (1 : ℝ) / p =
      ∑ p ∈ Nat.primesLE K, (1 : ℝ) / p - ∑ p ∈ Nat.primesLE Z, (1 : ℝ) / p := by
    rw [← Finset.sum_sdiff hsub]; ring
  have hllz : Real.log (Real.log z) = Real.log (1 / a) := by rw [hz, Real.log_exp]
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  have hllK : Real.log (Real.log K) - Real.log (1 / a) ≤ D := by
    have : Real.log (Real.log K) - Real.log (1 / a) = Real.log (a * Real.log K) := by
      rw [Real.log_mul ha0.ne' hlogK.ne', one_div, Real.log_inv]; ring
    rw [this]
    have := Real.log_le_sub_one_of_pos (mul_pos ha0 hlogK)
    linarith
  have hla : Real.log (1 / a) ≤ 1 / a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / a by positivity); linarith
  have hS1 : ∑ p ∈ Nat.primesLE Z, (1 : ℝ) / p ≤ 1 / a + E := by
    have := (abs_le.mp hMZ).2; rw [hllz] at this; linarith
  have hS2 : ∑ p ∈ Nat.primesLE K \ Nat.primesLE Z, (1 : ℝ) / p ≤ D + 2 * E := by
    rw [hdiff]
    have h1 := (abs_le.mp hMZ).1; have h2 := (abs_le.mp hMK).2
    rw [hllz] at h1
    linarith
  have e0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have := mul_le_mul_of_nonneg_left hS1 e0
  have := mul_le_mul_of_nonneg_left hS2 hB
  linarith
theorem pigeon (n K : ℕ) (hK : 1 ≤ K)
    (h : (Nat.smoothNumbersUpTo n (K + 1)).card < n / K) : Erdos962Prop n K := by
  by_contra hne
  have H : ∀ m ≤ n, ∃ i, 1 ≤ i ∧ i ≤ K ∧ ∀ p, Nat.Prime p → K < p → ¬ p ∣ (m + i) := by
    intro m hm
    by_contra hc
    apply hne
    refine ⟨m, hm, fun i hi => ?_⟩
    by_contra hp
    apply hc
    refine ⟨i, hi.1, hi.2, fun p pp hKp hd => hp ⟨p, pp, hKp, hd⟩⟩
  let i : ℕ → ℕ := fun j => if hj : j * K ≤ n then Classical.choose (H _ hj) else 1
  have hi1 : ∀ j, 1 ≤ i j ∧ i j ≤ K := by
    intro j
    by_cases hj : j * K ≤ n
    · have := Classical.choose_spec (H _ hj)
      simp only [i, hj, dite_true]
      exact ⟨this.1, this.2.1⟩
    · simp only [i, hj, dite_false]
      exact ⟨le_rfl, hK⟩
  have hi2 : ∀ j, j * K ≤ n → ∀ p, Nat.Prime p → K < p → ¬ p ∣ (j * K + i j) := by
    intro j hj
    have := Classical.choose_spec (H _ hj)
    simp only [i, hj, dite_true]
    exact this.2.2
  let g : ℕ → ℕ := fun j => j * K + i j
  have hmono : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h1 := hi1 j
    have h2 := hi1 (j + 1)
    simp only [g]
    nlinarith
  have hcard : (Finset.range (n / K)).card ≤ (Nat.smoothNumbersUpTo n (K + 1)).card := by
    apply Finset.card_le_card_of_injOn g
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio] at hj
      have hjK : (j + 1) * K ≤ n := by
        calc (j + 1) * K ≤ (n / K) * K := Nat.mul_le_mul_right _ hj
          _ ≤ n := Nat.div_mul_le_self n K
      have hjK' : j * K ≤ n := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ j)) hjK
      simp only [Finset.mem_coe, Nat.mem_smoothNumbersUpTo]
      have h1 := hi1 j
      refine ⟨?_, ?_⟩
      · simp only [g]; nlinarith
      · rw [Nat.mem_smoothNumbers']
        intro p pp hd
        by_contra hlt
        exact hi2 j hjK' p pp (by omega) hd
    · exact hmono.injective.injOn
  simp at hcard
  omega

theorem rankin (n K : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ((Nat.smoothNumbersUpTo n (K + 1)).card : ℝ) ≤
      (n : ℝ) ^ σ * ∏ p ∈ Nat.primesBelow (K + 1), (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  let f : ℕ →* ℝ :=
    { toFun := fun m => (m : ℝ) ^ (-σ)
      map_one' := by simp
      map_mul' := by
        intro x y
        push_cast
        exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) }
  have hf : ∀ m : ℕ, f m = (m : ℝ) ^ (-σ) := fun m => rfl
  have hlt : ∀ {p : ℕ}, Nat.Prime p → ‖f p‖ < 1 := by
    intro p hp
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have HS := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hlt (K + 1)).2
  set T := Nat.smoothNumbersUpTo n (K + 1)
  have hmem : ∀ x ∈ T, x ∈ Nat.smoothNumbers (K + 1) := fun x hx =>
    (Nat.mem_smoothNumbersUpTo.mp hx).2
  have hsum : ∑ m ∈ T, f m ≤ ∏ p ∈ Nat.primesBelow (K + 1), (1 - f p)⁻¹ := by
    rw [← Finset.sum_subtype_of_mem (fun m => f m) hmem]
    exact sum_le_hasSum _ (fun x _ => by
      rw [hf]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _) HS
  have h1 : (T.card : ℝ) ≤ ∑ m ∈ T, (n : ℝ) ^ σ * f m := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hmn := (Nat.mem_smoothNumbersUpTo.mp hm).1
    have hm0 : m ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers (hmem m hm)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    rw [hf, Real.rpow_neg hmpos.le]
    have : (m : ℝ) ^ σ ≤ (n : ℝ) ^ σ :=
      Real.rpow_le_rpow hmpos.le (by exact_mod_cast hmn) hσ.le
    have hp : 0 < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hmpos _
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    simpa using this
  rw [← Finset.mul_sum] at h1
  calc (T.card : ℝ) ≤ (n : ℝ) ^ σ * ∑ m ∈ T, f m := h1
    _ ≤ (n : ℝ) ^ σ * ∏ p ∈ Nat.primesBelow (K + 1), (1 - f p)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by simp only [hf]

theorem key (c b E : ℝ) (hc : 0 < c) (hc1 : c < 1) (hb : 0 < b) (hθ : c * b < 1 / 2)
    (hE : ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ E)
    (n : ℕ) (hn : 1 ≤ n)
    (h1 : 1 ≤ Real.log (Real.log n))
    (h2 : 1 ≤ c * b * Real.log (Real.log n))
    (h3 : 2 * b * Real.log (Real.log n) ≤ Real.sqrt (Real.log n * Real.log (Real.log n)))
    (h4 : 2 * Real.log 2 + 4 * (Real.exp 1 *
        (Real.sqrt (Real.log n * Real.log (Real.log n)) / (b * Real.log (Real.log n)) + E) +
        2 * Real.log n ^ (c * b) * (1 + Real.log (Real.log n) + 2 * E)) ≤
        (b - c) * Real.sqrt (Real.log n * Real.log (Real.log n)))
    (h5 : c * Real.sqrt (Real.log n * Real.log (Real.log n)) + 2 * Real.log 2 < Real.log n) :
    c * Real.sqrt (Real.log n * Real.log (Real.log n)) ≤ Real.log (Erdos962.k n : ℝ) := by
  set L := Real.log n with hL
  set Λ := Real.log L with hΛ
  set S := Real.sqrt (L * Λ) with hS
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL1 : 1 < L := by
    by_contra hh
    push Not at hh
    have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
    have : Real.log L ≤ 0 := Real.log_nonpos hL0 hh
    linarith
  have hLΛ : 0 < L * Λ := by positivity
  have hSpos : 0 < S := Real.sqrt_pos.mpr hLΛ
  have hS2 : S ^ 2 = L * Λ := Real.sq_sqrt hLΛ.le
  set y := Real.exp (c * S) with hy
  have hy1 : 1 ≤ y := Real.one_le_exp (by positivity)
  set K := ⌈y⌉₊ with hK
  have hKy : y ≤ K := Nat.le_ceil y
  have hK2y : (K : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ y by linarith); linarith
  have hKpos : (0 : ℝ) < K := by linarith
  set a := b * Λ / S with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ hSpos]; linarith
  have hinv : 1 / a = S / (b * Λ) := by rw [ha]; field_simp
  have hz2 : 2 ≤ Real.exp (1 / a) := by
    have : 2 ≤ 1 / a := by rw [le_div_iff₀ ha0]; linarith
    have := Real.add_one_le_exp (1 / a); linarith
  have hzK : Real.exp (1 / a) ≤ K := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hKy
    rw [hinv, div_le_iff₀ (by positivity)]
    nlinarith
  have haS : c * S * a = c * b * Λ := by rw [ha]; field_simp
  have hKa : (K : ℝ) ^ a ≤ 2 * L ^ (c * b) := by
    calc (K : ℝ) ^ a ≤ (2 * y) ^ a := Real.rpow_le_rpow hKpos.le hK2y ha0.le
      _ = 2 ^ a * y ^ a := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * L ^ (c * b) := by
        have e1 : (2 : ℝ) ^ a ≤ 2 := by
          calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
        have e2 : y ^ a = L ^ (c * b) := by
          rw [hy, ← Real.exp_mul, haS, Real.rpow_def_of_pos (by linarith)]
          congr 1
          rw [hΛ]
          ring
        rw [e2]
        exact mul_le_mul_of_nonneg_right e1 (Real.rpow_nonneg (by linarith) _)
  have hD : a * Real.log K ≤ 1 + Λ := by
    have l1 : Real.log K ≤ Real.log 2 + c * S := by
      calc Real.log K ≤ Real.log (2 * y) := Real.log_le_log hKpos hK2y
        _ = Real.log 2 + c * S := by rw [Real.log_mul (by norm_num) (by positivity), hy, Real.log_exp]
    have l2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have l3 : a * Real.log K ≤ a * Real.log 2 + c * b * Λ := by
      have := mul_le_mul_of_nonneg_left l1 ha0.le
      nlinarith
    have l4 : a * Real.log 2 ≤ 1 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith
    nlinarith
  have hsum := sum_split K a (2 * L ^ (c * b)) (1 + Λ) E ha0 hz2 hzK hKa hD hE
  rw [hinv] at hsum
  have hprod := prod_bound K (1 - a) (by linarith)
  have hrank := rankin n K (1 - a) (by linarith)
  have haL : a * L = b * S := by
    rw [ha, div_mul_eq_mul_div, div_eq_iff hSpos.ne']
    linear_combination (-b) * hS2
  have hcard : ((Nat.smoothNumbersUpTo n (K + 1)).card : ℝ) ≤ (n : ℝ) / (4 * y) := by
    calc ((Nat.smoothNumbersUpTo n (K + 1)).card : ℝ)
        ≤ (n : ℝ) ^ (1 - a) * Real.exp (4 * ∑ p ∈ Nat.primesBelow (K + 1), (p : ℝ) ^ (-(1 - a))) :=
          le_trans hrank (mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hnpos.le _))
      _ ≤ (n : ℝ) ^ (1 - a) * Real.exp ((b - c) * S - 2 * Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnpos.le _)
          apply Real.exp_le_exp.mpr
          linarith
      _ = Real.exp (L - c * S - 2 * Real.log 2) := by
          rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add, ← hL]
          congr 1
          linarith
      _ = (n : ℝ) / (4 * y) := by
          rw [Real.exp_sub, Real.exp_sub, hL, Real.exp_log hnpos, ← hy,
            show (2 : ℝ) * Real.log 2 = Real.log 4 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
            Real.exp_log (by norm_num)]
          field_simp
  have hn4 : 4 * y < n := by
    have : Real.exp (c * S + 2 * Real.log 2) < Real.exp L := Real.exp_lt_exp.mpr h5
    rw [Real.exp_add, hL, Real.exp_log hnpos, ← hy,
      show (2 : ℝ) * Real.log 2 = Real.log 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)] at this
    linarith
  have hKn : K ≤ n := by
    have : (K : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hdiv : (n : ℝ) / K - 1 < ((n / K : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := n) (b := K) (by omega)
    have h' : (n : ℝ) < ((n / K : ℕ) : ℝ) * K + K := by exact_mod_cast h
    rw [div_sub_one hKpos.ne', div_lt_iff₀ hKpos]
    linarith
  have hlt : ((Nat.smoothNumbersUpTo n (K + 1)).card : ℝ) < ((n / K : ℕ) : ℝ) := by
    have e1 : (n : ℝ) / (4 * y) ≤ (n : ℝ) / (2 * K) :=
      div_le_div_of_nonneg_left hnpos.le (by positivity) (by linarith)
    have e2 : (n : ℝ) / (2 * K) < (n : ℝ) / K - 1 := by
      have : 1 < (n : ℝ) / (2 * K) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have : (n : ℝ) / K = 2 * ((n : ℝ) / (2 * K)) := by field_simp
      linarith
    linarith
  have hP := pigeon n K hK1 (by exact_mod_cast hlt)
  have hkK : K ≤ Erdos962.k n := Nat.le_findGreatest hKn hP
  have : y ≤ (Erdos962.k n : ℝ) := le_trans hKy (by exact_mod_cast hkK)
  calc c * S = Real.log y := by rw [hy, Real.log_exp]
    _ ≤ Real.log (Erdos962.k n : ℝ) := Real.log_le_log (by linarith) this
theorem eventually_conds (c b E : ℝ) (hc : 0 < c) (hc1 : c < 1) (hb : 0 < b) (hθ : c * b < 1 / 2)
    (hbc : c < b) (hE0 : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ Real.log L ∧ 1 ≤ c * b * Real.log L ∧
      2 * b * Real.log L ≤ Real.sqrt (L * Real.log L) ∧
      2 * Real.log 2 + 4 * (Real.exp 1 *
        (Real.sqrt (L * Real.log L) / (b * Real.log L) + E) +
        2 * L ^ (c * b) * (1 + Real.log L + 2 * E)) ≤
        (b - c) * Real.sqrt (L * Real.log L) ∧
      c * Real.sqrt (L * Real.log L) + 2 * Real.log 2 < L := by
  set δ0 := (b - c) / 4 with hδ0
  have hδ0pos : 0 < δ0 := by rw [hδ0]; linarith
  set M := max (max 1 (1 / (c * b))) (max (4 * Real.exp 1 / (δ0 * b)) (1 + 2 * E)) with hM
  set W := (2 * Real.log 2 + 4 * Real.exp 1 * E) / δ0 with hW
  have hW0 : 0 ≤ W := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have := Real.exp_pos 1
    positivity
  have f1 : ∀ᶠ L : ℝ in atTop, M ≤ Real.log L := Real.tendsto_log_atTop.eventually_ge_atTop M
  have hη : (0 : ℝ) < 1 / (4 * b ^ 2 + 4) := by positivity
  have f2 := Real.isLittleO_log_id_atTop.bound hη
  have f3 : ∀ᶠ L : ℝ in atTop, max 3 (W ^ 2) ≤ L := eventually_ge_atTop _
  have hr : (0 : ℝ) < 1 / 2 - c * b := by linarith
  have hη' : (0 : ℝ) < δ0 / 16 := by positivity
  have f4 := (isLittleO_log_rpow_atTop hr).bound hη'
  filter_upwards [f1, f2, f3, f4] with L h1 h2 h3 h4
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : 1 / (c * b) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : 4 * Real.exp 1 / (δ0 * b) ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM4 : 1 + 2 * E ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hL3 : 3 ≤ L := le_trans (le_max_left _ _) h3
  have hLW : W ^ 2 ≤ L := le_trans (le_max_right _ _) h3
  set Λ := Real.log L with hΛ
  have hΛ1 : 1 ≤ Λ := le_trans hM1 h1
  have hL0 : 0 < L := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ0, id, abs_of_pos hL0] at h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ0,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _)] at h4
  have h2' : (4 * b ^ 2 + 4) * Λ ≤ L := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h2; linarith
  set S := Real.sqrt (L * Λ) with hS
  have hLΛ : 0 ≤ L * Λ := by positivity
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSL : Real.sqrt L ≤ S := Real.sqrt_le_sqrt (by nlinarith)
  have hS2 : S ≤ L / 2 := by
    rw [hS, Real.sqrt_le_left (by linarith)]
    nlinarith
  refine ⟨hΛ1, ?_, ?_, ?_, ?_⟩
  · have : 1 / (c * b) ≤ Λ := le_trans hM2 h1
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  · rw [hS, Real.le_sqrt (by positivity) hLΛ]
    nlinarith
  · have TA : 2 * Real.log 2 + 4 * Real.exp 1 * E ≤ δ0 * S := by
      have : W ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hLW
      have : W ≤ S := le_trans this hSL
      rw [hW, div_le_iff₀ hδ0pos] at this
      linarith
    have TB : 4 * (Real.exp 1 * (S / (b * Λ))) ≤ δ0 * S := by
      have hΛ' : 4 * Real.exp 1 / (δ0 * b) ≤ Λ := le_trans hM3 h1
      rw [div_le_iff₀ (by positivity)] at hΛ'
      have : 4 * (Real.exp 1 * (S / (b * Λ))) = S * (4 * Real.exp 1) / (b * Λ) := by ring
      rw [this, div_le_iff₀ (by positivity)]
      calc S * (4 * Real.exp 1) ≤ S * (Λ * (δ0 * b)) := mul_le_mul_of_nonneg_left hΛ' hS0
        _ = δ0 * S * (b * Λ) := by ring
    have TC : 4 * (2 * L ^ (c * b) * (1 + Λ + 2 * E)) ≤ δ0 * S := by
      have hΛE : 1 + Λ + 2 * E ≤ 2 * Λ := by
        have := le_trans hM4 h1; linarith
      have hP : 0 ≤ L ^ (c * b) := Real.rpow_nonneg hL0.le _
      have hsq : L ^ (c * b) * L ^ (1 / 2 - c * b) = Real.sqrt L := by
        rw [← Real.rpow_add hL0, Real.sqrt_eq_rpow]; ring_nf
      calc 4 * (2 * L ^ (c * b) * (1 + Λ + 2 * E)) ≤ 16 * (L ^ (c * b) * Λ) := by nlinarith
        _ ≤ 16 * (L ^ (c * b) * (δ0 / 16 * L ^ (1 / 2 - c * b))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left h4 hP
        _ = δ0 * Real.sqrt L := by rw [← hsq]; ring
        _ ≤ δ0 * S := mul_le_mul_of_nonneg_left hSL hδ0pos.le
    have : 2 * Real.log 2 + 4 * (Real.exp 1 * (S / (b * Λ) + E) +
        2 * L ^ (c * b) * (1 + Λ + 2 * E)) =
        (2 * Real.log 2 + 4 * Real.exp 1 * E) + 4 * (Real.exp 1 * (S / (b * Λ))) +
          4 * (2 * L ^ (c * b) * (1 + Λ + 2 * E)) := by ring
    rw [this]
    have : (b - c) * S = 4 * (δ0 * S) := by rw [hδ0]; ring
    rw [this]
    have := mul_nonneg hδ0pos.le hS0
    linarith
  · have := Real.log_two_lt_d9
    have : c * S ≤ S := mul_le_of_le_one_left hS0 hc1.le
    linarith
theorem lower_c (c : ℝ) (hc : 0 < c) (hc2 : c < 1 / Real.sqrt 2) :
    ∀ᶠ n : ℕ in atTop,
      c * Real.sqrt (Real.log n * Real.log (Real.log n)) ≤ Real.log (Erdos962.k n : ℝ) := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs : c * Real.sqrt 2 < 1 := by rwa [lt_div_iff₀ hs] at hc2
  have hcc : 2 * c ^ 2 < 1 := by nlinarith
  set b := (c + 1 / (2 * c)) / 2 with hb
  have hcb : c * b = (c ^ 2 + 1 / 2) / 2 := by rw [hb]; field_simp
  have hθ : c * b < 1 / 2 := by rw [hcb]; linarith
  have hbc : c < b := by
    rw [hb]
    have : c < 1 / (2 * c) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hb0 : 0 < b := by linarith
  have hc1 : c < 1 := by nlinarith
  have hE := OMALib.Mertens.abs_sum_inv_sub_log_log_le
  have hE0 : 0 ≤ OMALib.Mertens.mertens2Const := le_trans (abs_nonneg _) (hE 2 le_rfl)
  have hev := eventually_conds c b OMALib.Mertens.mertens2Const hc hc1 hb0 hθ hbc hE0
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hev, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn
  exact key c b _ hc hc1 hb0 hθ hE n hn1 h1 h2 h3 h4 h5

end E962

theorem OMA.solution : type_of% @Erdos962.erdos_962.variants.tang_lower_bound := by
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hSpos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (Real.log n * Real.log (Real.log n)) := by
    filter_upwards [ht.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hn hn1
    apply Real.sqrt_pos.mpr
    have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have : 0 < Real.log (n : ℝ) := by
      rcases this.lt_or_eq with h | h
      · exact h
      · rw [← h] at hn; simp at hn; linarith
    positivity
  have hs : 0 < Real.sqrt 2 := by positivity
  refine ⟨fun n => max 0 (1 / Real.sqrt 2 -
    Real.log (Erdos962.k n : ℝ) / Real.sqrt (Real.log n * Real.log (Real.log n))), ?_, ?_⟩
  · intro δ hδ
    set d := min (δ / 2) (1 / (2 * Real.sqrt 2)) with hd
    have hd0 : 0 < d := lt_min (by linarith) (by positivity)
    have hd1 : d ≤ 1 / (2 * Real.sqrt 2) := min_le_right _ _
    have hd2 : d ≤ δ / 2 := min_le_left _ _
    have hhalf : 1 / (2 * Real.sqrt 2) < 1 / Real.sqrt 2 := by
      apply one_div_lt_one_div_of_lt hs; linarith
    have hev := E962.lower_c (1 / Real.sqrt 2 - d) (by linarith) (by linarith)
    filter_upwards [hev, hSpos] with n hn hS
    have hq : 1 / Real.sqrt 2 - d ≤ Real.log (Erdos962.k n : ℝ) /
        Real.sqrt (Real.log n * Real.log (Real.log n)) := by
      rw [le_div_iff₀ hS]; exact hn
    rw [abs_of_nonneg (le_max_left _ _)]
    apply max_lt hδ
    linarith
  · filter_upwards [hSpos] with n hS
    have : 1 / Real.sqrt 2 - max 0 (1 / Real.sqrt 2 -
        Real.log (Erdos962.k n : ℝ) / Real.sqrt (Real.log n * Real.log (Real.log n))) ≤
        Real.log (Erdos962.k n : ℝ) / Real.sqrt (Real.log n * Real.log (Real.log n)) := by
      have := le_max_right 0 (1 / Real.sqrt 2 -
        Real.log (Erdos962.k n : ℝ) / Real.sqrt (Real.log n * Real.log (Real.log n)))
      linarith
    calc _ ≤ Real.log (Erdos962.k n : ℝ) / Real.sqrt (Real.log n * Real.log (Real.log n)) *
          Real.sqrt (Real.log n * Real.log (Real.log n)) := mul_le_mul_of_nonneg_right this hS.le
      _ = _ := div_mul_cancel₀ _ hS.ne'

