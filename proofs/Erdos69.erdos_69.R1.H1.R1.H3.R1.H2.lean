import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H3_R1
import Mathlib

/-! # Prime reciprocal mass and rounding error in the second moment

Mertens' theorem bounds the reciprocal sum on the specified moving interval
by twice the triple logarithm plus a constant. The progression contains at
least one eighth of the square root of x many integers. This absorbs the
two-prime rounding term of order x to the power 1/25.

The elementary Mertens estimates through mertensG_step are from
@senamakel's merged Erdős 962 proof, commit
d757b84b7870c7b80a9e62d5e93a293328aee0d4.
The real-variable form adapts @marcusbuffett's Erdős 377 proof. -/

section

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


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377
end

section
open Filter Finset Real
namespace Numeric69
lemma prog_card (x Q b : ℕ) (hx : 256 ≤ x) (hQ : 0 < Q) (hQr : (Q:ℝ) ≤ √(x:ℝ)) :
    √(x:ℝ) ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card:ℝ) := by
  let u := x.sqrt
  have hQn : Q ≤ u := by
    change Q ≤ x.sqrt
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.le_floor hQr
  have hu : 16 ≤ u := by
    exact Nat.le_sqrt.mpr hx
  let f (i : ℕ) := x/2/Q*Q + (i+1)*Q + b%Q
  have hi : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    have he : (i+1)*Q=(j+1)*Q := by omega
    have := Nat.eq_of_mul_eq_mul_right hQ he
    omega
  have him : (range (u/4)).image f ⊆ (Icc (x/2) x).filter fun n => n%Q=b%Q := by
    rintro _ hi'
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hi'
    have hir := mem_range.mp hi
    have hdiv := Nat.div_mul_le_self (x/2) Q
    have hmod := Nat.mod_add_div (x/2) Q
    rw [Nat.mul_comm Q] at hmod
    have hm := Nat.mod_lt (x/2) hQ
    have hb := Nat.mod_lt b hQ
    have hsu := Nat.sqrt_le x
    change u*u ≤ x at hsu
    have hsum : (i+2)*Q ≤ x/2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
      calc
        (i+2)*Q*2 = (2*(i+2))*Q := by ring
        _ ≤ u*u := Nat.mul_le_mul (by omega) hQn
        _ ≤ x := hsu
    have hbase : Q ≤ (i+1)*Q := by exact Nat.le_mul_of_pos_left Q (by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · dsimp [f]; omega
    · dsimp [f]; rw [show i+2=i+1+1 by omega, Nat.add_mul, one_mul] at hsum; omega
    · simp [f,Nat.add_mod]
  have hcard := card_le_card him
  rw [card_image_of_injective _ hi,card_range] at hcard
  have hf := Nat.lt_floor_add_one (√(x:ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hf
  change √(x:ℝ) < (u:ℝ)+1 at hf
  have hbound : u+1 ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card) := by omega
  exact hf.le.trans (by exact_mod_cast hbound)
lemma floor_power (l : ℝ) (hl : 100 ≤ l) :
    let K := ⌊2*log l/log 2⌋₊
    0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ l^2 ≤ 2*(2:ℝ)^K := by
  let t := 2*log l/log 2
  let K := ⌊t⌋₊
  have hl0 : 0 < l := by linarith
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hlog).2
    have := log_le_log (by norm_num : (0:ℝ)<2) (show 2≤l by linarith)
    linarith
  have heq : (2:ℝ)^t=l^2 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hh : log 2 * t = 2*log l := by dsimp [t]; field_simp
    rw [hh, show 2 * log l = log (l^2) by simp [Real.log_pow], Real.exp_log (by positivity)]
  have h1 : (K:ℝ) ≤ t := Nat.floor_le (by linarith)
  have h2 : t ≤ (K:ℝ)+1 := (Nat.lt_floor_add_one t).le
  have hK : 1 ≤ K := Nat.le_floor (by simpa using ht)
  refine ⟨hK, ?_, ?_⟩
  · calc (2:ℝ)^K = 2^(K:ℝ) := (Real.rpow_natCast ..).symm
         _ ≤ 2^t := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
         _ = _ := heq
  · calc l^2 = (2:ℝ)^t := heq.symm
         _ ≤ 2^((K:ℝ)+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
         _ = _ := by rw [Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_one]; ring
end Numeric69
end

section
open Filter Real
namespace Numeric69
lemma growth (A : ℝ) : ∀ᶠ x : ℕ in atTop,
    let w := log (log x)
    let l := log w
    let D := exp (4*l^11)
    let R := (x:ℝ)^(1/w^2)
    256 ≤ x ∧ A ≤ l ∧ 100 ≤ l ∧ 2*D < R ∧ D < √(x:ℝ) ∧ D < (x/2:ℕ) ∧
      A ≤ R ∧ R ≤ x ∧ log (log R) = w - 2*l := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hwtop := tendsto_log_atTop.comp hlog
  have hltop := tendsto_log_atTop.comp hwtop
  have he := (tendsto_exp_div_pow_atTop 13).comp hwtop
  filter_upwards [eventually_ge_atTop 256,hlog.eventually_ge_atTop 1,hwtop.eventually_ge_atTop 2,
    hltop.eventually_ge_atTop (max A 100),he.eventually_ge_atTop 16] with x hx hxlog hw0 hl0 hexp
  let w := log (log (x:ℝ))
  let l := log w
  let R := (x:ℝ)^(1/w^2)
  have hxR : 1 < (x:ℝ) := by exact_mod_cast (show 1<x by omega)
  change 1 ≤ log (x:ℝ) at hxlog
  change 2 ≤ w at hw0
  change max A 100 ≤ l at hl0
  change 16 ≤ exp w / w^13 at hexp
  have hw : 0 < w := by linarith
  have hA := (le_max_left A 100).trans hl0
  have hl := (le_max_right A 100).trans hl0
  have hlw : l ≤ w := (log_le_sub_one_of_pos hw).trans (by linarith)
  have hwp : 16*w^13 ≤ log (x:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<w^13)).mp hexp
    simpa [w,Real.exp_log (by linarith : 0<log (x:ℝ))] using hh
  have h11 := pow_le_pow_left₀ (show 0 ≤ l by linarith) hlw 11
  have h13 : w^11 ≤ w^13 := pow_le_pow_right₀ (by linarith) (by decide)
  have hl11 : l ≤ l^11 := le_self_pow₀ (by linarith) (by decide)
  have hlogR : log R = log (x:ℝ) / w^2 := by dsimp [R]; rw [log_rpow (by linarith)]; ring
  have hratio : 16*w^11 ≤ log R := by
    rw [hlogR,le_div_iff₀ (by positivity)]
    calc 16 * w^11 * w^2 = 16*w^13 := by ring
         _ ≤ _ := hwp
  have hlR : 0 < log R := by linarith [show 0 < w^11 by positivity]
  have hR0 : 0 < R := rpow_pos_of_pos (by linarith) _
  have heR : 2*exp (4*l^11) < R := by
    rw [← exp_log (by norm_num : (0:ℝ)<2), ← exp_add, ← exp_log hR0]
    apply exp_lt_exp.mpr
    nlinarith only [hratio,h11,hl11,hl,log_two_lt_d9]
  have hD : exp (4*l^11) < √(x:ℝ) := by
    rw [← exp_log (Real.sqrt_pos.2 (by linarith : 0<(x:ℝ))), log_sqrt (by positivity)]
    apply exp_lt_exp.mpr
    linarith only [h11,h13,hwp,hl11,hl]
  have hs : √(x:ℝ) < (x/2:ℕ) := by
    have hs16 : 16 ≤ √(x:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by
      have h : (256:ℝ)≤ x := by exact_mod_cast hx
      norm_num; linarith)
    have hdiv : (x:ℝ) ≤ 2*((x/2:ℕ):ℝ)+1 := by exact_mod_cast (show x≤2*(x/2)+1 by omega)
    nlinarith [sq_sqrt (by positivity : (0:ℝ) ≤ x),sq_nonneg (√(x:ℝ)-8)]
  refine ⟨hx,hA,hl,heR,hD,hD.trans hs,?_,?_,?_⟩
  · have := add_one_le_exp (log R)
    rw [exp_log hR0] at this
    linarith only [this,hratio,hl11,h11,hA,hl]
  · calc R ≤ (x:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hxR.le
          ((div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (w-2)]))
         _ = _ := rpow_one _
  · change log (log R) = w - 2*l
    rw [hlogR,log_div (by linarith) (by positivity),log_pow]; norm_num [w,l]
end Numeric69
end

section
open Real Filter Finset
open scoped Topology
namespace Numeric69
lemma prime_mass (C x R y : ℝ) (hR : R ≤ x) (hy : y ≤ x)
    (hC1 : |Mass377.S x - log (log x) - C| < 1) (hC2 : |Mass377.S R - log (log R) - C| < 1) :
    let P := (range (⌊y⌋₊+1)).filter fun p : ℕ => p.Prime ∧ R < p ∧ (p:ℝ) ≤ y
    (∑ p ∈ P,(1:ℝ)/p) ≤ log (log x) - log (log R) + 2 := by
  intro P
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ :=
    fun p hp => Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono hR),
      (Nat.mem_primesLE.mp hp).2⟩
  have hP : P ⊆ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊R⌋₊ := by
    intro p hp
    obtain ⟨hprime, hpR, hpy⟩ := (mem_filter.mp hp).2
    refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpy.trans hy),hprime⟩,?_⟩
    intro h
    have hpos : 0 < p := hprime.pos
    have hh := (Nat.mem_primesLE.mp h).1
    have := (Nat.le_floor_iff' hpos.ne').mp hh
    linarith
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (1:ℝ)/p) hP (by intros; positivity)
  have he := Finset.sum_sdiff hsub (f := fun p : ℕ => (1:ℝ)/p)
  change _ + Mass377.S R = Mass377.S x at he
  linarith only [hsum,he,(abs_lt.mp hC1).2,(abs_lt.mp hC2).1]

theorem numeric_bound :
  ∀ η : ℝ, 0 < η → ∀ᶠ x : ℕ in atTop,
    let l := log (log (log x))
    let K := ⌊2*log l/log 2⌋₊
    let D := exp (4*l^11)
    let R := (x:ℝ)^(1/log (log x)^2)
    100 ≤ l ∧ 0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ 2*D < R ∧ D < (x/2:ℕ) ∧
    ∀ y : ℝ, y ≤ (x:ℝ)^(1/50:ℝ) → ∀ Q b : ℕ, 0 < Q → (Q:ℝ) ≤ D →
      let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
      let P := (range (⌊y⌋₊+1)).filter fun p : ℕ => p.Prime ∧ R < p ∧ (p:ℝ) ≤ y
      (N.card:ℝ)*(1/(3*2^K))*(∑ p ∈ P, (1:ℝ)/p) + 4*(P.card:ℝ)^2 ≤ η*N.card := by
  intro η hη
  obtain ⟨C,hC⟩ := Mass377.realMertens
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hC 1 (by norm_num))
  have ht := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<23/50)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (256/η)
  filter_upwards [growth (max M (8/η)),ht] with x hg hscale
  obtain ⟨hx,hlM,hl,hdR,hds,hdi,hRM,hRx,hRlog⟩ := hg
  let l := log (log (log (x:ℝ)))
  let K := ⌊2*log l/log 2⌋₊
  let R := (x:ℝ)^(1/log (log x)^2)
  let z := (x:ℝ)^(1/50:ℝ)
  change 100 ≤ l at hl
  change max M (8/η) ≤ l at hlM
  change max M (8/η) ≤ R at hRM
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1≤x by omega)
  have hx0 : (0:ℝ) < x := by linarith
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1 (by norm_num)
  have hzx : z ≤ x := by
    calc z ≤ (x:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hx1 (by norm_num)
         _ = _ := rpow_one _
  obtain ⟨hK,hK2,hKlo⟩ := floor_power l hl
  refine ⟨hl,hK,hK2,hdR,hdi,?_⟩
  intro y hy Q b hQ hQD N P
  have hprog := prog_card x Q b hx hQ (hQD.trans hds.le)
  change √(x:ℝ) ≤ 8*(N.card:ℝ) at hprog
  have hbound (t : ℝ) (ht : M ≤ t) : |Mass377.S t - log (log t) - C| < 1 := by
    simpa only [Real.dist_eq] using hM t ht
  have hmr : M ≤ R := (le_max_left _ _).trans hRM
  have hsum := prime_mass C (x:ℝ) R y hRx (hy.trans hzx)
    (hbound _ (hmr.trans hRx)) (hbound _ hmr)
  change (∑ p ∈ P,(1:ℝ)/p) ≤ log (log x) - log (log R) + 2 at hsum
  rw [hRlog] at hsum
  have hlin : 8 ≤ η*l := by
    have := (div_le_iff₀ hη).mp ((le_max_right M (8/η)).trans hlM)
    linarith
  have hsmall : (∑ p ∈ P,(1:ℝ)/p) ≤ (η/2)*(3*(2:ℝ)^K) := by
    have h1 : 2*l+2 ≤ 4*l := by linarith
    have h2 := mul_le_mul_of_nonneg_right hlin (show 0 ≤ l by linarith)
    have h3 := mul_le_mul_of_nonneg_left hKlo hη.le
    change _ ≤ log (log x) - (log (log x) - 2*l) + 2 at hsum
    nlinarith only [hsum,h1,h2,h3,hη,mul_nonneg hη.le (show 0≤(2:ℝ)^K by positivity),hl]
  have hmain : (N.card:ℝ)*(1/(3*2^K))*(∑ p ∈ P,(1:ℝ)/p) ≤ (N.card:ℝ)*(η/2) := by
    have hd : 0 < 3*(2:ℝ)^K := by positivity
    calc
      _ = (N.card:ℝ) * ((∑ p ∈ P,(1:ℝ)/p) / (3*(2:ℝ)^K)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((div_le_iff₀ hd).2 hsmall) (by positivity)
  have hc : (P.card : ℝ) ≤ 2*z := by
    have hf := Finset.card_filter_le (range (⌊y⌋₊+1)) (fun p : ℕ => p.Prime ∧ R<p ∧ (p:ℝ)≤y)
    change P.card ≤ _ at hf
    rw [card_range] at hf
    have hc' : P.card ≤ ⌊z⌋₊+1 := hf.trans (Nat.add_le_add_right (Nat.floor_mono (show y ≤ z from hy)) 1)
    have hc'' : (P.card : ℝ) ≤ (⌊z⌋₊:ℝ)+1 := by exact_mod_cast hc'
    linarith [Nat.floor_le (show 0≤z by positivity)]
  have hpows : z^2 * (x:ℝ)^(23/50 : ℝ) = √(x:ℝ) := by
    dsimp [z]
    rw [← rpow_natCast,← rpow_mul hx0.le,← rpow_add hx0,Real.sqrt_eq_rpow]
    norm_num
  change 256/η ≤ (x:ℝ)^(23/50 : ℝ) at hscale
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hη).mp hscale) (sq_nonneg z)
  have hlarge : 256*z^2 ≤ η*√(x:ℝ) := by
    rw [← hpows]
    linarith only [hm]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (P.card:ℝ)) hc 2
  have hηn := mul_le_mul_of_nonneg_left hprog hη.le
  nlinarith only [hmain,hlarge,hsq,hηn]
end Numeric69
end

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H3_R1.H2 :=
  Numeric69.numeric_bound
