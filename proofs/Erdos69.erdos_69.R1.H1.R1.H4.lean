import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1
import Mathlib

/-! # Weighted far tail and prime-square error

Average the number of prime divisors on the progression, separating primes
dividing its modulus, primes up to the square root, and larger primes. The
square-divisibility events each occupy at most one residue class among p
consecutive progression elements, up to a bounded endpoint error.

The interval counts and the finite modulus bounds adapt @marcusbuffett's
variance proof and reduction for Erdős 69. The elementary Mertens estimates
come from @senamakel's Erdős 962 proof, commit
d757b84b7870c7b80a9e62d5e93a293328aee0d4. The real-variable convergence
and growth estimates adapt @marcusbuffett's Erdős 377 and Erdős 69 proofs. -/

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
namespace Tail69
open Finset
open scoped Classical
lemma finite_bounds (l : ℝ) (hl : 100 ≤ l) (K H : ℕ)
    (hC : (2:ℝ)^K ≤ l^2) (hK : (K:ℝ) ≤ l^2) (hH : (H:ℝ) ≤ l^2)
    (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (hp : ∀ E ∈ (range K).powerset, (p E:ℝ) ≤ Real.exp (l^3) ∧
      |s E| ≤ 8*(K:ℤ)^2*p E) :
    let C := (range K).powerset
    let S := C ×ˢ Ico (K+1) (K+H+1)
    let r (a : Finset ℕ × ℕ) : ℤ := (p a.1:ℤ)*a.2-s a.1
    let W := ∏ a ∈ S.offDiag, (r a.1-r a.2).natAbs
    W ≠ 0 →
      (((∏ E ∈ C, p E) * (∏ q ∈ W.primeFactors \ C.image p, q^W.factorization q) : ℕ):ℝ) ≤
        Real.exp (4*l^11) ∧
      (∀ E ∈ C, |(s E:ℝ)| ≤ Real.exp (4*l^11)) ∧
      ∀ a ∈ S, |(r a:ℝ)| ≤ Real.exp (4*l^11) := by
  classical
  intro C S r W hW
  have hl0 : 0 ≤ l := by linarith
  have grow {i j : ℕ} (hij : i ≤ j) : l^i ≤ l^j := pow_le_pow_right₀ (by linarith) hij
  have hP := Real.pow_div_factorial_le_exp (l^3) (pow_nonneg hl0 3) 2
  norm_num at hP
  have hl4 : 100*l^4 ≤ l^6 := by
    have hl2 : 100 ≤ l^2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hl2 (pow_nonneg hl0 4)]
  have hlocal : 2*l^2+8*l^4 ≤ Real.exp (l^3) := by
    nlinarith only [hP,hl4,grow (i:=2) (j:=4) (by decide),pow_nonneg hl0 4]
  have h2P : 2 ≤ Real.exp (l^3) := by
    nlinarith [Real.add_one_le_exp (l^3),grow (i:=1) (j:=3) (by decide)]
  have hK2 : (K:ℝ)^2 ≤ l^4 := by
    calc
      _ ≤ (l^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      _ = _ := by ring
  have hss (E) (he : E ∈ C) : |(s E:ℝ)| ≤ (8*l^4)*Real.exp (l^3) := by
    have orig : |(s E:ℝ)| ≤ 8*(K:ℝ)^2*(p E:ℝ) := by exact_mod_cast (hp E he).2
    exact orig.trans (mul_le_mul (by linarith : 8*(K:ℝ)^2 ≤ 8*l^4) (hp E he).1
      (Nat.cast_nonneg _) (by positivity))
  have hr (a) (ha : a ∈ S) : |(r a:ℝ)| ≤ Real.exp (2*l^3) := by
    obtain ⟨he,hh⟩ := mem_product.mp ha
    have hval : (a.2:ℝ) ≤ 2*l^2 := by
      have ha' : a.2 ≤ K+H := by have := (mem_Ico.mp hh).2; omega
      have h' : (a.2:ℝ) ≤ K+(H:ℝ) := by exact_mod_cast ha'
      linarith
    have hv := mul_le_mul hval (hp a.1 he).1 (Nat.cast_nonneg _) (by positivity)
    change |(((p a.1:ℤ)*(a.2:ℤ)-s a.1:ℤ):ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(p a.1:ℝ)*a.2| + |(s a.1:ℝ)| := abs_sub _ _
      _ ≤ (2*l^2+8*l^4)*Real.exp (l^3) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (p a.1:ℝ)*a.2)]
        nlinarith only [hv,hss a.1 he]
      _ ≤ Real.exp (l^3)*Real.exp (l^3) :=
        mul_le_mul_of_nonneg_right hlocal (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hc : (C.card:ℝ) ≤ l^2 := by simpa [C] using hC
  have hS : (S.card:ℝ) ≤ l^4 := by
    have z : S.card = C.card * H := by simp [S]
    rw [z,Nat.cast_mul]
    calc
      _ ≤ l^2*l^2 := mul_le_mul hc hH (Nat.cast_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hoff : (S.offDiag.card:ℝ) ≤ l^8 := by
    have hsub : S.offDiag ⊆ S ×ˢ S := fun a ha =>
      mem_product.mpr ⟨(mem_offDiag.mp ha).1,(mem_offDiag.mp ha).2.1⟩
    have h' : S.offDiag.card ≤ S.card*S.card := by simpa using card_le_card hsub
    have hh : (S.offDiag.card:ℝ) ≤ (S.card:ℝ)*S.card := by exact_mod_cast h'
    calc
      _ ≤ _ := hh
      _ ≤ l^4*l^4 := mul_le_mul hS hS (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hWle : (W:ℝ) ≤ Real.exp (3*l^11) := by
    dsimp only [W]
    push_cast
    calc
      _ ≤ ∏ _ ∈ S.offDiag, Real.exp (3*l^3) := by
        apply Finset.prod_le_prod
        · intros; positivity
        · intro a ha
          obtain ⟨h1,h2,_⟩ := mem_offDiag.mp ha
          have h' : |(r a.1:ℝ)-(r a.2:ℝ)| ≤ Real.exp (2*l^3)+Real.exp (2*l^3) :=
            (abs_sub _ _).trans (add_le_add (hr _ h1) (hr _ h2))
          have he : Real.exp (3*l^3) = Real.exp (l^3)*Real.exp (2*l^3) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [he]
          have := mul_le_mul_of_nonneg_right h2P (Real.exp_pos (2*l^3)).le
          simp only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] 
          linarith
      _ = Real.exp ((S.offDiag.card:ℝ)*(3*l^3)) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hoff (show 0 ≤ 3*l^3 by positivity)])
  have hPle : ((∏ E ∈ C, p E : ℕ):ℝ) ≤ Real.exp (l^11) := by
    push_cast
    calc
      _ ≤ ∏ _ ∈ C, Real.exp (l^3) := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun E he => (hp E he).1)
      _ = Real.exp ((C.card:ℝ)*l^3) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hl0 3),grow (i:=5) (j:=11) (by decide)])
  have hD : (∏ q ∈ W.primeFactors \ C.image p, q ^ W.factorization q) ≤ W := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hW)
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hW]
    exact prod_dvd_prod_of_subset _ _ _ sdiff_subset
  have hex : Real.exp (2*l^3) ≤ Real.exp (4*l^11) := Real.exp_le_exp.mpr (by
    nlinarith [grow (i:=3) (j:=11) (by decide),pow_nonneg hl0 11])
  refine ⟨?_,?_,fun a ha => (hr a ha).trans hex⟩
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (l^11) * Real.exp (3*l^11) := mul_le_mul hPle
        (le_trans (by exact_mod_cast hD) hWle) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro E he
    apply (hss E he).trans
    apply le_trans _ hex
    rw [show 2*l^3 = l^3+l^3 by ring,Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith [sq_nonneg l]




end Tail69
end

section
namespace Tail69
open Finset
open scoped Classical
def blockPrefix (n m r : ℕ) := (range n).filter fun i => i%m=r

lemma full_blocks (k m r : ℕ) (hm : 0 < m) (hr : r < m) :
    (blockPrefix (k*m) m r).card = k := by
  have eq : blockPrefix (k*m) m r = (range k).image (fun t => t*m+r) := by
    ext i
    simp only [blockPrefix,mem_filter,mem_range,mem_image]
    constructor
    · rintro ⟨hi,he⟩
      exact ⟨i/m,(Nat.div_lt_iff_lt_mul hm).2 hi, by
        rw [←he,Nat.mul_comm]; exact Nat.div_add_mod i m⟩
    · rintro ⟨t,ht,rfl⟩
      constructor
      · calc
          _ < t*m+m := Nat.add_lt_add_left hr _
          _ = (t+1)*m := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ ht
      · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  rw [eq,card_image_of_injective,card_range]
  intro u v he
  exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel he)

lemma prefix_error (n m r : ℕ) (hm : 0 < m) (hr : r < m) :
    |((blockPrefix n m r).card:ℝ)-(n:ℝ)/m| ≤ 1 := by
  have mono {a b : ℕ} (h : a ≤ b) : blockPrefix a m r ⊆ blockPrefix b m r :=
    filter_subset_filter _ (range_mono h)
  have l := card_le_card (mono (Nat.div_mul_le_self n m))
  have u := card_le_card (mono (a:=n) (b:=(n/m+1)*m) (by
    exact ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m))).le))
  rw [full_blocks _ _ _ hm hr] at l u
  have l' : ((n/m:ℕ):ℝ) ≤ (blockPrefix n m r).card := by exact_mod_cast l
  have u' : ((blockPrefix n m r).card:ℝ) ≤ (n/m:ℕ)+1 := by exact_mod_cast u
  have dl : ((n/m:ℕ):ℝ)*(m:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
  have du : (n:ℝ) < (((n/m:ℕ):ℝ)+1)*m := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m)))
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have lo := (le_div_iff₀ mp).2 dl
  have up := (div_lt_iff₀ mp).2 du
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def interval (L U m r : ℕ) := (Icc L U).filter fun i => i%m=r%m

lemma interval_error (L U m r : ℕ) (hm : 0 < m) :
    |((interval L U m r).card:ℝ)-((U+1-L:ℕ):ℝ)/m| ≤ 2 := by
  by_cases h : L ≤ U+1
  · have hsub : blockPrefix L m (r%m) ⊆ blockPrefix (U+1) m (r%m) :=
      filter_subset_filter _ (range_mono h)
    have e : interval L U m r = blockPrefix (U+1) m (r%m) \ blockPrefix L m (r%m) := by
      ext i
      simp only [interval,blockPrefix,mem_sdiff,mem_filter,mem_Icc,mem_range]
      omega
    rw [e,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub),Nat.cast_sub h,Nat.cast_add_one]
    have h1 := abs_le.mp (prefix_error (U+1) m (r%m) hm (Nat.mod_lt _ hm))
    have h2 := abs_le.mp (prefix_error L m (r%m) hm (Nat.mod_lt _ hm))
    push_cast at h1
    rw [sub_div]
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  · have h' : U<L := by omega
    simp [interval,Finset.Icc_eq_empty_of_lt h',Nat.sub_eq_zero_of_le (by omega : U+1≤L)]

lemma class_error (L U Q b m r : ℕ) (hQ : 0<Q) (hm : 0 < m) (co : Q.Coprime m) :
    |(((interval L U Q b).filter (fun i => i%m=r%m)).card:ℝ) -
      ((interval L U Q b).card:ℝ)/m| ≤ 4 := by
  let c := Nat.chineseRemainder co b r
  have e : (interval L U Q b).filter (fun i => i%m=r%m) = interval L U (Q*m) c.val := by
    ext i
    simp only [interval,mem_filter,mem_Icc]
    change ((_ ∧ i ≡ b [MOD Q]) ∧ i ≡ r [MOD m]) ↔ _ ∧ i ≡ c.val [MOD Q*m]
    rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
    constructor
    · rintro ⟨⟨a,hb⟩,hr⟩
      exact ⟨a,hb.trans c.prop.1.symm,hr.trans c.prop.2.symm⟩
    · rintro ⟨a,hb,hr⟩
      exact ⟨⟨a,hb.trans c.prop.1⟩,hr.trans c.prop.2⟩
  rw [e]
  have h1 := interval_error L U (Q*m) c.val (Nat.mul_pos hQ hm)
  have h2 := interval_error L U Q b hQ
  have m1 : 1≤(m:ℝ) := by exact_mod_cast hm
  have h2' : |(((interval L U Q b).card:ℝ)-((U+1-L:ℕ):ℝ)/Q)/m| ≤ 2 := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < m)]
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  rw [sub_div,div_div] at h2'
  rw [Nat.cast_mul] at h1
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2'
  exact abs_le.mpr ⟨by linarith,by linarith⟩


def residue (q : ℕ) (z : ℤ) := ((-z : ℤ) : ZMod q).val

lemma residue_iff {q n : ℕ} (hq : q ≠ 0) (z : ℤ) :
    (q:ℤ) ∣ (n:ℤ)+z ↔ n ≡ residue q z [MOD q] := by
  letI : NeZero q := ⟨hq⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.natCast_eq_natCast_iff]
  simp [residue,ZMod.natCast_zmod_val,eq_neg_iff_add_eq_zero]


end Tail69
end

section
open Finset
namespace Tail69
lemma square_factor {ι : Type*} [DecidableEq ι] (C : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ C, (p i).Prime) (hinj : Set.InjOn p (↑C)) (W : ℕ)
    {i : ι} (hi : i ∈ C) :
    ∃ v : ℕ, ((∏ j ∈ C,p j) * ∏ q ∈ W.primeFactors \ C.image p, q^W.factorization q)
      = p i * v ∧ (p i).Coprime v := by
  classical
  let A := ∏ j ∈ C.erase i,p j
  let B := ∏ q ∈ W.primeFactors \ C.image p,q^W.factorization q
  refine ⟨A*B,?_,?_⟩
  · rw [← Finset.mul_prod_erase C p hi]; dsimp [A,B]; ring
  · apply Nat.Coprime.mul_right
    · apply Nat.Coprime.prod_right
      intro j hj
      obtain ⟨hne,hjC⟩ := mem_erase.mp hj
      exact (Nat.coprime_primes (hp _ hi) (hp _ hjC)).mpr (fun h => hne (hinj hi hjC h).symm)
    · apply Nat.Coprime.prod_right
      intro q hq
      obtain ⟨hqW,hqC⟩ := mem_sdiff.mp hq
      exact ((Nat.coprime_primes (hp _ hi) (Nat.prime_of_mem_primeFactors hqW)).mpr
        (fun he => hqC (mem_image.mpr ⟨i,hi,he⟩))).pow_right _
lemma square_count (L U Q b p v : ℕ) (hQ : 0<Q) (hp : p.Prime) (eqQ : Q=p*v) (co : p.Coprime v)
    (s : ℤ) :
    let N := interval L U Q b
    ((N.filter fun (n : ℕ) => (p:ℤ)^2 ∣ (n:ℤ)+s).card:ℝ) ≤ N.card/p + 4 := by
  classical
  intro N
  let F := N.filter fun (n : ℕ) => (p:ℤ)^2 ∣ (n:ℤ)+s
  by_cases hf : F.Nonempty
  · obtain ⟨u,hu⟩ := hf
    have hsub : F ⊆ interval L U (Q*p) u := by
      intro n hn
      obtain ⟨hn1,hn2⟩ := mem_filter.mp hn
      obtain ⟨hu1,hu2⟩ := mem_filter.mp hu
      obtain ⟨hni,hnq⟩ := mem_filter.mp hn1
      obtain ⟨hui,huq⟩ := mem_filter.mp hu1
      refine mem_filter.mpr ⟨hni,?_⟩
      have hQmod : n ≡ u [MOD Q] := hnq.trans huq.symm
      have hv : n ≡ u [MOD v] := hQmod.of_dvd (eqQ ▸ dvd_mul_left _ _)
      have hs : n ≡ u [MOD p^2] := by
        apply Nat.modEq_iff_dvd.mpr
        push_cast
        simpa only [add_sub_add_right_eq_sub] using Int.dvd_sub hu2 hn2
      have hh := (Nat.modEq_and_modEq_iff_modEq_mul (co.pow_left 2)).mp ⟨hs,hv⟩
      rwa [show Q*p=p^2*v by rw [eqQ]; ring]
    have hu := (abs_le.mp (interval_error L U (Q*p) u (Nat.mul_pos hQ hp.pos))).2
    have hN := (abs_le.mp (interval_error L U Q b hQ)).1
    change -2 ≤ (N.card:ℝ) - _ at hN
    have hcr : (F.card:ℝ) ≤ (interval L U (Q*p) u).card := by exact_mod_cast card_le_card hsub
    rw [Nat.cast_mul,← div_div] at hu
    have hpr : 1 ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
    have he := div_le_div_of_nonneg_right (show ((U+1-L:ℕ):ℝ)/Q ≤ N.card+2 by linarith only [hN]) (by positivity : (0:ℝ) ≤ p)
    rw [add_div] at he
    have h2 : 2/(p:ℝ) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    change (F.card:ℝ) ≤ _
    linarith only [hcr,hu,he,h2]
  · rw [not_nonempty_iff_eq_empty] at hf
    change (F.card:ℝ) ≤ _
    simp [hf]; positivity
end Tail69
end

section
open Finset Real
namespace Tail69
lemma linear_geometric (a b : ℝ) : HasSum (fun h : ℕ => (a+b*h)/2^(h+1)) (a+b) := by
  have h1 := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left (a/2)
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left (b/2)
  have hh := h1.add h2
  have he : a/2 * (1-1/2:ℝ)⁻¹ + b/2 * ((1/2:ℝ)/(1-1/2)^2) = a+b := by ring
  rw [he] at hh
  apply hh.congr_fun
  intro h
  simp only [Pi.add_apply,one_div,inv_pow,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring_nf <;> norm_num [one_div]
lemma sum_tsum_bound (N : Finset ℕ) (f : ℕ → ℕ → ℝ) (a b : ℝ)
    (hn : ∀ n ∈ N, ∀ h, 0 ≤ f n h)
    (hm : ∀ h : ℕ, ∑ n ∈ N,f n h ≤ (a+b*h)/2^(h+1)) :
    ∑ n ∈ N, ∑' h : ℕ, f n h ≤ a+b := by
  have hg := linear_geometric a b
  have hs (n : ℕ) (hN : n ∈ N) : Summable (f n) :=
    hg.summable.of_nonneg_of_le (hn n hN) (fun h =>
      (Finset.single_le_sum (f := fun n => f n h) (fun i hi => hn i hi h) hN).trans (hm h))
  calc
    _ = ∑' h : ℕ, ∑ n ∈ N, f n h := (Summable.tsum_finsetSum hs).symm
    _ ≤ ∑' h : ℕ, (a+b*h)/2^(h+1) :=
      Summable.tsum_le_tsum hm (hg.summable.of_nonneg_of_le (fun h => sum_nonneg (fun i hi => hn i hi h)) hm) hg.summable
    _ = _ := hg.tsum_eq
end Tail69
end

section
open Finset Filter Real
namespace Tail69
lemma large_factors (x m j : ℕ) (hx : 2 ≤ x) (hm : m ≤ x*(j+2)) :
    (m.primeFactors.filter (fun p => x.sqrt < p)).card ≤ 2*(j+2) := by
  classical
  by_cases h0 : m=0
  · simp [h0]
  let F := m.primeFactors.filter (fun p => x.sqrt < p)
  have hprod : (∏ p ∈ F,p) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero h0)
    (dvd_trans (Finset.prod_dvd_prod_of_subset _ _ id (filter_subset _ _)) (Nat.prod_primeFactors_dvd _))
  have hb : x^F.card ≤ (∏ p ∈ F,p)^2 := calc
    _ = ∏ _p ∈ F,x := by simp
    _ ≤ ∏ p ∈ F,p^2 := Finset.prod_le_prod' fun p hp => (Nat.sqrt_lt'.mp (mem_filter.mp hp).2).le
    _ = _ := Finset.prod_pow ..
  have hlin : j+2 ≤ x^(j+1) := by
    exact (show j+2 ≤ 2^(j+1) from (j+1).lt_two_pow_self).trans (Nat.pow_le_pow_left hx _)
  have hpow : m ≤ x^(j+2) := hm.trans (by simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left x hlin)
  apply (pow_le_pow_iff_right₀ (by omega : 1<x)).1
  calc
    x^F.card ≤ (∏ p ∈ F,p)^2 := hb
    _ ≤ (x^(j+2))^2 := Nat.pow_le_pow_left (hprod.trans hpow) _
    _ = x^(2*(j+2)) := by rw [←pow_mul,Nat.mul_comm (j+2)]

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

lemma mean (x Q b j : ℕ) (hx : 256≤x) (hQ : 0<Q) (hQt : (Q:ℝ) ≤ √(x:ℝ))
    (z : ℤ) (hm : ∀ n ∈ interval (x/2) x Q b, ((n:ℤ)+z).natAbs ≤ x*(j+2)) :
    let N := interval (x/2) x Q b
    (∑ n ∈ N, (ArithmeticFunction.cardDistinctFactors ((n:ℤ)+z).natAbs:ℝ)) ≤
      N.card*(2*log Q + 2*(j+2) + Mass377.S x + 64) := by
  classical
  intro N
  let P := (Nat.primesLE x.sqrt).filter (fun p => ¬p ∣ Q)
  let G (n : ℕ) := P.filter (fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+z)
  have point (n : ℕ) (hn : n ∈ N) :
      (ArithmeticFunction.cardDistinctFactors ((n:ℤ)+z).natAbs:ℝ) ≤ 2*log Q + 2*(j+2) + (G n).card := by
    let m := ((n:ℤ)+z).natAbs
    let F := m.primeFactors.filter fun p => x.sqrt<p
    have hsub : m.primeFactors ⊆ (Q.primeFactors ∪ F) ∪ G n := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      by_cases hd : p ∣ Q
      · exact mem_union_left _ (mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hpr,hd,hQ.ne'⟩))
      by_cases hl : x.sqrt < p
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp,hl⟩))
      apply mem_union_right
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hpr⟩,hd⟩,?_⟩
      exact Int.dvd_natAbs.mp (by exact_mod_cast (Nat.dvd_of_mem_primeFactors hp : p ∣ m))
    have hcount := (card_le_card hsub).trans (card_union_le ..)
    have hnat : m.primeFactors.card ≤ Q.primeFactors.card + 2*(j+2) + (G n).card := by
      have hlarge := large_factors x m j (by omega) (hm n hn)
      have hun := card_union_le Q.primeFactors F
      change F.card ≤ _ at hlarge
      omega
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
    have hreal : (m.primeFactors.card:ℝ) ≤ Q.primeFactors.card + 2*((j:ℝ)+2) + (G n).card := by exact_mod_cast hnat
    change (m.primeFactors.card:ℝ) ≤ _
    linarith only [hreal,countQ Q hQ]
  have hsum : ∑ n ∈ N, ((G n).card:ℝ) =
      ∑ p ∈ P, ((N.filter fun (n : ℕ) => (p:ℤ) ∣ (n:ℤ)+z).card:ℝ) := by
    simp only [G,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [sum_comm]
  have hpc : (P.card:ℝ) ≤ √(x:ℝ)+1 := by
    have hs : P ⊆ range (x.sqrt+1) := fun p hp => mem_range.mpr (by have := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1; omega)
    have hh := card_le_card hs
    rw [card_range] at hh
    have hhr : (P.card:ℝ) ≤ (x.sqrt:ℝ)+1 := by exact_mod_cast hh
    linarith only [hhr,Real.nat_sqrt_le_real_sqrt (a:=x)]
  have hNs := Numeric69.prog_card x Q b hx hQ hQt
  change √(x:ℝ) ≤ 8*(N.card:ℝ) at hNs
  have hNk : 1≤ (N.card:ℝ) := by
    have hs16 : 16 ≤ √(x:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by exact_mod_cast hx)
    linarith
  have hcmp (p : ℕ) (hp : p∈P) : ((N.filter fun (n : ℕ) => (p:ℤ) ∣ (n:ℤ)+z).card:ℝ) ≤ N.card*(1/(p:ℝ))+4 := by
    obtain ⟨hple,hnot⟩ := mem_filter.mp hp
    have hpr := (Nat.mem_primesLE.mp hple).2
    have eq : N.filter (fun (n : ℕ) => (p:ℤ) ∣ (n:ℤ)+z) = N.filter (fun n => n%p=(residue p z)%p) := by
      ext n; simp only [mem_filter,residue_iff hpr.ne_zero]; rfl
    rw [eq]
    have h := (abs_le.mp (class_error (x/2) x Q b p (residue p z) hQ hpr.pos (hpr.coprime_iff_not_dvd.mpr hnot).symm)).2
    change _ - (N.card:ℝ)/p ≤ 4 at h
    rw [mul_one_div]; linarith
  have hin : P ⊆ Nat.primesLE ⌊(x:ℝ)⌋₊ := by
    rw [Nat.floor_natCast]
    intro p hp
    have hh := Nat.mem_primesLE.mp (mem_filter.mp hp).1
    exact Nat.mem_primesLE.mpr ⟨hh.1.trans (Nat.sqrt_le_self _),hh.2⟩
  have hmass : (∑ p ∈ P, 1/(p:ℝ)) ≤ Mass377.S x :=
    sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => by positivity)
  have ht := sum_le_sum point
  have hcomp := sum_le_sum hcmp
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul,←mul_sum] at hcomp ht
  rw [hsum] at ht
  nlinarith only [ht,hcomp,mul_le_mul_of_nonneg_left hmass (show (0:ℝ)≤N.card by positivity),
    hpc,hNs,hNk]
end Tail69
end

section
open Filter Finset Real
namespace Tail69
lemma shift_size (x n p j : ℕ) (s : ℤ) (hn : n ≤ x) (hp : p ≤ x) (hs : s.natAbs ≤ x) :
    ((n:ℤ)+((p:ℤ)*j-s)).natAbs ≤ x*(j+2) := by
  calc
    _ ≤ (n:ℤ).natAbs + ((p:ℤ)*j-s).natAbs := Int.natAbs_add_le .. 
    _ ≤ (n:ℤ).natAbs + (((p:ℤ)*j).natAbs+s.natAbs) :=
      Nat.add_le_add_left (Int.natAbs_sub_le ..) _
    _ ≤ _ := by simp only [Int.natAbs_mul,Int.natAbs_natCast]; nlinarith [Nat.mul_le_mul_right j hp]

lemma vertex (x Q b p v J : ℕ) (s : ℤ) (hx : 256≤x) (hQ : 0<Q)
    (hQt : (Q:ℝ) ≤ √(x:ℝ)) (hp : p.Prime) (eqQ : Q=p*v) (co : p.Coprime v)
    (hpx : p≤x) (hsx : s.natAbs≤x) :
    let N := interval (x/2) x Q b
    let r (j : ℕ) := (p:ℤ)*j-s
    (∑ n ∈ N, ∑' h : ℕ, ((ArithmeticFunction.cardDistinctFactors ((n:ℤ)+r (h+J+1)).natAbs:ℝ)
       / 2^(h+J+1) + (if (p:ℤ)^2 ∣ (n:ℤ)+r (h+1) then (1:ℝ) else 0)/2^(h+1))) ≤
      N.card*((2*log Q + 2*((J:ℝ)+4) + Mass377.S x + 64)/2^J + 1/p) + 4 := by
  classical
  intro N r
  let a : ℝ := N.card*(2*log Q + 2*((J:ℝ)+3) + Mass377.S x + 64)/2^J + (N.card:ℝ)/p+4
  let c : ℝ := 2*N.card/2^J
  apply le_trans (b := a+c)
  · apply sum_tsum_bound N _ a c
    · intro n hn h
      split_ifs <;> positivity
    · intro h
      have hmean := mean x Q b (h+J+1) hx hQ hQt (r (h+J+1))
        (fun n hn => shift_size x n p (h+J+1) s (mem_Icc.mp (mem_filter.mp hn).1).2 hpx hsx)
      have hsq := square_count (x/2) x Q b p v hQ hp eqQ co (r (h+1))
      change (∑ n ∈ N, (ArithmeticFunction.cardDistinctFactors ((n:ℤ)+r (h+J+1)).natAbs:ℝ)) ≤ _ at hmean
      change ((N.filter fun (n : ℕ) => (p:ℤ)^2 ∣ (n:ℤ)+r (h+1)).card:ℝ) ≤ (N.card:ℝ)/p+4 at hsq
      have hi : (∑ n ∈ N, if (p:ℤ)^2 ∣ (n:ℤ)+r (h+1) then (1:ℝ) else 0) ≤ (N.card:ℝ)/p+4 := by
        simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hsq
      rw [sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
      push_cast at hmean
      calc
        _ ≤ (N.card*(2*log Q+2*((h:ℝ)+J+1+2)+Mass377.S x+64))/2^(h+J+1) +
            ((N.card:ℝ)/p+4)/2^(h+1) := by gcongr
        _ = _ := by
          dsimp [a,c]
          rw [show h+J+1=(h+1)+J by omega,pow_add (2:ℝ) (h+1) J]
          ring
  · dsimp [a,c]; ring_nf; exact le_refl _
end Tail69
end

section
open Real
namespace Tail69
lemma final_bound (l S X η : ℝ) (K H : ℕ) (hl : 100≤l) (hη : 200≤η*l)
    (hSm : S ≤ 2*exp l) (hX : l^3 ≤ X)
    (h11 : l^11 ≤ exp l) (hK : (2:ℝ)^K ≤ l^2) (hH : H=⌊l^2⌋₊) (q : ℝ) (hq : q ≤ 4*l^11) :
    (2:ℝ)^K * (X * ((2*q+2*((K+H:ℕ)+4)+S+64)/2^(K+H) + 8/exp (l^3)) + 4) ≤ η*X := by
  let w := exp l
  have hw : 0<w := exp_pos _
  have hl0 : 0<l := by linarith
  have hl1 : 1≤l := by linarith
  have hX0 : 0≤X := (by positivity : (0:ℝ)≤l^3).trans hX
  have hlw : l ≤ w := by linarith [add_one_le_exp l]
  have hl2 : l^2 ≤ l^11 := pow_le_pow_right₀ hl1 (by decide)
  have hk : (K:ℝ) ≤ l^2 := le_trans (by exact_mod_cast (K.lt_two_pow_self.le)) hK
  have hh : (H:ℝ) ≤ l^2 := hH ▸ Nat.floor_le (sq_nonneg _)
  have hh' : l^2 < (H:ℝ)+1 := hH ▸ Nat.lt_floor_add_one _
  have hpow : w^2 ≤ (2:ℝ)^H := by
    change (exp l)^2 ≤ _
    rw [←Real.exp_nat_mul,←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
    apply exp_le_exp.mpr
    have hhalf := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ log 2 by linarith [log_two_gt_d9])
      (show (0:ℝ)≤H by positivity)
    norm_num
    nlinarith [sq_nonneg (l-50)]
  let A : ℝ := 2*q+2*((K+H:ℕ)+4)+S+64
  have hA : A ≤ 100*w := by
    dsimp [A]; push_cast
    change S ≤ 2*w at hSm
    change l^11 ≤ w at h11
    linarith
  have ht1 : A*l ≤ 100*(2:ℝ)^H := calc
    _ ≤ (100*w)*l := mul_le_mul_of_nonneg_right hA hl0.le
    _ ≤ 100*(w*w) := by nlinarith [mul_le_mul_of_nonneg_left hlw hw.le]
    _ ≤ _ := by linarith [show w*w = w^2 by ring]
  have ht2 : (2:ℝ)^K * l ≤ exp (l^3) := calc
    _ ≤ l^2*l := mul_le_mul_of_nonneg_right hK hl0.le
    _ ≤ _ := by linarith [add_one_le_exp (l^3),show l^2*l=l^3 by ring]
  have ht3 : (2:ℝ)^K*l ≤ X := (mul_le_mul_of_nonneg_right hK hl0.le).trans
    ((show l^2*l=l^3 by ring).trans_le hX)
  have h1 : A/(2:ℝ)^H ≤ 100/l := (div_le_div_iff₀ (by positivity) hl0).2 ht1
  have h2 : (2:ℝ)^K*(8/exp (l^3)) ≤ 8/l := by
    rw [←mul_div_assoc,div_le_div_iff₀ (exp_pos _) hl0]; linarith only [ht2]
  have h3 : 4*(2:ℝ)^K ≤ 4/l*X := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hl0]; linarith only [ht3]
  change (2:ℝ)^K*(X*(A/2^(K+H)+8/exp (l^3))+4) ≤ _
  calc
    _ = X*(A/2^H)+ X*((2:ℝ)^K*(8/exp (l^3))) + 4*(2:ℝ)^K := by
      rw [pow_add]; field_simp <;> ring
    _ ≤ X*(100/l)+X*(8/l)+4/l*X := by gcongr
    _ = (112/l)*X := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hl0).2 (by linarith)) hX0
end Tail69
end

section
open Finset Filter Real
open scoped Classical
namespace Tail69
theorem tail :
  ∀ η : ℝ, 0 < η → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    ∀ (K H Q b : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    let l := Real.log (Real.log (Real.log x))
    let C := (Finset.range K).powerset
    let r := fun (E : Finset ℕ) (h : ℕ) => (p E : ℤ) * h - s E
    let S := C ×ˢ Finset.Ico (K + 1) (K + H + 1)
    let W := ∏ a ∈ S.offDiag, (r a.1.1 a.1.2 - r a.2.1 a.2.2).natAbs
    let N := (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)
    K = ⌊2 * Real.log l / Real.log 2⌋₊ → H = ⌊l ^ 2⌋₊ →
    (∀ E ∈ C, (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * p E ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * K ^ 2 * p E ∧ (b : ℤ) ≡ s E [ZMOD p E] ∧
      ∀ k < K, r (symmDiff E {k}) (k + 1) = r E (k + 1)) →
    Set.InjOn p C → W ≠ 0 →
    Q = (∏ E ∈ C, p E) * ∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ →
    (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b →
    ∑ n ∈ N, ∑ E ∈ C, ∑' h : ℕ,
        ((ArithmeticFunction.cardDistinctFactors ((n : ℤ) + r E (h + K + H + 1)).natAbs : ℝ)
            / 2 ^ (h + K + H + 1)
          + (if (p E : ℤ) ^ 2 ∣ (n : ℤ) + r E (h + 1) then (1 : ℝ) else 0) / 2 ^ (h + 1))
      ≤ η * N.card := by
  intro η hη
  apply eventually_atTop.mp
  obtain ⟨c,hc⟩ := Mass377.realMertens
  have he1 := (hc.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const
    (show c<c+1 by linarith)
  have ht := tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))))
  have he2 := ((tendsto_exp_div_pow_atTop 11).comp ht).eventually_ge_atTop 1
  filter_upwards [Numeric69.growth (max (c+1) (200/η)),he1,he2] with x hg hc' he
  obtain ⟨hx,hlmax,hl,hDR,hDs,hDx,_,_,_⟩ := hg
  intro K H Q b p s l C r S W N hK hH hp hinj hW hQdef _
  let D := exp (4*l^11)
  change 100≤l at hl
  change max (c+1) (200/η) ≤ l at hlmax
  change 1 ≤ exp l / l^11 at he
  change D < √(x:ℝ) at hDs
  have hl0 : 0 < l := by linarith
  have hl1 : 1 ≤ l := by linarith
  have hl11 : l^11 ≤ exp l := by have := (le_div_iff₀ (by positivity : 0 < l^11)).mp he; linarith
  have hkfloor := Numeric69.floor_power l hl
  have hk : (2:ℝ)^K ≤ l^2 := hK ▸ hkfloor.2.1
  have hk' : (K:ℝ) ≤ l^2 := (show (K:ℝ) ≤ (2:ℝ)^K by exact_mod_cast K.lt_two_pow_self.le).trans hk
  have hh' : (H:ℝ) ≤ l^2 := hH ▸ Nat.floor_le (sq_nonneg _)
  have hbds := finite_bounds l hl K H hk hk' hh' p s (fun E hE =>
    ⟨(hp E hE).2.2.1, (hp E hE).2.2.2.1⟩) hW
  have hQD : (Q:ℝ) ≤ D := by rw [hQdef]; exact hbds.1
  have hQ : 0<Q := by
    rw [hQdef]; apply Nat.mul_pos
    · exact prod_pos (fun E hE => (hp E hE).1.pos)
    · exact prod_pos (fun q hq => pow_pos (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1).pos _)
  have hQt := hQD.trans hDs.le
  have hLogQ : log (Q:ℝ) ≤ 4*l^11 := (Real.log_le_iff_le_exp (by exact_mod_cast hQ)).2 hQD
  have hxreal : (1:ℝ) < x := by exact_mod_cast (show 1<x by omega)
  have hlog3 : 0 < log (log (x:ℝ)) := by
    have h256 : (256:ℝ) ≤ x := by exact_mod_cast hx
    have hh : 1 < log (x:ℝ) := (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
    exact log_pos hh
  have hw : exp l = log (log x) := Real.exp_log hlog3
  change Mass377.S x - log (log x) < c+1 at hc'
  have hSm : Mass377.S x ≤ 2*exp l := by
    have hle := (le_max_left (c+1) (200/η)).trans hlmax
    linarith [add_one_le_exp l]
  have hNc := Numeric69.prog_card x Q b hx hQ hQt
  change √(x:ℝ) ≤ 8*(N.card:ℝ) at hNc
  have hNl : l^3 ≤ (N.card:ℝ) := by
    have h4 := pow_le_pow_right₀ hl1 (by decide : 4≤11)
    have hw4 : 2*l^3 ≤ l^4 := by
      rw [pow_succ]; nlinarith [mul_nonneg (show 0≤l-2 by linarith) (pow_nonneg hl0.le 3)]
    change exp (4*l^11) < √(x:ℝ) at hDs
    nlinarith only [hNc,hDs,add_one_le_exp (4*l^11),h4,hw4]
  have hηl : 200 ≤ η*l := by
    have := (div_le_iff₀ hη).mp ((le_max_right (c+1) (200/η)).trans hlmax)
    linarith
  let A : ℝ := (2*log Q + 2*((K+H:ℕ)+4) + Mass377.S x + 64) / 2^(K+H)
  let B : ℝ := N.card*(A+8/exp (l^3))+4
  rw [sum_comm]
  calc
    _ ≤ ∑ _E ∈ C, B := by
      apply sum_le_sum
      intro E hE
      obtain ⟨v,hv,hco⟩ := square_factor C p (fun e he => (hp e he).1) hinj W hE
      rw [← hQdef] at hv
      have hpD : (p E:ℝ) ≤ D := by
        apply ((hp E hE).2.2.1).trans (exp_le_exp.mpr ?_)
        have h3 := pow_le_pow_right₀ hl1 (by decide : 3≤11)
        linarith [show 0≤l^11 by positivity]
      have hDx' : D ≤ x := by
        change exp (4*l^11) < ((x/2:ℕ):ℝ) at hDx
        exact hDx.le.trans (by exact_mod_cast Nat.div_le_self x 2)
      have hpx : p E ≤ x := by exact_mod_cast hpD.trans hDx'
      have hsx : (s E).natAbs ≤ x := by
        have ha := (hbds.2.1 E hE).trans hDx'
        exact_mod_cast (show ((s E).natAbs:ℝ) ≤ x by simpa only [Nat.cast_natAbs,Int.cast_abs] using ha)
      have hver := vertex x Q b (p E) v (K+H) (s E) hx hQ hQt (hp E hE).1 hv hco hpx hsx
      have hrec : 1 / (p E:ℝ) ≤ 8/exp (l^3) := by
        apply (div_le_div_iff₀ (by exact_mod_cast (hp E hE).1.pos) (exp_pos _)).2
        linarith only [(hp E hE).2.1]
      dsimp only at hver
      have hiv : interval (x/2) x Q b = N := rfl
      rw [hiv] at hver
      apply le_trans (b := (N.card:ℝ) * (A + 1/(p E:ℝ)) + 4)
      · simpa only [r, A, Nat.add_assoc] using hver
      · dsimp only [B]; gcongr
    _ = (2:ℝ)^K*B := by simp [C]
    _ ≤ _ := final_bound l (Mass377.S x) N.card η K H hl hηl hSm hNl hl11 hk hH (log Q) hLogQ
end Tail69
end

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1.H4 :=
  Tail69.tail
