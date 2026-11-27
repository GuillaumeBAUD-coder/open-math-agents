import FormalConjectures.ErdosProblems.«377»
import Mathlib

/-!
# First moment of the prime reciprocal sum for central binomial coefficients

Credit: @marcusbuffett. The elementary Mertens estimates through `mertensG_step`
come from @senamakel's merged proof of the Tang lower bound for Erdős 962,
open-math-agents commit d757b84b7870c7b80a9e62d5e93a293328aee0d4.

Lucas' theorem counts admissible base-p digits. Grouping the primes by the
number of complete digits gives a geometric majorant and, in each fixed group,
an asymptotic reciprocal-prime mass given by Mertens' theorem.
-/

section
open Filter Finset
open scoped BigOperators Topology
namespace Digits377
abbrev good (p n : ℕ) := ¬p ∣ n.centralBinom
def cnt (p x : ℕ) := Nat.count (good p) x
def half (p : ℕ) := (p+1)/2

lemma small_good {p i : ℕ} (hp : p.Prime) (hi : 2*i<p) : good p i := by
  intro h
  have hf : p ∣ (i+i).factorial := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial i i]
    apply dvd_mul_of_dvd_left _ _
    apply dvd_mul_of_dvd_left _ _
    simpa [Nat.centralBinom,two_mul] using h
  have := hp.dvd_factorial.mp hf
  omega

lemma good_append {p i : ℕ} (hp : p.Prime) (hi : i<p) (q : ℕ) :
    good p (q*p+i) ↔ i < half p ∧ good p q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n:=2*(q*p+i)) (k:=q*p+i) (p:=p)
  rw [show 2*(q*p+i)=(2*q)*p+2*i by ring] at hl
  have hdiv (a b : ℕ) : (a*p+b)/p = a+b/p := by rw [Nat.mul_comm a p,Nat.mul_add_div hp.pos]
  simp only [Nat.mul_add_mod_self_right,hdiv,Nat.mod_eq_of_lt hi,Nat.div_eq_of_lt hi,add_zero] at hl
  have hh := hl.dvd_iff (dvd_refl p)
  change ¬p ∣ (2*(q*p+i)).choose (q*p+i) ↔ _
  rw [show 2*(q*p+i)=(2*q)*p+2*i by ring,hh,hp.dvd_mul]
  by_cases h : 2*i<p
  · rw [Nat.mod_eq_of_lt h,Nat.div_eq_of_lt h,add_zero]
    have hnd : ¬p∣(2*i).choose i := small_good hp h
    have hh' : i<half p := by unfold half; omega
    simp [hnd,hh',good,Nat.centralBinom]
  · have hmod : (2*i) % p < i := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
    rw [Nat.choose_eq_zero_of_lt hmod]
    have hh' : ¬i<half p := by unfold half; omega
    simp [hh']

lemma count_block {p : ℕ} (hp : p.Prime) (q : ℕ) :
    Nat.count (fun n => good p (q*p+n)) p = if good p q then half p else 0 := by
  rw [Nat.count_eq_card_filter_range]
  by_cases hq : good p q
  · rw [if_pos hq]
    have heq : (range p).filter (fun n => good p (q*p+n)) = range (half p) := by
      ext i
      simp only [mem_filter,mem_range]
      have hh : half p ≤ p := by dsimp [half]; omega
      exact ⟨fun ⟨hi,h⟩ => ((good_append hp hi q).1 h).1,
        fun h => ⟨h.trans_le hh,(good_append hp (h.trans_le hh) q).2 ⟨h,hq⟩⟩⟩
    rw [heq,card_range]
  · rw [if_neg hq,card_eq_zero,filter_eq_empty_iff]
    intro i hi h
    exact hq ((good_append hp (mem_range.1 hi) q).1 h).2

lemma count_mul {p : ℕ} (hp : p.Prime) (q : ℕ) : cnt p (q*p) = cnt p q * half p := by
  induction q with
  | zero => simp [cnt]
  | succ q ih =>
    simp only [Nat.succ_mul,cnt,Nat.count_add,Nat.count_succ,count_block hp]
    change cnt p (q*p) + _ = (cnt p q + _) * _
    rw [ih]; split_ifs <;> simp [Nat.add_mul]

lemma count_pow {p : ℕ} (hp : p.Prime) (q k : ℕ) : cnt p (q*p^k) = cnt p q * half p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,←Nat.mul_assoc,count_mul hp,ih,pow_succ,Nat.mul_assoc]

lemma count_small {p q : ℕ} (hp : p.Prime) (hq : 2*q ≤ p) : cnt p q = q := by
  rw [cnt,Nat.count_eq_card_filter_range]
  have h : (range q).filter (good p) = range q := filter_eq_self.2 fun i hi => small_good hp (by have := mem_range.1 hi; omega)
  simp [h]

lemma count_bounds {p x k : ℕ} (hp : p.Prime) :
    cnt p (x / p^k) * half p^k ≤ cnt p x ∧
    cnt p x ≤ cnt p (x / p^k+1) * half p^k := by
  have hd : 0<p^k := pow_pos hp.pos _
  rw [←count_pow hp,←count_pow hp]
  exact ⟨Nat.count_monotone _ (Nat.div_mul_le_self _ _),
    Nat.count_monotone _ (by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ x hd).le)⟩

end Digits377
end

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
open Real Filter Finset
open scoped Topology BigOperators
namespace Mass377
noncomputable abbrev root (a : ℝ) (k : ℕ) (x : ℝ) := (a*x)^((k:ℝ)⁻¹)
noncomputable def window (a b : ℝ) (k : ℕ) (x : ℝ) :=
  Nat.primesLE ⌊root b k x⌋₊ \ Nat.primesLE ⌊root a (k+1) x⌋₊
noncomputable abbrev weight (s : Finset ℕ) := ∑ p ∈ s, (1:ℝ)/p
lemma weight_mono {s t : Finset ℕ} (h : s⊆t) : weight s ≤ weight t :=
  sum_le_sum_of_subset_of_nonneg h fun i _ _ => by positivity
lemma primes_mono {x y : ℝ} (h : x≤y) : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans (Nat.floor_mono h),hp.2⟩
lemma rootTop {a : ℝ} (ha : 0<a) {k : ℕ} (hk : 0<k) :
    Tendsto (root a k) atTop atTop :=
  (tendsto_rpow_atTop (inv_pos.2 (Nat.cast_pos.2 hk))).comp (tendsto_id.const_mul_atTop ha)
lemma root_mertens {B : ℝ} (hB : Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 B))
    {a : ℝ} (ha : 0<a) {k : ℕ} (hk : 0<k) :
    Tendsto (fun x : ℝ => S (root a k x)-log (log x)) atTop (𝓝 (B+log ((k:ℝ)⁻¹))) := by
  have hR := hB.comp (rootTop ha hk)
  have hq : Tendsto (fun x : ℝ => log a / log x + 1) atTop (𝓝 1) := by
    simpa using (show Tendsto (fun x : ℝ => log a / log x) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_log_atTop).add_const 1
  have hL := hq.log (by norm_num)
  rw [log_one] at hL
  have h := (hR.add_const (log ((k:ℝ)⁻¹))).add hL
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1,(tendsto_id.const_mul_atTop ha).eventually_gt_atTop 1] with x hx hax
  have hx' : 0<x := by linarith
  have h0 := (log_pos hx).ne'
  change 1<a*x at hax
  have h1 := (log_pos hax).ne'
  have hk' := (inv_pos.2 (Nat.cast_pos.2 hk) : 0<(k:ℝ)⁻¹).ne'
  have hlog : log a / log x + 1 = log (a*x) / log x := by
    rw [log_mul ha.ne' hx'.ne',add_div,div_self h0]
  simp only [Function.comp_apply,root,log_rpow (mul_pos ha hx'),log_mul hk' h1,hlog,log_div h1 h0]
  ring
lemma window_mass {a b : ℝ} (ha : 0<a) (hb : 0<b) {k : ℕ} (hk : 0<k) :
    Tendsto (fun x : ℝ => weight (window a b k x)) atTop
      (𝓝 (log (k+1:ℕ)-log k)) := by
  obtain ⟨B,hB⟩ := realMertens
  have h := (root_mertens hB hb hk).sub (root_mertens hB ha (Nat.succ_pos k))
  simp only [log_inv,add_sub_add_left_eq_sub,neg_sub_neg] at h
  have hpos : 0 < log (k+1:ℕ)-log k := sub_pos.2 (log_lt_log (Nat.cast_pos.2 hk) (by exact_mod_cast Nat.lt_succ_self k))
  apply h.congr'
  filter_upwards [h.eventually_const_lt hpos] with x hx
  change 0 < (S (root b k x) - log (log x)) - (S (root a (k+1) x) - log (log x)) at hx
  have horder : root a (k+1) x ≤ root b k x := by
    by_contra! hn
    have := weight_mono (primes_mono hn.le)
    change S (root b k x) ≤ S (root a (k+1) x) at this
    linarith
  have hs := sum_sdiff (primes_mono horder) (f:=fun p : ℕ => (1:ℝ)/p)
  change _ = ∑ p ∈ _ \ _, _
  linarith
lemma mem_window {a b x : ℝ} {p k : ℕ} (ha : 0≤a*x) (hb : 0≤b*x) (hk : 0<k) :
    p ∈ window a b k x ↔ p.Prime ∧ (p:ℝ)^k ≤ b*x ∧ a*x < (p:ℝ)^(k+1) := by
  have hr (c : ℝ) (hc : 0≤c*x) (j : ℕ) (hj : 0<j) :
      p≤⌊root c j x⌋₊ ↔ (p:ℝ)^j ≤ c*x := by
    rw [Nat.le_floor_iff (rpow_nonneg hc _),le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hc (Nat.cast_pos.2 hj),rpow_natCast]
  rw [window,Finset.mem_sdiff,Nat.mem_primesLE,Nat.mem_primesLE,hr b hb k hk,hr a ha (k+1) (Nat.succ_pos k)]
  constructor
  · rintro ⟨⟨hu,hp⟩,hn⟩
    exact ⟨hp,hu,lt_of_not_ge (fun hh => hn ⟨hh,hp⟩)⟩
  · rintro ⟨hp,hu,hl⟩
    exact ⟨⟨hu,hp⟩,fun hh => hl.not_ge hh.1⟩
end Mass377
end

section
open Filter Finset
open scoped Topology
namespace Digits377
noncomputable abbrev v (p : ℕ) := (half p : ℝ)/p
noncomputable abbrev dens (x p : ℕ) := (cnt p x : ℝ)/x
lemma half_bounds (p : ℕ) : p ≤ 2*half p ∧ 2*half p ≤ p+1 := by unfold half; omega
lemma v_bounds {p : ℕ} (hp : 2≤p) : (1/2:ℝ) ≤ v p ∧ v p ≤ 3/4 := by
  obtain ⟨h1,h2⟩ := half_bounds p
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h1' : (p:ℝ)≤2*half p := by exact_mod_cast h1
  have h2' : 2*(half p:ℝ)≤p+1 := by exact_mod_cast h2
  constructor
  · apply (le_div_iff₀ (by linarith : 0<(p:ℝ))).2; linarith
  · apply (div_le_iff₀ (by linarith : 0<(p:ℝ))).2; linarith
lemma v_limit : Tendsto v atTop (𝓝 (1/2:ℝ)) := by
  have ht : Tendsto (fun p : ℕ => (1:ℝ)/p) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ : ℕ => (1/2:ℝ)) (h:=fun p : ℕ => 1/2+1/(p:ℝ))
    tendsto_const_nhds (by simpa using ht.const_add (1/2:ℝ))
  · filter_upwards [eventually_ge_atTop 2] with p hp using (v_bounds hp).1
  · filter_upwards [eventually_ge_atTop 2] with p hp
    have h2' : 2*(half p:ℝ) ≤ p+1 := by exact_mod_cast (half_bounds p).2
    have hp' : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
    apply (div_le_iff₀ hp').2
    rw [add_mul,div_mul_cancel₀ _ hp'.ne']; linarith
lemma cnt_estimates {p x k : ℕ} (hp : p.Prime) :
    (cnt p x:ℝ) ≤ ((x:ℝ)+p^k)*(v p)^k ∧
    (2*(x/p^k)≤p → ((x:ℝ)-p^k)*(v p)^k ≤ cnt p x) := by
  let q := x/p^k
  have hd : 0<p^k := pow_pos hp.pos _
  have hp' := Nat.cast_pos (α:=ℝ).2 hp.pos
  have hv : 0 ≤ (v p)^k := by unfold v; positivity
  have fact : (p:ℝ)^k * v p^k = (half p:ℝ)^k := by
    rw [←mul_pow]; congr 1; unfold v; field_simp
  have h0 : (q:ℝ)*(p:ℝ)^k ≤ x := by exact_mod_cast Nat.div_mul_le_self x (p^k)
  have h1 : (x:ℝ) ≤ ((q:ℝ)+1)*(p:ℝ)^k := by
    exact_mod_cast (show x≤(q+1)*p^k by simpa [q,Nat.mul_comm] using (Nat.lt_mul_div_succ x hd).le)
  obtain ⟨hl,hu⟩ := count_bounds (x:=x) (k:=k) hp
  have hc : cnt p (q+1) ≤ q+1 := Nat.count_le _
  have hu' : (cnt p x:ℝ) ≤ ((q:ℝ)+1)*(half p:ℝ)^k := by
    exact_mod_cast hu.trans (Nat.mul_le_mul_right _ hc)
  constructor
  · calc (cnt p x:ℝ) ≤ _ := hu'
         _ = (((q:ℝ)+1)*(p:ℝ)^k)*v p^k := by rw [mul_assoc,fact]
         _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hv
  · intro hsmall
    rw [count_small hp hsmall] at hl
    have hl' : (q:ℝ)*(half p:ℝ)^k ≤ cnt p x := by exact_mod_cast hl
    calc _ ≤ ((q:ℝ)*(p:ℝ)^k)*v p^k := mul_le_mul_of_nonneg_right (by linarith) hv
         _ = _ := by rw [mul_assoc,fact]
         _ ≤ _ := hl'
lemma dens_upper {p x k : ℕ} (hp : p.Prime) (hd : p^k≤x) :
    dens x p ≤ 2*(3/4:ℝ)^k := by
  have hx : 0<(x:ℝ) := by exact_mod_cast lt_of_lt_of_le (pow_pos hp.pos _) hd
  have hd' : (p:ℝ)^k ≤ x := by exact_mod_cast hd
  apply (div_le_iff₀ hx).2
  calc (cnt p x:ℝ) ≤ _ := (cnt_estimates (x:=x) (k:=k) hp).1
       _ ≤ (2*x)*(3/4:ℝ)^k := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ (by unfold v; positivity) (v_bounds hp.two_le).2 _) (by unfold v; positivity) (by positivity)
       _ = _ := by ring
lemma dens_approx {p x k : ℕ} {η : ℝ} (hp : p.Prime) (hx : 0<x)
    (hd : (p:ℝ)^k ≤ η*x) (hlarge : 4*(x:ℝ) < (p:ℝ)^(k+1)) :
    |dens x p-v p^k| ≤ η := by
  have hx' : 0<(x:ℝ) := by exact_mod_cast hx
  have hp' := pow_pos (Nat.cast_pos (α:=ℝ).2 hp.pos) k
  have hq : (x/p^k:ℕ)*p^k ≤ x := Nat.div_mul_le_self _ _
  have hs : 2*(x/p^k) ≤ p := by
    have hg : 4*x < p^k*p := by rw [pow_succ] at hlarge; exact_mod_cast hlarge
    by_contra! hh
    nlinarith [Nat.mul_le_mul_right (p^k) (show p≤2*(x/p^k) by omega)]
  obtain ⟨hu,hl⟩ := cnt_estimates (x:=x) (k:=k) hp
  have hv : 0≤v p^k := by unfold v; positivity
  have hv1 : v p^k ≤ 1 := pow_le_one₀ (by unfold v; positivity) (by linarith [(v_bounds hp.two_le).2])
  have herr : (p:ℝ)^k * v p^k ≤ η*x := (mul_le_of_le_one_right hp'.le hv1).trans hd
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ hx']; linarith [hl hs]
  · rw [sub_le_iff_le_add,div_le_iff₀ hx']; linarith
end Digits377
end

section
open Real Filter Finset Digits377 Mass377
open scoped Topology
namespace Avg377
noncomputable abbrev outer (k x : ℕ) := window 1 1 k x
noncomputable abbrev row (k x : ℕ) := ∑ p ∈ outer k x, dens x p * (1/p)
lemma outer_mem {p k x : ℕ} (hk : 0<k) :
    p∈outer k x ↔ p.Prime ∧ p^k≤x ∧ x<p^(k+1) := by
  rw [mem_window (by positivity) (by positivity) hk]
  norm_cast
  simp
lemma mass_bound : ∃ C : ℝ, 0≤C ∧ ∀ k x : ℕ, 0<k → weight (outer k x) ≤ C := by
  have hw := window_mass (a:=1) (b:=1) (k:=1) (by norm_num) (by norm_num) (by decide)
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hw.eventually_lt_const (show log (1+1:ℕ)-log (1:ℕ) < log (1+1:ℕ)-log (1:ℕ)+1 by linarith))
  let U : ℝ := max 2 T
  let C := max (S U) (log (1+1:ℕ)-log (1:ℕ)+1)
  refine ⟨C,(show 0≤S U from sum_nonneg (fun _ _ => by positivity)).trans (le_max_left _ _),?_⟩
  intro k x hk
  obtain rfl|hx := Nat.eq_zero_or_pos x
  · have he : outer k 0=∅ := eq_empty_iff_forall_notMem.2 fun p hp => by
      obtain ⟨hprime,h,_⟩ := (outer_mem hk).1 hp
      exact (pow_pos hprime.pos k).not_ge h
    simp only [he,weight,sum_empty]
    exact (show 0≤S U from sum_nonneg (fun _ _ => by positivity)).trans (le_max_left _ _)
  have hx1 : (1:ℝ)≤x := by exact_mod_cast hx
  let y := root 1 (k+1) (x:ℝ)
  have hy : 0≤y := by dsimp [y,root]; positivity
  have hk' : 0<(k:ℝ) := Nat.cast_pos.2 hk
  have hroot : root 1 k (x:ℝ) ≤ y^2 := by
    simp only [y,root,one_mul]
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul (Nat.cast_nonneg x)]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast
    have hk1 : 1≤(k:ℝ) := by exact_mod_cast hk
    rw [inv_eq_one_div,inv_eq_one_div,div_mul_eq_mul_div,one_mul,div_le_div_iff₀ hk' (by linarith)]
    linarith
  have hsub : outer k x ⊆ window 1 1 1 (y^2) := by
    intro p hp
    obtain ⟨hpr,_,_⟩ := (outer_mem hk).1 hp
    obtain ⟨hup,hlo⟩ := Finset.mem_sdiff.1 hp
    obtain ⟨hle,_⟩ := Nat.mem_primesLE.1 hup
    have hlo' : y < p := by
      by_contra! h
      exact hlo (Nat.mem_primesLE.2 ⟨Nat.le_floor h,hpr⟩)
    have hle' := (Nat.floor_le (by dsimp [root]; positivity : 0≤root 1 k (x:ℝ)))
    have hp_le : (p:ℝ) ≤ root 1 k (x:ℝ) := (Nat.cast_le.2 hle).trans hle'
    apply (mem_window (by positivity) (by positivity) (by decide : 0<1)).2
    simp only [one_mul,pow_one]
    exact ⟨hpr,hp_le.trans hroot,by exact pow_lt_pow_left₀ hlo' hy (by decide : 2 ≠ 0)⟩
  apply (weight_mono hsub).trans
  by_cases ht : T ≤ y^2
  · exact (hT _ ht).le.trans (le_max_right _ _)
  · apply (weight_mono (t:=Nat.primesLE ⌊U⌋₊) ?_).trans (le_max_left _ _)
    intro p hp
    obtain ⟨hpr,hp',_⟩ := (mem_window (by positivity) (by positivity) (by decide : 0<1)).1 hp
    simp only [pow_one,one_mul] at hp'
    exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hp'.trans ((le_of_not_ge ht).trans (le_max_right _ _))),hpr⟩
lemma row_bound {C : ℝ} (hC : ∀ k x : ℕ, 0<k → weight (outer k x) ≤ C)
    (k x : ℕ) (hk : 0<k) : ‖row k x‖ ≤ 2*C*(3/4:ℝ)^k := by
  have hpos : 0≤row k x := sum_nonneg fun _ _ => by unfold Digits377.dens; positivity
  rw [Real.norm_of_nonneg hpos]
  calc row k x ≤ ∑ p ∈ outer k x, (2*(3/4:ℝ)^k)*(1/p) := by
         apply sum_le_sum
         intro p hp
         obtain ⟨hpr,hd,_⟩ := (outer_mem hk).1 hp
         exact mul_le_mul_of_nonneg_right (dens_upper hpr hd) (by positivity)
       _ = (2*(3/4:ℝ)^k)*weight (outer k x) := (mul_sum ..).symm
       _ ≤ (2*(3/4:ℝ)^k)*C := mul_le_mul_of_nonneg_left (hC k x hk) (by positivity)
       _ = _ := by ring
end Avg377
end

section
open Real Filter Finset Digits377 Mass377 Avg377
open scoped Topology
namespace Avg377
lemma inner_sub {η : ℝ} (hη : 0<η) (hη1 : η≤1) {k x : ℕ} (hk : 0<k) :
    window 4 η k x ⊆ outer k x := by
  intro p hp
  obtain ⟨hpr,hu,hl⟩ := (mem_window (by positivity) (by positivity) hk).1 hp
  apply (mem_window (by positivity) (by positivity) hk).2
  simp only [one_mul]
  exact ⟨hpr,hu.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) x]),by linarith [Nat.cast_nonneg (α:=ℝ) x]⟩
lemma row_limit (k : ℕ) (hk : 0<k) : Tendsto (row k) atTop (𝓝 ((1/2:ℝ)^k * (log (k+1:ℕ)-log k))) := by
  let t := (1/2:ℝ)^k
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  let O (x : ℕ) := outer k x
  have hO : Tendsto (fun x : ℕ => weight (O x)) atTop (𝓝 (log (k+1:ℕ)-log k)) :=
    (window_mass (by norm_num) (by norm_num) hk).comp tendsto_natCast_atTop_atTop
  obtain ⟨C,hC,hbound⟩ := mass_bound
  have hdiff : Tendsto (fun x : ℕ => row k x - t*weight (O x)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η := min 1 (ε/(4*(C+1)))
    have hη : 0<η := lt_min (by norm_num) (by positivity)
    have hη1 : η≤1 := min_le_left .. 
    have hηε : 2*η*C ≤ ε/2 := by
      have hh := (le_div_iff₀ (by positivity : 0<4*(C+1))).1 (min_le_right 1 (ε/(4*(C+1))))
      change η*(4*(C+1))≤ε at hh
      linarith
    let I (x : ℕ) := window 4 η k x
    have hI : Tendsto (fun x : ℕ => weight (I x)) atTop (𝓝 (log (k+1:ℕ)-log k)) :=
      (window_mass (by norm_num) hη hk).comp tendsto_natCast_atTop_atTop
    have hEdge := hO.sub hI
    rw [sub_self] at hEdge
    obtain ⟨P,hP⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 (v_limit.pow k)) η hη)
    have hPbig := ((rootTop (a:=4) (by norm_num) (Nat.succ_pos k)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (P:ℝ)
    filter_upwards [hEdge.eventually_lt_const (half_pos hε),hPbig,eventually_gt_atTop 0] with x hedge hbig hx
    change weight (O x)-weight (I x)<ε/2 at hedge
    have hsub : I x ⊆ O x := inner_sub hη hη1 hk
    let E (p : ℕ) := |dens x p - t| *(1/(p:ℝ))
    have hi : ∀ p ∈ I x, E p ≤ 2*η*(1/p) := by
      intro p hip
      obtain ⟨hp,hu,hl⟩ := (mem_window (by positivity) (by positivity) hk).1 hip
      have hlow : root 4 (k+1) (x:ℝ) < (p:ℝ) := by
        by_contra! hn
        exact (Finset.mem_sdiff.1 hip).2 (Nat.mem_primesLE.2 ⟨Nat.le_floor hn,hp⟩)
      have hpP : P ≤ p := by exact_mod_cast (show (P:ℝ) ≤ p from (hbig.trans_lt hlow).le)
      have ha := dens_approx hp hx hu hl
      have hv := hP p hpP
      rw [Real.dist_eq] at hv
      have h := abs_sub_le (dens x p) (v p^k) t
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have ho (p : ℕ) : E p ≤ 1/p := by
      have hd0 : 0≤dens x p := by unfold Digits377.dens; positivity
      have hd1 : dens x p ≤ 1 := (div_le_one (Nat.cast_pos.2 hx)).2 (by exact_mod_cast (Nat.count_le (good p) : cnt p x ≤ x))
      exact mul_le_of_le_one_left (by positivity) (abs_le.2 ⟨by linarith,by linarith⟩)
    have hs := sum_sdiff hsub (f:=E)
    have hs' := sum_sdiff hsub (f:=fun p : ℕ => (1:ℝ)/p)
    have hsi : ∑ p ∈ I x, E p ≤ 2*η*weight (I x) := by
      simpa only [weight,mul_sum] using sum_le_sum hi
    have hso : ∑ p ∈ O x \ I x, E p ≤ weight (O x \ I x) := sum_le_sum fun p _ => ho p
    have hsum : |row k x - t*weight (O x)| ≤ ∑ p ∈ O x, E p := by
      change |(∑ p ∈ O x, _) - t*∑ p ∈ O x, _| ≤ _
      rw [mul_sum,← sum_sub_distrib]
      apply (abs_sum_le_sum_abs ..).trans
      apply sum_le_sum
      intro p _
      rw [←sub_mul,abs_mul,abs_of_nonneg (by positivity : 0≤1/(p:ℝ))]
    have hm := (weight_mono hsub).trans (hbound k x hk)
    have hhi := mul_le_mul_of_nonneg_left hm (by positivity : 0≤2*η)
    change weight (O x \ I x) + weight (I x) = weight (O x) at hs'
    rw [Real.dist_eq,sub_zero]
    linarith
  simpa [t] using hdiff.add (hO.const_mul t)
end Avg377
end

section
open Filter Finset Erdos377 Digits377
open scoped Topology BigOperators
namespace Avg377
noncomputable abbrev ob (p x : ℕ) := ((Icc p x).filter (good p)).card
noncomputable abbrev full (x : ℕ) := ∑ p ∈ Nat.primesLE x, Digits377.cnt p x / (p:ℝ)
noncomputable abbrev observed (x : ℕ) := ∑ n ∈ Icc 1 x, sumInvPrimesNotDvdCentralBinom n
lemma eq_obs (x : ℕ) : observed x = ∑ p ∈ Nat.primesLE x, (ob p x:ℝ)/p := by
  classical
  have hf (n : ℕ) (hn : n≤x) : sumInvPrimesNotDvdCentralBinom n =
      ∑ p ∈ Nat.primesLE x, if p≤n ∧ good p n then (1:ℝ)/p else 0 := by
    rw [sumInvPrimesNotDvdCentralBinom,←Nat.primesLE_eq_filter_Icc_one]
    have hs : (Nat.primesLE x).filter (fun p => p≤n) = Nat.primesLE n := by
      ext p
      rw [Finset.mem_filter,Nat.mem_primesLE,Nat.mem_primesLE]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hn,h.2⟩,h.1⟩⟩
    rw [←hs,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : p≤n <;> by_cases hd : p ∣ n.centralBinom <;> simp [hp,hd,good]
  change (∑ n ∈ Icc 1 x, _) = _
  rw [sum_congr rfl (fun n hn => hf n (mem_Icc.1 hn).2),sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpp := (Nat.mem_primesLE.1 hp).2.one_le
  have hs : (Icc 1 x).filter (fun n => p≤n ∧ good p n) = (Icc p x).filter (good p) := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  rw [←sum_filter,hs]
  simp [ob,div_eq_mul_inv]
lemma ob_eq {p x : ℕ} (hp : p≤x) : ob p x + cnt p p = cnt p (x+1) := by
  classical
  let A := (range (x+1)).filter (good p)
  let B := (range p).filter (good p)
  have h : B ⊆ A := filter_subset_filter _ (range_mono (by omega))
  have he : A \ B = (Icc p x).filter (good p) := by
    ext n; simp only [A,B,Finset.mem_sdiff,mem_filter,mem_range,mem_Icc]; omega
  have hh := Finset.card_sdiff_add_card_eq_card h
  rw [he] at hh
  simpa only [ob,cnt,Nat.count_eq_card_filter_range,A,B] using hh
lemma ob_error {p x : ℕ} (hp : p≤x) (hpr : p.Prime) :
    |(ob p x:ℝ)/p - cnt p x / p| ≤ 2 := by
  have h := ob_eq hp
  have hs : cnt p (x+1) = cnt p x + if good p x then 1 else 0 := Nat.count_succ ..
  have hc : cnt p p ≤ p := Nat.count_le _
  have hlo : cnt p x ≤ ob p x+p := by split_ifs at hs <;> omega
  have hhi : ob p x ≤ cnt p x+p := by have := hpr.pos; split_ifs at hs <;> omega
  have hlo' : (cnt p x:ℝ) ≤ ob p x+p := by exact_mod_cast hlo
  have hhi' : (ob p x:ℝ) ≤ cnt p x+p := by exact_mod_cast hhi
  have hp' := Nat.cast_pos (α:=ℝ).2 hpr.pos
  rw [←sub_div,abs_div,abs_of_pos hp',div_le_iff₀ hp',abs_le]
  constructor <;> linarith
lemma mean_error : Tendsto (fun x : ℕ => (1:ℝ)/x*(observed x-full x)) atTop (𝓝 0) := by
  have hpi := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun x : ℕ => (2*(Real.log 4+1))/Real.log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hpi,eventually_ge_atTop 2] with x hpi hx
  simp only [Nat.floor_natCast] at hpi
  have hx' : (1:ℝ)<x := by exact_mod_cast (show 1<x by omega)
  have hraw : |observed x-full x| ≤ 2*Nat.primeCounting x := by
    rw [eq_obs,full,←sum_sub_distrib]
    calc _ ≤ _ := abs_sum_le_sum_abs ..
         _ ≤ ∑ _p ∈ Nat.primesLE x, (2:ℝ) := by
           apply sum_le_sum
           intro p hp
           exact ob_error (Nat.mem_primesLE.1 hp).1 (Nat.mem_primesLE.1 hp).2
         _ = _ := by simp [Nat.primesLE_card_eq_primeCounting,mul_comm]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤(1:ℝ)/x)]
  calc 1/(x:ℝ)*|observed x-full x| ≤ (1/x)*(2*((Real.log 4+1)*x/Real.log x)) := by gcongr; linarith
       _ = _ := by field_simp <;> ring
end Avg377
end

section
open Filter Finset Real Avg377 Digits377 Mass377
open scoped Topology BigOperators
namespace Avg377
lemma fibers (x j : ℕ) :
    outer (j+1) x = (Nat.primesLE x).filter (fun p => Nat.log p x - 1 = j) := by
  ext p
  rw [outer_mem (Nat.succ_pos j),Finset.mem_filter,Nat.mem_primesLE]
  have hlog := Nat.log_eq_iff (b:=p) (n:=x) (Or.inl (Nat.succ_ne_zero j))
  constructor
  · rintro ⟨hp,h1,h2⟩
    have hl := hlog.2 ⟨h1,h2⟩
    have hpx : p≤x := (show p≤p^(j+1) by
      simpa only [pow_one] using (Nat.pow_le_pow_right hp.pos (show 1≤j+1 by omega))).trans h1
    exact ⟨⟨hpx,hp⟩,by omega⟩
  · rintro ⟨⟨hpx,hp⟩,hl⟩
    have h := Nat.log_pos hp.one_lt hpx
    exact ⟨hp,hlog.1 (by omega)⟩
lemma row_sum (x : ℕ) : (∑' j : ℕ, row (j+1) x) = 1/(x:ℝ) * full x := by
  classical
  let f (p : ℕ) := Nat.log p x-1
  have hm (p : ℕ) (_ : p∈Nat.primesLE x) : f p∈range (x+1) := mem_range.2 (by dsimp [f]; have := Nat.log_le_self p x; omega)
  rw [tsum_eq_sum (s:=range (x+1)) (fun j hj => ?_)]
  · simp only [row,fibers]
    rw [sum_fiberwise_of_maps_to hm]
    rw [full,mul_sum]
    apply sum_congr rfl
    intro p _; unfold Digits377.dens; ring
  · rw [row,fibers]
    have he : (Nat.primesLE x).filter (fun p => Nat.log p x-1=j) = ∅ := by
      apply filter_eq_empty_iff.2
      rintro p hp rfl
      exact hj (hm p hp)
    rw [he,sum_empty]
lemma log_series : (∑' j : ℕ, (1/2:ℝ)^(j+1)*(log (j+1+1:ℕ)-log (j+1:ℕ))) =
    ∑' j : ℕ, log (j+2:ℝ)/2^(j+2) := by
  let a (n : ℕ) := log n*(1/2:ℝ)^n
  have ha : Summable a := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (r:=(1/2:ℝ)) (by norm_num)
    simp only [pow_one] at hs
    apply hs.of_norm_bounded
    intro n
    obtain rfl|hn := Nat.eq_zero_or_pos n
    · simp [a]
    · have hlog := log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
      have hl := log_le_sub_one_of_pos (Nat.cast_pos.2 hn : 0<(n:ℝ))
      rw [Real.norm_of_nonneg (show 0≤a n by dsimp [a]; positivity)]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h1 := (summable_nat_add_iff 1).2 ha
  have h2 := (summable_nat_add_iff 2).2 ha
  have heq : (∑' j : ℕ, a (j+1)) = ∑' j : ℕ, a (j+2) := by
    rw [h1.tsum_eq_zero_add]
    simpa only [a,Nat.zero_add,Nat.cast_one,log_one,zero_mul,zero_add] using (rfl : (∑' b : ℕ, a (b+1+1)) = ∑' b : ℕ, a (b+2))
  calc _ = ∑' j : ℕ, (2*a (j+2) - a (j+1)) := by
          apply tsum_congr
          intro j
          simp only [a,show j+2=(j+1)+1 by omega,pow_succ]
          ring
       _ = 2*(∑' j : ℕ, a (j+2)) - ∑' j : ℕ, a (j+1) := by
          rw [(h2.mul_left 2).tsum_sub h1,tsum_mul_left]
       _ = ∑' j : ℕ, a (j+2) := by rw [heq]; ring
       _ = _ := by apply tsum_congr; intro j; simp [a,div_eq_mul_inv]
lemma full_limit : Tendsto (fun x : ℕ => 1/(x:ℝ)*full x) atTop
    (𝓝 (∑' j : ℕ, log (j+2:ℝ)/2^(j+2))) := by
  obtain ⟨C,hC,hb⟩ := mass_bound
  have hs : Summable (fun j : ℕ => 2*C*(3/4:ℝ)^(j+1)) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num : (3/4:ℝ)<1))).mul_left _
  have h := tendsto_tsum_of_dominated_convergence (f:=fun x j : ℕ => row (j+1) x) hs
    (fun j => row_limit _ (Nat.succ_pos j))
    (Eventually.of_forall (fun x j => row_bound hb _ x (Nat.succ_pos j)))
  rw [log_series] at h
  exact h.congr (fun x => row_sum x)
end Avg377

theorem OMA.solution : type_of% @Erdos377.erdos_377.variants.limit.i := by
  intro γ hγ
  rw [hγ]
  have h := mean_error.add full_limit
  rw [zero_add] at h
  apply h.congr
  intro x; change (1/(x:ℝ)*(observed x-full x) + 1/x*full x) = 1/x*observed x; ring
end
