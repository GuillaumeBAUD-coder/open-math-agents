import FormalConjectures.ErdosProblems.«542»

-- Problem: Erdős Problem 542 — log power
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/542.lean:109 (declaration Erdos542.erdos_542.variants.log_power)
-- Credit: @NoahPuckett-IO
-- Proof: the Schinzel--Szekeres minimal-threshold construction at n = 2^(2^(6t)); the
-- construction and its density estimate are adapted from an Apache-2.0 formalization
-- (plby/lean-proofs, Erdos542), with the Mertens-type input replaced by a self-contained
-- elementary bound (Chebyshev plus summation by parts) proved below.

namespace OMA.E542

open Finset Set
open scoped BigOperators ArithmeticFunction.Omega

/-- The LCM condition, including `A ⊆ {1,...,n}`. -/
def PairwiseLCMExceeds (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

/-- Integers in `[1,n]` which are not divisible by any member of `A`. -/
def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬a ∣ m

lemma card_Icc_filter_dvd_le_div (y d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
  classical
  calc
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card
        ≤ (Finset.Icc 1 (y / d)).card := by
          refine Finset.card_le_card_of_injOn
            (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
            (t := Finset.Icc 1 (y / d))
            (fun n : ℕ => n / d) ?_ ?_
          · intro n hn
            have hn' : n ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hn
            rw [Finset.mem_filter] at hn'
            have hnIcc := Finset.mem_Icc.mp hn'.1
            have hdn : d ∣ n := hn'.2
            have htarget : n / d ∈ Finset.Icc 1 (y / d) := by
              rw [Finset.mem_Icc]
              refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
              exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hnIcc.1 hdn) hd)
            simpa using htarget
          · intro a ha b hb hab
            have ha' : a ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using ha
            have hb' : b ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hb
            rw [Finset.mem_filter] at ha'
            rw [Finset.mem_filter] at hb'
            have hda : d ∣ a := ha'.2
            have hdb : d ∣ b := hb'.2
            have hab' : a / d = b / d := by simpa using hab
            calc
              a = a / d * d := (Nat.div_mul_cancel hda).symm
              _ = b / d * d := by rw [hab']
              _ = b := Nat.div_mul_cancel hdb
    _ = y / d := by simp

namespace Mert
open Real Finset

lemma prod_pow_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h : ∀ p ∈ s, p ^ e p ∣ M) : (∏ p ∈ s, p ^ e p) ∣ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    have ha : a.Prime := hs a (Finset.mem_insert_self a r)
    have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ r, p ^ e p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      have hpp : p.Prime := hs p (Finset.mem_insert_of_mem hp)
      have hne : a ≠ p := fun h => har (h ▸ hp)
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes ha hpp).2 hne)
    exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a r))
      (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp)))

lemma pow_div_dvd_factorial {p N : ℕ} (hp : p.Prime) : p ^ (N / p) ∣ N.factorial := by
  by_cases hN : N / p = 0
  · simp [hN]
  have hpN : p ≤ N := by
    by_contra hc
    push Not at hc
    exact hN (Nat.div_eq_of_lt hc)
  have hlog : 0 < Nat.log p N := Nat.log_pos hp.one_lt hpN
  rw [hp.pow_dvd_factorial_iff (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
  have hmem : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
    simp only [Finset.mem_Ico]; omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) hmem
  simpa using this

/-- primes up to `N` -/
def P (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

lemma log_prod_P (N : ℕ) (e : ℕ → ℕ) :
    Real.log ((∏ p ∈ P N, p ^ e p : ℕ) : ℝ) = ∑ p ∈ P N, (e p : ℝ) * Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Finset.mem_filter.1 hp).2.pos
    positivity

lemma S_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ P N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  have hdvd : (∏ p ∈ P N, p ^ (N / p)) ∣ N.factorial :=
    prod_pow_dvd _ _ _ (fun p hp => (Finset.mem_filter.1 hp).2)
      (fun p hp => pow_div_dvd_factorial (Finset.mem_filter.1 hp).2)
  have hle : (∏ p ∈ P N, p ^ (N / p)) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos N) hdvd).trans (Nat.factorial_le_pow N)
  have hpos : (0 : ℝ) < ((∏ p ∈ P N, p ^ (N / p) : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ P N, p ^ (N / p) :=
      Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.1 hp).2.pos _
    exact_mod_cast this
  have h1 : ((∏ p ∈ P N, p ^ (N / p) : ℕ) : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast hle
  have hA : ∑ p ∈ P N, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have := Real.log_le_log hpos h1
    rw [log_prod_P, Real.log_pow] at this
    exact this
  have hprim : ∑ p ∈ P N, Real.log p ≤ N * Real.log 4 := by
    have hp4 : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
      exact_mod_cast (primorial_lt_four_pow N (by omega)).le
    have hpp : (0 : ℝ) < ((primorial N : ℕ) : ℝ) := by exact_mod_cast primorial_pos N
    have := Real.log_le_log hpp hp4
    have heq : ((primorial N : ℕ) : ℝ) = ((∏ p ∈ P N, p ^ 1 : ℕ) : ℝ) := by
      simp [primorial, P]
    rw [heq, log_prod_P, Real.log_pow] at this
    simpa using this
  have hfl : ∀ p ∈ P N, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hpr := (Finset.mem_filter.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    have hdm := Nat.div_add_mod N p
    have hml := Nat.mod_lt N hpr.pos
    have hcast : (N : ℝ) = p * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    have hml' : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast hml
    rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
    nlinarith
  have hsum := Finset.sum_le_sum hfl
  have hexp : ∑ p ∈ P N, ((N : ℝ) / p - 1) * Real.log p =
      N * ∑ p ∈ P N, Real.log p / p - ∑ p ∈ P N, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpr := (Finset.mem_filter.1 hp).2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
    field_simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * ∑ p ∈ P N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left key hN0

noncomputable def T (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), if n.Prime then (1 : ℝ) / n else 0
noncomputable def S (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), if n.Prime then Real.log n / n else 0

lemma S_eq (N : ℕ) : S N = ∑ p ∈ P N, Real.log p / p := by
  rw [S, P, Finset.sum_filter]

lemma T_eq (N : ℕ) : T N = ∑ p ∈ P N, (1 : ℝ) / p := by
  rw [T, P, Finset.sum_filter]

lemma step (N : ℕ) (hN : 2 ≤ N) :
    T (N + 1) - S (N + 1) / Real.log (N + 1 : ℕ) ≤
      (T N - S N / Real.log N) + (Real.log (Real.log (N + 1 : ℕ)) - Real.log (Real.log N)) +
        Real.log 4 * (1 / Real.log N - 1 / Real.log (N + 1 : ℕ)) := by
  have ha : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hab : Real.log N < Real.log (N + 1 : ℕ) :=
    Real.log_lt_log (by exact_mod_cast (show 0 < N by omega))
      (by exact_mod_cast (show N < N + 1 by omega))
  have hb : 0 < Real.log (N + 1 : ℕ) := ha.trans hab
  have hS : S N ≤ Real.log N + Real.log 4 := by
    rw [S_eq]; exact S_le N (by omega)
  have hTS : T (N + 1) - S (N + 1) / Real.log (N + 1 : ℕ) =
      T N - S N / Real.log (N + 1 : ℕ) := by
    simp only [T, S]
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => if n.Prime then Real.log n / n else 0)]
    split_ifs
    · have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · simp
  set a := Real.log N
  set b := Real.log (N + 1 : ℕ)
  have hlg : 1 - a / b ≤ Real.log b - Real.log a := by
    have := Real.log_le_sub_one_of_pos (show 0 < a / b by positivity)
    rw [Real.log_div ha.ne' hb.ne'] at this
    linarith
  have hd : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab.le
  rw [hTS]
  have e1 : T N - S N / b = (T N - S N / a) + S N * (1 / a - 1 / b) := by
    field_simp; ring
  have e2 : S N * (1 / a - 1 / b) ≤ (a + Real.log 4) * (1 / a - 1 / b) :=
    mul_le_mul_of_nonneg_right hS hd
  have e3 : (a + Real.log 4) * (1 / a - 1 / b) =
      (1 - a / b) + Real.log 4 * (1 / a - 1 / b) := by
    field_simp
  linarith

lemma invariant (N : ℕ) (hN : 2 ≤ N) :
    T N - S N / Real.log N ≤ (T 2 - S 2 / Real.log (2 : ℕ)) +
      (Real.log (Real.log N) - Real.log (Real.log (2 : ℕ))) +
        Real.log 4 * (1 / Real.log (2 : ℕ) - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have := step n hn
    linarith

theorem mertens_weak : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ P N, (1 : ℝ) / p ≤ Real.log (Real.log N) + C := by
  refine ⟨(T 2 - S 2 / Real.log (2 : ℕ)) - Real.log (Real.log (2 : ℕ)) +
      Real.log 4 * (1 / Real.log (2 : ℕ)) + 1 + Real.log 4 / Real.log (2 : ℕ), ?_⟩
  intro N hN
  have hinv := invariant N hN
  have h2 : 0 < Real.log (2 : ℕ) := Real.log_pos (by norm_num)
  have ha : Real.log (2 : ℕ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hapos : 0 < Real.log N := h2.trans_le ha
  have hS : S N ≤ Real.log N + Real.log 4 := by rw [S_eq]; exact S_le N (by omega)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hq : S N / Real.log N ≤ 1 + Real.log 4 / Real.log (2 : ℕ) := by
    rw [div_le_iff₀ hapos]
    have : Real.log 4 / Real.log (2 : ℕ) * Real.log N ≥ Real.log 4 := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ h2]
      exact mul_le_mul_of_nonneg_left ha h4
    nlinarith
  have hpos : 0 ≤ Real.log 4 * (1 / Real.log N) := by positivity
  rw [← T_eq]
  nlinarith

end Mert

noncomputable def omegaPower (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else z ^ Ω n, by simp⟩

lemma omegaPower_apply {z : ℝ} {n : ℕ} (hn : n ≠ 0) :
    omegaPower z n = z ^ Ω n := by simp [omegaPower, hn]

lemma omegaPower_multiplicative (z : ℝ) : (omegaPower z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [omegaPower]
  · intro m n hm hn hcop
    simp [omegaPower, hm, hn, mul_ne_zero hm hn,
      ArithmeticFunction.cardFactors_mul hm hn, pow_add]

noncomputable def omegaIncrement (z : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * omegaPower z

lemma omegaIncrement_multiplicative (z : ℝ) : (omegaIncrement z).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul (omegaPower_multiplicative z)

lemma omegaIncrement_mul_zeta (z : ℝ) :
    omegaIncrement z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = omegaPower z := by
  calc
    omegaIncrement z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
        omegaPower z * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [omegaIncrement]
      ac_rfl
    _ = omegaPower z := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]

lemma omegaIncrement_prime_pow_succ (z : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    omegaIncrement z (p ^ (e + 1)) = (z - 1) * z ^ e := by
  have hsum (r : ℕ) :
      (∑ k ∈ Finset.range (r + 1), omegaIncrement z (p ^ k)) = z ^ r := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f (p ^ r))
      (omegaIncrement_mul_zeta z)
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp] at h
    rw [omegaPower_apply (pow_ne_zero r hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp] at h
    exact h
  have hnext := hsum (e + 1)
  have hprev := hsum e
  rw [Finset.sum_range_succ] at hnext
  calc
    omegaIncrement z (p ^ (e + 1)) = z ^ (e + 1) - z ^ e := by linarith
    _ = (z - 1) * z ^ e := by rw [pow_succ]; ring

lemma omegaIncrement_nonneg (z : ℝ) (hz : 1 ≤ z) (n : ℕ) :
    0 ≤ omegaIncrement z n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [(omegaIncrement_multiplicative z).multiplicative_factorization _ hn]
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hePos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hePos)
  change 0 ≤ omegaIncrement z (p ^ n.factorization p)
  rw [he, omegaIncrement_prime_pow_succ z hpPrime e]
  positivity

lemma omegaPower_eq_sum_divisors (z : ℝ) {n : ℕ} (hn : n ≠ 0) :
    z ^ Ω n = ∑ d ∈ n.divisors, omegaIncrement z d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (omegaIncrement_mul_zeta z)
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [omegaPower_apply hn] at h
  exact h.symm

lemma omega_weighted_sum_le_increment_recip (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ m ∈ Finset.Icc 1 N, z ^ Ω m) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ) := by
  classical
  calc
    (∑ m ∈ Finset.Icc 1 N, z ^ Ω m) =
        ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, omegaIncrement z d := by
      apply Finset.sum_congr rfl
      intro m hm
      exact omegaPower_eq_sum_divisors z (by
        have := (Finset.mem_Icc.mp hm).1
        omega)
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m), omegaIncrement z d := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hd' := Nat.mem_divisors.mp hd
        have hmpos : 0 < m := by omega
        exact ⟨⟨Nat.succ_le_iff.mpr (Nat.pos_of_mem_divisors hd),
          (Nat.le_of_dvd hmpos hd'.1).trans (Finset.mem_Icc.mp hm).2⟩, hd'.1⟩
      · intro d hd hnot
        exact omegaIncrement_nonneg z hz d
    _ = ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 N).filter fun m => d ∣ m).card : ℝ) * omegaIncrement z d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / d) * omegaIncrement z d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hcard := card_Icc_filter_dvd_le_div N d hdpos
      have hcardR : (((Finset.Icc 1 N).filter fun m => d ∣ m).card : ℝ) ≤
          (N : ℝ) / d := (Nat.cast_le.mpr hcard).trans Nat.cast_div_le
      exact mul_le_mul_of_nonneg_right hcardR (omegaIncrement_nonneg z hz d)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
      field_simp

noncomputable def incrementDiv (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else omegaIncrement z n / (n : ℝ), by simp⟩

lemma incrementDiv_apply {z : ℝ} {n : ℕ} (hn : n ≠ 0) :
    incrementDiv z n = omegaIncrement z n / (n : ℝ) := by simp [incrementDiv, hn]

lemma incrementDiv_multiplicative (z : ℝ) : (incrementDiv z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [incrementDiv, omegaIncrement_multiplicative z |>.map_one]
  · intro m n hm hn hcop
    rw [incrementDiv_apply hm, incrementDiv_apply hn, incrementDiv_apply (mul_ne_zero hm hn),
      (omegaIncrement_multiplicative z).map_mul_of_coprime hcop]
    push_cast
    field_simp

lemma incrementDiv_prime_pow_succ (z : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    incrementDiv z (p ^ (e + 1)) =
      (z - 1) / (p : ℝ) * (z / (p : ℝ)) ^ e := by
  rw [incrementDiv_apply (pow_ne_zero _ hp.ne_zero), omegaIncrement_prime_pow_succ z hp]
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma incrementDiv_nonneg (z : ℝ) (hz : 1 ≤ z) (n : ℕ) : 0 ≤ incrementDiv z n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [incrementDiv_apply hn]
  exact div_nonneg (omegaIncrement_nonneg z hz n) (by positivity)

lemma increment_recip_le_factorial_divisors (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ)) ≤
      ∑ d ∈ N.factorial.divisors, incrementDiv z d := by
  calc
    (∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N, incrementDiv z d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [incrementDiv_apply]
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
    _ ≤ ∑ d ∈ N.factorial.divisors, incrementDiv z d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Nat.mem_divisors]
        exact ⟨Nat.dvd_factorial
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
          (Finset.mem_Icc.mp hd).2,
          ne_of_gt (Nat.factorial_pos N)⟩
      · intro d hd hnot
        rw [incrementDiv_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
        exact div_nonneg (omegaIncrement_nonneg z hz d) (by positivity)

lemma factorial_divisor_sum_eq_euler (N : ℕ) (z : ℝ) :
    (∑ d ∈ N.factorial.divisors, incrementDiv z d) =
      ∏ p ∈ N.factorial.primeFactors,
        ∑ k ∈ Finset.range (N.factorial.factorization p + 1), incrementDiv z (p ^ k) := by
  let h := incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  calc
    (∑ d ∈ N.factorial.divisors, incrementDiv z d) = h N.factorial := by
      change (∑ d ∈ N.factorial.divisors, incrementDiv z d) =
        (incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) N.factorial
      exact ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = ∏ p ∈ N.factorial.primeFactors, h (p ^ N.factorial.factorization p) := by
      rw [((incrementDiv_multiplicative z).mul
        ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization h
          (ne_of_gt (Nat.factorial_pos N))]
      rfl
    _ = ∏ p ∈ N.factorial.primeFactors,
          ∑ k ∈ Finset.range (N.factorial.factorization p + 1), incrementDiv z (p ^ k) := by
      apply Finset.prod_congr rfl
      intro p hp
      change (incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
          (p ^ N.factorial.factorization p) = _
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow
        (Nat.prime_of_mem_primeFactors hp)]

lemma incrementDiv_euler_factor_le (z : ℝ) {p E : ℕ}
    (hz1 : 1 ≤ z) (hp : p.Prime) (hzp : z < p) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv z (p ^ k)) ≤
      1 + (z - 1) / ((p : ℝ) - z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ z / (p : ℝ) := div_nonneg (by linarith) hpR.le
  have hr1 : z / (p : ℝ) < 1 := (div_lt_one hpR).2 hzp
  rw [Finset.sum_range_succ']
  have hterms :
      (∑ k ∈ Finset.range E, incrementDiv z (p ^ (k + 1))) =
        (z - 1) / (p : ℝ) * ∑ k ∈ Finset.range E, (z / (p : ℝ)) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact incrementDiv_prime_pow_succ z hp k
  rw [hterms]
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := E) hr0 hr1
  simp only [Nat.Ico_zero_eq_range, pow_zero, one_div] at hgeom
  have hcoef : 0 ≤ (z - 1) / (p : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hgeom hcoef
  have hzero : incrementDiv z (p ^ 0) = 1 := by
    simpa using (incrementDiv_multiplicative z).map_one
  rw [hzero]
  calc
    (z - 1) / (p : ℝ) * ∑ k ∈ Finset.range E, (z / (p : ℝ)) ^ k + 1 ≤
        (z - 1) / (p : ℝ) * (1 - z / (p : ℝ))⁻¹ + 1 := by linarith
    _ = 1 + (z - 1) / ((p : ℝ) - z) := by
      field_simp
      ring

lemma small_euler_factor_le_two {p E : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤ 2 := by
  have hb := incrementDiv_euler_factor_le ((21 : ℝ) / 20) (E := E)
    (by norm_num) hp (by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : ((21 : ℝ) / 20 - 1) / ((p : ℝ) - 21 / 20) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  linarith

lemma large_euler_factor_le_exp {p E : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤
      Real.exp ((11 : ℝ) / 200 / p) := by
  have hb := incrementDiv_euler_factor_le ((21 : ℝ) / 20) (E := E)
    (by norm_num) hp (by
      have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp13
      linarith)
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp13
  have hfrac : (((21 : ℝ) / 20 - 1) / ((p : ℝ) - 21 / 20)) ≤
      (11 : ℝ) / 200 / p := by
    have hpPos : (0 : ℝ) < p := by positivity
    have hden : (0 : ℝ) < (p : ℝ) - 21 / 20 := by linarith
    rw [div_le_div_iff₀ hden hpPos]
    norm_num
    nlinarith
  exact hb.trans (by linarith [hfrac, Real.add_one_le_exp ((11 : ℝ) / 200 / p)])

lemma factorial_euler_product_bound (N : ℕ) :
    (∏ p ∈ N.factorial.primeFactors,
        ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
          incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤
      32 * Real.exp ((11 : ℝ) / 200 *
        ∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) := by
  let P := N.factorial.primeFactors
  let f : ℕ → ℝ := fun p =>
    ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
      incrementDiv ((21 : ℝ) / 20) (p ^ k)
  have hsplit :
      (∏ p ∈ P, f p) = (∏ p ∈ P.filter (fun p => p < 13), f p) *
        ∏ p ∈ P.filter (fun p => ¬p < 13), f p := by
    exact (Finset.prod_filter_mul_prod_filter_not P (fun p => p < 13) f).symm
  have hf0 (p : ℕ) : 0 ≤ f p := by
    dsimp [f]
    apply Finset.sum_nonneg
    intro k hk
    exact incrementDiv_nonneg ((21 : ℝ) / 20) (by norm_num) _
  rw [hsplit]
  have hsmall : (∏ p ∈ P.filter (fun p => p < 13), f p) ≤ 32 := by
    calc
      (∏ p ∈ P.filter (fun p => p < 13), f p) ≤
          ∏ p ∈ P.filter (fun p => p < 13), (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact hf0 p
        · intro p hp
          exact small_euler_factor_le_two (Nat.prime_of_mem_primeFactors
            (Finset.mem_filter.mp hp).1)
      _ = 2 ^ (P.filter (fun p => p < 13)).card := by simp
      _ ≤ 2 ^ 5 := by
        have hsub : P.filter (fun p => p < 13) ⊆ ({2, 3, 5, 7, 11} : Finset ℕ) := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hpPrime := Nat.prime_of_mem_primeFactors hp'.1
          have hp2 := hpPrime.two_le
          have hple : p ≤ 12 := by omega
          interval_cases p <;> norm_num at hpPrime
          all_goals simp
        have hc := Finset.card_le_card hsub
        norm_num at hc
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc
      _ = 32 := by norm_num
  have hlarge : (∏ p ∈ P.filter (fun p => ¬p < 13), f p) ≤
      Real.exp ((11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p) := by
    calc
      (∏ p ∈ P.filter (fun p => ¬p < 13), f p) ≤
          ∏ p ∈ P.filter (fun p => ¬p < 13),
            Real.exp ((11 : ℝ) / 200 / p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact hf0 p
        · intro p hp
          have hpnot := (Finset.mem_filter.mp hp).2
          exact large_euler_factor_le_exp
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) (by omega)
      _ = Real.exp (∑ p ∈ P.filter (fun p => ¬p < 13),
            (11 : ℝ) / 200 / p) := by rw [← Real.exp_sum]
      _ ≤ Real.exp ((11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p) := by
        apply Real.exp_le_exp.mpr
        calc
          (∑ p ∈ P.filter (fun p => ¬p < 13), (11 : ℝ) / 200 / p) ≤
              ∑ p ∈ P, (11 : ℝ) / 200 / p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro p hp hnot
            have hpPrime := Nat.prime_of_mem_primeFactors hp
            exact div_nonneg (by norm_num) (by exact_mod_cast hpPrime.pos.le)
          _ = (11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
  have hnonnegLarge : 0 ≤ ∏ p ∈ P.filter (fun p => ¬p < 13), f p := by
    apply Finset.prod_nonneg
    intro p hp
    exact hf0 p
  exact (mul_le_mul hsmall hlarge hnonnegLarge (by norm_num)).trans_eq (by ring)

lemma factorial_prime_reciprocal_mertens :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) ≤
        Real.log (Real.log (N : ℝ)) + C := by
  obtain ⟨C, hC⟩ := Mert.mertens_weak
  refine ⟨C, fun N hN => ?_⟩
  have hsub : N.factorial.primeFactors ⊆ Mert.P N := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    simp only [Mert.P, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ((hpPrime.dvd_factorial).mp (Nat.dvd_of_mem_primeFactors hp)),
      hpPrime⟩
  calc (∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) ≤ ∑ p ∈ Mert.P N, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ _ := hC N hN

theorem omega_weighted_sum_bound :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C)) := by
  obtain ⟨C, hC⟩ := factorial_prime_reciprocal_mertens
  refine ⟨C, ?_⟩
  intro N hN
  calc
    (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          omegaIncrement ((21 : ℝ) / 20) d / (d : ℝ) :=
      omega_weighted_sum_le_increment_recip N _ (by norm_num)
    _ ≤ (N : ℝ) * ∑ d ∈ N.factorial.divisors,
          incrementDiv ((21 : ℝ) / 20) d := by
      gcongr
      exact increment_recip_le_factorial_divisors N _ (by norm_num)
    _ = (N : ℝ) * ∏ p ∈ N.factorial.primeFactors,
          ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
            incrementDiv ((21 : ℝ) / 20) (p ^ k) := by
      rw [factorial_divisor_sum_eq_euler]
    _ ≤ (N : ℝ) * (32 * Real.exp ((11 : ℝ) / 200 *
          ∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p)) := by
      gcongr
      exact factorial_euler_product_bound N
    _ ≤ (N : ℝ) * (32 * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) := by
      gcongr
      exact hC N hN
    _ = 32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C)) := by ring

def thresholdSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun r => n < r * r.minFac

def minimalThresholdSet (n : ℕ) : Finset ℕ :=
  (thresholdSet n).filter fun a =>
    ∀ c ∈ thresholdSet n, c ∣ a → a ∣ c

lemma threshold_minimal_cover {n r : ℕ} (hr : r ∈ thresholdSet n) :
    ∃ a ∈ minimalThresholdSet n, a ∣ r := by
  classical
  let D := (thresholdSet n).filter fun c => c ∣ r
  have hD : D.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, dvd_rfl⟩⟩
  let a := D.min' hD
  have haD : a ∈ D := Finset.min'_mem D hD
  have haParts := Finset.mem_filter.mp haD
  refine ⟨a, ?_, haParts.2⟩
  rw [minimalThresholdSet, Finset.mem_filter]
  refine ⟨haParts.1, ?_⟩
  intro c hc hca
  have hcr : c ∣ r := dvd_trans hca haParts.2
  have hcD : c ∈ D := Finset.mem_filter.mpr ⟨hc, hcr⟩
  have hac : a ≤ c := Finset.min'_le D c hcD
  have hcpos : 0 < c := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    omega
  have hapos : 0 < a := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp haParts.1).1).1
    omega
  have hcaLe : c ≤ a := Nat.le_of_dvd hapos hca
  exact (Nat.le_antisymm hcaLe hac) ▸ dvd_rfl

lemma minimalThreshold_antichain {n a b : ℕ}
    (ha : a ∈ minimalThresholdSet n) (hb : b ∈ minimalThresholdSet n)
    (hab : a ≠ b) : ¬a ∣ b := by
  intro hdvd
  have hbparts := Finset.mem_filter.mp hb
  have haparts := Finset.mem_filter.mp ha
  have hba := hbparts.2 a haparts.1 hdvd
  exact hab (Nat.dvd_antisymm hdvd hba)

lemma minimalThreshold_lcm_gt_of_lt {n a b : ℕ}
    (ha : a ∈ minimalThresholdSet n) (hb : b ∈ minimalThresholdSet n)
    (hab : a < b) : n < Nat.lcm a b := by
  have haT := (Finset.mem_filter.mp ha).1
  have hbT := (Finset.mem_filter.mp hb).1
  have haIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp haT).1
  have hbIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hbT).1
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  let g := Nat.gcd a b
  let q₁ := a / g
  let q₂ := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b hapos
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have haeq : g * q₁ = a := by
    dsimp [q₁]
    simpa [mul_comm] using Nat.div_mul_cancel hga
  have hbeq : g * q₂ = b := by
    dsimp [q₂]
    simpa [mul_comm] using Nat.div_mul_cancel hgb
  have hq_lt : q₁ < q₂ := by
    rw [← (Nat.mul_lt_mul_left hgpos)]
    simpa [haeq, hbeq] using hab
  have hq1ne : q₁ ≠ 1 := by
    intro hq
    rw [hq, mul_one] at haeq
    have hag : a = g := haeq.symm
    have habDvd : a ∣ b := hag ▸ hgb
    exact minimalThreshold_antichain ha hb (ne_of_lt hab) habDvd
  have hq1two : 2 ≤ q₁ := by
    have hqpos : 0 < q₁ := by
      have : 0 < g * q₁ := haeq.symm ▸ hapos
      exact Nat.pos_of_mul_pos_left this
    omega
  have hq1dvd : q₁ ∣ a := ⟨g, by simpa [mul_comm] using haeq.symm⟩
  have hmin : a.minFac ≤ q₁ := Nat.minFac_le_of_dvd hq1two hq1dvd
  have hlcmEq : Nat.lcm a b = g * q₁ * q₂ := by
    have hprod := Nat.gcd_mul_lcm a b
    have hcancel : Nat.lcm a b = g * q₁ * q₂ := by
      apply Nat.eq_of_mul_eq_mul_left hgpos
      calc
        g * Nat.lcm a b = a * b := hprod
        _ = (g * q₁) * (g * q₂) := by rw [haeq, hbeq]
        _ = g * (g * q₁ * q₂) := by ring
    exact hcancel
  have haThresh : n < a * a.minFac := (Finset.mem_filter.mp haT).2
  calc
    n < a * a.minFac := haThresh
    _ ≤ a * q₁ := Nat.mul_le_mul_left a hmin
    _ < a * q₂ := (Nat.mul_lt_mul_left hapos).2 hq_lt
    _ = Nat.lcm a b := by rw [hlcmEq, ← haeq]

lemma minimalThreshold_admissible (n : ℕ) :
    PairwiseLCMExceeds n (minimalThresholdSet n) := by
  constructor
  · intro a ha
    have haT := (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp haT).1
  · intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact minimalThreshold_lcm_gt_of_lt ha hb hlt
    · rw [Nat.lcm_comm]
      exact minimalThreshold_lcm_gt_of_lt hb ha hgt

lemma uncovered_not_threshold {n b : ℕ}
    (hb : b ∈ uncovered n (minimalThresholdSet n)) : b ∉ thresholdSet n := by
  intro hbT
  obtain ⟨a, ha, hab⟩ := threshold_minimal_cover hbT
  have hb' := Finset.mem_filter.mp hb
  exact hb'.2 a ha hab

lemma uncovered_power_bound {n b : ℕ}
    (hb : b ∈ uncovered n (minimalThresholdSet n)) :
    b ^ (2 ^ Ω b) ≤ n ^ (2 ^ Ω b - 1) := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      have hbParts := Finset.mem_filter.mp hb
      have hbIcc := Finset.mem_Icc.mp hbParts.1
      by_cases hb1 : b = 1
      · subst b
        simp
      · have hbgt : 1 < b := by omega
        let p := b.minFac
        let c := b / p
        have hpPrime : p.Prime := Nat.minFac_prime hb1
        have hp2 : 2 ≤ p := hpPrime.two_le
        have hpdvd : p ∣ b := Nat.minFac_dvd b
        have hceq : c * p = b := by
          dsimp [c]
          exact Nat.div_mul_cancel hpdvd
        have hcpos : 0 < c := by
          dsimp [c]
          exact Nat.div_pos (Nat.minFac_le (by omega)) hpPrime.pos
        have hclt : c < b := by
          dsimp [c]
          exact Nat.div_lt_self (by omega) (by omega)
        have hcIcc : c ∈ Finset.Icc 1 n := by
          rw [Finset.mem_Icc]
          exact ⟨hcpos, (Nat.le_of_dvd (by omega) ⟨p, hceq.symm⟩).trans hbIcc.2⟩
        have hcUncovered : c ∈ uncovered n (minimalThresholdSet n) := by
          rw [uncovered, Finset.mem_filter]
          refine ⟨hcIcc, ?_⟩
          intro a ha hac
          exact hbParts.2 a ha (dvd_trans hac ⟨p, hceq.symm⟩)
        have hOmega : Ω b = Ω c + 1 := by
          rw [← hceq, ArithmeticFunction.cardFactors_mul (ne_of_gt hcpos) hpPrime.ne_zero,
            ArithmeticFunction.cardFactors_apply_prime hpPrime]
        have hnotT := uncovered_not_threshold hb
        have hbp : b * p ≤ n := by
          rw [thresholdSet, Finset.mem_filter] at hnotT
          push Not at hnotT
          exact hnotT hbParts.1
        have hbSq : b ^ 2 ≤ n * c := by
          have hmul := Nat.mul_le_mul_left c hbp
          calc
            b ^ 2 = c * (b * p) := by rw [pow_two, ← hceq]; ring
            _ ≤ c * n := hmul
            _ = n * c := by ring
        have hIH := ih c hclt hcUncovered
        rw [hOmega]
        let E := 2 ^ Ω c
        have hpow := Nat.pow_le_pow_left hbSq E
        have hmulIH := Nat.mul_le_mul_left (n ^ E) hIH
        dsimp [E] at hpow hmulIH ⊢
        calc
          b ^ (2 ^ (Ω c + 1)) = (b ^ 2) ^ (2 ^ Ω c) := by
            rw [← pow_mul]
            congr 1
            rw [pow_succ]
            omega
          _ ≤ (n * c) ^ (2 ^ Ω c) := hpow
          _ = n ^ (2 ^ Ω c) * c ^ (2 ^ Ω c) := by rw [mul_pow]
          _ ≤ n ^ (2 ^ Ω c) * n ^ (2 ^ Ω c - 1) := hmulIH
          _ = n ^ (2 ^ (Ω c + 1) - 1) := by
            rw [← pow_add, pow_succ]
            congr 1
            have hpos : 0 < 2 ^ Ω c := pow_pos (by omega) _
            have : 1 ≤ 2 ^ Ω c := by omega
            omega

/-! ### The explicit sparse subsequence -/

/-- The exponent used for the ambient interval at stage `t`. -/
def constructionExponent (t : ℕ) : ℕ := 2 ^ (6 * t)

/-- The ambient endpoint at stage `t`. -/
def constructionAmbient (t : ℕ) : ℕ := 2 ^ constructionExponent t

/-- The minimal-threshold family at stage `t`. -/
def constructionFamily (t : ℕ) : Finset ℕ :=
  minimalThresholdSet (constructionAmbient t)

lemma constructionFamily_admissible (t : ℕ) :
    PairwiseLCMExceeds (constructionAmbient t) (constructionFamily t) := by
  exact minimalThreshold_admissible _

lemma pow_two_le_constructionExponent {t e : ℕ} (he : e ≤ 5 * t) :
    2 ^ t * 2 ^ e ≤ constructionExponent t := by
  calc
    2 ^ t * 2 ^ e ≤ 2 ^ t * 2 ^ (5 * t) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he)
    _ = constructionExponent t := by
      rw [← pow_add]
      simp only [constructionExponent]
      congr 1
      omega

lemma lowOmega_uncovered_le {t b : ℕ}
    (hb : b ∈ uncovered (constructionAmbient t) (constructionFamily t))
    (hΩ : Ω b ≤ 5 * t) :
    b ≤ 2 ^ (constructionExponent t - 2 ^ t) := by
  have hpow := uncovered_power_bound hb
  let E := 2 ^ Ω b
  let R := constructionExponent t
  let D := 2 ^ t
  have hEpos : 0 < E := by positivity
  have hDE : D * E ≤ R := by
    exact pow_two_le_constructionExponent hΩ
  have hDR : D ≤ R := le_trans (Nat.le_mul_of_pos_right D (by positivity)) hDE
  have hexp : R * (E - 1) ≤ (R - D) * E := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_mul]
    simpa using Nat.sub_le_sub_left hDE (R * E)
  have htarget : b ^ E ≤ (2 ^ (R - D)) ^ E := by
    calc
      b ^ E ≤ (2 ^ R) ^ (E - 1) := by
        simpa [constructionAmbient, R, E] using hpow
      _ = 2 ^ (R * (E - 1)) := by rw [pow_mul]
      _ ≤ 2 ^ ((R - D) * E) := Nat.pow_le_pow_right (by omega) hexp
      _ = (2 ^ (R - D)) ^ E := by rw [pow_mul]
  simpa [D, R] using (Nat.pow_le_pow_iff_left hEpos.ne').mp htarget

def highOmegaUpTo (N K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m => K < Ω m

lemma uncovered_card_le_low_add_high (t : ℕ) :
    (uncovered (constructionAmbient t) (constructionFamily t)).card ≤
      2 ^ (constructionExponent t - 2 ^ t) +
        (highOmegaUpTo (constructionAmbient t) (5 * t)).card := by
  let B := 2 ^ (constructionExponent t - 2 ^ t)
  let H := highOmegaUpTo (constructionAmbient t) (5 * t)
  have hsub : uncovered (constructionAmbient t) (constructionFamily t) ⊆
      Finset.Icc 1 B ∪ H := by
    intro b hb
    by_cases hΩ : Ω b ≤ 5 * t
    · rw [Finset.mem_union]
      exact Or.inl (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1,
          lowOmega_uncovered_le hb hΩ⟩)
    · rw [Finset.mem_union]
      exact Or.inr (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hb).1, Nat.lt_of_not_ge hΩ⟩)
  calc
    (uncovered (constructionAmbient t) (constructionFamily t)).card ≤
        (Finset.Icc 1 B ∪ H).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 B).card + H.card := Finset.card_union_le _ _
    _ = B + H.card := by simp [B]

lemma highOmega_card_weight_le (N K : ℕ) :
    ((highOmegaUpTo N K).card : ℝ) * ((21 : ℝ) / 20) ^ (K + 1) ≤
      ∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m := by
  calc
    ((highOmegaUpTo N K).card : ℝ) * ((21 : ℝ) / 20) ^ (K + 1) =
        ∑ m ∈ highOmegaUpTo N K, ((21 : ℝ) / 20) ^ (K + 1) := by simp
    _ ≤ ∑ m ∈ highOmegaUpTo N K, ((21 : ℝ) / 20) ^ Ω m := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hm).2
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro m hm hnot
      positivity

lemma log_log_constructionAmbient_le (t : ℕ) :
    Real.log (Real.log (constructionAmbient t : ℝ)) ≤
      (21 : ℝ) / 5 * t := by
  have hRpos : (0 : ℝ) < constructionExponent t := by
    exact_mod_cast (show 0 < constructionExponent t by
      simp [constructionExponent])
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hloglog2 : Real.log (Real.log (2 : ℝ)) ≤ 0 :=
    Real.log_nonpos hlog2pos.le (by
      linarith [Real.log_two_lt_d9])
  have hmain : ((6 * t : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
      (21 : ℝ) / 5 * t := by
    push_cast
    have ht : (0 : ℝ) ≤ t := by positivity
    nlinarith [Real.log_two_lt_d9]
  rw [constructionAmbient, Nat.cast_pow, Real.log_pow,
    Real.log_mul hRpos.ne' (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))]
  have hRlog : Real.log (constructionExponent t : ℝ) =
      ((6 * t : ℕ) : ℝ) * Real.log (2 : ℝ) := by
    rw [constructionExponent, Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hRlog]
  linarith

lemma highOmega_density_le_geometric (C : ℝ)
    (hC : ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) (t : ℕ) :
    ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
        constructionAmbient t ≤
      (32 * Real.exp ((11 : ℝ) / 200 * C)) *
        (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
  let N := constructionAmbient t
  let K := 5 * t + 1
  let z : ℝ := 21 / 20
  let A : ℝ := (11 : ℝ) / 200 * (Real.log (Real.log (N : ℝ)) + C)
  have hN2 : 2 ≤ N := by
    dsimp [N, constructionAmbient, constructionExponent]
    exact Nat.one_lt_pow (by positivity) (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN2)
  have hzpos : 0 < z := by norm_num [z]
  have hzpowpos : 0 < z ^ K := pow_pos hzpos _
  have hweighted := hC N hN2
  have hmark := highOmega_card_weight_le N (5 * t)
  have hcardWeighted :
      ((highOmegaUpTo N (5 * t)).card : ℝ) * z ^ K ≤
        32 * (N : ℝ) * Real.exp A := by
    exact hmark.trans (by simpa [z, K, A] using hweighted)
  have hraw :
      ((highOmegaUpTo N (5 * t)).card : ℝ) / (N : ℝ) ≤
        32 * Real.exp A / z ^ K := by
    apply (div_le_iff₀ hNpos).2
    calc
      ((highOmegaUpTo N (5 * t)).card : ℝ) ≤
          (32 * (N : ℝ) * Real.exp A) / z ^ K :=
        (le_div_iff₀ hzpowpos).2 hcardWeighted
      _ = (32 * Real.exp A / z ^ K) * (N : ℝ) := by ring
  have hlogz : (1 : ℝ) / 21 ≤ Real.log z := by
    dsimp [z]
    convert Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 21 / 20 by norm_num) using 1
    all_goals norm_num
  have hAexp :
      A - (K : ℝ) * Real.log z ≤
        -(149 : ℝ) / 21000 * t + (11 : ℝ) / 200 * C := by
    have hloglog := log_log_constructionAmbient_le t
    have ht : (0 : ℝ) ≤ t := by positivity
    dsimp [A, K, N]
    push_cast
    nlinarith
  calc
    ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
        constructionAmbient t ≤ 32 * Real.exp A / z ^ K := by
      simpa [N] using hraw
    _ = 32 * Real.exp (A - (K : ℝ) * Real.log z) := by
      rw [Real.exp_sub]
      have hzexp : Real.exp ((K : ℝ) * Real.log z) = z ^ K := by
        rw [Real.exp_nat_mul, Real.exp_log hzpos]
      rw [hzexp]
      ring
    _ ≤ 32 * Real.exp (-(149 : ℝ) / 21000 * t + (11 : ℝ) / 200 * C) := by
      gcongr
    _ = (32 * Real.exp ((11 : ℝ) / 200 * C)) *
        (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
      rw [Real.exp_add]
      have hexp : Real.exp (-(149 : ℝ) / 21000 * (t : ℝ)) =
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
        rw [mul_comm, Real.exp_nat_mul]
      rw [hexp]
      ring

lemma self_le_two_pow (t : ℕ) : t ≤ 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
      omega

lemma lowPart_density_le_geometric (t : ℕ) :
    ((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
        constructionAmbient t ≤ ((1 : ℝ) / 2) ^ t := by
  let R := constructionExponent t
  let D := 2 ^ t
  have hDR : D ≤ R := by
    dsimp [D, R, constructionExponent]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hR : R - D + D = R := Nat.sub_add_cancel hDR
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have heq : ((2 : ℝ) ^ (R - D)) / (2 : ℝ) ^ R = ((1 : ℝ) / 2) ^ D := by
    have hden : (2 : ℝ) ^ R = (2 : ℝ) ^ (R - D) * (2 : ℝ) ^ D := by
      rw [← pow_add, hR]
    rw [hden, div_pow]
    field_simp
    simp
  calc
    ((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
        constructionAmbient t = ((1 : ℝ) / 2) ^ D := by
      simpa [constructionAmbient, R, D] using heq
    _ ≤ ((1 : ℝ) / 2) ^ t :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (self_le_two_pow t)

lemma uncovered_density_le_geometric (C : ℝ)
    (hC : ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) (t : ℕ) :
    ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
        constructionAmbient t ≤
      ((1 : ℝ) / 2) ^ t +
        (32 * Real.exp ((11 : ℝ) / 200 * C)) *
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
  have hcard := uncovered_card_le_low_add_high t
  have hcast :
      ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) ≤
        (2 ^ (constructionExponent t - 2 ^ t) : ℕ) +
          ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) := by
    exact_mod_cast hcard
  have hNpos : (0 : ℝ) < constructionAmbient t := by
    exact_mod_cast (show 0 < constructionAmbient t by
      simp [constructionAmbient])
  calc
    ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
        constructionAmbient t ≤
      (((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) +
        (highOmegaUpTo (constructionAmbient t) (5 * t)).card) /
          constructionAmbient t := (div_le_div_iff_of_pos_right hNpos).2 hcast
    _ = (((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
          constructionAmbient t) +
        (((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
          constructionAmbient t) := by rw [add_div]
    _ ≤ ((1 : ℝ) / 2) ^ t +
        (32 * Real.exp ((11 : ℝ) / 200 * C)) *
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
      gcongr
      · exact lowPart_density_le_geometric t
      · exact highOmega_density_le_geometric C hC t

lemma one_not_mem_constructionFamily (t : ℕ) : 1 ∉ constructionFamily t := by
  intro h
  have h1 : 1 ∈ thresholdSet (constructionAmbient t) := (Finset.mem_filter.1 h).1
  have h2 := (Finset.mem_filter.1 h1).2
  have hpos : 0 < constructionAmbient t := by simp [constructionAmbient]
  simp at h2
  omega

lemma ambient_tendsto : Filter.Tendsto constructionAmbient Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_id
  have h1 := Nat.lt_two_pow_self (n := 6 * t)
  have h2 := Nat.lt_two_pow_self (n := 2 ^ (6 * t))
  simp only [id, constructionAmbient, constructionExponent]
  omega

lemma log_ambient (t : ℕ) :
    Real.log (constructionAmbient t : ℝ) = (2 : ℝ) ^ (6 * t) * Real.log 2 := by
  simp [constructionAmbient, constructionExponent, Real.log_pow]

end OMA.E542

open OMA.E542 in
theorem OMA.solution : type_of% @Erdos542.erdos_542.variants.log_power := by
  obtain ⟨C, hC⟩ := omega_weighted_sum_bound
  set B : ℝ := 32 * Real.exp ((11 : ℝ) / 200 * C) with hB
  have hBpos : 0 < B := by positivity
  refine ⟨1 / 1000, by norm_num, ?_⟩
  apply ambient_tendsto.frequently
  apply Filter.Eventually.frequently
  have hev : ∀ᶠ t : ℕ in Filter.atTop, (21000 * (B + 1) / 23 : ℝ) ≤ t := by
    filter_upwards [Filter.eventually_ge_atTop ⌈(21000 * (B + 1) / 23 : ℝ)⌉₊] with t ht
    exact (Nat.le_ceil _).trans (by exact_mod_cast ht)
  filter_upwards [hev] with t ht
  refine ⟨constructionFamily t, ?_, one_not_mem_constructionFamily t, ?_⟩
  · obtain ⟨h1, h2⟩ := constructionFamily_admissible t
    refine ⟨fun a ha => ?_, fun a ha b hb hab => h2 a ha b hb hab⟩
    have := h1 a ha
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact this
  · have hdens := uncovered_density_le_geometric C hC t
    set N : ℕ := constructionAmbient t with hN
    have hNpos : (0 : ℝ) < N := by
      have : 0 < constructionAmbient t := by simp [constructionAmbient]
      exact_mod_cast this
    have hcardeq : (Erdos542.uncovered N (constructionFamily t)).card =
        (uncovered N (constructionFamily t)).card := rfl
    rw [hcardeq]
    set U : ℝ := ((uncovered N (constructionFamily t)).card : ℝ)
    set q : ℝ := Real.exp (-(149 : ℝ) / 21000) with hq
    have hq0 : 0 < q := Real.exp_pos _
    have hhalf : (1 : ℝ) / 2 ≤ q := by
      rw [hq]
      have := Real.add_one_le_exp (-(149 : ℝ) / 21000)
      linarith
    have hpow : ((1 : ℝ) / 2) ^ t ≤ q ^ t := pow_le_pow_left₀ (by norm_num) hhalf t
    have hqt : q ^ t = Real.exp (-(149 : ℝ) / 21000 * t) := by
      rw [hq, ← Real.exp_nat_mul]; ring_nf
    have hU : U ≤ N * ((B + 1) * Real.exp (-(149 : ℝ) / 21000 * t)) := by
      have h1 : U / N ≤ (B + 1) * Real.exp (-(149 : ℝ) / 21000 * t) := by
        rw [← hqt]; nlinarith
      rwa [div_le_iff₀ hNpos, mul_comm] at h1
    -- the logarithm
    set R : ℝ := (2 : ℝ) ^ (6 * t) with hR
    have hRpos : 0 < R := by positivity
    have hL : Real.log (N : ℝ) = R * Real.log 2 := by rw [hN, log_ambient]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hLpos : 0 < Real.log (N : ℝ) := by rw [hL]; positivity
    have hLR : Real.log (N : ℝ) ≤ R := by
      rw [hL]; nlinarith
    have hRc : R ^ ((1 : ℝ) / 1000) = Real.exp (6 * t * Real.log 2 / 1000) := by
      rw [Real.rpow_def_of_pos hRpos, hR, Real.log_pow]
      push_cast
      ring_nf
    have hLc : Real.log (N : ℝ) ^ ((1 : ℝ) / 1000) ≤ Real.exp (6 * t / 1000) := by
      calc Real.log (N : ℝ) ^ ((1 : ℝ) / 1000) ≤ R ^ ((1 : ℝ) / 1000) :=
            Real.rpow_le_rpow hLpos.le hLR (by norm_num)
        _ = Real.exp (6 * t * Real.log 2 / 1000) := hRc
        _ ≤ Real.exp (6 * t / 1000) := by
            apply Real.exp_le_exp.2
            have ht0 : (0 : ℝ) ≤ t := by positivity
            nlinarith
    have hLcpos : 0 < Real.log (N : ℝ) ^ ((1 : ℝ) / 1000) := Real.rpow_pos_of_pos hLpos _
    have hkey : (B + 1) * Real.exp (-(149 : ℝ) / 21000 * t) * Real.exp (6 * t / 1000) ≤ 1 := by
      rw [mul_assoc, ← Real.exp_add]
      have hx : -(149 : ℝ) / 21000 * t + 6 * t / 1000 = -((23 : ℝ) / 21000 * t) := by ring
      rw [hx, Real.exp_neg]
      have he := Real.add_one_le_exp ((23 : ℝ) / 21000 * t)
      have hepos := Real.exp_pos ((23 : ℝ) / 21000 * t)
      rw [mul_inv_le_iff₀ hepos]
      have : B + 1 ≤ (23 : ℝ) / 21000 * t := by
        have := ht
        rw [div_le_iff₀ (by norm_num)] at this
        linarith
      linarith
    rw [le_div_iff₀ hLcpos]
    calc U * Real.log (N : ℝ) ^ ((1 : ℝ) / 1000)
        ≤ (N * ((B + 1) * Real.exp (-(149 : ℝ) / 21000 * t))) * Real.exp (6 * t / 1000) := by
          apply mul_le_mul hU hLc hLcpos.le
          positivity
      _ = N * ((B + 1) * Real.exp (-(149 : ℝ) / 21000 * t) * Real.exp (6 * t / 1000)) := by ring
      _ ≤ N * 1 := mul_le_mul_of_nonneg_left hkey hNpos.le
      _ = N := mul_one _
