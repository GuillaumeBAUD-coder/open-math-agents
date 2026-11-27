import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H2: hypothesis H2 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @smurali12
-- H2 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → p % 4 = 3 → q % 4 = 1 →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- All remaining pairs of primes p < q. -/

private lemma geom_sum_mul_sub_one (a n : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Finset.range n, a ^ i) * (a - 1) = a ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, ih, pow_succ, Nat.mul_sub_left_distrib, mul_one]
    have h1 : 1 ≤ a ^ n := Nat.one_le_pow n a ha
    have h2 : a ^ n ≤ a ^ n * a := Nat.le_mul_of_pos_right _ ha
    omega

private lemma div_sub_one_eq_geom_sum (a n : ℕ) (ha : 2 ≤ a) :
    (a ^ n - 1) / (a - 1) = ∑ i ∈ Finset.range n, a ^ i := by
  rw [← geom_sum_mul_sub_one a n (by omega), Nat.mul_div_cancel _ (by omega)]

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq _hpq hmod hp4 hq4 hdiv
  let N := (q ^ p - 1) / (q - 1)
  let M := (p ^ q - 1) / (p - 1)
  change N ∣ M at hdiv
  have hN_sum : N = ∑ i ∈ Finset.range p, q ^ i :=
    div_sub_one_eq_geom_sum q p hq.two_le
  have hN_mul : N * (q - 1) = q ^ p - 1 := by
    rw [hN_sum]
    exact geom_sum_mul_sub_one q p hq.pos
  have hM_mul : M * (p - 1) = p ^ q - 1 := by
    rw [show M = ∑ i ∈ Finset.range q, p ^ i from div_sub_one_eq_geom_sum p q hp.two_le]
    exact geom_sum_mul_sub_one p q hp.pos
  have hN_mod4 : N % 4 = 3 := by
    rw [hN_sum]
    have hpow : ∀ i : ℕ, q ^ i % 4 = 1 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, Nat.mul_mod, ih, hq4]
    have hsum_mod4 : ∀ n : ℕ, (∑ i ∈ Finset.range n, q ^ i) % 4 = n % 4 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow n]
        omega
    rw [hsum_mod4 p, hp4]
  have hN_ge3 : 3 ≤ N := by omega
  have hN_modp : N % p = 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hqp_pos : 1 ≤ q ^ p := Nat.one_le_pow p q hq.pos
    have hq_pos : 1 ≤ q := hq.pos
    have heq_nat : N * (q - 1) + 1 = q ^ p := by omega
    have heq_zmod : (N : ZMod p) * ((q : ZMod p) - 1) + 1 = (q : ZMod p) ^ p := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) heq_nat
      push_cast [hq_pos] at h
      exact h
    rw [ZMod.pow_card] at heq_zmod
    have hmul_zero : ((N : ZMod p) - 1) * ((q : ZMod p) - 1) = 0 := by
      linear_combination heq_zmod
    have hq_ne : (q : ZMod p) - 1 ≠ 0 := by
      intro hzero
      have hdvd : p ∣ q - 1 := (ZMod.natCast_eq_zero_iff (q - 1) p).mp (by
        rw [Nat.cast_sub hq_pos, Nat.cast_one]
        exact hzero)
      obtain ⟨k, hk⟩ := hdvd
      have hqmod : q % p = 1 := by
        rw [show q = p * k + 1 by omega, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hp.one_lt]
      exact hmod hqmod
    have hN1 : (N : ZMod p) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hmul_zero).resolve_right hq_ne)
    have hdvdN : p ∣ N - 1 := (ZMod.natCast_eq_zero_iff (N - 1) p).mp (by
      rw [Nat.cast_sub (by omega), Nat.cast_one, hN1, sub_self])
    obtain ⟨k, hk⟩ := hdvdN
    rw [show N = p * k + 1 by omega, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hp.one_lt]
  have hNdvd : N ∣ p ^ q - 1 := by
    rw [← hM_mul]
    exact dvd_mul_of_dvd_left hdiv (p - 1)
  have hp_pos : 1 ≤ p ^ q := Nat.one_le_pow q p hp.pos
  obtain ⟨k, hk⟩ := hNdvd
  have hmodZ : ((p : ℤ) ^ q) % (N : ℤ) = 1 := by
    have h1 : (p : ℤ) ^ q = 1 + (N : ℤ) * (k : ℤ) := by
      zify [hp_pos] at hk ⊢
      linarith
    rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by norm_num) (by omega)]
  have hJ_pow : jacobiSym (p : ℤ) N ^ q = 1 := by
    rw [← jacobiSym.pow_left, jacobiSym.mod_left, hmodZ, jacobiSym.one_left]
  have hJ_one : jacobiSym (p : ℤ) N = 1 := by
    have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
    rcases jacobiSym.trichotomy (p : ℤ) N with h0 | h1 | hn1
    · rw [h0, zero_pow hq.ne_zero] at hJ_pow
      norm_num at hJ_pow
    · exact h1
    · rw [hn1, hq_odd.neg_one_pow] at hJ_pow
      norm_num at hJ_pow
  have hJ_neg_one : jacobiSym (p : ℤ) N = -1 := by
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN_mod4]
    have hNpZ : (N : ℤ) % (p : ℤ) = 1 := by
      have hnat : N = 1 + p * (N / p) := by
        have := Nat.div_add_mod N p
        omega
      have h1 : (N : ℤ) = 1 + (p : ℤ) * ((N / p : ℕ) : ℤ) := by exact_mod_cast hnat
      rw [h1, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hp.one_lt)]
    rw [jacobiSym.mod_left, hNpZ, jacobiSym.one_left]
  rw [hJ_one] at hJ_neg_one
  norm_num at hJ_neg_one

