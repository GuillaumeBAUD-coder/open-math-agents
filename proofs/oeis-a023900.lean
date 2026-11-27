import OMAStatements.S_oeis_a023900
import Mathlib

/-!
# Serov's two formulas for OEIS A023900

With `a n = ∑ d ∣ n, d * μ d` and `term m i = 4 * min i (m - i) - m`:
1. `∑ i ∈ Icc 1 m, term m i = -1` for odd `m` (Gauss sum).
2. Moebius inversion: the sum over `i` coprime to `m` equals
   `∑ d ∣ m, μ d * ∑ j ∈ Icc 1 (m / d), term m (d * j)`, and
   `term (d * k) (d * j) = d * term k j`, so the coprime sum is `-a m`.
3. `a` is multiplicative and `a (2 ^ t) = -1` for `t ≥ 1`, so `a (2 ^ t * m) = -a m`.
-/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

namespace OMA.A023900Proof

open OMA.S_oeis_a023900

lemma sum_min (j : ℕ) :
    ∑ i ∈ Finset.range (2 * j + 2), min i (2 * j + 1 - i) = j * (j + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 2 * (j + 1) + 2 = (2 * j + 2) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ']
    have h : ∀ i ∈ Finset.range (2 * j + 2),
        min (i + 1) (2 * (j + 1) + 1 - (i + 1)) = min i (2 * j + 1 - i) + 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      omega
    have h1 : min 0 (2 * (j + 1) + 1 - 0) = 0 := by omega
    have h2 : min (2 * j + 2 + 1) (2 * (j + 1) + 1 - (2 * j + 2 + 1)) = 0 := by omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih, h1, h2]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

lemma total (m : ℕ) (hm : Odd m) : ∑ i ∈ Finset.Icc 1 m, term m i = -1 := by
  obtain ⟨j, rfl⟩ := hm
  have h := sum_min j
  have e : Finset.range (2 * j + 2) = insert 0 (Finset.Icc 1 (2 * j + 1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [e, Finset.sum_insert (by simp)] at h
  have h0 : min 0 (2 * j + 1 - 0) = 0 := by omega
  rw [h0, zero_add] at h
  have h' : (∑ i ∈ Finset.Icc 1 (2 * j + 1), ((min i (2 * j + 1 - i) : ℕ) : ℤ))
      = (j : ℤ) * (j + 1) := by
    exact_mod_cast h
  simp only [term]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h']
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

lemma term_mul (d k j : ℕ) : term (d * k) (d * j) = d * term k j := by
  have e : d * k - d * j = d * (k - j) := (Nat.mul_sub d k j).symm
  simp only [term]
  rw [e, Nat.mul_min_mul_left]
  push_cast
  ring

lemma coprime_sum (m : ℕ) (hm : 0 < m) (f : ℕ → ℤ) :
    ∑ i ∈ (Finset.Icc 1 m).filter (fun i => i.gcd m = 1), f i
      = ∑ d ∈ m.divisors, μ d * ∑ j ∈ Finset.Icc 1 (m / d), f (d * j) := by
  have key : ∀ g : ℕ, (∑ d ∈ g.divisors, μ d) = if g = 1 then 1 else 0 := by
    intro g
    rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  rw [Finset.sum_filter]
  have h1 : ∀ i ∈ Finset.Icc 1 m, (if i.gcd m = 1 then f i else 0)
      = ∑ d ∈ m.divisors, if d ∣ i then μ d * f i else 0 := by
    intro i _
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hs : m.divisors.filter (fun d => d ∣ i) = (i.gcd m).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      have : i.gcd m ≠ 0 := (Nat.gcd_pos_of_pos_right i hm).ne'
      have : m ≠ 0 := hm.ne'
      tauto
    rw [hs, key]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  symm
  refine Finset.sum_bij (fun j _ => d * j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hdpos hj.1, ?_⟩, dvd_mul_right d j⟩
    exact (Nat.mul_le_mul_left d hj.2).trans (Nat.mul_div_le m d)
  · intro j₁ _ j₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hdpos h
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    obtain ⟨⟨hi1, hi2⟩, c, rfl⟩ := hi
    refine ⟨c, ?_, rfl⟩
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_mul_pos_left hi1, ?_⟩
    rw [Nat.le_div_iff_mul_le hdpos, mul_comm]
    exact hi2
  · intro j _
    rfl

lemma a_two_pow (t : ℕ) (ht : 0 < t) : a (2 ^ t) = -1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simp only [a]
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ k ∈ Finset.range s,
      ((2 ^ (k + 1 + 1) : ℕ) : ℤ) * μ (2 ^ (k + 1 + 1)) = 0 := by
    intro k _
    rw [moebius_apply_prime_pow Nat.prime_two (by omega)]
    simp
  rw [Finset.sum_congr rfl h]
  have h2 : μ (2 ^ (0 + 1)) = -1 := by
    rw [moebius_apply_prime_pow Nat.prime_two (by omega)]
    simp
  rw [h2]
  simp

lemma a_two_pow_mul (t m : ℕ) (ht : 0 < t) (hm : Odd m) : a (2 ^ t * m) = - a m := by
  have hF : (pmul ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) μ
      * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
    ((isMultiplicative_id.natCast).pmul isMultiplicative_moebius).mul
      isMultiplicative_zeta.natCast
  have hFa : ∀ n, (pmul ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) μ
      * (ζ : ArithmeticFunction ℤ)) n = a n := by
    intro n
    rw [coe_mul_zeta_apply]
    simp [a, pmul_apply]
  have hcop : Nat.Coprime (2 ^ t) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  rw [← hFa, hF.map_mul_of_coprime hcop, hFa, hFa, a_two_pow t ht]
  ring

end OMA.A023900Proof

open OMA.S_oeis_a023900 OMA.A023900Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a023900.main := by
  intro n t m hn hm hnt
  have hmpos : 0 < m := hm.pos
  have hcop : ∑ i ∈ (Finset.Icc 1 m).filter (fun i => i.gcd m = 1), term m i = - a m := by
    rw [coprime_sum m hmpos, a, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hkodd : Odd k := by
      subst hk
      exact (Nat.odd_mul.mp hm).2
    have hdiv : m / d = k := by
      subst hk
      exact Nat.mul_div_cancel_left k hdpos
    have h : ∀ j ∈ Finset.Icc 1 k, term m (d * j) = d * term k j := fun j _ => by
      rw [hk, term_mul]
    rw [hdiv, Finset.sum_congr rfl h, ← Finset.mul_sum, total k hkodd]
    ring
  have hgt : (Finset.Icc 1 m).filter (fun i => 1 < i.gcd m)
      = (Finset.Icc 1 m).filter (fun i => ¬ i.gcd m = 1) := by
    refine Finset.filter_congr fun i _ => ?_
    have : 0 < i.gcd m := Nat.gcd_pos_of_pos_right i hmpos
    omega
  have h2 : ∑ i ∈ (Finset.Icc 1 m).filter (fun i => 1 < i.gcd m), term m i = -1 + a m := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) (fun i => i.gcd m = 1) (term m)
    rw [total m hm, hcop] at h
    rw [hgt]
    linarith
  rw [hcop, h2]
  rcases Nat.eq_zero_or_pos t with ht | ht
  · have hmn : m = n := by rw [hnt, ht]; simp
    rw [if_pos hmn, if_neg (by omega), hmn]
    constructor <;> ring
  · have h2t : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have hlt : m < n := by rw [hnt]; nlinarith
    rw [if_neg (by omega), if_pos hlt, hnt, a_two_pow_mul t m ht hm]
    constructor <;> ring
