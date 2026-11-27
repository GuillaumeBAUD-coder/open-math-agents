import OMAStatements.S_oeis_a002457
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Proof of Shunia's square-root formula for OEIS A002457

For every `n > 0`, let `B = 16 ^ n`, `x = 1 / (4 * B)`, and `F(u) = (1 + 4 * u) ^ (n + 1/2)`.
Then `4^n * B^n * F(x) = sqrt((B + 1) ^ (2*n + 1))`.

Writing `F(u) = (1 + 4*u) ^ (-1/2) * (1 + 4*u) ^ (n + 1)` shows by Leibniz's rule that every
Taylor coefficient `c_k = F^(k)(0) / k!` is an integer `cZ n k`, strictly positive for `k ≤ n + 1`,
with `c_n = (2*n + 1)! / (n!)^2 = a(n)` and `c_{n+1} = 2 * a(n) / (n + 1)`.

Therefore `S = 4^n * B^n * T_n(x) = ∑_{k=0}^n c_k * 4^{n-k} * B^{n-k}` is a natural number
satisfying `S ≡ c_n = a(n) (mod B)` and `a(n) = (2*n + 1) * C(2*n, n) < 4^n * 4^n = B`, so
`S % B = a(n)`.

By Lagrange's remainder theorem for `F` on `[0, x]`, there exists `ξ ∈ (0, x)` such that
`0 < 4^n * B^n * (F(x) - T_n(x)) ≤ 4^n * B^n * c_{n+1} * x^{n+1} = a(n) / (2*(n+1)*B) < 1`.
Hence `S^2 < (B + 1)^{2*n + 1} < (S + 1)^2`, giving `Nat.sqrt ((B + 1) ^ (2*n + 1)) = S` and
`Nat.sqrt ((B + 1) ^ (2*n + 1)) % B = a(n)`.
-/

namespace OMA.P_oeis_a002457

private def a (n : ℕ) : ℕ :=
  Nat.factorial (2 * n + 1) / Nat.factorial n ^ 2

private lemma iteratedDeriv_one_add_four_mul_rpow (k : ℕ) (α : ℝ) :
    ∀ t : ℝ, 0 < 1 + 4 * t →
      iteratedDeriv k (fun u : ℝ => (1 + 4 * u) ^ α) t =
        4 ^ k * (∏ j ∈ Finset.range k, (α - j)) * (1 + 4 * t) ^ (α - k) := by
  induction k generalizing α with
  | zero =>
    intro t _
    simp
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ']
    have hderiv_fun : deriv (fun u : ℝ => (1 + 4 * u) ^ α) =ᶠ[nhds t]
        fun u : ℝ => (4 * α) * (1 + 4 * u) ^ (α - 1) := by
      have hopen : IsOpen {u : ℝ | 0 < 1 + 4 * u} :=
        isOpen_lt continuous_const (by fun_prop)
      filter_upwards [hopen.mem_nhds ht] with u hu
      have hlin : HasDerivAt (fun v : ℝ => 1 + 4 * v) 4 u := by
        simpa using ((hasDerivAt_id u).const_mul 4).const_add 1
      have hrp : HasDerivAt (fun v : ℝ => (1 + 4 * v) ^ α)
          (α * (1 + 4 * u) ^ (α - 1) * 4) u := by
        have hbase := Real.hasDerivAt_rpow_const (x := 1 + 4 * u) (p := α) (Or.inl hu.ne')
        simpa [Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hbase.comp u hlin
      rw [hrp.deriv]
      ring
    rw [hderiv_fun.iteratedDeriv_eq k]
    rw [iteratedDeriv_const_mul_field (4 * α) (fun u : ℝ => (1 + 4 * u) ^ (α - 1))]
    rw [ih (α - 1) t ht, Finset.prod_range_succ']
    have hpow : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
    have hexp : α - 1 - (k : ℝ) = α - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hpow, hexp]
    simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
    have hprod : (∏ x ∈ Finset.range k, (α - 1 - (x : ℝ))) =
        ∏ x ∈ Finset.range k, (α - ((x : ℝ) + 1)) := by
      refine Finset.prod_congr rfl fun j _ => by ring
    rw [hprod]
    ring

private lemma choose_two_mul_succ (j : ℕ) :
    (j + 1) * Nat.choose (2 * (j + 1)) (j + 1) =
      2 * (2 * j + 1) * Nat.choose (2 * j) j := by
  have hc1 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ 2 * j)
  have hc2 := Nat.choose_mul_factorial_mul_factorial (by omega : j + 1 ≤ 2 * (j + 1))
  rw [show 2 * j - j = j by omega] at hc1
  rw [show 2 * (j + 1) - (j + 1) = j + 1 by omega, Nat.factorial_succ] at hc2
  have hc1' : Nat.choose (2 * j) j * j.factorial ^ 2 = Nat.factorial (2 * j) := by
    calc Nat.choose (2 * j) j * j.factorial ^ 2
        = Nat.choose (2 * j) j * j.factorial * j.factorial := by ring
      _ = Nat.factorial (2 * j) := hc1
  have hc2' : Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial) ^ 2 =
      Nat.factorial (2 * (j + 1)) := by
    calc Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial) ^ 2
        = Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial) * ((j + 1) * j.factorial) := by ring
      _ = Nat.factorial (2 * (j + 1)) := hc2
  have hjpos : 0 < (j + 1) * j.factorial ^ 2 :=
    Nat.mul_pos (Nat.succ_pos j) (pow_pos (Nat.factorial_pos j) 2)
  have h1 : (j + 1) * Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial ^ 2) =
      Nat.factorial (2 * (j + 1)) := by
    calc (j + 1) * Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial ^ 2)
        = Nat.choose (2 * (j + 1)) (j + 1) * ((j + 1) * j.factorial) ^ 2 := by ring
      _ = Nat.factorial (2 * (j + 1)) := hc2'
  have h2 : 2 * (2 * j + 1) * Nat.choose (2 * j) j * ((j + 1) * j.factorial ^ 2) =
      Nat.factorial (2 * (j + 1)) := by
    have h2j : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [h2j, Nat.factorial_succ, Nat.factorial_succ, ← hc1']
    ring
  exact Nat.mul_right_cancel hjpos (h1.trans h2.symm)

private lemma iteratedDeriv_neg_half_zero (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => (1 + 4 * u) ^ (-(1 / 2 : ℝ))) 0 =
      (-1 : ℝ) ^ j * (Nat.choose (2 * j) j : ℝ) * (j.factorial : ℝ) := by
  rw [iteratedDeriv_one_add_four_mul_rpow j (-(1 / 2 : ℝ)) 0 (by norm_num)]
  simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have hmul' : 4 ^ j * 4 * ((∏ x ∈ Finset.range j, (-(1 / 2 : ℝ) - (x : ℝ))) *
        (-(1 / 2 : ℝ) - (j : ℝ))) =
        (4 ^ j * ∏ x ∈ Finset.range j, (-(1 / 2 : ℝ) - (x : ℝ))) * (4 * (-(1 / 2 : ℝ) - (j : ℝ))) := by
      ring
    rw [hmul', ih]
    have hstepR : ((j + 1 : ℕ) : ℝ) * (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) =
        2 * (2 * (j : ℝ) + 1) * (Nat.choose (2 * j) j : ℝ) := by
      exact_mod_cast choose_two_mul_succ j
    calc
      (-1 : ℝ) ^ j * (Nat.choose (2 * j) j : ℝ) * (j.factorial : ℝ) * (4 * (-(1 / 2 : ℝ) - (j : ℝ)))
        = (-1 : ℝ) ^ j * (-1) * (2 * (2 * (j : ℝ) + 1) * (Nat.choose (2 * j) j : ℝ)) * (j.factorial : ℝ) := by ring
      _ = (-1 : ℝ) ^ j * (-1) * (((j + 1 : ℕ) : ℝ) * (Nat.choose (2 * (j + 1)) (j + 1) : ℝ)) * (j.factorial : ℝ) := by
          rw [← hstepR]
      _ = (-1 : ℝ) ^ (j + 1) * (Nat.choose (2 * (j + 1)) (j + 1) : ℝ) * ((j + 1).factorial : ℝ) := by
          rw [pow_succ, Nat.factorial_succ]
          push_cast
          ring

private lemma iteratedDeriv_nat_pow_zero (n m : ℕ) :
    iteratedDeriv m (fun u : ℝ => (1 + 4 * u) ^ (n + 1)) 0 =
      4 ^ m * (Nat.choose (n + 1) m : ℝ) * (m.factorial : ℝ) := by
  have heq : (fun u : ℝ => (1 + 4 * u) ^ (n + 1)) =
      fun u : ℝ => (1 + 4 * u) ^ ((n + 1 : ℕ) : ℝ) := by
    ext u
    rw [Real.rpow_natCast]
  rw [heq, iteratedDeriv_one_add_four_mul_rpow m ((n + 1 : ℕ) : ℝ) 0 (by norm_num)]
  simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
  have hdesc : (∏ j ∈ Finset.range m, (((n + 1 : ℕ) : ℝ) - (j : ℝ))) =
      ((Nat.descFactorial (n + 1) m : ℕ) : ℝ) := by
    by_cases hm : m ≤ n + 1
    · induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, ih (by omega), Nat.descFactorial_succ]
        rw [Nat.cast_mul, Nat.cast_sub (by omega : m ≤ n + 1)]
        ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero]
      exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : n + 1 < m)) (by simp)
  rw [hdesc, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

private def cZ (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ j * (Nat.choose (2 * j) j : ℤ) *
      (Nat.choose (n + 1) (k - j) : ℤ) * 4 ^ (k - j)

private lemma iteratedDeriv_f_zero (n k : ℕ) :
    iteratedDeriv k (fun u : ℝ => (1 + 4 * u) ^ ((n : ℝ) + 1 / 2)) 0 / (k.factorial : ℝ) =
      (cZ n k : ℝ) := by
  let g : ℝ → ℝ := fun u => (1 + 4 * u) ^ (-(1 / 2 : ℝ))
  let h : ℝ → ℝ := fun u => (1 + 4 * u) ^ (n + 1)
  have heq : (fun u : ℝ => (1 + 4 * u) ^ ((n : ℝ) + 1 / 2)) =ᶠ[nhds 0] g * h := by
    have hopen : IsOpen {u : ℝ | 0 < 1 + 4 * u} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds (by norm_num : (0 : ℝ) < 1 + 4 * 0)] with u hu
    simp only [Pi.mul_apply, g, h]
    rw [← Real.rpow_natCast (1 + 4 * u) (n + 1), ← Real.rpow_add hu]
    congr 1
    push_cast
    ring
  rw [heq.iteratedDeriv_eq k]
  have hg : ContDiffAt ℝ k g 0 := by
    have hlin : ContDiffAt ℝ k (fun u : ℝ => 1 + 4 * u) 0 := by fun_prop
    exact hlin.rpow_const_of_ne (by norm_num)
  have hh : ContDiffAt ℝ k h 0 := by fun_prop
  rw [iteratedDeriv_mul hg hh]
  simp only [g, h]
  have hsum : (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        iteratedDeriv i (fun u : ℝ => (1 + 4 * u) ^ (-(1 / 2 : ℝ))) 0 *
        iteratedDeriv (k - i) (fun u : ℝ => (1 + 4 * u) ^ (n + 1)) 0) / (k.factorial : ℝ) =
      ∑ i ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ i * (Nat.choose (2 * i) i : ℝ) *
          (Nat.choose (n + 1) (k - i) : ℝ) * 4 ^ (k - i) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [iteratedDeriv_neg_half_zero i, iteratedDeriv_nat_pow_zero n (k - i)]
    have hc : (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ) = (k.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hkpos : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp [hkpos]
    rw [show (k.choose i : ℝ) * (Nat.choose (2 * i) i : ℝ) * (i.factorial : ℝ) *
        (Nat.choose (n + 1) (k - i) : ℝ) * ((k - i).factorial : ℝ) =
        ((k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)) *
        (Nat.choose (2 * i) i : ℝ) * (Nat.choose (n + 1) (k - i) : ℝ) by ring, hc]
    ring
  rw [hsum]
  simp only [cZ]
  push_cast
  rfl

private lemma prod_half_eq_a (n : ℕ) :
    (a n : ℝ) =
      4 ^ n * (∏ j ∈ Finset.range n, ((n : ℝ) + 1 / 2 - (j : ℝ))) / (n.factorial : ℝ) := by
  have ha_dvd : ∀ m : ℕ, (m.factorial ^ 2) ∣ Nat.factorial (2 * m + 1) := by
    intro m
    have hc := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    have h2m : 2 * m - m = m := by omega
    rw [h2m] at hc
    have hfact : Nat.factorial (2 * m + 1) = (2 * m + 1) * Nat.factorial (2 * m) :=
      Nat.factorial_succ (2 * m)
    rw [hfact, ← hc]
    refine ⟨(2 * m + 1) * Nat.choose (2 * m) m, ?_⟩
    ring
  have ha_mul : ∀ m : ℕ, (a m : ℝ) * (m.factorial : ℝ) ^ 2 = (Nat.factorial (2 * m + 1) : ℝ) := by
    intro m
    exact_mod_cast Nat.div_mul_cancel (ha_dvd m)
  have hprod_mul : ∀ m : ℕ,
      4 ^ m * (∏ j ∈ Finset.range m, ((m : ℝ) + 1 / 2 - (j : ℝ))) * (m.factorial : ℝ) =
        (Nat.factorial (2 * m + 1) : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hshift : (∏ j ∈ Finset.range (m + 1), (((m + 1 : ℕ) : ℝ) + 1 / 2 - (j : ℝ))) =
          ((m : ℝ) + 3 / 2) * (∏ j ∈ Finset.range m, ((m : ℝ) + 1 / 2 - (j : ℝ))) := by
        rw [Finset.prod_range_succ', mul_comm]
        have hz : ((m + 1 : ℕ) : ℝ) + 1 / 2 - ((0 : ℕ) : ℝ) = (m : ℝ) + 3 / 2 := by push_cast; ring
        rw [hz]
        congr 1
        refine Finset.prod_congr rfl fun j _ => by push_cast; ring
      rw [hshift, pow_succ, Nat.factorial_succ]
      have hf : Nat.factorial (2 * (m + 1) + 1) =
          (2 * m + 3) * (2 * m + 2) * Nat.factorial (2 * m + 1) := by
        have h1 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
        rw [h1, Nat.factorial_succ, Nat.factorial_succ]
        ring
      rw [hf]
      push_cast
      calc
        (4 ^ m * 4) * (((m : ℝ) + 3 / 2) * (∏ j ∈ Finset.range m, ((m : ℝ) + 1 / 2 - (j : ℝ)))) *
            (((m : ℝ) + 1) * (m.factorial : ℝ))
          = 2 * (2 * (m : ℝ) + 3) * ((m : ℝ) + 1) *
              (4 ^ m * (∏ j ∈ Finset.range m, ((m : ℝ) + 1 / 2 - (j : ℝ))) * (m.factorial : ℝ)) := by
            ring
        _ = 2 * (2 * (m : ℝ) + 3) * ((m : ℝ) + 1) * (Nat.factorial (2 * m + 1) : ℝ) := by
            rw [ih]
        _ = (2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2) * (Nat.factorial (2 * m + 1) : ℝ) := by
            ring
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h1 := ha_mul n
  have h2 := hprod_mul n
  rw [eq_div_iff hfn]
  exact mul_right_cancel₀ hfn (by linarith [h1, h2])

private lemma cZ_nonneg_of_le (n k : ℕ) (hk : k ≤ n + 1) : 0 ≤ cZ n k := by
  have hpos : (0 : ℝ) < (cZ n k : ℝ) := by
    rw [← iteratedDeriv_f_zero n k, iteratedDeriv_one_add_four_mul_rpow k _ 0 (by norm_num)]
    simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
    apply div_pos
    · apply mul_pos (pow_pos (by norm_num) k)
      apply Finset.prod_pos
      intro j hj
      rw [Finset.mem_range] at hj
      have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : j ≤ n)
      linarith
    · exact Nat.cast_pos.mpr (Nat.factorial_pos k)
  exact_mod_cast hpos.le

private lemma toNat_cast_of_nonneg {z : ℤ} (hz : 0 ≤ z) : (z.toNat : ℝ) = (z : ℝ) := by
  have : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  exact_mod_cast this

private lemma cZ_n_eq_a (n : ℕ) : (cZ n n).toNat = a n := by
  have hR : ((cZ n n).toNat : ℝ) = (a n : ℝ) := by
    rw [toNat_cast_of_nonneg (cZ_nonneg_of_le n n (by omega))]
    rw [← iteratedDeriv_f_zero n n, iteratedDeriv_one_add_four_mul_rpow n _ 0 (by norm_num)]
    simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
    exact (prod_half_eq_a n).symm
  exact_mod_cast hR

private lemma cZ_succ_eq (n : ℕ) :
    (cZ n (n + 1) : ℝ) = 2 * (a n : ℝ) / ((n : ℝ) + 1) := by
  rw [← iteratedDeriv_f_zero n (n + 1),
    iteratedDeriv_one_add_four_mul_rpow (n + 1) _ 0 (by norm_num)]
  simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
  rw [Finset.prod_range_succ, pow_succ, Nat.factorial_succ, prod_half_eq_a n]
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hfn, hn1]
  ring

private lemma a_eq_mul_choose (n : ℕ) : a n = (2 * n + 1) * Nat.choose (2 * n) n := by
  unfold a
  have hc := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have h2n : 2 * n - n = n := by omega
  rw [h2n] at hc
  have hfact : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) :=
    Nat.factorial_succ (2 * n)
  rw [hfact, ← hc, show Nat.choose (2 * n) n * n.factorial * n.factorial = n.factorial ^ 2 * Nat.choose (2 * n) n by ring]
  rw [show (2 * n + 1) * (n.factorial ^ 2 * Nat.choose (2 * n) n) =
    (n.factorial ^ 2) * ((2 * n + 1) * Nat.choose (2 * n) n) by ring]
  exact Nat.mul_div_cancel_left _ (pow_pos (Nat.factorial_pos n) 2)

private lemma two_mul_add_one_lt_four_pow (n : ℕ) (hn : 0 < n) : 2 * n + 1 < 4 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · norm_num
    · have ih' := ih (Nat.succ_pos m)
      rw [pow_succ]
      omega

private lemma a_lt_sixteen_pow (n : ℕ) (hn : 0 < n) : a n < 16 ^ n := by
  rw [a_eq_mul_choose]
  have hch : Nat.choose (2 * n) n ≤ 2 ^ (2 * n) := by
    have hs := Nat.sum_range_choose (2 * n)
    have hmem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem).trans hs.le
  have h4 : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  have hlt := two_mul_add_one_lt_four_pow n hn
  have h1 : (2 * n + 1) * Nat.choose (2 * n) n ≤ (2 * n + 1) * 4 ^ n :=
    Nat.mul_le_mul_left _ (h4 ▸ hch)
  have h2 : (2 * n + 1) * 4 ^ n < 4 ^ n * 4 ^ n :=
    Nat.mul_lt_mul_of_pos_right hlt (pow_pos (by decide) n)
  have h16 : 4 ^ n * 4 ^ n = 16 ^ n := by
    rw [← mul_pow]
    norm_num
  omega

theorem main_aux :
    ∀ n : ℕ, 0 < n → a n = Nat.sqrt ((16 ^ n + 1) ^ (2 * n + 1)) % 16 ^ n := by
  intro n hn
  let B : ℕ := 16 ^ n
  let S : ℕ := ∑ k ∈ Finset.range (n + 1), (cZ n k).toNat * 4 ^ (n - k) * B ^ (n - k)
  have hS_mod : S % B = a n := by
    dsimp [S]
    rw [Finset.sum_range_succ, Nat.sub_self]
    simp only [pow_zero, mul_one, cZ_n_eq_a n]
    have hdvd : B ∣ ∑ k ∈ Finset.range n, (cZ n k).toNat * 4 ^ (n - k) * B ^ (n - k) := by
      apply Finset.dvd_sum
      intro k hk
      rw [Finset.mem_range] at hk
      exact dvd_mul_of_dvd_right (dvd_pow_self B (by omega : n - k ≠ 0)) _
    rcases hdvd with ⟨q, hq⟩
    rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt (a_lt_sixteen_pow n hn)]
  let x : ℝ := 1 / (4 * (B : ℝ))
  have hx_pos : 0 < x := by
    dsimp [x, B]
    positivity
  let F : ℝ → ℝ := fun u => (1 + 4 * u) ^ ((n : ℝ) + 1 / 2)
  have hF_smooth : ContDiffOn ℝ (n + 1) F (Set.uIcc 0 x) := by
    have hlin : ContDiffOn ℝ (n + 1) (fun u : ℝ => 1 + 4 * u) (Set.uIcc 0 x) := by fun_prop
    refine hlin.rpow_const_of_ne fun u hu => ?_
    rw [Set.uIcc_of_le hx_pos.le, Set.mem_Icc] at hu
    linarith [hu.1]
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hx_pos.ne hF_smooth
  rw [Set.uIoo_of_le hx_pos.le] at hξ
  have htaylor : (S : ℝ) = (4 : ℝ) ^ n * (B : ℝ) ^ n * taylorWithinEval F n (Set.uIcc 0 x) 0 x := by
    rw [taylor_within_apply]
    dsimp [S]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hk_le : k ≤ n + 1 := by omega
    have hcz : ((cZ n k).toNat : ℝ) = (cZ n k : ℝ) :=
      toNat_cast_of_nonneg (cZ_nonneg_of_le n k hk_le)
    have hder : iteratedDerivWithin k F (Set.uIcc 0 x) 0 = iteratedDeriv k F 0 := by
      refine iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx_pos.ne) ?_ ?_
      · exact ((by fun_prop : ContDiffAt ℝ k (fun u : ℝ => 1 + 4 * u) 0).rpow_const_of_ne (by norm_num))
      · exact Set.left_mem_uIcc
    rw [hder, sub_zero, hcz, ← iteratedDeriv_f_zero n k]
    have h4ne : (4 : ℝ) ≠ 0 := by norm_num
    have hBne : (B : ℝ) ≠ 0 := by dsimp [B]; positivity
    have h4 : (4 : ℝ) ^ (n - k) = (4 : ℝ) ^ n * ((4 : ℝ) ^ k)⁻¹ := by
      rw [← pow_sub₀ _ h4ne hk]
    have hB : (B : ℝ) ^ (n - k) = (B : ℝ) ^ n * ((B : ℝ) ^ k)⁻¹ := by
      rw [← pow_sub₀ _ hBne hk]
    rw [h4, hB]
    dsimp [x, F]
    rw [one_div_pow, mul_pow,
      show (1 : ℝ) / ((4 : ℝ) ^ k * (B : ℝ) ^ k) = ((4 : ℝ) ^ k)⁻¹ * ((B : ℝ) ^ k)⁻¹ by
        rw [one_div, mul_inv]]
    ring
  have hFx_sq : ((4 : ℝ) ^ n * (B : ℝ) ^ n * F x) ^ 2 = (((B + 1) ^ (2 * n + 1) : ℕ) : ℝ) := by
    have h14x : 1 + 4 * x = ((B + 1 : ℕ) : ℝ) / (B : ℝ) := by
      dsimp [x, B]
      have hBpos : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by positivity
      field_simp [hBpos.ne']
      push_cast
      ring
    have h14x_pos : 0 < 1 + 4 * x := by
      rw [h14x]
      dsimp [B]
      positivity
    dsimp [F]
    rw [mul_pow, ← Real.rpow_natCast ((1 + 4 * x) ^ ((n : ℝ) + 1 / 2)) 2,
      ← Real.rpow_mul h14x_pos.le]
    have hexp : ((n : ℝ) + 1 / 2) * ((2 : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast, h14x, div_pow, mul_pow]
    have hBne : (B : ℝ) ≠ 0 := by dsimp [B]; positivity
    have hB2 : ((B : ℝ) ^ n) ^ 2 = (B : ℝ) ^ (2 * n) := by ring
    have h16 : ((4 : ℝ) ^ n) ^ 2 = (B : ℝ) := by
      dsimp [B]
      rw [← pow_mul]
      have h16_nat : (4 : ℝ) ^ (n * 2) = ((16 ^ n : ℕ) : ℝ) := by
        push_cast
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
        ring_nf
      exact h16_nat
    rw [hB2, h16]
    field_simp [hBne]
    push_cast
    ring
  have hrem_pos : 0 < F x - taylorWithinEval F n (Set.uIcc 0 x) 0 x := by
    rw [hrem]
    have hξ_pos : 0 < 1 + 4 * ξ := by linarith [hξ.1]
    rw [iteratedDeriv_one_add_four_mul_rpow (n + 1) _ ξ hξ_pos]
    have hprod_pos : 0 < ∏ j ∈ Finset.range (n + 1), (((n : ℝ) + 1 / 2) - (j : ℝ)) := by
      apply Finset.prod_pos
      intro j hj
      rw [Finset.mem_range] at hj
      have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : j ≤ n)
      linarith
    have hrp_pos : 0 < (1 + 4 * ξ) ^ (((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos hξ_pos _
    have hx_pow_pos : 0 < (x - 0) ^ (n + 1) := by
      rw [sub_zero]
      exact pow_pos hx_pos _
    positivity
  have hrem_ub : F x - taylorWithinEval F n (Set.uIcc 0 x) 0 x ≤ (cZ n (n + 1) : ℝ) * x ^ (n + 1) := by
    rw [hrem]
    have hξ_pos : 0 < 1 + 4 * ξ := by linarith [hξ.1]
    have hξ_ge1 : 1 ≤ 1 + 4 * ξ := by linarith [hξ.1]
    rw [iteratedDeriv_one_add_four_mul_rpow (n + 1) _ ξ hξ_pos]
    have hexp_neg : ((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ) = -(1 / 2 : ℝ) := by push_cast; ring
    rw [hexp_neg]
    have hrp_le1 : (1 + 4 * ξ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hξ_ge1 (by norm_num)
    have hcz_eq : (4 : ℝ) ^ (n + 1) * (∏ j ∈ Finset.range (n + 1), (((n : ℝ) + 1 / 2) - (j : ℝ))) /
        ((n + 1).factorial : ℝ) = (cZ n (n + 1) : ℝ) := by
      rw [← iteratedDeriv_f_zero n (n + 1),
        iteratedDeriv_one_add_four_mul_rpow (n + 1) _ 0 (by norm_num)]
      simp only [mul_zero, add_zero, Real.one_rpow, mul_one]
    have hcz_nonneg : 0 ≤ (cZ n (n + 1) : ℝ) := by
      exact_mod_cast cZ_nonneg_of_le n (n + 1) le_rfl
    have hx_pow_nonneg : 0 ≤ (x - 0) ^ (n + 1) := by
      rw [sub_zero]
      exact pow_nonneg hx_pos.le _
    calc
      4 ^ (n + 1) * (∏ j ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (j : ℝ))) *
          (1 + 4 * ξ) ^ (-(1 / 2 : ℝ)) * (x - 0) ^ (n + 1) / ((n + 1).factorial : ℝ)
        = (cZ n (n + 1) : ℝ) * (x - 0) ^ (n + 1) * (1 + 4 * ξ) ^ (-(1 / 2 : ℝ)) := by
          rw [← hcz_eq]
          ring
      _ ≤ (cZ n (n + 1) : ℝ) * (x - 0) ^ (n + 1) * 1 := by
          apply mul_le_mul_of_nonneg_left hrp_le1
          exact mul_nonneg hcz_nonneg hx_pow_nonneg
      _ = (cZ n (n + 1) : ℝ) * x ^ (n + 1) := by rw [sub_zero, mul_one]
  have hscale_pos : (0 : ℝ) < (4 : ℝ) ^ n * (B : ℝ) ^ n := by dsimp [B]; positivity
  have h_lower_R : (S : ℝ) < (4 : ℝ) ^ n * (B : ℝ) ^ n * F x := by
    rw [htaylor]
    nlinarith [mul_pos hscale_pos hrem_pos]
  have h_upper_R : (4 : ℝ) ^ n * (B : ℝ) ^ n * F x < (S : ℝ) + 1 := by
    have h1 : (4 : ℝ) ^ n * (B : ℝ) ^ n * F x - (S : ℝ) ≤
        (4 : ℝ) ^ n * (B : ℝ) ^ n * ((cZ n (n + 1) : ℝ) * x ^ (n + 1)) := by
      rw [htaylor, ← mul_sub]
      exact mul_le_mul_of_nonneg_left hrem_ub hscale_pos.le
    have h2 : (4 : ℝ) ^ n * (B : ℝ) ^ n * ((cZ n (n + 1) : ℝ) * x ^ (n + 1)) =
        (a n : ℝ) / (2 * ((n : ℝ) + 1) * (B : ℝ)) := by
      rw [cZ_succ_eq]
      dsimp [x]
      have h4ne : (4 : ℝ) ≠ 0 := by norm_num
      have hBne : (B : ℝ) ≠ 0 := by dsimp [B]; positivity
      have hn1ne : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [one_div, mul_inv, mul_pow, inv_pow, inv_pow, pow_succ, pow_succ]
      field_simp [h4ne, hBne, hn1ne]
      ring
    have ha_lt_B : (a n : ℝ) < (B : ℝ) := by exact_mod_cast a_lt_sixteen_pow n hn
    have h3 : (a n : ℝ) / (2 * ((n : ℝ) + 1) * (B : ℝ)) < 1 := by
      have hden : (0 : ℝ) < 2 * ((n : ℝ) + 1) * (B : ℝ) := by dsimp [B]; positivity
      rw [div_lt_one hden]
      have hBpos : (0 : ℝ) < (B : ℝ) := by dsimp [B]; positivity
      nlinarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
    linarith
  have h_lower_sq : S ^ 2 ≤ (B + 1) ^ (2 * n + 1) := by
    have hsqR : ((S ^ 2 : ℕ) : ℝ) < (((B + 1) ^ (2 * n + 1) : ℕ) : ℝ) := by
      rw [← hFx_sq]
      push_cast
      exact pow_lt_pow_left₀ h_lower_R (Nat.cast_nonneg _) (by decide)
    exact (Nat.cast_lt.mp hsqR).le
  have h_upper_sq : (B + 1) ^ (2 * n + 1) < (S + 1) ^ 2 := by
    have hsqR : (((B + 1) ^ (2 * n + 1) : ℕ) : ℝ) < (((S + 1) ^ 2 : ℕ) : ℝ) := by
      rw [← hFx_sq]
      push_cast
      have hpos : 0 ≤ (4 : ℝ) ^ n * (B : ℝ) ^ n * F x := by
        linarith [(Nat.cast_nonneg S : (0 : ℝ) ≤ (S : ℝ))]
      exact pow_lt_pow_left₀ h_upper_R hpos (by decide)
    exact Nat.cast_lt.mp hsqR
  have hsqrt : S = Nat.sqrt ((B + 1) ^ (2 * n + 1)) :=
    Nat.eq_sqrt'.mpr ⟨h_lower_sq, h_upper_sq⟩
  rw [← hsqrt, hS_mod]

end OMA.P_oeis_a002457

theorem OMA.solution : type_of% @OMA.S_oeis_a002457.main :=
  fun n hn => (OMA.P_oeis_a002457.main_aux n hn).symm
