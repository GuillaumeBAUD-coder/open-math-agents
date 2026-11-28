import OMAStatements.S_oeis_a167139
import Mathlib

namespace OMA.S_oeis_a167139

open PowerSeries BigOperators

private lemma coeff_zero_logOneAddX : PowerSeries.coeff 0 logOneAddX = 0 := by
  simp [logOneAddX]

private lemma coeff_lt_logOneAddX_pow (n k : ℕ) (hk : k < n) :
    PowerSeries.coeff k (logOneAddX ^ n) = 0 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (logOneAddX ^ n) * PowerSeries.coeff b logOneAddX)]
      refine Finset.sum_eq_zero fun a ha => ?_
      have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < n
      · rw [ih a hlt, zero_mul]
      · have hka : k - a = 0 := by omega
        rw [hka, coeff_zero_logOneAddX, mul_zero]

private lemma coeff_self_logOneAddX_pow (n : ℕ) :
    PowerSeries.coeff n (logOneAddX ^ n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (logOneAddX ^ n) * PowerSeries.coeff b logOneAddX)]
      rw [Finset.sum_eq_single n]
      · rw [ih, Nat.add_sub_cancel_left]
        simp [logOneAddX]
      · intro a ha hne
        have han : a ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hlt : a < n
        · rw [coeff_lt_logOneAddX_pow n a hlt, zero_mul]
        · have haeq : a = n + 1 := by omega
          rw [haeq, Nat.sub_self, coeff_zero_logOneAddX, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma one_add_X_mul_deriv_logOneAddX :
    (1 + PowerSeries.X) * PowerSeries.derivative ℚ logOneAddX = 1 := by
  apply PowerSeries.ext; intro k
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one, PowerSeries.coeff_derivative]
  cases k with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, add_zero]
      simp [logOneAddX]
  | succ k =>
      rw [if_neg (Nat.succ_ne_zero k), PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      simp only [logOneAddX, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
      have hk2 : ((k : ℚ) + 2) ≠ 0 := by positivity
      push_cast
      have h1 : (-1 : ℚ) ^ (k + 1) / ((k : ℚ) + 1 + 1) * ((k : ℚ) + 1 + 1) = (-1 : ℚ) ^ (k + 1) :=
        div_mul_cancel₀ _ (by linarith)
      have h2 : (-1 : ℚ) ^ k / ((k : ℚ) + 1) * ((k : ℚ) + 1) = (-1 : ℚ) ^ k :=
        div_mul_cancel₀ _ hk1
      rw [h1, h2, pow_succ]
      ring

/-- Key identity: `∑_{n=0}^k (r^n / n!) * [x^k] log(1+x)^n = C(r, k)` for all `r, k : ℕ`! -/
private lemma sum_pow_div_fact_coeff_logOneAddX (r : ℕ) :
    ∀ k : ℕ,
      ∑ n ∈ Finset.range (k + 1),
        ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * PowerSeries.coeff k (logOneAddX ^ n) =
      (Nat.choose r k : ℚ) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun k =>
    ∑ n ∈ Finset.range (k + 1),
      ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * PowerSeries.coeff k (logOneAddX ^ n)
  let G : PowerSeries ℚ := (1 + PowerSeries.X : PowerSeries ℚ) ^ r
  have hF0 : PowerSeries.coeff 0 F = 1 := by simp [F]
  have hG0 : PowerSeries.coeff 0 G = 1 := by simp [G]
  have hF_ode : (1 + PowerSeries.X) * PowerSeries.derivative ℚ F = PowerSeries.C (r : ℚ) * F := by
    apply PowerSeries.ext; intro k
    -- For any `N ≥ k + 1`, `F` agrees with `F_N := ∑_{n=0}^N (r^n/n!) * logOneAddX^n` on coeffs `≤ k + 1`!
    let FN : PowerSeries ℚ := ∑ n ∈ Finset.range (k + 2),
      PowerSeries.C ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * logOneAddX ^ n
    have hagree : ∀ j ≤ k + 1, PowerSeries.coeff j F = PowerSeries.coeff j FN := by
      intro j hj
      simp only [F, FN, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul]
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun n hn hnot => ?_
      simp only [Finset.mem_range] at hn hnot
      rw [coeff_lt_logOneAddX_pow n j (by omega), mul_zero]
    have hderiv_FN : (1 + PowerSeries.X) * PowerSeries.derivative ℚ FN =
        PowerSeries.C (r : ℚ) * (∑ n ∈ Finset.range (k + 1),
          PowerSeries.C ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * logOneAddX ^ n) := by
      simp only [FN, map_sum]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
          PowerSeries.derivative_one, add_zero]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul,
          PowerSeries.derivative_pow, pow_succ, Nat.factorial_succ, Nat.cast_mul]
      have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have hC : PowerSeries.C ((r : ℚ) ^ n * (r : ℚ) / (((n + 1 : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ))) *
          (((n + 1 : ℕ) : PowerSeries ℚ) * logOneAddX ^ n) =
          PowerSeries.C (r : ℚ) * PowerSeries.C ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * logOneAddX ^ n := by
        rw [show ((n + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((n + 1 : ℕ) : ℚ) by rw [map_natCast],
            ← mul_assoc, ← map_mul, ← map_mul]
        congr 1; congr 1
        field_simp
      calc (1 + PowerSeries.X) * (PowerSeries.C ((r : ℚ) ^ n * (r : ℚ) / (((n + 1 : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ))) *
              (((n + 1 : ℕ) : PowerSeries ℚ) * logOneAddX ^ n * PowerSeries.derivative ℚ logOneAddX))
          = (PowerSeries.C ((r : ℚ) ^ n * (r : ℚ) / (((n + 1 : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ))) *
              (((n + 1 : ℕ) : PowerSeries ℚ) * logOneAddX ^ n)) *
              ((1 + PowerSeries.X) * PowerSeries.derivative ℚ logOneAddX) := by ring
        _ = (PowerSeries.C (r : ℚ) * PowerSeries.C ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * logOneAddX ^ n) * 1 := by
              rw [hC, one_add_X_mul_deriv_logOneAddX]
        _ = PowerSeries.C (r : ℚ) * (PowerSeries.C ((r : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * logOneAddX ^ n) := by
              ring
    have hlhs : PowerSeries.coeff k ((1 + PowerSeries.X) * PowerSeries.derivative ℚ F) =
        PowerSeries.coeff k ((1 + PowerSeries.X) * PowerSeries.derivative ℚ FN) := by
      rw [add_mul, one_mul, add_mul, one_mul, map_add, map_add,
          PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hagree (k + 1) (le_refl _)]
      cases k with
      | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
      | succ k =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hagree (k + 1) (by omega)]
    rw [hlhs, hderiv_FN, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    congr 1
    simp only [F, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul]
  have hG_ode : (1 + PowerSeries.X) * PowerSeries.derivative ℚ G = PowerSeries.C (r : ℚ) * G := by
    cases r with
    | zero => simp [G]
    | succ r =>
        simp only [G, PowerSeries.derivative_pow, map_add, PowerSeries.derivative_one,
            PowerSeries.derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [show ((r + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((r + 1 : ℕ) : ℚ) by rw [map_natCast]]
        ring
  have hFG : ∀ k, PowerSeries.coeff k F = PowerSeries.coeff k G := by
    intro k
    induction k with
    | zero => rw [hF0, hG0]
    | succ k ih =>
        have hF1 := congrArg (PowerSeries.coeff k) hF_ode
        have hG1 := congrArg (PowerSeries.coeff k) hG_ode
        rw [add_mul, one_mul, map_add, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul] at hF1 hG1
        have hX : PowerSeries.coeff k (PowerSeries.X * PowerSeries.derivative ℚ F) =
            PowerSeries.coeff k (PowerSeries.X * PowerSeries.derivative ℚ G) := by
          cases k with
          | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
          | succ k =>
              rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
                  PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, ih]
        rw [ih, hX] at hF1
        have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
        have : PowerSeries.coeff (k + 1) F * ((k : ℚ) + 1) =
            PowerSeries.coeff (k + 1) G * ((k : ℚ) + 1) := by linarith
        exact mul_right_cancel₀ hk1 this
  intro k
  have hcoeffG : PowerSeries.coeff k G = (Nat.choose r k : ℚ) := by
    simp only [G]
    rw [add_comm (1 : PowerSeries ℚ), add_pow, map_sum]
    have hterm : ∀ x ∈ Finset.range (r + 1),
        PowerSeries.coeff k (PowerSeries.X ^ x * (1 : PowerSeries ℚ) ^ (r - x) *
          ((Nat.choose r x : ℕ) : PowerSeries ℚ)) =
        if k = x then (Nat.choose r x : ℚ) else 0 := by
      intro x _
      rw [one_pow, mul_one,
          show ((Nat.choose r x : ℕ) : PowerSeries ℚ) = PowerSeries.C ((Nat.choose r x : ℕ) : ℚ) by
            rw [map_natCast],
          mul_comm (PowerSeries.X ^ x), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · simp only [Finset.mem_range, not_lt] at hmem
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  simpa [F, hcoeffG] using hFG k

private def S2 (n a : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (a + 1), (-1 : ℤ) ^ (a - i) * (Nat.choose a i : ℤ) * (i : ℤ) ^ n

private lemma choose_alt_sum (a k : ℕ) :
    ∑ i ∈ Finset.range (a + 1),
      ((-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ)) * (Nat.choose i k : ℚ) =
    if k = a then 1 else 0 := by
  have hpoly : ((1 + Polynomial.X : Polynomial ℚ) - 1) ^ a = Polynomial.X ^ a := by ring
  have hlhs : ((1 + Polynomial.X : Polynomial ℚ) - 1) ^ a =
      ∑ i ∈ Finset.range (a + 1),
        Polynomial.C ((-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ)) * (1 + Polynomial.X) ^ i := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, show ((-1 : Polynomial ℚ) ^ (a - i)) = Polynomial.C ((-1 : ℚ) ^ (a - i)) by
      rw [map_pow, map_neg, map_one],
      show ((Nat.choose a i : ℕ) : Polynomial ℚ) = Polynomial.C ((Nat.choose a i : ℕ) : ℚ) by
      rw [Polynomial.C_eq_natCast]]
    ring
  rw [hlhs] at hpoly
  have hcoeff := congrArg (Polynomial.coeff · k) hpoly
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at hcoeff
  rw [← hcoeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_C_mul]
  congr 1
  rw [add_comm (1 : Polynomial ℚ), add_pow, Polynomial.finsetSum_coeff]
  simp only [one_pow, one_mul, ← Polynomial.C_eq_natCast, mul_comm (Polynomial.X ^ _),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hmem
  · rfl
  · simp only [Finset.mem_range, not_lt] at hmem
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

private lemma S1_mul_S2 (k a : ℕ) :
    ∑ n ∈ Finset.range (k + 1),
      ((S2 n a : ℤ) : ℚ) / ((Nat.factorial n : ℕ) : ℚ) * PowerSeries.coeff k (logOneAddX ^ n) =
    if k = a then 1 else 0 := by
  simp only [S2, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ Finset.range (a + 1),
      ∑ n ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ) * (i : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ) *
          PowerSeries.coeff k (logOneAddX ^ n) =
      ((-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ)) * (Nat.choose i k : ℚ) := by
    intro i _
    rw [← sum_pow_div_fact_coeff_logOneAddX i k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl hterm]
  exact choose_alt_sum a k

private lemma S2_eq_zero_of_lt (n a : ℕ) (h : n < a) : S2 n a = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have h0 := S1_mul_S2 n a
      rw [if_neg (by omega), Finset.sum_range_succ] at h0
      have hprev : ∑ x ∈ Finset.range n,
          ((S2 x a : ℤ) : ℚ) / ((Nat.factorial x : ℕ) : ℚ) * PowerSeries.coeff n (logOneAddX ^ x) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [ih x (Finset.mem_range.mp hx) (by have := Finset.mem_range.mp hx; omega),
              Int.cast_zero, zero_div, zero_mul]
      rw [hprev, zero_add, coeff_self_logOneAddX_pow, mul_one] at h0
      have hfn : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hq : ((S2 n a : ℤ) : ℚ) = 0 := (div_eq_zero_iff.mp h0).resolve_right hfn
      exact_mod_cast hq

private lemma logSeriesCoeff_eq_sum_S2 (L : ℕ → ℚ) :
    ∀ n : ℕ, L n = ∑ a ∈ Finset.range (n + 1), (S2 n a : ℚ) * logSeriesCoeff L a := by
  -- Prove `L n = ∑_{a ≤ n} S2(n, a) * logSeriesCoeff L a` by strong induction on `n`,
  -- using `logSeriesCoeff (fun n => L n - ∑_{a ≤ n} S2(n, a) * c a) k = 0` for all `k`!
  let R : ℕ → ℚ := fun n => L n - ∑ a ∈ Finset.range (n + 1), (S2 n a : ℚ) * logSeriesCoeff L a
  have hR_log : ∀ k, logSeriesCoeff R k = 0 := by
    intro k
    have h1 : logSeriesCoeff R k =
        logSeriesCoeff L k -
        ∑ n ∈ Finset.range (k + 1),
          (∑ a ∈ Finset.range (k + 1), (S2 n a : ℚ) * logSeriesCoeff L a) / ((Nat.factorial n : ℕ) : ℚ) *
            PowerSeries.coeff k (logOneAddX ^ n) := by
      simp only [logSeriesCoeff, R, sub_div, sub_mul, Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      congr 2
      refine Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ k + 1)) fun a ha hnot => ?_
      simp only [Finset.mem_range] at ha hnot
      rw [S2_eq_zero_of_lt n a (by omega), Int.cast_zero, zero_mul]
    rw [h1]
    simp only [Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h2 : ∑ a ∈ Finset.range (k + 1),
        ∑ n ∈ Finset.range (k + 1),
          (S2 n a : ℚ) * logSeriesCoeff L a / ((Nat.factorial n : ℕ) : ℚ) *
            PowerSeries.coeff k (logOneAddX ^ n) =
        logSeriesCoeff L k := by
      have hterm : ∀ a ∈ Finset.range (k + 1),
          ∑ n ∈ Finset.range (k + 1),
            (S2 n a : ℚ) * logSeriesCoeff L a / ((Nat.factorial n : ℕ) : ℚ) *
              PowerSeries.coeff k (logOneAddX ^ n) =
          if k = a then logSeriesCoeff L k else 0 := by
        intro a _
        have hpull : ∑ n ∈ Finset.range (k + 1),
            (S2 n a : ℚ) * logSeriesCoeff L a / ((Nat.factorial n : ℕ) : ℚ) *
              PowerSeries.coeff k (logOneAddX ^ n) =
            logSeriesCoeff L a * ∑ n ∈ Finset.range (k + 1),
              (S2 n a : ℚ) / ((Nat.factorial n : ℕ) : ℚ) * PowerSeries.coeff k (logOneAddX ^ n) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
        rw [hpull, S1_mul_S2 k a]
        split_ifs with hka
        · subst hka; ring
        · ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    rw [h2, sub_self]
  intro n
  have hRn : R n = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have h0 := hR_log n
        simp only [logSeriesCoeff] at h0
        rw [Finset.sum_range_succ] at h0
        have hprev : ∑ x ∈ Finset.range n,
            R x / ((Nat.factorial x : ℕ) : ℚ) * PowerSeries.coeff n (logOneAddX ^ x) = 0 :=
          Finset.sum_eq_zero fun x hx => by rw [ih x (Finset.mem_range.mp hx), zero_div, zero_mul]
        rw [hprev, zero_add, coeff_self_logOneAddX_pow, mul_one] at h0
        have hfn : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        exact (div_eq_zero_iff.mp h0).resolve_right hfn
  exact sub_eq_zero.mp hRn

private lemma logSeriesCoeff_mul_isInt {L M : ℕ → ℚ}
    (hL : ∀ k, ∃ z : ℤ, logSeriesCoeff L k = (z : ℚ))
    (hM : ∀ k, ∃ z : ℤ, logSeriesCoeff M k = (z : ℚ)) :
    ∀ k, ∃ z : ℤ, logSeriesCoeff (fun n => L n * M n) k = (z : ℚ) := by
  choose c hc using hL
  choose d hd using hM
  intro k
  -- Expand `L n * M n = ∑_{a ≤ k} ∑_{b ≤ k} c a * d b * S2(n, a) * S2(n, b)` for `n ≤ k`!
  have hLM : logSeriesCoeff (fun n => L n * M n) k =
      ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (c a : ℚ) * (d b : ℚ) *
          ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ)) *
            ((-1 : ℚ) ^ (b - j) * (Nat.choose b j : ℚ)) *
            (Nat.choose (i * j) k : ℚ) := by
    have hstep1 : logSeriesCoeff (fun n => L n * M n) k =
        ∑ n ∈ Finset.range (k + 1),
          (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (c a : ℚ) * (d b : ℚ) * ((S2 n a : ℚ) * (S2 n b : ℚ))) / ((Nat.factorial n : ℕ) : ℚ) *
          PowerSeries.coeff k (logOneAddX ^ n) := by
      simp only [logSeriesCoeff]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      congr 2
      have hLn : L n = ∑ a ∈ Finset.range (k + 1), (S2 n a : ℚ) * (c a : ℚ) := by
        rw [logSeriesCoeff_eq_sum_S2 L n]
        symm
        rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ k + 1))]
        · refine Finset.sum_congr rfl fun a _ => by rw [hc a]
        · intro a ha hnot
          simp only [Finset.mem_range] at ha hnot
          rw [S2_eq_zero_of_lt n a (by omega), Int.cast_zero, zero_mul]
      have hMn : M n = ∑ b ∈ Finset.range (k + 1), (S2 n b : ℚ) * (d b : ℚ) := by
        rw [logSeriesCoeff_eq_sum_S2 M n]
        symm
        rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ k + 1))]
        · refine Finset.sum_congr rfl fun b _ => by rw [hd b]
        · intro b hb hnot
          simp only [Finset.mem_range] at hb hnot
          rw [S2_eq_zero_of_lt n b (by omega), Int.cast_zero, zero_mul]
      rw [hLn, hMn, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
    rw [hstep1]
    simp only [Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hpull : ∑ n ∈ Finset.range (k + 1),
        (c a : ℚ) * (d b : ℚ) * ((S2 n a : ℚ) * (S2 n b : ℚ)) / ((Nat.factorial n : ℕ) : ℚ) *
          PowerSeries.coeff k (logOneAddX ^ n) =
        (c a : ℚ) * (d b : ℚ) *
          ∑ n ∈ Finset.range (k + 1),
            ((S2 n a : ℚ) * (S2 n b : ℚ)) / ((Nat.factorial n : ℕ) : ℚ) *
              PowerSeries.coeff k (logOneAddX ^ n) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
    rw [hpull]
    congr 1
    have hexpand : ∀ n, ((S2 n a : ℚ) * (S2 n b : ℚ)) / ((Nat.factorial n : ℕ) : ℚ) *
        PowerSeries.coeff k (logOneAddX ^ n) =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((-1 : ℚ) ^ (a - i) * (Nat.choose a i : ℚ)) *
          ((-1 : ℚ) ^ (b - j) * (Nat.choose b j : ℚ)) *
          ((((i * j : ℕ) : ℚ) ^ n / ((Nat.factorial n : ℕ) : ℚ)) * PowerSeries.coeff k (logOneAddX ^ n)) := by
      intro n
      simp only [S2, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_mul, mul_pow]; ring
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, sum_pow_div_fact_coeff_logOneAddX (i * j) k]
  refine ⟨∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
      c a * d b *
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((-1 : ℤ) ^ (a - i) * (Nat.choose a i : ℤ)) *
          ((-1 : ℤ) ^ (b - j) * (Nat.choose b j : ℤ)) *
          (Nat.choose (i * j) k : ℤ), ?_⟩
  rw [hLM]
  push_cast
  rfl

theorem main_proof :
    ∀ (L : ℕ → ℚ) (m : ℕ), 1 ≤ m →
      (∀ k : ℕ, ∃ z : ℤ, logSeriesCoeff L k = (z : ℚ)) →
      ∀ k : ℕ, ∃ z : ℤ, logSeriesCoeff (fun n => (L n) ^ m) k = (z : ℚ) := by
  intro L m hm hL
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero => simpa using hL
      | succ m =>
          have hprev := ih (by omega)
          have hmul := logSeriesCoeff_mul_isInt hprev hL
          simpa [pow_succ] using hmul

end OMA.S_oeis_a167139

theorem OMA.solution : type_of% @OMA.S_oeis_a167139.main :=
  OMA.S_oeis_a167139.main_proof
