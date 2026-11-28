import OMAStatements.S_oeis_a152260
import Mathlib

namespace OMA.S_oeis_a152260

open PowerSeries BigOperators

private lemma stirling2_eq_zero_of_lt : ∀ n k : ℕ, n < k → stirling2 n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      simp only [stirling2]
      rw [stirling2_eq_zero_of_lt n (k + 1) (by omega), stirling2_eq_zero_of_lt n k (by omega)]
      simp

/-- Standard expansion of `j^n` in the falling-factorial / binomial basis:
`j^n = ∑_{k=0}^n k! * S2(n, k) * C(j, k)`. -/
private lemma pow_eq_sum_stirling2 :
    ∀ (n j : ℕ),
      (j : ℚ) ^ n =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose j k : ℚ)
  | 0, j => by simp [stirling2]
  | n + 1, j => by
      rw [pow_succ, pow_eq_sum_stirling2 n j, Finset.sum_mul]
      -- Use `C(j, k) * j = (k + 1) * C(j, k + 1) + k * C(j, k)`!
      have hmul : ∀ k : ℕ,
          (Nat.choose j k : ℚ) * (j : ℚ) =
            ((k + 1 : ℕ) : ℚ) * (Nat.choose j (k + 1) : ℚ) + (k : ℚ) * (Nat.choose j k : ℚ) := by
        intro k
        by_cases hkj : k ≤ j
        · have hnat : Nat.choose j (k + 1) * (k + 1) = Nat.choose j k * (j - k) := by
            have := Nat.choose_succ_right_eq j k
            linarith
          have hq : (Nat.choose j (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
              (Nat.choose j k : ℚ) * ((j : ℚ) - (k : ℚ)) := by
            have := congr_arg (Nat.cast (R := ℚ)) hnat
            push_cast [Nat.cast_sub hkj] at this ⊢
            exact this
          linarith
        · have h1 : Nat.choose j k = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have h2 : Nat.choose j (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [h1, h2]
      have hstep :
          ∑ k ∈ Finset.range (n + 1),
            (Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose j k : ℚ) * (j : ℚ) =
          (∑ k ∈ Finset.range (n + 1),
            (Nat.factorial (k + 1) : ℚ) * (stirling2 n k : ℚ) * (Nat.choose j (k + 1) : ℚ)) +
          (∑ k ∈ Finset.range (n + 1),
            (Nat.factorial k : ℚ) * ((k : ℚ) * (stirling2 n k : ℚ)) * (Nat.choose j k : ℚ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc ((Nat.factorial k : ℚ) * (stirling2 n k : ℚ)), hmul k, Nat.factorial_succ]
        push_cast
        ring
      rw [hstep]
      -- Now align both sums with `∑ k ∈ Finset.range (n + 2)`!
      rw [Finset.sum_range_succ' (f := fun k => (Nat.factorial k : ℚ) * (stirling2 (n + 1) k : ℚ) * (Nat.choose j k : ℚ))]
      simp only [stirling2, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ' (f := fun k => (Nat.factorial k : ℚ) * ((k : ℚ) * (stirling2 n k : ℚ)) * (Nat.choose j k : ℚ))]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      rw [Finset.sum_range_succ (f := fun k => (Nat.factorial (k + 1) : ℚ) * (stirling2 n k : ℚ) * (Nat.choose j (k + 1) : ℚ))]
      rw [Finset.sum_range_succ (f := fun k => (Nat.factorial (k + 1) : ℚ) * (((k + 1) * stirling2 n (k + 1) + stirling2 n k : ℕ) : ℚ) * (Nat.choose j (k + 1) : ℚ))]
      have htop : (n + 1) * stirling2 n (n + 1) + stirling2 n n = stirling2 n n := by
        rw [stirling2_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n), mul_zero, zero_add]
      rw [htop, add_right_comm, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Nat.cast_add, Nat.cast_mul]
      ring

/-- Negative binomial power series `B_a(X) = ∑_{j ≥ 0} C(a + j - 1, j) * X^j` for `a ≥ 1`. -/
private noncomputable def negBinom (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun j => (Nat.choose (a + j - 1) j : ℚ)

/-- `(1 - X) * B_{a + 1} = B_a` for all `a ≥ 1`. -/
private lemma one_sub_X_mul_negBinom (a : ℕ) (ha : 1 ≤ a) :
    (1 - PowerSeries.X) * negBinom (a + 1) = negBinom a := by
  apply PowerSeries.ext; intro j
  rw [sub_mul, one_mul, map_sub, negBinom, negBinom]
  cases j with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, sub_zero, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      simp
  | succ j =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have h1 : a + 1 + (j + 1) - 1 = (a + j) + 1 := by omega
      have h2 : a + 1 + j - 1 = a + j := by omega
      have h3 : a + (j + 1) - 1 = a + j := by omega
      rw [h1, h2, h3, Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- `(1 - X)^a * B_a = 1` for all `a ≥ 1`. -/
private lemma one_sub_X_pow_mul_negBinom :
    ∀ a : ℕ, 1 ≤ a → (1 - PowerSeries.X) ^ a * negBinom a = 1
  | 0, h => by omega
  | 1, _ => by
      rw [pow_one]
      apply PowerSeries.ext; intro j
      rw [sub_mul, one_mul, map_sub, negBinom, PowerSeries.coeff_one]
      cases j with
      | zero =>
          rw [PowerSeries.coeff_zero_X_mul, sub_zero, PowerSeries.coeff_mk]; simp
      | succ j =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
          simp
  | a + 2, _ => by
      rw [pow_succ, mul_assoc, one_sub_X_mul_negBinom (a + 1) (by omega)]
      exact one_sub_X_pow_mul_negBinom (a + 1) (by omega)

/-- Binomial product identity:
`C(n + j - 1, j) * C(j, k) = C(n + k - 1, k) * C(n + j - 1, j - k)` for `1 ≤ n` and `k ≤ j`. -/
private lemma choose_mul_choose_eq (n j k : ℕ) (hn : 1 ≤ n) (hkj : k ≤ j) :
    Nat.choose (n + j - 1) j * Nat.choose j k =
      Nat.choose (n + k - 1) k * Nat.choose (n + j - 1) (j - k) := by
  have hfac1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ n + j - 1 by omega)
  have hfac2 := Nat.choose_mul_factorial_mul_factorial hkj
  have hfac3 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k - 1 by omega)
  have hfac4 := Nat.choose_mul_factorial_mul_factorial (show j - k ≤ n + j - 1 by omega)
  have ha1 : n + j - 1 - j = n - 1 := by omega
  have ha3 : n + k - 1 - k = n - 1 := by omega
  have ha4 : n + j - 1 - (j - k) = n + k - 1 := by omega
  rw [ha1] at hfac1
  rw [ha3] at hfac3
  rw [ha4] at hfac4
  have hprod :
      (Nat.choose (n + j - 1) j * Nat.choose j k) *
        (Nat.factorial k * Nat.factorial (j - k) * Nat.factorial (n - 1) * Nat.factorial (n + k - 1)) =
      (Nat.choose (n + k - 1) k * Nat.choose (n + j - 1) (j - k)) *
        (Nat.factorial k * Nat.factorial (j - k) * Nat.factorial (n - 1) * Nat.factorial (n + k - 1)) := by
    calc
      (Nat.choose (n + j - 1) j * Nat.choose j k) *
          (Nat.factorial k * Nat.factorial (j - k) * Nat.factorial (n - 1) * Nat.factorial (n + k - 1))
        = (Nat.choose (n + j - 1) j * (Nat.choose j k * Nat.factorial k * Nat.factorial (j - k))) *
            Nat.factorial (n - 1) * Nat.factorial (n + k - 1) := by ring
      _ = (Nat.choose (n + j - 1) j * Nat.factorial j * Nat.factorial (n - 1)) *
            Nat.factorial (n + k - 1) := by rw [hfac2]
      _ = Nat.factorial (n + j - 1) * Nat.factorial (n + k - 1) := by rw [hfac1]
      _ = (Nat.choose (n + j - 1) (j - k) * Nat.factorial (j - k) * Nat.factorial (n + k - 1)) *
            (Nat.choose (n + k - 1) k * Nat.factorial k * Nat.factorial (n - 1)) := by
            rw [hfac4, hfac3]
      _ = (Nat.choose (n + k - 1) k * Nat.choose (n + j - 1) (j - k)) *
            (Nat.factorial k * Nat.factorial (j - k) * Nat.factorial (n - 1) * Nat.factorial (n + k - 1)) := by
            ring
  have hpos : 0 < Nat.factorial k * Nat.factorial (j - k) * Nat.factorial (n - 1) * Nat.factorial (n + k - 1) := by
    positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hprod

/-- `(n : ℚ)⁻¹ * C(n + k - 1, k) = C(n + k, k) / (n + k)` for `1 ≤ n`. -/
private lemma choose_ratio_eq (n k : ℕ) (hn : 1 ≤ n) :
    (n : ℚ)⁻¹ * (Nat.choose (n + k - 1) k : ℚ) =
      (Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) := by
  have hnat : (n + k) * Nat.choose (n + k - 1) k = n * Nat.choose (n + k) k := by
    have hfac1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k - 1 by omega)
    have hfac2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
    have ha1 : n + k - 1 - k = n - 1 := by omega
    have ha2 : n + k - k = n := by omega
    rw [ha1] at hfac1
    rw [ha2] at hfac2
    have hfn : Nat.factorial n = n * Nat.factorial (n - 1) := by
      cases n with
      | zero => omega
      | succ n => simp [Nat.factorial_succ]
    have hfnk : Nat.factorial (n + k) = (n + k) * Nat.factorial (n + k - 1) := by
      have : n + k = (n + k - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ, ← this]
    have hmul :
        ((n + k) * Nat.choose (n + k - 1) k) * (Nat.factorial k * Nat.factorial (n - 1)) =
        (n * Nat.choose (n + k) k) * (Nat.factorial k * Nat.factorial (n - 1)) := by
      calc
        ((n + k) * Nat.choose (n + k - 1) k) * (Nat.factorial k * Nat.factorial (n - 1))
          = (n + k) * (Nat.choose (n + k - 1) k * Nat.factorial k * Nat.factorial (n - 1)) := by ring
        _ = (n + k) * Nat.factorial (n + k - 1) := by rw [hfac1]
        _ = Nat.factorial (n + k) := hfnk.symm
        _ = Nat.choose (n + k) k * Nat.factorial k * Nat.factorial n := hfac2.symm
        _ = (n * Nat.choose (n + k) k) * (Nat.factorial k * Nat.factorial (n - 1)) := by
              rw [hfn]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
  have hn_ne : (n : ℚ) ≠ 0 := by positivity
  have hnk_ne : ((n + k : ℕ) : ℚ) ≠ 0 := by positivity
  have hq : ((n + k : ℕ) : ℚ) * (Nat.choose (n + k - 1) k : ℚ) =
      (n : ℚ) * (Nat.choose (n + k) k : ℚ) := by
    exact_mod_cast hnat
  field_simp [hn_ne, hnk_ne]
  linarith

theorem main_proof :
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ n →
      a152260 n m =
        ∑ k ∈ Finset.Icc 1 m,
          (Nat.choose (n + k) k : ℚ) * (Nat.choose (n - k) (m - k) : ℚ) *
            (Nat.factorial k : ℚ) * (-1 : ℚ) ^ (m - k) * (stirling2 n k : ℚ) /
            ((n + k : ℕ) : ℚ) := by
  intro n m hn hm hmn
  -- Express the inner series `∑_{j ≥ 0} C(n + j - 1, j) * j^n * X^j` as a finite sum over `k ∈ 1..n`!
  have hinner :
      (PowerSeries.mk fun j => (Nat.choose (n + j - 1) j : ℚ) * (j : ℚ) ^ n) =
        ∑ k ∈ Finset.Icc 1 n,
          PowerSeries.C ((Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose (n + k - 1) k : ℚ)) *
            PowerSeries.X ^ k * negBinom (n + k) := by
    apply PowerSeries.ext; intro j
    rw [PowerSeries.coeff_mk, map_sum, pow_eq_sum_stirling2 n j, Finset.mul_sum]
    rw [Finset.sum_range_succ']
    have h0 : stirling2 n 0 = 0 := by
      cases n with
      | zero => omega
      | succ n => rfl
    simp only [h0, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [show Finset.Icc 1 n = (Finset.range n).image (· + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega]
    rw [Finset.sum_image (by intro a _ b _ hab; dsimp at hab; omega)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc (PowerSeries.C _), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hkj : k + 1 ≤ j
    · simp only [hkj, ↓reduceIte, negBinom, PowerSeries.coeff_mk]
      have hidx : n + (k + 1) + (j - (k + 1)) - 1 = n + j - 1 := by omega
      rw [hidx]
      have hch : (Nat.choose (n + j - 1) j : ℚ) * (Nat.choose j (k + 1) : ℚ) =
          (Nat.choose (n + (k + 1) - 1) (k + 1) : ℚ) * (Nat.choose (n + j - 1) (j - (k + 1)) : ℚ) := by
        exact_mod_cast choose_mul_choose_eq n j (k + 1) hn hkj
      calc
        (Nat.choose (n + j - 1) j : ℚ) *
            ((Nat.factorial (k + 1) : ℚ) * (stirling2 n (k + 1) : ℚ) * (Nat.choose j (k + 1) : ℚ))
          = (Nat.factorial (k + 1) : ℚ) * (stirling2 n (k + 1) : ℚ) *
              ((Nat.choose (n + j - 1) j : ℚ) * (Nat.choose j (k + 1) : ℚ)) := by ring
        _ = (Nat.factorial (k + 1) : ℚ) * (stirling2 n (k + 1) : ℚ) *
              (Nat.choose (n + (k + 1) - 1) (k + 1) : ℚ) * (Nat.choose (n + j - 1) (j - (k + 1)) : ℚ) := by
              rw [hch]; ring
    · simp only [hkj, ↓reduceIte, mul_zero]
      have hch0 : Nat.choose j (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hch0]
  -- Now simplify `a152260Series n` using `(1 - X)^(2n) * negBinom (n + k) = (1 - X)^(n - k)`!
  have hser :
      a152260Series n =
        ∑ k ∈ Finset.Icc 1 n,
          PowerSeries.C ((Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) *
            (Nat.factorial k : ℚ) * (stirling2 n k : ℚ)) *
            PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k) := by
    unfold a152260Series
    rw [hinner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hpow : (1 - PowerSeries.X : PowerSeries ℚ) ^ (2 * n) =
        (1 - PowerSeries.X) ^ (n - k) * (1 - PowerSeries.X) ^ (n + k) := by
      rw [← pow_add]; congr 1; omega
    have hcancel := one_sub_X_pow_mul_negBinom (n + k) (by omega)
    have hC :
        PowerSeries.C ((n : ℚ)⁻¹) *
          PowerSeries.C ((Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose (n + k - 1) k : ℚ)) =
        PowerSeries.C ((Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) *
          (Nat.factorial k : ℚ) * (stirling2 n k : ℚ)) := by
      rw [← map_mul]
      congr 1
      have hr := choose_ratio_eq n k hn
      linear_combination (Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * hr
    calc
      PowerSeries.C ((n : ℚ)⁻¹) * (1 - PowerSeries.X) ^ (2 * n) *
          (PowerSeries.C ((Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose (n + k - 1) k : ℚ)) *
            PowerSeries.X ^ k * negBinom (n + k))
        = (PowerSeries.C ((n : ℚ)⁻¹) *
            PowerSeries.C ((Nat.factorial k : ℚ) * (stirling2 n k : ℚ) * (Nat.choose (n + k - 1) k : ℚ))) *
            PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k) *
            ((1 - PowerSeries.X) ^ (n + k) * negBinom (n + k)) := by
              rw [hpow]; ring
      _ = PowerSeries.C ((Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) *
            (Nat.factorial k : ℚ) * (stirling2 n k : ℚ)) *
            PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k) := by
              rw [hC, hcancel, mul_one]
  -- Extract coefficient `m` from `hser`!
  unfold a152260
  rw [hser, map_sum]
  have hcoeff_pow : ∀ (a r : ℕ),
      PowerSeries.coeff r ((1 - PowerSeries.X : PowerSeries ℚ) ^ a) =
        (-1 : ℚ) ^ r * (Nat.choose a r : ℚ) := by
    intro a r
    have h1 : (1 - PowerSeries.X : PowerSeries ℚ) ^ a =
        ∑ j ∈ Finset.range (a + 1),
          PowerSeries.C ((-1 : ℚ) ^ j * (Nat.choose a j : ℚ)) * PowerSeries.X ^ j := by
      rw [show (1 - PowerSeries.X : PowerSeries ℚ) = -PowerSeries.X + 1 by ring, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one, neg_pow]
      have hC : PowerSeries.C ((-1 : ℚ) ^ j * (Nat.choose a j : ℚ)) =
          (-1 : PowerSeries ℚ) ^ j * ((Nat.choose a j : ℕ) : PowerSeries ℚ) := by
        rw [map_mul, map_pow, map_neg, map_one, map_natCast]
      rw [hC]; ring
    rw [h1, map_sum]
    by_cases hra : r ≤ a
    · rw [Finset.sum_eq_single r]
      · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]; simp
      · intro j _ hne
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne.symm, mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : r ≠ j := by have := Finset.mem_range.mp hj; omega
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne, mul_zero]
  have hsplit :
      ∑ k ∈ Finset.Icc 1 n,
        PowerSeries.coeff m
          (PowerSeries.C ((Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) *
            (Nat.factorial k : ℚ) * (stirling2 n k : ℚ)) *
            PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k)) =
      ∑ k ∈ Finset.Icc 1 m,
        PowerSeries.coeff m
          (PowerSeries.C ((Nat.choose (n + k) k : ℚ) / ((n + k : ℕ) : ℚ) *
            (Nat.factorial k : ℚ) * (stirling2 n k : ℚ)) *
            PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k)) := by
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hmn) ?_
    intro k hk hnot
    have hkm : m < k := by
      simp only [Finset.mem_Icc] at hk hnot
      omega
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
        if_neg (by omega), mul_zero]
  rw [hsplit]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos hkm, hcoeff_pow]
  ring

end OMA.S_oeis_a152260

theorem OMA.solution : type_of% @OMA.S_oeis_a152260.main :=
  OMA.S_oeis_a152260.main_proof
