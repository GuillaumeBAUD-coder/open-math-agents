import OMAStatements.S_oeis_a384819
import Mathlib

namespace OMA.S_oeis_a384819

open PowerSeries BigOperators

private lemma expLogSeries_ode (C : ℕ → ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (expLogSeries C) =
      expLogSeries C * PowerSeries.mk fun n => if n = 0 then 0 else (C n : ℚ) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]
      simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, expLogSeries,
          PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (PowerSeries.mk (expLogCoeffs C)) *
              PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))]
      rw [expLogCoeffs]
      have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [div_mul_cancel₀ _ hpos]
      rw [Finset.sum_range_succ, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Nat.sub_self]
      simp only [↓reduceIte, mul_zero, add_zero]
      -- Reverse the sum `i ↦ n - i`!
      rw [Fin.sum_univ_eq_sum_range (fun k => (C (k + 1) : ℚ) * expLogCoeffs C (n - k)) (n + 1)]
      rw [← Finset.sum_range_reflect (fun k => (C (k + 1) : ℚ) * expLogCoeffs C (n - k)) (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n + 1 := Finset.mem_range.mp hi
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hne : n + 1 - i ≠ 0 := by omega
      have h1 : n + 1 - 1 - i + 1 = n + 1 - i := by omega
      have h2 : n - (n + 1 - 1 - i) = i := by omega
      simp only [hne, ↓reduceIte, h1, h2]
      ring

/-- Uniqueness of `expLogSeries C`: any `F` with `F(0) = 1` and `X * F' = F * (∑_{n ≥ 1} C(n) X^n)`
equals `expLogSeries C`. -/
private lemma eq_expLogSeries_of_ode (C : ℕ → ℤ) (F : PowerSeries ℚ)
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : PowerSeries.X * PowerSeries.derivative ℚ F =
      F * PowerSeries.mk fun n => if n = 0 then 0 else (C n : ℚ)) :
    F = expLogSeries C := by
  apply PowerSeries.ext; intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [h0, expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
    | succ n =>
        have hF := congr_arg (PowerSeries.coeff (n + 1)) hode
        have hE := congr_arg (PowerSeries.coeff (n + 1)) (expLogSeries_ode C)
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i F *
                PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hF
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (expLogSeries C) *
                PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hE
        rw [Finset.sum_range_succ, PowerSeries.coeff_mk, Nat.sub_self, if_pos rfl, mul_zero, add_zero] at hF hE
        have hsum_eq :
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k F * PowerSeries.coeff (n + 1 - k)
                (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (expLogSeries C) * PowerSeries.coeff (n + 1 - k)
                (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [ih k (Finset.mem_range.mp hk)]
        rw [hsum_eq, ← hE] at hF
        have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hpos hF

/-- Integer-coefficient power series `(1 - X^d)^(-m)` for `d ≥ 1` and `m : ℤ`. -/
private noncomputable def eulerFactor (d : ℕ) (m : ℤ) : PowerSeries ℚ :=
  if 0 ≤ m then
    ((PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0) ^ m.toNat)
  else
    ((1 - PowerSeries.X ^ d) ^ (-m).toNat)

private lemma isIntegerSeries_mul {f g : PowerSeries ℚ}
    (hf : isIntegerSeries f) (hg : isIntegerSeries g) : isIntegerSeries (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ k ∈ Finset.range (n + 1), zf k * zg (n - k), ?_⟩
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hzf k, hzg (n - k), Int.cast_mul]

private lemma isIntegerSeries_one : isIntegerSeries (1 : PowerSeries ℚ) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

private lemma isIntegerSeries_pow {f : PowerSeries ℚ} (hf : isIntegerSeries f) :
    ∀ k : ℕ, isIntegerSeries (f ^ k)
  | 0 => by simpa using isIntegerSeries_one
  | k + 1 => by rw [pow_succ]; exact isIntegerSeries_mul (isIntegerSeries_pow hf k) hf

private lemma isIntegerSeries_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (hf : ∀ i ∈ s, isIntegerSeries (f i)) : isIntegerSeries (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isIntegerSeries_one
  | @insert a s has ih =>
      rw [Finset.prod_insert has]
      exact isIntegerSeries_mul (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isIntegerSeries_eulerFactor (d : ℕ) (m : ℤ) : isIntegerSeries (eulerFactor d m) := by
  unfold eulerFactor
  split_ifs
  · apply isIntegerSeries_pow
    intro n; rw [PowerSeries.coeff_mk]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  · apply isIntegerSeries_pow
    intro n; rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    refine ⟨(if n = 0 then 1 else 0) - (if n = d then 1 else 0), ?_⟩
    push_cast; split_ifs <;> ring

private lemma geom_mul_one_sub (d : ℕ) (hd : 1 ≤ d) :
    (1 - PowerSeries.X ^ d) * (PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0) = 1 := by
  apply PowerSeries.ext; intro n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    have hnot : ¬ d ≤ 0 := by omega
    simp [hnot]
  · simp only [hn0, ↓reduceIte]
    by_cases hle : d ≤ n
    · simp only [hle, ↓reduceIte, PowerSeries.coeff_mk]
      have hiff : d ∣ n - d ↔ d ∣ n := by
        constructor
        · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl d)
        · intro h; exact (Nat.dvd_sub_self_right.mpr (Or.inl h))
      by_cases hdiv : d ∣ n
      · simp [hdiv, hiff.mpr hdiv]
      · simp [hdiv, mt hiff.mp hdiv]
    · simp only [hle, ↓reduceIte, sub_zero]
      have hndiv : ¬ d ∣ n := fun h => hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h)
      simp [hndiv]

private lemma coeff_zero_eulerFactor (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    PowerSeries.coeff 0 (eulerFactor d m) = 1 := by
  unfold eulerFactor
  split_ifs
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_mk]
    simp
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_sub, map_one, map_pow,
        PowerSeries.constantCoeff_X, zero_pow (by omega), sub_zero, one_pow]

private lemma eulerFactor_ode (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (eulerFactor d m) =
      eulerFactor d m * PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (m : ℚ)) else 0 := by
  set G : PowerSeries ℚ := PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0
  have hG : (1 - PowerSeries.X ^ d) * G = 1 := geom_mul_one_sub d hd
  have hG_tail : PowerSeries.mk (fun n => if n ≠ 0 ∧ d ∣ n then (1 : ℚ) else 0) =
      PowerSeries.X ^ d * G := by
    apply PowerSeries.ext; intro n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    by_cases hle : d ≤ n
    · have hn0 : n ≠ 0 := by omega
      simp only [hle, hn0, ne_eq, not_false_eq_true, true_and, ↓reduceIte, G, PowerSeries.coeff_mk]
      have hiff : d ∣ n - d ↔ d ∣ n := by
        constructor
        · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl d)
        · intro h; exact Nat.dvd_sub_self_right.mpr (Or.inl h)
      by_cases hdiv : d ∣ n
      · simp [hdiv, hiff.mpr hdiv]
      · simp [hdiv, mt hiff.mp hdiv]
    · simp only [hle, ↓reduceIte]
      split_ifs with h
      · exfalso; exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero h.1) h.2)
      · rfl
  have hRHS_eq :
      PowerSeries.mk (fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (m : ℚ)) else 0) =
      PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G) := by
    rw [← hG_tail]
    apply PowerSeries.ext; intro n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    split_ifs <;> ring
  rw [hRHS_eq]
  have hd_one_sub : PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d) =
      -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
    rw [map_sub, Derivation.map_one_eq_zero, zero_sub, mul_neg, Derivation.leibniz_pow,
        PowerSeries.derivative_X, smul_eq_mul, mul_one, nsmul_eq_mul]
    have hX : PowerSeries.X * ((d : PowerSeries ℚ) * PowerSeries.X ^ (d - 1)) =
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
      have hpow : (PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ (d - 1) = PowerSeries.X ^ d := by
        rw [← pow_succ']; congr 1; omega
      rw [show (d : PowerSeries ℚ) = PowerSeries.C (d : ℚ) by rw [map_natCast]]
      linear_combination PowerSeries.C (d : ℚ) * hpow
    rw [hX]; ring
  have hdG : PowerSeries.X * PowerSeries.derivative ℚ G =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G := by
    have hdiff := congr_arg (fun f => PowerSeries.X * PowerSeries.derivative ℚ f) hG
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, mul_zero, mul_add] at hdiff
    simp only [smul_eq_mul] at hdiff
    have h1 : PowerSeries.X * (G * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) =
        -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by
      calc
        PowerSeries.X * (G * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d))
          = G * (PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) := by ring
        _ = G * (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) := by rw [hd_one_sub]
        _ = -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by ring
    have h2 : (1 - PowerSeries.X ^ d) * (PowerSeries.X * PowerSeries.derivative ℚ G) =
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by
      linear_combination hdiff - h1
    calc
      PowerSeries.X * PowerSeries.derivative ℚ G
        = ((1 - PowerSeries.X ^ d) * G) * (PowerSeries.X * PowerSeries.derivative ℚ G) := by
            rw [hG, one_mul]
      _ = G * ((1 - PowerSeries.X ^ d) * (PowerSeries.X * PowerSeries.derivative ℚ G)) := by ring
      _ = G * (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G) := by rw [h2]
      _ = PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G := by ring
  unfold eulerFactor
  split_ifs with hm
  · cases hk : m.toNat with
    | zero =>
        have hm0 : (m : ℚ) = 0 := by
          have h1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
          rw [hk] at h1
          exact_mod_cast h1.symm
        simp [hm0]
    | succ k =>
        have hmk : ((k + 1 : ℕ) : ℚ) = (m : ℚ) := by
          have : ((k + 1 : ℕ) : ℤ) = m := by rw [← hk]; exact Int.toNat_of_nonneg hm
          exact_mod_cast this
        rw [Derivation.leibniz_pow, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        change PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * (G ^ k * PowerSeries.derivative ℚ G)) = _
        calc
          PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * (G ^ k * PowerSeries.derivative ℚ G))
            = ((k + 1 : ℕ) : PowerSeries ℚ) * G ^ k * (PowerSeries.X * PowerSeries.derivative ℚ G) := by ring
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * G ^ k * (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G) := by
                rw [hdG]
          _ = G ^ (k + 1) * (PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G)) := by
                rw [pow_succ, ← hmk, map_mul, show ((k + 1 : ℕ) : PowerSeries ℚ) =
                  PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast]]
                ring
  · cases hk : (-m).toNat with
    | zero =>
        have hm0 : (m : ℚ) = 0 := by
          have h1 : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
          rw [hk] at h1
          have hmz : m = 0 := by omega
          exact_mod_cast hmz
        simp [hm0]
    | succ k =>
        have hmk : ((k + 1 : ℕ) : ℚ) = -(m : ℚ) := by
          have : ((k + 1 : ℕ) : ℤ) = -m := by rw [← hk]; exact Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [Derivation.leibniz_pow, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        calc
          PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * ((1 - PowerSeries.X ^ d) ^ k *
              PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)))
            = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) := by ring
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) := by rw [hd_one_sub]
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) * ((1 - PowerSeries.X ^ d) * G) := by
                rw [hG, mul_one]
          _ = (1 - PowerSeries.X ^ d) ^ (k + 1) *
                (PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G)) := by
                have hm_eq : PowerSeries.C (m : ℚ) = -((k + 1 : ℕ) : PowerSeries ℚ) := by
                  have h1 : (m : ℚ) = -((k + 1 : ℕ) : ℚ) := by linarith
                  rw [h1, map_neg, map_natCast]
                rw [pow_succ, map_mul, hm_eq]
                ring

/-- Product rule for `X * (∏ f_i)' = (∏ f_i) * ∑ (X * f_i' / f_i)`. -/
private lemma prod_eulerFactor_ode (N : ℕ) (M : ℕ → ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
      (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) *
        ∑ d ∈ Finset.Icc 1 N,
          PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
      rw [hIcc, Finset.prod_insert hnot, Finset.sum_insert hnot, Derivation.leibniz,
          smul_eq_mul, smul_eq_mul, mul_add]
      set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
      set F := eulerFactor (N + 1) (M (N + 1))
      have hF := eulerFactor_ode (N + 1) (by omega) (M (N + 1))
      calc
        PowerSeries.X * (F * PowerSeries.derivative ℚ P) +
            PowerSeries.X * (P * PowerSeries.derivative ℚ F)
          = F * (PowerSeries.X * PowerSeries.derivative ℚ P) +
              P * (PowerSeries.X * PowerSeries.derivative ℚ F) := by ring
        _ = F * (P * ∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0) +
              P * (F * PowerSeries.mk fun n =>
                if n ≠ 0 ∧ (N + 1) ∣ n then (((N + 1 : ℕ) : ℚ) * (M (N + 1) : ℚ)) else 0) := by
              rw [ih, hF]
        _ = F * P * (PowerSeries.mk (fun n =>
                if n ≠ 0 ∧ (N + 1) ∣ n then (((N + 1 : ℕ) : ℚ) * (M (N + 1) : ℚ)) else 0) +
              ∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0) := by
              ring

/-- **Direction ⇐**: If `C(n) = ∑_{d ∣ n} d * M(d)` for some `M : ℕ → ℤ`,
then `expLogSeries C` has integer coefficients! -/
private lemma isIntegerSeries_of_euler_decomp (C M : ℕ → ℤ)
    (hCM : ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d) :
    isIntegerSeries (expLogSeries C) := by
  intro N
  set P : PowerSeries ℚ := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
  have hP_int : isIntegerSeries P :=
    isIntegerSeries_prod _ _ fun d _ => isIntegerSeries_eulerFactor d (M d)
  -- Show `coeff n P = coeff n (expLogSeries C)` for all `n ≤ N`!
  have hagree : ∀ n ≤ N, PowerSeries.coeff n P = PowerSeries.coeff n (expLogSeries C) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
          have hP0 : PowerSeries.coeff 0 P = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
            refine Finset.prod_eq_one fun d hd => ?_
            rw [← PowerSeries.coeff_zero_eq_constantCoeff]
            exact coeff_zero_eulerFactor d (Finset.mem_Icc.mp hd).1 (M d)
          rw [hP0, expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
      | succ n =>
          have hP_ode := congr_arg (PowerSeries.coeff (n + 1)) (prod_eulerFactor_ode N M)
          have hE_ode := congr_arg (PowerSeries.coeff (n + 1)) (expLogSeries_ode C)
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i P *
                  PowerSeries.coeff j (∑ d ∈ Finset.Icc 1 N,
                    PowerSeries.mk fun m => if m ≠ 0 ∧ d ∣ m then ((d : ℚ) * (M d : ℚ)) else 0))] at hP_ode
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i (expLogSeries C) *
                  PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hE_ode
          have hsum_eq :
              ∑ k ∈ Finset.range (n + 2),
                PowerSeries.coeff k P *
                  PowerSeries.coeff (n + 1 - k) (∑ d ∈ Finset.Icc 1 N,
                    PowerSeries.mk fun m => if m ≠ 0 ∧ d ∣ m then ((d : ℚ) * (M d : ℚ)) else 0) =
              ∑ k ∈ Finset.range (n + 2),
                PowerSeries.coeff k (expLogSeries C) *
                  PowerSeries.coeff (n + 1 - k) (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkl : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            by_cases hkeq : k = n + 1
            · subst hkeq; simp [map_sum]
            · rw [ih k (by omega) (by omega)]
              congr 1
              rw [map_sum, PowerSeries.coeff_mk]
              have hm_pos : 1 ≤ n + 1 - k := by omega
              have hm_ne : n + 1 - k ≠ 0 := by omega
              simp only [hm_ne, ne_eq, not_false_eq_true, true_and, ↓reduceIte, PowerSeries.coeff_mk]
              rw [← Finset.sum_filter]
              have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ n + 1 - k) = Nat.divisors (n + 1 - k) := by
                ext d
                simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
                constructor
                · intro ⟨_, hd⟩; exact ⟨hd, hm_ne⟩
                · intro ⟨hd, _⟩
                  exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm_pos,
                    le_trans (Nat.le_of_dvd hm_pos hd) (by omega)⟩, hd⟩
              rw [hfilt, hCM (n + 1 - k) hm_pos, Int.cast_sum]
              refine Finset.sum_congr rfl fun d _ => by push_cast; ring
          rw [hsum_eq, ← hE_ode] at hP_ode
          have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
          exact mul_right_cancel₀ hpos hP_ode
  obtain ⟨z, hz⟩ := hP_int N
  exact ⟨z, (hagree N (le_refl N)).symm.trans hz⟩

/-- **Direction ⇒**: If `expLogSeries C` has integer coefficients, then there exists `M : ℕ → ℤ`
such that `C n = ∑_{d ∣ n} d * M d` for all `n ≥ 1`! -/
private lemma exists_euler_decomp_of_isIntegerSeries (C : ℕ → ℤ)
    (hC : isIntegerSeries (expLogSeries C)) :
    ∃ M : ℕ → ℤ, ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d := by
  -- Greedy construction: for each `N`, there exists `M : ℕ → ℤ` such that
  -- `∏_{d=1}^N eulerFactor d (M d)` agrees with `expLogSeries C` on all `n ≤ N`!
  -- Actually define `M` by strong recursion using `Classical.choose` on the remainder series!
  -- Even simpler: prove by induction on `N` that there exists `M : ℕ → ℤ` with
  -- `∀ n, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d`!
  -- Wait: since `M n` is UNIQUELY determined by `C` (`n * M n = C n - ∑_{d ∣ n, d < n} d * M d`),
  -- we can just define `M` directly by strong recursion in `ℚ` and prove `M n ∈ ℤ`!
  have hM_exists : ∀ N : ℕ, ∃ M : ℕ → ℤ,
      ∀ n : ℕ, n ≤ N →
        PowerSeries.coeff n (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
          PowerSeries.coeff n (expLogSeries C) := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ => 0, fun n hn => ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        simp [expLogSeries, expLogCoeffs]
    | succ N ih =>
        obtain ⟨M, hM⟩ := ih
        set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
        have hP_int : isIntegerSeries P :=
          isIntegerSeries_prod _ _ fun d _ => isIntegerSeries_eulerFactor d (M d)
        obtain ⟨zE, hzE⟩ := hC (N + 1)
        obtain ⟨zP, hzP⟩ := hP_int (N + 1)
        let m : ℤ := zE - zP
        let M' : ℕ → ℤ := Function.update M (N + 1) m
        refine ⟨M', fun n hn => ?_⟩
        have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
        rw [hIcc, Finset.prod_insert hnot]
        have hprod_eq : ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M' d) = P := by
          refine Finset.prod_congr rfl fun d hd => ?_
          have hne : d ≠ N + 1 := by have := (Finset.mem_Icc.mp hd).2; omega
          simp [M', hne]
        rw [hprod_eq]
        have hM'N : M' (N + 1) = m := Function.update_self (N + 1) m M
        rw [hM'N]
        -- Compute `coeff k (eulerFactor (N + 1) m)` for `k ≤ N + 1`:
        -- `1` at `k = 0`, `m` at `k = N + 1`, `0` for `0 < k < N + 1`!
        have hF_coeff : ∀ k ≤ N + 1,
            PowerSeries.coeff k (eulerFactor (N + 1) m) =
              if k = 0 then 1 else if k = N + 1 then (m : ℚ) else 0 := by
          intro k hk
          cases k with
          | zero =>
              simp [coeff_zero_eulerFactor (N + 1) (by omega) m]
          | succ k =>
              have hode := congr_arg (PowerSeries.coeff (k + 1))
                (eulerFactor_ode (N + 1) (by omega) m)
              rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i j => PowerSeries.coeff i (eulerFactor (N + 1) m) *
                      PowerSeries.coeff j (PowerSeries.mk fun r =>
                        if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0))] at hode
              by_cases hkN : k + 1 = N + 1
              · rw [hkN] at hode ⊢
                rw [Finset.sum_range_succ'] at hode
                have htail :
                    ∑ j ∈ Finset.range (N + 1),
                      PowerSeries.coeff (j + 1) (eulerFactor (N + 1) m) *
                        PowerSeries.coeff (N + 1 - (j + 1)) (PowerSeries.mk fun r =>
                          if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0) = 0 := by
                  refine Finset.sum_eq_zero fun j hj => ?_
                  rw [PowerSeries.coeff_mk]
                  have hlt : N + 1 - (j + 1) < N + 1 := by omega
                  have hnotd : ¬ (N + 1 - (j + 1) ≠ 0 ∧ (N + 1) ∣ (N + 1 - (j + 1))) := by
                    rintro ⟨hne, hd⟩
                    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) (by omega)
                  rw [if_neg hnotd, mul_zero]
                rw [htail, zero_add, Nat.sub_zero, coeff_zero_eulerFactor (N + 1) (by omega) m,
                    one_mul, PowerSeries.coeff_mk] at hode
                simp only [Nat.succ_ne_zero, ne_eq, not_false_eq_true, dvd_refl, and_self,
                  ↓reduceIte] at hode ⊢
                have hkN_q : ((k : ℚ) + 1) = ((N + 1 : ℕ) : ℚ) := by exact_mod_cast hkN
                rw [hkN_q] at hode
                have hpos : ((N + 1 : ℕ) : ℚ) ≠ 0 := by positivity
                exact mul_left_cancel₀ hpos (by linarith)
              · have hzero :
                    ∑ j ∈ Finset.range (k + 2),
                      PowerSeries.coeff j (eulerFactor (N + 1) m) *
                        PowerSeries.coeff (k + 1 - j) (PowerSeries.mk fun r =>
                          if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0) = 0 := by
                  refine Finset.sum_eq_zero fun j hj => ?_
                  rw [PowerSeries.coeff_mk]
                  have hnotd : ¬ (k + 1 - j ≠ 0 ∧ (N + 1) ∣ (k + 1 - j)) := by
                    rintro ⟨hne, hd⟩
                    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) (by omega)
                  rw [if_neg hnotd, mul_zero]
                rw [hzero] at hode
                have hpos : ((k : ℚ) + 1) ≠ 0 := by positivity
                simp only [Nat.succ_ne_zero, hkN, ↓reduceIte]
                exact (mul_eq_zero.mp hode).resolve_right hpos
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (eulerFactor (N + 1) m) * PowerSeries.coeff j P)]
        by_cases hnN : n = N + 1
        · subst hnN
          rw [Finset.sum_range_succ', Finset.sum_range_succ]
          have hmid :
              ∑ k ∈ Finset.range N,
                PowerSeries.coeff (k + 1) (eulerFactor (N + 1) m) * PowerSeries.coeff (N + 1 - (k + 1)) P = 0 := by
            refine Finset.sum_eq_zero fun k hk => ?_
            have hkl : k < N := Finset.mem_range.mp hk
            rw [hF_coeff (k + 1) (by omega), if_neg (Nat.succ_ne_zero k),
                if_neg (by omega : k + 1 ≠ N + 1), zero_mul]
          rw [hmid, zero_add, hF_coeff 0 (by omega), hF_coeff (N + 1) (le_refl _),
              Nat.sub_zero, Nat.sub_self]
          have hP0 : PowerSeries.coeff 0 P = 1 := by
            rw [hM 0 (Nat.zero_le N), expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
          simp only [↓reduceIte, Nat.succ_ne_zero, one_mul, hP0, mul_one]
          rw [hzP, hzE]
          simp only [m, Int.cast_sub]
          ring
        · rw [Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range n,
                PowerSeries.coeff (k + 1) (eulerFactor (N + 1) m) * PowerSeries.coeff (n - (k + 1)) P = 0 := by
            refine Finset.sum_eq_zero fun k hk => ?_
            have hkl : k < n := Finset.mem_range.mp hk
            rw [hF_coeff (k + 1) (by omega), if_neg (Nat.succ_ne_zero k),
                if_neg (by omega : k + 1 ≠ N + 1), zero_mul]
          rw [htail, zero_add, hF_coeff 0 (by omega), Nat.sub_zero]
          simp only [↓reduceIte, one_mul]
          exact hM n (by omega)
  -- Define `M_nat n` by extracting `M_N n` from `hM_exists n` (it is unique for `d ≤ N`)!
  -- Actually we can show that for any `N` and `M` from `hM_exists N`,
  -- `C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d` for all `1 ≤ n ≤ N`!
  -- Even cleaner: prove `∀ N, ∃ M : ℕ → ℤ, ∀ n, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, d * M d`,
  -- AND note `M d` is uniquely determined by `C` (Möbius inversion / strong recursion)!
  have hM_div : ∀ (N : ℕ) (M : ℕ → ℤ),
      (∀ n ≤ N, PowerSeries.coeff n (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
        PowerSeries.coeff n (expLogSeries C)) →
      ∀ n : ℕ, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d := by
    intro N M hM n hn1 hnN
    induction n using Nat.strong_induction_on with
    | h n ih =>
      set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
      have hP_ode := congr_arg (PowerSeries.coeff n) (prod_eulerFactor_ode N M)
      have hE_ode := congr_arg (PowerSeries.coeff n) (expLogSeries_ode C)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at hP_ode hE_ode
      rw [hM (m + 1) hnN] at hP_ode
      have heq := hP_ode.symm.trans hE_ode
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i P *
              PowerSeries.coeff j (∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0)),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (expLogSeries C) *
              PowerSeries.coeff j (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)))] at heq
      conv_lhs at heq => rw [Finset.sum_range_succ']
      conv_rhs at heq => rw [Finset.sum_range_succ']
      have htail :
          ∑ k ∈ Finset.range (m + 1),
            PowerSeries.coeff (k + 1) P *
              PowerSeries.coeff (m + 1 - (k + 1)) (∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0) =
          ∑ k ∈ Finset.range (m + 1),
            PowerSeries.coeff (k + 1) (expLogSeries C) *
              PowerSeries.coeff (m + 1 - (k + 1)) (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkl : k < m + 1 := Finset.mem_range.mp hk
        rw [hM (k + 1) (by omega)]
        congr 1
        by_cases hkm : k = m
        · subst hkm; simp [map_sum]
        · have hpos : 1 ≤ m + 1 - (k + 1) := by omega
          have hne : m + 1 - (k + 1) ≠ 0 := by omega
          rw [map_sum, PowerSeries.coeff_mk]
          simp only [hne, ne_eq, not_false_eq_true, true_and, ↓reduceIte, PowerSeries.coeff_mk]
          rw [← Finset.sum_filter]
          have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ m + 1 - (k + 1)) =
              Nat.divisors (m + 1 - (k + 1)) := by
            ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
            constructor
            · intro ⟨_, hd⟩; exact ⟨hd, hne⟩
            · intro ⟨hd, _⟩
              exact ⟨⟨Nat.pos_of_dvd_of_pos hd hpos,
                le_trans (Nat.le_of_dvd hpos hd) (by omega)⟩, hd⟩
          rw [hfilt, ih (m + 1 - (k + 1)) (by omega) hpos (by omega), Int.cast_sum]
          refine Finset.sum_congr rfl fun d _ => by push_cast; ring
      rw [htail, Nat.sub_zero, hM 0 (Nat.zero_le N)] at heq
      have hE0 : PowerSeries.coeff 0 (expLogSeries C) = 1 := by simp [expLogSeries, expLogCoeffs]
      rw [hE0, one_mul, one_mul] at heq
      have hterm :
          PowerSeries.coeff (m + 1) (∑ d ∈ Finset.Icc 1 N,
            PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0) =
          PowerSeries.coeff (m + 1) (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)) := by
        linarith
      rw [map_sum, PowerSeries.coeff_mk] at hterm
      simp only [Nat.succ_ne_zero, ne_eq, not_false_eq_true, true_and, ↓reduceIte,
        PowerSeries.coeff_mk] at hterm
      rw [← Finset.sum_filter] at hterm
      have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ m + 1) = Nat.divisors (m + 1) := by
        ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · intro ⟨_, hd⟩; exact ⟨hd, Nat.succ_ne_zero m⟩
        · intro ⟨hd, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
            le_trans (Nat.le_of_dvd (by omega) hd) hnN⟩, hd⟩
      rw [hfilt] at hterm
      have hq : ((C (m + 1) : ℤ) : ℚ) = ((∑ d ∈ Nat.divisors (m + 1), (d : ℤ) * M d : ℤ) : ℚ) := by
        rw [Int.cast_sum, ← hterm]
        refine Finset.sum_congr rfl fun d _ => by push_cast; ring
      exact_mod_cast hq
  -- Global `M`: for each `d`, pick `M_d` from `hM_exists d` (and show `M_N d = M_d d` for all `d ≤ N`)!
  choose Mfam hMfam using hM_exists
  refine ⟨fun d => Mfam d d, fun n hn => ?_⟩
  have huniq : ∀ (N₁ N₂ : ℕ) (M₁ M₂ : ℕ → ℤ),
      (∀ k, 1 ≤ k → k ≤ N₁ → C k = ∑ d ∈ Nat.divisors k, (d : ℤ) * M₁ d) →
      (∀ k, 1 ≤ k → k ≤ N₂ → C k = ∑ d ∈ Nat.divisors k, (d : ℤ) * M₂ d) →
      ∀ d, 1 ≤ d → d ≤ N₁ → d ≤ N₂ → M₁ d = M₂ d := by
    intro N₁ N₂ M₁ M₂ h1 h2 d hd1 hdN₁ hdN₂
    induction d using Nat.strong_induction_on with
    | h d ih =>
      have heq := (h1 d hd1 hdN₁).symm.trans (h2 d hd1 hdN₂)
      have hmem : d ∈ Nat.divisors d := Nat.mem_divisors.mpr ⟨dvd_refl d, by omega⟩
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at heq
      have hrest :
          ∑ x ∈ (Nat.divisors d).erase d, (x : ℤ) * M₁ x =
          ∑ x ∈ (Nat.divisors d).erase d, (x : ℤ) * M₂ x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : x ≠ d := (Finset.mem_erase.mp hx).1
        have hxd : x ∣ d := (Nat.mem_divisors.mp (Finset.mem_erase.mp hx).2).1
        have hx1 : 1 ≤ x := Nat.pos_of_dvd_of_pos hxd (by omega)
        have hxlt : x < d := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hxd) hne
        rw [ih x hxlt hx1 (by omega) (by omega)]
      rw [hrest] at heq
      have hmul : (d : ℤ) * M₁ d = (d : ℤ) * M₂ d := by linarith
      exact mul_left_cancel₀ (by omega : (d : ℤ) ≠ 0) hmul
  have hn_eq := hM_div n (Mfam n) (hMfam n) n hn (le_refl n)
  rw [hn_eq]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
  congr 1
  exact huniq n d (Mfam n) (Mfam d)
    (hM_div n (Mfam n) (hMfam n)) (hM_div d (Mfam d) (hMfam d)) d hd1 hdle (le_refl d)

/-- Gauss congruence from Euler decomposition:
if `C n = ∑_{d ∣ n} d * M d`, then `p^r ∣ (C (p^r * m) - C (p^(r-1) * m))` for `p` prime, `r ≥ 1`, `p ∤ m`. -/
private lemma gauss_cong_of_euler_decomp (C M : ℕ → ℤ)
    (hCM : ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d)
    {p r m : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)) := by
  have hpos1 : 1 ≤ p ^ r * m := Nat.mul_pos (pow_pos hp.pos r) hm
  have hpos2 : 1 ≤ p ^ (r - 1) * m := Nat.mul_pos (pow_pos hp.pos (r - 1)) hm
  rw [hCM _ hpos1, hCM _ hpos2]
  have hsub : Nat.divisors (p ^ (r - 1) * m) ⊆ Nat.divisors (p ^ r * m) := by
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    refine Nat.mem_divisors.mpr ⟨dvd_trans hdiv ?_, by omega⟩
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow p (by omega)) m
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.dvd_sum fun d hd => ?_
  have hmem1 := (Finset.mem_sdiff.mp hd).1
  have hnot2 := (Finset.mem_sdiff.mp hd).2
  have hd_div : d ∣ p ^ r * m := (Nat.mem_divisors.mp hmem1).1
  have hd_ndiv : ¬ d ∣ p ^ (r - 1) * m := fun h => hnot2 (Nat.mem_divisors.mpr ⟨h, by omega⟩)
  have hpr_dvd : p ^ r ∣ d := by
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_div hpos1
    have hcop : Nat.Coprime (p ^ r) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left r
    -- Write `d = g * u` where `g = gcd(d, p^r)` divides `p^r` and `u` divides `m`!
    obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hd_div
    have hpow := (Nat.dvd_prime_pow hp).mp ha
    obtain ⟨k, hk, rfl⟩ := hpow
    by_cases hkr : k = r
    · subst hkr; exact dvd_mul_right (p ^ k) b
    · exfalso; apply hd_ndiv
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) hb
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpr_dvd) (M d)

/-- Binomial lifting: for any `b : ℤ`, prime `p`, `r ≥ 1`, `p^r ∣ (b^(p^r) - b^(p^(r-1)))`. -/

theorem main_proof :
    ∀ a : ℕ → ℕ,
      (∀ n : ℕ, 1 ≤ n → a n < n) →
      isIntegerSeries (expLogSeries fun n => (n : ℤ) ^ 2 - (a n : ℤ)) →
      ∀ p n : ℕ, p.Prime → 1 ≤ n → a (p ^ n) = p - 1 := by
  intro a hlt hint p n hp hn
  set C : ℕ → ℤ := fun k => (k : ℤ) ^ 2 - (a k : ℤ)
  obtain ⟨M, hM⟩ := exists_euler_decomp_of_isIntegerSeries C hint
  have hgauss : ∀ (p r : ℕ), p.Prime → 1 ≤ r →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r) - C (p ^ (r - 1))) := fun p r hp hr => by
    simpa [mul_one] using gauss_cong_of_euler_decomp C M hM (p := p) (r := r) (m := 1) hp hr (le_refl 1) hp.not_dvd_one
  have ha1 : a 1 = 0 := by have := hlt 1 (le_refl 1); omega
  induction n with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          have h1 := hgauss p 1 hp (le_refl 1)
          simp only [pow_one, pow_zero, Nat.sub_self, C, ha1, Nat.cast_zero, sub_zero] at h1
          have hltp : a p < p := hlt p hp.one_le
          have hdvd_p : (p : ℤ) ∣ ((a p : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
            have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
              have := hp.one_le; omega
            rw [hp1]
            have h2 : (p : ℤ) ∣ ((p : ℤ) ^ 2 - (p : ℤ)) := ⟨(p : ℤ) - 1, by ring⟩
            have h3 := dvd_sub h2 h1
            rwa [show ((p : ℤ) ^ 2 - (p : ℤ)) - ((p : ℤ) ^ 2 - (a p : ℤ) - ((1 : ℕ) : ℤ) ^ 2) =
                (a p : ℤ) - ((p : ℤ) - 1) by push_cast; ring] at h3
          obtain ⟨q, hq⟩ := hdvd_p
          have hq0 : q = 0 := by
            have hlt1 : (a p : ℤ) < (p : ℤ) := by exact_mod_cast hltp
            have hge0 : (0 : ℤ) ≤ (a p : ℤ) := Int.natCast_nonneg _
            have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
            have hlt2 : ((p - 1 : ℕ) : ℤ) < (p : ℤ) := by have := hp.one_le; omega
            have hge2 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := Int.natCast_nonneg _
            nlinarith
          have heq : (a p : ℤ) = ((p - 1 : ℕ) : ℤ) := by rw [hq0, mul_zero] at hq; linarith
          rw [zero_add, pow_one]
          exact_mod_cast heq
      | succ k =>
          have hprev : a (p ^ (k + 1)) = p - 1 := ih (by omega)
          have hstep := hgauss p (k + 2) hp (by omega)
          simp only [C] at hstep
          rw [show k + 2 - 1 = k + 1 by omega, hprev] at hstep
          have hsq1 : ((p ^ (k + 2) : ℕ) : ℤ) ∣ (((p ^ (k + 2) : ℕ) : ℤ) ^ 2) := dvd_pow_self _ (by omega)
          have hsq2 : ((p ^ (k + 2) : ℕ) : ℤ) ∣ (((p ^ (k + 1) : ℕ) : ℤ) ^ 2) := by
            have hle : k + 2 ≤ 2 * (k + 1) := by omega
            have hnat : p ^ (k + 2) ∣ (p ^ (k + 1)) ^ 2 := by
              rw [← pow_mul, mul_comm (k + 1) 2]
              exact Nat.pow_dvd_pow p hle
            exact_mod_cast hnat
          have hdvd_diff : ((p ^ (k + 2) : ℕ) : ℤ) ∣ ((a (p ^ (k + 2)) : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
            have h1 := dvd_sub (dvd_sub hsq1 hsq2) hstep
            rwa [show (((p ^ (k + 2) : ℕ) : ℤ) ^ 2 - ((p ^ (k + 1) : ℕ) : ℤ) ^ 2) -
                ((((p ^ (k + 2) : ℕ) : ℤ) ^ 2 - (a (p ^ (k + 2)) : ℤ)) -
                  (((p ^ (k + 1) : ℕ) : ℤ) ^ 2 - ((p - 1 : ℕ) : ℤ))) =
                (a (p ^ (k + 2)) : ℤ) - ((p - 1 : ℕ) : ℤ) by ring] at h1
          have hlt_pk : a (p ^ (k + 2)) < p ^ (k + 2) := hlt _ (Nat.one_le_pow _ _ hp.pos)
          have hlt_p1 : p - 1 < p ^ (k + 2) := by
            have : p ≤ p ^ (k + 2) := Nat.le_self_pow (by omega) p
            have := hp.two_le; omega
          obtain ⟨q, hq⟩ := hdvd_diff
          have hq0 : q = 0 := by
            have h1 : (a (p ^ (k + 2)) : ℤ) < ((p ^ (k + 2) : ℕ) : ℤ) := by exact_mod_cast hlt_pk
            have h2 : ((p - 1 : ℕ) : ℤ) < ((p ^ (k + 2) : ℕ) : ℤ) := by exact_mod_cast hlt_p1
            have h3 : (0 : ℤ) ≤ (a (p ^ (k + 2)) : ℤ) := Int.natCast_nonneg _
            have h4 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := Int.natCast_nonneg _
            nlinarith
          have heq : (a (p ^ (k + 2)) : ℤ) = ((p - 1 : ℕ) : ℤ) := by rw [hq0, mul_zero] at hq; linarith
          exact_mod_cast heq

end OMA.S_oeis_a384819

theorem OMA.solution : type_of% @OMA.S_oeis_a384819.main :=
  OMA.S_oeis_a384819.main_proof
