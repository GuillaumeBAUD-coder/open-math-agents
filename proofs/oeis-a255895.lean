import OMAStatements.S_oeis_a255895
import Mathlib

namespace OMA.S_oeis_a255895

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
private lemma pow_prime_pow_sub_dvd {p : ℕ} (hp : p.Prime) (b : ℤ) :
    ∀ r : ℕ, 1 ≤ r → ((p ^ r : ℕ) : ℤ) ∣ (b ^ (p ^ r) - b ^ (p ^ (r - 1)))
  | 0, h => by omega
  | 1, _ => by
      simp only [pow_one, Nat.sub_self, pow_zero]
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [ZMod.pow_card]
  | r + 2, _ => by
      have ih := pow_prime_pow_sub_dvd hp b (r + 1) (by omega)
      simp only [Nat.add_sub_cancel] at ih ⊢
      obtain ⟨t, ht⟩ := ih
      set u : ℤ := b ^ (p ^ r)
      have hbu : b ^ (p ^ (r + 1)) = u + ((p ^ (r + 1) : ℕ) : ℤ) * t := by linarith
      have hpow1 : b ^ (p ^ (r + 2)) = (b ^ (p ^ (r + 1))) ^ p := by
        rw [← pow_mul, ← pow_succ]
      have hpow2 : b ^ (p ^ (r + 1)) = u ^ p := by
        simp only [u, ← pow_mul, ← pow_succ]
      have hr2 : r + 2 - 1 = r + 1 := by omega
      rw [hr2, hpow1]
      nth_rw 1 [hbu]
      rw [add_comm u, add_pow, Finset.sum_range_succ', Nat.sub_zero, ← hpow2]
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
        add_sub_cancel_right]
      refine Finset.dvd_sum fun j hj => ?_
      have hjlt : j < p := Finset.mem_range.mp hj
      by_cases hjp : j + 1 = p
      · rw [hjp]
        have hdvd : ((p ^ (r + 2) : ℕ) : ℤ) ∣ (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ p := by
          rw [mul_pow, ← Nat.cast_pow, ← pow_mul]
          refine dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p ?_)) _
          have hp2 : 2 ≤ p := hp.two_le
          nlinarith
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
      · have hch : p ∣ Nat.choose p (j + 1) := hp.dvd_choose_self (by omega) (by omega)
        have hch_z : (p : ℤ) ∣ (Nat.choose p (j + 1) : ℤ) := Int.natCast_dvd_natCast.mpr hch
        have hpow_z : ((p ^ (r + 1) : ℕ) : ℤ) ∣ (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) := by
          conv_rhs => rw [pow_succ']
          exact dvd_mul_of_dvd_left (dvd_mul_right _ t) _
        have hprod : ((p ^ (r + 2) : ℕ) : ℤ) ∣
            (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * (Nat.choose p (j + 1) : ℤ) := by
          rw [pow_succ, Nat.cast_mul]
          exact mul_dvd_mul hpow_z hch_z
        have hre : (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * u ^ (p - (j + 1)) *
            (Nat.choose p (j + 1) : ℤ) =
            u ^ (p - (j + 1)) * ((((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * (Nat.choose p (j + 1) : ℤ)) := by
          ring
        rw [hre]
        exact dvd_mul_of_dvd_right hprod _

/-- Gauss congruence for `C' n = (C n)^n` when `C` satisfies the Gauss congruence! -/
private lemma gauss_cong_pow_self (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)))
    {p r m : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    ((p ^ r : ℕ) : ℤ) ∣
      ((C (p ^ r * m)) ^ (p ^ r * m) - (C (p ^ (r - 1) * m)) ^ (p ^ (r - 1) * m)) := by
  set a := C (p ^ r * m)
  set b := C (p ^ (r - 1) * m)
  have hab : ((p ^ r : ℕ) : ℤ) ∣ (a - b) := hC hp hr hm hpm
  have h1 : ((p ^ r : ℕ) : ℤ) ∣ (a ^ (p ^ r * m) - b ^ (p ^ r * m)) :=
    dvd_trans hab (sub_dvd_pow_sub_pow a b (p ^ r * m))
  have h2 : ((p ^ r : ℕ) : ℤ) ∣ (b ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m)) := by
    rw [pow_mul, pow_mul]
    exact dvd_trans (pow_prime_pow_sub_dvd hp b r hr) (sub_dvd_pow_sub_pow _ _ m)
  have hsum : a ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m) =
      (a ^ (p ^ r * m) - b ^ (p ^ r * m)) + (b ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m)) := by ring
  rw [hsum]
  exact dvd_add h1 h2

/-- Divisibility of the Möbius convolution by `d` from Gauss congruences:
if `C` satisfies Gauss congruences at all prime powers, then
`d ∣ ∑_{k ∣ d} μ(d / k) * C(k)` for every `d ≥ 1`! -/
private lemma dvd_moebius_sum_of_gauss_cong (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)))
    (d : ℕ) (hd : 1 ≤ d) :
    (d : ℤ) ∣ ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k := by
  -- Suffices to show `p^r ∣ sum` for every prime power `p^r ‖ d`, by strong induction on `d`!
  -- Better: use `Nat.Coprime` decomposition `d = p^r * u` with `p ∤ u`!
  have hprime_pow : ∀ {p r u : ℕ}, p.Prime → 1 ≤ r → 1 ≤ u → ¬ p ∣ u →
      ((p ^ r : ℕ) : ℤ) ∣
        ∑ k ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius (p ^ r * u / k) : ℤ) * C k := by
    intro p r u hp hr hu hpu
    -- Reindex by `t = d / k` (`∑_{t ∣ d} μ(t) * C(d / t)`)!
    have hreidx :
        ∑ k ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius (p ^ r * u / k) : ℤ) * C k =
        ∑ t ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius t : ℤ) * C (p ^ r * u / t) := by
      refine Finset.sum_nbij (fun k => p ^ r * u / k) ?_ ?_ ?_ ?_
      · intro k hk
        have hkd := (Nat.mem_divisors.mp hk).1
        exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hkd, Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have h1 := (Nat.mem_divisors.mp hk₁).1
        have h2 := (Nat.mem_divisors.mp hk₂).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        have h1' : k₁ * (p ^ r * u / k₁) = p ^ r * u := Nat.mul_div_cancel' h1
        have h2' : k₂ * (p ^ r * u / k₂) = p ^ r * u := Nat.mul_div_cancel' h2
        have hdiv_pos : 0 < p ^ r * u / k₁ := Nat.div_pos (Nat.le_of_dvd hpos h1) (Nat.pos_of_dvd_of_pos h1 hpos)
        dsimp at heq
        rw [← heq] at h2'
        exact Nat.eq_of_mul_eq_mul_right hdiv_pos (h1'.trans h2'.symm)
      · intro t ht
        have htd := (Nat.mem_divisors.mp ht).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        refine ⟨p ^ r * u / t, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd htd,
          Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩, ?_⟩
        exact Nat.div_div_self htd (by omega)
      · intro k hk
        have hkd := (Nat.mem_divisors.mp hk).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        rw [Nat.div_div_self hkd (by omega)]
    rw [hreidx]
    -- Reindex `t ∈ divisors (p^r * u)` as `(i, s) ∈ range (r + 1) ×ˢ divisors u` via `(i, s) ↦ p^i * s`!
    have hsplit :
        ∑ t ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius t : ℤ) * C (p ^ r * u / t) =
        ∑ x ∈ Finset.range (r + 1) ×ˢ Nat.divisors u,
          (ArithmeticFunction.moebius (p ^ x.1 * x.2) : ℤ) * C (p ^ r * u / (p ^ x.1 * x.2)) := by
      symm
      refine Finset.sum_nbij (fun x => p ^ x.1 * x.2) ?_ ?_ ?_ ?_
      · intro x hx
        have h1 : x.1 ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hx).1)
        have h2 : x.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx).2).1
        exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.pow_dvd_pow p h1) h2,
          Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        dsimp at heq
        have hs1 : x₁.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx₁).2).1
        have hs2 : x₂.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx₂).2).1
        have hnp1 : ¬ p ∣ x₁.2 := fun h => hpu (dvd_trans h hs1)
        have hnp2 : ¬ p ∣ x₂.2 := fun h => hpu (dvd_trans h hs2)
        have hi : x₁.1 = x₂.1 := by
          have h1 : (p ^ x₁.1 * x₁.2).factorization p = x₁.1 := by
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.pos_of_dvd_of_pos hs1 hu).ne',
                Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
                Nat.factorization_eq_zero_of_not_dvd hnp1, add_zero]
          have h2 : (p ^ x₂.1 * x₂.2).factorization p = x₂.1 := by
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.pos_of_dvd_of_pos hs2 hu).ne',
                Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
                Nat.factorization_eq_zero_of_not_dvd hnp2, add_zero]
          rw [← h1, heq, h2]
        have hs : x₁.2 = x₂.2 := by
          rw [hi] at heq
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos x₂.1) heq
        exact Prod.ext hi hs
      · intro t ht
        have htd : t ∣ p ^ r * u := (Nat.mem_divisors.mp ht).1
        obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp htd
        obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
        exact ⟨(i, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Nat.mem_divisors.mpr ⟨hb, by omega⟩⟩, rfl⟩
      · intro _ _; rfl
    rw [hsplit, Finset.sum_product_right]
    refine Finset.dvd_sum fun s hs => ?_
    have hsu : s ∣ u := (Nat.mem_divisors.mp hs).1
    have hps : ¬ p ∣ s := fun h => hpu (dvd_trans h hsu)
    have hcop_ps : Nat.Coprime p s := hp.coprime_iff_not_dvd.mpr hps
    have hus_pos : 1 ≤ u / s := Nat.div_pos (Nat.le_of_dvd hu hsu) (Nat.pos_of_dvd_of_pos hsu hu)
    have hpus : ¬ p ∣ u / s := fun h => hpu (dvd_trans h (Nat.div_dvd_of_dvd hsu))
    -- Split `range (r + 1)` into `i = 0`, `i = 1`, and `i ≥ 2` (where `moebius (p^i * s) = 0`)!
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    dsimp only
    simp only [Nat.succ_eq_add_one]
    have hzero :
        ∑ i ∈ Finset.range r',
          (ArithmeticFunction.moebius (p ^ (i + 1 + 1) * s) : ℤ) *
            C (p ^ (r' + 1) * u / (p ^ (i + 1 + 1) * s)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hnsq : ¬ Squarefree (p ^ (i + 1 + 1) * s) := by
        intro hsq
        have hp2 : p * p ∣ p ^ (i + 1 + 1) * s := by
          have : p * p ∣ p ^ (i + 1 + 1) := by
            rw [← sq]; exact Nat.pow_dvd_pow p (by omega)
          exact dvd_mul_of_dvd_left this s
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hp2))
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, zero_mul]
    rw [hzero, zero_add]
    have h0 : p ^ (r' + 1) * u / (p ^ 0 * s) = p ^ (r' + 1) * (u / s) := by
      rw [pow_zero, one_mul, Nat.mul_div_assoc _ hsu]
    have h1 : p ^ (r' + 1) * u / (p ^ 1 * s) = p ^ r' * (u / s) := by
      rw [pow_one, pow_succ', mul_assoc, Nat.mul_div_mul_left _ _ hp.pos, Nat.mul_div_assoc _ hsu]
    have hmu1 : (ArithmeticFunction.moebius (p ^ 1 * s) : ℤ) = -(ArithmeticFunction.moebius s : ℤ) := by
      rw [pow_one, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_ps,
          ArithmeticFunction.moebius_apply_prime hp]
      ring
    rw [zero_add, h0, h1, hmu1, pow_zero, one_mul]
    have hcomb : -(ArithmeticFunction.moebius s : ℤ) * C (p ^ r' * (u / s)) +
        (ArithmeticFunction.moebius s : ℤ) * C (p ^ (r' + 1) * (u / s)) =
        (ArithmeticFunction.moebius s : ℤ) *
          (C (p ^ (r' + 1) * (u / s)) - C (p ^ r' * (u / s))) := by ring
    rw [hcomb]
    have hstep : ((p ^ (r' + 1) : ℕ) : ℤ) ∣
        (C (p ^ (r' + 1) * (u / s)) - C (p ^ r' * (u / s))) := by
      simpa [Nat.add_sub_cancel] using hC hp (show 1 ≤ r' + 1 by omega) hus_pos hpus
    exact dvd_mul_of_dvd_right hstep _
  -- Combine all prime-power divisibilities via `Nat.prod_factorization_pow_eq_self`!
  have hd_ne : d ≠ 0 := by omega
  have hprod_eq : (∏ p ∈ d.primeFactors, ((p ^ d.factorization p : ℕ) : ℤ)) = (d : ℤ) := by
    rw [← Nat.cast_prod, ← Nat.support_factorization d]
    exact_mod_cast Nat.prod_factorization_pow_eq_self hd_ne
  rw [← hprod_eq]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    exact (((Nat.coprime_primes hp' hq').mpr hpq).pow _ _).isCoprime
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hr : 1 ≤ d.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hpow_dvd : p ^ d.factorization p ∣ d := Nat.ordProj_dvd d p
    set r := d.factorization p
    set u := d / p ^ r
    have hdu : p ^ r * u = d := Nat.mul_div_cancel' hpow_dvd
    have hu_pos : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hpow_dvd) (pow_pos hp'.pos r)
    have hpu : ¬ p ∣ u := by
      intro h
      have hpow1 : p ^ (r + 1) ∣ d := by
        rw [← hdu, pow_succ]
        exact Nat.mul_dvd_mul_left (p ^ r) h
      have hle := (hp'.pow_dvd_iff_le_factorization hd_ne).mp hpow1
      omega
    rw [← hdu]
    exact hprime_pow hp' hr hu_pos hpu

/-- **Direction ⇐ (Gauss congruence version)**:
if `C` satisfies Gauss congruences at all prime powers, then `expLogSeries C` has integer coefficients! -/
private lemma isIntegerSeries_of_gauss_cong (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m))) :
    isIntegerSeries (expLogSeries C) := by
  let M : ℕ → ℤ := fun d =>
    if d = 0 then 0 else (∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k) / (d : ℤ)
  apply isIntegerSeries_of_euler_decomp C M
  intro n hn
  have hd_mul : ∀ d ∈ Nat.divisors n,
      (d : ℤ) * M d = ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k := by
    intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
    simp only [M, show d ≠ 0 by omega, ↓reduceIte]
    exact Int.mul_ediv_cancel' (dvd_moebius_sum_of_gauss_cong C hC d hd1)
  rw [Finset.sum_congr rfl hd_mul]
  -- Apply Möbius inversion: `∑_{d ∣ n} ∑_{k ∣ d} μ(d / k) * C(k) = C(n)`!
  -- Rewrite as `∑_{k ∣ n} C(k) * (∑_{t ∣ n / k} μ(t))` and use `∑_{t ∣ m} μ(t) = [m = 1]`!
  have hswap :
      ∑ d ∈ Nat.divisors n, ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k =
      ∑ k ∈ Nat.divisors n, C k * ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) := by
    have h1 :
        ∑ d ∈ Nat.divisors n, ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k =
        ∑ p ∈ (Nat.divisors n).sigma Nat.divisors, (ArithmeticFunction.moebius (p.1 / p.2) : ℤ) * C p.2 :=
      Finset.sum_sigma' (Nat.divisors n) Nat.divisors
        (fun d k => (ArithmeticFunction.moebius (d / k) : ℤ) * C k)
    have h2 :
        ∑ k ∈ Nat.divisors n, C k * ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) =
        ∑ p ∈ (Nat.divisors n).sigma (fun k => Nat.divisors (n / k)),
          C p.1 * (ArithmeticFunction.moebius p.2 : ℤ) := by
      rw [← Finset.sum_sigma' (Nat.divisors n) (fun k => Nat.divisors (n / k))
        (fun k t => C k * (ArithmeticFunction.moebius t : ℤ))]
      refine Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    rw [h1, h2]
    refine Finset.sum_nbij (fun p => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      have hd := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp).1).1
      have hk := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp).2).1
      have hkn : p.2 ∣ n := dvd_trans hk hd
      have hpos : 0 < p.2 := Nat.pos_of_dvd_of_pos hkn (by omega)
      have hdiv_pos : 0 < n / p.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hpos
      refine Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨hkn, by omega⟩,
        Nat.mem_divisors.mpr ⟨?_, Nat.ne_of_gt hdiv_pos⟩⟩
      obtain ⟨c, hc⟩ := hd
      obtain ⟨e, he⟩ := hk
      refine ⟨c, ?_⟩
      rw [hc, he, mul_assoc, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]
    · intro p₁ hp₁ p₂ hp₂ heq
      have hk1 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp₁).2).1
      have hk2 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp₂).2).1
      have h2eq : p₁.2 = p₂.2 := congr_arg Sigma.fst heq
      have hdiv : p₁.1 / p₁.2 = p₂.1 / p₂.2 := by
        simpa [h2eq] using (Sigma.mk.inj_iff.mp heq).2
      have h1eq : p₁.1 = p₂.1 := by
        rw [← Nat.mul_div_cancel' hk1, ← Nat.mul_div_cancel' hk2, hdiv, h2eq]
      exact Sigma.ext h1eq (heq_of_eq h2eq)
    · intro q hq
      have hkn := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hq).1).1
      have htn := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hq).2).1
      have hpos : 0 < q.1 := Nat.pos_of_dvd_of_pos hkn (by omega)
      refine ⟨⟨q.1 * q.2, q.1⟩, Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨?_, by omega⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right q.1 q.2, by
          have htpos : 0 < q.2 := Nat.pos_of_dvd_of_pos htn (Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hpos)
          positivity⟩⟩, ?_⟩
      · have := Nat.mul_dvd_mul_left q.1 htn
        rwa [Nat.mul_div_cancel' hkn] at this
      · ext
        · rfl
        · exact heq_of_eq (Nat.mul_div_cancel_left q.2 hpos)
    · intro p _; ring
  rw [hswap, Finset.sum_eq_single n]
  · rw [Nat.div_self (by omega)]; simp
  · intro k hk hne
    have hkn := (Nat.mem_divisors.mp hk).1
    have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hkn (by omega)
    have hdiv_gt : n / k ≠ 1 := by
      intro h1
      have := Nat.mul_div_cancel' hkn
      rw [h1, mul_one] at this
      exact hne this
    have hmu0 : ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) = 0 := by
      have h := congr_arg (fun f : ArithmeticFunction ℤ => f (n / k))
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg hdiv_gt] at h
      rw [← h, Nat.sum_divisorsAntidiagonal
        (fun x y => ArithmeticFunction.moebius x * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) y)]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hdiv_pos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hk_pos
      have ht_dvd := (Nat.mem_divisors.mp ht).1
      have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos ht_dvd hdiv_pos
      have hq_pos : 0 < n / k / t := Nat.div_pos (Nat.le_of_dvd hdiv_pos ht_dvd) ht_pos
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq_pos.ne']
    rw [hmu0, mul_zero]
  · intro h; exfalso; exact h (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)


/-! ### Part 2: Explicit Finite-Difference Formula and Kummer + Stern Congruences for `A000364` -/

/-- Forward difference operator `(Δ^k f)(x) = ∑_{j=0}^k (-1)^(k-j) C(k, j) f(x + j)`. -/
private def fwdDiff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f, x => f x
  | k + 1, f, x => fwdDiff k f (x + 1) - fwdDiff k f x

private lemma fwdDiff_eq_sum (k : ℕ) (f : ℕ → ℤ) (x : ℕ) :
    fwdDiff k f x = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + j) := by
  induction k generalizing x with
  | zero => simp [fwdDiff]
  | succ k ih =>
      rw [fwdDiff, ih (x + 1), ih x]
      -- Combine the middle `j = 1..k` terms via Pascal's identity!
      have hmid1 : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + 1 + j) =
          f (x + (k + 1)) +
          ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + (j + 1)) := by
        rw [Finset.sum_range_succ, add_comm]
        simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
        congr 1
        · congr 1; omega
        · refine Finset.sum_congr rfl fun j _ => by congr 1; congr 1; omega
      have hmid2 : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + j) =
          (-1 : ℤ) ^ k * f x +
          ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k - (j + 1)) * (Nat.choose k (j + 1) : ℤ) * f (x + (j + 1)) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero]
      rw [hmid1, hmid2]
      conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
          Nat.sub_zero, Nat.choose_zero_right, mul_one, add_zero]
      have hsub : f (x + (k + 1)) +
          (∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + (j + 1))) -
          ((-1 : ℤ) ^ k * f x +
          ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k - (j + 1)) * (Nat.choose k (j + 1) : ℤ) * f (x + (j + 1))) =
          (∑ j ∈ Finset.range k,
            ((-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) - (-1 : ℤ) ^ (k - (j + 1)) * (Nat.choose k (j + 1) : ℤ)) *
              f (x + (j + 1))) +
          (-1 : ℤ) ^ (k + 1) * f x + f (x + (k + 1)) := by
        have h1 : ∀ j, ((-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) -
            (-1 : ℤ) ^ (k - (j + 1)) * (Nat.choose k (j + 1) : ℤ)) * f (x + (j + 1)) =
            (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * f (x + (j + 1)) -
            (-1 : ℤ) ^ (k - (j + 1)) * (Nat.choose k (j + 1) : ℤ) * f (x + (j + 1)) := fun j => by ring
        simp_rw [h1]
        rw [Finset.sum_sub_distrib, pow_succ]
        ring
      rw [hsub]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < k := Finset.mem_range.mp hj
      have hsign : (-1 : ℤ) ^ (k - j) = -((-1 : ℤ) ^ (k - (j + 1))) := by
        rw [show k - j = (k - (j + 1)) + 1 by omega, pow_succ]; ring
      have hch : (Nat.choose (k + 1) (j + 1) : ℤ) = (Nat.choose k j : ℤ) + (Nat.choose k (j + 1) : ℤ) := by
        exact_mod_cast Nat.choose_succ_succ k j
      rw [Nat.succ_sub_succ, hch, hsign]
      ring

private lemma fwdDiff_add (k : ℕ) (f g : ℕ → ℤ) (x : ℕ) :
    fwdDiff k (fun y => f y + g y) x = fwdDiff k f x + fwdDiff k g x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [fwdDiff, ih]; ring

private lemma fwdDiff_const_mul (k : ℕ) (c : ℤ) (f : ℕ → ℤ) (x : ℕ) :
    fwdDiff k (fun y => c * f y) x = c * fwdDiff k f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [fwdDiff, ih]; ring

private lemma fwdDiff_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℕ → ℤ) (x : ℕ) :
    fwdDiff k (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, fwdDiff k (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      induction k generalizing x with
      | zero => rfl
      | succ k ih => simp [fwdDiff, ih]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, fwdDiff_add, ih]

private lemma fwdDiff_zero_of_lt_deg :
    ∀ (d k : ℕ) (x : ℕ), d < k → fwdDiff k (fun y => (y : ℤ) ^ d) x = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ihd =>
      intro k x hdk
      cases k with
      | zero => omega
      | succ k =>
          rw [fwdDiff]
          have hstep : (fun y : ℕ => ((y + 1 : ℕ) : ℤ) ^ d - (y : ℤ) ^ d) =
              fun (y : ℕ) => ∑ i ∈ Finset.range d, (Nat.choose d i : ℤ) * (y : ℤ) ^ i := by
            funext y
            rw [Nat.cast_add, Nat.cast_one, add_pow, Finset.sum_range_succ]
            simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
            refine Finset.sum_congr rfl fun i _ => by ring
          have hrew : fwdDiff k (fun y => (y : ℤ) ^ d) (x + 1) - fwdDiff k (fun y => (y : ℤ) ^ d) x =
              fwdDiff k (fun y => ((y + 1 : ℕ) : ℤ) ^ d - (y : ℤ) ^ d) x := by
            have : ∀ m (g : ℕ → ℤ) z, fwdDiff m (fun y => g (y + 1) - g y) z =
                fwdDiff m g (z + 1) - fwdDiff m g z := by
              intro m; induction m with
              | zero => intro g z; rfl
              | succ m ihm => intro g z; simp only [fwdDiff, ihm]
            exact (this k (fun y => (y : ℤ) ^ d) x).symm
          rw [hrew, hstep, fwdDiff_sum]
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [fwdDiff_const_mul, ihd i (Finset.mem_range.mp hi) k x (by have := Finset.mem_range.mp hi; omega), mul_zero]

private lemma fwdDiff_poly_zero_of_lt (P : Polynomial ℤ) (k x : ℕ) (hdeg : P.natDegree < k) :
    fwdDiff k (fun y => P.eval (y : ℤ)) x = 0 := by
  have hP : (fun y : ℕ => P.eval (y : ℤ)) =
      fun (y : ℕ) => ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (y : ℤ) ^ i := by
    funext y
    rw [Polynomial.eval_eq_sum_range]
  rw [hP, fwdDiff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [fwdDiff_const_mul, fwdDiff_zero_of_lt_deg i k x (by have := Finset.mem_range.mp hi; omega), mul_zero]

private lemma fwdDiff_leibniz (k : ℕ) (u v : ℕ → ℤ) (x : ℕ) :
    fwdDiff k (fun y => u y * v y) x =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i) := by
  induction k generalizing x with
  | zero => simp [fwdDiff]
  | succ k ih =>
      rw [fwdDiff, ih (x + 1), ih x]
      -- Use `fwdDiff i u (x + 1) = fwdDiff (i + 1) u x + fwdDiff i u x`!
      have h1 : ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℤ) * fwdDiff i u (x + 1) * fwdDiff (k - i) v (x + 1 + i) =
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1))) +
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hstep : fwdDiff i u (x + 1) = fwdDiff (i + 1) u x + fwdDiff i u x := by
          simp [fwdDiff]
        have hx1 : x + 1 + i = x + (i + 1) := by omega
        have hx2 : x + i + 1 = x + (i + 1) := by omega
        rw [hx1, hx2, hstep]; ring
      rw [h1]
      have hdiff : (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i + 1)) -
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i)) =
          ∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k + 1 - i) v (x + i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [show k + 1 - i = (k - i) + 1 by omega, fwdDiff]; ring
      have hcomb : (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1))) +
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i + 1)) -
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k - i) v (x + i)) =
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1))) +
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℤ) * fwdDiff i u x * fwdDiff (k + 1 - i) v (x + i)) := by
        rw [← hdiff]; ring
      rw [hcomb]
      conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
      -- Split first sum at `k`, second sum at `0`:
      conv_lhs =>
        arg 1
        rw [Finset.sum_range_succ]
      conv_lhs =>
        arg 2
        rw [Finset.sum_range_succ']
      simp only [Nat.sub_self, Nat.sub_zero, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one,
          one_mul, add_zero, Nat.succ_sub_succ]
      have hmid : (∑ i ∈ Finset.range k,
            (Nat.choose k i : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1))) +
          (∑ i ∈ Finset.range k,
            (Nat.choose k (i + 1) : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1))) =
          ∑ i ∈ Finset.range k,
            (Nat.choose (k + 1) (i + 1) : ℤ) * fwdDiff (i + 1) u x * fwdDiff (k - i) v (x + (i + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hch : (Nat.choose (k + 1) (i + 1) : ℤ) = (Nat.choose k i : ℤ) + (Nat.choose k (i + 1) : ℤ) := by
          exact_mod_cast Nat.choose_succ_succ k i
        rw [hch]; ring
      linear_combination hmid

private lemma two_pow_dvd_fwdDiff_odd_pow (n k x : ℕ) :
    ((2 ^ k : ℕ) : ℤ) ∣ fwdDiff k (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ n) x := by
  induction k generalizing n x with
  | zero => simp [fwdDiff]
  | succ k ih =>
      rw [fwdDiff]
      have hstep : (fun y : ℕ => ((2 * (y + 1) + 1 : ℕ) : ℤ) ^ n - ((2 * y + 1 : ℕ) : ℤ) ^ n) =
          fun y => 2 * ∑ i ∈ Finset.range n,
            (Nat.choose n i : ℤ) * 2 ^ (n - 1 - i) * ((2 * y + 1 : ℕ) : ℤ) ^ i := by
        funext y
        have h2 : ((2 * (y + 1) + 1 : ℕ) : ℤ) = ((2 * y + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
        rw [h2, add_pow, Finset.sum_range_succ]
        simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i < n := Finset.mem_range.mp hi
        rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ]
        ring
      have hrew : fwdDiff k (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ n) (x + 1) -
            fwdDiff k (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ n) x =
          fwdDiff k (fun y => ((2 * (y + 1) + 1 : ℕ) : ℤ) ^ n - ((2 * y + 1 : ℕ) : ℤ) ^ n) x := by
        have : ∀ m (g : ℕ → ℤ) z, fwdDiff m (fun y => g (y + 1) - g y) z =
            fwdDiff m g (z + 1) - fwdDiff m g z := by
          intro m; induction m with
          | zero => intro g z; rfl
          | succ m ihm => intro g z; simp only [fwdDiff, ihm]
        exact (this k (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ n) x).symm
      rw [hrew, hstep, fwdDiff_const_mul, fwdDiff_sum, pow_succ, Nat.cast_mul, mul_comm ((2 ^ k : ℕ) : ℤ)]
      refine mul_dvd_mul (dvd_refl (2 : ℤ)) (Finset.dvd_sum fun i _ => ?_)
      rw [fwdDiff_const_mul]
      exact dvd_mul_of_dvd_right (ih i x) _

/-- Explicit finite-difference formula for Euler (secant) numbers `A000364(n)`:
`eulerSec n = (-1)^n * ∑_{k=0}^{2n} (-1/2)^k * fwdDiff k (fun j => (2j+1)^(2n)) 0`. -/
private lemma eulerSec_eq_fwdDiff_sum (n : ℕ) :
    (eulerSec n : ℚ) =
      (-1 : ℚ) ^ n *
        ∑ k ∈ Finset.range (2 * n + 1),
          ((-1 / 2 : ℚ) ^ k) * (fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n)) 0 : ℚ) := by
  -- Prove via formal power series `cosh(x) * S(x) = 1`!
  let expQ (c : ℚ) : PowerSeries ℚ :=
    PowerSeries.mk fun m => c ^ m / ((Nat.factorial m : ℕ) : ℚ)
  have hexpQ_mul : ∀ a b : ℚ, expQ a * expQ b = expQ (a + b) := by
    intro a b; apply PowerSeries.ext; intro m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (expQ a) * PowerSeries.coeff j (expQ b))]
    simp only [expQ, PowerSeries.coeff_mk]
    rw [add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hch : ((Nat.choose m i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ) * ((Nat.factorial (m - i) : ℕ) : ℚ) =
        ((Nat.factorial m : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial him
    have hfi : ((Nat.factorial i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hfmi : ((Nat.factorial (m - i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - i))
    have hfm : ((Nat.factorial m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hch_ne : ((Nat.choose m i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos him).ne'
    rw [← hch]; field_simp
  let U : PowerSeries ℚ := expQ 2 - 1
  have hU0 : PowerSeries.coeff 0 U = 0 := by simp [U, expQ]
  have hU_pow_lt : ∀ (k m : ℕ), m < k → PowerSeries.coeff m (U ^ k) = 0 := by
    intro k; induction k with
    | zero => intro m hm; omega
    | succ k ih =>
        intro m hm
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (U ^ k) * PowerSeries.coeff b U)]
        refine Finset.sum_eq_zero fun a ha => ?_
        have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hlt : a < k
        · rw [ih a hlt, zero_mul]
        · rw [show m - a = 0 by omega, hU0, mul_zero]
  have hU_pow_coeff : ∀ (k m : ℕ),
      PowerSeries.coeff m (expQ 1 * U ^ k) =
        (fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ m) 0 : ℚ) / ((Nat.factorial m : ℕ) : ℚ) := by
    intro k m
    have hexp_pow : expQ 1 * U ^ k =
        ∑ j ∈ Finset.range (k + 1),
          PowerSeries.C ((-1 : ℚ) ^ (k - j) * (Nat.choose k j : ℚ)) * expQ ((2 * j + 1 : ℕ) : ℚ) := by
      simp only [U, sub_eq_add_neg, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hpow : ∀ t : ℕ, (expQ 2) ^ t = expQ ((2 * t : ℕ) : ℚ) := by
        intro t
        induction t with
        | zero => apply PowerSeries.ext; intro r; cases r <;> simp [expQ]
        | succ t iht =>
            rw [pow_succ, iht, hexpQ_mul]; congr 1; push_cast; ring
      rw [hpow j, show (-1 : PowerSeries ℚ) ^ (k - j) = PowerSeries.C ((-1 : ℚ) ^ (k - j)) by
        rw [map_pow, map_neg, map_one],
        show ((Nat.choose k j : ℕ) : PowerSeries ℚ) = PowerSeries.C ((Nat.choose k j : ℕ) : ℚ) by
        rw [map_natCast]]
      have hmul : expQ 1 * expQ ((2 * j : ℕ) : ℚ) = expQ ((2 * j + 1 : ℕ) : ℚ) := by
        rw [hexpQ_mul]; congr 1; push_cast; ring
      calc expQ 1 * (expQ ((2 * j : ℕ) : ℚ) * PowerSeries.C ((-1 : ℚ) ^ (k - j)) *
              PowerSeries.C ((Nat.choose k j : ℕ) : ℚ))
          = PowerSeries.C ((-1 : ℚ) ^ (k - j) * (Nat.choose k j : ℚ)) * (expQ 1 * expQ ((2 * j : ℕ) : ℚ)) := by
              rw [map_mul]; ring
        _ = PowerSeries.C ((-1 : ℚ) ^ (k - j) * (Nat.choose k j : ℚ)) * expQ ((2 * j + 1 : ℕ) : ℚ) := by
              rw [hmul]
    rw [hexp_pow, map_sum, fwdDiff_eq_sum]
    simp only [PowerSeries.coeff_C_mul, expQ, PowerSeries.coeff_mk, zero_add, Int.cast_sum,
        Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => by ring
  let S : PowerSeries ℚ := PowerSeries.mk fun m =>
    ∑ k ∈ Finset.range (m + 1), ((-1 / 2 : ℚ) ^ k) * PowerSeries.coeff m (expQ 1 * U ^ k)
  let coshQ : PowerSeries ℚ := PowerSeries.C (1 / 2 : ℚ) * (expQ 1 + expQ (-1))
  have hcosh_mul_S : coshQ * S = 1 := by
    apply PowerSeries.ext; intro m
    let SN : PowerSeries ℚ := ∑ k ∈ Finset.range (m + 1), PowerSeries.C ((-1 / 2 : ℚ) ^ k) * (expQ 1 * U ^ k)
    have hagree : ∀ j ≤ m, PowerSeries.coeff j S = PowerSeries.coeff j SN := by
      intro j hj
      simp only [S, SN, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul]
      refine Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ m + 1)) fun k hk hnot => ?_
      simp only [Finset.mem_range] at hk hnot
      have h0 : PowerSeries.coeff j (expQ 1 * U ^ k) = 0 := by
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => PowerSeries.coeff a (expQ 1) * PowerSeries.coeff b (U ^ k))]
        refine Finset.sum_eq_zero fun a ha => ?_
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [hU_pow_lt k (j - a) (by omega), mul_zero]
      rw [h0, mul_zero]
    have hmul_agree : PowerSeries.coeff m (coshQ * S) = PowerSeries.coeff m (coshQ * SN) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a coshQ * PowerSeries.coeff b S),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a coshQ * PowerSeries.coeff b SN)]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [hagree (m - a) (by omega)]
    rw [hmul_agree]
    -- `coshQ * expQ 1 = (1/2) * (expQ 2 + 1) = 1 + (1/2) * U`!
    have hce : coshQ * expQ 1 = 1 + PowerSeries.C (1 / 2 : ℚ) * U := by
      simp only [coshQ, U]
      have h1 : expQ 1 * expQ 1 = expQ 2 := by rw [hexpQ_mul]; norm_num
      have h2 : expQ (-1) * expQ 1 = 1 := by
        rw [hexpQ_mul]; simp only [neg_add_cancel]
        apply PowerSeries.ext; intro r; cases r <;> simp [expQ]
      calc PowerSeries.C (1 / 2 : ℚ) * (expQ 1 + expQ (-1)) * expQ 1
          = PowerSeries.C (1 / 2 : ℚ) * (expQ 1 * expQ 1 + expQ (-1) * expQ 1) := by ring
        _ = PowerSeries.C (1 / 2 : ℚ) * (expQ 2 + 1) := by rw [h1, h2]
        _ = 1 + PowerSeries.C (1 / 2 : ℚ) * (expQ 2 - 1) := by
              have hhalf : PowerSeries.C (1 / 2 : ℚ) * (2 : PowerSeries ℚ) = 1 := by
                rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) by rw [map_ofNat], ← map_mul]; norm_num
              linear_combination hhalf
    have hgeom : coshQ * SN = 1 - PowerSeries.C ((-1 / 2 : ℚ) ^ (m + 1)) * U ^ (m + 1) := by
      have h1 : coshQ * SN = (1 - PowerSeries.C (-1 / 2 : ℚ) * U) *
          ∑ k ∈ Finset.range (m + 1), (PowerSeries.C (-1 / 2 : ℚ) * U) ^ k := by
        simp only [SN, Finset.mul_sum]
        have hfac : ∀ k, coshQ * (PowerSeries.C ((-1 / 2 : ℚ) ^ k) * (expQ 1 * U ^ k)) =
            (1 - PowerSeries.C (-1 / 2 : ℚ) * U) * (PowerSeries.C (-1 / 2 : ℚ) * U) ^ k := by
          intro k
          rw [mul_pow, ← map_pow]
          have hneg : PowerSeries.C (1 / 2 : ℚ) = -PowerSeries.C (-1 / 2 : ℚ) := by
            rw [← map_neg]; congr 1; norm_num
          calc coshQ * (PowerSeries.C ((-1 / 2 : ℚ) ^ k) * (expQ 1 * U ^ k))
              = (coshQ * expQ 1) * (PowerSeries.C ((-1 / 2 : ℚ) ^ k) * U ^ k) := by ring
            _ = (1 + PowerSeries.C (1 / 2 : ℚ) * U) * (PowerSeries.C ((-1 / 2 : ℚ) ^ k) * U ^ k) := by rw [hce]
            _ = (1 - PowerSeries.C (-1 / 2 : ℚ) * U) * (PowerSeries.C ((-1 / 2 : ℚ) ^ k) * U ^ k) := by
                  rw [hneg]; ring
        exact Finset.sum_congr rfl fun k _ => hfac k
      rw [h1]
      have hgs := geom_sum_mul (PowerSeries.C (-1 / 2 : ℚ) * U) (m + 1)
      rw [mul_pow, ← map_pow] at hgs
      linear_combination -hgs
    rw [hgeom, map_sub, PowerSeries.coeff_C_mul, hU_pow_lt (m + 1) m (by omega), mul_zero, sub_zero]
  -- Now show `eulerSec n = (-1)^n * (2n)! * coeff (2n) S` by strong induction on `n`!
  have hS_odd : ∀ r : ℕ, PowerSeries.coeff (2 * r + 1) S = 0 := by
    intro r
    -- `coshQ` is even, so `S` is even (by induction on `r`)!
    induction r using Nat.strong_induction_on with
    | h r ih =>
        have h0 := congrArg (PowerSeries.coeff (2 * r + 1)) hcosh_mul_S
        rw [PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a coshQ * PowerSeries.coeff b S)] at h0
        have hcosh_odd : ∀ t, PowerSeries.coeff (2 * t + 1) coshQ = 0 := fun t => by
          simp only [coshQ, PowerSeries.coeff_C_mul, map_add, expQ, PowerSeries.coeff_mk, one_pow,
              Odd.neg_one_pow ⟨t, rfl⟩]
          ring
        have hcosh0 : PowerSeries.coeff 0 coshQ = 1 := by
          simp only [coshQ, PowerSeries.coeff_C_mul, map_add, expQ, PowerSeries.coeff_mk]; norm_num
        rw [Finset.sum_range_succ', Nat.sub_zero, hcosh0, one_mul] at h0
        have hrest0 : ∑ x ∈ Finset.range (2 * r + 1),
            PowerSeries.coeff (x + 1) coshQ * PowerSeries.coeff (2 * r + 1 - (x + 1)) S = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxr : x < 2 * r + 1 := Finset.mem_range.mp hx
          rcases Nat.even_or_odd (x + 1) with ⟨t, ht⟩ | ⟨t, ht⟩
          · have hodd : 2 * r + 1 - (x + 1) = 2 * (r - t) + 1 := by omega
            rw [hodd, ih (r - t) (by omega), mul_zero]
          · rw [ht, hcosh_odd t, zero_mul]
        rw [hrest0, zero_add] at h0
        exact h0
  have hS_even : ∀ m : ℕ, (eulerSec m : ℚ) =
      (-1 : ℚ) ^ m * ((Nat.factorial (2 * m) : ℕ) : ℚ) * PowerSeries.coeff (2 * m) S := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        cases m with
        | zero =>
            have h0 := congrArg (PowerSeries.coeff 0) hcosh_mul_S
            have hcosh0 : PowerSeries.coeff 0 coshQ = 1 := by
              simp only [coshQ, PowerSeries.coeff_C_mul, map_add, expQ, PowerSeries.coeff_mk]; norm_num
            rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
                ← PowerSeries.coeff_zero_eq_constantCoeff,
                hcosh0, one_mul, PowerSeries.coeff_one, if_pos rfl] at h0
            simp [eulerSec, h0]
        | succ m =>
            have h0 := congrArg (PowerSeries.coeff (2 * (m + 1))) hcosh_mul_S
            rw [PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a coshQ * PowerSeries.coeff b S)] at h0
            have hcosh_even : ∀ t, PowerSeries.coeff (2 * t) coshQ = 1 / ((Nat.factorial (2 * t) : ℕ) : ℚ) := fun t => by
              simp only [coshQ, PowerSeries.coeff_C_mul, map_add, expQ, PowerSeries.coeff_mk, one_pow,
                  Even.neg_one_pow (even_two_mul t)]
              ring
            have hcosh_odd : ∀ t, PowerSeries.coeff (2 * t + 1) coshQ = 0 := fun t => by
              simp only [coshQ, PowerSeries.coeff_C_mul, map_add, expQ, PowerSeries.coeff_mk, one_pow,
                  Odd.neg_one_pow ⟨t, rfl⟩]
              ring
            -- Keep only even indices `2 * j` for `j = 0..m+1`:
            have heven_sum : ∑ x ∈ Finset.range (2 * (m + 1) + 1),
                PowerSeries.coeff x coshQ * PowerSeries.coeff (2 * (m + 1) - x) S =
                ∑ j ∈ Finset.range (m + 2),
                  PowerSeries.coeff (2 * j) coshQ * PowerSeries.coeff (2 * (m + 1 - j)) S := by
              have hfilt : ∑ x ∈ Finset.range (2 * (m + 1) + 1),
                  PowerSeries.coeff x coshQ * PowerSeries.coeff (2 * (m + 1) - x) S =
                  ∑ x ∈ (Finset.range (2 * (m + 1) + 1)).filter (fun x => 2 ∣ x),
                    PowerSeries.coeff x coshQ * PowerSeries.coeff (2 * (m + 1) - x) S := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun x _ => ?_
                by_cases h2 : 2 ∣ x
                · rw [if_pos h2]
                · rw [if_neg h2]
                  have hodd : x = 2 * (x / 2) + 1 := by omega
                  rw [hodd, hcosh_odd (x / 2), zero_mul]
              rw [hfilt]
              symm
              refine Finset.sum_nbij (fun j => 2 * j) ?_ ?_ ?_ ?_
              · intro j hj
                simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
                exact ⟨by omega, dvd_mul_right 2 j⟩
              · intro a _ b _ hab; dsimp only at hab; omega
              · intro x hx
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
                obtain ⟨j, rfl⟩ := hx.2
                exact ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), rfl⟩
              · intro j hj
                simp only [Finset.mem_range] at hj
                rw [show 2 * (m + 1) - 2 * j = 2 * (m + 1 - j) by omega]
            rw [heven_sum, Finset.sum_range_succ'] at h0
            have hcosh0 : PowerSeries.coeff 0 coshQ = 1 := by simpa using hcosh_even 0
            simp only [mul_zero, Nat.sub_zero, hcosh0, one_mul] at h0
            -- Multiply by `(-1)^(m+1) * (2(m+1))!`:
            have hmul := congrArg (fun z : ℚ => (-1 : ℚ) ^ (m + 1) * ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) * z) h0
            rw [mul_zero, mul_add] at hmul
            have htarget : (-1 : ℚ) ^ (m + 1) * ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) *
                PowerSeries.coeff (2 * (m + 1)) S =
                -((-1 : ℚ) ^ (m + 1) * ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) *
                  ∑ j ∈ Finset.range (m + 1),
                    PowerSeries.coeff (2 * (j + 1)) coshQ * PowerSeries.coeff (2 * (m + 1 - (j + 1))) S) := by
              linarith
            rw [htarget, eulerSec, Int.cast_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
            -- Reindex `j ∈ range (m + 1)` by `k = m - j` (so `j + 1 = m + 1 - k`)!
            rw [Fin.sum_univ_eq_sum_range (fun k =>
              (((-1 : ℤ) ^ (m - k) * (Nat.choose (2 * (m + 1)) (2 * k) : ℤ) * eulerSec k : ℤ) : ℚ))]
            refine Finset.sum_nbij (fun k => m - k) ?_ ?_ ?_ ?_
            · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
            · intro a ha b hb hab
              simp only [Finset.mem_coe, Finset.mem_range] at ha hb
              dsimp only at hab; omega
            · intro j hj
              simp only [Finset.mem_coe, Finset.mem_range] at hj
              exact ⟨m - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
            · intro k hk
              simp only [Finset.mem_range] at hk
              have hsub1 : m + 1 - (m - k + 1) = k := by omega
              have hsub2 : 2 * (m - k + 1) = 2 * (m + 1) - 2 * k := by omega
              rw [hsub1, hcosh_even (m - k + 1), hsub2]
              have hih := ih k (by omega)
              have hch : ((Nat.choose (2 * (m + 1)) (2 * k) : ℕ) : ℚ) *
                  ((Nat.factorial (2 * k) : ℕ) : ℚ) * ((Nat.factorial (2 * (m + 1) - 2 * k) : ℕ) : ℚ) =
                  ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) := by
                exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : 2 * k ≤ 2 * (m + 1))
              have hfk : ((Nat.factorial (2 * k) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
              have hfk2 : ((Nat.factorial (2 * (m + 1) - 2 * k) : ℕ) : ℚ) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
              have hsign : -((-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ k) = (-1 : ℚ) ^ (m - k) := by
                have h1 : (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ k = (-1 : ℚ) ^ (m - k + 1 + 2 * k) := by
                  rw [← pow_add]; congr 1; omega
                rw [h1, pow_add, Even.neg_one_pow (even_two_mul k), mul_one, pow_succ]; ring
              push_cast
              rw [hih, ← hch, ← hsign]
              have hsq2 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, Even.neg_one_pow ⟨k, by ring⟩]
              field_simp
              rw [hsq2]; ring
  rw [hS_even n]
  simp only [S, PowerSeries.coeff_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hU_pow_coeff k (2 * n)]
  have hfn : ((Nat.factorial (2 * n) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Kummer + Stern Gauss congruence for Euler numbers `A000364(n + m)`:
`p^r ∣ (eulerSec (p^r * u + m) - eulerSec (p^(r-1) * u + m))` for every prime `p`, `r ≥ 1`, `u ≥ 1`, `m ≥ 0`! -/
private lemma eulerSec_gauss_cong (m : ℕ) {p r u : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hu : 1 ≤ u) :
    ((p ^ r : ℕ) : ℤ) ∣ (eulerSec (p ^ r * u + m) - eulerSec (p ^ (r - 1) * u + m)) := by
  set n1 := p ^ r * u + m
  set n2 := p ^ (r - 1) * u + m
  have hn2_le : n2 ≤ n1 := by
    have : p ^ (r - 1) ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
    simp only [n1, n2]; nlinarith
  have hE1 := eulerSec_eq_fwdDiff_sum n1
  have hE2 := eulerSec_eq_fwdDiff_sum n2
  -- Extend `hE2`'s sum to `2 * n1 + 1` since `fwdDiff k` of a degree `2 * n2` polynomial is 0 for `k > 2 * n2`!
  have hE2_ext : (eulerSec n2 : ℚ) =
      (-1 : ℚ) ^ n2 *
        ∑ k ∈ Finset.range (2 * n1 + 1),
          ((-1 / 2 : ℚ) ^ k) * (fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 : ℚ) := by
    rw [hE2]; congr 1
    refine Finset.sum_subset (Finset.range_mono (by omega : 2 * n2 + 1 ≤ 2 * n1 + 1)) fun k hk hnot => ?_
    simp only [Finset.mem_range] at hk hnot
    let P : Polynomial ℤ := (2 * Polynomial.X + 1) ^ (2 * n2)
    have hPeval : (fun j : ℕ => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) = fun (j : ℕ) => P.eval (j : ℤ) := by
      funext j; simp [P]
    have hPdeg : P.natDegree < k := by
      have h1 : P.natDegree ≤ 2 * n2 * (2 * Polynomial.X + 1 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_pow_le
      have h2 : (2 * Polynomial.X + 1 : Polynomial ℤ).natDegree ≤ 1 := by
        have := Polynomial.natDegree_add_le (2 * Polynomial.X : Polynomial ℤ) 1
        have hX : (2 * Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
          simp
        simp only [Polynomial.natDegree_one] at this
        omega
      nlinarith
    rw [hPeval, fwdDiff_poly_zero_of_lt P k 0 hPdeg, Int.cast_zero, mul_zero]
  rcases hp.eq_two_or_odd with rfl | hodd
  · -- Case `p = 2` (Stern's congruence via `fwdDiff_leibniz` + `(2j+1)^2 = 1 + 8*C(j+1,2)`)!
    -- Wait: check sign `(-1)^n1` vs `(-1)^n2`!
    -- For `r = 1`: `n1 = 2*u + m`, `n2 = u + m` -> signs can differ!
    -- Wait: for `r = 1`, `eulerSec n` is ALWAYS ODD (`eulerSec n ≡ 1 (mod 2)`), so `2 ∣ (eulerSec n1 - eulerSec n2)`!
    by_cases hr1 : r = 1
    · subst hr1
      -- Every `eulerSec n` is odd (from `eulerSec_eq_fwdDiff_sum` mod 2: only `k = 0` survives)!
      have hodd_E : ∀ t : ℕ, ∃ c : ℤ, eulerSec t = 2 * c + 1 := by
        intro t
        have hEt := eulerSec_eq_fwdDiff_sum t
        have hsum_int : ∃ s : ℤ,
            ∑ k ∈ Finset.range (2 * t + 1),
              ((-1 / 2 : ℚ) ^ k) * (fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * t)) 0 : ℚ) =
            (2 * s + 1 : ℚ) := by
          rw [Finset.sum_range_succ']
          have hfd0 : fwdDiff 0 (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * t)) 0 = 1 := by simp [fwdDiff]
          rw [hfd0]
          simp only [pow_zero, one_mul, Int.cast_one]
          have hterm : ∀ k : ℕ,
              ∃ c : ℤ, ((-1 / 2 : ℚ) ^ (k + 1)) *
                (fwdDiff (k + 1) (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * t)) 0 : ℚ) = (2 * c : ℚ) := by
            intro k
            -- `fwdDiff (k+1) ((2j+1)^(2t)) 0` is divisible by `2^(k+2)` (since `(2j+1)^2 = 1 + 8*T_j`!)
            have h4 : ((2 ^ (k + 2) : ℕ) : ℤ) ∣ fwdDiff (k + 1) (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * t)) 0 := by
              -- `fwdDiff (k+1) ((1 + 8*T)^t) 0`: `T(y) = y*(y+1)/2`, every `Δ` on `(2y+1)^2` gives `8*(y+1)`!
              have hstep : (fun y : ℕ => ((2 * (y + 1) + 1 : ℕ) : ℤ) ^ (2 * t) - ((2 * y + 1 : ℕ) : ℤ) ^ (2 * t)) =
                  fun y => 4 * ∑ i ∈ Finset.range t,
                    (Nat.choose t i : ℤ) * 4 ^ (t - 1 - i) *
                      (((2 * (y + 1) : ℕ) : ℤ) ^ (t - i) * ((2 * y + 1 : ℕ) : ℤ) ^ (2 * i)) := by
                funext y
                have hsq : ((2 * (y + 1) + 1 : ℕ) : ℤ) ^ 2 =
                    ((2 * y + 1 : ℕ) : ℤ) ^ 2 + 4 * ((2 * (y + 1) : ℕ) : ℤ) := by push_cast; ring
                rw [pow_mul, pow_mul, hsq, add_pow, Finset.sum_range_succ]
                simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i hi => ?_
                have hit : i < t := Finset.mem_range.mp hi
                rw [mul_pow, show t - i = (t - 1 - i) + 1 by omega, pow_succ (4 : ℤ), ← pow_mul]
                ring
              have hrew : fwdDiff (k + 1) (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * t)) 0 =
                  fwdDiff k (fun y => ((2 * (y + 1) + 1 : ℕ) : ℤ) ^ (2 * t) - ((2 * y + 1 : ℕ) : ℤ) ^ (2 * t)) 0 := by
                have : ∀ m (g : ℕ → ℤ) z, fwdDiff (m + 1) g z = fwdDiff m (fun y => g (y + 1) - g y) z := by
                  intro m; induction m with
                  | zero => intro g z; rfl
                  | succ m ihm => intro g z; rw [fwdDiff, ihm, ihm, ← fwdDiff]
                exact this k _ 0
              rw [hrew, hstep, fwdDiff_const_mul, fwdDiff_sum]
              have hpow : ((2 ^ (k + 2) : ℕ) : ℤ) = 4 * ((2 ^ k : ℕ) : ℤ) := by
                rw [pow_succ, pow_succ]; push_cast; ring
              rw [hpow]
              refine mul_dvd_mul (dvd_refl 4) (Finset.dvd_sum fun i _ => ?_)
              rw [fwdDiff_const_mul]
              refine dvd_mul_of_dvd_right ?_ _
              rw [fwdDiff_leibniz]
              refine Finset.dvd_sum fun a ha => ?_
              have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              have hd1 : ((2 ^ a : ℕ) : ℤ) ∣ fwdDiff a (fun y => ((2 * (y + 1) : ℕ) : ℤ) ^ (t - i)) 0 := by
                clear hrew hstep hpow ha hak
                generalize t - i = d
                induction a generalizing d with
                | zero => simp [fwdDiff]
                | succ a iha =>
                    have hrew2 : ∀ x, fwdDiff (a + 1) (fun y => ((2 * (y + 1) : ℕ) : ℤ) ^ d) x =
                        fwdDiff a (fun y => ((2 * (y + 2) : ℕ) : ℤ) ^ d - ((2 * (y + 1) : ℕ) : ℤ) ^ d) x := by
                      intro x
                      have : ∀ m (g : ℕ → ℤ) z, fwdDiff (m + 1) g z = fwdDiff m (fun y => g (y + 1) - g y) z := by
                        intro m; induction m with
                        | zero => intro g z; rfl
                        | succ m ihm => intro g z; rw [fwdDiff, ihm, ihm, ← fwdDiff]
                      exact this a _ x
                    have hst : (fun y : ℕ => ((2 * (y + 2) : ℕ) : ℤ) ^ d - ((2 * (y + 1) : ℕ) : ℤ) ^ d) =
                        fun y => 2 * ∑ j ∈ Finset.range d,
                          (Nat.choose d j : ℤ) * 2 ^ (d - 1 - j) * ((2 * (y + 1) : ℕ) : ℤ) ^ j := by
                      funext y
                      have h2 : ((2 * (y + 2) : ℕ) : ℤ) = ((2 * (y + 1) : ℕ) : ℤ) + 2 := by push_cast; ring
                      rw [h2, add_pow, Finset.sum_range_succ]
                      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun j hj => ?_
                      have hjd : j < d := Finset.mem_range.mp hj
                      rw [show d - j = (d - 1 - j) + 1 by omega, pow_succ]; ring
                    rw [hrew2 0, hst, fwdDiff_const_mul, fwdDiff_sum, pow_succ, Nat.cast_mul, mul_comm ((2 ^ a : ℕ) : ℤ)]
                    refine mul_dvd_mul (dvd_refl 2) (Finset.dvd_sum fun j _ => ?_)
                    rw [fwdDiff_const_mul]
                    exact dvd_mul_of_dvd_right (iha j) _
              have hd2 : ((2 ^ (k - a) : ℕ) : ℤ) ∣ fwdDiff (k - a) (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ (2 * i)) a :=
                two_pow_dvd_fwdDiff_odd_pow (2 * i) (k - a) a
              have hprod : ((2 ^ k : ℕ) : ℤ) ∣
                  fwdDiff a (fun y => ((2 * (y + 1) : ℕ) : ℤ) ^ (t - i)) 0 *
                  fwdDiff (k - a) (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ (2 * i)) a := by
                rw [show ((2 ^ k : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) * ((2 ^ (k - a) : ℕ) : ℤ) by
                  rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_of_le hak]]
                exact mul_dvd_mul hd1 hd2
              rw [mul_assoc, zero_add]
              exact dvd_mul_of_dvd_right hprod _
            obtain ⟨c, hc⟩ := h4
            refine ⟨(-1 : ℤ) ^ (k + 1) * c, ?_⟩
            rw [hc, pow_succ (2 : ℕ), div_pow]; push_cast; field_simp
          choose c hc using hterm
          refine ⟨∑ k ∈ Finset.range (2 * t), c k, ?_⟩
          rw [Finset.sum_congr rfl fun k _ => hc k]
          push_cast [Finset.mul_sum]; ring
        obtain ⟨s, hs⟩ := hsum_int
        rw [hs] at hEt
        rcases Nat.even_or_odd t with ⟨q, hq⟩ | ⟨q, hq⟩
        · rw [Even.neg_one_pow ⟨q, by omega⟩, one_mul] at hEt
          exact ⟨s, by exact_mod_cast hEt⟩
        · rw [Odd.neg_one_pow ⟨q, by omega⟩] at hEt
          refine ⟨-s - 1, ?_⟩
          have : (eulerSec t : ℚ) = ((2 * (-s - 1) + 1 : ℤ) : ℚ) := by push_cast; linarith
          exact_mod_cast this
      obtain ⟨c1, hc1⟩ := hodd_E n1
      obtain ⟨c2, hc2⟩ := hodd_E n2
      refine ⟨c1 - c2, ?_⟩
      rw [hc1, hc2]; ring
    · -- `r ≥ 2`: `n1 = 2^r * u + m` and `n2 = 2^(r-1) * u + m` have the SAME parity (`(-1)^n1 = (-1)^n2`)!
      have hr2 : 2 ≤ r := by omega
      have hsign_eq : (-1 : ℚ) ^ n1 = (-1 : ℚ) ^ n2 := by
        have hdiff_even : Even (n1 - n2) := by
          refine ⟨2 ^ (r - 2) * u, ?_⟩
          have h1 : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
          have h2 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by rw [← pow_succ', show r - 2 + 1 = r - 1 by omega]
          simp only [n1, n2]
          rw [Nat.add_sub_add_right, h1, show 2 * 2 ^ (r - 1) * u - 2 ^ (r - 1) * u = 2 ^ (r - 1) * u by
            rw [mul_assoc, two_mul, Nat.add_sub_cancel], h2]
          ring
        rw [show n1 = n2 + (n1 - n2) by omega, pow_add, Even.neg_one_pow hdiff_even, mul_one]
      have hterm_dvd : ∀ k ∈ Finset.range (2 * n1 + 1),
          ((2 ^ (k + r) : ℕ) : ℤ) ∣
            fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 := by
        intro k _
        have hfac : (fun j : ℕ => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) =
            fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2) *
              ((((2 * j + 1 : ℕ) : ℤ) ^ 2) ^ (2 ^ (r - 1) * u) - 1) := by
          funext j
          have hexp : 2 * n1 = 2 * n2 + 2 * (2 ^ (r - 1) * u) := by
            have h1 : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
            simp only [n1, n2]; rw [h1]; ring
          rw [hexp, pow_add, ← pow_mul]; ring
        rw [hfac, fwdDiff_leibniz]
        refine Finset.dvd_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hd1 : ((2 ^ i : ℕ) : ℤ) ∣ fwdDiff i (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 :=
          two_pow_dvd_fwdDiff_odd_pow (2 * n2) i 0
        -- Show `2^(r + (k - i)) ∣ fwdDiff (k - i) (fun y => ((2y+1)^2)^(2^(r-1)*u) - 1) i`!
        have hd2 : ((2 ^ (r + (k - i)) : ℕ) : ℤ) ∣
            fwdDiff (k - i) (fun y => (((2 * y + 1 : ℕ) : ℤ) ^ 2) ^ (2 ^ (r - 1) * u) - 1) i := by
          set N := 2 ^ (r - 1) * u
          have hexp_bin : (fun y : ℕ => (((2 * y + 1 : ℕ) : ℤ) ^ 2) ^ N - 1) =
              fun y => ∑ s ∈ Finset.Icc 1 N,
                ((Nat.choose N s : ℤ) * (8 : ℤ) ^ s) * ((Nat.choose (y + 1) 2 : ℤ) ^ s) := by
            funext y
            have hsq : ((2 * y + 1 : ℕ) : ℤ) ^ 2 = 1 + 8 * (Nat.choose (y + 1) 2 : ℤ) := by
              have hch2 : 2 * Nat.choose (y + 1) 2 = (y + 1) * y := by
                rw [Nat.choose_two_right, Nat.add_sub_cancel]
                exact Nat.mul_div_cancel' (Nat.even_mul_pred_self (y + 1)).two_dvd
              have hch2' : 2 * (Nat.choose (y + 1) 2 : ℤ) = ((y + 1 : ℕ) : ℤ) * (y : ℤ) := by
                exact_mod_cast hch2
              push_cast at hch2' ⊢; linarith
            rw [hsq, add_comm 1, add_pow, Finset.sum_range_succ']
            simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
            refine Finset.sum_nbij (fun s => s + 1) ?_ ?_ ?_ ?_
            · intro s hs; simp only [Finset.mem_range, Finset.mem_Icc] at hs ⊢; omega
            · intro a _ b _ hab; dsimp only at hab; omega
            · intro s hs; simp only [Finset.mem_coe, Finset.mem_Icc] at hs
              exact ⟨s - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
            · intro s _; rw [mul_pow]; ring
          rw [hexp_bin, fwdDiff_sum]
          refine Finset.dvd_sum fun s hs => ?_
          simp only [Finset.mem_Icc] at hs
          rw [fwdDiff_const_mul]
          by_cases h2s : 2 * s < k - i
          · -- `C(y+1, 2)^s` is a polynomial of degree `2 * s < k - i`, so its `fwdDiff (k - i)` is `0`!
            -- Multiply by `2^s` so `2^s * C(y+1, 2)^s = (y*(y+1))^s`, a polynomial in `ℤ[X]` of degree `2*s`!
            have h0 : (2 : ℤ) ^ s * fwdDiff (k - i) (fun y => (Nat.choose (y + 1) 2 : ℤ) ^ s) i = 0 := by
              rw [← fwdDiff_const_mul]
              let P : Polynomial ℤ := (Polynomial.X * (Polynomial.X + 1)) ^ s
              have hPeval : (fun y : ℕ => (2 : ℤ) ^ s * (Nat.choose (y + 1) 2 : ℤ) ^ s) =
                  fun (y : ℕ) => P.eval (y : ℤ) := by
                funext y
                have hch2 : 2 * (Nat.choose (y + 1) 2 : ℤ) = (y : ℤ) * ((y : ℤ) + 1) := by
                  have h := Nat.choose_two_right (y + 1)
                  rw [Nat.add_sub_cancel] at h
                  have hd : 2 ∣ (y + 1) * y := (Nat.even_mul_pred_self (y + 1)).two_dvd
                  have hm : 2 * Nat.choose (y + 1) 2 = (y + 1) * y := by rw [h]; exact Nat.mul_div_cancel' hd
                  have hm' : 2 * (Nat.choose (y + 1) 2 : ℤ) = ((y + 1 : ℕ) : ℤ) * (y : ℤ) := by exact_mod_cast hm
                  push_cast at hm'; linarith
                simp only [P, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_add,
                    Polynomial.eval_X, Polynomial.eval_one, ← mul_pow, hch2]
              have hPdeg : P.natDegree < k - i := by
                have h1 : P.natDegree ≤ s * (Polynomial.X * (Polynomial.X + 1) : Polynomial ℤ).natDegree :=
                  Polynomial.natDegree_pow_le
                have h2 : (Polynomial.X * (Polynomial.X + 1) : Polynomial ℤ).natDegree ≤ 2 := by
                  have := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℤ)) (q := Polynomial.X + 1)
                  have hX1 : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≤ 1 := by
                    have := Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℤ) 1
                    simp only [Polynomial.natDegree_X, Polynomial.natDegree_one] at this; omega
                  simp only [Polynomial.natDegree_X] at this; omega
                nlinarith
              rw [hPeval, fwdDiff_poly_zero_of_lt P (k - i) i hPdeg]
            have hzero : fwdDiff (k - i) (fun y => (Nat.choose (y + 1) 2 : ℤ) ^ s) i = 0 :=
              (mul_eq_zero.mp h0).resolve_left (by positivity)
            rw [hzero, mul_zero]; exact dvd_zero _
          · -- `k - i ≤ 2 * s`: `2^(r + 2*s) ∣ C(N, s) * 8^s`!
            have hki_le : k - i ≤ 2 * s := by omega
            have hd_nat : 2 ^ (r + (k - i)) ∣ Nat.choose N s * 8 ^ s := by
              -- `s * C(N, s) = N * C(N - 1, s - 1)`, so `v_2(C(N, s)) ≥ (r - 1) - v_2(s)`!
              have hN0 : N ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega)
              have hs0 : s ≠ 0 := by omega
              by_cases hch0 : Nat.choose N s = 0
              · rw [hch0, zero_mul]; exact dvd_zero _
              · have hmul : s * Nat.choose N s = N * Nat.choose (N - 1) (s - 1) := by
                  have h1 := Nat.add_one_mul_choose_eq (N - 1) (s - 1)
                  rw [show N - 1 + 1 = N by omega, show s - 1 + 1 = s by omega] at h1; linarith
                have hch_pos : Nat.choose (N - 1) (s - 1) ≠ 0 := by
                  intro h; rw [h, mul_zero] at hmul; exact mul_ne_zero hs0 hch0 hmul
                have hfac := congrArg (fun x => x.factorization 2) hmul
                rw [Nat.factorization_mul hs0 hch0, Nat.factorization_mul hN0 hch_pos,
                    Finsupp.add_apply, Finsupp.add_apply] at hfac
                have hNr : r - 1 ≤ N.factorization 2 :=
                  (Nat.prime_two.pow_dvd_iff_le_factorization hN0).mp (dvd_mul_right (2 ^ (r - 1)) u)
                set vs := s.factorization 2
                have hvs_le : vs ≤ s - 1 := by
                  have h1 : 2 ^ vs ≤ s := Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) (Nat.ordProj_dvd s 2)
                  have h2 : vs < 2 ^ vs := Nat.lt_two_pow_self
                  omega
                have hch_val : (r - 1) - vs ≤ (Nat.choose N s).factorization 2 := by omega
                have hch_dvd : 2 ^ ((r - 1) - vs) ∣ Nat.choose N s :=
                  (Nat.prime_two.pow_dvd_iff_le_factorization hch0).mpr hch_val
                have h8 : 8 ^ s = 2 ^ (3 * s) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
                rw [h8]
                have hmul_dvd : 2 ^ ((r - 1) - vs + 3 * s) ∣ Nat.choose N s * 2 ^ (3 * s) := by
                  rw [pow_add]; exact mul_dvd_mul hch_dvd (dvd_refl _)
                exact dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hmul_dvd
            exact dvd_mul_of_dvd_left (by exact_mod_cast hd_nat) _
        have hprod : ((2 ^ (k + r) : ℕ) : ℤ) ∣
            fwdDiff i (fun y => ((2 * y + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 *
            fwdDiff (k - i) (fun y => (((2 * y + 1 : ℕ) : ℤ) ^ 2) ^ (2 ^ (r - 1) * u) - 1) i := by
          rw [show ((2 ^ (k + r) : ℕ) : ℤ) = ((2 ^ i : ℕ) : ℤ) * ((2 ^ (r + (k - i)) : ℕ) : ℤ) by
            rw [← Nat.cast_mul, ← pow_add, show k + r = i + (r + (k - i)) by omega]]
          exact mul_dvd_mul hd1 hd2
        rw [mul_assoc, zero_add]
        exact dvd_mul_of_dvd_right hprod _
      -- Sum over `k = 0..2*n1`!
      have hdiff_q : ((eulerSec n1 - eulerSec n2 : ℤ) : ℚ) =
          (-1 : ℚ) ^ n1 *
            ∑ k ∈ Finset.range (2 * n1 + 1),
              ((-1 / 2 : ℚ) ^ k) *
                (fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 : ℚ) := by
        rw [Int.cast_sub, hE1, hE2_ext, ← hsign_eq, ← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hfd : fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 =
            fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1)) 0 -
            fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 := by
          have : (fun j : ℕ => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) =
              fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) + (-1 : ℤ) * ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2) := by
            funext j; ring
          rw [this, fwdDiff_add, fwdDiff_const_mul]; ring
        rw [hfd, Int.cast_sub]; ring
      choose c hc using fun k (hk : k ∈ Finset.range (2 * n1 + 1)) => hterm_dvd k hk
      refine ⟨(if Even n1 then (1 : ℤ) else -1) *
          ∑ k ∈ (Finset.range (2 * n1 + 1)).attach, (-1 : ℤ) ^ k.1 * c k.1 k.2, ?_⟩
      have hq_eq : ((eulerSec n1 - eulerSec n2 : ℤ) : ℚ) =
          (((2 ^ r : ℕ) : ℤ) * ((if Even n1 then (1 : ℤ) else -1) *
            ∑ k ∈ (Finset.range (2 * n1 + 1)).attach, (-1 : ℤ) ^ k.1 * c k.1 k.2) : ℤ) := by
        rw [hdiff_q]
        have hsign : (-1 : ℚ) ^ n1 = ((if Even n1 then (1 : ℤ) else -1 : ℤ) : ℚ) := by
          rcases Nat.even_or_odd n1 with he | ho
          · rw [if_pos he, Even.neg_one_pow he]; simp
          · rw [if_neg (Nat.not_even_iff_odd.mpr ho), Odd.neg_one_pow ho]; simp
        rw [hsign, ← Finset.sum_attach (Finset.range (2 * n1 + 1))]
        rw [Int.cast_mul, Int.cast_mul, Int.cast_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ⟨k, hk⟩ _ => ?_
        dsimp only
        rw [hc k hk, pow_add, div_pow]; push_cast; field_simp
      exact_mod_cast hq_eq
  · -- Case `p` odd prime (Kummer's congruence: `(2j+1)^(2*n1) ≡ (2j+1)^(2*n2) (mod p^r)` for ALL `j`!)
    have hsign_eq : (-1 : ℚ) ^ n1 = (-1 : ℚ) ^ n2 := by
      have hp_odd : Odd p := Nat.odd_iff.mpr hodd
      have hdiff_even : Even (n1 - n2) := by
        have hsub : n1 - n2 = (p ^ r - p ^ (r - 1)) * u := by
          have : p ^ (r - 1) ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
          simp only [n1, n2]; rw [Nat.add_sub_add_right, ← Nat.sub_mul]
        rw [hsub]
        have he1 : Even (p ^ r - p ^ (r - 1)) := by
          rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ', Nat.sub_add_cancel hr],
              show p * p ^ (r - 1) - p ^ (r - 1) = (p - 1) * p ^ (r - 1) by
                rw [Nat.sub_mul, one_mul]]
          exact Even.mul_right (by obtain ⟨t, ht⟩ := hp_odd; exact ⟨t, by omega⟩) _
        exact Even.mul_right he1 u
      rw [show n1 = n2 + (n1 - n2) by omega, pow_add, Even.neg_one_pow hdiff_even, mul_one]
    have hpow_cong : ∀ j : ℕ, ((p ^ r : ℕ) : ℤ) ∣
        (((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) := by
      intro j
      by_cases hpj : p ∣ (2 * j + 1)
      · -- `p ∣ (2*j+1)` and `2 * n2 ≥ r` (since `p ≥ 3, u ≥ 1` -> `2 * 3^(r-1) ≥ r`)!
        have hr_le : r ≤ 2 * n2 := by
          have hp3 : 3 ≤ p := by have := hp.two_le; omega
          have h1 : r - 1 < 2 ^ (r - 1) := Nat.lt_two_pow_self
          have h2 : 2 ^ (r - 1) ≤ p ^ (r - 1) := Nat.pow_le_pow_left hp.two_le (r - 1)
          have h3 : p ^ (r - 1) ≤ n2 := by simp only [n2]; nlinarith
          omega
        have hd1 : p ^ r ∣ (2 * j + 1) ^ (2 * n1) :=
          dvd_trans (Nat.pow_dvd_pow p (by omega)) (pow_dvd_pow_of_dvd hpj _)
        have hd2 : p ^ r ∣ (2 * j + 1) ^ (2 * n2) :=
          dvd_trans (Nat.pow_dvd_pow p hr_le) (pow_dvd_pow_of_dvd hpj _)
        exact dvd_sub (by exact_mod_cast hd1) (by exact_mod_cast hd2)
      · have hcop : Nat.Coprime (2 * j + 1) (p ^ r) :=
          (hp.coprime_iff_not_dvd.mpr hpj).symm.pow_right r
        have htot : Nat.totient (p ^ r) = p ^ (r - 1) * (p - 1) :=
          Nat.totient_prime_pow hp (by omega)
        have heul : (2 * j + 1) ^ (p ^ (r - 1) * (p - 1)) ≡ 1 [MOD p ^ r] := by
          rw [← htot]; exact Nat.ModEq.pow_totient hcop
        have hexp : 2 * n1 = 2 * n2 + (p ^ (r - 1) * (p - 1)) * (2 * u) := by
          have h1 : p ^ r = p * p ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
          simp only [n1, n2]; rw [h1]; zify [hp.one_le]; ring
        have hmod : (2 * j + 1) ^ (2 * n1) ≡ (2 * j + 1) ^ (2 * n2) [MOD p ^ r] := by
          have hstep : (2 * j + 1) ^ (2 * n1) =
              (2 * j + 1) ^ (2 * n2) * ((2 * j + 1) ^ (p ^ (r - 1) * (p - 1))) ^ (2 * u) := by
            rw [hexp, pow_add]; congr 1; rw [pow_mul]
          rw [hstep]
          simpa using (heul.pow (2 * u)).mul_left ((2 * j + 1) ^ (2 * n2))
        exact Int.ModEq.dvd (by exact_mod_cast hmod.symm)
    -- Multiply `(eulerSec n1 - eulerSec n2)` by `2^(2*n1)` to clear all `1/2^k` denominators!
    have hmul_dvd : ((p ^ r : ℕ) : ℤ) ∣ ((2 ^ (2 * n1) : ℕ) : ℤ) * (eulerSec n1 - eulerSec n2) := by
      have hfd_dvd : ∀ k, ((p ^ r : ℕ) : ℤ) ∣
          fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 := by
        intro k
        rw [fwdDiff_eq_sum]
        refine Finset.dvd_sum fun j _ => ?_
        rw [zero_add]
        exact dvd_mul_of_dvd_right (hpow_cong j) _
      have hq : (((2 ^ (2 * n1) : ℕ) : ℤ) * (eulerSec n1 - eulerSec n2) : ℚ) =
          (((if Even n1 then (1 : ℤ) else -1) *
            ∑ k ∈ Finset.range (2 * n1 + 1),
              (-1 : ℤ) ^ k * ((2 ^ (2 * n1 - k) : ℕ) : ℤ) *
                fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 : ℤ) : ℚ) := by
        have hsign : (-1 : ℚ) ^ n1 = ((if Even n1 then (1 : ℤ) else -1 : ℤ) : ℚ) := by
          rcases Nat.even_or_odd n1 with he | ho
          · rw [if_pos he, Even.neg_one_pow he]; simp
          · rw [if_neg (Nat.not_even_iff_odd.mpr ho), Odd.neg_one_pow ho]; simp
        rw [hE1, hE2_ext, ← hsign_eq, ← mul_sub, ← Finset.sum_sub_distrib, hsign]
        rw [Int.cast_mul, Int.cast_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ 2 * n1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hfd : fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 =
            fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1)) 0 -
            fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 := by
          have : (fun j : ℕ => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) =
              fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) + (-1 : ℤ) * ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2) := by
            funext j; ring
          rw [this, fwdDiff_add, fwdDiff_const_mul]; ring
        rw [hfd]
        have h2pow : (2 : ℚ) ^ (2 * n1) = (2 : ℚ) ^ k * (2 : ℚ) ^ (2 * n1 - k) := by
          rw [← pow_add, Nat.add_sub_of_le hkn]
        rw [div_pow]; push_cast; rw [h2pow]; field_simp
      have hint_eq : ((2 ^ (2 * n1) : ℕ) : ℤ) * (eulerSec n1 - eulerSec n2) =
          (if Even n1 then (1 : ℤ) else -1) *
            ∑ k ∈ Finset.range (2 * n1 + 1),
              (-1 : ℤ) ^ k * ((2 ^ (2 * n1 - k) : ℕ) : ℤ) *
                fwdDiff k (fun j => ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n1) - ((2 * j + 1 : ℕ) : ℤ) ^ (2 * n2)) 0 := by
        exact_mod_cast hq
      rw [hint_eq]
      exact dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (hfd_dvd k) _) _
    have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) ((2 ^ (2 * n1) : ℕ) : ℤ) := by
      have hnat : Nat.Coprime (p ^ r) (2 ^ (2 * n1)) :=
        ((hp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by norm_num) h; have := hp.two_le; omega)).pow_left r).pow_right (2 * n1)
      exact Nat.isCoprime_iff_coprime.mpr hnat
    exact hcop.dvd_of_dvd_mul_left hmul_dvd

theorem main_proof :
    ∀ m : ℕ, isIntegerSeries (expLogSeries fun n => eulerSec (n + m)) := by
  intro m
  apply isIntegerSeries_of_gauss_cong (fun n => eulerSec (n + m))
  intro p r u hp hr hu _
  exact eulerSec_gauss_cong m hp hr hu

end OMA.S_oeis_a255895

theorem OMA.solution : type_of% @OMA.S_oeis_a255895.main :=
  OMA.S_oeis_a255895.main_proof
