import OMAStatements.S_oeis_a163921
import Mathlib

namespace OMA.S_oeis_a163921

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


/-! ### Part 1: `p`-integrality of rationals -/

private def isPInt (p : ℕ) (q : ℚ) : Prop :=
  ∃ (num : ℤ) (den : ℕ), ¬ p ∣ den ∧ q = (num : ℚ) / (den : ℚ)

private lemma isPInt_int {p : ℕ} (hp : p.Prime) (z : ℤ) : isPInt p (z : ℚ) :=
  ⟨z, 1, hp.not_dvd_one, by simp⟩

private lemma isPInt_zero {p : ℕ} (hp : p.Prime) : isPInt p 0 :=
  ⟨0, 1, hp.not_dvd_one, by simp⟩

private lemma isPInt_neg {p : ℕ} {x : ℚ} (hx : isPInt p x) : isPInt p (-x) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  exact ⟨-a, b, hb, by push_cast; ring⟩

private lemma isPInt_add {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x + y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by intro h; subst h; exact hb (dvd_zero p))
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  refine ⟨a * d + c * b, b * d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
  push_cast; field_simp [hb0, hd0]

private lemma isPInt_sub {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x - y) := by
  rw [sub_eq_add_neg]; exact isPInt_add hp hx (isPInt_neg hy)

private lemma isPInt_mul {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x * y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  refine ⟨a * c, b * d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
  push_cast; ring

private lemma isPInt_pow {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    ∀ k : ℕ, isPInt p (x ^ k)
  | 0 => by simpa using isPInt_int hp 1
  | k + 1 => by rw [pow_succ]; exact isPInt_mul hp (isPInt_pow hp hx k) hx

private lemma isPInt_sum {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, isPInt p (f i)) : isPInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPInt_zero hp
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      exact isPInt_add hp (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isPInt_div_nat {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x)
    {u : ℕ} (hu : ¬ p ∣ u) : isPInt p (x / (u : ℚ)) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  refine ⟨a, b * u, fun h => (hp.dvd_mul.mp h).elim hb hu, ?_⟩
  rw [div_div, Nat.cast_mul]

private lemma not_dvd_den_of_isPInt {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : isPInt p q) :
    ¬ p ∣ q.den := by
  obtain ⟨a, b, hb, heq⟩ := hq
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero p)
  have h1 : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
    have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    rw [hq_eq] at heq
    have hqd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hbq0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    field_simp [hqd0, hbq0] at heq
    linarith
  have hz : q.num * (b : ℤ) = a * (q.den : ℤ) := by exact_mod_cast h1
  intro hpd
  have hpdz : (p : ℤ) ∣ (q.den : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  have hprod : (p : ℤ) ∣ q.num * (b : ℤ) := by rw [hz]; exact dvd_mul_of_dvd_right hpdz a
  have hpn : (p : ℤ) ∣ q.num := by
    have hcop : IsCoprime (p : ℤ) (b : ℤ) := (hp.coprime_iff_not_dvd.mpr hb).isCoprime
    exact hcop.dvd_of_dvd_mul_right hprod
  have hp_num : p ∣ q.num.natAbs := by
    obtain ⟨t, ht⟩ := hpn
    exact ⟨t.natAbs, by
      have := congr_arg Int.natAbs ht
      simpa [Int.natAbs_mul] using this⟩
  have hcop_q : Nat.Coprime q.num.natAbs q.den := q.reduced
  exact hp.not_dvd_one (hcop_q ▸ Nat.dvd_gcd hp_num hpd)

private lemma isInt_of_forall_prime_isPInt {q : ℚ} (h : ∀ p : ℕ, p.Prime → isPInt p q) :
    ∃ z : ℤ, q = (z : ℚ) := by
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact not_dvd_den_of_isPInt hp (h p hp) hpd
  refine ⟨q.num, ?_⟩
  rw [← Rat.num_div_den q, hden]
  simp

private lemma isPInt_mul_p_inv {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    isPInt p ((p : ℚ) * x / (p : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rwa [mul_div_cancel_left₀ _ hp0]

private lemma isPInt_of_isPInt_div_p {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : isPInt p (x / (p : ℚ))) : isPInt p x := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have heq : x = (p : ℚ) * (x / (p : ℚ)) := by field_simp [hp0]
  rw [heq]
  exact isPInt_mul hp (isPInt_int hp p) hx

/-! ### Part 2: `p`-adic valuation of factorials `v_p(k!) ≤ k - 1` -/

private lemma factorization_factorial_rec {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, (Nat.factorial k).factorization p = k / p + (Nat.factorial (k / p)).factorization p := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k),
          Finsupp.add_apply, ih]
      by_cases hdiv : p ∣ k + 1
      · obtain ⟨q, hq⟩ := hdiv
        have hq_pos : 1 ≤ q := by
          by_contra h0; have : q = 0 := by omega
          rw [this, mul_zero] at hq; omega
        have hdiv1 : (k + 1) / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp.pos]
        have hdiv0 : k / p = q - 1 := by
          have hkeq : k = p * (q - 1) + (p - 1) := by
            cases q with
            | zero => omega
            | succ q' => rw [Nat.mul_succ] at hq; simp only [Nat.add_sub_cancel]; have := hp.two_le; omega
          rw [hkeq, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.two_le; omega), add_zero]
        have hfac_q : Nat.factorial q = q * Nat.factorial (q - 1) := by
          cases q with
          | zero => omega
          | succ q' => simp [Nat.factorial_succ]
        rw [Nat.succ_eq_add_one, hdiv1, hdiv0, hq, Nat.factorization_mul hp.ne_zero (by omega), Finsupp.add_apply,
            hp.factorization_self, hfac_q, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _),
            Finsupp.add_apply]
        omega
      · have hdiv_eq : (k + 1) / p = k / p := by
          have hmod : (k + 1) % p ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
          have h1 := Nat.div_add_mod k p
          have h2 := Nat.div_add_mod (k + 1) p
          have hlt1 := Nat.mod_lt k hp.pos
          have hlt2 := Nat.mod_lt (k + 1) hp.pos
          have hp1 : 1 ≤ (k + 1) % p := Nat.pos_of_ne_zero hmod
          by_contra hne
          have hlt : k / p < (k + 1) / p := lt_of_le_of_ne (Nat.div_le_div_right (by omega)) (Ne.symm hne)
          have : p * (k / p + 1) ≤ p * ((k + 1) / p) := Nat.mul_le_mul_left p hlt
          nlinarith
        rw [hdiv_eq, Nat.factorization_eq_zero_of_not_dvd hdiv, zero_add]

private lemma factorization_factorial_lt {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, 1 ≤ k → (Nat.factorial k).factorization p ≤ k - 1 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [factorization_factorial_rec hp]
    by_cases hlt : k < p
    · rw [Nat.div_eq_of_lt hlt]; simp
    · have hq_pos : 1 ≤ k / p := Nat.div_pos (by omega) hp.pos
      have hq_lt : k / p < k := Nat.div_lt_self (by omega) hp.one_lt
      have ih' := ih (k / p) hq_lt hq_pos
      have h2q : 2 * (k / p) ≤ k := by
        have := Nat.mul_div_le k p
        have := hp.two_le
        nlinarith
      omega

private lemma isPInt_pow_div_factorial {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    isPInt p ((p : ℚ) ^ (k - 1) / (Nat.factorial k : ℚ)) := by
  set F := Nat.factorial k
  set v := F.factorization p
  set u := F / p ^ v
  have hF_pos : 0 < F := Nat.factorial_pos k
  have hpow_dvd : p ^ v ∣ F := Nat.ordProj_dvd F p
  have hFu : p ^ v * u = F := Nat.mul_div_cancel' hpow_dvd
  have hpu : ¬ p ∣ u := by
    intro h
    have hpow1 : p ^ (v + 1) ∣ F := by
      rw [← hFu, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ v) h
    have hle := (hp.pow_dvd_iff_le_factorization hF_pos.ne').mp hpow1
    omega
  have hv_le : v ≤ k - 1 := factorization_factorial_lt hp k hk
  refine ⟨((p ^ (k - 1 - v) : ℕ) : ℤ), u, hpu, ?_⟩
  have hF_cast : (F : ℚ) = (p : ℚ) ^ v * (u : ℚ) := by exact_mod_cast hFu.symm
  have hpv0 : (p : ℚ) ^ v ≠ 0 := by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    positivity
  have hu0 : (u : ℚ) ≠ 0 := by
    exact_mod_cast (show u ≠ 0 by intro h; rw [h, mul_zero] at hFu; omega)
  have hexp : (p : ℚ) ^ (k - 1) = (p : ℚ) ^ (k - 1 - v) * (p : ℚ) ^ v := by
    rw [← pow_add]; congr 1; omega
  rw [show (Nat.factorial k : ℚ) = (F : ℚ) from rfl, hF_cast, hexp]
  push_cast
  field_simp [hpv0, hu0]

/-! ### Part 3: Formal `expSeries` and `substPow p` (i.e. `F(X^p)`) -/

private noncomputable def expCoeffs (G : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) G * expCoeffs G (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

private noncomputable def expSeries (G : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (expCoeffs G)

private lemma coeff_zero_expSeries (G : PowerSeries ℚ) :
    PowerSeries.coeff 0 (expSeries G) = 1 := by
  rw [expSeries, PowerSeries.coeff_mk, expCoeffs]

private lemma expSeries_ode (G : PowerSeries ℚ) :
    PowerSeries.X * PowerSeries.derivative ℚ (expSeries G) =
      expSeries G * (PowerSeries.X * PowerSeries.derivative ℚ G) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_zero_X_mul, mul_zero]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, expSeries,
          PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (PowerSeries.mk (expCoeffs G)) *
              PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))]
      rw [expCoeffs]
      have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [div_mul_cancel₀ _ hpos]
      rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero]
      rw [Fin.sum_univ_eq_sum_range
        (fun k => ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) G * expCoeffs G (n - k)) (n + 1)]
      rw [← Finset.sum_range_reflect
        (fun k => ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) G * expCoeffs G (n - k)) (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n + 1 := Finset.mem_range.mp hi
      rw [PowerSeries.coeff_mk]
      have h1 : n + 1 - 1 - i + 1 = n + 1 - i := by omega
      have h2 : n - (n + 1 - 1 - i) = i := by omega
      have h3 : n + 1 - i = (n - i) + 1 := by omega
      rw [h1, h2, h3, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      have h4 : ((n + 1 - 1 - i : ℕ) : ℚ) + 1 = ((n - i : ℕ) : ℚ) + 1 := by
        rw [show n + 1 - 1 - i = n - i by omega]
      rw [h4]
      ring

private lemma eq_expSeries_upTo {G F : PowerSeries ℚ} {N : ℕ}
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : ∀ n, 1 ≤ n → n ≤ N →
      PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative ℚ F) =
      PowerSeries.coeff n (F * (PowerSeries.X * PowerSeries.derivative ℚ G))) :
    ∀ n ≤ N, PowerSeries.coeff n F = PowerSeries.coeff n (expSeries G) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [h0, coeff_zero_expSeries]
    | succ n =>
        have hF := hode (n + 1) (by omega) hn
        have hE := congr_arg (PowerSeries.coeff (n + 1)) (expSeries_ode G)
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i F *
                PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))] at hF
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (expSeries G) *
                PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))] at hE
        rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero] at hF hE
        have hsum :
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k F * PowerSeries.coeff (n + 1 - k) (PowerSeries.X * PowerSeries.derivative ℚ G) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (expSeries G) *
                PowerSeries.coeff (n + 1 - k) (PowerSeries.X * PowerSeries.derivative ℚ G) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [ih k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega)]
        rw [hsum, ← hE] at hF
        have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hpos hF

private lemma eq_expSeries_of_ode {G F : PowerSeries ℚ}
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : PowerSeries.X * PowerSeries.derivative ℚ F =
      F * (PowerSeries.X * PowerSeries.derivative ℚ G)) :
    F = expSeries G := by
  apply PowerSeries.ext; intro n
  exact eq_expSeries_upTo h0 (fun m _ _ => congr_arg (PowerSeries.coeff m) hode) n (le_refl n)

private lemma expSeries_add (G₁ G₂ : PowerSeries ℚ) :
    expSeries (G₁ + G₂) = expSeries G₁ * expSeries G₂ := by
  symm
  apply eq_expSeries_of_ode
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
        coeff_zero_expSeries, coeff_zero_expSeries, mul_one]
  · rw [Derivation.leibniz, map_add, mul_add, mul_add]
    simp only [smul_eq_mul]
    have h1 := expSeries_ode G₁
    have h2 := expSeries_ode G₂
    calc
      PowerSeries.X * (expSeries G₁ * PowerSeries.derivative ℚ (expSeries G₂)) +
          PowerSeries.X * (expSeries G₂ * PowerSeries.derivative ℚ (expSeries G₁))
        = expSeries G₁ * (PowerSeries.X * PowerSeries.derivative ℚ (expSeries G₂)) +
            expSeries G₂ * (PowerSeries.X * PowerSeries.derivative ℚ (expSeries G₁)) := by ring
      _ = expSeries G₁ * (expSeries G₂ * (PowerSeries.X * PowerSeries.derivative ℚ G₂)) +
            expSeries G₂ * (expSeries G₁ * (PowerSeries.X * PowerSeries.derivative ℚ G₁)) := by
            rw [h1, h2]
      _ = expSeries G₁ * expSeries G₂ *
            (PowerSeries.X * PowerSeries.derivative ℚ G₁ +
             PowerSeries.X * PowerSeries.derivative ℚ G₂) := by ring

private lemma expSeries_zero : expSeries 0 = 1 := by
  symm
  apply eq_expSeries_of_ode
  · simp
  · simp

private lemma expSeries_nsmul (G : PowerSeries ℚ) (m : ℕ) :
    expSeries (PowerSeries.C (m : ℚ) * G) = (expSeries G) ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
      rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul, expSeries_add, ih, pow_succ]

/-- Formal substitution `F(X^p)`. -/
private noncomputable def substPow (p : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) F else 0

private lemma coeff_substPow (p : ℕ) (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (substPow p F) = if p ∣ n then PowerSeries.coeff (n / p) F else 0 := by
  rw [substPow, PowerSeries.coeff_mk]

private lemma substPow_mul {p : ℕ} (hp : 0 < p) (F G : PowerSeries ℚ) :
    substPow p (F * G) = substPow p F * substPow p G := by
  apply PowerSeries.ext; intro n
  rw [coeff_substPow]
  conv_rhs =>
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (substPow p F) * PowerSeries.coeff j (substPow p G))]
  by_cases hdiv : p ∣ n
  · obtain ⟨m, rfl⟩ := hdiv
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hp]
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i F * PowerSeries.coeff j G)]
    have hsub : (Finset.range (m + 1)).image (fun k => p * k) ⊆ Finset.range (p * m + 1) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      have hkl : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Finset.mem_range.mpr (by nlinarith)
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkl : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsub_eq : p * m - p * k = p * (m - k) := (Nat.mul_sub_left_distrib p m k).symm
      rw [coeff_substPow, coeff_substPow, hsub_eq]
      simp [dvd_mul_right, Nat.mul_div_cancel_left _ hp]
    · intro x hx hnot
      rw [coeff_substPow]
      split_ifs with hpx
      · exfalso; apply hnot
        obtain ⟨k, rfl⟩ := hpx
        have hxl : p * k ≤ p * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have hkl : k ≤ m := Nat.le_of_mul_le_mul_left hxl hp
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      · rw [zero_mul]
  · simp only [hdiv, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkl : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_substPow, coeff_substPow]
    split_ifs with h1 h2
    · exfalso; apply hdiv
      rw [← Nat.add_sub_of_le hkl]
      exact dvd_add h1 h2
    · ring
    · ring
    · ring

private lemma substPow_pow {p : ℕ} (hp : 0 < p) (F : PowerSeries ℚ) :
    ∀ k : ℕ, substPow p (F ^ k) = (substPow p F) ^ k := by
  intro k
  induction k with
  | zero =>
      apply PowerSeries.ext; intro j
      rw [pow_zero, pow_zero, coeff_substPow, PowerSeries.coeff_one]
      by_cases hj : j = 0
      · subst hj; simp
      · rw [PowerSeries.coeff_one, if_neg hj]
        by_cases hdiv : p ∣ j
        · rw [if_pos hdiv]
          obtain ⟨q, rfl⟩ := hdiv
          rw [Nat.mul_div_cancel_left _ hp, if_neg (fun h => hj (by rw [h, mul_zero]))]
        · rw [if_neg hdiv]
  | succ k ih => rw [pow_succ, pow_succ, substPow_mul hp, ih]

private lemma X_mul_deriv_substPow {p : ℕ} (hp : 0 < p) (F : PowerSeries ℚ) :
    PowerSeries.X * PowerSeries.derivative ℚ (substPow p F) =
      PowerSeries.C (p : ℚ) * substPow p (PowerSeries.X * PowerSeries.derivative ℚ F) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, coeff_substPow]
      simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_substPow,
          PowerSeries.coeff_C_mul, coeff_substPow]
      by_cases hdiv : p ∣ n + 1
      · simp only [hdiv, ↓reduceIte]
        obtain ⟨m, hm⟩ := hdiv
        have hm_pos : 1 ≤ m := by
          by_contra h0; have : m = 0 := by omega
          rw [this, mul_zero] at hm; omega
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hdiv_eq : (n + 1) / p = m' + 1 := by rw [hm, Nat.mul_div_cancel_left _ hp]
        rw [hdiv_eq, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        have hcast : ((n : ℚ) + 1) = (p : ℚ) * ((m' : ℚ) + 1) := by exact_mod_cast hm
        rw [hcast]; ring
      · simp [hdiv]

private lemma expSeries_substPow {p : ℕ} (hp : 0 < p) (G : PowerSeries ℚ) :
    expSeries (substPow p G) = substPow p (expSeries G) := by
  symm
  apply eq_expSeries_of_ode
  · rw [coeff_substPow]; simp [coeff_zero_expSeries]
  · rw [X_mul_deriv_substPow hp, X_mul_deriv_substPow hp, expSeries_ode, substPow_mul hp]
    ring

/-! ### Part 4: Dwork's Lemma -/

private lemma exp_p_mul_div_p_isPInt {p N : ℕ} (hp : p.Prime) {F : PowerSeries ℚ}
    (hF0 : PowerSeries.coeff 0 F = 0)
    (hFp : ∀ n ≤ N, isPInt p (PowerSeries.coeff n F)) :
    ∀ n, 1 ≤ n → n ≤ N → isPInt p (PowerSeries.coeff n (expSeries (PowerSeries.C (p : ℚ) * F)) / (p : ℚ)) := by
  have hFpow_pInt : ∀ (k n : ℕ), n ≤ N → isPInt p (PowerSeries.coeff n (F ^ k)) := by
    intro k
    induction k with
    | zero =>
        intro n _
        rw [pow_zero, PowerSeries.coeff_one]
        split_ifs
        · exact isPInt_int hp 1
        · exact isPInt_zero hp
    | succ k ih =>
        intro n hn
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (F ^ k) * PowerSeries.coeff j F)]
        refine isPInt_sum hp _ _ fun j hj => ?_
        have hjl : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact isPInt_mul hp (ih j (by omega)) (hFp (n - j) (by omega))
  have hFpow_zero : ∀ (k n : ℕ), n < k → PowerSeries.coeff n (F ^ k) = 0 := by
    intro k
    induction k with
    | zero => intro n hn; omega
    | succ k ih =>
        intro n hn
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (F ^ k) * PowerSeries.coeff j F)]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjl : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        by_cases hjn : j = n
        · subst hjn; rw [Nat.sub_self, hF0, mul_zero]
        · rw [ih j (by omega), zero_mul]
  let Etrunc : PowerSeries ℚ :=
    ∑ k ∈ Finset.range (N + 1),
      PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k
  have hE0 : PowerSeries.coeff 0 Etrunc = 1 := by
    simp only [Etrunc, map_sum, PowerSeries.coeff_C_mul]
    rw [Finset.sum_range_succ']
    have htail :
        ∑ k ∈ Finset.range N,
          ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff 0 (F ^ (k + 1)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hFpow_zero (k + 1) 0 (by omega), mul_zero]
    rw [htail, zero_add]
    simp
  have hE_ode : ∀ n, 1 ≤ n → n ≤ N →
      PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative ℚ Etrunc) =
      PowerSeries.coeff n (Etrunc * (PowerSeries.X * PowerSeries.derivative ℚ (PowerSeries.C (p : ℚ) * F))) := by
    have hderiv_E :
        PowerSeries.derivative ℚ Etrunc =
          PowerSeries.C (p : ℚ) *
            (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
            PowerSeries.derivative ℚ F := by
      simp only [Etrunc, map_sum]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
        Derivation.map_one_eq_zero, add_zero, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
          mul_zero, add_zero, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
      simp only [Nat.add_sub_cancel]
      have hc : PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
          ((k + 1 : ℕ) : PowerSeries ℚ) =
          PowerSeries.C (p : ℚ) * PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) := by
        rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast],
            ← map_mul, ← map_mul]
        congr 1
        rw [pow_succ', Nat.factorial_succ, Nat.cast_mul]
        have hpos : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hpos]
      calc
        PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
            (((k + 1 : ℕ) : PowerSeries ℚ) * (F ^ k * PowerSeries.derivative ℚ F))
          = (PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
              ((k + 1 : ℕ) : PowerSeries ℚ)) * (F ^ k * PowerSeries.derivative ℚ F) := by ring
        _ = PowerSeries.C (p : ℚ) * PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) *
              (F ^ k * PowerSeries.derivative ℚ F) := by rw [hc]
        _ = PowerSeries.C (p : ℚ) * (PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
              PowerSeries.derivative ℚ F := by ring
    have hE_split : Etrunc =
        (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) +
        PowerSeries.C ((p : ℚ) ^ N / (Nat.factorial N : ℚ)) * F ^ N :=
      Finset.sum_range_succ _ N
    have hderiv_C : PowerSeries.derivative ℚ (PowerSeries.C (p : ℚ) * F) =
        PowerSeries.C (p : ℚ) * PowerSeries.derivative ℚ F := by
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    intro n hn1 hnN
    rw [hderiv_E, hderiv_C]
    have hdiff :
        Etrunc * (PowerSeries.X * (PowerSeries.C (p : ℚ) * PowerSeries.derivative ℚ F)) -
        PowerSeries.X * (PowerSeries.C (p : ℚ) *
          (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
          PowerSeries.derivative ℚ F) =
        PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) *
          (F ^ N * (PowerSeries.X * PowerSeries.derivative ℚ F)) := by
      rw [hE_split]
      have hcp : PowerSeries.C ((p : ℚ) ^ N / (Nat.factorial N : ℚ)) * PowerSeries.C (p : ℚ) =
          PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) := by
        rw [← map_mul]; congr 1; rw [pow_succ]; ring
      linear_combination (F ^ N * PowerSeries.X * PowerSeries.derivative ℚ F) * hcp
    have hzero : PowerSeries.coeff n
        (PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) *
          (F ^ N * (PowerSeries.X * PowerSeries.derivative ℚ F))) = 0 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (F ^ N) * PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ F))]
      have hsum0 :
          ∑ k ∈ Finset.range (n + 1),
            PowerSeries.coeff k (F ^ N) * PowerSeries.coeff (n - k) (PowerSeries.X * PowerSeries.derivative ℚ F) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkl : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        by_cases hkn : k = n
        · subst hkn; rw [Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero]
        · rw [hFpow_zero N k (by omega), zero_mul]
      rw [hsum0, mul_zero]
    have hsub := congr_arg (PowerSeries.coeff n) hdiff
    rw [map_sub, hzero] at hsub
    linarith
  have hE_eq := eq_expSeries_upTo hE0 hE_ode
  intro n hn1 hnN
  rw [← hE_eq n hnN]
  simp only [Etrunc, map_sum, PowerSeries.coeff_C_mul]
  rw [Finset.sum_range_succ', add_div, Finset.sum_div]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    PowerSeries.coeff_one, show n ≠ 0 by omega, ↓reduceIte, zero_div, add_zero]
  refine isPInt_sum hp _ _ fun k _ => ?_
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrew : ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff n (F ^ (k + 1)) / (p : ℚ) =
      ((p : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff n (F ^ (k + 1)) := by
    rw [pow_succ]; field_simp [hp0]
  rw [hrew]
  exact isPInt_mul hp (by simpa using isPInt_pow_div_factorial hp (show 1 ≤ k + 1 by omega))
    (hFpow_pInt (k + 1) n hnN)

/-- Freshman's dream for `p`-integral power series: if `H` has `p`-integral coefficients `≤ n`,
then `([X^n] H^p - (if p ∣ n then ([X^(n/p)] H)^p else 0)) / p` is `p`-integral! -/
private lemma freshman_dream_series {p n : ℕ} (hp : p.Prime) {H : PowerSeries ℚ}
    (hHp : ∀ j ≤ n, isPInt p (PowerSeries.coeff j H)) :
    isPInt p ((PowerSeries.coeff n (H ^ p) -
      if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0) / (p : ℚ)) := by
  have hden_nd : ∀ j ∈ Finset.range (n + 1), ¬ p ∣ (PowerSeries.coeff j H).den := fun j hj =>
    not_dvd_den_of_isPInt hp (hHp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  set D : ℕ := ∏ j ∈ Finset.range (n + 1), (PowerSeries.coeff j H).den
  have hD_nd : ¬ p ∣ D := by
    intro h
    obtain ⟨j, hj, hjd⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp h
    exact hden_nd j hj hjd
  have hD0 : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by intro h; rw [h] at hD_nd; exact hD_nd (dvd_zero p))
  -- Build the integer polynomial `Pz ∈ ℤ[X]` agreeing with `D * H` through degree `n`!
  have hDH_int : ∀ j, ∃ z : ℤ, (if j ≤ n then (D : ℚ) * PowerSeries.coeff j H else 0) = (z : ℚ) := by
    intro j
    by_cases hjn : j ≤ n
    · simp only [hjn, ↓reduceIte]
      have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hdiv : (PowerSeries.coeff j H).den ∣ D := Finset.dvd_prod_of_mem _ hmem
      obtain ⟨c, hc⟩ := hdiv
      set x := PowerSeries.coeff j H
      have hq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
      have hqd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
      refine ⟨x.num * (c : ℤ), ?_⟩
      calc (D : ℚ) * x
        _ = (x.den : ℚ) * (c : ℚ) * ((x.num : ℚ) / (x.den : ℚ)) := by
              rw [hc, Nat.cast_mul]; congr 1
        _ = ((x.num * (c : ℤ) : ℤ) : ℚ) := by
              push_cast; field_simp [hqd0]
    · exact ⟨0, by simp [hjn]⟩
  choose z hz using hDH_int
  let Pz : Polynomial ℤ := ∑ j ∈ Finset.range (n + 1), Polynomial.C (z j) * Polynomial.X ^ j
  have hPz_coeff : ∀ j ≤ n, (Pz.coeff j : ℚ) = (D : ℚ) * PowerSeries.coeff j H := by
    intro j hj
    simp only [Pz, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte, mul_one]; have := hz j; simpa [hj] using this.symm
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hPz_pow : ((Pz ^ p).coeff n : ℚ) = (D : ℚ) ^ p * PowerSeries.coeff n (H ^ p) := by
    have hagree : ∀ (t r : ℕ), r ≤ n →
        PowerSeries.coeff r ((Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ))) ^ t) =
        PowerSeries.coeff r ((PowerSeries.C (D : ℚ) * H) ^ t) := by
      intro t
      induction t with
      | zero => intro r _; rfl
      | succ t iht =>
          intro r hr
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a ((Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ))) ^ t) *
                  PowerSeries.coeff b (Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ)))),
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a ((PowerSeries.C (D : ℚ) * H) ^ t) *
                  PowerSeries.coeff b (PowerSeries.C (D : ℚ) * H))]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hal : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          rw [iht a (by omega), Polynomial.coeff_coe, Polynomial.coeff_map, Int.coe_castRingHom,
              PowerSeries.coeff_C_mul]
          dsimp only
          rw [hPz_coeff (r - a) (by omega)]
    have h := hagree p n (le_refl n)
    rw [← Polynomial.coe_pow, ← Polynomial.map_pow, Polynomial.coeff_coe, Polynomial.coeff_map,
        Int.coe_castRingHom, mul_pow, ← map_pow, PowerSeries.coeff_C_mul] at h
    exact h
  -- Reduce `Pz ^ p` modulo `p` in `(ZMod p)[X]` using `Finset.sum_pow_char`!
  have : Fact p.Prime := ⟨hp⟩
  have hmod : (p : ℤ) ∣ ((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hpoly_mod : (Pz.map (Int.castRingHom (ZMod p))) ^ p =
        ∑ j ∈ Finset.range (n + 1), Polynomial.C ((z j : ZMod p) ^ p) * Polynomial.X ^ (p * j) := by
      have h1 : Pz.map (Int.castRingHom (ZMod p)) =
          ∑ j ∈ Finset.range (n + 1), Polynomial.C (z j : ZMod p) * Polynomial.X ^ j := by
        simp [Pz, Polynomial.map_sum]
      rw [h1, ← frobenius_def, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [frobenius_def, mul_pow, ← map_pow, ← pow_mul, mul_comm j p]
    have hc := congr_arg (fun Q : Polynomial (ZMod p) => Q.coeff n) hpoly_mod
    rw [← Polynomial.map_pow, Polynomial.coeff_map, Int.coe_castRingHom] at hc
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    rw [Int.cast_sub, hc]
    by_cases hdiv : p ∣ n
    · simp only [hdiv, ↓reduceIte, Int.cast_pow]
      obtain ⟨m, rfl⟩ := hdiv
      have hm_le : m ≤ p * m := Nat.le_mul_of_pos_left m hp.pos
      rw [Finset.sum_eq_single m]
      · simp [Nat.mul_div_cancel_left _ hp.pos]
      · intro b _ hne
        have : p * m ≠ p * b := fun h => hne (Nat.eq_of_mul_eq_mul_left hp.pos h).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hdiv, ↓reduceIte, Int.cast_zero, sub_zero]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : n ≠ p * b := fun h => hdiv ⟨b, h⟩
      simp [this]
  obtain ⟨t, ht⟩ := hmod
  have hDp_nd : ¬ p ∣ D ^ p := fun h => hD_nd (hp.dvd_of_dvd_pow h)
  refine ⟨t, D ^ p, hDp_nd, ?_⟩
  have ht_q : ((Pz ^ p).coeff n : ℚ) - (if p ∣ n then ((z (n / p) : ℚ) ^ p) else 0) =
      (p : ℚ) * (t : ℚ) := by
    have : ((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0 : ℤ) = (p : ℤ) * t := ht
    have hq : (((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0 : ℤ) : ℚ) = (p : ℚ) * (t : ℚ) := by
      exact_mod_cast this
    rw [← hq]
    split_ifs <;> push_cast <;> ring
  rw [hPz_pow] at ht_q
  have hrhs : (if p ∣ n then (z (n / p) : ℚ) ^ p else 0) =
      (D : ℚ) ^ p * (if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0) := by
    split_ifs
    · have hle : n / p ≤ n := Nat.div_le_self n p
      have hzn := hz (n / p)
      simp only [hle, ↓reduceIte] at hzn
      rw [← mul_pow, hzn]
    · ring
  rw [hrhs] at ht_q
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hDp0 : (D : ℚ) ^ p ≠ 0 := pow_ne_zero p hD0
  push_cast
  field_simp [hp0, hDp0]
  linarith

/-- Fermat's Little Theorem for `p`-integral rationals: `(x^p - x) / p` is `p`-integral! -/
private lemma fermat_pInt {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    isPInt p ((x ^ p - x) / (p : ℚ)) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by intro h; subst h; exact hb (dvd_zero p))
  have : Fact p.Prime := ⟨hp⟩
  have hmod : (p : ℤ) ∣ (a ^ p - a * (b : ℤ) ^ (p - 1)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card]
    have hb_ne : (b : ZMod p) ≠ 0 := by
      intro h; exact hb ((ZMod.natCast_eq_zero_iff b p).mp h)
    rw [ZMod.pow_card_sub_one_eq_one hb_ne, mul_one, sub_self]
  obtain ⟨t, ht⟩ := hmod
  have hbp_nd : ¬ p ∣ b ^ p := fun h => hb (hp.dvd_of_dvd_pow h)
  refine ⟨t, b ^ p, hbp_nd, ?_⟩
  have ht_q : (a : ℚ) ^ p - (a : ℚ) * (b : ℚ) ^ (p - 1) = (p : ℚ) * (t : ℚ) := by exact_mod_cast ht
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hbp0 : (b : ℚ) ^ p ≠ 0 := pow_ne_zero p hb0
  have hbp_split : (b : ℚ) ^ p = (b : ℚ) * (b : ℚ) ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.two_le; omega
  push_cast
  rw [div_pow]
  field_simp [hp0, hb0, hbp0]
  linear_combination (b : ℚ) * ht_q - (a : ℚ) * hbp_split

/-- **Dwork's Lemma (truncated)**: if `G(0) = 0` and `(G(X^p) - p * G(X)) / p` has `p`-integral
coefficients through degree `N`, then `expSeries G` has `p`-integral coefficients through degree `N`! -/
private lemma dwork_lemma {p N : ℕ} (hp : p.Prime) {G : PowerSeries ℚ}
    (hG0 : PowerSeries.coeff 0 G = 0)
    (hG : ∀ m, 1 ≤ m → m ≤ N →
      isPInt p (PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ))) :
    ∀ n ≤ N, isPInt p (PowerSeries.coeff n (expSeries G)) := by
  set H := expSeries G
  let F : PowerSeries ℚ := PowerSeries.mk fun m =>
    if m = 0 then 0 else PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ)
  have hF0 : PowerSeries.coeff 0 F = 0 := by simp [F]
  have hFp : ∀ m ≤ N, isPInt p (PowerSeries.coeff m F) := by
    intro m hm
    rw [PowerSeries.coeff_mk]
    split_ifs with h0
    · exact isPInt_zero hp
    · exact hG m (by omega) hm
  have hCF_eq : PowerSeries.C (p : ℚ) * F = substPow p G - PowerSeries.C (p : ℚ) * G := by
    apply PowerSeries.ext; intro m
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [↓reduceIte, mul_zero, map_sub, coeff_substPow, dvd_zero, Nat.zero_div,
        PowerSeries.coeff_C_mul, hG0, sub_zero]
    · simp only [hm0, ↓reduceIte]
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp [hp0]
  set E := expSeries (PowerSeries.C (p : ℚ) * F)
  have hE0 : PowerSeries.coeff 0 E = 1 := coeff_zero_expSeries _
  have hEp : ∀ m, 1 ≤ m → m ≤ N → isPInt p (PowerSeries.coeff m E / (p : ℚ)) :=
    exp_p_mul_div_p_isPInt hp hF0 hFp
  have hH_rel : substPow p H = H ^ p * E := by
    rw [← expSeries_substPow hp.pos G, ← expSeries_nsmul G p, ← expSeries_add]
    congr 1
    rw [hCF_eq]; ring
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [coeff_zero_expSeries]; exact isPInt_int hp 1
    | succ n' =>
        set n := n' + 1
        let Htrunc : PowerSeries ℚ := PowerSeries.mk fun j => if j < n then PowerSeries.coeff j H else 0
        have hHt_pInt : ∀ j, isPInt p (PowerSeries.coeff j Htrunc) := by
          intro j; rw [PowerSeries.coeff_mk]
          split_ifs with hj
          · exact ih j hj (by omega)
          · exact isPInt_zero hp
        have hHt_pow_pInt : ∀ (k j : ℕ), isPInt p (PowerSeries.coeff j (Htrunc ^ k)) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs
              · exact isPInt_int hp 1
              · exact isPInt_zero hp
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (Htrunc ^ k) * PowerSeries.coeff r Htrunc)]
              exact isPInt_sum hp _ _ fun i _ => isPInt_mul hp (ihk i) (hHt_pInt (j - i))
        have hHt0 : PowerSeries.coeff 0 Htrunc = 1 := by
          rw [PowerSeries.coeff_mk, if_pos (by omega : 0 < n), coeff_zero_expSeries]
        let R : PowerSeries ℚ := H - Htrunc
        have hR_lt : ∀ j < n, PowerSeries.coeff j R = 0 := by
          intro j hj
          rw [map_sub, PowerSeries.coeff_mk, if_pos hj, sub_self]
        have hR_n : PowerSeries.coeff n R = PowerSeries.coeff n H := by
          rw [map_sub, PowerSeries.coeff_mk, if_neg (by omega), sub_zero]
        have hR_pow_zero : ∀ (k j : ℕ), 2 ≤ k → j ≤ n → PowerSeries.coeff j (R ^ k) = 0 := by
          intro k j hk hj
          obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
          rw [pow_add, sq, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i r => PowerSeries.coeff i (R * R) * PowerSeries.coeff r (R ^ k'))]
          refine Finset.sum_eq_zero fun i hi => ?_
          have hil : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hRR : PowerSeries.coeff i (R * R) = 0 := by
            rw [PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a R * PowerSeries.coeff b R)]
            refine Finset.sum_eq_zero fun a ha => ?_
            have hal : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            by_cases han : a < n
            · rw [hR_lt a han, zero_mul]
            · rw [hR_lt (i - a) (by omega), mul_zero]
          rw [hRR, zero_mul]
        -- Expand `H ^ p = (R + Htrunc) ^ p` and read off coefficients `≤ n`!
        have hHp_eq : H ^ p = ∑ k ∈ Finset.range (p + 1),
            PowerSeries.C ((Nat.choose p k : ℕ) : ℚ) * (R ^ k * Htrunc ^ (p - k)) := by
          have hHR : H = R + Htrunc := by simp [R]
          rw [hHR, add_pow]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show ((Nat.choose p k : ℕ) : PowerSeries ℚ) = PowerSeries.C ((Nat.choose p k : ℕ) : ℚ) by
            rw [map_natCast]]
          ring
        have hHp_lt : ∀ j < n, PowerSeries.coeff j (H ^ p) = PowerSeries.coeff j (Htrunc ^ p) := by
          intro j hj
          rw [hHp_eq, map_sum, Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range p,
                PowerSeries.coeff j (PowerSeries.C ((Nat.choose p (k + 1) : ℕ) : ℚ) *
                  (R ^ (k + 1) * Htrunc ^ (p - (k + 1)))) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a (R ^ (k + 1)) * PowerSeries.coeff b (Htrunc ^ (p - (k + 1))))]
            have hsum0 :
                ∑ a ∈ Finset.range (j + 1),
                  PowerSeries.coeff a (R ^ (k + 1)) * PowerSeries.coeff (j - a) (Htrunc ^ (p - (k + 1))) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              have hal : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              have hRa : PowerSeries.coeff a (R ^ (k + 1)) = 0 := by
                rw [pow_succ', PowerSeries.coeff_mul,
                    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                      (fun u v => PowerSeries.coeff u R * PowerSeries.coeff v (R ^ k))]
                refine Finset.sum_eq_zero fun u hu => ?_
                have hul : u ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
                rw [hR_lt u (by omega), zero_mul]
              rw [hRa, zero_mul]
            rw [hsum0, mul_zero]
          rw [htail, zero_add]
          simp
        have hHp_n : PowerSeries.coeff n (H ^ p) =
            PowerSeries.coeff n (Htrunc ^ p) + (p : ℚ) * PowerSeries.coeff n H := by
          rw [hHp_eq, map_sum, Finset.sum_range_succ']
          obtain ⟨p', hp'⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
          rw [hp', Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range p',
                PowerSeries.coeff n (PowerSeries.C ((Nat.choose (p' + 1) (k + 1 + 1) : ℕ) : ℚ) *
                  (R ^ (k + 1 + 1) * Htrunc ^ (p' + 1 - (k + 1 + 1)))) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a (R ^ (k + 1 + 1)) *
                    PowerSeries.coeff b (Htrunc ^ (p' + 1 - (k + 1 + 1))))]
            have hsum0 :
                ∑ a ∈ Finset.range (n + 1),
                  PowerSeries.coeff a (R ^ (k + 1 + 1)) *
                    PowerSeries.coeff (n - a) (Htrunc ^ (p' + 1 - (k + 1 + 1))) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              have hal : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              rw [hR_pow_zero (k + 1 + 1) a (by omega) hal, zero_mul]
            rw [hsum0, mul_zero]
          rw [htail, zero_add, ← hp']
          have hterm1 : PowerSeries.coeff n (PowerSeries.C ((Nat.choose p 1 : ℕ) : ℚ) *
              (R ^ 1 * Htrunc ^ (p - 1))) = (p : ℚ) * PowerSeries.coeff n H := by
            rw [Nat.choose_one_right, pow_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a R * PowerSeries.coeff b (Htrunc ^ (p - 1))),
                Finset.sum_range_succ]
            have h0 : ∑ a ∈ Finset.range n, PowerSeries.coeff a R * PowerSeries.coeff (n - a) (Htrunc ^ (p - 1)) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              rw [hR_lt a (Finset.mem_range.mp ha), zero_mul]
            rw [h0, zero_add, hR_n, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
                ← PowerSeries.coeff_zero_eq_constantCoeff, hHt0, one_pow, mul_one]
          rw [hterm1]
          simp [add_comm]
        -- Extract `[X^n]` from `substPow p H = H ^ p * E`!
        have hrel_n := congr_arg (PowerSeries.coeff n) hH_rel
        rw [coeff_substPow, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (H ^ p) * PowerSeries.coeff j E),
            Finset.sum_range_succ, Nat.sub_self, hE0, mul_one, hHp_n] at hrel_n
        have hsum_tail :
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (H ^ p) * PowerSeries.coeff (n - k) E =
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * PowerSeries.coeff (n - k) E := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hHp_lt k (Finset.mem_range.mp hk)]
        rw [hsum_tail] at hrel_n
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hHn_eq : PowerSeries.coeff n H =
            ((if p ∣ n then PowerSeries.coeff (n / p) H else 0) - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) -
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * (PowerSeries.coeff (n - k) E / (p : ℚ)) := by
          have hdiv_sum :
              ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * (PowerSeries.coeff (n - k) E / (p : ℚ)) =
              (∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * PowerSeries.coeff (n - k) E) / (p : ℚ) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun k _ => by ring
          rw [hdiv_sum]
          field_simp [hp0]
          linarith
        rw [hHn_eq]
        refine isPInt_sub hp ?_ ?_
        · -- First term: combine `freshman_dream_series` and `fermat_pInt`!
          have hfr := freshman_dream_series (n := n) hp (fun j _ => hHt_pInt j)
          have hHt_div : (if p ∣ n then (PowerSeries.coeff (n / p) Htrunc) ^ p else 0) =
              if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0 := by
            split_ifs with hdiv
            · have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
              rw [PowerSeries.coeff_mk, if_pos hlt]
            · rfl
          rw [hHt_div] at hfr
          by_cases hdiv : p ∣ n
          · simp only [hdiv, ↓reduceIte] at hfr ⊢
            have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
            have hfer := fermat_pInt hp (ih (n / p) hlt (by omega))
            have hrew : (PowerSeries.coeff (n / p) H - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) =
                -((PowerSeries.coeff (n / p) H ^ p - PowerSeries.coeff (n / p) H) / (p : ℚ)) -
                ((PowerSeries.coeff n (Htrunc ^ p) - PowerSeries.coeff (n / p) H ^ p) / (p : ℚ)) := by
              ring
            rw [hrew]
            exact isPInt_sub hp (isPInt_neg hfer) hfr
          · simp only [hdiv, ↓reduceIte, sub_zero] at hfr ⊢
            have hrew : (0 - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) =
                -(PowerSeries.coeff n (Htrunc ^ p) / (p : ℚ)) := by ring
            rw [hrew]
            exact isPInt_neg hfr
        · -- Second term: `∑_{k < n} coeff k (Htrunc ^ p) * (coeff (n - k) E / p)`
          refine isPInt_sum hp _ _ fun k hk => ?_
          have hkl : k < n := Finset.mem_range.mp hk
          exact isPInt_mul hp (hHt_pow_pInt p k) (hEp (n - k) (by omega) (by omega))

/-! ### Part 5: Binomial lifting in `PowerSeries ℤ` & Dwork criterion for `∑ f_n(X)^n X^n / n` -/

private lemma pow_prime_pow_sub_dvd_series {p : ℕ} (hp : p.Prime)
    {A B : PowerSeries ℚ}
    (hA : ∀ j, ∃ z : ℤ, PowerSeries.coeff j A = (z : ℚ))
    (hB : ∀ j, ∃ z : ℤ, PowerSeries.coeff j B = (z : ℚ))
    (hAB : ∀ j, isPInt p ((PowerSeries.coeff j A - PowerSeries.coeff j B) / (p : ℚ))) :
    ∀ (v : ℕ) (j : ℕ), isPInt p ((PowerSeries.coeff j (A ^ (p ^ v)) - PowerSeries.coeff j (B ^ (p ^ v))) /
      ((p ^ (v + 1) : ℕ) : ℚ)) := by
  -- Work via `D := A - B = C p * U` where `U` has integer coefficients!
  have hAB_int : ∀ j, ∃ t : ℤ, PowerSeries.coeff j A - PowerSeries.coeff j B = (p : ℚ) * (t : ℚ) := by
    intro j
    obtain ⟨za, hza⟩ := hA j
    obtain ⟨zb, hzb⟩ := hB j
    have hnd := not_dvd_den_of_isPInt hp (hAB j)
    have hdiv : (p : ℤ) ∣ (za - zb) := by
      obtain ⟨num, den, hden, heq⟩ := hAB j
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hden0 : (den : ℚ) ≠ 0 := by
        exact_mod_cast (show den ≠ 0 by intro h; subst h; exact hden (dvd_zero p))
      rw [hza, hzb] at heq
      have h1 : ((za : ℚ) - (zb : ℚ)) * (den : ℚ) = (num : ℚ) * (p : ℚ) := by
        field_simp [hp0, hden0] at heq; linarith
      have hz : (za - zb) * (den : ℤ) = num * (p : ℤ) := by exact_mod_cast h1
      have hcop : IsCoprime (p : ℤ) (den : ℤ) := (hp.coprime_iff_not_dvd.mpr hden).isCoprime
      exact hcop.dvd_of_dvd_mul_right (by rw [hz]; exact dvd_mul_left (p : ℤ) num)
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨t, ?_⟩
    rw [hza, hzb]; exact_mod_cast ht
  -- Lift `A = B + C (p : ℚ) * U` by induction on `v`!
  have hlift : ∀ v : ℕ, ∃ U : PowerSeries ℚ,
      (∀ j, ∃ z : ℤ, PowerSeries.coeff j U = (z : ℚ)) ∧
      A ^ (p ^ v) = B ^ (p ^ v) + PowerSeries.C ((p ^ (v + 1) : ℕ) : ℚ) * U := by
    intro v
    induction v with
    | zero =>
        choose t ht using hAB_int
        refine ⟨PowerSeries.mk (fun j => (t j : ℚ)), fun j => ⟨t j, by simp⟩, ?_⟩
        apply PowerSeries.ext; intro j
        rw [pow_zero, pow_one, pow_one, zero_add, pow_one, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
        linarith [ht j]
    | succ v ih =>
        obtain ⟨U, hU_int, hU_eq⟩ := ih
        have hB_pow_int : ∀ (k j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (B ^ k) = (z : ℚ) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (B ^ k) * PowerSeries.coeff r B)]
              choose z1 hz1 using ihk
              choose z2 hz2 using hB
              refine ⟨∑ i ∈ Finset.range (j + 1), z1 i * z2 (j - i), ?_⟩
              rw [Int.cast_sum]
              refine Finset.sum_congr rfl fun i _ => by rw [hz1 i, hz2 (j - i), Int.cast_mul]
        have hU_pow_int : ∀ (k j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (U ^ k) = (z : ℚ) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (U ^ k) * PowerSeries.coeff r U)]
              choose z1 hz1 using ihk
              choose z2 hz2 using hU_int
              refine ⟨∑ i ∈ Finset.range (j + 1), z1 i * z2 (j - i), ?_⟩
              rw [Int.cast_sum]
              refine Finset.sum_congr rfl fun i _ => by rw [hz1 i, hz2 (j - i), Int.cast_mul]
        have hmul_int : ∀ {X Y : PowerSeries ℚ},
            (∀ j, ∃ z : ℤ, PowerSeries.coeff j X = (z : ℚ)) →
            (∀ j, ∃ z : ℤ, PowerSeries.coeff j Y = (z : ℚ)) →
            ∀ j, ∃ z : ℤ, PowerSeries.coeff j (X * Y) = (z : ℚ) := by
          intro X Y hX hY j
          rw [PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i r => PowerSeries.coeff i X * PowerSeries.coeff r Y)]
          choose zx hzx using hX
          choose zy hzy using hY
          refine ⟨∑ i ∈ Finset.range (j + 1), zx i * zy (j - i), ?_⟩
          rw [Int.cast_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [hzx i, hzy (j - i), Int.cast_mul]
        -- Expand `A ^ (p^(v+1)) = (B^(p^v) + p^(v+1) * U)^p`!
        let c (k : ℕ) : ℕ :=
          if k + 1 = p then p ^ ((v + 1) * p - (v + 2))
          else (Nat.choose p (k + 1) / p) * p ^ ((v + 1) * k)
        let V : PowerSeries ℚ :=
          ∑ k ∈ Finset.range p,
            PowerSeries.C ((c k : ℕ) : ℚ) * (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1)))
        refine ⟨V, ?_, ?_⟩
        · intro j
          simp only [V, map_sum, PowerSeries.coeff_C_mul]
          have hterm : ∀ k,
              ∃ z : ℤ, ((c k : ℕ) : ℚ) * PowerSeries.coeff j (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) = (z : ℚ) := by
            intro k
            have hB_int' : ∀ r, ∃ z : ℤ, PowerSeries.coeff r ((B ^ (p ^ v)) ^ (p - (k + 1))) = (z : ℚ) := by
              rw [← pow_mul]; exact hB_pow_int _
            obtain ⟨z, hz⟩ := hmul_int (hU_pow_int (k + 1)) hB_int' j
            exact ⟨(c k : ℤ) * z, by rw [hz]; push_cast; ring⟩
          choose zf hzf using hterm
          refine ⟨∑ k ∈ Finset.range p, zf k, ?_⟩
          rw [Int.cast_sum]
          exact Finset.sum_congr rfl fun k _ => hzf k
        · rw [pow_succ, pow_mul, pow_mul, hU_eq, add_comm (B ^ (p ^ v)), add_pow, Finset.sum_range_succ']
          simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
          rw [add_comm _ ((B ^ (p ^ v)) ^ p)]
          congr 1
          simp only [V, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hklt : k < p := Finset.mem_range.mp hk
          rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul]
          have hcoeff_eq :
              PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) *
                ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ) =
              PowerSeries.C (((p ^ (v + 2) : ℕ) : ℚ) * ((c k : ℕ) : ℚ)) := by
            rw [show ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ) =
              PowerSeries.C ((Nat.choose p (k + 1) : ℕ) : ℚ) by rw [map_natCast], ← map_mul]
            congr 1
            norm_cast
            simp only [c]
            by_cases hkp : k + 1 = p
            · simp only [hkp, ↓reduceIte, Nat.choose_self, mul_one]
              rw [← pow_mul, ← pow_add]
              congr 1
              have hp2 : 2 ≤ p := hp.two_le
              have hle : v + 2 ≤ (v + 1) * p := by nlinarith
              omega
            · simp only [hkp, ↓reduceIte]
              have hch : p ∣ Nat.choose p (k + 1) := hp.dvd_choose_self (by omega) (by omega)
              have hch_eq : p * (Nat.choose p (k + 1) / p) = Nat.choose p (k + 1) := Nat.mul_div_cancel' hch
              rw [← pow_mul]
              have hexp : (v + 1) * (k + 1) = (v + 1) + (v + 1) * k := by ring
              rw [hexp, pow_add, pow_succ (a := p) (v + 1)]
              calc
                p ^ (v + 1) * p ^ ((v + 1) * k) * Nat.choose p (k + 1)
                  = p ^ (v + 1) * p ^ ((v + 1) * k) * (p * (Nat.choose p (k + 1) / p)) := by rw [hch_eq]
                _ = p ^ (v + 1) * p * (Nat.choose p (k + 1) / p * p ^ ((v + 1) * k)) := by ring
          calc
            PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) * U ^ (k + 1) *
                (B ^ (p ^ v)) ^ (p - (k + 1)) * ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ)
              = (PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) *
                  ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ)) *
                  (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) := by ring
            _ = PowerSeries.C (((p ^ (v + 2) : ℕ) : ℚ) * ((c k : ℕ) : ℚ)) *
                  (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) := by rw [hcoeff_eq]
  intro v j
  obtain ⟨U, hU_int, hU_eq⟩ := hlift v
  obtain ⟨z, hz⟩ := hU_int j
  have hdiff : PowerSeries.coeff j (A ^ (p ^ v)) - PowerSeries.coeff j (B ^ (p ^ v)) =
      ((p ^ (v + 1) : ℕ) : ℚ) * (z : ℚ) := by
    have := congr_arg (PowerSeries.coeff j) hU_eq
    rw [map_add, PowerSeries.coeff_C_mul, hz] at this
    linarith
  rw [hdiff]
  have hpv0 : ((p ^ (v + 1) : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p ^ (v + 1) := pow_pos hp.pos _
    exact_mod_cast this.ne'
  rw [mul_div_cancel_left₀ _ hpv0]
  exact isPInt_int hp z

/-- General Dwork integrality theorem for `G = ∑_{n=1}^N (f n)^n * X^n / n`:
if each `f n` has integer coefficients and `(f (p * n))^p ≡ f(n)(X^p) (mod p)` for all primes `p`
and `1 ≤ n ≤ N / p`, then `expSeries G` has integer coefficients through degree `N`! -/
private lemma dwork_pow_logSeries_isInt (N : ℕ) (f : ℕ → PowerSeries ℚ)
    (hf_int : ∀ n j, ∃ z : ℤ, PowerSeries.coeff j (f n) = (z : ℚ))
    (hf_cong : ∀ (p n j : ℕ), p.Prime → 1 ≤ n → n * p ≤ N →
      isPInt p ((PowerSeries.coeff j ((f (p * n)) ^ p) - PowerSeries.coeff j (substPow p (f n))) / (p : ℚ))) :
    ∀ k ≤ N, ∃ z : ℤ,
      PowerSeries.coeff k (expSeries (∑ n ∈ Finset.Icc 1 N,
        PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((f n) ^ n * PowerSeries.X ^ n))) = (z : ℚ) := by
  set G : PowerSeries ℚ := ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((f n) ^ n * PowerSeries.X ^ n)
  have hG0 : PowerSeries.coeff 0 G = 0 := by
    simp only [G, map_sum, PowerSeries.coeff_C_mul]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [mul_comm ((f n) ^ n), PowerSeries.coeff_X_pow_mul']
    simp [show ¬ n ≤ 0 by omega]
  intro k hk
  apply isInt_of_forall_prime_isPInt
  intro p hp
  apply dwork_lemma hp hG0 _ k hk
  intro m hm1 hmN
  -- Compute `[X^m] (substPow p G - C p * G) / p`!
  have hsubst_G : substPow p G = ∑ n ∈ Finset.Icc 1 N,
      PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) := by
    apply PowerSeries.ext; intro r
    simp only [G, coeff_substPow, map_sum, PowerSeries.coeff_C_mul]
    by_cases hpr : p ∣ r
    · simp only [hpr, ↓reduceIte]
      obtain ⟨r', rfl⟩ := hpr
      rw [Nat.mul_div_cancel_left _ hp.pos]
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      rw [mul_comm ((f n) ^ n), PowerSeries.coeff_X_pow_mul',
          mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul',
          ← substPow_pow hp.pos (f n) n, coeff_substPow]
      by_cases hnr : n ≤ r'
      · have hpn : p * n ≤ p * r' := Nat.mul_le_mul_left p hnr
        have hsub : p * r' - p * n = p * (r' - n) := (Nat.mul_sub_left_distrib p r' n).symm
        simp only [hnr, hpn, ↓reduceIte, hsub, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos]
      · have hpn : ¬ p * n ≤ p * r' := fun h => hnr (Nat.le_of_mul_le_mul_left h hp.pos)
        simp [hnr, hpn]
    · simp only [hpr, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul']
      split_ifs with hpn
      · rw [← substPow_pow hp.pos (f n) n, coeff_substPow]
        have hndiv : ¬ p ∣ r - p * n := fun h => hpr (by
          rw [← Nat.sub_add_cancel hpn]; exact dvd_add h (dvd_mul_right p n))
        simp [hndiv]
      · ring
  -- Split `Icc 1 N` in `C p * G` into multiples of `p` and non-multiples of `p`!
  have hG_split :
      PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ) =
      (∑ n ∈ (Finset.Icc 1 (N / p)),
        ((PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) -
          PowerSeries.coeff m (((f (p * n)) ^ p) ^ n * PowerSeries.X ^ (p * n))) /
          ((p * n : ℕ) : ℚ))) -
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
        (PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n) / (n : ℚ))) := by
    rw [map_sub, hsubst_G, PowerSeries.coeff_C_mul]
    simp only [G, map_sum, PowerSeries.coeff_C_mul]
    -- Restrict the `substPow p G` sum to `Icc 1 (N / p)` since for `n > N / p`, `p * n > N ≥ m`!
    have hsubst_trim :
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℚ)) * PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) =
        ∑ n ∈ Finset.Icc 1 (N / p), (1 / (n : ℚ)) * PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) := by
      symm
      refine Finset.sum_subset (by
        intro n hn; simp only [Finset.mem_Icc] at hn ⊢
        exact ⟨hn.1, le_trans hn.2 (Nat.div_le_self N p)⟩) ?_
      intro n hn hnot
      simp only [Finset.mem_Icc] at hn hnot
      have hgt : N < p * n := by
        have hlt : N / p < n := by omega
        have := Nat.lt_mul_of_div_lt hlt hp.pos
        linarith
      rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
    -- Split `G` sum into `p ∣ n` and `¬ p ∣ n`!
    have hG_part :
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℚ)) * PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n) =
        (∑ n ∈ Finset.Icc 1 (N / p),
          (1 / ((p * n : ℕ) : ℚ)) * PowerSeries.coeff m (((f (p * n)) ^ p) ^ n * PowerSeries.X ^ (p * n))) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
          (1 / (n : ℚ)) * PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)]
      congr 1
      symm
      refine Finset.sum_nbij (fun n => p * n) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        refine ⟨⟨by have := hp.pos; nlinarith, ?_⟩, dvd_mul_right p n⟩
        have := Nat.mul_le_mul_left p hn.2
        exact le_trans this (Nat.mul_div_le N p)
      · intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hp.pos hab
      · intro k hk
        obtain ⟨hkIcc, ⟨n, rfl⟩⟩ := Finset.mem_filter.mp hk
        obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkIcc
        refine ⟨n, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra h0; have : n = 0 := by omega
          rw [this, mul_zero] at hk1; omega
        · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith)
      · intro n _; rw [← pow_mul]
    rw [hsubst_trim, hG_part]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [mul_add, sub_add_eq_sub_sub, sub_div, sub_div, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; field_simp [hp0]
    · refine Finset.sum_congr rfl fun n _ => ?_
      field_simp [hp0]
  rw [hG_split]
  refine isPInt_sub hp ?_ ?_
  · -- First sum: for each `n ∈ Icc 1 (N / p)`, apply `pow_prime_pow_sub_dvd_series`!
    refine isPInt_sum hp _ _ fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n * p ≤ N := by
      have := (Finset.mem_Icc.mp hn).2
      have := Nat.mul_le_mul_left p this
      linarith [Nat.mul_div_le N p]
    rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul',
        mul_comm (((f (p * n)) ^ p) ^ n), PowerSeries.coeff_X_pow_mul']
    by_cases hle : p * n ≤ m
    · simp only [hle, ↓reduceIte]
      set v := n.factorization p
      set u := n / p ^ v
      have hpow_dvd : p ^ v ∣ n := Nat.ordProj_dvd n p
      have hnu : p ^ v * u = n := Nat.mul_div_cancel' hpow_dvd
      have hpu : ¬ p ∣ u := by
        intro h
        have hpow1 : p ^ (v + 1) ∣ n := by
          rw [← hnu, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ v) h
        have hle' := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpow1
        omega
      have hA_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j ((f (p * n)) ^ p) = (z : ℚ) := by
        have hpow_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j ((f (p * n)) ^ t) = (z : ℚ) := by
          intro t
          induction t with
          | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ t iht =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun a b => PowerSeries.coeff a ((f (p * n)) ^ t) * PowerSeries.coeff b (f (p * n)))]
              choose z1 hz1 using iht
              choose z2 hz2 using hf_int (p * n)
              exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
                rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
        exact hpow_int p
      have hB_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j (substPow p (f n)) = (z : ℚ) := by
        intro j; rw [coeff_substPow]
        split_ifs
        · exact hf_int n (j / p)
        · exact ⟨0, by simp⟩
      have hlift := pow_prime_pow_sub_dvd_series hp hA_int hB_int
        (fun j => hf_cong p n j hp hn1 hnN) v
      -- Now raise to the `u`-th power: `A^(p^v * u) - B^(p^v * u) = (A^(p^v) - B^(p^v)) * ∑ ...`!
      set A' := ((f (p * n)) ^ p) ^ (p ^ v)
      set B' := (substPow p (f n)) ^ (p ^ v)
      have hA'B'_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (A' ^ t) = (z : ℚ) := by
        intro t
        have : A' ^ t = (f (p * n)) ^ (p * p ^ v * t) := by simp only [A', ← pow_mul]
        rw [this]
        induction (p * p ^ v * t) with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ s ihs =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((f (p * n)) ^ s) * PowerSeries.coeff b (f (p * n)))]
            choose z1 hz1 using ihs
            choose z2 hz2 using hf_int (p * n)
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      have hB'_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (B' ^ t) = (z : ℚ) := by
        intro t
        have : B' ^ t = (substPow p (f n)) ^ (p ^ v * t) := by simp only [B', ← pow_mul]
        rw [this]
        induction (p ^ v * t) with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ s ihs =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((substPow p (f n)) ^ s) * PowerSeries.coeff b (substPow p (f n)))]
            choose z1 hz1 using ihs
            choose z2 hz2 using hB_int
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      have hfactor : A' ^ u - B' ^ u = (A' - B') * ∑ i ∈ Finset.range u, A' ^ i * B' ^ (u - 1 - i) := by
        simpa [mul_comm] using (geom_sum₂_mul A' B' u).symm
      have hpn_eq : ((p * n : ℕ) : ℚ) = ((p ^ (v + 1) : ℕ) : ℚ) * (u : ℚ) := by
        have : p * n = p ^ (v + 1) * u := by rw [← hnu, pow_succ', mul_assoc]
        exact_mod_cast this
      have hrew : (PowerSeries.coeff (m - p * n) ((substPow p (f n)) ^ n) -
          PowerSeries.coeff (m - p * n) (((f (p * n)) ^ p) ^ n)) / ((p * n : ℕ) : ℚ) =
          -((PowerSeries.coeff (m - p * n) (A' ^ u - B' ^ u)) / ((p ^ (v + 1) : ℕ) : ℚ)) / (u : ℚ) := by
        have h1 : ((f (p * n)) ^ p) ^ n = A' ^ u := by
          simp only [A', ← pow_mul, mul_assoc, hnu]
        have h2 : (substPow p (f n)) ^ n = B' ^ u := by
          simp only [B', ← pow_mul, hnu]
        rw [h1, h2, map_sub, hpn_eq]
        ring
      rw [hrew]
      refine isPInt_div_nat hp (isPInt_neg ?_) hpu
      rw [hfactor, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (A' - B') *
              PowerSeries.coeff b (∑ i ∈ Finset.range u, A' ^ i * B' ^ (u - 1 - i))),
          Finset.sum_div]
      refine isPInt_sum hp _ _ fun a _ => ?_
      rw [mul_div_right_comm, map_sub]
      refine isPInt_mul hp (hlift a) ?_
      rw [map_sum]
      refine isPInt_sum hp _ _ fun i _ => ?_
      rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun x y => PowerSeries.coeff x (A' ^ i) * PowerSeries.coeff y (B' ^ (u - 1 - i)))]
      refine isPInt_sum hp _ _ fun x _ => ?_
      obtain ⟨z1, hz1⟩ := hA'B'_int i x
      obtain ⟨z2, hz2⟩ := hB'_int (u - 1 - i) (m - p * n - a - x)
      rw [hz1, hz2]
      exact isPInt_mul hp (isPInt_int hp z1) (isPInt_int hp z2)
    · simp [hle, isPInt_zero hp]
  · -- Second sum: `¬ p ∣ n`, and `(f n)^n` has integer coefficients!
    refine isPInt_sum hp _ _ fun n hn => ?_
    have hnp : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    refine isPInt_div_nat hp ?_ hnp
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
    split_ifs
    · have hpow_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j ((f n) ^ t) = (z : ℚ) := by
        intro t
        induction t with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ t iht =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((f n) ^ t) * PowerSeries.coeff b (f n))]
            choose z1 hz1 using iht
            choose z2 hz2 using hf_int n
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      obtain ⟨z, hz⟩ := hpow_int n (m - n)
      rw [hz]; exact isPInt_int hp z
    · exact isPInt_zero hp



/-! ### Part 6: Application to OEIS A163921 -/

private lemma coeff_logSeriesTrunc_congr (L : ℕ → ℤ) (f₁ f₂ : PowerSeries ℚ) (N₁ N₂ k : ℕ)
    (hk1 : k ≤ N₁) (hk2 : k ≤ N₂)
    (hf : ∀ j < k, PowerSeries.coeff j f₁ = PowerSeries.coeff j f₂) :
    PowerSeries.coeff k (logSeriesTrunc L f₁ N₁) = PowerSeries.coeff k (logSeriesTrunc L f₂ N₂) := by
  have htrim : ∀ (f : PowerSeries ℚ) (N : ℕ), k ≤ N →
      PowerSeries.coeff k (logSeriesTrunc L f N) = PowerSeries.coeff k (logSeriesTrunc L f k) := by
    intro f N hkN
    simp only [logSeriesTrunc, map_sum, PowerSeries.coeff_C_mul]
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hkN) ?_
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    rw [mul_comm ((scaleX (L n : ℚ) f) ^ n), PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
  rw [htrim f₁ N₁ hk1, htrim f₂ N₂ hk2]
  simp only [logSeriesTrunc, map_sum, PowerSeries.coeff_C_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
  congr 1
  rw [mul_comm ((scaleX (L n : ℚ) f₁) ^ n), PowerSeries.coeff_X_pow_mul',
      mul_comm ((scaleX (L n : ℚ) f₂) ^ n), PowerSeries.coeff_X_pow_mul',
      if_pos hnk, if_pos hnk]
  have hpow_eq : ∀ (t r : ℕ), r < k →
      PowerSeries.coeff r ((scaleX (L n : ℚ) f₁) ^ t) =
      PowerSeries.coeff r ((scaleX (L n : ℚ) f₂) ^ t) := by
    intro t
    induction t with
    | zero => intro r _; rfl
    | succ t iht =>
        intro r hr
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a ((scaleX (L n : ℚ) f₁) ^ t) *
                PowerSeries.coeff b (scaleX (L n : ℚ) f₁)),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a ((scaleX (L n : ℚ) f₂) ^ t) *
                PowerSeries.coeff b (scaleX (L n : ℚ) f₂))]
        refine Finset.sum_congr rfl fun a ha => ?_
        have hal : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [iht a (by omega), scaleX, scaleX, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hf (r - a) (by omega)]
  exact hpow_eq n (k - n) (by omega)

private lemma gCoeffs_eq_expCoeffs (L : ℕ → ℤ) (N : ℕ) :
    ∀ k ≤ N,
      gCoeffs L k = expCoeffs (logSeriesTrunc L (PowerSeries.mk fun j => if j < N then gCoeffs L j else 0) N) k := by
  set GprevN : PowerSeries ℚ := PowerSeries.mk fun j => if j < N then gCoeffs L j else 0
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => rw [gCoeffs, expCoeffs]
    | succ k' =>
        rw [gCoeffs, expCoeffs]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hjlt : j.val < k' + 1 := j.isLt
        rw [ih (k' - j.val) (by omega) (by omega)]
        congr 1
        congr 1
        exact coeff_logSeriesTrunc_congr L _ GprevN (k' + 1) N (j.val + 1) (by omega) (by omega)
          (fun r hr => by
            simp only [GprevN, PowerSeries.coeff_mk]
            rw [if_pos (by omega), if_pos (by omega)])

theorem main_proof :
    ∀ L : ℕ → ℤ, isIntegerSeries (expLogSeries L) →
      ∀ n : ℕ, ∃ z : ℤ, gCoeffs L n = (z : ℚ) := by
  intro L hL
  obtain ⟨M, hM⟩ := exists_euler_decomp_of_isIntegerSeries L hL
  have hL_cong : ∀ {p m : ℕ}, p.Prime → 1 ≤ m → ((p : ℕ) : ℤ) ∣ (L (p * m) - L m) := by
    intro p m hp hm
    set v := m.factorization p
    set u := m / p ^ v
    have hpow_dvd : p ^ v ∣ m := Nat.ordProj_dvd m p
    have hmu : p ^ v * u = m := Nat.mul_div_cancel' hpow_dvd
    have hu1 : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hpow_dvd) (pow_pos hp.pos v)
    have hpu : ¬ p ∣ u := by
      intro h
      have hpow1 : p ^ (v + 1) ∣ m := by rw [← hmu, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ v) h
      have hle := (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hm)).mp hpow1
      dsimp only [v] at hle; omega
    have hgc := gauss_cong_of_euler_decomp L M hM hp (show 1 ≤ v + 1 by omega) hu1 hpu
    simp only [Nat.add_sub_cancel] at hgc
    rw [pow_succ', mul_assoc, hmu] at hgc
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right p (p ^ v))) hgc
  intro n
  induction n using Nat.strong_induction_on with
  | h N ih =>
    set Gprev : PowerSeries ℚ := PowerSeries.mk fun j => if j < N then gCoeffs L j else 0
    have hGprev_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j Gprev = (z : ℚ) := by
      intro j
      rw [PowerSeries.coeff_mk]
      split_ifs with hj
      · exact ih j hj
      · exact ⟨0, by simp⟩
    let f : ℕ → PowerSeries ℚ := fun m => scaleX (L m : ℚ) Gprev
    have hf_int : ∀ m j, ∃ z : ℤ, PowerSeries.coeff j (f m) = (z : ℚ) := by
      intro m j
      obtain ⟨z, hz⟩ := hGprev_int j
      simp only [f, scaleX, PowerSeries.coeff_mk, hz]
      exact ⟨(L m) ^ j * z, by push_cast; ring⟩
    have hf_cong : ∀ (p m j : ℕ), p.Prime → 1 ≤ m → m * p ≤ N →
        isPInt p ((PowerSeries.coeff j ((f (p * m)) ^ p) - PowerSeries.coeff j (substPow p (f m))) / (p : ℚ)) := by
      intro p m j hp hm _
      have hfr := freshman_dream_series (p := p) (n := j) hp (fun r _ => by
        obtain ⟨z, hz⟩ := hf_int (p * m) r
        rw [hz]; exact isPInt_int hp z)
      rw [coeff_substPow]
      by_cases hdiv : p ∣ j
      · simp only [hdiv, ↓reduceIte] at hfr ⊢
        have hrew : (PowerSeries.coeff j ((f (p * m)) ^ p) - PowerSeries.coeff (j / p) (f m)) / (p : ℚ) =
            (PowerSeries.coeff j ((f (p * m)) ^ p) - (PowerSeries.coeff (j / p) (f (p * m))) ^ p) / (p : ℚ) +
            ((PowerSeries.coeff (j / p) (f (p * m))) ^ p - PowerSeries.coeff (j / p) (f m)) / (p : ℚ) := by
          ring
        rw [hrew]
        refine isPInt_add hp hfr ?_
        obtain ⟨z, hz⟩ := hGprev_int (j / p)
        simp only [f, scaleX, PowerSeries.coeff_mk, hz]
        have : Fact p.Prime := ⟨hp⟩
        have hLmod : (L (p * m) : ZMod p) = (L m : ZMod p) := by
          have hd := hL_cong hp hm
          have h0 : ((L (p * m) - L m : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
          rw [Int.cast_sub] at h0
          exact sub_eq_zero.mp h0
        have hmod : (p : ℤ) ∣ (((L (p * m)) ^ (j / p) * z) ^ p - (L m) ^ (j / p) * z) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [mul_pow, ZMod.pow_card, ZMod.pow_card, hLmod, sub_self]
        obtain ⟨t, ht⟩ := hmod
        have ht_q : ((L (p * m) : ℚ) ^ (j / p) * (z : ℚ)) ^ p - (L m : ℚ) ^ (j / p) * (z : ℚ) =
            (p : ℚ) * (t : ℚ) := by exact_mod_cast ht
        rw [ht_q]
        exact isPInt_mul_p_inv hp (isPInt_int hp t)
      · simp only [hdiv, ↓reduceIte, sub_zero] at hfr ⊢
        exact hfr
    have hint := dwork_pow_logSeries_isInt N f hf_int hf_cong N (le_refl N)
    rw [gCoeffs_eq_expCoeffs L N N (le_refl N)]
    simpa [expSeries, logSeriesTrunc, f] using hint

end OMA.S_oeis_a163921

theorem OMA.solution : type_of% @OMA.S_oeis_a163921.main :=
  OMA.S_oeis_a163921.main_proof
