import OMAStatements.S_oeis_a262005
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA262005Proof

open OMA.S_oeis_a262005

private lemma xDeriv_mul (F G : PowerSeries ℤ) :
    xDeriv (F * G) = xDeriv F * G + F * xDeriv G := by
  ext n
  simp only [xDeriv, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = n := by simpa using hp
  have hni : (n : ℤ) = (p.1 : ℤ) + (p.2 : ℤ) := by omega
  rw [hni]; ring

private lemma xDeriv_one_sub_X_sq :
    xDeriv ((1 - PowerSeries.X) ^ 2) = -2 * PowerSeries.X * (1 - PowerSeries.X) := by
  ext n
  have h2C : (2 : PowerSeries ℤ) = PowerSeries.C 2 := rfl
  have h1 : (1 - PowerSeries.X : PowerSeries ℤ) ^ 2 =
      1 - PowerSeries.C 2 * PowerSeries.X + PowerSeries.X ^ 2 := by
    rw [← h2C]; ring
  have h2 : (-2 * PowerSeries.X * (1 - PowerSeries.X) : PowerSeries ℤ) =
      -(PowerSeries.C 2 * PowerSeries.X) + PowerSeries.C 2 * PowerSeries.X ^ 2 := by
    rw [← h2C]; ring
  rw [h1, h2]
  simp only [xDeriv, PowerSeries.coeff_mk, map_add, map_sub, map_neg,
    PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | m + 3 =>
    simp [show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega]

private def prodFactor (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.range n,
    (((k + 1 : ℕ) : ℤ) ^ 4 - ((k + 1 : ℕ) : ℤ) ^ 3 + ((k + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) + 1)

private lemma coeffF_eq (n : ℕ) : coeffF n = ((n + 1 : ℕ) : ℤ) * prodFactor n := rfl

private lemma prodFactor_succ (n : ℕ) :
    prodFactor (n + 1) = prodFactor n *
      (((n + 1 : ℕ) : ℤ) ^ 4 - ((n + 1 : ℕ) : ℤ) ^ 3 + ((n + 1 : ℕ) : ℤ) ^ 2 - ((n + 1 : ℕ) : ℤ) + 1) := by
  unfold prodFactor
  rw [Finset.prod_range_succ]

private lemma prodFactor_mod3 :
    ∀ n : ℕ, (prodFactor n : ZMod 3) =
      if n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 5 then 1 else 2 := by
  intro n
  induction n with
  | zero => simp [prodFactor]
  | succ n ih =>
    rw [prodFactor_succ, Int.cast_mul, ih]
    have hstep : (((((n + 1 : ℕ) : ℤ) ^ 4 - ((n + 1 : ℕ) : ℤ) ^ 3 + ((n + 1 : ℕ) : ℤ) ^ 2 -
        ((n + 1 : ℕ) : ℤ) + 1 : ℤ)) : ZMod 3) = if n % 6 = 1 ∨ n % 6 = 4 then 2 else 1 := by
      have hmod : (n : ZMod 3) = ((n % 6 : ℕ) : ZMod 3) := by
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
      push_cast
      rw [hmod]
      have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
      interval_cases (n % 6) <;> decide
    rw [hstep]
    have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
    have hsucc : (n + 1) % 6 = (n % 6 + 1) % 6 := by omega
    rw [hsucc]
    interval_cases (n % 6) <;> decide

private lemma coeffF_mod3 (n : ℕ) :
    (coeffF n : ZMod 3) =
      match n % 6 with
      | 0 => 1
      | 1 => 2
      | 2 => 0
      | 3 => 2
      | 4 => 1
      | _ => 0 := by
  rw [coeffF_eq, Int.cast_mul, prodFactor_mod3]
  have hmod : (n : ZMod 3) = ((n % 6 : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
  push_cast
  rw [hmod]
  have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
  interval_cases (n % 6) <;> decide

private lemma prodFactor_mod4 :
    ∀ n : ℕ, (prodFactor n : ZMod 4) =
      if n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 6 ∨ n % 8 = 7 then 1 else 3 := by
  intro n
  induction n with
  | zero => simp [prodFactor]
  | succ n ih =>
    rw [prodFactor_succ, Int.cast_mul, ih]
    have hstep : (((((n + 1 : ℕ) : ℤ) ^ 4 - ((n + 1 : ℕ) : ℤ) ^ 3 + ((n + 1 : ℕ) : ℤ) ^ 2 -
        ((n + 1 : ℕ) : ℤ) + 1 : ℤ)) : ZMod 4) = if n % 8 = 1 ∨ n % 8 = 5 then 3 else 1 := by
      have hmod : (n : ZMod 4) = ((n % 8 : ℕ) : ZMod 4) := by
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
      push_cast
      rw [hmod]
      have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
      interval_cases (n % 8) <;> decide
    rw [hstep]
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    have hsucc : (n + 1) % 8 = (n % 8 + 1) % 8 := by omega
    rw [hsucc]
    interval_cases (n % 8) <;> decide

private lemma coeffF_mod4 (n : ℕ) :
    (coeffF n : ZMod 4) =
      match n % 8 with
      | 0 => 1
      | 1 => 2
      | 2 => 1
      | 3 => 0
      | 4 => 3
      | 5 => 2
      | 6 => 3
      | _ => 0 := by
  rw [coeffF_eq, Int.cast_mul, prodFactor_mod4]
  have hmod : (n : ZMod 4) = ((n % 8 : ℕ) : ZMod 4) := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
  push_cast
  rw [hmod]
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  interval_cases (n % 8) <;> decide

private lemma coeffF_mod5 (n : ℕ) :
    (coeffF n : ZMod 5) =
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 3 else if n = 3 then 4 else 0 := by
  match n with
  | 0 => unfold coeffF; decide
  | 1 => unfold coeffF; decide
  | 2 => unfold coeffF; decide
  | 3 => unfold coeffF; decide
  | m + 4 =>
    simp only [show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega,
      show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega, ↓reduceIte]
    rw [coeffF_eq, Int.cast_mul]
    have h5 : (prodFactor (m + 4) : ZMod 5) = 0 := by
      unfold prodFactor
      rw [Int.cast_prod]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 3 < m + 4))
      decide
    rw [h5, mul_zero]

private lemma coeff_F_mul_one_sub_X_sq (n : ℕ) :
    PowerSeries.coeff n (seriesF * (1 - PowerSeries.X) ^ 2) =
      if n = 0 then coeffF 0
      else if n = 1 then coeffF 1 - 2 * coeffF 0
      else coeffF n - 2 * coeffF (n - 1) + coeffF (n - 2) := by
  have h1 : (1 - PowerSeries.X : PowerSeries ℤ) ^ 2 = 1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 := by ring
  rw [h1, mul_add, mul_sub, mul_one, map_add, map_sub]
  have h2C : seriesF * (2 * PowerSeries.X) = PowerSeries.C 2 * (PowerSeries.X * seriesF) := by
    rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 from rfl]; ring
  rw [h2C, PowerSeries.coeff_C_mul, mul_comm seriesF (PowerSeries.X ^ 2),
    PowerSeries.coeff_X_pow_mul']
  have hXmul : ∀ m : ℕ, PowerSeries.coeff m (PowerSeries.X * seriesF) =
      if m = 0 then 0 else PowerSeries.coeff (m - 1) seriesF := by
    intro m
    rw [show PowerSeries.X * seriesF = PowerSeries.X ^ 1 * seriesF by ring,
      PowerSeries.coeff_X_pow_mul']
    split_ifs <;> omega
  rw [hXmul]
  simp only [seriesF, PowerSeries.coeff_mk]
  match n with
  | 0 => simp
  | 1 => simp
  | m + 2 =>
    simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, show 2 ≤ m + 2 by omega,
      ↓reduceIte]

private lemma sixty_dvd_xDeriv_G (n : ℕ) :
    ((60 : ℕ) : ℤ) ∣ PowerSeries.coeff n (xDeriv (seriesF * (1 - PowerSeries.X) ^ 2)) := by
  have h3 : ((3 : ℕ) : ℤ) ∣ PowerSeries.coeff n (xDeriv (seriesF * (1 - PowerSeries.X) ^ 2)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [xDeriv, PowerSeries.coeff_mk, coeff_F_mul_one_sub_X_sq]
    match n with
    | 0 => simp
    | 1 =>
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.cast_one, one_mul,
        Int.cast_sub, Int.cast_mul, Int.cast_ofNat, coeffF_mod3]
      decide
    | m + 2 =>
      simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ↓reduceIte,
        show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod3]
      have hnmod : ((m + 2 : ℕ) : ZMod 3) = (((m % 6 + 2 : ℕ) : ZMod 3)) := by
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
      rw [hnmod, show (m + 2) % 6 = (m % 6 + 2) % 6 by omega,
        show (m + 1) % 6 = (m % 6 + 1) % 6 by omega]
      have hlt : m % 6 < 6 := Nat.mod_lt m (by decide)
      interval_cases (m % 6) <;> decide
  have h4 : ((4 : ℕ) : ℤ) ∣ PowerSeries.coeff n (xDeriv (seriesF * (1 - PowerSeries.X) ^ 2)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [xDeriv, PowerSeries.coeff_mk, coeff_F_mul_one_sub_X_sq]
    match n with
    | 0 => simp
    | 1 =>
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.cast_one, one_mul,
        Int.cast_sub, Int.cast_mul, Int.cast_ofNat, coeffF_mod4]
      decide
    | m + 2 =>
      simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ↓reduceIte,
        show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod4]
      have hnmod : ((m + 2 : ℕ) : ZMod 4) = (((m % 8 + 2 : ℕ) : ZMod 4)) := by
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]; omega
      rw [hnmod, show (m + 2) % 8 = (m % 8 + 2) % 8 by omega,
        show (m + 1) % 8 = (m % 8 + 1) % 8 by omega]
      have hlt : m % 8 < 8 := Nat.mod_lt m (by decide)
      interval_cases (m % 8) <;> decide
  have h5 : ((5 : ℕ) : ℤ) ∣ PowerSeries.coeff n (xDeriv (seriesF * (1 - PowerSeries.X) ^ 2)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [xDeriv, PowerSeries.coeff_mk, coeff_F_mul_one_sub_X_sq]
    match n with
    | 0 => simp
    | 1 =>
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.cast_one, one_mul,
        Int.cast_sub, Int.cast_mul, Int.cast_ofNat, coeffF_mod5]
      decide
    | 2 =>
      simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
        show 2 - 1 = 1 by decide, show 2 - 2 = 0 by decide,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod5]
      decide
    | 3 =>
      simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, ↓reduceIte,
        show 3 - 1 = 2 by decide, show 3 - 2 = 1 by decide,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod5]
      decide
    | 4 =>
      simp only [show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide, ↓reduceIte,
        show 4 - 1 = 3 by decide, show 4 - 2 = 2 by decide,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod5]
      decide
    | 5 =>
      simp only [show (5 : ℕ) ≠ 0 by decide, show (5 : ℕ) ≠ 1 by decide, ↓reduceIte,
        show 5 - 1 = 4 by decide, show 5 - 2 = 3 by decide,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod5]
      decide
    | m + 6 =>
      simp only [show m + 6 ≠ 0 by omega, show m + 6 ≠ 1 by omega, ↓reduceIte,
        show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat, coeffF_mod5]
      simp [show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega,
        show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
        show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega]
  rcases h3 with ⟨a, ha⟩
  rcases h4 with ⟨b, hb⟩
  rcases h5 with ⟨c, hc⟩
  norm_num at ha hb hc ⊢
  omega

private lemma cancel_coeff0_one (U F : PowerSeries (ZMod 60))
    (hU0 : PowerSeries.coeff 0 U = 1) (h : U * F = 0) : F = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) h
    rw [map_zero, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j F),
      Finset.sum_range_succ'] at hn
    simp only [Nat.sub_zero, hU0, one_mul] at hn
    have htail : ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) F = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih (n - (k + 1)) (by omega), map_zero, mul_zero]
    rw [htail, zero_add] at hn
    exact hn

private lemma prove_main (A : PowerSeries ℤ) (hA : IsA262005 A) :
    ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 2 [ZMOD 60] := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 60) := PowerSeries.map (Int.castRingHom (ZMod 60))
  have hprod : seriesF * (1 - PowerSeries.X) * ((1 - PowerSeries.X) * A - 2 * PowerSeries.X) =
      xDeriv (seriesF * (1 - PowerSeries.X) ^ 2) := by
    rw [xDeriv_mul, xDeriv_one_sub_X_sq, ← hA.2]
    ring
  have hzero : phi (xDeriv (seriesF * (1 - PowerSeries.X) ^ 2)) = 0 := by
    ext n
    simp only [phi, PowerSeries.coeff_map, Int.coe_castRingHom, map_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 60).mpr (sixty_dvd_xDeriv_G n)
  have hphi_prod : phi (seriesF * (1 - PowerSeries.X)) * phi ((1 - PowerSeries.X) * A - 2 * PowerSeries.X) = 0 := by
    rw [← map_mul, hprod, hzero]
  have hU0 : PowerSeries.coeff 0 (phi (seriesF * (1 - PowerSeries.X))) = 1 := by
    rw [PowerSeries.coeff_map, Int.coe_castRingHom, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    have hF0 : PowerSeries.coeff 0 seriesF = 1 := by simp [seriesF, coeffF]
    simp [hF0]
  have hlin : phi ((1 - PowerSeries.X) * A - 2 * PowerSeries.X) = 0 :=
    cancel_coeff0_one _ _ hU0 hphi_prod
  have heq : (1 - PowerSeries.X) * phi A = 2 * PowerSeries.X := by
    have h := hlin
    simp only [map_sub, map_mul, map_one, map_ofNat] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact sub_eq_zero.mp h
  have hA0 : PowerSeries.coeff 0 (phi A) = 0 := by simp [phi, hA.1]
  have hA_mod60 : ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n (phi A) = 2 := by
    intro n
    induction n with
    | zero => omega
    | succ m ih =>
      intro _
      have hm := congrArg (PowerSeries.coeff (m + 1)) heq
      rw [sub_mul, one_mul, map_sub,
        show PowerSeries.X * phi A = PowerSeries.X ^ 1 * phi A by ring,
        PowerSeries.coeff_X_pow_mul', if_pos (by omega : 1 ≤ m + 1), Nat.add_sub_cancel] at hm
      rw [show (2 : PowerSeries (ZMod 60)) * PowerSeries.X = PowerSeries.C 2 * PowerSeries.X from rfl,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X] at hm
      cases m with
      | zero =>
        simp only [↓reduceIte, mul_one, hA0, sub_zero] at hm
        exact hm
      | succ m' =>
        simp only [show m' + 1 + 1 ≠ 1 by omega, ↓reduceIte, mul_zero] at hm
        have hprev := ih (by omega)
        rw [hprev] at hm
        exact sub_eq_zero.mp hm
  intro n hn
  change PowerSeries.coeff n A ≡ 2 [ZMOD ((60 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  have h := hA_mod60 n hn
  simpa [phi] using h

end OeisA262005Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a262005.main :=
  OeisA262005Proof.prove_main
