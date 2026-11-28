import OMAStatements.S_oeis_a144636
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The scaled series (1/6) A(6x), whose coefficients are 6^(n-1) times those of A. -/
noncomputable def a144636Y (A : PowerSeries ℚ) : PowerSeries ℚ := C (1 / 6 : ℚ) * rescale (6 : ℚ) A

theorem a144636_six_mul (A : PowerSeries ℚ) : 6 * a144636Y A = rescale (6 : ℚ) A := by
  unfold a144636Y
  rw [← mul_assoc, show (6 : PowerSeries ℚ) * C (1 / 6 : ℚ) = 1 by
    rw [← map_ofNat (C (R := ℚ)) 6, ← map_mul]; norm_num]
  ring

theorem a144636_eqn (A : PowerSeries ℚ) (hA : A ^ 3 + 3 * A ^ 2 + 6 * A = 6 * X) :
    a144636Y A + 3 * a144636Y A ^ 2 + 6 * a144636Y A ^ 3 = X := by
  have h := congrArg (rescale (6 : ℚ)) hA
  simp only [map_add, map_mul, map_pow, map_ofNat, rescale_X] at h
  rw [← a144636_six_mul A] at h
  have h36 : (36 : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  apply mul_left_cancel₀ h36
  linear_combination h

theorem a144636_const (A : PowerSeries ℚ) (hA0 : constantCoeff A = 0) :
    constantCoeff (a144636Y A) = 0 := by
  unfold a144636Y
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_C_mul, coeff_rescale,
    coeff_zero_eq_constantCoeff_apply, hA0, mul_zero, mul_zero]

theorem a144636_approx (Y : PowerSeries ℚ) (hY0 : constantCoeff Y = 0)
    (hY : Y + 3 * Y ^ 2 + 6 * Y ^ 3 = X) (n : ℕ) :
    ∃ Z : PowerSeries ℤ, constantCoeff Z = 0 ∧
      (X : PowerSeries ℚ) ^ n ∣ Y - map (Int.castRingHom ℚ) Z := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨Z, hZ0, hdvd⟩ := ih
    refine ⟨X - 3 * Z ^ 2 - 6 * Z ^ 3, by simp [hZ0], ?_⟩
    set W := map (Int.castRingHom ℚ) Z with hW
    have hW0 : constantCoeff W = 0 := by
      rw [hW, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hZ0, map_zero]
    have hmap : map (Int.castRingHom ℚ) (X - 3 * Z ^ 2 - 6 * Z ^ 3) =
        X - 3 * W ^ 2 - 6 * W ^ 3 := by
      simp only [hW, map_sub, map_mul, map_pow, map_X]
      rw [map_ofNat, map_ofNat]
    rw [hmap]
    have key : Y - (X - 3 * W ^ 2 - 6 * W ^ 3) =
        (Y - W) * (-3 * (Y + W) - 6 * (Y ^ 2 + Y * W + W ^ 2)) := by
      linear_combination hY
    rw [key, pow_succ]
    apply mul_dvd_mul hdvd
    rw [X_dvd_iff]
    simp [hY0, hW0]

theorem a144636_int (Y : PowerSeries ℚ) (hY0 : constantCoeff Y = 0)
    (hY : Y + 3 * Y ^ 2 + 6 * Y ^ 3 = X) :
    ∃ Z : PowerSeries ℤ, map (Int.castRingHom ℚ) Z = Y := by
  choose Z _ hZd using a144636_approx Y hY0 hY
  refine ⟨mk (fun n => coeff n (Z (n + 1))), ?_⟩
  ext n
  rw [coeff_map, coeff_mk]
  have h := (X_pow_dvd_iff.mp (hZd (n + 1))) n (Nat.lt_succ_self n)
  rw [map_sub, coeff_map] at h
  exact (sub_eq_zero.mp h).symm

theorem a144636_int_eqn (Y : PowerSeries ℚ) (Z : PowerSeries ℤ)
    (hZ : map (Int.castRingHom ℚ) Z = Y) (hY : Y + 3 * Y ^ 2 + 6 * Y ^ 3 = X) :
    Z + 3 * Z ^ 2 + 6 * Z ^ 3 = X := by
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_add, map_mul, map_pow, map_X, hZ]
  rw [map_ofNat, map_ofNat, hY]

theorem a144636_sq_coeff (f : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (f ^ 2) = if 2 ∣ n then coeff (n / 2) f else 0 := by
  rw [pow_two, coeff_mul_eq_coeff_trunc_mul_trunc f f (Nat.lt_succ_self n), ← Polynomial.coe_mul,
    Polynomial.coeff_coe, ← pow_two, ← Polynomial.map_frobenius_expand 2, ZMod.frobenius_zmod,
    Polynomial.map_id, Polynomial.coeff_expand (by norm_num), coeff_trunc]
  have : n / 2 < n + 1 := by omega
  simp [this]

theorem a144636_parity (e : ℕ → ZMod 2)
    (h : ∀ n, e n + (if 2 ∣ n then e (n / 2) else 0) = if n = 1 then 1 else 0) :
    ∀ n, 1 ≤ n → (e n = 1 ↔ ∃ k, n = 2 ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm1 : 1 ≤ m := by omega
    have hn1 : n ≠ 1 := by omega
    have h2 : 2 ∣ n := ⟨m, by omega⟩
    have hdiv : n / 2 = m := by omega
    have hn := h n
    rw [if_pos h2, if_neg hn1, hdiv] at hn
    have hem : e n = e m := by
      have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact key _ _ hn
    rw [hem, ih m (by omega) hm1]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by rw [pow_succ]; omega⟩
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · have h2 : ¬ 2 ∣ n := by omega
    have hn' := h n
    rw [if_neg h2, add_zero] at hn'
    by_cases h1 : n = 1
    · rw [if_pos h1] at hn'
      exact ⟨fun _ => ⟨0, by simp [h1]⟩, fun _ => hn'⟩
    · rw [if_neg h1] at hn'
      rw [hn']
      constructor
      · intro h01
        exact absurd h01 (by decide)
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; exact absurd hk h1
        | succ k => rw [pow_succ] at hk; omega

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a144636.main := by
  intro A hA0 hA n hn
  set Y := OMA.Helpers.a144636Y A with hYdef
  have hY0 : constantCoeff Y = 0 := OMA.Helpers.a144636_const A hA0
  have hY := OMA.Helpers.a144636_eqn A hA
  obtain ⟨Z, hZ⟩ := OMA.Helpers.a144636_int Y hY0 hY
  have hZe := OMA.Helpers.a144636_int_eqn Y Z hZ hY
  have hcoef : (6 : ℚ) ^ (n - 1) * ((n.factorial : ℚ) * coeff n A) / (n.factorial : ℚ) =
      ((coeff n Z : ℤ) : ℚ) := by
    have h1 : (6 : ℚ) ^ (n - 1) * ((n.factorial : ℚ) * coeff n A) / (n.factorial : ℚ) =
        (6 : ℚ) ^ (n - 1) * coeff n A := by
      have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      field_simp
    have h2 : coeff n Y = ((coeff n Z : ℤ) : ℚ) := by rw [← hZ, coeff_map]; rfl
    rw [h1, ← h2, hYdef, OMA.Helpers.a144636Y, coeff_C_mul, coeff_rescale]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel]
    ring
  rw [hcoef]
  set Zb := map (Int.castRingHom (ZMod 2)) Z with hZb
  have h3 : (3 : PowerSeries (ZMod 2)) = 1 := by
    rw [← map_ofNat (C (R := ZMod 2)) 3, show (OfNat.ofNat 3 : ZMod 2) = 1 by decide, map_one]
  have h6 : (6 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat (C (R := ZMod 2)) 6, show (OfNat.ofNat 6 : ZMod 2) = 0 by decide, map_zero]
  have hZbe : Zb + Zb ^ 2 = X := by
    have := congrArg (map (Int.castRingHom (ZMod 2))) hZe
    simp only [map_add, map_mul, map_pow, map_ofNat, map_X] at this
    rw [h3, h6] at this
    rw [← hZb] at this
    simpa using this
  have he : ∀ k, coeff k Zb + (if 2 ∣ k then coeff (k / 2) Zb else 0) = if k = 1 then 1 else 0 := by
    intro k
    rw [← OMA.Helpers.a144636_sq_coeff, ← coeff_X, ← map_add, hZbe]
  rw [← OMA.Helpers.a144636_parity (fun k => coeff k Zb) he n hn]
  simp only [hZb, coeff_map, eq_intCast]
  rw [ZMod.intCast_eq_one_iff_odd]
  constructor
  · rintro ⟨m, hm, heq⟩
    rw [Int.cast_inj.mp heq]
    exact hm
  · intro h
    exact ⟨_, h, rfl⟩
