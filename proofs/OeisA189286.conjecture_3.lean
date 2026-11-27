import FormalConjectures.OEIS.«189286»
import Mathlib

/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

Licensed under the Apache License, Version 2.0 (the License);
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an AS IS BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
-- Adapted for Left to Solve by importing the pinned upstream definitions and pinning the target.
-- Original formal proof by Yuto Nakahara, Apache-2.0,
-- https://github.com/YutoNakahara/oeis-a189286-lean/blob/259c8073aa8d83ccdb9fdc9361e82480338d3177/Solution.lean

/-! The normalized binomial convolution in OEIS A189286 has integer values. -/

namespace OeisA189286

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private lemma choose_3n_mul_factorials (n : ℕ) :
    (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
  have := Nat.choose_mul_factorial_mul_factorial (n := 3 * n) (k := n) (by omega)
  rwa [show 3 * n - n = 2 * n by omega] at this

private def fStep (q r : ℕ) : ℕ := 6 * r / q - 3 * r / q - 2 * r / q

private def gStep (q r : ℕ) : ℕ := 3 * r / q - 2 * r / q

private lemma nat_div_eq_of_le_lt {q m j : ℕ} (hq : 0 < q)
    (h1 : j * q ≤ m) (h2 : m < (j + 1) * q) : m / q = j :=
  le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr h2))
    ((Nat.le_div_iff_mul_le hq).mpr h1)

private lemma fStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    3 * r / q + 2 * r / q ≤ 6 * r / q ∧
    fStep q r = if 6 * r < q then 0 else if 6 * r < 5 * q then 1 else 2 := by
  unfold fStep
  by_cases h1 : 6 * r < q
  · have h6 : 6 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    simp [h1, h6, h3, h2]
  · by_cases h2 : 6 * r < 2 * q
    · have h6 : 6 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_neg h1, if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 3 * q
      · have h6 : 6 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg h1, if_pos (by omega)]
        omega
      · by_cases h4 : 6 * r < 4 * q
        · have h6 : 6 * r / q = 3 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          rw [if_neg h1, if_pos (by omega)]
          omega
        · by_cases h5 : 6 * r < 5 * q
          · have h6 : 6 * r / q = 4 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_pos h5]
            omega
          · have h6 : 6 * r / q = 5 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_neg h5]
            omega

private lemma gStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    2 * r / q ≤ 3 * r / q ∧
    gStep q r = if (2 * q ≤ 6 * r ∧ 6 * r < 3 * q) ∨ 4 * q ≤ 6 * r then 1 else 0 := by
  unfold gStep
  by_cases h1 : 6 * r < 2 * q
  · have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    rw [if_neg (by omega)]
    omega
  · by_cases h2 : 6 * r < 3 * q
    · have h3 : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 4 * q
      · have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg (by omega)]
        omega
      · have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_pos (by omega)]
        omega

private lemma div_six_eq {q a : ℕ} (hq : 0 < q) :
    6 * a / q = 3 * a / q + 2 * a / q + a / q + fStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (fStep_spec hq (Nat.mod_lt a hq)).1
  have h6 := hmul 6
  have h3 := hmul 3
  have h2 := hmul 2
  unfold fStep
  omega

private lemma div_three_eq {q a : ℕ} (hq : 0 < q) :
    3 * a / q = 2 * a / q + a / q + gStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (gStep_spec hq (Nat.mod_lt a hq)).1
  have h3 := hmul 3
  have h2 := hmul 2
  unfold gStep
  omega

private lemma padicValNat_tNat_eq_sum {p k b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (6 * k) < b) :
    padicValNat p (tNat k) = ∑ i ∈ Finset.Ico 1 b, fStep (p ^ i) (k % p ^ i) := by
  have hfac := congrArg (padicValNat p) (tNat_mul_factorials k)
  rw [padicValNat.mul
        (mul_ne_zero (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (tNat_pos k).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 6 * k / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (3 * k / p ^ i + 2 * k / p ^ i + k / p ^ i +
        fStep (p ^ i) (k % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_six_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_choose_3n_eq_sum {p n b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (3 * n) < b) :
    padicValNat p ((3 * n).choose n) = ∑ i ∈ Finset.Ico 1 b, gStep (p ^ i) (n % p ^ i) := by
  have hfac := congrArg (padicValNat p) (choose_3n_mul_factorials n)
  rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 3 * n / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (2 * n / p ^ i + n / p ^ i + gStep (p ^ i) (n % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_three_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_eq_sum_ite_dvd {p x b : ℕ} [hp : Fact p.Prime]
    (hx : 0 < x) (hb : Nat.log p x < b) :
    padicValNat p x = ∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ x then 1 else 0 := by
  have hr : padicValNat p x < b := lt_of_le_of_lt (padicValNat_le_nat_log x) hb
  have hfilt : (Finset.Ico 1 b).filter (fun i => p ^ i ∣ x) =
      Finset.Ico 1 (padicValNat p x + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, padicValNat_dvd_iff_le hx.ne']
    omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      hfilt, Nat.card_Ico]
  omega

private lemma gStep_le_fStep_add {q k m : ℕ} (hq : 0 < q) :
    gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hfk := (fStep_spec hq (Nat.mod_lt k hq)).2
  have hfm := (fStep_spec hq (Nat.mod_lt m hq)).2
  have hgn := (gStep_spec hq (Nat.mod_lt (k + m) hq)).2
  have hmod : (k + m) % q = (k % q + m % q) % q := Nat.add_mod k m q
  by_cases hkm : k % q + m % q < q
  · rw [Nat.mod_eq_of_lt hkm] at hmod
    rw [hmod] at hgn ⊢
    split_ifs at hfk hfm hgn <;> omega
  · have hsub : (k + m) % q = k % q + m % q - q := by
      have hklt := Nat.mod_lt k hq
      have hmlt := Nat.mod_lt m hq
      rw [hmod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hgn ⊢
    have hklt := Nat.mod_lt k hq
    have hmlt := Nat.mod_lt m hq
    split_ifs at hfk hfm hgn <;> omega

private lemma two_mul_mod_of_dvd {q n : ℕ} (hn : 0 < n) (hq : 2 ≤ q) (hdiv : q ∣ 2 * n - 1) :
    2 * (n % q) = q + 1 := by
  rcases hdiv with ⟨c, hc⟩
  have hr : n % q < q := Nat.mod_lt n (by omega)
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have h2n : 2 * n = q * c + 1 := by omega
  have heq : q * c + 1 = 2 * (q * (n / q)) + 2 * (n % q) := by linarith
  have h1 : c < 2 * (n / q) + 2 := by nlinarith
  have h2 : 2 * (n / q) ≤ c := by
    by_contra hlt
    have hle : c + 1 ≤ 2 * (n / q) := by omega
    have hmul : q * c + q ≤ 2 * (q * (n / q)) := by
      calc q * c + q = q * (c + 1) := by ring
        _ ≤ q * (2 * (n / q)) := Nat.mul_le_mul_left q hle
        _ = 2 * (q * (n / q)) := by ring
    omega
  have hne : c ≠ 2 * (n / q) := by
    intro h
    rw [h] at heq
    have : 2 * (n % q) = 1 := by linarith
    omega
  have hc_eq : c = 2 * (n / q) + 1 := by omega
  rw [hc_eq] at heq
  linarith

private lemma dvd_of_two_mul_mod {q n : ℕ} (hn : 0 < n) (hmod : 2 * (n % q) = q + 1) :
    q ∣ 2 * n - 1 := by
  refine ⟨2 * (n / q) + 1, ?_⟩
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have : 2 * n = q * (2 * (n / q) + 1) + 1 := by linarith
  omega

private lemma gStep_add_one_le_fStep_add {q k m : ℕ} (hq : 5 ≤ q) (hn : 0 < k + m)
    (hdiv : q ∣ 2 * (k + m) - 1) :
    1 + gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hqpos : 0 < q := by omega
  have h2 := two_mul_mod_of_dvd hn (by omega) hdiv
  have hgn := (gStep_spec hqpos (Nat.mod_lt (k + m) hqpos)).2
  have hg0 : gStep q ((k + m) % q) = 0 := by
    rw [hgn, if_neg (by omega)]
  rw [hg0, add_zero]
  have hfk := (fStep_spec hqpos (Nat.mod_lt k hqpos)).2
  have hfm := (fStep_spec hqpos (Nat.mod_lt m hqpos)).2
  by_contra hlt
  have hfk0 : fStep q (k % q) = 0 := by omega
  have hfm0 : fStep q (m % q) = 0 := by omega
  have hksmall : 6 * (k % q) < q := by
    by_contra h
    rw [hfk, if_neg h] at hfk0
    by_cases h5 : 6 * (k % q) < 5 * q
    · rw [if_pos h5] at hfk0; omega
    · rw [if_neg h5] at hfk0; omega
  have hmsmall : 6 * (m % q) < q := by
    by_contra h
    rw [hfm, if_neg h] at hfm0
    by_cases h5 : 6 * (m % q) < 5 * q
    · rw [if_pos h5] at hfm0; omega
    · rw [if_neg h5] at hfm0; omega
  have hmod : (k + m) % q = k % q + m % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

private lemma mod_three_mul {q a : ℕ} (hq : 0 < q) :
    a % (3 * q) = ((a / q) % 3) * q + a % q := by
  have h1 : q * (a / q) + a % q = a := Nat.div_add_mod a q
  have h2 : 3 * ((a / q) / 3) + (a / q) % 3 = a / q := Nat.div_add_mod (a / q) 3
  have h3 : (a / q) % 3 < 3 := Nat.mod_lt _ (by omega)
  have h4 : a % q < q := Nat.mod_lt _ hq
  have hlt : ((a / q) % 3) * q + a % q < 3 * q := by nlinarith
  have heq : a = ((a / q) % 3 * q + a % q) + (3 * q) * ((a / q) / 3) := by nlinarith
  conv_lhs => rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma exists_surplus_base3_aux {k m : ℕ} (hn : 0 < k + m)
    (hk3 : k % 3 = 0) (hm3 : m % 3 = 2) :
    ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * (k + m) - 1) + 2),
      (if 3 ^ j ∣ 2 * (k + m) - 1 then 1 else 0) + gStep (3 ^ j) ((k + m) % 3 ^ j) + 1 ≤
        fStep (3 ^ j) (k % 3 ^ j) + fStep (3 ^ j) (m % 3 ^ j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set n := k + m
  set r := padicValNat 3 (2 * n - 1)
  have h3dvd : 3 ∣ 2 * n - 1 := by
    refine dvd_of_two_mul_mod hn ?_
    have : n % 3 = (k % 3 + m % 3) % 3 := Nat.add_mod k m 3
    omega
  have hr1 : 1 ≤ r := one_le_padicValNat_of_dvd (by omega) h3dvd
  by_contra hnone
  push Not at hnone
  have hstep : ∀ j, 1 ≤ j → j ≤ r → k % 3 ^ j = 0 ∧ 2 * (m % 3 ^ j) = 3 ^ j + 1 := by
    intro j hj1 hjr
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        simpa using ⟨hk3, by omega⟩
      · have ⟨hkj, hmj⟩ := ih (by omega) (by omega)
        set q := 3 ^ j
        have hqpos : 0 < q := pow_pos (by omega : 0 < 3) j
        have h3q : 3 ^ (j + 1) = 3 * q := by rw [pow_succ']
        have h3q_pos : 0 < 3 ^ (j + 1) := pow_pos (by omega : 0 < 3) (j + 1)
        have h3q_ge : 5 ≤ 3 ^ (j + 1) := by
          have : 3 ^ 2 ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hdvd_next : 3 ^ (j + 1) ∣ 2 * n - 1 :=
          (padicValNat_dvd_iff_le (p := 3) (by omega)).mpr hjr
        have hgn0 : gStep (3 ^ (j + 1)) (n % 3 ^ (j + 1)) = 0 := by
          have h2n := two_mul_mod_of_dvd hn (by omega) hdvd_next
          have hgs := (gStep_spec h3q_pos (Nat.mod_lt n h3q_pos)).2
          rw [hgs, if_neg (by omega)]
        have hbound := hnone (j + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [if_pos hdvd_next, hgn0, add_zero] at hbound
        have hk_next : k % (3 * q) = ((k / q) % 3) * q := by
          rw [mod_three_mul hqpos, hkj, add_zero]
        have hm_next : m % (3 * q) = ((m / q) % 3) * q + m % q := mod_three_mul hqpos
        have hfm_ge : 1 ≤ fStep (3 ^ (j + 1)) (m % 3 ^ (j + 1)) := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt m h3q_pos)).2
          rw [h3q, hm_next] at hfs ⊢
          have h6m : 3 * q ≤ 6 * (((m / q) % 3) * q + m % q) := by
            have : 0 ≤ ((m / q) % 3) * q := Nat.zero_le _
            omega
          rw [hfs, if_neg (by omega)]
          split_ifs <;> omega
        have hfk_eq0 : fStep (3 ^ (j + 1)) (k % 3 ^ (j + 1)) = 0 := by omega
        have hdk0 : (k / q) % 3 = 0 := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt k h3q_pos)).2
          rw [h3q, hk_next] at hfs hfk_eq0
          have hlt : 6 * (((k / q) % 3) * q) < 3 * q := by
            by_contra hge
            rw [hfs, if_neg hge] at hfk_eq0
            by_cases h5 : 6 * (((k / q) % 3) * q) < 5 * (3 * q)
            · rw [if_pos h5] at hfk_eq0; omega
            · rw [if_neg h5] at hfk_eq0; omega
          by_contra hne
          have h1 : 1 ≤ (k / q) % 3 := by omega
          have hmul : 1 * q ≤ ((k / q) % 3) * q := Nat.mul_le_mul_right q h1
          omega
        have hk_zero : k % 3 ^ (j + 1) = 0 := by rw [h3q, hk_next, hdk0, zero_mul]
        have hm_eq : m % 3 ^ (j + 1) = n % 3 ^ (j + 1) := by
          have hmod : n % 3 ^ (j + 1) = (k % 3 ^ (j + 1) + m % 3 ^ (j + 1)) % 3 ^ (j + 1) :=
            Nat.add_mod k m _
          rw [hk_zero, zero_add, Nat.mod_mod] at hmod
          exact hmod.symm
        exact ⟨hk_zero, hm_eq.symm ▸ two_mul_mod_of_dvd hn (by omega) hdvd_next⟩
  have ⟨hkr, hmr⟩ := hstep r hr1 le_rfl
  set q := 3 ^ r
  have hq3 : 3 ≤ q := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by omega) hr1
  have hqpos : 0 < q := by omega
  have h3q : 3 ^ (r + 1) = 3 * q := by rw [pow_succ']
  have hndvd : ¬ 3 ^ (r + 1) ∣ 2 * n - 1 := pow_succ_padicValNat_not_dvd (p := 3) (by omega)
  have hbound := hnone (r + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  rw [if_neg hndvd, zero_add, h3q] at hbound
  set dk := (k / q) % 3
  set dm := (m / q) % 3
  have hdk_lt : dk < 3 := Nat.mod_lt _ (by omega)
  have hdm_lt : dm < 3 := Nat.mod_lt _ (by omega)
  have hk_next : k % (3 * q) = dk * q := by rw [mod_three_mul hqpos, hkr, add_zero]
  have hm_next : m % (3 * q) = dm * q + m % q := mod_three_mul hqpos
  have hn_next : n % (3 * q) = ((dk + dm) % 3) * q + m % q := by
    have hmq_lt : m % q < q := Nat.mod_lt m hqpos
    have h1 : n % (3 * q) = (k % (3 * q) + m % (3 * q)) % (3 * q) := Nat.add_mod k m _
    rw [hk_next, hm_next] at h1
    have h2 : dk * q + (dm * q + m % q) =
        (((dk + dm) % 3) * q + m % q) + (3 * q) * ((dk + dm) / 3) := by
      have := Nat.div_add_mod (dk + dm) 3
      nlinarith
    have h3 : ((dk + dm) % 3) * q + m % q < 3 * q := by
      have : (dk + dm) % 3 < 3 := Nat.mod_lt _ (by omega)
      nlinarith
    rw [h1, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
  have hneq1 : (dk + dm) % 3 ≠ 1 := by
    intro h1
    apply hndvd
    rw [h3q]
    refine dvd_of_two_mul_mod hn ?_
    rw [hn_next, h1]
    omega
  have hfk := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt k (by omega))).2
  have hfm := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt m (by omega))).2
  have hgn := (gStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt n (by omega))).2
  rw [hk_next, hm_next, hn_next] at hbound
  rw [hk_next] at hfk
  rw [hm_next] at hfm
  rw [hn_next] at hgn
  interval_cases dk <;> interval_cases dm <;>
    simp only [Nat.reduceAdd, Nat.reduceMod, zero_mul, one_mul, zero_add] at hneq1 hbound hfk hfm hgn ⊢
  all_goals
    try exact absurd rfl hneq1
  all_goals
    split_ifs at hfk hfm hgn <;> omega

private lemma padicValNat_denom_le_tNat_mul {p n k m : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hkm : k + m = n) :
    padicValNat p ((2 * n - 1) * (3 * n).choose n) ≤ padicValNat p (tNat k * tNat m) := by
  have : Fact p.Prime := ⟨hp⟩
  set b := Nat.log p (6 * n) + 1
  have hb6n : Nat.log p (6 * n) < b := Nat.lt_succ_self _
  have hb6k : Nat.log p (6 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb6m : Nat.log p (6 * m) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb3n : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb2n : Nat.log p (2 * n - 1) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.mul (tNat_pos k).ne' (tNat_pos m).ne',
      padicValNat_eq_sum_ite_dvd (by omega) hb2n,
      padicValNat_choose_3n_eq_sum hb3n,
      padicValNat_tNat_eq_sum hb6k,
      padicValNat_tNat_eq_sum hb6m,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  by_cases h3 : p = 3 ∧ 3 ∣ 2 * n - 1
  · rcases h3 with ⟨rfl, h3dvd⟩
    set L : ℕ → ℕ := fun i => (if 3 ^ i ∣ 2 * n - 1 then 1 else 0) + gStep (3 ^ i) (n % 3 ^ i)
    set R : ℕ → ℕ := fun i => fStep (3 ^ i) (k % 3 ^ i) + fStep (3 ^ i) (m % 3 ^ i)
    change ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i
    have hge2 : ∀ i ∈ Finset.Ico 2 b, L i ≤ R i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      dsimp only [L, R]
      by_cases hd : 3 ^ i ∣ 2 * n - 1
      · rw [if_pos hd, ← hkm]
        have h3i_ge : 5 ≤ 3 ^ i := by
          have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) hi.1
          omega
        exact gStep_add_one_le_fStep_add h3i_ge (by omega) (hkm ▸ hd)
      · rw [if_neg hd, zero_add, ← hkm]
        exact gStep_le_fStep_add (pow_pos (by omega : 0 < 3) i)
    by_cases hL1 : L 1 ≤ R 1
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      by_cases hi1 : i = 1
      · subst hi1; exact hL1
      · exact hge2 i (Finset.mem_Ico.mpr ⟨by omega, hi.2⟩)
    · have h2n3 : n % 3 = 2 := by
        have := two_mul_mod_of_dvd hn (by omega) h3dvd
        omega
      have hL1_val : L 1 = 2 := by
        dsimp only [L]
        rw [pow_one, if_pos h3dvd, h2n3]
        decide
      have hk3_lt : k % 3 < 3 := Nat.mod_lt k (by omega)
      have hm3_lt : m % 3 < 3 := Nat.mod_lt m (by omega)
      have hkm3 : (k % 3 + m % 3) % 3 = 2 := by
        rw [← Nat.add_mod, hkm, h2n3]
      have hfk1 := (fStep_spec (q := 3) (r := k % 3) (by omega) hk3_lt).2
      have hfm1 := (fStep_spec (q := 3) (r := m % 3) (by omega) hm3_lt).2
      have hcases : (k % 3 = 0 ∧ m % 3 = 2) ∨ (k % 3 = 2 ∧ m % 3 = 0) := by
        have hR1 : R 1 < 2 := by omega
        dsimp only [R] at hR1
        rw [pow_one] at hR1
        split_ifs at hfk1 hfm1 <;> omega
      have hR1_val : R 1 = 1 := by
        dsimp only [R]
        rw [pow_one]
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · rw [hk0, hm2]; decide
        · rw [hk2, hm0]; decide
      have hsurplus : ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * n - 1) + 2), L j + 1 ≤ R j := by
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := k) (m := m) (by omega) hk0 hm2
          exact ⟨j, by rwa [hkm] at hj, by simpa only [L, R, hkm] using hle⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := m) (m := k) (by omega) hm0 hk2
          refine ⟨j, by rwa [add_comm m k, hkm] at hj, ?_⟩
          dsimp only [L, R]
          rw [add_comm m k, hkm] at hle
          omega
      obtain ⟨j, hj_mem, hj_surp⟩ := hsurplus
      rw [Finset.mem_Ico] at hj_mem
      have hr_pow : 3 ^ (padicValNat 3 (2 * n - 1) + 1) ≤ 6 * n := by
        have hpow_dvd : 3 ^ padicValNat 3 (2 * n - 1) ∣ 2 * n - 1 := pow_padicValNat_dvd
        have hle : 3 ^ padicValNat 3 (2 * n - 1) ≤ 2 * n - 1 := Nat.le_of_dvd (by omega) hpow_dvd
        rw [pow_succ']
        omega
      have hr_lt_b : padicValNat 3 (2 * n - 1) + 1 < b :=
        Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) hr_pow)
      have hj_in : j ∈ Finset.Ico 2 b := Finset.mem_Ico.mpr ⟨hj_mem.1, by omega⟩
      have h1b : 1 < b := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot h1b, Finset.sum_eq_sum_Ico_succ_bot h1b]
      rw [← Finset.add_sum_erase _ _ hj_in, ← Finset.add_sum_erase _ _ hj_in]
      have hrest : ∑ i ∈ (Finset.Ico 2 b).erase j, L i ≤ ∑ i ∈ (Finset.Ico 2 b).erase j, R i :=
        Finset.sum_le_sum fun i hi => hge2 i (Finset.mem_of_mem_erase hi)
      omega
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    by_cases hd : p ^ i ∣ 2 * n - 1
    · rw [if_pos hd, ← hkm]
      have hp_dvd : p ∣ 2 * n - 1 := dvd_trans (dvd_pow_self p (by omega)) hd
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hp_dvd
        omega
      have hp3 : p ≠ 3 := fun h3' => h3 ⟨h3', h3' ▸ hp_dvd⟩
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hne4 : p ≠ 4 := by intro h4; rw [h4] at hp; exact absurd hp (by decide)
        omega
      have hpi5 : 5 ≤ p ^ i :=
        le_trans hp5 (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hi.1)
      exact gStep_add_one_le_fStep_add hpi5 (by omega) (hkm ▸ hd)
    · rw [if_neg hd, zero_add, ← hkm]
      exact gStep_le_fStep_add (pow_pos hp.pos i)

private lemma denom_dvd_tNat_mul {n k m : ℕ} (hn : 0 < n) (hkm : k + m = n) :
    (2 * n - 1) * (3 * n).choose n ∣ tNat k * tNat m := by
  rw [← Nat.factorization_le_iff_dvd (denom_pos hn).ne'
      (Nat.mul_pos (tNat_pos k) (tNat_pos m)).ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact padicValNat_denom_le_tNat_mul hp hn hkm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma denom_dvd_sNat {n : ℕ} (hn : 0 < n) :
    (2 * n - 1) * (3 * n).choose n ∣ sNat n := by
  unfold sNat
  refine Finset.dvd_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact denom_dvd_tNat_mul hn (Nat.add_sub_of_le hkn)


/-! ## 2-adic valuation and parity of `a n / 8` (Conjecture 3) -/

private def s2 (m : ℕ) : ℕ := (Nat.digits 2 m).sum

private lemma s2_zero : s2 0 = 0 := rfl

private lemma s2_two_mul (m : ℕ) : s2 (2 * m) = s2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · unfold s2
    rw [Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < 2 * m)]
    simp [Nat.mul_div_right m (by decide : 0 < 2)]

private lemma s2_two_mul_add_one (m : ℕ) : s2 (2 * m + 1) = s2 m + 1 := by
  unfold s2
  rw [Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < 2 * m + 1)]
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hmod, hdiv, List.sum_cons, add_comm]

private lemma s2_pos {m : ℕ} (hm : 0 < m) : 0 < s2 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul, s2_two_mul]
      exact ih k (by omega) (by omega)
    · rw [s2_two_mul_add_one]
      omega

private lemma s2_le_self (m : ℕ) : s2 m ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [s2_zero]
    · rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [← two_mul, s2_two_mul]
        have := ih k (by omega)
        omega
      · rw [s2_two_mul_add_one]
        have := ih k (by omega)
        omega

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_two_mul, ih]

private lemma s2_eq_one_iff {m : ℕ} (hm : 0 < m) : s2 m = 1 ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro hs
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [← two_mul] at hs hm ⊢
        rw [s2_two_mul] at hs
        obtain ⟨j, hj⟩ := ih k (by omega) (by omega) hs
        exact ⟨j + 1, by rw [hj, pow_succ']⟩
      · rw [s2_two_mul_add_one] at hs
        have hk0 : k = 0 := by
          by_contra hk
          have := s2_pos (Nat.pos_of_ne_zero hk)
          omega
        exact ⟨0, by omega⟩
  · rintro ⟨k, rfl⟩
    exact s2_pow_two k

private lemma s2_three_mul_pow_two (k : ℕ) : s2 (3 * 2 ^ k) = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', show 3 * (2 * 2 ^ k) = 2 * (3 * 2 ^ k) by ring, s2_two_mul, ih]

private lemma two_le_s2_three_mul {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  have hpos : 0 < s2 (3 * n) := s2_pos (by omega)
  by_contra hlt
  have h1 : s2 (3 * n) = 1 := by omega
  obtain ⟨k, hk⟩ := (s2_eq_one_iff (by omega)).mp h1
  have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
  have h3not : ¬ (3 ∣ 2 ^ k) := by
    intro h
    have h32 : 3 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h)
    omega
  exact h3not h3dvd

private lemma padicValNat_two_factorial (m : ℕ) :
    padicValNat 2 m.factorial = m - s2 m := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  simpa [s2] using h

private lemma padicValNat_two_tNat (k : ℕ) :
    padicValNat 2 (tNat k) = 2 * s2 k := by
  have hfac := tNat_mul_factorials k
  have hval := congrArg (padicValNat 2) hfac
  have ht : tNat k ≠ 0 := (tNat_pos k).ne'
  have h3 : (3 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h2 : (2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h1 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero ht h3) h2) h1,
      padicValNat.mul (mul_ne_zero ht h3) h2,
      padicValNat.mul ht h3] at hval
  simp only [padicValNat_two_factorial] at hval
  have hs6 : s2 (6 * k) = s2 (3 * k) := by
    rw [show 6 * k = 2 * (3 * k) by ring, s2_two_mul]
  have hs2 : s2 (2 * k) = s2 k := s2_two_mul k
  have hl3 : s2 (3 * k) ≤ 3 * k := s2_le_self (3 * k)
  have hl1 : s2 k ≤ k := s2_le_self k
  omega

private lemma padicValNat_two_choose_3n (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) + s2 (3 * n) = 2 * s2 n := by
  have hfac := choose_3n_mul_factorials n
  have hval := congrArg (padicValNat 2) hfac
  have hc : (3 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h1 : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have h2 : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat.mul (mul_ne_zero hc h1) h2, padicValNat.mul hc h1] at hval
  simp only [padicValNat_two_factorial] at hval
  have hs2 : s2 (2 * n) = s2 n := s2_two_mul n
  have hl3 : s2 (3 * n) ≤ 3 * n := s2_le_self (3 * n)
  have hl1 : s2 n ≤ n := s2_le_self n
  omega

private lemma padicValNat_two_choose {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (n.choose k) + s2 n = s2 k + s2 (n - k) := by
  have hfac := Nat.choose_mul_factorial_mul_factorial hk
  have hval := congrArg (padicValNat 2) hfac
  have hc : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have h1 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  have h2 : (n - k).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat.mul (mul_ne_zero hc h1) h2, padicValNat.mul hc h1] at hval
  simp only [padicValNat_two_factorial] at hval
  have hln : s2 n ≤ n := s2_le_self n
  have hlk : s2 k ≤ k := s2_le_self k
  have hlnk : s2 (n - k) ≤ n - k := s2_le_self (n - k)
  omega

private lemma padicValNat_two_eq_zero_iff_odd {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 m = 0 ↔ Odd m := by
  constructor
  · intro h0
    rw [Nat.odd_iff]
    by_contra hne
    have hdvd : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have hpos : 0 < padicValNat 2 m := one_le_padicValNat_of_dvd hm hdvd
    omega
  · intro hodd
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨k, hk⟩ := hodd
    omega

private lemma odd_choose_two_mul_iff (m k : ℕ) :
    Odd ((2 * m).choose k) ↔ k % 2 = 0 ∧ Odd (m.choose (k / 2)) := by
  have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2 * m) (k := k)
  have h2m : 2 * m % 2 = 0 := by omega
  have h2d : 2 * m / 2 = m := by omega
  rw [h2m, h2d] at hluc
  change (2 * m).choose k % 2 = (Nat.choose 0 (k % 2) * m.choose (k / 2)) % 2 at hluc
  rw [Nat.odd_iff, Nat.odd_iff, hluc]
  have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk2 with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma odd_choose_two_mul_add_one_iff (m k : ℕ) :
    Odd ((2 * m + 1).choose k) ↔ Odd (m.choose (k / 2)) := by
  have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2 * m + 1) (k := k)
  have h2m : (2 * m + 1) % 2 = 1 := by omega
  have h2d : (2 * m + 1) / 2 = m := by omega
  rw [h2m, h2d] at hluc
  change (2 * m + 1).choose k % 2 = (Nat.choose 1 (k % 2) * m.choose (k / 2)) % 2 at hluc
  rw [Nat.odd_iff, Nat.odd_iff, hluc]
  have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk2 with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma card_odd_choose (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun k => Odd (n.choose k))).card = 2 ^ s2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [← two_mul, s2_two_mul]
        have hbij : ((Finset.range (m + 1)).filter (fun j => Odd (m.choose j))).image (fun j => 2 * j) =
            (Finset.range (2 * m + 1)).filter (fun k => Odd ((2 * m).choose k)) := by
          ext k
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, odd_choose_two_mul_iff]
          constructor
          · rintro ⟨j, ⟨hj, hodd⟩, rfl⟩
            exact ⟨by omega, by omega, by simpa using hodd⟩
          · rintro ⟨hk, hmod, hodd⟩
            exact ⟨k / 2, ⟨by omega, hodd⟩, by omega⟩
        rw [← hbij, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
        exact ih m (by omega)
      · rw [s2_two_mul_add_one, pow_succ]
        let S := (Finset.range (m + 1)).filter (fun j => Odd (m.choose j))
        let S0 := S.image (fun j => 2 * j)
        let S1 := S.image (fun j => 2 * j + 1)
        have hdisj : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]
          intro k h0 h1
          obtain ⟨j0, _, rfl⟩ := Finset.mem_image.mp h0
          obtain ⟨j1, _, h⟩ := Finset.mem_image.mp h1
          omega
        have hunion : S0 ∪ S1 =
            (Finset.range (2 * m + 1 + 1)).filter (fun k => Odd ((2 * m + 1).choose k)) := by
          ext k
          simp only [S0, S1, S, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_range, odd_choose_two_mul_add_one_iff]
          constructor
          · rintro (⟨j, ⟨hj, hodd⟩, rfl⟩ | ⟨j, ⟨hj, hodd⟩, rfl⟩)
            · exact ⟨by omega, by simpa using hodd⟩
            · exact ⟨by omega, by rw [show (2 * j + 1) / 2 = j by omega]; exact hodd⟩
          · rintro ⟨hk, hodd⟩
            have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
            rcases hmod with h0 | h1
            · left; exact ⟨k / 2, ⟨by omega, hodd⟩, by omega⟩
            · right; exact ⟨k / 2, ⟨by omega, hodd⟩, by omega⟩
        rw [← hunion, Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (fun _ _ h => by omega),
            Finset.card_image_of_injective _ (fun _ _ h => by omega),
            ih m (by omega), mul_two]

private lemma card_odd_choose_half_even {n : ℕ} (hn : 0 < n) (hnot : ¬ ∃ k : ℕ, n = 2 ^ k) :
    Even ((Finset.range ((n + 1) / 2)).filter (fun k => Odd (n.choose k))).card := by
  let A := (Finset.range ((n + 1) / 2)).filter (fun k => Odd (n.choose k))
  let B := A.image (fun k => n - k)
  let All := (Finset.range (n + 1)).filter (fun k => Odd (n.choose k))
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro k hkA hkB
    obtain ⟨hk1, _⟩ := Finset.mem_filter.mp hkA
    obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hkB
    have hk_lt := Finset.mem_range.mp hk1
    have hj_lt := Finset.mem_range.mp (Finset.mem_filter.mp hjA).1
    omega
  have hunion : A ∪ B = All := by
    ext k
    simp only [A, B, All, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨hk, hodd⟩ | ⟨j, ⟨hj, hodd⟩, rfl⟩)
      · exact ⟨by omega, hodd⟩
      · refine ⟨by omega, ?_⟩
        rwa [Nat.choose_symm (by omega : j ≤ n)]
    · rintro ⟨hk, hodd⟩
      by_cases hlt : k < (n + 1) / 2
      · left; exact ⟨hlt, hodd⟩
      · by_cases hmid : 2 * k = n
        · exfalso
          have hval0 : padicValNat 2 (n.choose k) = 0 :=
            (padicValNat_two_eq_zero_iff_odd (Nat.choose_pos (by omega)).ne').mpr hodd
          have hch := padicValNat_two_choose (n := n) (k := k) (by omega)
          have hsub : n - k = k := by omega
          rw [hval0, zero_add, hsub, ← hmid, s2_two_mul k] at hch
          have hpos : 0 < s2 k := s2_pos (by omega)
          omega
        · right
          refine ⟨n - k, ⟨by omega, ?_⟩, by omega⟩
          rwa [Nat.choose_symm (by omega : k ≤ n)]
  have hinj : Set.InjOn (fun k => n - k) (A : Set ℕ) := by
    intro x hx y hy heq
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    dsimp only at heq
    omega
  have hcard : 2 * A.card = 2 ^ s2 n := by
    have h1 : All.card = 2 ^ s2 n := card_odd_choose n
    rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
        ← two_mul] at h1
    exact h1
  have hs2 : 2 ≤ s2 n := by
    have hpos := s2_pos hn
    have hne1 : s2 n ≠ 1 := fun h1 => hnot ((s2_eq_one_iff hn).mp h1)
    omega
  have h4 : 4 ∣ 2 ^ s2 n := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide]
    exact Nat.pow_dvd_pow 2 hs2
  rw [← hcard] at h4
  obtain ⟨t, ht⟩ := h4
  exact ⟨t, by change A.card = t + t; omega⟩

private lemma sNat_split_odd (r : ℕ) :
    sNat (2 * r + 1) = 2 * ∑ k ∈ Finset.range (r + 1), tNat k * tNat (2 * r + 1 - k) := by
  unfold sNat
  have hsplit : Finset.range (2 * r + 1 + 1) =
      Finset.range (r + 1) ∪ Finset.Ico (r + 1) (2 * r + 2) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range (r + 1)) (Finset.Ico (r + 1) (2 * r + 2)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hsym : ∑ k ∈ Finset.Ico (r + 1) (2 * r + 2), tNat k * tNat (2 * r + 1 - k) =
      ∑ k ∈ Finset.range (r + 1), tNat k * tNat (2 * r + 1 - k) := by
    refine Finset.sum_nbij (fun k => 2 * r + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro x hx y hy heq
      simp only [Finset.mem_coe, Finset.mem_Ico] at hx hy
      dsimp only at heq
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_range, Set.mem_image, Finset.mem_Ico] at hj ⊢
      exact ⟨2 * r + 1 - j, ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Ico] at hk
      rw [show 2 * r + 1 - (2 * r + 1 - k) = k by omega, mul_comm]
  rw [hsym, ← two_mul]

private lemma sNat_split_even (r : ℕ) :
    sNat (2 * r) = tNat r * tNat r + 2 * ∑ k ∈ Finset.range r, tNat k * tNat (2 * r - k) := by
  unfold sNat
  have hsplit : Finset.range (2 * r + 1) =
      insert r (Finset.range r ∪ Finset.Ico (r + 1) (2 * r + 1)) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hrnot : r ∉ Finset.range r ∪ Finset.Ico (r + 1) (2 * r + 1) := by
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range r) (Finset.Ico (r + 1) (2 * r + 1)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [hsplit, Finset.sum_insert hrnot, Finset.sum_union hdisj, show 2 * r - r = r by omega]
  have hsym : ∑ k ∈ Finset.Ico (r + 1) (2 * r + 1), tNat k * tNat (2 * r - k) =
      ∑ k ∈ Finset.range r, tNat k * tNat (2 * r - k) := by
    refine Finset.sum_nbij (fun k => 2 * r - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro x hx y hy heq
      simp only [Finset.mem_coe, Finset.mem_Ico] at hx hy
      dsimp only at heq
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_range, Set.mem_image, Finset.mem_Ico] at hj ⊢
      exact ⟨2 * r - j, ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Ico] at hk
      rw [show 2 * r - (2 * r - k) = k by omega, mul_comm]
  rw [hsym, ← two_mul]

private lemma padicValNat_two_pair_term {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (2 * (tNat k * tNat (n - k))) =
      padicValNat 2 ((3 * n).choose n) + s2 (3 * n) + 1 + 2 * padicValNat 2 (n.choose k) := by
  have hne : tNat k * tNat (n - k) ≠ 0 := mul_ne_zero (tNat_pos k).ne' (tNat_pos (n - k)).ne'
  rw [padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hne,
      padicValNat.self (by decide : 1 < 2),
      padicValNat.mul (tNat_pos k).ne' (tNat_pos (n - k)).ne',
      padicValNat_two_tNat k, padicValNat_two_tNat (n - k)]
  have hc3 := padicValNat_two_choose_3n n
  have hck := padicValNat_two_choose hk
  omega

private lemma padicValNat_two_mid_term {r : ℕ} (hr : 0 < r) :
    padicValNat 2 ((3 * (2 * r)).choose (2 * r)) + 4 ≤ padicValNat 2 (tNat r * tNat r) := by
  rw [padicValNat.mul (tNat_pos r).ne' (tNat_pos r).ne', padicValNat_two_tNat r]
  have hc3 := padicValNat_two_choose_3n (2 * r)
  rw [s2_two_mul r] at hc3
  have hs3 : 2 ≤ s2 (3 * (2 * r)) := two_le_s2_three_mul (by omega)
  have hsr : 1 ≤ s2 r := s2_pos hr
  omega

private lemma pow_two_dvd_iff_le_padicValNat {m e : ℕ} (hm : m ≠ 0) :
    2 ^ e ∣ m ↔ e ≤ padicValNat 2 m :=
  padicValNat_dvd_iff_le hm

private lemma dvd_sNat_two_pow_add_three {n : ℕ} (hn : 0 < n) :
    2 ^ (padicValNat 2 ((3 * n).choose n) + 3) ∣ sNat n := by
  set d := padicValNat 2 ((3 * n).choose n)
  have hs3 : 2 ≤ s2 (3 * n) := two_le_s2_three_mul hn
  have hpair : ∀ k ≤ n, 2 ^ (d + 3) ∣ 2 * (tNat k * tNat (n - k)) := by
    intro k hk
    rw [pow_two_dvd_iff_le_padicValNat (mul_ne_zero (by decide) (mul_ne_zero (tNat_pos k).ne' (tNat_pos (n - k)).ne'))]
    rw [padicValNat_two_pair_term hk]
    omega
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2r : n = 2 * r := by omega
    subst h2r
    rw [sNat_split_even r]
    refine Nat.dvd_add ?_ ?_
    · rw [pow_two_dvd_iff_le_padicValNat (mul_ne_zero (tNat_pos r).ne' (tNat_pos r).ne')]
      have := padicValNat_two_mid_term (by omega : 0 < r)
      omega
    · rw [Finset.mul_sum]
      exact Finset.dvd_sum fun k hk => hpair k (by have := Finset.mem_range.mp hk; omega)
  · subst hr
    rw [sNat_split_odd r, Finset.mul_sum]
    exact Finset.dvd_sum fun k hk => hpair k (by have := Finset.mem_range.mp hk; omega)

private lemma sum_mod_two_of_pow_two_dvd {ι : Type*} (s : Finset ι) (f : ι → ℕ) (e : ℕ)
    (hdvd : ∀ i ∈ s, 2 ^ e ∣ f i) :
    (∑ i ∈ s, f i) / 2 ^ e % 2 =
      (s.filter (fun i => ¬ 2 ^ (e + 1) ∣ f i)).card % 2 := by
  have hdiv_sum : (∑ i ∈ s, f i) / 2 ^ e = ∑ i ∈ s, f i / 2 ^ e := by
    have hpos : 0 < 2 ^ e := Nat.pow_pos (by decide)
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [Nat.mul_div_cancel' (Finset.dvd_sum hdvd), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => (Nat.mul_div_cancel' (hdvd i hi)).symm
  rw [hdiv_sum, Finset.sum_nat_mod]
  have hterm : ∀ i ∈ s, f i / 2 ^ e % 2 = if ¬ 2 ^ (e + 1) ∣ f i then 1 else 0 := by
    intro i hi
    obtain ⟨q, hq⟩ := hdvd i hi
    have hpos : 0 < 2 ^ e := Nat.pow_pos (by decide)
    have hdiv : f i / 2 ^ e = q := by rw [hq, Nat.mul_div_right q hpos]
    rw [hdiv]
    by_cases h2q : 2 ∣ q
    · have hpow : 2 ^ (e + 1) ∣ f i := by
        obtain ⟨u, rfl⟩ := h2q
        exact ⟨u, by rw [hq, pow_succ]; ring⟩
      rw [if_neg (not_not.mpr hpow)]
      exact Nat.mod_eq_zero_of_dvd h2q
    · have hnpow : ¬ 2 ^ (e + 1) ∣ f i := by
        rintro ⟨u, hu⟩
        apply h2q
        refine ⟨u, ?_⟩
        have : 2 ^ e * q = 2 ^ e * (2 * u) := by
          calc 2 ^ e * q = f i := hq.symm
            _ = 2 ^ (e + 1) * u := hu
            _ = 2 ^ e * (2 * u) := by rw [pow_succ]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      rw [if_pos hnpow]
      omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul, mul_one]

private lemma not_dvd_sNat_two_pow_add_four_iff {n : ℕ} (hn : 0 < n) :
    ¬ 2 ^ (padicValNat 2 ((3 * n).choose n) + 4) ∣ sNat n ↔ ∃ k : ℕ, n = 2 ^ k := by
  set d := padicValNat 2 ((3 * n).choose n)
  have hs3 : 2 ≤ s2 (3 * n) := two_le_s2_three_mul hn
  have hdvd3 : 2 ^ (d + 3) ∣ sNat n := dvd_sNat_two_pow_add_three hn
  have hodd_iff : ¬ 2 ^ (d + 4) ∣ sNat n ↔ (sNat n / 2 ^ (d + 3)) % 2 = 1 := by
    obtain ⟨q, hq⟩ := hdvd3
    have hpos : 0 < 2 ^ (d + 3) := Nat.pow_pos (by decide)
    have hdiv : sNat n / 2 ^ (d + 3) = q := by rw [hq, Nat.mul_div_right q hpos]
    rw [hdiv]
    constructor
    · intro hndvd
      by_contra hne1
      have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      obtain ⟨u, rfl⟩ := h2q
      exact hndvd ⟨u, by rw [hq, pow_succ]; ring⟩
    · rintro hq1 ⟨u, hu⟩
      have : 2 ^ (d + 3) * q = 2 ^ (d + 3) * (2 * u) := by
        calc 2 ^ (d + 3) * q = sNat n := hq.symm
          _ = 2 ^ (d + 4) * u := hu
          _ = 2 ^ (d + 3) * (2 * u) := by rw [pow_succ]; ring
      have := Nat.eq_of_mul_eq_mul_left hpos this
      omega
  rw [hodd_iff]
  have hhalf_eq : (sNat n / 2 ^ (d + 3)) % 2 =
      ((Finset.range ((n + 1) / 2)).filter
        (fun k => ¬ 2 ^ (d + 4) ∣ 2 * (tNat k * tNat (n - k)))).card % 2 := by
    have hpair3 : ∀ k ∈ Finset.range ((n + 1) / 2),
        2 ^ (d + 3) ∣ 2 * (tNat k * tNat (n - k)) := by
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [pow_two_dvd_iff_le_padicValNat
        (mul_ne_zero (by decide) (mul_ne_zero (tNat_pos k).ne' (tNat_pos (n - k)).ne'))]
      rw [padicValNat_two_pair_term hkn]
      omega
    rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
    · have h2r : n = 2 * r := by omega
      subst h2r
      have hhalf : (2 * r + 1) / 2 = r := by omega
      rw [hhalf, sNat_split_even r, Finset.mul_sum]
      have hmid4 : 2 ^ (d + 4) ∣ tNat r * tNat r := by
        rw [pow_two_dvd_iff_le_padicValNat (mul_ne_zero (tNat_pos r).ne' (tNat_pos r).ne')]
        exact padicValNat_two_mid_term (by omega : 0 < r)
      have hmid3 : 2 ^ (d + 3) ∣ tNat r * tNat r :=
        dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hmid4
      have hsum3 : 2 ^ (d + 3) ∣ ∑ k ∈ Finset.range r, 2 * (tNat k * tNat (2 * r - k)) :=
        Finset.dvd_sum fun k hk => hpair3 k (by rwa [hhalf])
      have hdiv_add :
          (tNat r * tNat r + ∑ k ∈ Finset.range r, 2 * (tNat k * tNat (2 * r - k))) / 2 ^ (d + 3) =
          (tNat r * tNat r) / 2 ^ (d + 3) +
          (∑ k ∈ Finset.range r, 2 * (tNat k * tNat (2 * r - k))) / 2 ^ (d + 3) := by
        have hpos : 0 < 2 ^ (d + 3) := Nat.pow_pos (by decide)
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [Nat.mul_div_cancel' (Nat.dvd_add hmid3 hsum3), mul_add,
            Nat.mul_div_cancel' hmid3, Nat.mul_div_cancel' hsum3]
      have hmid_even : (tNat r * tNat r) / 2 ^ (d + 3) % 2 = 0 := by
        obtain ⟨u, hu⟩ := hmid4
        have hpos : 0 < 2 ^ (d + 3) := Nat.pow_pos (by decide)
        have : (tNat r * tNat r) / 2 ^ (d + 3) = 2 * u := by
          rw [hu, pow_succ, mul_assoc, Nat.mul_div_right _ hpos]
        rw [this]
        omega
      rw [hdiv_add, Nat.add_mod, hmid_even, zero_add, Nat.mod_mod]
      exact sum_mod_two_of_pow_two_dvd _ _ (d + 3) (fun k hk => hpair3 k (by rwa [hhalf]))
    · subst hr
      have hhalf : (2 * r + 1 + 1) / 2 = r + 1 := by omega
      rw [hhalf, sNat_split_odd r, Finset.mul_sum]
      exact sum_mod_two_of_pow_two_dvd _ _ (d + 3) (fun k hk => hpair3 k (by rwa [hhalf]))
  rw [hhalf_eq]
  have hfilter_iff : ∀ k ∈ Finset.range ((n + 1) / 2),
      ¬ 2 ^ (d + 4) ∣ 2 * (tNat k * tNat (n - k)) ↔ s2 (3 * n) = 2 ∧ Odd (n.choose k) := by
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [pow_two_dvd_iff_le_padicValNat
      (mul_ne_zero (by decide) (mul_ne_zero (tNat_pos k).ne' (tNat_pos (n - k)).ne')),
      padicValNat_two_pair_term hkn,
      ← padicValNat_two_eq_zero_iff_odd (Nat.choose_pos hkn).ne']
    omega
  constructor
  · intro h1
    by_contra hnot
    by_cases hs3eq : s2 (3 * n) = 2
    · have hfeq : (Finset.range ((n + 1) / 2)).filter
          (fun k => ¬ 2 ^ (d + 4) ∣ 2 * (tNat k * tNat (n - k))) =
          (Finset.range ((n + 1) / 2)).filter (fun k => Odd (n.choose k)) := by
        apply Finset.filter_congr
        intro k hk
        rw [hfilter_iff k hk, hs3eq]
        simp
      rw [hfeq] at h1
      obtain ⟨t, ht⟩ := card_odd_choose_half_even hn hnot
      omega
    · have hfeq : (Finset.range ((n + 1) / 2)).filter
          (fun k => ¬ 2 ^ (d + 4) ∣ 2 * (tNat k * tNat (n - k))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk
        rw [hfilter_iff k hk]
        intro h
        exact hs3eq h.1
      rw [hfeq] at h1
      simp at h1
  · rintro ⟨j, rfl⟩
    have hs3eq : s2 (3 * 2 ^ j) = 2 := s2_three_mul_pow_two j
    have hfeq : (Finset.range ((2 ^ j + 1) / 2)).filter
        (fun k => ¬ 2 ^ (d + 4) ∣ 2 * (tNat k * tNat (2 ^ j - k))) = {0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, hndvd⟩
        have hodd : Odd ((2 ^ j).choose k) := ((hfilter_iff k (Finset.mem_range.mpr hk)).mp hndvd).2
        have hval0 : padicValNat 2 ((2 ^ j).choose k) = 0 :=
          (padicValNat_two_eq_zero_iff_odd (Nat.choose_pos (by omega)).ne').mpr hodd
        have hch := padicValNat_two_choose (n := 2 ^ j) (k := k) (by omega)
        rw [hval0, zero_add, s2_pow_two j] at hch
        by_contra hk0
        have h1 := s2_pos (Nat.pos_of_ne_zero hk0)
        have h2 := s2_pos (by omega : 0 < 2 ^ j - k)
        omega
      · rintro rfl
        have h0lt : 0 < (2 ^ j + 1) / 2 := by
          have : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
          omega
        refine ⟨h0lt, (hfilter_iff 0 (Finset.mem_range.mpr h0lt)).mpr ⟨hs3eq, by simp⟩⟩
    rw [hfeq]
    decide

private theorem conjecture_3_proof (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  obtain ⟨q, hq⟩ := denom_dvd_sNat hn
  have hq_pos : 0 < q := by
    by_contra h0
    have hq0 : q = 0 := by omega
    rw [hq0, mul_zero] at hq
    exact (sNat_pos n).ne' hq
  have hd_val : padicValNat 2 ((2 * n - 1) * (3 * n).choose n) =
      padicValNat 2 ((3 * n).choose n) := by
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne']
    have hodd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
    rw [(padicValNat_two_eq_zero_iff_odd (by omega)).mpr hodd, zero_add]
  have hval_s : padicValNat 2 (sNat n) = padicValNat 2 ((3 * n).choose n) + padicValNat 2 q := by
    rw [hq, padicValNat.mul (denom_pos hn).ne' hq_pos.ne', hd_val]
  have h8dvd : 8 ∣ q := by
    have h3 : 2 ^ (padicValNat 2 ((3 * n).choose n) + 3) ∣ sNat n :=
      dvd_sNat_two_pow_add_three hn
    rw [pow_two_dvd_iff_le_padicValNat (sNat_pos n).ne', hval_s] at h3
    have h23 : 2 ^ 3 ∣ q := (pow_two_dvd_iff_le_padicValNat hq_pos.ne').mpr (by omega)
    simpa using h23
  obtain ⟨m0, hm0⟩ := h8dvd
  refine ⟨(m0 : ℤ), ?_, ?_⟩
  · have hd_ne : (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (denom_pos hn).ne'
    rw [a_eq_div_nat hn, hq, Nat.cast_mul, mul_div_cancel_left₀ _ hd_ne, hm0]
    push_cast
    ring
  · rw [Int.odd_coe_nat]
    rw [← not_dvd_sNat_two_pow_add_four_iff hn,
        pow_two_dvd_iff_le_padicValNat (sNat_pos n).ne', hval_s, hm0,
        padicValNat.mul (by decide : (8 : ℕ) ≠ 0) (by omega : m0 ≠ 0)]
    have h8v : padicValNat 2 8 = 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, padicValNat.prime_pow]
    rw [h8v, ← padicValNat_two_eq_zero_iff_odd (by omega : m0 ≠ 0)]
    omega

end OeisA189286

theorem OMA.solution : type_of% @OeisA189286.conjecture_3 :=
  OeisA189286.conjecture_3_proof
