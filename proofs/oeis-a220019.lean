import OMAStatements.S_oeis_a220019
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

-- Problem: A220019: Number of cyclotomic cosets of 7 mod 10^n.
-- Upstream: formal-conjectures statements/oeis-a220019.lean:0 (declaration OMA.S_oeis_a220019.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Proof via Burnside's lemma on Additive (ZMod M) acting on ZMod (10^n) by multiplication by 7^k,
-- combined with 2-adic and 5-adic Lifting the Exponent for 7^k - 1 and CRT factorization.

namespace OMA_A220019

open OMA.S_oeis_a220019 Finset

/-! ### Part 1: 2-adic and 5-adic LTE for `7^k - 1` -/

/-- Exact 2-adic valuation of `7^(2^j * m) - 1` for `j ≥ 1` and `m` odd:
`7^(2^j * m) - 1 = 2^(j + 3) * t` with `t` odd. -/
private lemma pow7_sub_one_two_adic_pow :
    ∀ j : ℕ, ∃ t : ℕ, Odd t ∧ 7 ^ (2 ^ (j + 1)) - 1 = 2 ^ (j + 4) * t := by
  intro j
  induction j with
  | zero =>
    exact ⟨3, ⟨1, rfl⟩, by decide⟩
  | succ j ih =>
    rcases ih with ⟨t, ⟨u, rfl⟩, ht⟩
    have hpow : 7 ^ (2 ^ (j + 2)) = (7 ^ (2 ^ (j + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ]
    have hge1 : 1 ≤ 7 ^ (2 ^ (j + 1)) := Nat.one_le_pow _ _ (by omega)
    have hfac : 7 ^ (2 ^ (j + 2)) - 1 = (7 ^ (2 ^ (j + 1)) - 1) * (7 ^ (2 ^ (j + 1)) + 1) := by
      rw [hpow]
      zify [hge1, show 1 ≤ (7 ^ (2 ^ (j + 1))) ^ 2 by nlinarith]
      ring
    have hplus : 7 ^ (2 ^ (j + 1)) + 1 = 2 * (2 ^ (j + 3) * (2 * u + 1) + 1) := by
      have h7 : 7 ^ (2 ^ (j + 1)) = 2 ^ (j + 4) * (2 * u + 1) + 1 := by omega
      rw [h7, pow_succ]
      ring
    refine ⟨(2 * u + 1) * (2 ^ (j + 3) * (2 * u + 1) + 1), ?_, ?_⟩
    · have heven : 2 ∣ 2 ^ (j + 3) := dvd_pow_self 2 (by omega)
      rcases heven with ⟨w, hw⟩
      refine ⟨u + (2 * u + 1) * (w * (2 * u + 1)), ?_⟩
      rw [hw]; ring
    · rw [hfac, ht, hplus, pow_succ]
      ring

private lemma odd_sum_geom_odd {a m : ℕ} (ha : Odd a) (hm : Odd m) :
    Odd (∑ i ∈ range m, a ^ i) := by
  have hmod : ∀ i, a ^ i % 2 = 1 := by
    intro i
    rcases ha with ⟨k, rfl⟩
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      omega
  have hsum : ∀ k, (∑ i ∈ range k, a ^ i) % 2 = k % 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, Nat.add_mod, ih, hmod k]
      omega
  rw [Nat.odd_iff, hsum m]
  exact Nat.odd_iff.mp hm

private lemma pow_sub_one_eq_mul_geom (a m : ℕ) (ha : 1 ≤ a) :
    a ^ m - 1 = (a - 1) * ∑ i ∈ range m, a ^ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hge : 1 ≤ a ^ m := Nat.one_le_pow _ _ ha
    have hge' : 1 ≤ a ^ (m + 1) := Nat.one_le_pow _ _ ha
    rw [sum_range_succ, mul_add, ← ih]
    zify [ha, hge, hge']
    rw [pow_succ]
    ring

private lemma pow7_sub_one_two_adic (j m : ℕ) (hm : Odd m) :
    ∃ t : ℕ, Odd t ∧ 7 ^ (2 ^ (j + 1) * m) - 1 = 2 ^ (j + 4) * t := by
  obtain ⟨t0, ht0, h0⟩ := pow7_sub_one_two_adic_pow j
  have ha : 1 ≤ 7 ^ (2 ^ (j + 1)) := Nat.one_le_pow _ _ (by omega)
  have hodd_a : Odd (7 ^ (2 ^ (j + 1))) := Odd.pow ⟨3, rfl⟩
  have hgeom := odd_sum_geom_odd hodd_a hm
  refine ⟨t0 * ∑ i ∈ range m, (7 ^ (2 ^ (j + 1))) ^ i, ht0.mul hgeom, ?_⟩
  rw [pow_mul, pow_sub_one_eq_mul_geom _ m ha, h0, mul_assoc]

private lemma gcd_mul_right_of_coprime {a b c : ℕ} (h : Nat.Coprime b c) :
    Nat.gcd (a * b) c = Nat.gcd a c := by
  apply Nat.dvd_antisymm
  · have hd_ab : Nat.gcd (a * b) c ∣ a * b := Nat.gcd_dvd_left (a * b) c
    have hd_c : Nat.gcd (a * b) c ∣ c := Nat.gcd_dvd_right (a * b) c
    have hcop : Nat.Coprime (Nat.gcd (a * b) c) b := (h.coprime_dvd_right hd_c).symm
    exact Nat.dvd_gcd (hcop.dvd_of_dvd_mul_right hd_ab) hd_c
  · exact Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a c) b) (Nat.gcd_dvd_right a c)

private lemma gcd_pow7_sub_one_two_odd (k n : ℕ) (hk : Odd k) (hn : 1 ≤ n) :
    Nat.gcd (7 ^ k - 1) (2 ^ n) = 2 := by
  have hmod4 : 7 ^ k % 4 = 3 := by
    rcases hk with ⟨m, rfl⟩
    have h49 : 7 ^ 2 % 4 = 1 := by decide
    rw [pow_add, pow_mul, pow_one, Nat.mul_mod, Nat.pow_mod, h49]
    simp
  have hge1 : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by omega)
  have hdvd2 : 2 ∣ 7 ^ k - 1 := by omega
  have hndvd4 : ¬ 4 ∣ 7 ^ k - 1 := by omega
  rcases hdvd2 with ⟨t, ht⟩
  have ht_odd : Odd t := by
    rw [Nat.odd_iff]; omega
  have hcop : Nat.Coprime t (2 ^ (n - 1)) :=
    Nat.Coprime.pow_right _ ((Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro h2; rcases ht_odd with ⟨u, hu⟩; omega)).symm)
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm]
  rw [ht, h2n, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

private lemma gcd_pow7_sub_one_two_even (j m n : ℕ) (hm : Odd m) :
    Nat.gcd (7 ^ (2 ^ (j + 1) * m) - 1) (2 ^ n) = 2 ^ (min n (j + 4)) := by
  obtain ⟨t, ht, hEq⟩ := pow7_sub_one_two_adic j m hm
  rw [hEq]
  have hcop : Nat.Coprime t (2 ^ n) :=
    Nat.Coprime.pow_right _ ((Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro h2; rcases ht with ⟨u, hu⟩; omega)).symm)
  rw [gcd_mul_right_of_coprime hcop]
  by_cases h : n ≤ j + 4
  · rw [Nat.min_eq_left h]
    exact Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)
  · rw [Nat.min_eq_right (by omega)]
    exact Nat.gcd_eq_left (Nat.pow_dvd_pow 2 (by omega))

/-- Exact 5-adic valuation of `7^(4 * 5^j) - 1`: `5^(j + 2) * t` with `5 ∤ t`. -/
private lemma pow7_sub_one_five_adic_pow :
    ∀ j : ℕ, ∃ t : ℕ, ¬ 5 ∣ t ∧ 7 ^ (4 * 5 ^ j) - 1 = 5 ^ (j + 2) * t := by
  intro j
  induction j with
  | zero =>
    exact ⟨96, by decide, by decide⟩
  | succ j ih =>
    rcases ih with ⟨t, ht5, ht⟩
    set a := 7 ^ (4 * 5 ^ j)
    have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
    have hpow : 7 ^ (4 * 5 ^ (j + 1)) = a ^ 5 := by
      dsimp [a]; rw [← pow_mul]; congr 1; ring
    have hfac : 7 ^ (4 * 5 ^ (j + 1)) - 1 = (a - 1) * (1 + a + a ^ 2 + a ^ 3 + a ^ 4) := by
      rw [hpow, pow_sub_one_eq_mul_geom a 5 ha1]
      simp [Finset.sum_range_succ]
    -- Write a = 1 + 5^(j+2) * t = 1 + 25 * (5^j * t).
    -- Then 1 + a + a^2 + a^3 + a^4 = 5 + 10*(a-1) + 10*(a-1)^2 + 5*(a-1)^3 + (a-1)^4
    -- = 5 * (1 + 2*(a-1) + 2*(a-1)^2 + (a-1)^3 + 5^(4*j+7) * t^4) ≡ 5 (mod 25)!
    have hd25 : 25 ∣ a - 1 := by
      rw [ht]
      have : 25 ∣ 5 ^ (j + 2) := by
        rw [show (25 : ℕ) = 5 ^ 2 by decide]
        exact Nat.pow_dvd_pow 5 (by omega)
      exact dvd_mul_of_dvd_left this t
    rcases hd25 with ⟨w, hw⟩
    have ha_eq : a = 1 + 25 * w := by omega
    have hgeom : 1 + a + a ^ 2 + a ^ 3 + a ^ 4 =
        5 * (1 + 50 * w + 1250 * w ^ 2 + 15625 * w ^ 3 + 78125 * w ^ 4) := by
      rw [ha_eq]; ring
    set q := 1 + 50 * w + 1250 * w ^ 2 + 15625 * w ^ 3 + 78125 * w ^ 4
    have hq5 : ¬ 5 ∣ q := by omega
    refine ⟨t * q, ?_, ?_⟩
    · intro h5
      rcases (Nat.prime_five.dvd_mul).mp h5 with h | h
      · exact ht5 h
      · exact hq5 h
    · rw [hfac, ht, hgeom, pow_succ]
      ring

private lemma pow7_sub_one_five_adic (j m : ℕ) (hm : ¬ 5 ∣ m) :
    ∃ t : ℕ, ¬ 5 ∣ t ∧ 7 ^ (4 * 5 ^ j * m) - 1 = 5 ^ (j + 2) * t := by
  obtain ⟨t0, ht0, h0⟩ := pow7_sub_one_five_adic_pow j
  set a := 7 ^ (4 * 5 ^ j)
  have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have h5a : 5 ∣ a - 1 := by
    rw [h0]; exact dvd_mul_of_dvd_left (dvd_pow_self 5 (by omega)) t0
  have ha_mod5 : a % 5 = 1 := by omega
  have hgeom_mod5 : ∀ k, (∑ i ∈ range k, a ^ i) % 5 = k % 5 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, ha_mod5]
      simp
  have hgeom5 : ¬ 5 ∣ ∑ i ∈ range m, a ^ i := by
    intro h5
    apply hm
    have h1 : (∑ i ∈ range m, a ^ i) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [hgeom_mod5 m] at h1
    exact Nat.dvd_of_mod_eq_zero h1
  refine ⟨t0 * ∑ i ∈ range m, a ^ i, ?_, ?_⟩
  · intro h5
    rcases (Nat.prime_five.dvd_mul).mp h5 with h | h
    · exact ht0 h
    · exact hgeom5 h
  · rw [pow_mul, pow_sub_one_eq_mul_geom a m ha1, h0, mul_assoc]

private lemma gcd_pow7_sub_one_five_not_four (k n : ℕ) (hk : ¬ 4 ∣ k) :
    Nat.gcd (7 ^ k - 1) (5 ^ n) = 1 := by
  have hmod5 : 7 ^ k % 5 ≠ 1 := by
    have h74 : 7 ^ 4 % 5 = 1 := by decide
    have hdiv : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
    rw [hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h74, one_pow]
    have hr : k % 4 < 4 := Nat.mod_lt k (by decide)
    have hr0 : k % 4 ≠ 0 := fun h0 => hk (Nat.dvd_of_mod_eq_zero h0)
    interval_cases h : (k % 4)
    · exact absurd rfl hr0
    · decide
    · decide
    · decide
  have hge1 : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by omega)
  have hndvd5 : ¬ 5 ∣ 7 ^ k - 1 := by omega
  exact (Nat.Coprime.pow_right n (Nat.prime_five.coprime_iff_not_dvd.mpr hndvd5).symm).gcd_eq_one

private lemma gcd_pow7_sub_one_five_four (j m n : ℕ) (hm : ¬ 5 ∣ m) :
    Nat.gcd (7 ^ (4 * 5 ^ j * m) - 1) (5 ^ n) = 5 ^ (min n (j + 2)) := by
  obtain ⟨t, ht5, hEq⟩ := pow7_sub_one_five_adic j m hm
  rw [hEq]
  have hcop : Nat.Coprime t (5 ^ n) :=
    Nat.Coprime.pow_right n (Nat.prime_five.coprime_iff_not_dvd.mpr ht5).symm
  rw [gcd_mul_right_of_coprime hcop]
  by_cases h : n ≤ j + 2
  · rw [Nat.min_eq_left h]
    exact Nat.gcd_eq_right (Nat.pow_dvd_pow 5 h)
  · rw [Nat.min_eq_right (by omega)]
    exact Nat.gcd_eq_left (Nat.pow_dvd_pow 5 (by omega))

/-! ### Part 2: Fixed-point counting and Burnside's lemma on `ZMod (10^n)` -/

private lemma card_mul_eq_zero_zmod (N c : ℕ) [NeZero N] :
    (univ.filter (fun x : ZMod N => (c : ZMod N) * x = 0)).card = Nat.gcd c N := by
  have hN : 0 < N := NeZero.pos N
  set d := Nat.gcd c N
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right c hN
  have hd_dvd_c : d ∣ c := Nat.gcd_dvd_left c N
  have hd_dvd_N : d ∣ N := Nat.gcd_dvd_right c N
  set q := N / d
  have hN_eq : N = q * d := (Nat.div_mul_cancel hd_dvd_N).symm
  have hcop : Nat.Coprime (c / d) q := by
    exact Nat.coprime_div_gcd_div_gcd hd_pos (m := c) (n := N)
  have hiff : ∀ x : Fin N, ((c : ZMod N) * (x.val : ZMod N) = 0) ↔ q ∣ x.val := by
    intro x
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    constructor
    · intro hNdvd
      have h1 : q * d ∣ (c / d) * d * x.val := by
        rwa [← hN_eq, Nat.div_mul_cancel hd_dvd_c]
      rw [mul_assoc, mul_comm d x.val, ← mul_assoc] at h1
      have h2 : q ∣ (c / d) * x.val := (mul_dvd_mul_iff_right (by omega : d ≠ 0)).mp (by
        simpa [mul_assoc] using h1)
      exact hcop.symm.dvd_of_dvd_mul_left h2
    · rintro ⟨t, ht⟩
      refine ⟨(c / d) * t, ?_⟩
      calc
        c * x.val = (c / d * d) * (q * t) := by rw [Nat.div_mul_cancel hd_dvd_c, ht]
        _ = (q * d) * ((c / d) * t) := by ring
        _ = N * ((c / d) * t) := by rw [← hN_eq]
  -- Biject `{x : ZMod N | c * x = 0}` with `Fin d` via `t ↦ (q * t : ZMod N)`
  have hcard_fin : (univ.filter (fun x : ZMod N => (c : ZMod N) * x = 0)).card =
      (univ : Finset (Fin d)).card := by
    refine Finset.card_bij (fun x _ => ⟨x.val / q, ?_⟩) ?_ ?_ ?_
    · have hxlt : x.val < N := ZMod.val_lt x
      exact Nat.div_lt_of_lt_mul (by rw [← hN_eq]; exact hxlt)
    · intro x _; exact mem_univ _
    · intro x1 hx1 x2 hx2 hEq
      have h1 : (c : ZMod N) * (x1.val : ZMod N) = 0 := by
        simpa using (mem_filter.mp hx1).2
      have h2 : (c : ZMod N) * (x2.val : ZMod N) = 0 := by
        simpa using (mem_filter.mp hx2).2
      have hd1 : q ∣ x1.val := (hiff ⟨x1.val, ZMod.val_lt x1⟩).mp h1
      have hd2 : q ∣ x2.val := (hiff ⟨x2.val, ZMod.val_lt x2⟩).mp h2
      have hdiv : x1.val / q = x2.val / q := congrArg Fin.val hEq
      have hval : x1.val = x2.val := by
        rw [← Nat.mul_div_cancel' hd1, ← Nat.mul_div_cancel' hd2, hdiv]
      exact ZMod.val_injective N hval
    · intro t _
      have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hN hd_dvd_N) hd_pos
      have hlt : q * t.val < N := by
        rw [hN_eq]; exact Nat.mul_lt_mul_of_pos_left t.isLt hqpos
      refine ⟨((q * t.val : ℕ) : ZMod N), mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · exact (hiff ⟨q * t.val, hlt⟩).mpr ⟨t.val, rfl⟩
      · apply Fin.ext
        dsimp
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_right _ hqpos]
  simpa using hcard_fin

private lemma card_fixed_pow7 (n k : ℕ) :
    (univ.filter (fun x : ZMod (10 ^ n) => (7 : ZMod (10 ^ n)) ^ k * x = x)).card =
      Nat.gcd (7 ^ k - 1) (10 ^ n) := by
  have hge1 : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by omega)
  have hcast : ((7 ^ k - 1 : ℕ) : ZMod (10 ^ n)) = (7 : ZMod (10 ^ n)) ^ k - 1 := by
    rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
    rfl
  have hfilt : univ.filter (fun x : ZMod (10 ^ n) => (7 : ZMod (10 ^ n)) ^ k * x = x) =
      univ.filter (fun x : ZMod (10 ^ n) => ((7 ^ k - 1 : ℕ) : ZMod (10 ^ n)) * x = 0) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, hcast, sub_mul, one_mul, sub_eq_zero]
  rw [hfilt]
  exact card_mul_eq_zero_zmod (10 ^ n) (7 ^ k - 1)

/-- Period exponent `M n = 2 ^ (max 2 (n - 3)) * 5 ^ (n - 2)` satisfies `10^n ∣ 7^(M n) - 1` for `n ≥ 4`. -/
private def expA (n : ℕ) : ℕ := max 2 (n - 3)
private def expB (n : ℕ) : ℕ := n - 2
private def periodM (n : ℕ) : ℕ := 2 ^ expA n * 5 ^ expB n

private lemma periodM_pos (n : ℕ) : 0 < periodM n := by
  unfold periodM; positivity

private lemma ten_pow_dvd_pow7_periodM (n : ℕ) (hn : 4 ≤ n) :
    10 ^ n ∣ 7 ^ periodM n - 1 := by
  have h10 : (10 : ℕ) ^ n = 2 ^ n * 5 ^ n := by
    rw [show (10 : ℕ) = 2 * 5 by rfl, mul_pow]
  rw [h10]
  have hcop : Nat.Coprime (2 ^ n) (5 ^ n) := (by decide : Nat.Coprime 2 5).pow n n
  apply hcop.mul_dvd_of_dvd_of_dvd
  · -- 2^n | 7^(2^(expA n) * 5^(expB n)) - 1
    have hA : 1 ≤ expA n := by unfold expA; omega
    have hodd : Odd (5 ^ expB n) := Odd.pow ⟨2, rfl⟩
    obtain ⟨t, _, ht⟩ := pow7_sub_one_two_adic (expA n - 1) (5 ^ expB n) hodd
    have hM : 2 ^ (expA n - 1 + 1) * 5 ^ expB n = periodM n := by
      unfold periodM; congr 2; omega
    rw [hM] at ht
    rw [ht]
    have hle : n ≤ expA n - 1 + 4 := by unfold expA; omega
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hle) t
  · -- 5^n | 7^(2^(expA n) * 5^(expB n)) - 1
    have hA2 : 2 ≤ expA n := by unfold expA; omega
    have hM : periodM n = 4 * 5 ^ expB n * 2 ^ (expA n - 2) := by
      unfold periodM
      have : 2 ^ expA n = 4 * 2 ^ (expA n - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]; congr 1; omega
      rw [this]; ring
    have hnd5 : ¬ 5 ∣ 2 ^ (expA n - 2) := by
      intro h5
      have := Nat.prime_five.dvd_of_dvd_pow h5
      omega
    obtain ⟨t, _, ht⟩ := pow7_sub_one_five_adic (expB n) (2 ^ (expA n - 2)) hnd5
    rw [hM, ht]
    have hle : n ≤ expB n + 2 := by unfold expB; omega
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 5 hle) t

/-- Burnside identity: `periodM n * a n = ∑ k ∈ range (periodM n), gcd(7^k - 1, 10^n)`. -/
private lemma periodM_mul_a_eq_sum (n : ℕ) (hn : 4 ≤ n) :
    (periodM n : ℤ) * a n = ∑ k ∈ range (periodM n), (Nat.gcd (7 ^ k - 1) (10 ^ n) : ℤ) := by
  classical
  set M := periodM n
  have hMpos : 0 < M := periodM_pos n
  have : NeZero M := ⟨by omega⟩
  have : NeZero (10 ^ n) := ⟨by positivity⟩
  let : Fintype (Multiplicative (ZMod M)) := Fintype.ofEquiv (ZMod M) Multiplicative.ofAdd
  set u7 : (ZMod (10 ^ n))ˣ := ZMod.unitOfCoprime 7 ((by decide : Nat.Coprime 7 10).pow_right n)
  have hu7_powM : u7 ^ M = 1 := by
    apply Units.ext
    change (7 : ZMod (10 ^ n)) ^ M = 1
    have hge1 : 1 ≤ 7 ^ M := Nat.one_le_pow _ _ (by omega)
    have hd := ten_pow_dvd_pow7_periodM n hn
    have h0 : ((7 ^ M - 1 : ℕ) : ZMod (10 ^ n)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one] at h0
    exact sub_eq_zero.mp h0
  let φ : Multiplicative (ZMod M) →* (ZMod (10 ^ n))ˣ :=
    { toFun := fun k => u7 ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun x y => by
        change u7 ^ ((Multiplicative.toAdd x + Multiplicative.toAdd y).val) =
          u7 ^ (Multiplicative.toAdd x).val * u7 ^ (Multiplicative.toAdd y).val
        rw [← pow_add, ZMod.val_add]
        set s := (Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val
        have hdiv : s = M * (s / M) + s % M := (Nat.div_add_mod s M).symm
        conv_rhs => rw [hdiv, pow_add, pow_mul, hu7_powM, one_pow, one_mul] }
  let : MulAction (Multiplicative (ZMod M)) (ZMod (10 ^ n)) :=
    MulAction.compHom (ZMod (10 ^ n)) φ
  -- Show the orbit relations of `Subgroup.zpowers u7` and `Multiplicative (ZMod M)` coincide!
  have horb_eq : ∀ x y : ZMod (10 ^ n),
      MulAction.orbitRel (Subgroup.zpowers u7) (ZMod (10 ^ n)) x y ↔
      MulAction.orbitRel (Multiplicative (ZMod M)) (ZMod (10 ^ n)) x y := by
    intro x y
    constructor
    · rintro ⟨⟨g, hg⟩, hgx⟩
      rw [Subgroup.mem_zpowers_iff] at hg
      rcases hg with ⟨m, rfl⟩
      refine ⟨Multiplicative.ofAdd (m : ZMod M), ?_⟩
      change (u7 ^ ((m : ZMod M).val)) • y = x
      rw [← hgx]
      change (u7 ^ ((m : ZMod M).val)) • y = (u7 ^ m) • y
      congr 1
      have hmod : (m : ℤ) ≡ ((m : ZMod M).val : ℤ) [ZMOD (M : ℤ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        simp
      obtain ⟨q, hq⟩ := Int.ModEq.symm hmod |>.dvd
      have hm_eq : m = ((m : ZMod M).val : ℤ) + (M : ℤ) * q := by linarith
      conv_rhs => rw [hm_eq]
      rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, hu7_powM, one_zpow, mul_one]
    · rintro ⟨k, hkx⟩
      exact ⟨⟨u7 ^ (Multiplicative.toAdd k).val, Subgroup.npow_mem_zpowers u7 _⟩, hkx⟩
  -- Hence the orbit quotients have the same cardinality!
  have hquot_equiv :
      MulAction.orbitRel.Quotient (Subgroup.zpowers u7) (ZMod (10 ^ n)) ≃
      MulAction.orbitRel.Quotient (Multiplicative (ZMod M)) (ZMod (10 ^ n)) :=
    Quotient.congr (Equiv.refl _) (fun x y => horb_eq x y)
  have ha_nat : a n = (Fintype.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod M)) (ZMod (10 ^ n))) : ℤ) := by
    unfold a
    rw [Nat.card_congr hquot_equiv, Nat.card_eq_fintype_card]
  -- Apply Burnside's lemma!
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod M)) (ZMod (10 ^ n))
  have hcardG : Fintype.card (Multiplicative (ZMod M)) = M := by
    rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  rw [hcardG] at hburn
  -- Rewrite the LHS sum over `Multiplicative (ZMod M)` as sum over `k ∈ range M`!
  have hsum_eq :
      (∑ k : Multiplicative (ZMod M), Fintype.card (MulAction.fixedBy (ZMod (10 ^ n)) k)) =
      ∑ k ∈ range M, Nat.gcd (7 ^ k - 1) (10 ^ n) := by
    have heq : (∑ k : Multiplicative (ZMod M), Fintype.card (MulAction.fixedBy (ZMod (10 ^ n)) k)) =
        ∑ k : Fin M, Nat.gcd (7 ^ k.val - 1) (10 ^ n) := by
      let e : Multiplicative (ZMod M) ≃ Fin M :=
        { toFun := fun k => ⟨(Multiplicative.toAdd k).val, ZMod.val_lt _⟩
          invFun := fun i => Multiplicative.ofAdd (i.val : ZMod M)
          left_inv := fun k => by simp
          right_inv := fun i => by
            apply Fin.ext
            simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] }
      refine Fintype.sum_equiv e _ _ (fun k => ?_)
      have hfix : Fintype.card (MulAction.fixedBy (ZMod (10 ^ n)) k) =
          (univ.filter (fun x : ZMod (10 ^ n) => (7 : ZMod (10 ^ n)) ^ (Multiplicative.toAdd k).val * x = x)).card := by
        rw [Fintype.card_subtype]
        apply congrArg Finset.card
        ext x
        simp only [mem_filter, mem_univ, true_and, MulAction.mem_fixedBy]
        change ((u7 ^ (Multiplicative.toAdd k).val : (ZMod (10 ^ n))ˣ) : ZMod (10 ^ n)) * x = x ↔ _
        simp [u7]
      rw [hfix, card_fixed_pow7]
      rfl
    rw [heq, Fin.sum_univ_eq_sum_range (fun k => Nat.gcd (7 ^ k - 1) (10 ^ n)) M]
  rw [ha_nat]
  have hnat : M * Fintype.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod M)) (ZMod (10 ^ n))) =
      ∑ k ∈ range M, Nat.gcd (7 ^ k - 1) (10 ^ n) := by
    linarith [hburn, hsum_eq]
  exact_mod_cast hnat

/-! ### Part 3: Exact evaluation of the Burnside sum via CRT -/

/-- Exact 2-adic gcd for `k ∈ range (2^A)` when `n ≥ 4`, `A = expA n`. -/
private def g2 (n k : ℕ) : ℕ := Nat.gcd (7 ^ k - 1) (2 ^ n)
private def g5 (n k : ℕ) : ℕ := Nat.gcd (7 ^ k - 1) (5 ^ n)

private lemma gcd_ten_split (n k : ℕ) :
    Nat.gcd (7 ^ k - 1) (10 ^ n) = g2 n k * g5 n k := by
  have h10 : (10 : ℕ) ^ n = 2 ^ n * 5 ^ n := by
    rw [show (10 : ℕ) = 2 * 5 by rfl, mul_pow]
  rw [h10, g2, g5]
  set m := 7 ^ k - 1
  have hcop : Nat.Coprime (2 ^ n) (5 ^ n) := (by decide : Nat.Coprime 2 5).pow n n
  apply Nat.dvd_antisymm
  · obtain ⟨d1, d2, hd1, hd2, hEq⟩ := Nat.dvd_mul.mp (Nat.gcd_dvd_right m (2 ^ n * 5 ^ n))
    have hdm : d1 * d2 ∣ m := hEq ▸ Nat.gcd_dvd_left m (2 ^ n * 5 ^ n)
    rw [← hEq]
    exact mul_dvd_mul
      (Nat.dvd_gcd (dvd_trans (dvd_mul_right d1 d2) hdm) hd1)
      (Nat.dvd_gcd (dvd_trans (dvd_mul_left d2 d1) hdm) hd2)
  · have hcop_g : Nat.Coprime (Nat.gcd m (2 ^ n)) (Nat.gcd m (5 ^ n)) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right m (2 ^ n))).coprime_dvd_right
        (Nat.gcd_dvd_right m (5 ^ n))
    exact Nat.dvd_gcd
      (hcop_g.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left m (2 ^ n)) (Nat.gcd_dvd_left m (5 ^ n)))
      (mul_dvd_mul (Nat.gcd_dvd_right m (2 ^ n)) (Nat.gcd_dvd_right m (5 ^ n)))

/-- Periodicity of `g2 n` modulo `2 ^ expA n` for `n ≥ 4`. -/
private lemma g2_periodic (n k q : ℕ) (hn : 4 ≤ n) :
    g2 n (k + 2 ^ expA n * q) = g2 n k := by
  unfold g2
  have hge1 : 1 ≤ 7 ^ (2 ^ expA n * q) := Nat.one_le_pow _ _ (by omega)
  have hge2 : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by omega)
  have hdvd : 2 ^ n ∣ 7 ^ (2 ^ expA n * q) - 1 := by
    have hA : 1 ≤ expA n := by unfold expA; omega
    obtain ⟨t, _, ht⟩ := pow7_sub_one_two_adic_pow (expA n - 1)
    have h1 : 2 ^ (expA n - 1 + 1) = 2 ^ expA n := by congr 1; omega
    rw [h1] at ht
    have h2 : 2 ^ n ∣ 7 ^ (2 ^ expA n) - 1 := by
      rw [ht]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by unfold expA; omega)) t
    rw [pow_mul, pow_sub_one_eq_mul_geom _ q (Nat.one_le_pow _ _ (by omega))]
    exact dvd_mul_of_dvd_left h2 _
  have hmod : (7 ^ (k + 2 ^ expA n * q) - 1) % (2 ^ n) = (7 ^ k - 1) % (2 ^ n) := by
    have h7 : 7 ^ (k + 2 ^ expA n * q) - 1 =
        (7 ^ k - 1) + 7 ^ k * (7 ^ (2 ^ expA n * q) - 1) := by
      rw [pow_add]
      zify [hge1, hge2, show 1 ≤ 7 ^ k * 7 ^ (2 ^ expA n * q) by nlinarith]
      ring
    rw [h7, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdvd, mul_zero, Nat.zero_mod,
      add_zero, Nat.mod_mod]
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]

/-- Periodicity of `g5 n` modulo `4 * 5 ^ expB n` for `n ≥ 4`. -/
private lemma g5_periodic (n k q : ℕ) (hn : 4 ≤ n) :
    g5 n (k + 4 * 5 ^ expB n * q) = g5 n k := by
  unfold g5
  have hge1 : 1 ≤ 7 ^ (4 * 5 ^ expB n * q) := Nat.one_le_pow _ _ (by omega)
  have hge2 : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by omega)
  have hdvd : 5 ^ n ∣ 7 ^ (4 * 5 ^ expB n * q) - 1 := by
    obtain ⟨t, _, ht⟩ := pow7_sub_one_five_adic_pow (expB n)
    have h2 : 5 ^ n ∣ 7 ^ (4 * 5 ^ expB n) - 1 := by
      rw [ht]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 5 (by unfold expB; omega)) t
    rw [pow_mul, pow_sub_one_eq_mul_geom _ q (Nat.one_le_pow _ _ (by omega))]
    exact dvd_mul_of_dvd_left h2 _
  have hmod : (7 ^ (k + 4 * 5 ^ expB n * q) - 1) % (5 ^ n) = (7 ^ k - 1) % (5 ^ n) := by
    have h7 : 7 ^ (k + 4 * 5 ^ expB n * q) - 1 =
        (7 ^ k - 1) + 7 ^ k * (7 ^ (4 * 5 ^ expB n * q) - 1) := by
      rw [pow_add]
      zify [hge1, hge2, show 1 ≤ 7 ^ k * 7 ^ (4 * 5 ^ expB n * q) by nlinarith]
      ring
    rw [h7, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdvd, mul_zero, Nat.zero_mod,
      add_zero, Nat.mod_mod]
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]

private lemma g2_mod_eq {n k1 k2 : ℕ} (hn : 4 ≤ n) (h : k1 % 2 ^ expA n = k2 % 2 ^ expA n) :
    g2 n k1 = g2 n k2 := by
  have h1 : g2 n k1 = g2 n (k1 % 2 ^ expA n) := by
    conv_lhs => rw [← Nat.mod_add_div k1 (2 ^ expA n)]
    exact g2_periodic n _ _ hn
  have h2 : g2 n k2 = g2 n (k2 % 2 ^ expA n) := by
    conv_lhs => rw [← Nat.mod_add_div k2 (2 ^ expA n)]
    exact g2_periodic n _ _ hn
  rw [h1, h2, h]

private lemma g5_mod_eq {n k1 k2 : ℕ} (hn : 4 ≤ n)
    (h : k1 % (4 * 5 ^ expB n) = k2 % (4 * 5 ^ expB n)) :
    g5 n k1 = g5 n k2 := by
  have h1 : g5 n k1 = g5 n (k1 % (4 * 5 ^ expB n)) := by
    conv_lhs => rw [← Nat.mod_add_div k1 (4 * 5 ^ expB n)]
    exact g5_periodic n _ _ hn
  have h2 : g5 n k2 = g5 n (k2 % (4 * 5 ^ expB n)) := by
    conv_lhs => rw [← Nat.mod_add_div k2 (4 * 5 ^ expB n)]
    exact g5_periodic n _ _ hn
  rw [h1, h2, h]

/-- Sum of `g2 n (4 * t)` over `t ∈ range (2 ^ (expA n - 2))` equals `4 * (n - 3) * 2 ^ expA n` for `n ≥ 4`. -/
private lemma sum_g2_mul_four (n : ℕ) (hn : 4 ≤ n) :
    ∑ t ∈ range (2 ^ (expA n - 2)), g2 n (4 * t) = 4 * (n - 3) * 2 ^ expA n := by
  by_cases h4 : n = 4
  · subst h4
    have : expA 4 = 2 := by decide
    simp [this, g2]
  · have hn5 : 5 ≤ n := by omega
    have hA : expA n = n - 3 := by unfold expA; omega
    -- Prove by induction on m = n - 5 that ∑_{t < 2^m} g2 n (4 * t) = 4 * (n - 3) * 2^(n-3)
    -- More generally, prove for any m ≤ n - 5:
    -- ∑_{t < 2^m} gcd(7^(4*t) - 1, 2^n) = 2^n + m * 2^(n-1) -- wait, at m = n - 5:
    -- 2^n + (n - 5) * 2^(n-1) = (n - 3) * 2^(n-1) = 4 * (n - 3) * 2^(n-3)!
    -- Actually prove for ANY s ≤ n - 5 and ANY c with `s + c = n - 5`? Even simpler:
    -- For ANY m : ℕ with `m + 5 ≤ n`:
    -- ∑_{t ∈ range (2^m)} g2 n (2^(n - 3 - m) * t) = (m + 2) * 2^(n - 1)!
    -- Wait: let's prove by induction on `m` that for all `d ≥ 2` with `d + m + 3 = n`:
    -- `∑ t ∈ range (2^m), g2 n (2^d * t) = 2^n + m * 2^(n - 1)`!
    have hgen : ∀ m d : ℕ, 2 ≤ d → d + m + 3 = n →
        ∑ t ∈ range (2 ^ m), g2 n (2 ^ d * t) = 2 ^ n + m * 2 ^ (n - 1) := by
      intro m
      induction m with
      | zero =>
        intro d _ _
        simp [g2]
      | succ m ih =>
        intro d hd hsum
        -- Split `range (2^(m+1))` into even `2*u` and odd `2*u + 1` (`u ∈ range (2^m)`)!
        have hsplit' : ∑ t ∈ range (2 ^ (m + 1)), g2 n (2 ^ d * t) =
            ∑ u ∈ range (2 ^ m), (g2 n (2 ^ d * (2 * u)) + g2 n (2 ^ d * (2 * u + 1))) := by
          have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
          rw [h2]
          -- Induction on N = 2^m
          generalize (2 ^ m) = N
          induction N with
          | zero => simp
          | succ N ihN =>
            rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, ihN]
            ring
        rw [hsplit', sum_add_distrib]
        have heven : ∑ u ∈ range (2 ^ m), g2 n (2 ^ d * (2 * u)) =
            2 ^ n + m * 2 ^ (n - 1) := by
          have hrew : ∀ u, 2 ^ d * (2 * u) = 2 ^ (d + 1) * u := fun u => by rw [pow_succ]; ring
          simp_rw [hrew]
          exact ih (d + 1) (by omega) (by omega)
        have hodd : ∀ u ∈ range (2 ^ m), g2 n (2 ^ d * (2 * u + 1)) = 2 ^ (d + 3) := by
          intro u _
          unfold g2
          have hd1 : d = (d - 1) + 1 := by omega
          conv_lhs => rw [hd1]
          rw [gcd_pow7_sub_one_two_even (d - 1) (2 * u + 1) n ⟨u, rfl⟩]
          congr 1
          omega
        rw [heven, sum_congr rfl hodd, sum_const, card_range, smul_eq_mul]
        have hpow : 2 ^ m * 2 ^ (d + 3) = 2 ^ (n - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [hpow]
        ring
    have hres := hgen (n - 5) 2 (le_refl 2) (by omega)
    rw [hA]
    have h4eq : (4 : ℕ) = 2 ^ 2 := by decide
    have hsub : n - 3 - 2 = n - 5 := by omega
    rw [hsub, h4eq, hres]
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm]
    have h2n1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]; congr 1; omega
    rw [h2n, h2n1]
    have : n - 5 + 2 = n - 3 := by omega
    calc
      2 * (4 * 2 ^ (n - 3)) + (n - 5) * (4 * 2 ^ (n - 3))
          = (n - 5 + 2) * (4 * 2 ^ (n - 3)) := by ring
      _ = 4 * (n - 3) * 2 ^ (n - 3) := by rw [this]; ring

/-- Sum of `g5 n (4 * k)` over `k ∈ range (5 ^ expB n)` equals `5 * (4 * n - 3) * 5 ^ expB n` for `n ≥ 4`. -/
private lemma sum_g5_mul_four (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ range (5 ^ expB n), g5 n (4 * k) = 5 * (4 * n - 3) * 5 ^ expB n := by
  have hB : expB n = n - 2 := rfl
  -- Prove by induction on `m` that for all `d` with `d + m + 2 = n`:
  -- `∑ k ∈ range (5^m), g5 n (4 * 5^d * k) = 5^n + 4 * m * 5^(n - 1)`!
  have hgen : ∀ m d : ℕ, d + m + 2 = n →
      ∑ k ∈ range (5 ^ m), g5 n (4 * 5 ^ d * k) = 5 ^ n + 4 * m * 5 ^ (n - 1) := by
    intro m
    induction m with
    | zero =>
      intro d _
      simp [g5]
    | succ m ih =>
      intro d hsum
      have hsplit : ∑ k ∈ range (5 ^ (m + 1)), g5 n (4 * 5 ^ d * k) =
          ∑ u ∈ range (5 ^ m),
            (g5 n (4 * 5 ^ d * (5 * u)) +
             g5 n (4 * 5 ^ d * (5 * u + 1)) +
             g5 n (4 * 5 ^ d * (5 * u + 2)) +
             g5 n (4 * 5 ^ d * (5 * u + 3)) +
             g5 n (4 * 5 ^ d * (5 * u + 4))) := by
        have h5 : 5 ^ (m + 1) = 5 * 5 ^ m := by rw [pow_succ, mul_comm]
        rw [h5]
        generalize (5 ^ m) = N
        induction N with
        | zero => simp
        | succ N ihN =>
          rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ,
            sum_range_succ, sum_range_succ, sum_range_succ, ihN]
          ring
      rw [hsplit, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib]
      have h0 : ∑ u ∈ range (5 ^ m), g5 n (4 * 5 ^ d * (5 * u)) = 5 ^ n + 4 * m * 5 ^ (n - 1) := by
        have hrew : ∀ u, 4 * 5 ^ d * (5 * u) = 4 * 5 ^ (d + 1) * u := fun u => by rw [pow_succ]; ring
        simp_rw [hrew]
        exact ih (d + 1) (by omega)
      have hrem : ∀ r ∈ ({1, 2, 3, 4} : Finset ℕ),
          ∀ u ∈ range (5 ^ m), g5 n (4 * 5 ^ d * (5 * u + r)) = 5 ^ (d + 2) := by
        intro r hr u _
        unfold g5
        have hnd5 : ¬ 5 ∣ (5 * u + r) := by
          simp at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega
        rw [gcd_pow7_sub_one_five_four d (5 * u + r) n hnd5]
        congr 1; omega
      rw [h0,
        sum_congr rfl (hrem 1 (by simp)), sum_congr rfl (hrem 2 (by simp)),
        sum_congr rfl (hrem 3 (by simp)), sum_congr rfl (hrem 4 (by simp)),
        sum_const, card_range, smul_eq_mul]
      have hpow : 5 ^ m * 5 ^ (d + 2) = 5 ^ (n - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      ring
  have hres := hgen (n - 2) 0 (by omega)
  rw [hB]
  simp only [pow_zero, mul_one] at hres
  rw [hres]
  have h5n : 5 ^ n = 5 * 5 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm]
  have h5n1 : 5 ^ (n - 1) = 5 * 5 ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, mul_comm]
  rw [h5n, h5n1]
  have hcoef : 5 + 4 * (n - 2) = 4 * n - 3 := by omega
  calc
    5 * (5 * 5 ^ (n - 2)) + 4 * (n - 2) * (5 * 5 ^ (n - 2))
        = (5 + 4 * (n - 2)) * (5 * 5 ^ (n - 2)) := by ring
    _ = 5 * (4 * n - 3) * 5 ^ (n - 2) := by rw [hcoef]; ring

/-- Sum of `g2 n k` over `k ∈ range (2 ^ expA n)` with `¬ 4 ∣ k` equals `5 * 2 ^ expA n` for `n ≥ 4`. -/
private lemma sum_g2_not_four (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ (range (2 ^ expA n)).filter (fun k => ¬ 4 ∣ k), g2 n k = 5 * 2 ^ expA n := by
  have hA2 : 2 ≤ expA n := by unfold expA; omega
  have hpow : 2 ^ expA n = 4 * 2 ^ (expA n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]; congr 1; omega
  have hsum_mod4 : ∀ N : ℕ,
      ∑ k ∈ (range (4 * N)).filter (fun k => ¬ 4 ∣ k), g2 n k =
      ∑ u ∈ range N, (g2 n (4 * u + 1) + g2 n (4 * u + 2) + g2 n (4 * u + 3)) := by
    intro N
    rw [sum_filter]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
        ih, sum_range_succ]
      have h0 : 4 ∣ 4 * N := dvd_mul_right 4 N
      have h1 : ¬ 4 ∣ 4 * N + 1 := by omega
      have h2 : ¬ 4 ∣ 4 * N + 2 := by omega
      have h3 : ¬ 4 ∣ 4 * N + 3 := by omega
      simp [h0, h1, h2, h3]
      ring
  rw [hpow, hsum_mod4]
  have hterm : ∀ u ∈ range (2 ^ (expA n - 2)),
      g2 n (4 * u + 1) + g2 n (4 * u + 2) + g2 n (4 * u + 3) = 20 := by
    intro u _
    have h1 : g2 n (4 * u + 1) = 2 := by
      unfold g2
      exact gcd_pow7_sub_one_two_odd (4 * u + 1) n ⟨2 * u, by ring⟩ (by omega)
    have h2 : g2 n (4 * u + 2) = 16 := by
      unfold g2
      have heq : 4 * u + 2 = 2 ^ (0 + 1) * (2 * u + 1) := by ring
      rw [heq, gcd_pow7_sub_one_two_even 0 (2 * u + 1) n ⟨u, rfl⟩]
      have hmin : min n (0 + 4) = 4 := by omega
      rw [hmin]
      decide
    have h3 : g2 n (4 * u + 3) = 2 := by
      unfold g2
      exact gcd_pow7_sub_one_two_odd (4 * u + 3) n ⟨2 * u + 1, by ring⟩ (by omega)
    rw [h1, h2, h3]
  rw [sum_congr rfl hterm, sum_const, card_range, smul_eq_mul]
  ring

/-- Sum of a `P`-periodic function over `range (P * N)` equals `N` times its sum over `range P`. -/
private lemma sum_range_mul_periodic (P N : ℕ) (f : ℕ → ℕ) (hf : ∀ k, f (k + P) = f k) :
    ∑ k ∈ range (P * N), f k = N * ∑ a ∈ range P, f a := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    have hshift : ∀ a ∈ range P, f (P * N + a) = f a := by
      intro a _
      clear ih
      induction N with
      | zero => simp
      | succ M ihM =>
        rw [Nat.mul_succ, add_assoc, add_comm P a, ← add_assoc, hf, ihM]
    rw [sum_congr rfl hshift]
    ring

/-- Sum over multiples of 4 in `range (4 * L)`. -/
private lemma sum_filter_four_dvd (L : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ (range (4 * L)).filter (fun k => 4 ∣ k), f k = ∑ m ∈ range L, f (4 * m) := by
  rw [sum_filter]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    have h0 : 4 ∣ 4 * L := dvd_mul_right 4 L
    have h1 : ¬ 4 ∣ 4 * L + 1 := by omega
    have h2 : ¬ 4 ∣ 4 * L + 2 := by omega
    have h3 : ¬ 4 ∣ 4 * L + 3 := by omega
    simp [h0, h1, h2, h3]

/-- Elementary CRT factorization of a product sum over `range (P * Q)` for coprime `P, Q`. -/
private lemma sum_range_mul_coprime (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hcop : Nat.Coprime P Q) (f g : ℕ → ℕ)
    (hf : ∀ m, f m = f (m % P)) (hg : ∀ m, g m = g (m % Q)) :
    ∑ m ∈ range (P * Q), f m * g m = (∑ a ∈ range P, f a) * (∑ b ∈ range Q, g b) := by
  let φ : ℕ → ℕ × ℕ := fun m => (m % P, m % Q)
  have hinj : Set.InjOn φ (range (P * Q) : Set ℕ) := by
    intro x hx y hy hEq
    have hxlt : x < P * Q := mem_range.mp hx
    have hylt : y < P * Q := mem_range.mp hy
    have hPeq : x % P = y % P := congrArg Prod.fst hEq
    have hQeq : x % Q = y % Q := congrArg Prod.snd hEq
    have hle_eq : ∀ u v : ℕ, u ≤ v → v < P * Q → u % P = v % P → u % Q = v % Q → u = v := by
      intro u v huv hvlt huP huQ
      have hdP : P ∣ v - u := by
        have h1 : v = P * (v / P) + v % P := (Nat.div_add_mod v P).symm
        have h2 : u = P * (u / P) + u % P := (Nat.div_add_mod u P).symm
        have hdiv : u / P ≤ v / P := Nat.div_le_div_right huv
        refine ⟨v / P - u / P, ?_⟩
        rw [Nat.mul_sub]
        omega
      have hdQ : Q ∣ v - u := by
        have h1 : v = Q * (v / Q) + v % Q := (Nat.div_add_mod v Q).symm
        have h2 : u = Q * (u / Q) + u % Q := (Nat.div_add_mod u Q).symm
        have hdiv : u / Q ≤ v / Q := Nat.div_le_div_right huv
        refine ⟨v / Q - u / Q, ?_⟩
        rw [Nat.mul_sub]
        omega
      have hdPQ : P * Q ∣ v - u := hcop.mul_dvd_of_dvd_of_dvd hdP hdQ
      have hsub_lt : v - u < P * Q := by omega
      have hzero : v - u = 0 := Nat.eq_zero_of_dvd_of_lt hdPQ hsub_lt
      omega
    rcases le_total x y with hxy | hyx
    · exact hle_eq x y hxy hylt hPeq hQeq
    · exact (hle_eq y x hyx hxlt hPeq.symm hQeq.symm).symm
  have hsub : (range (P * Q)).image φ ⊆ range P ×ˢ range Q := by
    intro p hp
    rcases mem_image.mp hp with ⟨m, _, rfl⟩
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt m hP), mem_range.mpr (Nat.mod_lt m hQ)⟩
  have hcard : (range P ×ˢ range Q).card ≤ ((range (P * Q)).image φ).card := by
    rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range]
  have himg : (range (P * Q)).image φ = range P ×ˢ range Q :=
    eq_of_subset_of_card_le hsub hcard
  rw [Finset.sum_mul_sum, ← Finset.sum_product' (s := range P) (t := range Q) (f := fun a b => f a * g b),
    ← himg, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp [φ]
  rw [← hf m, ← hg m]

/-- Exact evaluation of the Burnside sum for `n ≥ 4`. -/
private lemma sum_gcd_ten_eq (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ range (periodM n), Nat.gcd (7 ^ k - 1) (10 ^ n) =
      (5 + 20 * (n - 3) * (4 * n - 3)) * periodM n := by
  have hA2 : 2 ≤ expA n := by unfold expA; omega
  have h4A : 4 ∣ 2 ^ expA n := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide]
    exact Nat.pow_dvd_pow 2 hA2
  have hA_split : 2 ^ expA n = 4 * 2 ^ (expA n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]; congr 1; omega
  simp_rw [gcd_ten_split]
  rw [← Finset.sum_filter_add_sum_filter_not (range (periodM n)) (fun k => 4 ∣ k)]
  -- Part 1: `¬ 4 ∣ k`, where `g5 n k = 1`
  have hpart_not4 :
      ∑ k ∈ (range (periodM n)).filter (fun k => ¬ 4 ∣ k), g2 n k * g5 n k =
      5 * periodM n := by
    have hg5_one : ∀ k ∈ (range (periodM n)).filter (fun k => ¬ 4 ∣ k),
        g2 n k * g5 n k = g2 n k := by
      intro k hk
      have hnd4 : ¬ 4 ∣ k := (mem_filter.mp hk).2
      rw [g5, gcd_pow7_sub_one_five_not_four k n hnd4, mul_one]
    rw [sum_congr rfl hg5_one, sum_filter]
    have hper : ∀ k, (if ¬ 4 ∣ k + 2 ^ expA n then g2 n (k + 2 ^ expA n) else 0) =
        (if ¬ 4 ∣ k then g2 n k else 0) := by
      intro k
      have h4iff : (4 ∣ k + 2 ^ expA n) ↔ (4 ∣ k) := Nat.dvd_add_left h4A
      have hg2 : g2 n (k + 2 ^ expA n) = g2 n k := by
        simpa using g2_periodic n k 1 hn
      simp [h4iff, hg2]
    unfold periodM
    rw [sum_range_mul_periodic (2 ^ expA n) (5 ^ expB n) _ hper, ← sum_filter,
      sum_g2_not_four n hn]
    ring
  -- Part 2: `4 ∣ k`, write `k = 4 * m` and factor via CRT
  have hpart_4 :
      ∑ k ∈ (range (periodM n)).filter (fun k => 4 ∣ k), g2 n k * g5 n k =
      20 * (n - 3) * (4 * n - 3) * periodM n := by
    have hM4 : periodM n = 4 * (2 ^ (expA n - 2) * 5 ^ expB n) := by
      unfold periodM; rw [hA_split]; ring
    rw [hM4, sum_filter_four_dvd]
    have hcop : Nat.Coprime (2 ^ (expA n - 2)) (5 ^ expB n) :=
      (by decide : Nat.Coprime 2 5).pow _ _
    have hf : ∀ m, g2 n (4 * m) = g2 n (4 * (m % 2 ^ (expA n - 2))) := by
      intro m
      apply g2_mod_eq hn
      have h1 : (4 * m) % (4 * 2 ^ (expA n - 2)) = 4 * (m % 2 ^ (expA n - 2)) :=
        Nat.mul_mod_mul_left 4 m (2 ^ (expA n - 2))
      have h2 : (4 * (m % 2 ^ (expA n - 2))) % (4 * 2 ^ (expA n - 2)) =
          4 * (m % 2 ^ (expA n - 2)) :=
        Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m (by positivity)) (by decide))
      rw [hA_split, h1, h2]
    have hg : ∀ m, g5 n (4 * m) = g5 n (4 * (m % 5 ^ expB n)) := by
      intro m
      apply g5_mod_eq hn
      have h1 : (4 * m) % (4 * 5 ^ expB n) = 4 * (m % 5 ^ expB n) :=
        Nat.mul_mod_mul_left 4 m (5 ^ expB n)
      have h2 : (4 * (m % 5 ^ expB n)) % (4 * 5 ^ expB n) =
          4 * (m % 5 ^ expB n) :=
        Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m (by positivity)) (by decide))
      rw [h1, h2]
    rw [sum_range_mul_coprime (2 ^ (expA n - 2)) (5 ^ expB n) (by positivity) (by positivity)
      hcop (fun m => g2 n (4 * m)) (fun m => g5 n (4 * m)) hf hg,
      sum_g2_mul_four n hn, sum_g5_mul_four n hn, hA_split]
    ring
  rw [hpart_4, hpart_not4]
  ring

private lemma a_formula (n : ℕ) (hn : 3 < n) :
    a n = 5 * (16 * (n : ℤ) ^ 2 - 60 * n + 37) := by
  have hn4 : 4 ≤ n := by omega
  have hburn := periodM_mul_a_eq_sum n hn4
  have hsum := sum_gcd_ten_eq n hn4
  have hsumZ : ∑ k ∈ range (periodM n), (Nat.gcd (7 ^ k - 1) (10 ^ n) : ℤ) =
      ((5 + 20 * (n - 3) * (4 * n - 3)) * periodM n : ℕ) := by
    rw [← hsum]
    push_cast
    rfl
  rw [hsumZ] at hburn
  have hcoef : ((5 + 20 * (n - 3) * (4 * n - 3) : ℕ) : ℤ) =
      5 * (16 * (n : ℤ) ^ 2 - 60 * n + 37) := by
    have hsub1 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    have hsub2 : ((4 * n - 3 : ℕ) : ℤ) = 4 * (n : ℤ) - 3 := by omega
    push_cast
    rw [hsub1, hsub2]
    ring
  have hEq : (periodM n : ℤ) * a n = (periodM n : ℤ) * (5 * (16 * (n : ℤ) ^ 2 - 60 * n + 37)) := by
    rw [hburn, Nat.cast_mul, hcoef, mul_comm]
  have hMne : (periodM n : ℤ) ≠ 0 := by
    exact_mod_cast (periodM_pos n).ne'
  exact mul_left_cancel₀ hMne hEq

private lemma a_rec (n : ℕ) (hn : 6 < n) :
    a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [a_formula n (by omega), a_formula (n - 1) (by omega),
    a_formula (n - 2) (by omega), a_formula (n - 3) (by omega)]
  have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have h2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have h3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  rw [h1, h2, h3]
  ring

end OMA_A220019

theorem OMA.solution : type_of% @OMA.S_oeis_a220019.main :=
  ⟨OMA_A220019.a_formula, OMA_A220019.a_rec⟩
