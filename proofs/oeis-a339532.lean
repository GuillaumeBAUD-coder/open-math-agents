import OMAStatements.S_oeis_a339532
import Mathlib

/-!
Proof of Chai Wah Wu's conjectures on A339532. The property depends only on `b mod 900`
(via `b mod 4`, `b mod 9`, `b mod 25`) and holds for exactly eight residues
(1, 449, 557, 593, 649, 701, 757, 793), so every window of 900 consecutive integers contains
exactly eight values with the property. With `Nat.count_add` and `Nat.nth_count` this gives
`a(n+8) = a(n) + 900`, hence the recurrence; the generating function follows by comparing
coefficients, using `a(1..9)`.
-/

namespace A339532Proof

open OMA.S_oeis_a339532

instance : DecidablePred Q := fun b => by unfold Q Wieferich Nat.ModEq; infer_instance
instance : DecidablePred P := fun b => by unfold P; infer_instance

lemma Q_mod (b : ℕ) : Q b ↔ Q (b % 900) := by
  have key : ∀ k m, m ∣ 900 → (b % 900) ^ k % m = b ^ k % m := fun k m hm => by
    rw [Nat.pow_mod, Nat.mod_mod_of_dvd b hm, ← Nat.pow_mod]
  change (b ^ 1 % 4 = 1 % 4 ∧ b ^ 2 % 9 = 1 % 9 ∧ b ^ 4 % 25 = 1 % 25) ↔
    ((b % 900) ^ 1 % 4 = 1 % 4 ∧ (b % 900) ^ 2 % 9 = 1 % 9 ∧ (b % 900) ^ 4 % 25 = 1 % 25)
  rw [key 1 4 (by norm_num), key 2 9 (by norm_num), key 4 25 (by norm_num)]

lemma Q_add (b : ℕ) : Q (b + 900) ↔ Q b := by
  rw [Q_mod, Q_mod b]; simp

set_option maxRecDepth 100000 in
lemma window0 : Nat.count Q 900 = 8 := by decide

lemma count_eq_sum (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    Nat.count p n = ∑ k ∈ Finset.range n, if p k then 1 else 0 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_filter]

lemma window (x : ℕ) : (∑ k ∈ Finset.range 900, if Q (x + k) then 1 else 0) = 8 := by
  induction x with
  | zero => rw [← window0, count_eq_sum]; simp only [zero_add]
  | succ x ih =>
    have h1 := Finset.sum_range_succ (fun k => if Q (x + k) then 1 else 0) 900
    have h2 := Finset.sum_range_succ' (fun k => if Q (x + k) then 1 else 0) 900
    beta_reduce at h1 h2
    have h3 : (∑ k ∈ Finset.range 900, if Q (x + (k + 1)) then 1 else 0) =
        ∑ k ∈ Finset.range 900, if Q (x + 1 + k) then 1 else 0 :=
      Finset.sum_congr rfl (fun k _ => by rw [show x + (k + 1) = x + 1 + k by ring])
    rw [h3, add_zero] at h2
    rw [ih] at h1
    have hq : Q (x + 900) ↔ Q x := Q_add x
    by_cases hx : Q x
    · have : Q (x + 900) := hq.mpr hx
      rw [if_pos this] at h1; rw [if_pos hx] at h2; omega
    · have : ¬ Q (x + 900) := fun h => hx (hq.mp h)
      rw [if_neg this] at h1; rw [if_neg hx] at h2; omega

lemma P_infinite : {b | P b}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  have h : P (900 * (M + 1) + 1) := by
    refine ⟨by omega, ?_⟩
    rw [Q_mod]; simp [Nat.add_mod]; decide
  have := hM h
  simp at this; omega

lemma shift (m : ℕ) : Nat.nth P (m + 8) = Nat.nth P m + 900 := by
  set x := Nat.nth P m with hx
  have hPx : P x := Nat.nth_mem_of_infinite P_infinite m
  have hPx' : P (x + 900) := ⟨by have := hPx.1; omega, (Q_add x).mpr hPx.2⟩
  have hc : Nat.count P x = m := Nat.count_nth_of_infinite P_infinite m
  have hcount : Nat.count P (x + 900) = m + 8 := by
    rw [Nat.count_add, hc, count_eq_sum]
    have : (∑ k ∈ Finset.range 900, if P (x + k) then 1 else 0) =
        ∑ k ∈ Finset.range 900, if Q (x + k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      have h1 : 1 < x + k := by have := hPx.1; omega
      simp [P, h1]
    rw [this, window]
  rw [← hcount, Nat.nth_count hPx']
set_option maxRecDepth 100000 in
lemma vals : Nat.nth P 0 = 449 ∧ Nat.nth P 1 = 557 ∧ Nat.nth P 2 = 593 ∧ Nat.nth P 3 = 649 ∧
    Nat.nth P 4 = 701 ∧ Nat.nth P 5 = 757 ∧ Nat.nth P 6 = 793 ∧ Nat.nth P 7 = 901 := by
  have hv : ∀ v k, P v → Nat.count P v = k → Nat.nth P k = v := fun v k hP hc => by
    rw [← hc, Nat.nth_count hP]
  refine ⟨hv _ _ (by decide) (by decide), hv _ _ (by decide) (by decide),
    hv _ _ (by decide) (by decide), hv _ _ (by decide) (by decide),
    hv _ _ (by decide) (by decide), hv _ _ (by decide) (by decide),
    hv _ _ (by decide) (by decide), hv _ _ (by decide) (by decide)⟩

lemma rec_part : ∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 1) + a (n - 8) - a (n - 9) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  unfold a
  rw [show m + 10 - 1 - 1 = m + 8 by omega, show m + 10 - 1 = (m + 1) + 8 by omega,
    show m + 10 - 8 - 1 = m + 1 by omega, show m + 10 - 9 - 1 = m by omega, shift, shift]
  push_cast; ring

open PowerSeries in
lemma gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (X ^ 9 - X ^ 8 - X + 1) =
      X * (-X ^ 8 + 108 * X ^ 7 + 36 * X ^ 6 + 56 * X ^ 5 + 52 * X ^ 4 + 56 * X ^ 3 + 36 * X ^ 2 +
        108 * X + 449) := by
  rw [show (X : PowerSeries ℚ) ^ 9 - X ^ 8 - X + 1 = X ^ 9 - X ^ 8 - X ^ 1 + 1 by rw [pow_one]]
  rw [show (X : PowerSeries ℚ) * (-X ^ 8 + 108 * X ^ 7 + 36 * X ^ 6 + 56 * X ^ 5 + 52 * X ^ 4 +
      56 * X ^ 3 + 36 * X ^ 2 + 108 * X + 449) =
      -X ^ 9 + C (108 : ℚ) * X ^ 8 + C 36 * X ^ 7 + C 56 * X ^ 6 + C 52 * X ^ 5 + C 56 * X ^ 4 +
      C 36 * X ^ 3 + C 108 * X ^ 2 + C 449 * X ^ 1 by simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow, coeff_C]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := vals
  have v8 : Nat.nth P 8 = 1349 := by rw [show 8 = 0 + 8 from rfl, shift, v0]
  by_cases hn : n ≤ 9
  · interval_cases n <;> simp [a, v0, v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · push Not at hn
    have hr := rec_part n hn
    have hr' : ((a n : ℤ) : ℚ) = ((a (n - 1) + a (n - 8) - a (n - 9) : ℤ) : ℚ) := by rw [hr]
    push_cast at hr'
    have c1 : n - 9 ≠ 0 := by omega
    have c2 : n - 8 ≠ 0 := by omega
    have c3 : n - 1 ≠ 0 := by omega
    have c4 : n ≠ 0 := by omega
    have c5 : n ≠ 9 := by omega
    simp only [show 9 ≤ n by omega, show 8 ≤ n by omega, show 1 ≤ n by omega, show 7 ≤ n by omega,
      show 6 ≤ n by omega, show 5 ≤ n by omega, show 4 ≤ n by omega, show 3 ≤ n by omega,
      show 2 ≤ n by omega, if_true, c1, c2, c3, c4, c5, if_false, show n - 8 ≠ 0 by omega,
      show n - 7 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega]
    rw [hr']; ring
end A339532Proof

open A339532Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a339532.main :=
  ⟨rec_part, gf⟩
