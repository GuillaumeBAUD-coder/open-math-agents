import OMAStatements.S_oeis_a267294

-- Problem: A267294, Rule 121 elementary cellular automaton.
-- Credit: @prasledi (the owner of the agent is credited as the solver)
-- Proof: outside the light cone every cell equals the background t mod 2. From t = 7 on,
-- the row read from its left end is a fixed pattern of 14 cells depending on t mod 4,
-- followed by the background. Hence a(n+4) = 256 a(n) + 255 [n odd] for n >= 7, which
-- gives the recurrence for n >= 13; the generating function follows from a(0..12).

namespace OMA.P_oeis_a267294

open OMA.S_oeis_a267294

def L : ℕ → List Bool
  | 0 => [true, true, true, false, false, false, false, false, true, true, true, false, false, false]
  | 1 => [false, true, false, true, true, true, true, true, false, true, false, true, true, true]
  | 2 => [true, true, false, true, true, false, false, false, true, true, false, true, true, false]
  | _ => [false, true, true, true, true, true, true, true, false, true, true, true, true, true]

def D (r : ℕ) (j : ℤ) : Bool :=
  if 0 ≤ j ∧ j < 14 then (L r).getD j.toNat false else (r % 2 == 1)

lemma rule_bg (b : Bool) : ruleOut 121 b b b = !b := by
  cases b <;> rfl

lemma bg : ∀ (t : ℕ) (i : ℤ), (i < -(t : ℤ) ∨ (t : ℤ) < i) → cell 121 t i = (t % 2 == 1)
  | 0, i, h => by
      have hi : i ≠ 0 := by omega
      simp [cell, hi]
  | t + 1, i, h => by
      have h1 := bg t (i - 1) (by omega)
      have h2 := bg t i (by omega)
      have h3 := bg t (i + 1) (by omega)
      show ruleOut 121 (cell 121 t (i - 1)) (cell 121 t i) (cell 121 t (i + 1)) = _
      rw [h1, h2, h3, rule_bg]
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have : (t + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (t + 1) % 2 = 0 := by omega
        simp [h, this]

lemma D_out (r : ℕ) (j : ℤ) (h : j < 0 ∨ 14 ≤ j) : D r j = (r % 2 == 1) := by
  unfold D
  rw [if_neg (by omega)]

lemma step_fin' : ∀ r : Fin 4, ∀ k : Fin 16,
    ruleOut 121 (D r.val ((k.val : ℤ) - 2)) (D r.val ((k.val : ℤ) - 1)) (D r.val (k.val : ℤ)) =
      D ((r.val + 1) % 4) (k.val : ℤ) := by
  decide

lemma step_fin (r : ℕ) (hr : r < 4) (k : ℕ) (hk : k < 16) :
    ruleOut 121 (D r ((k : ℤ) - 2)) (D r ((k : ℤ) - 1)) (D r (k : ℤ)) = D ((r + 1) % 4) (k : ℤ) :=
  step_fin' ⟨r, hr⟩ ⟨k, hk⟩

lemma step (r : ℕ) (hr : r < 4) (j : ℤ) :
    ruleOut 121 (D r (j - 2)) (D r (j - 1)) (D r j) = D ((r + 1) % 4) j := by
  by_cases hj : 0 ≤ j ∧ j < 16
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, by omega⟩
    exact step_fin r hr k (by omega)
  · rw [D_out r (j - 2) (by omega), D_out r (j - 1) (by omega), D_out r j (by omega),
      D_out _ j (by omega), rule_bg]
    interval_cases r <;> rfl

lemma base_fin' : ∀ k : Fin 15, cell 121 7 ((k.val : ℤ) - 7) = D 3 ((k.val : ℤ) - 7 + 7) := by
  decide +kernel

lemma base_fin (k : ℕ) (hk : k < 15) : cell 121 7 ((k : ℤ) - 7) = D 3 ((k : ℤ) - 7 + 7) :=
  base_fin' ⟨k, hk⟩

lemma form : ∀ t, 7 ≤ t → ∀ i : ℤ, cell 121 t i = D (t % 4) (i + t) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
      intro i
      by_cases hi : -7 ≤ i ∧ i ≤ 7
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) - 7 := ⟨(i + 7).toNat, by omega⟩
        exact base_fin k (by omega)
      · rw [bg 7 i (by omega), D_out 3 _ (by push_cast; omega)]
  | succ t ht ih =>
      intro i
      show ruleOut 121 (cell 121 t (i - 1)) (cell 121 t i) (cell 121 t (i + 1)) = _
      rw [ih, ih, ih]
      have e1 : i - 1 + (t : ℤ) = (i + ((t + 1 : ℕ) : ℤ)) - 2 := by push_cast; ring
      have e2 : i + (t : ℤ) = (i + ((t + 1 : ℕ) : ℤ)) - 1 := by push_cast; ring
      have e3 : i + 1 + (t : ℤ) = i + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, e3, step (t % 4) (Nat.mod_lt _ (by norm_num))]
      congr 1
      omega

def F (r n j : ℕ) : ℤ := if D r (j : ℤ) then (2 : ℤ) ^ (2 * n - j) else 0

lemma a_eq (n : ℕ) (hn : 7 ≤ n) :
    a n = ∑ j ∈ Finset.range (2 * n + 1), F (n % 4) n j := by
  unfold a F
  apply Finset.sum_congr rfl
  intro j _
  rw [form n hn]
  congr 2
  ring

lemma shift (n : ℕ) (hn : 7 ≤ n) :
    a (n + 4) = 256 * a n + (if n % 2 = 1 then 255 else 0) := by
  rw [a_eq (n + 4) (by omega), a_eq n hn]
  have hr : (n + 4) % 4 = n % 4 := by omega
  rw [hr, show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ 2 * n := by simp at hj; omega
    unfold F
    split_ifs
    · rw [show 2 * (n + 4) - j = (2 * n - j) + 8 by omega, pow_add]; ring
    · ring
  · have hb : ∀ k < 8, F (n % 4) (n + 4) (2 * n + 1 + k) =
        if n % 2 = 1 then (2 : ℤ) ^ (7 - k) else 0 := by
      intro k hk
      unfold F
      rw [D_out _ _ (by push_cast; omega)]
      rw [show 2 * (n + 4) - (2 * n + 1 + k) = 7 - k by omega]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have : n % 4 % 2 = 0 := by omega
        simp [h, this]
      · have : n % 4 % 2 = 1 := by omega
        simp [h, this]
    rw [Finset.sum_congr rfl (fun k hk => hb k (Finset.mem_range.mp hk))]
    split_ifs <;> simp [Finset.sum_range_succ]

lemma rec13 (n : ℕ) (hn : 13 ≤ n) : a n = a (n - 2) + 256 * a (n - 4) - 256 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h1 := shift (m + 2) (by omega)
  have h2 := shift m (by omega)
  rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 6 = m by omega]
  rw [show m + 6 = m + 2 + 4 by ring, h1, h2]
  have : (m + 2) % 2 = m % 2 := by omega
  rw [this]
  ring

lemma v0 : a 0 = 1 := by decide
lemma v1 : a 1 = 1 := by decide
lemma v2 : a 2 = 26 := by decide
lemma v3 : a 3 = 59 := by decide
lemma v4 : a 4 = 476 := by decide
lemma v5 : a 5 = 751 := by decide +kernel
lemma v6 : a 6 = 7024 := by decide +kernel
lemma v7 : a 7 = 16319 := by rw [a_eq 7 (by norm_num)]; decide
lemma v8 : a 8 = 115136 := by rw [a_eq 8 (by norm_num)]; decide
lemma v9 : a 9 = 195327 := by rw [a_eq 9 (by norm_num)]; decide
lemma v10 : a 10 = 1776384 := by rw [a_eq 10 (by norm_num)]; decide
lemma v11 : a 11 = 4177919 := by rw [a_eq 11 (by norm_num)]; decide
lemma v12 : a 12 = 29474816 := by rw [a_eq 12 (by norm_num)]; decide

open PowerSeries in
lemma gf (b : ℕ → ℤ)
    (h13 : ∀ n, 13 ≤ n → b n = b (n - 2) + 256 * b (n - 4) - 256 * b (n - 6))
    (v0 : b 0 = 1) (v1 : b 1 = 1) (v2 : b 2 = 26) (v3 : b 3 = 59) (v4 : b 4 = 476)
    (v5 : b 5 = 751) (v6 : b 6 = 7024) (v7 : b 7 = 16319) (v8 : b 8 = 115136)
    (v9 : b 9 = 195327) (v10 : b 10 = 1776384) (v11 : b 11 = 4177919) (v12 : b 12 = 29474816) :
    (PowerSeries.mk (fun n => (b n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2) : PowerSeries ℚ) = 1 + X + 25 * X ^ 2 + 58 * X ^ 3 + 194 * X ^ 4 + 436 * X ^ 5 + 148 * X ^ 6 + 720 * X ^ 7 - 7088 * X ^ 8 + 1856 * X ^ 9 - 15040 * X ^ 10 - 2816 * X ^ 11 + 21760 * X ^ 12) := by
  set f := PowerSeries.mk (fun n => (b n : ℚ)) with hf
  have key : f * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2) : PowerSeries ℚ) =
      f - f * X ^ 2 - C (256 : ℚ) * (f * X ^ 4) + C (256 : ℚ) * (f * X ^ 6) := by
    rw [map_ofNat]; ring
  rw [key]
  ext n
  simp only [← map_ofNat (C (R := ℚ))]
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, hf, coeff_mk, coeff_X_pow, coeff_X,
    coeff_one, mul_ite, mul_one, mul_zero, coeff_C]
  by_cases hn : 13 ≤ n
  · have := h13 n hn
    have h1 : (b n : ℚ) = b (n - 2) + 256 * b (n - 4) - 256 * b (n - 6) := by exact_mod_cast this
    have hle : ∀ k, k ≤ 12 → (k ≤ n) = True := fun k hk => by simp; omega
    have hz : ∀ k, k ≤ 12 → (n - k = 0) = False := fun k hk => by simp; omega
    have hne : ∀ k, k ≤ 12 → (n = k) = False := fun k hk => by simp; omega
    have h6 : (6 ≤ n) = True := by simp; omega
    simp only [hle, hz, hne, h6, if_true, if_false, Nat.reduceLeDiff, le_refl, Nat.ofNat_le, true_implies]
    rw [h1]; ring
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] <;> norm_num

end OMA.P_oeis_a267294

open OMA.P_oeis_a267294 OMA.S_oeis_a267294 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267294.main := by
  refine ⟨fun n hn => by exact_mod_cast rec13 n hn, ?_⟩
  exact gf a rec13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
