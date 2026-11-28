import OMAStatements.S_oeis_a270013
import Mathlib

-- Problem: oeis-a270013
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: for Rule 7 every cell is ON at stage 1, then the whole plane alternates
-- (all ON gives k = 4 everywhere, so all OFF; all OFF gives k = 0, so all ON). Rule 5 is all OFF
-- at stage 2 and then alternates the same way, so aOf 5 n = a n for n >= 2. Hence
-- a n = (2n+3)^2 for even n > 0 and -(2n+1)^2 for odd n, a 0 = 8; the closed forms, the
-- recurrence and the generating function follow by parity cases and coefficient comparison.

namespace OMA.Sol_a270013
open PowerSeries OMA.S_oeis_a270013


lemma rule_c4 (c : Bool) : rule c 4 = false := by cases c <;> decide

lemma state_one (p : ℤ × ℤ) : state 1 p = true := by
  obtain ⟨x, y⟩ := p
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [state, nbrs] <;> decide
  · simp only [state, nbrs, List.countP_cons, List.countP_nil, Prod.mk.injEq, h,
      decide_false, decide_eq_true_eq]
    split_ifs <;> first | omega | decide

lemma state_succ : ∀ t p, state (t + 1) p = decide (t % 2 = 0) := by
  intro t
  induction t with
  | zero => intro p; simpa using state_one p
  | succ t ih =>
    intro p
    have hf : state (t + 1) = fun _ => decide (t % 2 = 0) := funext ih
    show rule (state (t + 1) p) ((nbrs p).countP (fun q => state (t + 1) q)) = _
    rw [hf]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : ¬ ((t + 1) % 2 = 0) := by omega
      simp only [h, h', nbrs]
      simp only [decide_true, decide_false, List.countP_cons, List.countP_nil]
      decide
    · have h' : (t + 1) % 2 = 0 := by omega
      simp only [h, h', nbrs]
      simp only [decide_true, decide_false, List.countP_cons, List.countP_nil]
      decide

lemma rule5_true (k : ℕ) : ruleOf 5 true k = false := by
  rcases k with _ | _ | k
  · decide
  · decide
  · unfold ruleOf
    apply Nat.testBit_lt_two_pow
    show 5 < 2 ^ (2 * (k + 2) + 1)
    have : 2 ^ 5 ≤ 2 ^ (2 * (k + 2) + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma stateOf5_one (p : ℤ × ℤ) : stateOf 5 1 p = decide (p ≠ (0, 0)) := by
  obtain ⟨x, y⟩ := p
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    show ruleOf 5 (stateOf 5 0 (0,0)) _ = _
    simp only [stateOf, decide_true]
    rw [rule5_true]; simp
  · simp only [stateOf, nbrs, List.countP_cons, List.countP_nil, Prod.mk.injEq, ne_eq, h,
      decide_false, not_false_eq_true, decide_true, decide_eq_true_eq]
    split_ifs <;> first | omega | decide

lemma stateOf5_two (p : ℤ × ℤ) : stateOf 5 2 p = false := by
  have hf : stateOf 5 1 = fun p => decide (p ≠ (0, 0)) := funext stateOf5_one
  show ruleOf 5 (stateOf 5 1 p) ((nbrs p).countP (fun q => stateOf 5 1 q)) = _
  rw [hf]
  by_cases h : p = (0, 0)
  · subst h
    simp [nbrs]
    decide
  · simp only [ne_eq, h, not_false_eq_true, decide_true]
    exact rule5_true _

lemma stateOf5_succ : ∀ t p, stateOf 5 (t + 2) p = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero => intro p; simpa using stateOf5_two p
  | succ t ih =>
    intro p
    have hf : stateOf 5 (t + 2) = fun _ => decide (t % 2 = 1) := funext ih
    show ruleOf 5 (stateOf 5 (t + 2) p) ((nbrs p).countP (fun q => stateOf 5 (t + 2) q)) = _
    rw [hf]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp only [h, h', nbrs]
      simp only [decide_true, decide_false, List.countP_cons, List.countP_nil]
      decide
    · have h' : ¬ ((t + 1) % 2 = 1) := by omega
      simp only [h, h', nbrs]
      simp only [decide_true, decide_false, List.countP_cons, List.countP_nil]
      decide

lemma stateOf5_eq (s : ℕ) (hs : 2 ≤ s) : stateOf 5 s = state s := by
  funext p
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  rw [stateOf5_succ, show t + 2 = (t + 1) + 1 by omega, state_succ]
  simp only [decide_eq_decide]; omega

lemma sum_const_if (m : ℕ) (b : Prop) [Decidable b] :
    (∑ x ∈ Finset.range m, ∑ y ∈ Finset.range m, (if b then 1 else 0 : ℕ)) =
      if b then m * m else 0 := by
  split_ifs <;> simp

lemma a_succ (m : ℕ) : a (m + 1) =
    if m % 2 = 0 then -((2 * (m : ℤ) + 3) ^ 2) else (2 * (m : ℤ) + 5) ^ 2 := by
  unfold a
  simp only [state_succ, decide_eq_true_eq]
  rw [sum_const_if, sum_const_if]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h' : ¬ ((m + 1) % 2 = 0) := by omega
    simp only [h, h', if_true, if_false]
    push_cast; ring
  · have h' : (m + 1) % 2 = 0 := by omega
    have h'' : ¬ (m % 2 = 0) := by omega
    simp only [h', h'', if_true, if_false]
    push_cast; ring

lemma a_closed (n : ℕ) (hn : 0 < n) : a n =
    if n % 2 = 0 then (2 * (n : ℤ) + 3) ^ 2 else -((2 * (n : ℤ) + 1) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h' : ¬ ((m + 1) % 2 = 0) := by omega
    simp only [h, h', if_true, if_false]; push_cast; ring
  · have h' : (m + 1) % 2 = 0 := by omega
    have h'' : ¬ (m % 2 = 0) := by omega
    simp only [h', h'', if_true, if_false]; push_cast; ring

lemma a_zero : a 0 = 8 := by
  unfold a
  simp only [state_succ]
  simp [state, Finset.filter_singleton]

lemma a_rec (m : ℕ) : a (m + 6) + a (m + 5) - 2 * a (m + 4) - 2 * a (m + 3) + a (m + 2) + a (m + 1) = 0 := by
  rw [a_closed (m+6) (by omega), a_closed (m+5) (by omega), a_closed (m+4) (by omega),
    a_closed (m+3) (by omega), a_closed (m+2) (by omega), a_closed (m+1) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · simp [Nat.add_mod, h]; ring
  · simp [Nat.add_mod, h]; ring

lemma gf : A = (8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5) * ((1 - X) ^ 2 * (1 + X) ^ 3)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have hD : ((1 - X) ^ 2 * (1 + X) ^ 3 : ℚ⟦X⟧) =
      X ^ 0 + X ^ 1 - C (2:ℚ) * X ^ 2 - C (2:ℚ) * X ^ 3 + X ^ 4 + X ^ 5 := by
    simp only [map_ofNat]; ring
  have hN : (8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5 : ℚ⟦X⟧) =
      C (8:ℚ) * X ^ 0 - X ^ 1 + C (24:ℚ) * X ^ 2 + C (2:ℚ) * X ^ 3 - X ^ 5 := by
    simp only [map_ofNat]; ring
  have hAD : A * (X ^ 0 + X ^ 1 - C (2:ℚ) * X ^ 2 - C (2:ℚ) * X ^ 3 + X ^ 4 + X ^ 5) =
      A * X ^ 0 + A * X ^ 1 - C (2:ℚ) * (A * X ^ 2) - C (2:ℚ) * (A * X ^ 3) + A * X ^ 4 + A * X ^ 5 := by
    ring
  rw [hD, hN, hAD]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
  have h1 := a_closed 1 (by omega)
  have h2 := a_closed 2 (by omega)
  have h3 := a_closed 3 (by omega)
  have h4 := a_closed 4 (by omega)
  have h5 := a_closed 5 (by omega)
  norm_num at h1 h2 h3 h4 h5
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, h1]; norm_num
  · simp [a_zero, h1, h2]; norm_num
  · simp [a_zero, h1, h2, h3]; norm_num
  · simp [a_zero, h1, h2, h3, h4]; norm_num
  · simp [a_zero, h1, h2, h3, h4, h5]; norm_num
  · have := a_rec m
    simp only [show ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 = 0) by omega,
      show ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 = 1) by omega,
      show ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 = 2) by omega,
      show ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 = 3) by omega,
      show ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 = 5) by omega,
      show 0 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega, if_true, if_false]
    rw [show m + 1 + 1 + 1 + 1 + 1 + 1 - 0 = m + 6 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 5 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 4 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 3 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 2 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 by omega]
    have hq : ((a (m + 6) + a (m + 5) - 2 * a (m + 4) - 2 * a (m + 3) + a (m + 2) + a (m + 1) : ℤ) : ℚ) = 0 := by
      rw [this]; simp
    push_cast at hq
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    linarith

theorem main_proof :
    (∀ n : ℕ, 0 < n →
      (a n : ℚ) = 4 + 5 * (-1) ^ n + (4 + 8 * (-1) ^ n) * n + 4 * (-1) ^ n * n ^ 2) ∧
    (∀ n : ℕ, 1 < n → a n = aOf 5 n) ∧
    (∀ n : ℕ, 0 < n → Even n → (a n : ℚ) = 4 * n ^ 2 + 12 * n + 9) ∧
    (∀ n : ℕ, 0 < n → Odd n → (a n : ℚ) = -4 * n ^ 2 - 4 * n - 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = -a (n - 1) + 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - a (n - 5)) ∧
    A = (8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5) * ((1 - X) ^ 2 * (1 + X) ^ 3)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, gf⟩
  · intro n hn
    rw [a_closed n hn]
    rcases Nat.even_or_odd n with h | h
    · have h' : n % 2 = 0 := Nat.even_iff.mp h
      rw [h.neg_one_pow]; simp only [h', if_true]; push_cast; ring
    · have h' : ¬ (n % 2 = 0) := by have := Nat.odd_iff.mp h; omega
      rw [h.neg_one_pow]; simp only [h', if_false]; push_cast; ring
  · intro n hn
    unfold a aOf
    rw [stateOf5_eq (n + 1) (by omega), stateOf5_eq n (by omega)]
  · intro n hn h
    have h' : n % 2 = 0 := Nat.even_iff.mp h
    rw [a_closed n hn]; simp only [h', if_true]; push_cast; ring
  · intro n hn h
    have h' : ¬ (n % 2 = 0) := by have := Nat.odd_iff.mp h; omega
    rw [a_closed n hn]; simp only [h', if_false]; push_cast; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have := a_rec m
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega]
    linarith

end OMA.Sol_a270013

theorem OMA.solution : type_of% @OMA.S_oeis_a270013.main := OMA.Sol_a270013.main_proof
