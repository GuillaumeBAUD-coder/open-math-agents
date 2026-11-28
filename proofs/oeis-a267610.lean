import OMAStatements.S_oeis_a267610
import Mathlib

/-!
# A267610: the Rascoe generating function for Rule 182

* Rule 182 is `(l xor c xor r) or (l and not c and r)` (`ruleOut_182`).
* `r90 t i` is the Rule 90 automaton from one ON cell. Its row `t` is Pascal's row `t`
  modulo `2`, placed on the positions `2 j - t` (`r90_choose`, `r90_support`).
* Row `k` of Rule 182 is OFF exactly where row `k + 1` of Rule 90 is ON, inside `[-k, k]`
  (`cell_eq`). Hence row `k` has `S (k + 1) - 2` OFF cells, where `S m` counts the odd
  entries of Pascal's row `m` (`off_count`), and `a n = A006046 (n + 2) - 2 n - 3`.
* The generating function identity then follows by comparing coefficients.
-/

namespace OMA.A267610Proof

open OMA.S_oeis_a267610 PowerSeries Finset

/-- Rule 90 from a single ON cell. -/
def r90 : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => xor (r90 t (i - 1)) (r90 t (i + 1))

theorem ruleOut_182 (l c r : Bool) :
    ruleOut 182 l c r = (xor (xor l c) r || (l && !c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

theorem r90_support : ∀ (t : ℕ) (x : ℤ), r90 t x = true →
    -(t : ℤ) ≤ x ∧ x ≤ t ∧ (x + t) % 2 = 0
  | 0, x, h => by
    simp only [r90, decide_eq_true_eq] at h
    subst h
    simp
  | t + 1, x, h => by
    simp only [r90] at h
    cases ha : r90 t (x - 1) <;> cases hb : r90 t (x + 1) <;> rw [ha, hb] at h
    · simp at h
    · have := r90_support t _ hb
      push_cast
      omega
    · have := r90_support t _ ha
      push_cast
      omega
    · simp at h

theorem xor_odd (a b : ℕ) :
    xor (decide (Odd a)) (decide (Odd b)) = decide (Odd (a + b)) := by
  simp only [Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [ha, hb, Nat.add_mod]

theorem r90_choose : ∀ (t j : ℕ) (i : ℤ), j ≤ t → i = 2 * (j : ℤ) - t →
    r90 t i = decide (Odd (t.choose j))
  | 0, j, i, hj, hi => by
    obtain rfl : j = 0 := by omega
    subst hi
    simp [r90]
  | t + 1, j, i, hj, hi => by
    simp only [r90]
    rcases j with _ | j
    · have h1 : r90 t (i - 1) = false := by
        cases h : r90 t (i - 1)
        · rfl
        · have := r90_support t _ h
          push_cast at hi
          omega
      have h2 : r90 t (i + 1) = true := by
        rw [r90_choose t 0 (i + 1) (by omega) (by push_cast at hi ⊢; omega)]
        simp
      rw [h1, h2]
      simp
    · have h1 : r90 t (i - 1) = decide (Odd (t.choose j)) :=
        r90_choose t j (i - 1) (by omega) (by push_cast at hi ⊢; omega)
      have h2 : r90 t (i + 1) = decide (Odd (t.choose (j + 1))) := by
        by_cases hjt : j + 1 ≤ t
        · exact r90_choose t (j + 1) (i + 1) hjt (by push_cast at hi ⊢; omega)
        · have hjt' : j = t := by omega
          subst hjt'
          rw [Nat.choose_succ_self]
          cases h : r90 j (i + 1)
          · simp
          · have := r90_support j _ h
            push_cast at hi
            omega
      rw [h1, h2, xor_odd, Nat.choose_succ_succ']

theorem r90_right (t : ℕ) : r90 t (t : ℤ) = true := by
  rw [r90_choose t t _ le_rfl (by ring)]
  simp

theorem r90_left (t : ℕ) : r90 t (-(t : ℤ)) = true := by
  rw [r90_choose t 0 _ (Nat.zero_le _) (by simp)]
  simp

/-- The local step of `cell_eq`, as a statement about Booleans and integer positions. -/
theorem step_logic (k : ℕ) (i : ℤ) (a b c : Bool)
    (s1 : a = true → -((k + 1 : ℕ) : ℤ) ≤ i - 1 ∧ i - 1 ≤ ((k + 1 : ℕ) : ℤ) ∧
      (i - 1 + ((k + 1 : ℕ) : ℤ)) % 2 = 0)
    (s2 : b = true → -((k + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((k + 1 : ℕ) : ℤ) ∧
      (i + ((k + 1 : ℕ) : ℤ)) % 2 = 0)
    (s3 : c = true → -((k + 1 : ℕ) : ℤ) ≤ i + 1 ∧ i + 1 ≤ ((k + 1 : ℕ) : ℤ) ∧
      (i + 1 + ((k + 1 : ℕ) : ℤ)) % 2 = 0)
    (c1 : i - 1 = ((k + 1 : ℕ) : ℤ) → a = true) (c2 : i - 1 = -((k + 1 : ℕ) : ℤ) → a = true)
    (c5 : i + 1 = ((k + 1 : ℕ) : ℤ) → c = true) (c6 : i + 1 = -((k + 1 : ℕ) : ℤ) → c = true) :
    (xor (xor (decide (-(k : ℤ) ≤ i - 1 ∧ i - 1 ≤ k) && !a) (decide (-(k : ℤ) ≤ i ∧ i ≤ k) && !b))
        (decide (-(k : ℤ) ≤ i + 1 ∧ i + 1 ≤ k) && !c) ||
      ((decide (-(k : ℤ) ≤ i - 1 ∧ i - 1 ≤ k) && !a) && !(decide (-(k : ℤ) ≤ i ∧ i ≤ k) && !b) &&
        (decide (-(k : ℤ) ≤ i + 1 ∧ i + 1 ≤ k) && !c))) =
    (decide (-((k + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((k + 1 : ℕ) : ℤ)) && !xor a c) := by
  cases a <;> cases b <;> cases c <;>
    simp only [Bool.false_eq_true, false_implies, eq_self, true_implies, imp_false,
      implies_true] at s1 s2 s3 c1 c2 c5 c6 <;>
    by_cases p1 : -(k : ℤ) ≤ i - 1 ∧ i - 1 ≤ k <;>
    by_cases p2 : -(k : ℤ) ≤ i ∧ i ≤ k <;>
    by_cases p3 : -(k : ℤ) ≤ i + 1 ∧ i + 1 ≤ k <;>
    by_cases p4 : -((k + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((k + 1 : ℕ) : ℤ) <;>
    simp only [p1, p2, p3, p4, decide_true, decide_false] <;>
    first
    | rfl
    | (exfalso; omega)

theorem cell_eq : ∀ (k : ℕ) (i : ℤ),
    cell 182 k i = (decide (-(k : ℤ) ≤ i ∧ i ≤ k) && !r90 (k + 1) i)
  | 0, i => by
    by_cases h : i = 0
    · subst h
      decide
    · simp [cell, r90, h]
      intro h2 h3
      exfalso
      omega
  | k + 1, i => by
    have e := cell_eq k
    show ruleOut 182 (cell 182 k (i - 1)) (cell 182 k i) (cell 182 k (i + 1)) = _
    rw [e, e, e, ruleOut_182]
    have hr : r90 (k + 1 + 1) i = xor (r90 (k + 1) (i - 1)) (r90 (k + 1) (i + 1)) := rfl
    rw [hr]
    exact step_logic k i _ _ _ (r90_support (k + 1) (i - 1)) (r90_support (k + 1) i)
      (r90_support (k + 1) (i + 1))
      (fun h => by rw [h]; exact r90_right (k + 1)) (fun h => by rw [h]; exact r90_left (k + 1))
      (fun h => by rw [h]; exact r90_right (k + 1)) (fun h => by rw [h]; exact r90_left (k + 1))

/-- The number of odd entries in row `m` of Pascal's triangle. -/
def S (m : ℕ) : ℕ := ((Finset.range (m + 1)).filter (fun j => Odd (m.choose j))).card

theorem sum_range_two_mul (f : ℕ → ℕ) : ∀ n : ℕ,
    ∑ p ∈ range (2 * n), f p = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_two_mul f n, sum_range_succ]
    ring

theorem odd_count (k : ℕ) :
    (∑ p ∈ range (2 * k + 1), if r90 (k + 1) ((p : ℤ) - k) then 1 else 0) + 2 = S (k + 1) := by
  rw [sum_range_succ, sum_range_two_mul]
  have z : ∀ q : ℕ, Even q → r90 (k + 1) ((q : ℤ) - k) = false := by
    intro q hq
    obtain ⟨r, rfl⟩ := hq
    cases h : r90 (k + 1) (((r + r : ℕ) : ℤ) - k)
    · rfl
    · have := r90_support (k + 1) _ h
      push_cast at this
      omega
  have o : ∀ j : ℕ, j < k →
      r90 (k + 1) (((2 * j + 1 : ℕ) : ℤ) - k) = decide (Odd ((k + 1).choose (j + 1))) := by
    intro j hj
    exact r90_choose (k + 1) (j + 1) _ (by omega) (by push_cast; ring)
  rw [z (2 * k) (even_two_mul k)]
  have hs : ∀ j ∈ range k,
      ((if r90 (k + 1) (((2 * j : ℕ) : ℤ) - k) then 1 else 0) +
        (if r90 (k + 1) (((2 * j + 1 : ℕ) : ℤ) - k) then 1 else 0)) =
      (if Odd ((k + 1).choose (j + 1)) then 1 else 0) := by
    intro j hj
    rw [z (2 * j) (even_two_mul j), o j (mem_range.mp hj)]
    by_cases h : Odd ((k + 1).choose (j + 1)) <;> simp [h]
  rw [sum_congr rfl hs]
  simp only [S, card_filter]
  rw [sum_range_succ, sum_range_succ']
  simp only [Nat.choose_self, Nat.choose_zero_right, odd_one, if_true]
  simp

theorem off_count (k : ℕ) : (2 * k + 1 : ℤ) - onCount 182 k = (S (k + 1) : ℤ) - 2 := by
  have h : onCount 182 k +
      (∑ p ∈ range (2 * k + 1), if r90 (k + 1) ((p : ℤ) - k) then 1 else 0) = 2 * k + 1 := by
    unfold onCount
    rw [← sum_add_distrib]
    have : ∀ p ∈ range (2 * k + 1),
        ((if cell 182 k ((p : ℤ) - k) then 1 else 0) +
          (if r90 (k + 1) ((p : ℤ) - k) then 1 else 0)) = 1 := by
      intro p hp
      have hp' := mem_range.mp hp
      have hin : -(k : ℤ) ≤ (p : ℤ) - k ∧ (p : ℤ) - k ≤ k := by omega
      rw [cell_eq, decide_eq_true hin]
      cases r90 (k + 1) ((p : ℤ) - k) <;> simp
    rw [sum_congr rfl this]
    simp
  have h2 := odd_count k
  omega

theorem a_eq (n : ℕ) : (a n : ℚ) = (A006046 (n + 2) : ℚ) - 2 * n - 3 := by
  have ha : a n = ∑ k ∈ range (n + 1), ((S (k + 1) : ℤ) - 2) := by
    unfold a
    exact sum_congr rfl fun k _ => off_count k
  have hA : A006046 (n + 2) = 1 + ∑ k ∈ range (n + 1), S (k + 1) := by
    unfold A006046
    rw [show n + 2 = n + 1 + 1 by ring, sum_range_succ']
    have h0 : ((Finset.range (0 + 1)).filter (fun j => Odd (Nat.choose 0 j))).card = 1 := by
      decide
    rw [h0, add_comm]
    rfl
  rw [ha, hA, sum_sub_distrib]
  push_cast
  simp
  ring

/-- `C = ∑_{n ≥ 1} (2 n - 1) X^n`. -/
noncomputable def C : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else 2 * (n : ℚ) - 1

theorem step1 :
    X ^ 2 * PowerSeries.mk (fun n => (a n : ℚ)) =
      PowerSeries.mk (fun n => (A006046 n : ℚ)) - C := by
  ext n
  rw [coeff_X_pow_mul', map_sub, coeff_mk, C, coeff_mk]
  rcases n with _ | _ | n
  · simp [A006046]
  · simp only [show ¬ (2 ≤ 0 + 1) by omega, if_false]
    have : A006046 (0 + 1) = 1 := by decide
    rw [this]
    norm_num
  · rw [if_pos (by omega), coeff_mk, a_eq, if_neg (by omega)]
    rw [show n + 1 + 1 - 2 = n by omega]
    push_cast
    ring

theorem step2 : (1 - X) ^ 2 * C = X * (1 + X) := by
  have e1 : (1 - X) ^ 2 * C = C - (X ^ 1 * C + X ^ 1 * C) + X ^ 2 * C := by ring
  have e2 : (X : ℚ⟦X⟧) * (1 + X) = X ^ 1 + X ^ 2 := by ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', coeff_X_pow, C, coeff_mk]
  rcases n with _ | _ | n
  · simp
  · norm_num
  · rcases n with _ | n
    · norm_num
    · simp only [show ¬ (n + 1 + 1 + 1 = 0) by omega, show 1 ≤ n + 1 + 1 + 1 by omega,
        show 2 ≤ n + 1 + 1 + 1 by omega, show ¬ (n + 1 + 1 + 1 = 1) by omega,
        show ¬ (n + 1 + 1 + 1 = 2) by omega, show n + 1 + 1 + 1 - 1 = n + 2 by omega,
        show n + 1 + 1 + 1 - 2 = n + 1 by omega, show ¬ (n + 2 = 0) by omega,
        show ¬ (n + 1 = 0) by omega, if_true, if_false]
      push_cast
      ring

theorem solution :
    X ^ 2 * (1 - X) ^ 2 * PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X) ^ 2 * PowerSeries.mk (fun n => (A006046 n : ℚ)) - X * (1 + X) := by
  rw [← step2, mul_comm (X ^ 2 : ℚ⟦X⟧), mul_assoc, step1]
  ring

end OMA.A267610Proof

/-- The submitted solution. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a267610.main := OMA.A267610Proof.solution
