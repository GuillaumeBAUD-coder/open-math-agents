import OMAStatements.S_oeis_a265284
import Mathlib

namespace A265284

open OMA.S_oeis_a265284

def T : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: false :: T k

def V : ℕ → List Bool
  | 0 => []
  | k + 1 => false :: true :: V k

lemma scan_T (k : ℕ) (Y : List Bool) :
    scan true false (T k ++ Y) = V k ++ scan true false Y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show scan true false (true :: false :: (T k ++ Y)) = false :: true :: (V k ++ scan true false Y)
    rw [scan, scan, ih]
    rfl

lemma V_false (k : ℕ) (Z : List Bool) : V k ++ false :: Z = false :: (T k ++ Z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show false :: true :: (V k ++ false :: Z) = false :: (true :: false :: (T k ++ Z))
    rw [ih]

lemma T_snoc (k : ℕ) (Z : List Bool) : T k ++ true :: false :: Z = T (k + 1) ++ Z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show true :: false :: (T k ++ true :: false :: Z) = true :: false :: (T (k + 1) ++ Z)
    rw [ih]

lemma ones_T (k : ℕ) (Y : List Bool) : ones (T k ++ Y) = (k : ℤ) + ones Y := by
  induction k with
  | zero => simp [T]
  | succ k ih =>
    have h1 : ones (T (k + 1) ++ Y) = 1 + (0 + ones (T k ++ Y)) := rfl
    rw [h1, ih]
    push_cast
    ring

lemma ones_V (k : ℕ) (Y : List Bool) : ones (V k ++ Y) = (k : ℤ) + ones Y := by
  induction k with
  | zero => simp [V]
  | succ k ih =>
    have h1 : ones (V (k + 1) ++ Y) = 0 + (1 + ones (V k ++ Y)) := rfl
    rw [h1, ih]
    push_cast
    ring

def E (m : ℕ) : List Bool := true :: true :: false :: (T (2 * m) ++ [true, true])

def O (m : ℕ) : List Bool := true :: true :: true :: (V (2 * m) ++ [false, true, true, true])

lemma next_E (m : ℕ) : next (E m) = O m := by
  have e : E m ++ [false, false] =
      true :: true :: false :: (T (2 * m) ++ [true, true, false, false]) := by
    simp [E]
  show scan false false (E m ++ [false, false]) = O m
  rw [e, scan, scan, scan, scan_T]
  rfl

lemma E_succ (m : ℕ) : E (m + 1) =
    true :: true :: false :: true :: (V (2 * m) ++ [false, true, false, true, true]) := by
  have e3 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  show true :: true :: false :: (T (2 * (m + 1)) ++ [true, true]) = _
  rw [V_false, T_snoc, e3]
  rfl

lemma next_O (m : ℕ) : next (O m) = E (m + 1) := by
  have e : O m ++ [false, false] =
      true :: true :: true :: false :: (T (2 * m) ++ [true, true, true, false, false]) := by
    have e0 : O m ++ [false, false] =
        true :: true :: true :: (V (2 * m) ++ false :: [true, true, true, false, false]) := by
      simp [O]
    rw [e0, V_false]
  show scan false false (O m ++ [false, false]) = E (m + 1)
  rw [e, scan, scan, scan, scan, scan_T, E_succ]
  rfl

lemma rows (m : ℕ) : row (2 * m + 2) = E m ∧ row (2 * m + 3) = O m := by
  induction m with
  | zero =>
    have h : row 2 = E 0 := by decide
    refine ⟨h, ?_⟩
    show next (row 2) = O 0
    rw [h, next_E]
  | succ k ih =>
    have h1 : row (2 * (k + 1) + 2) = E (k + 1) := by
      have e : 2 * (k + 1) + 2 = 2 * k + 3 + 1 := by ring
      rw [e]
      show next (row (2 * k + 3)) = E (k + 1)
      rw [ih.2, next_O]
    refine ⟨h1, ?_⟩
    have e : 2 * (k + 1) + 3 = 2 * (k + 1) + 2 + 1 := by ring
    rw [e]
    show next (row (2 * (k + 1) + 2)) = O (k + 1)
    rw [h1, next_E]

lemma ones_E (m : ℕ) : ones (E m) = 2 * (m : ℤ) + 4 := by
  have h : ones (E m) = 1 + (1 + (0 + ones (T (2 * m) ++ [true, true]))) := rfl
  have h2 : ones [true, true] = 2 := by decide
  rw [h, ones_T, h2]
  push_cast
  ring

lemma ones_O (m : ℕ) : ones (O m) = 2 * (m : ℤ) + 6 := by
  have h : ones (O m) = 1 + (1 + (1 + ones (V (2 * m) ++ [false, true, true, true]))) := rfl
  have h2 : ones [false, true, true, true] = 3 := by decide
  rw [h, ones_V, h2]
  push_cast
  ring

lemma closed (m : ℕ) : 2 * a (2 * m + 1) = 4 * (m : ℤ) ^ 2 + 16 * m + 8 ∧
    2 * a (2 * m + 2) = 4 * (m : ℤ) ^ 2 + 20 * m + 16 := by
  induction m with
  | zero => constructor <;> decide
  | succ k ih =>
    have h1 : a (2 * (k + 1) + 1) = a (2 * k + 2) + ones (row (2 * k + 3)) := by
      have e : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by ring
      rw [e]
      rfl
    have h2 : a (2 * (k + 1) + 2) = a (2 * (k + 1) + 1) + ones (row (2 * (k + 1) + 2)) := rfl
    rw [(rows k).2, ones_O] at h1
    rw [(rows (k + 1)).1, ones_E] at h2
    constructor
    · rw [h1]
      push_cast
      linear_combination ih.2
    · rw [h2, h1]
      push_cast
      linear_combination ih.2

lemma odd_form (m : ℕ) : 2 * a (2 * m + 1) = 4 * (m : ℤ) ^ 2 + 16 * m + 8 := (closed m).1

lemma even_form (m : ℕ) : 2 * a (2 * m + 2) = 4 * (m : ℤ) ^ 2 + 20 * m + 16 := (closed m).2

lemma rec4 (k : ℕ) : a (k + 5) = 2 * a (k + 4) - 2 * a (k + 2) + a (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have h5 := odd_form (m + 2)
    have h4 := even_form (m + 1)
    have h2 := even_form m
    have h1 := odd_form m
    rw [show 2 * (m + 2) + 1 = 2 * m + 5 by ring] at h5
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring] at h4
    push_cast at h5 h4
    linarith
  · have h6 := even_form (m + 2)
    have h5 := odd_form (m + 2)
    have h3 := odd_form (m + 1)
    have h2 := even_form m
    rw [show 2 * (m + 2) + 2 = 2 * m + 1 + 5 by ring] at h6
    rw [show 2 * (m + 2) + 1 = 2 * m + 1 + 4 by ring] at h5
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring] at h3
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring] at h2
    push_cast at h6 h5 h3
    linarith

end A265284

open OMA.S_oeis_a265284 in
theorem OMA.solution : type_of% @OMA.S_oeis_a265284.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have h := A265284.even_form k
      have hp : ((-1 : ℤ)) ^ (2 * (k + 1)) = 1 := by
        rw [pow_mul]
        norm_num
      rw [hp, show 2 * (k + 1) = 2 * k + 2 by ring]
      push_cast
      linear_combination 2 * h
    · have h := A265284.odd_form m
      have hp : ((-1 : ℤ)) ^ (2 * m + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [hp]
      push_cast
      linear_combination 2 * h
  · intro n hn he
    obtain ⟨r, hr⟩ := he
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨r - 1, by omega⟩
    have h := A265284.even_form k
    push_cast
    linear_combination h
  · intro n ho
    obtain ⟨m, rfl⟩ := ho
    have h := A265284.odd_form m
    push_cast
    linear_combination h
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
      show k + 5 - 4 = k + 1 by omega]
    exact A265284.rec4 k
  · intro n
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with
      rfl | rfl | rfl | rfl | rfl | h5
    · decide
    · decide
    · decide
    · decide
    · decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have hnum : numeratorCoeff (k + 5) = 0 := by
        unfold numeratorCoeff
        split <;> first | rfl | omega
      have hprod : productCoeff (k + 5) =
          a (k + 5) - 2 * a (k + 4) + 2 * a (k + 2) - a (k + 1) := rfl
      rw [hprod, hnum, A265284.rec4 k]
      ring
