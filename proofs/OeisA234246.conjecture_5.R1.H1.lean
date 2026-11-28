import OMAReductions.R_OeisA234246_conjecture_5_R1
import Mathlib

-- Step OeisA234246.conjecture_5.R1.H1: hypothesis H1 of reduction OeisA234246.conjecture_5.R1
-- Credit: @prathameshnium. Finite check for 8 ≤ n ≤ 407.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 0.

/-! Step OeisA234246.conjecture_5.R1.H1. -/

namespace OMA.AOeisA234246_conjecture_5Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `2` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 2 2

theorem noDiv_sound (p : ℕ) : ∀ f d, noDiv p f d = true → ∀ m, d ≤ m → m * m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro d h; simp [noDiv] at h
  | succ f ih =>
    intro d h m hdm hmm hdiv
    simp only [noDiv] at h
    by_cases h1 : Nat.blt p (d * d) = true
    · rw [Nat.blt_eq] at h1
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : Nat.beq (p % d) 0 = true
      · rw [if_pos h2] at h; exact Bool.false_ne_true h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with h3 | h3
        · subst h3
          exact h2 (by rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih (d + 1) h m h3 hmm hdiv

theorem isPrimeB_sound (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, h⟩ := h
  have hnd := noDiv_sound p 2 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [k, r] => (decide (0 < k) && (decide (k < n) && decide (k.totient * (n - k).totient + 1 = r * r)))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := (Nat.beq n 10 || (Nat.beq n 20 || core n w))

/-- `checkList n l`: entry `i` of `l` is a witness that `good (n + i) _` holds. -/
def checkList : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | n, x :: xs => good n x && checkList (n + 1) xs

theorem checkList_sound : ∀ (l : List (List ℕ)) (n : ℕ), checkList n l = true →
    ∀ i, i < l.length → ∃ x, good (n + i) x = true := by
  intro l
  induction l with
  | nil => intro n _ i hi; simp at hi
  | cons x xs ih =>
    intro n h i hi
    simp only [checkList, Bool.and_eq_true] at h
    cases i with
    | zero => exact ⟨x, by simpa using h.1⟩
    | succ i =>
      obtain ⟨y, hy⟩ := ih (n + 1) h.2 i (by simpa using hi)
      exact ⟨y, by rw [show n + (i + 1) = n + 1 + i by omega]; exact hy⟩

theorem core_sound (n : ℕ) (w : List ℕ) (h : core n w = true) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k.totient * (n - k).totient + 1) := by
  unfold core at h
  split at h
  next k r =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨k, a0, a1, (by unfold IsSquare; exact ⟨r, a2⟩)⟩
  next => exact absurd h Bool.false_ne_true

theorem good_sound (n : ℕ) (w : List ℕ) (hn : 7 < n) (hne10 : n ≠ 10) (hne20 : n ≠ 20)
    (h : good n w = true) : ∃ k, 0 < k ∧ k < n ∧ IsSquare (k.totient * (n - k).totient + 1) := by
  simp only [good, Bool.or_eq_true] at h
  rcases h with h | h | h
  · rw [Nat.beq_eq] at h; exact absurd h hne10
  · rw [Nat.beq_eq] at h; exact absurd h hne20
  · exact core_sound n w h

/-! One witness for each `n = 8, …, 407`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 3], [4, 3], [], [3, 3], [4, 3], [3, 3], [4, 3], [3, 3], [1, 3], [1, 3], [2, 3], [5, 5], [], [1, 3], [2, 3], [5, 5], [3, 5], [1, 3], [2, 3], [6, 5], [10, 5], [3, 5], [4, 5], [1, 3], [2, 3]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 8 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5, 7], [6, 5], [10, 9], [1, 5], [2, 5], [3, 7], [3, 5], [1, 5], [2, 5], [3, 7], [4, 7], [3, 9], [3, 5], [1, 5], [2, 5], [3, 7], [4, 7], [8, 7], [6, 7], [8, 9], [1, 5], [2, 5], [3, 7], [4, 7], [1, 5]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 33 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 5], [3, 7], [4, 7], [6, 9], [6, 7], [19, 19], [3, 11], [4, 11], [1, 7], [2, 7], [7, 19], [13, 17], [8, 11], [1, 5], [2, 5], [1, 5], [2, 5], [3, 7], [4, 7], [20, 17], [3, 9], [1, 5], [2, 5], [3, 7], [4, 7]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 58 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[6, 11], [6, 7], [1, 5], [2, 5], [3, 7], [4, 7], [15, 17], [6, 7], [1, 5], [2, 5], [3, 7], [4, 7], [8, 15], [3, 11], [4, 11], [9, 23], [6, 11], [5, 17], [10, 17], [3, 11], [3, 9], [4, 9], [1, 7], [1, 7], [2, 7]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 83 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[9, 19], [30, 25], [12, 13], [7, 17], [7, 17], [1, 7], [2, 7], [49, 29], [3, 15], [4, 15], [14, 17], [6, 15], [28, 23], [5, 15], [5, 17], [12, 17], [1, 9], [2, 9], [4, 11], [3, 11], [4, 11], [7, 19], [6, 11], [1, 7], [2, 7]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 108 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[4, 13], [20, 17], [3, 9], [4, 9], [7, 17], [6, 9], [9, 17], [5, 17], [1, 7], [2, 7], [8, 17], [1, 11], [1, 7], [2, 7], [7, 17], [3, 15], [4, 15], [3, 13], [4, 13], [15, 33], [3, 9], [4, 9], [13, 29], [1, 11], [1, 7]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 133 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 7], [16, 31], [6, 11], [7, 19], [5, 25], [7, 17], [11, 31], [1, 9], [1, 9], [2, 9], [9, 25], [1, 7], [2, 7], [10, 23], [18, 19], [12, 23], [5, 25], [3, 13], [1, 11], [1, 9], [2, 9], [5, 15], [25, 49], [1, 7], [2, 7]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 158 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[11, 29], [1, 11], [2, 11], [12, 15], [5, 17], [3, 17], [3, 11], [4, 11], [6, 17], [6, 11], [7, 19], [7, 31], [5, 17], [9, 31], [21, 31], [8, 17], [3, 13], [4, 13], [1, 9], [2, 9], [17, 31], [1, 13], [2, 13], [5, 23], [9, 19]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 183 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[25, 49], [8, 23], [29, 71], [1, 7], [2, 7], [4, 19], [9, 31], [6, 19], [1, 13], [2, 13], [22, 29], [7, 25], [3, 19], [1, 9], [2, 9], [4, 17], [8, 17], [6, 17], [1, 11], [2, 11], [12, 17], [3, 15], [4, 15], [18, 29], [1, 11]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 208 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[2, 11], [12, 17], [3, 15], [4, 15], [7, 23], [6, 15], [5, 17], [12, 17], [16, 31], [5, 25], [14, 37], [10, 17], [1, 11], [1, 13], [1, 9], [2, 9], [1, 11], [2, 11], [10, 31], [10, 21], [12, 31], [12, 21], [24, 31], [3, 21], [4, 21]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 233 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[33, 49], [6, 21], [8, 17], [3, 13], [1, 13], [2, 13], [6, 13], [1, 9], [2, 9], [21, 31], [20, 31], [11, 29], [57, 71], [11, 31], [11, 41], [5, 23], [28, 31], [5, 17], [3, 17], [4, 17], [8, 17], [6, 17], [10, 17], [23, 43], [3, 19]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 258 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[4, 19], [53, 79], [6, 19], [69, 89], [1, 11], [2, 11], [4, 17], [9, 41], [6, 17], [5, 31], [3, 15], [4, 15], [3, 17], [4, 17], [3, 13], [4, 13], [3, 17], [3, 19], [1, 9], [2, 9], [4, 23], [30, 33], [6, 23], [20, 31], [3, 17]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 283 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[4, 17], [1, 11], [2, 11], [1, 11], [2, 11], [8, 31], [13, 55], [8, 35], [3, 25], [4, 25], [3, 17], [4, 17], [36, 41], [5, 25], [8, 25], [11, 31], [1, 17], [2, 17], [7, 41], [5, 23], [9, 41], [26, 49], [5, 31], [1, 9], [2, 9]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 308 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[8, 31], [12, 23], [7, 31], [11, 49], [9, 31], [3, 23], [4, 23], [1, 15], [2, 15], [14, 31], [5, 25], [15, 47], [1, 13], [2, 13], [11, 31], [10, 25], [20, 47], [12, 25], [1, 11], [2, 11], [24, 47], [6, 15], [11, 41], [15, 49], [16, 49]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 333 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[22, 31], [7, 31], [11, 59], [9, 31], [7, 41], [19, 55], [9, 41], [3, 19], [1, 17], [1, 11], [2, 11], [6, 21], [6, 17], [10, 37], [42, 31], [1, 11], [2, 11], [4, 25], [6, 17], [6, 25], [134, 89], [10, 31], [11, 49], [7, 31], [16, 31]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 358 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 17], [4, 17], [31, 59], [6, 17], [15, 31], [13, 49], [13, 47], [5, 31], [22, 49], [18, 31], [1, 13], [2, 13], [10, 31], [11, 49], [1, 11], [2, 11], [4, 25], [13, 55], [6, 25], [20, 39], [11, 41], [1, 19], [2, 19], [24, 39], [1, 13]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 383 w15 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `8 ≤ n ≤ 407` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 407) : ∃ x, good n x = true := by
  by_cases c0 : n < 33
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 58
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 83
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 108
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 133
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 158
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 183
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 208
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 233
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 258
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 283
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 308
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 333
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 358
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 383
  · exact chunk ok14 len14 (by omega) (by omega)
  exact chunk ok15 len15 (by omega) (by omega)

end OMA.AOeisA234246_conjecture_5Tab

open OMA.AOeisA234246_conjecture_5Tab in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_5_R1.H1 := by
  intro n hn hne10 hne20 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact good_sound n w hn hne10 hne20 hw
