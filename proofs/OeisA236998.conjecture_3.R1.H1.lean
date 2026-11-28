import OMAReductions.R_OeisA236998_conjecture_3_R1
import Mathlib

-- Step OeisA236998.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA236998.conjecture_3.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 401.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 0.

/-! Step OeisA236998.conjecture_3.R1.H1. -/

namespace OMA.AOeisA236998_conjecture_3Tab

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
  | [k, r] => (decide (0 < k) && (decide (k < n) && decide (k * (n - k).totient = r * r)))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := (Nat.beq n 4 || (Nat.beq n 7 || (Nat.beq n 60 || (Nat.beq n 199 || (Nat.beq n 267 || core n w)))))

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
    ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient) := by
  unfold core at h
  split at h
  next k r =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨k, a0, a1, (by unfold IsSquare; exact ⟨r, a2⟩)⟩
  next => exact absurd h Bool.false_ne_true

theorem good_sound (n : ℕ) (w : List ℕ) (hn : 1 < n) (h4 : n ≠ 4) (h7 : n ≠ 7) (h60 : n ≠ 60) (h199 : n ≠ 199) (h267 : n ≠ 267)
    (h : good n w = true) : ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient) := by
  simp only [good, Bool.or_eq_true] at h
  rcases h with h | h | h | h | h | h
  · rw [Nat.beq_eq] at h; exact absurd h h4
  · rw [Nat.beq_eq] at h; exact absurd h h7
  · rw [Nat.beq_eq] at h; exact absurd h h60
  · rw [Nat.beq_eq] at h; exact absurd h h199
  · rw [Nat.beq_eq] at h; exact absurd h h267
  · exact core_sound n w h

/-! One witness for each `n = 2, …, 401`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 1], [], [2, 2], [1, 2], [], [2, 2], [1, 2], [9, 3], [1, 2], [4, 4], [1, 2], [4, 4], [6, 6], [3, 6], [2, 4], [1, 4], [9, 6], [6, 6], [2, 6], [2, 4], [8, 8], [3, 6], [12, 12], [2, 4]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[8, 12], [8, 8], [2, 6], [5, 10], [3, 6], [2, 4], [1, 4], [18, 12], [1, 4], [4, 8], [18, 18], [1, 6], [3, 6], [2, 6], [1, 4], [18, 12], [9, 12], [4, 8], [3, 6], [8, 12], [32, 16], [12, 12], [1, 4], [16, 16], [6, 12]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[4, 8], [2, 8], [12, 12], [5, 10], [2, 6], [9, 12], [1, 6], [8, 16], [], [1, 4], [6, 12], [24, 24], [1, 6], [7, 14], [2, 8], [4, 12], [3, 12], [9, 12], [2, 8], [5, 10], [8, 16], [16, 24], [48, 24], [1, 6], [6, 12]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[1, 6], [4, 12], [16, 24], [4, 12], [8, 24], [2, 8], [9, 18], [6, 12], [9, 18], [1, 8], [6, 18], [8, 16], [4, 16], [6, 12], [18, 36], [10, 20], [2, 12], [9, 24], [40, 40], [6, 12], [2, 12], [2, 8], [8, 24], [32, 32], [14, 28]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1, 10], [6, 24], [2, 8], [4, 20], [49, 42], [3, 12], [3, 12], [1, 6], [8, 16], [22, 44], [3, 18], [2, 12], [15, 30], [1, 6], [12, 24], [9, 18], [4, 12], [2, 12], [7, 28], [12, 36], [2, 8], [9, 18], [12, 24], [6, 24], [1, 10]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 6], [5, 20], [1, 8], [4, 12], [27, 36], [4, 16], [3, 12], [9, 30], [9, 18], [3, 18], [1, 8], [18, 24], [15, 30], [4, 16], [14, 42], [10, 20], [3, 12], [16, 32], [9, 24], [50, 40], [3, 12], [2, 12], [11, 22], [2, 12], [25, 30]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[7, 28], [18, 36], [2, 12], [81, 54], [8, 24], [6, 30], [52, 52], [3, 12], [8, 24], [1, 8], [36, 36], [49, 42], [4, 16], [2, 18], [18, 36], [27, 36], [6, 18], [5, 20], [5, 20], [1, 8], [36, 48], [28, 56], [3, 18], [24, 60], [16, 32]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[24, 48], [32, 48], [9, 24], [12, 24], [5, 20], [44, 44], [3, 12], [2, 12], [20, 40], [1, 12], [75, 60], [14, 28], [4, 24], [8, 24], [99, 66], [2, 12], [1, 8], [9, 36], [25, 40], [3, 24], [10, 40], [1, 14], [], [6, 24], [4, 28]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[50, 60], [1, 10], [48, 48], [1, 8], [4, 20], [27, 36], [4, 16], [45, 60], [25, 60], [9, 30], [70, 70], [3, 12], [5, 30], [10, 40], [27, 54], [21, 42], [2, 12], [24, 48], [1, 12], [3, 18], [5, 30], [4, 24], [2, 12], [5, 20], [45, 90]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[25, 50], [9, 36], [20, 60], [2, 12], [75, 60], [24, 48], [7, 28], [18, 36], [16, 48], [2, 12], [20, 60], [26, 52], [7, 28], [18, 36], [1, 8], [8, 24], [75, 60], [4, 16], [2, 18], [18, 36], [96, 120], [24, 48], [9, 24], [98, 84], [1, 10]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[18, 36], [6, 36], [2, 12], [30, 60], [15, 60], [2, 16], [1, 16], [9, 30], [8, 24], [4, 32], [24, 48], [8, 32], [8, 32], [6, 36], [6, 24], [], [14, 42], [3, 18], [18, 36], [24, 72], [2, 12], [16, 64], [1, 12], [25, 50], [36, 48]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 20], [8, 24], [21, 42], [8, 32], [46, 92], [9, 36], [8, 40], [5, 30], [75, 60], [1, 12], [32, 64], [18, 36], [4, 24], [18, 48], [40, 100], [54, 72], [1, 12], [3, 24], [63, 84], [4, 24], [1, 12], [22, 44], [20, 60], [4, 24], [9, 36]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5, 30], [12, 48], [24, 48], [1, 12], [17, 68], [32, 80], [4, 24], [36, 72], [25, 60], [8, 40], [6, 24], [9, 36], [48, 72], [21, 42], [1, 12], [20, 60], [6, 24], [4, 24], [15, 60], [18, 60], [2, 16], [121, 110], [9, 36], [2, 24], [24, 60]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3, 18], [2, 18], [25, 60], [24, 48], [8, 48], [36, 72], [6, 36], [8, 36], [5, 20], [12, 36], [64, 96], [10, 40], [6, 36], [15, 60], [18, 72], [2, 16], [96, 144], [3, 30], [3, 18], [69, 138], [60, 120], [8, 32], [6, 42], [20, 40], [24, 72]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[32, 64], [12, 60], [12, 36], [7, 28], [11, 44], [6, 36], [18, 48], [80, 120], [3, 24], [121, 88], [10, 40], [144, 144], [49, 84], [1, 12], [6, 24], [2, 24], [4, 24], [12, 48], [50, 80], [1, 12], [32, 64], [8, 48], [4, 24], [22, 88], [28, 56]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 20], [84, 84], [9, 36], [16, 48], [1, 12], [20, 60], [8, 40], [4, 24], [60, 120], [2, 16], [54, 108], [7, 42], [3, 24], [12, 36], [3, 24], [8, 32], [18, 60], [7, 42], [1, 14], [6, 24], [32, 96], [4, 28], [38, 114], [12, 48], [66, 132]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 401` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 401) : ∃ x, good n x = true := by
  by_cases c0 : n < 27
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 52
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 77
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 102
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 127
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 152
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 177
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 202
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 227
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 252
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 277
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 302
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 327
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 352
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 377
  · exact chunk ok14 len14 (by omega) (by omega)
  exact chunk ok15 len15 (by omega) (by omega)

end OMA.AOeisA236998_conjecture_3Tab

open OMA.AOeisA236998_conjecture_3Tab in
theorem OMA.solution : OMA.R_OeisA236998_conjecture_3_R1.H1 := by
  intro n hn h4 h7 h60 h199 h267 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact good_sound n w hn h4 h7 h60 h199 h267 hw
