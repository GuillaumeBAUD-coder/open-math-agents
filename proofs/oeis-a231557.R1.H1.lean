import OMAReductions.R_oeis_a231557_R1
import Mathlib

-- Step oeis-a231557.R1.H1: hypothesis H1 of reduction oeis-a231557.R1
-- Credit: @prathameshnium. Finite check for 1 ≤ n ≤ 162.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 67108981.

/-! Step oeis-a231557.R1.H1. -/

namespace OMA.Aoeis_a231557Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `8194` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 8194 2

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
  have hnd := noDiv_sound p 8194 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [k] => (decide (0 < k) && (decide (k ≤ n) && isPrimeB (2 ^ k + (n - k))))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := core n w

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
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ (2 ^ k + (n - k)).Prime := by
  unfold core at h
  split at h
  next k =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨k, a0, a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1, …, 162`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1], [1], [2], [1], [2], [1], [4], [3], [2], [1], [2], [1], [6], [3], [2], [1], [2], [1], [4], [5], [2], [1], [8], [3], [4]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3], [2], [1], [2], [1], [4], [3], [8], [5], [2], [1], [10], [3], [2], [1], [2], [1], [6], [5], [2], [1], [4], [3], [4], [11]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 26 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2], [1], [20], [3], [4], [3], [2], [1], [2], [1], [4], [3], [8], [13], [2], [1], [4], [3], [2], [1], [2], [1], [6], [3], [12]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 51 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[5], [2], [1], [6], [5], [2], [1], [8], [3], [4], [5], [2], [1], [4], [7], [4], [3], [6], [11], [2], [1], [4], [3], [2], [1]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 76 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2], [1], [10], [3], [2], [1], [2], [1], [6], [5], [2], [1], [16], [9], [4], [9], [12], [7], [4], [7], [6], [3], [6], [5], [2]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 101 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1], [4], [9], [2], [1], [8], [3], [6], [3], [2], [1], [2], [1], [4], [5], [6], [7], [26], [3], [4], [3], [2], [1], [2], [1]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 126 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[4], [3], [6], [5], [2], [1], [10], [3], [12], [7], [2], [1]]
theorem len6 : w6.length = 12 := rfl
theorem ok6 : checkList 151 w6 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `1 ≤ n ≤ 162` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 162) : ∃ x, good n x = true := by
  by_cases c0 : n < 26
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 51
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 76
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 101
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 126
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 151
  · exact chunk ok5 len5 (by omega) (by omega)
  exact chunk ok6 len6 (by omega) (by omega)

end OMA.Aoeis_a231557Tab

open OMA.Aoeis_a231557Tab in
theorem OMA.solution : OMA.R_oeis_a231557_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
