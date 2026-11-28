import OMAReductions.R_oeis_a224030_R1
import Mathlib

-- Step oeis-a224030.R1.H1: hypothesis H1 of reduction oeis-a224030.R1
-- Credit: @prathameshnium. Finite check for 5 ≤ n ≤ 217.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 20436751.

/-! Step oeis-a224030.R1.H1. -/

namespace OMA.Aoeis_a224030Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `4522` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 4522 2

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
  have hnd := noDiv_sound p 4522 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [k] => (decide (0 < k) && (decide (k < n) && (isPrimeB (2 * n + k) && isPrimeB (2 * n ^ 3 + k ^ 3))))
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
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * n + k) ∧ Nat.Prime (2 * n ^ 3 + k ^ 3) := by
  unfold core at h
  split at h
  next k =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨k, a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 5, …, 217`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1], [1], [5], [3], [1], [3], [1], [5], [3], [9], [11], [5], [7], [5], [9], [1], [1], [3], [7], [5], [3], [1], [7], [5], [1]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 5 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[1], [5], [3], [5], [11], [1], [29], [15], [33], [19], [23], [19], [5], [15], [1], [7], [9], [3], [13], [15], [3], [5], [3], [33], [31]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 30 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[29], [39], [23], [33], [19], [7], [29], [3], [47], [9], [9], [49], [5], [13], [11], [9], [15], [7], [3], [31], [7], [5], [27], [35], [21]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 55 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[13], [19], [27], [25], [11], [3], [1], [5], [5], [21], [47], [11], [13], [5], [5], [1], [1], [45], [37], [1], [11], [9], [35], [33], [55]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 80 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[19], [21], [15], [7], [5], [3], [1], [3], [25], [29], [11], [19], [7], [3], [55], [1], [39], [13], [5], [15], [19], [19], [3], [25], [19]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 105 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[33], [19], [5], [3], [1], [7], [35], [3], [5], [35], [1], [31], [23], [45], [25], [21], [19], [13], [15], [81], [13], [5], [27], [5], [5]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 130 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[3], [5], [75], [57], [41], [33], [75], [25], [27], [9], [1], [65], [3], [13], [29], [7], [25], [53], [3], [11], [23], [91], [65], [33], [21]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 155 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[7], [101], [37], [7], [5], [27], [1], [5], [25], [5], [21], [1], [17], [45], [9], [19], [39], [15], [5], [11], [9], [29], [17], [13], [1]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 180 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[11], [49], [5], [17], [15], [23], [45], [25], [23], [15], [3], [25], [5]]
theorem len8 : w8.length = 13 := rfl
theorem ok8 : checkList 205 w8 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `5 ≤ n ≤ 217` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 5 ≤ n) (h2 : n ≤ 217) : ∃ x, good n x = true := by
  by_cases c0 : n < 30
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 55
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 80
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 105
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 130
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 155
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 180
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 205
  · exact chunk ok7 len7 (by omega) (by omega)
  exact chunk ok8 len8 (by omega) (by omega)

end OMA.Aoeis_a224030Tab

open OMA.Aoeis_a224030Tab in
theorem OMA.solution : OMA.R_oeis_a224030_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
