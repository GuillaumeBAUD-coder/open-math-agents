import OMAReductions.R_oeis_a230037_R1
import Mathlib

-- Step oeis-a230037.R1.H1: hypothesis H1 of reduction oeis-a230037.R1
-- Credit: @prathameshnium. Finite check for 3 ≤ n ≤ 1002.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 6451.

/-! Step oeis-a230037.R1.H1. -/

namespace OMA.Aoeis_a230037Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `82` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 82 2

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
  have hnd := noDiv_sound p 82 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (x ≤ y) && (decide (y ≤ z) && (decide (x + y + z = n) && (isPrimeB (6 * x - 1) && (isPrimeB (6 * x + 1) && (isPrimeB (6 * y - 1) && (isPrimeB (6 * y + 1) && (isPrimeB (6 * z - 1) && (isPrimeB (6 * z + 1) && (isPrimeB (6 * x * y - 1) && isPrimeB (6 * x * y + 1))))))))))))
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
    ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z + 1).Prime ∧ (6 * x * y - 1).Prime ∧ (6 * x * y + 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8, isPrimeB_sound _ a9, isPrimeB_sound _ a10, isPrimeB_sound _ a11⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 3, …, 1002`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 2, 3], [1, 1, 5], [1, 2, 5], [1, 1, 7], [1, 2, 7], [1, 3, 7], [1, 1, 10], [1, 2, 10], [1, 1, 12], [1, 2, 12], [1, 3, 12], [2, 5, 10], [1, 5, 12], [1, 1, 17], [1, 1, 18], [1, 2, 18], [1, 3, 18], [1, 5, 17], [1, 5, 18], [1, 1, 23], [1, 2, 23], [1, 1, 25]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 3 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[1, 2, 25], [1, 3, 25], [1, 12, 17], [1, 5, 25], [1, 1, 30], [1, 2, 30], [1, 1, 32], [1, 1, 33], [1, 2, 33], [1, 3, 33], [1, 5, 32], [1, 5, 33], [1, 1, 38], [1, 2, 38], [1, 1, 40], [1, 2, 40], [1, 3, 40], [1, 12, 32], [1, 5, 40], [1, 1, 45], [1, 2, 45], [1, 1, 47], [1, 2, 47], [1, 3, 47], [1, 18, 33]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 28 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1, 5, 47], [1, 1, 52], [1, 2, 52], [1, 3, 52], [1, 18, 38], [1, 5, 52], [1, 18, 40], [1, 1, 58], [1, 2, 58], [1, 3, 58], [1, 10, 52], [1, 5, 58], [1, 12, 52], [1, 7, 58], [1, 33, 33], [5, 5, 58], [1, 10, 58], [1, 17, 52], [1, 12, 58], [1, 1, 70], [1, 2, 70], [1, 1, 72], [1, 2, 72], [1, 3, 72], [1, 18, 58]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 53 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[1, 5, 72], [1, 1, 77], [1, 2, 77], [1, 3, 77], [1, 23, 58], [1, 5, 77], [1, 25, 58], [1, 7, 77], [1, 33, 52], [5, 5, 77], [1, 10, 77], [1, 1, 87], [1, 2, 87], [1, 3, 87], [1, 33, 58], [1, 5, 87], [1, 23, 70], [1, 7, 87], [1, 18, 77], [1, 1, 95], [1, 2, 95], [1, 3, 95], [1, 12, 87], [1, 5, 95], [1, 1, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 78 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1, 2, 100], [1, 3, 100], [1, 1, 103], [1, 2, 103], [1, 3, 103], [1, 7, 100], [1, 1, 107], [1, 2, 107], [1, 3, 107], [1, 1, 110], [1, 2, 110], [1, 3, 110], [1, 7, 107], [1, 5, 110], [1, 58, 58], [1, 7, 110], [1, 18, 100], [1, 12, 107], [1, 10, 110], [1, 18, 103], [1, 12, 110], [1, 23, 100], [1, 17, 107], [1, 18, 107], [1, 23, 103]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 103 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 17, 110], [1, 18, 110], [1, 52, 77], [1, 23, 107], [7, 25, 100], [1, 25, 107], [1, 23, 110], [1, 47, 87], [1, 25, 110], [1, 1, 135], [1, 2, 135], [1, 1, 137], [1, 1, 138], [1, 2, 138], [1, 3, 138], [1, 5, 137], [1, 5, 138], [1, 1, 143], [1, 2, 143], [1, 3, 143], [1, 10, 137], [1, 1, 147], [1, 2, 147], [1, 3, 147], [7, 10, 135]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 128 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[1, 5, 147], [1, 10, 143], [1, 7, 147], [1, 12, 143], [1, 18, 138], [1, 10, 147], [1, 23, 135], [1, 12, 147], [1, 17, 143], [1, 18, 143], [1, 25, 137], [1, 25, 138], [1, 17, 147], [1, 18, 147], [1, 23, 143], [1, 30, 137], [1, 25, 143], [1, 32, 137], [1, 23, 147], [1, 1, 170], [1, 2, 170], [1, 1, 172], [1, 2, 172], [1, 3, 172], [1, 1, 175]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 153 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[1, 2, 175], [1, 1, 177], [1, 2, 177], [1, 3, 177], [1, 38, 143], [1, 5, 177], [1, 1, 182], [1, 2, 182], [1, 3, 182], [5, 5, 177], [1, 5, 182], [1, 18, 170], [1, 7, 182], [1, 18, 172], [5, 5, 182], [1, 10, 182], [1, 1, 192], [1, 2, 192], [1, 3, 192], [1, 58, 138], [1, 5, 192], [1, 23, 175], [1, 7, 192], [1, 18, 182], [1, 58, 143]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 178 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[1, 10, 192], [1, 33, 170], [1, 12, 192], [1, 23, 182], [1, 1, 205], [1, 2, 205], [1, 3, 205], [1, 17, 192], [1, 5, 205], [2, 5, 205], [1, 7, 205], [1, 38, 175], [1, 1, 213], [1, 2, 213], [1, 1, 215], [1, 2, 215], [1, 1, 217], [1, 2, 217], [1, 3, 217], [1, 1, 220], [1, 2, 220], [1, 3, 220], [1, 7, 217], [1, 5, 220], [2, 5, 220]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 203 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[1, 7, 220], [1, 23, 205], [1, 12, 217], [1, 10, 220], [1, 18, 213], [1, 12, 220], [1, 18, 215], [1, 17, 217], [1, 18, 217], [1, 23, 213], [1, 17, 220], [1, 18, 220], [1, 1, 238], [1, 2, 238], [1, 3, 238], [1, 25, 217], [1, 1, 242], [1, 2, 242], [1, 3, 242], [1, 33, 213], [1, 5, 242], [1, 1, 247], [1, 1, 248], [1, 2, 248], [1, 3, 248]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 228 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[1, 5, 247], [1, 5, 248], [1, 7, 247], [1, 7, 248], [1, 18, 238], [1, 10, 247], [1, 10, 248], [1, 12, 247], [1, 12, 248], [1, 23, 238], [1, 45, 217], [1, 25, 238], [1, 17, 247], [1, 17, 248], [1, 18, 248], [1, 25, 242], [1, 30, 238], [1, 1, 268], [1, 2, 268], [1, 1, 270], [1, 2, 270], [1, 3, 270], [1, 32, 242], [1, 5, 270], [1, 38, 238]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 253 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[1, 7, 270], [1, 10, 268], [1, 1, 278], [1, 2, 278], [1, 3, 278], [1, 12, 270], [1, 5, 278], [1, 1, 283], [1, 2, 283], [1, 3, 283], [1, 17, 270], [1, 1, 287], [1, 2, 287], [1, 3, 287], [1, 23, 268], [1, 5, 287], [1, 10, 283], [1, 7, 287], [1, 12, 283], [1, 18, 278], [1, 10, 287], [1, 30, 268], [1, 1, 298], [1, 2, 298], [1, 3, 298]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 278 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[1, 32, 270], [1, 5, 298], [1, 17, 287], [1, 7, 298], [1, 23, 283], [1, 87, 220], [1, 10, 298], [1, 137, 172], [1, 12, 298], [1, 33, 278], [1, 25, 287], [1, 1, 312], [1, 1, 313], [1, 2, 313], [1, 3, 313], [1, 5, 312], [1, 5, 313], [1, 7, 312], [1, 7, 313], [1, 23, 298], [1, 10, 312], [1, 1, 322], [1, 2, 322], [1, 3, 322], [1, 1, 325]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 303 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[1, 2, 325], [1, 3, 325], [1, 7, 322], [1, 5, 325], [1, 18, 313], [1, 7, 325], [1, 95, 238], [1, 1, 333], [1, 2, 333], [1, 3, 333], [1, 12, 325], [1, 5, 333], [1, 1, 338], [1, 2, 338], [1, 3, 338], [1, 17, 325], [1, 5, 338], [1, 32, 312], [1, 7, 338], [1, 33, 313], [1, 25, 322], [1, 1, 347], [1, 1, 348], [1, 2, 348], [1, 3, 348]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 328 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[1, 5, 347], [1, 1, 352], [1, 2, 352], [1, 3, 352], [1, 1, 355], [1, 2, 355], [1, 1, 357], [1, 2, 357], [1, 3, 357], [1, 23, 338], [1, 5, 357], [1, 25, 338], [1, 7, 357], [1, 10, 355], [1, 18, 348], [1, 10, 357], [1, 30, 338], [1, 12, 357], [1, 18, 352], [1, 23, 348], [1, 17, 355], [1, 18, 355], [1, 1, 373], [1, 2, 373], [1, 3, 373]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 353 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[1, 25, 352], [1, 5, 373], [1, 1, 378], [1, 2, 378], [1, 3, 378], [1, 25, 357], [1, 5, 378], [1, 32, 352], [1, 7, 378], [1, 1, 385], [1, 2, 385], [1, 3, 385], [1, 32, 357], [1, 5, 385], [1, 1, 390], [1, 2, 390], [1, 3, 390], [1, 47, 347], [1, 5, 390], [1, 18, 378], [1, 7, 390], [1, 1, 397], [1, 2, 397], [1, 3, 397], [1, 23, 378]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 378 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[1, 5, 397], [1, 18, 385], [1, 7, 397], [1, 32, 373], [1, 33, 373], [1, 10, 397], [1, 18, 390], [1, 12, 397], [1, 25, 385], [1, 33, 378], [1, 87, 325], [1, 23, 390], [1, 17, 397], [1, 18, 397], [1, 38, 378], [1, 32, 385], [1, 33, 385], [1, 72, 347], [1, 23, 397], [1, 138, 283], [1, 25, 397], [1, 33, 390], [1, 72, 352], [1, 40, 385], [1, 1, 425]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 403 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[1, 2, 425], [1, 3, 425], [1, 32, 397], [1, 5, 425], [1, 58, 373], [1, 7, 425], [1, 1, 432], [1, 2, 432], [1, 3, 432], [1, 58, 378], [1, 5, 432], [1, 100, 338], [1, 7, 432], [1, 107, 333], [1, 103, 338], [1, 10, 432], [1, 18, 425], [1, 1, 443], [1, 2, 443], [1, 3, 443], [1, 95, 352], [1, 5, 443], [1, 1, 448], [1, 2, 448], [1, 3, 448]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 428 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[1, 95, 357], [1, 1, 452], [1, 2, 452], [1, 3, 452], [1, 1, 455], [1, 2, 455], [1, 3, 455], [1, 7, 452], [1, 5, 455], [1, 18, 443], [1, 7, 455], [1, 38, 425], [1, 12, 452], [1, 10, 455], [1, 1, 465], [1, 2, 465], [1, 1, 467], [1, 2, 467], [1, 3, 467], [1, 23, 448], [1, 5, 467], [1, 18, 455], [1, 7, 467], [1, 10, 465], [1, 33, 443]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 453 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1, 10, 467], [1, 23, 455], [1, 12, 467], [1, 25, 455], [1, 33, 448], [1, 17, 465], [1, 18, 465], [1, 17, 467], [1, 18, 467], [1, 38, 448], [1, 32, 455], [1, 23, 465], [1, 137, 352], [1, 23, 467], [1, 143, 348], [1, 25, 467], [1, 38, 455], [1, 137, 357], [1, 30, 465], [1, 1, 495], [1, 2, 495], [1, 3, 495], [1, 32, 467], [1, 5, 495], [1, 1, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 478 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[1, 2, 500], [1, 3, 500], [1, 52, 452], [1, 5, 500], [1, 58, 448], [1, 7, 500], [1, 135, 373], [1, 77, 432], [1, 10, 500], [1, 138, 373], [1, 12, 500], [1, 18, 495], [1, 47, 467], [1, 72, 443], [1, 138, 378], [1, 17, 500], [1, 18, 500], [1, 52, 467], [1, 25, 495], [1, 1, 520], [1, 2, 520], [1, 3, 520], [1, 72, 452], [1, 5, 520], [1, 213, 313]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 503 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[1, 7, 520], [1, 33, 495], [1, 1, 528], [1, 2, 528], [1, 3, 528], [1, 12, 520], [1, 5, 528], [1, 137, 397], [1, 7, 528], [1, 238, 298], [1, 17, 520], [1, 10, 528], [1, 72, 467], [1, 12, 528], [5, 215, 322], [1, 47, 495], [1, 1, 542], [1, 1, 543], [1, 2, 543], [1, 3, 543], [1, 5, 542], [1, 5, 543], [1, 7, 542], [1, 7, 543], [1, 1, 550]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 528 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[1, 2, 550], [1, 3, 550], [1, 12, 542], [1, 5, 550], [1, 1, 555], [1, 2, 555], [1, 3, 555], [1, 17, 542], [1, 5, 555], [1, 1, 560], [1, 2, 560], [1, 1, 562], [1, 2, 562], [1, 3, 562], [1, 1, 565], [1, 2, 565], [1, 3, 565], [1, 7, 562], [1, 5, 565], [1, 238, 333], [1, 7, 565], [1, 18, 555], [1, 12, 562], [1, 10, 565], [1, 33, 543]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 553 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1, 12, 565], [1, 1, 577], [1, 1, 578], [1, 2, 578], [1, 3, 578], [1, 5, 577], [1, 5, 578], [1, 7, 577], [1, 7, 578], [1, 58, 528], [1, 10, 577], [1, 10, 578], [1, 1, 588], [1, 2, 588], [1, 1, 590], [1, 2, 590], [1, 3, 590], [1, 1, 593], [1, 2, 593], [1, 3, 593], [1, 7, 590], [1, 1, 597], [1, 2, 597], [1, 3, 597], [1, 23, 578]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 578 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[1, 5, 597], [1, 10, 593], [1, 7, 597], [1, 12, 593], [1, 18, 588], [1, 10, 597], [1, 18, 590], [1, 12, 597], [1, 17, 593], [1, 18, 593], [1, 47, 565], [1, 1, 612], [1, 2, 612], [1, 3, 612], [1, 23, 593], [1, 5, 612], [1, 25, 593], [1, 7, 612], [1, 23, 597], [1, 33, 588], [1, 10, 612], [1, 30, 593], [1, 12, 612], [1, 32, 593], [1, 33, 593]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 603 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[1, 30, 597], [1, 38, 590], [1, 1, 628], [1, 2, 628], [1, 3, 628], [1, 70, 562], [1, 5, 628], [1, 72, 562], [1, 7, 628], [1, 58, 578], [1, 25, 612], [1, 1, 637], [1, 2, 637], [1, 3, 637], [1, 268, 373], [1, 5, 637], [1, 1, 642], [1, 2, 642], [1, 3, 642], [1, 18, 628], [1, 5, 642], [1, 58, 590], [1, 7, 642], [1, 38, 612], [1, 23, 628]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 628 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1, 10, 642], [1, 25, 628], [1, 1, 653], [1, 2, 653], [1, 1, 655], [1, 2, 655], [1, 3, 655], [1, 17, 642], [1, 5, 655], [1, 33, 628], [1, 7, 655], [1, 10, 653], [1, 52, 612], [1, 10, 655], [1, 38, 628], [1, 12, 655], [1, 1, 667], [1, 2, 667], [1, 3, 667], [1, 1, 670], [1, 2, 670], [1, 3, 670], [1, 7, 667], [1, 5, 670], [1, 1, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 653 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[1, 2, 675], [1, 3, 675], [1, 12, 667], [1, 5, 675], [1, 103, 578], [1, 7, 675], [1, 1, 682], [1, 2, 682], [1, 3, 682], [1, 33, 653], [1, 5, 682], [1, 18, 670], [1, 1, 688], [1, 2, 688], [1, 3, 688], [1, 10, 682], [1, 5, 688], [1, 1, 693], [1, 2, 693], [1, 3, 693], [1, 30, 667], [1, 5, 693], [1, 17, 682], [1, 7, 693], [2, 110, 590]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 678 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[1, 32, 670], [1, 10, 693], [1, 1, 703], [1, 2, 703], [1, 1, 705], [1, 2, 705], [1, 1, 707], [1, 2, 707], [1, 3, 707], [1, 1, 710], [1, 2, 710], [1, 1, 712], [1, 2, 712], [1, 3, 712], [1, 23, 693], [1, 5, 712], [1, 25, 693], [1, 7, 712], [1, 10, 710], [1, 18, 703], [1, 10, 712], [1, 18, 705], [1, 1, 723], [1, 2, 723], [1, 3, 723]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 703 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[1, 17, 710], [1, 5, 723], [1, 17, 712], [1, 7, 723], [1, 38, 693], [1, 25, 707], [1, 10, 723], [1, 52, 682], [1, 12, 723], [1, 33, 703], [1, 25, 712], [1, 1, 737], [1, 2, 737], [1, 3, 737], [1, 18, 723], [1, 5, 737], [1, 33, 710], [1, 7, 737], [1, 33, 712], [1, 23, 723], [1, 10, 737], [1, 1, 747], [1, 2, 747], [1, 3, 747], [1, 58, 693]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 728 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[1, 5, 747], [1, 30, 723], [1, 1, 753], [1, 2, 753], [1, 3, 753], [1, 10, 747], [1, 5, 753], [1, 1, 758], [1, 2, 758], [1, 3, 758], [1, 25, 737], [1, 5, 758], [1, 17, 747], [1, 7, 758], [1, 138, 628], [1, 30, 737], [1, 10, 758], [1, 32, 737], [1, 12, 758], [1, 18, 753], [1, 25, 747], [1, 70, 703], [1, 1, 773], [1, 2, 773], [1, 1, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 753 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[1, 2, 775], [1, 3, 775], [1, 32, 747], [1, 5, 775], [1, 23, 758], [1, 7, 775], [1, 10, 773], [1, 47, 737], [1, 10, 775], [1, 33, 753], [1, 12, 775], [1, 1, 787], [1, 2, 787], [1, 3, 787], [1, 18, 773], [1, 5, 787], [1, 18, 775], [1, 7, 787], [1, 58, 737], [1, 23, 773], [1, 10, 787], [1, 23, 775], [1, 1, 798], [1, 2, 798], [1, 1, 800]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 778 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[1, 2, 800], [1, 3, 800], [1, 17, 787], [1, 5, 800], [1, 33, 773], [1, 7, 800], [1, 10, 798], [1, 72, 737], [1, 10, 800], [1, 38, 773], [1, 12, 800], [1, 38, 775], [1, 77, 737], [1, 17, 798], [1, 18, 798], [1, 17, 800], [1, 18, 800], [1, 32, 787], [1, 33, 787], [1, 23, 798], [1, 47, 775], [1, 1, 822], [1, 2, 822], [1, 3, 822], [1, 103, 723]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 803 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[1, 5, 822], [1, 30, 798], [1, 1, 828], [1, 2, 828], [1, 3, 828], [1, 10, 822], [1, 5, 828], [1, 12, 822], [1, 7, 828], [1, 1, 835], [1, 2, 835], [1, 1, 837], [1, 2, 837], [1, 3, 837], [1, 138, 703], [1, 5, 837], [1, 45, 798], [1, 7, 837], [1, 10, 835], [1, 18, 828], [1, 10, 837], [1, 95, 753], [1, 12, 837], [1, 52, 798], [1, 1, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 828 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[1, 2, 850], [1, 3, 850], [1, 17, 837], [1, 5, 850], [1, 58, 798], [1, 7, 850], [1, 23, 835], [1, 72, 787], [1, 10, 850], [1, 33, 828], [1, 12, 850], [1, 110, 753], [1, 77, 787], [1, 30, 835], [1, 38, 828], [1, 17, 850], [1, 18, 850], [1, 32, 837], [1, 33, 837], [1, 278, 593], [1, 72, 800], [1, 1, 872], [1, 2, 872], [1, 3, 872], [1, 103, 773]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 853 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[1, 5, 872], [1, 103, 775], [1, 7, 872], [1, 30, 850], [1, 1, 880], [1, 2, 880], [1, 3, 880], [1, 12, 872], [1, 5, 880], [1, 58, 828], [1, 7, 880], [1, 38, 850], [1, 17, 872], [1, 10, 880], [1, 138, 753], [1, 12, 880], [1, 58, 835], [1, 72, 822], [1, 23, 872], [1, 138, 758], [1, 17, 880], [1, 18, 880], [1, 77, 822], [1, 72, 828], [1, 103, 798]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 878 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[1, 30, 872], [1, 23, 880], [1, 1, 903], [1, 2, 903], [1, 3, 903], [1, 70, 837], [1, 1, 907], [1, 2, 907], [1, 3, 907], [1, 138, 773], [1, 5, 907], [1, 10, 903], [1, 1, 913], [1, 2, 913], [1, 3, 913], [1, 10, 907], [1, 1, 917], [1, 2, 917], [1, 3, 917], [1, 1, 920], [1, 2, 920], [1, 3, 920], [1, 7, 917], [1, 5, 920], [1, 23, 903]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 903 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[1, 7, 920], [1, 25, 903], [1, 12, 917], [1, 10, 920], [1, 18, 913], [1, 12, 920], [1, 30, 903], [1, 17, 917], [1, 18, 917], [1, 23, 913], [1, 17, 920], [1, 18, 920], [1, 32, 907], [1, 23, 917], [1, 1, 940], [1, 2, 940], [1, 1, 942], [1, 1, 943], [1, 2, 943], [1, 3, 943], [1, 5, 942], [1, 5, 943], [1, 7, 942], [1, 7, 943], [1, 38, 913]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 928 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[1, 10, 942], [1, 10, 943], [1, 12, 942], [1, 12, 943], [1, 268, 688], [1, 17, 940], [1, 1, 957], [1, 2, 957], [1, 3, 957], [1, 18, 943], [1, 5, 957], [1, 23, 940], [1, 7, 957], [1, 23, 942], [1, 23, 943], [1, 10, 957], [1, 25, 943], [1, 12, 957], [1, 30, 940], [1, 58, 913], [1, 30, 942], [1, 30, 943], [1, 17, 957], [1, 18, 957], [1, 1, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 953 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[1, 2, 975], [1, 3, 975], [1, 1, 978], [1, 2, 978], [1, 1, 980], [1, 2, 980], [1, 3, 980], [1, 77, 907], [1, 5, 980], [1, 213, 773], [1, 7, 980], [1, 10, 978], [1, 32, 957], [1, 10, 980], [1, 238, 753], [1, 12, 980], [1, 18, 975], [1, 52, 942], [1, 17, 978], [1, 18, 978], [1, 17, 980], [1, 18, 980], [1, 177, 822], [1, 25, 975], [1, 23, 978]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 978 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `3 ≤ n ≤ 1002` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 1002) : ∃ x, good n x = true := by
  by_cases c0 : n < 28
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 53
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 78
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 103
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 128
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 153
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 178
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 203
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 228
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 253
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 278
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 303
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 328
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 353
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 378
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 403
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 428
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 453
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 478
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 503
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 528
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 553
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 578
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 603
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 628
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 653
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 678
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 703
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 728
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 753
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 778
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 803
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 828
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 853
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 878
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 903
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 928
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 953
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 978
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a230037Tab

open OMA.Aoeis_a230037Tab in
theorem OMA.solution : OMA.R_oeis_a230037_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
