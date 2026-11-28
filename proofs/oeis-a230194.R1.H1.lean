import OMAReductions.R_oeis_a230194_R1
import Mathlib

-- Step oeis-a230194.R1.H1: hypothesis H1 of reduction oeis-a230194.R1
-- Credit: @prathameshnium. Finite check for 6 ≤ n ≤ 1005.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5879.

/-! Step oeis-a230194.R1.H1. -/

namespace OMA.Aoeis_a230194Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `78` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 78 2

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
  have hnd := noDiv_sound p 78 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && (isPrimeB (6 * x - 1) && (isPrimeB (6 * x + 1) && (isPrimeB (6 * x - 5) && (isPrimeB (6 * x + 5) && (isPrimeB (6 * y - 1) && (isPrimeB (6 * y - 5) && (isPrimeB (6 * y + 5) && (isPrimeB (6 * (x + y) + 5) && (isPrimeB (6 * z - 1) && (isPrimeB (6 * z - 5) && isPrimeB (6 * z + 5)))))))))))))))
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
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * x - 5).Prime ∧ (6 * x + 5).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y - 5).Prime ∧ (6 * y + 5).Prime ∧ (6 * (x + y) + 5).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z - 5).Prime ∧ (6 * z + 5).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8, isPrimeB_sound _ a9, isPrimeB_sound _ a10, isPrimeB_sound _ a11, isPrimeB_sound _ a12, isPrimeB_sound _ a13, isPrimeB_sound _ a14⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 6, …, 1005`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2, 2], [2, 2, 3], [2, 2, 4], [2, 4, 3], [2, 4, 4], [2, 2, 7], [2, 2, 8], [2, 4, 7], [2, 4, 8], [3, 4, 8], [2, 7, 7], [2, 7, 8], [2, 2, 14], [2, 14, 3], [2, 4, 14], [2, 2, 17], [2, 2, 18], [2, 4, 17], [2, 4, 18], [3, 4, 18], [2, 2, 22], [2, 7, 18], [2, 4, 22], [3, 4, 22], [2, 14, 14]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 6 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[2, 7, 22], [2, 2, 28], [2, 14, 17], [2, 4, 28], [3, 4, 28], [7, 7, 22], [2, 7, 28], [2, 14, 22], [3, 8, 28], [18, 4, 18], [2, 22, 17], [2, 2, 38], [2, 2, 39], [2, 4, 38], [2, 4, 39], [2, 22, 22], [2, 7, 38], [2, 7, 39], [2, 39, 8], [3, 8, 39], [7, 22, 22], [2, 22, 28], [3, 28, 22], [2, 14, 38], [2, 14, 39]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 31 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 2, 52], [7, 22, 28], [2, 4, 52], [2, 39, 18], [3, 18, 39], [2, 7, 52], [2, 22, 38], [2, 2, 59], [3, 39, 22], [2, 4, 59], [3, 4, 59], [7, 22, 38], [2, 2, 64], [2, 39, 28], [2, 4, 64], [3, 4, 64], [17, 52, 3], [2, 7, 64], [2, 64, 8], [2, 14, 59], [2, 22, 52], [7, 52, 18], [2, 2, 74], [2, 39, 38], [2, 4, 74]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 56 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[2, 2, 77], [2, 77, 3], [2, 4, 77], [2, 64, 18], [3, 8, 74], [2, 7, 77], [2, 77, 8], [2, 2, 84], [2, 84, 3], [2, 4, 84], [3, 4, 84], [7, 77, 8], [2, 7, 84], [2, 64, 28], [3, 8, 84], [2, 77, 17], [2, 77, 18], [2, 22, 74], [3, 74, 22], [2, 14, 84], [2, 22, 77], [7, 77, 18], [2, 84, 17], [2, 64, 38], [2, 39, 64]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 81 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 39, 64], [2, 77, 28], [2, 22, 84], [7, 64, 38], [7, 39, 64], [7, 52, 52], [2, 2, 108], [7, 22, 84], [2, 4, 108], [2, 39, 74], [3, 39, 74], [2, 2, 113], [2, 39, 77], [2, 4, 113], [3, 4, 113], [17, 52, 52], [2, 7, 113], [3, 113, 7], [2, 14, 108], [2, 39, 84], [3, 39, 84], [7, 7, 113], [2, 74, 52], [2, 14, 113], [2, 64, 64]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 106 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 77, 52], [2, 22, 108], [3, 113, 17], [3, 18, 113], [2, 74, 59], [3, 74, 59], [2, 22, 113], [2, 77, 59], [3, 28, 108], [2, 64, 74], [3, 74, 64], [7, 22, 113], [2, 64, 77], [3, 28, 113], [2, 84, 59], [17, 52, 77], [2, 2, 143], [3, 143, 2], [2, 4, 143], [2, 64, 84], [2, 2, 147], [2, 7, 143], [2, 4, 147], [2, 39, 113], [3, 39, 113]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 131 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 7, 147], [7, 7, 143], [3, 8, 147], [2, 14, 143], [2, 74, 84], [2, 2, 157], [7, 147, 8], [2, 4, 157], [3, 4, 157], [7, 74, 84], [2, 2, 162], [2, 22, 143], [2, 4, 162], [3, 4, 162], [2, 84, 84], [2, 7, 162], [7, 22, 143], [2, 2, 169], [2, 64, 108], [2, 4, 169], [3, 4, 169], [7, 162, 8], [2, 7, 169], [2, 64, 113], [3, 8, 169]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 156 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 22, 157], [7, 147, 28], [3, 18, 162], [2, 39, 143], [2, 14, 169], [2, 2, 182], [2, 2, 183], [2, 4, 182], [2, 4, 183], [3, 4, 183], [2, 7, 182], [2, 7, 183], [2, 22, 169], [2, 84, 108], [38, 14, 143], [7, 7, 182], [7, 7, 183], [2, 14, 182], [2, 14, 183], [3, 14, 183], [2, 182, 17], [2, 182, 18], [2, 39, 162], [3, 18, 183], [3, 143, 59]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 181 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 22, 182], [2, 2, 203], [7, 39, 162], [2, 4, 203], [2, 39, 169], [3, 39, 169], [2, 7, 203], [2, 64, 147], [3, 8, 203], [7, 39, 169], [7, 52, 157], [7, 7, 203], [2, 2, 214], [2, 14, 203], [2, 4, 214], [2, 2, 217], [2, 77, 143], [2, 4, 217], [2, 39, 183], [3, 8, 214], [2, 7, 217], [2, 22, 203], [2, 64, 162], [2, 84, 143], [2, 14, 214]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 206 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 14, 214], [7, 22, 203], [2, 14, 217], [2, 214, 18], [2, 64, 169], [2, 77, 157], [2, 217, 18], [2, 22, 214], [3, 74, 162], [7, 64, 169], [2, 22, 217], [2, 2, 238], [2, 2, 239], [2, 4, 238], [2, 4, 239], [3, 4, 239], [2, 7, 238], [2, 7, 239], [2, 64, 183], [3, 8, 239], [17, 52, 182], [2, 2, 248], [2, 2, 249], [2, 4, 248], [2, 4, 249]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 231 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 4, 249], [2, 7, 248], [2, 7, 249], [2, 74, 183], [3, 8, 249], [2, 77, 182], [2, 22, 238], [2, 2, 259], [2, 14, 248], [2, 4, 259], [3, 4, 259], [7, 22, 238], [2, 7, 259], [2, 64, 203], [3, 8, 259], [2, 2, 267], [2, 22, 248], [2, 2, 269], [3, 4, 267], [2, 4, 269], [2, 7, 267], [2, 267, 8], [2, 7, 269], [2, 39, 238], [2, 39, 239]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 256 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[3, 39, 239], [2, 77, 203], [2, 14, 267], [2, 169, 113], [2, 14, 269], [2, 267, 17], [2, 267, 18], [3, 18, 267], [2, 39, 248], [2, 39, 249], [2, 22, 267], [2, 182, 108], [2, 22, 269], [3, 74, 217], [7, 39, 249], [2, 77, 217], [2, 182, 113], [3, 28, 267], [2, 259, 38], [2, 39, 259], [3, 39, 259], [17, 267, 18], [2, 84, 217], [2, 64, 238], [2, 64, 239]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 281 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[17, 22, 267], [2, 267, 38], [2, 39, 267], [3, 39, 267], [2, 39, 269], [3, 39, 269], [7, 162, 143], [2, 259, 52], [2, 64, 248], [2, 64, 249], [2, 2, 312], [2, 77, 238], [2, 4, 312], [3, 4, 312], [2, 259, 59], [2, 7, 312], [2, 312, 8], [3, 8, 312], [2, 74, 248], [2, 64, 259], [3, 74, 249], [2, 77, 248], [2, 14, 312], [2, 214, 113], [3, 113, 214]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 306 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 182, 147], [2, 217, 113], [2, 64, 267], [2, 84, 248], [2, 64, 269], [2, 22, 312], [2, 2, 333], [2, 77, 259], [2, 4, 333], [2, 169, 169], [2, 182, 157], [2, 7, 333], [2, 74, 267], [3, 8, 333], [2, 74, 269], [2, 77, 267], [7, 7, 333], [2, 77, 269], [2, 14, 333], [3, 14, 333], [7, 77, 267], [2, 312, 38], [2, 39, 312], [2, 169, 183], [2, 84, 269]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 331 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 269, 84], [2, 22, 333], [7, 39, 312], [2, 214, 143], [3, 143, 214], [17, 77, 267], [2, 217, 143], [2, 214, 147], [2, 249, 113], [3, 113, 249], [2, 182, 182], [2, 182, 183], [7, 147, 214], [2, 259, 108], [17, 269, 84], [7, 52, 312], [2, 2, 368], [2, 214, 157], [2, 4, 368], [3, 4, 368], [2, 217, 157], [2, 7, 368], [2, 64, 312], [3, 8, 368], [3, 269, 108]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 356 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 217, 162], [2, 267, 113], [3, 113, 267], [2, 14, 368], [2, 169, 214], [3, 214, 169], [2, 182, 203], [2, 74, 312], [3, 18, 368], [7, 169, 214], [2, 77, 312], [2, 22, 368], [7, 74, 312], [2, 249, 143], [3, 143, 249], [2, 2, 392], [7, 22, 368], [2, 4, 392], [2, 64, 333], [3, 214, 183], [2, 7, 392], [2, 217, 183], [2, 2, 399], [2, 259, 143], [2, 4, 399]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 381 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[3, 4, 399], [7, 162, 238], [2, 7, 399], [2, 39, 368], [2, 169, 239], [2, 2, 407], [2, 77, 333], [2, 4, 407], [3, 4, 407], [2, 14, 399], [2, 7, 407], [2, 407, 8], [2, 259, 157], [2, 84, 333], [2, 169, 249], [7, 7, 407], [2, 182, 238], [2, 14, 407], [2, 239, 183], [7, 169, 249], [2, 267, 157], [2, 312, 113], [2, 2, 424], [2, 399, 28], [2, 4, 424]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 406 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 22, 407], [2, 182, 248], [2, 7, 424], [2, 64, 368], [3, 8, 424], [2, 217, 217], [2, 407, 28], [2, 169, 267], [2, 399, 38], [2, 14, 424], [3, 14, 424], [17, 312, 113], [2, 182, 259], [2, 74, 368], [3, 18, 424], [17, 22, 407], [2, 77, 368], [2, 22, 424], [3, 39, 407], [18, 249, 183], [2, 182, 267], [2, 2, 448], [2, 2, 449], [2, 4, 448], [2, 4, 449]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 431 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 4, 449], [2, 7, 448], [2, 7, 449], [2, 449, 8], [2, 399, 59], [2, 312, 147], [7, 7, 448], [7, 7, 449], [2, 14, 448], [2, 14, 449], [3, 14, 449], [2, 217, 248], [2, 74, 392], [2, 449, 18], [3, 18, 449], [2, 77, 392], [2, 22, 448], [2, 22, 449], [7, 449, 18], [2, 74, 399], [2, 312, 162], [2, 2, 473], [2, 77, 399], [2, 4, 473], [2, 239, 239]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 456 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[7, 162, 312], [2, 7, 473], [2, 74, 407], [3, 8, 473], [2, 84, 399], [2, 77, 407], [7, 7, 473], [2, 217, 269], [2, 14, 473], [2, 39, 449], [3, 39, 449], [77, 407, 8], [2, 84, 407], [3, 18, 473], [7, 39, 449], [2, 182, 312], [2, 2, 493], [3, 473, 22], [2, 4, 493], [2, 74, 424], [3, 74, 424], [2, 7, 493], [2, 77, 424], [2, 169, 333], [7, 74, 424]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 481 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[18, 39, 449], [2, 267, 238], [2, 239, 267], [2, 14, 493], [2, 84, 424], [3, 269, 239], [7, 392, 113], [7, 239, 267], [2, 39, 473], [2, 64, 449], [18, 74, 424], [2, 22, 493], [2, 2, 514], [7, 39, 473], [2, 4, 514], [3, 4, 514], [2, 407, 113], [2, 7, 514], [2, 74, 448], [2, 74, 449], [3, 74, 449], [2, 77, 448], [2, 77, 449], [3, 214, 312], [2, 14, 514]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 506 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 217, 312], [7, 52, 473], [7, 77, 449], [2, 39, 493], [2, 84, 449], [2, 267, 267], [7, 162, 368], [2, 22, 514], [2, 64, 473], [3, 113, 424], [3, 269, 269], [7, 392, 143], [7, 22, 514], [2, 399, 143], [3, 28, 514], [7, 147, 392], [52, 22, 473], [2, 399, 147], [2, 74, 473], [3, 74, 473], [17, 267, 267], [2, 77, 473], [2, 239, 312], [7, 74, 473], [2, 39, 514]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 531 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 407, 147], [7, 77, 473], [2, 2, 554], [2, 64, 493], [2, 4, 554], [3, 4, 554], [2, 312, 248], [2, 7, 554], [2, 449, 113], [3, 8, 554], [2, 407, 157], [17, 77, 473], [7, 7, 554], [2, 74, 493], [2, 14, 554], [2, 407, 162], [2, 77, 493], [2, 259, 312], [2, 239, 333], [3, 18, 554], [2, 182, 392], [7, 77, 493], [2, 22, 554], [2, 84, 493], [2, 64, 514]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 556 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 2, 577], [7, 392, 183], [2, 4, 577], [2, 214, 368], [3, 28, 554], [2, 7, 577], [2, 217, 368], [3, 8, 577], [3, 113, 473], [2, 74, 514], [2, 182, 407], [2, 407, 183], [2, 2, 589], [2, 259, 333], [2, 4, 589], [3, 4, 589], [77, 407, 113], [2, 7, 589], [3, 589, 7], [2, 84, 514], [2, 22, 577], [2, 267, 333], [7, 7, 589], [2, 399, 203], [2, 14, 589]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 581 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[3, 14, 589], [2, 2, 603], [2, 182, 424], [2, 4, 603], [3, 4, 603], [2, 217, 392], [2, 7, 603], [2, 22, 589], [3, 8, 603], [2, 214, 399], [3, 214, 399], [7, 7, 603], [2, 39, 577], [2, 14, 603], [2, 64, 554], [3, 554, 64], [17, 157, 448], [2, 214, 407], [3, 18, 603], [7, 64, 554], [2, 217, 407], [2, 22, 603], [17, 22, 589], [2, 259, 368], [2, 39, 589]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 606 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[3, 39, 589], [2, 182, 448], [2, 77, 554], [2, 449, 183], [7, 39, 589], [7, 52, 577], [2, 2, 633], [3, 473, 162], [2, 4, 633], [2, 84, 554], [3, 214, 424], [2, 7, 633], [2, 64, 577], [2, 39, 603], [3, 39, 603], [17, 52, 577], [2, 312, 333], [2, 239, 407], [2, 14, 633], [2, 249, 399], [3, 399, 249], [17, 267, 368], [2, 74, 577], [2, 449, 203], [2, 64, 589]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 631 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 2, 652], [2, 22, 633], [2, 2, 654], [3, 4, 652], [2, 4, 654], [2, 7, 652], [2, 652, 8], [2, 7, 654], [2, 169, 493], [2, 74, 589], [3, 74, 589], [2, 217, 448], [2, 14, 652], [2, 64, 603], [2, 14, 654], [2, 652, 17], [2, 2, 668], [3, 18, 652], [2, 4, 668], [2, 84, 589], [2, 22, 652], [2, 7, 668], [2, 22, 654], [2, 74, 603], [3, 74, 603]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 656 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[7, 22, 652], [2, 77, 603], [3, 28, 652], [2, 14, 668], [2, 169, 514], [17, 652, 17], [7, 77, 603], [3, 633, 52], [2, 84, 603], [2, 239, 449], [17, 22, 652], [2, 22, 668], [2, 2, 689], [3, 39, 652], [2, 4, 689], [3, 4, 689], [7, 22, 668], [2, 7, 689], [2, 64, 633], [2, 249, 449], [18, 259, 424], [17, 52, 633], [7, 7, 689], [3, 554, 147], [2, 14, 689]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 681 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 312, 392], [17, 22, 668], [7, 147, 554], [2, 39, 668], [2, 259, 449], [7, 52, 652], [2, 77, 633], [2, 22, 689], [2, 239, 473], [3, 473, 239], [3, 654, 59], [2, 267, 448], [2, 64, 652], [2, 84, 633], [2, 64, 654], [2, 312, 407], [52, 652, 18], [3, 143, 577], [2, 249, 473], [2, 169, 554], [3, 554, 169], [7, 52, 668], [2, 74, 652], [3, 74, 652], [2, 39, 689]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 706 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 77, 652], [7, 392, 333], [2, 77, 654], [2, 64, 668], [3, 143, 589], [7, 77, 652], [17, 52, 668], [2, 84, 652], [3, 554, 182], [2, 84, 654], [3, 654, 84], [2, 267, 473], [3, 473, 267], [2, 74, 668], [3, 74, 668], [2, 2, 742], [2, 77, 668], [2, 4, 742], [3, 4, 742], [18, 143, 589], [2, 7, 742], [7, 77, 668], [3, 8, 742], [2, 84, 668], [2, 64, 689]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 731 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[3, 689, 64], [2, 2, 753], [2, 14, 742], [2, 4, 753], [2, 169, 589], [2, 182, 577], [2, 7, 753], [2, 312, 449], [3, 8, 753], [2, 74, 689], [2, 22, 742], [2, 652, 113], [2, 77, 689], [2, 14, 753], [2, 214, 554], [3, 214, 554], [7, 162, 603], [2, 182, 589], [2, 169, 603], [2, 84, 689], [3, 689, 84], [2, 22, 753], [2, 2, 774], [3, 143, 633], [2, 4, 774]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 756 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[3, 4, 774], [7, 22, 753], [2, 7, 774], [2, 449, 333], [3, 8, 774], [3, 269, 514], [2, 182, 603], [3, 473, 312], [7, 449, 333], [2, 14, 774], [3, 14, 774], [17, 22, 753], [2, 214, 577], [2, 39, 753], [2, 239, 554], [2, 217, 577], [2, 652, 143], [2, 22, 774], [7, 39, 753], [2, 399, 399], [2, 407, 392], [2, 2, 798], [2, 2, 799], [2, 4, 798], [2, 4, 799]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 781 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[3, 4, 799], [2, 7, 798], [2, 7, 799], [3, 8, 798], [3, 8, 799], [2, 652, 157], [7, 7, 798], [7, 7, 799], [2, 14, 798], [2, 14, 799], [2, 407, 407], [2, 182, 633], [2, 74, 742], [2, 64, 753], [3, 18, 799], [2, 77, 742], [2, 22, 798], [2, 22, 799], [3, 554, 267], [2, 169, 654], [3, 269, 554], [2, 2, 823], [2, 84, 742], [2, 4, 823], [2, 239, 589]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 806 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[3, 589, 239], [2, 7, 823], [2, 407, 424], [3, 8, 823], [3, 143, 689], [2, 182, 652], [2, 652, 183], [2, 2, 834], [2, 14, 823], [2, 4, 834], [3, 4, 834], [17, 157, 668], [2, 7, 834], [2, 239, 603], [3, 8, 834], [2, 267, 577], [2, 22, 823], [7, 7, 834], [2, 214, 633], [2, 14, 834], [2, 2, 847], [2, 182, 668], [2, 4, 847], [2, 249, 603], [3, 18, 834]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 831 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[2, 7, 847], [2, 407, 448], [2, 22, 834], [3, 589, 267], [2, 84, 774], [3, 269, 589], [17, 22, 823], [2, 14, 847], [2, 39, 823], [2, 64, 799], [2, 847, 17], [2, 847, 18], [2, 214, 652], [3, 113, 753], [2, 214, 654], [2, 22, 847], [2, 267, 603], [2, 182, 689], [2, 74, 798], [2, 39, 834], [2, 2, 872], [2, 77, 798], [2, 4, 872], [3, 4, 872], [7, 39, 834]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 856 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 7, 872], [2, 407, 473], [3, 8, 872], [2, 84, 798], [2, 84, 799], [3, 799, 84], [2, 217, 668], [2, 14, 872], [2, 64, 823], [3, 113, 774], [2, 312, 577], [2, 652, 238], [2, 239, 652], [2, 259, 633], [2, 239, 654], [2, 22, 872], [7, 872, 18], [7, 239, 652], [2, 74, 823], [2, 64, 834], [2, 847, 52], [2, 77, 823], [2, 249, 652], [3, 589, 312], [2, 214, 689]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 881 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3, 214, 689], [7, 77, 823], [2, 217, 689], [2, 84, 823], [2, 74, 834], [3, 74, 834], [147, 652, 113], [2, 39, 872], [3, 39, 872], [2, 259, 654], [3, 399, 514], [2, 312, 603], [7, 39, 872], [2, 249, 668], [2, 84, 834], [2, 267, 652], [7, 162, 753], [2, 74, 847], [2, 169, 753], [3, 473, 449], [2, 77, 847], [17, 157, 753], [7, 74, 847], [2, 259, 668], [2, 239, 689]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 906 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[3, 689, 239], [17, 312, 603], [2, 84, 847], [7, 259, 668], [7, 239, 689], [17, 267, 652], [2, 182, 753], [2, 64, 872], [3, 113, 823], [2, 249, 689], [3, 689, 249], [52, 652, 238], [7, 64, 872], [2, 449, 493], [2, 169, 774], [2, 2, 942], [2, 312, 633], [2, 4, 942], [2, 834, 113], [2, 259, 689], [2, 7, 942], [2, 942, 8], [3, 8, 942], [7, 834, 113], [2, 399, 554]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 931 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[3, 399, 554], [2, 847, 108], [2, 14, 942], [3, 14, 942], [3, 589, 368], [2, 217, 742], [2, 847, 113], [2, 407, 554], [3, 554, 407], [2, 449, 514], [2, 22, 942], [7, 162, 798], [2, 312, 654], [2, 169, 798], [2, 169, 799], [3, 799, 169], [2, 217, 753], [3, 28, 942], [7, 169, 798], [7, 169, 799], [7, 392, 577], [7, 147, 823], [2, 2, 974], [2, 834, 143], [2, 4, 974]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 956 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[2, 2, 977], [2, 182, 798], [2, 4, 977], [2, 974, 8], [3, 8, 974], [2, 7, 977], [2, 652, 333], [3, 8, 977], [52, 269, 668], [2, 14, 974], [3, 14, 974], [2, 847, 143], [2, 14, 977], [2, 169, 823], [3, 18, 974], [2, 847, 147], [2, 977, 18], [2, 22, 974], [3, 589, 407], [52, 259, 689], [2, 22, 977], [7, 392, 603], [2, 259, 742], [2, 249, 753], [2, 169, 834]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 981 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `6 ≤ n ≤ 1005` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 6 ≤ n) (h2 : n ≤ 1005) : ∃ x, good n x = true := by
  by_cases c0 : n < 31
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 56
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 81
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 106
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 131
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 156
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 181
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 206
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 231
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 256
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 281
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 306
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 331
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 356
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 381
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 406
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 431
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 456
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 481
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 506
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 531
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 556
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 581
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 606
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 631
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 656
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 681
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 706
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 731
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 756
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 781
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 806
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 831
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 856
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 881
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 906
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 931
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 956
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 981
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a230194Tab

open OMA.Aoeis_a230194Tab in
theorem OMA.solution : OMA.R_oeis_a230194_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
