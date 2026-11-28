import OMAReductions.R_OeisA229969_conjecture_2_R1
import Mathlib

-- Step OeisA229969.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_2.R1
-- Credit: @prathameshnium. Finite check for 7 ≤ n ≤ 1006.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 322999.

/-! Step OeisA229969.conjecture_2.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_2Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `570` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 570 2

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
  have hnd := noDiv_sound p 570 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && ((decide (x = 3) || (decide (x = 4) || (decide (x = 6) || (decide (x = 10) || decide (x = 15))))) && (isPrimeB (2 * y - 1) && (isPrimeB (2 * z - 1) && (isPrimeB (2 * x * y - 1) && (isPrimeB (2 * x * z - 1) && isPrimeB (2 * y * z - 1)))))))))
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
    ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
      (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y - 1).Prime ∧ (2 * x * z - 1).Prime ∧ (2 * y * z - 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    exact ⟨x, y, z, a0, a1, a2, (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact a3), isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 7, …, 1006`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 2, 2], [3, 2, 3], [3, 3, 3], [3, 3, 4], [3, 4, 4], [4, 4, 4], [3, 3, 7], [4, 4, 6], [3, 3, 9], [3, 3, 10], [3, 2, 12], [3, 3, 12], [15, 2, 2], [3, 2, 15], [3, 3, 15], [3, 7, 12], [4, 9, 10], [4, 4, 16], [3, 3, 19], [3, 4, 19], [4, 4, 19], [3, 3, 22], [4, 4, 21], [10, 10, 10], [6, 6, 19]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 7 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[4, 4, 24], [6, 6, 21], [6, 6, 22], [6, 7, 22], [3, 3, 30], [3, 4, 30], [4, 4, 30], [10, 10, 19], [4, 6, 30], [10, 10, 21], [4, 4, 34], [6, 7, 30], [10, 10, 24], [15, 15, 15], [3, 3, 40], [3, 2, 42], [3, 3, 42], [6, 6, 37], [3, 2, 45], [3, 3, 45], [3, 4, 45], [4, 4, 45], [6, 6, 42], [3, 3, 49], [10, 10, 36]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 32 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[10, 10, 37], [3, 3, 52], [10, 7, 42], [3, 15, 42], [6, 6, 49], [4, 4, 54], [4, 4, 55], [4, 6, 54], [4, 6, 55], [6, 6, 54], [6, 6, 55], [6, 7, 55], [6, 6, 57], [3, 3, 64], [10, 10, 51], [10, 10, 52], [10, 12, 51], [15, 22, 37], [6, 15, 54], [3, 3, 70], [3, 10, 64], [15, 9, 54], [6, 16, 57], [6, 19, 55], [3, 3, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 57 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 4, 75], [4, 4, 75], [4, 4, 76], [3, 7, 75], [4, 6, 76], [4, 4, 79], [3, 3, 82], [4, 6, 79], [3, 3, 84], [6, 6, 79], [3, 2, 87], [3, 3, 87], [6, 6, 82], [10, 10, 75], [3, 9, 84], [3, 7, 87], [4, 4, 90], [4, 4, 91], [15, 15, 70], [4, 6, 91], [3, 12, 87], [6, 6, 91], [6, 2, 96], [3, 3, 99], [3, 3, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 82 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[15, 2, 90], [6, 6, 96], [6, 6, 97], [3, 7, 100], [6, 6, 99], [3, 10, 99], [3, 10, 100], [15, 12, 87], [3, 12, 100], [6, 19, 91], [10, 7, 100], [6, 15, 97], [10, 10, 99], [3, 3, 114], [3, 4, 114], [3, 2, 117], [3, 3, 117], [4, 6, 114], [3, 2, 120], [3, 3, 120], [3, 7, 117], [6, 2, 120], [4, 4, 121], [3, 10, 117], [4, 6, 121]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 107 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[6, 6, 120], [6, 6, 121], [6, 2, 126], [3, 3, 129], [3, 4, 129], [4, 4, 129], [6, 6, 126], [15, 12, 112], [10, 10, 120], [3, 3, 135], [3, 10, 129], [4, 10, 129], [4, 4, 136], [6, 7, 132], [6, 19, 121], [6, 6, 135], [6, 7, 135], [4, 9, 136], [4, 10, 136], [6, 6, 139], [3, 2, 147], [3, 3, 147], [4, 21, 129], [10, 10, 135], [10, 10, 136]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 132 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[10, 30, 117], [10, 7, 141], [4, 19, 136], [3, 10, 147], [10, 10, 141], [4, 4, 154], [3, 3, 157], [4, 6, 154], [3, 3, 159], [6, 6, 154], [10, 10, 147], [6, 6, 156], [10, 12, 147], [15, 19, 136], [6, 6, 159], [3, 12, 157], [10, 22, 141], [4, 4, 166], [3, 3, 169], [10, 10, 156], [15, 15, 147], [15, 16, 147], [6, 19, 154], [4, 10, 166], [3, 3, 175]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 157 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[3, 4, 175], [3, 3, 177], [6, 9, 169], [4, 6, 175], [6, 6, 174], [6, 6, 175], [4, 4, 180], [4, 10, 175], [3, 3, 184], [3, 4, 184], [4, 4, 184], [15, 22, 156], [4, 6, 184], [10, 10, 175], [6, 6, 184], [10, 10, 177], [3, 3, 192], [6, 6, 187], [6, 7, 187], [6, 21, 174], [3, 7, 192], [4, 4, 195], [10, 7, 187], [3, 3, 199], [3, 19, 184]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 182 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[6, 6, 195], [6, 7, 195], [4, 4, 201], [15, 15, 180], [3, 3, 205], [4, 24, 184], [6, 6, 201], [4, 9, 201], [3, 2, 210], [3, 3, 210], [6, 6, 205], [3, 10, 205], [6, 57, 156], [3, 7, 210], [10, 10, 201], [3, 9, 210], [3, 3, 217], [6, 2, 216], [10, 10, 205], [3, 3, 220], [3, 4, 220], [4, 4, 220], [6, 7, 216], [6, 2, 222], [10, 10, 211]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 207 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[6, 15, 211], [15, 34, 184], [6, 6, 222], [3, 3, 229], [3, 4, 229], [4, 4, 229], [3, 15, 220], [4, 4, 231], [6, 9, 225], [15, 15, 211], [4, 4, 234], [6, 15, 222], [4, 9, 231], [15, 19, 211], [3, 3, 240], [4, 9, 234], [4, 10, 234], [6, 21, 222], [3, 7, 240], [15, 16, 220], [4, 4, 244], [6, 7, 240], [4, 6, 244], [6, 54, 195], [3, 3, 250]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 232 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 4, 250], [3, 3, 252], [6, 9, 244], [4, 6, 250], [6, 30, 225], [6, 6, 250], [4, 4, 255], [6, 6, 252], [6, 7, 252], [10, 10, 246], [10, 7, 250], [3, 3, 262], [4, 4, 261], [10, 10, 250], [6, 15, 250], [10, 10, 252], [6, 15, 252], [10, 12, 252], [10, 10, 255], [6, 54, 216], [3, 12, 262], [4, 19, 255], [15, 12, 252], [15, 15, 250], [10, 21, 250]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 257 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[15, 15, 252], [6, 6, 271], [6, 7, 271], [15, 15, 255], [6, 9, 271], [3, 22, 262], [10, 7, 271], [15, 19, 255], [10, 9, 271], [3, 3, 285], [15, 27, 250], [10, 9, 274], [4, 4, 286], [3, 3, 289], [3, 4, 289], [4, 4, 289], [15, 9, 274], [4, 6, 289], [6, 15, 279], [6, 6, 289], [4, 4, 294], [4, 10, 289], [4, 6, 294], [10, 24, 271], [6, 6, 294]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 282 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 15, 289], [4, 4, 300], [10, 10, 289], [3, 3, 304], [4, 21, 286], [15, 42, 255], [4, 9, 300], [10, 10, 294], [6, 15, 294], [3, 9, 304], [10, 10, 297], [3, 30, 285], [10, 12, 297], [15, 31, 274], [6, 21, 294], [6, 6, 310], [6, 7, 310], [10, 10, 304], [15, 9, 301], [3, 19, 304], [10, 7, 310], [3, 3, 322], [6, 2, 321], [10, 10, 310], [15, 15, 301]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 307 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[4, 4, 324], [6, 6, 321], [6, 6, 322], [3, 2, 330], [3, 3, 330], [3, 12, 322], [15, 2, 321], [4, 4, 331], [15, 24, 301], [4, 76, 261], [3, 9, 330], [3, 10, 330], [6, 16, 322], [4, 10, 331], [15, 15, 316], [4, 4, 339], [15, 12, 321], [10, 9, 330], [10, 10, 330], [10, 10, 331], [4, 9, 339], [4, 10, 339], [4, 4, 346], [15, 19, 321], [4, 21, 331]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 332 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[6, 30, 321], [10, 9, 339], [10, 10, 339], [10, 19, 331], [3, 3, 355], [10, 21, 331], [6, 6, 351], [6, 37, 321], [3, 7, 355], [6, 9, 351], [6, 6, 355], [4, 4, 360], [15, 15, 339], [6, 9, 355], [10, 10, 351], [15, 15, 342], [10, 12, 351], [4, 24, 346], [15, 9, 351], [6, 19, 351], [15, 2, 360], [15, 12, 351], [6, 22, 351], [6, 2, 372], [15, 15, 351]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 357 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[10, 21, 351], [4, 19, 360], [6, 6, 372], [3, 3, 379], [15, 70, 301], [6, 30, 351], [15, 22, 351], [15, 2, 372], [15, 15, 360], [3, 3, 385], [3, 4, 385], [4, 4, 385], [6, 16, 372], [4, 45, 346], [10, 175, 211], [3, 15, 379], [3, 10, 385], [6, 6, 387], [6, 7, 387], [3, 19, 379], [15, 15, 372], [3, 15, 385], [6, 19, 379], [3, 3, 399], [3, 4, 399]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 382 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[4, 4, 399], [4, 19, 385], [4, 6, 399], [3, 52, 355], [6, 6, 399], [15, 12, 385], [15, 19, 379], [10, 10, 394], [15, 15, 385], [6, 139, 271], [3, 15, 399], [6, 6, 406], [6, 7, 406], [6, 15, 399], [6, 9, 406], [15, 2, 405], [4, 4, 415], [6, 6, 412], [10, 21, 394], [6, 6, 414], [15, 27, 385], [4, 4, 420], [6, 9, 414], [4, 6, 420], [10, 10, 411]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 407 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[6, 6, 420], [6, 7, 420], [6, 16, 412], [6, 9, 420], [3, 3, 430], [6, 76, 355], [3, 3, 432], [6, 19, 414], [6, 22, 412], [6, 6, 429], [3, 7, 432], [3, 10, 430], [4, 55, 385], [3, 3, 439], [3, 4, 439], [4, 4, 439], [3, 15, 430], [4, 4, 441], [3, 3, 444], [3, 9, 439], [4, 9, 439], [4, 10, 439], [6, 6, 442], [4, 10, 441], [15, 90, 351]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 432 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[15, 15, 427], [10, 9, 439], [10, 10, 439], [10, 9, 441], [10, 10, 441], [4, 4, 454], [6, 15, 442], [6, 2, 456], [15, 9, 441], [3, 19, 444], [4, 9, 454], [6, 6, 456], [15, 12, 442], [6, 22, 442], [3, 3, 465], [3, 4, 465], [4, 4, 465], [10, 22, 442], [4, 30, 441], [10, 136, 330], [3, 9, 465], [4, 9, 465], [4, 4, 471], [3, 3, 474], [4, 6, 471]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 457 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[3, 2, 477], [3, 3, 477], [15, 15, 454], [4, 10, 471], [15, 15, 456], [3, 10, 474], [4, 19, 465], [10, 37, 442], [3, 3, 484], [10, 10, 471], [3, 12, 477], [15, 22, 456], [10, 10, 474], [4, 76, 415], [6, 6, 484], [4, 4, 489], [15, 27, 456], [4, 6, 489], [10, 51, 439], [6, 6, 489], [3, 15, 484], [10, 7, 486], [4, 4, 496], [10, 9, 486], [10, 10, 486]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 482 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[3, 30, 474], [10, 24, 474], [4, 16, 489], [6, 15, 489], [6, 6, 499], [3, 2, 507], [3, 3, 507], [10, 12, 492], [10, 21, 484], [3, 114, 399], [10, 21, 486], [4, 4, 510], [15, 15, 489], [3, 10, 507], [10, 51, 460], [10, 7, 505], [6, 6, 511], [4, 4, 516], [10, 10, 505], [3, 3, 520], [3, 4, 520], [4, 4, 520], [6, 6, 517], [6, 7, 517], [6, 54, 471]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 507 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[15, 12, 505], [6, 2, 525], [4, 10, 520], [3, 12, 520], [6, 19, 511], [6, 6, 525], [3, 3, 532], [10, 22, 507], [10, 10, 520], [3, 3, 535], [10, 7, 525], [4, 19, 520], [15, 19, 510], [3, 7, 535], [6, 15, 525], [3, 9, 535], [6, 16, 526], [10, 19, 520], [3, 15, 532], [10, 21, 520], [10, 10, 532], [6, 21, 526], [10, 19, 525], [15, 15, 525], [10, 135, 411]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 532 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[4, 4, 549], [6, 6, 546], [6, 6, 547], [3, 22, 535], [3, 3, 555], [15, 15, 532], [4, 10, 549], [15, 57, 492], [6, 42, 517], [6, 49, 511], [6, 6, 555], [3, 3, 562], [10, 10, 549], [3, 135, 432], [3, 3, 565], [3, 4, 565], [4, 4, 565], [15, 15, 544], [4, 6, 565], [6, 15, 555], [6, 6, 565], [4, 9, 565], [10, 7, 562], [6, 9, 565], [15, 70, 496]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 557 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[10, 10, 562], [3, 3, 577], [10, 9, 565], [10, 10, 565], [10, 51, 525], [6, 55, 526], [3, 3, 582], [15, 19, 555], [3, 22, 565], [4, 91, 496], [3, 7, 582], [10, 21, 562], [6, 6, 582], [6, 7, 582], [10, 10, 576], [3, 12, 582], [4, 45, 549], [4, 75, 520], [3, 42, 555], [6, 49, 546], [4, 4, 594], [3, 3, 597], [4, 6, 594], [3, 40, 562], [6, 6, 594]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 582 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[4, 9, 594], [10, 22, 576], [6, 9, 594], [3, 10, 597], [15, 91, 505], [3, 12, 597], [6, 6, 601], [10, 42, 562], [3, 15, 597], [15, 15, 586], [3, 2, 612], [3, 3, 612], [6, 6, 607], [3, 82, 535], [6, 6, 609], [15, 16, 591], [4, 4, 615], [15, 12, 597], [3, 10, 612], [10, 30, 586], [4, 4, 619], [4, 9, 615], [6, 16, 607], [6, 15, 609], [6, 70, 555]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 607 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[10, 10, 612], [4, 4, 625], [4, 21, 609], [4, 6, 625], [3, 3, 630], [3, 4, 630], [4, 4, 630], [10, 10, 619], [4, 6, 630], [15, 115, 511], [6, 6, 630], [6, 7, 630], [4, 21, 619], [3, 3, 639], [6, 15, 625], [4, 34, 609], [3, 3, 642], [4, 30, 615], [10, 21, 619], [6, 15, 630], [6, 21, 625], [4, 9, 640], [4, 4, 646], [15, 15, 625], [6, 49, 601]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 632 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[6, 21, 630], [3, 3, 652], [10, 9, 640], [3, 3, 654], [3, 4, 654], [4, 4, 654], [10, 7, 646], [6, 6, 652], [6, 7, 652], [10, 10, 646], [3, 12, 652], [4, 4, 660], [10, 10, 649], [4, 6, 660], [10, 21, 640], [6, 6, 660], [6, 7, 660], [10, 19, 645], [10, 19, 646], [15, 15, 646], [4, 19, 654], [6, 42, 630], [15, 15, 649], [10, 9, 661], [10, 10, 661]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 657 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[15, 15, 652], [10, 24, 649], [15, 27, 642], [10, 30, 645], [10, 31, 645], [3, 30, 654], [15, 24, 649], [15, 22, 652], [10, 19, 661], [10, 36, 645], [4, 4, 684], [6, 6, 681], [6, 7, 681], [15, 16, 664], [4, 346, 346], [3, 42, 652], [10, 7, 681], [4, 4, 691], [6, 42, 652], [4, 6, 691], [3, 87, 612], [6, 6, 691], [4, 9, 691], [4, 55, 646], [6, 9, 691]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 682 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[10, 36, 661], [6, 42, 660], [15, 42, 652], [3, 2, 705], [3, 3, 705], [3, 4, 705], [4, 4, 705], [10, 64, 640], [10, 24, 681], [4, 21, 691], [3, 9, 705], [3, 3, 712], [6, 22, 691], [3, 3, 714], [3, 3, 715], [4, 4, 714], [3, 15, 705], [6, 6, 712], [6, 7, 712], [10, 70, 646], [10, 36, 681], [10, 99, 619], [15, 9, 705], [3, 12, 715], [10, 21, 700]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 707 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[4, 4, 724], [6, 40, 687], [4, 4, 726], [15, 15, 705], [6, 70, 660], [15, 2, 720], [4, 4, 730], [4, 30, 705], [4, 10, 726], [10, 31, 700], [15, 22, 705], [10, 7, 726], [10, 10, 724], [3, 30, 712], [10, 10, 726], [15, 27, 705], [3, 3, 742], [4, 4, 741], [3, 3, 744], [15, 16, 720], [15, 91, 646], [3, 3, 747], [4, 9, 741], [6, 97, 652], [3, 99, 654]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 732 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[3, 7, 747], [6, 2, 750], [6, 6, 747], [6, 7, 747], [6, 19, 736], [6, 6, 750], [6, 7, 750], [4, 4, 756], [6, 9, 750], [15, 15, 736], [10, 10, 747], [15, 12, 741], [15, 12, 742], [15, 19, 736], [15, 15, 741], [15, 15, 742], [15, 2, 756], [10, 64, 700], [15, 15, 745], [10, 66, 700], [15, 15, 747], [15, 22, 741], [15, 19, 745], [3, 30, 747], [3, 3, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 757 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[3, 4, 775], [4, 4, 775], [15, 24, 745], [3, 2, 780], [3, 3, 780], [10, 30, 747], [10, 52, 726], [6, 6, 777], [3, 3, 784], [3, 4, 784], [4, 4, 784], [10, 36, 747], [4, 4, 786], [3, 12, 780], [4, 6, 786], [3, 2, 792], [3, 3, 792], [6, 7, 786], [10, 24, 766], [10, 205, 586], [6, 6, 790], [6, 7, 790], [10, 10, 784], [3, 3, 799], [10, 30, 766]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 782 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[15, 12, 780], [3, 30, 775], [4, 19, 786], [15, 15, 780], [6, 6, 799], [15, 52, 745], [6, 30, 777], [6, 22, 786], [6, 244, 565], [3, 99, 714], [6, 21, 790], [15, 2, 801], [15, 42, 762], [3, 42, 775], [15, 301, 505], [6, 6, 810], [15, 52, 756], [6, 271, 547], [6, 42, 777], [6, 6, 814], [4, 4, 819], [6, 36, 786], [10, 75, 744], [3, 52, 775], [15, 15, 801]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 807 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[4, 9, 819], [6, 175, 652], [10, 52, 772], [3, 3, 829], [6, 40, 790], [6, 21, 810], [15, 12, 811], [6, 19, 814], [3, 3, 834], [3, 3, 835], [3, 4, 835], [4, 4, 835], [15, 15, 814], [3, 7, 835], [6, 6, 834], [3, 45, 799], [3, 10, 835], [4, 10, 835], [6, 97, 747], [3, 49, 799], [10, 7, 835], [3, 3, 847], [6, 49, 799], [10, 10, 835], [3, 3, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 832 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[4, 4, 849], [4, 19, 835], [6, 6, 847], [4, 21, 835], [6, 21, 834], [3, 9, 850], [4, 10, 849], [10, 19, 835], [3, 12, 850], [10, 21, 835], [6, 6, 855], [3, 3, 862], [10, 10, 849], [3, 75, 792], [3, 84, 784], [10, 7, 855], [6, 6, 861], [6, 6, 862], [10, 10, 855], [6, 9, 861], [15, 15, 847], [15, 16, 847], [4, 4, 871], [3, 42, 835], [6, 76, 799]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 857 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[4, 4, 874], [3, 3, 877], [4, 6, 874], [4, 10, 871], [3, 3, 880], [3, 4, 880], [4, 4, 880], [6, 9, 874], [4, 6, 880], [10, 10, 871], [6, 6, 880], [3, 10, 880], [10, 7, 877], [3, 3, 889], [6, 16, 874], [10, 10, 877], [3, 3, 892], [6, 19, 874], [10, 10, 880], [6, 6, 889], [4, 4, 894], [4, 4, 895], [6, 9, 889], [4, 6, 895], [10, 250, 646]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 882 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[6, 6, 895], [10, 21, 877], [4, 4, 901], [15, 15, 880], [6, 16, 889], [10, 10, 892], [15, 9, 889], [4, 4, 906], [15, 99, 801], [6, 15, 895], [10, 52, 855], [3, 3, 912], [15, 15, 889], [4, 10, 906], [10, 31, 880], [15, 15, 892], [15, 2, 906], [4, 136, 784], [15, 15, 895], [10, 10, 906], [10, 37, 880], [4, 30, 894], [4, 30, 895], [15, 66, 849], [6, 30, 895]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 907 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[15, 37, 880], [4, 34, 895], [4, 24, 906], [4, 30, 901], [6, 6, 924], [3, 22, 912], [10, 22, 906], [6, 9, 924], [15, 9, 916], [3, 49, 889], [3, 147, 792], [6, 6, 931], [4, 4, 936], [15, 24, 906], [3, 3, 940], [15, 16, 916], [4, 220, 724], [6, 6, 937], [3, 2, 945], [3, 3, 945], [3, 4, 945], [4, 4, 945], [10, 10, 934], [3, 7, 945], [10, 10, 936]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 932 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[3, 42, 912], [3, 10, 945], [4, 4, 951], [3, 12, 945], [4, 6, 951], [10, 7, 945], [3, 3, 957], [6, 7, 951], [10, 10, 945], [6, 6, 954], [3, 7, 957], [15, 16, 937], [6, 6, 957], [6, 7, 957], [4, 16, 951], [15, 12, 945], [3, 3, 967], [4, 4, 966], [15, 15, 945], [6, 19, 951], [3, 7, 967], [6, 195, 777], [4, 9, 966], [4, 10, 966], [3, 3, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 957 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[15, 22, 945], [10, 7, 966], [15, 15, 954], [3, 7, 975], [10, 10, 966], [6, 6, 975], [6, 7, 975], [4, 34, 951], [3, 12, 975], [6, 54, 931], [10, 37, 945], [3, 45, 945], [6, 37, 951], [6, 49, 940], [3, 3, 990], [3, 4, 990], [4, 4, 990], [6, 36, 957], [3, 7, 990], [6, 55, 940], [4, 4, 994], [3, 3, 997], [4, 6, 994], [6, 42, 957], [6, 6, 994]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 982 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `7 ≤ n ≤ 1006` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 7 ≤ n) (h2 : n ≤ 1006) : ∃ x, good n x = true := by
  by_cases c0 : n < 32
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 57
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 82
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 107
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 132
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 157
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 182
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 207
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 232
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 257
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 282
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 307
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 332
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 357
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 382
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 407
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 432
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 457
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 482
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 507
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 532
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 557
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 582
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 607
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 632
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 657
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 682
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 707
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 732
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 757
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 782
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 807
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 832
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 857
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 882
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 907
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 932
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 957
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 982
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA229969_conjecture_2Tab

open OMA.AOeisA229969_conjecture_2Tab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_2_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
