import OMAReductions.R_oeis_a229974_R1
import Mathlib

-- Step oeis-a229974.R1.H1: hypothesis H1 of reduction oeis-a229974.R1
-- Credit: @prathameshnium. Finite check for 4 ≤ n ≤ 810.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 910141.

/-! Step oeis-a229974.R1.H1. -/

namespace OMA.Aoeis_a229974Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `956` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 956 2

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
  have hnd := noDiv_sound p 956 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < x) && (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && (isPrimeB (2 * x - 1) && (isPrimeB (2 * x + 1) && (isPrimeB (2 * x * y - 1) && (isPrimeB (2 * x * y + 1) && (isPrimeB (2 * x * y * z - 1) && isPrimeB (2 * x * y * z + 1))))))))))
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
      (2 * x - 1).Prime ∧ (2 * x + 1).Prime ∧ (2 * x * y - 1).Prime ∧ (2 * x * y + 1).Prime ∧
      (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6, isPrimeB_sound _ a7, isPrimeB_sound _ a8, isPrimeB_sound _ a9⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 4, …, 810`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 1, 1], [3, 1, 1], [2, 1, 3], [3, 1, 3], [6, 1, 1], [3, 1, 5], [2, 3, 5], [2, 3, 6], [3, 3, 6], [3, 5, 5], [2, 3, 9], [6, 5, 4], [3, 1, 12], [3, 3, 11], [2, 1, 15], [6, 9, 4], [2, 3, 15], [2, 1, 18], [3, 1, 18], [3, 10, 10], [2, 3, 19], [2, 3, 20], [2, 18, 6], [2, 15, 10], [2, 15, 11]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 4 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 1, 25], [2, 1, 27], [2, 3, 26], [3, 23, 6], [2, 27, 4], [2, 3, 29], [3, 3, 29], [2, 18, 16], [3, 1, 33], [6, 5, 27], [2, 15, 22], [2, 3, 35], [2, 3, 36], [3, 1, 38], [3, 5, 35], [2, 15, 27], [3, 17, 25], [2, 18, 26], [6, 16, 25], [2, 1, 45], [2, 18, 29], [2, 27, 21], [2, 1, 48], [3, 3, 46], [2, 27, 24]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 29 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 17, 34], [2, 3, 50], [2, 15, 39], [3, 33, 21], [6, 15, 37], [3, 12, 44], [2, 1, 57], [2, 48, 11], [3, 1, 58], [2, 1, 60], [2, 18, 44], [3, 3, 59], [3, 12, 51], [2, 15, 50], [3, 10, 55], [2, 15, 52], [3, 3, 64], [2, 18, 51], [2, 15, 55], [2, 15, 56], [2, 3, 69], [2, 27, 46], [2, 15, 59], [3, 3, 71], [6, 5, 67]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 54 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 5, 71], [2, 57, 21], [2, 1, 78], [2, 45, 35], [3, 30, 50], [2, 15, 67], [2, 60, 23], [2, 78, 6], [3, 18, 66], [2, 15, 71], [2, 18, 69], [2, 1, 87], [2, 3, 86], [6, 1, 85], [3, 5, 85], [3, 7, 84], [2, 27, 66], [2, 3, 91], [2, 15, 80], [3, 10, 85], [2, 27, 70], [3, 40, 57], [2, 3, 96], [2, 15, 85], [6, 1, 96]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 79 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 78, 24], [2, 15, 88], [3, 12, 91], [3, 1, 103], [2, 1, 105], [2, 15, 92], [2, 87, 21], [2, 1, 108], [2, 45, 65], [2, 60, 51], [2, 57, 55], [2, 3, 110], [2, 108, 6], [3, 3, 111], [2, 87, 29], [2, 18, 99], [3, 5, 112], [2, 105, 14], [2, 15, 105], [2, 15, 106], [2, 3, 119], [2, 18, 105], [2, 3, 121], [3, 110, 14], [2, 15, 111]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 104 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 3, 124], [2, 15, 113], [3, 77, 51], [2, 105, 25], [2, 15, 116], [3, 40, 91], [3, 77, 55], [3, 3, 130], [3, 70, 64], [6, 15, 117], [2, 3, 134], [2, 3, 135], [3, 1, 137], [3, 1, 138], [2, 15, 126], [2, 3, 139], [2, 18, 125], [3, 12, 131], [3, 1, 143], [2, 60, 86], [3, 5, 141], [2, 45, 103], [2, 18, 131], [2, 60, 90], [2, 1, 150]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 129 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 3, 149], [2, 18, 135], [3, 7, 146], [2, 150, 5], [2, 27, 129], [2, 18, 139], [2, 57, 101], [2, 3, 156], [3, 138, 21], [3, 5, 155], [2, 15, 147], [3, 23, 139], [2, 3, 161], [2, 15, 150], [2, 1, 165], [2, 165, 2], [2, 48, 120], [2, 15, 154], [2, 165, 5], [3, 45, 125], [2, 3, 169], [2, 18, 155], [3, 1, 172], [2, 105, 70], [3, 5, 170]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 154 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 3, 174], [3, 58, 119], [2, 3, 176], [3, 3, 176], [2, 27, 154], [3, 5, 176], [3, 7, 175], [2, 15, 169], [2, 105, 80], [2, 150, 36], [2, 108, 79], [2, 18, 170], [2, 105, 84], [2, 15, 175], [6, 16, 171], [2, 3, 189], [2, 150, 43], [2, 165, 29], [3, 103, 91], [2, 15, 181], [2, 108, 89], [2, 3, 195], [2, 150, 49], [2, 60, 140], [2, 15, 186]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 179 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 48, 154], [2, 48, 155], [2, 45, 159], [3, 23, 181], [2, 87, 119], [2, 60, 147], [2, 1, 207], [3, 5, 203], [2, 15, 195], [2, 45, 166], [2, 150, 62], [2, 207, 6], [2, 15, 199], [2, 60, 155], [3, 5, 210], [3, 1, 215], [2, 87, 131], [2, 3, 216], [3, 10, 209], [3, 5, 215], [2, 27, 195], [2, 48, 175], [2, 15, 209], [3, 5, 219], [2, 27, 199]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 204 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[2, 3, 224], [2, 45, 183], [2, 3, 226], [2, 165, 65], [6, 1, 226], [2, 87, 145], [2, 57, 176], [2, 60, 174], [3, 3, 231], [2, 27, 209], [2, 105, 132], [2, 78, 160], [3, 3, 235], [3, 1, 238], [2, 45, 196], [2, 57, 185], [2, 15, 228], [3, 1, 242], [3, 3, 241], [2, 87, 159], [2, 57, 190], [2, 60, 188], [2, 18, 231], [2, 45, 205], [3, 5, 245]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 229 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 12, 239], [2, 3, 250], [3, 7, 246], [3, 3, 251], [2, 1, 255], [2, 18, 239], [2, 165, 93], [2, 1, 258], [2, 105, 155], [2, 105, 156], [2, 60, 202], [2, 3, 260], [3, 58, 205], [2, 60, 205], [3, 70, 195], [2, 3, 264], [2, 60, 208], [2, 105, 164], [3, 1, 268], [2, 15, 256], [2, 18, 254], [3, 5, 267], [2, 1, 273], [3, 58, 216], [2, 27, 249]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 254 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 45, 232], [2, 3, 275], [2, 273, 6], [3, 1, 278], [6, 55, 222], [2, 27, 255], [2, 3, 280], [2, 3, 281], [3, 1, 283], [6, 1, 281], [2, 273, 14], [2, 78, 210], [2, 1, 288], [3, 175, 114], [2, 45, 246], [2, 3, 289], [2, 273, 20], [3, 10, 283], [3, 38, 256], [2, 45, 251], [2, 3, 294], [2, 3, 295], [2, 18, 281], [2, 105, 195], [2, 57, 244]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 279 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 12, 289], [2, 45, 258], [2, 150, 154], [2, 165, 140], [2, 207, 99], [2, 18, 289], [2, 15, 293], [2, 3, 306], [2, 45, 265], [2, 207, 104], [3, 10, 301], [2, 57, 256], [2, 258, 56], [3, 1, 313], [2, 15, 301], [2, 3, 314], [2, 18, 300], [2, 108, 211], [2, 150, 170], [6, 16, 301], [2, 105, 217], [2, 57, 266], [2, 3, 321], [2, 60, 265], [2, 57, 269]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 304 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 57, 270], [3, 40, 287], [2, 273, 56], [3, 3, 326], [2, 1, 330], [2, 27, 305], [2, 15, 318], [2, 15, 319], [3, 1, 333], [6, 85, 247], [2, 57, 280], [2, 3, 335], [3, 7, 331], [3, 1, 338], [2, 45, 296], [2, 207, 135], [2, 27, 316], [2, 3, 341], [2, 105, 240], [3, 135, 210], [2, 3, 344], [2, 45, 303], [2, 18, 331], [3, 1, 348], [3, 45, 305]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 329 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[2, 48, 304], [2, 45, 308], [2, 45, 309], [2, 255, 100], [2, 27, 329], [3, 1, 355], [2, 1, 357], [2, 3, 356], [2, 105, 255], [3, 95, 265], [2, 78, 284], [3, 5, 357], [2, 1, 363], [2, 105, 260], [2, 15, 351], [2, 60, 307], [2, 87, 281], [2, 60, 309], [3, 238, 131], [2, 357, 14], [2, 273, 99], [2, 1, 372], [2, 45, 329], [2, 15, 360], [2, 27, 349]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 354 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 18, 359], [2, 105, 273], [2, 15, 364], [3, 1, 378], [2, 207, 174], [2, 3, 379], [2, 27, 356], [2, 165, 219], [3, 33, 351], [2, 45, 341], [2, 45, 342], [2, 357, 31], [2, 18, 371], [2, 105, 285], [2, 165, 226], [2, 15, 377], [2, 255, 138], [2, 15, 379], [3, 10, 384], [2, 15, 381], [2, 78, 319], [2, 258, 140], [2, 15, 384], [2, 330, 70], [3, 100, 300]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 379 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[2, 3, 399], [2, 1, 402], [2, 18, 386], [3, 5, 399], [2, 1, 405], [2, 288, 119], [2, 255, 153], [2, 45, 364], [2, 45, 365], [2, 105, 306], [2, 105, 307], [3, 47, 365], [2, 3, 411], [2, 60, 355], [2, 105, 311], [2, 3, 414], [2, 1, 417], [3, 138, 280], [2, 330, 90], [2, 255, 166], [2, 15, 407], [2, 60, 363], [2, 105, 319], [2, 105, 320], [3, 40, 385]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 404 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[3, 1, 425], [2, 3, 425], [2, 273, 156], [2, 60, 370], [2, 150, 281], [2, 105, 327], [2, 18, 415], [2, 105, 329], [2, 45, 390], [2, 45, 391], [2, 27, 410], [2, 87, 351], [2, 3, 436], [2, 165, 275], [2, 330, 111], [3, 52, 389], [2, 3, 440], [3, 7, 436], [2, 15, 430], [2, 60, 386], [2, 258, 189], [2, 1, 447], [2, 105, 344], [2, 150, 300], [2, 417, 34]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 429 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[2, 18, 434], [2, 18, 435], [2, 18, 436], [2, 330, 125], [2, 87, 369], [2, 27, 430], [2, 165, 293], [2, 288, 171], [2, 15, 445], [2, 105, 356], [3, 5, 456], [2, 3, 460], [2, 165, 299], [3, 10, 454], [2, 15, 451], [2, 48, 419], [2, 105, 363], [2, 1, 468], [3, 3, 466], [2, 60, 411], [2, 87, 385], [2, 3, 470], [2, 3, 471], [2, 165, 310], [2, 405, 71]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 454 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 87, 390], [2, 48, 430], [2, 165, 314], [2, 60, 420], [2, 27, 454], [2, 60, 422], [2, 105, 378], [2, 1, 483], [2, 60, 425], [3, 30, 455], [2, 18, 469], [2, 27, 461], [3, 312, 176], [3, 238, 251], [2, 150, 341], [2, 3, 489], [2, 3, 490], [3, 3, 490], [3, 3, 491], [2, 165, 331], [3, 1, 495], [2, 57, 441], [2, 60, 439], [2, 45, 455], [2, 87, 414]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 479 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 18, 484], [2, 60, 443], [3, 3, 500], [2, 15, 490], [2, 255, 251], [3, 10, 496], [2, 1, 507], [2, 273, 236], [2, 105, 405], [2, 15, 496], [2, 45, 467], [2, 15, 498], [2, 3, 511], [2, 60, 455], [2, 330, 186], [2, 273, 244], [2, 288, 230], [2, 150, 369], [2, 405, 115], [2, 165, 356], [2, 60, 462], [2, 1, 522], [3, 12, 511], [2, 330, 195], [3, 110, 415]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 504 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 48, 479], [2, 3, 525], [2, 1, 528], [3, 1, 528], [2, 60, 471], [2, 27, 505], [2, 3, 530], [2, 60, 474], [2, 150, 385], [2, 165, 371], [2, 15, 522], [2, 405, 133], [2, 78, 461], [3, 18, 521], [3, 455, 85], [2, 27, 515], [2, 207, 336], [2, 45, 499], [3, 1, 543], [2, 57, 489], [2, 87, 460], [2, 27, 521], [2, 3, 546], [3, 18, 531], [2, 45, 506]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 529 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 18, 534], [2, 27, 526], [2, 255, 299], [2, 60, 495], [3, 100, 455], [2, 273, 284], [2, 3, 555], [2, 273, 286], [3, 3, 556], [3, 5, 555], [2, 78, 484], [2, 18, 545], [2, 15, 549], [3, 58, 506], [2, 60, 506], [2, 330, 237], [2, 1, 567], [2, 3, 566], [2, 60, 510], [2, 57, 514], [2, 3, 569], [2, 48, 525], [2, 288, 286], [2, 15, 560], [2, 255, 321]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 554 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 258, 319], [2, 150, 428], [2, 150, 429], [2, 105, 475], [2, 405, 176], [2, 3, 579], [2, 3, 580], [2, 48, 536], [3, 3, 581], [2, 1, 585], [2, 483, 104], [2, 288, 300], [2, 150, 439], [2, 15, 575], [2, 87, 504], [2, 60, 532], [2, 45, 548], [2, 585, 9], [3, 1, 593], [3, 270, 325], [2, 3, 594], [2, 18, 580], [2, 45, 554], [3, 33, 566], [2, 357, 244]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 579 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[2, 258, 344], [2, 15, 588], [2, 3, 601], [2, 45, 560], [2, 357, 249], [2, 18, 589], [2, 357, 251], [2, 288, 321], [3, 5, 604], [2, 207, 404], [2, 3, 609], [2, 18, 595], [2, 3, 611], [2, 585, 30], [2, 447, 169], [2, 57, 560], [2, 105, 513], [2, 528, 91], [2, 60, 560], [2, 27, 594], [3, 390, 231], [2, 105, 518], [2, 78, 546], [2, 60, 565], [2, 567, 59]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 604 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[2, 3, 624], [2, 15, 613], [2, 258, 371], [2, 15, 615], [2, 255, 376], [2, 3, 629], [2, 3, 630], [2, 108, 526], [2, 15, 620], [2, 60, 576], [2, 105, 532], [2, 87, 551], [2, 165, 474], [2, 45, 595], [2, 165, 476], [2, 150, 492], [2, 363, 280], [2, 105, 539], [2, 330, 315], [2, 27, 619], [3, 30, 616], [2, 78, 570], [2, 1, 648], [3, 425, 224], [2, 57, 594]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 629 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 108, 544], [2, 108, 545], [2, 45, 609], [2, 105, 550], [2, 15, 641], [2, 48, 609], [2, 273, 385], [2, 528, 131], [3, 170, 489], [2, 45, 616], [2, 60, 602], [2, 18, 645], [2, 273, 391], [3, 10, 654], [2, 45, 621], [2, 60, 607], [2, 108, 560], [2, 15, 654], [2, 585, 85], [3, 385, 285], [2, 258, 414], [2, 1, 672], [2, 150, 524], [2, 585, 90], [3, 25, 650]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 654 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[2, 3, 674], [2, 165, 513], [2, 1, 678], [3, 18, 661], [2, 105, 576], [2, 18, 664], [2, 60, 623], [2, 45, 639], [2, 405, 280], [3, 110, 575], [2, 288, 399], [2, 3, 685], [2, 3, 686], [2, 45, 645], [2, 27, 664], [2, 405, 287], [2, 57, 636], [2, 3, 691], [2, 150, 545], [2, 27, 669], [2, 105, 592], [2, 27, 671], [2, 18, 681], [2, 330, 370], [2, 255, 446]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 679 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 3, 699], [3, 10, 692], [2, 18, 686], [2, 45, 660], [3, 25, 680], [2, 15, 692], [3, 5, 702], [2, 78, 631], [2, 45, 665], [2, 15, 696], [2, 417, 295], [2, 48, 665], [3, 1, 712], [3, 18, 696], [2, 27, 689], [2, 357, 360], [2, 15, 703], [2, 48, 671], [3, 18, 701], [2, 447, 274], [2, 3, 719], [2, 27, 696], [2, 648, 76], [2, 45, 680], [2, 57, 669]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 704 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 48, 679], [2, 27, 701], [2, 15, 714], [2, 15, 715], [3, 170, 560], [3, 12, 719], [2, 18, 715], [2, 48, 686], [2, 105, 630], [3, 45, 690], [2, 15, 722], [2, 3, 735], [2, 288, 451], [2, 165, 575], [2, 567, 174], [2, 468, 274], [2, 45, 698], [2, 48, 696], [3, 3, 741], [2, 105, 641], [2, 108, 639], [2, 48, 700], [2, 48, 701], [3, 33, 716], [2, 1, 750]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 729 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[2, 108, 644], [2, 3, 750], [2, 3, 751], [2, 105, 650], [2, 357, 399], [2, 87, 670], [2, 18, 740], [2, 45, 714], [2, 15, 745], [2, 672, 89], [2, 48, 714], [2, 57, 706], [2, 78, 686], [3, 268, 496], [2, 27, 739], [2, 15, 752], [2, 15, 753], [2, 105, 664], [3, 38, 731], [3, 70, 700], [2, 57, 715], [2, 3, 770], [2, 528, 246], [3, 1, 773], [2, 672, 104]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 754 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[2, 48, 729], [2, 45, 733], [2, 165, 614], [3, 385, 394], [2, 1, 780], [2, 78, 704], [2, 27, 756], [2, 750, 34], [3, 5, 779], [2, 27, 759], [2, 648, 139], [2, 3, 785], [2, 3, 786], [3, 18, 771], [2, 330, 461], [2, 507, 285], [2, 1, 792], [2, 60, 734], [2, 165, 630], [2, 567, 229], [2, 363, 434], [2, 27, 771], [2, 45, 754], [2, 105, 695], [2, 60, 741]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 779 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[2, 165, 637], [2, 78, 725], [2, 60, 744], [2, 105, 700], [2, 255, 551], [2, 18, 789], [2, 27, 781]]
theorem len32 : w32.length = 7 := rfl
theorem ok32 : checkList 804 w32 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `4 ≤ n ≤ 810` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 4 ≤ n) (h2 : n ≤ 810) : ∃ x, good n x = true := by
  by_cases c0 : n < 29
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 54
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 79
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 104
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 129
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 154
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 179
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 204
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 229
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 254
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 279
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 304
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 329
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 354
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 379
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 404
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 429
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 454
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 479
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 504
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 529
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 554
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 579
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 604
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 629
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 654
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 679
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 704
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 729
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 754
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 779
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 804
  · exact chunk ok31 len31 (by omega) (by omega)
  exact chunk ok32 len32 (by omega) (by omega)

end OMA.Aoeis_a229974Tab

open OMA.Aoeis_a229974Tab in
theorem OMA.solution : OMA.R_oeis_a229974_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
