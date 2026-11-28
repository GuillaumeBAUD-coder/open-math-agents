import OMAReductions.R_OeisA229969_conjecture_4_R1
import Mathlib

-- Step OeisA229969.conjecture_4.R1.H1: hypothesis H1 of reduction OeisA229969.conjecture_4.R1
-- Credit: @prathameshnium. Finite check for 5 ≤ n ≤ 1004.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1015501.

/-! Step OeisA229969.conjecture_4.R1.H1. -/

namespace OMA.AOeisA229969_conjecture_4Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1009` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1009 2

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
  have hnd := noDiv_sound p 1009 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y, z] => (decide (0 < y) && (decide (0 < z) && (decide (x + y + z = n) && (decide (x = 3 ∨ x = 6) && (isPrimeB (2 * y + 1) && (isPrimeB (2 * x * y * z - 1) && isPrimeB (2 * x * y * z + 1)))))))
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
      (x = 3 ∨ x = 6) ∧
      (2 * y + 1).Prime ∧ (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime := by
  unfold core at h
  split at h
  next x y z =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨x, y, z, a0, a1, a2, a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 5, …, 1004`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 1, 1], [3, 1, 2], [3, 1, 3], [6, 1, 1], [3, 1, 5], [3, 2, 5], [3, 1, 7], [6, 1, 5], [6, 1, 6], [3, 1, 10], [3, 8, 4], [3, 1, 12], [3, 3, 11], [6, 2, 10], [6, 9, 4], [3, 2, 15], [3, 1, 17], [3, 1, 18], [6, 1, 16], [3, 2, 19], [3, 2, 20], [6, 1, 19], [3, 1, 23], [3, 5, 20], [3, 1, 25]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 5 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 3, 24], [3, 2, 26], [3, 6, 23], [6, 1, 26], [3, 1, 30], [3, 3, 29], [3, 1, 32], [3, 1, 33], [6, 5, 27], [6, 9, 24], [3, 2, 35], [3, 2, 36], [3, 1, 38], [6, 1, 36], [3, 1, 40], [3, 18, 24], [3, 11, 32], [6, 8, 33], [6, 6, 36], [3, 1, 45], [3, 8, 39], [3, 1, 47], [3, 3, 46], [6, 21, 26], [3, 6, 45]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 30 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 2, 50], [3, 1, 52], [6, 1, 50], [6, 15, 37], [3, 11, 45], [3, 2, 55], [3, 6, 52], [3, 1, 58], [6, 2, 55], [3, 54, 7], [3, 3, 59], [6, 56, 4], [3, 6, 58], [3, 30, 35], [3, 56, 10], [3, 3, 64], [3, 26, 42], [3, 6, 63], [3, 5, 65], [3, 1, 70], [6, 2, 67], [3, 1, 72], [3, 3, 71], [6, 5, 67], [3, 5, 71]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 55 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 9, 68], [3, 1, 77], [6, 5, 71], [3, 15, 65], [3, 69, 12], [3, 78, 4], [6, 2, 78], [3, 9, 75], [3, 15, 70], [3, 9, 77], [3, 2, 85], [3, 1, 87], [6, 1, 85], [6, 1, 86], [3, 11, 80], [6, 2, 87], [3, 2, 91], [3, 6, 88], [6, 1, 91], [3, 1, 95], [3, 8, 89], [3, 2, 96], [3, 15, 84], [6, 1, 96], [3, 1, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 80 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 9, 93], [3, 21, 82], [3, 1, 103], [3, 5, 100], [3, 99, 7], [3, 3, 104], [3, 1, 107], [3, 5, 104], [6, 95, 12], [3, 1, 110], [3, 2, 110], [6, 2, 108], [6, 1, 110], [3, 5, 110], [3, 5, 111], [6, 2, 112], [6, 2, 113], [3, 3, 116], [3, 95, 25], [3, 2, 119], [3, 3, 119], [6, 1, 119], [6, 5, 116], [6, 1, 121], [3, 2, 124]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 105 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[6, 114, 10], [6, 1, 124], [3, 3, 126], [6, 2, 125], [3, 29, 102], [3, 119, 13], [3, 3, 130], [6, 5, 126], [6, 2, 130], [3, 1, 135], [3, 2, 135], [3, 1, 137], [3, 1, 138], [3, 5, 135], [3, 2, 139], [6, 30, 109], [6, 1, 139], [3, 1, 143], [6, 2, 140], [3, 5, 141], [3, 3, 144], [3, 1, 147], [3, 9, 140], [3, 30, 120], [3, 2, 149]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 130 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[6, 2, 147], [6, 1, 149], [3, 11, 143], [6, 5, 147], [6, 140, 13], [3, 153, 4], [3, 2, 156], [3, 11, 148], [6, 1, 156], [3, 26, 135], [6, 2, 157], [3, 2, 161], [3, 8, 156], [6, 1, 161], [6, 9, 154], [3, 155, 12], [3, 3, 165], [3, 6, 163], [6, 5, 162], [3, 1, 170], [3, 5, 167], [3, 1, 172], [6, 8, 163], [3, 5, 170], [3, 1, 175]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 155 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[6, 2, 172], [3, 1, 177], [3, 3, 176], [6, 1, 176], [3, 5, 176], [3, 9, 173], [3, 1, 182], [3, 3, 181], [6, 11, 171], [3, 11, 175], [3, 18, 169], [3, 3, 185], [3, 5, 184], [3, 105, 85], [3, 2, 189], [3, 20, 172], [3, 1, 192], [6, 5, 186], [3, 35, 160], [3, 186, 10], [3, 2, 195], [6, 179, 16], [6, 1, 195], [3, 5, 195], [3, 5, 196]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 180 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[3, 3, 199], [6, 5, 195], [3, 200, 4], [6, 2, 200], [3, 1, 205], [3, 3, 204], [3, 5, 203], [3, 6, 203], [6, 75, 132], [6, 9, 199], [6, 2, 207], [3, 18, 195], [3, 1, 213], [3, 5, 210], [3, 1, 215], [3, 3, 214], [3, 1, 217], [3, 209, 10], [6, 1, 216], [3, 1, 220], [3, 8, 214], [6, 2, 218], [3, 5, 219], [6, 2, 220], [3, 2, 224]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 205 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 5, 222], [6, 1, 224], [3, 11, 218], [6, 1, 226], [3, 5, 226], [3, 9, 223], [3, 21, 212], [3, 3, 231], [6, 2, 230], [6, 5, 228], [3, 5, 232], [3, 3, 235], [3, 1, 238], [6, 2, 235], [3, 209, 32], [3, 53, 189], [3, 1, 242], [3, 3, 241], [6, 11, 231], [3, 239, 7], [3, 20, 227], [3, 1, 247], [3, 1, 248], [6, 2, 245], [3, 6, 245]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 230 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 2, 250], [3, 11, 242], [6, 1, 250], [3, 15, 240], [3, 6, 250], [3, 5, 252], [3, 5, 253], [3, 228, 31], [6, 245, 12], [3, 14, 247], [3, 2, 260], [3, 8, 255], [6, 1, 260], [3, 20, 245], [3, 2, 264], [3, 9, 258], [6, 1, 264], [3, 1, 268], [6, 2, 265], [3, 1, 270], [3, 5, 267], [3, 2, 271], [6, 6, 265], [6, 1, 271], [3, 6, 270]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 255 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[3, 2, 275], [6, 2, 273], [3, 1, 278], [6, 95, 182], [3, 20, 261], [3, 2, 280], [3, 2, 281], [3, 1, 283], [6, 1, 281], [3, 5, 281], [3, 270, 17], [3, 1, 287], [3, 21, 268], [6, 6, 281], [3, 2, 289], [3, 285, 7], [6, 1, 289], [3, 39, 255], [6, 2, 290], [3, 2, 294], [3, 2, 295], [6, 1, 294], [3, 1, 298], [3, 20, 280], [6, 5, 293]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 280 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[6, 2, 297], [3, 293, 10], [3, 3, 301], [3, 5, 300], [3, 11, 295], [3, 288, 19], [3, 2, 306], [3, 8, 301], [6, 1, 306], [6, 14, 294], [3, 8, 304], [3, 1, 312], [3, 1, 313], [3, 65, 250], [3, 2, 314], [3, 3, 314], [6, 1, 314], [3, 315, 4], [6, 2, 315], [3, 15, 306], [3, 3, 319], [3, 1, 322], [3, 308, 16], [6, 1, 321], [3, 1, 325]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 305 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[6, 320, 4], [3, 3, 325], [3, 3, 326], [6, 320, 7], [3, 6, 325], [3, 320, 12], [3, 326, 7], [3, 1, 333], [6, 156, 176], [3, 5, 331], [3, 2, 335], [6, 6, 329], [3, 1, 338], [6, 6, 331], [3, 329, 12], [6, 2, 337], [3, 2, 341], [3, 21, 323], [6, 1, 341], [3, 2, 344], [3, 9, 338], [3, 1, 347], [3, 1, 348], [6, 26, 321], [3, 14, 337]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 330 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 9, 343], [3, 1, 352], [3, 11, 343], [3, 5, 350], [3, 1, 355], [3, 2, 355], [3, 1, 357], [6, 1, 355], [6, 1, 356], [3, 354, 7], [3, 5, 357], [3, 15, 348], [3, 14, 350], [6, 345, 17], [3, 14, 352], [3, 3, 364], [3, 3, 365], [3, 11, 358], [6, 345, 22], [3, 359, 12], [6, 5, 364], [3, 3, 370], [3, 1, 373], [6, 350, 22], [3, 330, 46]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 355 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 5, 372], [3, 371, 7], [3, 1, 378], [6, 2, 375], [3, 2, 379], [6, 369, 10], [6, 1, 379], [3, 8, 376], [6, 5, 377], [3, 1, 385], [6, 5, 379], [3, 5, 383], [3, 3, 386], [6, 2, 385], [3, 1, 390], [6, 5, 384], [3, 6, 387], [3, 384, 10], [3, 5, 390], [3, 9, 387], [3, 393, 4], [3, 1, 397], [3, 3, 396], [3, 15, 385], [3, 2, 399]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 380 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[3, 2, 400], [6, 1, 399], [6, 1, 400], [3, 90, 315], [6, 33, 370], [3, 9, 398], [3, 380, 28], [3, 3, 406], [6, 2, 405], [6, 5, 403], [6, 2, 407], [3, 2, 411], [3, 14, 400], [6, 1, 411], [3, 2, 414], [3, 404, 13], [6, 1, 414], [3, 3, 416], [6, 11, 406], [3, 414, 7], [6, 2, 417], [3, 3, 420], [6, 6, 415], [3, 15, 410], [3, 1, 425]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 405 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[3, 2, 425], [3, 18, 410], [6, 1, 425], [3, 20, 410], [3, 404, 27], [3, 428, 4], [3, 1, 432], [3, 3, 431], [6, 35, 397], [3, 9, 427], [3, 14, 423], [3, 2, 436], [6, 11, 425], [6, 1, 436], [3, 410, 31], [3, 2, 440], [3, 6, 437], [3, 1, 443], [6, 6, 436], [6, 8, 435], [3, 20, 427], [3, 3, 445], [3, 1, 448], [3, 35, 415], [3, 15, 436]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 430 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 14, 438], [3, 1, 452], [3, 15, 439], [3, 375, 80], [3, 1, 455], [3, 398, 59], [3, 8, 450], [3, 8, 451], [6, 15, 442], [3, 5, 456], [3, 2, 460], [3, 6, 457], [6, 1, 460], [6, 6, 456], [3, 1, 465], [6, 5, 459], [3, 1, 467], [3, 3, 466], [6, 2, 465], [6, 464, 4], [3, 2, 470], [3, 2, 471], [6, 1, 470], [6, 1, 471], [3, 459, 17]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 455 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[3, 473, 4], [6, 2, 473], [3, 6, 473], [3, 5, 475], [3, 14, 467], [3, 20, 462], [3, 476, 7], [3, 6, 478], [6, 5, 477], [3, 470, 16], [3, 20, 467], [3, 8, 480], [3, 6, 483], [3, 5, 485], [3, 2, 489], [3, 2, 490], [6, 1, 489], [6, 1, 490], [3, 455, 40], [3, 1, 495], [3, 473, 24], [6, 2, 493], [3, 6, 493], [3, 15, 485], [3, 1, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 480 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[6, 15, 484], [3, 3, 500], [3, 9, 495], [3, 135, 370], [6, 5, 498], [3, 9, 498], [6, 2, 503], [6, 8, 498], [6, 50, 457], [3, 9, 502], [3, 485, 27], [3, 2, 511], [3, 510, 4], [6, 1, 511], [3, 5, 511], [3, 5, 512], [6, 20, 495], [3, 9, 510], [6, 6, 511], [3, 1, 520], [3, 3, 519], [3, 18, 505], [3, 14, 510], [3, 105, 420], [3, 9, 517]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 505 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 2, 525], [3, 33, 495], [3, 1, 528], [6, 5, 522], [3, 15, 516], [3, 2, 530], [3, 18, 515], [6, 1, 530], [3, 495, 40], [3, 6, 530], [3, 39, 498], [3, 3, 535], [3, 9, 530], [3, 455, 85], [3, 14, 527], [3, 525, 17], [3, 1, 542], [3, 1, 543], [3, 15, 530], [3, 5, 541], [6, 2, 542], [3, 2, 546], [3, 11, 538], [6, 1, 546], [3, 1, 550]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 530 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[3, 8, 544], [3, 95, 458], [3, 11, 543], [6, 11, 541], [3, 1, 555], [3, 2, 555], [3, 15, 543], [6, 1, 555], [3, 5, 555], [3, 1, 560], [3, 23, 539], [3, 1, 562], [3, 15, 549], [6, 36, 526], [3, 1, 565], [3, 2, 565], [3, 2, 566], [6, 1, 565], [6, 1, 566], [3, 2, 569], [3, 15, 557], [6, 1, 569], [3, 56, 518], [6, 2, 570], [3, 21, 555]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 555 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[3, 3, 574], [3, 1, 577], [3, 1, 578], [6, 15, 562], [3, 2, 579], [3, 2, 580], [6, 1, 579], [6, 1, 580], [3, 575, 10], [3, 36, 550], [3, 8, 579], [3, 3, 585], [3, 1, 588], [3, 30, 560], [3, 1, 590], [3, 30, 562], [3, 33, 560], [3, 1, 593], [6, 35, 557], [3, 2, 594], [3, 30, 567], [3, 1, 597], [3, 33, 566], [6, 15, 582], [3, 29, 572]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 580 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[3, 5, 597], [3, 2, 601], [6, 6, 595], [6, 1, 601], [3, 6, 600], [6, 2, 602], [3, 3, 605], [3, 5, 604], [3, 15, 595], [3, 2, 609], [3, 608, 4], [3, 1, 612], [3, 21, 593], [6, 1, 611], [6, 18, 595], [3, 9, 608], [3, 3, 615], [3, 9, 610], [6, 600, 17], [6, 5, 613], [3, 15, 607], [3, 3, 620], [3, 8, 616], [3, 615, 10], [3, 2, 624]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 605 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[3, 615, 12], [6, 1, 624], [3, 1, 628], [6, 20, 607], [3, 2, 629], [3, 2, 630], [6, 1, 629], [6, 1, 630], [6, 11, 621], [3, 21, 615], [3, 18, 619], [3, 1, 637], [3, 30, 609], [3, 140, 500], [3, 5, 636], [6, 2, 637], [3, 1, 642], [3, 51, 593], [6, 2, 640], [3, 6, 640], [3, 14, 633], [6, 638, 7], [6, 5, 641], [6, 15, 632], [3, 5, 646]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 630 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[3, 14, 638], [3, 3, 650], [3, 1, 653], [6, 15, 637], [3, 1, 655], [6, 2, 652], [6, 651, 4], [3, 8, 651], [3, 35, 625], [3, 11, 650], [3, 8, 654], [6, 11, 649], [3, 6, 658], [6, 11, 651], [6, 35, 628], [6, 2, 662], [3, 1, 667], [3, 8, 661], [6, 660, 7], [3, 1, 670], [3, 3, 669], [6, 6, 664], [3, 14, 660], [6, 11, 661], [3, 1, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 655 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[6, 14, 660], [6, 1, 674], [3, 11, 668], [6, 6, 671], [6, 9, 669], [3, 9, 673], [3, 1, 682], [3, 36, 648], [6, 651, 31], [3, 35, 651], [3, 2, 685], [3, 2, 686], [3, 1, 688], [6, 1, 686], [3, 644, 47], [3, 8, 684], [3, 2, 691], [3, 1, 693], [6, 1, 691], [6, 15, 678], [3, 8, 689], [6, 2, 693], [3, 15, 684], [6, 5, 692], [3, 2, 699]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 680 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[3, 14, 688], [6, 1, 699], [3, 1, 703], [3, 680, 25], [3, 1, 705], [3, 5, 702], [3, 1, 707], [3, 6, 703], [3, 30, 680], [3, 1, 710], [3, 690, 22], [3, 1, 712], [3, 18, 696], [3, 20, 695], [6, 15, 698], [3, 8, 709], [6, 711, 4], [3, 8, 711], [6, 21, 696], [3, 2, 719], [6, 2, 717], [6, 1, 719], [3, 1, 723], [3, 5, 720], [6, 719, 4]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 705 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[3, 8, 719], [6, 6, 719], [3, 11, 718], [6, 5, 722], [3, 719, 12], [3, 9, 723], [3, 5, 728], [3, 8, 726], [6, 725, 7], [3, 14, 722], [3, 2, 735], [3, 1, 737], [6, 1, 735], [6, 36, 701], [6, 14, 724], [3, 5, 737], [3, 8, 735], [3, 3, 741], [3, 15, 730], [6, 5, 738], [3, 740, 7], [3, 1, 747], [6, 6, 740], [6, 716, 31], [3, 744, 7]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 730 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[3, 2, 750], [3, 2, 751], [3, 1, 753], [6, 1, 751], [3, 11, 745], [6, 2, 752], [6, 8, 747], [3, 1, 758], [6, 2, 755], [6, 5, 753], [3, 713, 49], [3, 3, 760], [3, 15, 749], [6, 755, 7], [3, 20, 746], [6, 2, 762], [6, 2, 763], [3, 8, 761], [6, 735, 32], [3, 6, 765], [3, 2, 770], [3, 5, 768], [3, 1, 773], [6, 21, 751], [3, 1, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 755 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[3, 3, 774], [3, 6, 772], [6, 6, 770], [6, 11, 766], [6, 15, 763], [6, 5, 774], [3, 8, 775], [3, 5, 779], [6, 765, 17], [3, 779, 7], [3, 2, 785], [3, 1, 787], [6, 1, 785], [6, 1, 786], [3, 11, 780], [3, 785, 7], [6, 2, 788], [3, 5, 789], [3, 15, 780], [3, 21, 775], [3, 15, 782], [6, 6, 789], [3, 1, 798], [6, 2, 795], [3, 1, 800]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 780 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[3, 5, 797], [6, 5, 795], [3, 14, 790], [6, 125, 677], [3, 21, 785], [3, 800, 7], [6, 6, 799], [3, 8, 801], [6, 5, 802], [3, 5, 806], [3, 2, 810], [6, 21, 789], [6, 1, 810], [3, 125, 690], [3, 2, 814], [6, 5, 809], [6, 1, 814], [3, 5, 814], [6, 6, 811], [6, 5, 813], [3, 68, 754], [3, 1, 822], [6, 56, 765], [6, 30, 792], [3, 14, 812]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 805 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[3, 53, 774], [6, 2, 823], [3, 1, 828], [3, 75, 755], [3, 21, 810], [3, 14, 818], [6, 11, 819], [3, 14, 820], [6, 6, 826], [3, 1, 835], [3, 833, 4], [3, 1, 837], [3, 15, 824], [6, 5, 832], [3, 2, 839], [3, 20, 822], [6, 1, 839], [3, 3, 841], [6, 1, 841], [6, 9, 834], [3, 2, 845], [6, 2, 843], [6, 1, 845], [3, 740, 110], [3, 1, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 830 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[3, 5, 847], [3, 6, 847], [3, 5, 849], [6, 26, 826], [6, 9, 844], [3, 29, 828], [3, 2, 856], [3, 8, 851], [6, 1, 856], [3, 11, 850], [6, 5, 854], [3, 2, 861], [3, 860, 4], [6, 1, 861], [6, 5, 858], [3, 8, 859], [3, 35, 833], [3, 9, 860], [6, 5, 862], [3, 2, 869], [3, 3, 869], [3, 1, 872], [3, 6, 868], [6, 26, 846], [3, 6, 870]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 855 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[3, 2, 875], [3, 6, 872], [6, 1, 875], [3, 5, 875], [3, 1, 880], [3, 75, 807], [3, 876, 7], [3, 846, 38], [6, 15, 867], [6, 873, 10], [6, 15, 869], [6, 2, 883], [6, 5, 881], [6, 30, 857], [3, 21, 870], [3, 23, 869], [6, 6, 884], [3, 809, 85], [3, 5, 890], [3, 5, 891], [3, 30, 867], [3, 888, 10], [3, 15, 884], [6, 6, 891], [3, 5, 896]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 880 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3, 29, 873], [3, 891, 12], [3, 1, 903], [6, 2, 900], [3, 20, 886], [3, 2, 905], [3, 1, 907], [6, 1, 905], [6, 861, 46], [3, 56, 855], [3, 3, 909], [3, 5, 908], [3, 1, 913], [6, 2, 910], [6, 15, 898], [3, 3, 914], [3, 1, 917], [6, 6, 910], [3, 65, 855], [3, 1, 920], [3, 900, 22], [3, 5, 918], [3, 9, 915], [3, 15, 910], [6, 9, 914]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 905 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[3, 3, 924], [3, 3, 925], [3, 18, 911], [3, 5, 925], [3, 9, 922], [3, 2, 930], [3, 2, 931], [6, 1, 930], [6, 1, 931], [3, 15, 921], [6, 2, 932], [3, 3, 935], [3, 6, 933], [6, 915, 22], [3, 1, 940], [3, 3, 939], [3, 1, 942], [3, 1, 943], [3, 935, 10], [3, 20, 926], [3, 114, 833], [3, 2, 946], [3, 3, 946], [6, 1, 946], [3, 56, 895]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 930 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[3, 5, 947], [3, 23, 930], [3, 6, 948], [6, 6, 946], [3, 21, 935], [6, 9, 945], [3, 1, 957], [3, 3, 956], [3, 50, 910], [3, 20, 941], [3, 14, 948], [3, 956, 7], [6, 21, 940], [6, 2, 960], [3, 11, 955], [3, 44, 923], [3, 20, 948], [3, 3, 966], [6, 6, 961], [3, 21, 950], [3, 965, 7], [6, 5, 965], [3, 6, 968], [3, 965, 10], [3, 1, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 955 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[3, 2, 975], [6, 11, 964], [3, 1, 978], [6, 930, 47], [3, 1, 980], [3, 9, 973], [3, 11, 972], [3, 3, 981], [3, 5, 980], [3, 6, 980], [3, 975, 12], [3, 2, 986], [3, 3, 986], [6, 1, 986], [3, 974, 17], [6, 2, 987], [3, 6, 987], [3, 3, 991], [6, 5, 987], [6, 8, 985], [3, 2, 995], [3, 3, 995], [6, 1, 995], [6, 975, 22], [3, 5, 996]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 980 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `5 ≤ n ≤ 1004` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 5 ≤ n) (h2 : n ≤ 1004) : ∃ x, good n x = true := by
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
  by_cases c8 : n < 230
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 255
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 280
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 305
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 330
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 355
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 380
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 405
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 430
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 455
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 480
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 505
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 530
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 555
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 580
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 605
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 630
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 655
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 680
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 705
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 730
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 755
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 780
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 805
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 830
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 855
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 880
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 905
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 930
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 955
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 980
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA229969_conjecture_4Tab

open OMA.AOeisA229969_conjecture_4Tab in
theorem OMA.solution : OMA.R_OeisA229969_conjecture_4_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
