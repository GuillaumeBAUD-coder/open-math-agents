import OMAReductions.R_oeis_a230252_R1
import Mathlib

-- Step oeis-a230252.R1.H1: hypothesis H1 of reduction oeis-a230252.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 890.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 771763.

/-! Step oeis-a230252.R1.H1. -/

namespace OMA.Aoeis_a230252Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `880` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 880 2

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
  have hnd := noDiv_sound p 880 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (2 * x + 1) && (isPrimeB (x ^ 2 + x + 1) && isPrimeB (y ^ 2 + y + 1))))))
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
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x + 1).Prime ∧ (x ^ 2 + x + 1).Prime ∧ (y ^ 2 + y + 1).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 890`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [1, 3], [2, 3], [1, 5], [1, 6], [2, 6], [1, 8], [2, 8], [3, 8], [6, 6], [1, 12], [2, 12], [1, 14], [1, 15], [2, 15], [1, 17], [2, 17], [3, 17], [1, 20], [1, 21], [2, 21], [3, 21], [1, 24], [2, 24]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 24], [1, 27], [2, 27], [3, 27], [14, 17], [5, 27], [6, 27], [1, 33], [2, 33], [3, 33], [20, 17], [5, 33], [1, 38], [2, 38], [3, 38], [1, 41], [2, 41], [3, 41], [21, 24], [5, 41], [6, 41], [15, 33], [8, 41], [33, 17], [1, 50]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 50], [3, 50], [21, 33], [1, 54], [2, 54], [3, 54], [1, 57], [2, 57], [1, 59], [2, 59], [3, 59], [1, 62], [2, 62], [3, 62], [33, 33], [1, 66], [2, 66], [3, 66], [1, 69], [2, 69], [1, 71], [2, 71], [3, 71], [6, 69], [1, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[2, 75], [1, 77], [1, 78], [2, 78], [1, 80], [2, 80], [3, 80], [6, 78], [5, 80], [6, 80], [21, 66], [8, 80], [14, 75], [1, 89], [1, 90], [2, 90], [3, 90], [5, 89], [5, 90], [6, 90], [8, 89], [8, 90], [21, 78], [1, 99], [2, 99]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1, 101], [2, 101], [3, 101], [6, 99], [1, 105], [2, 105], [3, 105], [8, 101], [5, 105], [1, 110], [1, 111], [2, 111], [3, 111], [5, 110], [5, 111], [6, 111], [1, 117], [2, 117], [1, 119], [2, 119], [3, 119], [6, 117], [5, 119], [6, 119], [15, 111]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[8, 119], [50, 78], [54, 75], [20, 110], [14, 117], [1, 131], [2, 131], [3, 131], [69, 66], [5, 131], [6, 131], [21, 117], [1, 138], [2, 138], [3, 138], [1, 141], [2, 141], [1, 143], [2, 143], [3, 143], [6, 141], [1, 147], [2, 147], [3, 147], [1, 150]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 150], [3, 150], [1, 153], [2, 153], [1, 155], [2, 155], [3, 155], [6, 153], [5, 155], [6, 155], [1, 161], [1, 162], [2, 162], [1, 164], [2, 164], [3, 164], [1, 167], [1, 168], [2, 168], [3, 168], [5, 167], [5, 168], [1, 173], [2, 173], [3, 173]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[1, 176], [2, 176], [3, 176], [33, 147], [5, 176], [6, 176], [15, 168], [8, 176], [21, 164], [33, 153], [14, 173], [15, 173], [1, 188], [1, 189], [2, 189], [3, 189], [1, 192], [2, 192], [1, 194], [2, 194], [3, 194], [6, 192], [5, 194], [6, 194], [33, 168]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[8, 194], [14, 189], [1, 203], [2, 203], [3, 203], [1, 206], [2, 206], [3, 206], [1, 209], [2, 209], [3, 209], [21, 192], [5, 209], [6, 209], [1, 215], [2, 215], [3, 215], [1, 218], [2, 218], [3, 218], [33, 189], [5, 218], [6, 218], [33, 192], [8, 218]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[21, 206], [75, 153], [14, 215], [15, 215], [69, 162], [1, 231], [2, 231], [3, 231], [20, 215], [5, 231], [1, 236], [2, 236], [3, 236], [78, 162], [5, 236], [6, 236], [54, 189], [8, 236], [14, 231], [1, 245], [1, 246], [2, 246], [3, 246], [5, 245], [5, 246]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[6, 246], [8, 245], [8, 246], [105, 150], [20, 236], [21, 236], [69, 189], [14, 245], [14, 246], [15, 246], [89, 173], [54, 209], [33, 231], [20, 245], [20, 246], [1, 266], [2, 266], [3, 266], [78, 192], [5, 266], [6, 266], [1, 272], [2, 272], [3, 272], [138, 138]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[5, 272], [6, 272], [1, 278], [1, 279], [2, 279], [3, 279], [5, 278], [5, 279], [6, 279], [8, 278], [8, 279], [1, 287], [1, 288], [2, 288], [1, 290], [2, 290], [3, 290], [1, 293], [2, 293], [3, 293], [105, 192], [5, 293], [6, 293], [21, 279], [8, 293]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[14, 288], [15, 288], [14, 290], [15, 290], [75, 231], [14, 293], [15, 293], [21, 288], [1, 309], [2, 309], [3, 309], [20, 293], [5, 309], [1, 314], [2, 314], [3, 314], [168, 150], [5, 314], [6, 314], [33, 288], [8, 314], [14, 309], [15, 309], [89, 236], [33, 293]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[138, 189], [14, 314], [15, 314], [1, 329], [2, 329], [3, 329], [1, 332], [2, 332], [3, 332], [90, 246], [1, 336], [2, 336], [3, 336], [8, 332], [5, 336], [6, 336], [1, 342], [2, 342], [1, 344], [2, 344], [3, 344], [6, 342], [1, 348], [2, 348], [3, 348]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[1, 351], [2, 351], [3, 351], [41, 314], [5, 351], [6, 351], [1, 357], [2, 357], [3, 357], [89, 272], [5, 357], [6, 357], [20, 344], [8, 357], [15, 351], [89, 278], [20, 348], [21, 348], [1, 369], [2, 369], [3, 369], [41, 332], [5, 369], [6, 369], [89, 287]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[8, 369], [21, 357], [1, 378], [2, 378], [3, 378], [1, 381], [2, 381], [1, 383], [2, 383], [3, 383], [6, 381], [5, 383], [6, 383], [21, 369], [8, 383], [14, 378], [1, 392], [2, 392], [3, 392], [1, 395], [2, 395], [3, 395], [1, 398], [2, 398], [3, 398]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[21, 381], [1, 402], [2, 402], [1, 404], [1, 405], [2, 405], [3, 405], [5, 404], [5, 405], [6, 405], [8, 404], [8, 405], [33, 381], [1, 414], [2, 414], [1, 416], [2, 416], [3, 416], [6, 414], [5, 416], [6, 416], [21, 402], [8, 416], [20, 405], [21, 405]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[1, 426], [2, 426], [3, 426], [14, 416], [5, 426], [6, 426], [41, 392], [8, 426], [1, 434], [1, 435], [2, 435], [3, 435], [5, 434], [5, 435], [6, 435], [8, 434], [8, 435], [75, 369], [41, 404], [20, 426], [21, 426], [1, 447], [2, 447], [3, 447], [119, 332]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[5, 447], [6, 447], [1, 453], [2, 453], [1, 455], [1, 456], [2, 456], [3, 456], [5, 455], [5, 456], [6, 456], [8, 455], [8, 456], [453, 12], [50, 416], [14, 453], [15, 453], [14, 455], [14, 456], [15, 456], [89, 383], [20, 453], [21, 453], [20, 455], [20, 456]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1, 476], [2, 476], [3, 476], [33, 447], [5, 476], [6, 476], [69, 414], [8, 476], [50, 435], [33, 453], [89, 398], [33, 455], [33, 456], [1, 489], [2, 489], [3, 489], [89, 404], [5, 489], [6, 489], [1, 495], [2, 495], [3, 495], [155, 344], [5, 495], [1, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 500], [3, 500], [15, 489], [5, 500], [6, 500], [54, 453], [8, 500], [14, 495], [15, 495], [119, 392], [78, 434], [1, 512], [2, 512], [3, 512], [21, 495], [5, 512], [6, 512], [1, 518], [2, 518], [3, 518], [33, 489], [5, 518], [6, 518], [69, 456], [1, 525]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 525], [3, 525], [131, 398], [5, 525], [1, 530], [1, 531], [2, 531], [1, 533], [2, 533], [3, 533], [6, 531], [1, 537], [2, 537], [3, 537], [1, 540], [2, 540], [3, 540], [14, 530], [5, 540], [6, 540], [14, 533], [8, 540], [54, 495], [20, 530], [14, 537]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[1, 551], [2, 551], [3, 551], [1, 554], [2, 554], [3, 554], [21, 537], [5, 554], [6, 554], [1, 560], [2, 560], [3, 560], [33, 531], [5, 560], [6, 560], [1, 566], [1, 567], [2, 567], [3, 567], [5, 566], [5, 567], [1, 572], [2, 572], [3, 572], [141, 435]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[5, 572], [6, 572], [54, 525], [1, 579], [2, 579], [3, 579], [1, 582], [2, 582], [1, 584], [2, 584], [3, 584], [6, 582], [5, 584], [6, 584], [54, 537], [8, 584], [14, 579], [15, 579], [41, 554], [14, 582], [15, 582], [14, 584], [15, 584], [21, 579], [41, 560]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[20, 582], [21, 582], [1, 603], [2, 603], [1, 605], [2, 605], [3, 605], [6, 603], [1, 609], [2, 609], [3, 609], [1, 612], [2, 612], [3, 612], [50, 566], [5, 612], [6, 612], [14, 605], [8, 612], [54, 567], [1, 621], [2, 621], [3, 621], [1, 624], [2, 624]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[1, 626], [2, 626], [3, 626], [6, 624], [5, 626], [6, 626], [21, 612], [8, 626], [14, 621], [1, 635], [2, 635], [3, 635], [15, 624], [5, 635], [6, 635], [21, 621], [1, 642], [2, 642], [1, 644], [2, 644], [3, 644], [6, 642], [5, 644], [6, 644], [69, 582]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[8, 644], [41, 612], [33, 621], [20, 635], [14, 642], [15, 642], [14, 644], [15, 644], [78, 582], [89, 572], [20, 642], [21, 642], [20, 644], [21, 644], [54, 612], [41, 626], [33, 635], [1, 668], [2, 668], [3, 668], [1, 671], [2, 671], [3, 671], [33, 642], [5, 671]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[6, 671], [1, 677], [2, 677], [3, 677], [69, 612], [5, 677], [6, 677], [75, 609], [8, 677], [15, 671], [1, 686], [2, 686], [3, 686], [69, 621], [5, 686], [6, 686], [69, 624], [8, 686], [69, 626], [54, 642], [1, 696], [2, 696], [3, 696], [14, 686], [5, 696]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[1, 701], [2, 701], [3, 701], [138, 567], [5, 701], [6, 701], [99, 609], [8, 701], [14, 696], [15, 696], [41, 671], [69, 644], [90, 624], [14, 701], [15, 701], [21, 696], [41, 677], [33, 686], [78, 642], [1, 720], [2, 720], [3, 720], [89, 635], [5, 720], [6, 720]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[1, 726], [2, 726], [1, 728], [2, 728], [3, 728], [6, 726], [5, 728], [6, 728], [15, 720], [1, 735], [2, 735], [3, 735], [155, 584], [5, 735], [6, 735], [14, 728], [8, 735], [1, 743], [2, 743], [3, 743], [21, 726], [1, 747], [2, 747], [3, 747], [8, 743]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[5, 747], [6, 747], [119, 635], [8, 747], [1, 755], [2, 755], [3, 755], [33, 726], [5, 755], [6, 755], [1, 761], [1, 762], [2, 762], [3, 762], [5, 761], [5, 762], [6, 762], [1, 768], [2, 768], [3, 768], [554, 218], [5, 768], [1, 773], [2, 773], [3, 773]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[15, 762], [5, 773], [6, 773], [33, 747], [8, 773], [14, 768], [1, 782], [2, 782], [3, 782], [1, 785], [2, 785], [3, 785], [21, 768], [5, 785], [6, 785], [168, 624], [1, 792], [2, 792], [3, 792], [14, 782], [5, 792], [6, 792], [1, 798], [2, 798], [3, 798]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[1, 801], [2, 801], [3, 801], [20, 785], [5, 801], [6, 801], [131, 677], [8, 801], [75, 735], [50, 761], [14, 798], [1, 812], [2, 812], [3, 812], [15, 801], [5, 812], [6, 812], [1, 818], [1, 819], [2, 819], [3, 819], [5, 818], [5, 819], [6, 819], [1, 825]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[2, 825], [1, 827], [2, 827], [3, 827], [6, 825], [5, 827], [6, 827], [15, 819], [8, 827], [54, 782], [1, 836], [2, 836], [3, 836], [1, 839], [2, 839], [3, 839], [75, 768], [5, 839], [6, 839], [21, 825], [1, 846], [2, 846], [3, 846], [14, 836], [5, 846]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[6, 846], [14, 839], [8, 846], [54, 801], [1, 855], [2, 855], [1, 857], [2, 857], [3, 857], [1, 860], [2, 860], [3, 860], [138, 726], [1, 864], [2, 864], [3, 864], [8, 860], [5, 864], [6, 864], [14, 857], [8, 864], [54, 819], [14, 860], [15, 860], [1, 875]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 875], [3, 875], [1, 878], [2, 878], [3, 878], [90, 792], [5, 878], [6, 878], [21, 864], [8, 878], [41, 846], [33, 855], [14, 875], [15, 875]]
theorem len35 : w35.length = 14 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 890` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 890) : ∃ x, good n x = true := by
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
  by_cases c15 : n < 402
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 427
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 452
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 477
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 502
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 527
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 552
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 577
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 602
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 627
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 652
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 677
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 702
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 727
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 752
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 777
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 802
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 827
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 852
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 877
  · exact chunk ok34 len34 (by omega) (by omega)
  exact chunk ok35 len35 (by omega) (by omega)

end OMA.Aoeis_a230252Tab

open OMA.Aoeis_a230252Tab in
theorem OMA.solution : OMA.R_oeis_a230252_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
