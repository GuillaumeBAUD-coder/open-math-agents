import OMAReductions.R_oeis_a199800_R1
import Mathlib

-- Step oeis-a199800.R1.H1: hypothesis H1 of reduction oeis-a199800.R1
-- Credit: @prathameshnium. Finite check for 12 ≤ n ≤ 1011.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5881.

/-! Step oeis-a199800.R1.H1. -/

namespace OMA.Aoeis_a199800Tab

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
  | [p, q] => (decide (0 < q) && (decide (n = p + q) && (isPrimeB (p) && (isPrimeB (6 * q - 1) && isPrimeB (6 * q + 1)))))
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
    ∃ p q : ℕ, 0 < q ∧ n = p + q ∧ p.Prime ∧ (6 * q - 1).Prime ∧ (6 * q + 1).Prime := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, q, a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 12, …, 1011`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 10], [3, 10], [2, 12], [3, 12], [11, 5], [5, 12], [11, 7], [2, 17], [2, 18], [3, 18], [5, 17], [5, 18], [7, 17], [2, 23], [3, 23], [2, 25], [3, 25], [11, 18], [5, 25], [13, 18], [2, 30], [3, 30], [2, 32], [2, 33], [3, 33]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 12 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5, 32], [5, 33], [7, 32], [2, 38], [3, 38], [2, 40], [3, 40], [11, 33], [5, 40], [13, 33], [2, 45], [3, 45], [2, 47], [3, 47], [11, 40], [5, 47], [13, 40], [2, 52], [3, 52], [11, 45], [5, 52], [11, 47], [7, 52], [2, 58], [3, 58]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 37 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[17, 45], [5, 58], [17, 47], [7, 58], [19, 47], [29, 38], [23, 45], [11, 58], [23, 47], [13, 58], [2, 70], [3, 70], [2, 72], [3, 72], [29, 47], [5, 72], [31, 47], [2, 77], [3, 77], [11, 70], [5, 77], [11, 72], [7, 77], [13, 72], [41, 45]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 62 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[17, 70], [11, 77], [2, 87], [3, 87], [19, 72], [5, 87], [23, 70], [7, 87], [23, 72], [19, 77], [2, 95], [3, 95], [29, 70], [5, 95], [29, 72], [2, 100], [3, 100], [17, 87], [2, 103], [3, 103], [7, 100], [5, 103], [2, 107], [3, 107], [11, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 87 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 110], [3, 110], [7, 107], [5, 110], [13, 103], [7, 110], [11, 107], [19, 100], [13, 107], [11, 110], [19, 103], [13, 110], [17, 107], [53, 72], [19, 107], [17, 110], [41, 87], [19, 110], [23, 107], [31, 100], [29, 103], [23, 110], [31, 103], [83, 52], [29, 107]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 112 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 135], [3, 135], [2, 137], [2, 138], [3, 138], [5, 137], [5, 138], [7, 137], [2, 143], [3, 143], [37, 110], [5, 143], [2, 147], [3, 147], [13, 138], [5, 147], [43, 110], [7, 147], [17, 138], [13, 143], [19, 138], [11, 147], [59, 100], [13, 147], [23, 138]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 137 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[19, 143], [53, 110], [17, 147], [107, 58], [19, 147], [29, 138], [31, 137], [31, 138], [23, 147], [61, 110], [2, 170], [3, 170], [2, 172], [3, 172], [29, 147], [2, 175], [3, 175], [2, 177], [3, 177], [11, 170], [5, 177], [11, 172], [2, 182], [3, 182], [11, 175]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 162 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 182], [11, 177], [7, 182], [13, 177], [19, 172], [17, 175], [11, 182], [2, 192], [3, 192], [19, 177], [5, 192], [23, 175], [7, 192], [23, 177], [19, 182], [59, 143], [11, 192], [29, 175], [13, 192], [29, 177], [2, 205], [3, 205], [17, 192], [5, 205], [19, 192]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 187 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[7, 205], [31, 182], [37, 177], [2, 213], [3, 213], [2, 215], [3, 215], [2, 217], [3, 217], [29, 192], [2, 220], [3, 220], [7, 217], [5, 220], [11, 215], [7, 220], [11, 217], [37, 192], [13, 217], [11, 220], [17, 215], [13, 220], [17, 217], [43, 192], [19, 217]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 212 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[17, 220], [23, 215], [19, 220], [2, 238], [3, 238], [29, 213], [5, 238], [2, 242], [3, 242], [29, 217], [5, 242], [31, 217], [2, 247], [2, 248], [3, 248], [5, 247], [5, 248], [7, 247], [7, 248], [41, 215], [19, 238], [11, 247], [11, 248], [13, 247], [13, 248]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 237 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[47, 215], [43, 220], [17, 247], [17, 248], [19, 247], [19, 248], [53, 215], [31, 238], [2, 268], [3, 268], [2, 270], [3, 270], [59, 215], [5, 270], [29, 247], [7, 270], [31, 247], [11, 268], [2, 278], [3, 278], [67, 215], [5, 278], [37, 247], [2, 283], [3, 283]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 262 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[17, 270], [5, 283], [2, 287], [3, 287], [13, 278], [5, 287], [23, 270], [7, 287], [17, 278], [13, 283], [19, 278], [11, 287], [29, 270], [2, 298], [3, 298], [19, 283], [5, 298], [17, 287], [7, 298], [19, 287], [29, 278], [61, 247], [11, 298], [23, 287], [13, 298]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 287 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[29, 283], [43, 270], [2, 312], [2, 313], [3, 313], [5, 312], [5, 313], [7, 312], [7, 313], [23, 298], [107, 215], [11, 312], [2, 322], [3, 322], [13, 313], [2, 325], [3, 325], [7, 322], [5, 325], [19, 312], [7, 325], [11, 322], [47, 287], [2, 333], [3, 333]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 312 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[59, 278], [5, 333], [17, 322], [2, 338], [3, 338], [17, 325], [5, 338], [11, 333], [7, 338], [13, 333], [79, 268], [23, 325], [2, 347], [2, 348], [3, 348], [5, 347], [5, 348], [2, 352], [3, 352], [23, 333], [2, 355], [3, 355], [2, 357], [3, 357], [13, 348]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 337 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5, 357], [11, 352], [7, 357], [13, 352], [11, 355], [19, 348], [11, 357], [17, 352], [13, 357], [19, 352], [17, 355], [61, 312], [17, 357], [2, 373], [3, 373], [29, 348], [5, 373], [31, 348], [2, 378], [3, 378], [167, 215], [5, 378], [11, 373], [7, 378], [13, 373]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 362 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 385], [3, 385], [11, 378], [5, 385], [13, 378], [2, 390], [3, 390], [37, 357], [5, 390], [11, 385], [7, 390], [13, 385], [2, 397], [3, 397], [11, 390], [5, 397], [13, 390], [7, 397], [53, 352], [59, 347], [17, 390], [11, 397], [19, 390], [13, 397], [59, 352]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 387 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[79, 333], [23, 390], [17, 397], [37, 378], [19, 397], [79, 338], [61, 357], [29, 390], [23, 397], [31, 390], [37, 385], [71, 352], [67, 357], [47, 378], [29, 397], [2, 425], [3, 425], [107, 322], [5, 425], [41, 390], [7, 425], [43, 390], [2, 432], [3, 432], [11, 425]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 412 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[5, 432], [13, 425], [7, 432], [43, 397], [89, 352], [17, 425], [11, 432], [19, 425], [2, 443], [3, 443], [109, 338], [5, 443], [17, 432], [2, 448], [3, 448], [67, 385], [5, 448], [2, 452], [3, 452], [13, 443], [2, 455], [3, 455], [7, 452], [5, 455], [13, 448]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 437 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[7, 455], [11, 452], [67, 397], [13, 452], [11, 455], [2, 465], [3, 465], [2, 467], [3, 467], [19, 452], [5, 467], [41, 432], [7, 467], [23, 452], [11, 465], [29, 448], [11, 467], [31, 448], [13, 467], [29, 452], [17, 465], [31, 452], [17, 467], [37, 448], [19, 467]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 462 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[97, 390], [23, 465], [37, 452], [23, 467], [43, 448], [37, 455], [41, 452], [29, 465], [43, 452], [29, 467], [2, 495], [3, 495], [47, 452], [5, 495], [53, 448], [2, 500], [3, 500], [37, 467], [5, 500], [11, 495], [7, 500], [13, 495], [61, 448], [43, 467], [11, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 487 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[17, 495], [13, 500], [19, 495], [67, 448], [61, 455], [17, 500], [23, 495], [19, 500], [53, 467], [73, 448], [2, 520], [3, 520], [29, 495], [5, 520], [31, 495], [7, 520], [61, 467], [29, 500], [2, 528], [3, 528], [37, 495], [5, 528], [67, 467], [7, 528], [41, 495]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 512 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[17, 520], [43, 495], [11, 528], [73, 467], [13, 528], [47, 495], [23, 520], [2, 542], [2, 543], [3, 543], [5, 542], [5, 543], [7, 542], [7, 543], [23, 528], [2, 550], [3, 550], [11, 543], [5, 550], [13, 543], [2, 555], [3, 555], [17, 542], [5, 555], [11, 550]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 537 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 560], [3, 560], [2, 562], [3, 562], [11, 555], [2, 565], [3, 565], [7, 562], [5, 565], [11, 560], [7, 565], [11, 562], [19, 555], [13, 562], [11, 565], [17, 560], [13, 565], [2, 577], [2, 578], [3, 578], [5, 577], [5, 578], [7, 577], [7, 578], [31, 555]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 562 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[37, 550], [11, 577], [11, 578], [2, 588], [3, 588], [2, 590], [3, 590], [17, 577], [2, 593], [3, 593], [7, 590], [5, 593], [2, 597], [3, 597], [11, 590], [5, 597], [13, 590], [7, 597], [17, 588], [13, 593], [17, 590], [11, 597], [19, 590], [13, 597], [23, 588]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 587 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[19, 593], [23, 590], [2, 612], [3, 612], [19, 597], [5, 612], [41, 577], [7, 612], [23, 597], [31, 590], [29, 593], [11, 612], [31, 593], [13, 612], [29, 597], [37, 590], [31, 597], [17, 612], [2, 628], [3, 628], [67, 565], [5, 628], [37, 597], [7, 628], [43, 593]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 612 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[47, 590], [41, 597], [2, 637], [3, 637], [13, 628], [5, 637], [31, 612], [2, 642], [3, 642], [53, 593], [5, 642], [11, 637], [7, 642], [13, 637], [23, 628], [59, 593], [11, 642], [17, 637], [2, 653], [3, 653], [2, 655], [3, 655], [17, 642], [5, 655], [19, 642]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 637 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[7, 655], [73, 590], [11, 653], [23, 642], [11, 655], [79, 588], [13, 655], [2, 667], [3, 667], [29, 642], [2, 670], [3, 670], [7, 667], [5, 670], [23, 653], [2, 675], [3, 675], [37, 642], [5, 675], [11, 670], [7, 675], [13, 670], [2, 682], [3, 682], [11, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 662 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[5, 682], [13, 675], [7, 682], [2, 688], [3, 688], [17, 675], [5, 688], [19, 675], [2, 693], [3, 693], [107, 590], [5, 693], [11, 688], [7, 693], [13, 688], [47, 655], [61, 642], [11, 693], [2, 703], [3, 703], [2, 705], [3, 705], [2, 707], [3, 707], [23, 688]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 687 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 710], [3, 710], [2, 712], [3, 712], [11, 705], [5, 712], [11, 707], [7, 712], [13, 707], [11, 710], [17, 705], [11, 712], [17, 707], [2, 723], [3, 723], [17, 710], [5, 723], [17, 712], [7, 723], [19, 712], [29, 703], [23, 710], [11, 723], [23, 712], [13, 723]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 712 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[67, 670], [31, 707], [2, 737], [3, 737], [29, 712], [5, 737], [31, 712], [7, 737], [103, 642], [23, 723], [37, 710], [11, 737], [2, 747], [3, 747], [41, 710], [5, 747], [41, 712], [7, 747], [2, 753], [3, 753], [47, 710], [5, 753], [47, 712], [2, 758], [3, 758]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 737 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[59, 703], [5, 758], [11, 753], [7, 758], [13, 753], [79, 688], [31, 737], [11, 758], [17, 753], [13, 758], [19, 753], [61, 712], [37, 737], [2, 773], [3, 773], [2, 775], [3, 775], [67, 712], [5, 775], [23, 758], [7, 775], [71, 712], [11, 773], [73, 712], [11, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 762 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[29, 758], [13, 775], [2, 787], [3, 787], [79, 712], [5, 787], [83, 710], [7, 787], [37, 758], [23, 773], [109, 688], [11, 787], [41, 758], [2, 798], [3, 798], [2, 800], [3, 800], [17, 787], [5, 800], [19, 787], [7, 800], [61, 747], [11, 798], [23, 787], [11, 800]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 787 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[37, 775], [13, 800], [41, 773], [17, 798], [29, 787], [17, 800], [31, 787], [19, 800], [47, 773], [23, 798], [47, 775], [23, 800], [2, 822], [3, 822], [53, 773], [5, 822], [41, 787], [7, 822], [2, 828], [3, 828], [59, 773], [5, 828], [47, 787], [7, 828], [61, 775]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 812 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[2, 835], [3, 835], [2, 837], [3, 837], [13, 828], [5, 837], [43, 800], [7, 837], [17, 828], [11, 835], [19, 828], [11, 837], [137, 712], [13, 837], [23, 828], [2, 850], [3, 850], [17, 837], [5, 850], [19, 837], [7, 850], [23, 835], [31, 828], [23, 837], [11, 850]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 837 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[89, 773], [13, 850], [29, 835], [37, 828], [29, 837], [17, 850], [31, 837], [19, 850], [83, 787], [43, 828], [37, 835], [23, 850], [2, 872], [3, 872], [41, 835], [5, 872], [41, 837], [7, 872], [43, 837], [31, 850], [2, 880], [3, 880], [47, 837], [5, 880], [113, 773]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 862 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[7, 880], [53, 835], [17, 872], [53, 837], [11, 880], [139, 753], [13, 880], [59, 835], [23, 872], [59, 837], [17, 880], [61, 837], [19, 880], [113, 787], [29, 872], [67, 835], [23, 880], [67, 837], [2, 903], [3, 903], [79, 828], [5, 903], [2, 907], [3, 907], [31, 880]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 887 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[5, 907], [41, 872], [7, 907], [2, 913], [3, 913], [37, 880], [5, 913], [2, 917], [3, 917], [41, 880], [2, 920], [3, 920], [7, 917], [5, 920], [13, 913], [7, 920], [11, 917], [79, 850], [13, 917], [11, 920], [19, 913], [13, 920], [17, 917], [107, 828], [19, 917]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 912 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[17, 920], [31, 907], [19, 920], [23, 917], [61, 880], [2, 940], [3, 940], [2, 942], [2, 943], [3, 943], [5, 942], [5, 943], [7, 942], [7, 943], [11, 940], [179, 773], [11, 942], [11, 943], [13, 942], [13, 943], [17, 940], [41, 917], [2, 957], [3, 957], [19, 942]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 937 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[5, 957], [23, 940], [7, 957], [23, 942], [23, 943], [47, 920], [11, 957], [29, 940], [13, 957], [29, 942], [29, 943], [31, 942], [17, 957], [103, 872], [19, 957], [2, 975], [3, 975], [37, 942], [2, 978], [3, 978], [2, 980], [3, 980], [41, 943], [5, 980], [11, 975]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 962 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[7, 980], [13, 975], [11, 978], [47, 943], [11, 980], [17, 975], [13, 980], [19, 975], [17, 978], [53, 943], [17, 980], [23, 975], [19, 980], [43, 957], [23, 978], [59, 943], [23, 980], [29, 975], [293, 712], [31, 975], [29, 978], [101, 907], [29, 980], [53, 957], [31, 980]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 987 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `12 ≤ n ≤ 1011` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 12 ≤ n) (h2 : n ≤ 1011) : ∃ x, good n x = true := by
  by_cases c0 : n < 37
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 62
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 87
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 112
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 137
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 162
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 187
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 212
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 237
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 262
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 287
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 312
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 337
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 362
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 387
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 412
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 437
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 462
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 487
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 512
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 537
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 562
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 587
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 612
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 637
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 662
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 687
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 712
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 737
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 762
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 787
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 812
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 837
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 862
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 887
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 912
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 937
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 962
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 987
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a199800Tab

open OMA.Aoeis_a199800Tab in
theorem OMA.solution : OMA.R_oeis_a199800_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
