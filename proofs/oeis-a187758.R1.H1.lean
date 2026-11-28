import OMAReductions.R_oeis_a187758_R1
import Mathlib

-- Step oeis-a187758.R1.H1: hypothesis H1 of reduction oeis-a187758.R1
-- Credit: @prathameshnium. Finite check for 5 ≤ n ≤ 1004.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5927.

/-! Step oeis-a187758.R1.H1. -/

namespace OMA.Aoeis_a187758Tab

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
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (2 * x - 3) && (isPrimeB (2 * x + 3) && (isPrimeB (6 * y + 1) && isPrimeB (6 * y + 5)))))))
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
    (2 * x - 3).Prime ∧ (2 * x + 3).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 5, …, 1004`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[4, 1], [4, 2], [4, 3], [5, 3], [7, 2], [4, 6], [4, 7], [5, 7], [7, 6], [7, 7], [4, 11], [5, 11], [4, 13], [5, 13], [8, 11], [4, 16], [4, 17], [4, 18], [5, 18], [7, 17], [4, 21], [5, 21], [10, 17], [7, 21], [8, 21]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 5 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[13, 17], [4, 27], [5, 27], [17, 16], [7, 27], [8, 27], [4, 32], [5, 32], [17, 21], [7, 32], [8, 32], [4, 37], [4, 38], [5, 38], [7, 37], [7, 38], [8, 38], [10, 37], [10, 38], [17, 32], [4, 46], [5, 46], [20, 32], [7, 46], [8, 46]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 30 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[4, 51], [4, 52], [5, 52], [7, 51], [7, 52], [8, 52], [10, 51], [4, 58], [5, 58], [13, 51], [7, 58], [8, 58], [4, 63], [5, 63], [17, 52], [4, 66], [5, 66], [20, 52], [7, 66], [8, 66], [17, 58], [10, 66], [4, 73], [5, 73], [13, 66]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 55 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[4, 76], [4, 77], [5, 77], [7, 76], [7, 77], [4, 81], [5, 81], [4, 83], [5, 83], [8, 81], [7, 83], [8, 83], [55, 37], [10, 83], [13, 81], [22, 73], [13, 83], [20, 77], [17, 81], [22, 77], [17, 83], [20, 81], [25, 77], [20, 83], [28, 76]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 80 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[22, 83], [4, 102], [5, 102], [25, 83], [7, 102], [8, 102], [4, 107], [5, 107], [32, 81], [7, 107], [8, 107], [4, 112], [5, 112], [35, 83], [7, 112], [8, 112], [38, 83], [10, 112], [50, 73], [17, 107], [13, 112], [43, 83], [4, 123], [5, 123], [17, 112]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 105 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[4, 126], [5, 126], [4, 128], [5, 128], [8, 126], [7, 128], [8, 128], [25, 112], [10, 128], [13, 126], [17, 123], [4, 137], [5, 137], [17, 126], [7, 137], [8, 137], [4, 142], [4, 143], [5, 143], [7, 142], [4, 146], [4, 147], [5, 147], [7, 146], [7, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 130 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[4, 151], [5, 151], [10, 147], [7, 151], [8, 151], [4, 156], [5, 156], [20, 142], [7, 156], [8, 156], [4, 161], [5, 161], [20, 147], [7, 161], [8, 161], [28, 142], [10, 161], [4, 168], [5, 168], [13, 161], [7, 168], [8, 168], [35, 142], [10, 168], [28, 151]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 155 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[38, 142], [13, 168], [35, 147], [22, 161], [28, 156], [4, 181], [4, 182], [5, 182], [7, 181], [7, 182], [8, 182], [10, 181], [10, 182], [25, 168], [13, 181], [13, 182], [28, 168], [50, 147], [17, 181], [17, 182], [32, 168], [20, 181], [20, 182], [22, 181], [22, 182]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 180 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[77, 128], [4, 202], [5, 202], [52, 156], [7, 202], [8, 202], [43, 168], [10, 202], [32, 181], [32, 182], [13, 202], [35, 181], [4, 213], [5, 213], [17, 202], [4, 216], [4, 217], [5, 217], [7, 216], [7, 217], [8, 217], [10, 216], [10, 217], [67, 161], [13, 216]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 205 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[13, 217], [50, 181], [50, 182], [17, 216], [17, 217], [22, 213], [20, 216], [20, 217], [22, 216], [22, 217], [38, 202], [4, 237], [4, 238], [5, 238], [7, 237], [4, 241], [5, 241], [10, 237], [7, 241], [8, 241], [13, 237], [4, 247], [4, 248], [5, 248], [7, 247]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 230 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[7, 248], [8, 248], [10, 247], [10, 248], [22, 237], [13, 247], [13, 248], [4, 258], [5, 258], [17, 247], [4, 261], [5, 261], [4, 263], [5, 263], [8, 261], [4, 266], [5, 266], [4, 268], [5, 268], [8, 266], [7, 268], [8, 268], [130, 147], [10, 268], [13, 266]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 255 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[17, 263], [4, 277], [5, 277], [17, 266], [7, 277], [8, 277], [4, 282], [5, 282], [20, 268], [7, 282], [8, 282], [25, 266], [10, 282], [25, 268], [17, 277], [13, 282], [28, 268], [20, 277], [32, 266], [17, 282], [32, 268], [4, 297], [5, 297], [35, 268], [7, 297]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 280 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[8, 297], [38, 268], [10, 297], [50, 258], [32, 277], [13, 297], [43, 268], [35, 277], [50, 263], [17, 297], [4, 311], [4, 312], [5, 312], [7, 311], [7, 312], [8, 312], [10, 311], [10, 312], [55, 268], [13, 311], [13, 312], [85, 241], [50, 277], [17, 311], [17, 312]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 305 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[53, 277], [20, 311], [20, 312], [22, 311], [22, 312], [38, 297], [4, 332], [4, 333], [5, 333], [7, 332], [7, 333], [8, 333], [10, 332], [10, 333], [32, 312], [13, 332], [13, 333], [35, 312], [80, 268], [17, 332], [17, 333], [4, 347], [5, 347], [20, 333], [7, 347]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 330 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[8, 347], [88, 268], [10, 347], [25, 333], [77, 282], [4, 356], [5, 356], [50, 312], [7, 356], [8, 356], [32, 333], [10, 356], [20, 347], [35, 333], [13, 356], [38, 332], [4, 367], [5, 367], [17, 356], [7, 367], [8, 367], [20, 356], [4, 373], [5, 373], [32, 347]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 355 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[7, 373], [8, 373], [4, 378], [5, 378], [17, 367], [7, 378], [4, 382], [5, 382], [10, 378], [7, 382], [8, 382], [13, 378], [10, 382], [20, 373], [38, 356], [4, 391], [5, 391], [50, 347], [7, 391], [8, 391], [4, 396], [5, 396], [4, 398], [5, 398], [8, 396]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 380 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[7, 398], [8, 398], [25, 382], [10, 398], [13, 396], [4, 406], [5, 406], [80, 332], [7, 406], [8, 406], [17, 398], [4, 412], [5, 412], [20, 398], [7, 412], [8, 412], [25, 396], [10, 412], [17, 406], [28, 396], [13, 412], [20, 406], [4, 423], [5, 423], [17, 412]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 405 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[7, 423], [8, 423], [20, 412], [10, 423], [22, 412], [53, 382], [13, 423], [25, 412], [32, 406], [43, 396], [4, 436], [5, 436], [130, 312], [7, 436], [8, 436], [22, 423], [10, 436], [4, 443], [5, 443], [13, 436], [7, 443], [4, 447], [4, 448], [5, 448], [7, 447]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 430 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[4, 451], [5, 451], [10, 447], [7, 451], [8, 451], [13, 447], [10, 451], [4, 458], [5, 458], [13, 451], [7, 458], [8, 458], [20, 447], [10, 458], [22, 447], [4, 466], [5, 466], [25, 447], [7, 466], [8, 466], [17, 458], [4, 472], [5, 472], [20, 458], [7, 472]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 455 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[4, 476], [5, 476], [10, 472], [7, 476], [8, 476], [13, 472], [10, 476], [140, 347], [22, 466], [13, 476], [32, 458], [25, 466], [20, 472], [17, 476], [22, 472], [52, 443], [4, 492], [5, 492], [22, 476], [7, 492], [8, 492], [25, 476], [10, 492], [52, 451], [28, 476]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 480 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[13, 492], [55, 451], [4, 503], [5, 503], [17, 492], [4, 506], [5, 506], [20, 492], [7, 506], [8, 506], [43, 472], [10, 506], [4, 513], [5, 513], [13, 506], [7, 513], [8, 513], [50, 472], [10, 513], [32, 492], [22, 503], [13, 513], [35, 492], [22, 506], [53, 476]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 505 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[17, 513], [4, 527], [5, 527], [20, 513], [7, 527], [4, 531], [5, 531], [10, 527], [7, 531], [8, 531], [4, 536], [5, 536], [50, 492], [7, 536], [8, 536], [32, 513], [4, 542], [5, 542], [17, 531], [7, 542], [8, 542], [20, 531], [10, 542], [17, 536], [88, 466]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 530 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[13, 542], [20, 536], [4, 553], [5, 553], [17, 542], [7, 553], [4, 557], [5, 557], [10, 553], [7, 557], [8, 557], [13, 553], [10, 557], [32, 536], [38, 531], [13, 557], [35, 536], [80, 492], [20, 553], [17, 557], [22, 553], [118, 458], [20, 557], [25, 553], [22, 557]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 555 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[4, 576], [4, 577], [5, 577], [7, 576], [7, 577], [8, 577], [10, 576], [10, 577], [35, 553], [13, 576], [13, 577], [38, 553], [4, 588], [5, 588], [17, 577], [7, 588], [8, 588], [20, 577], [10, 588], [22, 577], [43, 557], [13, 588], [25, 577], [50, 553], [28, 576]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 580 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[17, 588], [4, 602], [5, 602], [20, 588], [7, 602], [8, 602], [35, 576], [10, 602], [25, 588], [38, 576], [13, 602], [4, 612], [5, 612], [115, 503], [7, 612], [4, 616], [5, 616], [10, 612], [7, 616], [8, 616], [13, 612], [10, 616], [25, 602], [52, 576], [13, 616]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 605 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[28, 602], [43, 588], [20, 612], [17, 616], [22, 612], [188, 447], [4, 632], [5, 632], [22, 616], [7, 632], [8, 632], [25, 616], [10, 632], [55, 588], [28, 616], [4, 641], [5, 641], [35, 612], [7, 641], [8, 641], [4, 646], [5, 646], [20, 632], [7, 646], [8, 646]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 630 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[4, 651], [5, 651], [4, 653], [5, 653], [8, 651], [7, 653], [4, 657], [5, 657], [10, 653], [7, 657], [8, 657], [13, 653], [10, 657], [17, 651], [28, 641], [13, 657], [4, 667], [5, 667], [20, 653], [7, 667], [8, 667], [25, 651], [10, 667], [25, 653], [22, 657]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 655 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[13, 667], [28, 653], [25, 657], [32, 651], [17, 667], [28, 657], [35, 651], [20, 667], [35, 653], [22, 667], [88, 602], [38, 653], [4, 688], [5, 688], [43, 651], [7, 688], [4, 692], [5, 692], [10, 688], [7, 692], [8, 692], [13, 688], [10, 692], [50, 653], [53, 651]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 680 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[13, 692], [53, 653], [50, 657], [20, 688], [17, 692], [22, 688], [175, 536], [20, 692], [25, 688], [22, 692], [113, 602], [28, 688], [25, 692], [67, 651], [52, 667], [28, 692], [80, 641], [55, 667], [35, 688], [32, 692], [113, 612], [38, 688], [35, 692], [77, 651], [88, 641]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 705 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[38, 692], [43, 688], [130, 602], [80, 653], [67, 667], [43, 692], [85, 651], [80, 657], [50, 688], [88, 651], [52, 688], [53, 688], [50, 692], [55, 688], [52, 692], [4, 741], [5, 741], [55, 692], [7, 741], [8, 741], [97, 653], [10, 741], [85, 667], [137, 616], [13, 741]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 730 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[67, 688], [4, 752], [4, 753], [5, 753], [7, 752], [7, 753], [8, 753], [10, 752], [10, 753], [97, 667], [13, 752], [13, 753], [155, 612], [80, 688], [17, 752], [17, 753], [118, 653], [20, 752], [20, 753], [22, 752], [22, 753], [35, 741], [4, 773], [5, 773], [38, 741]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 755 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[7, 773], [8, 773], [115, 667], [10, 773], [32, 752], [32, 753], [13, 773], [35, 752], [35, 753], [97, 692], [17, 773], [38, 753], [4, 788], [5, 788], [53, 741], [7, 788], [8, 788], [130, 667], [10, 788], [167, 632], [133, 667], [4, 797], [4, 798], [5, 798], [7, 797]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 780 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[7, 798], [4, 802], [5, 802], [10, 798], [7, 802], [8, 802], [13, 798], [10, 802], [25, 788], [17, 797], [13, 802], [28, 788], [20, 797], [20, 798], [17, 802], [22, 798], [80, 741], [20, 802], [25, 798], [22, 802], [28, 797], [4, 822], [5, 822], [55, 773], [7, 822]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 805 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[8, 822], [43, 788], [4, 828], [5, 828], [32, 802], [7, 828], [8, 828], [4, 833], [5, 833], [17, 822], [7, 833], [8, 833], [20, 822], [10, 833], [22, 822], [17, 828], [13, 833], [25, 822], [20, 828], [52, 797], [4, 846], [5, 846], [50, 802], [7, 846], [8, 846]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 830 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[22, 833], [10, 846], [35, 822], [25, 833], [13, 846], [32, 828], [28, 833], [230, 632], [17, 846], [67, 797], [4, 861], [5, 861], [115, 752], [7, 861], [8, 861], [97, 773], [10, 861], [50, 822], [85, 788], [13, 861], [4, 871], [4, 872], [5, 872], [7, 871], [7, 872]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 855 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[8, 872], [10, 871], [10, 872], [22, 861], [13, 871], [13, 872], [25, 861], [85, 802], [17, 871], [17, 872], [88, 802], [20, 871], [20, 872], [22, 871], [22, 872], [4, 891], [5, 891], [25, 872], [7, 891], [8, 891], [28, 872], [10, 891], [80, 822], [32, 871], [13, 891]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 880 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[77, 828], [4, 902], [5, 902], [17, 891], [7, 902], [4, 906], [5, 906], [10, 902], [7, 906], [8, 906], [13, 902], [10, 906], [4, 913], [5, 913], [13, 906], [7, 913], [4, 917], [5, 917], [10, 913], [7, 917], [4, 921], [5, 921], [10, 917], [7, 921], [8, 921]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 905 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[13, 917], [10, 921], [4, 928], [5, 928], [13, 921], [7, 928], [8, 928], [20, 917], [10, 928], [22, 917], [38, 902], [13, 928], [25, 917], [22, 921], [38, 906], [4, 941], [4, 942], [5, 942], [7, 941], [7, 942], [8, 942], [10, 941], [4, 948], [5, 948], [13, 941]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 930 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[7, 948], [8, 948], [55, 902], [10, 948], [17, 942], [4, 956], [5, 956], [20, 942], [7, 956], [8, 956], [17, 948], [10, 956], [4, 963], [5, 963], [13, 956], [7, 963], [8, 963], [55, 917], [10, 963], [32, 942], [178, 797], [13, 963], [4, 973], [5, 973], [38, 941]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 955 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[4, 976], [5, 976], [80, 902], [7, 976], [8, 976], [22, 963], [10, 976], [85, 902], [25, 963], [13, 976], [17, 973], [4, 987], [5, 987], [17, 976], [7, 987], [8, 987], [20, 976], [10, 987], [22, 976], [43, 956], [13, 987], [25, 976], [85, 917], [55, 948], [17, 987]]
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

end OMA.Aoeis_a187758Tab

open OMA.Aoeis_a187758Tab in
theorem OMA.solution : OMA.R_oeis_a187758_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
