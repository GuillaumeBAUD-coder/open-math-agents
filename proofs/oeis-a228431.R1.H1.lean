import OMAReductions.R_oeis_a228431_R1
import Mathlib

-- Step oeis-a228431.R1.H1: hypothesis H1 of reduction oeis-a228431.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 764.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1151413.

/-! Step oeis-a228431.R1.H1. -/

namespace OMA.Aoeis_a228431Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1075` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1075 2

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
  have hnd := noDiv_sound p 1075 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (n = x + y) && isPrimeB (x * (x + 1) / 2 + y * (2 * y - 1)))))
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
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
        (x * (x + 1) / 2 + y * (2 * y - 1)).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 764`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [3, 1], [1, 4], [2, 4], [1, 6], [7, 1], [5, 4], [3, 7], [1, 10], [2, 10], [1, 12], [10, 4], [1, 14], [3, 13], [16, 1], [2, 16], [1, 18], [7, 13], [4, 17], [3, 19], [1, 22], [10, 14], [1, 24], [19, 7]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[1, 26], [3, 25], [13, 16], [2, 28], [9, 22], [22, 10], [1, 32], [7, 27], [4, 31], [2, 34], [1, 36], [31, 7], [1, 38], [3, 37], [4, 37], [2, 40], [13, 30], [7, 37], [4, 41], [6, 40], [16, 31], [11, 37], [1, 48], [19, 31], [1, 50]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 49], [13, 40], [22, 32], [1, 54], [10, 46], [1, 56], [7, 51], [28, 31], [2, 58], [4, 57], [22, 40], [16, 47], [6, 58], [16, 49], [10, 56], [1, 66], [19, 49], [1, 68], [18, 52], [13, 58], [2, 70], [4, 69], [43, 31], [13, 62], [18, 58]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[13, 64], [7, 71], [13, 66], [7, 73], [1, 80], [3, 79], [1, 82], [11, 73], [1, 84], [31, 55], [5, 82], [18, 70], [1, 88], [7, 83], [1, 90], [10, 82], [8, 85], [3, 91], [1, 94], [2, 94], [16, 81], [58, 40], [13, 86], [6, 94], [4, 97]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[22, 80], [1, 102], [7, 97], [1, 104], [3, 103], [1, 106], [2, 106], [13, 96], [7, 103], [1, 110], [18, 94], [1, 112], [2, 112], [12, 103], [19, 97], [8, 109], [18, 100], [25, 94], [2, 118], [4, 117], [10, 112], [8, 115], [3, 121], [16, 109], [2, 124]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 126], [22, 106], [5, 124], [6, 124], [4, 127], [7, 125], [13, 120], [7, 127], [17, 118], [3, 133], [1, 136], [19, 119], [1, 138], [22, 118], [5, 136], [6, 136], [49, 94], [2, 142], [4, 141], [19, 127], [1, 146], [3, 145], [1, 148], [11, 139], [1, 150]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[10, 142], [4, 149], [31, 123], [1, 154], [7, 149], [12, 145], [19, 139], [5, 154], [18, 142], [25, 136], [2, 160], [16, 147], [7, 157], [1, 164], [3, 163], [16, 151], [2, 166], [21, 148], [7, 163], [4, 167], [15, 157], [1, 172], [7, 167], [4, 171], [10, 166]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 172], [19, 159], [40, 139], [14, 166], [1, 180], [10, 172], [1, 182], [6, 178], [16, 169], [2, 184], [12, 175], [19, 169], [1, 188], [18, 172], [4, 187], [11, 181], [4, 189], [7, 187], [1, 194], [3, 193], [13, 184], [46, 152], [12, 187], [22, 178], [1, 200]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[7, 195], [13, 190], [2, 202], [4, 201], [7, 199], [5, 202], [7, 201], [16, 193], [2, 208], [1, 210], [7, 205], [16, 197], [6, 208], [16, 199], [2, 214], [1, 216], [19, 199], [5, 214], [3, 217], [1, 220], [11, 211], [1, 222], [10, 214], [1, 224], [3, 223]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[40, 187], [2, 226], [13, 216], [19, 211], [4, 227], [3, 229], [13, 220], [7, 227], [1, 234], [7, 229], [25, 212], [3, 235], [1, 238], [14, 226], [4, 237], [58, 184], [4, 239], [7, 237], [4, 241], [2, 244], [16, 231], [46, 202], [1, 248], [7, 243], [25, 226]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[2, 250], [1, 252], [58, 196], [28, 227], [6, 250], [1, 256], [19, 239], [13, 246], [43, 217], [20, 241], [30, 232], [64, 199], [2, 262], [12, 253], [31, 235], [16, 251], [3, 265], [52, 217], [19, 251], [1, 270], [22, 250], [8, 265], [3, 271], [13, 262], [7, 269]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[1, 276], [7, 271], [1, 278], [6, 274], [1, 280], [11, 271], [4, 279], [22, 262], [13, 272], [18, 268], [1, 286], [2, 286], [1, 288], [19, 271], [1, 290], [6, 286], [37, 256], [2, 292], [9, 286], [7, 289], [25, 272], [18, 280], [16, 283], [14, 286], [37, 264]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[7, 295], [1, 302], [3, 301], [13, 292], [7, 299], [28, 279], [34, 274], [1, 308], [3, 307], [16, 295], [43, 269], [1, 312], [43, 271], [1, 314], [6, 310], [28, 289], [2, 316], [16, 303], [31, 289], [1, 320], [3, 319], [4, 319], [7, 317], [24, 301], [43, 283]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[1, 326], [19, 309], [13, 316], [14, 316], [13, 318], [31, 301], [8, 325], [3, 331], [1, 334], [10, 326], [1, 336], [7, 331], [5, 334], [6, 334], [1, 340], [2, 340], [9, 334], [55, 289], [1, 344], [3, 343], [1, 346], [14, 334], [1, 348], [58, 292], [16, 335]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 349], [4, 349], [22, 332], [1, 354], [19, 337], [16, 341], [3, 355], [1, 358], [2, 358], [9, 352], [58, 304], [16, 347], [30, 334], [13, 352], [2, 364], [16, 351], [58, 310], [5, 364], [19, 351], [16, 355], [2, 370], [24, 349], [7, 367], [16, 359], [3, 373]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[1, 376], [22, 356], [12, 367], [94, 286], [5, 376], [15, 367], [13, 370], [7, 377], [1, 384], [19, 367], [1, 386], [3, 385], [61, 328], [14, 376], [12, 379], [10, 382], [28, 365], [3, 391], [52, 343], [2, 394], [25, 372], [19, 379], [8, 391], [3, 397], [1, 400]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[7, 395], [1, 402], [58, 346], [32, 373], [22, 384], [1, 406], [2, 406], [16, 393], [22, 388], [5, 406], [7, 405], [13, 400], [10, 404], [1, 414], [10, 406], [5, 412], [27, 391], [61, 358], [22, 398], [1, 420], [31, 391], [16, 407], [6, 418], [1, 424], [7, 419]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[13, 414], [22, 406], [1, 428], [18, 412], [4, 427], [7, 425], [1, 432], [67, 367], [8, 427], [10, 426], [37, 400], [43, 395], [16, 423], [19, 421], [13, 428], [6, 436], [4, 439], [2, 442], [16, 429], [10, 436], [8, 439], [3, 445], [16, 433], [2, 448], [4, 447]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[46, 406], [4, 449], [18, 436], [1, 454], [11, 445], [13, 444], [19, 439], [25, 434], [6, 454], [4, 457], [10, 452], [1, 462], [10, 454], [17, 448], [6, 460], [1, 466], [14, 454], [13, 456], [7, 463], [5, 466], [3, 469], [1, 472], [7, 467], [1, 474], [22, 454]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[17, 460], [18, 460], [16, 463], [11, 469], [9, 472], [7, 475], [8, 475], [7, 477], [1, 484], [10, 476], [1, 486], [31, 457], [25, 464], [3, 487], [4, 487], [7, 485], [24, 469], [55, 439], [4, 491], [15, 481], [1, 496], [2, 496], [1, 498], [31, 469], [4, 497]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[3, 499], [16, 487], [11, 493], [4, 501], [10, 496], [16, 491], [18, 490], [1, 508], [19, 491], [1, 510], [7, 505], [1, 512], [18, 496], [64, 451], [2, 514], [1, 516], [22, 496], [8, 511], [19, 501], [16, 505], [2, 520], [12, 511], [46, 478], [1, 524], [6, 520]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[40, 487], [14, 514], [1, 528], [22, 508], [5, 526], [6, 526], [1, 532], [2, 532], [4, 531], [22, 514], [13, 524], [7, 531], [13, 526], [2, 538], [4, 537], [10, 532], [4, 539], [6, 538], [37, 508], [38, 508], [1, 546], [7, 541], [25, 524], [54, 496], [13, 538]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[70, 482], [1, 552], [7, 547], [1, 554], [3, 553], [1, 556], [2, 556], [16, 543], [22, 538], [5, 556], [18, 544], [16, 547], [11, 553], [9, 556], [22, 544], [17, 550], [7, 561], [25, 544], [11, 559], [9, 562], [10, 562], [1, 572], [3, 571], [1, 574], [7, 569]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[45, 532], [19, 559], [32, 547], [7, 573], [25, 556], [2, 580], [4, 579], [10, 574], [4, 581], [7, 579], [16, 571], [2, 586], [12, 577], [7, 583], [4, 587], [18, 574], [13, 580], [2, 592], [1, 594], [43, 553], [16, 581], [7, 591], [25, 574], [7, 593], [25, 576]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[10, 592], [13, 590], [15, 589], [37, 568], [19, 587], [1, 606], [79, 529], [1, 608], [22, 588], [1, 610], [23, 589], [4, 609], [31, 583], [4, 611], [10, 606], [28, 589], [2, 616], [12, 607], [19, 601], [8, 613], [7, 615], [1, 622], [22, 602], [9, 616], [31, 595]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[16, 611], [3, 625], [16, 613], [58, 572], [4, 627], [55, 577], [16, 617], [15, 619], [37, 598], [14, 622], [25, 612], [19, 619], [8, 631], [3, 637], [1, 640], [7, 635], [9, 634], [10, 634], [1, 644], [6, 640], [16, 631], [11, 637], [1, 648], [7, 643], [1, 650]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[6, 646], [16, 637], [35, 619], [4, 651], [43, 613], [5, 652], [31, 627], [16, 643], [19, 641], [4, 657], [22, 640], [4, 659], [7, 657], [16, 649], [10, 656], [13, 654], [7, 661], [5, 664], [18, 652], [25, 646], [2, 670], [9, 664], [7, 667], [16, 659], [22, 654]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[13, 664], [2, 676], [13, 666], [7, 673], [4, 677], [3, 679], [16, 667], [22, 662], [4, 681], [10, 676], [5, 682], [6, 682], [73, 616], [2, 688], [16, 675], [58, 634], [1, 692], [3, 691], [52, 643], [14, 682], [1, 696], [46, 652], [8, 691], [3, 697], [13, 688]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[10, 692], [4, 699], [43, 661], [1, 704], [15, 691], [1, 706], [2, 706], [1, 708], [19, 691], [13, 698], [3, 709], [64, 649], [22, 692], [1, 714], [19, 697], [25, 692], [6, 712], [13, 706], [7, 713], [4, 717], [22, 700], [37, 686], [7, 717], [13, 712], [19, 707]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[16, 711], [34, 694], [17, 712], [6, 724], [40, 691], [2, 730], [12, 721], [22, 712], [16, 719], [6, 730], [25, 712], [2, 736], [40, 699], [22, 718], [1, 740], [3, 739], [1, 742], [11, 733], [21, 724], [19, 727], [13, 734], [19, 729], [1, 748], [14, 736], [1, 750]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[10, 742], [1, 752], [7, 747], [16, 739], [10, 746], [13, 744], [46, 712], [53, 706], [6, 754], [28, 733], [26, 736], [4, 759], [7, 757]]
theorem len30 : w30.length = 13 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 764` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 764) : ∃ x, good n x = true := by
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
  exact chunk ok30 len30 (by omega) (by omega)

end OMA.Aoeis_a228431Tab

open OMA.Aoeis_a228431Tab in
theorem OMA.solution : OMA.R_oeis_a228431_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
