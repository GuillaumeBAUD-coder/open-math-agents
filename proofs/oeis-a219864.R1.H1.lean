import OMAReductions.R_oeis_a219864_R1
import Mathlib

-- Step oeis-a219864.R1.H1: hypothesis H1 of reduction oeis-a219864.R1
-- Credit: @prathameshnium. Finite check for 8 ≤ n ≤ 1007.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 306871.

/-! Step oeis-a219864.R1.H1. -/

namespace OMA.Aoeis_a219864Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `555` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 555 2

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
  have hnd := noDiv_sound p 555 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (p + q = n) && (isPrimeB (p) && isPrimeB (2 * p * q + 1)))
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
    ∃ p q : ℕ, p + q = n ∧ Nat.Prime p ∧ Nat.Prime (2 * p * q + 1) := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨p, q, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 8, …, 1007`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 5], [2, 7], [3, 7], [2, 9], [2, 10], [3, 10], [3, 11], [2, 13], [3, 13], [2, 15], [5, 13], [3, 16], [2, 18], [3, 18], [7, 15], [5, 18], [2, 22], [13, 12], [2, 24], [2, 25], [3, 25], [2, 27], [2, 28], [7, 24], [5, 27]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 8 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 30], [7, 27], [3, 32], [2, 34], [7, 30], [3, 35], [2, 37], [3, 37], [2, 39], [7, 35], [3, 40], [11, 33], [2, 43], [7, 39], [2, 45], [3, 45], [3, 46], [2, 48], [2, 49], [7, 45], [23, 30], [3, 51], [3, 52], [11, 45], [5, 52]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 33 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 55], [2, 57], [2, 58], [3, 58], [2, 60], [13, 50], [3, 61], [3, 62], [2, 64], [37, 30], [5, 63], [2, 67], [7, 63], [2, 69], [2, 70], [3, 70], [5, 69], [2, 73], [3, 73], [11, 66], [19, 59], [3, 76], [2, 78], [2, 79], [7, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 58 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[53, 30], [3, 81], [7, 78], [2, 84], [5, 82], [13, 75], [2, 87], [2, 88], [13, 78], [11, 81], [3, 90], [3, 91], [2, 93], [5, 91], [31, 66], [3, 95], [2, 97], [7, 93], [2, 99], [2, 100], [3, 100], [2, 102], [3, 102], [3, 103], [2, 105]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 83 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 105], [7, 102], [2, 108], [5, 106], [7, 105], [3, 110], [2, 112], [3, 112], [2, 114], [2, 115], [3, 115], [11, 108], [5, 115], [3, 118], [5, 117], [5, 118], [3, 121], [3, 122], [3, 123], [31, 96], [3, 125], [2, 127], [7, 123], [3, 128], [2, 130]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 108 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[13, 120], [3, 131], [5, 130], [19, 117], [2, 135], [3, 135], [19, 120], [3, 137], [2, 139], [31, 111], [5, 138], [2, 142], [3, 142], [2, 144], [17, 130], [13, 135], [3, 146], [2, 148], [7, 144], [2, 150], [5, 148], [3, 151], [2, 153], [2, 154], [127, 30]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 133 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[5, 153], [3, 156], [7, 153], [11, 150], [2, 160], [43, 120], [3, 161], [2, 163], [37, 129], [2, 165], [3, 165], [3, 166], [2, 168], [2, 169], [7, 165], [3, 170], [7, 167], [3, 172], [3, 173], [2, 175], [3, 175], [2, 177], [3, 177], [3, 178], [101, 81]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 158 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[13, 170], [3, 181], [2, 183], [5, 181], [7, 180], [5, 183], [3, 186], [3, 187], [2, 189], [2, 190], [79, 114], [2, 192], [2, 193], [7, 189], [11, 186], [3, 195], [7, 192], [5, 195], [2, 199], [7, 195], [3, 200], [2, 202], [3, 202], [5, 201], [2, 205]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 183 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[3, 205], [2, 207], [7, 203], [3, 208], [11, 201], [5, 208], [13, 201], [2, 213], [2, 214], [67, 150], [3, 215], [3, 216], [3, 217], [2, 219], [2, 220], [3, 220], [3, 221], [19, 206], [7, 219], [5, 222], [13, 215], [7, 222], [5, 225], [7, 224], [37, 195]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 208 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 230], [2, 232], [19, 216], [2, 234], [2, 235], [13, 225], [5, 234], [2, 238], [3, 238], [5, 237], [5, 238], [3, 241], [3, 242], [2, 244], [7, 240], [3, 245], [5, 244], [3, 247], [2, 249], [11, 241], [19, 234], [2, 252], [2, 253], [19, 237], [2, 255]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 233 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 255], [7, 252], [2, 258], [3, 258], [7, 255], [83, 180], [2, 262], [7, 258], [3, 263], [2, 265], [19, 249], [2, 267], [19, 251], [3, 268], [5, 267], [3, 270], [3, 271], [2, 273], [2, 274], [37, 240], [5, 273], [2, 277], [3, 277], [2, 279], [7, 275]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 258 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[43, 240], [2, 282], [3, 282], [3, 283], [11, 276], [13, 275], [13, 276], [2, 288], [5, 286], [31, 261], [3, 290], [3, 291], [3, 292], [3, 293], [2, 295], [13, 285], [3, 296], [2, 298], [3, 298], [2, 300], [3, 300], [7, 297], [2, 303], [2, 304], [7, 300]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 283 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 305], [2, 307], [7, 303], [2, 309], [7, 305], [3, 310], [2, 312], [3, 312], [3, 313], [5, 312], [29, 289], [61, 258], [17, 303], [2, 319], [31, 291], [5, 318], [2, 322], [3, 322], [2, 324], [2, 325], [3, 325], [11, 318], [5, 325], [13, 318], [2, 330]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 308 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[19, 314], [3, 331], [3, 332], [3, 333], [7, 330], [3, 335], [3, 336], [7, 333], [3, 338], [2, 340], [13, 330], [5, 339], [2, 343], [31, 315], [2, 345], [19, 329], [7, 342], [3, 347], [3, 348], [7, 345], [29, 324], [2, 352], [3, 352], [5, 351], [41, 316]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 333 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 355], [2, 357], [2, 358], [7, 354], [5, 357], [3, 360], [7, 357], [2, 363], [3, 363], [37, 330], [5, 363], [11, 358], [3, 367], [17, 354], [2, 370], [3, 370], [2, 372], [2, 373], [3, 373], [11, 366], [3, 375], [7, 372], [17, 363], [3, 378], [61, 321]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 358 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 380], [3, 381], [3, 382], [17, 369], [5, 382], [3, 385], [2, 387], [2, 388], [13, 378], [197, 195], [3, 390], [3, 391], [17, 378], [5, 391], [37, 360], [3, 395], [3, 396], [3, 397], [2, 399], [2, 400], [13, 390], [2, 402], [2, 403], [31, 375], [2, 405]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 383 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[13, 395], [3, 406], [5, 405], [2, 409], [31, 381], [29, 384], [3, 411], [3, 412], [2, 414], [7, 410], [13, 405], [2, 417], [3, 417], [19, 402], [11, 411], [3, 420], [7, 417], [2, 423], [2, 424], [7, 420], [3, 425], [2, 427], [7, 423], [5, 426], [2, 430]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 408 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[19, 414], [53, 381], [2, 433], [7, 429], [2, 435], [19, 419], [3, 436], [2, 438], [11, 430], [7, 435], [53, 390], [3, 441], [7, 438], [2, 444], [5, 442], [3, 445], [2, 447], [3, 447], [3, 448], [2, 450], [5, 448], [3, 451], [3, 452], [3, 453], [7, 450]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 433 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 455], [7, 452], [7, 453], [3, 458], [11, 451], [13, 450], [3, 461], [17, 448], [7, 459], [2, 465], [3, 465], [3, 466], [2, 468], [2, 469], [37, 435], [149, 324], [2, 472], [3, 472], [17, 459], [2, 475], [3, 475], [3, 476], [2, 478], [7, 474], [71, 411]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 458 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[59, 424], [3, 481], [2, 483], [19, 467], [37, 450], [5, 483], [2, 487], [7, 483], [5, 486], [5, 487], [19, 474], [11, 483], [2, 493], [19, 477], [71, 426], [3, 495], [13, 486], [2, 498], [2, 499], [97, 405], [3, 500], [7, 497], [31, 474], [2, 504], [5, 502]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 483 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[19, 489], [2, 507], [5, 505], [3, 508], [17, 495], [3, 510], [3, 511], [2, 513], [3, 513], [31, 486], [59, 459], [2, 517], [13, 507], [3, 518], [2, 520], [3, 520], [2, 522], [7, 518], [13, 513], [11, 516], [5, 523], [7, 522], [2, 528], [3, 528], [7, 525]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 508 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 530], [2, 532], [7, 528], [2, 534], [2, 535], [43, 495], [3, 536], [2, 538], [3, 538], [2, 540], [5, 538], [13, 531], [3, 542], [3, 543], [7, 540], [3, 545], [5, 544], [7, 543], [59, 492], [5, 547], [3, 550], [3, 551], [2, 553], [3, 553], [2, 555]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 533 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[3, 555], [13, 546], [3, 557], [2, 559], [37, 525], [3, 560], [5, 559], [3, 562], [11, 555], [7, 560], [3, 565], [2, 567], [2, 568], [67, 504], [2, 570], [13, 560], [43, 531], [2, 573], [2, 574], [331, 246], [83, 495], [2, 577], [3, 577], [3, 578], [17, 565]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 558 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[13, 570], [5, 579], [2, 583], [3, 583], [2, 585], [3, 585], [3, 586], [5, 585], [2, 589], [7, 585], [3, 590], [3, 591], [7, 588], [2, 594], [2, 595], [3, 595], [2, 597], [2, 598], [7, 594], [11, 591], [5, 598], [3, 601], [3, 602], [2, 604], [37, 570]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 583 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[3, 605], [3, 606], [3, 607], [2, 609], [2, 610], [13, 600], [5, 609], [3, 612], [7, 609], [5, 612], [3, 615], [3, 616], [2, 618], [2, 619], [31, 591], [59, 564], [3, 621], [3, 622], [3, 623], [5, 622], [13, 615], [11, 618], [11, 619], [3, 628], [2, 630]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 608 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[19, 614], [7, 627], [3, 632], [5, 631], [7, 630], [29, 609], [2, 637], [3, 637], [2, 639], [11, 631], [13, 630], [3, 641], [3, 642], [19, 627], [5, 642], [23, 625], [3, 646], [2, 648], [3, 648], [61, 591], [5, 648], [2, 652], [13, 642], [2, 654], [2, 655]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 633 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[3, 655], [29, 630], [2, 658], [7, 654], [5, 657], [5, 658], [3, 661], [11, 654], [2, 664], [7, 660], [23, 645], [23, 646], [3, 667], [2, 669], [7, 665], [3, 670], [2, 672], [2, 673], [13, 663], [11, 666], [3, 675], [3, 676], [2, 678], [5, 676], [331, 351]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 658 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[5, 678], [2, 682], [3, 682], [3, 683], [2, 685], [3, 685], [2, 687], [2, 688], [3, 688], [5, 687], [13, 680], [7, 687], [3, 692], [2, 694], [7, 690], [23, 675], [2, 697], [13, 687], [2, 699], [2, 700], [3, 700], [5, 699], [5, 700], [3, 703], [11, 696]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 683 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[3, 705], [7, 702], [2, 708], [2, 709], [7, 705], [3, 710], [11, 703], [3, 712], [2, 714], [2, 715], [103, 615], [3, 716], [5, 715], [43, 678], [11, 711], [13, 710], [3, 721], [53, 672], [2, 724], [37, 690], [29, 699], [2, 727], [3, 727], [2, 729], [7, 725]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 708 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[43, 690], [11, 723], [7, 728], [31, 705], [5, 732], [5, 733], [19, 720], [2, 738], [2, 739], [97, 645], [3, 740], [2, 742], [7, 738], [5, 741], [11, 736], [43, 705], [17, 732], [3, 747], [19, 732], [2, 750], [5, 748], [3, 751], [3, 752], [3, 753], [7, 750]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 733 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[23, 735], [5, 754], [13, 747], [2, 759], [2, 760], [3, 760], [2, 762], [7, 758], [7, 759], [2, 765], [3, 765], [3, 766], [3, 767], [13, 758], [7, 765], [3, 770], [2, 772], [7, 768], [3, 773], [7, 770], [3, 775], [2, 777], [3, 777], [7, 774], [2, 780]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 758 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[13, 770], [13, 771], [11, 774], [2, 784], [37, 750], [173, 615], [5, 784], [3, 787], [3, 788], [11, 781], [109, 684], [2, 792], [5, 790], [3, 793], [2, 795], [13, 785], [19, 780], [3, 797], [3, 798], [7, 795], [3, 800], [2, 802], [3, 802], [2, 804], [2, 805]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 783 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[3, 805], [2, 807], [7, 803], [7, 804], [11, 801], [3, 810], [7, 807], [2, 813], [2, 814], [31, 786], [23, 795], [7, 812], [3, 817], [3, 818], [5, 817], [13, 810], [5, 819], [3, 822], [7, 819], [2, 825], [3, 825], [3, 826], [2, 828], [3, 828], [7, 825]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 808 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[29, 804], [2, 832], [3, 832], [3, 833], [7, 830], [3, 835], [11, 828], [3, 837], [7, 834], [2, 840], [79, 764], [7, 837], [2, 843], [3, 843], [31, 816], [5, 843], [2, 847], [43, 807], [5, 846], [7, 845], [3, 850], [3, 851], [2, 853], [3, 853], [5, 852]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 833 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[19, 839], [13, 846], [2, 858], [11, 850], [7, 855], [5, 858], [2, 862], [13, 852], [2, 864], [2, 865], [43, 825], [2, 867], [11, 859], [3, 868], [47, 825], [5, 868], [3, 871], [3, 872], [11, 865], [31, 846], [5, 873], [5, 874], [13, 867], [2, 879], [7, 875]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 858 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[3, 880], [2, 882], [2, 883], [13, 873], [2, 885], [5, 883], [13, 876], [3, 887], [2, 889], [7, 885], [53, 840], [3, 891], [7, 888], [11, 885], [2, 895], [13, 885], [5, 894], [2, 898], [7, 894], [5, 897], [43, 860], [3, 901], [2, 903], [2, 904], [7, 900]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 883 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3, 905], [3, 906], [3, 907], [2, 909], [7, 905], [43, 870], [5, 909], [7, 908], [3, 913], [137, 780], [13, 905], [13, 906], [2, 918], [2, 919], [31, 891], [3, 920], [3, 921], [7, 918], [2, 924], [2, 925], [19, 909], [2, 927], [3, 927], [3, 928], [41, 891]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 908 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[3, 930], [7, 927], [2, 933], [5, 931], [37, 900], [53, 885], [5, 934], [3, 937], [101, 840], [2, 940], [3, 940], [2, 942], [3, 942], [3, 943], [5, 942], [5, 943], [13, 936], [2, 948], [2, 949], [151, 801], [3, 950], [5, 949], [19, 936], [5, 951], [2, 955]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 933 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[13, 945], [3, 956], [2, 958], [3, 958], [47, 915], [53, 910], [7, 957], [2, 963], [3, 963], [7, 960], [3, 965], [7, 962], [61, 909], [2, 969], [2, 970], [3, 970], [2, 972], [7, 968], [3, 973], [5, 972], [3, 975], [3, 976], [11, 969], [2, 979], [31, 951]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 958 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[3, 980], [2, 982], [7, 978], [5, 981], [7, 980], [193, 795], [11, 978], [3, 987], [67, 924], [5, 987], [19, 974], [31, 963], [3, 992], [17, 979], [61, 936], [5, 993], [2, 997], [7, 993], [17, 984], [2, 1000], [13, 990], [3, 1001], [2, 1003], [13, 993], [2, 1005]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 983 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `8 ≤ n ≤ 1007` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 1007) : ∃ x, good n x = true := by
  by_cases c0 : n < 33
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 58
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 83
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 108
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 133
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 158
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 183
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 208
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 233
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 258
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 283
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 308
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 333
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 358
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 383
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 408
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 433
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 458
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 483
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 508
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 533
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 558
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 583
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 608
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 633
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 658
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 683
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 708
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 733
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 758
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 783
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 808
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 833
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 858
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 883
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 908
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 933
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 958
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 983
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a219864Tab

open OMA.Aoeis_a219864Tab in
theorem OMA.solution : OMA.R_oeis_a219864_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
