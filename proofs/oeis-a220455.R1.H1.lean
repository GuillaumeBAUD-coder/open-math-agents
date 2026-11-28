import OMAReductions.R_oeis_a220455_R1
import Mathlib

-- Step oeis-a220455.R1.H1: hypothesis H1 of reduction oeis-a220455.R1
-- Credit: @prathameshnium. Finite check for 8 ≤ n ≤ 1007.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 347401.

/-! Step oeis-a220455.R1.H1. -/

namespace OMA.Aoeis_a220455Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `591` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 591 2

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
  have hnd := noDiv_sound p 591 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (3 * x - 2) && (isPrimeB (3 * x + 2) && isPrimeB (2 * x * y + 1))))))
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
    (3 * x - 2).Prime ∧ (3 * x + 2).Prime ∧ (2 * x * y + 1).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 8, …, 1007`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 5], [3, 6], [3, 7], [5, 6], [5, 7], [3, 10], [3, 11], [3, 12], [3, 13], [15, 2], [5, 13], [3, 16], [3, 17], [3, 18], [7, 15], [5, 18], [3, 21], [13, 12], [3, 23], [7, 20], [3, 25], [3, 26], [3, 27], [7, 24], [5, 27]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 8 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 30], [7, 27], [3, 32], [3, 33], [7, 30], [3, 35], [7, 32], [3, 37], [3, 38], [7, 35], [3, 40], [23, 21], [5, 40], [7, 39], [5, 42], [3, 45], [3, 46], [3, 47], [5, 46], [7, 45], [23, 30], [3, 51], [3, 52], [15, 41], [5, 52]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 33 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 55], [3, 56], [7, 53], [3, 58], [5, 57], [13, 50], [3, 61], [3, 62], [3, 63], [27, 40], [5, 63], [3, 66], [7, 63], [3, 68], [7, 65], [3, 70], [5, 69], [3, 72], [3, 73], [15, 62], [23, 55], [3, 76], [3, 77], [5, 76], [7, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 58 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[33, 50], [3, 81], [7, 78], [3, 83], [5, 82], [13, 75], [15, 74], [3, 87], [13, 78], [15, 77], [3, 90], [3, 91], [23, 72], [5, 91], [37, 60], [3, 95], [3, 96], [7, 93], [35, 66], [5, 97], [3, 100], [3, 101], [3, 102], [3, 103], [5, 102]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 83 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 105], [7, 102], [3, 107], [5, 106], [7, 105], [3, 110], [5, 109], [3, 112], [33, 83], [15, 102], [3, 115], [15, 104], [5, 115], [3, 118], [5, 117], [5, 118], [3, 121], [3, 122], [3, 123], [15, 112], [3, 125], [3, 126], [7, 123], [3, 128], [15, 117]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 108 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[13, 120], [3, 131], [5, 130], [15, 121], [5, 132], [3, 135], [33, 106], [3, 137], [3, 138], [27, 115], [5, 138], [13, 131], [3, 142], [3, 143], [27, 120], [13, 135], [3, 146], [3, 147], [7, 144], [5, 147], [5, 148], [3, 151], [15, 140], [3, 153], [15, 142]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 133 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[5, 153], [3, 156], [7, 153], [27, 134], [5, 157], [15, 148], [3, 161], [5, 160], [27, 139], [5, 162], [3, 165], [3, 166], [15, 155], [3, 168], [7, 165], [3, 170], [7, 167], [3, 172], [3, 173], [5, 172], [3, 175], [5, 174], [3, 177], [3, 178], [15, 167]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 158 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[13, 170], [3, 181], [3, 182], [5, 181], [7, 180], [5, 183], [3, 186], [3, 187], [3, 188], [5, 187], [103, 90], [23, 171], [3, 192], [7, 189], [27, 170], [3, 195], [7, 192], [5, 195], [13, 188], [7, 195], [3, 200], [13, 191], [3, 202], [5, 201], [7, 200]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 183 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[3, 205], [3, 206], [7, 203], [3, 208], [35, 177], [5, 208], [13, 201], [35, 180], [3, 213], [127, 90], [3, 215], [3, 216], [3, 217], [5, 216], [7, 215], [3, 220], [3, 221], [15, 210], [7, 219], [5, 222], [13, 215], [7, 222], [5, 225], [7, 224], [27, 205]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 208 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 230], [15, 219], [37, 198], [3, 233], [7, 230], [13, 225], [5, 234], [3, 237], [3, 238], [5, 237], [5, 238], [3, 241], [3, 242], [3, 243], [7, 240], [3, 245], [5, 244], [3, 247], [3, 248], [77, 175], [43, 210], [23, 231], [33, 222], [55, 201], [5, 252]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 233 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 255], [7, 252], [3, 257], [3, 258], [7, 255], [65, 198], [3, 261], [7, 258], [3, 263], [5, 262], [15, 253], [3, 266], [33, 237], [3, 268], [5, 267], [3, 270], [3, 271], [23, 252], [5, 271], [37, 240], [5, 273], [3, 276], [3, 277], [3, 278], [7, 275]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 258 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[43, 240], [5, 279], [3, 282], [3, 283], [15, 272], [13, 275], [13, 276], [3, 287], [5, 286], [15, 277], [3, 290], [3, 291], [3, 292], [3, 293], [15, 282], [13, 285], [3, 296], [3, 297], [3, 298], [5, 297], [3, 300], [7, 297], [5, 300], [5, 301], [7, 300]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 283 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 305], [5, 304], [7, 303], [5, 306], [7, 305], [3, 310], [3, 311], [3, 312], [3, 313], [5, 312], [15, 303], [103, 216], [15, 305], [7, 314], [127, 195], [5, 318], [5, 319], [3, 322], [65, 261], [5, 322], [3, 325], [15, 314], [5, 325], [13, 318], [5, 327]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 308 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[33, 300], [3, 331], [3, 332], [3, 333], [7, 330], [3, 335], [3, 336], [7, 333], [3, 338], [5, 337], [13, 330], [5, 339], [3, 342], [15, 331], [35, 312], [23, 325], [7, 342], [3, 347], [3, 348], [7, 345], [15, 338], [5, 349], [3, 352], [5, 351], [35, 322]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 333 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 355], [3, 356], [3, 357], [7, 354], [5, 357], [3, 360], [7, 357], [15, 350], [3, 363], [37, 330], [5, 363], [13, 356], [3, 367], [225, 146], [5, 367], [3, 370], [5, 369], [5, 370], [3, 373], [15, 362], [3, 375], [7, 372], [35, 345], [3, 378], [75, 307]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 358 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 380], [3, 381], [3, 382], [15, 371], [5, 382], [3, 385], [33, 356], [5, 385], [13, 378], [15, 377], [3, 390], [3, 391], [33, 362], [5, 391], [37, 360], [3, 395], [3, 396], [3, 397], [3, 398], [7, 395], [13, 390], [27, 377], [5, 400], [15, 391], [5, 402]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 383 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[13, 395], [3, 406], [5, 405], [7, 404], [37, 375], [15, 398], [3, 411], [3, 412], [5, 411], [7, 410], [13, 405], [23, 396], [3, 417], [27, 394], [15, 407], [3, 420], [7, 417], [5, 420], [3, 423], [7, 420], [3, 425], [3, 426], [7, 423], [5, 426], [5, 427]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 408 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[15, 418], [77, 357], [3, 432], [7, 429], [77, 360], [33, 405], [3, 436], [23, 417], [15, 426], [7, 435], [15, 428], [3, 441], [7, 438], [3, 443], [5, 442], [3, 445], [3, 446], [3, 447], [3, 448], [35, 417], [5, 448], [3, 451], [3, 452], [3, 453], [7, 450]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 433 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 455], [7, 452], [7, 453], [3, 458], [15, 447], [13, 450], [3, 461], [23, 442], [7, 459], [5, 462], [3, 465], [3, 466], [3, 467], [13, 458], [15, 457], [35, 438], [5, 469], [3, 472], [15, 461], [5, 472], [3, 475], [3, 476], [5, 475], [7, 474], [15, 467]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 458 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[153, 330], [3, 481], [5, 480], [75, 411], [27, 460], [5, 483], [3, 486], [7, 483], [5, 486], [5, 487], [15, 478], [27, 467], [3, 492], [15, 481], [15, 482], [3, 495], [13, 486], [5, 495], [7, 494], [55, 447], [3, 500], [7, 497], [33, 472], [3, 503], [5, 502]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 483 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[55, 453], [3, 506], [5, 505], [3, 508], [35, 477], [3, 510], [3, 511], [5, 510], [3, 513], [15, 502], [15, 503], [15, 504], [13, 507], [3, 518], [5, 517], [3, 520], [15, 509], [7, 518], [13, 513], [15, 512], [5, 523], [7, 522], [3, 527], [3, 528], [7, 525]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 508 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 530], [3, 531], [7, 528], [23, 513], [15, 522], [33, 505], [3, 536], [5, 535], [3, 538], [35, 507], [5, 538], [13, 531], [3, 542], [3, 543], [7, 540], [3, 545], [5, 544], [7, 543], [27, 524], [5, 547], [3, 550], [3, 551], [3, 552], [3, 553], [5, 552]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 533 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[3, 555], [13, 546], [3, 557], [7, 554], [15, 547], [3, 560], [5, 559], [3, 562], [23, 543], [7, 560], [3, 565], [5, 564], [5, 565], [33, 538], [35, 537], [13, 560], [43, 531], [3, 572], [5, 571], [117, 460], [35, 543], [3, 576], [3, 577], [3, 578], [15, 567]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 558 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[13, 570], [5, 579], [5, 580], [3, 583], [5, 582], [3, 585], [3, 586], [5, 585], [3, 588], [7, 585], [3, 590], [3, 591], [7, 588], [3, 593], [27, 570], [3, 595], [23, 576], [3, 597], [7, 594], [27, 575], [5, 598], [3, 601], [3, 602], [5, 601], [15, 592]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 583 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[3, 605], [3, 606], [3, 607], [15, 596], [15, 597], [13, 600], [5, 609], [3, 612], [7, 609], [5, 612], [3, 615], [3, 616], [5, 615], [3, 618], [15, 607], [35, 588], [3, 621], [3, 622], [3, 623], [5, 622], [13, 615], [75, 554], [15, 615], [3, 628], [5, 627]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 608 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[15, 618], [7, 627], [3, 632], [5, 631], [7, 630], [15, 623], [7, 632], [3, 637], [5, 636], [27, 615], [13, 630], [3, 641], [3, 642], [27, 619], [5, 642], [23, 625], [3, 646], [5, 645], [3, 648], [27, 625], [5, 648], [3, 651], [13, 642], [3, 653], [5, 652]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 633 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[3, 655], [27, 632], [3, 657], [7, 654], [5, 657], [5, 658], [3, 661], [15, 650], [7, 659], [7, 660], [23, 645], [23, 646], [3, 667], [5, 666], [7, 665], [3, 670], [3, 671], [5, 670], [13, 663], [15, 662], [3, 675], [3, 676], [23, 657], [5, 676], [15, 667]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 658 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[5, 678], [5, 679], [3, 682], [3, 683], [7, 680], [3, 685], [5, 684], [27, 663], [3, 688], [5, 687], [13, 680], [7, 687], [3, 692], [3, 693], [7, 690], [23, 675], [3, 696], [13, 687], [5, 696], [5, 697], [3, 700], [5, 699], [5, 700], [3, 703], [27, 680]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 683 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[3, 705], [7, 702], [3, 707], [7, 704], [7, 705], [3, 710], [127, 587], [3, 712], [15, 701], [5, 712], [55, 663], [3, 716], [5, 715], [43, 678], [15, 707], [13, 710], [3, 721], [27, 698], [3, 723], [37, 690], [15, 713], [3, 726], [3, 727], [15, 716], [7, 725]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 708 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[43, 690], [23, 711], [7, 728], [27, 709], [5, 732], [5, 733], [27, 712], [3, 737], [23, 718], [27, 715], [3, 740], [3, 741], [7, 738], [5, 741], [15, 732], [15, 733], [105, 644], [3, 747], [27, 724], [15, 737], [5, 748], [3, 751], [3, 752], [3, 753], [7, 750]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 733 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[15, 743], [5, 754], [13, 747], [3, 758], [35, 727], [3, 760], [3, 761], [7, 758], [7, 759], [5, 762], [3, 765], [3, 766], [3, 767], [13, 758], [7, 765], [3, 770], [5, 769], [7, 768], [3, 773], [7, 770], [3, 775], [3, 776], [3, 777], [7, 774], [15, 767]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 758 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[13, 770], [13, 771], [23, 762], [15, 771], [37, 750], [33, 755], [5, 784], [3, 787], [3, 788], [15, 777], [55, 738], [15, 779], [5, 790], [3, 793], [75, 722], [13, 785], [93, 706], [3, 797], [3, 798], [7, 795], [3, 800], [7, 797], [3, 802], [5, 801], [15, 792]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 783 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[3, 805], [33, 776], [7, 803], [7, 804], [15, 797], [3, 810], [7, 807], [5, 810], [5, 811], [15, 802], [15, 803], [7, 812], [3, 817], [3, 818], [5, 817], [13, 810], [5, 819], [3, 822], [7, 819], [5, 822], [3, 825], [3, 826], [23, 807], [3, 828], [7, 825]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 808 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[225, 608], [3, 831], [3, 832], [3, 833], [7, 830], [3, 835], [23, 816], [3, 837], [7, 834], [77, 765], [15, 828], [7, 837], [23, 822], [3, 843], [27, 820], [5, 843], [3, 846], [33, 817], [5, 846], [7, 845], [3, 850], [3, 851], [3, 852], [3, 853], [5, 852]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 833 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[65, 793], [13, 846], [27, 833], [55, 806], [7, 855], [5, 858], [3, 861], [13, 852], [3, 863], [7, 860], [43, 825], [3, 866], [13, 857], [3, 868], [27, 845], [5, 868], [3, 871], [3, 872], [23, 853], [117, 760], [5, 873], [5, 874], [13, 867], [5, 876], [7, 875]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 858 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[3, 880], [23, 861], [37, 848], [13, 873], [5, 882], [5, 883], [13, 876], [3, 887], [5, 886], [7, 885], [65, 828], [3, 891], [7, 888], [15, 881], [65, 832], [13, 885], [5, 894], [5, 895], [7, 894], [5, 897], [15, 888], [3, 901], [3, 902], [3, 903], [7, 900]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 883 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3, 905], [3, 906], [3, 907], [3, 908], [7, 905], [43, 870], [5, 909], [7, 908], [3, 913], [15, 902], [13, 905], [13, 906], [3, 917], [5, 916], [15, 907], [3, 920], [3, 921], [7, 918], [23, 903], [5, 922], [75, 853], [3, 926], [3, 927], [3, 928], [27, 905]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 908 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[3, 930], [7, 927], [23, 912], [5, 931], [37, 900], [15, 923], [5, 934], [3, 937], [33, 908], [5, 937], [3, 940], [3, 941], [3, 942], [3, 943], [5, 942], [5, 943], [13, 936], [3, 947], [3, 948], [15, 937], [3, 950], [5, 949], [15, 940], [5, 951], [5, 952]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 933 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[13, 945], [3, 956], [3, 957], [3, 958], [15, 947], [33, 930], [7, 957], [5, 960], [3, 963], [7, 960], [3, 965], [7, 962], [27, 943], [5, 966], [15, 957], [3, 970], [3, 971], [7, 968], [3, 973], [5, 972], [3, 975], [3, 976], [153, 827], [3, 978], [37, 945]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 958 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[3, 980], [5, 979], [7, 978], [5, 981], [7, 980], [15, 973], [15, 974], [3, 987], [27, 964], [5, 987], [23, 970], [55, 939], [3, 992], [33, 963], [225, 772], [5, 993], [5, 994], [7, 993], [15, 986], [7, 995], [13, 990], [3, 1001], [13, 992], [13, 993], [15, 992]]
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

end OMA.Aoeis_a220455Tab

open OMA.Aoeis_a220455Tab in
theorem OMA.solution : OMA.R_oeis_a220455_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
