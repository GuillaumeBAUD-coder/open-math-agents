import OMAReductions.R_oeis_a220431_R1
import Mathlib

-- Step oeis-a220431.R1.H1: hypothesis H1 of reduction oeis-a220431.R1
-- Credit: @prathameshnium. Finite check for 4 ≤ n ≤ 1003.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 169049.

/-! Step oeis-a220431.R1.H1. -/

namespace OMA.Aoeis_a220431Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `413` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 413 2

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
  have hnd := noDiv_sound p 413 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (3 * x - 1) && (isPrimeB (3 * x + 1) && isPrimeB (x * y - 1))))))
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
    (3 * x - 1).Prime ∧ (3 * x + 1).Prime ∧ (x * y - 1).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 4, …, 1003`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2], [2, 3], [2, 4], [4, 3], [2, 6], [2, 7], [4, 6], [2, 9], [2, 10], [6, 7], [2, 12], [4, 11], [4, 12], [2, 15], [2, 16], [4, 15], [6, 14], [2, 19], [4, 18], [2, 21], [2, 22], [4, 21], [2, 24], [14, 13], [6, 22]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 4 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[2, 27], [4, 26], [4, 27], [2, 30], [2, 31], [6, 28], [6, 29], [2, 34], [4, 33], [2, 36], [2, 37], [24, 16], [20, 21], [2, 40], [36, 7], [2, 42], [4, 41], [4, 42], [2, 45], [6, 42], [4, 45], [6, 44], [2, 49], [4, 48], [2, 51]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 29 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 52], [6, 49], [2, 54], [2, 55], [6, 52], [2, 57], [4, 56], [4, 57], [20, 42], [20, 43], [4, 60], [6, 59], [2, 64], [4, 63], [2, 66], [14, 55], [4, 66], [2, 69], [2, 70], [6, 67], [14, 60], [4, 71], [6, 70], [2, 75], [2, 76]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 54 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[24, 55], [6, 74], [2, 79], [4, 78], [6, 77], [2, 82], [34, 51], [2, 84], [4, 83], [6, 82], [2, 87], [6, 84], [4, 87], [2, 90], [2, 91], [4, 90], [20, 75], [4, 92], [34, 63], [2, 96], [2, 97], [4, 96], [2, 99], [2, 100], [10, 93]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 79 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[6, 98], [6, 99], [6, 100], [14, 93], [2, 106], [4, 105], [24, 86], [10, 101], [4, 108], [6, 107], [2, 112], [4, 111], [2, 114], [2, 115], [76, 42], [2, 117], [4, 116], [4, 117], [2, 120], [2, 121], [4, 120], [14, 111], [4, 122], [4, 123], [2, 126]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 104 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[4, 125], [4, 126], [2, 129], [20, 112], [6, 127], [2, 132], [4, 131], [10, 126], [2, 135], [2, 136], [6, 133], [20, 120], [2, 139], [10, 132], [2, 141], [2, 142], [4, 141], [6, 140], [4, 143], [46, 102], [2, 147], [6, 144], [4, 147], [14, 138], [6, 147]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 129 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[4, 150], [14, 141], [2, 154], [24, 133], [2, 156], [2, 157], [10, 150], [2, 159], [4, 158], [6, 157], [6, 158], [4, 161], [4, 162], [14, 153], [2, 166], [4, 165], [6, 164], [2, 169], [10, 162], [36, 137], [14, 160], [4, 171], [2, 174], [2, 175], [6, 172]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 154 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 177], [10, 170], [6, 175], [2, 180], [6, 177], [4, 180], [14, 171], [2, 184], [24, 163], [6, 182], [2, 187], [4, 186], [6, 185], [2, 190], [36, 157], [2, 192], [20, 175], [24, 172], [2, 195], [6, 192], [10, 189], [6, 194], [2, 199], [24, 178], [2, 201]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 179 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[6, 198], [6, 199], [14, 192], [2, 205], [10, 198], [6, 203], [4, 206], [4, 207], [2, 210], [2, 211], [4, 210], [24, 191], [6, 210], [10, 207], [2, 216], [2, 217], [4, 216], [6, 215], [2, 220], [6, 217], [2, 222], [4, 221], [4, 222], [2, 225], [10, 218]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 204 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[24, 205], [14, 216], [2, 229], [4, 228], [2, 231], [2, 232], [6, 229], [2, 234], [10, 227], [46, 192], [36, 203], [14, 226], [4, 237], [2, 240], [36, 207], [6, 238], [6, 239], [2, 244], [4, 243], [2, 246], [10, 239], [4, 246], [80, 171], [2, 250], [6, 247]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 229 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[2, 252], [6, 249], [6, 250], [2, 255], [6, 252], [4, 255], [6, 254], [14, 247], [4, 258], [2, 261], [2, 262], [6, 259], [6, 260], [4, 263], [6, 262], [24, 245], [4, 266], [10, 261], [20, 252], [2, 271], [6, 268], [6, 269], [2, 274], [4, 273], [50, 228]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 254 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[6, 273], [4, 276], [2, 279], [10, 272], [10, 273], [2, 282], [4, 281], [24, 262], [2, 285], [2, 286], [6, 283], [14, 276], [2, 289], [4, 288], [6, 287], [14, 280], [4, 291], [2, 294], [4, 293], [10, 288], [2, 297], [14, 286], [4, 297], [2, 300], [2, 301]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 279 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[6, 298], [14, 291], [2, 304], [10, 297], [6, 302], [2, 307], [4, 306], [2, 309], [2, 310], [46, 267], [6, 308], [10, 305], [34, 282], [14, 303], [2, 316], [4, 315], [14, 306], [6, 315], [10, 312], [2, 321], [2, 322], [4, 321], [2, 324], [4, 323], [6, 322]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 304 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[2, 327], [4, 326], [4, 327], [2, 330], [2, 331], [4, 330], [6, 329], [4, 332], [34, 303], [20, 318], [2, 337], [6, 334], [2, 339], [10, 332], [10, 333], [2, 342], [24, 321], [4, 342], [140, 207], [2, 346], [10, 339], [6, 344], [6, 345], [60, 292], [2, 351]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 329 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[4, 350], [10, 345], [6, 350], [2, 355], [6, 352], [20, 339], [4, 356], [4, 357], [2, 360], [6, 357], [4, 360], [6, 359], [2, 364], [4, 363], [20, 348], [2, 367], [34, 336], [20, 351], [2, 370], [66, 307], [2, 372], [4, 371], [4, 372], [14, 363], [2, 376]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 354 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[4, 375], [6, 374], [2, 379], [4, 378], [2, 381], [6, 378], [4, 381], [60, 326], [2, 385], [10, 378], [2, 387], [4, 386], [6, 385], [24, 368], [20, 373], [4, 390], [6, 389], [2, 394], [4, 393], [6, 392], [4, 395], [4, 396], [2, 399], [10, 392], [6, 397]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 379 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[60, 344], [6, 399], [4, 402], [2, 405], [2, 406], [4, 405], [6, 404], [4, 407], [10, 402], [2, 411], [2, 412], [10, 405], [2, 414], [2, 415], [10, 408], [6, 413], [4, 416], [4, 417], [2, 420], [10, 413], [10, 414], [24, 401], [10, 416], [144, 283], [6, 422]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 404 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 427], [6, 424], [2, 429], [2, 430], [10, 423], [2, 432], [4, 431], [6, 430], [60, 377], [6, 432], [10, 429], [36, 404], [2, 439], [154, 288], [2, 441], [2, 442], [6, 439], [2, 444], [20, 427], [36, 412], [6, 443], [4, 446], [4, 447], [14, 438], [50, 403]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 429 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[6, 448], [6, 449], [2, 454], [4, 453], [2, 456], [14, 445], [4, 456], [6, 455], [2, 460], [6, 457], [14, 450], [6, 459], [4, 462], [2, 465], [36, 432], [6, 463], [20, 450], [2, 469], [4, 468], [2, 471], [4, 470], [10, 465], [2, 474], [14, 463], [10, 468]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 454 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 477], [6, 474], [4, 477], [14, 468], [6, 477], [34, 450], [66, 419], [2, 484], [4, 483], [2, 486], [6, 483], [6, 484], [2, 489], [4, 488], [36, 457], [2, 492], [14, 481], [6, 490], [14, 483], [2, 496], [4, 495], [6, 494], [2, 499], [10, 492], [36, 467]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 479 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[4, 500], [4, 501], [6, 500], [2, 505], [6, 502], [2, 507], [6, 504], [4, 507], [2, 510], [2, 511], [4, 510], [14, 501], [10, 506], [24, 493], [2, 516], [2, 517], [4, 516], [6, 515], [2, 520], [60, 463], [20, 504], [4, 521], [4, 522], [2, 525], [2, 526]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 504 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[4, 525], [24, 506], [10, 521], [4, 528], [2, 531], [2, 532], [24, 511], [14, 522], [2, 535], [6, 532], [14, 525], [4, 536], [6, 535], [200, 342], [6, 537], [24, 520], [14, 531], [2, 544], [64, 483], [2, 546], [2, 547], [10, 540], [2, 549], [10, 542], [46, 507]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 529 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 552], [4, 551], [4, 552], [2, 555], [10, 548], [66, 493], [6, 554], [2, 559], [10, 552], [20, 543], [2, 562], [4, 561], [6, 560], [2, 565], [6, 562], [20, 549], [24, 546], [4, 567], [24, 548], [20, 553], [6, 568], [6, 569], [4, 572], [10, 567], [2, 576]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 554 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 577], [36, 544], [6, 575], [4, 578], [6, 577], [2, 582], [10, 575], [24, 562], [50, 537], [2, 586], [4, 585], [20, 570], [4, 587], [4, 588], [2, 591], [6, 588], [6, 589], [2, 594], [4, 593], [10, 588], [2, 597], [4, 596], [64, 537], [14, 588], [2, 601]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 579 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[4, 600], [6, 599], [14, 592], [4, 603], [66, 542], [2, 607], [4, 606], [2, 609], [20, 592], [10, 603], [2, 612], [34, 581], [4, 612], [2, 615], [2, 616], [4, 615], [24, 596], [2, 619], [34, 588], [6, 617], [14, 610], [24, 601], [6, 620], [2, 625], [190, 438]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 604 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[14, 615], [4, 626], [34, 597], [2, 630], [6, 627], [6, 628], [14, 621], [6, 630], [4, 633], [50, 588], [4, 635], [4, 636], [2, 639], [2, 640], [6, 637], [2, 642], [6, 639], [10, 636], [2, 645], [2, 646], [4, 645], [6, 644], [2, 649], [4, 648], [2, 651]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 629 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 652], [10, 645], [2, 654], [10, 647], [6, 652], [6, 653], [6, 654], [6, 655], [2, 660], [2, 661], [6, 658], [20, 645], [2, 664], [10, 657], [20, 648], [4, 665], [4, 666], [6, 665], [4, 668], [6, 667], [6, 668], [4, 671], [4, 672], [14, 663], [10, 668]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 654 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[4, 675], [14, 666], [4, 677], [4, 678], [2, 681], [4, 680], [6, 679], [2, 684], [4, 683], [6, 682], [2, 687], [14, 676], [24, 667], [14, 678], [2, 691], [6, 688], [6, 689], [4, 692], [10, 687], [36, 662], [6, 693], [10, 690], [20, 681], [2, 700], [276, 427]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 679 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[20, 684], [4, 701], [10, 696], [2, 705], [6, 702], [4, 705], [14, 696], [6, 705], [10, 702], [6, 707], [2, 712], [4, 711], [2, 714], [2, 715], [6, 712], [2, 717], [6, 714], [6, 715], [2, 720], [10, 713], [4, 720], [24, 701], [2, 724], [24, 703], [2, 726]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 704 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 727], [4, 726], [6, 725], [2, 730], [10, 723], [14, 720], [6, 729], [4, 732], [90, 647], [2, 736], [4, 735], [14, 726], [6, 735], [24, 718], [2, 741], [2, 742], [4, 741], [2, 744], [2, 745], [6, 742], [2, 747], [6, 744], [46, 705], [2, 750], [6, 747]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 729 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[4, 750], [6, 749], [10, 746], [4, 753], [2, 756], [4, 755], [4, 756], [14, 747], [80, 682], [10, 753], [2, 762], [10, 755], [10, 756], [20, 747], [2, 766], [10, 759], [6, 764], [4, 767], [60, 712], [80, 693], [2, 772], [4, 771], [14, 762], [2, 775], [36, 742]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 754 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[2, 777], [6, 774], [6, 775], [2, 780], [20, 763], [4, 780], [6, 779], [2, 784], [24, 763], [2, 786], [10, 779], [6, 784], [36, 755], [2, 790], [6, 787], [2, 792], [4, 791], [4, 792], [90, 707], [6, 792], [90, 709], [14, 786], [2, 799], [4, 798], [2, 801]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 779 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[6, 798], [4, 801], [2, 804], [2, 805], [36, 772], [2, 807], [64, 746], [10, 801], [2, 810], [2, 811], [10, 804], [14, 801], [2, 814], [4, 813], [6, 812], [4, 815], [34, 786], [2, 819], [4, 818], [60, 763], [50, 774], [14, 811], [6, 820], [20, 807], [6, 822]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 804 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[4, 825], [6, 824], [2, 829], [10, 822], [350, 483], [2, 832], [4, 831], [2, 834], [2, 835], [36, 802], [14, 825], [4, 836], [4, 837], [60, 782], [6, 837], [4, 840], [14, 831], [6, 840], [4, 843], [6, 842], [2, 847], [34, 816], [2, 849], [2, 850], [6, 847]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 829 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[6, 848], [20, 835], [4, 852], [2, 855], [20, 838], [46, 813], [24, 836], [46, 815], [34, 828], [2, 861], [2, 862], [6, 859], [14, 852], [14, 853], [6, 862], [2, 867], [4, 866], [4, 867], [14, 858], [2, 871], [24, 850], [20, 855], [2, 874], [4, 873], [6, 872]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 854 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 877], [10, 870], [50, 831], [2, 880], [6, 877], [24, 860], [6, 879], [4, 882], [50, 837], [10, 878], [4, 885], [6, 884], [2, 889], [10, 882], [36, 857], [2, 892], [6, 889], [2, 894], [2, 895], [6, 892], [20, 879], [4, 896], [36, 865], [90, 812], [2, 901]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 879 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[6, 898], [6, 899], [4, 902], [10, 897], [2, 906], [6, 903], [4, 906], [50, 861], [4, 908], [6, 907], [2, 912], [4, 911], [10, 906], [14, 903], [2, 916], [4, 915], [6, 914], [10, 911], [4, 918], [6, 917], [6, 918], [34, 891], [2, 924], [4, 923], [6, 922]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 904 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[14, 915], [10, 920], [10, 921], [104, 828], [2, 931], [4, 930], [6, 929], [2, 934], [24, 913], [2, 936], [2, 937], [34, 906], [2, 939], [2, 940], [66, 877], [24, 920], [10, 935], [4, 942], [2, 945], [6, 942], [4, 945], [14, 936], [6, 945], [10, 942], [2, 951]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 929 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[10, 944], [4, 951], [2, 954], [24, 933], [6, 952], [2, 957], [4, 956], [34, 927], [20, 942], [6, 957], [10, 954], [14, 951], [4, 962], [4, 963], [2, 966], [2, 967], [4, 966], [14, 957], [10, 962], [6, 967], [6, 968], [6, 969], [34, 942], [2, 975], [2, 976]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 954 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[10, 969], [6, 974], [4, 977], [4, 978], [6, 977], [4, 980], [4, 981], [6, 980], [4, 983], [46, 942], [2, 987], [4, 986], [4, 987], [2, 990], [10, 983], [6, 988], [60, 935], [2, 994], [90, 907], [20, 978], [2, 997], [34, 966], [2, 999], [2, 1000], [6, 997]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 979 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `4 ≤ n ≤ 1003` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 4 ≤ n) (h2 : n ≤ 1003) : ∃ x, good n x = true := by
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
  by_cases c32 : n < 829
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 854
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 879
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 904
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 929
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 954
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 979
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a220431Tab

open OMA.Aoeis_a220431Tab in
theorem OMA.solution : OMA.R_oeis_a220431_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
