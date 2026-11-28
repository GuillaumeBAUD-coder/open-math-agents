import OMAReductions.R_oeis_a218654_R1
import Mathlib

-- Step oeis-a218654.R1.H1: hypothesis H1 of reduction oeis-a218654.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 892.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 801469.

/-! Step oeis-a218654.R1.H1. -/

namespace OMA.Aoeis_a218654Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `897` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 897 2

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
  have hnd := noDiv_sound p 897 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (x ≤ y) && (decide (x + y = n) && isPrimeB (x ^ 2 + 3 * x * y + y ^ 2))))
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
    ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x ^ 2 + 3 * x * y + y ^ 2) := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 892`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 5], [1, 7], [1, 8], [1, 9], [1, 10], [5, 7], [1, 12], [3, 11], [1, 14], [1, 15], [3, 14], [5, 13], [1, 18], [1, 19], [1, 20], [3, 19], [2, 21], [1, 23], [3, 22], [1, 25]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[4, 23], [1, 27], [3, 26], [1, 29], [1, 30], [9, 23], [2, 31], [3, 31], [1, 34], [5, 31], [2, 35], [1, 37], [1, 38], [7, 33], [1, 40], [5, 37], [2, 41], [1, 43], [1, 44], [1, 45], [3, 44], [1, 47], [3, 46], [1, 49], [2, 49]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 49], [1, 52], [1, 53], [1, 54], [1, 55], [2, 55], [3, 55], [1, 58], [1, 59], [5, 56], [3, 59], [2, 61], [1, 63], [1, 64], [1, 65], [5, 62], [1, 67], [4, 65], [1, 69], [2, 69], [5, 67], [2, 71], [3, 71], [7, 68], [1, 75]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[2, 75], [5, 73], [3, 76], [7, 73], [2, 79], [3, 79], [1, 82], [5, 79], [1, 84], [1, 85], [4, 83], [7, 81], [1, 88], [7, 83], [4, 87], [3, 89], [1, 92], [1, 93], [8, 87], [1, 95], [4, 93], [5, 93], [4, 95], [1, 99], [1, 100]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[5, 97], [1, 102], [3, 101], [8, 97], [9, 97], [5, 102], [13, 95], [4, 105], [3, 107], [2, 109], [13, 99], [3, 110], [1, 113], [1, 114], [5, 111], [5, 112], [5, 113], [4, 115], [1, 119], [2, 119], [3, 119], [11, 112], [3, 121], [1, 124], [1, 125]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[9, 118], [3, 125], [8, 121], [1, 129], [1, 130], [5, 127], [5, 128], [1, 133], [4, 131], [19, 117], [4, 133], [1, 137], [4, 135], [1, 139], [1, 140], [5, 137], [2, 141], [1, 143], [1, 144], [9, 137], [8, 139], [1, 147], [1, 148], [11, 139], [2, 149]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[9, 143], [1, 152], [1, 153], [1, 154], [11, 145], [3, 154], [1, 157], [1, 158], [1, 159], [5, 156], [7, 155], [1, 162], [1, 163], [2, 163], [7, 159], [2, 165], [25, 143], [1, 168], [3, 167], [1, 170], [3, 169], [2, 171], [1, 173], [2, 173], [1, 175]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 172], [11, 167], [3, 176], [1, 179], [1, 180], [23, 159], [2, 181], [1, 183], [2, 183], [1, 185], [2, 185], [1, 187], [10, 179], [11, 179], [1, 190], [5, 187], [1, 192], [9, 185], [1, 194], [1, 195], [2, 195], [5, 193], [1, 198], [3, 197], [4, 197]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[7, 195], [1, 202], [5, 199], [4, 201], [1, 205], [4, 203], [5, 203], [1, 208], [17, 193], [2, 209], [5, 207], [7, 206], [11, 203], [1, 214], [5, 211], [8, 209], [1, 217], [1, 218], [1, 219], [2, 219], [7, 215], [6, 217], [3, 221], [1, 224], [5, 221]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3, 224], [11, 217], [9, 220], [1, 229], [1, 230], [5, 227], [1, 232], [5, 229], [2, 233], [1, 235], [5, 232], [3, 235], [3, 236], [1, 239], [1, 240], [3, 239], [10, 233], [1, 243], [16, 229], [1, 245], [4, 243], [1, 247], [4, 245], [3, 247], [2, 249]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[17, 235], [7, 246], [3, 251], [4, 251], [5, 251], [4, 253], [1, 257], [1, 258], [3, 257], [2, 259], [5, 257], [1, 262], [1, 263], [1, 264], [11, 255], [4, 263], [1, 267], [4, 265], [17, 253], [4, 267], [13, 259], [5, 268], [5, 269], [3, 272], [7, 269]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 275], [5, 273], [4, 275], [3, 277], [1, 280], [5, 277], [2, 281], [5, 279], [1, 284], [17, 269], [2, 285], [1, 287], [10, 279], [1, 289], [2, 289], [3, 289], [3, 290], [1, 293], [7, 288], [1, 295], [2, 295], [1, 297], [3, 296], [7, 293], [1, 300]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[13, 289], [1, 302], [3, 301], [1, 304], [1, 305], [4, 303], [15, 293], [1, 308], [3, 307], [5, 306], [17, 295], [3, 310], [1, 313], [4, 311], [5, 311], [2, 315], [35, 283], [1, 318], [9, 311], [4, 317], [5, 317], [1, 322], [19, 305], [3, 322], [5, 321]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[7, 320], [5, 323], [4, 325], [1, 329], [1, 330], [3, 329], [7, 326], [15, 319], [1, 334], [11, 325], [3, 334], [3, 335], [1, 338], [13, 327], [2, 339], [17, 325], [1, 342], [3, 341], [8, 337], [5, 341], [3, 344], [5, 343], [1, 348], [1, 349], [1, 350]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[3, 349], [2, 351], [1, 353], [3, 352], [11, 345], [2, 355], [1, 357], [5, 354], [1, 359], [1, 360], [13, 349], [2, 361], [1, 363], [4, 361], [19, 347], [3, 364], [3, 365], [14, 355], [19, 351], [4, 367], [7, 365], [1, 372], [1, 373], [2, 373], [11, 365]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[7, 370], [1, 377], [5, 374], [1, 379], [4, 377], [7, 375], [2, 381], [5, 379], [1, 384], [1, 385], [7, 380], [5, 383], [8, 381], [11, 379], [1, 390], [5, 387], [1, 392], [5, 389], [1, 394], [1, 395], [3, 394], [3, 395], [4, 395], [7, 393], [1, 400]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[25, 377], [2, 401], [3, 401], [1, 404], [5, 401], [3, 404], [1, 407], [3, 406], [3, 407], [19, 392], [3, 409], [3, 410], [11, 403], [6, 409], [7, 409], [5, 412], [1, 417], [1, 418], [1, 419], [4, 417], [15, 407], [1, 422], [3, 421], [3, 422], [5, 421]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[8, 419], [1, 427], [5, 424], [7, 423], [1, 430], [7, 425], [1, 432], [11, 423], [16, 419], [5, 431], [3, 434], [7, 431], [5, 434], [3, 437], [2, 439], [3, 439], [3, 440], [19, 425], [1, 444], [5, 441], [2, 445], [1, 447], [1, 448], [1, 449], [2, 449]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3, 449], [1, 452], [3, 451], [1, 454], [1, 455], [9, 448], [3, 455], [4, 455], [7, 453], [1, 460], [13, 449], [1, 462], [3, 461], [4, 461], [7, 459], [2, 465], [1, 467], [9, 460], [11, 459], [1, 470], [5, 467], [1, 472], [1, 473], [1, 474], [9, 467]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[2, 475], [1, 477], [10, 469], [11, 469], [1, 480], [15, 467], [5, 478], [3, 481], [6, 479], [1, 485], [5, 482], [7, 481], [4, 485], [1, 489], [2, 489], [13, 479], [8, 485], [1, 493], [1, 494], [1, 495], [2, 495], [11, 487], [1, 498], [1, 499], [1, 500]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[3, 499], [5, 498], [1, 503], [2, 503], [1, 505], [7, 500], [15, 493], [4, 505], [1, 509], [1, 510], [9, 503], [5, 508], [3, 511], [1, 514], [5, 511], [4, 513], [1, 517], [1, 518], [11, 509], [7, 514], [17, 505], [16, 507], [9, 515], [2, 523], [15, 511]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[5, 522], [1, 527], [3, 526], [1, 529], [5, 526], [9, 523], [2, 531], [5, 529], [2, 533], [5, 531], [2, 535], [13, 525], [4, 535], [13, 527], [1, 540], [7, 535], [7, 536], [1, 543], [3, 542], [5, 541], [2, 545], [1, 547], [1, 548], [1, 549], [1, 550]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[7, 545], [6, 547], [3, 551], [2, 553], [7, 549], [2, 555], [5, 553], [5, 554], [1, 559], [1, 560], [5, 557], [7, 556], [11, 553], [3, 562], [15, 551], [5, 562], [3, 565], [1, 568], [37, 533], [1, 570], [3, 569], [1, 572], [9, 565], [8, 567], [19, 557]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[3, 574], [1, 577], [4, 575], [11, 569], [1, 580], [43, 539], [3, 580], [3, 581], [2, 583], [17, 569], [2, 585], [1, 587], [1, 588], [7, 583], [1, 590], [19, 573], [2, 591], [1, 593], [1, 594], [1, 595], [14, 583], [1, 597], [3, 596], [11, 589], [4, 597]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[13, 589], [5, 598], [1, 603], [2, 603], [1, 605], [2, 605], [3, 605], [4, 605], [1, 609], [5, 606], [7, 605], [3, 610], [5, 609], [2, 613], [1, 615], [9, 608], [1, 617], [4, 615], [7, 613], [4, 617], [19, 603], [3, 620], [1, 623], [1, 624], [5, 621]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[4, 623], [3, 625], [1, 628], [17, 613], [7, 624], [3, 629], [1, 632], [3, 631], [4, 631], [5, 631], [8, 629], [15, 623], [1, 638], [1, 639], [4, 637], [13, 629], [2, 641], [1, 643], [2, 643], [1, 645], [4, 643], [1, 647], [4, 645], [7, 643], [1, 650]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[5, 647], [2, 651], [1, 653], [1, 654], [19, 637], [2, 655], [13, 645], [1, 658], [7, 653], [7, 654], [3, 659], [16, 647], [3, 661], [2, 663], [7, 659], [3, 664], [1, 667], [5, 664], [1, 669], [2, 669], [5, 667], [1, 672], [5, 669], [4, 671], [1, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[5, 672], [7, 671], [4, 675], [9, 671], [2, 679], [5, 677], [1, 682], [13, 671], [4, 681], [1, 685], [5, 682], [5, 683], [4, 685], [7, 683], [1, 690], [13, 679], [1, 692], [3, 691], [1, 694], [7, 689], [3, 694], [11, 687], [1, 698], [11, 689], [2, 699]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[5, 697], [2, 701], [3, 701], [1, 704], [1, 705], [5, 702], [1, 707], [1, 708], [19, 691], [4, 707], [3, 709], [5, 708], [5, 709], [1, 714], [1, 715], [2, 715], [5, 713], [9, 710], [1, 719], [9, 712], [5, 717], [2, 721], [1, 723], [2, 723], [17, 709]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 725], [1, 727], [4, 725], [9, 721], [4, 727], [29, 703], [2, 731], [5, 729], [4, 731], [9, 727], [3, 734], [5, 733], [1, 738], [7, 733], [4, 737], [19, 723], [1, 742], [11, 733], [6, 739], [1, 745], [10, 737], [5, 743], [9, 740], [1, 749], [6, 745]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[3, 749], [1, 752], [1, 753], [2, 753], [17, 739], [7, 750], [11, 747], [5, 754], [9, 751], [1, 760], [5, 757], [1, 762], [15, 749], [1, 764], [19, 747], [4, 763], [11, 757], [1, 768], [3, 767], [11, 760], [7, 765], [7, 766], [19, 755], [6, 769], [1, 775]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[13, 764], [5, 773], [1, 778], [1, 779], [1, 780], [3, 779], [7, 776], [3, 781], [2, 783], [1, 785], [3, 784], [3, 785], [4, 785], [11, 779], [5, 786], [23, 769], [6, 787], [1, 793], [11, 784], [17, 779], [5, 792], [1, 797], [4, 795], [17, 783], [2, 799]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[5, 797], [1, 802], [1, 803], [2, 803], [5, 801], [14, 793], [21, 787], [1, 808], [7, 803], [4, 807], [15, 797], [2, 811], [1, 813], [1, 814], [1, 815], [3, 814], [37, 781], [5, 814], [3, 817], [4, 817], [13, 809], [2, 821], [5, 819], [1, 824], [9, 817]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[10, 817], [5, 823], [4, 825], [3, 827], [11, 820], [5, 827], [1, 832], [13, 821], [2, 833], [17, 819], [2, 835], [1, 837], [4, 835], [11, 829], [2, 839], [5, 837], [2, 841], [5, 839], [1, 844], [11, 835], [3, 844], [1, 847], [10, 839], [3, 847], [4, 847]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[5, 847], [10, 843], [3, 851], [2, 853], [1, 855], [2, 855], [5, 853], [5, 854], [9, 851], [5, 856], [3, 859], [1, 862], [5, 859], [4, 861], [7, 859], [7, 860], [13, 855], [8, 861], [13, 857], [7, 864], [5, 867], [1, 872], [5, 869], [3, 872], [25, 851]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[14, 863], [11, 867], [5, 874], [3, 877], [1, 880], [13, 869], [3, 880], [1, 883], [1, 884], [19, 867], [7, 880], [5, 883], [1, 888], [1, 889], [2, 889], [3, 889]]
theorem len35 : w35.length = 16 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 892` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 892) : ∃ x, good n x = true := by
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

end OMA.Aoeis_a218654Tab

open OMA.Aoeis_a218654Tab in
theorem OMA.solution : OMA.R_oeis_a218654_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
