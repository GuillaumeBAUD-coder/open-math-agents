import OMAReductions.R_oeis_a230351_R1
import Mathlib

-- Step oeis-a230351.R1.H1: hypothesis H1 of reduction oeis-a230351.R1
-- Credit: @prathameshnium. Finite check for 4 ≤ n ≤ 750.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1104097.

/-! Step oeis-a230351.R1.H1. -/

namespace OMA.Aoeis_a230351Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1052` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1052 2

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
  have hnd := noDiv_sound p 1052 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (0 < q) && (decide (p + q = n) && (isPrimeB (p) && (isPrimeB (2 * p ^ 2 - 1) && isPrimeB (2 * q ^ 2 - 1)))))
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
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧
    p.Prime ∧ (2 * p ^ 2 - 1).Prime ∧ (2 * q ^ 2 - 1).Prime := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, q, a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 4, …, 750`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2], [2, 3], [2, 4], [3, 4], [2, 6], [2, 7], [2, 8], [3, 8], [2, 10], [2, 11], [3, 11], [2, 13], [3, 13], [2, 15], [3, 15], [2, 17], [2, 18], [3, 18], [7, 15], [2, 21], [2, 22], [3, 22], [2, 24], [2, 25], [3, 25]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 4 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[7, 22], [2, 28], [3, 28], [7, 25], [11, 22], [13, 21], [7, 28], [2, 34], [3, 34], [2, 36], [3, 36], [2, 38], [2, 39], [3, 39], [2, 41], [2, 42], [2, 43], [3, 43], [2, 45], [2, 46], [3, 46], [7, 43], [2, 49], [2, 50], [3, 50]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 29 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 52], [3, 52], [7, 49], [7, 50], [2, 56], [3, 56], [11, 49], [2, 59], [3, 59], [7, 56], [2, 62], [2, 63], [2, 64], [3, 64], [43, 25], [7, 62], [7, 63], [2, 69], [3, 69], [11, 62], [11, 63], [2, 73], [3, 73], [13, 64], [2, 76]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 54 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 76], [7, 73], [17, 64], [2, 80], [2, 81], [3, 81], [43, 42], [13, 73], [2, 85], [3, 85], [2, 87], [3, 87], [11, 80], [7, 85], [2, 91], [2, 92], [3, 92], [11, 85], [2, 95], [3, 95], [7, 92], [2, 98], [3, 98], [7, 95], [11, 92]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 79 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 102], [3, 102], [11, 95], [43, 64], [13, 95], [7, 102], [2, 108], [2, 109], [3, 109], [11, 102], [2, 112], [2, 113], [3, 113], [2, 115], [3, 115], [7, 112], [2, 118], [3, 118], [7, 115], [11, 112], [11, 113], [7, 118], [11, 115], [2, 125], [2, 126]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 104 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 127], [3, 127], [13, 118], [7, 125], [7, 126], [2, 132], [3, 132], [2, 134], [3, 134], [11, 127], [2, 137], [3, 137], [7, 134], [2, 140], [2, 141], [3, 141], [2, 143], [3, 143], [7, 140], [7, 141], [17, 132], [7, 143], [11, 140], [11, 141], [13, 140]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 129 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[11, 143], [2, 153], [2, 154], [2, 155], [3, 155], [2, 157], [2, 158], [3, 158], [2, 160], [3, 160], [7, 157], [7, 158], [2, 164], [2, 165], [3, 165], [11, 158], [13, 157], [7, 164], [7, 165], [2, 171], [2, 172], [3, 172], [11, 165], [13, 164], [7, 171]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 154 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[7, 172], [2, 178], [2, 179], [3, 179], [2, 181], [3, 181], [2, 183], [3, 183], [2, 185], [2, 186], [3, 186], [2, 188], [3, 188], [7, 185], [7, 186], [2, 192], [3, 192], [11, 185], [11, 186], [2, 196], [2, 197], [3, 197], [2, 199], [2, 200], [3, 200]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 179 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[7, 197], [13, 192], [2, 204], [3, 204], [2, 206], [3, 206], [11, 199], [7, 204], [13, 199], [2, 211], [3, 211], [11, 204], [2, 214], [3, 214], [7, 211], [13, 206], [41, 179], [7, 214], [2, 220], [3, 220], [13, 211], [11, 214], [41, 185], [7, 220], [17, 211]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 204 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[41, 188], [2, 228], [3, 228], [137, 95], [2, 231], [2, 232], [3, 232], [109, 127], [17, 220], [7, 231], [2, 237], [2, 238], [3, 238], [11, 231], [11, 232], [2, 242], [3, 242], [109, 137], [2, 245], [3, 245], [7, 242], [2, 248], [2, 249], [3, 249], [2, 251]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 229 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3, 251], [7, 248], [7, 249], [43, 214], [2, 256], [3, 256], [11, 249], [2, 259], [3, 259], [7, 256], [13, 251], [2, 263], [3, 263], [2, 265], [2, 266], [3, 266], [7, 263], [43, 228], [2, 270], [3, 270], [11, 263], [2, 273], [2, 274], [3, 274], [13, 265]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 254 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 277], [3, 277], [7, 274], [2, 280], [3, 280], [7, 277], [11, 274], [13, 273], [7, 280], [11, 277], [41, 248], [2, 288], [3, 288], [41, 251], [2, 291], [3, 291], [2, 293], [2, 294], [2, 295], [3, 295], [2, 297], [3, 297], [7, 294], [2, 300], [2, 301]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 279 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3, 301], [11, 294], [2, 304], [2, 305], [3, 305], [43, 266], [13, 297], [7, 304], [7, 305], [2, 311], [2, 312], [3, 312], [11, 305], [13, 304], [7, 311], [7, 312], [43, 277], [17, 304], [11, 311], [2, 321], [2, 322], [2, 323], [3, 323], [113, 214], [7, 321]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 304 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[7, 322], [7, 323], [2, 329], [3, 329], [11, 322], [2, 332], [3, 332], [7, 329], [2, 335], [3, 335], [7, 332], [11, 329], [2, 339], [3, 339], [11, 332], [43, 301], [13, 332], [7, 339], [43, 304], [2, 346], [3, 346], [11, 339], [109, 242], [13, 339], [7, 346]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 329 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[43, 311], [2, 353], [3, 353], [11, 346], [109, 249], [13, 346], [7, 353], [73, 288], [41, 321], [17, 346], [11, 353], [2, 363], [2, 364], [2, 365], [3, 365], [2, 367], [3, 367], [7, 364], [7, 365], [41, 332], [2, 372], [3, 372], [2, 374], [2, 375], [3, 375]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 354 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[7, 372], [2, 378], [2, 379], [3, 379], [11, 372], [17, 367], [7, 378], [2, 384], [3, 384], [2, 386], [3, 386], [11, 379], [7, 384], [13, 379], [2, 391], [3, 391], [11, 384], [17, 379], [11, 386], [7, 391], [13, 386], [109, 291], [17, 384], [11, 391], [17, 386]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 379 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[2, 402], [3, 402], [41, 365], [43, 364], [2, 406], [3, 406], [43, 367], [2, 409], [2, 410], [3, 410], [109, 305], [13, 402], [2, 414], [3, 414], [2, 416], [3, 416], [11, 409], [2, 419], [3, 419], [7, 416], [59, 365], [11, 414], [7, 419], [11, 416], [2, 426]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 404 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[2, 427], [3, 427], [17, 414], [13, 419], [7, 426], [7, 427], [2, 433], [3, 433], [2, 435], [3, 435], [2, 437], [3, 437], [109, 332], [2, 440], [2, 441], [2, 442], [3, 442], [2, 444], [3, 444], [7, 441], [2, 447], [2, 448], [3, 448], [11, 441], [11, 442]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 429 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[2, 452], [3, 452], [127, 329], [2, 455], [3, 455], [7, 452], [2, 458], [2, 459], [3, 459], [11, 452], [17, 447], [7, 458], [7, 459], [2, 465], [2, 466], [3, 466], [2, 468], [3, 468], [2, 470], [3, 470], [2, 472], [3, 472], [11, 465], [2, 475], [3, 475]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 454 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[7, 472], [43, 437], [11, 470], [7, 475], [11, 472], [2, 482], [3, 482], [11, 475], [17, 470], [2, 486], [2, 487], [3, 487], [2, 489], [3, 489], [7, 486], [7, 487], [13, 482], [7, 489], [11, 486], [11, 487], [13, 486], [2, 498], [3, 498], [13, 489], [2, 501]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 479 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[3, 501], [7, 498], [17, 489], [2, 505], [3, 505], [11, 498], [2, 508], [3, 508], [7, 505], [41, 472], [2, 512], [3, 512], [2, 514], [3, 514], [13, 505], [2, 517], [3, 517], [2, 519], [3, 519], [11, 512], [7, 517], [11, 514], [7, 519], [13, 514], [2, 526]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 504 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 526], [2, 528], [3, 528], [13, 519], [7, 526], [2, 532], [2, 533], [3, 533], [2, 535], [3, 535], [7, 532], [7, 533], [2, 539], [3, 539], [11, 532], [2, 542], [3, 542], [7, 539], [137, 410], [2, 546], [3, 546], [11, 539], [2, 549], [3, 549], [7, 546]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 529 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 552], [3, 552], [7, 549], [11, 546], [2, 556], [3, 556], [11, 549], [2, 559], [3, 559], [7, 556], [59, 505], [2, 563], [3, 563], [11, 556], [109, 459], [2, 567], [3, 567], [43, 528], [2, 570], [2, 571], [3, 571], [2, 573], [3, 573], [7, 570], [7, 571]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 554 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 577], [3, 577], [11, 570], [2, 580], [3, 580], [2, 582], [3, 582], [13, 573], [7, 580], [11, 577], [7, 582], [13, 577], [11, 580], [43, 549], [11, 582], [17, 577], [13, 582], [109, 487], [2, 595], [3, 595], [17, 582], [41, 559], [59, 542], [7, 595], [137, 466]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 579 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[2, 602], [3, 602], [11, 595], [109, 498], [2, 606], [3, 606], [2, 608], [3, 608], [2, 610], [3, 610], [41, 573], [7, 608], [43, 573], [7, 610], [41, 577], [2, 617], [3, 617], [2, 619], [2, 620], [3, 620], [2, 622], [2, 623], [3, 623], [7, 620], [11, 617]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 604 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[7, 622], [7, 623], [11, 620], [13, 619], [11, 622], [11, 623], [13, 622], [2, 634], [3, 634], [2, 636], [3, 636], [17, 623], [7, 634], [109, 533], [7, 636], [73, 571], [11, 634], [73, 573], [11, 636], [109, 539], [13, 636], [73, 577], [17, 634], [2, 650], [2, 651]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 629 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 652], [3, 652], [2, 654], [3, 654], [7, 651], [7, 652], [41, 619], [2, 659], [3, 659], [11, 652], [13, 651], [11, 654], [7, 659], [13, 654], [17, 651], [17, 652], [11, 659], [17, 654], [13, 659], [2, 671], [3, 671], [41, 634], [17, 659], [2, 675], [3, 675]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 654 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[43, 636], [109, 571], [2, 679], [3, 679], [73, 610], [13, 671], [157, 528], [7, 679], [179, 508], [13, 675], [109, 580], [11, 679], [2, 689], [2, 690], [3, 690], [43, 651], [2, 693], [3, 693], [7, 690], [2, 696], [3, 696], [7, 693], [11, 690], [13, 689], [2, 701]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 679 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[3, 701], [2, 703], [3, 703], [11, 696], [2, 706], [3, 706], [2, 708], [3, 708], [2, 710], [3, 710], [11, 703], [2, 713], [3, 713], [2, 715], [3, 715], [11, 708], [2, 718], [3, 718], [2, 720], [2, 721], [3, 721], [7, 718], [11, 715], [7, 720], [7, 721]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 704 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[11, 718], [17, 713], [2, 729], [3, 729], [2, 731], [3, 731], [17, 718], [7, 729], [2, 735], [2, 736], [3, 736], [11, 729], [2, 739], [3, 739], [7, 736], [2, 742], [2, 743], [3, 743], [11, 736], [13, 735], [7, 742], [7, 743]]
theorem len29 : w29.length = 22 := rfl
theorem ok29 : checkList 729 w29 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `4 ≤ n ≤ 750` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 4 ≤ n) (h2 : n ≤ 750) : ∃ x, good n x = true := by
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
  exact chunk ok29 len29 (by omega) (by omega)

end OMA.Aoeis_a230351Tab

open OMA.Aoeis_a230351Tab in
theorem OMA.solution : OMA.R_oeis_a230351_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
