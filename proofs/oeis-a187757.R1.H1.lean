import OMAReductions.R_oeis_a187757_R1
import Mathlib

-- Step oeis-a187757.R1.H1: hypothesis H1 of reduction oeis-a187757.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 5927.

/-! Step oeis-a187757.R1.H1. -/

namespace OMA.Aoeis_a187757Tab

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
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (x + y = n) && (isPrimeB (6 * x - 1) && (isPrimeB (6 * x + 1) && (isPrimeB (6 * y + 1) && isPrimeB (6 * y + 5)))))))
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
    (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 1], [1, 2], [1, 3], [2, 3], [3, 3], [1, 6], [1, 7], [2, 7], [3, 7], [5, 6], [1, 11], [2, 11], [1, 13], [2, 13], [3, 13], [1, 16], [1, 17], [1, 18], [2, 18], [3, 18], [1, 21], [2, 21], [3, 21], [7, 18], [5, 21]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[10, 17], [1, 27], [2, 27], [3, 27], [10, 21], [5, 27], [1, 32], [2, 32], [3, 32], [18, 18], [5, 32], [1, 37], [1, 38], [2, 38], [3, 38], [5, 37], [5, 38], [7, 37], [7, 38], [25, 21], [1, 46], [2, 46], [3, 46], [12, 38], [5, 46]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1, 51], [1, 52], [2, 52], [3, 52], [5, 51], [5, 52], [7, 51], [1, 58], [2, 58], [3, 58], [10, 52], [5, 58], [1, 63], [2, 63], [3, 63], [1, 66], [2, 66], [3, 66], [7, 63], [5, 66], [40, 32], [7, 66], [1, 73], [2, 73], [3, 73]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[1, 76], [1, 77], [2, 77], [3, 77], [5, 76], [1, 81], [2, 81], [1, 83], [2, 83], [3, 83], [10, 77], [5, 83], [12, 77], [7, 83], [10, 81], [40, 52], [10, 83], [17, 77], [12, 83], [23, 73], [45, 52], [17, 81], [18, 81], [17, 83], [18, 83]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[25, 77], [1, 102], [2, 102], [3, 102], [23, 83], [5, 102], [1, 107], [2, 107], [3, 107], [30, 81], [5, 107], [1, 112], [2, 112], [3, 112], [33, 83], [5, 112], [45, 73], [7, 112], [18, 102], [38, 83], [10, 112], [40, 83], [1, 123], [2, 123], [3, 123]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[1, 126], [2, 126], [1, 128], [2, 128], [3, 128], [25, 107], [5, 128], [32, 102], [7, 128], [10, 126], [25, 112], [1, 137], [2, 137], [3, 137], [18, 123], [5, 137], [1, 142], [1, 143], [2, 143], [3, 143], [1, 146], [1, 147], [2, 147], [3, 147], [5, 146]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[1, 151], [2, 151], [3, 151], [12, 143], [5, 151], [1, 156], [2, 156], [3, 156], [17, 143], [5, 156], [1, 161], [2, 161], [3, 161], [18, 147], [5, 161], [25, 142], [7, 161], [1, 168], [2, 168], [3, 168], [25, 147], [5, 168], [18, 156], [7, 168], [25, 151]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[30, 147], [10, 168], [18, 161], [12, 168], [25, 156], [1, 181], [1, 182], [2, 182], [3, 182], [5, 181], [5, 182], [7, 181], [7, 182], [47, 143], [10, 181], [10, 182], [12, 181], [12, 182], [52, 143], [40, 156], [95, 102], [17, 181], [17, 182], [18, 182], [33, 168]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[95, 107], [1, 202], [2, 202], [3, 202], [25, 181], [5, 202], [40, 168], [7, 202], [87, 123], [30, 181], [10, 202], [32, 181], [1, 213], [2, 213], [3, 213], [1, 216], [1, 217], [2, 217], [3, 217], [5, 216], [5, 217], [7, 216], [7, 217], [12, 213], [10, 216]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[10, 217], [12, 216], [12, 217], [17, 213], [18, 213], [30, 202], [17, 216], [17, 217], [18, 217], [23, 213], [95, 142], [1, 237], [1, 238], [2, 238], [3, 238], [1, 241], [2, 241], [3, 241], [7, 238], [5, 241], [10, 237], [1, 247], [1, 248], [2, 248], [3, 248]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[5, 247], [5, 248], [7, 247], [7, 248], [18, 238], [10, 247], [10, 248], [1, 258], [2, 258], [3, 258], [1, 261], [2, 261], [1, 263], [2, 263], [3, 263], [1, 266], [2, 266], [1, 268], [2, 268], [3, 268], [25, 247], [5, 268], [33, 241], [7, 268], [10, 266]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[30, 247], [1, 277], [2, 277], [3, 277], [18, 263], [5, 277], [1, 282], [2, 282], [3, 282], [18, 268], [5, 282], [25, 263], [7, 282], [32, 258], [23, 268], [10, 282], [25, 268], [12, 282], [18, 277], [30, 266], [95, 202], [1, 297], [2, 297], [3, 297], [33, 268]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5, 297], [40, 263], [7, 297], [23, 282], [38, 268], [10, 297], [40, 268], [12, 297], [33, 277], [45, 266], [1, 311], [1, 312], [2, 312], [3, 312], [5, 311], [5, 312], [7, 311], [7, 312], [23, 297], [10, 311], [10, 312], [12, 311], [12, 312], [77, 248], [58, 268]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[30, 297], [17, 311], [17, 312], [18, 312], [70, 261], [95, 237], [1, 332], [1, 333], [2, 333], [3, 333], [5, 332], [5, 333], [7, 332], [7, 333], [30, 311], [10, 332], [10, 333], [12, 332], [12, 333], [220, 126], [70, 277], [1, 347], [2, 347], [3, 347], [18, 333]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5, 347], [87, 266], [7, 347], [23, 332], [23, 333], [1, 356], [2, 356], [3, 356], [143, 217], [5, 356], [30, 332], [7, 356], [17, 347], [18, 347], [10, 356], [70, 297], [1, 367], [2, 367], [3, 367], [38, 333], [5, 367], [17, 356], [1, 373], [2, 373], [3, 373]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[10, 367], [5, 373], [1, 378], [2, 378], [3, 378], [70, 312], [1, 382], [2, 382], [3, 382], [30, 356], [5, 382], [10, 378], [7, 382], [12, 378], [18, 373], [1, 391], [2, 391], [3, 391], [17, 378], [5, 391], [1, 396], [2, 396], [1, 398], [2, 398], [3, 398]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[70, 332], [5, 398], [72, 332], [7, 398], [10, 396], [1, 406], [2, 406], [3, 406], [12, 398], [5, 406], [30, 382], [1, 412], [2, 412], [3, 412], [10, 406], [5, 412], [12, 406], [7, 412], [38, 382], [23, 398], [10, 412], [17, 406], [1, 423], [2, 423], [3, 423]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[45, 382], [5, 423], [17, 412], [7, 423], [25, 406], [100, 332], [10, 423], [38, 396], [12, 423], [30, 406], [1, 436], [2, 436], [3, 436], [17, 423], [5, 436], [30, 412], [7, 436], [1, 443], [2, 443], [3, 443], [100, 347], [1, 447], [1, 448], [2, 448], [3, 448]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[1, 451], [2, 451], [3, 451], [7, 448], [5, 451], [10, 447], [7, 451], [1, 458], [2, 458], [3, 458], [95, 367], [5, 458], [17, 447], [7, 458], [18, 448], [1, 466], [2, 466], [3, 466], [12, 458], [5, 466], [25, 447], [1, 472], [2, 472], [3, 472], [10, 466]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1, 476], [2, 476], [3, 476], [32, 448], [5, 476], [10, 472], [7, 476], [12, 472], [38, 447], [10, 476], [40, 447], [12, 476], [17, 472], [18, 472], [25, 466], [45, 447], [1, 492], [2, 492], [3, 492], [30, 466], [5, 492], [32, 466], [7, 492], [52, 448], [25, 476]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[10, 492], [45, 458], [1, 503], [2, 503], [3, 503], [1, 506], [2, 506], [3, 506], [7, 503], [5, 506], [40, 472], [7, 506], [1, 513], [2, 513], [3, 513], [25, 492], [5, 513], [47, 472], [7, 513], [18, 503], [30, 492], [10, 513], [18, 506], [12, 513], [23, 503]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[215, 312], [1, 527], [2, 527], [3, 527], [18, 513], [1, 531], [2, 531], [3, 531], [32, 503], [5, 531], [1, 536], [2, 536], [3, 536], [338, 202], [5, 536], [70, 472], [1, 542], [2, 542], [3, 542], [10, 536], [5, 542], [12, 536], [7, 542], [23, 527], [38, 513]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[10, 542], [17, 536], [1, 553], [2, 553], [3, 553], [30, 527], [1, 557], [2, 557], [3, 557], [25, 536], [5, 557], [10, 553], [7, 557], [12, 553], [30, 536], [10, 557], [32, 536], [12, 557], [17, 553], [18, 553], [30, 542], [70, 503], [17, 557], [18, 557], [23, 553]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1, 576], [1, 577], [2, 577], [3, 577], [5, 576], [5, 577], [7, 576], [7, 577], [32, 553], [10, 576], [10, 577], [12, 576], [1, 588], [2, 588], [3, 588], [100, 492], [5, 588], [17, 577], [7, 588], [138, 458], [40, 557], [10, 588], [23, 576], [12, 588], [25, 576]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[25, 577], [1, 602], [2, 602], [3, 602], [18, 588], [5, 602], [32, 576], [7, 602], [33, 577], [23, 588], [10, 602], [1, 612], [2, 612], [3, 612], [40, 576], [1, 616], [2, 616], [3, 616], [18, 602], [5, 616], [10, 612], [7, 616], [12, 612], [23, 602], [10, 616]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[25, 602], [12, 616], [17, 612], [18, 612], [95, 536], [30, 602], [1, 632], [2, 632], [3, 632], [100, 536], [5, 632], [107, 531], [7, 632], [38, 602], [25, 616], [1, 641], [2, 641], [3, 641], [33, 612], [5, 641], [1, 646], [2, 646], [3, 646], [18, 632], [5, 646]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1, 651], [2, 651], [1, 653], [2, 653], [3, 653], [25, 632], [1, 657], [2, 657], [3, 657], [10, 651], [5, 657], [10, 653], [7, 657], [12, 653], [25, 641], [10, 657], [1, 667], [2, 667], [3, 667], [18, 653], [5, 667], [32, 641], [7, 667], [18, 657], [23, 653]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[10, 667], [25, 653], [12, 667], [23, 657], [30, 651], [25, 657], [30, 653], [17, 667], [18, 667], [33, 653], [30, 657], [47, 641], [1, 688], [2, 688], [3, 688], [25, 667], [1, 692], [2, 692], [3, 692], [45, 651], [5, 692], [10, 688], [7, 692], [12, 688], [170, 531]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[10, 692], [52, 651], [12, 692], [17, 688], [18, 688], [40, 667], [172, 536], [17, 692], [18, 692], [23, 688], [45, 667], [25, 688], [47, 667], [23, 692], [70, 646], [25, 692], [30, 688], [52, 667], [32, 688], [33, 688], [30, 692], [70, 653], [32, 692], [33, 692], [38, 688]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[70, 657], [40, 688], [72, 657], [38, 692], [143, 588], [40, 692], [45, 688], [77, 657], [47, 688], [95, 641], [45, 692], [87, 651], [47, 692], [52, 688], [95, 646], [1, 741], [2, 741], [3, 741], [143, 602], [5, 741], [135, 612], [7, 741], [103, 646], [58, 692], [10, 741]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[95, 657], [1, 752], [1, 753], [2, 753], [3, 753], [5, 752], [5, 753], [7, 752], [7, 753], [110, 651], [10, 752], [10, 753], [12, 752], [12, 753], [25, 741], [100, 667], [192, 576], [17, 752], [17, 753], [18, 753], [170, 602], [32, 741], [1, 773], [2, 773], [3, 773]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[25, 752], [5, 773], [38, 741], [7, 773], [40, 741], [30, 752], [10, 773], [32, 752], [12, 773], [33, 753], [95, 692], [47, 741], [1, 788], [2, 788], [3, 788], [40, 752], [5, 788], [137, 657], [7, 788], [23, 773], [45, 752], [1, 797], [1, 798], [2, 798], [3, 798]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[5, 797], [1, 802], [2, 802], [3, 802], [18, 788], [5, 802], [10, 798], [7, 802], [12, 798], [23, 788], [10, 802], [25, 788], [12, 802], [17, 798], [18, 798], [205, 612], [30, 788], [17, 802], [18, 802], [23, 798], [25, 797], [1, 822], [2, 822], [3, 822], [38, 788]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[5, 822], [30, 798], [1, 828], [2, 828], [3, 828], [10, 822], [5, 828], [1, 833], [2, 833], [3, 833], [40, 797], [5, 833], [17, 822], [7, 833], [100, 741], [40, 802], [10, 833], [47, 797], [12, 833], [18, 828], [1, 846], [2, 846], [3, 846], [17, 833], [5, 846]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[30, 822], [7, 846], [32, 822], [33, 822], [10, 846], [385, 472], [12, 846], [107, 752], [32, 828], [33, 828], [1, 861], [2, 861], [3, 861], [32, 833], [5, 861], [45, 822], [7, 861], [23, 846], [72, 798], [10, 861], [1, 871], [1, 872], [2, 872], [3, 872], [5, 871]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[5, 872], [7, 871], [7, 872], [47, 833], [10, 871], [10, 872], [12, 871], [12, 872], [52, 833], [25, 861], [135, 752], [17, 871], [17, 872], [18, 872], [30, 861], [1, 891], [2, 891], [3, 891], [23, 872], [5, 891], [25, 872], [7, 891], [38, 861], [72, 828], [10, 891]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[30, 872], [1, 902], [2, 902], [3, 902], [45, 861], [1, 906], [2, 906], [3, 906], [38, 872], [5, 906], [10, 902], [7, 906], [1, 913], [2, 913], [3, 913], [45, 872], [1, 917], [2, 917], [3, 917], [30, 891], [1, 921], [2, 921], [3, 921], [12, 913], [5, 921]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[10, 917], [7, 921], [1, 928], [2, 928], [3, 928], [30, 902], [5, 928], [17, 917], [7, 928], [23, 913], [135, 802], [10, 928], [18, 921], [12, 928], [70, 871], [1, 941], [1, 942], [2, 942], [3, 942], [5, 941], [5, 942], [7, 941], [1, 948], [2, 948], [3, 948]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[10, 942], [5, 948], [12, 942], [7, 948], [95, 861], [1, 956], [2, 956], [3, 956], [12, 948], [5, 956], [45, 917], [7, 956], [1, 963], [2, 963], [3, 963], [25, 942], [5, 963], [52, 917], [7, 963], [23, 948], [30, 942], [10, 963], [1, 973], [2, 973], [3, 973]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[1, 976], [2, 976], [3, 976], [7, 973], [5, 976], [40, 942], [7, 976], [138, 846], [12, 973], [10, 976], [45, 942], [1, 987], [2, 987], [3, 987], [18, 973], [5, 987], [17, 976], [7, 987], [32, 963], [23, 973], [10, 987], [25, 973], [12, 987], [52, 948], [25, 976]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 977 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 1001` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 1001) : ∃ x, good n x = true := by
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
  by_cases c35 : n < 902
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 927
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 952
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 977
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a187757Tab

open OMA.Aoeis_a187757Tab in
theorem OMA.solution : OMA.R_oeis_a187757_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
