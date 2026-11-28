import OMAReductions.R_oeis_a230230_R1
import Mathlib

-- Step oeis-a230230.R1.H1: hypothesis H1 of reduction oeis-a230230.R1
-- Credit: @prathameshnium. Finite check for 4 ≤ n ≤ 1003.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 6007.

/-! Step oeis-a230230.R1.H1. -/

namespace OMA.Aoeis_a230230Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `79` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 79 2

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
  have hnd := noDiv_sound p 79 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (p + q = 2 * n) && (isPrimeB (p) && (isPrimeB (q) && (isPrimeB (3 * p - 10) && isPrimeB (3 * q + 10)))))
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
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime (3 * p - 10) ∧
        Nat.Prime (3 * q + 10) := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, q, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 4, …, 1003`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[5, 3], [7, 3], [5, 7], [7, 7], [5, 11], [7, 11], [13, 7], [5, 17], [5, 19], [7, 19], [5, 23], [7, 23], [13, 19], [5, 29], [5, 31], [7, 31], [11, 29], [11, 31], [13, 31], [17, 29], [5, 43], [7, 43], [5, 47], [7, 47], [13, 43]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 4 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[11, 47], [13, 47], [19, 43], [17, 47], [5, 61], [7, 61], [23, 47], [5, 67], [7, 67], [5, 71], [5, 73], [7, 73], [11, 71], [11, 73], [13, 73], [17, 71], [17, 73], [19, 73], [5, 89], [7, 89], [31, 67], [11, 89], [13, 89], [31, 73], [5, 101]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 29 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[7, 101], [37, 73], [5, 107], [5, 109], [7, 109], [5, 113], [7, 113], [13, 109], [11, 113], [13, 113], [19, 109], [17, 113], [19, 113], [61, 73], [23, 113], [31, 107], [31, 109], [5, 137], [7, 137], [37, 109], [11, 137], [13, 137], [79, 73], [5, 149], [5, 151]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 54 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[7, 151], [11, 149], [11, 151], [13, 151], [17, 149], [5, 163], [7, 163], [23, 149], [11, 163], [13, 163], [41, 137], [17, 163], [19, 163], [5, 179], [7, 179], [37, 151], [11, 179], [13, 179], [31, 163], [17, 179], [19, 179], [37, 163], [5, 197], [5, 199], [7, 199]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 79 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[11, 197], [11, 199], [13, 199], [17, 197], [5, 211], [7, 211], [23, 197], [11, 211], [13, 211], [47, 179], [17, 211], [19, 211], [5, 227], [7, 227], [37, 199], [5, 233], [7, 233], [31, 211], [5, 239], [5, 241], [7, 241], [11, 239], [11, 241], [13, 241], [17, 239]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 104 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[17, 241], [19, 241], [23, 239], [23, 241], [67, 199], [41, 227], [31, 239], [31, 241], [41, 233], [5, 271], [7, 271], [41, 239], [11, 271], [13, 271], [5, 281], [5, 283], [7, 283], [11, 281], [11, 283], [13, 283], [17, 281], [17, 283], [19, 283], [23, 281], [23, 283]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 129 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[37, 271], [83, 227], [31, 281], [31, 283], [83, 233], [37, 281], [37, 283], [41, 281], [41, 283], [163, 163], [47, 281], [47, 283], [61, 271], [53, 281], [53, 283], [67, 271], [59, 281], [5, 337], [7, 337], [107, 239], [11, 337], [13, 337], [5, 347], [7, 347], [19, 337]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 154 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 353], [7, 353], [79, 283], [5, 359], [7, 359], [31, 337], [11, 359], [13, 359], [37, 337], [17, 359], [5, 373], [7, 373], [23, 359], [11, 373], [13, 373], [41, 347], [17, 373], [19, 373], [41, 353], [23, 373], [61, 337], [41, 359], [5, 397], [7, 397], [5, 401]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 179 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[7, 401], [13, 397], [11, 401], [5, 409], [7, 409], [17, 401], [11, 409], [13, 409], [23, 401], [17, 409], [19, 409], [83, 347], [23, 409], [37, 397], [5, 431], [7, 431], [31, 409], [11, 431], [5, 439], [7, 439], [17, 431], [11, 439], [13, 439], [23, 431], [17, 439]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 204 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[19, 439], [59, 401], [5, 457], [7, 457], [107, 359], [5, 463], [7, 463], [41, 431], [11, 463], [13, 463], [47, 431], [17, 463], [19, 463], [5, 479], [7, 479], [31, 457], [11, 479], [5, 487], [7, 487], [5, 491], [7, 491], [13, 487], [11, 491], [13, 491], [19, 487]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 229 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[17, 491], [19, 491], [229, 283], [23, 491], [37, 479], [31, 487], [41, 479], [31, 491], [37, 487], [47, 479], [5, 523], [7, 523], [41, 491], [11, 523], [13, 523], [47, 491], [17, 523], [19, 523], [53, 491], [23, 523], [61, 487], [59, 491], [61, 491], [31, 523], [317, 239]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 254 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[67, 491], [37, 523], [83, 479], [41, 523], [79, 487], [5, 563], [7, 563], [109, 463], [11, 563], [5, 571], [7, 571], [17, 563], [5, 577], [7, 577], [23, 563], [11, 577], [13, 577], [101, 491], [17, 577], [19, 577], [5, 593], [7, 593], [31, 571], [11, 593], [13, 593]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 279 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[31, 577], [17, 593], [5, 607], [7, 607], [23, 593], [11, 607], [13, 607], [5, 617], [5, 619], [7, 619], [11, 617], [11, 619], [13, 619], [17, 617], [17, 619], [19, 619], [23, 617], [23, 619], [37, 607], [5, 641], [7, 641], [31, 619], [5, 647], [7, 647], [37, 619]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 304 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[11, 647], [13, 647], [199, 463], [5, 659], [5, 661], [7, 661], [11, 659], [11, 661], [13, 661], [17, 659], [5, 673], [7, 673], [23, 659], [11, 673], [13, 673], [41, 647], [17, 673], [19, 673], [47, 647], [5, 691], [7, 691], [41, 659], [11, 691], [13, 691], [5, 701]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 329 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[7, 701], [19, 691], [11, 701], [5, 709], [7, 709], [17, 701], [11, 709], [13, 709], [23, 701], [17, 709], [19, 709], [83, 647], [23, 709], [61, 673], [89, 647], [37, 701], [31, 709], [41, 701], [53, 691], [37, 709], [5, 743], [7, 743], [61, 691], [11, 743], [13, 743]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 354 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[67, 691], [17, 743], [5, 757], [7, 757], [5, 761], [7, 761], [13, 757], [11, 761], [13, 761], [19, 757], [17, 761], [19, 761], [109, 673], [23, 761], [167, 619], [31, 757], [47, 743], [5, 787], [7, 787], [53, 743], [11, 787], [13, 787], [41, 761], [17, 787], [19, 787]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 379 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[47, 761], [23, 787], [151, 661], [5, 809], [7, 809], [31, 787], [11, 809], [13, 809], [37, 787], [5, 821], [7, 821], [157, 673], [11, 821], [13, 821], [79, 757], [17, 821], [19, 821], [151, 691], [23, 821], [37, 809], [61, 787], [41, 809], [31, 821], [67, 787], [47, 809]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 404 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[37, 821], [151, 709], [41, 821], [107, 757], [79, 787], [47, 821], [61, 809], [163, 709], [53, 821], [67, 809], [307, 571], [59, 821], [61, 821], [97, 787], [269, 617], [5, 883], [7, 883], [5, 887], [7, 887], [13, 883], [11, 887], [13, 887], [19, 883], [17, 887], [19, 887]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 429 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[151, 757], [23, 887], [5, 907], [7, 907], [107, 809], [11, 907], [13, 907], [101, 821], [5, 919], [7, 919], [41, 887], [11, 919], [13, 919], [5, 929], [7, 929], [19, 919], [11, 929], [13, 929], [37, 907], [5, 941], [7, 941], [31, 919], [5, 947], [7, 947], [37, 919]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 454 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[11, 947], [13, 947], [79, 883], [17, 947], [19, 947], [61, 907], [23, 947], [31, 941], [67, 907], [47, 929], [31, 947], [61, 919], [41, 941], [37, 947], [67, 919], [41, 947], [61, 929], [109, 883], [47, 947], [67, 929], [79, 919], [53, 947], [5, 997], [7, 997], [59, 947]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 479 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[11, 997], [13, 997], [83, 929], [5, 1009], [7, 1009], [5, 1013], [7, 1013], [13, 1009], [5, 1019], [7, 1019], [19, 1009], [11, 1019], [13, 1019], [37, 997], [17, 1019], [5, 1033], [7, 1033], [23, 1019], [11, 1033], [13, 1033], [101, 947], [17, 1033], [19, 1033], [41, 1013], [5, 1051]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 504 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[7, 1051], [41, 1019], [11, 1051], [13, 1051], [47, 1019], [17, 1051], [19, 1051], [53, 1019], [5, 1069], [7, 1069], [59, 1019], [11, 1069], [13, 1069], [137, 947], [17, 1069], [19, 1069], [269, 821], [5, 1087], [7, 1087], [83, 1013], [11, 1087], [13, 1087], [5, 1097], [7, 1097], [19, 1087]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 529 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[5, 1103], [7, 1103], [61, 1051], [11, 1103], [13, 1103], [31, 1087], [17, 1103], [5, 1117], [7, 1117], [23, 1103], [11, 1117], [13, 1117], [191, 941], [17, 1117], [19, 1117], [41, 1097], [23, 1117], [109, 1033], [41, 1103], [59, 1087], [31, 1117], [47, 1103], [83, 1069], [37, 1117], [5, 1151]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 554 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[5, 1153], [7, 1153], [11, 1151], [11, 1153], [13, 1153], [5, 1163], [7, 1163], [19, 1153], [11, 1163], [13, 1163], [61, 1117], [17, 1163], [19, 1163], [31, 1153], [23, 1163], [37, 1151], [37, 1153], [5, 1187], [7, 1187], [79, 1117], [11, 1187], [13, 1187], [151, 1051], [17, 1187], [5, 1201]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 579 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[7, 1201], [23, 1187], [11, 1201], [13, 1201], [53, 1163], [17, 1201], [19, 1201], [59, 1163], [23, 1201], [109, 1117], [41, 1187], [67, 1163], [31, 1201], [5, 1229], [7, 1229], [37, 1201], [11, 1229], [13, 1229], [157, 1087], [17, 1229], [19, 1229], [97, 1153], [23, 1229], [53, 1201], [223, 1033]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 604 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[107, 1151], [31, 1229], [61, 1201], [101, 1163], [37, 1229], [67, 1201], [41, 1229], [109, 1163], [157, 1117], [47, 1229], [191, 1087], [79, 1201], [53, 1229], [5, 1279], [7, 1279], [59, 1229], [11, 1279], [13, 1279], [5, 1289], [7, 1289], [19, 1279], [11, 1289], [13, 1289], [151, 1153], [17, 1289]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 629 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[5, 1303], [7, 1303], [5, 1307], [7, 1307], [13, 1303], [11, 1307], [13, 1307], [19, 1303], [5, 1319], [7, 1319], [277, 1051], [11, 1319], [13, 1319], [31, 1303], [17, 1319], [19, 1319], [37, 1303], [23, 1319], [37, 1307], [67, 1279], [41, 1307], [31, 1319], [151, 1201], [47, 1307], [37, 1319]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 654 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[79, 1279], [41, 1319], [59, 1303], [61, 1303], [5, 1361], [7, 1361], [67, 1303], [5, 1367], [7, 1367], [97, 1279], [5, 1373], [7, 1373], [79, 1303], [11, 1373], [5, 1381], [7, 1381], [17, 1373], [11, 1381], [13, 1381], [23, 1373], [17, 1381], [19, 1381], [41, 1361], [23, 1381], [373, 1033]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 679 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[41, 1367], [37, 1373], [31, 1381], [41, 1373], [97, 1319], [37, 1381], [47, 1373], [41, 1381], [223, 1201], [53, 1373], [47, 1381], [151, 1279], [59, 1373], [5, 1429], [7, 1429], [131, 1307], [11, 1429], [13, 1429], [5, 1439], [7, 1439], [19, 1429], [11, 1439], [13, 1439], [151, 1303], [5, 1451]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 704 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[7, 1451], [31, 1429], [11, 1451], [13, 1451], [37, 1429], [17, 1451], [19, 1451], [193, 1279], [23, 1451], [5, 1471], [7, 1471], [41, 1439], [11, 1471], [13, 1471], [47, 1439], [17, 1471], [19, 1471], [41, 1451], [23, 1471], [67, 1429], [47, 1451], [61, 1439], [31, 1471], [5, 1499], [7, 1499]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 729 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[37, 1471], [11, 1499], [13, 1499], [313, 1201], [17, 1499], [19, 1499], [367, 1153], [23, 1499], [53, 1471], [97, 1429], [89, 1439], [31, 1499], [61, 1471], [83, 1451], [5, 1531], [7, 1531], [41, 1499], [11, 1531], [13, 1531], [47, 1499], [5, 1543], [7, 1543], [53, 1499], [5, 1549], [7, 1549]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 754 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[59, 1499], [11, 1549], [13, 1549], [191, 1373], [17, 1549], [19, 1549], [131, 1439], [23, 1549], [31, 1543], [5, 1571], [7, 1571], [31, 1549], [11, 1571], [13, 1571], [37, 1549], [5, 1583], [7, 1583], [61, 1531], [11, 1583], [13, 1583], [67, 1531], [17, 1583], [5, 1597], [7, 1597], [5, 1601]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 779 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[7, 1601], [13, 1597], [5, 1607], [7, 1607], [19, 1597], [11, 1607], [13, 1607], [79, 1543], [17, 1607], [19, 1607], [31, 1597], [23, 1607], [31, 1601], [37, 1597], [53, 1583], [31, 1607], [97, 1543], [41, 1601], [37, 1607], [97, 1549], [41, 1607], [53, 1597], [109, 1543], [47, 1607], [59, 1597]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 804 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[61, 1597], [53, 1607], [61, 1601], [67, 1597], [59, 1607], [5, 1663], [7, 1663], [5, 1667], [7, 1667], [13, 1663], [11, 1667], [13, 1667], [19, 1663], [17, 1667], [19, 1667], [157, 1531], [23, 1667], [109, 1583], [31, 1663], [89, 1607], [31, 1667], [37, 1663], [5, 1697], [5, 1699], [7, 1699]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 829 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[11, 1697], [11, 1699], [13, 1699], [17, 1697], [17, 1699], [19, 1699], [23, 1697], [23, 1699], [61, 1663], [59, 1667], [5, 1723], [7, 1723], [131, 1601], [11, 1723], [13, 1723], [5, 1733], [7, 1733], [19, 1723], [11, 1733], [5, 1741], [7, 1741], [17, 1733], [11, 1741], [13, 1741], [23, 1733]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 854 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[17, 1741], [19, 1741], [191, 1571], [23, 1741], [67, 1699], [101, 1667], [37, 1733], [31, 1741], [41, 1733], [53, 1723], [37, 1741], [47, 1733], [41, 1741], [61, 1723], [53, 1733], [47, 1741], [67, 1723], [59, 1733], [53, 1741], [97, 1699], [101, 1697], [59, 1741], [61, 1741], [107, 1697], [5, 1801]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 879 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[7, 1801], [443, 1367], [11, 1801], [13, 1801], [5, 1811], [7, 1811], [19, 1801], [11, 1811], [13, 1811], [163, 1663], [5, 1823], [7, 1823], [31, 1801], [11, 1823], [5, 1831], [7, 1831], [17, 1823], [11, 1831], [13, 1831], [23, 1823], [17, 1831], [19, 1831], [41, 1811], [23, 1831], [157, 1699]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 904 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[47, 1811], [37, 1823], [31, 1831], [41, 1823], [167, 1699], [37, 1831], [47, 1823], [41, 1831], [151, 1723], [5, 1871], [7, 1871], [79, 1801], [5, 1877], [5, 1879], [7, 1879], [11, 1877], [11, 1879], [13, 1879], [17, 1877], [17, 1879], [19, 1879], [23, 1877], [23, 1879], [163, 1741], [83, 1823]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 929 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[31, 1877], [31, 1879], [41, 1871], [37, 1877], [37, 1879], [5, 1913], [7, 1913], [199, 1723], [11, 1913], [13, 1913], [97, 1831], [17, 1913], [19, 1913], [193, 1741], [23, 1913], [59, 1879], [61, 1879], [131, 1811], [31, 1913], [67, 1879], [137, 1811], [37, 1913], [151, 1801], [5, 1949], [7, 1949]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 954 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[79, 1879], [11, 1949], [13, 1949], [163, 1801], [17, 1949], [19, 1949], [229, 1741], [23, 1949], [61, 1913], [97, 1879], [101, 1877], [31, 1949], [151, 1831], [107, 1877], [37, 1949], [109, 1879], [41, 1949], [79, 1913], [163, 1831], [47, 1949], [167, 1831], [199, 1801], [53, 1949], [5, 1999], [7, 1999]]
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

end OMA.Aoeis_a230230Tab

open OMA.Aoeis_a230230Tab in
theorem OMA.solution : OMA.R_oeis_a230230_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
