import OMAReductions.R_oeis_a227909_R1
import Mathlib

-- Step oeis-a227909.R1.H1: hypothesis H1 of reduction oeis-a227909.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 606299.

/-! Step oeis-a227909.R1.H1. -/

namespace OMA.Aoeis_a227909Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `780` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 780 2

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
  have hnd := noDiv_sound p 780 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (p + q = 2 * n) && (isPrimeB (p) && (isPrimeB (q) && isPrimeB ((p - 1) * (q + 1) - 1))))
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
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime ((p - 1) * (q + 1) - 1) := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, q, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2], [3, 3], [3, 5], [5, 5], [5, 7], [3, 11], [5, 11], [7, 11], [7, 13], [5, 17], [5, 19], [3, 23], [11, 17], [11, 19], [3, 29], [11, 23], [5, 31], [7, 31], [17, 23], [5, 37], [3, 41], [5, 41], [7, 41], [7, 43], [5, 47]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[11, 43], [3, 53], [11, 47], [37, 23], [43, 19], [5, 59], [7, 59], [37, 31], [11, 59], [5, 67], [13, 61], [23, 53], [7, 71], [7, 73], [11, 71], [11, 73], [3, 83], [17, 71], [7, 83], [3, 89], [5, 89], [17, 79], [19, 79], [41, 59], [19, 83]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[7, 97], [17, 89], [19, 89], [31, 79], [5, 107], [5, 109], [3, 113], [71, 47], [7, 113], [13, 109], [23, 101], [13, 113], [19, 109], [17, 113], [43, 89], [3, 131], [29, 107], [11, 127], [31, 109], [11, 131], [7, 137], [7, 139], [17, 131], [11, 139], [109, 43]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[5, 149], [5, 151], [7, 151], [11, 149], [5, 157], [7, 157], [17, 149], [11, 157], [7, 163], [23, 149], [23, 151], [3, 173], [41, 137], [67, 113], [3, 179], [5, 179], [5, 181], [7, 181], [101, 89], [29, 163], [3, 191], [17, 179], [7, 191], [7, 193], [29, 173]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[7, 197], [67, 139], [11, 197], [11, 199], [13, 199], [17, 197], [43, 173], [37, 181], [71, 149], [29, 193], [13, 211], [59, 167], [17, 211], [37, 193], [5, 227], [5, 229], [3, 233], [41, 197], [17, 223], [3, 239], [11, 233], [5, 241], [7, 241], [11, 239], [13, 239]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[3, 251], [23, 233], [7, 251], [31, 229], [5, 257], [13, 251], [73, 193], [11, 257], [7, 263], [79, 193], [17, 257], [5, 271], [97, 181], [11, 269], [11, 271], [3, 281], [23, 263], [47, 241], [61, 229], [11, 281], [17, 277], [3, 293], [29, 269], [67, 233], [61, 241]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[11, 293], [13, 293], [37, 271], [17, 293], [5, 307], [7, 307], [89, 227], [7, 311], [37, 283], [11, 311], [7, 317], [13, 313], [71, 257], [17, 313], [19, 313], [17, 317], [5, 331], [31, 307], [47, 293], [11, 331], [7, 337], [53, 293], [31, 317], [67, 283], [41, 311]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[5, 349], [7, 349], [101, 257], [11, 349], [3, 359], [5, 359], [19, 347], [19, 349], [107, 263], [5, 367], [7, 367], [29, 347], [47, 331], [7, 373], [23, 359], [11, 373], [79, 307], [29, 359], [31, 359], [43, 349], [5, 389], [7, 389], [67, 331], [17, 383], [13, 389]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[67, 337], [5, 401], [7, 401], [31, 379], [11, 401], [17, 397], [7, 409], [59, 359], [11, 409], [3, 419], [41, 383], [43, 383], [7, 421], [137, 293], [11, 421], [3, 431], [17, 419], [7, 431], [67, 373], [23, 419], [5, 439], [3, 443], [17, 431], [7, 443], [13, 439]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[53, 401], [7, 449], [19, 439], [17, 443], [5, 457], [67, 397], [5, 461], [37, 431], [331, 139], [5, 467], [11, 463], [19, 457], [11, 467], [31, 449], [211, 271], [17, 467], [7, 479], [67, 421], [11, 479], [5, 487], [3, 491], [29, 467], [37, 461], [37, 463], [11, 491]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[5, 499], [7, 499], [41, 467], [7, 503], [3, 509], [5, 509], [13, 503], [19, 499], [11, 509], [31, 491], [127, 397], [5, 521], [29, 499], [151, 379], [83, 449], [13, 521], [13, 523], [149, 389], [31, 509], [19, 523], [23, 521], [23, 523], [7, 541], [41, 509], [11, 541]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[271, 283], [47, 509], [11, 547], [97, 463], [41, 521], [7, 557], [67, 499], [89, 479], [47, 523], [73, 499], [11, 563], [5, 571], [139, 439], [137, 443], [5, 577], [7, 577], [227, 359], [11, 577], [67, 523], [5, 587], [7, 587], [3, 593], [11, 587], [31, 569], [31, 571]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5, 599], [13, 593], [67, 541], [47, 563], [19, 593], [37, 577], [53, 563], [11, 607], [157, 463], [29, 593], [163, 461], [7, 619], [107, 521], [11, 619], [31, 601], [17, 617], [37, 599], [19, 619], [137, 503], [29, 613], [3, 641], [89, 557], [7, 641], [7, 643], [5, 647]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[13, 641], [3, 653], [17, 641], [7, 653], [3, 659], [71, 593], [5, 661], [37, 631], [11, 659], [11, 661], [31, 643], [17, 659], [107, 571], [61, 619], [5, 677], [23, 661], [3, 683], [11, 677], [71, 619], [151, 541], [17, 677], [5, 691], [37, 661], [41, 659], [41, 661]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[31, 673], [107, 599], [7, 701], [97, 613], [11, 701], [13, 701], [7, 709], [227, 491], [37, 683], [3, 719], [5, 719], [73, 653], [67, 661], [71, 659], [23, 709], [43, 691], [17, 719], [19, 719], [67, 673], [59, 683], [43, 701], [3, 743], [71, 677], [7, 743], [43, 709]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[107, 647], [17, 739], [31, 727], [17, 743], [29, 733], [3, 761], [47, 719], [29, 739], [37, 733], [71, 701], [5, 769], [277, 499], [59, 719], [7, 773], [13, 769], [23, 761], [43, 743], [19, 769], [107, 683], [19, 773], [43, 751], [23, 773], [11, 787], [31, 769], [5, 797]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[7, 797], [79, 727], [47, 761], [67, 743], [3, 809], [53, 761], [29, 787], [7, 811], [47, 773], [13, 809], [13, 811], [17, 809], [7, 821], [7, 823], [11, 821], [5, 829], [13, 823], [17, 821], [17, 823], [19, 823], [5, 839], [7, 839], [19, 829], [191, 659], [13, 839]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[97, 757], [83, 773], [89, 769], [37, 823], [89, 773], [7, 857], [13, 853], [41, 827], [11, 859], [103, 769], [53, 821], [17, 859], [67, 811], [41, 839], [5, 877], [127, 757], [5, 881], [11, 877], [7, 883], [11, 881], [11, 883], [13, 883], [41, 857], [17, 883], [79, 823]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[17, 887], [23, 883], [31, 877], [137, 773], [5, 907], [3, 911], [53, 863], [7, 911], [61, 859], [41, 881], [47, 877], [7, 919], [17, 911], [11, 919], [103, 829], [5, 929], [29, 907], [31, 907], [167, 773], [13, 929], [37, 907], [5, 941], [7, 941], [181, 769], [11, 941]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[43, 911], [3, 953], [11, 947], [101, 859], [43, 919], [11, 953], [13, 953], [199, 769], [17, 953], [149, 823], [7, 967], [233, 743], [11, 967], [127, 853], [5, 977], [7, 977], [67, 919], [17, 971], [7, 983], [73, 919], [11, 983], [5, 991], [211, 787], [71, 929], [61, 941]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[7, 997], [23, 983], [31, 977], [181, 829], [29, 983], [43, 971], [3, 1013], [41, 977], [11, 1009], [3, 1019], [5, 1019], [29, 997], [7, 1021], [17, 1013], [13, 1019], [3, 1031], [5, 1031], [29, 1009], [7, 1033], [281, 761], [5, 1039], [79, 967], [29, 1019], [11, 1039], [3, 1049]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[41, 1013], [7, 1049], [7, 1051], [11, 1049], [41, 1021], [31, 1033], [47, 1019], [17, 1051], [37, 1033], [23, 1049], [11, 1063], [43, 1033], [29, 1049], [47, 1033], [73, 1009], [71, 1013], [37, 1049], [19, 1069], [41, 1049], [23, 1069], [61, 1033], [47, 1049], [7, 1091], [7, 1093], [5, 1097]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[11, 1093], [3, 1103], [11, 1097], [101, 1009], [43, 1069], [23, 1091], [7, 1109], [67, 1051], [101, 1019], [29, 1093], [61, 1063], [113, 1013], [19, 1109], [37, 1093], [23, 1109], [5, 1129], [7, 1129], [29, 1109], [11, 1129], [19, 1123], [41, 1103], [59, 1087], [79, 1069], [101, 1049], [23, 1129]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[67, 1087], [47, 1109], [7, 1151], [151, 1009], [11, 1151], [41, 1123], [43, 1123], [107, 1061], [7, 1163], [19, 1153], [23, 1151], [13, 1163], [61, 1117], [71, 1109], [11, 1171], [397, 787], [83, 1103], [59, 1129], [37, 1153], [5, 1187], [7, 1187], [109, 1087], [17, 1181], [37, 1163], [31, 1171]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[11, 1193], [13, 1193], [7, 1201], [107, 1103], [19, 1193], [13, 1201], [23, 1193], [17, 1201], [7, 1213], [5, 1217], [7, 1217], [3, 1223], [47, 1181], [17, 1213], [3, 1229], [5, 1229], [43, 1193], [37, 1201], [17, 1223], [5, 1237], [13, 1231], [23, 1223], [11, 1237], [127, 1123], [23, 1229]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[5, 1249], [7, 1249], [29, 1229], [31, 1229], [199, 1063], [5, 1259], [7, 1259], [31, 1237], [41, 1229], [41, 1231], [151, 1123], [53, 1223], [19, 1259], [211, 1069], [59, 1223], [5, 1279], [73, 1213], [29, 1259], [7, 1283], [3, 1289], [107, 1187], [5, 1291], [19, 1279], [11, 1289], [11, 1291]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[67, 1237], [17, 1289], [11, 1297], [7, 1303], [5, 1307], [97, 1217], [13, 1303], [59, 1259], [31, 1289], [43, 1279], [5, 1319], [7, 1319], [37, 1291], [41, 1289], [11, 1321], [31, 1303], [107, 1229], [31, 1307], [307, 1033], [53, 1289], [17, 1327], [43, 1303], [71, 1277], [71, 1279], [31, 1321]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[47, 1307], [53, 1303], [31, 1327], [131, 1229], [41, 1321], [37, 1327], [47, 1319], [7, 1361], [277, 1093], [5, 1367], [53, 1321], [73, 1303], [11, 1367], [7, 1373], [61, 1321], [101, 1283], [5, 1381], [7, 1381], [71, 1319], [179, 1213], [103, 1291], [29, 1367], [17, 1381], [97, 1303], [101, 1301]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[23, 1381], [79, 1327], [89, 1319], [11, 1399], [3, 1409], [5, 1409], [97, 1319], [127, 1291], [557, 863], [101, 1321], [43, 1381], [167, 1259], [29, 1399], [7, 1423], [5, 1427], [113, 1321], [157, 1279], [347, 1091], [17, 1423], [3, 1439], [71, 1373], [13, 1433], [127, 1321], [17, 1433], [5, 1447]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[3, 1451], [5, 1451], [11, 1447], [31, 1429], [11, 1451], [5, 1459], [37, 1429], [41, 1427], [211, 1259], [13, 1459], [47, 1427], [29, 1447], [7, 1471], [47, 1433], [23, 1459], [3, 1481], [5, 1481], [29, 1459], [67, 1423], [233, 1259], [13, 1481], [13, 1483], [11, 1487], [7, 1493], [3, 1499]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[11, 1493], [7, 1499], [79, 1429], [71, 1439], [19, 1493], [3, 1511], [5, 1511], [29, 1489], [31, 1489], [23, 1499], [13, 1511], [37, 1489], [29, 1499], [37, 1493], [541, 991], [47, 1487], [13, 1523], [67, 1471], [41, 1499], [11, 1531], [73, 1471], [53, 1493], [149, 1399], [61, 1489], [53, 1499]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[5, 1549], [97, 1459], [107, 1451], [7, 1553], [3, 1559], [53, 1511], [17, 1549], [97, 1471], [71, 1499], [5, 1567], [151, 1423], [5, 1571], [7, 1571], [31, 1549], [23, 1559], [17, 1567], [3, 1583], [149, 1439], [47, 1543], [13, 1579], [23, 1571], [43, 1553], [19, 1579], [17, 1583], [23, 1579]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[3, 1601], [23, 1583], [37, 1571], [157, 1453], [29, 1583], [61, 1553], [67, 1549], [257, 1361], [41, 1579], [13, 1609], [11, 1613], [7, 1619], [19, 1609], [71, 1559], [23, 1609], [7, 1627], [17, 1619], [17, 1621], [31, 1609], [5, 1637], [113, 1531], [19, 1627], [41, 1607], [41, 1609], [43, 1609]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[71, 1583], [19, 1637], [37, 1621], [467, 1193], [41, 1621], [67, 1597], [29, 1637], [31, 1637], [127, 1543], [53, 1619], [5, 1669], [79, 1597], [41, 1637], [11, 1669], [103, 1579], [17, 1667], [23, 1663], [19, 1669], [131, 1559], [23, 1669], [31, 1663], [29, 1667], [79, 1619], [7, 1693], [5, 1697]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[67, 1637], [13, 1693], [11, 1697], [17, 1693], [13, 1699], [107, 1607], [7, 1709], [151, 1567], [11, 1709], [29, 1693], [61, 1663], [29, 1697], [7, 1721], [7, 1723], [23, 1709], [11, 1723], [3, 1733], [17, 1721], [17, 1723], [43, 1699], [131, 1613], [5, 1741], [79, 1669], [17, 1733], [5, 1747]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[7, 1747], [197, 1559], [37, 1721], [61, 1699], [41, 1721], [5, 1759], [7, 1759], [101, 1667], [11, 1759], [31, 1741], [107, 1667], [67, 1709], [151, 1627], [71, 1709], [59, 1723], [7, 1777], [89, 1697], [29, 1759], [67, 1723], [5, 1787], [5, 1789], [7, 1789], [179, 1619], [47, 1753], [79, 1723]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[17, 1787], [5, 1801], [61, 1747], [197, 1613], [149, 1663], [3, 1811], [5, 1811], [29, 1789], [31, 1789], [11, 1811], [41, 1783], [37, 1789], [227, 1601], [137, 1693], [31, 1801], [23, 1811], [47, 1789], [37, 1801], [431, 1409], [19, 1823], [43, 1801], [23, 1823], [17, 1831], [127, 1723], [29, 1823]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[7, 1847], [79, 1777], [137, 1721], [71, 1789], [31, 1831], [17, 1847], [43, 1823], [7, 1861], [47, 1823], [151, 1721], [13, 1861], [5, 1871], [11, 1867], [7, 1873], [11, 1871], [271, 1613], [7, 1879], [101, 1787], [17, 1873], [3, 1889], [5, 1889], [23, 1873], [31, 1867], [11, 1889], [13, 1889]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[3, 1901], [5, 1901], [7, 1901], [211, 1699], [23, 1889], [7, 1907], [37, 1879], [11, 1907], [7, 1913], [163, 1759], [11, 1913], [59, 1867], [67, 1861], [197, 1733], [31, 1901], [3, 1931], [5, 1931], [67, 1871], [61, 1879], [11, 1931], [37, 1907], [79, 1867], [17, 1931], [37, 1913], [151, 1801]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[47, 1907], [7, 1949], [79, 1879], [71, 1889], [13, 1949], [97, 1867], [53, 1913], [17, 1951], [37, 1933], [23, 1949], [23, 1951], [3, 1973], [71, 1907], [67, 1913], [229, 1753], [5, 1979], [13, 1973], [37, 1951], [17, 1973], [5, 1987], [7, 1987], [23, 1973], [127, 1871], [67, 1933], [53, 1949]]
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

end OMA.Aoeis_a227909Tab

open OMA.Aoeis_a227909Tab in
theorem OMA.solution : OMA.R_oeis_a227909_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
