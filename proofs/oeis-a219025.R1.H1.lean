import OMAReductions.R_oeis_a219025_R1
import Mathlib

-- Step oeis-a219025.R1.H1: hypothesis H1 of reduction oeis-a219025.R1
-- Credit: @prathameshnium. Finite check for 6 ≤ n ≤ 1005.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 6337.

/-! Step oeis-a219025.R1.H1. -/

namespace OMA.Aoeis_a219025Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `81` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 81 2

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
  have hnd := noDiv_sound p 81 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (decide (p < n) && (isPrimeB (p) && (isPrimeB (6 * n - p) && isPrimeB (6 * n + p))))
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
    ∃ p : ℕ, p < n ∧ Nat.Prime p ∧ Nat.Prime (6 * n - p) ∧ Nat.Prime (6 * n + p) := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 6, …, 1005`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[5], [5], [5], [7], [7], [5], [11], [5], [5], [7], [7], [5], [5], [13], [7], [13], [5], [11], [5], [13], [7], [5], [5], [7], [13]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 6 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5], [19], [31], [7], [13], [17], [11], [5], [5], [11], [5], [11], [19], [7], [7], [5], [11], [5], [13], [7], [43], [5], [41], [7], [17]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 31 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[23], [5], [11], [5], [7], [7], [59], [5], [5], [7], [13], [19], [11], [5], [11], [5], [11], [5], [5], [7], [7], [5], [11], [13], [19]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 56 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[23], [29], [11], [5], [11], [7], [19], [19], [13], [17], [23], [5], [11], [7], [7], [67], [5], [11], [7], [7], [7], [5], [41], [7], [11]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 81 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[5], [11], [5], [7], [13], [7], [11], [5], [7], [29], [5], [41], [31], [5], [19], [7], [41], [5], [17], [7], [5], [11], [29], [13], [7]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 106 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[43], [5], [11], [7], [13], [5], [61], [31], [5], [13], [7], [29], [5], [43], [7], [53], [5], [31], [13], [19], [23], [29], [11], [5], [11]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 131 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[17], [5], [19], [13], [7], [47], [5], [31], [7], [7], [13], [11], [11], [5], [11], [5], [19], [71], [5], [11], [5], [29], [19], [13], [11]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 156 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[17], [5], [5], [13], [7], [7], [29], [59], [17], [11], [17], [29], [5], [67], [17], [5], [11], [71], [7], [13], [43], [11], [5], [7], [7]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 181 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[13], [41], [11], [5], [23], [17], [101], [19], [5], [7], [5], [5], [11], [7], [41], [47], [29], [61], [17], [23], [53], [61], [41], [7], [19]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 206 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[13], [31], [31], [5], [29], [7], [61], [5], [5], [7], [7], [19], [29], [17], [11], [5], [11], [5], [5], [11], [17], [19], [31], [43], [19]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 231 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[13], [11], [5], [5], [7], [13], [29], [19], [13], [7], [13], [5], [11], [5], [7], [43], [5], [19], [23], [13], [37], [5], [31], [47], [13]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 256 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[23], [29], [61], [5], [11], [7], [101], [5], [13], [7], [13], [31], [89], [23], [17], [113], [5], [79], [7], [11], [5], [11], [29], [23], [41]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 281 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[53], [19], [59], [7], [13], [5], [5], [11], [5], [11], [17], [29], [41], [37], [13], [47], [19], [59], [43], [37], [23], [11], [19], [23], [7]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 306 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[7], [5], [5], [7], [7], [13], [5], [11], [5], [13], [7], [59], [5], [47], [17], [7], [29], [181], [5], [11], [7], [29], [19], [13], [31]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 331 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5], [11], [5], [67], [19], [13], [31], [89], [23], [47], [17], [41], [5], [7], [17], [13], [11], [31], [7], [37], [13], [11], [29], [7], [7]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 356 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[47], [5], [11], [7], [23], [23], [11], [19], [23], [7], [5], [5], [19], [7], [13], [5], [11], [5], [5], [11], [17], [29], [19], [13], [7]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 381 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[37], [5], [11], [13], [13], [7], [5], [61], [37], [13], [97], [29], [31], [37], [73], [5], [11], [71], [5], [7], [53], [31], [11], [17], [29]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 406 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[7], [41], [19], [13], [53], [67], [71], [19], [13], [7], [13], [5], [41], [7], [7], [13], [5], [5], [5], [7], [7], [19], [11], [5], [11]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 431 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[5], [11], [19], [13], [7], [37], [5], [11], [7], [13], [5], [281], [11], [23], [17], [7], [29], [5], [7], [7], [5], [109], [11], [13], [23]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 456 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[53], [5], [11], [53], [7], [37], [5], [11], [37], [13], [7], [109], [5], [7], [31], [23], [19], [31], [67], [37], [5], [11], [19], [13], [7]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 481 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[13], [19], [139], [13], [19], [17], [11], [11], [5], [29], [13], [19], [29], [5], [71], [37], [71], [29], [23], [13], [47], [41], [89], [7], [11]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 506 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[5], [11], [11], [13], [7], [13], [31], [179], [17], [11], [83], [61], [41], [7], [53], [23], [31], [31], [37], [29], [7], [11], [5], [5], [17]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 531 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[7], [19], [41], [7], [13], [5], [41], [71], [23], [17], [37], [11], [61], [43], [13], [37], [59], [31], [73], [17], [7], [5], [61], [17], [11]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 556 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[53], [79], [29], [13], [19], [17], [5], [11], [5], [7], [13], [5], [59], [7], [11], [5], [11], [5], [13], [7], [67], [5], [5], [7], [7]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 581 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[23], [29], [11], [17], [17], [7], [29], [19], [7], [19], [5], [31], [11], [5], [19], [7], [61], [29], [17], [11], [23], [61], [29], [5], [13]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 606 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[7], [31], [5], [43], [13], [37], [29], [5], [13], [7], [43], [29], [5], [13], [7], [13], [29], [41], [13], [11], [17], [5], [11], [5], [13]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 631 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[7], [61], [19], [47], [29], [23], [29], [11], [17], [23], [7], [71], [5], [7], [7], [23], [19], [11], [113], [23], [37], [11], [11], [17], [31]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 656 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[7], [19], [41], [53], [17], [17], [11], [29], [5], [13], [7], [59], [19], [37], [31], [43], [29], [29], [17], [41], [5], [59], [41], [5], [11]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 681 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[5], [11], [5], [43], [29], [5], [11], [5], [13], [7], [43], [61], [19], [43], [37], [37], [5], [11], [5], [13], [7], [79], [5], [17], [17]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 706 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[23], [29], [59], [47], [13], [7], [59], [19], [13], [17], [5], [5], [61], [17], [13], [127], [31], [5], [13], [7], [13], [5], [5], [43], [17]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 731 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[13], [19], [101], [7], [37], [17], [11], [59], [37], [7], [47], [19], [41], [23], [17], [23], [11], [41], [5], [7], [7], [11], [5], [17], [23]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 756 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[37], [29], [61], [47], [19], [13], [71], [5], [83], [11], [13], [31], [29], [107], [19], [17], [31], [5], [5], [13], [7], [19], [59], [7], [31]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 781 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[53], [29], [61], [23], [29], [5], [59], [79], [53], [13], [7], [31], [179], [5], [11], [7], [61], [5], [7], [7], [13], [5], [31], [37], [7]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 806 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[13], [19], [5], [5], [11], [5], [29], [59], [47], [19], [53], [29], [19], [13], [11], [37], [5], [11], [7], [13], [7], [281], [79], [23], [17]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 831 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[17], [29], [41], [73], [7], [13], [59], [11], [5], [19], [83], [31], [19], [17], [11], [47], [5], [41], [17], [23], [23], [181], [41], [107], [43]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 856 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[107], [11], [89], [43], [13], [7], [241], [5], [53], [7], [67], [29], [61], [17], [23], [43], [31], [269], [13], [7], [7], [5], [19], [7], [11]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 881 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[5], [29], [29], [17], [11], [17], [29], [29], [43], [11], [163], [19], [229], [7], [37], [5], [31], [19], [13], [19], [113], [61], [5], [17], [11]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 906 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[5], [61], [41], [47], [29], [43], [31], [109], [103], [17], [5], [5], [11], [5], [13], [7], [29], [5], [43], [11], [5], [29], [61], [13], [13]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 931 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[43], [41], [31], [37], [19], [17], [29], [29], [43], [11], [5], [11], [59], [7], [7], [13], [11], [11], [5], [7], [5], [5], [11], [5], [23]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 956 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[17], [11], [29], [23], [13], [37], [131], [59], [53], [13], [7], [29], [79], [83], [17], [53], [29], [349], [13], [47], [67], [31], [11], [13], [23]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 981 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `6 ≤ n ≤ 1005` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 6 ≤ n) (h2 : n ≤ 1005) : ∃ x, good n x = true := by
  by_cases c0 : n < 31
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 56
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 81
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 106
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 131
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 156
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 181
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 206
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 231
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 256
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 281
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 306
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 331
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 356
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 381
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 406
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 431
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 456
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 481
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 506
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 531
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 556
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 581
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 606
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 631
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 656
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 681
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 706
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 731
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 756
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 781
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 806
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 831
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 856
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 881
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 906
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 931
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 956
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 981
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a219025Tab

open OMA.Aoeis_a219025Tab in
theorem OMA.solution : OMA.R_oeis_a219025_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
