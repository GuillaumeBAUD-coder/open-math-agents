import OMAReductions.R_oeis_a240233_R1
import Mathlib

-- Step oeis-a240233.R1.H1: hypothesis H1 of reduction oeis-a240233.R1
-- Credit: @prathameshnium. Finite check for 1 ≤ n ≤ 1000.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 12289.

/-! Step oeis-a240233.R1.H1. -/

namespace OMA.Aoeis_a240233Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `112` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 112 2

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
  have hnd := noDiv_sound p 112 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (isPrimeB (p) && (isPrimeB (p + 6 * n) && isPrimeB (p + 12 * n)))
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
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 6 * n) ∧ Nat.Prime (p + 12 * n) := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1, …, 1000`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[5], [5], [5], [5], [7], [7], [5], [5], [5], [7], [5], [7], [11], [5], [11], [5], [7], [23], [13], [11], [5], [5], [41], [5], [7]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[37], [29], [11], [5], [13], [7], [5], [13], [23], [13], [7], [5], [5], [23], [11], [11], [5], [5], [13], [7], [5], [29], [23], [13], [7]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 26 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[5], [19], [41], [13], [17], [11], [7], [5], [19], [7], [7], [7], [5], [5], [7], [5], [7], [11], [29], [13], [5], [17], [5], [19], [7]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 51 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[7], [5], [11], [5], [7], [5], [7], [23], [5], [11], [7], [19], [13], [23], [7], [11], [5], [13], [23], [23], [11], [17], [5], [5], [13]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 76 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[11], [5], [13], [29], [17], [5], [5], [5], [19], [41], [67], [29], [5], [59], [19], [31], [67], [11], [5], [7], [7], [7], [5], [43], [11]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 101 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[31], [7], [43], [23], [7], [11], [17], [11], [5], [17], [5], [89], [11], [29], [13], [7], [5], [5], [13], [7], [7], [37], [103], [13], [11]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 126 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[61], [7], [11], [13], [7], [5], [5], [5], [23], [11], [17], [5], [31], [29], [7], [37], [7], [11], [83], [13], [37], [17], [11], [43], [11]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 151 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[31], [7], [103], [13], [43], [7], [37], [11], [5], [19], [7], [7], [53], [19], [13], [5], [29], [23], [23], [11], [5], [19], [5], [23], [17]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 176 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[11], [17], [5], [73], [7], [67], [37], [43], [23], [19], [11], [5], [23], [23], [11], [71], [5], [73], [5], [7], [41], [29], [23], [23], [11]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 201 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[17], [5], [5], [53], [29], [47], [7], [41], [29], [13], [11], [7], [5], [19], [7], [5], [59], [23], [29], [13], [5], [5], [23], [73], [11]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 226 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[37], [37], [5], [19], [19], [7], [37], [23], [13], [47], [5], [37], [31], [13], [7], [11], [5], [5], [23], [17], [67], [37], [31], [13], [7]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 251 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[7], [5], [53], [23], [13], [61], [5], [11], [5], [13], [17], [19], [5], [43], [19], [7], [7], [31], [13], [7], [7], [7], [83], [29], [23]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 276 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5], [19], [61], [23], [17], [37], [109], [13], [19], [7], [7], [17], [11], [29], [17], [5], [29], [5], [19], [11], [67], [17], [13], [29], [23]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 301 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[17], [127], [11], [19], [7], [17], [5], [5], [13], [7], [47], [5], [71], [5], [13], [7], [29], [11], [5], [13], [5], [47], [41], [43], [11]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 326 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5], [17], [23], [5], [11], [17], [79], [31], [83], [19], [41], [79], [163], [23], [17], [17], [5], [5], [23], [17], [11], [19], [5], [29], [17]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 351 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[11], [79], [13], [13], [7], [11], [19], [41], [29], [23], [17], [19], [23], [5], [11], [11], [19], [13], [59], [11], [7], [29], [11], [5], [17]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 376 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[5], [47], [41], [13], [11], [5], [5], [73], [23], [13], [11], [59], [43], [19], [13], [7], [19], [23], [79], [11], [67], [17], [5], [13], [7]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 401 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[197], [29], [11], [5], [11], [7], [97], [101], [29], [7], [5], [37], [5], [13], [17], [11], [5], [31], [19], [7], [127], [17], [5], [5], [7]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 426 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[5], [7], [13], [29], [11], [5], [47], [5], [13], [7], [31], [19], [13], [5], [11], [47], [107], [43], [19], [13], [7], [5], [13], [13], [11]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 451 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[5], [17], [71], [43], [23], [11], [17], [5], [5], [7], [11], [5], [11], [29], [17], [11], [19], [11], [59], [41], [191], [17], [11], [223], [11]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 476 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[17], [29], [31], [43], [7], [101], [7], [173], [13], [23], [71], [7], [41], [5], [19], [71], [7], [13], [73], [17], [11], [5], [53], [23], [17]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 501 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[11], [5], [23], [13], [7], [17], [37], [31], [13], [7], [37], [7], [73], [23], [11], [61], [47], [13], [43], [29], [47], [17], [31], [19], [7]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 526 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[7], [79], [43], [5], [13], [7], [5], [13], [53], [13], [5], [17], [71], [23], [23], [11], [59], [41], [43], [29], [31], [97], [23], [19], [7]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 551 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[5], [37], [23], [43], [11], [5], [7], [31], [113], [7], [11], [59], [13], [59], [41], [11], [5], [13], [59], [11], [7], [89], [43], [19], [7]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 576 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[7], [5], [73], [73], [47], [37], [67], [11], [23], [11], [61], [5], [13], [43], [37], [97], [7], [61], [5], [19], [7], [157], [23], [53], [17]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 601 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[5], [5], [11], [29], [13], [11], [5], [53], [73], [23], [7], [29], [61], [13], [7], [7], [37], [73], [13], [19], [5], [29], [41], [29], [17]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 626 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[5], [5], [5], [5], [13], [7], [79], [41], [103], [7], [61], [157], [113], [43], [13], [17], [5], [43], [59], [29], [127], [17], [11], [5], [23]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 651 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[97], [37], [11], [19], [11], [7], [7], [13], [23], [17], [11], [109], [31], [5], [13], [71], [7], [53], [173], [47], [67], [59], [13], [59], [19]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 676 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[11], [5], [11], [19], [41], [101], [17], [5], [5], [23], [5], [137], [71], [5], [47], [31], [37], [31], [13], [7], [11], [5], [71], [5], [7]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 701 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[7], [29], [5], [73], [43], [11], [157], [11], [53], [11], [5], [19], [193], [73], [7], [37], [29], [193], [43], [11], [17], [37], [31], [13], [7]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 726 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[17], [5], [5], [43], [31], [31], [7], [13], [29], [7], [71], [149], [5], [13], [7], [7], [37], [41], [29], [17], [31], [17], [5], [5], [23]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 751 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[7], [17], [5], [29], [11], [5], [29], [23], [29], [11], [5], [29], [5], [53], [11], [5], [7], [31], [19], [47], [127], [79], [11], [109], [13]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 776 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[7], [5], [13], [163], [59], [67], [127], [23], [79], [29], [11], [5], [11], [19], [53], [37], [7], [23], [5], [11], [5], [19], [31], [13], [7]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 801 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[11], [5], [5], [19], [7], [37], [107], [11], [83], [41], [5], [17], [11], [43], [11], [41], [7], [23], [13], [11], [11], [5], [83], [5], [47]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 826 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[41], [97], [53], [23], [41], [17], [5], [5], [13], [11], [5], [89], [101], [89], [19], [37], [29], [71], [59], [13], [5], [149], [23], [79], [29]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 851 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[17], [89], [131], [59], [29], [17], [5], [5], [5], [37], [7], [109], [53], [103], [7], [41], [29], [23], [43], [107], [37], [17], [5], [43], [31]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 876 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[71], [7], [23], [13], [7], [67], [7], [53], [29], [17], [5], [5], [23], [19], [13], [11], [67], [11], [43], [7], [5], [107], [43], [29], [13]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 901 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[7], [7], [13], [109], [11], [5], [59], [43], [43], [31], [7], [17], [23], [5], [7], [7], [7], [53], [163], [13], [17], [19], [23], [23], [11]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 926 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[11], [67], [31], [19], [7], [47], [7], [31], [89], [31], [17], [7], [23], [29], [17], [5], [179], [5], [29], [37], [127], [17], [5], [13], [17]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 951 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[5], [7], [71], [29], [17], [11], [5], [5], [19], [13], [7], [59], [11], [19], [47], [41], [29], [23], [43], [41], [97], [5], [313], [53], [7]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 976 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `1 ≤ n ≤ 1000` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 1000) : ∃ x, good n x = true := by
  by_cases c0 : n < 26
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 51
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 76
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 101
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 126
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 151
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 176
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 201
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 226
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 251
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 276
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 301
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 326
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 351
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 376
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 401
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 426
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 451
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 476
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 501
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 526
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 551
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 576
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 601
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 626
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 651
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 676
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 701
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 726
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 751
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 776
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 801
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 826
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 851
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 876
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 901
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 926
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 951
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 976
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a240233Tab

open OMA.Aoeis_a240233Tab in
theorem OMA.solution : OMA.R_oeis_a240233_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
