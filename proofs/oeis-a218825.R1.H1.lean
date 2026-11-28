import OMAReductions.R_oeis_a218825_R1
import Mathlib

-- Step oeis-a218825.R1.H1: hypothesis H1 of reduction oeis-a218825.R1
-- Credit: @prathameshnium. Finite check for 9 ≤ n ≤ 349.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 6814429.

/-! Step oeis-a218825.R1.H1. -/

namespace OMA.Aoeis_a218825Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `2612` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 2612 2

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
  have hnd := noDiv_sound p 2612 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (p + 2 * q + 1 = 2 * n) && (isPrimeB (p) && (isPrimeB (q) && isPrimeB (p ^ 2 + 60 * q ^ 2))))
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
    ∃ p q : ℕ, p + 2 * q + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (p ^ 2 + 60 * q ^ 2) := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, q, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 9, …, 349`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[7, 5], [13, 3], [11, 5], [13, 5], [11, 7], [13, 7], [7, 11], [17, 7], [19, 7], [29, 3], [23, 7], [17, 11], [7, 17], [17, 13], [19, 13], [13, 17], [43, 3], [29, 11], [31, 11], [41, 7], [43, 7], [37, 11], [23, 19], [17, 23], [31, 17]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 9 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[29, 19], [7, 31], [67, 2], [11, 31], [13, 31], [19, 29], [73, 3], [7, 37], [73, 5], [11, 37], [53, 17], [31, 29], [53, 19], [7, 43], [37, 29], [83, 7], [13, 43], [7, 47], [17, 43], [11, 47], [13, 47], [71, 19], [29, 41], [67, 23], [29, 43]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 34 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[23, 47], [37, 41], [47, 37], [61, 31], [19, 53], [41, 43], [23, 53], [13, 59], [11, 61], [13, 61], [19, 59], [17, 61], [7, 67], [37, 53], [11, 67], [29, 59], [31, 59], [29, 61], [11, 71], [13, 71], [71, 43], [37, 61], [43, 59], [137, 13], [19, 73]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 59 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[73, 47], [23, 73], [37, 67], [31, 71], [41, 67], [11, 83], [97, 41], [23, 79], [17, 83], [67, 59], [173, 7], [11, 89], [13, 89], [47, 73], [17, 89], [19, 89], [53, 73], [23, 89], [37, 83], [83, 61], [13, 97], [7, 101], [149, 31], [11, 101], [13, 101]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 84 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[23, 97], [17, 101], [7, 107], [17, 103], [7, 109], [13, 107], [11, 109], [37, 97], [127, 53], [17, 109], [11, 113], [97, 71], [23, 109], [37, 103], [19, 113], [101, 73], [107, 71], [37, 107], [131, 61], [41, 107], [31, 113], [113, 73], [103, 79], [37, 113], [47, 109]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 109 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[61, 103], [103, 83], [137, 67], [19, 127], [61, 107], [71, 103], [61, 109], [7, 137], [89, 97], [151, 67], [73, 107], [11, 139], [13, 139], [19, 137], [41, 127], [23, 137], [241, 29], [23, 139], [109, 97], [31, 137], [53, 127], [11, 149], [97, 107], [11, 151], [13, 151]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 134 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[19, 149], [17, 151], [23, 149], [61, 131], [107, 109], [13, 157], [103, 113], [17, 157], [19, 157], [61, 137], [11, 163], [37, 151], [7, 167], [29, 157], [11, 167], [13, 167], [23, 163], [17, 167], [151, 101], [41, 157], [31, 163], [61, 149], [59, 151], [29, 167], [31, 167]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 159 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[53, 157], [7, 181], [73, 149], [11, 181], [17, 179], [19, 179], [233, 73], [67, 157], [37, 173], [23, 181], [61, 163], [7, 191], [89, 151], [11, 191], [13, 191], [71, 163], [41, 179], [19, 191], [17, 193], [7, 199], [109, 149], [23, 193], [13, 199], [139, 137], [197, 109]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 184 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[19, 199], [157, 131], [227, 97], [41, 191], [67, 179], [149, 139], [7, 211], [73, 179], [311, 61], [37, 199], [43, 197], [41, 199], [59, 191], [109, 167], [59, 193], [61, 193], [223, 113], [53, 199], [107, 173], [157, 149], [179, 139], [37, 211], [283, 89], [257, 103], [19, 223]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 209 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[73, 197], [23, 223], [89, 191], [19, 227], [17, 229], [31, 223], [13, 233], [347, 67], [29, 227], [7, 239], [101, 193], [23, 233], [97, 197], [47, 223], [41, 227], [31, 233], [113, 193], [23, 239], [109, 197], [83, 211], [109, 199], [151, 179], [29, 241], [11, 251], [157, 179]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 234 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[191, 163], [53, 233], [43, 239], [137, 193], [23, 251], [181, 173], [47, 241], [73, 229], [19, 257], [89, 223], [23, 257], [13, 263], [179, 181], [97, 223], [43, 251], [149, 199], [7, 271], [97, 227], [131, 211], [29, 263], [43, 257], [17, 271], [7, 277], [229, 167], [11, 277]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 259 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[41, 263], [43, 263], [449, 61], [19, 277], [37, 269], [359, 109], [17, 281], [19, 281], [17, 283], [31, 277], [193, 197], [107, 241], [89, 251], [67, 263], [29, 283], [11, 293], [61, 269], [59, 271], [37, 283], [43, 281], [41, 283], [23, 293], [73, 269], [71, 271], [29, 293]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 284 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[271, 173], [137, 241], [107, 257], [457, 83], [59, 283], [13, 307], [7, 311], [173, 229], [11, 311], [109, 263], [23, 307], [17, 311], [7, 317], [101, 271], [59, 293], [613, 17], [167, 241], [109, 271], [31, 311], [29, 313], [43, 307], [157, 251], [359, 151], [41, 311], [211, 227]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 309 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[41, 313], [7, 331], [157, 257], [47, 313], [53, 311], [211, 233], [17, 331], [7, 337], [61, 311], [11, 337], [13, 337], [103, 293], [17, 337], [59, 317], [157, 269], [239, 229]]
theorem len13 : w13.length = 16 := rfl
theorem ok13 : checkList 334 w13 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `9 ≤ n ≤ 349` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 9 ≤ n) (h2 : n ≤ 349) : ∃ x, good n x = true := by
  by_cases c0 : n < 34
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 59
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 84
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 109
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 134
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 159
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 184
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 209
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 234
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 259
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 284
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 309
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 334
  · exact chunk ok12 len12 (by omega) (by omega)
  exact chunk ok13 len13 (by omega) (by omega)

end OMA.Aoeis_a218825Tab

open OMA.Aoeis_a218825Tab in
theorem OMA.solution : OMA.R_oeis_a218825_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
