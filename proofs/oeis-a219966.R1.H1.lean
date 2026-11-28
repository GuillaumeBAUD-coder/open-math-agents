import OMAReductions.R_oeis_a219966_R1
import Mathlib

-- Step oeis-a219966.R1.H1: hypothesis H1 of reduction oeis-a219966.R1
-- Credit: @prathameshnium. Finite check for 12 ≤ n ≤ 1011.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 647.

/-! Step oeis-a219966.R1.H1. -/

namespace OMA.Aoeis_a219966Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `27` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 27 2

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
  have hnd := noDiv_sound p 27 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (p + q + (n % 2) * q = n) && (decide (2 * q ≤ n) && (isPrimeB (p) && (isPrimeB (q) && isPrimeB (q + 6)))))
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
    ∃ p q : ℕ, p + q + (n % 2) * q = n ∧ 2 * q ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (q + 6) := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, q, a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 12, …, 1011`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[7, 5], [3, 5], [7, 7], [5, 5], [11, 5], [3, 7], [11, 7], [5, 7], [13, 7], [7, 7], [11, 11], [13, 5], [13, 11], [3, 11], [13, 13], [5, 11], [17, 11], [3, 13], [17, 13], [5, 13], [19, 13], [7, 13], [17, 17], [13, 11], [19, 17]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 12 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 17], [31, 7], [5, 17], [23, 17], [7, 17], [29, 13], [17, 13], [31, 13], [11, 17], [23, 23], [13, 17], [31, 17], [3, 23], [37, 13], [5, 23], [29, 23], [7, 23], [31, 23], [29, 13], [43, 13], [11, 23], [41, 17], [13, 23], [37, 23], [47, 7]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 37 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[31, 31], [17, 23], [41, 23], [3, 31], [43, 23], [5, 31], [37, 31], [7, 31], [47, 23], [37, 17], [41, 31], [11, 31], [37, 37], [13, 31], [53, 23], [3, 37], [41, 37], [5, 37], [43, 37], [7, 37], [41, 41], [37, 23], [43, 41], [3, 41], [73, 13]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 62 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[5, 41], [47, 41], [7, 41], [53, 37], [17, 37], [61, 31], [11, 41], [47, 47], [13, 41], [59, 37], [3, 47], [61, 37], [5, 47], [53, 47], [7, 47], [61, 41], [29, 37], [67, 37], [11, 47], [53, 53], [13, 47], [61, 47], [3, 53], [73, 37], [5, 53]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 87 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[59, 53], [7, 53], [61, 53], [41, 37], [79, 37], [11, 53], [71, 47], [13, 53], [67, 53], [47, 37], [61, 61], [17, 53], [71, 53], [3, 61], [73, 53], [5, 61], [67, 61], [7, 61], [83, 47], [37, 47], [71, 61], [11, 61], [67, 67], [13, 61], [83, 53]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 112 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[3, 67], [71, 67], [5, 67], [73, 67], [7, 67], [89, 53], [37, 53], [83, 61], [11, 67], [73, 73], [13, 67], [101, 47], [3, 73], [83, 67], [5, 73], [79, 73], [7, 73], [101, 53], [61, 47], [83, 73], [11, 73], [97, 61], [13, 73], [107, 53], [67, 47]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 137 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[89, 73], [17, 73], [97, 67], [19, 73], [83, 83], [61, 53], [101, 67], [3, 83], [97, 73], [5, 83], [89, 83], [7, 83], [101, 73], [29, 73], [103, 73], [11, 83], [131, 47], [13, 83], [97, 83], [47, 67], [109, 73], [17, 83], [101, 83], [19, 83], [103, 83]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 162 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[41, 73], [127, 61], [23, 83], [107, 83], [97, 47], [109, 83], [47, 73], [97, 97], [29, 83], [113, 83], [3, 97], [101, 97], [5, 97], [103, 97], [7, 97], [101, 101], [37, 83], [103, 101], [3, 101], [103, 103], [5, 101], [107, 101], [3, 103], [107, 103], [5, 103]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 187 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[109, 103], [7, 103], [107, 107], [13, 101], [109, 107], [3, 107], [151, 67], [5, 107], [113, 107], [7, 107], [139, 83], [17, 103], [127, 97], [11, 107], [173, 53], [13, 107], [127, 101], [23, 103], [127, 103], [17, 107], [131, 101], [19, 107], [127, 107], [29, 103], [139, 97]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 212 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[23, 107], [131, 107], [37, 101], [137, 103], [47, 97], [139, 103], [29, 107], [137, 107], [31, 107], [139, 107], [41, 103], [151, 97], [43, 103], [149, 101], [37, 107], [149, 103], [47, 103], [151, 103], [41, 107], [149, 107], [43, 107], [151, 107], [53, 103], [157, 103], [47, 107]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 237 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[131, 131], [61, 101], [157, 107], [3, 131], [163, 103], [5, 131], [137, 131], [7, 131], [139, 131], [137, 67], [199, 73], [11, 131], [167, 107], [13, 131], [173, 103], [71, 103], [181, 97], [17, 131], [149, 131], [19, 131], [151, 131], [89, 97], [181, 103], [23, 131], [179, 107]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 262 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[73, 107], [157, 131], [83, 103], [193, 97], [29, 131], [191, 101], [31, 131], [163, 131], [89, 103], [193, 103], [83, 107], [167, 131], [37, 131], [193, 107], [107, 97], [151, 151], [41, 131], [173, 131], [3, 151], [199, 107], [5, 151], [157, 151], [7, 151], [179, 131], [97, 107]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 287 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[181, 131], [11, 151], [157, 157], [13, 151], [233, 83], [3, 157], [167, 151], [5, 157], [163, 157], [7, 157], [191, 131], [61, 131], [167, 157], [11, 157], [223, 103], [13, 157], [197, 131], [67, 131], [173, 157], [17, 157], [181, 151], [19, 157], [167, 167], [73, 131], [179, 157]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 312 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3, 167], [181, 157], [5, 167], [173, 167], [7, 167], [191, 151], [29, 157], [193, 151], [11, 167], [173, 173], [13, 167], [181, 167], [3, 173], [193, 157], [5, 173], [179, 173], [7, 173], [181, 173], [41, 157], [199, 157], [11, 173], [191, 167], [13, 173], [193, 167], [47, 157]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 337 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[211, 151], [17, 173], [191, 173], [19, 173], [193, 173], [53, 157], [211, 157], [23, 173], [197, 173], [37, 167], [199, 173], [59, 157], [223, 151], [29, 173], [269, 107], [31, 173], [211, 167], [173, 103], [223, 157], [47, 167], [191, 191], [37, 173], [193, 191], [3, 191], [193, 193]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 362 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[5, 191], [197, 191], [3, 193], [197, 193], [5, 193], [199, 193], [7, 193], [227, 167], [13, 191], [223, 173], [11, 193], [241, 157], [13, 193], [227, 173], [19, 191], [211, 191], [17, 193], [211, 193], [19, 193], [233, 173], [61, 173], [241, 167], [23, 193], [307, 103], [29, 191]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 387 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[239, 173], [31, 191], [223, 191], [29, 193], [223, 193], [31, 193], [227, 191], [37, 191], [227, 193], [107, 157], [229, 193], [37, 193], [233, 191], [43, 191], [233, 193], [41, 193], [271, 157], [43, 193], [239, 191], [97, 167], [239, 193], [47, 193], [241, 193], [53, 191], [263, 173]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 412 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[103, 167], [271, 167], [53, 193], [283, 157], [59, 191], [251, 191], [61, 191], [251, 193], [59, 193], [223, 223], [61, 193], [257, 191], [3, 223], [227, 223], [5, 223], [229, 223], [7, 223], [227, 227], [73, 191], [229, 227], [3, 227], [307, 151], [5, 227], [233, 227], [7, 227]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 437 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[239, 223], [17, 223], [241, 223], [11, 227], [233, 233], [13, 227], [241, 227], [3, 233], [277, 193], [5, 233], [239, 233], [7, 233], [241, 233], [29, 223], [283, 193], [11, 233], [251, 227], [13, 233], [257, 223], [167, 157], [331, 151], [17, 233], [251, 233], [19, 233], [263, 223]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 462 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[41, 223], [331, 157], [23, 233], [257, 233], [37, 227], [269, 223], [47, 223], [271, 223], [29, 233], [263, 233], [31, 233], [271, 227], [53, 223], [277, 223], [47, 227], [251, 251], [37, 233], [271, 233], [3, 251], [283, 223], [5, 251], [257, 251], [7, 251], [277, 233], [197, 157]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 487 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[409, 103], [11, 251], [257, 257], [13, 251], [283, 233], [3, 257], [367, 151], [5, 257], [263, 257], [7, 257], [271, 251], [137, 193], [331, 193], [11, 257], [263, 263], [13, 257], [271, 257], [3, 263], [307, 223], [5, 263], [269, 263], [7, 263], [271, 263], [89, 223], [313, 223]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 512 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[11, 263], [281, 257], [13, 263], [277, 263], [227, 157], [271, 271], [17, 263], [281, 263], [3, 271], [283, 263], [5, 271], [277, 271], [7, 271], [293, 257], [37, 257], [281, 271], [11, 271], [277, 277], [13, 271], [293, 263], [3, 277], [281, 277], [5, 277], [283, 277], [7, 277]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 537 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[311, 251], [37, 263], [293, 271], [11, 277], [373, 193], [13, 277], [311, 257], [43, 263], [293, 277], [17, 277], [349, 223], [19, 277], [311, 263], [61, 257], [313, 263], [23, 277], [307, 271], [37, 271], [317, 263], [67, 257], [311, 271], [29, 277], [307, 277], [31, 277], [353, 233]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 562 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[61, 263], [311, 277], [47, 271], [313, 277], [37, 277], [359, 233], [67, 263], [317, 277], [41, 277], [373, 223], [43, 277], [347, 251], [73, 263], [337, 263], [47, 277], [331, 271], [61, 271], [347, 257], [79, 263], [349, 257], [53, 277], [331, 277], [67, 271], [347, 263], [97, 257]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 587 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[349, 263], [59, 277], [307, 307], [61, 277], [353, 263], [3, 307], [311, 307], [5, 307], [313, 307], [7, 307], [311, 311], [97, 263], [313, 311], [3, 311], [349, 277], [5, 311], [317, 311], [7, 311], [353, 277], [17, 307], [409, 223], [11, 311], [383, 251], [13, 311], [359, 277]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 612 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[23, 307], [331, 307], [17, 311], [383, 257], [19, 311], [331, 311], [29, 307], [337, 307], [23, 311], [383, 263], [181, 233], [337, 311], [107, 271], [373, 277], [29, 311], [389, 263], [31, 311], [347, 307], [41, 307], [349, 307], [43, 307], [347, 311], [37, 311], [349, 311], [47, 307]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 637 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[331, 331], [41, 311], [353, 311], [3, 331], [359, 307], [5, 331], [337, 331], [7, 331], [359, 311], [157, 257], [401, 271], [11, 331], [367, 307], [13, 331], [419, 257], [151, 263], [347, 331], [17, 331], [349, 331], [19, 331], [419, 263], [61, 311], [353, 331], [23, 331], [379, 307]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 662 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[73, 307], [431, 257], [67, 311], [359, 331], [29, 331], [421, 271], [31, 331], [347, 347], [73, 311], [349, 347], [3, 347], [367, 331], [5, 347], [353, 347], [7, 347], [431, 271], [41, 331], [373, 331], [11, 347], [353, 353], [13, 347], [397, 311], [3, 353], [379, 331], [5, 353]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 687 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[359, 353], [7, 353], [367, 347], [53, 331], [409, 307], [11, 353], [461, 257], [13, 353], [367, 353], [59, 331], [499, 223], [17, 353], [461, 263], [19, 353], [373, 353], [113, 307], [397, 331], [23, 353], [383, 347], [37, 347], [379, 353], [71, 331], [367, 367], [29, 353], [383, 353]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 712 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[3, 367], [431, 307], [5, 367], [373, 367], [7, 367], [389, 353], [37, 353], [397, 347], [11, 367], [373, 373], [13, 367], [401, 347], [3, 373], [383, 367], [5, 373], [379, 373], [7, 373], [401, 353], [61, 347], [383, 373], [11, 373], [487, 271], [13, 373], [449, 311], [67, 347]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 737 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[389, 373], [17, 373], [397, 367], [19, 373], [383, 383], [61, 353], [401, 367], [3, 383], [397, 373], [5, 383], [389, 383], [7, 383], [401, 373], [29, 373], [409, 367], [11, 383], [431, 347], [13, 383], [397, 383], [47, 367], [409, 373], [17, 383], [401, 383], [19, 383], [419, 367]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 762 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[41, 373], [421, 367], [23, 383], [443, 347], [97, 347], [409, 383], [47, 373], [421, 373], [29, 383], [443, 353], [31, 383], [431, 367], [53, 373], [433, 367], [67, 367], [419, 383], [37, 383], [421, 383], [59, 373], [433, 373], [41, 383], [461, 347], [43, 383], [443, 367], [149, 331]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 787 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[439, 373], [47, 383], [431, 383], [109, 353], [433, 383], [71, 373], [487, 331], [53, 383], [467, 353], [127, 347], [439, 383], [89, 367], [457, 367], [59, 383], [443, 383], [61, 383], [461, 367], [83, 373], [457, 373], [97, 367], [449, 383], [67, 383], [461, 373], [89, 373], [463, 373]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 812 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[71, 383], [491, 347], [73, 383], [457, 383], [107, 367], [571, 271], [97, 373], [461, 383], [79, 383], [463, 383], [101, 373], [541, 307], [83, 383], [467, 383], [157, 347], [479, 373], [107, 373], [487, 367], [89, 383], [503, 353], [151, 353], [491, 367], [113, 373], [487, 373], [127, 367]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 837 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[479, 383], [97, 383], [491, 373], [131, 367], [433, 433], [101, 383], [521, 347], [3, 433], [487, 383], [5, 433], [439, 433], [7, 433], [491, 383], [109, 383], [443, 433], [11, 433], [547, 331], [13, 433], [569, 311], [367, 257], [449, 433], [17, 433], [577, 307], [19, 433], [443, 443]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 862 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[181, 353], [521, 367], [3, 443], [457, 433], [5, 443], [449, 443], [7, 443], [461, 433], [29, 433], [463, 433], [11, 443], [587, 311], [13, 443], [457, 443], [167, 367], [571, 331], [17, 443], [461, 443], [19, 443], [463, 443], [41, 433], [541, 367], [23, 443], [467, 443], [397, 257]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 887 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[479, 433], [47, 433], [457, 457], [29, 443], [563, 353], [3, 457], [461, 457], [5, 457], [463, 457], [7, 457], [461, 461], [37, 443], [463, 461], [3, 461], [619, 307], [5, 461], [467, 461], [7, 461], [487, 443], [17, 457], [499, 433], [11, 461], [491, 443], [13, 461], [479, 457]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 912 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[23, 457], [571, 367], [17, 461], [479, 461], [19, 461], [499, 443], [29, 457], [487, 457], [23, 461], [503, 443], [61, 443], [487, 461], [83, 433], [577, 373], [29, 461], [491, 461], [31, 461], [521, 433], [41, 457], [499, 457], [43, 457], [647, 311], [37, 461], [499, 461], [47, 457]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 937 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[631, 331], [41, 461], [503, 461], [43, 461], [509, 457], [53, 457], [601, 367], [47, 461], [509, 461], [277, 347], [599, 373], [59, 457], [541, 433], [53, 461], [593, 383], [211, 383], [521, 457], [113, 433], [523, 457], [59, 461], [521, 461], [61, 461], [523, 461], [71, 457], [613, 373]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 962 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[73, 457], [641, 347], [67, 461], [547, 443], [257, 367], [619, 373], [71, 461], [641, 353], [73, 461], [563, 433], [83, 457], [541, 457], [113, 443], [557, 443], [79, 461], [541, 461], [89, 457], [547, 457], [83, 461], [503, 503], [241, 383], [547, 461], [3, 503], [577, 433], [5, 503]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 987 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `12 ≤ n ≤ 1011` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 12 ≤ n) (h2 : n ≤ 1011) : ∃ x, good n x = true := by
  by_cases c0 : n < 37
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 62
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 87
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 112
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 137
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 162
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 187
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 212
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 237
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 262
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 287
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 312
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 337
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 362
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 387
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 412
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 437
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 462
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 487
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 512
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 537
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 562
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 587
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 612
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 637
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 662
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 687
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 712
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 737
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 762
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 787
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 812
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 837
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 862
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 887
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 912
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 937
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 962
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 987
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a219966Tab

open OMA.Aoeis_a219966Tab in
theorem OMA.solution : OMA.R_oeis_a219966_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
