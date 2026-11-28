import OMAReductions.R_OeisA237720_conjecture_3_R1
import Mathlib

-- Step OeisA237720.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA237720.conjecture_3.R1
-- Credit: @prathameshnium. Finite check for 3 ≤ n ≤ 1002.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 269.

/-! Step OeisA237720.conjecture_3.R1.H1. -/

namespace OMA.AOeisA237720_conjecture_3Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `18` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 18 2

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
  have hnd := noDiv_sound p 18 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, s] => (isPrimeB (p) && (decide (p < n) && (decide (s * s ≤ n + p ∧ n + p < (s + 1) * (s + 1)) && isPrimeB (s))))
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
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  unfold core at h
  split at h
  next p s =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, a1, (by rw [← Nat.eq_sqrt.mpr a2]; exact isPrimeB_sound _ a3)⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 3, …, 1002`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2], [2, 2], [2, 2], [2, 2], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [11, 5], [11, 5], [11, 5], [11, 5], [7, 5], [7, 5], [5, 5], [5, 5], [3, 5], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 3 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[2, 5], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5], [17, 7], [17, 7], [13, 7], [13, 7], [11, 7], [11, 7], [11, 7], [11, 7], [7, 7], [7, 7], [5, 7], [5, 7], [3, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 28 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [59, 11], [59, 11], [59, 11], [59, 11], [59, 11], [59, 11], [53, 11], [53, 11], [53, 11], [53, 11], [53, 11], [53, 11], [47, 11], [47, 11], [47, 11], [47, 11]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 53 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[43, 11], [43, 11], [41, 11], [41, 11], [41, 11], [41, 11], [37, 11], [37, 11], [37, 11], [37, 11], [37, 11], [37, 11], [31, 11], [31, 11], [29, 11], [29, 11], [29, 11], [29, 11], [29, 11], [29, 11], [23, 11], [23, 11], [23, 11], [23, 11], [19, 11]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 78 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[19, 11], [17, 11], [17, 11], [17, 11], [17, 11], [13, 11], [13, 11], [11, 11], [11, 11], [11, 11], [11, 11], [7, 11], [7, 11], [5, 11], [5, 11], [3, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 103 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [2, 11], [29, 13], [29, 13], [29, 13], [29, 13], [23, 13], [23, 13], [23, 13], [23, 13], [19, 13], [19, 13], [17, 13]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 128 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[17, 13], [17, 13], [17, 13], [13, 13], [13, 13], [11, 13], [11, 13], [11, 13], [11, 13], [7, 13], [7, 13], [5, 13], [5, 13], [3, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 153 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [2, 13], [97, 17], [97, 17], [97, 17], [97, 17], [97, 17], [97, 17], [89, 17], [89, 17], [89, 17]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 178 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[89, 17], [89, 17], [89, 17], [83, 17], [83, 17], [83, 17], [83, 17], [79, 17], [79, 17], [79, 17], [79, 17], [79, 17], [79, 17], [73, 17], [73, 17], [71, 17], [71, 17], [71, 17], [71, 17], [67, 17], [67, 17], [67, 17], [67, 17], [67, 17], [67, 17]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 203 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[61, 17], [61, 17], [59, 17], [59, 17], [59, 17], [59, 17], [59, 17], [59, 17], [53, 17], [53, 17], [53, 17], [53, 17], [53, 17], [53, 17], [47, 17], [47, 17], [47, 17], [47, 17], [43, 17], [43, 17], [41, 17], [41, 17], [41, 17], [41, 17], [37, 17]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 228 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[37, 17], [37, 17], [37, 17], [37, 17], [37, 17], [31, 17], [31, 17], [29, 17], [29, 17], [29, 17], [29, 17], [29, 17], [29, 17], [23, 17], [23, 17], [23, 17], [23, 17], [19, 17], [19, 17], [17, 17], [17, 17], [17, 17], [17, 17], [13, 17], [13, 17]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 253 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[11, 17], [11, 17], [11, 17], [11, 17], [7, 17], [7, 17], [5, 17], [5, 17], [3, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 278 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [2, 17], [41, 19], [41, 19], [37, 19], [37, 19], [37, 19], [37, 19]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 303 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[37, 19], [37, 19], [31, 19], [31, 19], [29, 19], [29, 19], [29, 19], [29, 19], [29, 19], [29, 19], [23, 19], [23, 19], [23, 19], [23, 19], [19, 19], [19, 19], [17, 19], [17, 19], [17, 19], [17, 19], [13, 19], [13, 19], [11, 19], [11, 19], [11, 19]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 328 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[11, 19], [7, 19], [7, 19], [5, 19], [5, 19], [3, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 353 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [2, 19], [131, 23], [131, 23], [131, 23], [131, 23], [127, 23]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 378 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [127, 23], [113, 23], [113, 23], [113, 23], [113, 23], [109, 23], [109, 23], [107, 23], [107, 23], [107, 23], [107, 23], [103, 23], [103, 23]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 403 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[101, 23], [101, 23], [101, 23], [101, 23], [97, 23], [97, 23], [97, 23], [97, 23], [97, 23], [97, 23], [97, 23], [97, 23], [89, 23], [89, 23], [89, 23], [89, 23], [89, 23], [89, 23], [83, 23], [83, 23], [83, 23], [83, 23], [79, 23], [79, 23], [79, 23]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 428 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[79, 23], [79, 23], [79, 23], [73, 23], [73, 23], [71, 23], [71, 23], [71, 23], [71, 23], [67, 23], [67, 23], [67, 23], [67, 23], [67, 23], [67, 23], [61, 23], [61, 23], [59, 23], [59, 23], [59, 23], [59, 23], [59, 23], [59, 23], [53, 23], [53, 23]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 453 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[53, 23], [53, 23], [53, 23], [53, 23], [47, 23], [47, 23], [47, 23], [47, 23], [43, 23], [43, 23], [41, 23], [41, 23], [41, 23], [41, 23], [37, 23], [37, 23], [37, 23], [37, 23], [37, 23], [37, 23], [31, 23], [31, 23], [29, 23], [29, 23], [29, 23]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 478 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[29, 23], [29, 23], [29, 23], [23, 23], [23, 23], [23, 23], [23, 23], [19, 23], [19, 23], [17, 23], [17, 23], [17, 23], [17, 23], [13, 23], [13, 23], [11, 23], [11, 23], [11, 23], [11, 23], [7, 23], [7, 23], [5, 23], [5, 23], [3, 23], [2, 23]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 503 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 528 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [2, 23], [269, 29], [269, 29], [269, 29], [269, 29]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 553 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[263, 29], [263, 29], [263, 29], [263, 29], [263, 29], [263, 29], [257, 29], [257, 29], [257, 29], [257, 29], [257, 29], [257, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [251, 29], [241, 29], [241, 29], [239, 29]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 578 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[239, 29], [239, 29], [239, 29], [239, 29], [239, 29], [233, 29], [233, 29], [233, 29], [233, 29], [229, 29], [229, 29], [227, 29], [227, 29], [227, 29], [227, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29], [223, 29]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 603 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[223, 29], [223, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [211, 29], [199, 29], [199, 29], [197, 29], [197, 29], [197, 29], [197, 29], [193, 29], [193, 29], [191, 29], [191, 29], [191, 29]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 628 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[191, 29], [191, 29], [191, 29], [191, 29], [191, 29], [191, 29], [191, 29], [181, 29], [181, 29], [179, 29], [179, 29], [179, 29], [179, 29], [179, 29], [179, 29], [173, 29], [173, 29], [173, 29], [173, 29], [173, 29], [173, 29], [167, 29], [167, 29], [167, 29], [167, 29]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 653 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[163, 29], [163, 29], [163, 29], [163, 29], [163, 29], [163, 29], [157, 29], [157, 29], [157, 29], [157, 29], [157, 29], [157, 29], [151, 29], [151, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [149, 29], [139, 29]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 678 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[139, 29], [137, 29], [137, 29], [137, 29], [137, 29], [137, 29], [137, 29], [131, 29], [131, 29], [131, 29], [131, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29], [127, 29]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 703 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[113, 29], [113, 29], [113, 29], [113, 29], [109, 29], [109, 29], [107, 29], [107, 29], [107, 29], [107, 29], [103, 29], [103, 29], [101, 29], [101, 29], [101, 29], [101, 29], [97, 29], [97, 29], [97, 29], [97, 29], [97, 29], [97, 29], [97, 29], [97, 29], [89, 29]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 728 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[89, 29], [89, 29], [89, 29], [89, 29], [89, 29], [83, 29], [83, 29], [83, 29], [83, 29], [79, 29], [79, 29], [79, 29], [79, 29], [79, 29], [79, 29], [73, 29], [73, 29], [71, 29], [71, 29], [71, 29], [71, 29], [67, 29], [67, 29], [67, 29], [67, 29]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 753 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[67, 29], [67, 29], [61, 29], [61, 29], [59, 29], [59, 29], [59, 29], [59, 29], [59, 29], [59, 29], [53, 29], [53, 29], [53, 29], [53, 29], [53, 29], [53, 29], [47, 29], [47, 29], [47, 29], [47, 29], [43, 29], [43, 29], [41, 29], [41, 29], [41, 29]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 778 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[41, 29], [37, 29], [37, 29], [37, 29], [37, 29], [37, 29], [37, 29], [31, 29], [31, 29], [29, 29], [29, 29], [29, 29], [29, 29], [29, 29], [29, 29], [23, 29], [23, 29], [23, 29], [23, 29], [19, 29], [19, 29], [17, 29], [17, 29], [17, 29], [17, 29]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 803 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[13, 29], [13, 29], [11, 29], [11, 29], [11, 29], [11, 29], [7, 29], [7, 29], [5, 29], [5, 29], [3, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 828 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 853 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [2, 29], [67, 31], [67, 31], [61, 31], [61, 31], [59, 31]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 878 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[59, 31], [59, 31], [59, 31], [59, 31], [59, 31], [53, 31], [53, 31], [53, 31], [53, 31], [53, 31], [53, 31], [47, 31], [47, 31], [47, 31], [47, 31], [43, 31], [43, 31], [41, 31], [41, 31], [41, 31], [41, 31], [37, 31], [37, 31], [37, 31], [37, 31]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 903 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[37, 31], [37, 31], [31, 31], [31, 31], [29, 31], [29, 31], [29, 31], [29, 31], [29, 31], [29, 31], [23, 31], [23, 31], [23, 31], [23, 31], [19, 31], [19, 31], [17, 31], [17, 31], [17, 31], [17, 31], [13, 31], [13, 31], [11, 31], [11, 31], [11, 31]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 928 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[11, 31], [7, 31], [7, 31], [5, 31], [5, 31], [3, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 953 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31], [2, 31]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 978 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `3 ≤ n ≤ 1002` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 1002) : ∃ x, good n x = true := by
  by_cases c0 : n < 28
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 53
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 78
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 103
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 128
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 153
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 178
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 203
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 228
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 253
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 278
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 303
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 328
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 353
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 378
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 403
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 428
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 453
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 478
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 503
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 528
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 553
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 578
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 603
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 628
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 653
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 678
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 703
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 728
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 753
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 778
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 803
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 828
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 853
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 878
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 903
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 928
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 953
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 978
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.AOeisA237720_conjecture_3Tab

open OMA.AOeisA237720_conjecture_3Tab in
theorem OMA.solution : OMA.R_OeisA237720_conjecture_3_R1.H1 := by
  intro n hn hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
