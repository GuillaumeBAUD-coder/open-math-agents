import OMAReductions.R_oeis_a059998_R1
import Mathlib

-- Step oeis-a059998.R1.H1: hypothesis H1 of reduction oeis-a059998.R1
-- Credit: @prathameshnium. Finite check for 6 ≤ n ≤ 1005.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 997.

/-! Step oeis-a059998.R1.H1. -/

namespace OMA.Aoeis_a059998Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `33` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 33 2

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
  have hnd := noDiv_sound p 33 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q, r] => (isPrimeB (p) && (isPrimeB (q) && (isPrimeB (r) && decide (p + q + r = n))))
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
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n := by
  unfold core at h
  split at h
  next p q r =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, q, r, isPrimeB_sound _ a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2, a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 6, …, 1005`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2, 2], [2, 2, 3], [2, 3, 3], [2, 2, 5], [2, 3, 5], [2, 2, 7], [2, 3, 7], [3, 3, 7], [2, 5, 7], [2, 2, 11], [2, 3, 11], [2, 2, 13], [2, 3, 13], [3, 3, 13], [2, 5, 13], [2, 2, 17], [2, 3, 17], [2, 2, 19], [2, 3, 19], [3, 3, 19], [2, 5, 19], [2, 2, 23], [2, 3, 23], [3, 3, 23], [2, 5, 23]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 6 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 5, 23], [2, 7, 23], [2, 2, 29], [2, 3, 29], [2, 2, 31], [2, 3, 31], [3, 3, 31], [2, 5, 31], [3, 5, 31], [2, 7, 31], [2, 2, 37], [2, 3, 37], [3, 3, 37], [2, 5, 37], [2, 2, 41], [2, 3, 41], [2, 2, 43], [2, 3, 43], [3, 3, 43], [2, 5, 43], [2, 2, 47], [2, 3, 47], [3, 3, 47], [2, 5, 47], [3, 5, 47]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 31 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[2, 7, 47], [2, 2, 53], [2, 3, 53], [3, 3, 53], [2, 5, 53], [3, 5, 53], [2, 7, 53], [2, 2, 59], [2, 3, 59], [2, 2, 61], [2, 3, 61], [3, 3, 61], [2, 5, 61], [3, 5, 61], [2, 7, 61], [2, 2, 67], [2, 3, 67], [3, 3, 67], [2, 5, 67], [2, 2, 71], [2, 3, 71], [2, 2, 73], [2, 3, 73], [3, 3, 73], [2, 5, 73]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 56 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 5, 73], [2, 7, 73], [2, 2, 79], [2, 3, 79], [3, 3, 79], [2, 5, 79], [2, 2, 83], [2, 3, 83], [3, 3, 83], [2, 5, 83], [3, 5, 83], [2, 7, 83], [2, 2, 89], [2, 3, 89], [3, 3, 89], [2, 5, 89], [3, 5, 89], [2, 7, 89], [3, 7, 89], [2, 19, 79], [2, 2, 97], [2, 3, 97], [3, 3, 97], [2, 5, 97], [2, 2, 101]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 81 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[2, 3, 101], [2, 2, 103], [2, 3, 103], [3, 3, 103], [2, 5, 103], [2, 2, 107], [2, 3, 107], [2, 2, 109], [2, 3, 109], [3, 3, 109], [2, 5, 109], [2, 2, 113], [2, 3, 113], [3, 3, 113], [2, 5, 113], [3, 5, 113], [2, 7, 113], [3, 7, 113], [2, 13, 109], [3, 13, 109], [2, 11, 113], [3, 11, 113], [2, 13, 113], [3, 13, 113], [2, 19, 109]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 106 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[2, 2, 127], [2, 3, 127], [3, 3, 127], [2, 5, 127], [2, 2, 131], [2, 3, 131], [3, 3, 131], [2, 5, 131], [3, 5, 131], [2, 7, 131], [2, 2, 137], [2, 3, 137], [2, 2, 139], [2, 3, 139], [3, 3, 139], [2, 5, 139], [3, 5, 139], [2, 7, 139], [3, 7, 139], [2, 11, 137], [3, 11, 137], [2, 11, 139], [2, 2, 149], [2, 3, 149], [2, 2, 151]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 131 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[2, 3, 151], [3, 3, 151], [2, 5, 151], [3, 5, 151], [2, 7, 151], [2, 2, 157], [2, 3, 157], [3, 3, 157], [2, 5, 157], [3, 5, 157], [2, 7, 157], [2, 2, 163], [2, 3, 163], [3, 3, 163], [2, 5, 163], [2, 2, 167], [2, 3, 167], [3, 3, 167], [2, 5, 167], [3, 5, 167], [2, 7, 167], [2, 2, 173], [2, 3, 173], [3, 3, 173], [2, 5, 173]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 156 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[3, 5, 173], [2, 7, 173], [2, 2, 179], [2, 3, 179], [2, 2, 181], [2, 3, 181], [3, 3, 181], [2, 5, 181], [3, 5, 181], [2, 7, 181], [3, 7, 181], [2, 11, 179], [3, 11, 179], [2, 11, 181], [2, 2, 191], [2, 3, 191], [2, 2, 193], [2, 3, 193], [3, 3, 193], [2, 5, 193], [2, 2, 197], [2, 3, 197], [2, 2, 199], [2, 3, 199], [3, 3, 199]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 181 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[2, 5, 199], [3, 5, 199], [2, 7, 199], [3, 7, 199], [2, 11, 197], [3, 11, 197], [2, 11, 199], [3, 11, 199], [2, 13, 199], [2, 2, 211], [2, 3, 211], [3, 3, 211], [2, 5, 211], [3, 5, 211], [2, 7, 211], [3, 7, 211], [2, 23, 197], [3, 23, 197], [2, 11, 211], [3, 11, 211], [2, 13, 211], [2, 2, 223], [2, 3, 223], [3, 3, 223], [2, 5, 223]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 206 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[2, 2, 227], [2, 3, 227], [2, 2, 229], [2, 3, 229], [3, 3, 229], [2, 5, 229], [2, 2, 233], [2, 3, 233], [3, 3, 233], [2, 5, 233], [3, 5, 233], [2, 7, 233], [2, 2, 239], [2, 3, 239], [2, 2, 241], [2, 3, 241], [3, 3, 241], [2, 5, 241], [3, 5, 241], [2, 7, 241], [3, 7, 241], [2, 11, 239], [3, 11, 239], [2, 11, 241], [2, 2, 251]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 231 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[2, 3, 251], [3, 3, 251], [2, 5, 251], [3, 5, 251], [2, 7, 251], [2, 2, 257], [2, 3, 257], [3, 3, 257], [2, 5, 257], [3, 5, 257], [2, 7, 257], [2, 2, 263], [2, 3, 263], [3, 3, 263], [2, 5, 263], [3, 5, 263], [2, 7, 263], [2, 2, 269], [2, 3, 269], [2, 2, 271], [2, 3, 271], [3, 3, 271], [2, 5, 271], [3, 5, 271], [2, 7, 271]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 256 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[2, 2, 277], [2, 3, 277], [3, 3, 277], [2, 5, 277], [2, 2, 281], [2, 3, 281], [2, 2, 283], [2, 3, 283], [3, 3, 283], [2, 5, 283], [3, 5, 283], [2, 7, 283], [3, 7, 283], [2, 11, 281], [3, 11, 281], [2, 11, 283], [2, 2, 293], [2, 3, 293], [3, 3, 293], [2, 5, 293], [3, 5, 293], [2, 7, 293], [3, 7, 293], [2, 19, 283], [3, 19, 283]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 281 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[2, 11, 293], [3, 11, 293], [2, 13, 293], [3, 13, 293], [2, 31, 277], [2, 2, 307], [2, 3, 307], [3, 3, 307], [2, 5, 307], [2, 2, 311], [2, 3, 311], [2, 2, 313], [2, 3, 313], [3, 3, 313], [2, 5, 313], [2, 2, 317], [2, 3, 317], [3, 3, 317], [2, 5, 317], [3, 5, 317], [2, 7, 317], [3, 7, 317], [2, 13, 313], [3, 13, 313], [2, 11, 317]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 306 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3, 11, 317], [2, 13, 317], [3, 13, 317], [2, 19, 313], [2, 2, 331], [2, 3, 331], [3, 3, 331], [2, 5, 331], [3, 5, 331], [2, 7, 331], [2, 2, 337], [2, 3, 337], [3, 3, 337], [2, 5, 337], [3, 5, 337], [2, 7, 337], [3, 7, 337], [2, 29, 317], [3, 29, 317], [2, 11, 337], [2, 2, 347], [2, 3, 347], [2, 2, 349], [2, 3, 349], [3, 3, 349]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 331 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[2, 5, 349], [2, 2, 353], [2, 3, 353], [3, 3, 353], [2, 5, 353], [3, 5, 353], [2, 7, 353], [2, 2, 359], [2, 3, 359], [3, 3, 359], [2, 5, 359], [3, 5, 359], [2, 7, 359], [3, 7, 359], [2, 19, 349], [2, 2, 367], [2, 3, 367], [3, 3, 367], [2, 5, 367], [3, 5, 367], [2, 7, 367], [2, 2, 373], [2, 3, 373], [3, 3, 373], [2, 5, 373]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 356 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[3, 5, 373], [2, 7, 373], [2, 2, 379], [2, 3, 379], [3, 3, 379], [2, 5, 379], [2, 2, 383], [2, 3, 383], [3, 3, 383], [2, 5, 383], [3, 5, 383], [2, 7, 383], [2, 2, 389], [2, 3, 389], [3, 3, 389], [2, 5, 389], [3, 5, 389], [2, 7, 389], [3, 7, 389], [2, 19, 379], [2, 2, 397], [2, 3, 397], [3, 3, 397], [2, 5, 397], [2, 2, 401]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 381 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[2, 3, 401], [3, 3, 401], [2, 5, 401], [3, 5, 401], [2, 7, 401], [3, 7, 401], [2, 13, 397], [2, 2, 409], [2, 3, 409], [3, 3, 409], [2, 5, 409], [3, 5, 409], [2, 7, 409], [3, 7, 409], [2, 17, 401], [3, 17, 401], [2, 11, 409], [2, 2, 419], [2, 3, 419], [2, 2, 421], [2, 3, 421], [3, 3, 421], [2, 5, 421], [3, 5, 421], [2, 7, 421]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 406 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[3, 7, 421], [2, 11, 419], [3, 11, 419], [2, 11, 421], [2, 2, 431], [2, 3, 431], [2, 2, 433], [2, 3, 433], [3, 3, 433], [2, 5, 433], [3, 5, 433], [2, 7, 433], [2, 2, 439], [2, 3, 439], [3, 3, 439], [2, 5, 439], [2, 2, 443], [2, 3, 443], [3, 3, 443], [2, 5, 443], [3, 5, 443], [2, 7, 443], [2, 2, 449], [2, 3, 449], [3, 3, 449]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 431 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[2, 5, 449], [3, 5, 449], [2, 7, 449], [3, 7, 449], [2, 19, 439], [2, 2, 457], [2, 3, 457], [3, 3, 457], [2, 5, 457], [2, 2, 461], [2, 3, 461], [2, 2, 463], [2, 3, 463], [3, 3, 463], [2, 5, 463], [2, 2, 467], [2, 3, 467], [3, 3, 467], [2, 5, 467], [3, 5, 467], [2, 7, 467], [3, 7, 467], [2, 13, 463], [3, 13, 463], [2, 11, 467]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 456 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[3, 11, 467], [2, 13, 467], [2, 2, 479], [2, 3, 479], [3, 3, 479], [2, 5, 479], [3, 5, 479], [2, 7, 479], [3, 7, 479], [2, 31, 457], [2, 2, 487], [2, 3, 487], [3, 3, 487], [2, 5, 487], [2, 2, 491], [2, 3, 491], [3, 3, 491], [2, 5, 491], [3, 5, 491], [2, 7, 491], [3, 7, 491], [2, 13, 487], [2, 2, 499], [2, 3, 499], [3, 3, 499]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 481 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[2, 5, 499], [2, 2, 503], [2, 3, 503], [3, 3, 503], [2, 5, 503], [3, 5, 503], [2, 7, 503], [2, 2, 509], [2, 3, 509], [3, 3, 509], [2, 5, 509], [3, 5, 509], [2, 7, 509], [3, 7, 509], [2, 19, 499], [3, 19, 499], [2, 11, 509], [3, 11, 509], [2, 13, 509], [2, 2, 521], [2, 3, 521], [2, 2, 523], [2, 3, 523], [3, 3, 523], [2, 5, 523]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 506 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[3, 5, 523], [2, 7, 523], [3, 7, 523], [2, 11, 521], [3, 11, 521], [2, 11, 523], [3, 11, 523], [2, 13, 523], [3, 13, 523], [2, 17, 521], [3, 17, 521], [2, 17, 523], [3, 17, 523], [2, 19, 523], [2, 2, 541], [2, 3, 541], [3, 3, 541], [2, 5, 541], [3, 5, 541], [2, 7, 541], [2, 2, 547], [2, 3, 547], [3, 3, 547], [2, 5, 547], [3, 5, 547]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 531 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[2, 7, 547], [3, 7, 547], [2, 47, 509], [3, 47, 509], [2, 11, 547], [2, 2, 557], [2, 3, 557], [3, 3, 557], [2, 5, 557], [3, 5, 557], [2, 7, 557], [2, 2, 563], [2, 3, 563], [3, 3, 563], [2, 5, 563], [3, 5, 563], [2, 7, 563], [2, 2, 569], [2, 3, 569], [2, 2, 571], [2, 3, 571], [3, 3, 571], [2, 5, 571], [3, 5, 571], [2, 7, 571]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 556 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[2, 2, 577], [2, 3, 577], [3, 3, 577], [2, 5, 577], [3, 5, 577], [2, 7, 577], [3, 7, 577], [2, 17, 569], [3, 17, 569], [2, 11, 577], [2, 2, 587], [2, 3, 587], [3, 3, 587], [2, 5, 587], [3, 5, 587], [2, 7, 587], [2, 2, 593], [2, 3, 593], [3, 3, 593], [2, 5, 593], [3, 5, 593], [2, 7, 593], [2, 2, 599], [2, 3, 599], [2, 2, 601]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 581 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[2, 3, 601], [3, 3, 601], [2, 5, 601], [3, 5, 601], [2, 7, 601], [2, 2, 607], [2, 3, 607], [3, 3, 607], [2, 5, 607], [3, 5, 607], [2, 7, 607], [2, 2, 613], [2, 3, 613], [3, 3, 613], [2, 5, 613], [2, 2, 617], [2, 3, 617], [2, 2, 619], [2, 3, 619], [3, 3, 619], [2, 5, 619], [3, 5, 619], [2, 7, 619], [3, 7, 619], [2, 11, 617]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 606 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[3, 11, 617], [2, 11, 619], [3, 11, 619], [2, 13, 619], [2, 2, 631], [2, 3, 631], [3, 3, 631], [2, 5, 631], [3, 5, 631], [2, 7, 631], [3, 7, 631], [2, 23, 617], [3, 23, 617], [2, 11, 631], [2, 2, 641], [2, 3, 641], [2, 2, 643], [2, 3, 643], [3, 3, 643], [2, 5, 643], [2, 2, 647], [2, 3, 647], [3, 3, 647], [2, 5, 647], [3, 5, 647]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 631 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[2, 7, 647], [2, 2, 653], [2, 3, 653], [3, 3, 653], [2, 5, 653], [3, 5, 653], [2, 7, 653], [2, 2, 659], [2, 3, 659], [2, 2, 661], [2, 3, 661], [3, 3, 661], [2, 5, 661], [3, 5, 661], [2, 7, 661], [3, 7, 661], [2, 11, 659], [3, 11, 659], [2, 11, 661], [3, 11, 661], [2, 13, 661], [2, 2, 673], [2, 3, 673], [3, 3, 673], [2, 5, 673]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 656 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[2, 2, 677], [2, 3, 677], [3, 3, 677], [2, 5, 677], [3, 5, 677], [2, 7, 677], [2, 2, 683], [2, 3, 683], [3, 3, 683], [2, 5, 683], [3, 5, 683], [2, 7, 683], [3, 7, 683], [2, 19, 673], [2, 2, 691], [2, 3, 691], [3, 3, 691], [2, 5, 691], [3, 5, 691], [2, 7, 691], [3, 7, 691], [2, 17, 683], [3, 17, 683], [2, 11, 691], [2, 2, 701]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 681 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[2, 3, 701], [3, 3, 701], [2, 5, 701], [3, 5, 701], [2, 7, 701], [3, 7, 701], [2, 19, 691], [2, 2, 709], [2, 3, 709], [3, 3, 709], [2, 5, 709], [3, 5, 709], [2, 7, 709], [3, 7, 709], [2, 17, 701], [3, 17, 701], [2, 11, 709], [2, 2, 719], [2, 3, 719], [3, 3, 719], [2, 5, 719], [3, 5, 719], [2, 7, 719], [3, 7, 719], [2, 19, 709]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 706 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[2, 2, 727], [2, 3, 727], [3, 3, 727], [2, 5, 727], [3, 5, 727], [2, 7, 727], [2, 2, 733], [2, 3, 733], [3, 3, 733], [2, 5, 733], [3, 5, 733], [2, 7, 733], [2, 2, 739], [2, 3, 739], [3, 3, 739], [2, 5, 739], [2, 2, 743], [2, 3, 743], [3, 3, 743], [2, 5, 743], [3, 5, 743], [2, 7, 743], [3, 7, 743], [2, 13, 739], [2, 2, 751]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 731 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[2, 3, 751], [3, 3, 751], [2, 5, 751], [3, 5, 751], [2, 7, 751], [2, 2, 757], [2, 3, 757], [3, 3, 757], [2, 5, 757], [2, 2, 761], [2, 3, 761], [3, 3, 761], [2, 5, 761], [3, 5, 761], [2, 7, 761], [3, 7, 761], [2, 13, 757], [2, 2, 769], [2, 3, 769], [3, 3, 769], [2, 5, 769], [2, 2, 773], [2, 3, 773], [3, 3, 773], [2, 5, 773]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 756 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[3, 5, 773], [2, 7, 773], [3, 7, 773], [2, 13, 769], [3, 13, 769], [2, 11, 773], [3, 11, 773], [2, 13, 773], [3, 13, 773], [2, 19, 769], [2, 2, 787], [2, 3, 787], [3, 3, 787], [2, 5, 787], [3, 5, 787], [2, 7, 787], [3, 7, 787], [2, 23, 773], [3, 23, 773], [2, 11, 787], [2, 2, 797], [2, 3, 797], [3, 3, 797], [2, 5, 797], [3, 5, 797]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 781 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[2, 7, 797], [3, 7, 797], [2, 19, 787], [3, 19, 787], [2, 11, 797], [3, 11, 797], [2, 13, 797], [2, 2, 809], [2, 3, 809], [2, 2, 811], [2, 3, 811], [3, 3, 811], [2, 5, 811], [3, 5, 811], [2, 7, 811], [3, 7, 811], [2, 11, 809], [3, 11, 809], [2, 11, 811], [2, 2, 821], [2, 3, 821], [2, 2, 823], [2, 3, 823], [3, 3, 823], [2, 5, 823]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 806 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[2, 2, 827], [2, 3, 827], [2, 2, 829], [2, 3, 829], [3, 3, 829], [2, 5, 829], [3, 5, 829], [2, 7, 829], [3, 7, 829], [2, 11, 827], [3, 11, 827], [2, 11, 829], [2, 2, 839], [2, 3, 839], [3, 3, 839], [2, 5, 839], [3, 5, 839], [2, 7, 839], [3, 7, 839], [2, 19, 829], [3, 19, 829], [2, 11, 839], [3, 11, 839], [2, 13, 839], [3, 13, 839]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 831 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[2, 31, 823], [2, 2, 853], [2, 3, 853], [3, 3, 853], [2, 5, 853], [2, 2, 857], [2, 3, 857], [2, 2, 859], [2, 3, 859], [3, 3, 859], [2, 5, 859], [2, 2, 863], [2, 3, 863], [3, 3, 863], [2, 5, 863], [3, 5, 863], [2, 7, 863], [3, 7, 863], [2, 13, 859], [3, 13, 859], [2, 11, 863], [3, 11, 863], [2, 13, 863], [3, 13, 863], [2, 19, 859]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 856 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[2, 2, 877], [2, 3, 877], [3, 3, 877], [2, 5, 877], [2, 2, 881], [2, 3, 881], [2, 2, 883], [2, 3, 883], [3, 3, 883], [2, 5, 883], [2, 2, 887], [2, 3, 887], [3, 3, 887], [2, 5, 887], [3, 5, 887], [2, 7, 887], [3, 7, 887], [2, 13, 883], [3, 13, 883], [2, 11, 887], [3, 11, 887], [2, 13, 887], [3, 13, 887], [2, 19, 883], [3, 19, 883]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 881 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[2, 17, 887], [3, 17, 887], [2, 19, 887], [3, 19, 887], [2, 31, 877], [2, 2, 907], [2, 3, 907], [3, 3, 907], [2, 5, 907], [2, 2, 911], [2, 3, 911], [3, 3, 911], [2, 5, 911], [3, 5, 911], [2, 7, 911], [3, 7, 911], [2, 13, 907], [2, 2, 919], [2, 3, 919], [3, 3, 919], [2, 5, 919], [3, 5, 919], [2, 7, 919], [3, 7, 919], [2, 17, 911]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 906 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[3, 17, 911], [2, 11, 919], [2, 2, 929], [2, 3, 929], [3, 3, 929], [2, 5, 929], [3, 5, 929], [2, 7, 929], [3, 7, 929], [2, 19, 919], [2, 2, 937], [2, 3, 937], [3, 3, 937], [2, 5, 937], [2, 2, 941], [2, 3, 941], [3, 3, 941], [2, 5, 941], [3, 5, 941], [2, 7, 941], [2, 2, 947], [2, 3, 947], [3, 3, 947], [2, 5, 947], [3, 5, 947]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 931 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[2, 7, 947], [2, 2, 953], [2, 3, 953], [3, 3, 953], [2, 5, 953], [3, 5, 953], [2, 7, 953], [3, 7, 953], [2, 43, 919], [3, 43, 919], [2, 11, 953], [3, 11, 953], [2, 13, 953], [3, 13, 953], [2, 31, 937], [2, 2, 967], [2, 3, 967], [3, 3, 967], [2, 5, 967], [2, 2, 971], [2, 3, 971], [3, 3, 971], [2, 5, 971], [3, 5, 971], [2, 7, 971]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 956 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[2, 2, 977], [2, 3, 977], [3, 3, 977], [2, 5, 977], [3, 5, 977], [2, 7, 977], [2, 2, 983], [2, 3, 983], [3, 3, 983], [2, 5, 983], [3, 5, 983], [2, 7, 983], [3, 7, 983], [2, 73, 919], [2, 2, 991], [2, 3, 991], [3, 3, 991], [2, 5, 991], [3, 5, 991], [2, 7, 991], [2, 2, 997], [2, 3, 997], [3, 3, 997], [2, 5, 997], [3, 5, 997]]
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

end OMA.Aoeis_a059998Tab

open OMA.Aoeis_a059998Tab in
theorem OMA.solution : OMA.R_oeis_a059998_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
