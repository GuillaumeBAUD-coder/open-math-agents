import OMAReductions.R_oeis_a227899_R1
import Mathlib

-- Step oeis-a227899.R1.H1: hypothesis H1 of reduction oeis-a227899.R1
-- Credit: @prathameshnium. Finite check for 4 ≤ n ≤ 754.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1126513.

/-! Step oeis-a227899.R1.H1. -/

namespace OMA.Aoeis_a227899Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1063` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1063 2

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
  have hnd := noDiv_sound p 1063 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (isPrimeB (p) && (decide (p < n) && (isPrimeB (3 * p - 4) && isPrimeB (n ^ 2 + (n - p) ^ 2))))
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
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (3 * p - 4).Prime ∧
      (n ^ 2 + (n - p) ^ 2).Prime := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 4, …, 754`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3], [3], [5], [5], [3], [5], [3], [5], [5], [3], [3], [11], [7], [5], [11], [3], [7], [11], [5], [3], [5], [3], [5], [5], [3]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 4 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[19], [7], [5], [5], [5], [5], [11], [7], [5], [31], [5], [3], [7], [17], [3], [3], [7], [5], [17], [5], [3], [7], [11], [7], [3]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 29 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[29], [29], [5], [5], [3], [5], [17], [5], [7], [5], [3], [3], [31], [7], [3], [29], [29], [5], [17], [11], [19], [11], [17], [5], [31]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 54 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[5], [3], [7], [5], [5], [5], [7], [17], [5], [3], [19], [11], [17], [5], [11], [3], [3], [5], [7], [5], [5], [11], [5], [5], [11]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 79 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3], [11], [11], [37], [5], [3], [3], [5], [5], [11], [5], [7], [11], [17], [5], [3], [59], [5], [5], [11], [5], [3], [5], [5], [3]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 104 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[29], [3], [5], [7], [3], [3], [11], [37], [19], [31], [5], [11], [5], [5], [31], [29], [3], [7], [19], [3], [3], [17], [31], [7], [11]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 129 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[19], [3], [5], [7], [3], [29], [7], [31], [5], [61], [3], [7], [7], [5], [31], [5], [7], [17], [7], [5], [79], [3], [5], [5], [5]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 154 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[19], [11], [5], [5], [5], [3], [3], [47], [7], [61], [19], [3], [11], [7], [11], [19], [7], [5], [17], [61], [3], [3], [17], [5], [31]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 179 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[79], [17], [5], [5], [11], [3], [11], [7], [5], [61], [5], [17], [11], [5], [5], [19], [19], [11], [17], [3], [3], [17], [11], [7], [31]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 204 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[79], [17], [37], [17], [5], [5], [3], [11], [47], [3], [29], [19], [5], [19], [5], [3], [3], [11], [17], [11], [19], [17], [5], [5], [131]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 229 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[5], [11], [37], [5], [31], [29], [3], [5], [7], [3], [5], [3], [11], [7], [3], [5], [11], [7], [19], [131], [3], [7], [7], [7], [3]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 254 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[19], [19], [5], [5], [3], [3], [47], [5], [17], [11], [3], [61], [37], [5], [31], [5], [17], [5], [5], [3], [5], [37], [61], [19], [61]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 279 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[59], [11], [7], [17], [151], [5], [7], [5], [7], [3], [19], [17], [17], [37], [61], [5], [3], [17], [5], [5], [79], [7], [5], [29], [3]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 304 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3], [7], [37], [17], [131], [5], [7], [11], [29], [5], [89], [11], [37], [7], [5], [29], [17], [5], [5], [11], [3], [31], [7], [5], [241]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 329 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[29], [19], [7], [5], [61], [3], [7], [7], [7], [5], [29], [3], [17], [7], [5], [29], [11], [5], [5], [31], [5], [7], [107], [5], [31]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 354 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[79], [11], [17], [5], [3], [19], [3], [5], [5], [5], [3], [19], [5], [17], [191], [3], [59], [7], [17], [31], [79], [3], [5], [19], [3]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 379 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[5], [7], [11], [19], [11], [3], [7], [5], [7], [3], [19], [29], [7], [37], [61], [3], [19], [7], [37], [5], [19], [11], [17], [17], [3]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 404 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[59], [3], [7], [59], [5], [3], [7], [5], [5], [5], [5], [29], [5], [5], [3], [19], [11], [31], [5], [3], [19], [17], [17], [5], [241]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 429 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[3], [11], [5], [29], [11], [5], [11], [5], [17], [131], [5], [7], [5], [5], [5], [5], [3], [7], [7], [5], [5], [7], [31], [19], [3]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 454 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[19], [11], [7], [29], [241], [19], [3], [5], [17], [191], [5], [11], [5], [17], [61], [59], [29], [7], [17], [131], [3], [7], [5], [47], [5]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 479 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[5], [3], [37], [5], [11], [19], [7], [17], [5], [11], [19], [31], [5], [17], [3], [479], [19], [7], [7], [3], [3], [29], [5], [5], [421]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 504 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[5], [3], [7], [5], [3], [5], [3], [61], [7], [3], [3], [7], [17], [47], [11], [5], [11], [5], [5], [11], [29], [7], [5], [5], [5]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 529 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[19], [31], [5], [17], [131], [3], [47], [37], [7], [31], [5], [7], [17], [17], [31], [3], [17], [5], [19], [5], [3], [3], [17], [47], [131]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 554 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[19], [3], [17], [19], [3], [5], [11], [7], [37], [241], [5], [11], [17], [7], [271], [5], [11], [7], [19], [3], [29], [7], [7], [5], [5]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 579 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[5], [19], [5], [5], [3], [5], [3], [11], [5], [3], [89], [7], [47], [5], [5], [19], [7], [5], [7], [5], [5], [17], [7], [17], [61]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 604 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[3], [11], [7], [5], [11], [3], [3], [11], [17], [3], [29], [11], [31], [5], [31], [59], [17], [7], [7], [5], [3], [47], [67], [59], [3]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 629 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[29], [3], [7], [7], [5], [5], [7], [5], [5], [5], [3], [17], [7], [17], [5], [5], [7], [5], [47], [5], [3], [11], [5], [7], [11]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 654 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[59], [3], [47], [5], [31], [149], [11], [17], [17], [3], [5], [17], [11], [7], [5], [5], [17], [17], [37], [11], [5], [11], [11], [29], [11]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 679 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[79], [29], [5], [29], [241], [59], [11], [5], [19], [11], [409], [7], [5], [17], [191], [3], [11], [5], [7], [5], [5], [7], [5], [107], [3]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 704 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[29], [11], [61], [19], [3], [3], [19], [5], [5], [61], [3], [3], [11], [5], [3], [59], [3], [11], [5], [5], [19], [7], [5], [7], [5]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 729 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[229]]
theorem len30 : w30.length = 1 := rfl
theorem ok30 : checkList 754 w30 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `4 ≤ n ≤ 754` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 4 ≤ n) (h2 : n ≤ 754) : ∃ x, good n x = true := by
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
  exact chunk ok30 len30 (by omega) (by omega)

end OMA.Aoeis_a227899Tab

open OMA.Aoeis_a227899Tab in
theorem OMA.solution : OMA.R_oeis_a227899_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
