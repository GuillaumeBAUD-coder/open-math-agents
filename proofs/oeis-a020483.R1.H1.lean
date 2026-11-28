import OMAReductions.R_oeis_a020483_R1
import Mathlib

-- Step oeis-a020483.R1.H1: hypothesis H1 of reduction oeis-a020483.R1
-- Credit: @prathameshnium. Finite check for 0 ≤ n ≤ 999.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 2003.

/-! Step oeis-a020483.R1.H1. -/

namespace OMA.Aoeis_a020483Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `46` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 46 2

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
  have hnd := noDiv_sound p 46 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p] => (isPrimeB (p) && isPrimeB (p + 2 * n))
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
    ∃ p : ℕ, p.Prime ∧ (p + 2 * n).Prime := by
  unfold core at h
  split at h
  next p =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1⟩ := h
    exact ⟨p, isPrimeB_sound _ a0, isPrimeB_sound _ a1⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 0, …, 999`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2], [3], [3], [5], [3], [3], [5], [3], [3], [5], [3], [7], [5], [3], [3], [7], [5], [3], [5], [3], [3], [5], [3], [7], [5]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 0 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3], [7], [5], [3], [3], [7], [5], [3], [5], [3], [3], [7], [5], [3], [5], [3], [7], [5], [3], [13], [7], [5], [3], [5], [3]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 25 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3], [5], [3], [3], [5], [3], [19], [13], [11], [13], [7], [5], [3], [5], [3], [7], [5], [3], [3], [11], [11], [7], [5], [3], [3]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 50 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [5], [3], [7], [5], [3], [7], [5], [3], [3], [11], [11], [7], [5], [3], [3], [5], [3], [3], [13]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 75 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[11], [31], [7], [5], [3], [13], [11], [13], [7], [5], [3], [5], [3], [3], [5], [3], [7], [5], [3], [3], [11], [29], [7], [5], [3]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 100 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [7], [5], [3], [3], [7], [5], [3], [5], [3], [3], [11], [23], [7], [5], [3], [19], [13], [11], [13]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 125 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[7], [5], [3], [5], [3], [3], [5], [3], [31], [13], [11], [31], [7], [5], [3], [7], [5], [3], [11], [11], [7], [5], [3], [3], [5]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 150 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[3], [7], [5], [3], [31], [7], [5], [3], [7], [5], [3], [7], [5], [3], [5], [3], [7], [5], [3], [13], [7], [5], [3], [5], [3]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 175 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[19], [7], [5], [3], [11], [11], [7], [5], [3], [3], [11], [11], [7], [5], [3], [3], [7], [5], [3], [5], [3], [7], [5], [3], [13]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 200 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[7], [5], [3], [5], [3], [3], [5], [3], [13], [11], [17], [7], [5], [3], [13], [7], [5], [3], [5], [3], [13], [7], [5], [3], [5]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 225 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3], [7], [5], [3], [13], [11], [11], [7], [5], [3], [3], [19], [17], [31], [13], [11], [31], [7], [5], [3], [7], [5], [3], [11], [23]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 250 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [7], [5], [3], [3], [7], [5], [3], [11], [23], [7], [5], [3], [7], [5], [3], [7], [5], [3], [3]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 275 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [5], [3], [3], [13], [11], [19], [7], [5], [3], [11], [11], [7], [5], [3], [3], [5], [3], [7], [5]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 300 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3], [7], [5], [3], [3], [13], [11], [13], [7], [5], [3], [5], [3], [7], [5], [3], [19], [7], [5], [3], [11], [17], [7], [5], [3]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 325 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[19], [7], [5], [3], [11], [17], [7], [5], [3], [43], [7], [5], [3], [7], [5], [3], [7], [5], [3], [5], [3], [19], [7], [5], [3]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 350 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[7], [5], [3], [5], [3], [13], [7], [5], [3], [5], [3], [37], [13], [11], [19], [7], [5], [3], [11], [23], [7], [5], [3], [13], [11]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 375 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[11], [7], [5], [3], [3], [11], [11], [7], [5], [3], [3], [5], [3], [3], [11], [23], [7], [5], [3], [19], [13], [11], [13], [7], [5]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 400 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[3], [5], [3], [3], [5], [3], [19], [13], [11], [13], [7], [5], [3], [5], [3], [3], [5], [3], [43], [19], [17], [19], [13], [11], [13]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 425 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[7], [5], [3], [5], [3], [19], [7], [5], [3], [11], [17], [7], [5], [3], [13], [7], [5], [3], [5], [3], [7], [5], [3], [7], [5]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 450 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[3], [19], [13], [11], [13], [7], [5], [3], [5], [3], [7], [5], [3], [7], [5], [3], [31], [7], [5], [3], [7], [5], [3], [13], [11]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 475 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[13], [7], [5], [3], [5], [3], [7], [5], [3], [3], [11], [11], [7], [5], [3], [3], [7], [5], [3], [11], [11], [7], [5], [3], [3]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 500 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[11], [11], [7], [5], [3], [3], [7], [5], [3], [19], [17], [19], [13], [11], [13], [7], [5], [3], [5], [3], [3], [5], [3], [7], [5]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 525 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[3], [7], [5], [3], [43], [7], [5], [3], [7], [5], [3], [7], [5], [3], [23], [23], [19], [17], [17], [13], [11], [11], [7], [5], [3]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 550 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[3], [11], [17], [7], [5], [3], [19], [7], [5], [3], [11], [29], [7], [5], [3], [7], [5], [3], [7], [5], [3], [31], [7], [5], [3]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 575 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[13], [11], [13], [7], [5], [3], [5], [3], [7], [5], [3], [7], [5], [3], [3], [7], [5], [3], [13], [11], [19], [7], [5], [3], [11]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 600 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[29], [7], [5], [3], [19], [17], [17], [13], [11], [11], [7], [5], [3], [3], [5], [3], [7], [5], [3], [3], [7], [5], [3], [5], [3]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 625 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[3], [5], [3], [13], [11], [11], [7], [5], [3], [3], [7], [5], [3], [41], [53], [31], [29], [47], [31], [23], [41], [19], [17], [53], [13]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 650 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[11], [29], [7], [5], [3], [7], [5], [3], [7], [5], [3], [37], [7], [5], [3], [19], [17], [43], [13], [11], [19], [7], [5], [3], [11]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 675 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[23], [7], [5], [3], [19], [13], [11], [13], [7], [5], [3], [5], [3], [3], [5], [3], [7], [5], [3], [13], [7], [5], [3], [5], [3]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 700 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[3], [7], [5], [3], [13], [11], [19], [7], [5], [3], [11], [11], [7], [5], [3], [3], [5], [3], [3], [5], [3], [7], [5], [3], [13]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 725 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[11], [29], [7], [5], [3], [13], [11], [17], [7], [5], [3], [31], [7], [5], [3], [13], [11], [19], [7], [5], [3], [7], [5], [3], [5]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 750 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[3], [7], [5], [3], [13], [7], [5], [3], [5], [3], [13], [7], [5], [3], [5], [3], [19], [13], [11], [13], [7], [5], [3], [5], [3]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 775 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[7], [5], [3], [3], [5], [3], [7], [5], [3], [3], [7], [5], [3], [11], [29], [7], [5], [3], [31], [19], [17], [67], [13], [11], [19]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 800 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [5], [3], [3], [29], [23], [37], [19], [17], [19], [13], [11], [13], [7], [5], [3], [5], [3], [3], [11]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 825 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[23], [7], [5], [3], [13], [11], [11], [7], [5], [3], [3], [11], [17], [7], [5], [3], [79], [7], [5], [3], [7], [5], [3], [7], [5]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 850 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[3], [7], [5], [3], [19], [17], [61], [13], [11], [19], [7], [5], [3], [7], [5], [3], [5], [3], [3], [13], [11], [19], [7], [5], [3]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 875 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[11], [29], [7], [5], [3], [13], [11], [17], [7], [5], [3], [67], [7], [5], [3], [17], [29], [13], [11], [23], [7], [5], [3], [31], [13]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 900 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[11], [19], [7], [5], [3], [7], [5], [3], [5], [3], [3], [5], [3], [3], [11], [53], [7], [5], [3], [13], [11], [41], [7], [5], [3]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 925 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[7], [5], [3], [7], [5], [3], [19], [17], [17], [13], [11], [11], [7], [5], [3], [3], [17], [17], [13], [11], [11], [7], [5], [3], [3]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 950 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[23], [41], [19], [17], [29], [13], [11], [23], [7], [5], [3], [7], [5], [3], [19], [7], [5], [3], [7], [5], [3], [5], [3], [3], [5]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 975 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `0 ≤ n ≤ 999` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 0 ≤ n) (h2 : n ≤ 999) : ∃ x, good n x = true := by
  by_cases c0 : n < 25
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 50
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 75
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 100
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 125
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 150
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 175
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 200
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 225
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 250
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 275
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 300
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 325
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 350
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 375
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 400
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 425
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 450
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 475
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 500
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 525
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 550
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 575
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 600
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 625
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 650
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 675
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 700
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 725
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 750
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 775
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 800
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 825
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 850
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 875
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 900
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 925
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 950
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 975
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a020483Tab

open OMA.Aoeis_a020483Tab in
theorem OMA.solution : OMA.R_oeis_a020483_R1.H1 := by
  intro n  hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
