import OMAReductions.R_oeis_a196660_R1
import Mathlib

-- Step oeis-a196660.R1.H1: hypothesis H1 of reduction oeis-a196660.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 40277.

/-! Step oeis-a196660.R1.H1. -/

namespace OMA.Aoeis_a196660Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `202` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 202 2

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
  have hnd := noDiv_sound p 202 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [k] => (decide (0 < k) && (decide (k < n) && isPrimeB (k * n + (n - 1))))
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
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (k * n + (n - 1)) := by
  unfold core at h
  split at h
  next k =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨k, a0, a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1], [1], [1], [3], [1], [1], [2], [1], [1], [3], [1], [7], [2], [1], [1], [3], [2], [1], [2], [1], [1], [5], [1], [5], [3]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[1], [2], [5], [1], [1], [3], [3], [1], [3], [1], [1], [2], [5], [1], [3], [1], [5], [2], [1], [2], [5], [3], [1], [2], [1]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[1], [3], [1], [1], [2], [1], [2], [5], [2], [7], [6], [3], [1], [5], [1], [5], [3], [1], [1], [3], [4], [13], [5], [1], [1]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3], [2], [1], [2], [7], [1], [3], [1], [5], [2], [1], [2], [15], [1], [1], [3], [5], [2], [3], [1], [1], [2], [1], [1], [9]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[4], [5], [2], [3], [1], [5], [3], [5], [3], [3], [1], [5], [1], [1], [2], [1], [2], [11], [1], [1], [3], [3], [4], [3], [1]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[5], [2], [1], [2], [3], [1], [5], [2], [1], [1], [3], [5], [1], [2], [1], [1], [3], [2], [13], [6], [1], [2], [9], [2], [11]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[3], [7], [1], [3], [1], [1], [3], [1], [2], [3], [3], [5], [2], [3], [1], [9], [2], [1], [2], [3], [4], [3], [1], [1], [6]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[1], [7], [9], [1], [7], [3], [5], [1], [3], [2], [1], [2], [7], [1], [21], [1], [7], [5], [1], [2], [3], [2], [1], [2], [1]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[4], [3], [4], [1], [2], [3], [4], [9], [1], [1], [6], [5], [2], [3], [1], [1], [2], [21], [1], [3], [1], [7], [6], [1], [2]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[3], [2], [1], [3], [1], [1], [15], [1], [5], [12], [3], [5], [5], [1], [13], [3], [3], [1], [11], [1], [5], [2], [5], [1], [11]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[1], [13], [2], [1], [4], [11], [2], [5], [3], [1], [1], [3], [4], [13], [2], [5], [5], [5], [2], [1], [3], [3], [1], [9], [2]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[11], [5], [1], [2], [3], [1], [5], [6], [1], [1], [5], [2], [1], [6], [3], [4], [3], [1], [11], [2], [1], [4], [15], [1], [1]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[5], [7], [1], [9], [3], [1], [3], [1], [1], [9], [4], [5], [2], [3], [1], [5], [2], [5], [3], [1], [1], [3], [1], [5], [2]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[1], [2], [5], [1], [1], [3], [5], [4], [11], [6], [1], [2], [1], [2], [11], [1], [13], [2], [5], [1], [5], [5], [7], [2], [1]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[4], [9], [2], [1], [3], [3], [4], [5], [1], [7], [3], [3], [1], [3], [2], [1], [2], [5], [1], [3], [1], [5], [5], [3], [1]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[9], [3], [1], [6], [1], [10], [3], [2], [1], [3], [1], [2], [5], [3], [11], [3], [3], [1], [3], [2], [5], [2], [1], [4], [21]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[3], [5], [5], [1], [1], [3], [2], [7], [2], [1], [1], [5], [1], [1], [3], [3], [4], [15], [1], [11], [5], [9], [5], [3], [2]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[1], [2], [1], [1], [3], [1], [7], [2], [5], [2], [3], [10], [1], [2], [1], [1], [5], [1], [7], [3], [3], [4], [5], [5], [7]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[5], [3], [1], [5], [1], [5], [2], [5], [1], [11], [3], [5], [9], [1], [7], [3], [3], [1], [2], [1], [13], [5], [1], [23], [2]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[1], [2], [9], [2], [7], [6], [3], [1], [5], [1], [11], [3], [1], [5], [9], [1], [5], [2], [3], [1], [3], [2], [1], [2], [3]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[5], [3], [2], [1], [6], [1], [2], [17], [1], [1], [6], [19], [5], [5], [1], [1], [2], [9], [1], [3], [3], [5], [2], [1], [1]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[11], [2], [7], [6], [1], [1], [3], [2], [1], [2], [5], [2], [15], [2], [7], [5], [5], [1], [3], [1], [1], [8], [1], [4], [3]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[1], [7], [5], [1], [2], [9], [4], [1], [3], [3], [1], [3], [4], [1], [2], [3], [5], [5], [2], [7], [3], [7], [2], [5], [1]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[1], [2], [11], [7], [11], [1], [7], [9], [3], [1], [3], [3], [5], [5], [1], [11], [3], [1], [7], [2], [1], [7], [5], [3], [1]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[8], [3], [2], [15], [3], [1], [2], [1], [4], [11], [1], [5], [6], [1], [1], [3], [4], [1], [5], [7], [4], [9], [2], [1], [2]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[5], [5], [11], [1], [19], [6], [3], [2], [3], [2], [5], [2], [1], [1], [11], [1], [13], [2], [1], [1], [5], [3], [1], [2], [1]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[1], [5], [1], [5], [6], [9], [2], [11], [1], [1], [3], [7], [1], [3], [2], [5], [2], [5], [5], [3], [3], [13], [11], [3], [2]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[3], [3], [5], [2], [1], [5], [3], [1], [7], [6], [1], [2], [5], [2], [1], [3], [5], [2], [9], [2], [11], [3], [7], [1], [3]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[5], [5], [2], [1], [4], [5], [4], [5], [2], [3], [1], [3], [1], [1], [6], [1], [2], [11], [1], [13], [3], [5], [1], [5], [1]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[1], [8], [5], [1], [9], [3], [5], [11], [3], [1], [5], [2], [11], [6], [1], [1], [3], [1], [1], [2], [1], [2], [5], [1], [7]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[14], [3], [4], [3], [1], [13], [2], [9], [7], [17], [1], [19], [5], [9], [1], [3], [7], [7], [2], [3], [1], [5], [5], [1], [6]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[1], [2], [5], [1], [7], [5], [7], [1], [11], [1], [5], [9], [5], [1], [3], [1], [7], [2], [7], [7], [3], [2], [1], [2], [1]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[10], [5], [1], [1], [2], [1], [2], [9], [1], [1], [5], [3], [1], [3], [2], [11], [3], [1], [2], [9], [5], [5], [5], [3], [2]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[3], [4], [1], [3], [3], [1], [3], [1], [1], [3], [3], [7], [9], [3], [11], [5], [3], [2], [11], [4], [1], [2], [1], [1], [11]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[3], [7], [9], [1], [8], [15], [4], [5], [2], [1], [1], [9], [2], [5], [3], [1], [4], [9], [2], [1], [5], [3], [1], [3], [6]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[1], [2], [5], [1], [21], [3], [5], [5], [3], [2], [3], [2], [1], [3], [7], [1], [3], [1], [1], [2], [5], [2], [5], [2], [1]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[3], [5], [2], [9], [1], [5], [3], [15], [2], [3], [1], [5], [2], [3], [1], [5], [2], [7], [5], [9], [5], [3], [1], [17], [2]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[15], [4], [5], [2], [1], [3], [23], [1], [3], [1], [1], [17], [1], [1], [17], [3], [5], [6], [1], [2], [23], [2], [5], [11], [1]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[4], [5], [1], [7], [3], [1], [4], [41], [2], [7], [3], [3], [5], [9], [1], [1], [2], [5], [2], [17], [6], [35], [5], [1], [1]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[3], [3], [25], [2], [3], [4], [3], [4], [7], [2], [1], [2], [11], [1], [7], [3], [9], [1], [9], [6], [1], [5], [1], [1], [3]]
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

end OMA.Aoeis_a196660Tab

open OMA.Aoeis_a196660Tab in
theorem OMA.solution : OMA.R_oeis_a196660_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
