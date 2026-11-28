import OMAReductions.R_oeis_a182481_R1
import Mathlib

-- Step oeis-a182481.R1.H1: hypothesis H1 of reduction oeis-a182481.R1
-- Credit: @prathameshnium. Finite check for 1 ≤ n ≤ 1000.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 448633.

/-! Step oeis-a182481.R1.H1. -/

namespace OMA.Aoeis_a182481Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `671` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 671 2

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
  have hnd := noDiv_sound p 671 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [k] => (decide (0 < k) && (isPrimeB (6 * k * n - 1) && isPrimeB (6 * k * n + 1)))
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
    ∃ k : ℕ, 0 < k ∧ Nat.Prime (6 * k * n - 1) ∧ Nat.Prime (6 * k * n + 1) := by
  unfold core at h
  split at h
  next k =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨k, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1, …, 1000`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1], [1], [1], [3], [1], [2], [1], [4], [2], [1], [3], [1], [4], [5], [2], [2], [1], [1], [2], [2], [7], [5], [1], [3], [1]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[2], [5], [16], [2], [1], [7], [1], [1], [5], [2], [2], [9], [1], [8], [1], [5], [9], [4], [5], [1], [3], [1], [4], [3], [2]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 26 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[7], [1], [20], [5], [2], [8], [14], [1], [3], [21], [43], [4], [6], [3], [5], [8], [4], [9], [2], [1], [3], [1], [14], [15], [9]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 51 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[30], [1], [4], [22], [7], [20], [21], [9], [7], [2], [2], [1], [4], [8], [3], [2], [9], [5], [10], [1], [2], [19], [6], [5], [1]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 76 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[7], [6], [1], [3], [10], [10], [1], [4], [8], [1], [3], [4], [4], [7], [8], [3], [15], [5], [2], [17], [2], [39], [14], [2], [4]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 101 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[3], [24], [19], [7], [3], [5], [4], [6], [2], [1], [15], [1], [1], [2], [4], [5], [5], [1], [3], [7], [7], [1], [11], [2], [7]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 126 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[13], [15], [4], [10], [3], [2], [4], [11], [20], [5], [2], [10], [6], [22], [3], [27], [5], [31], [2], [1], [13], [1], [9], [2], [1]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 151 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[2], [1], [4], [22], [7], [3], [1], [21], [5], [3], [10], [15], [5], [2], [11], [15], [1], [6], [43], [2], [3], [11], [6], [3], [4]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 176 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[23], [19], [5], [3], [1], [13], [4], [6], [5], [5], [7], [5], [1], [3], [1], [2], [1], [4], [5], [1], [7], [5], [5], [2], [3]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 201 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[2], [20], [10], [5], [4], [3], [5], [6], [13], [3], [22], [11], [1], [7], [15], [3], [1], [29], [33], [4], [7], [1], [1], [3], [2]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 226 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[3], [5], [5], [12], [7], [10], [9], [9], [20], [2], [13], [6], [14], [2], [4], [3], [5], [1], [10], [1], [2], [16], [4], [3], [2]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 251 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[3], [35], [1], [3], [2], [2], [14], [1], [28], [7], [25], [1], [19], [2], [4], [13], [19], [10], [2], [2], [23], [4], [1], [5], [5]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 276 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[3], [10], [9], [8], [18], [2], [25], [5], [10], [6], [17], [1], [1], [2], [4], [18], [35], [10], [3], [8], [2], [1], [10], [5], [1]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 301 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[3], [9], [11], [12], [26], [5], [15], [1], [22], [2], [50], [4], [1], [27], [6], [2], [11], [4], [2], [34], [20], [1], [1], [18], [3]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 326 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5], [1], [15], [7], [1], [2], [1], [11], [12], [10], [20], [5], [5], [3], [3], [13], [25], [31], [5], [3], [7], [5], [1], [22], [4]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 351 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[8], [9], [1], [2], [6], [8], [50], [5], [10], [1], [3], [6], [31], [20], [1], [30], [15], [4], [8], [14], [3], [1], [5], [2], [2]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 376 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[20], [14], [10], [13], [4], [3], [4], [5], [28], [11], [2], [30], [6], [2], [12], [3], [4], [5], [7], [3], [7], [14], [11], [13], [1]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 401 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[23], [9], [4], [15], [7], [3], [1], [66], [12], [12], [2], [6], [14], [15], [2], [7], [24], [1], [20], [3], [27], [14], [1], [42], [8]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 426 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[8], [1], [36], [10], [1], [5], [5], [10], [10], [2], [5], [6], [11], [8], [1], [3], [1], [25], [7], [2], [2], [11], [4], [12], [5]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 451 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[7], [10], [6], [13], [8], [37], [16], [6], [12], [5], [22], [11], [19], [2], [2], [3], [15], [4], [7], [1], [10], [11], [9], [13], [1]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 476 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[50], [9], [4], [27], [11], [23], [6], [6], [5], [4], [2], [5], [20], [7], [6], [15], [9], [10], [3], [1], [13], [10], [35], [3], [2]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 501 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[7], [14], [1], [22], [2], [18], [19], [14], [12], [3], [32], [44], [5], [7], [3], [5], [1], [1], [8], [12], [2], [26], [30], [7], [1]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 526 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[28], [19], [10], [30], [1], [3], [15], [134], [28], [1], [5], [1], [36], [7], [1], [2], [24], [14], [2], [4], [8], [15], [5], [3], [10]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 551 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[40], [1], [1], [2], [2], [3], [30], [5], [78], [3], [5], [26], [1], [12], [1], [20], [15], [1], [2], [3], [7], [1], [24], [8], [6]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 576 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[2], [4], [9], [5], [3], [15], [15], [4], [2], [9], [2], [1], [10], [20], [3], [8], [10], [5], [7], [3], [22], [9], [20], [2], [7]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 601 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[48], [6], [1], [2], [2], [25], [9], [14], [20], [6], [5], [1], [5], [22], [4], [10], [1], [14], [28], [11], [5], [6], [21], [5], [3]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 626 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[3], [4], [1], [8], [1], [23], [31], [6], [17], [13], [8], [4], [5], [10], [3], [17], [1], [11], [3], [1], [7], [25], [9], [2], [1]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 651 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[35], [6], [21], [17], [3], [12], [1], [15], [8], [2], [2], [11], [1], [8], [17], [2], [10], [1], [38], [19], [10], [20], [9], [2], [7]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 676 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[18], [5], [1], [7], [1], [30], [1], [14], [8], [1], [8], [1], [11], [10], [9], [8], [4], [6], [2], [5], [13], [10], [1], [17], [14]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 701 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[7], [61], [5], [32], [15], [20], [11], [19], [40], [2], [60], [1], [10], [18], [7], [3], [6], [16], [7], [10], [15], [1], [11], [15], [2]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 726 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[2], [4], [1], [5], [4], [18], [14], [1], [17], [3], [8], [4], [4], [25], [6], [18], [15], [5], [7], [2], [3], [6], [1], [3], [1]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 751 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[17], [9], [10], [5], [11], [7], [15], [9], [13], [2], [2], [1], [4], [5], [7], [17], [25], [6], [7], [4], [23], [5], [1], [12], [1]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 776 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[8], [10], [15], [7], [7], [5], [9], [10], [3], [2], [12], [11], [10], [2], [38], [13], [29], [14], [22], [9], [58], [1], [4], [15], [7]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 801 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[3], [11], [1], [10], [6], [20], [10], [4], [2], [1], [8], [1], [16], [2], [7], [2], [16], [4], [7], [2], [7], [5], [30], [5], [1]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 826 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[8], [54], [39], [10], [12], [2], [6], [10], [8], [4], [2], [10], [34], [27], [8], [33], [4], [6], [2], [6], [25], [1], [15], [3], [2]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 851 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[7], [21], [20], [17], [1], [10], [19], [4], [12], [13], [17], [14], [10], [7], [5], [5], [70], [14], [7], [7], [5], [16], [21], [13], [4]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 876 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[23], [4], [1], [25], [2], [18], [1], [5], [3], [4], [18], [6], [1], [3], [6], [5], [1], [5], [47], [1], [15], [9], [5], [3], [3]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 901 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[13], [10], [4], [23], [2], [2], [4], [6], [7], [3], [22], [5], [6], [3], [1], [20], [1], [1], [37], [5], [2], [5], [6], [17], [13]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 926 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[17], [24], [21], [5], [3], [3], [1], [14], [55], [4], [12], [31], [39], [8], [7], [3], [40], [6], [7], [18], [5], [11], [9], [10], [1]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 951 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[22], [20], [1], [12], [1], [3], [20], [11], [28], [12], [2], [4], [16], [5], [20], [3], [5], [4], [8], [2], [5], [24], [15], [7], [17]]
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

end OMA.Aoeis_a182481Tab

open OMA.Aoeis_a182481Tab in
theorem OMA.solution : OMA.R_oeis_a182481_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
