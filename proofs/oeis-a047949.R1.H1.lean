import OMAReductions.R_oeis_a047949_R1
import Mathlib

-- Step oeis-a047949.R1.H1: hypothesis H1 of reduction oeis-a047949.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 1001.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1039.

/-! Step oeis-a047949.R1.H1. -/

namespace OMA.Aoeis_a047949Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `34` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 34 2

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
  have hnd := noDiv_sound p 34 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [m] => (decide (m ≤ n) && (isPrimeB (n - m) && isPrimeB (n + m)))
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
    ∃ m : ℕ, m ≤ n ∧ Nat.Prime (n - m) ∧ Nat.Prime (n + m) := by
  unfold core at h
  split at h
  next m =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2⟩ := h
    exact ⟨m, a0, isPrimeB_sound _ a1, isPrimeB_sound _ a2⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 1001`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[0], [0], [1], [0], [1], [0], [3], [2], [3], [0], [1], [0], [3], [2], [3], [0], [1], [0], [3], [2], [9], [0], [5], [6], [3]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[4], [9], [0], [1], [0], [9], [4], [3], [6], [5], [0], [9], [2], [3], [0], [1], [0], [3], [2], [15], [0], [5], [12], [3], [8]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[9], [0], [7], [12], [3], [4], [15], [0], [1], [0], [9], [4], [3], [6], [5], [0], [15], [2], [3], [0], [1], [0], [15], [4], [3]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[6], [5], [0], [9], [2], [15], [0], [5], [12], [3], [14], [9], [0], [7], [12], [9], [4], [15], [6], [7], [0], [9], [2], [3], [0]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[1], [0], [3], [2], [3], [0], [1], [0], [3], [2], [15], [0], [13], [12], [15], [10], [9], [12], [7], [18], [9], [14], [15], [12], [13]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[0], [21], [2], [21], [0], [5], [6], [3], [4], [27], [0], [1], [0], [9], [10], [15], [6], [5], [6], [33], [10], [9], [0], [1], [0]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[15], [4], [3], [18], [7], [0], [9], [8], [3], [12], [5], [0], [15], [2], [15], [0], [5], [12], [3], [8], [9], [0], [7], [18], [3]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[4], [15], [0], [1], [0], [9], [10], [27], [6], [5], [6], [9], [8], [9], [0], [1], [0], [3], [2], [3], [0], [1], [0], [27], [10]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[9], [24], [7], [6], [27], [16], [15], [18], [13], [0], [15], [14], [15], [18], [17], [6], [21], [8], [9], [30], [11], [0], [27], [2], [3]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[0], [1], [0], [3], [2], [9], [0], [5], [6], [3], [4], [39], [0], [1], [0], [9], [14], [33], [6], [5], [24], [9], [8], [21], [0]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[11], [24], [3], [14], [15], [0], [19], [18], [3], [10], [21], [0], [7], [42], [3], [4], [39], [0], [1], [0], [9], [4], [3], [6], [5]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[0], [15], [2], [3], [0], [1], [0], [27], [8], [45], [6], [5], [18], [21], [20], [15], [0], [13], [12], [15], [14], [15], [18], [7], [30]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[9], [10], [27], [12], [25], [0], [39], [2], [3], [0], [1], [0], [3], [2], [33], [0], [35], [12], [27], [10], [9], [30], [7], [12], [33]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[10], [21], [18], [17], [0], [15], [16], [3], [18], [23], [0], [21], [8], [9], [48], [5], [6], [75], [8], [33], [0], [1], [0], [3], [2]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[15], [0], [5], [18], [3], [10], [9], [0], [7], [12], [69], [4], [15], [18], [7], [0], [15], [10], [3], [12], [25], [0], [15], [8], [3]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[24], [5], [0], [21], [2], [15], [0], [5], [12], [3], [14], [9], [0], [7], [18], [9], [4], [15], [6], [13], [0], [45], [2], [21], [0]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[19], [6], [15], [4], [27], [24], [11], [0], [9], [10], [45], [30], [5], [6], [15], [16], [21], [0], [1], [0], [21], [26], [15], [6], [5]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[6], [39], [10], [9], [0], [1], [0], [15], [4], [3], [6], [5], [0], [9], [2], [21], [0], [5], [12], [3], [14], [9], [0], [7], [12]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[9], [4], [33], [6], [7], [0], [9], [2], [3], [0], [1], [0], [3], [2], [33], [0], [11], [30], [9], [8], [15], [6], [13], [12], [15]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[10], [21], [0], [19], [18], [21], [4], [63], [6], [23], [0], [21], [2], [33], [0], [29], [6], [15], [4], [75], [6], [11], [0], [9], [2]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[39], [0], [5], [18], [3], [16], [69], [0], [11], [12], [9], [10], [27], [6], [7], [30], [39], [28], [21], [0], [1], [0], [33], [16], [87]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[36], [19], [42], [27], [10], [9], [24], [13], [12], [27], [34], [39], [18], [17], [0], [21], [20], [3], [24], [23], [0], [39], [8], [27], [42]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[5], [54], [33], [8], [15], [0], [11], [12], [3], [38], [15], [0], [7], [42], [3], [4], [45], [0], [1], [0], [15], [4], [3], [12], [55]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[0], [9], [8], [33], [12], [5], [36], [15], [8], [15], [0], [11], [12], [3], [22], [15], [0], [7], [18], [3], [4], [21], [0], [1], [0]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[15], [4], [3], [12], [7], [0], [9], [8], [3], [42], [5], [0], [27], [2], [3], [0], [1], [0], [21], [20], [9], [24], [7], [6], [27]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[14], [15], [12], [11], [0], [15], [14], [27], [18], [5], [6], [21], [8], [21], [0], [1], [0], [3], [2], [15], [0], [5], [42], [3], [8]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[9], [0], [7], [36], [3], [4], [15], [0], [1], [0], [15], [10], [45], [12], [7], [6], [9], [8], [39], [12], [11], [0], [27], [2], [15]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 652 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[0], [5], [48], [3], [20], [9], [0], [7], [24], [33], [4], [45], [12], [29], [0], [9], [16], [33], [48], [5], [36], [21], [40], [9], [0]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 677 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[25], [30], [57], [4], [33], [54], [25], [0], [9], [28], [21], [30], [5], [24], [57], [16], [9], [0], [19], [12], [21], [4], [15], [48], [7]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 702 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[0], [45], [10], [3], [12], [41], [0], [75], [8], [3], [36], [5], [0], [21], [2], [9], [0], [17], [6], [27], [4], [9], [48], [7], [0]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 727 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[9], [20], [3], [54], [5], [0], [15], [2], [9], [0], [11], [6], [45], [4], [57], [6], [29], [0], [27], [2], [15], [0], [13], [36], [33]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 752 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[20], [9], [18], [7], [30], [39], [14], [27], [12], [25], [0], [69], [20], [21], [18], [5], [36], [33], [26], [27], [0], [11], [12], [27], [28]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 777 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[51], [6], [7], [18], [33], [20], [21], [0], [1], [0], [15], [16], [45], [6], [5], [6], [9], [8], [9], [0], [1], [0], [3], [2], [3]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 802 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[0], [1], [0], [9], [8], [21], [6], [5], [24], [27], [16], [15], [0], [13], [12], [15], [14], [15], [18], [7], [36], [9], [10], [27], [12]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 827 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[25], [0], [27], [2], [3], [0], [1], [0], [3], [2], [75], [0], [43], [12], [45], [10], [9], [12], [7], [12], [9], [10], [45], [12], [53]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 852 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[0], [51], [2], [3], [0], [1], [0], [3], [2], [33], [0], [31], [30], [51], [28], [15], [36], [13], [12], [15], [10], [21], [12], [19], [18]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 877 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[39], [16], [93], [24], [23], [0], [21], [2], [27], [0], [25], [6], [27], [4], [93], [30], [11], [0], [9], [62], [15], [60], [5], [42], [15]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 902 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[20], [9], [0], [11], [78], [21], [4], [57], [6], [17], [0], [9], [2], [57], [0], [5], [24], [3], [8], [63], [0], [19], [42], [3], [32]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 927 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[15], [0], [13], [36], [15], [10], [39], [12], [7], [78], [9], [34], [27], [12], [25], [0], [15], [2], [51], [0], [5], [36], [3], [8], [57]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 952 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[0], [31], [12], [3], [10], [15], [0], [7], [48], [33], [4], [21], [42], [7], [0], [21], [16], [3], [18], [13], [0], [15], [22], [9], [18]]
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

end OMA.Aoeis_a047949Tab

open OMA.Aoeis_a047949Tab in
theorem OMA.solution : OMA.R_oeis_a047949_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
