import OMAReductions.R_oeis_a218797_R1
import Mathlib

-- Step oeis-a218797.R1.H1: hypothesis H1 of reduction oeis-a218797.R1
-- Credit: @prathameshnium. Finite check for 1715 ≤ n ≤ 1828.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 13271507.

/-! Step oeis-a218797.R1.H1. -/

namespace OMA.Aoeis_a218797Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `3645` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 3645 2

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
  have hnd := noDiv_sound p 3645 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q, r] => (decide (p ≤ q) && (decide (q ≤ r) && (decide (p + q + r + 1 = 2 * n) && (isPrimeB (p) && (isPrimeB (q) && (isPrimeB (r) && isPrimeB (p ^ 2 + q ^ 2 + r ^ 2)))))))
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
    ∃ p q r : ℕ, p ≤ q ∧ q ≤ r ∧ p + q + r + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime r ∧ Nat.Prime (p ^ 2 + q ^ 2 + r ^ 2) := by
  unfold core at h
  split at h
  next p q r =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨p, q, r, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5, isPrimeB_sound _ a6⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1715, …, 1828`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[3, 19, 3407], [3, 157, 3271], [3, 23, 3407], [3, 59, 3373], [3, 73, 3361], [3, 3, 3433], [3, 5, 3433], [3, 271, 3169], [3, 251, 3191], [3, 71, 3373], [3, 13, 3433], [3, 197, 3251], [3, 137, 3313], [3, 3, 3449], [3, 761, 2693], [3, 127, 3329], [3, 97, 3361], [3, 11, 3449], [3, 73, 3389], [3, 3, 3461], [3, 263, 3203], [3, 7, 3461], [3, 127, 3343], [3, 11, 3461], [3, 41, 3433]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1715 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[3, 757, 2719], [3, 17, 3461], [3, 67, 3413], [3, 181, 3301], [3, 113, 3371], [3, 17, 3469], [3, 19, 3469], [3, 23, 3467], [3, 31, 3461], [3, 151, 3343], [3, 83, 3413], [3, 31, 3467], [3, 31, 3469], [3, 3, 3499], [3, 191, 3313], [3, 37, 3469], [3, 137, 3371], [3, 103, 3407], [3, 79, 3433], [3, 191, 3323], [3, 47, 3469], [3, 457, 3061], [3, 809, 2711], [3, 11, 3511], [3, 7, 3517]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 1740 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 59, 3467], [3, 61, 3467], [3, 31, 3499], [3, 71, 3461], [3, 73, 3461], [3, 7, 3529], [3, 47, 3491], [3, 13, 3527], [3, 3, 3539], [3, 11, 3533], [3, 233, 3313], [3, 79, 3469], [3, 3, 3547], [3, 5, 3547], [3, 37, 3517], [3, 23, 3533], [3, 11, 3547], [3, 331, 3229], [3, 149, 3413], [3, 7, 3557], [3, 7, 3559], [3, 41, 3527], [3, 13, 3557], [3, 103, 3469], [3, 491, 3083]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 1765 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[3, 17, 3559], [3, 19, 3559], [3, 89, 3491], [3, 23, 3559], [3, 67, 3517], [3, 29, 3557], [3, 7, 3581], [3, 7, 3583], [3, 131, 3461], [3, 223, 3371], [3, 3, 3593], [3, 17, 3581], [3, 17, 3583], [3, 919, 2683], [3, 353, 3251], [3, 89, 3517], [3, 151, 3457], [3, 149, 3461], [3, 29, 3583], [3, 43, 3571], [3, 269, 3347], [3, 59, 3559], [3, 61, 3559], [3, 173, 3449], [3, 11, 3613]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 1790 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 3, 3623], [3, 101, 3527], [3, 71, 3559], [3, 73, 3559], [3, 11, 3623], [3, 109, 3527], [3, 181, 3457], [3, 23, 3617], [3, 11, 3631], [3, 7, 3637], [3, 317, 3329], [3, 17, 3631], [3, 7, 3643], [3, 59, 3593]]
theorem len4 : w4.length = 14 := rfl
theorem ok4 : checkList 1815 w4 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `1715 ≤ n ≤ 1828` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 1715 ≤ n) (h2 : n ≤ 1828) : ∃ x, good n x = true := by
  by_cases c0 : n < 1740
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 1765
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 1790
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 1815
  · exact chunk ok3 len3 (by omega) (by omega)
  exact chunk ok4 len4 (by omega) (by omega)

end OMA.Aoeis_a218797Tab

open OMA.Aoeis_a218797Tab in
theorem OMA.solution : OMA.R_oeis_a218797_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
