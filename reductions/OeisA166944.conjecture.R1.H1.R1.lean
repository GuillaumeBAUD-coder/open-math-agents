import OMAReductions.R_OeisA166944_conjecture_R1
import Mathlib.Tactic.IntervalCases

/-! For n ≥ 2 the sequence has the parity of n, and its values lie between n and 3n.
An odd increment at an odd index n divides n−2. If its size exceeds (n−2)/3,
then it must equal n−2. The two remaining questions ask when an increment
is dominated by an earlier one. -/

namespace OMA.R_OeisA166944_conjecture_R1_H1_R1
open OeisA166944

private lemma step (n : ℕ) :
    a (n + 2) = a (n + 1) + Nat.gcd (if (n + 2) % 2 = 0 then n + 2 else n) (a (n + 1)) := by
  rw [a]
  split <;> simp_all

private lemma difference (n : ℕ) :
    d (n + 2) = Nat.gcd (if (n + 2) % 2 = 0 then n + 2 else n) (a (n + 1)) := by
  unfold d
  rw [step]
  simp

private lemma odd_dvd_of_odd {v w : ℕ} (hw : w % 2 = 1) (hd : v ∣ w) :
    v % 2 = 1 := by
  by_contra h
  have hzero : v % 2 = 0 := by omega
  have := Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero hzero).trans hd)
  omega

lemma parity (n : ℕ) : a (n + 2) % 2 = (n + 2) % 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [step (n + 1)]
    let u := Nat.gcd (if (n + 3) % 2 = 0 then n + 3 else n + 1) (a (n + 2))
    change (a (n + 2) + u) % 2 = (n + 3) % 2
    have hu : u % 2 = 1 := by
      by_cases h : (n + 3) % 2 = 0
      · exact odd_dvd_of_odd (by omega : a (n + 2) % 2 = 1) (Nat.gcd_dvd_right ..)
      · have hslot : (if (n + 3) % 2 = 0 then n + 3 else n + 1) % 2 = 1 := by simp only [if_neg h]; omega
        exact odd_dvd_of_odd hslot (Nat.gcd_dvd_left ..)
    omega

lemma bounds (n : ℕ) : n ≤ a n ∧ a n ≤ 3 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|n
    · decide
    rw [step]
    let u := Nat.gcd (if (n + 2) % 2 = 0 then n + 2 else n) (a (n + 1))
    have left : u ∣ (if (n + 2) % 2 = 0 then n + 2 else n) := Nat.gcd_dvd_left ..
    have right : u ∣ a (n + 1) := Nat.gcd_dvd_right ..
    have slotpos : 0 < (if (n + 2) % 2 = 0 then n + 2 else n) := by split <;> omega
    have pos : 0 < u := Nat.gcd_pos_of_pos_left _ slotpos
    change n + 2 ≤ a (n + 1) + u ∧ a (n + 1) + u ≤ 3 * (n + 2)
    refine ⟨by omega, ?_⟩
    by_cases h : (n + 2) % 2 = 0
    · have l : u ∣ n + 2 := by simpa only [if_pos h] using left
      have hd := Nat.dvd_sub (l.mul_left 3) right
      have := Nat.le_of_dvd (by omega : 0 < 3 * (n + 2) - a (n + 1)) hd
      omega
    · have l : u ∣ n := by simpa only [if_neg h] using left
      have hpositive : 0 < n := by omega
      have heven : a (n + 1) % 2 = 0 := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        change a (k + 2) % 2 = 0
        have := parity k
        omega
      have ne : 3 * n ≠ a (n + 1) := by omega
      by_cases less : a (n + 1) < 3 * n
      · have hd := Nat.dvd_sub (l.mul_left 3) right
        have := Nat.le_of_dvd (by omega : 0 < 3 * n - a (n + 1)) hd
        omega
      · have hd := Nat.dvd_sub right (l.mul_left 3)
        have := Nat.le_of_dvd (by omega : 0 < a (n + 1) - 3 * n) hd
        omega

lemma early_appearance {R n : ℕ} (hR : 5 < R) (hn : 2 ≤ n) (hit : d n = R)
    (early : n < 2 * R) : R % 2 = 1 ∧ a (R + 1) = 2 * R := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [difference] at hit
  have left : R ∣ (if (j + 2) % 2 = 0 then j + 2 else j) := hit ▸ Nat.gcd_dvd_left ..
  have right : R ∣ a (j + 1) := hit ▸ Nat.gcd_dvd_right ..
  have hj : 0 < j := by
    by_contra hz
    have : j = 0 := by omega
    subst j
    change 2 = R at hit
    omega
  have hp := parity (j - 1)
  rw [show j - 1 + 2 = j + 1 by omega] at hp
  have odd : (j + 2) % 2 = 1 := by
    by_contra ho
    have he : (j + 2) % 2 = 0 := by omega
    have rOdd := odd_dvd_of_odd (by omega : a (j + 1) % 2 = 1) right
    have dl : R ∣ j + 2 := by simpa only [if_pos he] using left
    obtain ⟨m, hm⟩ := dl
    have m1 : m = 1 := by
      by_contra hn
      have h2 : 2 ≤ m := by
        by_cases hz : m = 0
        · simp [hz] at hm
        · omega
      have := Nat.mul_le_mul_left R h2
      omega
    rw [m1, Nat.mul_one] at hm
    omega
  have dl : R ∣ j := by simpa only [if_neg (by omega : (j + 2) % 2 ≠ 0)] using left
  have rOdd := odd_dvd_of_odd (by omega : j % 2 = 1) dl
  have jEq : j = R := by
    obtain ⟨m, hm⟩ := dl
    by_cases hm1 : m ≤ 1
    · interval_cases m <;> simp_all
    · have := Nat.mul_le_mul_left R (by omega : 2 ≤ m)
      omega
  subst j
  refine ⟨rOdd, ?_⟩
  obtain ⟨m, hm⟩ := right
  have hbound := bounds (R + 1)
  have small : m < 4 := by
    by_contra h
    have := Nat.mul_le_mul_left R (by omega : 4 ≤ m)
    omega
  interval_cases m <;> simp only [Nat.mul_zero, Nat.mul_succ] at hm <;> omega

lemma alignment_iff_early (R : ℕ) (hR : 5 < R) :
    (R % 2 = 1 ∧ a (R + 1) = 2 * R) ↔ ∃ n : ℕ, 2 ≤ n ∧ n < 2 * R ∧ d n = R := by
  constructor
  · rintro ⟨odd, ha⟩
    refine ⟨R + 2, by omega, by omega, ?_⟩
    rw [difference, ha]
    rw [if_neg (by omega)]
    exact Nat.gcd_eq_left (dvd_mul_left ..)
  · rintro ⟨n, hn, he, h⟩
    exact early_appearance hR hn h he

/-- Every large even - index increment occurs after an increment at least as large. -/
def H1 : Prop := ∀ n : ℕ, 2 ≤ n → n % 2 = 0 → 5 < d n →
  ∃ i : ℕ, 2 ≤ i ∧ i < n ∧ d n ≤ d i

/-- An odd - index increment bounded by one third of the shifted index is dominated earlier. -/
def H2 : Prop := ∀ n : ℕ, 2 ≤ n → n % 2 = 1 → 5 < d n → 3 * d n + 2 ≤ n →
  ∃ i : ℕ, 2 ≤ i ∧ i < n ∧ d n ≤ d i

theorem main : H1 → H2 → OMA.R_OeisA166944_conjecture_R1.H1 := by
  rintro evenSmall oddSmall R hR ⟨n, hn, hit, record⟩
  have nondom : ¬ ∃ i : ℕ, 2 ≤ i ∧ i < n ∧ d n ≤ d i := by
    rintro ⟨i, hi, lt, h⟩
    exact (not_le_of_gt (record i hi lt)) (hit ▸ h)
  have odd : n % 2 = 1 := by
    by_contra ho
    exact nondom (evenSmall n hn (by omega) (by omega))
  have bound : n < 3 * R + 2 := by
    by_contra! h
    exact nondom (oddSmall n hn odd (by omega) (by omega))
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have ddiv : R ∣ j := by
    rw [difference] at hit
    have hd : R ∣ (if (j + 2) % 2 = 0 then j + 2 else j) := hit ▸ Nat.gcd_dvd_left ..
    simpa only [if_neg (by omega : (j + 2) % 2 ≠ 0)] using hd
  obtain ⟨m, hm⟩ := ddiv
  have small : m < 3 := by
    by_contra h
    have := Nat.mul_le_mul_left R (by omega : 3 ≤ m)
    omega
  have hidx : j = R := by
    interval_cases m <;> simp only [Nat.mul_zero, Nat.mul_succ] at hm <;> omega
  exact (alignment_iff_early R hR).mpr ⟨j + 2, hn, by omega, hit⟩

end OMA.R_OeisA166944_conjecture_R1_H1_R1
