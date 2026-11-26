import FormalConjectures.OEIS.«135508»
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Conditional reduction by @harshshah1618.
-- The case p = 2 modulo 3 is discharged using H1.
-- H2 isolates the remaining coprimality obstruction; it is unproved.
namespace OMA.R_OeisA135508_conjecture_R1
open OeisA135508

lemma x_pos (n : ℕ) (hn : 1 ≤ n) : 0 < x n := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => decide
    | succ n ih =>
      change 0 < 2 * x (n + 1) + Nat.lcm (x (n + 1)) (n + 2)
      omega

lemma x_succ_fact (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = x n * (2 + (n + 1) / Nat.gcd (x n) (n + 1)) := by
  cases n with
  | zero => omega
  | succ k =>
    change 2 * x (k + 1) + Nat.lcm (x (k + 1)) (k + 2) = _
    rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    ring

lemma a_eq_div_gcd (n : ℕ) (hn : 1 ≤ n) :
    a n = (n + 1) / Nat.gcd (x n) (n + 1) := by
  rw [a, if_neg (by omega), x_succ_fact n hn]
  simp [x_pos n hn]

lemma a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ n + 1 := by
  rw [a_eq_div_gcd n hn]
  exact Nat.div_le_self _ _

lemma x_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x n ∣ x (n + 1) := by
  rw [x_succ_fact n hn]
  exact Nat.dvd_mul_right _ _

lemma prime_not_dvd_x_before {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n)
    (hsmall : n + 2 < p) : ¬ p ∣ x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · omega
    · simp [x, hp.not_dvd_one]
    · rw [x_succ_fact (k + 1) (by omega)]
      intro hd
      rcases hp.dvd_mul.mp hd with hleft | hright
      · exact ih (k + 1) (by omega) (by omega) (by omega) hleft
      · have hpos : 0 < (2 + (k + 2) / Nat.gcd (x (k + 1)) (k + 2) : ℕ) := by positivity
        have hle := Nat.div_le_self (k + 2) (Nat.gcd (x (k + 1)) (k + 2))
        exact Nat.not_dvd_of_pos_of_lt hpos (by omega) hright

lemma a_at_prime (p : ℕ) (hp : p.Prime) :
    a (p - 1) = if p ∣ x (p - 1) then 1 else p := by
  rw [a_eq_div_gcd _ (by have := hp.two_le; omega), Nat.sub_add_cancel hp.one_le]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, Nat.div_self hp.pos]
  · have hc : Nat.Coprime (x (p - 1)) p := (hp.coprime_iff_not_dvd.mpr hd).symm
    rw [hc.gcd_eq_one, Nat.div_one]

lemma a_dvd (n : ℕ) (hn : 1 ≤ n) : a n ∣ n + 1 := by
  rw [a_eq_div_gcd n hn]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

lemma x_succ_mul_a (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (a n + 2) := by
  rw [x_succ_fact n hn, a_eq_div_gcd n hn, Nat.add_comm 2]

lemma prime_dvd_x_at_next {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ x (p - 1) ↔ p ∣ x (p - 2) := by
  have he : p - 1 = (p - 2) + 1 := by omega
  rw [he, x_succ_mul_a _ (by omega), hp.dvd_mul]
  constructor
  · rintro (h | h)
    · exact h
    · have hb := a_le (p - 2) (by omega)
      have ha := a_dvd (p - 2) (by omega)
      have hupper : a (p - 2) + 2 < 2 * p := by omega
      have heq : a (p - 2) + 2 = p := by
        obtain ⟨k, hk⟩ := h
        have hkpos : 0 < k := by nlinarith
        have hkone : k = 1 := by nlinarith
        simpa only [hkone, Nat.mul_one] using hk
      have hane : a (p - 2) = p - 2 := by omega
      rw [hane] at ha
      have hh : p - 2 ∣ 1 := by
        have ha' : p - 2 ∣ (p - 2) + 1 := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using ha
        exact (Nat.dvd_add_iff_right (dvd_refl (p - 2))).mpr ha'
      have := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hh
      omega
  · exact Or.inl

lemma prime_dvd_x_iff {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ x (p - 1) ↔ a (p - 3) = p - 2 := by
  rw [prime_dvd_x_at_next hp hp5]
  have he : p - 2 = (p - 3) + 1 := by omega
  rw [he, x_succ_mul_a _ (by omega), hp.dvd_mul]
  have hpre := prime_not_dvd_x_before hp (p - 3) (by omega) (by omega)
  rw [or_iff_right hpre]
  constructor
  · intro hd
    have hb := a_le (p - 3) (by omega)
    have hl := Nat.le_of_dvd (by omega : 0 < a (p - 3) + 2) hd
    omega
  · intro ha
    have heq : a (p - 3) + 2 = p := by omega
    rw [heq]

lemma prime_target_iff {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    a (p - 1) = p ↔ a (p - 3) ≠ p - 2 := by
  constructor
  · intro ha heq
    have hd := (prime_dvd_x_iff hp hp5).mpr heq
    rw [a_at_prime p hp, if_pos hd] at ha
    omega
  · intro heq
    have hd : ¬ p ∣ x (p - 1) := fun hd => heq ((prime_dvd_x_iff hp hp5).mp hd)
    rw [a_at_prime p hp, if_neg hd]

def H1 : Prop := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n

def H2 : Prop := ∀ p : ℕ, p.Prime → 5 ≤ p → p % 3 = 1 →
  ¬ (p - 2).Prime → ¬ Nat.Coprime (x (p - 3)) (p - 2)

lemma prime_mod_three_two (hthree : H1) {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) (h5 : p ≠ 5) :
    a (p - 1) = p := by
  by_cases hp7 : 7 ≤ p
  · rw [prime_target_iff hp (by omega)]
    intro ha
    have hd := hthree (p - 3) (by omega)
    have hm : 3 ∣ (p - 3) + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hg : 3 ∣ Nat.gcd (x (p - 3)) ((p - 3) + 1) := Nat.dvd_gcd hd hm
    have hmul : a (p - 3) * Nat.gcd (x (p - 3)) ((p - 3) + 1) = (p - 3) + 1 := by
      rw [a_eq_div_gcd _ (by omega)]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hgpos := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
    have hrel : p - 2 = (p - 3) + 1 := by omega
    rw [ha, hrel] at hmul
    have hb := Nat.mul_le_mul_left ((p - 3) + 1) hgpos
    rw [hmul] at hb
    omega
  · have h : p = 2 ∨ p = 5 := by
      have hp2 := hp.two_le
      omega
    rcases h with rfl | rfl
    · decide
    · exact False.elim (h5 rfl)

theorem main : H1 → H2 → type_of% @OeisA135508.conjecture := by
  intro hthree hremain p hp hnot
  by_cases hp5 : 5 ≤ p
  · have hp3 : ¬ 3 ∣ p := fun h => by
      have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp h
      omega
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
      have hrem : p % 3 ≠ 0 := fun h => hp3 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases hmod with h1 | h2
    · rw [prime_target_iff hp hp5]
      intro ha
      apply hremain p hp hp5 h1 hnot
      have hmul : a (p - 3) * Nat.gcd (x (p - 3)) ((p - 3) + 1) = (p - 3) + 1 := by
        rw [a_eq_div_gcd _ (by omega)]
        exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
      have he : (p - 3) + 1 = p - 2 := by omega
      rw [he, ha] at hmul
      have hg : Nat.gcd (x (p - 3)) (p - 2) = 1 := by
        nlinarith [Nat.zero_le (Nat.gcd (x (p - 3)) (p - 2))]
      exact hg
    · exact prime_mod_three_two hthree hp h2 (fun h => by subst p; exact hnot (by decide))
  · have hp4 : p ≠ 4 := fun h => by subst p; exact (by decide : ¬ Nat.Prime 4) hp
    have h : p = 2 ∨ p = 3 := by have := hp.two_le; omega
    rcases h with rfl | rfl <;> decide

end OMA.R_OeisA135508_conjecture_R1
