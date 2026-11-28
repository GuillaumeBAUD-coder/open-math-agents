import OMAStatements.S_oeis_a364639
import Mathlib

namespace A364639Proof

open OMA.S_oeis_a364639

lemma ceil_step (a b : ℕ) (hb : 1 ≤ b) :
    ⌈((a : ℚ) + 1) / b⌉ - ⌈(a : ℚ) / b⌉ = if b ∣ a then 1 else 0 := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hv : a % b < b := Nat.mod_lt _ hb
  have hd : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hvd : b ∣ a ↔ a % b = 0 := Nat.dvd_iff_mod_eq_zero
  generalize a / b = u at *
  generalize a % b = v at *
  have hdq : (b : ℚ) * (u : ℚ) + (v : ℚ) = a := by exact_mod_cast hd
  have hvq : (v : ℚ) + 1 ≤ b := by exact_mod_cast hv
  have hv0 : (0 : ℚ) ≤ (v : ℚ) := by positivity
  have h1 : ⌈((a : ℚ) + 1) / b⌉ = (u : ℤ) + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · rw [lt_div_iff₀ hbq]; linarith
    · rw [div_le_iff₀ hbq]; linarith
  rw [h1]
  by_cases h : b ∣ a
  · rw [if_pos h]
    have h0 : v = 0 := hvd.mp h
    rw [h0] at hdq
    have h2 : ⌈(a : ℚ) / b⌉ = (u : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor
      · rw [lt_div_iff₀ hbq]; push_cast at hdq; linarith
      · rw [div_le_iff₀ hbq]; push_cast at hdq; linarith
    rw [h2]; ring
  · rw [if_neg h]
    have h0 : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h' | h'
      · exact absurd (hvd.mpr h') h
      · exact h'
    have h0q : (1 : ℚ) ≤ (v : ℚ) := by exact_mod_cast h0
    have h2 : ⌈(a : ℚ) / b⌉ = (u : ℤ) + 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor
      · rw [lt_div_iff₀ hbq]; linarith
      · rw [div_le_iff₀ hbq]; linarith
    rw [h2]; ring

lemma A_formula (k t i : ℕ) (hk : 1 ≤ k) (ht : k * (k + 1) = 2 * t) :
    A (t + i) k = ⌈((i : ℚ) + 1) / k⌉ - ⌈((i : ℚ) + 1) / ((k + 1 : ℕ) : ℚ)⌉ + 1 := by
  unfold A
  rw [if_pos ⟨hk, by omega⟩]
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hk0 : (k : ℚ) ≠ 0 := ne_of_gt hkq
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have htq : (t : ℚ) = (k : ℚ) * (k + 1) / 2 := by
    have : ((k * (k + 1) : ℕ) : ℚ) = ((2 * t : ℕ) : ℚ) := by rw [ht]
    push_cast at this
    linarith
  have h1 : c (t + i) k = ⌈((i : ℚ) + 1) / k⌉ := by
    unfold c
    congr 1
    push_cast
    rw [htq]; field_simp; ring
  have h2 : c (t + i) (k + 1) = ⌈((i : ℚ) + 1) / ((k + 1 : ℕ) : ℚ)⌉ - 1 := by
    unfold c
    have e : (((t + i : ℕ) : ℚ) + 1) / ((k + 1 : ℕ) : ℚ) - (((k + 1 : ℕ) : ℚ) + 1) / 2
        = ((i : ℚ) + 1) / ((k + 1 : ℕ) : ℚ) - ((1 : ℤ) : ℚ) := by
      push_cast
      rw [htq]; field_simp; ring
    rw [e, Int.ceil_sub_intCast]
  rw [h1, h2]; ring

lemma S_eq (k j : ℕ) (hk : 1 ≤ k) (hj : j < k * (k + 1)) :
    ((if k ∣ j + 1 then 1 else 0) - (if (k + 1) ∣ j + 1 then 1 else 0) : ℤ) = S k j := by
  have hr : j % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
  have hq : j / (k + 1) < k := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hj
  have hd : (k + 1) * (j / (k + 1)) + j % (k + 1) = j := Nat.div_add_mod j (k + 1)
  unfold S
  generalize j / (k + 1) = q at *
  generalize j % (k + 1) = r at *
  have e1 : (k + 1) ∣ j + 1 ↔ r = k := by
    constructor
    · intro h
      have h' : (k + 1) ∣ r + 1 := by
        have h2 : (k + 1) ∣ (k + 1) * q + (r + 1) := by
          have : (k + 1) * q + (r + 1) = j + 1 := by omega
          rw [this]; exact h
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h2
      have := Nat.le_of_dvd (by omega) h'
      omega
    · intro h
      refine ⟨q + 1, ?_⟩
      rw [← hd, h]; ring
  have e2 : k ∣ j + 1 ↔ (r + q + 1 = k ∨ (r = k ∧ q + 1 = k)) := by
    have hj1 : j + 1 = k * q + (r + q + 1) := by rw [← hd]; ring
    rw [hj1, Nat.dvd_add_right (dvd_mul_right _ _)]
    constructor
    · rintro ⟨m, hm⟩
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hm; omega
        · exact h
      have hm2 : m ≤ 2 := by
        by_contra hc
        have : k * 3 ≤ k * m := Nat.mul_le_mul_left k (by omega)
        omega
      interval_cases m <;> omega
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
  simp only [e1, e2]
  split_ifs <;> omega

theorem sol : type_of% @OMA.S_oeis_a364639.main := by
  intro k hk
  obtain ⟨t, ht⟩ : ∃ t, k * (k + 1) = 2 * t := by
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    exact ⟨m, by omega⟩
  have htdiv : k * (k + 1) / 2 = t := by omega
  have hk2 : 2 ≤ k * (k + 1) := by nlinarith
  rw [htdiv]
  constructor
  · unfold T
    have h0 := A_formula k t 0 hk ht
    rw [Nat.add_zero] at h0
    have hA : A (t - 1) k = 0 := by
      unfold A; rw [if_neg (by omega)]
    rw [h0, hA]
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h1 : ⌈(((0 : ℕ) : ℚ) + 1) / k⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · simp; positivity
      · push_cast; rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : ⌈(((0 : ℕ) : ℚ) + 1) / ((k + 1 : ℕ) : ℚ)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · simp; positivity
      · push_cast; rw [div_le_iff₀ (by positivity)]; linarith
    rw [h1, h2]; ring
  · intro i
    unfold T
    have e : t + 1 + i - 1 = t + i := by omega
    have e' : t + 1 + i = t + (i + 1) := by omega
    rw [e, e', A_formula k t (i + 1) hk ht, A_formula k t i hk ht]
    have s1 := ceil_step (i + 1) k hk
    have s2 := ceil_step (i + 1) (k + 1) (by omega)
    have hp : 0 < k * (k + 1) := by omega
    have hS := S_eq k (i % (k * (k + 1))) hk (Nat.mod_lt _ hp)
    have hi : i + 1 = i % (k * (k + 1)) + 1 + k * (k + 1) * (i / (k * (k + 1))) := by
      have := Nat.mod_add_div i (k * (k + 1)); omega
    have d1 : k ∣ i + 1 ↔ k ∣ i % (k * (k + 1)) + 1 := by
      rw [hi]
      exact Nat.dvd_add_left (Dvd.dvd.mul_right (dvd_mul_right k (k + 1)) _)
    have d2 : (k + 1) ∣ i + 1 ↔ (k + 1) ∣ i % (k * (k + 1)) + 1 := by
      rw [hi]
      exact Nat.dvd_add_left (Dvd.dvd.mul_right (dvd_mul_left (k + 1) k) _)
    rw [← hS]
    simp only [← d1, ← d2]
    push_cast at s1 s2 ⊢
    linarith

end A364639Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364639.main := A364639Proof.sol
