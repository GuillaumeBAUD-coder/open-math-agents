import OMAStatements.S_oeis_a347205
import Mathlib

/-! A347205: a(n) = T(n, wt(n) + 1) and a(2n) = sum of row n of T up to wt(n) + 1.
Key invariant: for n >= 1 and k <= wt(n), the prefix sum of row n up to k equals T(n', k),
where n' is n with its lowest set bit cleared. -/

namespace OMA.Helpers

open OMA.S_oeis_a347205


theorem A347_a_odd (h : ℕ) : a347205 (2 * h + 1) = a347205 h := by
  rw [a347205]
  try simp only
  have h1 : (2 * h + 1) % 2 = 1 := by omega
  have h2 : (2 * h + 1) / 2 = h := by omega
  simp [h1, h2]

theorem A347_a_even (h : ℕ) (hh : 1 ≤ h) :
    a347205 (2 * h) = a347205 h + a347205 (h - 2 ^ padicValNat 2 h) := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  rw [show 2 * (g + 1) = (2 * g + 1) + 1 by ring, a347205]
  try simp only
  have h1 : (2 * g + 1 + 1) % 2 = 0 := by omega
  have h2 : (2 * g + 1 + 1) / 2 = g + 1 := by omega
  simp [h1, h2]

theorem A347_T_odd (h k : ℕ) : T347205 (2 * h + 1) k =
    if k = wt h + 2 then T347205 h (wt h + 1) else T347205 h k := by
  rw [T347205]
  try simp only
  have h1 : (2 * h + 1) % 2 = 1 := by omega
  have h2 : (2 * h + 1) / 2 = h := by omega
  simp [h1, h2]

theorem A347_T_even (h k : ℕ) (hh : 1 ≤ h) :
    T347205 (2 * h) k = ∑ i ∈ Finset.Icc 1 k, T347205 h i := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  rw [show 2 * (g + 1) = (2 * g + 1) + 1 by ring, T347205]
  try simp only
  have h1 : (2 * g + 1 + 1) % 2 = 0 := by omega
  have h2 : (2 * g + 1 + 1) / 2 = g + 1 := by omega
  simp [h1, h2]

theorem A347_wt_odd (h : ℕ) : wt (2 * h + 1) = wt h + 1 := by
  rw [wt]
  have h1 : (2 * h + 1) % 2 = 1 := by omega
  have h2 : (2 * h + 1) / 2 = h := by omega
  rw [h1, h2]; ring

theorem A347_wt_even (h : ℕ) : wt (2 * h) = wt h := by
  rcases h with _ | g
  · rfl
  rw [show 2 * (g + 1) = (2 * g + 1) + 1 by ring, wt]
  have h1 : (2 * g + 1 + 1) % 2 = 0 := by omega
  have h2 : (2 * g + 1 + 1) / 2 = g + 1 := by omega
  rw [h1, h2]; ring


theorem A347_wt_zero : wt 0 = 0 := by rw [wt]

theorem A347_v_odd (h : ℕ) : padicValNat 2 (2 * h + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

theorem A347_v_even (h : ℕ) (hh : 1 ≤ h) : padicValNat 2 (2 * h) = padicValNat 2 h + 1 := by
  rw [padicValNat.mul (by norm_num) (by omega)]
  have : padicValNat 2 2 = 1 := padicValNat_self
  omega

theorem A347_pow_v_le (h : ℕ) (hh : 1 ≤ h) : 2 ^ padicValNat 2 h ≤ h :=
  Nat.le_of_dvd (by omega) pow_padicValNat_dvd

theorem A347_clr_odd (h : ℕ) : 2 * h + 1 - 2 ^ padicValNat 2 (2 * h + 1) = 2 * h := by
  rw [A347_v_odd]; simp

theorem A347_clr_even (h : ℕ) (hh : 1 ≤ h) :
    2 * h - 2 ^ padicValNat 2 (2 * h) = 2 * (h - 2 ^ padicValNat 2 h) := by
  rw [A347_v_even h hh, pow_succ]
  have := A347_pow_v_le h hh
  rw [Nat.mul_sub]
  ring_nf

theorem A347_parity_cases (n : ℕ) (hn : 1 ≤ n) :
    (∃ h, n = 2 * h + 1) ∨ (∃ h, 1 ≤ h ∧ n = 2 * h) := by
  rcases Nat.even_or_odd n with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · right; exact ⟨h, by omega, by ring⟩
  · left; exact ⟨h, rfl⟩

theorem A347_wt_clr : ∀ h : ℕ, 1 ≤ h → wt (h - 2 ^ padicValNat 2 h) + 1 = wt h := by
  intro h
  refine Nat.strong_induction_on h fun h ih => ?_
  intro hh
  rcases A347_parity_cases h hh with ⟨g, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [A347_clr_odd, A347_wt_even, A347_wt_odd]
  · rw [A347_clr_even g hg, A347_wt_even, A347_wt_even]
    exact ih g (by omega) hg

theorem A347_T_zero_right : ∀ n : ℕ, T347205 n 0 = 0 := by
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [T347205]; simp
  rcases A347_parity_cases n hn with ⟨g, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [A347_T_odd]
    rw [if_neg (by omega)]
    exact ih g (by omega)
  · rw [A347_T_even g 0 hg]; simp

theorem A347_T_one : ∀ n : ℕ, T347205 n 1 = 1 := by
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [T347205]; simp
  rcases A347_parity_cases n hn with ⟨g, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [A347_T_odd]
    rw [if_neg (by omega)]
    exact ih g (by omega)
  · rw [A347_T_even g 1 hg]; simp [ih g (by omega)]

theorem A347_T_zero_left (k : ℕ) : T347205 0 k = if k = 1 then 1 else 0 := by
  rw [T347205]

theorem A347_prefix_sum : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k ≤ wt n →
    ∑ i ∈ Finset.Icc 1 k, T347205 n i = T347205 (n - 2 ^ padicValNat 2 n) k := by
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro hn k hk
  rcases A347_parity_cases n hn with ⟨g, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [A347_clr_odd]
    rw [A347_wt_odd] at hk
    have hs : ∑ i ∈ Finset.Icc 1 k, T347205 (2 * g + 1) i = ∑ i ∈ Finset.Icc 1 k, T347205 g i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [A347_T_odd, if_neg (by omega)]
    rw [hs]
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · -- n = 1
      have : k = 0 ∨ k = 1 := by
        have := A347_wt_zero
        omega
      rcases this with rfl | rfl
      · simp [A347_T_zero_right]
      · simp [A347_T_one]
    · rw [A347_T_even g k hg]
  · rw [A347_clr_even g hg]
    rw [A347_wt_even] at hk
    have hs : ∑ i ∈ Finset.Icc 1 k, T347205 (2 * g) i =
        ∑ i ∈ Finset.Icc 1 k, T347205 (g - 2 ^ padicValNat 2 g) i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [A347_T_even g i hg]
      exact ih g (by omega) hg i (by omega)
    rw [hs]
    rcases Nat.eq_zero_or_pos (g - 2 ^ padicValNat 2 g) with h0 | hpos
    · rw [h0]
      have hw := A347_wt_clr g hg
      rw [h0] at hw
      have := A347_wt_zero
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · simp [A347_T_zero_right]
      · simp [A347_T_one]
    · rw [A347_T_even _ k hpos]

theorem A347_part1 : ∀ n : ℕ, a347205 n = T347205 n (wt n + 1) := by
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [a347205, A347_wt_zero, A347_T_zero_left]; rfl
  rcases A347_parity_cases n hn with ⟨g, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [A347_a_odd, A347_wt_odd, A347_T_odd, if_pos rfl]
    exact ih g (by omega)
  · rw [A347_a_even g hg, A347_wt_even, A347_T_even g _ hg, Finset.sum_Icc_succ_top (by omega)]
    rw [A347_prefix_sum g hg (wt g) le_rfl]
    have hw := A347_wt_clr g hg
    have e1 := ih g (by omega)
    have e2 := ih (g - 2 ^ padicValNat 2 g) (lt_of_le_of_lt (Nat.sub_le _ _) (by omega))
    rw [e1, e2, hw]
    ring

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a347205 in
theorem OMA.solution : type_of% @OMA.S_oeis_a347205.main := by
  intro n
  refine ⟨A347_part1 n, ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show 2 * 0 = 0 from rfl, A347_wt_zero, a347205]
    simp [A347_T_one]
  · rw [A347_part1, A347_wt_even, A347_T_even n _ hn]
