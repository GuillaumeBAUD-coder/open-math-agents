import OMAStatements.S_oeis_a306652
import Mathlib

namespace OMA.P_oeis_a306652

open Finset

/-- Summing an `n`-periodic function over `1..n` is invariant under shifting. -/
theorem shift_sum (n : ℕ) (f : ℕ → ℕ) (hp : ∀ m, f (m + n) = f m) (s : ℕ) :
    ∑ m ∈ Icc 1 n, f (m + s) = ∑ m ∈ Icc 1 n, f m := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hI : Icc 1 n = Ico 1 (n + 1) := by ext x; simp
    rw [← ih, hI, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    have key := (sum_range_succ' (fun i => f (1 + i + s)) n).symm.trans
      (sum_range_succ (fun i => f (1 + i + s)) n)
    have h1 : f (1 + n + s) = f (1 + 0 + s) := by
      rw [show 1 + n + s = (1 + s) + n by omega, hp]
    rw [h1] at key
    have key' := add_right_cancel key
    rw [← key']
    apply sum_congr rfl
    intro i _
    congr 1
    omega

/-- The `k`-th column of the double sum. -/
def T (c n k : ℕ) : ℕ :=
  ∑ m ∈ Icc 1 n, if k ∣ n ∧ n / k ∣ m ∧ k ∣ m + c then 1 else 0

theorem S_eq (c n : ℕ) : OMA.S_oeis_a306652.S c n = ∑ k ∈ Icc 1 n, T c n k := by
  unfold OMA.S_oeis_a306652.S T
  exact sum_comm

theorem T_zero_of_not_dvd (c n k : ℕ) (h : ¬ Nat.gcd (n / k) k ∣ c) : T c n k = 0 := by
  unfold T
  apply sum_eq_zero
  intro m _
  rw [if_neg]
  rintro ⟨_, hd, hk⟩
  apply h
  have h1 : Nat.gcd (n / k) k ∣ m := (Nat.gcd_dvd_left _ _).trans hd
  have h2 : Nat.gcd (n / k) k ∣ m + c := (Nat.gcd_dvd_right _ _).trans hk
  exact (Nat.dvd_add_right h1).mp h2

theorem T_eq_of_dvd_two (n k : ℕ) (hkn : k ∣ n) (h : Nat.gcd (n / k) k ∣ 2) :
    T 4 n k = T 2 n k := by
  set d := n / k with hd
  -- find `t` with `d * t ≡ 2 [MOD k]`
  obtain ⟨t, ht⟩ : ∃ t, d * t % k = 2 % k := by
    by_cases hk : k ≤ 2
    · refine ⟨0, ?_⟩
      interval_cases k
      · simp [hd] at h
      · simp
      · simp
    · have hg : Nat.gcd d k < k := lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) h) (by omega)
      obtain ⟨t0, -, ht0⟩ := Nat.exists_mul_mod_eq_gcd hg
      refine ⟨t0 * (2 / Nat.gcd d k), ?_⟩
      rw [← mul_assoc, Nat.mul_mod, ht0, Nat.mul_mod_mod, Nat.mul_div_cancel' h]
  have hdn : d ∣ n := Nat.div_dvd_of_dvd hkn
  let f : ℕ → ℕ := fun m => if k ∣ n ∧ d ∣ m ∧ k ∣ m + 2 then 1 else 0
  have hp : ∀ m, f (m + n) = f m := by
    intro m
    simp only [f]
    congr 1
    apply propext
    rw [Nat.dvd_add_left hdn, show m + n + 2 = m + 2 + n by omega, Nat.dvd_add_left hkn]
  have e := shift_sum n f hp (d * t)
  unfold T
  rw [← hd, ← e]
  apply sum_congr rfl
  intro m _
  simp only [f]
  congr 1
  apply propext
  rw [Nat.dvd_add_left (dvd_mul_right d t)]
  have hmod : m + d * t + 2 ≡ m + 4 [MOD k] := by
    have : d * t ≡ 2 [MOD k] := ht
    have := (Nat.ModEq.refl m).add (this.add (Nat.ModEq.refl 2))
    simpa [add_assoc] using this
  rw [(Nat.ModEq.dvd_iff hmod dvd_rfl)]

theorem sixteen_of (n k : ℕ) (hkn : k ∣ n) (h4 : Nat.gcd (n / k) k ∣ 4)
    (h2 : ¬ Nat.gcd (n / k) k ∣ 2) : 16 ∣ n := by
  have hg : Nat.gcd (n / k) k = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) h4
    interval_cases hx : Nat.gcd (n / k) k <;> simp_all
  have hd : 4 ∣ n / k := hg ▸ Nat.gcd_dvd_left _ _
  have hk : 4 ∣ k := hg ▸ Nat.gcd_dvd_right _ _
  have : n = n / k * k := (Nat.div_mul_cancel hkn).symm
  rw [this]
  exact Nat.mul_dvd_mul hd hk

theorem T_le (n k : ℕ) : T 2 n k ≤ T 4 n k := by
  by_cases h : Nat.gcd (n / k) k ∣ 2
  · by_cases hkn : k ∣ n
    · rw [T_eq_of_dvd_two n k hkn h]
    · unfold T
      rw [sum_eq_zero]
      · exact Nat.zero_le _
      intro m _
      rw [if_neg]
      exact fun hh => hkn hh.1
  · rw [T_zero_of_not_dvd 2 n k h]
    exact Nat.zero_le _

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    (OMA.S_oeis_a306652.a306652 n ≠ OMA.S_oeis_a306652.a147848 n ↔ 16 ∣ n) := by
  intro n hn
  unfold OMA.S_oeis_a306652.a306652 OMA.S_oeis_a306652.a147848
  rw [S_eq, S_eq]
  constructor
  · intro hne
    by_contra h16
    apply hne
    apply sum_congr rfl
    intro k _
    by_cases hkn : k ∣ n
    · by_cases h2 : Nat.gcd (n / k) k ∣ 2
      · exact T_eq_of_dvd_two n k hkn h2
      · have h4 : ¬ Nat.gcd (n / k) k ∣ 4 := fun h4 => h16 (sixteen_of n k hkn h4 h2)
        rw [T_zero_of_not_dvd 4 n k h4, T_zero_of_not_dvd 2 n k h2]
    · unfold T
      rw [sum_eq_zero, sum_eq_zero] <;>
      · intro m _
        rw [if_neg]
        exact fun hh => hkn hh.1
  · intro h16
    apply ne_of_gt
    have h4mem : 4 ∈ Icc 1 n := by
      have := Nat.le_of_dvd (by omega) h16
      simp; omega
    apply sum_lt_sum (fun k _ => T_le n k) ⟨4, h4mem, ?_⟩
    have h4n : 4 ∣ n := (by norm_num : 4 ∣ 16).trans h16
    have h4d : 4 ∣ n / 4 := by
      obtain ⟨q, rfl⟩ := h16
      rw [show 16 * q = 4 * (4 * q) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      exact dvd_mul_right 4 q
    have hg : Nat.gcd (n / 4) 4 = 4 := Nat.gcd_eq_right h4d
    rw [T_zero_of_not_dvd 2 n 4 (by rw [hg]; norm_num)]
    unfold T
    apply Nat.lt_of_lt_of_le _ (single_le_sum (f := fun m =>
      if 4 ∣ n ∧ n / 4 ∣ m ∧ 4 ∣ m + 4 then 1 else 0) (fun _ _ => Nat.zero_le _)
      (a := n / 4) ?_)
    · rw [if_pos ⟨h4n, dvd_rfl, (Nat.dvd_add_left (dvd_refl 4)).mpr h4d⟩]
      norm_num
    · simp only [mem_Icc]
      constructor
      · exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h4d; omega)
      · exact Nat.div_le_self n 4

end OMA.P_oeis_a306652

open OMA.P_oeis_a306652 in
theorem OMA.solution : type_of% @OMA.S_oeis_a306652.main := main_proof
