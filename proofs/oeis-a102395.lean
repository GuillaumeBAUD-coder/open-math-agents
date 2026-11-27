import OMAStatements.S_oeis_a102395
import Mathlib

open OMA.S_oeis_a102395
namespace A102395Proof

def AB : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | (t + 1) => (2 * (AB t).2, (AB t).1 + (AB t).2)

theorem AB_fst (t : ℕ) : (AB t).1 = A078008 t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | (t + 2), ih =>
      have h1 := ih (t + 1) (by omega)
      have h0 := ih t (by omega)
      simp only [AB] at h1 h0 ⊢
      rw [A078008]
      omega

def T (n s : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if (k + s) % 3 = 0 then n.choose k % 2 else 0

theorem T_ext (n s d : ℕ) :
    (∑ k ∈ Finset.range (n + 1 + d), if (k + s) % 3 = 0 then n.choose k % 2 else 0) = T n s := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc, Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem sum_two (M : ℕ) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.range (2 * M), f k) = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem lucas2 (q b j c : ℕ) (hb : b < 2) (hc : c < 2) :
    (2 * q + b).choose (2 * j + c) % 2 = (b.choose c * q.choose j) % 2 := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 * q + b) (2 * j + c) 2 ⟨Nat.prime_two⟩
  have e1 : (2 * q + b) % 2 = b := by omega
  have e2 : (2 * j + c) % 2 = c := by omega
  have e3 : (2 * q + b) / 2 = q := by omega
  have e4 : (2 * j + c) / 2 = j := by omega
  rw [e1, e2, e3, e4] at h
  exact h

theorem T_even (q s : ℕ) : T (2 * q) s = T q (2 * s) := by
  rw [← T_ext (2 * q) s 1, show 2 * q + 1 + 1 = 2 * (q + 1) by ring, sum_two]
  unfold T
  apply Finset.sum_congr rfl
  intro j _
  have l0 := lucas2 q 0 j 0 (by omega) (by omega)
  have l1 := lucas2 q 0 j 1 (by omega) (by omega)
  simp only [add_zero] at l0 l1
  rw [l0, l1]
  simp only [Nat.choose_zero_right, one_mul, Nat.choose_zero_succ, zero_mul, Nat.zero_mod]
  have : (2 * j + s) % 3 = 0 ↔ (j + 2 * s) % 3 = 0 := by omega
  by_cases h : (j + 2 * s) % 3 = 0
  · rw [if_pos (this.mpr h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; simp

theorem T_odd (q s : ℕ) : T (2 * q + 1) s = T q (2 * s) + T q (2 * s + 2) := by
  rw [← T_ext (2 * q + 1) s 0, show 2 * q + 1 + 1 + 0 = 2 * (q + 1) by ring, sum_two]
  unfold T
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have l0 := lucas2 q 1 j 0 (by omega) (by omega)
  have l1 := lucas2 q 1 j 1 (by omega) (by omega)
  simp only [add_zero] at l0 l1
  rw [l0, l1]
  simp only [Nat.choose_zero_right, one_mul, Nat.choose_self]
  have e0 : (2 * j + s) % 3 = 0 ↔ (j + 2 * s) % 3 = 0 := by omega
  have e1 : (2 * j + 1 + s) % 3 = 0 ↔ (j + (2 * s + 2)) % 3 = 0 := by omega
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl]

theorem m3 (q s : Nat) (h : ¬ (2 * q + 1) % 3 = s % 3) (h2 : ¬ q % 3 = 2 * s % 3) :
    q % 3 = (2 * s + 2) % 3 := by
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h3 | h3 | h3 <;>
  rcases (show s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 by omega) with h4 | h4 | h4 <;> omega

theorem T_main (n : ℕ) : ∃ m, ∀ s, T n s = if n % 3 = s % 3 then (AB m).1 else (AB m).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
    · rcases q with _ | q
      · refine ⟨0, fun s => ?_⟩
        simp [T, AB]
        split_ifs <;> omega
      · obtain ⟨m, hm⟩ := ih (q + 1) (by omega)
        refine ⟨m, fun s => ?_⟩
        rw [T_even, hm]
        have : (q + 1) % 3 = 2 * s % 3 ↔ 2 * (q + 1) % 3 = s % 3 := by omega
        rw [if_congr this rfl rfl]
    · obtain ⟨m, hm⟩ := ih q (by omega)
      refine ⟨m + 1, fun s => ?_⟩
      rw [T_odd, hm, hm]
      simp only [AB]
      by_cases h : (2 * q + 1) % 3 = s % 3
      · rw [if_pos h, if_neg (show ¬ q % 3 = 2 * s % 3 by omega),
          if_neg (show ¬ q % 3 = (2 * s + 2) % 3 by omega)]; ring
      · rw [if_neg h]
        by_cases h2 : q % 3 = 2 * s % 3
        · rw [if_pos h2, if_neg (show ¬ q % 3 = (2 * s + 2) % 3 by omega)]
        · rw [if_neg h2, if_pos (m3 q s h h2)]; ring

end A102395Proof

open A102395Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a102395.main := by
  intro n
  obtain ⟨m, hm⟩ := T_main n
  refine ⟨m, ?_⟩
  have h := hm n
  rw [if_pos rfl, AB_fst] at h
  rw [← h]
  unfold a T
  apply Finset.sum_congr rfl
  intro k _
  rw [add_comm n k]
