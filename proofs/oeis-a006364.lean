import OMAStatements.S_oeis_a006364
import Mathlib

-- Problem: A006364, the closed form with the binary weight.
-- Upstream: formal-conjectures statements/oeis-a006364.lean (declaration OMA.S_oeis_a006364.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: m qualifies exactly when m / 2 = 2j + t(j) with t the Thue-Morse bit, so the
-- (m+1)-st term is 4 (m / 2) + 2 t(m / 2) + m mod 2; the closed form follows by parity.

namespace OMA.P_oeis_a006364

open OMA.S_oeis_a006364

theorem bitCount_two_mul_add (j b : ℕ) (hb : b < 2) : bitCount (2 * j + b) = bitCount j + b := by
  rcases Nat.eq_zero_or_pos (2 * j + b) with h | h
  · have hj : j = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hj hb0
    rfl
  · unfold bitCount
    rw [Nat.digits_def' (by norm_num) h, List.sum_cons,
      show (2 * j + b) % 2 = b by omega, show (2 * j + b) / 2 = j by omega]
    ring

theorem bitCount_le : ∀ k : ℕ, bitCount k ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rfl
    · obtain ⟨j, b, hb, rfl⟩ : ∃ j b, b < 2 ∧ k = 2 * j + b :=
        ⟨k / 2, k % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 2).symm⟩
      rw [bitCount_two_mul_add j b hb]
      have := ih j (by omega)
      omega

/-- The Thue-Morse bit. -/
def t (j : ℕ) : ℕ := bitCount j % 2

/-- The claimed enumeration. -/
def f (m : ℕ) : ℕ := 4 * (m / 2) + 2 * t (m / 2) + m % 2

theorem f_two_mul_add (j b : ℕ) (hb : b < 2) : f (2 * j + b) = 4 * j + 2 * t j + b := by
  unfold f
  rw [show (2 * j + b) / 2 = j by omega, show (2 * j + b) % 2 = b by omega]

theorem t_lt (j : ℕ) : t j < 2 := Nat.mod_lt _ (by norm_num)

theorem f_mono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro m
  obtain ⟨j, b, hb, rfl⟩ : ∃ j b, b < 2 ∧ m = 2 * j + b :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 2).symm⟩
  rw [f_two_mul_add j b hb]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · rw [show 2 * j + 0 + 1 = 2 * j + 1 by ring, f_two_mul_add j 1 (by norm_num)]
    omega
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) + 0 by ring, f_two_mul_add (j + 1) 0 (by norm_num)]
    have := t_lt j
    omega

theorem f_maps (m : ℕ) : Qualifies (f m) := by
  obtain ⟨j, b, hb, rfl⟩ : ∃ j b, b < 2 ∧ m = 2 * j + b :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 2).symm⟩
  rw [f_two_mul_add j b hb]
  unfold Qualifies
  have ht := t_lt j
  rw [show (4 * j + 2 * t j + b) / 2 = 2 * j + t j by omega, bitCount_two_mul_add j _ ht]
  unfold t
  omega

theorem f_surj (m : ℕ) (hm : Qualifies m) : ∃ k, f k = m := by
  unfold Qualifies at hm
  obtain ⟨u, c, hc, rfl⟩ : ∃ u c, c < 2 ∧ m = 2 * u + c :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 2).symm⟩
  rw [show (2 * u + c) / 2 = u by omega] at hm
  obtain ⟨j, b, hb, rfl⟩ : ∃ j b, b < 2 ∧ u = 2 * j + b :=
    ⟨u / 2, u % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod u 2).symm⟩
  rw [bitCount_two_mul_add j b hb] at hm
  have htb : t j = b := by unfold t; omega
  refine ⟨2 * j + c, ?_⟩
  rw [f_two_mul_add j c hc, htb]
  ring

theorem nth_eq (m : ℕ) : Nat.nth Qualifies m = f m := by
  have hinf : (Set.ofPred Qualifies).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_maps
  have hU : ∀ k, k ∈ {k : ℕ | ∀ hf : (Set.ofPred Qualifies).Finite, k < hf.toFinset.card} :=
    fun k hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hU m)).symm
  · intro x hx
    obtain ⟨k, hk⟩ := f_surj x hx
    exact ⟨k, hU k, hk⟩
  · intro k _
    exact f_maps k
  · exact f_mono.strictMonoOn _

theorem neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rw [← Nat.mod_add_div k 2, pow_add, pow_mul]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem main' : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = 2 * (n : ℤ) + (-1 : ℤ) ^ (n - bitCount (n - 1)) - (3 + (-1 : ℤ) ^ n) / 2 := by
  intro n hn
  have hle := bitCount_le (n - 1)
  unfold a
  rw [nth_eq]
  obtain ⟨j, c, hc, he⟩ : ∃ j c, c < 2 ∧ n - 1 = 2 * j + c :=
    ⟨(n - 1) / 2, (n - 1) % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod (n - 1) 2).symm⟩
  rw [he, f_two_mul_add j c hc, bitCount_two_mul_add j c hc, neg_one_pow_eq, neg_one_pow_eq]
  rw [he, bitCount_two_mul_add j c hc] at hle
  have ht : t j = bitCount j % 2 := rfl
  have hn : n = 2 * j + c + 1 := by omega
  subst hn
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;>
    rcases Nat.mod_two_eq_zero_or_one (bitCount j) with h | h
  all_goals
    rw [ht, h]
    split_ifs <;> push_cast <;> omega

end OMA.P_oeis_a006364

theorem OMA.solution : type_of% @OMA.S_oeis_a006364.main := OMA.P_oeis_a006364.main'
