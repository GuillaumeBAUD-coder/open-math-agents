import OMAStatements.S_oeis_a056084
import Mathlib

namespace OMAProofA056084

def f (j : ℕ) : ℕ := if j % 2 = 0 then 729 * (j / 2) + 1 else 729 * (j / 2) + 728

set_option maxRecDepth 100000 in
lemma res : ∀ r < 729, (r ^ 8 % 729 = 1 ↔ r = 1 ∨ r = 728) := by
  decide

lemma p_iff (k : ℕ) : k ^ 8 % 9 ^ 3 = 1 ↔ k % 729 = 1 ∨ k % 729 = 728 := by
  rw [show (9 : ℕ) ^ 3 = 729 by norm_num, Nat.pow_mod]
  exact res _ (Nat.mod_lt _ (by norm_num))

lemma f_mono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold f
  split_ifs <;> omega

lemma f_mem (j : ℕ) : (f j) ^ 8 % 9 ^ 3 = 1 := by
  rw [p_iff]
  unfold f
  split_ifs <;> omega

lemma f_surj (k : ℕ) (hk : k ^ 8 % 9 ^ 3 = 1) : ∃ j, f j = k := by
  rw [p_iff] at hk
  rcases hk with h | h
  · exact ⟨2 * (k / 729), by unfold f; split_ifs <;> omega⟩
  · exact ⟨2 * (k / 729) + 1, by unfold f; split_ifs <;> omega⟩

lemma inf : (setOf fun k : ℕ => k ^ 8 % 9 ^ 3 = 1).Infinite :=
  Set.infinite_of_injective_forall_mem f_mono.injective f_mem

lemma nth_eq (j : ℕ) : Nat.nth (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1) j = f j := by
  have hS : ∀ n, n ∈ {n : ℕ | ∀ hf : Set.Finite (setOf fun k : ℕ => k ^ 8 % 9 ^ 3 = 1),
      n < hf.toFinset.card} := fun n hf => absurd hf inf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn
    (p := fun k : ℕ => k ^ 8 % 9 ^ 3 = 1) f ?_ ?_ ?_ (hS j)).symm
  · intro k hk
    obtain ⟨j, rfl⟩ := f_surj k hk
    exact ⟨j, hS j, rfl⟩
  · intro n _
    exact f_mem n
  · exact f_mono.strictMonoOn _

lemma f_even (i : ℕ) : f (2 * i) = 729 * i + 1 := by
  unfold f
  split_ifs <;> omega

lemma f_odd (i : ℕ) : f (2 * i + 1) = 729 * i + 728 := by
  unfold f
  split_ifs <;> omega

end OMAProofA056084

theorem OMA.solution : type_of% @OMA.S_oeis_a056084.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold OMA.S_oeis_a056084.a
  rw [show m + 1 - 1 = m by omega, OMAProofA056084.nth_eq]
  rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
  · rw [OMAProofA056084.f_even, pow_succ, pow_mul]
    push_cast
    norm_num
    ring
  · rw [OMAProofA056084.f_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, pow_mul]
    push_cast
    norm_num
    ring
