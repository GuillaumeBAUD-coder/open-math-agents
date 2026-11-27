import OMAStatements.S_oeis_a067281
import Mathlib

namespace A067281Aux
open OMA.S_oeis_a067281

lemma classes_succ (n : ℕ) : classes (n + 1) = (ordCompl[2] (n + 1)) ::ₘ classes n := by
  unfold classes
  rw [List.range_succ, List.map_append, List.map_singleton, Multiset.cons_coe]
  exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)

lemma mem_le (n x : ℕ) (hx : x ∈ classes n) : x ≤ n := by
  unfold classes at hx
  rw [Multiset.mem_coe, List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have h1 := Nat.ordCompl_le (k + 1) 2
  have h2 := List.mem_range.mp hk
  omega

lemma card_classes (n : ℕ) : (classes n).card = n := by
  unfold classes
  rw [Multiset.coe_card, List.length_map, List.length_range]
end A067281Aux

open OMA.S_oeis_a067281 A067281Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a067281.main := by
  intro n
  unfold OMA.S_oeis_a067281.a
  have hodd : ordCompl[2] (2 * n + 1) = 2 * n + 1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * n + 1)]; simp
  have hcl : classes (2 * n + 1) = (2 * n + 1) ::ₘ classes (2 * n) := by
    rw [classes_succ, hodd]
  have hnot : (2 * n + 1) ∉ classes (2 * n) := fun h => by
    have := mem_le _ _ h
    omega
  rw [Multiset.countPerms_filter_ne (2 * n + 1) (classes (2 * n + 1)), hcl]
  rw [Multiset.card_cons, card_classes, Multiset.count_cons_self,
    Multiset.count_eq_zero_of_notMem hnot, Nat.choose_one_right]
  rw [Multiset.filter_cons_of_neg _ (by simp), Multiset.filter_eq_self.mpr ?_]
  intro x hx heq
  exact hnot (heq ▸ hx)
