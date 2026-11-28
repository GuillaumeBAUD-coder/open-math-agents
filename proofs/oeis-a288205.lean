import OMAStatements.S_oeis_a288205
import Mathlib

namespace OMA.S_oeis_a288205
open Classical

def P : List ℕ := [0,0,1,0,0,1]

lemma sr_P : sr P = P ++ [0,0,0,1,0,0,1,0] := by decide

lemma sr_append (T : List ℕ) : sr (P ++ T) = sr P ++ sr T := by simp [P, sr]

lemma inv (M : ℕ) : ∃ T, sr^[M+2] [0,0] = P ++ T := by
  induction M with
  | zero => exact ⟨[0,0], by decide⟩
  | succ M ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨[0,0,0,1,0,0,1,0] ++ sr T, ?_⟩
    rw [Function.iterate_succ_apply', hT, sr_append, sr_P]
    simp

lemma hI (i : ℕ) (hi : i < 6) : IsOne i ↔ (i = 2 ∨ i = 5) := by
  have key : ∀ M ≥ 2, (sr^[M] [0,0])[i]? = P[i]? := by
    intro M hM
    obtain ⟨T, hT⟩ := inv (M - 2)
    have : M - 2 + 2 = M := by omega
    rw [this] at hT
    rw [hT]
    exact List.getElem?_append_left (by simp [P]; omega)
  constructor
  · rintro ⟨N, hN⟩
    have := hN (max N 2) (le_max_left _ _)
    rw [key _ (le_max_right _ _)] at this
    interval_cases i <;> simp [P] at this ⊢
  · intro h
    refine ⟨2, fun M hM => ?_⟩
    rw [key M hM]
    rcases h with rfl | rfl <;> simp [P]

end OMA.S_oeis_a288205

open OMA.S_oeis_a288205 Classical in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288205.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  have hc : Nat.count IsOne 5 = 1 := by
    simp [Nat.count_succ, hI]
  have hn : Nat.nth IsOne 1 = 5 := by
    have := Nat.nth_count (p := IsOne) (n := 5) ((hI 5 (by norm_num)).2 (by simp))
    rwa [hc] at this
  have ha : a 2 = 6 := by simp [a, hn]
  rw [ha] at h2
  revert h2
  decide
