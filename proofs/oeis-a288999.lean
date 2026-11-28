import OMAStatements.S_oeis_a288999
import Mathlib

namespace OMA.S_oeis_a288999
open Classical

def P : List ℕ := [0,0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0]

lemma sr_P : sr P = P ++ [0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,1] := by
  decide +kernel

lemma sr_append (T : List ℕ) : sr (P ++ T) = sr P ++ sr T := by simp [P, sr]

lemma inv (M : ℕ) : ∃ T, sr^[M+6] [0,0] = P ++ T := by
  induction M with
  | zero => exact ⟨[0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,1], by decide +kernel⟩
  | succ M ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨(List.drop 38 (sr P)) ++ sr T, ?_⟩
    rw [Function.iterate_succ_apply', hT, sr_append, sr_P]
    simp [P]

lemma hI (i : ℕ) (hi : i < 38) : IsOne i ↔ P[i]? = some 1 := by
  have key : ∀ M ≥ 6, (sr^[M] [0,0])[i]? = P[i]? := by
    intro M hM
    obtain ⟨T, hT⟩ := inv (M - 6)
    have : M - 6 + 6 = M := by omega
    rw [this] at hT
    rw [hT]
    exact List.getElem?_append_left (by simp [P]; omega)
  constructor
  · rintro ⟨N, hN⟩
    have := hN (max N 6) (le_max_left _ _)
    rwa [key _ (le_max_right _ _)] at this
  · intro h
    refine ⟨6, fun M hM => ?_⟩
    rw [key M hM, h]

end OMA.S_oeis_a288999

open OMA.S_oeis_a288999 Classical in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288999.main) := by
  intro h
  have h2 := h.2.2 11 (by norm_num)
  have hc : Nat.count IsOne 36 = 10 := by
    have : Nat.count IsOne 36 = Nat.count (fun i => P[i]? = some 1) 36 := by
      simp only [Nat.count_eq_card_filter_range]
      congr 1
      apply Finset.filter_congr
      intro x hx
      exact hI x (by simp at hx; omega)
    rw [this]
    decide +kernel
  have hn : Nat.nth IsOne 10 = 36 := by
    have := Nat.nth_count (p := IsOne) (n := 36) ((hI 36 (by norm_num)).2 (by decide +kernel))
    rwa [hc] at this
  have ha : a 11 = 37 := by simp [a, hn]
  rw [ha] at h2
  have hr : round ((11:ℕ) * Real.sqrt 2) = 15 := by
    have := h2
    push_cast at this
    have : round ((11:ℝ) * Real.sqrt 2) = 15 := by omega
    simpa using this
  rw [round_eq, Int.floor_eq_iff] at hr
  have hs : (1.4142:ℝ) < Real.sqrt 2 := by
    apply Real.lt_sqrt_of_sq_lt; norm_num
  push_cast at hr
  linarith [hr.2]
