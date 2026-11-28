import OMAStatements.S_oeis_a026465
import Mathlib

namespace A026465

open OMA.S_oeis_a026465

private def block (b : Bool) : List Bool := [b, !b, !b, b]

private def expand (s : List Bool) : List Bool := s.flatMap block

private def copies (m : ℕ) : List ℕ := List.replicate (2 * (m - 1)) 2

private def pattern (m : ℕ) : List ℕ := [1, 2] ++ copies m ++ [1]

private theorem tau_tau (s : List Bool) : tau (tau s) = expand s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp [tau, expand, block] at ih ⊢ <;> rw [ih]

private theorem run_same (b : Bool) (s : List Bool) :
    runAux b 1 (block b ++ s) = [2, 2] ++ runAux b 1 s := by
  cases b <;> simp [block, runAux]

private theorem run_diff (b c : Bool) (h : b ≠ c) (s : List Bool) :
    runAux b 1 (block c ++ s) = [1, 1, 2] ++ runAux c 1 s := by
  cases b <;> cases c <;> simp_all [block, runAux]

private theorem copies_succ (m : ℕ) (hm : 0 < m) :
    copies (m + 1) = copies m ++ [2, 2] := by
  unfold copies
  rw [show 2 * (m + 1 - 1) = 2 * (m - 1) + 2 by omega, List.replicate_add]
  rfl

private theorem expand_runAux (s : List Bool) (b : Bool) (m : ℕ) (hm : 0 < m) :
    [1, 2] ++ copies m ++ runAux b 1 (expand s) = (runAux b m s).flatMap pattern := by
  induction s generalizing b m with
  | nil => simp [expand, runAux, pattern]
  | cons c s ih =>
      change [1, 2] ++ copies m ++ runAux b 1 (block c ++ expand s) =
        (runAux b m (c :: s)).flatMap pattern
      by_cases hc : b = c
      · subst c
        rw [runAux, if_pos rfl, run_same, ← ih b (m + 1) (by omega), copies_succ m hm]
        simp only [List.append_assoc]
      · rw [runAux, if_neg hc, run_diff _ _ hc]
        simp only [List.flatMap_cons, pattern, ← ih c 1 (by decide), List.append_assoc]
        rfl

private theorem expand_runs (s : List Bool) :
    runLengths (expand s) = (runLengths s).flatMap pattern := by
  cases s with
  | nil => rfl
  | cons b s =>
      have h := expand_runAux s b 1 (by decide)
      cases b <;> simpa [expand, block, copies, runLengths, runAux] using h

private theorem stage_mem {k j : ℕ} (h : j ∈ runStage k) : j = 1 ∨ j = 2 := by
  induction k generalizing j with
  | zero => exact Or.inl (by simpa [runStage] using h)
  | succ k ih =>
      obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp h
      rcases ih hi with rfl | rfl
      · simp [alpha] at hj
        tauto
      · simp [alpha] at hj
        tauto

private theorem stage_runs (k : ℕ) : runLengths (thueStage (2 * k)) = runStage k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      simp only [thueStage, tau_tau, expand_runs, ih, runStage]
      apply List.flatMap_congr
      intro j hj
      rcases stage_mem hj with rfl | rfl <;> decide

private theorem extension (k : ℕ) : ∃ z : List ℕ, z ≠ [] ∧ runStage (k + 1) = runStage k ++ z := by
  induction k with
  | zero => exact ⟨[2, 1], by decide, by decide⟩
  | succ k ih =>
      obtain ⟨z, hz, he⟩ := ih
      cases z with
      | nil => exact (hz rfl).elim
      | cons j z =>
          have hj : j ∈ runStage (k + 1) := by rw [he]; simp
          refine ⟨(j :: z).flatMap alpha, ?_, ?_⟩
          · rcases stage_mem hj with rfl | rfl <;> simp [alpha]
          · change (runStage (k + 1)).flatMap alpha =
                (runStage k).flatMap alpha ++ (j :: z).flatMap alpha
            exact (congrArg (fun l => l.flatMap alpha) he).trans List.flatMap_append

private theorem reverse_alpha (j : ℕ) : (alpha j).reverse = alpha j := by
  rcases j with _ | _ | _ | j <;> rfl

private theorem reverse_map (l : List ℕ) :
    (l.flatMap alpha).reverse = l.reverse.flatMap alpha := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      simp [List.reverse_cons, List.flatMap_append, List.reverse_append, reverse_alpha, ih]

private theorem palindrome (k : ℕ) : (runStage k).reverse = runStage k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [runStage, reverse_map, ih]

private theorem length_ge (k : ℕ) : k + 1 ≤ (runStage k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
      obtain ⟨z, hz, he⟩ := extension k
      rw [he, List.length_append]
      have h : 0 < z.length := List.length_pos_iff.mpr hz
      omega

private theorem prefix_later (k : ℕ) : runStage k <+: (runStage (k + 1)).dropLast := by
  obtain ⟨z, hz, he⟩ := extension k
  rw [he, List.dropLast_append_of_ne_nil hz]
  exact ⟨_, rfl⟩

end A026465

open OMA.S_oeis_a026465 A026465 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026465.main := by
  have hRun (r : List ℕ) : runPrefix r ↔ ∃ k : ℕ, r <+: runStage k := by
    constructor
    · rintro ⟨k, h⟩
      rw [stage_runs] at h
      exact ⟨k, h.trans (List.dropLast_prefix _)⟩
    · rintro ⟨k, h⟩
      refine ⟨k + 1, ?_⟩
      rw [stage_runs]
      exact h.trans (prefix_later k)
  refine ⟨hRun, ?_⟩
  intro m
  exact ⟨runStage m, runStage m, by have := length_ge m; omega, palindrome m,
    (hRun _).mpr ⟨m, ⟨[], by simp⟩⟩, List.Sublist.refl _⟩