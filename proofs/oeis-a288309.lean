import OMAStatements.S_oeis_a288309

open OMA.S_oeis_a288309

private def pairs : List ℕ → ℕ
  | 0 :: 0 :: w => pairs w + 1
  | _ :: w => pairs w
  | [] => 0

private theorem scan : ∀ w : List ℕ, (∀ d ∈ w, d ≤ 1) →
    (∀ d ∈ step w, d ≤ 1) ∧ w.length = w.count 0 + w.count 1 ∧
    (step w).count 0 = w.count 0 + w.count 1 + pairs w ∧
    (step w).count 1 = 2 * w.count 1 + pairs w ∧
    pairs (0 :: step w) + pairs w = w.count 0
  | [], _ => by simp [step, pairs]
  | [0], _ => by decide
  | 0 :: 0 :: w, h | 0 :: 1 :: w, h | 1 :: w, h => by
    obtain ⟨hb, hl, hz, ho, hp⟩ := scan w (fun d hd => h d (by simp [hd]))
    simp [step, pairs, hl, hz, ho]
    exact ⟨hb, by omega⟩
  | 0 :: (k + 2) :: w, h | (k + 2) :: w, h => absurd (h (k + 2) (by simp)) (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a288309.main := by
  have I n : iter (n + 1) = step (iter n) := Function.iterate_succ_apply' _ _ _
  have P n : (∀ d ∈ iter n, d ≤ 1) ∧ ∃ t, iter n = 0 :: 0 :: t := by
    induction n with
    | zero => exact ⟨by simp [iter], [], rfl⟩
    | succ n ih =>
      obtain ⟨hb, t, ht⟩ := ih
      exact ⟨I n ▸ (scan _ hb).1, 1 :: 0 :: step t, by rw [I, ht]; rfl⟩
  have E n : (iter (n + 1)).count 0 = (iter n).count 0 + (iter n).count 1 + pairs (iter n) ∧
      (iter (n + 1)).count 1 = 2 * (iter n).count 1 + pairs (iter n) ∧
      pairs (iter (n + 1)) + pairs (iter n) = (iter n).count 0 ∧
      (iter n).length = (iter n).count 0 + (iter n).count 1 := by
    obtain ⟨hb, t, ht⟩ := P n
    obtain ⟨-, hl, hz, ho, hp⟩ := scan _ hb
    have : pairs (0 :: step (iter n)) = pairs (step (iter n)) := by rw [ht]; rfl
    rw [I]
    omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 | 1 | 2 => rfl
    | k + 3 =>
      have := E k; have := E (k + 1); have := E (k + 2); have := E (k + 3)
      rw [A, ← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega)]
      simp only [add_assoc, Nat.reduceAdd] at *
      omega
