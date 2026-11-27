import FormalConjectures.Paper.CatchUpConjecture

-- Reduction CatchUp.value_of_even_mul_succ_self_div_two.R1 of The Catch-Up game and conjecture
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The conjecture (the game on {1, ..., N} is a draw when T_N is even) splits into two
-- independent guarantees, one per player, both stated after the forced first move:
--   H1: the first player draws by opening with 1. After p1 takes 1, the position is
--       valueAux ((Icc 1 N).erase 1) 0 1 false from the point of view of p2, and p2 cannot win.
--   H2: the second player never loses: whatever x p1 opens with, p2 cannot lose.
-- main unfolds the first move of valueAux, handles N = 0 and combines the two halves through
-- elementary facts about Outcome.best and Outcome.neg.
--
-- Evidence: an exact port of valueAux, evaluated exhaustively for every N with T_N even
-- and N up to 24, shows that opening with 1 always draws (H1) and that no opening wins for
-- the first player (H2). Not every opening draws: some lose for the first player, namely
-- x = 2 for N = 3; x = 3, 4 for N = 4; x = 5, 6, 7 for N = 7; and x = 10 for N = 11.
-- From N = 12 to N = 24, every opening draws.

namespace OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R1

open CatchUp

/-- The first player can force at least a draw by opening with `1`: after that move the
second player, now to move and behind by `1`, cannot force a win. -/
def H1 : Prop :=
  ∀ N : ℕ, Even (N * (N + 1) / 2) → 1 ≤ N →
    CatchUp.valueAux ((Finset.Icc 1 N).erase 1) 0 1 false ≠ CatchUp.Outcome.win

/-- The second player can force at least a draw: whatever number `x` the first player
takes first, the second player, now to move and behind by `x`, does not lose. -/
def H2 : Prop :=
  ∀ N : ℕ, Even (N * (N + 1) / 2) → ∀ x ∈ Finset.Icc 1 N,
    CatchUp.valueAux ((Finset.Icc 1 N).erase x) 0 x false ≠ CatchUp.Outcome.loss

lemma best_ne_loss_aux (os : List Outcome) : ∀ acc : Outcome,
    (acc ≠ .loss ∨ ∃ o ∈ os, o ≠ .loss) →
    os.foldl (fun
      | .win,  _     => .win
      | _,     .win  => .win
      | .draw, _     => .draw
      | _,     .draw => .draw
      | _,     _     => .loss) acc ≠ .loss := by
  induction os with
  | nil => intro acc h; simpa using h
  | cons o os ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨o', ho', hne⟩
    · left; cases acc <;> cases o <;> simp_all
    · simp only [List.mem_cons] at ho'
      rcases ho' with rfl | ho'
      · left; cases acc <;> cases o' <;> simp_all
      · by_cases hx : (match acc, o with
          | .win,  _     => Outcome.win
          | _,     .win  => .win
          | .draw, _     => .draw
          | _,     .draw => .draw
          | _,     _     => .loss) = .loss
        · right; exact ⟨o', ho', hne⟩
        · left; exact hx

lemma best_ne_loss {os : List Outcome} {o : Outcome} (ho : o ∈ os) (hne : o ≠ .loss) :
    Outcome.best os ≠ .loss :=
  best_ne_loss_aux os .loss (Or.inr ⟨o, ho, hne⟩)

lemma best_ne_win_aux (os : List Outcome) : ∀ acc : Outcome, acc ≠ .win →
    (∀ o ∈ os, o ≠ .win) →
    os.foldl (fun
      | .win,  _     => .win
      | _,     .win  => .win
      | .draw, _     => .draw
      | _,     .draw => .draw
      | _,     _     => .loss) acc ≠ .win := by
  induction os with
  | nil => intro acc h _; simpa using h
  | cons o os ih =>
    intro acc hacc hall
    simp only [List.foldl_cons]
    apply ih
    · have := hall o (by simp)
      cases acc <;> cases o <;> simp_all
    · intro o' ho'; exact hall o' (by simp [ho'])

lemma best_ne_win {os : List Outcome} (h : ∀ o ∈ os, o ≠ .win) : Outcome.best os ≠ .win :=
  best_ne_win_aux os .loss (by decide) h

lemma neg_ne_loss {o : Outcome} (h : o ≠ .win) : o.neg ≠ .loss := by
  cases o <;> simp_all [Outcome.neg]

lemma neg_ne_win {o : Outcome} (h : o ≠ .loss) : o.neg ≠ .win := by
  cases o <;> simp_all [Outcome.neg]

lemma value_unfold (S : Finset ℕ) (hS : S ≠ ∅) :
    value S = Outcome.best (S.attach.toList.map (fun x =>
      (valueAux (S.erase x.1) 0 (0 + x.1) false).neg)) := by
  rw [value, valueAux]
  simp [hS]

lemma value_empty : value ∅ = .draw := by
  rw [value, valueAux]; simp

theorem main : H1 → H2 → type_of% @CatchUp.value_of_even_mul_succ_self_div_two := by
  intro h1 h2 N hN
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · have : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
    rw [this]; exact value_empty
  · have hS : Finset.Icc 1 N ≠ ∅ := by
      intro h
      have : (1 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
      simp [h] at this
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
    have a : value (Finset.Icc 1 N) ≠ .loss := by
      rw [value_unfold _ hS]
      refine best_ne_loss (o := (valueAux ((Finset.Icc 1 N).erase 1) 0 (0 + 1) false).neg)
        ?_ ?_
      · rw [List.mem_map]
        exact ⟨⟨1, hmem⟩, by simp, rfl⟩
      · apply neg_ne_loss
        simpa using h1 N hN hpos
    have b : value (Finset.Icc 1 N) ≠ .win := by
      rw [value_unfold _ hS]
      apply best_ne_win
      intro o ho
      rw [List.mem_map] at ho
      obtain ⟨⟨x, hx⟩, _, rfl⟩ := ho
      apply neg_ne_win
      simpa using h2 N hN x hx
    cases h : value (Finset.Icc 1 N) with
    | win => exact absurd h b
    | loss => exact absurd h a
    | draw => rfl

end OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R1
