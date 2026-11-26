import FormalConjectures.ErdosProblems.«954»

-- Problem: Erdős Problem 954 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/954.lean:106 (declaration Erdos954.erdos_954.variants.lower)
-- Credit: @danhab05 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Idea. Write N(x) for the number of pairs counted by `solutionCount x`. If N(x) < x, then for every
-- stage m ≤ x the stage count is also below x, so x lies in the set whose least element defines the
-- next term: every term a_1, ..., a_x is at most x. The x pairs (0, j) with 1 ≤ j ≤ x are then all
-- counted (a_0 = 0), so N(x) ≥ x after all.

open Erdos954

/-- A stage copies every earlier value: only the index `k + 2` is new at stage `k + 1`. -/
lemma OMA.rosenAux_succ_of_ne (k i : ℕ) (h : i ≠ k + 2) : rosenAux (k + 1) i = rosenAux k i := by
  show (if i = k + 2 then _ else rosenAux k i) = rosenAux k i
  rw [if_neg h]

/-- The value appended at stage `k + 1`. -/
lemma OMA.rosenAux_succ_self (k : ℕ) :
    rosenAux (k + 1) (k + 2) = sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} := by
  show (if k + 2 = k + 2 then _ else rosenAux k (k + 2)) = _
  rw [if_pos rfl]

/-- Stage `k` already holds the final values of the sequence at every index `i ≤ k + 1`. -/
lemma OMA.rosenAux_stable : ∀ k i : ℕ, i ≤ k + 1 → rosenAux k i = rosen i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · rfl
    · show rosenAux 0 1 = rosenAux (0 + 1) 1
      rw [OMA.rosenAux_succ_of_ne 0 1 (by omega)]
  | succ k ih =>
    intro i hi
    by_cases h : i = k + 2
    · subst h
      show rosenAux (k + 1) (k + 2) = rosenAux (k + 1 + 1) (k + 2)
      rw [OMA.rosenAux_succ_of_ne (k + 1) (k + 2) (by omega)]
    · rw [OMA.rosenAux_succ_of_ne k i h]
      exact ih i (by omega)

/-- The defining minimum of the sequence, stated with the sequence itself. -/
lemma OMA.rosen_add_two (k : ℕ) :
    rosen (k + 2) = sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} := by
  rw [← OMA.rosenAux_stable (k + 1) (k + 2) (by omega)]
  exact OMA.rosenAux_succ_self k

/-- `pairCount a m n` only reads the values of `a` at indices `≤ m`. -/
lemma OMA.pairCount_congr {a b : ℕ → ℕ} {m : ℕ} (h : ∀ i, i ≤ m → a i = b i) (n : ℕ) :
    pairCount a m n = pairCount b m n := by
  unfold pairCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  rw [h p.1 (by omega), h p.2 (by omega)]

/-- Allowing more indices can only add pairs. -/
lemma OMA.pairCount_mono (a : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') (n : ℕ) :
    pairCount a m n ≤ pairCount a m' n := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hp.2⟩

/-- If `a 0 = 0` and `a 1, …, a x` are all at most `x`, the `x` pairs `(0, j)` are counted. -/
lemma OMA.le_pairCount (a : ℕ → ℕ) (x : ℕ) (h0 : a 0 = 0)
    (h : ∀ j, 1 ≤ j → j ≤ x → a j ≤ x) : x ≤ pairCount a x x := by
  unfold pairCount
  have hsub : (Finset.Icc 1 x).image (fun j : ℕ => ((0 : ℕ), j)) ⊆
      (Finset.range (x + 1) ×ˢ Finset.range (x + 1)).filter
        (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ a p.1 + a p.2 ≤ x) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    rw [Finset.mem_Icc] at hj
    refine Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩, ?_, ?_, ?_⟩
    · show 0 < x + 1
      omega
    · show j < x + 1
      omega
    · show 0 ≤ j
      omega
    · show 1 ≤ j
      exact hj.1
    · show a 0 + a j ≤ x
      rw [h0, Nat.zero_add]
      exact h j hj.1 hj.2
  have hcard : ((Finset.Icc 1 x).image (fun j : ℕ => ((0 : ℕ), j))).card = x := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro u v huv
      exact (Prod.mk.inj huv).2
  calc x = ((Finset.Icc 1 x).image (fun j : ℕ => ((0 : ℕ), j))).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem OMA.solution : type_of% @Erdos954.erdos_954.variants.lower := by
  intro x
  by_contra hlt
  have hx : pairCount rosen x x < x := Nat.lt_of_not_le hlt
  have key : ∀ j, 1 ≤ j → j ≤ x → rosen j ≤ x := by
    intro j hj1 hjx
    by_cases hj : j = 1
    · subst hj
      have h1 : rosen 1 = 1 := rosen_one
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      rw [OMA.rosen_add_two k]
      apply Nat.sInf_le
      show pairCount (rosenAux k) (k + 1) x < x
      calc pairCount (rosenAux k) (k + 1) x
          = pairCount rosen (k + 1) x :=
            OMA.pairCount_congr (fun i hi => OMA.rosenAux_stable k i hi) x
        _ ≤ pairCount rosen x x := OMA.pairCount_mono rosen (by omega) x
        _ < x := hx
  exact absurd (OMA.le_pairCount rosen x rosen_zero key) (Nat.not_le_of_lt hx)
