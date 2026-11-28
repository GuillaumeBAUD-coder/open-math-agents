import OMAStatements.S_oeis_a233252

/-!
Proof of Barker's conjectures for A233252 (n X 4 arrays over 0..5 with no clash between
horizontal or antidiagonal neighbours, top left entry 0, 1 appearing before 2, 3 and 4, and 2
appearing before 3 in row-major order).

Rows. Appending a row `r` below an array `p` with `n` rows (`snocA233252`), the result is good
iff `p` is good and `r` satisfies `RowOKA233252 p r` (`goodSnocA233252`): no horizontal clash in
`r`, no antidiagonal clash between the last row of `p` and `r`, `r 0 = 0` when `n = 0`, and
every 2, 3, 4 (resp. 3) of `r` comes after a 1 (resp. a 2) of `p` or an earlier one of `r`.
The cells before a cell of `p` lie in `p`, so the conditions on `p` do not change.

Classes. Two entries clash iff they have the same class `0 ↦ 0, 5 ↦ 0, 1 ↦ 1, 4 ↦ 1,
2 ↦ 2, 3 ↦ 2` (`clashIffA233252`). In a good array with at least one row the entry in row 0,
column 1 is 1 (`has1A233252`), so later 2s and 4s are always allowed, and a 3 needs a 2 before
it. Hence for such `p` the row condition only depends on the classes of the entries in columns
1, 2, 3 of the last row of `p` and on whether a 2 has appeared (`rowOKIffA233252`). These states
satisfy `ReachA233252` (`reachA233252`): neighbouring classes differ, and when no 2 has
appeared there is no 3 either, so no class 2.

Types. The type of a good array is 0 if no 2 has appeared, and otherwise 1 or 2 according as
the classes of its last row in columns 1 and 3 agree or not (`TA233252`). For each of the 14
reachable states, the number of new rows giving each type depends only on the type of the
state, by the transfer matrix `WA233252 = [[16, 32, 40], [0, 80, 80], [0, 64, 64]]`
(`tableA233252`, a finite check by `decide +kernel` over all rows); the first row gives the
types with multiplicities 4, 2, 4 (`baseTableA233252`). So the numbers `cntA233252 m τ` of good
arrays with `m + 1` rows and type `τ` satisfy `cnt 0 = (4, 2, 4)` and
`cnt (m + 1) τ = Sum_τ' cnt m τ' * W τ' τ` (`cntSuccA233252`).

Closed form. By induction, `cnt m 0 = 4 * 16^m`, `cnt m 1 = 4 * 144^m - 2 * 16^m` and
`cnt m 2 = 4 * 144^m`, so `a (m + 1) = 8 * 144^m + 2 * 16^m = 2^(4m+1) (4 * 9^(m+1) + 9) / 9`.
The generating function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a233252 Finset

/-- Some cell of the array `p` has the value `v`. -/
def HasA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (v : Fin 6) : Prop := ∃ i j, p i j = v

/-- The order condition for the new last row `r` below `p`: every `v` of `r` comes after a `u`
of `p` or after a `u` earlier in `r`. -/
def RowABA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) (u v : Fin 6) : Prop :=
  ∀ j : Fin 4, r j = v → HasA233252 p u ∨ ∃ j' : Fin 4, j' < j ∧ r j' = u

/-- The conditions on a new last row `r` below an array `p` with `n` rows. -/
def RowOKA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) : Prop :=
  (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (r j) (r ⟨j.val + 1, hj⟩)) ∧
  (∀ i : Fin n, i.val + 1 = n → ∀ (j : Fin 4) (hj : j.val + 1 < 4),
    ¬ Clash (p i ⟨j.val + 1, hj⟩) (r j)) ∧
  (n = 0 → r 0 = 0) ∧
  RowABA233252 p r 1 2 ∧ RowABA233252 p r 1 3 ∧ RowABA233252 p r 1 4 ∧ RowABA233252 p r 2 3

section snoc

variable {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6)

/-- Appending the row `r` to `p`. -/
abbrev snocA233252 : Fin (n + 1) → Fin 4 → Fin 6 := Fin.snoc p r

theorem snocLtA233252 (k : ℕ) (h : k < n + 1) (hk : k < n) :
    snocA233252 p r ⟨k, h⟩ = p ⟨k, hk⟩ :=
  Fin.snoc_castSucc (α := fun _ => Fin 4 → Fin 6) (i := ⟨k, hk⟩) (p := p) (x := r)

theorem snocEqA233252 (k : ℕ) (h : k < n + 1) (hk : k = n) : snocA233252 p r ⟨k, h⟩ = r := by
  subst hk
  exact Fin.snoc_last (α := fun _ => Fin 4 → Fin 6) (p := p) (x := r)

theorem snocCastA233252 (i : Fin n) : snocA233252 p r i.castSucc = p i :=
  Fin.snoc_castSucc (α := fun _ => Fin 4 → Fin 6) (i := i) (p := p) (x := r)

theorem snocLastA233252 : snocA233252 p r (Fin.last n) = r :=
  Fin.snoc_last (α := fun _ => Fin 4 → Fin 6) (p := p) (x := r)

theorem horizSnocA233252 :
    (∀ (i : Fin (n + 1)) (j : Fin 4) (hj : j.val + 1 < 4),
      ¬ Clash (snocA233252 p r i j) (snocA233252 p r i ⟨j.val + 1, hj⟩)) ↔
    (∀ (i : Fin n) (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (p i j) (p i ⟨j.val + 1, hj⟩)) ∧
    (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (r j) (r ⟨j.val + 1, hj⟩)) := by
  constructor
  · intro h
    refine ⟨fun i j hj => ?_, fun j hj => ?_⟩
    · have := h i.castSucc j hj
      rwa [snocCastA233252] at this
    · have := h (Fin.last n) j hj
      rwa [snocLastA233252] at this
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => intro j hj; rw [snocLastA233252]; exact h2 j hj
    | cast i => intro j hj; rw [snocCastA233252]; exact h1 i j hj

theorem antiSnocA233252 :
    (∀ (i : Fin (n + 1)) (j : Fin 4) (hi : i.val + 1 < n + 1) (hj : j.val + 1 < 4),
      ¬ Clash (snocA233252 p r i ⟨j.val + 1, hj⟩) (snocA233252 p r ⟨i.val + 1, hi⟩ j)) ↔
    (∀ (i : Fin n) (j : Fin 4) (hi : i.val + 1 < n) (hj : j.val + 1 < 4),
      ¬ Clash (p i ⟨j.val + 1, hj⟩) (p ⟨i.val + 1, hi⟩ j)) ∧
    (∀ i : Fin n, i.val + 1 = n → ∀ (j : Fin 4) (hj : j.val + 1 < 4),
      ¬ Clash (p i ⟨j.val + 1, hj⟩) (r j)) := by
  constructor
  · intro h
    refine ⟨fun i j hi hj => ?_, fun i hi j hj => ?_⟩
    · have := h i.castSucc j (by rw [Fin.val_castSucc]; omega) hj
      rwa [snocCastA233252, snocLtA233252 p r (i.castSucc.val + 1) _ hi] at this
    · have := h i.castSucc j (by rw [Fin.val_castSucc]; omega) hj
      rwa [snocCastA233252, snocEqA233252 p r (i.castSucc.val + 1) _ hi] at this
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => intro j hi; simp at hi
    | cast i =>
      intro j hi hj
      rw [snocCastA233252]
      by_cases hlt : i.val + 1 < n
      · rw [snocLtA233252 p r (i.castSucc.val + 1) _ hlt]
        exact h1 i j hlt hj
      · rw [snocEqA233252 p r (i.castSucc.val + 1) _ (by rw [Fin.val_castSucc]; omega)]
        exact h2 i (by omega) j hj

theorem topSnocA233252 :
    (∀ h : 0 < n + 1, snocA233252 p r ⟨0, h⟩ 0 = 0) ↔
    (∀ h : 0 < n, p ⟨0, h⟩ 0 = 0) ∧ (n = 0 → r 0 = 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    constructor
    · intro h
      refine ⟨fun h' => absurd h' (lt_irrefl 0), fun _ => ?_⟩
      have := h (by omega)
      rwa [snocEqA233252 p r 0 _ rfl] at this
    · intro h h'
      rw [snocEqA233252 p r 0 h' rfl]
      exact h.2 rfl
  · constructor
    · intro h
      refine ⟨fun h' => ?_, fun h' => absurd h' (by omega)⟩
      have := h (by omega)
      rwa [snocLtA233252 p r 0 _ h'] at this
    · intro h h'
      rw [snocLtA233252 p r 0 h' hn]
      exact h.1 hn

theorem hasSnocA233252 (v : Fin 6) :
    HasA233252 (snocA233252 p r) v ↔ HasA233252 p v ∨ ∃ j, r j = v := by
  constructor
  · rintro ⟨i, j, h⟩
    induction i using Fin.lastCases with
    | last => rw [snocLastA233252] at h; exact Or.inr ⟨j, h⟩
    | cast i => rw [snocCastA233252] at h; exact Or.inl ⟨i, j, h⟩
  · rintro (⟨i, j, h⟩ | ⟨j, h⟩)
    · exact ⟨i.castSucc, j, by rw [snocCastA233252]; exact h⟩
    · exact ⟨Fin.last n, j, by rw [snocLastA233252]; exact h⟩

theorem abSnocA233252 (u v : Fin 6) :
    AppearsBefore (snocA233252 p r) u v ↔ AppearsBefore p u v ∧ RowABA233252 p r u v := by
  constructor
  · intro h
    refine ⟨fun i j hv => ?_, fun j hv => ?_⟩
    · obtain ⟨i', j', hb, hu⟩ := h i.castSucc j (by rw [snocCastA233252]; exact hv)
      induction i' using Fin.lastCases with
      | last =>
        exfalso
        rcases hb with hb | ⟨hb, -⟩
        · exact absurd hb (not_lt.mpr (Fin.castSucc_lt_last i).le)
        · exact Fin.castSucc_ne_last i hb.symm
      | cast i' =>
        rw [snocCastA233252] at hu
        refine ⟨i', j', ?_, hu⟩
        rcases hb with hb | ⟨hb, hj⟩
        · exact Or.inl (Fin.castSucc_lt_castSucc_iff.mp hb)
        · exact Or.inr ⟨Fin.castSucc_inj.mp hb, hj⟩
    · obtain ⟨i', j', hb, hu⟩ := h (Fin.last n) j (by rw [snocLastA233252]; exact hv)
      induction i' using Fin.lastCases with
      | last =>
        rw [snocLastA233252] at hu
        rcases hb with hb | ⟨-, hj⟩
        · exact absurd hb (lt_irrefl _)
        · exact Or.inr ⟨j', hj, hu⟩
      | cast i' =>
        rw [snocCastA233252] at hu
        exact Or.inl ⟨i', j', hu⟩
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last =>
      intro j hv
      rw [snocLastA233252] at hv
      rcases h2 j hv with ⟨i', j', hu⟩ | ⟨j', hj, hu⟩
      · exact ⟨i'.castSucc, j', Or.inl (Fin.castSucc_lt_last i'), by rw [snocCastA233252]; exact hu⟩
      · exact ⟨Fin.last n, j', Or.inr ⟨rfl, hj⟩, by rw [snocLastA233252]; exact hu⟩
    | cast i =>
      intro j hv
      rw [snocCastA233252] at hv
      obtain ⟨i', j', hb, hu⟩ := h1 i j hv
      refine ⟨i'.castSucc, j', ?_, by rw [snocCastA233252]; exact hu⟩
      rcases hb with hb | ⟨hb, hj⟩
      · exact Or.inl (Fin.castSucc_lt_castSucc_iff.mpr hb)
      · exact Or.inr ⟨by rw [hb], hj⟩

theorem goodSnocA233252 : Good (snocA233252 p r) ↔ Good p ∧ RowOKA233252 p r := by
  unfold Good RowOKA233252
  rw [horizSnocA233252, antiSnocA233252, topSnocA233252, abSnocA233252, abSnocA233252,
    abSnocA233252, abSnocA233252]
  constructor
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨h3, h3'⟩, ⟨h4, h4'⟩, ⟨h5, h5'⟩, ⟨h6, h6'⟩, ⟨h7, h7'⟩⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, ⟨h1', h2', h3', h4', h5', h6', h7'⟩⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, ⟨h1', h2', h3', h4', h5', h6', h7'⟩⟩
    exact ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨h3, h3'⟩, ⟨h4, h4'⟩, ⟨h5, h5'⟩, ⟨h6, h6'⟩, ⟨h7, h7'⟩⟩

end snoc

/-! ### Decidability, classes, explicit forms -/

instance decClashA233252 (u v : Fin 6) : Decidable (Clash u v) := by
  unfold Clash; infer_instance

instance decHasA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (v : Fin 6) :
    Decidable (HasA233252 p v) := by
  unfold HasA233252; infer_instance

instance decABA233252 {n : ℕ} (x : Fin n → Fin 4 → Fin 6) (u v : Fin 6) :
    Decidable (AppearsBefore x u v) := by
  unfold AppearsBefore Before; infer_instance

instance decGoodA233252 {n : ℕ} (x : Fin n → Fin 4 → Fin 6) : Decidable (Good x) := by
  unfold Good; infer_instance

instance decRowABA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) (u v : Fin 6) :
    Decidable (RowABA233252 p r u v) := by
  unfold RowABA233252; infer_instance

instance decRowOKA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) :
    Decidable (RowOKA233252 p r) := by
  unfold RowOKA233252; infer_instance

/-- The class of an entry: 0 for 0 and 5, 1 for 1 and 4, 2 for 2 and 3. -/
def clsA233252 : Fin 6 → Fin 3 := ![0, 1, 2, 2, 1, 0]

theorem clashIffA233252 : ∀ u v : Fin 6, Clash u v ↔ clsA233252 u = clsA233252 v := by
  decide

theorem cls2IffA233252 : ∀ v : Fin 6, clsA233252 v = 2 ↔ v = 2 ∨ v = 3 := by
  decide

theorem horiz4A233252 (r : Fin 4 → Fin 6) :
    (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (r j) (r ⟨j.val + 1, hj⟩)) ↔
      ¬ Clash (r 0) (r 1) ∧ ¬ Clash (r 1) (r 2) ∧ ¬ Clash (r 2) (r 3) := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h1, h2⟩ j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact absurd hj (by decide)

theorem cross4A233252 (q r : Fin 4 → Fin 6) :
    (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (q ⟨j.val + 1, hj⟩) (r j)) ↔
      ¬ Clash (q 1) (r 0) ∧ ¬ Clash (q 2) (r 1) ∧ ¬ Clash (q 3) (r 2) := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h1, h2⟩ j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact absurd hj (by decide)

theorem forall4A233252 (P : Fin 4 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem exists4A233252 (P : Fin 4 → Prop) : (∃ j, P j) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 := by
  constructor
  · rintro ⟨j, h⟩
    fin_cases j
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

theorem rowABIffA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) (u v : Fin 6) :
    RowABA233252 p r u v ↔
      (r 0 = v → HasA233252 p u) ∧ (r 1 = v → HasA233252 p u ∨ r 0 = u) ∧
      (r 2 = v → HasA233252 p u ∨ r 0 = u ∨ r 1 = u) ∧
      (r 3 = v → HasA233252 p u ∨ r 0 = u ∨ r 1 = u ∨ r 2 = u) := by
  unfold RowABA233252
  rw [forall4A233252]
  have e0 : (∃ j' : Fin 4, j' < 0 ∧ r j' = u) ↔ False := by
    constructor
    · rintro ⟨j', hj', -⟩
      exact absurd hj' (Fin.not_lt_zero j')
    · exact False.elim
  have e1 : (∃ j' : Fin 4, j' < 1 ∧ r j' = u) ↔ r 0 = u := by
    constructor
    · rintro ⟨j', hj', h⟩
      fin_cases j'
      · exact h
      all_goals exact absurd hj' (by decide)
    · intro h
      exact ⟨0, by decide, h⟩
  have e2 : (∃ j' : Fin 4, j' < 2 ∧ r j' = u) ↔ r 0 = u ∨ r 1 = u := by
    constructor
    · rintro ⟨j', hj', h⟩
      fin_cases j'
      · exact Or.inl h
      · exact Or.inr h
      all_goals exact absurd hj' (by decide)
    · rintro (h | h)
      · exact ⟨0, by decide, h⟩
      · exact ⟨1, by decide, h⟩
  have e3 : (∃ j' : Fin 4, j' < 3 ∧ r j' = u) ↔ r 0 = u ∨ r 1 = u ∨ r 2 = u := by
    constructor
    · rintro ⟨j', hj', h⟩
      fin_cases j'
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hj' (by decide)
    · rintro (h | h | h)
      · exact ⟨0, by decide, h⟩
      · exact ⟨1, by decide, h⟩
      · exact ⟨2, by decide, h⟩
  rw [e0, e1, e2, e3, or_false]

/-- The rows of an array with one row less, and the sum over rows as four sums over entries. -/
def rowEquivA233252 : (Fin 4 → Fin 6) ≃ Fin 6 × Fin 6 × Fin 6 × Fin 6 where
  toFun r := (r 0, r 1, r 2, r 3)
  invFun t := ![t.1, t.2.1, t.2.2.1, t.2.2.2]
  left_inv r := by
    funext j
    fin_cases j <;> rfl
  right_inv t := rfl

theorem sum4A233252 (F : Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℕ) :
    ∑ r : Fin 4 → Fin 6, F (r 0) (r 1) (r 2) (r 3) = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  rw [Fintype.sum_equiv rowEquivA233252 (fun r => F (r 0) (r 1) (r 2) (r 3))
    (fun t => F t.1 t.2.1 t.2.2.1 t.2.2.2) (fun r => rfl)]
  simp only [Fintype.sum_prod_type]

/-! ### Types of arrays and the transfer tables -/

/-- The conditions on a new row `a b c d` below a row whose entries in columns 1, 2, 3 have the
classes `c1 c2 c3`, in an array where a 1 has appeared and `f` says whether a 2 has appeared. -/
def Q4A233252 (c1 c2 c3 : Fin 3) (f : Bool) (a b c d : Fin 6) : Prop :=
  ¬ Clash a b ∧ ¬ Clash b c ∧ ¬ Clash c d ∧
  c1 ≠ clsA233252 a ∧ c2 ≠ clsA233252 b ∧ c3 ≠ clsA233252 c ∧
  (a = 3 → f = true) ∧ (b = 3 → f = true ∨ a = 2) ∧ (c = 3 → f = true ∨ a = 2 ∨ b = 2) ∧
  (d = 3 → f = true ∨ a = 2 ∨ b = 2 ∨ c = 2)

instance decQ4A233252 (c1 c2 c3 : Fin 3) (f : Bool) (a b c d : Fin 6) :
    Decidable (Q4A233252 c1 c2 c3 f a b c d) := by
  unfold Q4A233252; infer_instance

/-- The order condition between the values `u` and `v` inside a first row `a b c d`. -/
def O0A233252 (u v a b c d : Fin 6) : Prop :=
  (a = v → False) ∧ (b = v → False ∨ a = u) ∧ (c = v → False ∨ a = u ∨ b = u) ∧
  (d = v → False ∨ a = u ∨ b = u ∨ c = u)

/-- The conditions on a first row `a b c d`. -/
def Q0A233252 (a b c d : Fin 6) : Prop :=
  ¬ Clash a b ∧ ¬ Clash b c ∧ ¬ Clash c d ∧ a = 0 ∧
  O0A233252 1 2 a b c d ∧ O0A233252 1 3 a b c d ∧ O0A233252 1 4 a b c d ∧ O0A233252 2 3 a b c d

instance decO0A233252 (u v a b c d : Fin 6) : Decidable (O0A233252 u v a b c d) := by
  unfold O0A233252; infer_instance

instance decQ0A233252 (a b c d : Fin 6) : Decidable (Q0A233252 a b c d) := by
  unfold Q0A233252; infer_instance

/-- Whether a 2 has appeared, after the row `a b c d` is added (`f`: before). -/
def newFlagA233252 (f : Bool) (a b c d : Fin 6) : Bool :=
  f || decide (a = 2 ∨ b = 2 ∨ c = 2 ∨ d = 2)

/-- The type of an array: 0 if no 2 has appeared (`f = false`); otherwise 1 if the classes `c1`,
`c3` of the entries in columns 1 and 3 of its last row agree, and 2 if not. -/
def typA233252 (f : Bool) (c1 c3 : Fin 3) : Fin 3 := if f then (if c1 = c3 then 1 else 2) else 0

/-- The number of new rows below a row of classes `c1 c2 c3` (flag `f`) giving the type `τ`. -/
def WkA233252 (c1 c2 c3 : Fin 3) (f : Bool) (τ : Fin 3) : ℕ :=
  ∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6,
    if Q4A233252 c1 c2 c3 f a b c d ∧
      typA233252 (newFlagA233252 f a b c d) (clsA233252 b) (clsA233252 d) = τ then 1 else 0

/-- The transfer matrix between types. -/
def WA233252 : Fin 3 → Fin 3 → ℕ := ![![16, 32, 40], ![0, 80, 80], ![0, 64, 64]]

/-- The states that occur: neighbouring classes differ, and without a 2 there is no class 2. -/
def ReachA233252 (c1 c2 c3 : Fin 3) (f : Bool) : Prop :=
  c1 ≠ c2 ∧ c2 ≠ c3 ∧ (f = false → c1 ≠ 2 ∧ c2 ≠ 2 ∧ c3 ≠ 2)

instance decReachA233252 (c1 c2 c3 : Fin 3) (f : Bool) :
    Decidable (ReachA233252 c1 c2 c3 f) := by
  unfold ReachA233252; infer_instance

theorem tableA233252 : ∀ c1 c2 c3 : Fin 3, ∀ f : Bool, ReachA233252 c1 c2 c3 f →
    ∀ τ : Fin 3, WkA233252 c1 c2 c3 f τ = WA233252 (typA233252 f c1 c3) τ := by
  decide +kernel

theorem baseTableA233252 : ∀ τ : Fin 3,
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6,
      if Q0A233252 a b c d ∧
        typA233252 (newFlagA233252 false a b c d) (clsA233252 b) (clsA233252 d) = τ
      then 1 else 0) = ![4, 2, 4] τ := by
  decide +kernel

/-! ### Flags, types and the facts about good arrays -/

/-- Whether some entry of `x` is 2. -/
def flagA233252 {n : ℕ} (x : Fin n → Fin 4 → Fin 6) : Bool := decide (HasA233252 x 2)

/-- The type of an array with at least one row. -/
def TA233252 {m : ℕ} (x : Fin (m + 1) → Fin 4 → Fin 6) : Fin 3 :=
  typA233252 (flagA233252 x) (clsA233252 (x (Fin.last m) 1)) (clsA233252 (x (Fin.last m) 3))

theorem flagSnocA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) :
    flagA233252 (snocA233252 p r) = newFlagA233252 (flagA233252 p) (r 0) (r 1) (r 2) (r 3) := by
  unfold flagA233252 newFlagA233252
  rw [← Bool.decide_or]
  exact decide_eq_decide.mpr (by rw [hasSnocA233252, exists4A233252])

theorem TSnocA233252 {n : ℕ} (p : Fin n → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) :
    TA233252 (snocA233252 p r) =
      typA233252 (newFlagA233252 (flagA233252 p) (r 0) (r 1) (r 2) (r 3)) (clsA233252 (r 1))
        (clsA233252 (r 3)) := by
  unfold TA233252
  rw [flagSnocA233252, snocLastA233252]

/-- In a good array with at least one row, a 1 has appeared: the entry in row 0, column 1. -/
theorem has1A233252 {m : ℕ} (p : Fin (m + 1) → Fin 4 → Fin 6) (hp : Good p) :
    HasA233252 p 1 := by
  obtain ⟨hh, -, ht, h12, h13, h14, -⟩ := hp
  set z : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩ with hz
  have h00 : p z 0 = 0 := ht (Nat.succ_pos m)
  have hc : ¬ Clash (p z 0) (p z 1) := hh z 0 (by decide)
  rw [h00] at hc
  have early : ∀ (i' : Fin (m + 1)) (j' : Fin 4), Before i' j' z 1 → p i' j' ≠ 1 := by
    rintro i' j' (hb | ⟨rfl, hj⟩)
    · exact absurd hb (Fin.not_lt_zero i')
    · have : j' = 0 := by
        fin_cases j'
        · rfl
        all_goals exact absurd hj (by decide)
      rw [this, h00]
      decide
  refine ⟨z, 1, ?_⟩
  by_contra hne
  have hv : p z 1 = 2 ∨ p z 1 = 3 ∨ p z 1 = 4 := by
    revert hc hne
    generalize p z 1 = v
    revert v
    decide
  rcases hv with hv | hv | hv
  · obtain ⟨i', j', hb, hu⟩ := h12 z 1 hv
    exact early i' j' hb hu
  · obtain ⟨i', j', hb, hu⟩ := h13 z 1 hv
    exact early i' j' hb hu
  · obtain ⟨i', j', hb, hu⟩ := h14 z 1 hv
    exact early i' j' hb hu

theorem reachA233252 {m : ℕ} (p : Fin (m + 1) → Fin 4 → Fin 6) (hp : Good p) :
    ReachA233252 (clsA233252 (p (Fin.last m) 1)) (clsA233252 (p (Fin.last m) 2))
      (clsA233252 (p (Fin.last m) 3)) (flagA233252 p) := by
  obtain ⟨hh, -, -, -, -, -, h23⟩ := hp
  refine ⟨fun h => hh (Fin.last m) 1 (by decide) ((clashIffA233252 _ _).mpr h),
    fun h => hh (Fin.last m) 2 (by decide) ((clashIffA233252 _ _).mpr h), fun hf => ?_⟩
  have no2 : ∀ i j, p i j ≠ 2 := by
    intro i j h
    have h2 : HasA233252 p 2 := ⟨i, j, h⟩
    simp [flagA233252, h2] at hf
  have no3 : ∀ i j, p i j ≠ 3 := by
    intro i j h
    obtain ⟨i', j', -, h'⟩ := h23 i j h
    exact no2 i' j' h'
  refine ⟨?_, ?_, ?_⟩ <;> rw [Ne, cls2IffA233252] <;> exact fun h => h.elim (no2 _ _) (no3 _ _)

theorem lastIffA233252 {m : ℕ} (P : Fin (m + 1) → Prop) :
    (∀ i : Fin (m + 1), i.val + 1 = m + 1 → P i) ↔ P (Fin.last m) := by
  constructor
  · intro h
    exact h _ (by simp)
  · intro h i hi
    have : i = Fin.last m := Fin.ext (by simp; omega)
    rw [this]
    exact h

theorem rowOKIffA233252 {m : ℕ} (p : Fin (m + 1) → Fin 4 → Fin 6) (h1 : HasA233252 p 1)
    (r : Fin 4 → Fin 6) :
    RowOKA233252 p r ↔ Q4A233252 (clsA233252 (p (Fin.last m) 1)) (clsA233252 (p (Fin.last m) 2))
      (clsA233252 (p (Fin.last m) 3)) (flagA233252 p) (r 0) (r 1) (r 2) (r 3) := by
  have e2 : HasA233252 p 2 ↔ flagA233252 p = true := by
    unfold flagA233252
    rw [decide_eq_true_iff]
  unfold RowOKA233252 Q4A233252
  rw [horiz4A233252, lastIffA233252 (fun i => ∀ (j : Fin 4) (hj : j.val + 1 < 4),
    ¬ Clash (p i ⟨j.val + 1, hj⟩) (r j)), cross4A233252, rowABIffA233252, rowABIffA233252,
    rowABIffA233252, rowABIffA233252, e2, clashIffA233252 (p (Fin.last m) 1),
    clashIffA233252 (p (Fin.last m) 2), clashIffA233252 (p (Fin.last m) 3)]
  constructor
  · rintro ⟨⟨h0, h1', h2⟩, ⟨c0, c1, c2⟩, -, -, -, -, ho⟩
    exact ⟨h0, h1', h2, c0, c1, c2, ho⟩
  · rintro ⟨h0, h1', h2, c0, c1, c2, ho⟩
    exact ⟨⟨h0, h1', h2⟩, ⟨c0, c1, c2⟩, fun h => absurd h (Nat.succ_ne_zero m),
      ⟨fun _ => h1, fun _ => Or.inl h1, fun _ => Or.inl h1, fun _ => Or.inl h1⟩,
      ⟨fun _ => h1, fun _ => Or.inl h1, fun _ => Or.inl h1, fun _ => Or.inl h1⟩,
      ⟨fun _ => h1, fun _ => Or.inl h1, fun _ => Or.inl h1, fun _ => Or.inl h1⟩, ho⟩

theorem rowOKZeroA233252 (p : Fin 0 → Fin 4 → Fin 6) (r : Fin 4 → Fin 6) :
    RowOKA233252 p r ↔ Q0A233252 (r 0) (r 1) (r 2) (r 3) := by
  have e : ∀ u, HasA233252 p u ↔ False := fun u =>
    ⟨fun ⟨i, _, _⟩ => i.elim0, False.elim⟩
  unfold RowOKA233252 Q0A233252 O0A233252
  rw [horiz4A233252, rowABIffA233252, rowABIffA233252, rowABIffA233252, rowABIffA233252, e, e]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, -, ht, ho⟩
    exact ⟨h0, h1, h2, ht rfl, ho⟩
  · rintro ⟨h0, h1, h2, ht, ho⟩
    exact ⟨⟨h0, h1, h2⟩, fun i => i.elim0, fun _ => ht, ho⟩

/-! ### Counting by types -/

/-- The number of good arrays with `m + 1` rows and type `τ`. -/
noncomputable def cntA233252 (m : ℕ) (τ : Fin 3) : ℕ :=
  ∑ x : Fin (m + 1) → Fin 4 → Fin 6, if Good x ∧ TA233252 x = τ then 1 else 0

theorem aEqA233252 (m : ℕ) : a (m + 1) = ∑ τ : Fin 3, cntA233252 m τ := by
  unfold a cntA233252
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : Good x
  · simp [hx]
  · simp [hx]

/-- Splitting off the last row of the arrays counted by `cntA233252`. -/
theorem splitA233252 (m : ℕ) (G : (Fin (m + 1) → Fin 4 → Fin 6) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 4 → Fin 6, G x =
      ∑ r : Fin 4 → Fin 6, ∑ p : Fin m → Fin 4 → Fin 6, G (snocA233252 p r) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin 4 → Fin 6))
    (fun pr => G (snocA233252 pr.2 pr.1)) G (fun _ => rfl)).symm

theorem cntZeroA233252 (τ : Fin 3) : cntA233252 0 τ = ![4, 2, 4] τ := by
  unfold cntA233252
  rw [splitA233252]
  simp only [Fintype.sum_unique]
  rw [← baseTableA233252 τ]
  refine (Finset.sum_congr rfl fun r _ => ?_).trans
    (sum4A233252 (fun a b c d => if Q0A233252 a b c d ∧
      typA233252 (newFlagA233252 false a b c d) (clsA233252 b) (clsA233252 d) = τ
      then 1 else 0))
  refine if_congr ?_ rfl rfl
  have hf : ∀ p : Fin 0 → Fin 4 → Fin 6, flagA233252 p = false := fun p => by
    unfold flagA233252
    exact decide_eq_false (fun ⟨i, _, _⟩ => i.elim0)
  rw [goodSnocA233252, TSnocA233252, rowOKZeroA233252, hf]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨⟨fun i => i.elim0, fun i => i.elim0,
    fun h' => absurd h' (lt_irrefl 0), fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0⟩, h.1⟩, h.2⟩⟩

theorem rowCountA233252 {m : ℕ} (p : Fin (m + 1) → Fin 4 → Fin 6) (hp : Good p) (τ : Fin 3) :
    (∑ r : Fin 4 → Fin 6, if RowOKA233252 p r ∧
      typA233252 (newFlagA233252 (flagA233252 p) (r 0) (r 1) (r 2) (r 3)) (clsA233252 (r 1))
        (clsA233252 (r 3)) = τ then 1 else 0) = WA233252 (TA233252 p) τ := by
  rw [TA233252, ← tableA233252 _ _ _ _ (reachA233252 p hp) τ]
  refine (Finset.sum_congr rfl fun r _ => ?_).trans
    (sum4A233252 (fun a b c d => if Q4A233252 (clsA233252 (p (Fin.last m) 1))
      (clsA233252 (p (Fin.last m) 2)) (clsA233252 (p (Fin.last m) 3)) (flagA233252 p) a b c d ∧
      typA233252 (newFlagA233252 (flagA233252 p) a b c d) (clsA233252 b) (clsA233252 d) = τ
      then 1 else 0))
  exact if_congr (and_congr_left' (rowOKIffA233252 p (has1A233252 p hp) r)) rfl rfl

theorem cntSuccA233252 (m : ℕ) (τ : Fin 3) :
    cntA233252 (m + 1) τ = ∑ τ' : Fin 3, cntA233252 m τ' * WA233252 τ' τ := by
  have h1 : cntA233252 (m + 1) τ = ∑ p : Fin (m + 1) → Fin 4 → Fin 6,
      if Good p then WA233252 (TA233252 p) τ else 0 := by
    unfold cntA233252
    rw [splitA233252, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : Good p
    · rw [if_pos hp, ← rowCountA233252 p hp τ]
      refine Finset.sum_congr rfl fun r _ => if_congr ?_ rfl rfl
      rw [goodSnocA233252, TSnocA233252]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hp, h.1⟩, h.2⟩⟩
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun r _ => if_neg ?_
      rw [goodSnocA233252]
      exact fun h => hp h.1.1
  rw [h1]
  unfold cntA233252
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : Good p
  · simp [hp]
  · simp [hp]

theorem WvalsA233252 : WA233252 0 0 = 16 ∧ WA233252 1 0 = 0 ∧ WA233252 2 0 = 0 ∧
    WA233252 0 1 = 32 ∧ WA233252 1 1 = 80 ∧ WA233252 2 1 = 64 ∧
    WA233252 0 2 = 40 ∧ WA233252 1 2 = 80 ∧ WA233252 2 2 = 64 := by
  decide

theorem cntClosedA233252 (m : ℕ) :
    cntA233252 m 0 = 4 * 16 ^ m ∧ cntA233252 m 1 + 2 * 16 ^ m = 4 * 144 ^ m ∧
      cntA233252 m 2 = 4 * 144 ^ m := by
  induction m with
  | zero =>
    rw [cntZeroA233252, cntZeroA233252, cntZeroA233252]
    decide
  | succ m ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    obtain ⟨w00, w10, w20, w01, w11, w21, w02, w12, w22⟩ := WvalsA233252
    rw [cntSuccA233252, cntSuccA233252, cntSuccA233252]
    simp only [Fin.sum_univ_three, w00, w10, w20, w01, w11, w21, w02, w12, w22, pow_succ]
    omega

theorem aClosedA233252 (m : ℕ) : a (m + 1) = 8 * 144 ^ m + 2 * 16 ^ m := by
  rw [aEqA233252, Fin.sum_univ_three]
  obtain ⟨h0, h1, h2⟩ := cntClosedA233252 m
  omega

theorem formulaA233252 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 2 ^ (4 * n - 3) * (4 * 9 ^ n + 9) / 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [aClosedA233252, show 4 * (m + 1) - 3 = 4 * m + 1 by omega]
  have h144 : (144 : ℚ) ^ m = 16 ^ m * 9 ^ m := by
    rw [← mul_pow]
    norm_num
  have h16 : (2 : ℚ) ^ (4 * m + 1) = 16 ^ m * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  push_cast
  rw [h144, h16, pow_succ]
  ring

theorem aValsA233252 : a 1 = 10 ∧ a 2 = 1184 := by
  refine ⟨?_, ?_⟩
  · have h := aClosedA233252 0
    norm_num at h
    exact h
  · have h := aClosedA233252 1
    norm_num at h
    exact h

open PowerSeries in
theorem genFunA233252 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 16 * X) * (1 - 144 * X)) = 2 * X * (5 - 208 * X) := by
  set P : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hP
  have key : PowerSeries.mk P * ((1 - 16 * X) * (1 - 144 * X)) =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 160 * (PowerSeries.mk P * X ^ 1) +
        C 2304 * (PowerSeries.mk P * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 : ℚ⟦X⟧) * X * (5 - 208 * X) = C 10 * X ^ 1 - C 416 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have hq : ∀ m : ℕ, (a (m + 1) : ℚ) = 8 * 144 ^ m + 2 * 16 ^ m := fun m => by
    rw [aClosedA233252]
    push_cast
    ring
  obtain ⟨v1, v2⟩ := aValsA233252
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hP, v1, v2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e3 : (a (j + 3) : ℚ) = 8 * 144 ^ (j + 2) + 2 * 16 ^ (j + 2) := hq (j + 2)
    have e2 : (a (j + 2) : ℚ) = 8 * 144 ^ (j + 1) + 2 * 16 ^ (j + 1) := hq (j + 1)
    have e1 : (a (j + 1) : ℚ) = 8 * 144 ^ j + 2 * 16 ^ j := hq j
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega, show ¬ (j + 3 = 1) by omega,
      show ¬ (j + 3 = 2) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false, hP, e1, e2, e3]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a233252.main :=
  ⟨OMA.Helpers.genFunA233252, OMA.Helpers.formulaA233252⟩
