import OMAStatements.S_oeis_a233163

/-!
Proof of Barker's conjectures for A233163 (n X 3 arrays over 0..7 in which no element is
adjacent to itself or to 7 minus itself, with top left element 0 and the three appearance-order
conditions in row major order).

Rows. Two entries clash when they are equal or sum to 7, that is, when they lie in the same
class of the pairs {0,7}, {1,6}, {2,5}, {3,4} (`clashClass`). The adjacency condition of an
array splits into conditions inside each row (`RowAdm`) and between consecutive rows
(`RowFollows`).

Appending a row (`good_snoc_iff`). For an array `B` with at least one row and a row `s`, the
array `B` followed by `s` is good iff `B` is good, `s` is admissible and compatible with the last
row of `B`, and every entry of `s` lying in one of the three sets is preceded, in `B` or earlier
in `s`, by the required value (`NewOrderOK`). In a good array with at least two rows the top left
2 X 2 block contains all four classes, so the values 1, 2 and 3 all occur
(`values_one_two_three`), and then `NewOrderOK` holds for every new row (`newOrderOK_of_good`).

Transfer. An admissible row is periodic (`EndsMatch`) when its two end entries lie in the same
class. A periodic admissible row has exactly 16 admissible compatible successors, all periodic;
a non-periodic one has exactly 8, none periodic (`succ_count`). Both facts only depend on the
class patterns of the rows: every class pattern is realized by exactly 8 rows
(`card_by_class`), and the class-level facts (2 and 1 successors) are checked by the kernel on
the 64 patterns (`succ_countC`).

Counting. Let `nEndsMatch n` and `nEndsDiffer n` count the good arrays with `n + 2` rows whose
last row is, respectively is not, periodic. Counting by the last row (`card_by_last_row`) gives
`nEndsMatch (n + 1) = 16 nEndsMatch n` and `nEndsDiffer (n + 1) = 8 nEndsDiffer n`; the base
values `nEndsMatch 0 = nEndsDiffer 0 = 4` and `a 1 = 3` are kernel computations over the three
good one-row arrays. Hence `a (n + 2) = 4 16^n + 4 8^n`, which is `8^n (2^(n+2) + 4)`. The
generating function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a233163 Finset

/-! ### Clashing entries and rows -/

/-- Two entries do not clash: they differ and do not sum to 7. -/
def NoClash (u v : Fin 8) : Prop := u ≠ v ∧ (u : ℕ) + v ≠ 7

instance (u v : Fin 8) : Decidable (NoClash u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ (u : ℕ) + v ≠ 7))

/-- A row is admissible: horizontally adjacent entries do not clash. -/
def RowAdm (r : Fin 3 → Fin 8) : Prop := NoClash (r 0) (r 1) ∧ NoClash (r 1) (r 2)

instance (r : Fin 3 → Fin 8) : Decidable (RowAdm r) :=
  inferInstanceAs (Decidable (NoClash (r 0) (r 1) ∧ NoClash (r 1) (r 2)))

/-- The row `s` may follow the row `r`: vertically and diagonally adjacent entries do not
clash. -/
def RowFollows (r s : Fin 3 → Fin 8) : Prop :=
  NoClash (r 0) (s 0) ∧ NoClash (r 0) (s 1) ∧ NoClash (r 1) (s 0) ∧ NoClash (r 1) (s 1) ∧
    NoClash (r 1) (s 2) ∧ NoClash (r 2) (s 1) ∧ NoClash (r 2) (s 2)

instance (r s : Fin 3 → Fin 8) : Decidable (RowFollows r s) :=
  inferInstanceAs (Decidable (NoClash (r 0) (s 0) ∧ NoClash (r 0) (s 1) ∧ NoClash (r 1) (s 0) ∧
    NoClash (r 1) (s 1) ∧ NoClash (r 1) (s 2) ∧ NoClash (r 2) (s 1) ∧ NoClash (r 2) (s 2)))

/-- A row is periodic: its two end entries lie in the same clashing class. -/
def EndsMatch (r : Fin 3 → Fin 8) : Prop := r 2 = r 0 ∨ (r 2 : ℕ) + r 0 = 7

instance (r : Fin 3 → Fin 8) : Decidable (EndsMatch r) :=
  inferInstanceAs (Decidable (r 2 = r 0 ∨ (r 2 : ℕ) + r 0 = 7))

theorem clash_cond_iff : ∀ u v : Fin 8, (v ≠ u ∧ (v : ℕ) ≠ 7 - (u : ℕ)) ↔ NoClash u v := by decide

theorem noClash_comm : ∀ u v : Fin 8, NoClash u v ↔ NoClash v u := by decide

theorem rowFollows_get {r s : Fin 3 → Fin 8} (h : RowFollows r s) :
    ∀ j j' : Fin 3, (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 → NoClash (r j) (s j') := by
  obtain ⟨c00, c01, c10, c11, c12, c21, c22⟩ := h
  intro j j' h1 h2
  fin_cases j <;> fin_cases j' <;> simp_all

theorem rowAdm_get {r : Fin 3 → Fin 8} (h : RowAdm r) :
    ∀ j j' : Fin 3, j ≠ j' → (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 → NoClash (r j) (r j') := by
  obtain ⟨h01, h12⟩ := h
  intro j j' hne h1 h2
  fin_cases j <;> fin_cases j' <;> simp_all [noClash_comm (r 1) (r 0), noClash_comm (r 2) (r 1)]

/-! ### Decidability of the statement's predicates -/

instance (i j i' j' : ℕ) : Decidable (Adj i j i' j') :=
  inferInstanceAs (Decidable ((i, j) ≠ (i', j') ∧ i ≤ i' + 1 ∧ i' ≤ i + 1 ∧ j ≤ j' + 1 ∧
    j' ≤ j + 1))

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 8) (v : Fin 8) (S : Finset (Fin 8)) :
    Decidable (AppearsBefore A v S) :=
  inferInstanceAs (Decidable (∀ (i : Fin n) (j : Fin 3), A i j ∈ S →
    ∃ (i' : Fin n) (j' : Fin 3), pos i' j' < pos i j ∧ A i' j' = v))

/-- The adjacency part of `Good`. -/
def AdjFree {n : ℕ} (A : Fin n → Fin 3 → Fin 8) : Prop :=
  ∀ (i i' : Fin n) (j j' : Fin 3), Adj i j i' j' →
    A i' j' ≠ A i j ∧ (A i' j' : ℕ) ≠ 7 - (A i j : ℕ)

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 8) : Decidable (AdjFree A) :=
  inferInstanceAs (Decidable (∀ (i i' : Fin n) (j j' : Fin 3), Adj i j i' j' →
    A i' j' ≠ A i j ∧ (A i' j' : ℕ) ≠ 7 - (A i j : ℕ)))

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 8) : Decidable (Good A) :=
  inferInstanceAs (Decidable (AdjFree A ∧ (∀ h : 0 < n, A ⟨0, h⟩ 0 = 0) ∧
    AppearsBefore A 1 {2, 3, 4, 5, 6} ∧ AppearsBefore A 2 {3, 4, 5} ∧ AppearsBefore A 3 {4}))

theorem good_iff_parts {n : ℕ} (A : Fin n → Fin 3 → Fin 8) :
    Good A ↔ AdjFree A ∧ (∀ h : 0 < n, A ⟨0, h⟩ 0 = 0) ∧
      AppearsBefore A 1 {2, 3, 4, 5, 6} ∧ AppearsBefore A 2 {3, 4, 5} ∧
        AppearsBefore A 3 {4} := Iff.rfl

theorem rowAdm_of_adjFree {n : ℕ} {A : Fin n → Fin 3 → Fin 8} (h : AdjFree A) (i : Fin n) :
    RowAdm (A i) := by
  refine ⟨(clash_cond_iff _ _).mp (h i i 0 1 ?_), (clash_cond_iff _ _).mp (h i i 1 2 ?_)⟩ <;>
    simp [Adj]

/-! ### Appending a row -/

/-- The new conditions on an appended row `s` coming from the condition that `v` appears
before `S`. -/
def NewAppears {k : ℕ} (B : Fin k → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) (v : Fin 8)
    (S : Finset (Fin 8)) : Prop :=
  ∀ j : Fin 3, s j ∈ S → (∃ (i' : Fin k) (j' : Fin 3), B i' j' = v) ∨
    ∃ j' : Fin 3, (j' : ℕ) < j ∧ s j' = v

instance {k : ℕ} (B : Fin k → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) (v : Fin 8)
    (S : Finset (Fin 8)) : Decidable (NewAppears B s v S) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, s j ∈ S → (∃ (i' : Fin k) (j' : Fin 3), B i' j' = v) ∨
    ∃ j' : Fin 3, (j' : ℕ) < j ∧ s j' = v))

/-- All three new order conditions. -/
def NewOrderOK {k : ℕ} (B : Fin k → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) : Prop :=
  NewAppears B s 1 {2, 3, 4, 5, 6} ∧ NewAppears B s 2 {3, 4, 5} ∧ NewAppears B s 3 {4}

instance {k : ℕ} (B : Fin k → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) : Decidable (NewOrderOK B s) :=
  inferInstanceAs (Decidable (NewAppears B s 1 {2, 3, 4, 5, 6} ∧ NewAppears B s 2 {3, 4, 5} ∧
    NewAppears B s 3 {4}))

theorem appears_snoc {k : ℕ} (B : Fin k → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) (v : Fin 8)
    (S : Finset (Fin 8)) :
    AppearsBefore (Fin.snoc B s : Fin (k + 1) → Fin 3 → Fin 8) v S ↔
      AppearsBefore B v S ∧ NewAppears B s v S := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun j hj => ?_⟩
    · obtain ⟨i', j', hlt, hv⟩ := h i.castSucc j (by simpa using hij)
      have hi' : (i' : ℕ) < k := by
        simp only [pos, Fin.val_castSucc] at hlt
        have := i.isLt; have := j.isLt; have := j'.isLt; omega
      have e : i' = (⟨i', hi'⟩ : Fin k).castSucc := Fin.ext rfl
      rw [e, Fin.snoc_castSucc] at hv
      refine ⟨⟨i', hi'⟩, j', ?_, hv⟩
      simpa [pos] using hlt
    · obtain ⟨i', j', hlt, hv⟩ := h (Fin.last k) j (by simpa using hj)
      by_cases hi' : (i' : ℕ) < k
      · left
        have e : i' = (⟨i', hi'⟩ : Fin k).castSucc := Fin.ext rfl
        rw [e, Fin.snoc_castSucc] at hv
        exact ⟨⟨i', hi'⟩, j', hv⟩
      · right
        have e : i' = Fin.last k := Fin.ext (by have := i'.isLt; simp; omega)
        rw [e, Fin.snoc_last] at hv
        rw [e] at hlt
        refine ⟨j', ?_, hv⟩
        simp only [pos, Fin.val_last] at hlt
        omega
  · rintro ⟨h1, h2⟩ i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc] at hij
      obtain ⟨i', j', hlt, hv⟩ := h1 i0 j hij
      exact ⟨i'.castSucc, j', by simpa [pos] using hlt, by simpa using hv⟩
    · rw [Fin.snoc_last] at hij
      rcases h2 j hij with ⟨i', j', hv⟩ | ⟨j', hlt, hv⟩
      · refine ⟨i'.castSucc, j', ?_, by simpa using hv⟩
        simp only [pos, Fin.val_castSucc, Fin.val_last]
        have := i'.isLt; have := j'.isLt; omega
      · exact ⟨Fin.last k, j', by simp only [pos, Fin.val_last]; omega, by simpa using hv⟩

theorem adjFree_snoc {k : ℕ} (B : Fin (k + 1) → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) :
    AdjFree (Fin.snoc B s : Fin (k + 2) → Fin 3 → Fin 8) ↔
      AdjFree B ∧ RowAdm s ∧ RowFollows (B (Fin.last k)) s := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i i' j j' hadj
      have := h i.castSucc i'.castSucc j j' (by simpa [Fin.val_castSucc] using hadj)
      simpa using this
    · have := rowAdm_of_adjFree h (Fin.last (k + 1))
      simpa using this
    · have hc : ∀ j j' : Fin 3, (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 →
          NoClash (B (Fin.last k) j) (s j') := by
        intro j j' h1 h2
        have := h (Fin.last k).castSucc (Fin.last (k + 1)) j j'
          ⟨by simp, by simp; omega, by simp, h1, h2⟩
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at this
        exact (clash_cond_iff _ _).mp this
      exact ⟨hc 0 0 (by decide) (by decide), hc 0 1 (by decide) (by decide),
        hc 1 0 (by decide) (by decide), hc 1 1 (by decide) (by decide),
        hc 1 2 (by decide) (by decide), hc 2 1 (by decide) (by decide),
        hc 2 2 (by decide) (by decide)⟩
  · rintro ⟨hB, hr, hc⟩ i i' j j' hadj
    rw [clash_cond_iff]
    obtain ⟨hne, h1, h2, h3, h4⟩ := hadj
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last i' with ⟨i0', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact (clash_cond_iff _ _).mp (hB i0 i0' j j' ⟨by simpa using hne, by simpa using h1,
        by simpa using h2, h3, h4⟩)
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have e : i0 = Fin.last k := Fin.ext (by
        have := i0.isLt; simp only [Fin.val_castSucc, Fin.val_last] at h2 ⊢; omega)
      rw [e]
      exact rowFollows_get hc j j' h3 h4
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have e : i0' = Fin.last k := Fin.ext (by
        have := i0'.isLt; simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢; omega)
      rw [e, noClash_comm]
      exact rowFollows_get hc j' j h4 h3
    · simp only [Fin.snoc_last]
      have hjj : j ≠ j' := by
        intro e; exact hne (by rw [e])
      exact rowAdm_get hr j j' hjj h3 h4

theorem topLeft_snoc_iff {k : ℕ} (B : Fin (k + 1) → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) :
    (∀ h : 0 < k + 2, (Fin.snoc B s : Fin (k + 2) → Fin 3 → Fin 8) ⟨0, h⟩ 0 = 0) ↔
      (∀ h : 0 < k + 1, B ⟨0, h⟩ 0 = 0) := by
  have e : (⟨0, by omega⟩ : Fin (k + 2)) = (⟨0, by omega⟩ : Fin (k + 1)).castSucc := rfl
  constructor
  · intro h _
    have := h (by omega)
    rw [e, Fin.snoc_castSucc] at this
    exact this
  · intro h _
    rw [e, Fin.snoc_castSucc]
    exact h (by omega)

theorem good_snoc_iff {k : ℕ} (B : Fin (k + 1) → Fin 3 → Fin 8) (s : Fin 3 → Fin 8) :
    Good (Fin.snoc B s : Fin (k + 2) → Fin 3 → Fin 8) ↔
      Good B ∧ RowAdm s ∧ RowFollows (B (Fin.last k)) s ∧ NewOrderOK B s := by
  rw [good_iff_parts, good_iff_parts, adjFree_snoc, topLeft_snoc_iff, appears_snoc, appears_snoc,
    appears_snoc]
  unfold NewOrderOK
  tauto

/-! ### The values 1, 2 and 3 occur in every good array with at least two rows -/

theorem block_four_classes : ∀ c1 c2 c3 : Fin 8, NoClash 0 c1 → NoClash 0 c2 → NoClash 0 c3 →
    NoClash c1 c2 → NoClash c1 c3 → NoClash c2 c3 →
    ((c1 = 1 ∨ c1 = 6) ∨ (c2 = 1 ∨ c2 = 6) ∨ (c3 = 1 ∨ c3 = 6)) ∧
    ((c1 = 2 ∨ c1 = 5) ∨ (c2 = 2 ∨ c2 = 5) ∨ (c3 = 2 ∨ c3 = 5)) ∧
    ((c1 = 3 ∨ c1 = 4) ∨ (c2 = 3 ∨ c2 = 4) ∨ (c3 = 3 ∨ c3 = 4)) := by
  decide

theorem value_of_appears {n : ℕ} {A : Fin n → Fin 3 → Fin 8} {v w : Fin 8} {S : Finset (Fin 8)}
    (hA : AppearsBefore A v S) (hw : w ∈ S) (i : Fin n) (j : Fin 3)
    (hij : A i j = v ∨ A i j = w) : ∃ (i : Fin n) (j : Fin 3), A i j = v := by
  rcases hij with h | h
  · exact ⟨i, j, h⟩
  · obtain ⟨i', j', -, h'⟩ := hA i j (h ▸ hw)
    exact ⟨i', j', h'⟩

theorem value_of_appears3 {n : ℕ} {A : Fin n → Fin 3 → Fin 8} {v w : Fin 8} {S : Finset (Fin 8)}
    (hA : AppearsBefore A v S) (hw : w ∈ S) (i1 i2 i3 : Fin n) (j1 j2 j3 : Fin 3)
    (h : (A i1 j1 = v ∨ A i1 j1 = w) ∨ (A i2 j2 = v ∨ A i2 j2 = w) ∨
      (A i3 j3 = v ∨ A i3 j3 = w)) : ∃ (i : Fin n) (j : Fin 3), A i j = v := by
  rcases h with h | h | h
  · exact value_of_appears hA hw i1 j1 h
  · exact value_of_appears hA hw i2 j2 h
  · exact value_of_appears hA hw i3 j3 h

theorem values_one_two_three {k : ℕ} {B : Fin (k + 2) → Fin 3 → Fin 8} (hB : Good B) :
    (∃ (i : Fin (k + 2)) (j : Fin 3), B i j = 1) ∧ (∃ (i : Fin (k + 2)) (j : Fin 3), B i j = 2) ∧
      (∃ (i : Fin (k + 2)) (j : Fin 3), B i j = 3) := by
  obtain ⟨hadj, htl, h1, h2, h3⟩ := hB
  have e0 : B 0 0 = 0 := htl (by omega)
  have ok : ∀ (i i' : Fin (k + 2)) (j j' : Fin 3), Adj i j i' j' → NoClash (B i j) (B i' j') :=
    fun i i' j j' h => (clash_cond_iff _ _).mp (hadj i i' j j' h)
  have a01 := ok 0 0 0 1 (by simp [Adj])
  have a10 := ok 0 1 0 0 (by simp [Adj])
  have a11 := ok 0 1 0 1 (by simp [Adj])
  have b1 := ok 0 1 1 0 (by simp [Adj])
  have b2 := ok 0 1 1 1 (by simp [Adj])
  have b3 := ok 1 1 0 1 (by simp [Adj])
  rw [e0] at a01 a10 a11
  obtain ⟨c1, c2, c3⟩ := block_four_classes _ _ _ a01 a10 a11 b1 b2 b3
  exact ⟨value_of_appears3 h1 (by decide) 0 1 1 1 0 1 c1,
    value_of_appears3 h2 (by decide) 0 1 1 1 0 1 c2,
    value_of_appears3 h3 (by decide) 0 1 1 1 0 1 c3⟩

theorem newOrderOK_of_good {k : ℕ} {B : Fin (k + 2) → Fin 3 → Fin 8} (hB : Good B)
    (s : Fin 3 → Fin 8) : NewOrderOK B s := by
  obtain ⟨oneRowTriple, e2, rowTriple⟩ := values_one_two_three hB
  exact ⟨fun _ _ => Or.inl oneRowTriple, fun _ _ => Or.inl e2, fun _ _ => Or.inl rowTriple⟩

/-! ### Counting by the last row -/

theorem card_by_last_row (k : ℕ) (T : (Fin 3 → Fin 8) → Prop) [DecidablePred T] :
    (univ.filter (fun A : Fin (k + 2) → Fin 3 → Fin 8 => Good A ∧ T (A (Fin.last (k + 1))))).card =
      ∑ B ∈ univ.filter (fun B : Fin (k + 1) → Fin 3 → Fin 8 => Good B),
        (univ.filter (fun s => RowAdm s ∧ RowFollows (B (Fin.last k)) s ∧ NewOrderOK B s ∧
          T s)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun A : Fin (k + 2) → Fin 3 → Fin 8 => Fin.init A)
    (t := univ.filter (fun B : Fin (k + 1) → Fin 3 → Fin 8 => Good B))]
  · apply sum_congr rfl
    intro B hB
    have hB' : Good B := by simpa using hB
    apply card_nbij' (fun A => A (Fin.last (k + 1))) (fun s => Fin.snoc B s)
    · intro A hA
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      obtain ⟨⟨hG, hT⟩, hinit⟩ := hA
      have hG' : Good (Fin.snoc (Fin.init A) (A (Fin.last (k + 1))) :
          Fin (k + 2) → Fin 3 → Fin 8) := by
        rw [Fin.snoc_init_self]; exact hG
      rw [good_snoc_iff, hinit] at hG'
      exact ⟨hG'.2.1, hG'.2.2.1, hG'.2.2.2, hT⟩
    · intro s hs
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      refine ⟨⟨(good_snoc_iff B s).mpr ⟨hB', hs.1, hs.2.1, hs.2.2.1⟩, ?_⟩, Fin.init_snoc _ _⟩
      simpa using hs.2.2.2
    · intro A hA
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA
      rw [← hA.2]
      exact Fin.snoc_init_self A
    · intro s _
      simp
  · intro A hA
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
    have hG' : Good (Fin.snoc (Fin.init A) (A (Fin.last (k + 1))) :
        Fin (k + 2) → Fin 3 → Fin 8) := by
      rw [Fin.snoc_init_self]; exact hA.1
    exact ((good_snoc_iff _ _).mp hG').1

/-! ### Successor rows depend only on clashing classes -/

/-- The clashing class of an entry: {0,7} ↦ 0, {1,6} ↦ 1, {2,5} ↦ 2, {3,4} ↦ 3. -/
def clashClass : Fin 8 → Fin 4 := ![0, 1, 2, 3, 3, 2, 1, 0]

theorem noClash_iff_class : ∀ u v : Fin 8, NoClash u v ↔ clashClass u ≠ clashClass v := by decide

theorem same_class_iff : ∀ u v : Fin 8,
    (v = u ∨ (v : ℕ) + u = 7) ↔ clashClass v = clashClass u := by decide

/-- Class-level version of `RowAdm`. -/
def RowAdmC (q : Fin 3 → Fin 4) : Prop := q 0 ≠ q 1 ∧ q 1 ≠ q 2

instance (q : Fin 3 → Fin 4) : Decidable (RowAdmC q) :=
  inferInstanceAs (Decidable (q 0 ≠ q 1 ∧ q 1 ≠ q 2))

/-- Class-level version of `RowFollows`. -/
def RowFollowsC (p q : Fin 3 → Fin 4) : Prop :=
  p 0 ≠ q 0 ∧ p 0 ≠ q 1 ∧ p 1 ≠ q 0 ∧ p 1 ≠ q 1 ∧ p 1 ≠ q 2 ∧ p 2 ≠ q 1 ∧ p 2 ≠ q 2

instance (p q : Fin 3 → Fin 4) : Decidable (RowFollowsC p q) :=
  inferInstanceAs (Decidable (p 0 ≠ q 0 ∧ p 0 ≠ q 1 ∧ p 1 ≠ q 0 ∧ p 1 ≠ q 1 ∧ p 1 ≠ q 2 ∧
    p 2 ≠ q 1 ∧ p 2 ≠ q 2))

/-- Class-level version of `EndsMatch`. -/
def EndsMatchC (q : Fin 3 → Fin 4) : Prop := q 2 = q 0

instance (q : Fin 3 → Fin 4) : Decidable (EndsMatchC q) := inferInstanceAs (Decidable (q 2 = q 0))

theorem rowAdm_iff (s : Fin 3 → Fin 8) : RowAdm s ↔ RowAdmC (clashClass ∘ s) := by
  simp only [RowAdm, RowAdmC, noClash_iff_class, Function.comp]

theorem rowFollows_iff (r s : Fin 3 → Fin 8) :
    RowFollows r s ↔ RowFollowsC (clashClass ∘ r) (clashClass ∘ s) := by
  simp only [RowFollows, RowFollowsC, noClash_iff_class, Function.comp]

theorem endsMatch_iff (s : Fin 3 → Fin 8) : EndsMatch s ↔ EndsMatchC (clashClass ∘ s) := by
  simp only [EndsMatch, EndsMatchC, same_class_iff, Function.comp]

theorem card_class_eq : ∀ c : Fin 4,
    (univ.filter (fun u : Fin 8 => clashClass u = c)).card = 2 := by
  decide

/-- Every class pattern of a row is realized by exactly 8 rows. -/
theorem card_class_fibre (q : Fin 3 → Fin 4) :
    (univ.filter (fun s : Fin 3 → Fin 8 => clashClass ∘ s = q)).card = 8 := by
  have h : univ.filter (fun s : Fin 3 → Fin 8 => clashClass ∘ s = q) =
      Fintype.piFinset (fun j => univ.filter (fun u : Fin 8 => clashClass u = q j)) := by
    ext s
    simp [Fintype.mem_piFinset, funext_iff]
  rw [h, Fintype.card_piFinset]
  simp [card_class_eq]

/-- Counting rows through their class patterns. -/
theorem card_by_class (P : (Fin 3 → Fin 4) → Prop) [DecidablePred P] :
    (univ.filter (fun s : Fin 3 → Fin 8 => P (clashClass ∘ s))).card =
      8 * (univ.filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := fun s : Fin 3 → Fin 8 => clashClass ∘ s) (t := univ.filter P)
    (fun s hs => by simpa using hs)]
  have : ∀ q ∈ univ.filter P,
      ((univ.filter (fun s : Fin 3 → Fin 8 => P (clashClass ∘ s))).filter
        (fun s => clashClass ∘ s = q)).card
        = 8 := by
    intro q hq
    rw [filter_filter]
    have hq' : P q := by simpa using hq
    refine Eq.trans ?_ (card_class_fibre q)
    congr 1
    apply filter_congr
    intro s _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hq', h⟩
  rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]

/-- The transfer facts on class patterns: a periodic admissible pattern has exactly two
compatible admissible successors, both periodic; a non-periodic one has exactly one, which is
non-periodic. -/
theorem succ_countC : ∀ p : Fin 3 → Fin 4, RowAdmC p →
    (univ.filter (fun q => RowAdmC q ∧ RowFollowsC p q ∧ EndsMatchC q)).card =
        (if EndsMatchC p then 2 else 0) ∧
      (univ.filter (fun q => RowAdmC q ∧ RowFollowsC p q ∧ ¬ EndsMatchC q)).card =
        (if EndsMatchC p then 0 else 1) := by
  decide +kernel

/-- Counting rows through their class patterns, for a predicate given on rows. -/
theorem card_by_class_of_iff (P : (Fin 3 → Fin 4) → Prop) [DecidablePred P]
    (Q : (Fin 3 → Fin 8) → Prop) [DecidablePred Q] (h : ∀ s, Q s ↔ P (clashClass ∘ s)) :
    (univ.filter Q).card = 8 * (univ.filter P).card := by
  rw [← card_by_class P]
  congr 1
  exact filter_congr (fun s _ => h s)

/-- The transfer facts on rows. -/
theorem succ_count (r : Fin 3 → Fin 8) (hr : RowAdm r) :
    (univ.filter (fun s => RowAdm s ∧ RowFollows r s ∧ EndsMatch s)).card =
        (if EndsMatch r then 16 else 0) ∧
      (univ.filter (fun s => RowAdm s ∧ RowFollows r s ∧ ¬ EndsMatch s)).card =
        (if EndsMatch r then 0 else 8) := by
  obtain ⟨hP, hQ⟩ := succ_countC (clashClass ∘ r) ((rowAdm_iff r).mp hr)
  have k1 := card_by_class_of_iff
    (fun q => RowAdmC q ∧ RowFollowsC (clashClass ∘ r) q ∧ EndsMatchC q)
    (fun s => RowAdm s ∧ RowFollows r s ∧ EndsMatch s)
    (fun s => by simp only [rowAdm_iff, rowFollows_iff, endsMatch_iff])
  have k2 := card_by_class_of_iff
    (fun q => RowAdmC q ∧ RowFollowsC (clashClass ∘ r) q ∧ ¬ EndsMatchC q)
    (fun s => RowAdm s ∧ RowFollows r s ∧ ¬ EndsMatch s)
    (fun s => by simp only [rowAdm_iff, rowFollows_iff, endsMatch_iff])
  rw [k1, k2, hP, hQ]
  by_cases h : EndsMatch r
  · simp [h, (endsMatch_iff r).mp h]
  · simp [h, show ¬ EndsMatchC (clashClass ∘ r) from fun h' => h ((endsMatch_iff r).mpr h')]

/-! ### The two counts and their recursions -/

/-- Good arrays with `n + 2` rows whose last row is periodic. -/
def nEndsMatch (n : ℕ) : ℕ :=
  (univ.filter (fun A : Fin (n + 2) → Fin 3 → Fin 8 =>
    Good A ∧ EndsMatch (A (Fin.last (n + 1))))).card

/-- Good arrays with `n + 2` rows whose last row is not periodic. -/
def nEndsDiffer (n : ℕ) : ℕ :=
  (univ.filter (fun A : Fin (n + 2) → Fin 3 → Fin 8 =>
    Good A ∧ ¬ EndsMatch (A (Fin.last (n + 1))))).card

theorem nEndsMatch_succ (n : ℕ) : nEndsMatch (n + 1) = 16 * nEndsMatch n := by
  unfold nEndsMatch
  rw [card_by_last_row (n + 1) EndsMatch]
  rw [sum_congr rfl (g := fun B : Fin (n + 2) → Fin 3 → Fin 8 =>
    if EndsMatch (B (Fin.last (n + 1))) then 16 else 0) ?_]
  · rw [sum_ite, sum_const, sum_const_zero, smul_eq_mul, add_zero, filter_filter, mul_comm]
  · intro B hB
    have hG : Good B := by simpa using hB
    have hrow : RowAdm (B (Fin.last (n + 1))) := rowAdm_of_adjFree hG.1 _
    rw [← (succ_count _ hrow).1]
    congr 1
    apply filter_congr
    intro s _
    have := newOrderOK_of_good hG s
    tauto

theorem nEndsDiffer_succ (n : ℕ) : nEndsDiffer (n + 1) = 8 * nEndsDiffer n := by
  unfold nEndsDiffer
  rw [card_by_last_row (n + 1) (fun r => ¬ EndsMatch r)]
  rw [sum_congr rfl (g := fun B : Fin (n + 2) → Fin 3 → Fin 8 =>
    if EndsMatch (B (Fin.last (n + 1))) then 0 else 8) ?_]
  · rw [sum_ite, sum_const_zero, sum_const, smul_eq_mul, zero_add, filter_filter, mul_comm]
  · intro B hB
    have hG : Good B := by simpa using hB
    have hrow : RowAdm (B (Fin.last (n + 1))) := rowAdm_of_adjFree hG.1 _
    rw [← (succ_count _ hrow).2]
    congr 1
    apply filter_congr
    intro s _
    have := newOrderOK_of_good hG s
    tauto

theorem card_eq_a (n : ℕ) : a n = (univ.filter (fun A : Fin n → Fin 3 → Fin 8 => Good A)).card := by
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem a_add_two_split (n : ℕ) : a (n + 2) = nEndsMatch n + nEndsDiffer n := by
  rw [card_eq_a, nEndsMatch, nEndsDiffer, ← card_filter_add_card_filter_not
    (s := univ.filter (fun A : Fin (n + 2) → Fin 3 → Fin 8 => Good A))
    (fun A => EndsMatch (A (Fin.last (n + 1)))), filter_filter, filter_filter]

/-! ### Base cases by kernel computation -/

/-- Rows as triples. -/
def rowTriple : (Fin 8 × Fin 8 × Fin 8) ≃ (Fin 3 → Fin 8) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun r := (r 0, r 1, r 2)
  left_inv t := rfl
  right_inv r := by ext j; fin_cases j <;> rfl

/-- One-row arrays as triples. -/
def oneRowTriple : (Fin 8 × Fin 8 × Fin 8) ≃ (Fin 1 → Fin 3 → Fin 8) where
  toFun t := fun _ => ![t.1, t.2.1, t.2.2]
  invFun A := (A 0 0, A 0 1, A 0 2)
  left_inv t := rfl
  right_inv A := by
    ext i j
    fin_cases i
    fin_cases j <;> rfl

theorem card_rows_triple (p : (Fin 3 → Fin 8) → Prop) [DecidablePred p] :
    (univ.filter p).card = (univ.filter (fun t => p (rowTriple t))).card := by
  apply card_nbij' rowTriple.symm rowTriple
  · intro r hr; simpa using hr
  · intro t ht; simpa using ht
  · intro r _; simp
  · intro t _; simp

theorem sum_one_row (f : (Fin 1 → Fin 3 → Fin 8) → ℕ) :
    ∑ B ∈ univ.filter (fun B : Fin 1 → Fin 3 → Fin 8 => Good B), f B =
      ∑ t ∈ univ.filter (fun t => Good (oneRowTriple t)), f (oneRowTriple t) := by
  apply sum_equiv oneRowTriple.symm
  · intro B; simp
  · intro B _; simp

theorem nEndsMatch_zero : nEndsMatch 0 = 4 := by
  unfold nEndsMatch
  rw [card_by_last_row 0 EndsMatch, sum_one_row, sum_congr rfl (fun t _ => card_rows_triple _)]
  decide +kernel

theorem nEndsDiffer_zero : nEndsDiffer 0 = 4 := by
  unfold nEndsDiffer
  rw [card_by_last_row 0 (fun r => ¬ EndsMatch r), sum_one_row,
    sum_congr rfl (fun t _ => card_rows_triple _)]
  decide +kernel

theorem a_one_val : a 1 = 3 := by
  rw [card_eq_a]
  have h := sum_one_row (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at h
  rw [h]
  decide +kernel

/-! ### Closed form and generating function -/

theorem nEndsMatch_eq (n : ℕ) : nEndsMatch n = 4 * 16 ^ n := by
  induction n with
  | zero => simp [nEndsMatch_zero]
  | succ n ih => rw [nEndsMatch_succ, ih]; ring

theorem nEndsDiffer_eq (n : ℕ) : nEndsDiffer n = 4 * 8 ^ n := by
  induction n with
  | zero => simp [nEndsDiffer_zero]
  | succ n ih => rw [nEndsDiffer_succ, ih]; ring

theorem a_add_two_closed (n : ℕ) : a (n + 2) = 4 * 16 ^ n + 4 * 8 ^ n := by
  rw [a_add_two_split, nEndsMatch_eq, nEndsDiffer_eq]

theorem barker_closed_form (n : ℕ) (hn : 1 < n) : a n = 8 ^ (n - 2) * (2 ^ n + 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_add_two_closed, Nat.add_sub_cancel, show (16 : ℕ) = 8 * 2 by norm_num, mul_pow, pow_add]
  ring

theorem a_two_val : a 2 = 8 := by
  rw [a_add_two_split, nEndsMatch_zero, nEndsDiffer_zero]

theorem a_three_val : a 3 = 96 := by
  rw [a_add_two_closed 1]
  norm_num

open PowerSeries in
/-- Barker's generating function, from the closed form. -/
theorem barker_gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 8 * X) * (1 - 16 * X)) = X * (3 - 64 * X + 288 * X ^ 2) := by
  set P : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hP
  have key : PowerSeries.mk P * ((1 - 8 * X) * (1 - 16 * X)) =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 24 * (PowerSeries.mk P * X ^ 1) +
        C 128 * (PowerSeries.mk P * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (3 - 64 * X + 288 * X ^ 2) =
      C 3 * X ^ 1 - C 64 * X ^ 2 + C 288 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 4
  · interval_cases k <;> norm_num [hP, a_one_val, a_two_val, a_three_val]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have h4 : a (j + 4) = 4 * 16 ^ (j + 2) + 4 * 8 ^ (j + 2) := a_add_two_closed (j + 2)
    have h3 : a (j + 3) = 4 * 16 ^ (j + 1) + 4 * 8 ^ (j + 1) := a_add_two_closed (j + 1)
    have h2 : a (j + 2) = 4 * 16 ^ j + 4 * 8 ^ j := a_add_two_closed j
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show j + 4 - 0 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
      show j + 4 - 2 = j + 2 by omega, show ¬ (j + 4 = 1) by omega,
      show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, if_true, if_false, hP,
      h4, h3, h2]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a233163.main :=
  ⟨OMA.Helpers.barker_gen_fun, OMA.Helpers.barker_closed_form⟩
