import OMAStatements.S_oeis_a202443

/-!
Proof of the conjectures of A202443 ((n + 2) X 6 binary arrays avoiding 0 0 1 and 1 1 0
horizontally, vertically and along nw-to-se diagonals).

An array is good iff every row is good (`H`) and every three consecutive rows satisfy `V`
(`valid_iff`). Removing the first row gives a transfer recursion: if `T m x y` counts the ways to
continue the rows `x, y` by `m` more rows, then `T 0 x y` is 1 or 0 as `x` and `y` are good rows
or not, `T (m + 1) x y` sums `T m y z` over the `z` with `H x` and `V x y z`, and for `n ≥ 1`,
`a n` is the sum of all `T n x y`. There are exactly 12 good rows (`H_iff`); they are coded by
`Fin 12`, `V` becomes a table lookup on codes, and `G` is the recursion on codes.

For `m ≥ 2`, six times `G m i j` is a quartic in `m` whose coefficients depend on the parity of
`m` (tables `QE` and `QO`). This is proved by induction from `m = 2`; each step is a finite check
of five coefficient identities per pair of codes, from one parity class to the other. Summing
gives the two closed forms of `a n`, and the generating function follows by comparing
coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202443 Finset

/-- A row of the array. -/
abbrev Row202443 := Fin 6 → Fin 2

/-- A row avoids the two patterns. -/
def H202443 (x : Row202443) : Prop :=
  ∀ c : Fin 4, avoids3 (x ⟨c.1, by omega⟩) (x ⟨c.1 + 1, by omega⟩) (x ⟨c.1 + 2, by omega⟩)

/-- Three consecutive rows: the columns and the diagonals avoid the two patterns. -/
def V202443 (x y z : Row202443) : Prop :=
  (∀ c : Fin 6, avoids3 (x c) (y c) (z c)) ∧
    ∀ c : Fin 4, avoids3 (x ⟨c.1, by omega⟩) (y ⟨c.1 + 1, by omega⟩) (z ⟨c.1 + 2, by omega⟩)

instance decH202443 (x : Row202443) : Decidable (H202443 x) := by
  unfold H202443 avoids3
  infer_instance

instance decV202443 (x y z : Row202443) : Decidable (V202443 x y z) := by
  unfold V202443 avoids3
  infer_instance

/-- The conditions of the statement for an array with `L` rows. -/
def Chn202443 {L : ℕ} (A : Fin L → Row202443) : Prop :=
  (∀ r, H202443 (A r)) ∧
    ∀ (i : ℕ) (h : i + 2 < L), V202443 (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem valid_iff202443 (n : ℕ) (A : Fin (n + 2) → Row202443) : isValid n A ↔ Chn202443 A := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => ⟨fun c => h2 c ⟨i, by omega⟩, fun c => h3 ⟨i, by omega⟩ c⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c r => (h2 r.1 (by omega)).1 c, fun r c => (h2 r.1 (by omega)).2 c⟩

theorem chn_cons202443 {m : ℕ} (x : Row202443) (B : Fin (m + 2) → Row202443) :
    Chn202443 (Fin.cons x B : Fin (m + 3) → Row202443) ↔
      (H202443 x ∧ V202443 x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩)) ∧ Chn202443 B := by
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := h1 ⟨0, by omega⟩
    have a2 := h2 0 (by omega)
    exact ⟨⟨a1, a2⟩, fun r => h1 r.succ, fun i hi => h2 (i + 1) (by omega)⟩
  · rintro ⟨⟨a1, a2⟩, h1, h2⟩
    refine ⟨fun r => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun r => ?_) r
      · exact a1
      · exact h1 r
    · cases i with
      | zero => exact a2
      | succ i => exact h2 i (by omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def T202443 (m : ℕ) (x y : Row202443) : ℕ := by
  classical
  exact ∑ B : Fin m → Row202443,
    if Chn202443 (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row202443) then 1 else 0

theorem T_zero202443 (x y : Row202443) : T202443 0 x y = if H202443 x ∧ H202443 y then 1 else 0 := by
  classical
  unfold T202443
  rw [Fintype.sum_unique]
  refine if_congr ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨fun r => ?_, fun i hi => by omega⟩⟩ rfl rfl
  · exact h.1 ⟨0, by omega⟩
  · exact h.1 ⟨1, by omega⟩
  · refine Fin.cases ?_ (fun r => ?_) r
    · exact h.1
    · refine Fin.cases ?_ (fun r => r.elim0) r
      exact h.2

theorem T_succ202443 (m : ℕ) (x y : Row202443) :
    T202443 (m + 1) x y = ∑ z : Row202443, if H202443 x ∧ V202443 x y z then T202443 m y z else 0 := by
  classical
  unfold T202443
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row202443).symm _
    (fun p => if Chn202443 (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row202443)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : H202443 x ∧ V202443 x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chn_cons202443]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chn_cons202443]
    exact fun h => hv h.1

theorem T_bad_left202443 (m : ℕ) (x y : Row202443) (hx : ¬ H202443 x) : T202443 m x y = 0 := by
  classical
  unfold T202443
  refine Finset.sum_eq_zero fun B _ => if_neg fun h => ?_
  have h0 := h.1 ⟨0, by omega⟩
  exact hx h0

theorem T_bad_right202443 (m : ℕ) (x y : Row202443) (hy : ¬ H202443 y) : T202443 m x y = 0 := by
  classical
  unfold T202443
  refine Finset.sum_eq_zero fun B _ => if_neg fun h => ?_
  have h0 := h.1 ⟨1, by omega⟩
  exact hy h0

theorem a_eq202443 (n : ℕ) (hn : n ≠ 0) : a n = ∑ x : Row202443, ∑ y : Row202443, T202443 n x y := by
  classical
  have h1 : a n = ∑ A : Fin (n + 2) → Row202443, if Chn202443 A then 1 else 0 := by
    unfold a
    rw [if_neg hn, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (valid_iff202443 n A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row202443).symm _
    (fun p => if Chn202443 (Fin.cons p.1 p.2 : Fin (n + 2) → Row202443) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row202443).symm _
    (fun p => if Chn202443 (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row202443) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The codes of the 12 good rows (bit `5 - c` is the entry in column `c`). -/
def code202443 (i : Fin 12) : ℕ := [0, 16, 20, 21, 23, 31, 32, 40, 42, 43, 47, 63].getD i.val 0

/-- The good row with code number `i`. -/
def row202443 (i : Fin 12) : Row202443 :=
  fun c => ⟨code202443 i / 2 ^ (5 - c.val) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- All rows, coded by `Fin 64`. -/
def full202443 (c : Fin 64) : Row202443 :=
  fun j => ⟨c.val / 2 ^ (5 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective202443 : Function.Injective row202443 := by
  decide +kernel

theorem full_bijective202443 : Function.Bijective full202443 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide +kernel, by simp⟩

theorem H_iff202443 : ∀ c : Fin 64, H202443 (full202443 c) ↔ ∃ i : Fin 12, row202443 i = full202443 c := by
  decide +kernel

theorem H_row202443 : ∀ i : Fin 12, H202443 (row202443 i) := by
  decide +kernel

/-- A sum over rows of a function vanishing off the good rows is a sum over the 12 codes. -/
theorem bridge202443 (f : Row202443 → ℕ) (hf : ∀ r, ¬ H202443 r → f r = 0) :
    ∑ r : Row202443, f r = ∑ i : Fin 12, f (row202443 i) := by
  classical
  have hmem : ∀ r : Row202443, H202443 r ↔ ∃ i, row202443 i = r := by
    intro r
    obtain ⟨c, rfl⟩ := full_bijective202443.2 r
    exact H_iff202443 c
  rw [← Finset.sum_filter_of_ne (p := H202443) (fun r _ h => by_contra fun hr => h (hf r hr))]
  have e : Finset.univ.filter H202443 = Finset.univ.map ⟨row202443, row_injective202443⟩ := by
    ext r
    simp [hmem]
  rw [e, Finset.sum_map]
  rfl

/-- `V` on codes, as a table. -/
def Vt202443 (i j k : Fin 12) : Bool :=
  Nat.beq (7567659180228683461806178766270876737338073535414032830525581949585456234959228916200334896569028815040482162830620903816275877959643974172088235323493957422495823321216724870097483136517733105834371225365359541183188261318649287199946178613811198099452226908323804346526092015249400036876328608459404675159212941428378294642798500425524340947480314280542019660506095066092748155383017432472599055381182502707531789457566002235530669871608920007991270715996464852543354844585598475181243912586342619954493563686325596161 / 2 ^ (144 * i.val + 12 * j.val + k.val) % 2) 1

theorem Vt_iff202443 : ∀ i j k : Fin 12,
    V202443 (row202443 i) (row202443 j) (row202443 k) ↔ Vt202443 i j k = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G202443 : ℕ → Fin 12 → Fin 12 → ℕ
  | 0, _, _ => 1
  | m + 1, i, j => ∑ k : Fin 12, if Vt202443 i j k then G202443 m j k else 0

theorem T_eq_G202443 (m : ℕ) : ∀ i j : Fin 12, T202443 m (row202443 i) (row202443 j) = G202443 m i j := by
  induction m with
  | zero =>
    intro i j
    rw [T_zero202443, if_pos ⟨H_row202443 i, H_row202443 j⟩]
    rfl
  | succ m ih =>
    intro i j
    rw [T_succ202443, bridge202443]
    · simp only [G202443]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih j k]
      refine if_congr ?_ rfl rfl
      rw [← Vt_iff202443]
      exact and_iff_right (H_row202443 i)
    · intro z hz
      simp only [T_bad_right202443 m _ z hz, ite_self]

theorem a_eq_G202443 (n : ℕ) (hn : n ≠ 0) : a n = ∑ i : Fin 12, ∑ j : Fin 12, G202443 n i j := by
  rw [a_eq202443 n hn, bridge202443]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [bridge202443]
    · exact Finset.sum_congr rfl fun j _ => T_eq_G202443 n i j
    · intro y hy
      exact T_bad_right202443 n _ y hy
  · intro x hx
    exact Finset.sum_eq_zero fun y _ => T_bad_left202443 n x y hx

/-- Coefficients (of `m ^ d`, row `d`, indexed by `12 i + j`) of six times `G m i j` for even
`m ≥ 2`. -/
def QE202443 : List (List ℤ) :=
  [[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 6, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 6, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
   [0, 6, 6, 8, 8, 10, 6, 6, 8, 8, 10, 28, 6, 0, 6, 6, 18, 6, 6, 0, 0, 0, 0, 10, 6, 6, 0, 6, 6, 6, 6, 0, 0, 0, 0, 8, 8, 6, 6, 0, 6, 6, 6, 0, 0, 0, 0, 8, 8, 6, 12, 6, 0, 6, 6, 0, 0, 0, 0, 6, 10, 12, 6, 6, 6, 0, 6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 6, 0, 6, 6, 6, 12, 10, 6, 0, 0, 0, 0, 6, 6, 0, 6, 12, 6, 8, 8, 0, 0, 0, 0, 6, 6, 6, 0, 6, 6, 8, 8, 0, 0, 0, 0, 6, 6, 6, 6, 0, 6, 6, 10, 0, 0, 0, 0, 6, 6, 18, 6, 6, 0, 6, 28, 10, 8, 8, 6, 6, 10, 8, 8, 6, 6, 0],
   [0, 0, 3, 3, 3, 15, 0, 3, 3, 3, 3, 16, 0, 0, 0, 3, 3, 6, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 12, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 12, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 6, 3, 3, 0, 0, 0, 16, 3, 3, 3, 3, 0, 15, 3, 3, 3, 0, 0],
   [0, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The same for odd `m ≥ 3`. -/
def QO202443 : List (List ℤ) :=
  [[6, 6, 3, 3, 3, 15, 6, 3, 3, 3, 3, 6, 6, 6, 6, 3, 3, 12, 6, 0, 0, 0, 0, 9, 9, 6, 6, 6, 6, 9, 6, 0, 0, 0, 0, 9, 9, 9, 6, 6, 6, 9, 6, 0, 6, 0, 0, 9, 9, 9, 6, 6, 6, 6, 6, 0, 0, 0, 0, 9, 9, 6, 3, 3, 6, 6, 6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 6, 6, 6, 3, 3, 6, 9, 9, 0, 0, 0, 0, 6, 6, 6, 6, 6, 9, 9, 9, 0, 0, 6, 0, 6, 9, 6, 6, 6, 9, 9, 9, 0, 0, 0, 0, 6, 9, 6, 6, 6, 6, 9, 9, 0, 0, 0, 0, 6, 12, 3, 3, 6, 6, 6, 6, 3, 3, 3, 3, 6, 15, 3, 3, 3, 6, 6],
   [0, 6, 6, 5, 5, 4, 6, 6, 5, 5, 4, 40, 6, 0, 6, 6, 18, 6, 6, 0, 0, 0, 0, 16, 6, 6, 0, 6, 6, 6, 6, 0, 0, 0, 0, 11, 11, 6, 6, 0, 6, 6, 6, 0, 0, 0, 0, 11, 11, 6, 12, 6, 0, 6, 6, 0, 0, 0, 0, 6, 16, 12, 6, 6, 6, 0, 6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 6, 0, 6, 6, 6, 12, 16, 6, 0, 0, 0, 0, 6, 6, 0, 6, 12, 6, 11, 11, 0, 0, 0, 0, 6, 6, 6, 0, 6, 6, 11, 11, 0, 0, 0, 0, 6, 6, 6, 6, 0, 6, 6, 16, 0, 0, 0, 0, 6, 6, 18, 6, 6, 0, 6, 40, 4, 5, 5, 6, 6, 4, 5, 5, 6, 6, 0],
   [0, 0, 3, 3, 3, 15, 0, 3, 3, 3, 3, 16, 0, 0, 0, 3, 3, 6, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 12, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 12, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 6, 3, 3, 0, 0, 0, 16, 3, 3, 3, 3, 0, 15, 3, 3, 3, 0, 0],
   [0, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def qE202443 (d : ℕ) (i j : Fin 12) : ℤ := (QE202443.getD d []).getD (12 * i.val + j.val) 0

def qO202443 (d : ℕ) (i j : Fin 12) : ℤ := (QO202443.getD d []).getD (12 * i.val + j.val) 0

/-- The coefficient table for the parity of `m`. -/
def qq202443 (m : ℕ) : ℕ → Fin 12 → Fin 12 → ℤ := if m % 2 = 0 then qE202443 else qO202443

/-- The quartic with coefficients `q`. -/
def Pol202443 (q : ℕ → Fin 12 → Fin 12 → ℤ) (i j : Fin 12) (m : ℤ) : ℤ :=
  q 4 i j * m ^ 4 + q 3 i j * m ^ 3 + q 2 i j * m ^ 2 + q 1 i j * m + q 0 i j

/-- One step of the recursion maps the quartics `p` to the quartics `q` (shifted by one). -/
def StepOK202443 (p q : ℕ → Fin 12 → Fin 12 → ℤ) : Prop :=
  ∀ i j : Fin 12,
    (∑ k : Fin 12, if Vt202443 i j k then p 4 j k else 0) = q 4 i j ∧
    (∑ k : Fin 12, if Vt202443 i j k then p 3 j k else 0) = 4 * q 4 i j + q 3 i j ∧
    (∑ k : Fin 12, if Vt202443 i j k then p 2 j k else 0) = 6 * q 4 i j + 3 * q 3 i j + q 2 i j ∧
    (∑ k : Fin 12, if Vt202443 i j k then p 1 j k else 0) =
      4 * q 4 i j + 3 * q 3 i j + 2 * q 2 i j + q 1 i j ∧
    (∑ k : Fin 12, if Vt202443 i j k then p 0 j k else 0) =
      q 4 i j + q 3 i j + q 2 i j + q 1 i j + q 0 i j

theorem stepEO202443 : StepOK202443 qE202443 qO202443 := by
  unfold StepOK202443
  decide +kernel

theorem stepOE202443 : StepOK202443 qO202443 qE202443 := by
  unfold StepOK202443
  decide +kernel

theorem step_gen202443 (p q : ℕ → Fin 12 → Fin 12 → ℤ) (hpq : StepOK202443 p q) (m : ℕ)
    (ih : ∀ k l : Fin 12, 6 * (G202443 m k l : ℤ) = Pol202443 p k l m) :
    ∀ i j : Fin 12, 6 * (G202443 (m + 1) i j : ℤ) = Pol202443 q i j ((m + 1 : ℕ) : ℤ) := by
  intro i j
  have hsum : 6 * (G202443 (m + 1) i j : ℤ) =
      ∑ k : Fin 12, if Vt202443 i j k then Pol202443 p j k m else 0 := by
    rw [G202443]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · exact ih j k
    · simp
  rw [hsum]
  have hP : ∀ k : Fin 12, (if Vt202443 i j k then Pol202443 p j k m else 0) =
      (if Vt202443 i j k then p 4 j k else 0) * (m : ℤ) ^ 4 +
      (if Vt202443 i j k then p 3 j k else 0) * (m : ℤ) ^ 3 +
      (if Vt202443 i j k then p 2 j k else 0) * (m : ℤ) ^ 2 +
      (if Vt202443 i j k then p 1 j k else 0) * (m : ℤ) +
      (if Vt202443 i j k then p 0 j k else 0) := by
    intro k
    split_ifs <;> simp [Pol202443]
  simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h4, h3, h2, h1, h0⟩ := hpq i j
  rw [h4, h3, h2, h1, h0]
  unfold Pol202443
  push_cast
  ring

theorem step_all202443 (m : ℕ) : StepOK202443 (qq202443 m) (qq202443 (m + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h' : (m + 1) % 2 = 1 := by omega
    simp only [qq202443, h, h', if_true, if_false, if_neg (show ¬ ((1 : ℕ) = 0) by omega)]
    exact stepEO202443
  · have h' : (m + 1) % 2 = 0 := by omega
    simp only [qq202443, h, h', if_true, if_false, if_neg (show ¬ ((1 : ℕ) = 0) by omega)]
    exact stepOE202443

theorem base_facts202443 : ∀ i j : Fin 12, 6 * (G202443 2 i j : ℤ) = Pol202443 (qq202443 2) i j ((2 : ℕ) : ℤ) := by
  decide +kernel

theorem G_closed202443 (m : ℕ) (hm : 2 ≤ m) :
    ∀ i j : Fin 12, 6 * (G202443 m i j : ℤ) = Pol202443 (qq202443 m) i j m := by
  induction m, hm using Nat.le_induction with
  | base => exact base_facts202443
  | succ m hm ih => exact step_gen202443 _ _ (step_all202443 m) m ih

theorem sumE_facts202443 :
    (∑ i : Fin 12, ∑ j : Fin 12, qE202443 4 i j) = 4 ∧ (∑ i : Fin 12, ∑ j : Fin 12, qE202443 3 i j) = 48 ∧
    (∑ i : Fin 12, ∑ j : Fin 12, qE202443 2 i j) = 236 ∧ (∑ i : Fin 12, ∑ j : Fin 12, qE202443 1 i j) = 708 ∧
    (∑ i : Fin 12, ∑ j : Fin 12, qE202443 0 i j) = 636 := by
  decide +kernel

theorem sumO_facts202443 :
    (∑ i : Fin 12, ∑ j : Fin 12, qO202443 4 i j) = 4 ∧ (∑ i : Fin 12, ∑ j : Fin 12, qO202443 3 i j) = 48 ∧
    (∑ i : Fin 12, ∑ j : Fin 12, qO202443 2 i j) = 236 ∧ (∑ i : Fin 12, ∑ j : Fin 12, qO202443 1 i j) = 732 ∧
    (∑ i : Fin 12, ∑ j : Fin 12, qO202443 0 i j) = 672 := by
  decide +kernel

theorem a_even202443 (n : ℕ) (hn : 2 ≤ n) (he : n % 2 = 0) :
    6 * (a n : ℤ) = 4 * (n : ℤ) ^ 4 + 48 * (n : ℤ) ^ 3 + 236 * (n : ℤ) ^ 2 + 708 * (n : ℤ) + 636 := by
  rw [a_eq_G202443 n (by omega)]
  push_cast
  simp only [Finset.mul_sum, G_closed202443 n hn]
  simp only [qq202443, he, if_true, if_pos rfl]
  simp only [Pol202443, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h4, h3, h2, h1, h0⟩ := sumE_facts202443
  rw [h4, h3, h2, h1, h0]

theorem a_odd202443 (n : ℕ) (hn : 2 ≤ n) (ho : n % 2 = 1) :
    6 * (a n : ℤ) = 4 * (n : ℤ) ^ 4 + 48 * (n : ℤ) ^ 3 + 236 * (n : ℤ) ^ 2 + 732 * (n : ℤ) + 672 := by
  rw [a_eq_G202443 n (by omega)]
  push_cast
  simp only [Finset.mul_sum, G_closed202443 n hn]
  simp only [qq202443, ho, if_false, if_neg (show ¬ ((1 : ℕ) = 0) by omega)]
  simp only [Pol202443, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h4, h3, h2, h1, h0⟩ := sumO_facts202443
  rw [h4, h3, h2, h1, h0]

theorem aEQ202443 (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 177 * (n : ℚ) + 159) := by
  have he' : n % 2 = 0 := Nat.even_iff.mp he
  have h := a_even202443 n (by omega) he'
  have h' : ((6 * (a n : ℤ) : ℤ) : ℚ) =
      ((4 * (n : ℤ) ^ 4 + 48 * (n : ℤ) ^ 3 + 236 * (n : ℤ) ^ 2 + 708 * (n : ℤ) + 636 : ℤ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

theorem aOQ202443 (n : ℕ) (hn : 1 < n) (ho : Odd n) :
    (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 183 * (n : ℚ) + 168) := by
  have ho' : n % 2 = 1 := Nat.odd_iff.mp ho
  have h := a_odd202443 n (by omega) ho'
  have h' : ((6 * (a n : ℤ) : ℤ) : ℚ) =
      ((4 * (n : ℤ) ^ 4 + 48 * (n : ℤ) ^ 3 + 236 * (n : ℤ) ^ 2 + 732 * (n : ℤ) + 672 : ℤ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

theorem G1_sum202443 : (∑ i : Fin 12, ∑ j : Fin 12, G202443 1 i j) = 338 := by
  decide +kernel

theorem a_vals202443 : (a 0 : ℚ) = 0 ∧ (a 1 : ℚ) = 338 ∧ (a 2 : ℚ) = 574 ∧ (a 3 : ℚ) = 1102 ∧ (a 4 : ℚ) = 1890 ∧ (a 5 : ℚ) = 3122 ∧ (a 6 : ℚ) = 4822 ∧ (a 7 : ℚ) = 7238 ∧ (a 8 : ℚ) = 10394 := by
  refine ⟨by simp [a], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq_G202443 1 one_ne_zero, G1_sum202443]
    norm_num
  · rw [aEQ202443 2 (by norm_num) ⟨1, rfl⟩]; norm_num
  · rw [aOQ202443 3 (by norm_num) ⟨1, rfl⟩]; norm_num
  · rw [aEQ202443 4 (by norm_num) ⟨2, rfl⟩]; norm_num
  · rw [aOQ202443 5 (by norm_num) ⟨2, rfl⟩]; norm_num
  · rw [aEQ202443 6 (by norm_num) ⟨3, rfl⟩]; norm_num
  · rw [aOQ202443 7 (by norm_num) ⟨3, rfl⟩]; norm_num
  · rw [aEQ202443 8 (by norm_num) ⟨4, rfl⟩]; norm_num

open PowerSeries in
theorem gf_generic202443 (f : ℕ → ℚ) (v0 : f 0 = 0) (v1 : f 1 = 338) (v2 : f 2 = 574)
    (v3 : f 3 = 1102) (v4 : f 4 = 1890) (v5 : f 5 = 3122) (v6 : f 6 = 4822)
    (v7 : f 7 = 7238) (v8 : f 8 = 10394)
    (hE : ∀ n : ℕ, 1 ≤ n → Even n → f n = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 177 * (n : ℚ) + 159))
    (hO : ∀ n : ℕ, 1 < n → Odd n → f n = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 183 * (n : ℚ) + 168)) :
    (PowerSeries.mk f) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 2) =
      2 * PowerSeries.X * (169 - 220 * PowerSeries.X - 141 * PowerSeries.X ^ 2 + 424 * PowerSeries.X ^ 3 - 133 * PowerSeries.X ^ 4 - 176 * PowerSeries.X ^ 5 + 137 * PowerSeries.X ^ 6 - 28 * PowerSeries.X ^ 7) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk f with hA
  have key : A * ((1 - X) ^ 5 * (1 + X) ^ 2) =
      A * X ^ 0 - C (3 : ℚ) * (A * X ^ 1) + A * X ^ 2 + C (5 : ℚ) * (A * X ^ 3) -
        C (5 : ℚ) * (A * X ^ 4) - A * X ^ 5 + C (3 : ℚ) * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have hrhs : (2 * X * (169 - 220 * X - 141 * X ^ 2 + 424 * X ^ 3 - 133 * X ^ 4 - 176 * X ^ 5 +
      137 * X ^ 6 - 28 * X ^ 7) : ℚ⟦X⟧) =
      C (338 : ℚ) * X ^ 1 - C (440 : ℚ) * X ^ 2 - C (282 : ℚ) * X ^ 3 + C (848 : ℚ) * X ^ 4 -
        C (266 : ℚ) * X ^ 5 - C (352 : ℚ) * X ^ 6 + C (274 : ℚ) * X ^ 7 - C (56 : ℚ) * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    simp only [show 0 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega,
      show 1 ≤ j + 9 by omega,
      show j + 9 - 1 = j + 8 by omega,
      show 2 ≤ j + 9 by omega,
      show j + 9 - 2 = j + 7 by omega,
      show 3 ≤ j + 9 by omega,
      show j + 9 - 3 = j + 6 by omega,
      show 4 ≤ j + 9 by omega,
      show j + 9 - 4 = j + 5 by omega,
      show 5 ≤ j + 9 by omega,
      show j + 9 - 5 = j + 4 by omega,
      show 6 ≤ j + 9 by omega,
      show j + 9 - 6 = j + 3 by omega,
      show 7 ≤ j + 9 by omega,
      show j + 9 - 7 = j + 2 by omega,
      show 8 ≤ j + 9 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 8 = 0) by omega,
      if_true, if_false]
    rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
    · rw [hE (2 * t + 2) (by omega) ⟨t + 1, by omega⟩, hO (2 * t + 3) (by omega) ⟨t + 1, by omega⟩, hE (2 * t + 4) (by omega) ⟨t + 2, by omega⟩, hO (2 * t + 5) (by omega) ⟨t + 2, by omega⟩, hE (2 * t + 6) (by omega) ⟨t + 3, by omega⟩, hO (2 * t + 7) (by omega) ⟨t + 3, by omega⟩, hE (2 * t + 8) (by omega) ⟨t + 4, by omega⟩, hO (2 * t + 9) (by omega) ⟨t + 4, by omega⟩]
      push_cast
      ring
    · rw [hO (2 * t + 1 + 2) (by omega) ⟨t + 1, by omega⟩, hE (2 * t + 1 + 3) (by omega) ⟨t + 2, by omega⟩, hO (2 * t + 1 + 4) (by omega) ⟨t + 2, by omega⟩, hE (2 * t + 1 + 5) (by omega) ⟨t + 3, by omega⟩, hO (2 * t + 1 + 6) (by omega) ⟨t + 3, by omega⟩, hE (2 * t + 1 + 7) (by omega) ⟨t + 4, by omega⟩, hO (2 * t + 1 + 8) (by omega) ⟨t + 4, by omega⟩, hE (2 * t + 1 + 9) (by omega) ⟨t + 5, by omega⟩]
      push_cast
      ring

theorem gen_fun202443 :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 2) =
      2 * PowerSeries.X * (169 - 220 * PowerSeries.X - 141 * PowerSeries.X ^ 2 + 424 * PowerSeries.X ^ 3 - 133 * PowerSeries.X ^ 4 - 176 * PowerSeries.X ^ 5 + 137 * PowerSeries.X ^ 6 - 28 * PowerSeries.X ^ 7) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals202443
  exact gf_generic202443 (fun n => (a n : ℚ)) v0 v1 v2 v3 v4 v5 v6 v7 v8 aEQ202443 aOQ202443

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202443.main :=
  ⟨OMA.Helpers.gen_fun202443, OMA.Helpers.aEQ202443, OMA.Helpers.aOQ202443⟩
