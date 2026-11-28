import OMAStatements.S_oeis_a239359

/-!
Proof of Barker's g.f. and recurrence for A239359 (n X 6 0..2 arrays with no element equal,
modulo 3, to one plus the sum of the elements to its left, above it, or diagonally to its
northwest).

Natural-number view. `ent A i j` is the entry at `(i, j)` (0 outside the array); `SL`, `SU`, `SD`
are the sums to the left, above, and on the northwest diagonal, as sums over ranges, and the three
filtered sums of the statement are equal to them (`sumL_eq`, `sumU_eq`, `sumD_eq`, the last by
the bijection `p ↦ i - 1 - p.1`). So `Valid A` is the conjunction `VN A` of the conditions
`CellOK A i j` (`valid_iff`).

Adding a row `r` at the bottom (`Fin.snoc`) does not change the old rows, their sums or their
conditions; the conditions of the new row involve only `r`, the column sums `SU A m j` and the
diagonal sums `SD A m j` of the next row (`vn_snoc`), and the new sums satisfy
`SU (m + 1) j = SU m j + r j` and `SD (m + 1) (j + 1) = SD m j + r j` (`SU_snoc_succ`,
`SD_snoc_succ`).

Automaton. The state `st A` of a valid array is the code of its six column sums and five diagonal
sums (positions 1..5) modulo 3, as eleven base-3 digits (`code`); invalid arrays have the dead
state 177147. Rows have codes below 729. Adding a row changes the state by the explicit
transition `tau` (`st_snoc`, from the digit lemmas `code_dg3`, `code_ddg`, `dg3_rc`, `lsum_rc`).

Tables. `RL` lists the 267 reachable state codes in increasing order, `LV` the 64 row codes that
pass the conditions on the sums to the left, and `SLI u` the indices of the successors of state
`u` under the rows of `LV`. Kernel checks (`chk_RL`, `chk_LV`, `chk_SLI`, with the Boolean copy
`tauB` of the transition) give that every array state is dead or reachable (`reach`) and that the
number of rows from state `u` to state `w` is the number of occurrences of `w` in `SLI u`
(`cnt_rl`).

Counting. With `Ni m u` the number of arrays with `m` rows in the state with index `u`,
`Ni (m + 1) w = Sum_u Ni m u * cntL w (SLI u)` (`Ni_succ`) and `a m = Sum_u Ni m u` (`a_eq`).
The table `GT` of the counts for `m = 0, ..., 18` is checked one step at a time on number
encodings in base `2 ^ 32` (`chk_GT`, `level_step`), which gives `a 1, ..., a 17`. The kernel
also checks `N 18 + 6 N 16 + N 14 = 4 N 17 + 4 N 15` entrywise (`chk_H`); by linearity of the step
this holds for all later shifts (`vec_rec`), and summing over the states gives the recurrence for
every `n > 17`. The generating function follows by comparing coefficients: those of x^0, ..., x^17
from the values, the higher ones vanish by the recurrence.
-/

namespace OMA.Helpers

open OMA.S_oeis_a239359 Finset

/-- A row of an n X 6 array. -/
abbrev Row := Fin 6 → Fin 3

/-- The entry of `A` in row `i` and column `j`, as a natural number (0 outside the array). -/
def ent {m : ℕ} (A : Fin m → Row) (i j : ℕ) : ℕ :=
  if h : i < m ∧ j < 6 then (A ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

theorem ent_fin {m : ℕ} (A : Fin m → Row) (i : Fin m) (j : Fin 6) :
    ent A i.val j.val = (A i j).val := by
  unfold ent
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

theorem ent_lt {m : ℕ} (A : Fin m → Row) (i j : ℕ) : ent A i j < 3 := by
  unfold ent
  split_ifs with h
  · exact (A ⟨i, h.1⟩ ⟨j, h.2⟩).isLt
  · norm_num

theorem sum_fin_lt {n : ℕ} (f : ℕ → ℕ) (b : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => k < b), f k.val = ∑ k ∈ range b.val, f k := by
  rw [Finset.sum_filter]
  have h1 : ∑ k : Fin n, (if k < b then f k.val else 0) =
      ∑ k : Fin n, (fun x => if x < b.val then f x else 0) k.val :=
    Finset.sum_congr rfl fun k _ => by simp only [Fin.lt_def]
  rw [h1, Fin.sum_univ_eq_sum_range (fun x => if x < b.val then f x else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have := b.isLt
  omega

/-- The sum of the entries to the left of `(i, j)`. -/
def SL {m : ℕ} (A : Fin m → Row) (i j : ℕ) : ℕ := ∑ k ∈ range j, ent A i k

/-- The sum of the entries above `(i, j)`. -/
def SU {m : ℕ} (A : Fin m → Row) (i j : ℕ) : ℕ := ∑ k ∈ range i, ent A k j

/-- The sum of the entries diagonally to the northwest of `(i, j)`. -/
def SD {m : ℕ} (A : Fin m → Row) (i j : ℕ) : ℕ :=
  ∑ k ∈ range (min i j), ent A (i - 1 - k) (j - 1 - k)

theorem sumL_eq {m : ℕ} (A : Fin m → Row) (i : Fin m) (j : Fin 6) :
    ∑ k ∈ univ.filter (fun k : Fin 6 => k < j), (A i k).val = SL A i.val j.val := by
  unfold SL
  rw [← sum_fin_lt (fun k => ent A i.val k) j]
  exact Finset.sum_congr rfl fun k _ => (ent_fin A i k).symm

theorem sumU_eq {m : ℕ} (A : Fin m → Row) (i : Fin m) (j : Fin 6) :
    ∑ k ∈ univ.filter (fun k : Fin m => k < i), (A k j).val = SU A i.val j.val := by
  unfold SU
  rw [← sum_fin_lt (fun k => ent A k j.val) i]
  exact Finset.sum_congr rfl fun k _ => (ent_fin A k j).symm

theorem sumD_eq {m : ℕ} (A : Fin m → Row) (i : Fin m) (j : Fin 6) :
    ∑ p ∈ univ.filter (fun p : Fin m × Fin 6 =>
      p.1 < i ∧ p.2 < j ∧ p.1.val + j.val = p.2.val + i.val), (A p.1 p.2).val =
      SD A i.val j.val := by
  unfold SD
  have hi := i.isLt
  have hj := j.isLt
  refine Finset.sum_nbij' (fun p => i.val - 1 - p.1.val)
    (fun k => (⟨i.val - 1 - k, by omega⟩, ⟨j.val - 1 - k, by omega⟩)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
    simp only [Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
    ext
    · simp only
      omega
    · simp only
      omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
    rw [← ent_fin A p.1 p.2]
    congr 1 <;> omega

/-- The conditions of `Valid` at the position `(i, j)`, in terms of natural numbers. -/
def CellOK {m : ℕ} (A : Fin m → Row) (i j : ℕ) : Prop :=
  ent A i j ≠ (1 + SL A i j) % 3 ∧ ent A i j ≠ (1 + SU A i j) % 3 ∧
    ent A i j ≠ (1 + SD A i j) % 3

/-- All conditions of `Valid`, in terms of natural numbers. -/
def VN {m : ℕ} (A : Fin m → Row) : Prop := ∀ i < m, ∀ j < 6, CellOK A i j

theorem valid_iff {m : ℕ} (A : Fin m → Row) : Valid A ↔ VN A := by
  unfold Valid VN
  constructor
  · intro h i hi j hj
    have := h ⟨i, hi⟩ ⟨j, hj⟩
    rw [sumL_eq, sumU_eq, sumD_eq, ← ent_fin] at this
    exact this
  · intro h i j
    rw [sumL_eq, sumU_eq, sumD_eq, ← ent_fin]
    exact h i.val i.isLt j.val j.isLt


/-! ### Adding a row at the bottom -/

/-- The entry of the row `r` in column `j`, as a natural number (0 outside the row). -/
def rv (r : Row) (j : ℕ) : ℕ := if h : j < 6 then (r ⟨j, h⟩).val else 0

theorem ent_snoc_lt {m : ℕ} (A : Fin m → Row) (r : Row) {i : ℕ} (hi : i < m) (j : ℕ) :
    ent (Fin.snoc A r : Fin (m + 1) → Row) i j = ent A i j := by
  unfold ent
  by_cases hj : j < 6
  · rw [dif_pos ⟨by omega, hj⟩, dif_pos ⟨hi, hj⟩]
    have : (⟨i, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg (fun h => hj h.2), dif_neg (fun h => hj h.2)]

theorem ent_snoc_last {m : ℕ} (A : Fin m → Row) (r : Row) (j : ℕ) :
    ent (Fin.snoc A r : Fin (m + 1) → Row) m j = rv r j := by
  unfold ent rv
  by_cases hj : j < 6
  · rw [dif_pos ⟨by omega, hj⟩, dif_pos hj]
    have : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [this, Fin.snoc_last]
  · rw [dif_neg (fun h => hj h.2), dif_neg hj]

/-- The sum of the first `j` entries of the row `r`. -/
def rL (r : Row) (j : ℕ) : ℕ := ∑ k ∈ range j, rv r k

theorem SL_snoc_lt {m : ℕ} (A : Fin m → Row) (r : Row) {i : ℕ} (hi : i < m) (j : ℕ) :
    SL (Fin.snoc A r : Fin (m + 1) → Row) i j = SL A i j := by
  unfold SL
  exact Finset.sum_congr rfl fun k _ => ent_snoc_lt A r hi k

theorem SU_snoc_le {m : ℕ} (A : Fin m → Row) (r : Row) {i : ℕ} (hi : i ≤ m) (j : ℕ) :
    SU (Fin.snoc A r : Fin (m + 1) → Row) i j = SU A i j := by
  unfold SU
  exact Finset.sum_congr rfl fun k hk => ent_snoc_lt A r (by simp at hk; omega) j

theorem SD_snoc_le {m : ℕ} (A : Fin m → Row) (r : Row) {i : ℕ} (hi : i ≤ m) (j : ℕ) :
    SD (Fin.snoc A r : Fin (m + 1) → Row) i j = SD A i j := by
  unfold SD
  exact Finset.sum_congr rfl fun k hk => ent_snoc_lt A r (by simp at hk; omega) _

theorem SL_snoc_last {m : ℕ} (A : Fin m → Row) (r : Row) (j : ℕ) :
    SL (Fin.snoc A r : Fin (m + 1) → Row) m j = rL r j := by
  unfold SL rL
  exact Finset.sum_congr rfl fun k _ => ent_snoc_last A r k

theorem cellOK_snoc_lt {m : ℕ} (A : Fin m → Row) (r : Row) {i : ℕ} (hi : i < m) (j : ℕ) :
    CellOK (Fin.snoc A r : Fin (m + 1) → Row) i j ↔ CellOK A i j := by
  unfold CellOK
  rw [ent_snoc_lt A r hi, SL_snoc_lt A r hi, SU_snoc_le A r hi.le, SD_snoc_le A r hi.le]

theorem cellOK_snoc_last {m : ℕ} (A : Fin m → Row) (r : Row) (j : ℕ) :
    CellOK (Fin.snoc A r : Fin (m + 1) → Row) m j ↔
      rv r j ≠ (1 + rL r j) % 3 ∧ rv r j ≠ (1 + SU A m j) % 3 ∧ rv r j ≠ (1 + SD A m j) % 3 := by
  unfold CellOK
  rw [ent_snoc_last, SL_snoc_last, SU_snoc_le A r le_rfl, SD_snoc_le A r le_rfl]

theorem vn_snoc {m : ℕ} (A : Fin m → Row) (r : Row) :
    VN (Fin.snoc A r : Fin (m + 1) → Row) ↔
      VN A ∧ ∀ j < 6, rv r j ≠ (1 + rL r j) % 3 ∧ rv r j ≠ (1 + SU A m j) % 3 ∧
        rv r j ≠ (1 + SD A m j) % 3 := by
  unfold VN
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, fun j hj => ?_⟩
    · exact (cellOK_snoc_lt A r hi j).mp (h i (by omega) j hj)
    · exact (cellOK_snoc_last A r j).mp (h m (by omega) j hj)
  · rintro ⟨h1, h2⟩ i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact (cellOK_snoc_lt A r hi' j).mpr (h1 i hi' j hj)
    · exact (cellOK_snoc_last A r j).mpr (h2 j hj)

theorem SU_snoc_succ {m : ℕ} (A : Fin m → Row) (r : Row) (j : ℕ) :
    SU (Fin.snoc A r : Fin (m + 1) → Row) (m + 1) j = SU A m j + rv r j := by
  unfold SU
  rw [Finset.sum_range_succ, ent_snoc_last]
  congr 1
  exact Finset.sum_congr rfl fun k hk => ent_snoc_lt A r (by simp at hk; omega) j

theorem SD_snoc_succ {m : ℕ} (A : Fin m → Row) (r : Row) (j : ℕ) :
    SD (Fin.snoc A r : Fin (m + 1) → Row) (m + 1) (j + 1) = SD A m j + rv r j := by
  unfold SD
  rw [show min (m + 1) (j + 1) = min m j + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  rw [ent_snoc_last]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [show m - (k + 1) = m - 1 - k by omega, show j - (k + 1) = j - 1 - k by omega]
  exact ent_snoc_lt A r (by omega) _

theorem SD_zero {m : ℕ} (A : Fin m → Row) (i : ℕ) : SD A i 0 = 0 := by
  unfold SD
  simp


/-! ### Codes of rows and states -/

/-- Digit `j` of `x` in base 3. -/
def dg3 (x j : ℕ) : ℕ := x / 3 ^ j % 3

theorem dg3_lt (x j : ℕ) : dg3 x j < 3 := Nat.mod_lt _ (by norm_num)

/-- The sum of the digits `0, ..., j - 1` of `c`. -/
def lsum (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => lsum c j + dg3 c j

/-- The diagonal digit `j` of a state code `s` (0 for `j = 0`). -/
def ddg (s j : ℕ) : ℕ := if j = 0 then 0 else dg3 s (j + 5)

/-- The state code with column digits `cf 0, ..., cf 5` and diagonal digits `df 1, ..., df 5`. -/
def code (cf df : ℕ → ℕ) : ℕ :=
  cf 0 + 3 * cf 1 + 9 * cf 2 + 27 * cf 3 + 81 * cf 4 + 243 * cf 5 + 729 * df 1 + 2187 * df 2 +
    6561 * df 3 + 19683 * df 4 + 59049 * df 5

/-- The code `c` of a row satisfies the conditions involving the sums to the left. -/
def rowL (c : ℕ) : Prop := ∀ j < 6, dg3 c j ≠ (1 + lsum c j) % 3

/-- The code `c` of a row satisfies the conditions involving the state `s` of the rows above. -/
def rowS (s c : ℕ) : Prop := ∀ j < 6, dg3 c j ≠ (1 + dg3 s j) % 3 ∧ dg3 c j ≠ (1 + ddg s j) % 3

instance rowLDec (c : ℕ) : Decidable (rowL c) :=
  inferInstanceAs (Decidable (∀ j < 6, dg3 c j ≠ (1 + lsum c j) % 3))

instance rowSDec (s c : ℕ) : Decidable (rowS s c) :=
  inferInstanceAs (Decidable (∀ j < 6, dg3 c j ≠ (1 + dg3 s j) % 3 ∧ dg3 c j ≠ (1 + ddg s j) % 3))

/-- The transition of the automaton on the row with code `c` (177147 is the dead state). -/
def tau (s c : ℕ) : ℕ :=
  if s < 177147 ∧ rowL c ∧ rowS s c then
    code (fun j => (dg3 s j + dg3 c j) % 3) (fun j => (dg3 c (j - 1) + ddg s (j - 1)) % 3)
  else 177147

theorem tau_dead (c : ℕ) : tau 177147 c = 177147 := by
  unfold tau
  rw [if_neg (by omega)]

theorem code_lt (cf df : ℕ → ℕ) (hc : ∀ j, cf j < 3) (hd : ∀ j, df j < 3) :
    code cf df < 177147 := by
  unfold code
  have := hc 0; have := hc 1; have := hc 2; have := hc 3; have := hc 4; have := hc 5
  have := hd 1; have := hd 2; have := hd 3; have := hd 4; have := hd 5
  omega

theorem code_dg3 (cf df : ℕ → ℕ) (hc : ∀ j, cf j < 3) (hd : ∀ j, df j < 3) :
    ∀ j < 6, dg3 (code cf df) j = cf j := by
  have := hc 0; have := hc 1; have := hc 2; have := hc 3; have := hc 4; have := hc 5
  have := hd 1; have := hd 2; have := hd 3; have := hd 4; have := hd 5
  intro j hj
  interval_cases j <;> simp only [dg3, code] <;> norm_num <;> omega

theorem code_ddg (cf df : ℕ → ℕ) (hc : ∀ j, cf j < 3) (hd : ∀ j, df j < 3) :
    ∀ j < 6, ddg (code cf df) j = if j = 0 then 0 else df j := by
  have := hc 0; have := hc 1; have := hc 2; have := hc 3; have := hc 4; have := hc 5
  have := hd 1; have := hd 2; have := hd 3; have := hd 4; have := hd 5
  intro j hj
  interval_cases j <;> simp only [ddg, dg3, code] <;> norm_num <;> omega

theorem code_congr {cf df cf' df' : ℕ → ℕ} (hc : ∀ j < 6, cf j = cf' j)
    (hd : ∀ j < 5, df (j + 1) = df' (j + 1)) : code cf df = code cf' df' := by
  unfold code
  rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), hc 3 (by norm_num),
    hc 4 (by norm_num), hc 5 (by norm_num), hd 0 (by norm_num), hd 1 (by norm_num),
    hd 2 (by norm_num), hd 3 (by norm_num), hd 4 (by norm_num)]

/-- The code of the row `r`. -/
def rc (r : Row) : ℕ :=
  (r 0).val + 3 * (r 1).val + 9 * (r 2).val + 27 * (r 3).val + 81 * (r 4).val + 243 * (r 5).val

/-- The row with code `c < 729`. -/
def rowOf (c : ℕ) : Row := fun j => ⟨c / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem rc_lt (r : Row) : rc r < 729 := by
  unfold rc
  have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt
  have := (r 3).isLt; have := (r 4).isLt; have := (r 5).isLt
  omega

theorem rowOf_rc (r : Row) : rowOf (rc r) = r := by
  funext j
  apply Fin.ext
  have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt
  have := (r 3).isLt; have := (r 4).isLt; have := (r 5).isLt
  fin_cases j <;> simp [rowOf, rc] <;> omega

theorem rc_rowOf (c : ℕ) (hc : c < 729) : rc (rowOf c) = c := by
  unfold rc rowOf
  simp
  omega

theorem dg3_rc (r : Row) : ∀ j < 6, dg3 (rc r) j = rv r j := by
  have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt
  have := (r 3).isLt; have := (r 4).isLt; have := (r 5).isLt
  intro j hj
  interval_cases j <;> simp [dg3, rc, rv] <;> omega

theorem lsum_rc (r : Row) : ∀ j ≤ 6, lsum (rc r) j = rL r j := by
  intro j hj
  induction j with
  | zero => simp [lsum, rL]
  | succ j ih =>
    rw [lsum, ih (by omega), dg3_rc r j (by omega), rL, rL, Finset.sum_range_succ]


/-! ### The state of an array -/

/-- The state code of an array with `m` rows: its column sums and the northwest-diagonal sums of
the positions of a next row, modulo 3, if it is valid; 177147 (dead) otherwise. -/
noncomputable def st {m : ℕ} (A : Fin m → Row) : ℕ := by
  classical
  exact if VN A then code (fun j => SU A m j % 3) (fun j => SD A m j % 3) else 177147

theorem st_snoc {m : ℕ} (A : Fin m → Row) (r : Row) :
    st (Fin.snoc A r : Fin (m + 1) → Row) = tau (st A) (rc r) := by
  classical
  unfold st
  by_cases hA : VN A
  · rw [if_pos hA]
    have hc : ∀ j, (fun j => SU A m j % 3) j < 3 := fun j => Nat.mod_lt _ (by norm_num)
    have hd : ∀ j, (fun j => SD A m j % 3) j < 3 := fun j => Nat.mod_lt _ (by norm_num)
    have hslt := code_lt _ _ hc hd
    have hdg := code_dg3 _ _ hc hd
    have hdd : ∀ j < 6, ddg (code (fun j => SU A m j % 3) (fun j => SD A m j % 3)) j =
        SD A m j % 3 := by
      intro j hj
      rw [code_ddg _ _ hc hd j hj]
      split_ifs with h
      · subst h
        rw [SD_zero]
      · rfl
    have key : (code (fun j => SU A m j % 3) (fun j => SD A m j % 3) < 177147 ∧ rowL (rc r) ∧
        rowS (code (fun j => SU A m j % 3) (fun j => SD A m j % 3)) (rc r)) ↔
        VN (Fin.snoc A r : Fin (m + 1) → Row) := by
      rw [vn_snoc]
      constructor
      · rintro ⟨_, hL, hS⟩
        refine ⟨hA, fun j hj => ?_⟩
        have h1 := hL j hj
        have h2 := hS j hj
        rw [dg3_rc r j hj, lsum_rc r j (by omega)] at h1
        rw [dg3_rc r j hj, hdg j hj, hdd j hj] at h2
        refine ⟨h1, fun h => h2.1 ?_, fun h => h2.2 ?_⟩
        · rw [h]
          omega
        · rw [h]
          omega
      · rintro ⟨_, h⟩
        refine ⟨hslt, fun j hj => ?_, fun j hj => ?_⟩
        · rw [dg3_rc r j hj, lsum_rc r j (by omega)]
          exact (h j hj).1
        · rw [dg3_rc r j hj, hdg j hj, hdd j hj]
          obtain ⟨_, h2, h3⟩ := h j hj
          refine ⟨fun e => h2 ?_, fun e => h3 ?_⟩
          · rw [e]
            omega
          · rw [e]
            omega
    unfold tau
    by_cases hB : VN (Fin.snoc A r : Fin (m + 1) → Row)
    · rw [if_pos hB, if_pos (key.mpr hB)]
      apply code_congr
      · intro j hj
        rw [SU_snoc_succ, hdg j hj, dg3_rc r j hj]
        omega
      · intro j hj
        rw [SD_snoc_succ, Nat.add_sub_cancel, dg3_rc r j (by omega), hdd j (by omega)]
        omega
    · rw [if_neg hB, if_neg (fun h => hB (key.mp h))]
  · rw [if_neg hA, if_neg (fun h => hA ((vn_snoc A r).mp h).1), tau_dead]

theorem st_lt_iff {m : ℕ} (A : Fin m → Row) : st A < 177147 ↔ VN A := by
  classical
  unfold st
  by_cases h : VN A
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => code_lt _ _ (fun j => Nat.mod_lt _ (by norm_num))
      (fun j => Nat.mod_lt _ (by norm_num))⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' h⟩

theorem st_le {m : ℕ} (A : Fin m → Row) : st A ≤ 177147 := by
  classical
  unfold st
  split_ifs
  · exact (code_lt _ _ (fun j => Nat.mod_lt _ (by norm_num))
      (fun j => Nat.mod_lt _ (by norm_num))).le
  · exact le_rfl

theorem st_zero (A : Fin 0 → Row) : st A = 0 := by
  classical
  unfold st
  rw [if_pos (show VN A from fun i hi => absurd hi (Nat.not_lt_zero _))]
  simp [code, SU, SD]


/-! ### A Boolean transition for the kernel -/

/-- The conditions of the row code `c` against the state code `s` in column `j`, as a Boolean. -/
def okS (s c j : ℕ) : Bool :=
  !(Nat.beq (dg3 c j) ((1 + dg3 s j) % 3)) && !(Nat.beq (dg3 c j) ((1 + ddg s j) % 3))

/-- `rowS` as a Boolean. -/
def rowSb (s c : ℕ) : Bool :=
  okS s c 0 && okS s c 1 && okS s c 2 && okS s c 3 && okS s c 4 && okS s c 5

/-- The transition on a row code satisfying `rowL`, computed with Booleans. -/
def tauB (s c : ℕ) : ℕ :=
  bif Nat.blt s 177147 && rowSb s c then
    code (fun j => (dg3 s j + dg3 c j) % 3) (fun j => (dg3 c (j - 1) + ddg s (j - 1)) % 3)
  else 177147

theorem forall_lt_six (P : ℕ → Prop) :
    (∀ j < 6, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
      h 4 (by norm_num), h 5 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ j hj
    interval_cases j <;> assumption

theorem okS_iff (s c j : ℕ) : okS s c j = true ↔
    (dg3 c j ≠ (1 + dg3 s j) % 3 ∧ dg3 c j ≠ (1 + ddg s j) % 3) := by
  unfold okS
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.beq_eq]

theorem rowSb_iff (s c : ℕ) : rowSb s c = true ↔ rowS s c := by
  unfold rowSb rowS
  rw [forall_lt_six]
  simp only [Bool.and_eq_true, okS_iff, and_assoc]

theorem tauB_eq (s c : ℕ) (hc : rowL c) : tauB s c = tau s c := by
  unfold tauB tau
  by_cases h : s < 177147 ∧ rowS s c
  · have hb : (Nat.blt s 177147 && rowSb s c) = true := by
      rw [Bool.and_eq_true, Nat.blt_eq, rowSb_iff]
      exact h
    rw [hb, if_pos ⟨h.1, hc, h.2⟩]
    rfl
  · have hb : (Nat.blt s 177147 && rowSb s c) = false := by
      rw [← Bool.not_eq_true, Bool.and_eq_true, Nat.blt_eq, rowSb_iff]
      exact h
    rw [hb, if_neg (fun h' => h ⟨h'.1, h'.2.2⟩)]
    rfl

theorem tau_live (s c : ℕ) (h : tau s c ≠ 177147) : rowL c := by
  unfold tau at h
  split_ifs at h with h'
  · exact h'.2.1
  · exact absurd rfl h

/-! ### Counting arrays by states -/

theorem sum_snoc (m : ℕ) (F : (Fin m → Row) → Row → ℕ) :
    ∑ B : Fin (m + 1) → Row, F (Fin.init B) (B (Fin.last m)) =
      ∑ β : Fin m → Row, ∑ γ : Row, F β γ := by
  calc ∑ B : Fin (m + 1) → Row, F (Fin.init B) (B (Fin.last m))
      = ∑ p : Row × (Fin m → Row), F p.2 p.1 :=
        (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Row)) (fun p => F p.2 p.1) _
          (fun p => by
            rw [show (Fin.snocEquiv (fun _ => Row)) p = Fin.snoc p.2 p.1 from rfl,
              Fin.init_snoc, Fin.snoc_last])).symm
    _ = ∑ γ : Row, ∑ β : Fin m → Row, F β γ := Fintype.sum_prod_type' (fun γ β => F β γ)
    _ = ∑ β : Fin m → Row, ∑ γ : Row, F β γ := Finset.sum_comm

theorem sum_row (F : ℕ → ℕ) : ∑ γ : Row, F (rc γ) = ∑ c ∈ range 729, F c :=
  Finset.sum_nbij' rc rowOf (fun γ _ => Finset.mem_range.mpr (rc_lt γ))
    (fun _ _ => Finset.mem_univ _) (fun γ _ => rowOf_rc γ)
    (fun c hc => rc_rowOf c (Finset.mem_range.mp hc)) (fun _ _ => rfl)

theorem sum_fiber {X : Type*} [Fintype X] (r : X → ℕ) (hr : ∀ x, r x < 177148) (h : ℕ → ℕ) :
    ∑ x, h (r x) = ∑ s ∈ range 177148, (∑ x, if r x = s then 1 else 0) * h s := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hr x))]

/-- The number of rows leading from the state `s` to the state `t`. -/
def cnt (s t : ℕ) : ℕ := ∑ c ∈ range 729, if tau s c = t then 1 else 0

/-- The number of arrays with `m` rows in the state `s`. -/
noncomputable def N (m s : ℕ) : ℕ := ∑ A : Fin m → Row, if st A = s then 1 else 0

theorem N_zero (s : ℕ) : N 0 s = if s = 0 then 1 else 0 := by
  unfold N
  rw [Fintype.sum_unique, st_zero]
  by_cases h : s = 0
  · subst h
    rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem N_succ (m t : ℕ) : N (m + 1) t = ∑ s ∈ range 177148, N m s * cnt s t := by
  have h0 : N (m + 1) t = ∑ B : Fin (m + 1) → Row,
      if tau (st (Fin.init B)) (rc (B (Fin.last m))) = t then 1 else 0 := by
    unfold N
    refine Finset.sum_congr rfl fun B _ => ?_
    have h := st_snoc (Fin.init B) (B (Fin.last m))
    rw [Fin.snoc_init_self] at h
    rw [h]
  have h3 : ∀ β : Fin m → Row, (∑ γ : Row, if tau (st β) (rc γ) = t then 1 else 0) =
      cnt (st β) t := fun β => sum_row (fun c => if tau (st β) c = t then 1 else 0)
  rw [h0, sum_snoc m (fun β γ => if tau (st β) (rc γ) = t then 1 else 0),
    Finset.sum_congr rfl (fun β _ => h3 β),
    sum_fiber (fun β : Fin m → Row => st β) (fun β => Nat.lt_succ_of_le (st_le β))
      (fun s => cnt s t)]
  rfl


/-! ### Tables -/

/-- The 267 reachable state codes, in increasing order. -/
def RL : List ℕ :=
  [0, 13, 39, 40, 94, 117, 120, 121, 243, 256, 282, 283, 324, 337, 351, 360, 363, 364, 486, 499,
    525, 526, 567, 580, 603, 606, 607, 5840, 5855, 5876, 5921, 5936, 5948, 5957, 5972, 6029, 6083,
    6098, 6110, 6119, 6134, 6164, 6179, 6191, 6200, 6215, 6341, 6407, 6434, 6443, 6458, 17520,
    17565, 17601, 17628, 17673, 17709, 17763, 17790, 17808, 17844, 17871, 17916, 18051, 18087,
    18114, 18159, 19696, 19722, 19777, 19939, 19965, 20020, 25565, 25574, 25646, 25655, 25808,
    25817, 25889, 25898, 26132, 26284, 26446, 26527, 26770, 33246, 33489, 35032, 35275, 35680,
    37255, 37498, 37741, 39649, 39798, 39811, 39879, 39892, 40041, 40054, 43168, 43546, 43654,
    47455, 47458, 47518, 47536, 47539, 47680, 47698, 47701, 47761, 47779, 47782, 52560, 52641,
    52695, 52803, 52884, 52938, 53019, 53127, 53181, 54853, 54904, 54985, 55096, 55147, 55339,
    55390, 59062, 59088, 59089, 59143, 59166, 59169, 59170, 59305, 59331, 59332, 59386, 59400,
    59409, 59412, 59413, 59481, 59494, 59548, 59574, 59629, 65006, 65492, 65623, 65704, 65866,
    65947, 66109, 72558, 72639, 72801, 72828, 76695, 76722, 76938, 76965, 78772, 78852, 78853,
    79015, 79095, 79096, 79258, 79338, 85333, 85414, 85576, 85657, 85738, 85900, 96385, 96628,
    96871, 98536, 98617, 99009, 99022, 99103, 105096, 105582, 106486, 106567, 106729, 106810,
    111765, 112008, 113872, 113902, 113953, 114145, 114196, 114439, 118179, 118192, 118218, 118219,
    118273, 118299, 118422, 118435, 118461, 118462, 118503, 118516, 118542, 118543, 118665, 118678,
    118692, 118704, 118705, 118746, 118759, 118785, 118786, 124136, 124244, 124271, 124358, 124379,
    124514, 124556, 124601, 124622, 129180, 129504, 137925, 137956, 138141, 138384, 138442, 142311,
    142365, 142374, 142554, 142608, 142617, 142797, 144544, 145030, 157599, 157612, 157680, 157693,
    157774, 157923, 157936, 158017, 158085, 158098, 158148, 158179, 164226, 164469, 164559, 164712,
    166183]

/-- The 64 row codes that satisfy the conditions involving the sums to the left. -/
def LV : List ℕ :=
  [0, 5, 8, 15, 24, 44, 45, 50, 71, 72, 77, 116, 132, 135, 140, 150, 197, 213, 216, 221, 231, 251,
    267, 314, 315, 320, 332, 348, 395, 396, 401, 405, 410, 420, 440, 449, 450, 455, 456, 459, 464,
    474, 486, 491, 501, 530, 531, 536, 575, 591, 602, 618, 621, 626, 636, 638, 639, 644, 648, 653,
    663, 692, 693, 698]

/-- For each reachable state (by index), the indices of the states reached by the rows of `LV`,
in the order of `LV`. -/
def SLI : List (List ℕ) :=
  [[0, 27, 51, 115, 252, 18, 221], [1, 253, 19, 222], [2, 20, 223], [3, 21, 224], [4, 23],
    [5, 33, 24], [6, 25], [7, 26], [8, 36, 57, 118, 255], [9, 256], [10], [11], [12, 41, 60, 119],
    [13], [14, 43, 61], [15, 44], [16], [17], [8, 212], [9, 213], [10, 214], [11, 215], [12], [13],
    [15], [16], [17], [105], [104], [], [108], [107], [], [], [106], [], [111], [110], [], [],
    [109], [114], [113], [], [], [112], [], [], [], [], [], [74, 243], [28, 73, 242, 46, 232], [76],
    [34, 50], [241], [234, 231], [78, 246], [40, 235], [37, 77, 245], [80], [45], [244], [37, 228],
    [], [45], [], [131, 148], [132, 149], [134, 253, 150, 261], [138], [139], [141, 256], [], [190],
    [], [191, 266], [], [192], [], [193], [], [166, 172], [], [169], [169], [226], [226], [], [],
    [], [153, 174, 157], [155, 176], [155], [], [], [], [146], [147], [38, 58, 142], [145], [], [],
    [], [], [197], [125, 90, 130], [], [124, 129], [200], [], [199], [128], [], [127], [163, 161],
    [55, 66, 87], [52, 162, 63, 160], [165], [62], [59, 164], [159], [62, 86], [59, 158],
    [91, 180, 93], [82, 175, 85], [178], [92, 181], [84, 177], [92], [84], [1, 253], [2], [3], [4],
    [5, 33], [6], [7], [9, 256, 222, 261], [10, 223], [11, 224], [13], [14, 43, 61, 48, 65],
    [15, 44, 49], [16], [17], [218], [220], [206, 253], [207], [], [], [], [67], [69], [70, 240],
    [72], [237], [], [227, 238, 230, 239], [], [236], [31, 75], [241], [42, 79, 81], [244, 247],
    [133], [136], [137], [140], [144], [145], [], [], [166], [168], [169], [171], [], [],
    [154, 175], [156, 177, 179, 249], [175, 248], [], [], [35, 56], [], [137], [], [], [198], [125],
    [200, 201], [128, 90], [68, 167], [71, 170, 173], [83], [91, 180], [82, 175], [92, 181, 182],
    [84, 177, 179], [175], [22], [23], [25], [26], [217], [219], [47, 64, 122], [], [], [],
    [216, 258], [217, 259], [219], [220], [30, 53, 116, 12], [13], [32, 54, 14], [16], [17],
    [202, 250, 208], [203, 251, 209], [204, 210], [205, 211], [], [102], [103], [], [], [101],
    [106], [], [], [], [], [260], [257], [152, 233], [151, 225, 143, 229], [254], [265], [], [264],
    [189, 265], [], [264], [188, 262, 263], [], [], [99, 123], [100], [97, 121], [98], [187],
    [121, 185], [186], [184], [117, 95, 120], [96], [29, 135, 39, 143], [183, 94], [173], [173],
    [194, 195], [167, 170], [88, 196, 89, 126]]

/-- The counts of the arrays with `m` rows in each reachable state, for `m = 0, ..., 18`. -/
def GT : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 1, 1, 0, 0, 1, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 2, 0, 1, 2, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0,
    0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 2,
    0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 3, 1, 1, 1, 1, 2, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1,
    1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 1, 1, 3, 2, 1, 3, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 2,
    1, 1, 1, 1, 1, 2, 0, 2, 0, 0, 2, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 0, 1, 0, 1, 0, 0, 3,
    0, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0],
   [1, 0, 0, 0, 0, 1, 0, 0, 5, 0, 0, 0, 6, 0, 4, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1,
    1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3, 1,
    1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 3, 0, 0, 2, 1, 1, 1, 4, 4, 1, 4, 1, 1, 1, 0, 0, 0,
    0, 1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 2, 2, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 3,
    1, 1, 1, 1, 1, 3, 2, 2, 2, 0, 2, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 1, 2, 1, 1,
    2, 0, 2, 2, 0, 1, 1, 2, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 2, 1, 1, 3, 2, 3, 2, 0, 0, 1, 0, 1, 0, 0, 4,
    0, 0, 1, 0, 1, 0, 1, 1, 3, 3, 1],
   [1, 0, 1, 0, 0, 2, 2, 0, 6, 0, 1, 0, 8, 0, 6, 4, 2, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1,
    1, 2, 1, 3, 5, 3, 1, 1, 1, 6, 1, 5, 4, 4, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6, 5, 5, 1,
    1, 1, 1, 1, 2, 1, 0, 2, 0, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 2, 3, 1, 0, 1,
    0, 1, 0, 1, 0, 2, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 1, 5, 6, 1, 5, 1, 1, 1, 1, 1, 2,
    0, 1, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 0, 1, 3, 2, 0, 1, 0, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4,
    1, 1, 1, 1, 1, 4, 2, 5, 2, 0, 5, 0, 1, 4, 1, 4, 1, 2, 0, 2, 2, 2, 2, 0, 0, 4, 0, 0, 2, 3, 1, 1,
    3, 2, 3, 3, 1, 1, 1, 3, 3, 2, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1,
    0, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3, 0, 2, 1, 1, 6, 2, 4, 3, 1, 1, 1, 0, 1, 1, 0, 5,
    0, 1, 1, 0, 1, 1, 2, 2, 4, 5, 1],
   [1, 1, 2, 2, 1, 3, 4, 2, 7, 0, 2, 0, 10, 0, 8, 8, 4, 0, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 1, 1, 1,
    1, 3, 1, 4, 6, 3, 1, 1, 1, 8, 1, 7, 7, 6, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 8, 7, 7, 1,
    1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 1,
    0, 1, 1, 1, 0, 3, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5, 4, 1, 6, 1, 1, 1, 6, 8, 1, 6, 1, 1, 1, 3, 1, 4,
    4, 1, 2, 1, 2, 2, 1, 1, 5, 2, 0, 2, 0, 0, 1, 4, 5, 0, 1, 0, 1, 2, 1, 3, 3, 2, 2, 4, 2, 2, 1, 5,
    1, 1, 1, 1, 1, 5, 2, 8, 4, 2, 8, 2, 1, 7, 2, 8, 3, 5, 1, 5, 2, 5, 3, 1, 1, 5, 0, 0, 3, 6, 1, 1,
    4, 4, 4, 4, 1, 1, 1, 4, 4, 3, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 2,
    0, 3, 2, 4, 1, 3, 4, 3, 1, 3, 3, 1, 1, 1, 4, 4, 1, 2, 1, 1, 9, 2, 5, 4, 2, 2, 1, 0, 1, 3, 0, 6,
    0, 1, 1, 0, 1, 1, 3, 3, 5, 8, 1],
   [1, 2, 4, 4, 2, 4, 9, 4, 8, 0, 5, 0, 12, 0, 10, 14, 12, 0, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1,
    1, 1, 4, 1, 5, 7, 3, 1, 1, 1, 10, 1, 9, 12, 8, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 7, 1, 2, 10, 9,
    9, 1, 1, 1, 1, 2, 4, 2, 4, 4, 2, 1, 1, 1, 1, 2, 6, 1, 8, 1, 4, 1, 10, 3, 1, 1, 1, 1, 7, 2, 9, 1,
    1, 1, 0, 1, 3, 1, 0, 4, 2, 4, 1, 1, 4, 1, 1, 1, 3, 6, 6, 1, 8, 1, 1, 1, 7, 10, 1, 7, 1, 1, 1, 4,
    1, 6, 8, 1, 3, 1, 3, 2, 1, 1, 8, 4, 1, 3, 2, 1, 1, 5, 8, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2, 7, 5, 2,
    1, 6, 1, 1, 1, 1, 1, 6, 4, 12, 8, 7, 12, 5, 2, 10, 2, 12, 6, 13, 1, 9, 2, 8, 4, 1, 1, 6, 0, 0,
    4, 9, 1, 1, 5, 6, 5, 5, 1, 1, 1, 5, 5, 4, 1, 0, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    0, 1, 1, 4, 2, 4, 2, 5, 1, 4, 5, 4, 1, 4, 4, 1, 1, 2, 5, 5, 4, 2, 1, 1, 12, 2, 6, 5, 3, 5, 1, 0,
    1, 4, 1, 7, 1, 1, 1, 0, 1, 1, 4, 4, 6, 11, 1],
   [1, 3, 7, 6, 3, 5, 17, 8, 9, 2, 10, 4, 14, 3, 12, 22, 26, 4, 1, 2, 4, 4, 1, 2, 4, 11, 4, 1, 1, 1,
    1, 1, 1, 5, 1, 6, 8, 3, 1, 1, 1, 12, 1, 11, 19, 10, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 8, 1, 2,
    12, 11, 11, 1, 1, 1, 1, 2, 5, 2, 7, 5, 5, 1, 1, 1, 1, 2, 7, 1, 10, 1, 5, 1, 16, 4, 1, 1, 1, 1,
    10, 2, 12, 1, 1, 1, 0, 1, 4, 1, 0, 5, 2, 5, 1, 1, 5, 1, 1, 1, 3, 7, 8, 1, 10, 1, 1, 1, 8, 12, 1,
    8, 1, 1, 1, 5, 1, 8, 12, 1, 4, 2, 4, 4, 2, 1, 12, 8, 4, 4, 7, 2, 1, 6, 12, 5, 1, 3, 2, 4, 2, 5,
    5, 2, 2, 10, 8, 2, 1, 7, 1, 1, 1, 1, 1, 7, 6, 16, 12, 19, 16, 13, 4, 13, 2, 15, 9, 21, 1, 13, 2,
    11, 5, 1, 1, 7, 1, 1, 5, 12, 1, 1, 6, 8, 6, 6, 1, 1, 1, 6, 6, 5, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2,
    1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7, 6, 5, 2, 6, 1, 5, 6, 5, 1, 5, 5, 1, 1, 2, 6, 6, 7, 2, 1, 1,
    15, 2, 7, 6, 4, 8, 1, 1, 1, 6, 4, 8, 3, 2, 1, 0, 1, 3, 5, 5, 7, 14, 1],
   [1, 5, 11, 10, 5, 6, 29, 16, 10, 8, 18, 15, 16, 8, 14, 32, 52, 14, 1, 3, 7, 6, 1, 4, 5, 21, 10,
    1, 1, 1, 1, 1, 1, 6, 1, 7, 9, 3, 1, 1, 1, 14, 1, 13, 28, 12, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 9,
    1, 2, 14, 13, 13, 1, 1, 1, 1, 2, 6, 2, 10, 6, 8, 1, 1, 1, 1, 2, 8, 1, 12, 1, 6, 1, 22, 5, 1, 1,
    1, 1, 13, 2, 15, 1, 3, 1, 0, 1, 6, 1, 1, 6, 2, 6, 1, 1, 6, 1, 1, 1, 3, 8, 10, 1, 12, 1, 1, 1, 9,
    14, 1, 9, 1, 1, 1, 6, 1, 10, 16, 1, 5, 2, 5, 6, 2, 1, 16, 13, 7, 5, 19, 5, 1, 7, 16, 13, 1, 4,
    2, 5, 2, 6, 6, 2, 2, 13, 11, 2, 1, 8, 1, 1, 1, 1, 1, 8, 7, 20, 15, 29, 20, 21, 5, 16, 2, 18, 12,
    29, 1, 17, 2, 14, 6, 3, 2, 8, 3, 4, 6, 15, 1, 1, 7, 10, 7, 7, 1, 1, 1, 7, 7, 6, 1, 3, 7, 6, 2,
    4, 1, 3, 7, 6, 1, 2, 4, 4, 1, 2, 1, 5, 5, 1, 7, 11, 13, 6, 2, 7, 1, 6, 7, 6, 1, 6, 6, 1, 1, 2,
    7, 7, 10, 2, 1, 1, 18, 2, 8, 7, 5, 11, 1, 3, 1, 9, 7, 9, 11, 2, 1, 1, 1, 6, 6, 6, 8, 17, 1],
   [1, 7, 16, 16, 7, 7, 45, 29, 11, 18, 30, 40, 18, 19, 16, 44, 94, 42, 1, 5, 11, 10, 1, 8, 6, 36,
    22, 1, 1, 1, 1, 1, 1, 7, 1, 8, 10, 3, 1, 1, 1, 16, 1, 15, 39, 14, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1,
    8, 10, 1, 2, 16, 15, 15, 1, 1, 1, 1, 2, 7, 2, 13, 7, 11, 1, 1, 1, 1, 2, 9, 1, 14, 1, 7, 1, 28,
    6, 1, 1, 1, 1, 16, 2, 18, 1, 6, 1, 1, 1, 9, 1, 3, 7, 2, 7, 1, 1, 7, 1, 1, 1, 3, 9, 12, 1, 14, 1,
    1, 1, 10, 16, 1, 10, 1, 1, 1, 7, 1, 12, 20, 1, 6, 2, 6, 7, 2, 1, 20, 19, 10, 6, 29, 8, 1, 8, 20,
    22, 1, 6, 2, 6, 2, 7, 7, 2, 2, 16, 14, 2, 1, 9, 1, 1, 1, 1, 1, 9, 8, 24, 18, 39, 24, 29, 6, 19,
    2, 21, 15, 37, 1, 21, 2, 17, 7, 6, 2, 9, 11, 7, 7, 18, 1, 1, 8, 12, 8, 8, 1, 1, 1, 8, 8, 7, 1,
    7, 11, 13, 2, 5, 1, 7, 11, 13, 1, 3, 7, 6, 1, 4, 1, 8, 8, 1, 12, 16, 29, 7, 2, 8, 1, 7, 8, 7, 1,
    7, 7, 1, 1, 2, 8, 8, 13, 2, 1, 1, 21, 2, 9, 8, 6, 14, 1, 7, 1, 11, 10, 10, 23, 2, 1, 2, 1, 9, 7,
    7, 9, 20, 1],
   [1, 9, 22, 23, 9, 8, 65, 48, 12, 33, 47, 79, 20, 39, 18, 58, 158, 94, 1, 7, 16, 16, 1, 14, 7, 56,
    42, 1, 1, 1, 1, 1, 1, 8, 1, 9, 11, 3, 1, 1, 1, 18, 1, 17, 52, 16, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1,
    9, 11, 1, 2, 18, 17, 17, 1, 1, 1, 1, 2, 8, 2, 16, 8, 14, 1, 1, 1, 1, 2, 10, 1, 16, 1, 8, 1, 34,
    7, 1, 1, 1, 1, 19, 2, 21, 1, 9, 1, 2, 1, 11, 1, 7, 8, 2, 8, 1, 1, 8, 1, 1, 1, 3, 10, 14, 1, 16,
    1, 1, 1, 11, 18, 1, 11, 1, 1, 1, 8, 1, 14, 24, 1, 7, 2, 7, 8, 2, 1, 24, 25, 13, 7, 39, 11, 1, 9,
    24, 32, 1, 9, 2, 7, 2, 8, 8, 2, 2, 19, 17, 2, 1, 10, 1, 1, 1, 1, 1, 10, 9, 28, 21, 49, 28, 37,
    7, 22, 2, 24, 18, 45, 1, 25, 2, 20, 8, 9, 2, 10, 23, 10, 8, 21, 1, 1, 9, 14, 9, 9, 1, 1, 1, 9,
    9, 8, 1, 12, 16, 29, 2, 6, 1, 12, 16, 29, 1, 5, 11, 10, 1, 5, 1, 12, 12, 1, 17, 22, 45, 8, 2, 9,
    1, 8, 9, 8, 1, 8, 8, 1, 1, 2, 9, 9, 16, 2, 1, 1, 24, 2, 10, 9, 7, 17, 1, 12, 1, 13, 13, 11, 39,
    2, 1, 3, 1, 12, 8, 8, 10, 23, 1],
   [1, 11, 29, 31, 11, 9, 89, 73, 13, 53, 70, 134, 22, 69, 20, 74, 250, 180, 1, 9, 22, 23, 1, 21, 8,
    81, 77, 1, 1, 1, 1, 1, 1, 9, 1, 10, 12, 3, 1, 1, 1, 20, 1, 19, 67, 18, 1, 1, 1, 9, 1, 1, 1, 1,
    1, 1, 10, 12, 1, 2, 20, 19, 19, 1, 1, 1, 1, 2, 9, 2, 19, 9, 17, 1, 1, 1, 1, 2, 11, 1, 18, 1, 9,
    1, 40, 8, 1, 1, 1, 1, 22, 2, 24, 1, 12, 1, 3, 1, 13, 1, 12, 9, 2, 9, 1, 1, 9, 1, 1, 1, 3, 11,
    16, 1, 18, 1, 1, 1, 12, 20, 1, 12, 1, 1, 1, 9, 1, 16, 28, 1, 8, 2, 8, 9, 2, 1, 28, 31, 16, 8,
    49, 14, 1, 10, 28, 44, 1, 11, 2, 8, 2, 9, 9, 2, 2, 22, 20, 2, 1, 11, 1, 1, 1, 1, 1, 11, 10, 32,
    24, 59, 32, 45, 8, 25, 2, 27, 21, 53, 1, 29, 2, 23, 9, 12, 2, 11, 39, 13, 9, 24, 1, 1, 10, 16,
    10, 10, 1, 1, 1, 10, 10, 9, 1, 17, 22, 45, 2, 7, 1, 17, 22, 45, 1, 7, 16, 16, 1, 7, 1, 17, 19,
    1, 22, 29, 62, 9, 2, 10, 1, 9, 10, 9, 1, 9, 9, 1, 1, 2, 10, 10, 19, 2, 1, 1, 27, 2, 11, 10, 8,
    20, 1, 17, 1, 15, 16, 12, 60, 2, 1, 5, 1, 15, 9, 9, 11, 26, 1],
   [1, 13, 37, 40, 13, 10, 117, 104, 14, 78, 100, 206, 24, 111, 22, 92, 376, 320, 1, 11, 29, 31, 1,
    28, 9, 111, 118, 1, 1, 1, 1, 1, 1, 10, 1, 11, 13, 3, 1, 1, 1, 22, 1, 21, 84, 20, 1, 1, 1, 10, 1,
    1, 1, 1, 1, 1, 11, 13, 1, 2, 22, 21, 21, 1, 1, 1, 1, 2, 10, 2, 22, 10, 20, 1, 1, 1, 1, 2, 12, 1,
    20, 1, 10, 1, 46, 9, 1, 1, 1, 1, 25, 2, 27, 1, 15, 1, 5, 1, 15, 1, 17, 10, 2, 10, 1, 1, 10, 1,
    1, 1, 3, 12, 18, 1, 20, 1, 1, 1, 13, 22, 1, 13, 1, 1, 1, 10, 1, 18, 32, 1, 9, 2, 9, 10, 2, 1,
    32, 37, 19, 9, 59, 17, 1, 11, 32, 57, 1, 13, 2, 9, 2, 10, 10, 2, 2, 25, 23, 2, 1, 12, 1, 1, 1,
    1, 1, 12, 11, 36, 27, 69, 36, 53, 9, 28, 2, 30, 24, 61, 1, 33, 2, 26, 10, 15, 2, 12, 60, 16, 10,
    27, 1, 1, 11, 18, 11, 11, 1, 1, 1, 11, 11, 10, 1, 22, 29, 62, 2, 8, 1, 22, 29, 62, 1, 9, 22, 23,
    1, 9, 1, 23, 27, 1, 27, 37, 80, 10, 2, 11, 1, 10, 11, 10, 1, 10, 10, 1, 1, 2, 11, 11, 22, 2, 1,
    1, 30, 2, 12, 11, 9, 23, 1, 22, 1, 17, 19, 13, 86, 2, 1, 7, 1, 18, 10, 10, 12, 29, 1],
   [1, 15, 46, 50, 15, 11, 149, 141, 15, 108, 138, 296, 26, 165, 24, 112, 542, 522, 1, 13, 37, 40,
    1, 35, 10, 146, 166, 1, 1, 1, 1, 1, 1, 11, 1, 12, 14, 3, 1, 1, 1, 24, 1, 23, 103, 22, 1, 1, 1,
    11, 1, 1, 1, 1, 1, 1, 12, 14, 1, 2, 24, 23, 23, 1, 1, 1, 1, 2, 11, 2, 25, 11, 23, 1, 1, 1, 1, 2,
    13, 1, 22, 1, 11, 1, 52, 10, 1, 1, 1, 1, 28, 2, 30, 1, 18, 1, 7, 1, 17, 1, 22, 11, 2, 11, 1, 1,
    11, 1, 1, 1, 3, 13, 20, 1, 22, 1, 1, 1, 14, 24, 1, 14, 1, 1, 1, 11, 1, 20, 36, 1, 10, 2, 10, 11,
    2, 1, 36, 43, 22, 10, 69, 20, 1, 12, 36, 70, 1, 15, 2, 10, 2, 11, 11, 2, 2, 28, 26, 2, 1, 13, 1,
    1, 1, 1, 1, 13, 12, 40, 30, 79, 40, 61, 10, 31, 2, 33, 27, 69, 1, 37, 2, 29, 11, 18, 2, 13, 86,
    19, 11, 30, 1, 1, 12, 20, 12, 12, 1, 1, 1, 12, 12, 11, 1, 27, 37, 80, 2, 9, 1, 27, 37, 80, 1,
    11, 29, 31, 1, 11, 1, 30, 36, 1, 32, 46, 99, 11, 2, 12, 1, 11, 12, 11, 1, 11, 11, 1, 1, 2, 12,
    12, 25, 2, 1, 1, 33, 2, 13, 12, 10, 26, 1, 27, 1, 19, 22, 14, 117, 2, 1, 9, 1, 21, 11, 11, 13,
    32, 1],
   [1, 17, 56, 61, 17, 12, 185, 184, 16, 143, 185, 405, 28, 231, 26, 134, 754, 794, 1, 15, 46, 50,
    1, 42, 11, 186, 221, 1, 1, 1, 1, 1, 1, 12, 1, 13, 15, 3, 1, 1, 1, 26, 1, 25, 124, 24, 1, 1, 1,
    12, 1, 1, 1, 1, 1, 1, 13, 15, 1, 2, 26, 25, 25, 1, 1, 1, 1, 2, 12, 2, 28, 12, 26, 1, 1, 1, 1, 2,
    14, 1, 24, 1, 12, 1, 58, 11, 1, 1, 1, 1, 31, 2, 33, 1, 21, 1, 9, 1, 19, 1, 27, 12, 2, 12, 1, 1,
    12, 1, 1, 1, 3, 14, 22, 1, 24, 1, 1, 1, 15, 26, 1, 15, 1, 1, 1, 12, 1, 22, 40, 1, 11, 2, 11, 12,
    2, 1, 40, 49, 25, 11, 79, 23, 1, 13, 40, 83, 1, 17, 2, 11, 2, 12, 12, 2, 2, 31, 29, 2, 1, 14, 1,
    1, 1, 1, 1, 14, 13, 44, 33, 89, 44, 69, 11, 34, 2, 36, 30, 77, 1, 41, 2, 32, 12, 21, 2, 14, 117,
    22, 12, 33, 1, 1, 13, 22, 13, 13, 1, 1, 1, 13, 13, 12, 1, 32, 46, 99, 2, 10, 1, 32, 46, 99, 1,
    13, 37, 40, 1, 13, 1, 38, 46, 1, 37, 56, 119, 12, 2, 13, 1, 12, 13, 12, 1, 12, 12, 1, 1, 2, 13,
    13, 28, 2, 1, 1, 36, 2, 14, 13, 11, 29, 1, 32, 1, 21, 25, 15, 153, 2, 1, 11, 1, 24, 12, 12, 14,
    35, 1],
   [1, 19, 67, 73, 19, 13, 225, 233, 17, 183, 242, 534, 30, 309, 28, 158, 1018, 1144, 1, 17, 56, 61,
    1, 49, 12, 231, 283, 1, 1, 1, 1, 1, 1, 13, 1, 14, 16, 3, 1, 1, 1, 28, 1, 27, 147, 26, 1, 1, 1,
    13, 1, 1, 1, 1, 1, 1, 14, 16, 1, 2, 28, 27, 27, 1, 1, 1, 1, 2, 13, 2, 31, 13, 29, 1, 1, 1, 1, 2,
    15, 1, 26, 1, 13, 1, 64, 12, 1, 1, 1, 1, 34, 2, 36, 1, 24, 1, 11, 1, 21, 1, 32, 13, 2, 13, 1, 1,
    13, 1, 1, 1, 3, 15, 24, 1, 26, 1, 1, 1, 16, 28, 1, 16, 1, 1, 1, 13, 1, 24, 44, 1, 12, 2, 12, 13,
    2, 1, 44, 55, 28, 12, 89, 26, 1, 14, 44, 96, 1, 19, 2, 12, 2, 13, 13, 2, 2, 34, 32, 2, 1, 15, 1,
    1, 1, 1, 1, 15, 14, 48, 36, 99, 48, 77, 12, 37, 2, 39, 33, 85, 1, 45, 2, 35, 13, 24, 2, 15, 153,
    25, 13, 36, 1, 1, 14, 24, 14, 14, 1, 1, 1, 14, 14, 13, 1, 37, 56, 119, 2, 11, 1, 37, 56, 119, 1,
    15, 46, 50, 1, 15, 1, 47, 57, 1, 42, 67, 140, 13, 2, 14, 1, 13, 14, 13, 1, 13, 13, 1, 1, 2, 14,
    14, 31, 2, 1, 1, 39, 2, 15, 14, 12, 32, 1, 37, 1, 23, 28, 16, 194, 2, 1, 13, 1, 27, 13, 13, 15,
    38, 1]]

/-- The reachable state with index `u`. -/
def rl (u : ℕ) : ℕ := RL.getD u 0

/-- The successor indices of the reachable state with index `u`. -/
def sli (u : ℕ) : List ℕ := SLI.getD u []

/-- The list is strictly increasing. -/
def sortedB : List ℕ → Bool
  | a :: b :: L => Nat.blt a b && sortedB (b :: L)
  | _ => true

theorem chk_RL : RL.length = 267 ∧ SLI.length = 267 ∧ rl 0 = 0 ∧ rl 266 < 177147 ∧
    sortedB RL = true := by
  decide +kernel

theorem sortedB_getD : ∀ (L : List ℕ), sortedB L = true →
    ∀ u, u + 1 < L.length → L.getD u 0 < L.getD (u + 1) 0
  | [], _, u, hu => by simp at hu
  | [_], _, u, hu => by simp at hu
  | a :: b :: L, h, u, hu => by
    simp only [sortedB, Bool.and_eq_true, Nat.blt_eq] at h
    cases u with
    | zero => simpa using h.1
    | succ u =>
      have := sortedB_getD (b :: L) h.2 u (by simp at hu ⊢; omega)
      simpa using this

theorem rl_step (u : ℕ) (hu : u + 1 < 267) : rl u < rl (u + 1) :=
  sortedB_getD RL chk_RL.2.2.2.2 u (by rw [chk_RL.1]; exact hu)

theorem rl_mono (u v : ℕ) (huv : u < v) (hv : v < 267) : rl u < rl v := by
  induction v with
  | zero => omega
  | succ v ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp huv with h | h
    · exact (ih h (by omega)).trans (rl_step v hv)
    · rw [h]
      exact rl_step v hv

theorem rl_lt (u : ℕ) (hu : u < 267) : rl u < 177147 := by
  rcases Nat.lt_or_ge u 266 with h | h
  · exact (rl_mono u 266 h (by norm_num)).trans chk_RL.2.2.2.1
  · rw [show u = 266 by omega]
    exact chk_RL.2.2.2.1

theorem rl_inj {u v : ℕ} (hu : u < 267) (hv : v < 267) (h : rl u = rl v) : u = v := by
  rcases Nat.lt_trichotomy u v with huv | huv | huv
  · exact absurd h (ne_of_lt (rl_mono u v huv hv))
  · exact huv
  · exact absurd h (ne_of_gt (rl_mono v u huv hu))

theorem chk_LV : (List.range 729).filter (fun c => decide (rowL c)) = LV := by
  decide +kernel

theorem mem_LV {c : ℕ} : c ∈ LV ↔ c < 729 ∧ rowL c := by
  rw [← chk_LV, List.mem_filter, List.mem_range, decide_eq_true_iff]

/-- Checks the successor lists `S` of the states `R` (and that each has at most 7 entries, all
below 267). -/
def chkAll : List ℕ → List (List ℕ) → Bool
  | s :: R, l :: S =>
    decide ((LV.map (tauB s)).filter (fun t => t != 177147) = l.map rl) &&
      l.all (fun v => Nat.blt v 267) && Nat.ble l.length 7 && chkAll R S
  | [], [] => true
  | _, _ => false

theorem chk_SLI : chkAll RL SLI = true := by
  decide +kernel

theorem chkAll_sound : ∀ (R : List ℕ) (S : List (List ℕ)), chkAll R S = true →
    ∀ u < R.length, (LV.map (tauB (R.getD u 0))).filter (fun t => t != 177147) =
      (S.getD u []).map rl ∧ (∀ v ∈ S.getD u [], v < 267) ∧ (S.getD u []).length ≤ 7
  | [], _, _, u, hu => by simp at hu
  | s :: R, [], h, _, _ => by simp [chkAll] at h
  | s :: R, l :: S, h, u, hu => by
    simp only [chkAll, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Nat.blt_eq,
      Nat.ble_eq] at h
    cases u with
    | zero => simpa using ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    | succ u =>
      have := chkAll_sound R S h.2 u (by simp at hu; omega)
      simpa using this

theorem sli_spec (u : ℕ) (hu : u < 267) :
    (LV.map (tau (rl u))).filter (fun t => t != 177147) = (sli u).map rl ∧
      (∀ v ∈ sli u, v < 267) ∧ (sli u).length ≤ 7 := by
  have h := chkAll_sound RL SLI chk_SLI u (by rw [chk_RL.1]; exact hu)
  have e : LV.map (tau (rl u)) = LV.map (tauB (rl u)) :=
    List.map_congr_left fun c hc => (tauB_eq _ c (mem_LV.mp hc).2).symm
  rw [e]
  exact h

/-! ### Reachability -/

theorem tau_rl (u c : ℕ) (hu : u < 267) (hc : c < 729) :
    tau (rl u) c = 177147 ∨ ∃ v < 267, tau (rl u) c = rl v := by
  by_cases h : tau (rl u) c = 177147
  · exact Or.inl h
  · right
    have hmem : c ∈ LV := mem_LV.mpr ⟨hc, tau_live _ _ h⟩
    have h2 : tau (rl u) c ∈ (LV.map (tau (rl u))).filter (fun t => t != 177147) := by
      rw [List.mem_filter]
      exact ⟨List.mem_map_of_mem hmem, by simpa using h⟩
    rw [(sli_spec u hu).1, List.mem_map] at h2
    obtain ⟨v, hv, e⟩ := h2
    exact ⟨v, (sli_spec u hu).2.1 v hv, e.symm⟩

theorem reach (m : ℕ) (A : Fin m → Row) : st A = 177147 ∨ ∃ u < 267, st A = rl u := by
  induction m with
  | zero =>
    right
    exact ⟨0, by norm_num, by rw [st_zero, chk_RL.2.2.1]⟩
  | succ m ih =>
    have h := st_snoc (Fin.init A) (A (Fin.last m))
    rw [Fin.snoc_init_self] at h
    rw [h]
    rcases ih (Fin.init A) with h0 | ⟨u, hu, e⟩
    · left
      rw [h0, tau_dead]
    · rw [e]
      exact tau_rl u _ hu (rc_lt _)

/-! ### Transfer counts through the successor lists -/

/-- The number of occurrences of `t` in a list. -/
def cntL (t : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: L => (if x = t then 1 else 0) + cntL t L

theorem cntL_append (t : ℕ) (L M : List ℕ) : cntL t (L ++ M) = cntL t L + cntL t M := by
  induction L with
  | nil => simp [cntL]
  | cons x L ih =>
    simp only [List.cons_append, cntL, ih]
    ring

theorem sum_range_cntL (f : ℕ → ℕ) (t n : ℕ) :
    ∑ c ∈ range n, (if f c = t then 1 else 0) = cntL t ((List.range n).map f) := by
  induction n with
  | zero => simp [cntL]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, cntL_append]
    simp [cntL]

theorem cntL_filter_map (f : ℕ → ℕ) (p : ℕ → Bool) (t : ℕ) :
    ∀ L : List ℕ, (∀ c ∈ L, p c = false → f c ≠ t) →
      cntL t ((L.filter p).map f) = cntL t (L.map f)
  | [], _ => rfl
  | c :: L, h => by
    have ih := cntL_filter_map f p t L (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    by_cases hp : p c = true
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.map_cons, cntL, cntL, ih]
    · rw [List.filter_cons_of_neg hp, List.map_cons, cntL, ih,
        if_neg (h c (List.mem_cons_self) (by simpa using hp))]
      ring

theorem cntL_filter_ne (t d : ℕ) (htd : t ≠ d) :
    ∀ M : List ℕ, cntL t (M.filter (fun x => x != d)) = cntL t M
  | [] => rfl
  | x :: M => by
    by_cases hx : x = d
    · rw [List.filter_cons_of_neg (by simp [hx]), cntL_filter_ne t d htd M, cntL,
        if_neg (fun e : x = t => htd (e.symm.trans hx))]
      ring
    · rw [List.filter_cons_of_pos (by simp [hx]), cntL, cntL, cntL_filter_ne t d htd M]

theorem cntL_map_rl (w : ℕ) (hw : w < 267) :
    ∀ V : List ℕ, (∀ v ∈ V, v < 267) → cntL (rl w) (V.map rl) = cntL w V
  | [], _ => rfl
  | v :: V, h => by
    rw [List.map_cons, cntL, cntL,
      cntL_map_rl w hw V (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))]
    congr 1
    have hv := h v List.mem_cons_self
    by_cases e : v = w
    · rw [if_pos (by rw [e]), if_pos e]
    · rw [if_neg (fun e' => e (rl_inj hv hw e')), if_neg e]

theorem cnt_rl (u w : ℕ) (hu : u < 267) (hw : w < 267) : cnt (rl u) (rl w) = cntL w (sli u) := by
  unfold cnt
  rw [sum_range_cntL (tau (rl u)) (rl w) 729,
    ← cntL_filter_map (tau (rl u)) (fun c => decide (rowL c)) (rl w) (List.range 729) ?_]
  · rw [chk_LV, ← cntL_filter_ne (rl w) 177147 (ne_of_lt (rl_lt w hw)), (sli_spec u hu).1,
      cntL_map_rl w hw _ (sli_spec u hu).2.1]
  · intro c _ hc e
    have hL := tau_live (rl u) c (by rw [e]; exact ne_of_lt (rl_lt w hw))
    simp [hL] at hc

/-! ### Counts by state indices -/

/-- The number of arrays with `m` rows in the reachable state with index `u`. -/
noncomputable def Ni (m u : ℕ) : ℕ := N m (rl u)

theorem N_off (m s : ℕ) (h1 : s ≠ 177147) (h2 : ∀ u < 267, s ≠ rl u) : N m s = 0 := by
  unfold N
  refine Finset.sum_eq_zero fun A _ => if_neg ?_
  rcases reach m A with h | ⟨u, hu, e⟩
  · rw [h]
    exact fun e' => h1 e'.symm
  · rw [e]
    exact fun e' => h2 u hu e'.symm

theorem cnt_dead_rl (w : ℕ) (hw : w < 267) : cnt 177147 (rl w) = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero fun c _ => if_neg ?_
  rw [tau_dead]
  exact ne_of_gt (rl_lt w hw)

theorem Ni_succ (m w : ℕ) (hw : w < 267) :
    Ni (m + 1) w = ∑ u ∈ range 267, Ni m u * cntL w (sli u) := by
  unfold Ni
  rw [N_succ]
  have himg : ∑ s ∈ (range 267).image rl, N m s * cnt s (rl w) =
      ∑ u ∈ range 267, N m (rl u) * cnt (rl u) (rl w) :=
    Finset.sum_image (fun u hu v hv e => rl_inj (mem_range.mp hu) (mem_range.mp hv) e)
  rw [← Finset.sum_subset (s₁ := (range 267).image rl) ?_ ?_, himg]
  · exact Finset.sum_congr rfl fun u hu => by rw [cnt_rl u w (mem_range.mp hu) hw]
  · intro s hs
    rw [mem_image] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    have := rl_lt u (mem_range.mp hu)
    exact mem_range.mpr (by omega)
  · intro s _ hns
    by_cases hd : s = 177147
    · rw [hd, cnt_dead_rl w hw, mul_zero]
    · rw [N_off m s hd (fun u hu e => hns (mem_image.mpr ⟨u, mem_range.mpr hu, e.symm⟩)),
        zero_mul]

theorem Ni_zero (u : ℕ) (hu : u < 267) : Ni 0 u = if u = 0 then 1 else 0 := by
  unfold Ni
  rw [N_zero]
  by_cases h : u = 0
  · rw [if_pos (by rw [h]; exact chk_RL.2.2.1), if_pos h]
  · rw [if_neg (fun e => h (rl_inj hu (by norm_num) (e.trans chk_RL.2.2.1.symm))), if_neg h]

theorem a_eq (m : ℕ) : a m = ∑ u ∈ range 267, Ni m u := by
  classical
  have h1 : a m = ∑ A : Fin m → Row, if st A < 177147 then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ =>
      if_congr ((valid_iff A).trans (st_lt_iff A).symm) rfl rfl
  rw [h1]
  unfold Ni N
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rcases reach m A with h | ⟨u0, hu0, e⟩
  · rw [h, if_neg (lt_irrefl _)]
    exact (Finset.sum_eq_zero fun u hu => if_neg (ne_of_gt (rl_lt u (mem_range.mp hu)))).symm
  · rw [e, if_pos (rl_lt u0 hu0)]
    rw [Finset.sum_congr rfl (fun u hu => if_congr
      (show rl u0 = rl u ↔ u0 = u from ⟨fun h => rl_inj hu0 (mem_range.mp hu) h,
        fun h => h ▸ rfl⟩) rfl rfl), Finset.sum_ite_eq, if_pos (mem_range.mpr hu0)]


/-! ### One step of the counts, through number encodings -/

/-- A list of counts read as the digits of a number in base `2 ^ 32`. -/
def enc : List ℕ → ℕ
  | [] => 0
  | x :: L => x + 4294967296 * enc L

/-- The number with a digit 1 (in base `2 ^ 32`) at each position listed in `ts`. -/
def wsum : List ℕ → ℕ
  | [] => 0
  | w :: ts => 4294967296 ^ w + wsum ts

/-- The encoding of the next counts, from the counts `G` and the successor lists `S`. -/
def pushN : List ℕ → List (List ℕ) → ℕ
  | g :: G, ts :: S => g * wsum ts + pushN G S
  | _, _ => 0

/-- The list `f k, f (k + 1), ..., f (k + n - 1)`. -/
def mkL (f : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | k, n + 1 => f k :: mkL f (k + 1) n

theorem mkL_length (f : ℕ → ℕ) : ∀ k n, (mkL f k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by rw [mkL, List.length_cons, mkL_length f (k + 1) n]

theorem mkL_getD (f : ℕ → ℕ) : ∀ k n w, w < n → (mkL f k n).getD w 0 = f (k + w)
  | _, 0, _, hw => absurd hw (Nat.not_lt_zero _)
  | k, n + 1, 0, _ => by rw [mkL, List.getD_cons_zero, Nat.add_zero]
  | k, n + 1, w + 1, hw => by
    rw [mkL, List.getD_cons_succ, mkL_getD f (k + 1) n w (by omega)]
    congr 1
    ring

theorem mkL_mem (f : ℕ → ℕ) : ∀ k n x, x ∈ mkL f k n → ∃ w < n, x = f (k + w)
  | _, 0, _, hx => by simp [mkL] at hx
  | k, n + 1, x, hx => by
    rw [mkL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨0, by omega, by rw [Nat.add_zero]⟩
    · obtain ⟨w, hw, rfl⟩ := mkL_mem f (k + 1) n x hx
      exact ⟨w + 1, by omega, by congr 1; ring⟩

theorem enc_mkL (f : ℕ → ℕ) : ∀ k n,
    enc (mkL f k n) = ∑ w ∈ range n, f (k + w) * 4294967296 ^ w
  | _, 0 => rfl
  | k, n + 1 => by
    rw [mkL, enc, enc_mkL f (k + 1) n, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show k + (w + 1) = k + 1 + w by ring]
    ring

theorem enc_inj : ∀ (L1 L2 : List ℕ), L1.length = L2.length → (∀ x ∈ L1, x < 4294967296) →
    (∀ x ∈ L2, x < 4294967296) → enc L1 = enc L2 → L1 = L2
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | x :: L1, y :: L2, hl, h1, h2, he => by
    rw [enc, enc] at he
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    have hxy : x = y := by omega
    have hL : enc L1 = enc L2 := by omega
    rw [hxy, enc_inj L1 L2 (by simpa using hl) (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
      (fun z hz => h2 z (List.mem_cons_of_mem _ hz)) hL]

theorem wsum_eq (n : ℕ) : ∀ ts : List ℕ, (∀ w ∈ ts, w < n) →
    wsum ts = ∑ w ∈ range n, cntL w ts * 4294967296 ^ w
  | [], _ => by simp [wsum, cntL]
  | v :: ts, h => by
    rw [wsum, wsum_eq n ts (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp only [cntL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (h v List.mem_cons_self))]

theorem pushN_eq : ∀ (G : List ℕ) (S : List (List ℕ)),
    pushN G S = ∑ u ∈ range (min G.length S.length), G.getD u 0 * wsum (S.getD u [])
  | [], _ => by simp [pushN]
  | _ :: _, [] => by simp [pushN]
  | g :: G, ts :: S => by
    rw [pushN, pushN_eq G S, List.length_cons, List.length_cons,
      show min (G.length + 1) (S.length + 1) = min G.length S.length + 1 by omega,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem cntL_le (t : ℕ) : ∀ L : List ℕ, cntL t L ≤ L.length
  | [] => le_rfl
  | x :: L => by
    rw [cntL, List.length_cons]
    have := cntL_le t L
    split_ifs <;> omega

theorem sum_getD : ∀ L : List ℕ, ∑ u ∈ range L.length, L.getD u 0 = L.sum
  | [] => rfl
  | x :: L => by
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← sum_getD L]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem level_step (G G' : List ℕ) (hG : G.length = 267) (hG' : G'.length = 267)
    (hb : ∀ x ∈ G', x < 4294967296) (hsum : G.sum ≤ 7657) (h : pushN G SLI = enc G') :
    ∀ w < 267, ∑ u ∈ range 267, G.getD u 0 * cntL w (sli u) = G'.getD w 0 := by
  set f : ℕ → ℕ := fun w => ∑ u ∈ range 267, G.getD u 0 * cntL w (sli u) with hf
  have h1 : pushN G SLI = enc (mkL f 0 267) := by
    rw [pushN_eq, hG, chk_RL.2.1, Nat.min_self, enc_mkL]
    simp only [Nat.zero_add, hf, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [show SLI.getD u [] = sli u from rfl, wsum_eq 267 (sli u) (sli_spec u (mem_range.mp hu)).2.1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hbound : ∀ w, f w < 4294967296 := by
    intro w
    have h2 : f w ≤ ∑ u ∈ range 267, G.getD u 0 * 7 :=
      Finset.sum_le_sum fun u hu => Nat.mul_le_mul_left _
        ((cntL_le w (sli u)).trans (sli_spec u (mem_range.mp hu)).2.2)
    rw [← Finset.sum_mul, ← hG, sum_getD] at h2
    omega
  have h3 : mkL f 0 267 = G' := enc_inj _ _ (by rw [mkL_length, hG'])
    (fun x hx => by
      obtain ⟨w, _, e⟩ := mkL_mem f 0 267 x hx
      rw [e]
      exact hbound _) hb (h1.symm.trans h)
  intro w hw
  rw [← h3, mkL_getD f 0 267 w hw, Nat.zero_add]

/-! ### The counts for `m ≤ 18` -/

/-- The entry `u` of the level `m` of the table `GT`. -/
def gv (m u : ℕ) : ℕ := (GT.getD m []).getD u 0

theorem chk_GT : (∀ m < 19, (GT.getD m []).length = 267 ∧
      (GT.getD m []).all (fun x => Nat.blt x 4294967296) = true) ∧
    GT.getD 0 [] = 1 :: List.replicate 266 0 ∧
    (∀ m < 18, (GT.getD m []).sum ≤ 7657) ∧
    ∀ m < 18, pushN (GT.getD m []) SLI = enc (GT.getD (m + 1) []) := by
  decide +kernel

/-- Checks the identity of the vector recurrence entry by entry. -/
def chkH : List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | a :: A, b :: B, c :: C, d :: D, e :: E =>
    Nat.beq (a + 6 * c + e) (4 * b + 4 * d) && chkH A B C D E
  | _, _, _, _, _ => true

theorem chkH_sound : ∀ (A B C D E : List ℕ), chkH A B C D E = true →
    ∀ u < A.length, u < B.length → u < C.length → u < D.length → u < E.length →
      A.getD u 0 + 6 * C.getD u 0 + E.getD u 0 = 4 * B.getD u 0 + 4 * D.getD u 0
  | [], _, _, _, _, _, u, hu, _, _, _, _ => by simp at hu
  | _ :: _, [], _, _, _, _, u, _, hu, _, _, _ => by simp at hu
  | _ :: _, _ :: _, [], _, _, _, u, _, _, hu, _, _ => by simp at hu
  | _ :: _, _ :: _, _ :: _, [], _, _, u, _, _, _, hu, _ => by simp at hu
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, u, _, _, _, _, hu => by simp at hu
  | a :: A, b :: B, c :: C, d :: D, e :: E, h, u, h1, h2, h3, h4, h5 => by
    simp only [chkH, Bool.and_eq_true, Nat.beq_eq] at h
    cases u with
    | zero => simpa using h.1
    | succ u =>
      simp only [List.getD_cons_succ]
      simp only [List.length_cons] at h1 h2 h3 h4 h5
      exact chkH_sound A B C D E h.2 u (by omega) (by omega) (by omega) (by omega) (by omega)

theorem chk_H : chkH (GT.getD 18 []) (GT.getD 17 []) (GT.getD 16 []) (GT.getD 15 [])
    (GT.getD 14 []) = true := by
  decide +kernel

theorem chk_sums : (GT.getD 1 []).sum = 7 ∧ (GT.getD 2 []).sum = 19 ∧
    (GT.getD 3 []).sum = 39 ∧ (GT.getD 4 []).sum = 77 ∧ (GT.getD 5 []).sum = 156 ∧
    (GT.getD 6 []).sum = 266 ∧ (GT.getD 7 []).sum = 409 ∧ (GT.getD 8 []).sum = 599 ∧
    (GT.getD 9 []).sum = 852 ∧ (GT.getD 10 []).sum = 1191 ∧ (GT.getD 11 []).sum = 1635 ∧
    (GT.getD 12 []).sum = 2213 ∧ (GT.getD 13 []).sum = 2944 ∧ (GT.getD 14 []).sum = 3837 ∧
    (GT.getD 15 []).sum = 4910 ∧ (GT.getD 16 []).sum = 6178 ∧ (GT.getD 17 []).sum = 7657 := by
  decide +kernel

theorem getD_replicate_zero : ∀ (n v : ℕ), (List.replicate n 0).getD v 0 = 0
  | 0, v => by rw [List.replicate_zero, List.getD_nil]
  | n + 1, 0 => by rw [List.replicate_succ, List.getD_cons_zero]
  | n + 1, v + 1 => by
    rw [List.replicate_succ, List.getD_cons_succ]
    exact getD_replicate_zero n v

theorem Ni_eq_gv : ∀ m ≤ 18, ∀ u < 267, Ni m u = gv m u := by
  intro m
  induction m with
  | zero =>
    intro _ u hu
    rw [Ni_zero u hu, gv, chk_GT.2.1]
    cases u with
    | zero => rfl
    | succ u => rw [if_neg (Nat.succ_ne_zero u), List.getD_cons_succ, getD_replicate_zero]
  | succ m ih =>
    intro hm w hw
    have hgt := chk_GT
    rw [Ni_succ m w hw, gv, ← level_step (GT.getD m []) (GT.getD (m + 1) [])
      (hgt.1 m (by omega)).1 (hgt.1 (m + 1) (by omega)).1
      (by
        have := (hgt.1 (m + 1) (by omega)).2
        simp only [List.all_eq_true, Nat.blt_eq] at this
        exact this)
      (hgt.2.2.1 m (by omega)) (hgt.2.2.2 m (by omega)) w hw]
    exact Finset.sum_congr rfl fun u hu => by rw [ih (by omega) u (mem_range.mp hu), gv]

theorem a_gt (m : ℕ) (hm : m ≤ 18) : a m = (GT.getD m []).sum := by
  rw [a_eq, ← sum_getD, (chk_GT.1 m (by omega)).1]
  exact Finset.sum_congr rfl fun u hu => by rw [Ni_eq_gv m hm u (mem_range.mp hu), gv]

/-! ### The recurrence -/

theorem vec_rec (k : ℕ) : ∀ u < 267,
    Ni (k + 18) u + 6 * Ni (k + 16) u + Ni (k + 14) u = 4 * Ni (k + 17) u + 4 * Ni (k + 15) u := by
  induction k with
  | zero =>
    intro u hu
    rw [Ni_eq_gv _ (by norm_num) u hu, Ni_eq_gv _ (by norm_num) u hu, Ni_eq_gv _ (by norm_num) u hu,
      Ni_eq_gv _ (by norm_num) u hu, Ni_eq_gv _ (by norm_num) u hu]
    have hl := chk_GT.1
    exact chkH_sound _ _ _ _ _ chk_H u (by rw [(hl 18 (by norm_num)).1]; exact hu)
      (by rw [(hl 17 (by norm_num)).1]; exact hu) (by rw [(hl 16 (by norm_num)).1]; exact hu)
      (by rw [(hl 15 (by norm_num)).1]; exact hu) (by rw [(hl 14 (by norm_num)).1]; exact hu)
  | succ k ih =>
    intro w hw
    rw [show k + 1 + 18 = k + 18 + 1 by ring, show k + 1 + 16 = k + 16 + 1 by ring,
      show k + 1 + 14 = k + 14 + 1 by ring, show k + 1 + 17 = k + 17 + 1 by ring,
      show k + 1 + 15 = k + 15 + 1 by ring, Ni_succ _ w hw, Ni_succ _ w hw, Ni_succ _ w hw,
      Ni_succ _ w hw, Ni_succ _ w hw, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h := ih u (mem_range.mp hu)
    calc Ni (k + 18) u * cntL w (sli u) + 6 * (Ni (k + 16) u * cntL w (sli u)) +
          Ni (k + 14) u * cntL w (sli u)
        = (Ni (k + 18) u + 6 * Ni (k + 16) u + Ni (k + 14) u) * cntL w (sli u) := by ring
      _ = (4 * Ni (k + 17) u + 4 * Ni (k + 15) u) * cntL w (sli u) := by rw [h]
      _ = 4 * (Ni (k + 17) u * cntL w (sli u)) + 4 * (Ni (k + 15) u * cntL w (sli u)) := by ring

theorem a_rec (k : ℕ) :
    a (k + 18) + 6 * a (k + 16) + a (k + 14) = 4 * a (k + 17) + 4 * a (k + 15) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u hu => vec_rec k u (mem_range.mp hu)

theorem recurrence (n : ℕ) (hn : 17 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 18 := ⟨n - 18, by omega⟩
  have h := a_rec k
  rw [show k + 18 - 1 = k + 17 by omega, show k + 18 - 2 = k + 16 by omega,
    show k + 18 - 3 = k + 15 by omega, show k + 18 - 4 = k + 14 by omega]
  have h' : ((a (k + 18) + 6 * a (k + 16) + a (k + 14) : ℕ) : ℤ) =
      ((4 * a (k + 17) + 4 * a (k + 15) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith


/-! ### The generating function -/

theorem a_vals : a 1 = 7 ∧ a 2 = 19 ∧ a 3 = 39 ∧ a 4 = 77 ∧ a 5 = 156 ∧ a 6 = 266 ∧
    a 7 = 409 ∧ a 8 = 599 ∧ a 9 = 852 ∧ a 10 = 1191 ∧ a 11 = 1635 ∧ a 12 = 2213 ∧
    a 13 = 2944 ∧ a 14 = 3837 ∧ a 15 = 4910 ∧ a 16 = 6178 ∧ a 17 = 7657 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    chk_sums
  exact ⟨by rw [a_gt 1 (by norm_num), h1], by rw [a_gt 2 (by norm_num), h2],
    by rw [a_gt 3 (by norm_num), h3], by rw [a_gt 4 (by norm_num), h4],
    by rw [a_gt 5 (by norm_num), h5], by rw [a_gt 6 (by norm_num), h6],
    by rw [a_gt 7 (by norm_num), h7], by rw [a_gt 8 (by norm_num), h8],
    by rw [a_gt 9 (by norm_num), h9], by rw [a_gt 10 (by norm_num), h10],
    by rw [a_gt 11 (by norm_num), h11], by rw [a_gt 12 (by norm_num), h12],
    by rw [a_gt 13 (by norm_num), h13], by rw [a_gt 14 (by norm_num), h14],
    by rw [a_gt 15 (by norm_num), h15], by rw [a_gt 16 (by norm_num), h16],
    by rw [a_gt 17 (by norm_num), h17]⟩

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        X * (7 - 9 * X + 5 * X ^ 2 + 7 * X ^ 3 + 13 * X ^ 4 - 33 * X ^ 5 + 12 * X ^ 6 +
          12 * X ^ 7 + 2 * X ^ 8 + 7 * X ^ 9 - 4 * X ^ 10 + 10 * X ^ 11 - 10 * X ^ 12 -
          10 * X ^ 13 + 9 * X ^ 14 - 3 * X ^ 15 + X ^ 16) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 4 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 4 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 2) - C 4 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (7 - 9 * X + 5 * X ^ 2 + 7 * X ^ 3 + 13 * X ^ 4 - 33 * X ^ 5 +
      12 * X ^ 6 + 12 * X ^ 7 + 2 * X ^ 8 + 7 * X ^ 9 - 4 * X ^ 10 + 10 * X ^ 11 -
      10 * X ^ 12 - 10 * X ^ 13 + 9 * X ^ 14 - 3 * X ^ 15 + X ^ 16) =
      C 7 * X ^ 1 - C 9 * X ^ 2 + C 5 * X ^ 3 + C 7 * X ^ 4 + C 13 * X ^ 5 - C 33 * X ^ 6 +
        C 12 * X ^ 7 + C 12 * X ^ 8 + C 2 * X ^ 9 + C 7 * X ^ 10 - C 4 * X ^ 11 +
        C 10 * X ^ 12 - C 10 * X ^ 13 - C 10 * X ^ 14 + C 9 * X ^ 15 - C 3 * X ^ 16 +
        C 1 * X ^ 17 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17⟩ := a_vals
  by_cases hk : k < 18
  · interval_cases k <;>
      norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 18 := ⟨k - 18, by omega⟩
    simp only [show 0 ≤ j + 18 by omega, show 1 ≤ j + 18 by omega, show 2 ≤ j + 18 by omega,
      show 3 ≤ j + 18 by omega, show 4 ≤ j + 18 by omega, show j + 18 - 0 = j + 18 by omega,
      show j + 18 - 1 = j + 17 by omega, show j + 18 - 2 = j + 16 by omega,
      show j + 18 - 3 = j + 15 by omega, show j + 18 - 4 = j + 14 by omega,
      show ¬ (j + 18 = 0) by omega, show ¬ (j + 18 = 1) by omega, show ¬ (j + 18 = 2) by omega,
      show ¬ (j + 18 = 3) by omega, show ¬ (j + 18 = 4) by omega, show ¬ (j + 18 = 5) by omega,
      show ¬ (j + 18 = 6) by omega, show ¬ (j + 18 = 7) by omega, show ¬ (j + 18 = 8) by omega,
      show ¬ (j + 18 = 9) by omega, show ¬ (j + 18 = 10) by omega,
      show ¬ (j + 18 = 11) by omega, show ¬ (j + 18 = 12) by omega,
      show ¬ (j + 18 = 13) by omega, show ¬ (j + 18 = 14) by omega,
      show ¬ (j + 18 = 15) by omega, show ¬ (j + 18 = 16) by omega,
      show ¬ (j + 18 = 17) by omega, show ¬ (j + 17 = 0) by omega,
      show ¬ (j + 16 = 0) by omega, show ¬ (j + 15 = 0) by omega, show ¬ (j + 14 = 0) by omega,
      if_true, if_false, hF]
    have hq : ((a (j + 18) + 6 * a (j + 16) + a (j + 14) : ℕ) : ℚ) =
        ((4 * a (j + 17) + 4 * a (j + 15) : ℕ) : ℚ) := by rw [a_rec j]
    push_cast at hq
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a239359.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
