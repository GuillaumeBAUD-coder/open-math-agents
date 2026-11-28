import OMAStatements.S_oeis_a223835
import Mathlib

/-!
Proof of A223835 (Hardin's empirical formula and Barker's g.f. and recurrence).
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)
Against the merged statement (rows as a list): the bridge `OMABridgeA223835.a_eq` shows it counts exactly the
arrays of the Fin-function formulation proved below.

Method: arrays are read row by row by a finite automaton whose state is the last row and, for every
line through it, whether that line has already descended. A generic library (below) proves that the
automaton accepts exactly the arrays of the statement; its table (56 live states) is checked by
`decide +kernel`. The counts from every state satisfy (E - 1)^6 = 0 from shift 3 on, checked by the
kernel at one shift and lifted to all shifts; that gives Hardin's polynomial, and from it Barker's
recurrence and g.f.
-/

/-!
Generic transfer-matrix toolkit (automaton form).

Words over a finite alphabet `A` are read by a deterministic automaton on states `ℕ`
(`δ : ℕ → A → ℕ`, acceptance `acc : ℕ → Bool`).
* `card_run`: the number of accepted words of length `n` from state `q` is `cnt n q`.
* `cntV_eq`: a list-valued (memoised) version of `cnt`, for kernel computation.
* `cnt_rec`: a linear relation checked on a `δ`-closed set of states at one shift holds at all shifts.
* `window`: if `x` satisfies a linear recurrence of order `D`, any other linear recurrence that holds
  for the first `D` shifts holds for all shifts.
-/

namespace TMLib

open Finset

section automaton

variable {A : Type} [Fintype A] [DecidableEq A] (δ : ℕ → A → ℕ) (acc : ℕ → Bool)

def run : ℕ → List A → ℕ
  | q, [] => q
  | q, a :: w => run (δ q a) w

def cnt : ℕ → ℕ → ℕ
  | 0, q => if acc q then 1 else 0
  | n + 1, q => ∑ a : A, cnt n (δ q a)

theorem cnt_succ (n q : ℕ) : cnt δ acc (n + 1) q = ∑ a : A, cnt δ acc n (δ q a) := rfl

theorem card_run (n : ℕ) : ∀ q : ℕ,
    (univ.filter (fun w : Fin n → A => acc (run δ q (List.ofFn w)) = true)).card =
      cnt δ acc n q := by
  induction n with
  | zero =>
    intro q
    by_cases h : acc q = true
    · simp [run, cnt, h]
    · simp [run, cnt, h]
  | succ n ih =>
    intro q
    rw [cnt_succ, ← Finset.sum_congr rfl (fun a _ => ih (δ q a))]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 1) → A => w 0) (t := univ)
      (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.filter_filter]
    apply Finset.card_nbij' (fun w => Fin.tail w) (fun t => Fin.cons a t)
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hw ⊢
      obtain ⟨h1, h2⟩ := hw
      rw [List.ofFn_succ, run, h2] at h1
      exact h1
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at ht ⊢
      refine ⟨?_, by simp⟩
      rw [List.ofFn_succ, run]
      simpa using ht
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hw
      rw [← hw.2]
      exact Fin.cons_self_tail w
    · intro t _
      simp

/-- Memoised `cnt` on the states `0, …, N-1`, as a list. -/
def cntV (N : ℕ) : ℕ → List ℕ
  | 0 => (List.range N).map (fun q => if acc q then 1 else 0)
  | n + 1 => (List.range N).map (fun q => ∑ a : A, (cntV N n).getD (δ q a) 0)

theorem cntV_eq (N : ℕ) (hN : ∀ q < N, ∀ a : A, δ q a < N) (n : ℕ) :
    ∀ q < N, (cntV δ acc N n).getD q 0 = cnt δ acc n q := by
  induction n with
  | zero =>
    intro q hq
    simp [cntV, cnt, List.getD_eq_getElem?_getD, hq]
  | succ n ih =>
    intro q hq
    simp only [cntV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
      Option.map_some, Option.getD_some]
    rw [cnt_succ]
    apply Finset.sum_congr rfl
    intro a _
    have := ih (δ q a) (hN q hq a)
    simpa [List.getD_eq_getElem?_getD] using this

theorem cnt_rec (S : Finset ℕ) (hS : ∀ q ∈ S, ∀ a : A, δ q a ∈ S) (d : ℕ) (c : ℕ → ℤ) (J : ℕ)
    (h : ∀ q ∈ S, (cnt δ acc (J + d) q : ℤ) = ∑ i ∈ range d, c i * cnt δ acc (J + i) q) :
    ∀ n, ∀ q ∈ S, (cnt δ acc (n + J + d) q : ℤ) = ∑ i ∈ range d, c i * cnt δ acc (n + J + i) q := by
  intro n
  induction n with
  | zero => intro q hq; simpa using h q hq
  | succ n ih =>
    intro q hq
    rw [show n + 1 + J + d = (n + J + d) + 1 by ring, cnt_succ]
    push_cast
    rw [Finset.sum_congr rfl (fun a _ => ih (δ q a) (hS q hq a)), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, show n + 1 + J + i = (n + J + i) + 1 by ring, cnt_succ]
    push_cast
    rfl

end automaton

theorem window (x : ℕ → ℤ) (D : ℕ) (q : ℕ → ℤ)
    (hx : ∀ n, x (n + D) = ∑ i ∈ range D, q i * x (n + i))
    (e : ℕ) (p : ℕ → ℤ)
    (h0 : ∀ n < D, x (n + e) = ∑ j ∈ range e, p j * x (n + j)) :
    ∀ n, x (n + e) = ∑ j ∈ range e, p j * x (n + j) := by
  let b : ℕ → ℤ := fun n => x (n + e) - ∑ j ∈ range e, p j * x (n + j)
  have hb : ∀ n, b n = x (n + e) - ∑ j ∈ range e, p j * x (n + j) := fun n => rfl
  have hbrec : ∀ n, b (n + D) = ∑ i ∈ range D, q i * b (n + i) := by
    intro n
    rw [hb, show n + D + e = (n + e) + D by ring, hx (n + e)]
    have e2 : ∀ j, x (n + D + j) = ∑ i ∈ range D, q i * x (n + j + i) := by
      intro j
      rw [show n + D + j = (n + j) + D by ring, hx (n + j)]
    simp only [e2, hb, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [show n + e + i = n + i + e by ring]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show n + j + i = n + i + j by ring]
      ring
  have hz : ∀ n, b n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < D
      · rw [hb, h0 n hn, sub_self]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + D := ⟨n - D, by omega⟩
        rw [hbrec m]
        apply Finset.sum_eq_zero
        intro i hi
        rw [ih (m + i) (by simp at hi; omega), mul_zero]
  intro n
  have := hz n
  rw [hb] at this
  linarith

end TMLib


/-!
Row-by-row step lemmas for "every line is unimodal" conditions on arrays `X : ℕ → ℕ → ℕ`
(rows `< m`, columns `< k`). A line of slope `s ∈ {-1, 0, 1}` through `(i, j)` meets row `t`
in column `j + s * (i - t)`: `s = 0` columns, `s = 1` antidiagonals (`i + j` constant),
`s = -1` diagonals (`j - i` constant). `Y` is `X` with one more row `r` (row index `m`).
-/

namespace UniLib

/-- No valley: the middle value is not strictly below both outer values. -/
def NV (u v w : ℕ) : Prop := ¬ (v < u ∧ v < w)

/-- Every line of slope `s` is unimodal (no valley among three of its cells). -/
def Uni (s : ℤ) (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ i1 i2 i3 j1 j2 j3 : ℕ, i1 < i2 → i2 < i3 → i3 < m → j1 < k → j2 < k → j3 < k →
    (j1 : ℤ) - j2 = s * ((i2 : ℤ) - i1) → (j2 : ℤ) - j3 = s * ((i3 : ℤ) - i2) →
    NV (X i1 j1) (X i2 j2) (X i3 j3)

/-- The line of slope `s` through the cell `(m - 1, j)` of the last row has a strict descent. -/
def Fl (s : ℤ) (m k : ℕ) (X : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∃ i1 i2 j1 j2 : ℕ, i1 < i2 ∧ i2 < m ∧ j1 < k ∧ j2 < k ∧ (j1 : ℤ) - j2 = s * ((i2 : ℤ) - i1) ∧
    (j2 : ℤ) - j = s * (((m : ℤ) - 1) - i2) ∧ X i2 j2 < X i1 j1

/-- Columns are nondecreasing downwards. -/
def ColND (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ i1 i2 j : ℕ, i1 < i2 → i2 < m → j < k → X i1 j ≤ X i2 j

/-- A row is unimodal. -/
def RowOK (k : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ j3, j3 < k → ∀ j2, j2 < j3 → ∀ j1, j1 < j2 → NV (r j1) (r j2) (r j3)

def RowsOK (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop := ∀ i < m, RowOK k (X i)

section step

variable {s : ℤ} {m k : ℕ} {X Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ}

theorem uni_step (hs : s = -1 ∨ s = 0 ∨ s = 1) (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    Uni s (m + 1) k Y ↔ Uni s m k X ∧
      ∀ j, j < k → ∀ j', j' < k → (j' : ℤ) = j + s → ¬ (Fl s m k X j' ∧ X (m - 1) j' < r j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
      have := h i1 i2 i3 j1 j2 j3 h12 h23 (by omega) hj1 hj2 hj3 e1 e2
      rwa [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 i3 h3 j3 hj3] at this
    · rintro j hj j' hj' hjj ⟨⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩, hlast⟩
      by_cases hi2 : i2 = m - 1
      · subst hi2
        have hjj2 : j2 = j' := by
          have : ((m : ℤ) - 1) - ((m - 1 : ℕ) : ℤ) = 0 := by omega
          rw [this, mul_zero] at e2; omega
        subst hjj2
        have := h i1 (m - 1) m j1 j2 j h12 (by omega) (by omega) hj1 hj2 hj e1 (by
          rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] <;> omega)
        rw [hY1 i1 (by omega) j1 hj1, hY1 (m - 1) (by omega) j2 hj2, hY2 j hj] at this
        exact this ⟨hlt, hlast⟩
      · by_cases hc : X i2 j2 < X (m - 1) j'
        · have := h i1 i2 (m - 1) j1 j2 j' h12 (by omega) (by omega) hj1 hj2 hj' e1 (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e2 ⊢ <;> omega)
          rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 (m - 1) (by omega) j' hj'] at this
          exact this ⟨hlt, hc⟩
        · have := h i1 (m - 1) m j1 j' j (by omega) (by omega) (by omega) hj1 hj' hj (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 e2 ⊢ <;> omega) (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at hjj ⊢ <;> omega)
          rw [hY1 i1 (by omega) j1 hj1, hY1 (m - 1) (by omega) j' hj', hY2 j hj] at this
          exact this ⟨by omega, hlast⟩
  · rintro ⟨hU, hL⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    by_cases hi3 : i3 < m
    · rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 i3 hi3 j3 hj3]
      exact hU i1 i2 i3 j1 j2 j3 h12 h23 hi3 hj1 hj2 hj3 e1 e2
    · have hi3m : i3 = m := by omega
      subst hi3m
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY2 j3 hj3]
      rintro ⟨hv1, hv2⟩
      obtain ⟨j', hj'⟩ : ∃ j' : ℕ, (j' : ℤ) = j3 + s :=
        ⟨(j3 + s).toNat, by rcases hs with rfl | rfl | rfl <;> omega⟩
      have hj'k : j' < k := by rcases hs with rfl | rfl | rfl <;> omega
      have hfl : Fl s i3 k X j' := ⟨i1, i2, j1, j2, h12, h23, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> omega, hv1⟩
      apply hL j3 hj3 j' hj'k hj' ⟨hfl, ?_⟩
      by_cases hi2 : i2 = i3 - 1
      · subst hi2
        have : j2 = j' := by rcases hs with rfl | rfl | rfl <;> omega
        subst this; exact hv2
      · have := hU i1 i2 (i3 - 1) j1 j2 j' h12 (by omega) (by omega) hj1 hj2 hj'k e1 (by
          rcases hs with rfl | rfl | rfl <;> omega)
        unfold NV at this
        omega

theorem fl_step (hs : s = -1 ∨ s = 0 ∨ s = 1) (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) (j : ℕ) (hj : j < k) :
    Fl s (m + 1) k Y j ↔ ∃ j', j' < k ∧ (j' : ℤ) = j + s ∧ (Fl s m k X j' ∨ r j < X (m - 1) j') := by
  constructor
  · rintro ⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩
    obtain ⟨j', hj'⟩ : ∃ j' : ℕ, (j' : ℤ) = j + s :=
      ⟨(j + s).toNat, by rcases hs with rfl | rfl | rfl <;> push_cast at e1 e2 <;> omega⟩
    have hj'k : j' < k := by rcases hs with rfl | rfl | rfl <;> push_cast at e1 e2 <;> omega
    refine ⟨j', hj'k, hj', ?_⟩
    by_cases hi2 : i2 < m
    · left
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 hi2 j2 hj2] at hlt
      exact ⟨i1, i2, j1, j2, h12, hi2, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> push_cast at e2 ⊢ <;> omega, hlt⟩
    · have hi2m : i2 = m := by omega
      subst hi2m
      have hjj : j2 = j := by rcases hs with rfl | rfl | rfl <;> push_cast at e2 <;> omega
      subst hjj
      rw [hY1 i1 (by omega) j1 hj1, hY2 j2 hj2] at hlt
      by_cases hc : r j2 < X (i2 - 1) j'
      · right; exact hc
      · left
        have hi1 : i1 < i2 - 1 := by
          by_contra hcon
          have h1 : i1 = i2 - 1 := by omega
          subst h1
          have : j1 = j' := by rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 ⊢ <;> omega
          subst this; omega
        exact ⟨i1, i2 - 1, j1, j', hi1, by omega, hj1, hj'k, by
          rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 ⊢ <;> omega, by
          push_cast [Nat.cast_sub hm]; ring, by omega⟩
  · rintro ⟨j', hj'k, hj', h | h⟩
    · obtain ⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩ := h
      refine ⟨i1, i2, j1, j2, h12, by omega, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> push_cast at e2 ⊢ <;> omega, ?_⟩
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 h2m j2 hj2]; exact hlt
    · refine ⟨m - 1, m, j', j, by omega, by omega, hj'k, hj, by
        rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] <;> omega, by
        push_cast; ring, ?_⟩
      rw [hY1 (m - 1) (by omega) j' hj'k, hY2 j hj]; exact h

theorem colnd_step (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    ColND (m + 1) k Y ↔ ColND m k X ∧ ∀ j < k, X (m - 1) j ≤ r j := by
  constructor
  · intro h
    refine ⟨fun i1 i2 j h12 h2 hj => ?_, fun j hj => ?_⟩
    · have := h i1 i2 j h12 (by omega) hj
      rwa [hY1 i1 (by omega) j hj, hY1 i2 h2 j hj] at this
    · have := h (m - 1) m j (by omega) (by omega) hj
      rwa [hY1 (m - 1) (by omega) j hj, hY2 j hj] at this
  · rintro ⟨hC, hL⟩ i1 i2 j h12 h2 hj
    by_cases hi2 : i2 < m
    · rw [hY1 i1 (by omega) j hj, hY1 i2 hi2 j hj]; exact hC i1 i2 j h12 hi2 hj
    · have : i2 = m := by omega
      subst this
      rw [hY1 i1 (by omega) j hj, hY2 j hj]
      by_cases h1 : i1 = i2 - 1
      · subst h1; exact hL j hj
      · exact le_trans (hC i1 (i2 - 1) j (by omega) (by omega) hj) (hL j hj)

theorem rows_step (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    RowsOK (m + 1) k Y ↔ RowsOK m k X ∧ RowOK k r := by
  have hrow : ∀ i < m, (RowOK k (Y i) ↔ RowOK k (X i)) := by
    intro i hi
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY1 i hi j1 (by omega), hY1 i hi j2 (by omega), hY1 i hi j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY1 i hi j1 (by omega), hY1 i hi j2 (by omega), hY1 i hi j3 c]
      exact h j3 c j2 b j1 a
  have hlast : RowOK k (Y m) ↔ RowOK k r := by
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY2 j1 (by omega), hY2 j2 (by omega), hY2 j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY2 j1 (by omega), hY2 j2 (by omega), hY2 j3 c]
      exact h j3 c j2 b j1 a
  constructor
  · intro h
    exact ⟨fun i hi => (hrow i hi).1 (h i (by omega)), hlast.1 (h m (by omega))⟩
  · rintro ⟨hR, hr⟩ i hi
    by_cases him : i < m
    · exact (hrow i him).2 (hR i him)
    · have : i = m := by omega
      subst this; exact hlast.2 hr

end step

/-! ## The family predicate, one row at a time -/

/-- Local "no rise after a descent" condition for lines of slope `s` entering row `r`. -/
def LC (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) (r : ℕ → ℕ) : Prop :=
  ∀ j, j < k → ∀ j', j' < k → (j' : ℤ) = j + s → ¬ (f j' ∧ L j' < r j)

/-- New descent flag of the line of slope `s` through column `j` of the new row `r`. -/
def NF (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) (r : ℕ → ℕ) (j : ℕ) : Prop :=
  ∃ j', j' < k ∧ (j' : ℤ) = j + s ∧ (f j' ∨ r j < L j')

/-- Rows unimodal; columns unimodal (`cu`) or nondecreasing; diagonals (`dg`) and antidiagonals
(`an`) unimodal when asked. -/
def P (cu dg an : Bool) (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  RowsOK m k X ∧ (if cu = true then Uni 0 m k X else ColND m k X) ∧
    (dg = true → Uni (-1) m k X) ∧ (an = true → Uni 1 m k X)

def LocOK (cu dg an : Bool) (k : ℕ) (L : ℕ → ℕ) (fc fd fa : ℕ → Prop) (r : ℕ → ℕ) : Prop :=
  RowOK k r ∧ (if cu = true then LC k 0 L fc r else ∀ j, j < k → L j ≤ r j) ∧
    (dg = true → LC k (-1) L fd r) ∧ (an = true → LC k 1 L fa r)

theorem P_step {cu dg an : Bool} {m k : ℕ} {X Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ} (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    P cu dg an (m + 1) k Y ↔ P cu dg an m k X ∧
      LocOK cu dg an k (X (m - 1)) (Fl 0 m k X) (Fl (-1) m k X) (Fl 1 m k X) r := by
  have hR := rows_step hY1 hY2
  have hC0 := uni_step (s := 0) (by norm_num) hm hY1 hY2
  have hCn := colnd_step hm hY1 hY2
  have hD := uni_step (s := -1) (by norm_num) hm hY1 hY2
  have hA := uni_step (s := 1) (by norm_num) hm hY1 hY2
  have hC : (if cu = true then Uni 0 (m + 1) k Y else ColND (m + 1) k Y) ↔
      (if cu = true then Uni 0 m k X else ColND m k X) ∧
        (if cu = true then LC k 0 (X (m - 1)) (Fl 0 m k X) r else ∀ j, j < k → X (m - 1) j ≤ r j) := by
    cases cu
    · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact hCn
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]; exact hC0
  have hDg : (dg = true → Uni (-1) (m + 1) k Y) ↔
      (dg = true → Uni (-1) m k X) ∧ (dg = true → LC k (-1) (X (m - 1)) (Fl (-1) m k X) r) := by
    cases dg
    · exact ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
        fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h => ⟨fun _ => (hD.1 (h rfl)).1, fun _ => (hD.1 (h rfl)).2⟩,
        fun h _ => hD.2 ⟨h.1 rfl, h.2 rfl⟩⟩
  have hAn : (an = true → Uni 1 (m + 1) k Y) ↔
      (an = true → Uni 1 m k X) ∧ (an = true → LC k 1 (X (m - 1)) (Fl 1 m k X) r) := by
    cases an
    · exact ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
        fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h => ⟨fun _ => (hA.1 (h rfl)).1, fun _ => (hA.1 (h rfl)).2⟩,
        fun h _ => hA.2 ⟨h.1 rfl, h.2 rfl⟩⟩
  unfold P LocOK
  rw [hR, hC, hDg, hAn]
  exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩⟩ => ⟨⟨a, c, e, g⟩, ⟨b, d, f, h⟩⟩,
    fun ⟨⟨a, c, e, g⟩, ⟨b, d, f, h⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩⟩⟩

theorem P_one {cu dg an : Bool} {k : ℕ} {Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ} (hY : ∀ j < k, Y 0 j = r j) :
    P cu dg an 1 k Y ↔ RowOK k r := by
  have hrow : RowOK k (Y 0) ↔ RowOK k r := by
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY j1 (by omega), hY j2 (by omega), hY j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY j1 (by omega), hY j2 (by omega), hY j3 c]
      exact h j3 c j2 b j1 a
  have hU : ∀ s, Uni s 1 k Y := fun s i1 i2 i3 _ _ _ h12 h23 h3 => by omega
  have hC : ColND 1 k Y := fun i1 i2 _ h12 h2 => by omega
  unfold P
  constructor
  · rintro ⟨h, -⟩; exact hrow.1 (h 0 (by omega))
  · intro h
    refine ⟨fun i hi => ?_, ?_, fun _ => hU _, fun _ => hU _⟩
    · have : i = 0 := by omega
      subst this; exact hrow.2 h
    · cases cu <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> first | exact hU _ | exact hC

theorem Fl_one {s : ℤ} {k : ℕ} {Y : ℕ → ℕ → ℕ} (j : ℕ) : ¬ Fl s 1 k Y j := by
  rintro ⟨i1, i2, _, _, h12, h2, -⟩; omega

theorem LC_congr {k : ℕ} {s : ℤ} {L L' : ℕ → ℕ} {f f' : ℕ → Prop} {r : ℕ → ℕ}
    (hL : ∀ j < k, L j = L' j) (hf : ∀ j < k, (f j ↔ f' j)) : LC k s L f r ↔ LC k s L' f' r := by
  unfold LC
  constructor
  · intro h j hj j' hj' e ⟨h1, h2⟩
    exact h j hj j' hj' e ⟨(hf j' hj').2 h1, by rw [hL j' hj']; exact h2⟩
  · intro h j hj j' hj' e ⟨h1, h2⟩
    exact h j hj j' hj' e ⟨(hf j' hj').1 h1, by rw [← hL j' hj']; exact h2⟩

theorem NF_congr {k : ℕ} {s : ℤ} {L L' : ℕ → ℕ} {f f' : ℕ → Prop} {r : ℕ → ℕ} (j : ℕ)
    (hL : ∀ j < k, L j = L' j) (hf : ∀ j < k, (f j ↔ f' j)) : NF k s L f r j ↔ NF k s L' f' r j := by
  unfold NF
  constructor
  · rintro ⟨j', hj', e, h⟩
    refine ⟨j', hj', e, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hf j' hj').1 h)
    · exact Or.inr (by rw [← hL j' hj']; exact h)
  · rintro ⟨j', hj', e, h⟩
    refine ⟨j', hj', e, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hf j' hj').2 h)
    · exact Or.inr (by rw [hL j' hj']; exact h)

theorem LocOK_congr {cu dg an : Bool} {k : ℕ} {L L' : ℕ → ℕ} {fc fd fa fc' fd' fa' : ℕ → Prop}
    {r : ℕ → ℕ} (hL : ∀ j < k, L j = L' j) (hc : cu = true → ∀ j < k, (fc j ↔ fc' j))
    (hd : dg = true → ∀ j < k, (fd j ↔ fd' j)) (ha : an = true → ∀ j < k, (fa j ↔ fa' j)) :
    LocOK cu dg an k L fc fd fa r ↔ LocOK cu dg an k L' fc' fd' fa' r := by
  unfold LocOK
  have hmono : (∀ j, j < k → L j ≤ r j) ↔ (∀ j, j < k → L' j ≤ r j) := by
    constructor
    · intro h j hj; rw [← hL j hj]; exact h j hj
    · intro h j hj; rw [hL j hj]; exact h j hj
  have h1 : (if cu = true then LC k 0 L fc r else ∀ j, j < k → L j ≤ r j) ↔
      (if cu = true then LC k 0 L' fc' r else ∀ j, j < k → L' j ≤ r j) := by
    cases cu
    · rw [if_neg (by decide), if_neg (by decide)]; exact hmono
    · rw [if_pos rfl, if_pos rfl]; exact LC_congr hL (hc rfl)
  have h2 : (dg = true → LC k (-1) L fd r) ↔ (dg = true → LC k (-1) L' fd' r) := by
    cases dg
    · exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h _ => (LC_congr hL (hd rfl)).1 (h rfl), fun h _ => (LC_congr hL (hd rfl)).2 (h rfl)⟩
  have h3 : (an = true → LC k 1 L fa r) ↔ (an = true → LC k 1 L' fa' r) := by
    cases an
    · exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h _ => (LC_congr hL (ha rfl)).1 (h rfl), fun h _ => (LC_congr hL (ha rfl)).2 (h rfl)⟩
  exact and_congr Iff.rfl (and_congr h1 (and_congr h2 h3))

/-! ## Table automaton (generated data) and the bridge -/

section table

variable (cu dg an : Bool) (k b R : ℕ) (dl rowL : List (List ℕ)) (fcL fdL faL : List (List Bool))

def δt (q c : ℕ) : ℕ := (dl.getD q []).getD c R
def Lq (q j : ℕ) : ℕ := (rowL.getD q []).getD j 0
def Fq (fl : List (List Bool)) (q j : ℕ) : Prop := (fl.getD q []).getD j false = true
/-- Digit `j` of the row code `c` in base `b`. -/
def rc (c j : ℕ) : ℕ := c / b ^ j % b

instance (fl : List (List Bool)) (q j : ℕ) : Decidable (Fq fl q j) := by unfold Fq; infer_instance
instance (k : ℕ) (r : ℕ → ℕ) : Decidable (RowOK k r) := by unfold RowOK NV; infer_instance
instance (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) [DecidablePred f] (r : ℕ → ℕ) :
    Decidable (LC k s L f r) := by unfold LC; infer_instance
instance (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) [DecidablePred f] (r : ℕ → ℕ) (j : ℕ) :
    Decidable (NF k s L f r j) := by unfold NF; infer_instance
instance (cu dg an : Bool) (k : ℕ) (L : ℕ → ℕ) (fc fd fa : ℕ → Prop) [DecidablePred fc]
    [DecidablePred fd] [DecidablePred fa] (r : ℕ → ℕ) : Decidable (LocOK cu dg an k L fc fd fa r) := by
  unfold LocOK; infer_instance

/-- First row `c` read from the start state `0`. -/
def StartOK (c : ℕ) : Prop :=
  (δt R dl 0 c = R ↔ ¬ RowOK k (rc b c)) ∧
    (δt R dl 0 c ≠ R → 1 ≤ δt R dl 0 c ∧ δt R dl 0 c < R ∧ ∀ j, j < k →
      Lq rowL (δt R dl 0 c) j = rc b c j ∧ ¬ Fq fcL (δt R dl 0 c) j ∧ ¬ Fq fdL (δt R dl 0 c) j ∧
        ¬ Fq faL (δt R dl 0 c) j)

/-- Last row and flags of the successor state `q'`, column `j`. -/
def FlagOK (q c q' j : ℕ) : Prop :=
  Lq rowL q' j = rc b c j ∧
    (cu = true → (Fq fcL q' j ↔ NF k 0 (Lq rowL q) (Fq fcL q) (rc b c) j)) ∧
    (dg = true → (Fq fdL q' j ↔ NF k (-1) (Lq rowL q) (Fq fdL q) (rc b c) j)) ∧
    (an = true → (Fq faL q' j ↔ NF k 1 (Lq rowL q) (Fq faL q) (rc b c) j))

/-- Row `c` read from a live state `q`. -/
def StepOK (q c : ℕ) : Prop :=
  (δt R dl q c = R ↔ ¬ LocOK cu dg an k (Lq rowL q) (Fq fcL q) (Fq fdL q) (Fq faL q) (rc b c)) ∧
    (δt R dl q c ≠ R → 1 ≤ δt R dl q c ∧ δt R dl q c < R ∧ ∀ j, j < k →
      FlagOK cu dg an k b rowL fcL fdL faL q c (δt R dl q c) j)

/-- The generated table is a correct automaton for `P`: state `0` = no row yet, `R` = dead. -/
def TableOK : Prop :=
  dl.length = R ∧ (∀ c, c < b ^ k → StartOK k b R dl rowL fcL fdL faL c) ∧
    (∀ q, q < R → 1 ≤ q → ∀ c, c < b ^ k → StepOK cu dg an k b R dl rowL fcL fdL faL q c)

instance (c : ℕ) : Decidable (StartOK k b R dl rowL fcL fdL faL c) := by
  unfold StartOK; infer_instance
instance (q c q' j : ℕ) : Decidable (FlagOK cu dg an k b rowL fcL fdL faL q c q' j) := by
  unfold FlagOK; infer_instance
instance (q c : ℕ) : Decidable (StepOK cu dg an k b R dl rowL fcL fdL faL q c) := by
  unfold StepOK; infer_instance
instance : Decidable (TableOK cu dg an k b R dl rowL fcL fdL faL) := by unfold TableOK; infer_instance

/-- The array of a word of row codes. -/
def Xw {n : ℕ} (w : Fin n → Fin (b ^ k)) (i j : ℕ) : ℕ := if h : i < n then rc b (w ⟨i, h⟩) j else 0

def δA (q : ℕ) (a : Fin (b ^ k)) : ℕ := δt R dl q a.val

def Matches (q m : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ j < k, X (m - 1) j = Lq rowL q j ∧ (cu = true → (Fq fcL q j ↔ Fl 0 m k X j)) ∧
    (dg = true → (Fq fdL q j ↔ Fl (-1) m k X j)) ∧ (an = true → (Fq faL q j ↔ Fl 1 m k X j))

theorem run_append {A : Type} (δ : ℕ → A → ℕ) (q : ℕ) (l1 l2 : List A) :
    TMLib.run δ q (l1 ++ l2) = TMLib.run δ (TMLib.run δ q l1) l2 := by
  induction l1 generalizing q with
  | nil => rfl
  | cons a l ih => exact ih (δ q a)

theorem bridge (hT : TableOK cu dg an k b R dl rowL fcL fdL faL) (n : ℕ) (w : Fin n → Fin (b ^ k)) :
    (n = 0 → TMLib.run (δA k b R dl) 0 (List.ofFn w) = 0) ∧
    (1 ≤ n → (TMLib.run (δA k b R dl) 0 (List.ofFn w) ≠ R ↔ P cu dg an n k (Xw k b w)) ∧
      (TMLib.run (δA k b R dl) 0 (List.ofFn w) ≠ R →
        1 ≤ TMLib.run (δA k b R dl) 0 (List.ofFn w) ∧ TMLib.run (δA k b R dl) 0 (List.ofFn w) < R ∧
        Matches cu dg an k rowL fcL fdL faL (TMLib.run (δA k b R dl) 0 (List.ofFn w)) n (Xw k b w))) := by
  obtain ⟨hlen, h0, hq⟩ := hT
  have dead : ∀ c, δt R dl R c = R := by
    intro c; unfold δt; rw [List.getD_eq_default dl [] (by omega)]; simp
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h => by omega⟩
  | succ n ih =>
    refine ⟨fun h => by omega, fun _ => ?_⟩
    set w0 : Fin n → Fin (b ^ k) := fun i => w i.castSucc with hw0
    set c := w (Fin.last n) with hc
    have hlist : List.ofFn w = List.ofFn w0 ++ [c] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    have hrun : TMLib.run (δA k b R dl) 0 (List.ofFn w) =
        δt R dl (TMLib.run (δA k b R dl) 0 (List.ofFn w0)) c.val := by
      rw [hlist, run_append]; rfl
    have hY1 : ∀ i < n, ∀ j < k, Xw k b w i j = Xw k b w0 i j := by
      intro i hi j _
      unfold Xw; rw [dif_pos (by omega), dif_pos hi]; try rfl
    have hY2 : ∀ j < k, Xw k b w n j = rc b c.val j := by
      intro j _; unfold Xw; rw [dif_pos (by omega)]; try rfl
    rw [hrun]
    obtain ⟨ih0, ih1⟩ := ih w0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- first row
      subst hn
      rw [ih0 rfl]
      obtain ⟨hc1, hc2⟩ : StartOK k b R dl rowL fcL fdL faL c.val := h0 c.val c.isLt
      have hP : P cu dg an (0 + 1) k (Xw k b w) ↔ RowOK k (rc b c.val) := P_one hY2
      refine ⟨by rw [hP, ne_eq, hc1, not_not], fun hne => ?_⟩
      obtain ⟨a1, a2, a3⟩ := hc2 hne
      refine ⟨a1, a2, fun j hj => ?_⟩
      obtain ⟨e1, e2, e3, e4⟩ := a3 j hj
      refine ⟨by rw [e1]; exact hY2 j hj, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
        exact iff_of_false (by assumption) (Fl_one j)
    · obtain ⟨ihP, ihM⟩ := ih1 hn
      have hstep := P_step (cu := cu) (dg := dg) (an := an) hn hY1 hY2
      by_cases hq0 : TMLib.run (δA k b R dl) 0 (List.ofFn w0) = R
      · rw [hq0, dead]
        refine ⟨?_, fun h => absurd rfl h⟩
        rw [hstep]
        simp only [ne_eq, not_true_eq_false, false_iff, not_and]
        intro hp; exact absurd hp (by rw [← ihP]; exact not_not.2 hq0)
      · set q := TMLib.run (δA k b R dl) 0 (List.ofFn w0) with hqdef
        obtain ⟨q1, q2, hM⟩ := ihM hq0
        have hPX : P cu dg an n k (Xw k b w0) := ihP.1 hq0
        obtain ⟨t1, t2⟩ : StepOK cu dg an k b R dl rowL fcL fdL faL q c.val := hq q q2 q1 c.val c.isLt
        have hloc : LocOK cu dg an k (Xw k b w0 (n - 1)) (Fl 0 n k (Xw k b w0)) (Fl (-1) n k (Xw k b w0))
            (Fl 1 n k (Xw k b w0)) (rc b c.val) ↔
            LocOK cu dg an k (Lq rowL q) (Fq fcL q) (Fq fdL q) (Fq faL q) (rc b c.val) :=
          LocOK_congr (fun j hj => (hM j hj).1) (fun h j hj => ((hM j hj).2.1 h).symm)
            (fun h j hj => ((hM j hj).2.2.1 h).symm) (fun h j hj => ((hM j hj).2.2.2 h).symm)
        refine ⟨?_, fun hne => ?_⟩
        · rw [hstep, hloc, ne_eq, t1, not_not]
          exact ⟨fun h => ⟨hPX, h⟩, fun h => h.2⟩
        · obtain ⟨u1, u2, u3⟩ := t2 hne
          refine ⟨u1, u2, fun j hj => ?_⟩
          obtain ⟨v1, v2, v3, v4⟩ := u3 j hj
          have hm' : n + 1 - 1 = n := by omega
          refine ⟨by rw [hm', v1]; exact hY2 j hj, fun h => ?_, fun h => ?_, fun h => ?_⟩
          · rw [v2 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.1 h)
          · rw [v3 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.2.1 h)
          · rw [v4 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.2.2 h)

end table

end UniLib

/-! ## From the statement's `Fin` arrays to the library, and polynomial closed forms -/

namespace UniLib

section finlemmas

variable {n k b : ℕ} (x : Fin n → Fin k → Fin b) (X : ℕ → ℕ → ℕ)
  (hX : ∀ (i : Fin n) (j : Fin k), ((x i j : Fin b) : ℕ) = X i j)
include hX

theorem rows_fin :
    (∀ i : Fin n, ∀ j1 j2 j3 : Fin k, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)) ↔
      RowsOK n k X := by
  constructor
  · intro h i hi j3 hj3 j2 hj2 j1 hj1
    have := h ⟨i, hi⟩ ⟨j1, by omega⟩ ⟨j2, by omega⟩ ⟨j3, hj3⟩ (Fin.mk_lt_mk.2 hj1) (Fin.mk_lt_mk.2 hj2)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i j1 j2 j3 h12 h23
    have := h i.val i.isLt j3.val j3.isLt j2.val h23 j1.val h12
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact this

theorem colnd_fin :
    (∀ i1 i2 : Fin n, ∀ j : Fin k, i1 ≤ i2 → x i1 j ≤ x i2 j) ↔ ColND n k X := by
  constructor
  · intro h i1 i2 j h12 h2 hj
    have := h ⟨i1, by omega⟩ ⟨i2, h2⟩ ⟨j, hj⟩ (Fin.mk_le_mk.2 (le_of_lt h12))
    simp only [Fin.le_iff_val_le_val, hX] at this
    exact this
  · intro h i1 i2 j h12
    simp only [Fin.le_iff_val_le_val, hX]
    rcases lt_or_eq_of_le h12 with h' | h'
    · exact h i1 i2 j h' i2.isLt j.isLt
    · rw [h']

theorem colu_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j : Fin k, i1 < i2 → i2 < i3 → ¬ (x i2 j < x i1 j ∧ x i2 j < x i3 j)) ↔
      Uni 0 n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have e1' : j1 = j2 := by simp only [zero_mul] at e1; omega
    have e2' : j2 = j3 := by simp only [zero_mul] at e2; omega
    subst e1' e2'
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j h12 h23
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j j j h12 h23 i3.isLt j.isLt j.isLt j.isLt (by simp) (by simp)

theorem anti_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin k, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
      (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)) ↔ Uni 1 n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23) (by show i1 + j1 = i2 + j2; omega)
      (by show i2 + j2 = i3 + j3; omega)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j1 j2 j3 h12 h23 i3.isLt j1.isLt j2.isLt j3.isLt (by omega) (by omega)

theorem diag_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin k, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
      (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)) ↔ Uni (-1) n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23) (by show j1 + i2 = j2 + i1; omega)
      (by show j2 + i3 = j3 + i2; omega)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j1 j2 j3 h12 h23 i3.isLt j1.isLt j2.isLt j3.isLt (by omega) (by omega)

end finlemmas

theorem arr_val {n k b : ℕ} (x : Fin n → Fin k → Fin b) (i : Fin n) (j : Fin k) :
    ((x i j : Fin b) : ℕ) = Xw k b (fun i => finFunctionFinEquiv (x i)) i j := by
  unfold Xw rc
  rw [dif_pos i.isLt, ← finFunctionFinEquiv_symm_apply_val]
  simp

open Classical in
theorem count_arrays {cu dg an : Bool} {n k b : ℕ} (pred : (Fin n → Fin k → Fin b) → Prop)
    {inst : DecidablePred pred}
    (h : ∀ x, pred x ↔ P cu dg an n k (Xw k b (fun i => finFunctionFinEquiv (x i)))) :
    (@Finset.filter _ pred inst Finset.univ).card =
      (Finset.univ.filter (fun w : Fin n → Fin (b ^ k) => P cu dg an n k (Xw k b w))).card := by
  apply Finset.card_equiv (Equiv.piCongrRight (fun _ => finFunctionFinEquiv))
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

open Classical in
theorem count_words (cu dg an : Bool) (k b R : ℕ) (dl rowL : List (List ℕ)) (fcL fdL faL : List (List Bool))
    (hT : TableOK cu dg an k b R dl rowL fcL fdL faL) (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun w : Fin n → Fin (b ^ k) => P cu dg an n k (Xw k b w))).card =
      TMLib.cnt (δA k b R dl) (fun q => decide (q ≠ R)) n 0 := by
  rw [← TMLib.card_run]
  exact congrArg Finset.card (Finset.filter_congr (fun w _ => by
    rw [decide_eq_true_iff]
    exact ((bridge cu dg an k b R dl rowL fcL fdL faL hT n w).2 hn).1.symm))

end UniLib

namespace TMLib

open Finset

/-- A sequence satisfying a linear recurrence from shift `J` on agrees with a polynomial `Pz / den`
(which satisfies the same recurrence everywhere) from `n0` on, once they agree on `[n0, n0 + J + D)`. -/
theorem rec_poly (x : ℕ → ℤ) (D J n0 : ℕ) (cc : ℕ → ℤ) (Pz : ℤ → ℤ) (den : ℤ)
    (hx : ∀ n, x (n + J + D) = ∑ i ∈ range D, cc i * x (n + J + i))
    (hP : ∀ t : ℤ, Pz (t + D) = ∑ i ∈ range D, cc i * Pz (t + i))
    (h0 : ∀ m, n0 ≤ m → m < n0 + J + D → den * x m = Pz m) :
    ∀ m, n0 ≤ m → den * x m = Pz m := by
  let z : ℕ → ℤ := fun n => den * x (n + (n0 + J)) - Pz ((n + (n0 + J) : ℕ) : ℤ)
  have hz : ∀ n, z (n + D) = ∑ i ∈ range D, cc i * z (n + i) := by
    intro n
    simp only [z]
    rw [show n + D + (n0 + J) = (n + n0) + J + D by ring, hx (n + n0)]
    rw [show (((n + n0) + J + D : ℕ) : ℤ) = ((n + n0 + J : ℕ) : ℤ) + D by push_cast; ring, hP]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show n + i + (n0 + J) = n + n0 + J + i by ring]
    push_cast
    ring
  have hz0 := window z D cc hz 0 (fun _ => 0) (fun n hn => by
    simp only [z, add_zero, Finset.range_zero, Finset.sum_empty]
    rw [h0 (n + (n0 + J)) (by omega) (by omega), sub_self])
  intro m hm
  by_cases hmJ : m < n0 + J + D
  · exact h0 m hm hmJ
  · have := hz0 (m - (n0 + J))
    simp only [z, add_zero, Finset.range_zero, Finset.sum_empty] at this
    rw [show m - (n0 + J) + (n0 + J) = m by omega] at this
    linarith

end TMLib


/-! Our own formulation (Fin-function arrays, no-valley conditions) and its proof. -/
namespace OMAOurA223835

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 5, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 5, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every diagonal (cells with `j - i` constant, read by increasing `i`) is unimodal. -/
def DiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 5, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
    (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (DiagonalsUnimodal x) := by
  unfold DiagonalsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 5, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223835(n): the number of `n X 5` arrays with entries 0..1 whose rows, diagonals and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 5 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ DiagonalsUnimodal x ∧ AntidiagonalsUnimodal x)).card




open UniLib Finset PowerSeries

def dl : List (List ℕ) := [[1, 2, 3, 4, 5, 56, 6, 7, 8, 56, 56, 56, 9, 56, 10, 11, 12, 56, 56, 56, 56, 56, 56, 56, 13, 56, 56, 56, 14, 56, 15, 16], [1, 2, 3, 4, 5, 56, 6, 7, 8, 56, 56, 56, 9, 56, 10, 11, 12, 56, 56, 56, 56, 56, 56, 56, 13, 56, 56, 56, 14, 56, 15, 16], [56, 17, 56, 4, 56, 56, 56, 7, 56, 56, 56, 56, 56, 56, 56, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 56, 18, 19, 56, 56, 20, 7, 56, 56, 56, 56, 56, 56, 21, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 19, 56, 56, 56, 7, 56, 56, 56, 56, 56, 56, 56, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 56, 56, 56, 23, 56, 24, 25, 56, 56, 56, 56, 26, 56, 10, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 27, 56, 15, 16], [56, 56, 56, 56, 56, 56, 28, 25, 56, 56, 56, 56, 56, 56, 21, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 25, 56, 56, 56, 56, 56, 56, 56, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 56, 56, 56, 56, 56, 56, 56, 29, 56, 56, 56, 30, 56, 31, 32, 56, 56, 56, 56, 56, 56, 56, 56, 33, 56, 56, 56, 14, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 34, 56, 31, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 27, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 36, 56, 56, 56, 56, 56, 56, 56, 13, 56, 56, 56, 14, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 33, 56, 56, 56, 14, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 27, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 37, 56, 19, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 38, 39, 56, 56, 28, 25, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 39, 56, 56, 56, 25, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 28, 25, 56, 56, 56, 56, 56, 56, 21, 11, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 40, 56, 41, 56, 56, 56, 56, 56, 42, 56, 35, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 41, 43, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 43, 56, 56, 56, 56, 56, 56, 56, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 42, 56, 35, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 44, 56, 22, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 44, 56, 22, 56], [56, 56, 56, 56, 56, 56, 41, 43, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 45, 56, 56, 56, 34, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 46, 56, 56, 56, 27, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 34, 56, 31, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 27, 56, 15, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 46, 56, 56, 56, 27, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 42, 56, 35, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 44, 56, 22, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 22, 16], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 47, 56, 56, 56, 56, 56, 56, 56, 33, 56, 56, 56, 56, 56, 56, 56], [56, 48, 56, 39, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 49, 50, 56, 56, 41, 43, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 50, 56, 56, 56, 43, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 40, 56, 41, 56, 56, 56, 56, 56, 42, 56, 35, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 41, 43, 56, 56, 56, 56, 56, 56, 35, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 42, 56, 35, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 44, 56, 22, 56], [56, 56, 56, 56, 56, 56, 56, 43, 56, 56, 56, 56, 56, 56, 56, 32, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 44, 56, 22, 56], [56, 56, 56, 56, 56, 56, 56, 56, 51, 56, 56, 56, 42, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 44, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 44, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 53, 56, 56, 56, 56, 56, 56, 56, 46, 56, 56, 56, 56, 56, 56, 56], [56, 54, 56, 50, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 49, 50, 56, 56, 41, 43, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 50, 56, 56, 56, 43, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 51, 56, 56, 56, 42, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 44, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 44, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 55, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 56, 56, 56, 56], [56, 54, 56, 50, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56], [56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 55, 56, 56, 56, 56, 56, 56, 56, 52, 56, 56, 56, 56, 56, 56, 56]]
def rowL : List (List ℕ) := [[], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [1, 1, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [1, 1, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [1, 1, 1, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [1, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]]
def fcL : List (List Bool) := [[], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false]]
def fdL : List (List Bool) := [[], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, true, false, false, false], [false, false, true, false, false], [false, false, true, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, true, false], [false, false, false, true, false], [false, false, false, true, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, true, false], [false, false, false, false, true], [false, false, false, false, true], [false, false, false, false, true], [false, false, false, false, true], [false, false, false, false, false], [false, false, false, false, true], [false, false, false, false, true], [false, false, false, false, false], [false, true, true, false, false], [false, false, true, true, false], [false, false, true, true, false], [false, false, false, true, true], [false, false, false, true, true], [false, false, false, false, true], [false, false, false, true, true], [false, false, false, false, false], [false, false, false, false, true], [false, false, false, false, false], [false, false, false, false, false], [false, true, true, true, false], [false, false, true, true, true], [false, false, true, true, true], [false, false, false, false, true], [false, false, false, false, false], [false, false, false, false, false], [false, true, true, true, true], [false, false, false, false, false]]
def faL : List (List Bool) := [[], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [true, false, false, false, false], [false, false, false, false, false], [true, false, false, false, false], [true, false, false, false, false], [true, false, false, false, false], [false, true, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, true, false, false, false], [false, true, false, false, false], [true, false, false, false, false], [false, false, true, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, true, false, false], [false, true, false, false, false], [true, false, false, false, false], [false, false, false, true, false], [false, false, false, false, false], [true, false, false, false, false], [false, false, false, false, false], [true, true, false, false, false], [true, false, false, false, false], [true, true, false, false, false], [false, false, false, false, false], [true, true, false, false, false], [false, true, true, false, false], [false, true, true, false, false], [false, false, true, true, false], [false, false, false, false, false], [true, false, false, false, false], [false, false, false, false, false], [true, true, true, false, false], [true, true, true, false, false], [false, true, true, true, false], [false, false, false, false, false], [true, true, true, true, false]]

set_option maxRecDepth 400000 in
theorem table_ok : TableOK false true true 5 2 56 dl rowL fcL fdL faL := by decide +kernel

theorem pred_iff (n : ℕ) (x : Fin n → Fin 5 → Fin 2) :
    (RowsUnimodal x ∧ ColumnsNondecreasing x ∧ DiagonalsUnimodal x ∧ AntidiagonalsUnimodal x) ↔ P false true true n 5 (Xw 5 2 (fun i => finFunctionFinEquiv (x i))) := by
  have hX := arr_val x
  unfold RowsUnimodal ColumnsNondecreasing DiagonalsUnimodal AntidiagonalsUnimodal
  rw [rows_fin x _ hX, colnd_fin x _ hX, diag_fin x _ hX, anti_fin x _ hX]
  unfold P
  rw [if_neg (by decide)]
  exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, fun _ => h2, fun _ => h3⟩, fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, h2 rfl, h3 rfl⟩⟩

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = TMLib.cnt (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) n 0 := by
  unfold a
  rw [count_arrays _ (pred_iff n), count_words false true true 5 2 56 dl rowL fcL fdL faL table_ok n hn]

theorem cl : ∀ q < 57, ∀ a : Fin (2 ^ 5), δA 5 2 56 dl q a < 57 := by
  have h : ∀ q, q < 57 → ∀ c, c < 2 ^ 5 → δt 56 dl q c < 57 := by decide +kernel
  intro q hq a
  exact h q hq a.val a.isLt

def cc (i : ℕ) : ℤ := ([-1, 6, -15, 20, -15, 6] : List ℤ).getD i 0

set_option maxRecDepth 400000 in
theorem vrel : ∀ q, q < 57 → ((TMLib.cntV (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 (3 + 6)).getD q 0 : ℤ) =
    ∑ i ∈ range 6, cc i * ((TMLib.cntV (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 (3 + i)).getD q 0 : ℤ) := by
  decide +kernel

theorem xrec (n : ℕ) : (TMLib.cnt (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) (n + 3 + 6) 0 : ℤ) =
    ∑ i ∈ range 6, cc i * (TMLib.cnt (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) (n + 3 + i) 0 : ℤ) := by
  have hS : ∀ q ∈ range 57, ∀ a : Fin (2 ^ 5), δA 5 2 56 dl q a ∈ range 57 :=
    fun q hq a => mem_range.2 (cl q (mem_range.1 hq) a)
  exact TMLib.cnt_rec (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) (range 57) hS 6 cc 3 (fun q hq => by
    have hq' := mem_range.1 hq
    have h := vrel q hq'
    rw [TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl (3 + 6) q hq'] at h
    rw [h]
    apply sum_congr rfl
    intro i _
    rw [TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl (3 + i) q hq']) n 0 (mem_range.2 (by norm_num))

def Pz (t : ℤ) : ℤ := 4 * t ^ 5 + 5 * t ^ 4 + 95 * t ^ 3 + 280 * t ^ 2 + 756 * t - 1080

theorem hP (t : ℤ) : Pz (t + 6) = ∑ i ∈ range 6, cc i * Pz (t + i) := by
  simp only [Pz, cc, sum_range_succ, sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

set_option maxRecDepth 400000 in
theorem hv : ∀ m, m < 3 + 3 + 6 → 3 ≤ m →
    30 * ((TMLib.cntV (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 m).getD 0 0 : ℤ) = Pz m := by
  decide +kernel

theorem cast_count (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = 2/15 * (n : ℚ) ^ 5 + 1/6 * (n : ℚ) ^ 4 + 19/6 * (n : ℚ) ^ 3 + 28/3 * (n : ℚ) ^ 2 + 126/5 * (n : ℚ) - 36 := by
  have h := TMLib.rec_poly (fun m => (TMLib.cnt (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) m 0 : ℤ)) 6 3 3 cc Pz 30
    xrec hP (fun m h1 h2 => by
      have := hv m h2 h1
      rwa [TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl m 0 (by norm_num)] at this) n hn
  rw [← a_eq n (by omega)] at h
  have h' : ((30 : ℤ) : ℚ) * (a n : ℚ) = ((Pz n : ℤ) : ℚ) := by exact_mod_cast h
  simp only [Pz] at h'
  push_cast at h'
  linarith

theorem recurrence (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  have key : (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
    rw [cast_count n (by omega), cast_count (n - 1) (by omega), cast_count (n - 2) (by omega), cast_count (n - 3) (by omega), cast_count (n - 4) (by omega), cast_count (n - 5) (by omega), cast_count (n - 6) (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega)]
    ring
  exact_mod_cast key

def pQ (t : ℚ) : ℚ := 2/15 * t ^ 5 + 1/6 * t ^ 4 + 19/6 * t ^ 3 + 28/3 * t ^ 2 + 126/5 * t - 36

theorem fd (t : ℚ) : pQ t - 6 * pQ (t - 1) + 15 * pQ (t - 2) - 20 * pQ (t - 3) + 15 * pQ (t - 4) - 6 * pQ (t - 5) + pQ (t - 6) = 0 := by
  unfold pQ
  ring

theorem v1 : a 1 = 16 := by
  rw [a_eq 1 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 1 0 (by norm_num)]
  decide +kernel
theorem v2 : a 2 = 86 := by
  rw [a_eq 2 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 2 0 (by norm_num)]
  decide +kernel
theorem v3 : a 3 = 255 := by
  rw [a_eq 3 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 3 0 (by norm_num)]
  decide +kernel
theorem v4 : a 4 = 596 := by
  rw [a_eq 4 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 4 0 (by norm_num)]
  decide +kernel
theorem v5 : a 5 = 1240 := by
  rw [a_eq 5 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 5 0 (by norm_num)]
  decide +kernel
theorem v6 : a 6 = 2388 := by
  rw [a_eq 6 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 6 0 (by norm_num)]
  decide +kernel
theorem v7 : a 7 = 4325 := by
  rw [a_eq 7 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 7 0 (by norm_num)]
  decide +kernel
theorem v8 : a 8 = 7436 := by
  rw [a_eq 8 (by norm_num), ← TMLib.cntV_eq (δA 5 2 56 dl) (fun q => decide (q ≠ 56)) 57 cl 8 0 (by norm_num)]
  decide +kernel

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
    X * (16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7) := by
  set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hf
  have hfd : ∀ m, 3 ≤ m → f m = pQ m := by
    intro m hm
    rw [hf]
    simp only
    rw [if_neg (by omega), cast_count m hm]
    rfl
  let A : PowerSeries ℚ := PowerSeries.mk f
  have hleft : A * (1 - X) ^ 6 = A - A * X ^ 1 * C 6 + A * X ^ 2 * C 15 - A * X ^ 3 * C 20 + A * X ^ 4 * C 15 - A * X ^ 5 * C 6 + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hright : (X : PowerSeries ℚ) * (16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7) = C 16 * X ^ 1 - C 10 * X ^ 2 - C 21 * X ^ 3 + C 36 * X ^ 4 + C 9 * X ^ 5 - C 18 * X ^ 6 + C 2 * X ^ 7 + C 2 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  change A * (1 - X) ^ 6 = _
  rw [hleft, hright]
  apply PowerSeries.ext
  intro d
  simp only [map_add, map_sub, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_C_mul, coeff_C,
    coeff_X_pow, A, coeff_mk]
  by_cases hd : d < 9
  · interval_cases d <;> simp [hf, v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · simp (disch := omega) only [if_pos, if_neg]
    rw [hfd d (by omega), hfd (d - 1) (by omega), hfd (d - 2) (by omega), hfd (d - 3) (by omega), hfd (d - 4) (by omega), hfd (d - 5) (by omega), hfd (d - 6) (by omega)]
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    linear_combination fd (d : ℚ)

theorem main_proof :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 2/15 * (n : ℚ) ^ 5 + 1/6 * (n : ℚ) ^ 4 + 19/6 * (n : ℚ) ^ 3 + 28/3 * (n : ℚ) ^ 2 + 126/5 * (n : ℚ) - 36) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) :=
  ⟨fun n hn => cast_count n (by omega), gf, recurrence⟩

end OMAOurA223835

/-!
Bridge to the merged statement (statements/oeis-a223835.lean): it counts arrays given as LISTS of rows, with
unimodality defined by `take`/`drop`, and diagonals produced by `diagFrom`/`adiagFrom`. We show it counts exactly
the arrays counted by `OMAOurA223835.a` (functions `Fin n → Fin 5 → Fin 2`, "no valley" conditions).
-/

namespace OMABridgeA223835

open OMA.S_oeis_a223835 (Unimodal adiagFrom diagFrom IsSolution)

/-- No valley: no `i < j < k` with `s[j] < s[i]` and `s[j] < s[k]`. -/
def NoValley (s : List ℕ) : Prop :=
  ∀ i j k (hk : k < s.length) (hij : i < j) (hjk : j < k),
    ¬ (s[j]'(by omega) < s[i]'(by omega) ∧ s[j]'(by omega) < s[k])

theorem unimodal_iff (s : List ℕ) : Unimodal s ↔ NoValley s := by
  constructor
  · rintro ⟨m, h1, h2⟩ i j k hk hij hjk ⟨hji, hjk'⟩
    by_cases hjm : j < m
    · have hle := List.pairwise_iff_getElem.mp h1 i j (by simp; omega) (by simp; omega) hij
      simp only [List.getElem_take] at hle
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, j = m + t := ⟨j - m, by omega⟩
      obtain ⟨u, rfl⟩ : ∃ u, k = m + u := ⟨k - m, by omega⟩
      have hge := List.pairwise_iff_getElem.mp h2 t u (by simp; omega) (by simp; omega) (by omega)
      simp only [List.getElem_drop] at hge
      omega
  · intro hnv
    rcases Nat.eq_zero_or_pos s.length with h0 | hpos
    · refine ⟨0, ?_, ?_⟩ <;> simp [List.length_eq_zero_iff.mp h0]
    · haveI : Nonempty (Fin s.length) := ⟨⟨0, hpos⟩⟩
      obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i : Fin s.length => s[i])
        Finset.univ_nonempty
      have hmax : ∀ i (hi : i < s.length), s[i] ≤ s[p] := fun i hi => hp ⟨i, hi⟩ (Finset.mem_univ _)
      refine ⟨p, ?_, ?_⟩
      · rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_take] at hi hj
        simp only [List.getElem_take]
        by_contra hlt
        have h3 := hmax i (by omega)
        exact hnv i j p p.2 hij (by omega) ⟨by omega, by omega⟩
      · rw [List.pairwise_iff_getElem]
        intro t u ht hu htu
        simp only [List.length_drop] at ht hu
        simp only [List.getElem_drop]
        by_contra hlt
        have h3 := hmax (p + t) (by omega)
        have h4 := hmax (p + u) (by omega)
        rcases Nat.eq_zero_or_pos t with rfl | htpos
        · simp only [Nat.add_zero] at hlt h3
          omega
        · exact hnv p (p + t) (p + u) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩

/-- Cell `(i, j)` of a list of rows, as a natural number (`0` outside). -/
def cell (L : List (Fin 5 → Fin 2)) (i j : ℕ) : ℕ :=
  if h : i < L.length then (if h' : j < 5 then ((L[i]'h) ⟨j, h'⟩ : ℕ) else 0) else 0

theorem cell_cons_zero (r : Fin 5 → Fin 2) (l : List (Fin 5 → Fin 2)) (j : ℕ) (h : j < 5) :
    cell (r :: l) 0 j = (r ⟨j, h⟩ : ℕ) := by
  simp [cell, h]

theorem cell_cons_succ (r : Fin 5 → Fin 2) (l : List (Fin 5 → Fin 2)) (t j : ℕ) :
    cell (r :: l) (t + 1) j = cell l t j := by
  simp [cell]

theorem cell_drop (L : List (Fin 5 → Fin 2)) (i t j : ℕ) : cell (L.drop i) t j = cell L (i + t) j := by
  unfold cell
  by_cases h : i + t < L.length
  · have h' : t < (L.drop i).length := by simp; omega
    rw [dif_pos h', dif_pos h]
    simp [List.getElem_drop]
  · have h' : ¬ t < (L.drop i).length := by simp; omega
    rw [dif_neg h', dif_neg h]

theorem diag_len : ∀ (L : List (Fin 5 → Fin 2)) (j : ℕ), (diagFrom L j).length = min L.length (5 - j)
  | [], j => by simp [diagFrom]
  | r :: l, j => by
    unfold diagFrom
    split_ifs with h
    · simp only [List.length_cons, diag_len l (j + 1)]; omega
    · simp only [List.length_nil, List.length_cons]; omega

theorem diag_get : ∀ (L : List (Fin 5 → Fin 2)) (j t : ℕ) (ht : t < (diagFrom L j).length),
    (diagFrom L j)[t] = cell L t (j + t)
  | [], j, t, ht => by simp [diagFrom] at ht
  | r :: l, j, t, ht => by
    unfold diagFrom at ht ⊢
    split_ifs at ht ⊢ with h
    · cases t with
      | zero => simp [cell_cons_zero r l j h]
      | succ t =>
        simp only [List.getElem_cons_succ, cell_cons_succ]
        rw [diag_get l (j + 1) t (by simp at ht; omega)]
        congr 1; omega
    · simp at ht

theorem adiag_len : ∀ (L : List (Fin 5 → Fin 2)) (j : ℕ),
    (adiagFrom L j).length = if j < 5 then min L.length (j + 1) else 0
  | [], j => by simp [adiagFrom]
  | r :: l, j => by
    unfold adiagFrom
    split_ifs with h h0
    · subst h0; simp only [List.length_cons, List.length_nil, if_pos (show (0 : ℕ) < 5 by norm_num)]; omega
    · simp only [List.length_cons, adiag_len l (j - 1), if_pos (show j - 1 < 5 by omega), if_pos h]; omega
    · simp only [List.length_nil, if_neg h]

theorem adiag_get : ∀ (L : List (Fin 5 → Fin 2)) (j t : ℕ) (ht : t < (adiagFrom L j).length),
    (adiagFrom L j)[t] = cell L t (j - t)
  | [], j, t, ht => by simp [adiagFrom] at ht
  | r :: l, j, t, ht => by
    unfold adiagFrom at ht ⊢
    split_ifs at ht ⊢ with h h0
    · cases t with
      | zero => simp [cell_cons_zero r l j h]
      | succ t => simp at ht
    · cases t with
      | zero => simp [cell_cons_zero r l j h]
      | succ t =>
        simp only [List.getElem_cons_succ, cell_cons_succ]
        rw [adiag_get l (j - 1) t (by simp at ht; omega)]
        congr 1; omega
    · simp at ht

/-- Cells of `List.ofFn x`. -/
theorem cell_ofFn {n : ℕ} (x : Fin n → Fin 5 → Fin 2) (i j : ℕ) (hi : i < n) (hj : j < 5) :
    cell (List.ofFn x) i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  simp [cell, hi, hj]

theorem novalley_iff (s : List ℕ) (f : ℕ → ℕ) (hf : ∀ t (ht : t < s.length), s[t] = f t) :
    NoValley s ↔ ∀ t1 t2 t3, t1 < t2 → t2 < t3 → t3 < s.length → ¬ (f t2 < f t1 ∧ f t2 < f t3) := by
  unfold NoValley
  constructor
  · intro h t1 t2 t3 h12 h23 h3
    have := h t1 t2 t3 h3 h12 h23
    rwa [hf, hf, hf] at this
  · intro h i j k hk hij hjk
    rw [hf, hf, hf]
    exact h i j k hij hjk hk

section arr
variable {n : ℕ} (x : Fin n → Fin 5 → Fin 2)

/-- The array as a function on `ℕ × ℕ` (`0` outside). -/
def C (i j : ℕ) : ℕ := cell (List.ofFn x) i j

theorem C_eq (i j : ℕ) (hi : i < n) (hj : j < 5) : C x i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) :=
  cell_ofFn x i j hi hj

theorem rows_iff :
    (∀ r ∈ List.ofFn x, Unimodal (List.ofFn fun j => (r j : ℕ))) ↔ OMAOurA223835.RowsUnimodal x := by
  rw [List.forall_mem_ofFn_iff]
  unfold OMAOurA223835.RowsUnimodal
  apply forall_congr'
  intro i
  rw [unimodal_iff, novalley_iff _ (fun t => if h : t < 5 then (x i ⟨t, h⟩ : ℕ) else 0)
    (fun t ht => by simp at ht; simp [ht])]
  simp only [List.length_ofFn]
  constructor
  · intro h j1 j2 j3 h12 h23 hv
    have := h j1 j2 j3 h12 h23 j3.2
    simp only [j1.2, j2.2, j3.2, dif_pos] at this
    exact this ⟨Fin.lt_def.mp hv.1, Fin.lt_def.mp hv.2⟩
  · intro h t1 t2 t3 h12 h23 h3 hv
    simp only [show t1 < 5 by omega, show t2 < 5 by omega, h3, dif_pos] at hv
    exact h ⟨t1, by omega⟩ ⟨t2, by omega⟩ ⟨t3, h3⟩ (Fin.mk_lt_mk.mpr h12) (Fin.mk_lt_mk.mpr h23)
      ⟨Fin.lt_def.mpr hv.1, Fin.lt_def.mpr hv.2⟩

theorem cols_iff :
    (List.ofFn x).IsChain (fun r s => ∀ j : Fin 5, r j ≤ s j) ↔ OMAOurA223835.ColumnsNondecreasing x := by
  haveI : IsTrans (Fin 5 → Fin 2) (fun r s => ∀ j : Fin 5, r j ≤ s j) :=
    ⟨fun _ _ _ h1 h2 j => le_trans (h1 j) (h2 j)⟩
  rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
  unfold OMAOurA223835.ColumnsNondecreasing
  constructor
  · intro h i1 i2 j hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact h i1 i2 hlt j
    · exact le_refl _
  · intro h i1 i2 hlt j
    exact h i1 i2 j (le_of_lt hlt)

/-- Every diagonal, as a statement about cells. -/
def DiagNV : Prop :=
  ∀ i1 i2 i3 j1 j2 j3 : ℕ, i1 < i2 → i2 < i3 → i3 < n → j1 < 5 → j2 < 5 → j3 < 5 →
    j1 + i2 = j2 + i1 → j2 + i3 = j3 + i2 → ¬ (C x i2 j2 < C x i1 j1 ∧ C x i2 j2 < C x i3 j3)

def AntiNV : Prop :=
  ∀ i1 i2 i3 j1 j2 j3 : ℕ, i1 < i2 → i2 < i3 → i3 < n → j1 < 5 → j2 < 5 → j3 < 5 →
    i1 + j1 = i2 + j2 → i2 + j2 = i3 + j3 → ¬ (C x i2 j2 < C x i1 j1 ∧ C x i2 j2 < C x i3 j3)

theorem diag_ours : OMAOurA223835.DiagonalsUnimodal x ↔ DiagNV x := by
  unfold OMAOurA223835.DiagonalsUnimodal DiagNV
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2 hv
    rw [C_eq x i1 j1 (by omega) hj1, C_eq x i2 j2 (by omega) hj2, C_eq x i3 j3 h3 hj3] at hv
    exact h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.mpr h12) (Fin.mk_lt_mk.mpr h23) e1 e2 ⟨Fin.lt_def.mpr hv.1, Fin.lt_def.mpr hv.2⟩
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2 hv
    have := h i1 i2 i3 j1 j2 j3 h12 h23 i3.2 j1.2 j2.2 j3.2 e1 e2
    rw [C_eq x i1 j1 i1.2 j1.2, C_eq x i2 j2 i2.2 j2.2, C_eq x i3 j3 i3.2 j3.2] at this
    exact this ⟨Fin.lt_def.mp hv.1, Fin.lt_def.mp hv.2⟩

theorem anti_ours : OMAOurA223835.AntidiagonalsUnimodal x ↔ AntiNV x := by
  unfold OMAOurA223835.AntidiagonalsUnimodal AntiNV
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2 hv
    rw [C_eq x i1 j1 (by omega) hj1, C_eq x i2 j2 (by omega) hj2, C_eq x i3 j3 h3 hj3] at hv
    exact h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.mpr h12) (Fin.mk_lt_mk.mpr h23) e1 e2 ⟨Fin.lt_def.mpr hv.1, Fin.lt_def.mpr hv.2⟩
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2 hv
    have := h i1 i2 i3 j1 j2 j3 h12 h23 i3.2 j1.2 j2.2 j3.2 e1 e2
    rw [C_eq x i1 j1 i1.2 j1.2, C_eq x i2 j2 i2.2 j2.2, C_eq x i3 j3 i3.2 j3.2] at this
    exact this ⟨Fin.lt_def.mp hv.1, Fin.lt_def.mp hv.2⟩

/-- The diagonal starting at row `i0`, column `j0`, has no valley. -/
theorem diagFrom_nv (i0 j0 : ℕ) :
    Unimodal (diagFrom ((List.ofFn x).drop i0) j0) ↔
      ∀ t1 t2 t3, t1 < t2 → t2 < t3 → i0 + t3 < n → j0 + t3 < 5 →
        ¬ (C x (i0 + t2) (j0 + t2) < C x (i0 + t1) (j0 + t1) ∧ C x (i0 + t2) (j0 + t2) < C x (i0 + t3) (j0 + t3)) := by
  rw [unimodal_iff, novalley_iff _ (fun t => C x (i0 + t) (j0 + t))
    (fun t ht => by rw [diag_get]; unfold C; rw [cell_drop])]
  rw [diag_len]
  simp only [List.length_drop, List.length_ofFn]
  constructor
  · intro h t1 t2 t3 h12 h23 h3 h3' ; exact h t1 t2 t3 h12 h23 (by omega)
  · intro h t1 t2 t3 h12 h23 h3; exact h t1 t2 t3 h12 h23 (by omega) (by omega)

theorem adiagFrom_nv (i0 j0 : ℕ) (hj0 : j0 < 5) :
    Unimodal (adiagFrom ((List.ofFn x).drop i0) j0) ↔
      ∀ t1 t2 t3, t1 < t2 → t2 < t3 → i0 + t3 < n → t3 ≤ j0 →
        ¬ (C x (i0 + t2) (j0 - t2) < C x (i0 + t1) (j0 - t1) ∧ C x (i0 + t2) (j0 - t2) < C x (i0 + t3) (j0 - t3)) := by
  rw [unimodal_iff, novalley_iff _ (fun t => C x (i0 + t) (j0 - t))
    (fun t ht => by rw [adiag_get]; unfold C; rw [cell_drop])]
  rw [adiag_len, if_pos hj0]
  simp only [List.length_drop, List.length_ofFn]
  constructor
  · intro h t1 t2 t3 h12 h23 h3 h3'; exact h t1 t2 t3 h12 h23 (by omega)
  · intro h t1 t2 t3 h12 h23 h3; exact h t1 t2 t3 h12 h23 (by omega) (by omega)

theorem diag_iff :
    ((∀ j < 5, Unimodal (diagFrom (List.ofFn x) j)) ∧ (∀ i, Unimodal (diagFrom ((List.ofFn x).drop i) 0)))
      ↔ OMAOurA223835.DiagonalsUnimodal x := by
  rw [diag_ours]
  have top : ∀ j, Unimodal (diagFrom (List.ofFn x) j) ↔ Unimodal (diagFrom ((List.ofFn x).drop 0) j) := by
    intro j; rw [List.drop_zero]
  simp only [top, diagFrom_nv]
  unfold DiagNV
  constructor
  · rintro ⟨hT, hL⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    by_cases hc : i1 ≤ j1
    · -- start on the top row, at column j1 - i1
      have := hT (j1 - i1) (by omega) i1 i2 i3 h12 h23 (by omega) (by omega)
      simp only [Nat.zero_add] at this
      rwa [show j1 - i1 + i1 = j1 by omega, show j1 - i1 + i2 = j2 by omega,
        show j1 - i1 + i3 = j3 by omega] at this
    · -- start on the left column, at row i1 - j1
      have := hL (i1 - j1) j1 j2 j3 (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.zero_add] at this
      rwa [show i1 - j1 + j1 = i1 by omega, show i1 - j1 + j2 = i2 by omega,
        show i1 - j1 + j3 = i3 by omega] at this
  · intro h
    refine ⟨fun j _ t1 t2 t3 h12 h23 h3 h3' => ?_, fun i t1 t2 t3 h12 h23 h3 h3' => ?_⟩
    · simp only [Nat.zero_add]
      exact h t1 t2 t3 (j + t1) (j + t2) (j + t3) h12 h23 (by omega) (by omega) (by omega) h3'
        (by omega) (by omega)
    · simp only [Nat.zero_add]
      exact h (i + t1) (i + t2) (i + t3) t1 t2 t3 (by omega) (by omega) h3 (by omega) (by omega) (by omega)
        (by omega) (by omega)

theorem anti_iff :
    ((∀ j < 5, Unimodal (adiagFrom (List.ofFn x) j)) ∧ (∀ i, Unimodal (adiagFrom ((List.ofFn x).drop i) 4)))
      ↔ OMAOurA223835.AntidiagonalsUnimodal x := by
  rw [anti_ours]
  have top : ∀ j, Unimodal (adiagFrom (List.ofFn x) j) ↔ Unimodal (adiagFrom ((List.ofFn x).drop 0) j) := by
    intro j; rw [List.drop_zero]
  unfold AntiNV
  constructor
  · rintro ⟨hT, hR⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    by_cases hc : i1 + j1 ≤ 4
    · -- start on the top row, at column i1 + j1
      have := (adiagFrom_nv x 0 (i1 + j1) (by omega)).mp ((top _).mp (hT (i1 + j1) (by omega)))
        i1 i2 i3 h12 h23 (by omega) (by omega)
      simp only [Nat.zero_add] at this
      rwa [show i1 + j1 - i1 = j1 by omega, show i1 + j1 - i2 = j2 by omega,
        show i1 + j1 - i3 = j3 by omega] at this
    · -- start on the right column, at row i1 + j1 - 4
      have := (adiagFrom_nv x (i1 + j1 - 4) 4 (by omega)).mp (hR (i1 + j1 - 4))
        (i1 - (i1 + j1 - 4)) (i2 - (i1 + j1 - 4)) (i3 - (i1 + j1 - 4)) (by omega) (by omega) (by omega) (by omega)
      rwa [show i1 + j1 - 4 + (i1 - (i1 + j1 - 4)) = i1 by omega,
        show i1 + j1 - 4 + (i2 - (i1 + j1 - 4)) = i2 by omega,
        show i1 + j1 - 4 + (i3 - (i1 + j1 - 4)) = i3 by omega,
        show 4 - (i1 - (i1 + j1 - 4)) = j1 by omega, show 4 - (i2 - (i1 + j1 - 4)) = j2 by omega,
        show 4 - (i3 - (i1 + j1 - 4)) = j3 by omega] at this
  · intro h
    refine ⟨fun j hj => (top j).mpr ((adiagFrom_nv x 0 j hj).mpr ?_),
      fun i => (adiagFrom_nv x i 4 (by norm_num)).mpr ?_⟩
    · intro t1 t2 t3 h12 h23 h3 h3'
      simp only [Nat.zero_add]
      exact h t1 t2 t3 (j - t1) (j - t2) (j - t3) h12 h23 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    · intro t1 t2 t3 h12 h23 h3 h3'
      exact h (i + t1) (i + t2) (i + t3) (4 - t1) (4 - t2) (4 - t3) (by omega) (by omega) h3
        (by omega) (by omega) (by omega) (by omega) (by omega)

theorem sol_iff : IsSolution (List.ofFn x) ↔
    (OMAOurA223835.RowsUnimodal x ∧ OMAOurA223835.ColumnsNondecreasing x ∧
      OMAOurA223835.DiagonalsUnimodal x ∧ OMAOurA223835.AntidiagonalsUnimodal x) := by
  unfold IsSolution
  rw [rows_iff, cols_iff, ← diag_iff, ← anti_iff]
  tauto

end arr

/-- Lists of `n` rows are functions `Fin n → row`. -/
def e (n : ℕ) : {l : List (Fin 5 → Fin 2) // l.length = n ∧ IsSolution l} ≃
    {x : Fin n → Fin 5 → Fin 2 // IsSolution (List.ofFn x)} where
  toFun l := ⟨fun i => l.1[i.1]'(by rw [l.2.1]; exact i.2), by
    have h : List.ofFn (fun i : Fin n => l.1[i.1]'(by rw [l.2.1]; exact i.2)) = l.1 := by
      apply List.ext_getElem <;> simp [l.2.1]
    rw [h]; exact l.2.2⟩
  invFun x := ⟨List.ofFn x.1, by simp, x.2⟩
  left_inv l := by
    apply Subtype.ext
    apply List.ext_getElem <;> simp [l.2.1]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

theorem a_eq (n : ℕ) : OMA.S_oeis_a223835.a n = OMAOurA223835.a n := by
  unfold OMA.S_oeis_a223835.a OMAOurA223835.a
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ((e n).trans (Equiv.subtypeEquivRight (fun x => sol_iff x)))

end OMABridgeA223835

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a223835.main := by
  obtain ⟨-, hgf, hrec⟩ := OMAOurA223835.main_proof
  have hA : ∀ n, OMA.S_oeis_a223835.a n = OMAOurA223835.a n := OMABridgeA223835.a_eq
  refine ⟨?_, ?_⟩
  · simp only [hA]
    have hmk : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMAOurA223835.a n : ℚ)) =
        X * PowerSeries.mk (fun n => (OMAOurA223835.a (n + 1) : ℚ)) := by
      ext d
      cases d with
      | zero => simp
      | succ d => simp [coeff_succ_X_mul]
    rw [hmk, mul_assoc] at hgf
    exact mul_left_cancel₀ X_ne_zero hgf
  · intro n hn
    simp only [hA]
    have := hrec n hn
    linarith
