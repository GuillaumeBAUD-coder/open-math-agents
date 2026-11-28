import OMAStatements.S_oeis_a184073

/-!
# A184073: Barker's conjectures, by a transfer count over the rows

An array is read from the top row down. Prepending a row `q` to a valid array `B` keeps it valid
exactly when `q ≤ B 0` lexicographically, the 2 X 2 sums of rows `q, B 0` differ by at most one
horizontally, and they differ by at most one from those of rows `B 0, B 1` (`good_cons`, from
`rows_cons` and `smooth_cons`). Column `j` stays lexicographically below column `j + 1` exactly
when `q j < q (j + 1)`, or `q j = q (j + 1)` and it was so before (`colFlag_cons`, `upd`). So the
arrays with `m + 2` rows and a given state (first row, second row, column flags) are counted by a
linear recursion on the 162 states (`card_S_succ`).

The kernel checks the state vectors for `2, …, 16` rows against explicit tables (`base0`,
`vec_step`, `cardS`), and that they satisfy the identity of the operator `(1 - shift) ^ 9` from
7 rows on (`D5`); the recursion propagates it to every later vector (`D_succ`, `D_zero`).
Summing over the states with all column flags set gives `a` (`a_eq`), hence the recurrence
(`a_rec`, `rec_main`), the closed form (`formula`) and the generating function (`gf`).
-/

namespace A184073P
open OMA.S_oeis_a184073 Finset

abbrev Row := Fin 2 → Fin 3

theorem cons_le_iff {α : Type*} [LinearOrder α] (a b : α) (l l' : List α) :
    a :: l ≤ b :: l' ↔ a < b ∨ a = b ∧ l ≤ l' := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  constructor
  · rintro (h | h)
    · change List.Lex (· < ·) _ _ at h
      cases h with
      | cons h => exact Or.inr ⟨rfl, Or.inl h⟩
      | rel h => exact Or.inl h
    · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 h
      exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact Or.inl (List.Lex.rel h)
    · exact Or.inl (List.Lex.cons h)
    · exact Or.inr rfl

/-- Whether column `j` is lexicographically at most column `j + 1`. -/
def colFlag {m : ℕ} (B : Fin m → Row) (j : Fin 1) : Bool :=
  decide (List.ofFn (fun i => B i j.castSucc) ≤ List.ofFn (fun i => B i j.succ))

def upd (q : Row) (P : Fin 1 → Bool) (j : Fin 1) : Bool :=
  decide (q j.castSucc < q j.succ) || (decide (q j.castSucc = q j.succ) && P j)

theorem colFlag_cons {m : ℕ} (q : Row) (B : Fin m → Row) :
    colFlag (Fin.cons q B : Fin (m + 1) → Row) = upd q (colFlag B) := by
  funext j
  simp only [colFlag, upd, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Bool.eq_iff_iff]
  simp [cons_le_iff]

theorem cols_iff {n : ℕ} (A : Fin (n + 1) → Row) :
    ColsNondecreasing A ↔ ∀ j, colFlag A j = true := by
  simp [ColsNondecreasing, colFlag, col]

theorem rows_cons {m : ℕ} (q : Row) (B : Fin (m + 1) → Row) :
    RowsNondecreasing (Fin.cons q B : Fin (m + 2) → Row) ↔
      List.ofFn q ≤ List.ofFn (B 0) ∧ RowsNondecreasing B := by
  unfold RowsNondecreasing row
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_one]
  refine and_congr_right' (forall_congr' fun i => ?_)
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

def bs (r s : Row) (j : Fin 1) : ℕ :=
  (r j.castSucc).val + (r j.succ).val + (s j.castSucc).val + (s j.succ).val

def hs (r s : Row) : Prop :=
  ∀ j j' : Fin 1, j.val + 1 = j'.val → bs r s j ≤ bs r s j' + 1 ∧ bs r s j' ≤ bs r s j + 1

def vs (q r s : Row) : Prop :=
  ∀ j : Fin 1, bs q r j ≤ bs r s j + 1 ∧ bs r s j ≤ bs q r j + 1

theorem sb_zero {m : ℕ} (q : Row) (B : Fin (m + 1) → Row) (j : Fin 1) :
    subblockSum (Fin.cons q B : Fin (m + 2) → Row) 0 j = bs q (B 0) j := by
  simp [subblockSum, bs, Fin.cons_one]

theorem sb_succ {m : ℕ} (q : Row) (B : Fin (m + 1) → Row) (i : Fin m) (j : Fin 1) :
    subblockSum (Fin.cons q B : Fin (m + 2) → Row) i.succ j = subblockSum B i j := by
  simp only [subblockSum]
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

theorem sb_first {m : ℕ} (B : Fin (m + 2) → Row) (j : Fin 1) :
    subblockSum B 0 j = bs (B 0) (B 1) j := by
  simp [subblockSum, bs]

theorem smooth_cons {m : ℕ} (q : Row) (B : Fin (m + 2) → Row) :
    SmoothSubblocks (Fin.cons q B : Fin (m + 3) → Row) ↔
      hs q (B 0) ∧ vs q (B 0) (B 1) ∧ SmoothSubblocks B := by
  constructor
  · intro h
    refine ⟨fun j j' hj => ?_, fun j => ?_, fun p p' hn => ?_⟩
    · have := h (0, j) (0, j') (Or.inl ⟨rfl, hj⟩)
      simpa only [sb_zero] using this
    · have := h (0, j) (1, j) (Or.inr ⟨by simp, rfl⟩)
      rw [sb_zero, show (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ from rfl, sb_succ,
        sb_first] at this
      exact this
    · have := h (p.1.succ, p.2) (p'.1.succ, p'.2) (by
        rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [h1], h2⟩
        · exact Or.inr ⟨by simp [Fin.val_succ, h1], h2⟩)
      simpa only [sb_succ] using this
  · rintro ⟨hh, hv, hB⟩ ⟨a, j⟩ ⟨b, j'⟩ hn
    simp only [Neighbors] at hn
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero =>
        rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
        · simpa only [sb_zero] using hh j j' h2
        · simp at h1
      | succ b =>
        rcases hn with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact absurd h1 (Fin.succ_ne_zero b).symm
        · have hb : b = 0 := by
            ext; simp [Fin.val_succ] at h1; omega
          subst hb; subst h2
          simp only
          rw [sb_zero, sb_succ, sb_first]
          exact hv j
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 (Fin.succ_ne_zero a)
        · simp at h1
      | succ b =>
        simp only
        rw [sb_succ, sb_succ]
        exact hB (a, j) (b, j') (by
          rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Fin.succ_injective _ h1, h2⟩
          · exact Or.inr ⟨by simp [Fin.val_succ] at h1; omega, h2⟩)

def Good {m : ℕ} (B : Fin (m + 1) → Row) : Prop := RowsNondecreasing B ∧ SmoothSubblocks B

instance {m : ℕ} : DecidablePred (@Good m) := fun B => by
  unfold Good RowsNondecreasing SmoothSubblocks Neighbors; infer_instance

abbrev St := Row × Row × (Fin 1 → Bool)

def key {m : ℕ} (B : Fin (m + 2) → Row) : St := (B 0, B 1, colFlag B)

def S (m : ℕ) (σ : St) : Finset (Fin (m + 2) → Row) := univ.filter (fun B => Good B ∧ key B = σ)

def tr (q r s : Row) : Prop := List.ofFn q ≤ List.ofFn r ∧ hs q r ∧ vs q r s

instance (q r s : Row) : Decidable (tr q r s) := by unfold tr hs vs; infer_instance

theorem good_cons {m : ℕ} (q : Row) (B : Fin (m + 2) → Row) :
    Good (Fin.cons q B : Fin (m + 3) → Row) ↔ tr q (B 0) (B 1) ∧ Good B := by
  unfold Good tr
  rw [rows_cons, smooth_cons]
  tauto

theorem card_cons {m : ℕ} (q : Row) (Q : (Fin (m + 3) → Row) → Prop) [DecidablePred Q] :
    (univ.filter (fun A : Fin (m + 3) → Row => Q A ∧ A 0 = q)).card =
      (univ.filter (fun B : Fin (m + 2) → Row => Q (Fin.cons q B))).card := by
  refine Finset.card_bij' (fun A _ => Fin.tail A) (fun B _ => Fin.cons q B) ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    rw [← hA.2, Fin.cons_self_tail]; exact hA.1
  · intro B hB
    simp only [mem_filter, mem_univ, true_and] at hB ⊢
    exact ⟨hB, Fin.cons_zero _ _⟩
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA
    rw [← hA.2, Fin.cons_self_tail]
  · intro B _
    exact Fin.tail_cons _ _

theorem card_filter_key (m : ℕ) (φ : St → Prop) [DecidablePred φ] :
    (univ.filter (fun B : Fin (m + 2) → Row => Good B ∧ φ (key B))).card =
      ∑ σ : St, if φ σ then (S m σ).card else 0 := by
  rw [card_eq_sum_card_fiberwise (f := key) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · congr 1
    ext B
    simp only [mem_filter, mem_univ, true_and, S]
    constructor
    · rintro ⟨⟨hg, _⟩, hk⟩; exact ⟨hg, hk⟩
    · rintro ⟨hg, hk⟩; exact ⟨⟨hg, hk ▸ h⟩, hk⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro B hB hk
    simp only [mem_filter, mem_univ, true_and] at hB
    exact h (hk ▸ hB.2)

theorem card_S_succ (m : ℕ) (q r : Row) (P' : Fin 1 → Bool) :
    (S (m + 1) (q, r, P')).card =
      ∑ s : Row, ∑ P : Fin 1 → Bool,
        if tr q r s ∧ upd q P = P' then (S m (r, s, P)).card else 0 := by
  have h1 : S (m + 1) (q, r, P') = univ.filter
      (fun A : Fin (m + 3) → Row => (Good A ∧ A 1 = r ∧ colFlag A = P') ∧ A 0 = q) := by
    ext A
    simp only [S, mem_filter, mem_univ, true_and, key, Prod.mk.injEq]
    tauto
  rw [h1, card_cons]
  simp only [good_cons, Fin.cons_one, colFlag_cons]
  have h2 : (univ.filter (fun B : Fin (m + 2) → Row =>
      (tr q (B 0) (B 1) ∧ Good B) ∧ B 0 = r ∧ upd q (colFlag B) = P')) =
      univ.filter (fun B : Fin (m + 2) → Row => Good B ∧
        (fun σ : St => σ.1 = r ∧ tr q σ.1 σ.2.1 ∧ upd q σ.2.2 = P') (key B)) := by
    apply filter_congr
    intro B _
    simp only [key]
    tauto
  rw [h2, card_filter_key m (fun σ : St => σ.1 = r ∧ tr q σ.1 σ.2.1 ∧ upd q σ.2.2 = P'),
    Fintype.sum_prod_type, sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ => sum_congr rfl fun P _ => ?_
    simp only [true_and]
  · intro r' _ hr
    refine sum_eq_zero fun x _ => ?_
    simp [hr]
  · intro h; exact absurd (mem_univ r) h

def code (r : Row) : ℕ := 3 * (r 0).val + (r 1).val

def fcode (P : Fin 1 → Bool) : ℕ := (P 0).toNat

def L0 : List (List (List ℕ)) :=
  [[[0, 1], [0, 1], [0, 1], [1, 0], [0, 1], [0, 1], [1, 0], [1, 0], [0, 1]],
   [[0, 0], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 1], [1, 0], [1, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 1], [0, 1], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L1 : List (List (List ℕ)) :=
  [[[1, 2], [0, 2], [0, 1], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 5], [0, 4], [0, 3], [0, 2], [0, 1], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 6], [0, 5], [0, 4], [0, 3], [0, 2], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [3, 0], [2, 0], [1, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [2, 2], [0, 3], [2, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 4], [0, 3], [0, 2], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [2, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [2, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L2 : List (List (List ℕ)) :=
  [[[2, 4], [0, 8], [0, 5], [3, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 15], [0, 17], [0, 6], [0, 6], [0, 3], [0, 2], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 21], [0, 7], [0, 10], [0, 9], [0, 3], [0, 2], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [6, 0], [6, 0], [3, 0], [2, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [5, 5], [0, 9], [3, 0], [2, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 10], [0, 3], [0, 3], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [3, 0], [2, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [3, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L3 : List (List (List ℕ)) :=
  [[[5, 12], [0, 21], [0, 7], [6, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 46], [0, 41], [0, 14], [0, 13], [0, 3], [0, 3], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 52], [0, 17], [0, 24], [0, 16], [0, 5], [0, 3], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [14, 0], [13, 0], [3, 0], [3, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [10, 14], [0, 16], [5, 0], [3, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 17], [0, 5], [0, 4], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [5, 0], [3, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [4, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L4 : List (List (List ℕ)) :=
  [[[11, 33], [0, 60], [0, 17], [14, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 117], [0, 98], [0, 30], [0, 29], [0, 5], [0, 5], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 117], [0, 33], [0, 48], [0, 26], [0, 8], [0, 4], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [30, 0], [29, 0], [5, 0], [5, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [18, 30], [0, 26], [8, 0], [4, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 27], [0, 8], [0, 5], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [8, 0], [4, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [5, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L5 : List (List (List ℕ)) :=
  [[[25, 93], [0, 147], [0, 33], [30, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 279], [0, 206], [0, 64], [0, 56], [0, 8], [0, 8], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 236], [0, 69], [0, 86], [0, 40], [0, 12], [0, 5], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [64, 0], [56, 0], [8, 0], [8, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [30, 56], [0, 40], [12, 0], [5, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 41], [0, 12], [0, 6], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [12, 0], [5, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [6, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L6 : List (List (List ℕ)) :=
  [[[55, 240], [0, 343], [0, 69], [64, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 613], [0, 403], [0, 128], [0, 98], [0, 12], [0, 12], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 448], [0, 136], [0, 143], [0, 59], [0, 17], [0, 6], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [128, 0], [98, 0], [12, 0], [12, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [47, 96], [0, 59], [17, 0], [6, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 60], [0, 17], [0, 7], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [17, 0], [6, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [7, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L7 : List (List (List ℕ)) :=
  [[[119, 583], [0, 741], [0, 136], [128, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1254], [0, 744], [0, 238], [0, 160], [0, 17], [0, 17], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 809], [0, 250], [0, 225], [0, 84], [0, 23], [0, 7], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [238, 0], [160, 0], [17, 0], [17, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [70, 155], [0, 84], [23, 0], [7, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 85], [0, 23], [0, 8], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [23, 0], [7, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [8, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L8 : List (List (List ℕ)) :=
  [[[247, 1324], [0, 1492], [0, 250], [238, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 2413], [0, 1307], [0, 415], [0, 248], [0, 23], [0, 23], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1398], [0, 432], [0, 339], [0, 116], [0, 30], [0, 8], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [415, 0], [248, 0], [23, 0], [23, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [100, 239], [0, 116], [30, 0], [8, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 117], [0, 30], [0, 9], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [30, 0], [8, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [9, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L9 : List (List (List ℕ)) :=
  [[[485, 2816], [0, 2828], [0, 432], [415, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 4406], [0, 2199], [0, 686], [0, 369], [0, 30], [0, 30], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 2323], [0, 709], [0, 493], [0, 156], [0, 38], [0, 9], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [686, 0], [369, 0], [30, 0], [30, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [138, 355], [0, 156], [38, 0], [9, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 157], [0, 38], [0, 10], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [38, 0], [9, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [10, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L10 : List (List (List ℕ)) :=
  [[[900, 5644], [0, 5092], [0, 709], [686, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 7690], [0, 3563], [0, 1085], [0, 531], [0, 38], [0, 38], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 3728], [0, 1115], [0, 696], [0, 205], [0, 47], [0, 10], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1085, 0], [531, 0], [38, 0], [38, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [185, 511], [0, 205], [47, 0], [10, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 206], [0, 47], [0, 11], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [47, 0], [10, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [11, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L11 : List (List (List ℕ)) :=
  [[[1586, 10736], [0, 8775], [0, 1115], [1085, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 12907], [0, 5586], [0, 1654], [0, 743], [0, 47], [0, 47], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 5801], [0, 1692], [0, 958], [0, 264], [0, 57], [0, 11], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1654, 0], [743, 0], [47, 0], [47, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [242, 716], [0, 264], [57, 0], [11, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 265], [0, 57], [0, 12], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [57, 0], [11, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [12, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L12 : List (List (List ℕ)) :=
  [[[2671, 19511], [0, 14561], [0, 1692], [1654, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 20937], [0, 8508], [0, 2444], [0, 1015], [0, 57], [0, 57], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 8783], [0, 2491], [0, 1290], [0, 334], [0, 68], [0, 12], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [2444, 0], [1015, 0], [57, 0], [57, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [310, 980], [0, 334], [68, 0], [12, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 335], [0, 68], [0, 13], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [68, 0], [12, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [13, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L13 : List (List (List ℕ)) :=
  [[[4325, 34072], [0, 23381], [0, 2491], [2444, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 32961], [0, 12632], [0, 3516], [0, 1358], [0, 68], [0, 68], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 12978], [0, 3573], [0, 1704], [0, 416], [0, 80], [0, 13], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [3516, 0], [1358, 0], [68, 0], [68, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [390, 1314], [0, 416], [80, 0], [13, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 417], [0, 80], [0, 14], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [80, 0], [13, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [14, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def L14 : List (List (List ℕ)) :=
  [[[6769, 57453], [0, 36477], [0, 3573], [3516, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 50535], [0, 18335], [0, 4942], [0, 1784], [0, 80], [0, 80], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 18764], [0, 5010], [0, 2213], [0, 511], [0, 93], [0, 14], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [4942, 0], [1784, 0], [80, 0], [80, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [483, 1730], [0, 511], [93, 0], [14, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 512], [0, 93], [0, 15], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [93, 0], [14, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [15, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]]]

def vec : ℕ → St → ℕ
  | 0 => fun σ => ((L0.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 1 => fun σ => ((L1.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 2 => fun σ => ((L2.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 3 => fun σ => ((L3.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 4 => fun σ => ((L4.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 5 => fun σ => ((L5.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 6 => fun σ => ((L6.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 7 => fun σ => ((L7.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 8 => fun σ => ((L8.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 9 => fun σ => ((L9.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 10 => fun σ => ((L10.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 11 => fun σ => ((L11.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 12 => fun σ => ((L12.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 13 => fun σ => ((L13.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | 14 => fun σ => ((L14.getD (code σ.1) []).getD (code σ.2.1) []).getD (fcode σ.2.2) 0
  | _ => fun _ => 0

theorem base0 : ∀ σ : St, (S 0 σ).card = vec 0 σ := by
  decide +kernel

theorem vec_step : ∀ k : ℕ, k < 14 → ∀ q r : Row, ∀ P' : Fin 1 → Bool,
    vec (k + 1) (q, r, P') = ∑ s : Row, ∑ P : Fin 1 → Bool,
      if tr q r s ∧ upd q P = P' then vec k (r, s, P) else 0 := by
  decide +kernel

theorem cardS : ∀ k : ℕ, k ≤ 14 → ∀ σ : St, (S k σ).card = vec k σ := by
  intro k
  induction k with
  | zero => intro _; exact base0
  | succ k ih =>
    intro hk ⟨q, r, P'⟩
    rw [card_S_succ, vec_step k (by omega)]
    refine sum_congr rfl fun s _ => sum_congr rfl fun P _ => ?_
    rw [ih (by omega)]

def D (m : ℕ) (σ : St) : ℤ :=
  ((S (m + 9) σ).card : ℤ) - 9 * (S (m + 8) σ).card + 36 * (S (m + 7) σ).card - 84 * (S (m + 6) σ).card + 126 * (S (m + 5) σ).card - 126 * (S (m + 4) σ).card + 84 * (S (m + 3) σ).card - 36 * (S (m + 2) σ).card + 9 * (S (m + 1) σ).card - (S m σ).card

theorem D_succ (m : ℕ) (q r : Row) (P' : Fin 1 → Bool) :
    D (m + 1) (q, r, P') = ∑ s : Row, ∑ P : Fin 1 → Bool,
      if tr q r s ∧ upd q P = P' then D m (r, s, P) else 0 := by
  have e : D (m + 1) (q, r, P') = ((S ((m + 9) + 1) (q, r, P')).card : ℤ) - 9 * (S ((m + 8) + 1) (q, r, P')).card + 36 * (S ((m + 7) + 1) (q, r, P')).card - 84 * (S ((m + 6) + 1) (q, r, P')).card + 126 * (S ((m + 5) + 1) (q, r, P')).card - 126 * (S ((m + 4) + 1) (q, r, P')).card + 84 * (S ((m + 3) + 1) (q, r, P')).card - 36 * (S ((m + 2) + 1) (q, r, P')).card + 9 * (S ((m + 1) + 1) (q, r, P')).card - (S (m + 1) (q, r, P')).card := rfl
  rw [e, card_S_succ (m + 9), card_S_succ (m + 8), card_S_succ (m + 7), card_S_succ (m + 6), card_S_succ (m + 5), card_S_succ (m + 4), card_S_succ (m + 3), card_S_succ (m + 2), card_S_succ (m + 1), card_S_succ m]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun s _ => sum_congr rfl fun P _ => ?_
  split_ifs <;> simp [D]

theorem D5 : ∀ σ : St, D 5 σ = 0 := by
  intro σ
  simp only [D]
  rw [cardS 14 (by norm_num), cardS 13 (by norm_num), cardS 12 (by norm_num), cardS 11 (by norm_num), cardS 10 (by norm_num), cardS 9 (by norm_num), cardS 8 (by norm_num), cardS 7 (by norm_num), cardS 6 (by norm_num), cardS 5 (by norm_num)]
  revert σ
  decide +kernel

theorem D_zero (m : ℕ) (hm : 5 ≤ m) : ∀ σ : St, D m σ = 0 := by
  induction m, hm using Nat.le_induction with
  | base => exact D5
  | succ m _ ih =>
    rintro ⟨q, r, P'⟩
    rw [D_succ]
    refine sum_eq_zero fun s _ => sum_eq_zero fun P _ => ?_
    rw [ih]; simp

def ψ (σ : St) : Prop := σ.2.2 = fun _ => true

instance : DecidablePred ψ := fun σ => by unfold ψ; infer_instance

theorem valid_iff {m : ℕ} (A : Fin (m + 2) → Row) : IsValid A ↔ Good A ∧ ψ (key A) := by
  unfold IsValid Good ψ key
  rw [cols_iff, funext_iff]
  tauto

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = ∑ σ : St, if ψ σ then ((S m σ).card : ℤ) else 0 := by
  have h : a (m + 1) = (univ.filter (fun B : Fin (m + 2) → Row => Good B ∧ ψ (key B))).card := by
    rw [a, Nat.card_congr (Equiv.subtypeEquivRight valid_iff), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [h, card_filter_key]
  push_cast
  rfl

theorem a1v : (a 1 : ℤ) = 29 := by
  rw [a_eq 0]
  simp only [cardS 0 (by norm_num)]
  decide +kernel

theorem a2v : (a 2 : ℤ) = 58 := by
  rw [a_eq 1]
  simp only [cardS 1 (by norm_num)]
  decide +kernel

theorem a3v : (a 3 : ℤ) = 150 := by
  rw [a_eq 2]
  simp only [cardS 2 (by norm_num)]
  decide +kernel

theorem a4v : (a 4 : ℤ) = 335 := by
  rw [a_eq 3]
  simp only [cardS 3 (by norm_num)]
  decide +kernel

theorem a5v : (a 5 : ℤ) = 728 := by
  rw [a_eq 4]
  simp only [cardS 4 (by norm_num)]
  decide +kernel

theorem a6v : (a 6 : ℤ) = 1499 := by
  rw [a_eq 5]
  simp only [cardS 5 (by norm_num)]
  decide +kernel

theorem a7v : (a 7 : ℤ) = 2968 := by
  rw [a_eq 6]
  simp only [cardS 6 (by norm_num)]
  decide +kernel

theorem a8v : (a 8 : ℤ) = 5645 := by
  rw [a_eq 7]
  simp only [cardS 7 (by norm_num)]
  decide +kernel

theorem a9v : (a 9 : ℤ) = 10331 := by
  rw [a_eq 8]
  simp only [cardS 8 (by norm_num)]
  decide +kernel

theorem a10v : (a 10 : ℤ) = 18242 := by
  rw [a_eq 9]
  simp only [cardS 9 (by norm_num)]
  decide +kernel

theorem a11v : (a 11 : ℤ) = 31173 := by
  rw [a_eq 10]
  simp only [cardS 10 (by norm_num)]
  decide +kernel

theorem a12v : (a 12 : ℤ) = 51709 := by
  rw [a_eq 11]
  simp only [cardS 11 (by norm_num)]
  decide +kernel

theorem a13v : (a 13 : ℤ) = 83492 := by
  rw [a_eq 12]
  simp only [cardS 12 (by norm_num)]
  decide +kernel

theorem a14v : (a 14 : ℤ) = 131554 := by
  rw [a_eq 13]
  simp only [cardS 13 (by norm_num)]
  decide +kernel

theorem a15v : (a 15 : ℤ) = 202727 := by
  rw [a_eq 14]
  simp only [cardS 14 (by norm_num)]
  decide +kernel

theorem a_rec (m : ℕ) (hm : 5 ≤ m) :
    (a (m + 10) : ℤ) = 9 * a (m + 9) - 36 * a (m + 8) + 84 * a (m + 7) - 126 * a (m + 6) + 126 * a (m + 5) - 84 * a (m + 4) + 36 * a (m + 3) - 9 * a (m + 2) + a (m + 1) := by
  have h := sum_eq_zero (s := (univ : Finset St)) (f := fun σ => if ψ σ then D m σ else 0)
    (fun σ _ => by simp [D_zero m hm σ])
  rw [show m + 10 = (m + 9) + 1 by ring, show m + 9 = (m + 8) + 1 by ring, show m + 8 = (m + 7) + 1 by ring, show m + 7 = (m + 6) + 1 by ring, show m + 6 = (m + 5) + 1 by ring, show m + 5 = (m + 4) + 1 by ring, show m + 4 = (m + 3) + 1 by ring, show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  have e : ∀ σ, (if ψ σ then D m σ else 0) = ((if ψ σ then ((S (m + 9) σ).card : ℤ) else 0) - 9 * (if ψ σ then ((S (m + 8) σ).card : ℤ) else 0) + 36 * (if ψ σ then ((S (m + 7) σ).card : ℤ) else 0) - 84 * (if ψ σ then ((S (m + 6) σ).card : ℤ) else 0) + 126 * (if ψ σ then ((S (m + 5) σ).card : ℤ) else 0) - 126 * (if ψ σ then ((S (m + 4) σ).card : ℤ) else 0) + 84 * (if ψ σ then ((S (m + 3) σ).card : ℤ) else 0) - 36 * (if ψ σ then ((S (m + 2) σ).card : ℤ) else 0) + 9 * (if ψ σ then ((S (m + 1) σ).card : ℤ) else 0) - (if ψ σ then ((S m σ).card : ℤ) else 0)) := by
    intro σ; split_ifs <;> simp [D]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  linarith

theorem rec_main (n : ℕ) (hn : 14 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [a_rec m (by omega)]
  simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega]

theorem formula (n : ℕ) (hn : 5 < n) :
    40320 * (a n : ℤ) = 1290240 - 1768560 * n + 1559788 * n ^ 2 -
      343756 * n ^ 3 + 72569 * n ^ 4 - 4480 * n ^ 5 + 602 * n ^ 6 - 4 * n ^ 7 + n ^ 8 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 15 with h | h
    · interval_cases n
      · rw [a6v]; norm_num
      · rw [a7v]; norm_num
      · rw [a8v]; norm_num
      · rw [a9v]; norm_num
      · rw [a10v]; norm_num
      · rw [a11v]; norm_num
      · rw [a12v]; norm_num
      · rw [a13v]; norm_num
      · rw [a14v]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have h1 := ih (k + 8) (by omega) (by omega)
      have h2 := ih (k + 7) (by omega) (by omega)
      have h3 := ih (k + 6) (by omega) (by omega)
      have h4 := ih (k + 5) (by omega) (by omega)
      have h5 := ih (k + 4) (by omega) (by omega)
      have h6 := ih (k + 3) (by omega) (by omega)
      have h7 := ih (k + 2) (by omega) (by omega)
      have h8 := ih (k + 1) (by omega) (by omega)
      have h9 := ih (k + 0) (by omega) (by omega)
      rw [rec_main (k + 9) (by omega)]
      simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show k + 9 - 9 = k + 0 by omega]
      push_cast at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
      linear_combination 9 * h1 - 36 * h2 + 84 * h3 - 126 * h4 + 126 * h5 - 84 * h6 + 36 * h7 - 9 * h8 + h9

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 9 =
    X * (29 - 203 * X + 672 * X ^ 2 - 1363 * X ^ 3 + 1895 * X ^ 4 - 1939 * X ^ 5 +
        1573 * X ^ 6 - 1117 * X ^ 7 + 749 * X ^ 8 - 450 * X ^ 9 + 209 * X ^ 10 - 65 * X ^ 11 +
        12 * X ^ 12 - X ^ 13) := by
  have e1 : ((1 - X) ^ 9 : PowerSeries ℤ) = 1 - C 9 * X ^ 1 + C 36 * X ^ 2 - C 84 * X ^ 3 + C 126 * X ^ 4 - C 126 * X ^ 5 + C 84 * X ^ 6 - C 36 * X ^ 7 + C 9 * X ^ 8 - X ^ 9 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (X * (29 - 203 * X + 672 * X ^ 2 - 1363 * X ^ 3 + 1895 * X ^ 4 - 1939 * X ^ 5 +
        1573 * X ^ 6 - 1117 * X ^ 7 + 749 * X ^ 8 - 450 * X ^ 9 + 209 * X ^ 10 - 65 * X ^ 11 +
        12 * X ^ 12 - X ^ 13) : PowerSeries ℤ) = C 29 * X ^ 1 - C 203 * X ^ 2 + C 672 * X ^ 3 - C 1363 * X ^ 4 + C 1895 * X ^ 5 - C 1939 * X ^ 6 + C 1573 * X ^ 7 - C 1117 * X ^ 8 + C 749 * X ^ 9 - C 450 * X ^ 10 + C 209 * X ^ 11 - C 65 * X ^ 12 + C 12 * X ^ 13 - X ^ 14 := by
    simp only [map_ofNat, pow_one]; ring
  rw [mul_comm, e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> simp [a1v, a2v, a3v, a4v, a5v, a6v, a7v, a8v, a9v, a10v, a11v, a12v, a13v, a14v]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 15 := ⟨k - 15, by omega⟩
    have hr := rec_main (j + 15) (by omega)
    simp only [show j + 15 - 1 = j + 14 by omega, show j + 15 - 2 = j + 13 by omega, show j + 15 - 3 = j + 12 by omega, show j + 15 - 4 = j + 11 by omega, show j + 15 - 5 = j + 10 by omega, show j + 15 - 6 = j + 9 by omega, show j + 15 - 7 = j + 8 by omega, show j + 15 - 8 = j + 7 by omega, show j + 15 - 9 = j + 6 by omega] at hr
    simp only [show 1 ≤ j + 15 by omega, show 2 ≤ j + 15 by omega, show 3 ≤ j + 15 by omega, show 4 ≤ j + 15 by omega, show 5 ≤ j + 15 by omega, show 6 ≤ j + 15 by omega, show 7 ≤ j + 15 by omega, show 8 ≤ j + 15 by omega, show 9 ≤ j + 15 by omega, show 10 ≤ j + 15 by omega, show 11 ≤ j + 15 by omega, show 12 ≤ j + 15 by omega, show 13 ≤ j + 15 by omega, show 14 ≤ j + 15 by omega, ↓reduceIte,
      show j + 15 - 1 = j + 14 by omega, show j + 15 - 2 = j + 13 by omega, show j + 15 - 3 = j + 12 by omega, show j + 15 - 4 = j + 11 by omega, show j + 15 - 5 = j + 10 by omega, show j + 15 - 6 = j + 9 by omega, show j + 15 - 7 = j + 8 by omega, show j + 15 - 8 = j + 7 by omega, show j + 15 - 9 = j + 6 by omega, show j + 15 - 10 = j + 5 by omega, show j + 15 - 11 = j + 4 by omega, show j + 15 - 12 = j + 3 by omega, show j + 15 - 13 = j + 2 by omega, show j + 15 - 14 = j + 1 by omega,
      show j + 15 ≠ 0 by omega, show j + 14 ≠ 0 by omega, show j + 13 ≠ 0 by omega, show j + 12 ≠ 0 by omega, show j + 11 ≠ 0 by omega, show j + 10 ≠ 0 by omega, show j + 9 ≠ 0 by omega, show j + 8 ≠ 0 by omega, show j + 7 ≠ 0 by omega, show j + 6 ≠ 0 by omega, show j + 15 ≠ 1 by omega, show j + 15 ≠ 2 by omega, show j + 15 ≠ 3 by omega, show j + 15 ≠ 4 by omega, show j + 15 ≠ 5 by omega, show j + 15 ≠ 6 by omega, show j + 15 ≠ 7 by omega, show j + 15 ≠ 8 by omega, show j + 15 ≠ 9 by omega, show j + 15 ≠ 10 by omega, show j + 15 ≠ 11 by omega, show j + 15 ≠ 12 by omega, show j + 15 ≠ 13 by omega, show j + 15 ≠ 14 by omega]
    linarith

end A184073P

theorem OMA.solution : type_of% @OMA.S_oeis_a184073.main :=
  ⟨A184073P.gf, A184073P.formula, A184073P.rec_main⟩
