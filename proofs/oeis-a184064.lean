import OMAStatements.S_oeis_a184064

/-!
# A184064: Barker's conjectures, by a transfer count over the rows

An array is read from the top row down. Prepending a row `q` to a valid array `B` keeps it valid
exactly when `q ≤ B 0` lexicographically, the 2 X 2 sums of rows `q, B 0` differ by at most one
horizontally, and they differ by at most one from those of rows `B 0, B 1` (`good_cons`, from
`rows_cons` and `smooth_cons`). Column `j` stays lexicographically below column `j + 1` exactly
when `q j < q (j + 1)`, or `q j = q (j + 1)` and it was so before (`colFlag_cons`, `upd`). So the
arrays with `m + 2` rows and a given state (first row, second row, column flags) are counted by a
linear recursion on the 256 states (`card_S_succ`).

The kernel checks the state vectors for `2, …, 10` rows against explicit tables (`base0`,
`vec_step`, `cardS`), and that they satisfy the fourth difference identity from 6 rows on (`D4`);
the recursion propagates it to every later vector (`D_succ`, `D_zero`). Summing over the states
with all column flags set gives `a` (`a_eq`), hence the recurrence for `n > 7` (`a_rec`,
`rec_main`), the closed form for `n > 3` (`formula`) and the generating function (`gf`).
-/

namespace A184064P
open OMA.S_oeis_a184064 Finset

abbrev Row := Fin 3 → Bool

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
def colFlag {m : ℕ} (B : Fin m → Row) (j : Fin 2) : Bool :=
  decide (List.ofFn (fun i => B i j.castSucc) ≤ List.ofFn (fun i => B i j.succ))

def upd (q : Row) (P : Fin 2 → Bool) (j : Fin 2) : Bool :=
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

def bs (r s : Row) (j : Fin 2) : ℕ :=
  (r j.castSucc).toNat + (r j.succ).toNat + (s j.castSucc).toNat + (s j.succ).toNat

def hs (r s : Row) : Prop :=
  ∀ j j' : Fin 2, j.val + 1 = j'.val → bs r s j ≤ bs r s j' + 1 ∧ bs r s j' ≤ bs r s j + 1

def vs (q r s : Row) : Prop :=
  ∀ j : Fin 2, bs q r j ≤ bs r s j + 1 ∧ bs r s j ≤ bs q r j + 1

theorem sb_zero {m : ℕ} (q : Row) (B : Fin (m + 1) → Row) (j : Fin 2) :
    subblockSum (Fin.cons q B : Fin (m + 2) → Row) 0 j = bs q (B 0) j := by
  simp [subblockSum, bs, Fin.cons_one]

theorem sb_succ {m : ℕ} (q : Row) (B : Fin (m + 1) → Row) (i : Fin m) (j : Fin 2) :
    subblockSum (Fin.cons q B : Fin (m + 2) → Row) i.succ j = subblockSum B i j := by
  simp only [subblockSum]
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

theorem sb_first {m : ℕ} (B : Fin (m + 2) → Row) (j : Fin 2) :
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

abbrev St := Row × Row × (Fin 2 → Bool)

def key {m : ℕ} (B : Fin (m + 2) → Row) : St := (B 0, B 1, colFlag B)

def S (m : ℕ) (σ : St) : Finset (Fin (m + 2) → Row) := univ.filter (fun B => Good B ∧ key B = σ)

def tr (q r s : Row) : Prop := List.ofFn q ≤ List.ofFn r ∧ hs q r ∧ vs q r s

instance (q r s : Row) : Decidable (tr q r s) := by unfold tr hs vs; infer_instance

theorem good_cons {m : ℕ} (q : Row) (B : Fin (m + 2) → Row) :
    Good (Fin.cons q B : Fin (m + 3) → Row) ↔ tr q (B 0) (B 1) ∧ Good B := by
  unfold Good tr
  rw [rows_cons, smooth_cons]
  tauto

theorem key_cons {m : ℕ} (q : Row) (B : Fin (m + 2) → Row) :
    key (Fin.cons q B : Fin (m + 3) → Row) = (q, B 0, upd q (colFlag B)) := by
  simp [key, colFlag_cons, Fin.cons_one]

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
  rw [card_eq_sum_card_fiberwise (f := key) (t := univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
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

theorem card_S_succ (m : ℕ) (q r : Row) (P' : Fin 2 → Bool) :
    (S (m + 1) (q, r, P')).card =
      ∑ s : Row, ∑ P : Fin 2 → Bool,
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


def code (r : Row) : ℕ := 4 * (r 0).toNat + 2 * (r 1).toNat + (r 2).toNat

def enc (σ : St) : ℕ := code σ.1 * 32 + code σ.2.1 * 4 + 2 * (σ.2.2 0).toNat + (σ.2.2 1).toNat

def L0 : List ℕ := [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L1 : List ℕ := [0, 2, 1, 2, 0, 2, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L2 : List ℕ := [0, 6, 4, 3, 0, 2, 0, 4, 0, 0, 11, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L3 : List ℕ := [0, 13, 15, 7, 0, 5, 0, 15, 0, 0, 24, 0, 0, 0, 0, 7, 0, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 7, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 7, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L4 : List ℕ := [0, 27, 39, 22, 0, 9, 0, 31, 0, 0, 44, 0, 0, 0, 0, 11, 0, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 13, 0, 0, 0, 6, 0, 0, 0, 9, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 9, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L5 : List ℕ := [0, 49, 83, 53, 0, 13, 0, 53, 0, 0, 70, 0, 0, 0, 0, 15, 0, 8, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 17, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L6 : List ℕ := [0, 79, 153, 106, 0, 17, 0, 83, 0, 0, 104, 0, 0, 0, 0, 19, 0, 10, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 121, 0, 0, 0, 0, 0, 10, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 21, 0, 0, 0, 10, 0, 0, 0, 13, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 13, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L7 : List ℕ := [0, 117, 257, 189, 0, 21, 0, 121, 0, 0, 146, 0, 0, 0, 0, 23, 0, 12, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 167, 0, 0, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 25, 0, 0, 0, 12, 0, 0, 0, 15, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 15, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L8 : List ℕ := [0, 163, 403, 310, 0, 25, 0, 167, 0, 0, 196, 0, 0, 0, 0, 27, 0, 14, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 0, 0, 0, 0, 0, 14, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 0, 0, 0, 29, 0, 0, 0, 14, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 17, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def L9 : List ℕ := [0, 217, 599, 477, 0, 29, 0, 221, 0, 0, 254, 0, 0, 0, 0, 31, 0, 16, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 283, 0, 0, 0, 0, 0, 16, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 285, 0, 0, 0, 33, 0, 0, 0, 16, 0, 0, 0, 19, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 19, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def vec : ℕ → St → ℕ
  | 0 => fun σ => L0.getD (enc σ) 0
  | 1 => fun σ => L1.getD (enc σ) 0
  | 2 => fun σ => L2.getD (enc σ) 0
  | 3 => fun σ => L3.getD (enc σ) 0
  | 4 => fun σ => L4.getD (enc σ) 0
  | 5 => fun σ => L5.getD (enc σ) 0
  | 6 => fun σ => L6.getD (enc σ) 0
  | 7 => fun σ => L7.getD (enc σ) 0
  | 8 => fun σ => L8.getD (enc σ) 0
  | _ => fun _ => 0

theorem base0 : ∀ σ : St, (S 0 σ).card = vec 0 σ := by
  decide +kernel

theorem vec_step : ∀ k : ℕ, k < 8 → ∀ q r : Row, ∀ P' : Fin 2 → Bool,
    vec (k + 1) (q, r, P') = ∑ s : Row, ∑ P : Fin 2 → Bool,
      if tr q r s ∧ upd q P = P' then vec k (r, s, P) else 0 := by
  decide +kernel

theorem cardS : ∀ k : ℕ, k ≤ 8 → ∀ σ : St, (S k σ).card = vec k σ := by
  intro k
  induction k with
  | zero => intro _; exact base0
  | succ k ih =>
    intro hk ⟨q, r, P'⟩
    rw [card_S_succ, vec_step k (by omega)]
    refine sum_congr rfl fun s _ => sum_congr rfl fun P _ => ?_
    rw [ih (by omega)]

def D (m : ℕ) (σ : St) : ℤ :=
  ((S (m + 4) σ).card : ℤ) - 4 * (S (m + 3) σ).card + 6 * (S (m + 2) σ).card -
    4 * (S (m + 1) σ).card + (S m σ).card

theorem D_succ (m : ℕ) (q r : Row) (P' : Fin 2 → Bool) :
    D (m + 1) (q, r, P') = ∑ s : Row, ∑ P : Fin 2 → Bool,
      if tr q r s ∧ upd q P = P' then D m (r, s, P) else 0 := by
  have e : D (m + 1) (q, r, P') = ((S ((m + 4) + 1) (q, r, P')).card : ℤ) -
      4 * (S ((m + 3) + 1) (q, r, P')).card + 6 * (S ((m + 2) + 1) (q, r, P')).card -
      4 * (S ((m + 1) + 1) (q, r, P')).card + (S (m + 1) (q, r, P')).card := rfl
  rw [e, card_S_succ (m + 4), card_S_succ (m + 3), card_S_succ (m + 2), card_S_succ (m + 1),
    card_S_succ m]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun s _ => sum_congr rfl fun P _ => ?_
  split_ifs <;> simp [D]

theorem D4 : ∀ σ : St, D 4 σ = 0 := by
  intro σ
  simp only [D]
  rw [cardS 8 (by norm_num), cardS 7 (by norm_num), cardS 6 (by norm_num), cardS 5 (by norm_num),
    cardS 4 (by norm_num)]
  revert σ
  decide +kernel

theorem D_zero (m : ℕ) (hm : 4 ≤ m) : ∀ σ : St, D m σ = 0 := by
  induction m, hm using Nat.le_induction with
  | base => exact D4
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

theorem a1v : (a 1 : ℤ) = 11 := by
  rw [a_eq 0]
  simp only [cardS 0 (by norm_num)]
  decide +kernel

theorem a2v : (a 2 : ℤ) = 16 := by
  rw [a_eq 1]
  simp only [cardS 1 (by norm_num)]
  decide +kernel

theorem a3v : (a 3 : ℤ) = 36 := by
  rw [a_eq 2]
  simp only [cardS 2 (by norm_num)]
  decide +kernel

theorem a4v : (a 4 : ℤ) = 73 := by
  rw [a_eq 3]
  simp only [cardS 3 (by norm_num)]
  decide +kernel

theorem a5v : (a 5 : ℤ) = 134 := by
  rw [a_eq 4]
  simp only [cardS 4 (by norm_num)]
  decide +kernel

theorem a6v : (a 6 : ℤ) = 225 := by
  rw [a_eq 5]
  simp only [cardS 5 (by norm_num)]
  decide +kernel

theorem a7v : (a 7 : ℤ) = 354 := by
  rw [a_eq 6]
  simp only [cardS 6 (by norm_num)]
  decide +kernel

theorem a8v : (a 8 : ℤ) = 529 := by
  rw [a_eq 7]
  simp only [cardS 7 (by norm_num)]
  decide +kernel

theorem a9v : (a 9 : ℤ) = 758 := by
  rw [a_eq 8]
  simp only [cardS 8 (by norm_num)]
  decide +kernel

theorem a_rec (m : ℕ) (hm : 4 ≤ m) :
    (a (m + 5) : ℤ) = 4 * a (m + 4) - 6 * a (m + 3) + 4 * a (m + 2) - a (m + 1) := by
  have h := sum_eq_zero (s := (univ : Finset St)) (f := fun σ => if ψ σ then D m σ else 0)
    (fun σ _ => by simp [D_zero m hm σ])
  rw [show m + 5 = (m + 4) + 1 by ring, show m + 4 = (m + 3) + 1 by ring,
    show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring, a_eq, a_eq, a_eq, a_eq, a_eq]
  have e : ∀ σ, (if ψ σ then D m σ else 0) =
      ((if ψ σ then ((S (m + 4) σ).card : ℤ) else 0) - 4 * (if ψ σ then ((S (m + 3) σ).card : ℤ) else 0) +
        6 * (if ψ σ then ((S (m + 2) σ).card : ℤ) else 0) - 4 * (if ψ σ then ((S (m + 1) σ).card : ℤ) else 0) +
        (if ψ σ then ((S m σ).card : ℤ) else 0)) := by
    intro σ; split_ifs <;> simp [D]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  linarith


theorem rec_main (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  rcases Nat.lt_or_ge n 9 with h | h
  · obtain rfl : n = 8 := by omega
    simp only [show 8 - 1 = 7 from rfl, show 8 - 2 = 6 from rfl, show 8 - 3 = 5 from rfl,
      show 8 - 4 = 4 from rfl, a8v, a7v, a6v, a5v, a4v]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [a_rec m (by omega)]
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]

theorem formula (n : ℕ) (hn : 3 < n) :
    3 * (a n : ℤ) = 4 * n ^ 3 - 15 * n ^ 2 + 74 * n - 93 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · rw [a4v]; norm_num
      · rw [a5v]; norm_num
      · rw [a6v]; norm_num
      · rw [a7v]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h1 := ih (k + 3) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      have h3 := ih (k + 1) (by omega) (by omega)
      have h4 := ih k (by omega) (by omega)
      rw [rec_main (k + 4) (by omega)]
      simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
      push_cast at h1 h2 h3 h4 ⊢
      linear_combination 4 * h1 - 6 * h2 + 4 * h3 - h4

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 4 =
    X * (11 - 28 * X + 38 * X ^ 2 - 19 * X ^ 3 + 5 * X ^ 4 - X ^ 5 + 2 * X ^ 6) := by
  have e1 : ((1 - X) ^ 4 : PowerSeries ℤ) = 1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (X * (11 - 28 * X + 38 * X ^ 2 - 19 * X ^ 3 + 5 * X ^ 4 - X ^ 5 + 2 * X ^ 6) :
      PowerSeries ℤ) = C 11 * X ^ 1 - C 28 * X ^ 2 + C 38 * X ^ 3 - C 19 * X ^ 4 + C 5 * X ^ 5 -
        X ^ 6 + C 2 * X ^ 7 := by
    simp only [map_ofNat, pow_one]; ring
  rw [mul_comm, e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 8 with h | h
  · interval_cases k <;> simp [a1v, a2v, a3v, a4v, a5v, a6v, a7v]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    have hr := rec_main (j + 8) (by omega)
    simp only [show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega,
      show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega] at hr
    simp only [show 1 ≤ j + 8 by omega, show 2 ≤ j + 8 by omega, show 3 ≤ j + 8 by omega,
      show 4 ≤ j + 8 by omega, ↓reduceIte, show j + 8 - 1 = j + 7 by omega,
      show j + 8 - 2 = j + 6 by omega, show j + 8 - 3 = j + 5 by omega,
      show j + 8 - 4 = j + 4 by omega, show j + 8 ≠ 0 by omega, show j + 7 ≠ 0 by omega,
      show j + 6 ≠ 0 by omega, show j + 5 ≠ 0 by omega, show j + 4 ≠ 0 by omega,
      show j + 8 ≠ 1 by omega, show j + 8 ≠ 2 by omega, show j + 8 ≠ 3 by omega,
      show j + 8 ≠ 4 by omega, show j + 8 ≠ 5 by omega, show j + 8 ≠ 6 by omega,
      show j + 8 ≠ 7 by omega]
    linarith

end A184064P

theorem OMA.solution : type_of% @OMA.S_oeis_a184064.main :=
  ⟨A184064P.gf, A184064P.formula, A184064P.rec_main⟩
