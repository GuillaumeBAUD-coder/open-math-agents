import OMAStatements.S_oeis_a224001
import Mathlib

/-!
OEIS A224001. Transfer argument on the first two columns.  Columns are encoded as triples.
For the first two columns u, v let U m u v be the number of good arrays with m + 2 columns
starting with u, v.  Peeling off the first column gives a linear recursion for U, and from
three steps on every U is a polynomial of degree 6 in m written in the binomial basis; the
coefficient tables are checked by kernel evaluation.
-/

namespace OMA.A224001aux

open OMA.S_oeis_a224001

abbrev T := Fin 3 × Fin 3 × Fin 3

def dec (t : T) : Fin 3 → Fin 3 := ![t.1, t.2.1, t.2.2]

def enc (r : Fin 3 → Fin 3) : T := (r 0, r 1, r 2)

theorem dec_enc (r : Fin 3 → Fin 3) : dec (enc r) = r := by
  funext i
  fin_cases i <;> rfl

theorem enc_dec (t : T) : enc (dec t) = t := by
  obtain ⟨a, b, c⟩ := t
  rfl

def encEquiv : (Fin 3 → Fin 3) ≃ T := ⟨enc, dec, dec_enc, enc_dec⟩

def BkT (u v : T) : Prop := BlockOK (dec u) (dec v)

def TrT (u v w : T) : Prop := TriOK (dec u) (dec v) (dec w)

instance : DecidableRel BkT := fun u v => by
  unfold BkT BlockOK
  infer_instance

instance (u v w : T) : Decidable (TrT u v w) := by
  unfold TrT TriOK
  infer_instance

abbrev GoodT {n : ℕ} (y : Fin n → T) : Prop :=
  (∀ i j : Fin n, (j : ℕ) = i + 1 → BkT (y i) (y j)) ∧
    (∀ i j l : Fin n, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TrT (y i) (y j) (y l))

theorem goodT_iff {n : ℕ} (y : Fin n → T) : GoodT y ↔ Good (fun i => dec (y i)) := Iff.rfl

theorem a_eq (n : ℕ) : a n = (Finset.univ.filter (fun y : Fin n → T => GoodT y)).card := by
  unfold a
  have e : {x : Fin n → Fin 3 → Fin 3 // Good x} ≃ {y : Fin n → T // GoodT y} :=
    (Equiv.piCongrRight (fun _ => encEquiv)).subtypeEquiv (fun x => by
      show Good x ↔ GoodT (fun i => enc (x i))
      have h : (fun i => dec (enc (x i))) = x := by
        funext i
        exact dec_enc (x i)
      rw [goodT_iff]
      show Good x ↔ Good (fun i => dec (enc (x i)))
      rw [h])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem v1 (m : ℕ) : ((1 : Fin (m + 3)) : ℕ) = 1 := by
  simp

theorem v2 (m : ℕ) : ((2 : Fin (m + 3)) : ℕ) = 2 := by
  simp

theorem good_peel {m : ℕ} (y : Fin (m + 3) → T) :
    GoodT y ↔ BkT (y 0) (y 1) ∧ TrT (y 0) (y 1) (y 2) ∧ GoodT (Fin.tail y) := by
  constructor
  · rintro ⟨hB, hT⟩
    refine ⟨hB 0 1 (by rw [v1]; simp), hT 0 1 2 (by rw [v1]; simp) (by rw [v1, v2]), ?_, ?_⟩
    · intro i j hij
      exact hB i.succ j.succ (by simp [hij])
    · intro i j l h1 h2
      exact hT i.succ j.succ l.succ (by simp [h1]) (by simp [h2])
  · rintro ⟨hB0, hT0, gB, gT⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        have hj : j = 1 := Fin.ext (by rw [v1]; simpa using hij)
        subst hj
        exact hB0
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' => exact gB i' j' (by simpa using hij)
    · intro i j l h1 h2
      induction i using Fin.cases with
      | zero =>
        have hj : j = 1 := Fin.ext (by rw [v1]; simpa using h1)
        subst hj
        have hl : l = 2 := Fin.ext (by rw [v2]; rw [v1] at h2; simpa using h2)
        subst hl
        exact hT0
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at h1
        | succ j' =>
          induction l using Fin.cases with
          | zero => simp at h2
          | succ l' => exact gT i' j' l' (by simpa using h1) (by simpa using h2)

theorem good2 (y : Fin 2 → T) : GoodT y ↔ BkT (y 0) (y 1) := by
  constructor
  · rintro ⟨hB, -⟩
    exact hB 0 1 rfl
  · intro hB
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hjlt := j.isLt
      have hi : i = 0 := Fin.ext (by show (i : ℕ) = 0; omega)
      have hj : j = 1 := Fin.ext (by show (j : ℕ) = 1; omega)
      subst hi
      subst hj
      exact hB
    · intro i j l h1' h2'
      have := l.isLt
      omega

def U (m : ℕ) (u v : T) : ℕ :=
  (Finset.univ.filter (fun y : Fin (m + 2) → T => GoodT y ∧ y 0 = u ∧ y 1 = v)).card

theorem U_zero (u v : T) : U 0 u v = if BkT u v then 1 else 0 := by
  unfold U
  by_cases hc : BkT u v
  · rw [if_pos hc, Finset.card_eq_one]
    refine ⟨![u, v], ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h0, h1⟩
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · rintro rfl
      exact ⟨(good2 _).2 hc, rfl, rfl⟩
  · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hg, h0, h1⟩ := hy
    have := (good2 y).1 hg
    rw [h0, h1] at this
    exact hc this

theorem U_succ (m : ℕ) (u v : T) :
    U (m + 1) u v
      = if BkT u v then ∑ w : T, (if TrT u v w then U m v w else 0) else 0 := by
  by_cases hc : BkT u v
  · rw [if_pos hc]
    have h1 : U (m + 1) u v
        = ((Finset.univ.filter (fun w : T => TrT u v w)).sigma
            (fun w => Finset.univ.filter
              (fun z : Fin (m + 2) → T => GoodT z ∧ z 0 = v ∧ z 1 = w))).card := by
      unfold U
      refine Finset.card_nbij' (fun y => ⟨y 2, Fin.tail y⟩)
        (fun p => Fin.cons (α := fun _ => T) u p.2) ?_ ?_ ?_ ?_
      · intro y hy
        obtain ⟨hg, h0, h1⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        obtain ⟨_, hT, hG⟩ := (good_peel y).1 hg
        refine Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hG, ?_, ?_⟩⟩)
        · rw [← h0, ← h1]
          exact hT
        · show y (Fin.succ 0) = v
          rw [Fin.succ_zero_eq_one]
          exact h1
        · show y (Fin.succ 1) = y 2
          rw [Fin.succ_one_eq_two]
      · intro p hp
        have hp' := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
        have hT := (Finset.mem_filter.1 hp'.1).2
        obtain ⟨hG, h0, h1⟩ := (Finset.mem_filter.1 hp'.2).2
        have c0 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 0 = u := rfl
        have c1 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 1 = v := by
          rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
          exact h0
        have c2 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 2 = p.1 := by
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          exact h1
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (good_peel _).2 ⟨?_, ?_, ?_⟩, c0, c1⟩)
        · beta_reduce
          rw [c0, c1]
          exact hc
        · beta_reduce
          rw [c0, c1, c2]
          exact hT
        · beta_reduce
          rw [Fin.tail_cons]
          exact hG
      · intro y hy
        obtain ⟨hg, h0, h1⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        show Fin.cons (α := fun _ => T) u (Fin.tail y) = y
        rw [← h0]
        exact Fin.cons_self_tail y
      · intro p hp
        have hp' := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
        obtain ⟨hG, h0, h1⟩ := (Finset.mem_filter.1 hp'.2).2
        obtain ⟨w, z⟩ := p
        have c2 : (Fin.cons (α := fun _ => T) u z : Fin (m + 3) → T) 2 = w := by
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          exact h1
        show (⟨(Fin.cons (α := fun _ => T) u z : Fin (m + 3) → T) 2,
          Fin.tail (Fin.cons (α := fun _ => T) u z)⟩ : (_ : T) × (Fin (m + 2) → T)) = ⟨w, z⟩
        rw [c2, Fin.tail_cons]
    rw [h1, Finset.card_sigma, Finset.sum_filter]
    rfl
  · rw [if_neg hc]
    unfold U
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hg, h0, h1⟩ := hy
    obtain ⟨hB, _, _⟩ := (good_peel y).1 hg
    rw [h0, h1] at hB
    exact hc hB

def idx (t : T) : ℕ := t.1.val * 9 + t.2.1.val * 3 + t.2.2.val

def look (tb : List (List ℕ)) (u v : T) : ℕ := (tb.getD (idx u) []).getD (idx v) 0

def e1 : T → T → ℕ := look [[27, 18, 9, 12, 12, 6, 3, 3, 3, 12, 8, 4, 8, 8, 4, 2, 2, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1],
  [0, 6, 3, 0, 12, 6, 0, 3, 3, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 3, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 12, 6, 0, 3, 3, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 12, 6, 0, 3, 3, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 4, 2, 2, 2, 0, 0, 0, 2, 2, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def e2 : T → T → ℕ := look [[157, 54, 15, 45, 45, 12, 6, 6, 6, 34, 21, 5, 21, 21, 5, 3, 3, 3, 3, 2, 1, 2, 2, 1, 1, 1, 1],
  [0, 33, 10, 0, 45, 12, 0, 6, 6, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 10, 0, 0, 11, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 45, 12, 0, 6, 6, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 45, 12, 0, 6, 6, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 11, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 21, 5, 3, 3, 3, 0, 0, 0, 2, 2, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 5, 0, 3, 3, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def d0 : T → T → ℕ := look [[476, 149, 35, 106, 106, 25, 10, 10, 10, 64, 37, 8, 37, 37, 8, 4, 4, 4, 3, 2, 1, 2, 2, 1, 1, 1, 1],
  [0, 112, 27, 0, 106, 25, 0, 10, 10, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 27, 0, 0, 24, 0, 0, 10, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 106, 25, 0, 10, 10, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 106, 25, 0, 10, 10, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 24, 0, 0, 10, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 37, 8, 4, 4, 4, 0, 0, 0, 2, 2, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 8, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def d1 : T → T → ℕ := look [[668, 199, 38, 103, 103, 21, 5, 5, 5, 38, 21, 4, 21, 21, 4, 1, 1, 1],
  [0, 178, 34, 0, 103, 21, 0, 5, 5, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 34, 0, 0, 21, 0, 0, 5, 0, 0, 0, 0, 0, 4, 0, 0, 1],
  [0, 0, 0, 0, 103, 21, 0, 5, 5, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 0, 0, 103, 21, 0, 5, 5, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 0, 0, 0, 21, 0, 0, 5, 0, 0, 0, 0, 0, 4, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 21, 4, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 4, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def d2 : T → T → ℕ := look [[591, 174, 27, 58, 58, 10, 1, 1, 1, 11, 6, 1, 6, 6, 1],
  [0, 168, 26, 0, 58, 10, 0, 1, 1, 0, 0, 0, 0, 6, 1],
  [0, 0, 26, 0, 0, 10, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 58, 10, 0, 1, 1, 0, 0, 0, 0, 6, 1],
  [0, 0, 0, 0, 58, 10, 0, 1, 1, 0, 0, 0, 0, 6, 1],
  [0, 0, 0, 0, 0, 10, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def d3 : T → T → ℕ := look [[361, 97, 11, 19, 19, 2, 0, 0, 0, 2, 1, 0, 1, 1],
  [0, 96, 11, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 11, 0, 0, 2],
  [0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 2],
  [],
  [],
  [],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def d4 : T → T → ℕ := look [[153, 32, 2, 3, 3],
  [0, 32, 2, 0, 3],
  [0, 0, 2],
  [0, 0, 0, 0, 3],
  [0, 0, 0, 0, 3]]

def d5 : T → T → ℕ := look [[40, 5],
  [0, 5]]

def d6 : T → T → ℕ := look [[5]]


set_option maxRecDepth 1000000 in
theorem G1 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then (if BkT v w then 1 else 0) else 0) else 0) = e1 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem G2 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then e1 v w else 0) else 0) = e2 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem G3 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then e2 v w else 0) else 0) = d0 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F0 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d0 v w else 0) else 0) = d0 u v + d1 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F1 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d1 v w else 0) else 0) = d1 u v + d2 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F2 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d2 v w else 0) else 0) = d2 u v + d3 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F3 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d3 v w else 0) else 0) = d3 u v + d4 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F4 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d4 v w else 0) else 0) = d4 u v + d5 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F5 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d5 v w else 0) else 0) = d5 u v + d6 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem F6 : ∀ u v : T, (if BkT u v then
    ∑ w : T, (if TrT u v w then d6 v w else 0) else 0) = d6 u v := by
  decide

set_option maxRecDepth 1000000 in
theorem Se1 : ∑ s : T × T, e1 s.1 s.2 = 476 := by decide

set_option maxRecDepth 1000000 in
theorem Se2 : ∑ s : T × T, e2 s.1 s.2 = 1144 := by decide

set_option maxRecDepth 1000000 in
theorem Sd0 : ∑ s : T × T, d0 s.1 s.2 = 2403 := by decide

set_option maxRecDepth 1000000 in
theorem Sd1 : ∑ s : T × T, d1 s.1 s.2 = 2211 := by decide

set_option maxRecDepth 1000000 in
theorem Sd2 : ∑ s : T × T, d2 s.1 s.2 = 1466 := by decide

set_option maxRecDepth 1000000 in
theorem Sd3 : ∑ s : T × T, d3 s.1 s.2 = 707 := by decide

set_option maxRecDepth 1000000 in
theorem Sd4 : ∑ s : T × T, d4 s.1 s.2 = 238 := by decide

set_option maxRecDepth 1000000 in
theorem Sd5 : ∑ s : T × T, d5 s.1 s.2 = 50 := by decide

set_option maxRecDepth 1000000 in
theorem Sd6 : ∑ s : T × T, d6 s.1 s.2 = 5 := by decide

set_option maxRecDepth 1000000 in
theorem Se0 : ∑ s : T × T, (if BkT s.1 s.2 then 1 else 0) = 157 := by decide


theorem U1 (u v : T) : U 1 u v = e1 u v := by
  show U (0 + 1) u v = _
  rw [U_succ]
  simp only [U_zero]
  exact G1 u v

theorem U2 (u v : T) : U 2 u v = e2 u v := by
  show U (1 + 1) u v = _
  rw [U_succ]
  simp only [U1]
  exact G2 u v

theorem Upoly (m : ℕ) : ∀ u v : T, U (m + 3) u v
    = d0 u v + d1 u v * m + d2 u v * m.choose 2 + d3 u v * m.choose 3 + d4 u v * m.choose 4
      + d5 u v * m.choose 5 + d6 u v * m.choose 6 := by
  induction m with
  | zero =>
    intro u v
    show U (2 + 1) u v = _
    rw [U_succ]
    simp only [U2]
    rw [G3 u v]
    simp
  | succ m ih =>
    intro u v
    show U ((m + 3) + 1) u v = _
    rw [U_succ]
    have key : ∀ w : T, (if TrT u v w then U (m + 3) v w else 0)
        = (if TrT u v w then d0 v w else 0) + (if TrT u v w then d1 v w else 0) * m
          + (if TrT u v w then d2 v w else 0) * m.choose 2
          + (if TrT u v w then d3 v w else 0) * m.choose 3
          + (if TrT u v w then d4 v w else 0) * m.choose 4
          + (if TrT u v w then d5 v w else 0) * m.choose 5
          + (if TrT u v w then d6 v w else 0) * m.choose 6 := by
      intro w
      rw [ih v w]
      by_cases h : TrT u v w <;> simp [h]
    rw [Finset.sum_congr rfl (fun w _ => key w)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    have f0 := F0 u v
    have f1 := F1 u v
    have f2 := F2 u v
    have f3 := F3 u v
    have f4 := F4 u v
    have f5 := F5 u v
    have f6 := F6 u v
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ m 4
    have p6 : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ m 5
    rw [Nat.choose_one_right] at p2
    by_cases hc : BkT u v
    · rw [if_pos hc] at f0 f1 f2 f3 f4 f5 f6 ⊢
      rw [f0, f1, f2, f3, f4, f5, f6, p2, p3, p4, p5, p6]
      ring
    · rw [if_neg hc] at f0 f1 f2 f3 f4 f5 f6 ⊢
      have z0 : d0 u v = 0 := by omega
      have z1 : d1 u v = 0 := by omega
      have z2 : d2 u v = 0 := by omega
      have z3 : d3 u v = 0 := by omega
      have z4 : d4 u v = 0 := by omega
      have z5 : d5 u v = 0 := by omega
      have z6 : d6 u v = 0 := by omega
      rw [z0, z1, z2, z3, z4, z5, z6]
      simp

theorem fiber (m : ℕ) : (Finset.univ.filter (fun y : Fin (m + 2) → T => GoodT y)).card
    = ∑ s : T × T, U m s.1 s.2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y => (y 0, y 1)) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold U
  congr 1
  ext y
  constructor
  · intro h
    have h1 := Finset.mem_filter.1 h
    have h2 := Finset.mem_filter.1 h1.1
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2.2, congrArg Prod.fst h1.2,
      congrArg Prod.snd h1.2⟩
  · intro h
    have h1 := Finset.mem_filter.1 h
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1.2.1⟩,
      Prod.ext h1.2.2.1 h1.2.2.2⟩

set_option maxRecDepth 100000 in
theorem cardT : (Finset.univ : Finset T).card = 27 := by decide

theorem a_one : a 1 = 27 := by
  rw [a_eq]
  have e : (Finset.univ.filter (fun y : Fin 1 → T => GoodT y)).card
      = (Finset.univ : Finset T).card := by
    refine Finset.card_nbij' (fun y => y 0) (fun t => fun _ => t) ?_ ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_coe.2 (Finset.mem_univ _)
    · intro t ht
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩)
      · intro i j hij
        have := j.isLt
        omega
      · intro i j l h1 h2
        have := l.isLt
        omega
    · intro y hy
      funext i
      show y 0 = y i
      rw [Fin.eq_zero i]
    · intro t ht
      rfl
  rw [e]
  exact cardT

theorem a_two : a 2 = 157 := by
  rw [a_eq]
  have h := fiber 0
  simp only [U_zero] at h
  rw [Se0] at h
  exact h

theorem a_three : a 3 = 476 := by
  rw [a_eq]
  have h := fiber 1
  simp only [U1] at h
  rw [Se1] at h
  exact h

theorem a_four : a 4 = 1144 := by
  rw [a_eq]
  have h := fiber 2
  simp only [U2] at h
  rw [Se2] at h
  exact h

theorem a_ge5 (m : ℕ) : a (m + 5) = 2403 + 2211 * m + 1466 * m.choose 2 + 707 * m.choose 3
    + 238 * m.choose 4 + 50 * m.choose 5 + 5 * m.choose 6 := by
  have h : a (m + 5) = ∑ s : T × T, U (m + 3) s.1 s.2 := (a_eq (m + 5)).trans (fiber (m + 3))
  rw [h]
  simp only [Upoly]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Sd0, Sd1, Sd2, Sd3, Sd4, Sd5, Sd6]

theorem ch2 (m : ℕ) : ((m.choose 2 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    rw [p, Nat.choose_one_right]
    push_cast
    rw [ih]
    ring

theorem ch3 (m : ℕ) : ((m.choose 3 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    rw [p]
    push_cast
    rw [ih, ch2]
    ring

theorem ch4 (m : ℕ) : ((m.choose 4 : ℕ) : ℚ)
    = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    rw [p]
    push_cast
    rw [ih, ch3]
    ring

theorem ch5 (m : ℕ) : ((m.choose 5 : ℕ) : ℚ)
    = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ m 4
    rw [p]
    push_cast
    rw [ih, ch4]
    ring

theorem ch6 (m : ℕ) : ((m.choose 6 : ℕ) : ℚ)
    = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4)
      * ((m : ℚ) - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ m 5
    rw [p]
    push_cast
    rw [ih, ch5]
    ring

theorem closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ)
    = (1 / 144) * (n : ℚ) ^ 6 + (5 / 48) * (n : ℚ) ^ 5 + (163 / 144) * (n : ℚ) ^ 4
      + (85 / 16) * (n : ℚ) ^ 3 + (895 / 36) * (n : ℚ) ^ 2 - (65 / 12) * (n : ℚ) + 3 := by
  by_cases h3 : n = 3
  · subst h3
    rw [a_three]
    norm_num
  by_cases h4 : n = 4
  · subst h4
    rw [a_four]
    norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [a_ge5 m]
  push_cast
  rw [ch2, ch3, ch4, ch5, ch6]
  ring

theorem gf_aux (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 27) (h2 : f 2 = 157) (h3 : f 3 = 476)
    (h4 : f 4 = 1144) (h5 : f 5 = 2403) (h6 : f 6 = 4614) (h7 : f 7 = 8291)
    (h8 : f 8 = 14141) (h9 : f 9 = 23109)
    (hr : ∀ n, f (n + 10) = 7 * f (n + 9) - 21 * f (n + 8) + 35 * f (n + 7) - 35 * f (n + 6)
      + 21 * f (n + 5) - 7 * f (n + 4) + f (n + 3)) :
    PowerSeries.mk f * (1 - PowerSeries.X) ^ 7
      = PowerSeries.X * (27 - 32 * PowerSeries.X - 56 * PowerSeries.X ^ 2
        + 164 * PowerSeries.X ^ 3 - 159 * PowerSeries.X ^ 4 + 85 * PowerSeries.X ^ 5
        - 32 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8) := by
  have k7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have k21 : (PowerSeries.C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
  have k35 : (PowerSeries.C (35 : ℚ) : PowerSeries ℚ) = 35 := map_ofNat _ 35
  have k27 : (PowerSeries.C (27 : ℚ) : PowerSeries ℚ) = 27 := map_ofNat _ 27
  have k32 : (PowerSeries.C (32 : ℚ) : PowerSeries ℚ) = 32 := map_ofNat _ 32
  have k56 : (PowerSeries.C (56 : ℚ) : PowerSeries ℚ) = 56 := map_ofNat _ 56
  have k164 : (PowerSeries.C (164 : ℚ) : PowerSeries ℚ) = 164 := map_ofNat _ 164
  have k159 : (PowerSeries.C (159 : ℚ) : PowerSeries ℚ) = 159 := map_ofNat _ 159
  have k85 : (PowerSeries.C (85 : ℚ) : PowerSeries ℚ) = 85 := map_ofNat _ 85
  have k9 : (PowerSeries.C (9 : ℚ) : PowerSeries ℚ) = 9 := map_ofNat _ 9
  have e1 : PowerSeries.mk f * (1 - PowerSeries.X) ^ 7
      = PowerSeries.mk f - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 1 * PowerSeries.mk f)
        + PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 2 * PowerSeries.mk f)
        - PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 3 * PowerSeries.mk f)
        + PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 4 * PowerSeries.mk f)
        - PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 5 * PowerSeries.mk f)
        + PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 6 * PowerSeries.mk f)
        - PowerSeries.X ^ 7 * PowerSeries.mk f := by
    rw [k7, k21, k35]
    ring
  have e2 : (PowerSeries.X : PowerSeries ℚ) * (27 - 32 * PowerSeries.X - 56 * PowerSeries.X ^ 2
        + 164 * PowerSeries.X ^ 3 - 159 * PowerSeries.X ^ 4 + 85 * PowerSeries.X ^ 5
        - 32 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8)
      = PowerSeries.C (27 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (32 : ℚ) * PowerSeries.X ^ 2
        - PowerSeries.C (56 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (164 : ℚ) * PowerSeries.X ^ 4
        - PowerSeries.C (159 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (85 : ℚ) * PowerSeries.X ^ 6
        - PowerSeries.C (32 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 8
        - PowerSeries.X ^ 9 := by
    rw [k27, k32, k56, k164, k159, k85, k9]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · norm_num [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, h4]
  · norm_num [h0, h1, h2, h3, h4, h5]
  · norm_num [h0, h1, h2, h3, h4, h5, h6]
  · norm_num [h0, h1, h2, h3, h4, h5, h6, h7]
  · norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · have := hr n
    simp
    linarith

end OMA.A224001aux

open OMA.S_oeis_a224001 OMA.A224001aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a224001.main := by
  have hq : ∀ k : ℕ, (a (k + 10) : ℚ) = 7 * (a (k + 9) : ℚ) - 21 * (a (k + 8) : ℚ)
      + 35 * (a (k + 7) : ℚ) - 35 * (a (k + 6) : ℚ) + 21 * (a (k + 5) : ℚ)
      - 7 * (a (k + 4) : ℚ) + (a (k + 3) : ℚ) := by
    intro k
    rw [closed (k + 10) (by omega), closed (k + 9) (by omega), closed (k + 8) (by omega),
      closed (k + 7) (by omega), closed (k + 6) (by omega), closed (k + 5) (by omega),
      closed (k + 4) (by omega), closed (k + 3) (by omega)]
    push_cast
    ring
  refine ⟨?_, ?_, closed⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have e1 : k + 10 - 1 = k + 9 := by omega
    have e2 : k + 10 - 2 = k + 8 := by omega
    have e3 : k + 10 - 3 = k + 7 := by omega
    have e4 : k + 10 - 4 = k + 6 := by omega
    have e5 : k + 10 - 5 = k + 5 := by omega
    have e6 : k + 10 - 6 = k + 4 := by omega
    have e7 : k + 10 - 7 = k + 3 := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    have := hq k
    exact_mod_cast this
  · unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    apply gf_aux
    · simp
    · simp [a_one]
    · simp [a_two]
    · simp [a_three]
    · simp [a_four]
    · have h := closed 5 (by norm_num)
      norm_num at h
      simp [h]
    · have h := closed 6 (by norm_num)
      norm_num at h
      simp [h]
    · have h := closed 7 (by norm_num)
      norm_num at h
      simp [h]
    · have h := closed 8 (by norm_num)
      norm_num at h
      simp [h]
    · have h := closed 9 (by norm_num)
      norm_num at h
      simp [h]
    · intro n
      have := hq n
      simpa using this
