import OMAStatements.S_oeis_a282523
import Mathlib

/-!
# oeis-a282523: counting n X 3 arrays row by row

The condition at a cell involves only its row and the rows above and below. Writing `F m p r` for
the number of ways to continue a top row `r` (with `p` the row above it, if any) by `m` more rows,
`F` satisfies a linear recursion over the next row. The defect of the conjectured recurrence
satisfies the same recursion and vanishes for `m = 0` (computed for all 72 states), so it vanishes
identically. Summing over the top row gives the recurrence for `a`, and the generating function
follows by comparing coefficients.
-/

namespace OMA.P_oeis_a282523

open OMA.S_oeis_a282523

abbrev R := Fin 3 → Fin 2

/-- The entry of an optional row at column `j`, `0` outside. -/
def rv (p : Option R) (j : ℤ) : ℕ :=
  match p with
  | none => 0
  | some r => if h : 0 ≤ j ∧ j < 3 then (r ⟨j.toNat, by omega⟩ : ℕ) else 0

/-- Row `i` of `x`, if it exists. -/
def orow {n : ℕ} (x : Fin n → R) (i : ℤ) : Option R :=
  if h : 0 ≤ i ∧ i < n then some (x ⟨i.toNat, by omega⟩) else none

lemma get_eq {n : ℕ} (x : Fin n → R) (i j : ℤ) : S_oeis_a282523.get x i j = rv (orow x i) j := by
  unfold S_oeis_a282523.get rv orow
  by_cases hi : 0 ≤ i ∧ i < n
  · rw [dif_pos hi]
    dsimp only
    by_cases hj : 0 ≤ j ∧ j < 3
    · rw [dif_pos ⟨hi.1, hi.2, hj.1, hj.2⟩, dif_pos hj]
    · rw [dif_neg (by tauto), dif_neg hj]
  · rw [dif_neg (by tauto), dif_neg hi]

/-- King-move ones around column `j` of row `r`, with rows `p` above and `s` below. -/
def kc (p : Option R) (r : R) (s : Option R) (j : ℤ) : ℕ :=
  rv p (j - 1) + rv p j + rv p (j + 1) + (rv (some r) (j - 1) + rv (some r) (j + 1)) +
    (rv s (j - 1) + rv s j + rv s (j + 1))

/-- The condition on row `r` between rows `p` and `s`. -/
def W (p : Option R) (r : R) (s : Option R) : Prop := ∀ j : Fin 3, r j = 1 → kc p r s j ≤ 2

instance (p : Option R) (r : R) (s : Option R) : Decidable (W p r s) := by
  unfold W; infer_instance

lemma orow_self {n : ℕ} (x : Fin n → R) (i : Fin n) : orow x (i : ℕ) = some (x i) := by
  unfold orow; rw [dif_pos (by omega)]; congr

lemma kingOnes_eq {n : ℕ} (x : Fin n → R) (i : Fin n) (j : Fin 3) :
    kingOnes x (i : ℕ) (j : ℕ) = kc (orow x ((i : ℕ) - 1)) (x i) (orow x ((i : ℕ) + 1)) (j : ℕ) := by
  unfold kingOnes kc
  simp only [Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, get_eq]
  simp only [show ((0 : Fin 3) = 1) ↔ False by decide, show ((2 : Fin 3) = 1) ↔ False by decide,
    false_and, and_false, and_self, if_false, if_true]
  simp only [add_zero, show ∀ z : ℤ, z + 1 - 1 = z from fun z => by ring,
    show ∀ z : ℤ, z + 2 - 1 = z + 1 from fun z => by ring,
    orow_self]
  try ring

lemma valid_iff {n : ℕ} (x : Fin n → R) :
    Valid x ↔ ∀ i : Fin n, W (orow x ((i : ℕ) - 1)) (x i) (orow x ((i : ℕ) + 1)) := by
  unfold Valid W
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [kingOnes_eq]

/-- The window conditions, row by row, with `p` the row above the first one. -/
def G : (m : ℕ) → Option R → (Fin m → R) → Prop
  | 0, _, _ => True
  | m + 1, p, y => W p (y 0) (orow (Fin.tail y) 0) ∧ G m (some (y 0)) (Fin.tail y)

instance decG : ∀ (m : ℕ) (p : Option R) (y : Fin m → R), Decidable (G m p y)
  | 0, _, _ => isTrue trivial
  | m + 1, p, y => by
    unfold G
    haveI := decG m (some (y 0)) (Fin.tail y)
    infer_instance

lemma orow_tail {m : ℕ} (y : Fin (m + 1) → R) (t : ℤ) (ht : 0 ≤ t) :
    orow (Fin.tail y) t = orow y (t + 1) := by
  unfold orow
  by_cases h : 0 ≤ t ∧ t < m
  · rw [dif_pos h, dif_pos (by omega)]
    simp only [Fin.tail, Option.some.injEq]
    congr 1; ext; simp only [Fin.val_succ]; omega
  · rw [dif_neg h, dif_neg (by omega)]

lemma G_iff : ∀ (m : ℕ) (p : Option R) (y : Fin m → R),
    G m p y ↔ ∀ i : Fin m, W (if (i : ℕ) = 0 then p else orow y ((i : ℕ) - 1)) (y i) (orow y ((i : ℕ) + 1)) := by
  intro m
  induction m with
  | zero => intro p y; exact ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | succ m ih =>
    intro p y
    rw [G, ih, Fin.forall_fin_succ]
    apply and_congr
    · simp only [Fin.val_zero, if_true, Nat.cast_zero, zero_add]
      rw [orow_tail y 0 le_rfl, zero_add]
    · refine forall_congr' fun i => ?_
      have e1 : orow (Fin.tail y) ((i : ℕ) + 1) = orow y (((i.succ : Fin (m + 1)) : ℕ) + 1) := by
        rw [orow_tail y _ (by omega)]; simp
      have e2 : (if (i : ℕ) = 0 then some (y 0) else orow (Fin.tail y) ((i : ℕ) - 1)) =
          orow y (((i.succ : Fin (m + 1)) : ℕ) - 1) := by
        split_ifs with h
        · have : ((i.succ : Fin (m + 1)) : ℕ) = 1 := by simp [h]
          rw [this]; unfold orow; rw [dif_pos (by omega)]; rfl
        · rw [orow_tail y _ (by omega)]; congr 1; (try simp)
      rw [e1, e2, if_neg (by simp)]
      rfl

lemma valid_iff_G {n : ℕ} (x : Fin n → R) : Valid x ↔ G n none x := by
  rw [valid_iff, G_iff]
  refine forall_congr' fun i => ?_
  split_ifs with h
  · rw [h]; unfold orow; rw [dif_neg (by omega)]
  · rfl

/-- Ways to continue a first row `r` (below an optional row `p`) by `m` more rows. -/
def F (m : ℕ) (p : Option R) (r : R) : ℕ :=
  (Finset.univ.filter fun y : Fin m → R => G (m + 1) p (Fin.cons r y)).card

lemma card_succ (m : ℕ) (P : (Fin (m + 1) → R) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ r : R, (Finset.univ.filter fun y : Fin m → R => P (Fin.cons r y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => R)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma a_eq (m : ℕ) : a (m + 1) = ∑ r : R, F m none r := by
  unfold a F
  rw [card_succ]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact congrArg Finset.card (Finset.filter_congr fun y _ => valid_iff_G _)

lemma orow_nil (y : Fin 0 → R) (t : ℤ) : orow y t = none := by
  unfold orow; rw [dif_neg (by omega)]

lemma orow_cons0 {m : ℕ} (s : R) (y : Fin m → R) : orow (Fin.cons s y : Fin (m + 1) → R) 0 = some s := by
  unfold orow; rw [dif_pos (by omega)]; rfl

lemma F_zero (p : Option R) (r : R) : F 0 p r = if W p r none then 1 else 0 := by
  unfold F
  have := orow_nil (Fin.tail (Fin.cons r (Fin.elim0 : Fin 0 → R) : Fin 1 → R)) 0
  split_ifs with h
  · rw [Finset.card_eq_one]; refine ⟨Fin.elim0, ?_⟩
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro hy; subst hy; refine ⟨?_, trivial⟩; simpa [this, orow_nil] using h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    apply h
    have hy0 := hy.1
    have : y = Fin.elim0 := funext fun i => i.elim0
    subst this
    simpa [this, orow_nil] using hy0

lemma F_succ (m : ℕ) (p : Option R) (r : R) :
    F (m + 1) p r = ∑ s : R, if W p r (some s) then F m (some r) s else 0 := by
  unfold F
  rw [card_succ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : ∀ y : Fin m → R, G (m + 1 + 1) p (Fin.cons r (Fin.cons s y)) ↔
      W p r (some s) ∧ G (m + 1) (some r) (Fin.cons s y) := by
    intro y
    rw [G]
    simp only [Fin.cons_zero, Fin.tail_cons, orow_cons0]
  simp only [e]
  split_ifs with h
  · simp [h]
  · simp [h]

lemma sumR {M : Type*} [AddCommMonoid M] (g : R → M) :
    ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, g ![y0, y1, y2] := by
  let e : Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun q => ![q.1, q.2.1, q.2.2], fun f => (f 0, f 1, f 2), fun q => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

lemma st_n_000 (m : ℕ) : F (m + 1) none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_n_001 (m : ℕ) : F (m + 1) none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_n_010 (m : ℕ) : F (m + 1) none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_n_011 (m : ℕ) : F (m + 1) none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_n_100 (m : ℕ) : F (m + 1) none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_n_101 (m : ℕ) : F (m + 1) none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_n_110 (m : ℕ) : F (m + 1) none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_n_111 (m : ℕ) : F (m + 1) none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_000_000 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_000_001 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_000_010 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_000_011 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_000_100 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_000_101 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_000_110 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_000_111 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_001_000 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_001_001 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_001_010 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_001_011 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_001_100 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_001_101 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_001_110 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_001_111 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_010_000 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_010_001 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_010_010 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_010_011 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_010_100 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_010_101 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_010_110 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_010_111 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_011_000 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_011_001 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_011_010 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_011_011 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_011_100 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_011_101 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_011_110 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_011_111 (m : ℕ) : F (m + 1) (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_100_000 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_100_001 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_100_010 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_100_011 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_100_100 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_100_101 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_100_110 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_100_111 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_101_000 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_101_001 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_101_010 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_101_011 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_101_100 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_101_101 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_101_110 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_101_111 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_110_000 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_110_001 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero, add_assoc]

lemma st_110_010 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_110_011 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_110_100 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_110_101 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_110_110 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_110_111 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_111_000 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, add_assoc]

lemma st_111_001 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_111_010 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_111_011 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_111_100 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + F m (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_111_101 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = F m (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_true, if_false, add_zero]

lemma st_111_110 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma st_111_111 (m : ℕ) : F (m + 1) (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_succ, sumR]
  simp only [Fin.sum_univ_two]
  simp +decide only [if_false, add_zero]

lemma v0_n_000 : F 0 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_001 : F 0 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_010 : F 0 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_011 : F 0 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_100 : F 0 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_101 : F 0 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_110 : F 0 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_n_111 : F 0 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_000 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_001 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_010 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_011 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_100 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_101 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_110 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_000_111 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_000 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_001 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_010 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_011 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_100 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_101 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_110 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_001_111 : F 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_010_000 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_001 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_010 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_011 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_100 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_101 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_110 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_010_111 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_011_000 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_011_001 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_011_010 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_011_011 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_011_100 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_011_101 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_011_110 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_011_111 : F 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_100_000 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_001 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_010 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_011 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_100 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_101 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_110 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_100_111 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_101_000 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_101_001 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_101_010 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_101_011 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_101_100 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_101_101 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_101_110 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_101_111 : F 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_110_000 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_110_001 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_110_010 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_110_011 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_110_100 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_110_101 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_110_110 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_110_111 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_111_000 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_111_001 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_111_010 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_111_011 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_111_100 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_111_101 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [F_zero]; decide

lemma v0_111_110 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v0_111_111 : F 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [F_zero]; decide

lemma v1_n_000 : F 1 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_n_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_n_001 : F 1 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 7 := by
  rw [st_n_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_011, v0_001_100, v0_001_101, v0_001_110, v0_001_111]

lemma v1_n_010 : F 1 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 7 := by
  rw [st_n_010]; simp only [v0_010_000, v0_010_001, v0_010_010, v0_010_011, v0_010_100, v0_010_101, v0_010_110]

lemma v1_n_011 : F 1 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 4 := by
  rw [st_n_011]; simp only [v0_011_000, v0_011_001, v0_011_010, v0_011_100]

lemma v1_n_100 : F 1 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 7 := by
  rw [st_n_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101, v0_100_110, v0_100_111]

lemma v1_n_101 : F 1 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_n_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_011, v0_101_100, v0_101_101, v0_101_110, v0_101_111]

lemma v1_n_110 : F 1 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4 := by
  rw [st_n_110]; simp only [v0_110_000, v0_110_001, v0_110_010, v0_110_100]

lemma v1_n_111 : F 1 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_n_111]; simp only [v0_111_000]

lemma v1_000_000 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_000_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_000_001 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 7 := by
  rw [st_000_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_011, v0_001_100, v0_001_101, v0_001_110, v0_001_111]

lemma v1_000_010 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 7 := by
  rw [st_000_010]; simp only [v0_010_000, v0_010_001, v0_010_010, v0_010_011, v0_010_100, v0_010_101, v0_010_110]

lemma v1_000_011 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 4 := by
  rw [st_000_011]; simp only [v0_011_000, v0_011_001, v0_011_010, v0_011_100]

lemma v1_000_100 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 7 := by
  rw [st_000_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101, v0_100_110, v0_100_111]

lemma v1_000_101 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_000_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_011, v0_101_100, v0_101_101, v0_101_110, v0_101_111]

lemma v1_000_110 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4 := by
  rw [st_000_110]; simp only [v0_110_000, v0_110_001, v0_110_010, v0_110_100]

lemma v1_000_111 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_000_111]; simp only [v0_111_000]

lemma v1_001_000 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_001_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_001_001 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 6 := by
  rw [st_001_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_100, v0_001_101, v0_001_110]

lemma v1_001_010 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4 := by
  rw [st_001_010]; simp only [v0_010_000, v0_010_001, v0_010_010, v0_010_100]

lemma v1_001_011 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_001_011]; simp only [v0_011_000]

lemma v1_001_100 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 7 := by
  rw [st_001_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101, v0_100_110, v0_100_111]

lemma v1_001_101 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_001_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_100, v0_101_101, v0_101_110]

lemma v1_001_110 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_001_110]; simp only [v0_110_000]

lemma v1_001_111 : F 1 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v1_010_000 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_010_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_010_001 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 6 := by
  rw [st_010_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_100, v0_001_101, v0_001_110]

lemma v1_010_010 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4 := by
  rw [st_010_010]; simp only [v0_010_000, v0_010_001, v0_010_010, v0_010_100]

lemma v1_010_011 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_010_011]; simp only [v0_011_000]

lemma v1_010_100 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 6 := by
  rw [st_010_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101]

lemma v1_010_101 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_010_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_100, v0_101_101]

lemma v1_010_110 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_010_110]; simp only [v0_110_000]

lemma v1_010_111 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v1_011_000 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_011_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_011_001 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 2 := by
  rw [st_011_001]; simp only [v0_001_000, v0_001_100]

lemma v1_011_010 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_011_010]; simp only [v0_010_000]

lemma v1_011_011 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v1_011_100 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 6 := by
  rw [st_011_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101]

lemma v1_011_101 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 2 := by
  rw [st_011_101]; simp only [v0_101_000, v0_101_100]

lemma v1_011_110 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v1_011_111 : F 1 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v1_100_000 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_100_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_100_001 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 7 := by
  rw [st_100_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_011, v0_001_100, v0_001_101, v0_001_110, v0_001_111]

lemma v1_100_010 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4 := by
  rw [st_100_010]; simp only [v0_010_000, v0_010_001, v0_010_010, v0_010_100]

lemma v1_100_011 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_100_011]; simp only [v0_011_000]

lemma v1_100_100 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 6 := by
  rw [st_100_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101]

lemma v1_100_101 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_100_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_011, v0_101_100, v0_101_101]

lemma v1_100_110 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_100_110]; simp only [v0_110_000]

lemma v1_100_111 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v1_101_000 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_101_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_101_001 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 6 := by
  rw [st_101_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_100, v0_001_101, v0_001_110]

lemma v1_101_010 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_101_010]; simp only [v0_010_000]

lemma v1_101_011 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v1_101_100 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 6 := by
  rw [st_101_100]; simp only [v0_100_000, v0_100_001, v0_100_010, v0_100_011, v0_100_100, v0_100_101]

lemma v1_101_101 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5 := by
  rw [st_101_101]; simp only [v0_101_000, v0_101_001, v0_101_010, v0_101_100, v0_101_101]

lemma v1_101_110 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v1_101_111 : F 1 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v1_110_000 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_110_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_110_001 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 6 := by
  rw [st_110_001]; simp only [v0_001_000, v0_001_001, v0_001_010, v0_001_100, v0_001_101, v0_001_110]

lemma v1_110_010 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1 := by
  rw [st_110_010]; simp only [v0_010_000]

lemma v1_110_011 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v1_110_100 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 2 := by
  rw [st_110_100]; simp only [v0_100_000, v0_100_001]

lemma v1_110_101 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 2 := by
  rw [st_110_101]; simp only [v0_101_000, v0_101_001]

lemma v1_110_110 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v1_110_111 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v1_111_000 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_111_000]; simp only [v0_000_000, v0_000_001, v0_000_010, v0_000_011, v0_000_100, v0_000_101, v0_000_110, v0_000_111]

lemma v1_111_001 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 2 := by
  rw [st_111_001]; simp only [v0_001_000, v0_001_100]

lemma v1_111_010 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v1_111_011 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v1_111_100 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 2 := by
  rw [st_111_100]; simp only [v0_100_000, v0_100_001]

lemma v1_111_101 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1 := by
  rw [st_111_101]; simp only [v0_101_000]

lemma v1_111_110 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v1_111_111 : F 1 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v2_n_000 : F 2 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_n_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_n_001 : F 2 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 32 := by
  rw [st_n_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_011, v1_001_100, v1_001_101, v1_001_110, v1_001_111]

lemma v2_n_010 : F 2 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_n_010]; simp only [v1_010_000, v1_010_001, v1_010_010, v1_010_011, v1_010_100, v1_010_101, v1_010_110]

lemma v2_n_011 : F 2 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 17 := by
  rw [st_n_011]; simp only [v1_011_000, v1_011_001, v1_011_010, v1_011_100]

lemma v2_n_100 : F 2 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 32 := by
  rw [st_n_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101, v1_100_110, v1_100_111]

lemma v2_n_101 : F 2 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_n_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_011, v1_101_100, v1_101_101, v1_101_110, v1_101_111]

lemma v2_n_110 : F 2 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 17 := by
  rw [st_n_110]; simp only [v1_110_000, v1_110_001, v1_110_010, v1_110_100]

lemma v2_n_111 : F 2 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_n_111]; simp only [v1_111_000]

lemma v2_000_000 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_000_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_000_001 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 32 := by
  rw [st_000_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_011, v1_001_100, v1_001_101, v1_001_110, v1_001_111]

lemma v2_000_010 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_000_010]; simp only [v1_010_000, v1_010_001, v1_010_010, v1_010_011, v1_010_100, v1_010_101, v1_010_110]

lemma v2_000_011 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 17 := by
  rw [st_000_011]; simp only [v1_011_000, v1_011_001, v1_011_010, v1_011_100]

lemma v2_000_100 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 32 := by
  rw [st_000_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101, v1_100_110, v1_100_111]

lemma v2_000_101 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_000_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_011, v1_101_100, v1_101_101, v1_101_110, v1_101_111]

lemma v2_000_110 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 17 := by
  rw [st_000_110]; simp only [v1_110_000, v1_110_001, v1_110_010, v1_110_100]

lemma v2_000_111 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_000_111]; simp only [v1_111_000]

lemma v2_001_000 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_001_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_001_001 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 31 := by
  rw [st_001_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_100, v1_001_101, v1_001_110]

lemma v2_001_010 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 24 := by
  rw [st_001_010]; simp only [v1_010_000, v1_010_001, v1_010_010, v1_010_100]

lemma v2_001_011 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_001_011]; simp only [v1_011_000]

lemma v2_001_100 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 32 := by
  rw [st_001_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101, v1_100_110, v1_100_111]

lemma v2_001_101 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_001_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_100, v1_101_101, v1_101_110]

lemma v2_001_110 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_001_110]; simp only [v1_110_000]

lemma v2_001_111 : F 2 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v2_010_000 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_010_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_010_001 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 31 := by
  rw [st_010_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_100, v1_001_101, v1_001_110]

lemma v2_010_010 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 24 := by
  rw [st_010_010]; simp only [v1_010_000, v1_010_001, v1_010_010, v1_010_100]

lemma v2_010_011 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_010_011]; simp only [v1_011_000]

lemma v2_010_100 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_010_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101]

lemma v2_010_101 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_010_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_100, v1_101_101]

lemma v2_010_110 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_010_110]; simp only [v1_110_000]

lemma v2_010_111 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v2_011_000 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_011_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_011_001 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 15 := by
  rw [st_011_001]; simp only [v1_001_000, v1_001_100]

lemma v2_011_010 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_011_010]; simp only [v1_010_000]

lemma v2_011_011 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v2_011_100 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_011_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101]

lemma v2_011_101 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 14 := by
  rw [st_011_101]; simp only [v1_101_000, v1_101_100]

lemma v2_011_110 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v2_011_111 : F 2 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v2_100_000 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_100_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_100_001 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 32 := by
  rw [st_100_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_011, v1_001_100, v1_001_101, v1_001_110, v1_001_111]

lemma v2_100_010 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 24 := by
  rw [st_100_010]; simp only [v1_010_000, v1_010_001, v1_010_010, v1_010_100]

lemma v2_100_011 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_100_011]; simp only [v1_011_000]

lemma v2_100_100 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_100_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101]

lemma v2_100_101 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_100_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_011, v1_101_100, v1_101_101]

lemma v2_100_110 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_100_110]; simp only [v1_110_000]

lemma v2_100_111 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v2_101_000 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_101_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_101_001 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 31 := by
  rw [st_101_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_100, v1_001_101, v1_001_110]

lemma v2_101_010 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_101_010]; simp only [v1_010_000]

lemma v2_101_011 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v2_101_100 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 31 := by
  rw [st_101_100]; simp only [v1_100_000, v1_100_001, v1_100_010, v1_100_011, v1_100_100, v1_100_101]

lemma v2_101_101 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 26 := by
  rw [st_101_101]; simp only [v1_101_000, v1_101_001, v1_101_010, v1_101_100, v1_101_101]

lemma v2_101_110 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v2_101_111 : F 2 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v2_110_000 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_110_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_110_001 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 31 := by
  rw [st_110_001]; simp only [v1_001_000, v1_001_001, v1_001_010, v1_001_100, v1_001_101, v1_001_110]

lemma v2_110_010 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 8 := by
  rw [st_110_010]; simp only [v1_010_000]

lemma v2_110_011 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v2_110_100 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 15 := by
  rw [st_110_100]; simp only [v1_100_000, v1_100_001]

lemma v2_110_101 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 14 := by
  rw [st_110_101]; simp only [v1_101_000, v1_101_001]

lemma v2_110_110 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v2_110_111 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v2_111_000 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_111_000]; simp only [v1_000_000, v1_000_001, v1_000_010, v1_000_011, v1_000_100, v1_000_101, v1_000_110, v1_000_111]

lemma v2_111_001 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 15 := by
  rw [st_111_001]; simp only [v1_001_000, v1_001_100]

lemma v2_111_010 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v2_111_011 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v2_111_100 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 15 := by
  rw [st_111_100]; simp only [v1_100_000, v1_100_001]

lemma v2_111_101 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 8 := by
  rw [st_111_101]; simp only [v1_101_000]

lemma v2_111_110 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v2_111_111 : F 2 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v3_n_000 : F 3 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_n_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_n_001 : F 3 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 172 := by
  rw [st_n_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_011, v2_001_100, v2_001_101, v2_001_110, v2_001_111]

lemma v3_n_010 : F 3 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 171 := by
  rw [st_n_010]; simp only [v2_010_000, v2_010_001, v2_010_010, v2_010_011, v2_010_100, v2_010_101, v2_010_110]

lemma v3_n_011 : F 3 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 97 := by
  rw [st_n_011]; simp only [v2_011_000, v2_011_001, v2_011_010, v2_011_100]

lemma v3_n_100 : F 3 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 172 := by
  rw [st_n_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101, v2_100_110, v2_100_111]

lemma v3_n_101 : F 3 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_n_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_011, v2_101_100, v2_101_101, v2_101_110, v2_101_111]

lemma v3_n_110 : F 3 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 97 := by
  rw [st_n_110]; simp only [v2_110_000, v2_110_001, v2_110_010, v2_110_100]

lemma v3_n_111 : F 3 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_n_111]; simp only [v2_111_000]

lemma v3_000_000 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_000_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_000_001 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 172 := by
  rw [st_000_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_011, v2_001_100, v2_001_101, v2_001_110, v2_001_111]

lemma v3_000_010 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 171 := by
  rw [st_000_010]; simp only [v2_010_000, v2_010_001, v2_010_010, v2_010_011, v2_010_100, v2_010_101, v2_010_110]

lemma v3_000_011 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 97 := by
  rw [st_000_011]; simp only [v2_011_000, v2_011_001, v2_011_010, v2_011_100]

lemma v3_000_100 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 172 := by
  rw [st_000_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101, v2_100_110, v2_100_111]

lemma v3_000_101 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_000_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_011, v2_101_100, v2_101_101, v2_101_110, v2_101_111]

lemma v3_000_110 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 97 := by
  rw [st_000_110]; simp only [v2_110_000, v2_110_001, v2_110_010, v2_110_100]

lemma v3_000_111 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_000_111]; simp only [v2_111_000]

lemma v3_001_000 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_001_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_001_001 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 164 := by
  rw [st_001_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_100, v2_001_101, v2_001_110]

lemma v3_001_010 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 129 := by
  rw [st_001_010]; simp only [v2_010_000, v2_010_001, v2_010_010, v2_010_100]

lemma v3_001_011 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_001_011]; simp only [v2_011_000]

lemma v3_001_100 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 172 := by
  rw [st_001_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101, v2_100_110, v2_100_111]

lemma v3_001_101 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_001_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_100, v2_101_101, v2_101_110]

lemma v3_001_110 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_001_110]; simp only [v2_110_000]

lemma v3_001_111 : F 3 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v3_010_000 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_010_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_010_001 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 164 := by
  rw [st_010_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_100, v2_001_101, v2_001_110]

lemma v3_010_010 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 129 := by
  rw [st_010_010]; simp only [v2_010_000, v2_010_001, v2_010_010, v2_010_100]

lemma v3_010_011 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_010_011]; simp only [v2_011_000]

lemma v3_010_100 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 164 := by
  rw [st_010_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101]

lemma v3_010_101 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_010_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_100, v2_101_101]

lemma v3_010_110 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_010_110]; simp only [v2_110_000]

lemma v3_010_111 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v3_011_000 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_011_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_011_001 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 75 := by
  rw [st_011_001]; simp only [v2_001_000, v2_001_100]

lemma v3_011_010 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_011_010]; simp only [v2_010_000]

lemma v3_011_011 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v3_011_100 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 164 := by
  rw [st_011_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101]

lemma v3_011_101 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 74 := by
  rw [st_011_101]; simp only [v2_101_000, v2_101_100]

lemma v3_011_110 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v3_011_111 : F 3 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v3_100_000 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_100_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_100_001 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 172 := by
  rw [st_100_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_011, v2_001_100, v2_001_101, v2_001_110, v2_001_111]

lemma v3_100_010 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 129 := by
  rw [st_100_010]; simp only [v2_010_000, v2_010_001, v2_010_010, v2_010_100]

lemma v3_100_011 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_100_011]; simp only [v2_011_000]

lemma v3_100_100 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 164 := by
  rw [st_100_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101]

lemma v3_100_101 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_100_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_011, v2_101_100, v2_101_101]

lemma v3_100_110 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_100_110]; simp only [v2_110_000]

lemma v3_100_111 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v3_101_000 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_101_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_101_001 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 164 := by
  rw [st_101_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_100, v2_001_101, v2_001_110]

lemma v3_101_010 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_101_010]; simp only [v2_010_000]

lemma v3_101_011 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v3_101_100 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 164 := by
  rw [st_101_100]; simp only [v2_100_000, v2_100_001, v2_100_010, v2_100_011, v2_100_100, v2_100_101]

lemma v3_101_101 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 139 := by
  rw [st_101_101]; simp only [v2_101_000, v2_101_001, v2_101_010, v2_101_100, v2_101_101]

lemma v3_101_110 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v3_101_111 : F 3 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v3_110_000 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_110_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_110_001 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 164 := by
  rw [st_110_001]; simp only [v2_001_000, v2_001_001, v2_001_010, v2_001_100, v2_001_101, v2_001_110]

lemma v3_110_010 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 43 := by
  rw [st_110_010]; simp only [v2_010_000]

lemma v3_110_011 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v3_110_100 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 75 := by
  rw [st_110_100]; simp only [v2_100_000, v2_100_001]

lemma v3_110_101 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 74 := by
  rw [st_110_101]; simp only [v2_101_000, v2_101_001]

lemma v3_110_110 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v3_110_111 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v3_111_000 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_111_000]; simp only [v2_000_000, v2_000_001, v2_000_010, v2_000_011, v2_000_100, v2_000_101, v2_000_110, v2_000_111]

lemma v3_111_001 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 75 := by
  rw [st_111_001]; simp only [v2_001_000, v2_001_100]

lemma v3_111_010 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v3_111_011 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v3_111_100 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 75 := by
  rw [st_111_100]; simp only [v2_100_000, v2_100_001]

lemma v3_111_101 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 43 := by
  rw [st_111_101]; simp only [v2_101_000]

lemma v3_111_110 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v3_111_111 : F 3 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v4_n_000 : F 4 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_n_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_n_001 : F 4 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 896 := by
  rw [st_n_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_011, v3_001_100, v3_001_101, v3_001_110, v3_001_111]

lemma v4_n_010 : F 4 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 888 := by
  rw [st_n_010]; simp only [v3_010_000, v3_010_001, v3_010_010, v3_010_011, v3_010_100, v3_010_101, v3_010_110]

lemma v4_n_011 : F 4 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 488 := by
  rw [st_n_011]; simp only [v3_011_000, v3_011_001, v3_011_010, v3_011_100]

lemma v4_n_100 : F 4 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 896 := by
  rw [st_n_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101, v3_100_110, v3_100_111]

lemma v4_n_101 : F 4 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_n_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_011, v3_101_100, v3_101_101, v3_101_110, v3_101_111]

lemma v4_n_110 : F 4 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 488 := by
  rw [st_n_110]; simp only [v3_110_000, v3_110_001, v3_110_010, v3_110_100]

lemma v4_n_111 : F 4 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_n_111]; simp only [v3_111_000]

lemma v4_000_000 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_000_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_000_001 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 896 := by
  rw [st_000_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_011, v3_001_100, v3_001_101, v3_001_110, v3_001_111]

lemma v4_000_010 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 888 := by
  rw [st_000_010]; simp only [v3_010_000, v3_010_001, v3_010_010, v3_010_011, v3_010_100, v3_010_101, v3_010_110]

lemma v4_000_011 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 488 := by
  rw [st_000_011]; simp only [v3_011_000, v3_011_001, v3_011_010, v3_011_100]

lemma v4_000_100 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 896 := by
  rw [st_000_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101, v3_100_110, v3_100_111]

lemma v4_000_101 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_000_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_011, v3_101_100, v3_101_101, v3_101_110, v3_101_111]

lemma v4_000_110 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 488 := by
  rw [st_000_110]; simp only [v3_110_000, v3_110_001, v3_110_010, v3_110_100]

lemma v4_000_111 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_000_111]; simp only [v3_111_000]

lemma v4_001_000 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_001_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_001_001 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 853 := by
  rw [st_001_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_100, v3_001_101, v3_001_110]

lemma v4_001_010 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 663 := by
  rw [st_001_010]; simp only [v3_010_000, v3_010_001, v3_010_010, v3_010_100]

lemma v4_001_011 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_001_011]; simp only [v3_011_000]

lemma v4_001_100 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 896 := by
  rw [st_001_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101, v3_100_110, v3_100_111]

lemma v4_001_101 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_001_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_100, v3_101_101, v3_101_110]

lemma v4_001_110 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_001_110]; simp only [v3_110_000]

lemma v4_001_111 : F 4 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v4_010_000 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_010_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_010_001 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 853 := by
  rw [st_010_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_100, v3_001_101, v3_001_110]

lemma v4_010_010 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 663 := by
  rw [st_010_010]; simp only [v3_010_000, v3_010_001, v3_010_010, v3_010_100]

lemma v4_010_011 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_010_011]; simp only [v3_011_000]

lemma v4_010_100 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 853 := by
  rw [st_010_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101]

lemma v4_010_101 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_010_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_100, v3_101_101]

lemma v4_010_110 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_010_110]; simp only [v3_110_000]

lemma v4_010_111 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v4_011_000 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_011_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_011_001 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 378 := by
  rw [st_011_001]; simp only [v3_001_000, v3_001_100]

lemma v4_011_010 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_011_010]; simp only [v3_010_000]

lemma v4_011_011 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v4_011_100 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 853 := by
  rw [st_011_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101]

lemma v4_011_101 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 370 := by
  rw [st_011_101]; simp only [v3_101_000, v3_101_100]

lemma v4_011_110 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v4_011_111 : F 4 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v4_100_000 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_100_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_100_001 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 896 := by
  rw [st_100_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_011, v3_001_100, v3_001_101, v3_001_110, v3_001_111]

lemma v4_100_010 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 663 := by
  rw [st_100_010]; simp only [v3_010_000, v3_010_001, v3_010_010, v3_010_100]

lemma v4_100_011 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_100_011]; simp only [v3_011_000]

lemma v4_100_100 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 853 := by
  rw [st_100_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101]

lemma v4_100_101 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_100_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_011, v3_101_100, v3_101_101]

lemma v4_100_110 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_100_110]; simp only [v3_110_000]

lemma v4_100_111 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v4_101_000 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_101_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_101_001 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 853 := by
  rw [st_101_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_100, v3_001_101, v3_001_110]

lemma v4_101_010 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_101_010]; simp only [v3_010_000]

lemma v4_101_011 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v4_101_100 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 853 := by
  rw [st_101_100]; simp only [v3_100_000, v3_100_001, v3_100_010, v3_100_011, v3_100_100, v3_100_101]

lemma v4_101_101 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 716 := by
  rw [st_101_101]; simp only [v3_101_000, v3_101_001, v3_101_010, v3_101_100, v3_101_101]

lemma v4_101_110 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v4_101_111 : F 4 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v4_110_000 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_110_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_110_001 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 853 := by
  rw [st_110_001]; simp only [v3_001_000, v3_001_001, v3_001_010, v3_001_100, v3_001_101, v3_001_110]

lemma v4_110_010 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 206 := by
  rw [st_110_010]; simp only [v3_010_000]

lemma v4_110_011 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v4_110_100 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 378 := by
  rw [st_110_100]; simp only [v3_100_000, v3_100_001]

lemma v4_110_101 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 370 := by
  rw [st_110_101]; simp only [v3_101_000, v3_101_001]

lemma v4_110_110 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v4_110_111 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v4_111_000 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_111_000]; simp only [v3_000_000, v3_000_001, v3_000_010, v3_000_011, v3_000_100, v3_000_101, v3_000_110, v3_000_111]

lemma v4_111_001 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 378 := by
  rw [st_111_001]; simp only [v3_001_000, v3_001_100]

lemma v4_111_010 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v4_111_011 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v4_111_100 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 378 := by
  rw [st_111_100]; simp only [v3_100_000, v3_100_001]

lemma v4_111_101 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 206 := by
  rw [st_111_101]; simp only [v3_101_000]

lemma v4_111_110 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v4_111_111 : F 4 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v5_n_000 : F 5 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_n_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_n_001 : F 5 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4637 := by
  rw [st_n_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_011, v4_001_100, v4_001_101, v4_001_110, v4_001_111]

lemma v5_n_010 : F 5 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4594 := by
  rw [st_n_010]; simp only [v4_010_000, v4_010_001, v4_010_010, v4_010_011, v4_010_100, v4_010_101, v4_010_110]

lemma v5_n_011 : F 5 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 2534 := by
  rw [st_n_011]; simp only [v4_011_000, v4_011_001, v4_011_010, v4_011_100]

lemma v5_n_100 : F 5 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4637 := by
  rw [st_n_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101, v4_100_110, v4_100_111]

lemma v5_n_101 : F 5 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_n_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_011, v4_101_100, v4_101_101, v4_101_110, v4_101_111]

lemma v5_n_110 : F 5 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 2534 := by
  rw [st_n_110]; simp only [v4_110_000, v4_110_001, v4_110_010, v4_110_100]

lemma v5_n_111 : F 5 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_n_111]; simp only [v4_111_000]

lemma v5_000_000 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_000_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_000_001 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4637 := by
  rw [st_000_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_011, v4_001_100, v4_001_101, v4_001_110, v4_001_111]

lemma v5_000_010 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 4594 := by
  rw [st_000_010]; simp only [v4_010_000, v4_010_001, v4_010_010, v4_010_011, v4_010_100, v4_010_101, v4_010_110]

lemma v5_000_011 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 2534 := by
  rw [st_000_011]; simp only [v4_011_000, v4_011_001, v4_011_010, v4_011_100]

lemma v5_000_100 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4637 := by
  rw [st_000_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101, v4_100_110, v4_100_111]

lemma v5_000_101 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_000_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_011, v4_101_100, v4_101_101, v4_101_110, v4_101_111]

lemma v5_000_110 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 2534 := by
  rw [st_000_110]; simp only [v4_110_000, v4_110_001, v4_110_010, v4_110_100]

lemma v5_000_111 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_000_111]; simp only [v4_111_000]

lemma v5_001_000 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_001_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_001_001 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4431 := by
  rw [st_001_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_100, v4_001_101, v4_001_110]

lemma v5_001_010 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 3466 := by
  rw [st_001_010]; simp only [v4_010_000, v4_010_001, v4_010_010, v4_010_100]

lemma v5_001_011 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_001_011]; simp only [v4_011_000]

lemma v5_001_100 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4637 := by
  rw [st_001_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101, v4_100_110, v4_100_111]

lemma v5_001_101 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_001_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_100, v4_101_101, v4_101_110]

lemma v5_001_110 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_001_110]; simp only [v4_110_000]

lemma v5_001_111 : F 5 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v5_010_000 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_010_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_010_001 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4431 := by
  rw [st_010_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_100, v4_001_101, v4_001_110]

lemma v5_010_010 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 3466 := by
  rw [st_010_010]; simp only [v4_010_000, v4_010_001, v4_010_010, v4_010_100]

lemma v5_010_011 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_010_011]; simp only [v4_011_000]

lemma v5_010_100 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4431 := by
  rw [st_010_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101]

lemma v5_010_101 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_010_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_100, v4_101_101]

lemma v5_010_110 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_010_110]; simp only [v4_110_000]

lemma v5_010_111 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v5_011_000 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_011_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_011_001 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1993 := by
  rw [st_011_001]; simp only [v4_001_000, v4_001_100]

lemma v5_011_010 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_011_010]; simp only [v4_010_000]

lemma v5_011_011 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v5_011_100 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4431 := by
  rw [st_011_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101]

lemma v5_011_101 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1950 := by
  rw [st_011_101]; simp only [v4_101_000, v4_101_100]

lemma v5_011_110 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v5_011_111 : F 5 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v5_100_000 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_100_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_100_001 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4637 := by
  rw [st_100_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_011, v4_001_100, v4_001_101, v4_001_110, v4_001_111]

lemma v5_100_010 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 3466 := by
  rw [st_100_010]; simp only [v4_010_000, v4_010_001, v4_010_010, v4_010_100]

lemma v5_100_011 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_100_011]; simp only [v4_011_000]

lemma v5_100_100 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4431 := by
  rw [st_100_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101]

lemma v5_100_101 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_100_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_011, v4_101_100, v4_101_101]

lemma v5_100_110 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_100_110]; simp only [v4_110_000]

lemma v5_100_111 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v5_101_000 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_101_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_101_001 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4431 := by
  rw [st_101_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_100, v4_001_101, v4_001_110]

lemma v5_101_010 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_101_010]; simp only [v4_010_000]

lemma v5_101_011 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v5_101_100 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 4431 := by
  rw [st_101_100]; simp only [v4_100_000, v4_100_001, v4_100_010, v4_100_011, v4_100_100, v4_100_101]

lemma v5_101_101 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 3725 := by
  rw [st_101_101]; simp only [v4_101_000, v4_101_001, v4_101_010, v4_101_100, v4_101_101]

lemma v5_101_110 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v5_101_111 : F 5 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v5_110_000 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_110_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_110_001 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 4431 := by
  rw [st_110_001]; simp only [v4_001_000, v4_001_001, v4_001_010, v4_001_100, v4_001_101, v4_001_110]

lemma v5_110_010 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 1097 := by
  rw [st_110_010]; simp only [v4_010_000]

lemma v5_110_011 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v5_110_100 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1993 := by
  rw [st_110_100]; simp only [v4_100_000, v4_100_001]

lemma v5_110_101 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1950 := by
  rw [st_110_101]; simp only [v4_101_000, v4_101_001]

lemma v5_110_110 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v5_110_111 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v5_111_000 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_111_000]; simp only [v4_000_000, v4_000_001, v4_000_010, v4_000_011, v4_000_100, v4_000_101, v4_000_110, v4_000_111]

lemma v5_111_001 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1993 := by
  rw [st_111_001]; simp only [v4_001_000, v4_001_100]

lemma v5_111_010 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v5_111_011 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v5_111_100 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 1993 := by
  rw [st_111_100]; simp only [v4_100_000, v4_100_001]

lemma v5_111_101 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 1097 := by
  rw [st_111_101]; simp only [v4_101_000]

lemma v5_111_110 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v5_111_111 : F 5 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v6_n_000 : F 6 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_n_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_n_001 : F 6 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 24128 := by
  rw [st_n_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_011, v5_001_100, v5_001_101, v5_001_110, v5_001_111]

lemma v6_n_010 : F 6 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 23922 := by
  rw [st_n_010]; simp only [v5_010_000, v5_010_001, v5_010_010, v5_010_011, v5_010_100, v5_010_101, v5_010_110]

lemma v6_n_011 : F 6 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 13196 := by
  rw [st_n_011]; simp only [v5_011_000, v5_011_001, v5_011_010, v5_011_100]

lemma v6_n_100 : F 6 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 24128 := by
  rw [st_n_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101, v5_100_110, v5_100_111]

lemma v6_n_101 : F 6 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_n_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_011, v5_101_100, v5_101_101, v5_101_110, v5_101_111]

lemma v6_n_110 : F 6 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 13196 := by
  rw [st_n_110]; simp only [v5_110_000, v5_110_001, v5_110_010, v5_110_100]

lemma v6_n_111 : F 6 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_n_111]; simp only [v5_111_000]

lemma v6_000_000 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_000_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_000_001 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 24128 := by
  rw [st_000_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_011, v5_001_100, v5_001_101, v5_001_110, v5_001_111]

lemma v6_000_010 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 23922 := by
  rw [st_000_010]; simp only [v5_010_000, v5_010_001, v5_010_010, v5_010_011, v5_010_100, v5_010_101, v5_010_110]

lemma v6_000_011 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 13196 := by
  rw [st_000_011]; simp only [v5_011_000, v5_011_001, v5_011_010, v5_011_100]

lemma v6_000_100 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 24128 := by
  rw [st_000_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101, v5_100_110, v5_100_111]

lemma v6_000_101 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_000_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_011, v5_101_100, v5_101_101, v5_101_110, v5_101_111]

lemma v6_000_110 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 13196 := by
  rw [st_000_110]; simp only [v5_110_000, v5_110_001, v5_110_010, v5_110_100]

lemma v6_000_111 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_000_111]; simp only [v5_111_000]

lemma v6_001_000 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_001_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_001_001 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 23031 := by
  rw [st_001_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_100, v5_001_101, v5_001_110]

lemma v6_001_010 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 18003 := by
  rw [st_001_010]; simp only [v5_010_000, v5_010_001, v5_010_010, v5_010_100]

lemma v6_001_011 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_001_011]; simp only [v5_011_000]

lemma v6_001_100 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 24128 := by
  rw [st_001_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101, v5_100_110, v5_100_111]

lemma v6_001_101 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_001_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_100, v5_101_101, v5_101_110]

lemma v6_001_110 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_001_110]; simp only [v5_110_000]

lemma v6_001_111 : F 6 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v6_010_000 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_010_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_010_001 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 23031 := by
  rw [st_010_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_100, v5_001_101, v5_001_110]

lemma v6_010_010 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 18003 := by
  rw [st_010_010]; simp only [v5_010_000, v5_010_001, v5_010_010, v5_010_100]

lemma v6_010_011 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_010_011]; simp only [v5_011_000]

lemma v6_010_100 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 23031 := by
  rw [st_010_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101]

lemma v6_010_101 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_010_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_100, v5_101_101]

lemma v6_010_110 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_010_110]; simp only [v5_110_000]

lemma v6_010_111 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v6_011_000 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_011_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_011_001 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 10312 := by
  rw [st_011_001]; simp only [v5_001_000, v5_001_100]

lemma v6_011_010 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_011_010]; simp only [v5_010_000]

lemma v6_011_011 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v6_011_100 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 23031 := by
  rw [st_011_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101]

lemma v6_011_101 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 10106 := by
  rw [st_011_101]; simp only [v5_101_000, v5_101_100]

lemma v6_011_110 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v6_011_111 : F 6 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v6_100_000 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_100_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_100_001 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 24128 := by
  rw [st_100_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_011, v5_001_100, v5_001_101, v5_001_110, v5_001_111]

lemma v6_100_010 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 18003 := by
  rw [st_100_010]; simp only [v5_010_000, v5_010_001, v5_010_010, v5_010_100]

lemma v6_100_011 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_100_011]; simp only [v5_011_000]

lemma v6_100_100 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 23031 := by
  rw [st_100_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101]

lemma v6_100_101 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_100_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_011, v5_101_100, v5_101_101]

lemma v6_100_110 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_100_110]; simp only [v5_110_000]

lemma v6_100_111 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v6_101_000 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_101_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_101_001 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 23031 := by
  rw [st_101_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_100, v5_001_101, v5_001_110]

lemma v6_101_010 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_101_010]; simp only [v5_010_000]

lemma v6_101_011 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v6_101_100 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 23031 := by
  rw [st_101_100]; simp only [v5_100_000, v5_100_001, v5_100_010, v5_100_011, v5_100_100, v5_100_101]

lemma v6_101_101 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 19359 := by
  rw [st_101_101]; simp only [v5_101_000, v5_101_001, v5_101_010, v5_101_100, v5_101_101]

lemma v6_101_110 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v6_101_111 : F 6 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v6_110_000 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_110_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_110_001 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 23031 := by
  rw [st_110_001]; simp only [v5_001_000, v5_001_001, v5_001_010, v5_001_100, v5_001_101, v5_001_110]

lemma v6_110_010 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 5675 := by
  rw [st_110_010]; simp only [v5_010_000]

lemma v6_110_011 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v6_110_100 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 10312 := by
  rw [st_110_100]; simp only [v5_100_000, v5_100_001]

lemma v6_110_101 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 10106 := by
  rw [st_110_101]; simp only [v5_101_000, v5_101_001]

lemma v6_110_110 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v6_110_111 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v6_111_000 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_111_000]; simp only [v5_000_000, v5_000_001, v5_000_010, v5_000_011, v5_000_100, v5_000_101, v5_000_110, v5_000_111]

lemma v6_111_001 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 10312 := by
  rw [st_111_001]; simp only [v5_001_000, v5_001_100]

lemma v6_111_010 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v6_111_011 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v6_111_100 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 10312 := by
  rw [st_111_100]; simp only [v5_100_000, v5_100_001]

lemma v6_111_101 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 5675 := by
  rw [st_111_101]; simp only [v5_101_000]

lemma v6_111_110 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v6_111_111 : F 6 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v7_n_000 : F 7 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_n_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_n_001 : F 7 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 125304 := by
  rw [st_n_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_011, v6_001_100, v6_001_101, v6_001_110, v6_001_111]

lemma v7_n_010 : F 7 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 124207 := by
  rw [st_n_010]; simp only [v6_010_000, v6_010_001, v6_010_010, v6_010_011, v6_010_100, v6_010_101, v6_010_110]

lemma v7_n_011 : F 7 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 68451 := by
  rw [st_n_011]; simp only [v6_011_000, v6_011_001, v6_011_010, v6_011_100]

lemma v7_n_100 : F 7 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 125304 := by
  rw [st_n_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101, v6_100_110, v6_100_111]

lemma v7_n_101 : F 7 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_n_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_011, v6_101_100, v6_101_101, v6_101_110, v6_101_111]

lemma v7_n_110 : F 7 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 68451 := by
  rw [st_n_110]; simp only [v6_110_000, v6_110_001, v6_110_010, v6_110_100]

lemma v7_n_111 : F 7 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_n_111]; simp only [v6_111_000]

lemma v7_000_000 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_000_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_000_001 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 125304 := by
  rw [st_000_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_011, v6_001_100, v6_001_101, v6_001_110, v6_001_111]

lemma v7_000_010 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 124207 := by
  rw [st_000_010]; simp only [v6_010_000, v6_010_001, v6_010_010, v6_010_011, v6_010_100, v6_010_101, v6_010_110]

lemma v7_000_011 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 68451 := by
  rw [st_000_011]; simp only [v6_011_000, v6_011_001, v6_011_010, v6_011_100]

lemma v7_000_100 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 125304 := by
  rw [st_000_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101, v6_100_110, v6_100_111]

lemma v7_000_101 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_000_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_011, v6_101_100, v6_101_101, v6_101_110, v6_101_111]

lemma v7_000_110 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 68451 := by
  rw [st_000_110]; simp only [v6_110_000, v6_110_001, v6_110_010, v6_110_100]

lemma v7_000_111 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_000_111]; simp only [v6_111_000]

lemma v7_001_000 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_001_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_001_001 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 119629 := by
  rw [st_001_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_100, v6_001_101, v6_001_110]

lemma v7_001_010 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 93498 := by
  rw [st_001_010]; simp only [v6_010_000, v6_010_001, v6_010_010, v6_010_100]

lemma v7_001_011 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_001_011]; simp only [v6_011_000]

lemma v7_001_100 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 125304 := by
  rw [st_001_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101, v6_100_110, v6_100_111]

lemma v7_001_101 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_001_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_100, v6_101_101, v6_101_110]

lemma v7_001_110 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_001_110]; simp only [v6_110_000]

lemma v7_001_111 : F 7 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v7_010_000 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_010_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_010_001 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 119629 := by
  rw [st_010_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_100, v6_001_101, v6_001_110]

lemma v7_010_010 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 93498 := by
  rw [st_010_010]; simp only [v6_010_000, v6_010_001, v6_010_010, v6_010_100]

lemma v7_010_011 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_010_011]; simp only [v6_011_000]

lemma v7_010_100 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 119629 := by
  rw [st_010_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101]

lemma v7_010_101 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_010_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_100, v6_101_101]

lemma v7_010_110 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_010_110]; simp only [v6_110_000]

lemma v7_010_111 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v7_011_000 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_011_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_011_001 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 53561 := by
  rw [st_011_001]; simp only [v6_001_000, v6_001_100]

lemma v7_011_010 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_011_010]; simp only [v6_010_000]

lemma v7_011_011 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v7_011_100 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 119629 := by
  rw [st_011_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101]

lemma v7_011_101 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 52464 := by
  rw [st_011_101]; simp only [v6_101_000, v6_101_100]

lemma v7_011_110 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v7_011_111 : F 7 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v7_100_000 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_100_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_100_001 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 125304 := by
  rw [st_100_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_011, v6_001_100, v6_001_101, v6_001_110, v6_001_111]

lemma v7_100_010 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 93498 := by
  rw [st_100_010]; simp only [v6_010_000, v6_010_001, v6_010_010, v6_010_100]

lemma v7_100_011 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_100_011]; simp only [v6_011_000]

lemma v7_100_100 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 119629 := by
  rw [st_100_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101]

lemma v7_100_101 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_100_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_011, v6_101_100, v6_101_101]

lemma v7_100_110 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_100_110]; simp only [v6_110_000]

lemma v7_100_111 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v7_101_000 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_101_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_101_001 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 119629 := by
  rw [st_101_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_100, v6_001_101, v6_001_110]

lemma v7_101_010 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_101_010]; simp only [v6_010_000]

lemma v7_101_011 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v7_101_100 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 119629 := by
  rw [st_101_100]; simp only [v6_100_000, v6_100_001, v6_100_010, v6_100_011, v6_100_100, v6_100_101]

lemma v7_101_101 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 100529 := by
  rw [st_101_101]; simp only [v6_101_000, v6_101_001, v6_101_010, v6_101_100, v6_101_101]

lemma v7_101_110 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v7_101_111 : F 7 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v7_110_000 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_110_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_110_001 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 119629 := by
  rw [st_110_001]; simp only [v6_001_000, v6_001_001, v6_001_010, v6_001_100, v6_001_101, v6_001_110]

lemma v7_110_010 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 29433 := by
  rw [st_110_010]; simp only [v6_010_000]

lemma v7_110_011 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v7_110_100 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 53561 := by
  rw [st_110_100]; simp only [v6_100_000, v6_100_001]

lemma v7_110_101 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 52464 := by
  rw [st_110_101]; simp only [v6_101_000, v6_101_001]

lemma v7_110_110 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v7_110_111 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v7_111_000 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_111_000]; simp only [v6_000_000, v6_000_001, v6_000_010, v6_000_011, v6_000_100, v6_000_101, v6_000_110, v6_000_111]

lemma v7_111_001 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 53561 := by
  rw [st_111_001]; simp only [v6_001_000, v6_001_100]

lemma v7_111_010 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v7_111_011 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v7_111_100 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 53561 := by
  rw [st_111_100]; simp only [v6_100_000, v6_100_001]

lemma v7_111_101 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 29433 := by
  rw [st_111_101]; simp only [v6_101_000]

lemma v7_111_110 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v7_111_111 : F 7 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

lemma v8_n_000 : F 8 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_n_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_n_001 : F 8 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 650863 := by
  rw [st_n_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_011, v7_001_100, v7_001_101, v7_001_110, v7_001_111]

lemma v8_n_010 : F 8 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 645188 := by
  rw [st_n_010]; simp only [v7_010_000, v7_010_001, v7_010_010, v7_010_011, v7_010_100, v7_010_101, v7_010_110]

lemma v8_n_011 : F 8 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 355660 := by
  rw [st_n_011]; simp only [v7_011_000, v7_011_001, v7_011_010, v7_011_100]

lemma v8_n_100 : F 8 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 650863 := by
  rw [st_n_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101, v7_100_110, v7_100_111]

lemma v8_n_101 : F 8 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_n_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_011, v7_101_100, v7_101_101, v7_101_110, v7_101_111]

lemma v8_n_110 : F 8 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 355660 := by
  rw [st_n_110]; simp only [v7_110_000, v7_110_001, v7_110_010, v7_110_100]

lemma v8_n_111 : F 8 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_n_111]; simp only [v7_111_000]

lemma v8_000_000 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_000_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_000_001 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 650863 := by
  rw [st_000_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_011, v7_001_100, v7_001_101, v7_001_110, v7_001_111]

lemma v8_000_010 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 645188 := by
  rw [st_000_010]; simp only [v7_010_000, v7_010_001, v7_010_010, v7_010_011, v7_010_100, v7_010_101, v7_010_110]

lemma v8_000_011 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 355660 := by
  rw [st_000_011]; simp only [v7_011_000, v7_011_001, v7_011_010, v7_011_100]

lemma v8_000_100 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 650863 := by
  rw [st_000_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101, v7_100_110, v7_100_111]

lemma v8_000_101 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_000_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_011, v7_101_100, v7_101_101, v7_101_110, v7_101_111]

lemma v8_000_110 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 355660 := by
  rw [st_000_110]; simp only [v7_110_000, v7_110_001, v7_110_010, v7_110_100]

lemma v8_000_111 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_000_111]; simp only [v7_111_000]

lemma v8_001_000 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_001_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_001_001 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 621430 := by
  rw [st_001_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_100, v7_001_101, v7_001_110]

lemma v8_001_010 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 485793 := by
  rw [st_001_010]; simp only [v7_010_000, v7_010_001, v7_010_010, v7_010_100]

lemma v8_001_011 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_001_011]; simp only [v7_011_000]

lemma v8_001_100 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 650863 := by
  rw [st_001_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101, v7_100_110, v7_100_111]

lemma v8_001_101 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_001_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_100, v7_101_101, v7_101_110]

lemma v8_001_110 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_001_110]; simp only [v7_110_000]

lemma v8_001_111 : F 8 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_001_111]

lemma v8_010_000 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_010_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_010_001 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 621430 := by
  rw [st_010_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_100, v7_001_101, v7_001_110]

lemma v8_010_010 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 485793 := by
  rw [st_010_010]; simp only [v7_010_000, v7_010_001, v7_010_010, v7_010_100]

lemma v8_010_011 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_010_011]; simp only [v7_011_000]

lemma v8_010_100 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 621430 := by
  rw [st_010_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101]

lemma v8_010_101 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_010_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_100, v7_101_101]

lemma v8_010_110 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_010_110]; simp only [v7_110_000]

lemma v8_010_111 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_010_111]

lemma v8_011_000 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_011_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_011_001 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 278341 := by
  rw [st_011_001]; simp only [v7_001_000, v7_001_100]

lemma v8_011_010 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_011_010]; simp only [v7_010_000]

lemma v8_011_011 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_011]

lemma v8_011_100 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 621430 := by
  rw [st_011_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101]

lemma v8_011_101 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 272666 := by
  rw [st_011_101]; simp only [v7_101_000, v7_101_100]

lemma v8_011_110 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_011_110]

lemma v8_011_111 : F 8 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_011_111]

lemma v8_100_000 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_100_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_100_001 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 650863 := by
  rw [st_100_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_011, v7_001_100, v7_001_101, v7_001_110, v7_001_111]

lemma v8_100_010 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 485793 := by
  rw [st_100_010]; simp only [v7_010_000, v7_010_001, v7_010_010, v7_010_100]

lemma v8_100_011 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_100_011]; simp only [v7_011_000]

lemma v8_100_100 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 621430 := by
  rw [st_100_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101]

lemma v8_100_101 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_100_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_011, v7_101_100, v7_101_101]

lemma v8_100_110 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_100_110]; simp only [v7_110_000]

lemma v8_100_111 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_100_111]

lemma v8_101_000 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_101_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_101_001 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 621430 := by
  rw [st_101_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_100, v7_001_101, v7_001_110]

lemma v8_101_010 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_101_010]; simp only [v7_010_000]

lemma v8_101_011 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_011]

lemma v8_101_100 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 621430 := by
  rw [st_101_100]; simp only [v7_100_000, v7_100_001, v7_100_010, v7_100_011, v7_100_100, v7_100_101]

lemma v8_101_101 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 522257 := by
  rw [st_101_101]; simp only [v7_101_000, v7_101_001, v7_101_010, v7_101_100, v7_101_101]

lemma v8_101_110 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_101_110]

lemma v8_101_111 : F 8 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_101_111]

lemma v8_110_000 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_110_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_110_001 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 621430 := by
  rw [st_110_001]; simp only [v7_001_000, v7_001_001, v7_001_010, v7_001_100, v7_001_101, v7_001_110]

lemma v8_110_010 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 153037 := by
  rw [st_110_010]; simp only [v7_010_000]

lemma v8_110_011 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_011]

lemma v8_110_100 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 278341 := by
  rw [st_110_100]; simp only [v7_100_000, v7_100_001]

lemma v8_110_101 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 272666 := by
  rw [st_110_101]; simp only [v7_101_000, v7_101_001]

lemma v8_110_110 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_110_110]

lemma v8_110_111 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_110_111]

lemma v8_111_000 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 794716 := by
  rw [st_111_000]; simp only [v7_000_000, v7_000_001, v7_000_010, v7_000_011, v7_000_100, v7_000_101, v7_000_110, v7_000_111]

lemma v8_111_001 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 278341 := by
  rw [st_111_001]; simp only [v7_001_000, v7_001_100]

lemma v8_111_010 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_010]

lemma v8_111_011 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_011]

lemma v8_111_100 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 278341 := by
  rw [st_111_100]; simp only [v7_100_000, v7_100_001]

lemma v8_111_101 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 153037 := by
  rw [st_111_101]; simp only [v7_101_000]

lemma v8_111_110 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  rw [st_111_110]

lemma v8_111_111 : F 8 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  rw [st_111_111]

/-- The defect of the recurrence for the counts from a given state. -/
def D (m : ℕ) (p : Option R) (r : R) : ℤ := (F (m + 8) p r : ℤ) - ((5 : ℤ) * (F (m + 7) p r : ℤ) + (2 : ℤ) * (F (m + 6) p r : ℤ) + (-1 : ℤ) * (F (m + 5) p r : ℤ) + (-24 : ℤ) * (F (m + 4) p r : ℤ) + (13 : ℤ) * (F (m + 3) p r : ℤ) + (0 : ℤ) * (F (m + 2) p r : ℤ) + (-2 : ℤ) * (F (m + 1) p r : ℤ) + (6 : ℤ) * (F (m + 0) p r : ℤ))

lemma D_succ (m : ℕ) (p : Option R) (r : R) :
    D (m + 1) p r = ∑ s : R, if W p r (some s) then D m (some r) s else 0 := by
  unfold D
  rw [show m + 1 + 0 = (m + 0) + 1 by omega, show m + 1 + 1 = (m + 1) + 1 by omega, show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega]
  rw [F_succ (m + 0), F_succ (m + 1), F_succ (m + 2), F_succ (m + 3), F_succ (m + 4), F_succ (m + 5), F_succ (m + 6), F_succ (m + 7), F_succ (m + 8)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

lemma d0_n_000 : D 0 none ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_000, v1_n_000, v2_n_000, v3_n_000, v4_n_000, v5_n_000, v6_n_000, v7_n_000, v8_n_000]; norm_num

lemma d0_n_001 : D 0 none ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_001, v1_n_001, v2_n_001, v3_n_001, v4_n_001, v5_n_001, v6_n_001, v7_n_001, v8_n_001]; norm_num

lemma d0_n_010 : D 0 none ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_010, v1_n_010, v2_n_010, v3_n_010, v4_n_010, v5_n_010, v6_n_010, v7_n_010, v8_n_010]; norm_num

lemma d0_n_011 : D 0 none ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_011, v1_n_011, v2_n_011, v3_n_011, v4_n_011, v5_n_011, v6_n_011, v7_n_011, v8_n_011]; norm_num

lemma d0_n_100 : D 0 none ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_100, v1_n_100, v2_n_100, v3_n_100, v4_n_100, v5_n_100, v6_n_100, v7_n_100, v8_n_100]; norm_num

lemma d0_n_101 : D 0 none ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_101, v1_n_101, v2_n_101, v3_n_101, v4_n_101, v5_n_101, v6_n_101, v7_n_101, v8_n_101]; norm_num

lemma d0_n_110 : D 0 none ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_110, v1_n_110, v2_n_110, v3_n_110, v4_n_110, v5_n_110, v6_n_110, v7_n_110, v8_n_110]; norm_num

lemma d0_n_111 : D 0 none ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_n_111, v1_n_111, v2_n_111, v3_n_111, v4_n_111, v5_n_111, v6_n_111, v7_n_111, v8_n_111]; norm_num

lemma d0_000_000 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_000, v1_000_000, v2_000_000, v3_000_000, v4_000_000, v5_000_000, v6_000_000, v7_000_000, v8_000_000]; norm_num

lemma d0_000_001 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_001, v1_000_001, v2_000_001, v3_000_001, v4_000_001, v5_000_001, v6_000_001, v7_000_001, v8_000_001]; norm_num

lemma d0_000_010 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_010, v1_000_010, v2_000_010, v3_000_010, v4_000_010, v5_000_010, v6_000_010, v7_000_010, v8_000_010]; norm_num

lemma d0_000_011 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_011, v1_000_011, v2_000_011, v3_000_011, v4_000_011, v5_000_011, v6_000_011, v7_000_011, v8_000_011]; norm_num

lemma d0_000_100 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_100, v1_000_100, v2_000_100, v3_000_100, v4_000_100, v5_000_100, v6_000_100, v7_000_100, v8_000_100]; norm_num

lemma d0_000_101 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_101, v1_000_101, v2_000_101, v3_000_101, v4_000_101, v5_000_101, v6_000_101, v7_000_101, v8_000_101]; norm_num

lemma d0_000_110 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_110, v1_000_110, v2_000_110, v3_000_110, v4_000_110, v5_000_110, v6_000_110, v7_000_110, v8_000_110]; norm_num

lemma d0_000_111 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_000_111, v1_000_111, v2_000_111, v3_000_111, v4_000_111, v5_000_111, v6_000_111, v7_000_111, v8_000_111]; norm_num

lemma d0_001_000 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_000, v1_001_000, v2_001_000, v3_001_000, v4_001_000, v5_001_000, v6_001_000, v7_001_000, v8_001_000]; norm_num

lemma d0_001_001 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_001, v1_001_001, v2_001_001, v3_001_001, v4_001_001, v5_001_001, v6_001_001, v7_001_001, v8_001_001]; norm_num

lemma d0_001_010 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_010, v1_001_010, v2_001_010, v3_001_010, v4_001_010, v5_001_010, v6_001_010, v7_001_010, v8_001_010]; norm_num

lemma d0_001_011 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_011, v1_001_011, v2_001_011, v3_001_011, v4_001_011, v5_001_011, v6_001_011, v7_001_011, v8_001_011]; norm_num

lemma d0_001_100 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_100, v1_001_100, v2_001_100, v3_001_100, v4_001_100, v5_001_100, v6_001_100, v7_001_100, v8_001_100]; norm_num

lemma d0_001_101 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_101, v1_001_101, v2_001_101, v3_001_101, v4_001_101, v5_001_101, v6_001_101, v7_001_101, v8_001_101]; norm_num

lemma d0_001_110 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_110, v1_001_110, v2_001_110, v3_001_110, v4_001_110, v5_001_110, v6_001_110, v7_001_110, v8_001_110]; norm_num

lemma d0_001_111 : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_001_111, v1_001_111, v2_001_111, v3_001_111, v4_001_111, v5_001_111, v6_001_111, v7_001_111, v8_001_111]; norm_num

lemma d0_010_000 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_000, v1_010_000, v2_010_000, v3_010_000, v4_010_000, v5_010_000, v6_010_000, v7_010_000, v8_010_000]; norm_num

lemma d0_010_001 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_001, v1_010_001, v2_010_001, v3_010_001, v4_010_001, v5_010_001, v6_010_001, v7_010_001, v8_010_001]; norm_num

lemma d0_010_010 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_010, v1_010_010, v2_010_010, v3_010_010, v4_010_010, v5_010_010, v6_010_010, v7_010_010, v8_010_010]; norm_num

lemma d0_010_011 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_011, v1_010_011, v2_010_011, v3_010_011, v4_010_011, v5_010_011, v6_010_011, v7_010_011, v8_010_011]; norm_num

lemma d0_010_100 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_100, v1_010_100, v2_010_100, v3_010_100, v4_010_100, v5_010_100, v6_010_100, v7_010_100, v8_010_100]; norm_num

lemma d0_010_101 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_101, v1_010_101, v2_010_101, v3_010_101, v4_010_101, v5_010_101, v6_010_101, v7_010_101, v8_010_101]; norm_num

lemma d0_010_110 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_110, v1_010_110, v2_010_110, v3_010_110, v4_010_110, v5_010_110, v6_010_110, v7_010_110, v8_010_110]; norm_num

lemma d0_010_111 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_010_111, v1_010_111, v2_010_111, v3_010_111, v4_010_111, v5_010_111, v6_010_111, v7_010_111, v8_010_111]; norm_num

lemma d0_011_000 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_000, v1_011_000, v2_011_000, v3_011_000, v4_011_000, v5_011_000, v6_011_000, v7_011_000, v8_011_000]; norm_num

lemma d0_011_001 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_001, v1_011_001, v2_011_001, v3_011_001, v4_011_001, v5_011_001, v6_011_001, v7_011_001, v8_011_001]; norm_num

lemma d0_011_010 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_010, v1_011_010, v2_011_010, v3_011_010, v4_011_010, v5_011_010, v6_011_010, v7_011_010, v8_011_010]; norm_num

lemma d0_011_011 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_011, v1_011_011, v2_011_011, v3_011_011, v4_011_011, v5_011_011, v6_011_011, v7_011_011, v8_011_011]; norm_num

lemma d0_011_100 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_100, v1_011_100, v2_011_100, v3_011_100, v4_011_100, v5_011_100, v6_011_100, v7_011_100, v8_011_100]; norm_num

lemma d0_011_101 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_101, v1_011_101, v2_011_101, v3_011_101, v4_011_101, v5_011_101, v6_011_101, v7_011_101, v8_011_101]; norm_num

lemma d0_011_110 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_110, v1_011_110, v2_011_110, v3_011_110, v4_011_110, v5_011_110, v6_011_110, v7_011_110, v8_011_110]; norm_num

lemma d0_011_111 : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_011_111, v1_011_111, v2_011_111, v3_011_111, v4_011_111, v5_011_111, v6_011_111, v7_011_111, v8_011_111]; norm_num

lemma d0_100_000 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_000, v1_100_000, v2_100_000, v3_100_000, v4_100_000, v5_100_000, v6_100_000, v7_100_000, v8_100_000]; norm_num

lemma d0_100_001 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_001, v1_100_001, v2_100_001, v3_100_001, v4_100_001, v5_100_001, v6_100_001, v7_100_001, v8_100_001]; norm_num

lemma d0_100_010 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_010, v1_100_010, v2_100_010, v3_100_010, v4_100_010, v5_100_010, v6_100_010, v7_100_010, v8_100_010]; norm_num

lemma d0_100_011 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_011, v1_100_011, v2_100_011, v3_100_011, v4_100_011, v5_100_011, v6_100_011, v7_100_011, v8_100_011]; norm_num

lemma d0_100_100 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_100, v1_100_100, v2_100_100, v3_100_100, v4_100_100, v5_100_100, v6_100_100, v7_100_100, v8_100_100]; norm_num

lemma d0_100_101 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_101, v1_100_101, v2_100_101, v3_100_101, v4_100_101, v5_100_101, v6_100_101, v7_100_101, v8_100_101]; norm_num

lemma d0_100_110 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_110, v1_100_110, v2_100_110, v3_100_110, v4_100_110, v5_100_110, v6_100_110, v7_100_110, v8_100_110]; norm_num

lemma d0_100_111 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_100_111, v1_100_111, v2_100_111, v3_100_111, v4_100_111, v5_100_111, v6_100_111, v7_100_111, v8_100_111]; norm_num

lemma d0_101_000 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_000, v1_101_000, v2_101_000, v3_101_000, v4_101_000, v5_101_000, v6_101_000, v7_101_000, v8_101_000]; norm_num

lemma d0_101_001 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_001, v1_101_001, v2_101_001, v3_101_001, v4_101_001, v5_101_001, v6_101_001, v7_101_001, v8_101_001]; norm_num

lemma d0_101_010 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_010, v1_101_010, v2_101_010, v3_101_010, v4_101_010, v5_101_010, v6_101_010, v7_101_010, v8_101_010]; norm_num

lemma d0_101_011 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_011, v1_101_011, v2_101_011, v3_101_011, v4_101_011, v5_101_011, v6_101_011, v7_101_011, v8_101_011]; norm_num

lemma d0_101_100 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_100, v1_101_100, v2_101_100, v3_101_100, v4_101_100, v5_101_100, v6_101_100, v7_101_100, v8_101_100]; norm_num

lemma d0_101_101 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_101, v1_101_101, v2_101_101, v3_101_101, v4_101_101, v5_101_101, v6_101_101, v7_101_101, v8_101_101]; norm_num

lemma d0_101_110 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_110, v1_101_110, v2_101_110, v3_101_110, v4_101_110, v5_101_110, v6_101_110, v7_101_110, v8_101_110]; norm_num

lemma d0_101_111 : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_101_111, v1_101_111, v2_101_111, v3_101_111, v4_101_111, v5_101_111, v6_101_111, v7_101_111, v8_101_111]; norm_num

lemma d0_110_000 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_000, v1_110_000, v2_110_000, v3_110_000, v4_110_000, v5_110_000, v6_110_000, v7_110_000, v8_110_000]; norm_num

lemma d0_110_001 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_001, v1_110_001, v2_110_001, v3_110_001, v4_110_001, v5_110_001, v6_110_001, v7_110_001, v8_110_001]; norm_num

lemma d0_110_010 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_010, v1_110_010, v2_110_010, v3_110_010, v4_110_010, v5_110_010, v6_110_010, v7_110_010, v8_110_010]; norm_num

lemma d0_110_011 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_011, v1_110_011, v2_110_011, v3_110_011, v4_110_011, v5_110_011, v6_110_011, v7_110_011, v8_110_011]; norm_num

lemma d0_110_100 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_100, v1_110_100, v2_110_100, v3_110_100, v4_110_100, v5_110_100, v6_110_100, v7_110_100, v8_110_100]; norm_num

lemma d0_110_101 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_101, v1_110_101, v2_110_101, v3_110_101, v4_110_101, v5_110_101, v6_110_101, v7_110_101, v8_110_101]; norm_num

lemma d0_110_110 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_110, v1_110_110, v2_110_110, v3_110_110, v4_110_110, v5_110_110, v6_110_110, v7_110_110, v8_110_110]; norm_num

lemma d0_110_111 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_110_111, v1_110_111, v2_110_111, v3_110_111, v4_110_111, v5_110_111, v6_110_111, v7_110_111, v8_110_111]; norm_num

lemma d0_111_000 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_000, v1_111_000, v2_111_000, v3_111_000, v4_111_000, v5_111_000, v6_111_000, v7_111_000, v8_111_000]; norm_num

lemma d0_111_001 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_001, v1_111_001, v2_111_001, v3_111_001, v4_111_001, v5_111_001, v6_111_001, v7_111_001, v8_111_001]; norm_num

lemma d0_111_010 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_010, v1_111_010, v2_111_010, v3_111_010, v4_111_010, v5_111_010, v6_111_010, v7_111_010, v8_111_010]; norm_num

lemma d0_111_011 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_011, v1_111_011, v2_111_011, v3_111_011, v4_111_011, v5_111_011, v6_111_011, v7_111_011, v8_111_011]; norm_num

lemma d0_111_100 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_100, v1_111_100, v2_111_100, v3_111_100, v4_111_100, v5_111_100, v6_111_100, v7_111_100, v8_111_100]; norm_num

lemma d0_111_101 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_101, v1_111_101, v2_111_101, v3_111_101, v4_111_101, v5_111_101, v6_111_101, v7_111_101, v8_111_101]; norm_num

lemma d0_111_110 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_110, v1_111_110, v2_111_110, v3_111_110, v4_111_110, v5_111_110, v6_111_110, v7_111_110, v8_111_110]; norm_num

lemma d0_111_111 : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] = 0 := by
  unfold D; simp only [zero_add, v0_111_111, v1_111_111, v2_111_111, v3_111_111, v4_111_111, v5_111_111, v6_111_111, v7_111_111, v8_111_111]; norm_num

lemma eR (q : R) : q = ![q 0, q 1, q 2] := by ext j; fin_cases j <;> rfl

lemma Dz_n (r : R) : D 0 none r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_n_000, d0_n_001, d0_n_010, d0_n_011, d0_n_100, d0_n_101, d0_n_110, d0_n_111]

lemma Dz_000 (r : R) : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_000_000, d0_000_001, d0_000_010, d0_000_011, d0_000_100, d0_000_101, d0_000_110, d0_000_111]

lemma Dz_001 (r : R) : D 0 (some ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_001_000, d0_001_001, d0_001_010, d0_001_011, d0_001_100, d0_001_101, d0_001_110, d0_001_111]

lemma Dz_010 (r : R) : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_010_000, d0_010_001, d0_010_010, d0_010_011, d0_010_100, d0_010_101, d0_010_110, d0_010_111]

lemma Dz_011 (r : R) : D 0 (some ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_011_000, d0_011_001, d0_011_010, d0_011_011, d0_011_100, d0_011_101, d0_011_110, d0_011_111]

lemma Dz_100 (r : R) : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_100_000, d0_100_001, d0_100_010, d0_100_011, d0_100_100, d0_100_101, d0_100_110, d0_100_111]

lemma Dz_101 (r : R) : D 0 (some ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_101_000, d0_101_001, d0_101_010, d0_101_011, d0_101_100, d0_101_101, d0_101_110, d0_101_111]

lemma Dz_110 (r : R) : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_110_000, d0_110_001, d0_110_010, d0_110_011, d0_110_100, d0_110_101, d0_110_110, d0_110_111]

lemma Dz_111 (r : R) : D 0 (some ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]) r = 0 := by
  rw [eR r]
  generalize r 0 = b0, r 1 = b1, r 2 = b2
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2
  exacts [d0_111_000, d0_111_001, d0_111_010, d0_111_011, d0_111_100, d0_111_101, d0_111_110, d0_111_111]

lemma D_zero (p : Option R) (r : R) : D 0 p r = 0 := by
  rcases p with _ | q
  · exact Dz_n r
  · rw [eR q]
    generalize q 0 = a0, q 1 = a1, q 2 = a2
    fin_cases a0 <;> fin_cases a1 <;> fin_cases a2
    exacts [Dz_000 r, Dz_001 r, Dz_010 r, Dz_011 r, Dz_100 r, Dz_101 r, Dz_110 r, Dz_111 r]

lemma D_all (m : ℕ) : ∀ p r, D m p r = 0 := by
  induction m with
  | zero => exact D_zero
  | succ m ih => intro p r; rw [D_succ]; simp only [ih, ite_self, Finset.sum_const_zero]

theorem a_rec (m : ℕ) : (a (m + 9) : ℤ) = (5 : ℤ) * (a (m + 8) : ℤ) + (2 : ℤ) * (a (m + 7) : ℤ) + (-1 : ℤ) * (a (m + 6) : ℤ) + (-24 : ℤ) * (a (m + 5) : ℤ) + (13 : ℤ) * (a (m + 4) : ℤ) + (0 : ℤ) * (a (m + 3) : ℤ) + (-2 : ℤ) * (a (m + 2) : ℤ) + (6 : ℤ) * (a (m + 1) : ℤ) := by
  have h1 : (a (m + 1) : ℤ) = ∑ r : R, (F (m + 0) none r : ℤ) := by
    rw [show m + 1 = (m + 0) + 1 from rfl, a_eq]; push_cast; rfl
  have h2 : (a (m + 2) : ℤ) = ∑ r : R, (F (m + 1) none r : ℤ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, a_eq]; push_cast; rfl
  have h3 : (a (m + 3) : ℤ) = ∑ r : R, (F (m + 2) none r : ℤ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, a_eq]; push_cast; rfl
  have h4 : (a (m + 4) : ℤ) = ∑ r : R, (F (m + 3) none r : ℤ) := by
    rw [show m + 4 = (m + 3) + 1 from rfl, a_eq]; push_cast; rfl
  have h5 : (a (m + 5) : ℤ) = ∑ r : R, (F (m + 4) none r : ℤ) := by
    rw [show m + 5 = (m + 4) + 1 from rfl, a_eq]; push_cast; rfl
  have h6 : (a (m + 6) : ℤ) = ∑ r : R, (F (m + 5) none r : ℤ) := by
    rw [show m + 6 = (m + 5) + 1 from rfl, a_eq]; push_cast; rfl
  have h7 : (a (m + 7) : ℤ) = ∑ r : R, (F (m + 6) none r : ℤ) := by
    rw [show m + 7 = (m + 6) + 1 from rfl, a_eq]; push_cast; rfl
  have h8 : (a (m + 8) : ℤ) = ∑ r : R, (F (m + 7) none r : ℤ) := by
    rw [show m + 8 = (m + 7) + 1 from rfl, a_eq]; push_cast; rfl
  have h9 : (a (m + 9) : ℤ) = ∑ r : R, (F (m + 8) none r : ℤ) := by
    rw [show m + 9 = (m + 8) + 1 from rfl, a_eq]; push_cast; rfl
  rw [h9, h8, h7, h6, h5, h4, h3, h2, h1]
  have hf : ∀ r, (F (m + 8) none r : ℤ) = (5 : ℤ) * (F (m + 7) none r : ℤ) + (2 : ℤ) * (F (m + 6) none r : ℤ) + (-1 : ℤ) * (F (m + 5) none r : ℤ) + (-24 : ℤ) * (F (m + 4) none r : ℤ) + (13 : ℤ) * (F (m + 3) none r : ℤ) + (0 : ℤ) * (F (m + 2) none r : ℤ) + (-2 : ℤ) * (F (m + 1) none r : ℤ) + (6 : ℤ) * (F (m + 0) none r : ℤ) := fun r => by
    have := D_all m none r; unfold D at this; linarith
  simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma sumR8 (g : R → ℕ) : ∑ r : R, g r = g ![(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + g ![(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + g ![(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + g ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)] + g ![(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)] + g ![(1 : Fin 2), (0 : Fin 2), (1 : Fin 2)] + g ![(1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] + g ![(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)] := by
  rw [sumR]; simp only [Fin.sum_univ_two, add_assoc]

lemma a1 : a 1 = 8 := by
  rw [show 1 = 0 + 1 by rfl, a_eq, sumR8]; simp only [v0_n_000, v0_n_001, v0_n_010, v0_n_011, v0_n_100, v0_n_101, v0_n_110, v0_n_111]

lemma a2 : a 2 = 43 := by
  rw [show 2 = 1 + 1 by rfl, a_eq, sumR8]; simp only [v1_n_000, v1_n_001, v1_n_010, v1_n_011, v1_n_100, v1_n_101, v1_n_110, v1_n_111]

lemma a3 : a 3 = 206 := by
  rw [show 3 = 2 + 1 by rfl, a_eq, sumR8]; simp only [v2_n_000, v2_n_001, v2_n_010, v2_n_011, v2_n_100, v2_n_101, v2_n_110, v2_n_111]

lemma a4 : a 4 = 1097 := by
  rw [show 4 = 3 + 1 by rfl, a_eq, sumR8]; simp only [v3_n_000, v3_n_001, v3_n_010, v3_n_011, v3_n_100, v3_n_101, v3_n_110, v3_n_111]

lemma a5 : a 5 = 5675 := by
  rw [show 5 = 4 + 1 by rfl, a_eq, sumR8]; simp only [v4_n_000, v4_n_001, v4_n_010, v4_n_011, v4_n_100, v4_n_101, v4_n_110, v4_n_111]

lemma a6 : a 6 = 29433 := by
  rw [show 6 = 5 + 1 by rfl, a_eq, sumR8]; simp only [v5_n_000, v5_n_001, v5_n_010, v5_n_011, v5_n_100, v5_n_101, v5_n_110, v5_n_111]

lemma a7 : a 7 = 153037 := by
  rw [show 7 = 6 + 1 by rfl, a_eq, sumR8]; simp only [v6_n_000, v6_n_001, v6_n_010, v6_n_011, v6_n_100, v6_n_101, v6_n_110, v6_n_111]

lemma a8 : a 8 = 794716 := by
  rw [show 8 = 7 + 1 by rfl, a_eq, sumR8]; simp only [v7_n_000, v7_n_001, v7_n_010, v7_n_011, v7_n_100, v7_n_101, v7_n_110, v7_n_111]


open PowerSeries in
theorem full :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) + 2 * a (n - 2) - a (n - 3) - 24 * a (n - 4) +
      13 * a (n - 5) - 2 * a (n - 7) + 6 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) *
        (1 - 5 * X - 2 * X ^ 2 + X ^ 3 + 24 * X ^ 4 - 13 * X ^ 5 + 2 * X ^ 7 - 6 * X ^ 8) =
      X * (8 + 3 * X - 25 * X ^ 2 - 11 * X ^ 3 + 13 * X ^ 4 - 2 * X ^ 5 + 4 * X ^ 6 + 6 * X ^ 7)) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [a_rec m]
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega,
      show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega]
    ring
  · set b := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hb
    have hL : b * (1 - 5 * X - 2 * X ^ 2 + X ^ 3 + 24 * X ^ 4 - 13 * X ^ 5 + 2 * X ^ 7 - 6 * X ^ 8) =
        b + C (-5 : ℤ) * (b * X ^ 1) + C (-2 : ℤ) * (b * X ^ 2) + C (1 : ℤ) * (b * X ^ 3) +
          C (24 : ℤ) * (b * X ^ 4) + C (-13 : ℤ) * (b * X ^ 5) + C (2 : ℤ) * (b * X ^ 7) +
          C (-6 : ℤ) * (b * X ^ 8) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    have hR : (X * (8 + 3 * X - 25 * X ^ 2 - 11 * X ^ 3 + 13 * X ^ 4 - 2 * X ^ 5 + 4 * X ^ 6 +
        6 * X ^ 7) : PowerSeries ℤ) = C (8 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (-25 : ℤ) * X ^ 3 +
          C (-11 : ℤ) * X ^ 4 + C (13 : ℤ) * X ^ 5 + C (-2 : ℤ) * X ^ 6 + C (4 : ℤ) * X ^ 7 +
          C (6 : ℤ) * X ^ 8 := by
      simp only [map_neg, map_ofNat, neg_mul]; ring
    rw [hL, hR]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', hb, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge c 9 with h | h
    · interval_cases c <;> simp [a1, a2, a3, a4, a5, a6, a7, a8]
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 9 := ⟨c - 9, by omega⟩
      have hr := a_rec m
      simp (disch := omega) only [if_pos, if_neg, show m + 9 - 1 = m + 8 by omega,
        show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
        show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega,
        show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega]
      linarith

end OMA.P_oeis_a282523

theorem OMA.solution : type_of% @OMA.S_oeis_a282523.main := OMA.P_oeis_a282523.full
