import OMAStatements.S_oeis_a208638
import Mathlib

/-!
# A208638: proof of Barker's g.f. and closed form

For 0..1 arrays, values are introduced in row major order iff x(0,0) = 0. An element has at most
one equal neighbor among left, up and up-right iff no two of these three neighbors are equal to it,
which is a condition on three consecutive columns. Encoding the columns as Fin 8, the number of
valid continuations after a pair of columns (p, c) is A 2^m + B m + C with (A, B, C) one of five
triples (checked by `decide` on the transfer coefficients), and summing over the admissible first
columns gives a(m + 2) = 20 2^m - m - 7, a(1) = 4, i.e. a(n) = 5 2^n - n - 5.
-/

open OMA.S_oeis_a208638

namespace OMA.P_a208638

open Finset

abbrev Col := Fin 3 → Fin 2

def pf (A B C : Bool) : Bool := !(A && B) && !(A && C) && !(B && C)

def eqo (p : Option Col) (i : Fin 3) (v : Fin 2) : Bool :=
  match p with
  | none => false
  | some d => decide (d i = v)

def okO (p : Option Col) (c : Col) (r : Option Col) : Bool :=
  pf (eqo p 1 (c 1)) (decide (c 0 = c 1)) (eqo r 0 (c 1)) &&
    pf (eqo p 2 (c 2)) (decide (c 1 = c 2)) (eqo r 1 (c 2))

def CLp (p : Option Col) (L : List Col) : Prop :=
  ∀ j (h : j < L.length), okO (if j = 0 then p else L[j - 1]?) L[j] L[j + 1]? = true

instance (p : Option Col) (L : List Col) : Decidable (CLp p L) := by
  unfold CLp; infer_instance

lemma CLp_one (p : Option Col) (c : Col) : CLp p [c] ↔ okO p c none = true := by
  constructor
  · intro h; simpa using h 0 (by simp)
  · intro h j hj
    have : j = 0 := by simpa using hj
    subst this; simpa using h

lemma CLp_cons (p : Option Col) (c d : Col) (l : List Col) :
    CLp p (c :: d :: l) ↔ okO p c (some d) = true ∧ CLp (some c) (d :: l) := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun j hj => ?_⟩
    have := h (j + 1) (by simp at hj ⊢; omega)
    rcases j with _ | j
    · simpa using this
    · simpa using this
  · rintro ⟨h0, h⟩ j hj
    rcases j with _ | j
    · simpa using h0
    · have := h j (by simp at hj ⊢; omega)
      rcases j with _ | j
      · simpa using this
      · simpa using this

def cntc (n : ℕ) (P : List Col → Prop) [DecidablePred P] : ℕ :=
  ((univ : Finset (Fin n → Col)).filter (fun f => P (List.ofFn f))).card

lemma cntc_succ (n : ℕ) (P : List Col → Prop) [DecidablePred P] :
    cntc (n + 1) P = ∑ a : Col, cntc n (fun L => P (a :: L)) := by
  unfold cntc
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]

lemma cntc_zero (P : List Col → Prop) [DecidablePred P] : cntc 0 P = if P [] then 1 else 0 := by
  unfold cntc
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; simpa using h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f _
    simpa using h

lemma cntc_congr (n : ℕ) (P Q : List Col → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ L, P L ↔ Q L) : cntc n P = cntc n Q := by
  unfold cntc; congr 1; ext f; simp [h]

def dec (k : Fin 8) : Col := ![⟨k.val % 2, by omega⟩, ⟨k.val / 2 % 2, by omega⟩, ⟨k.val / 4 % 2, by omega⟩]

def encE : Col ≃ Fin 8 where
  toFun c := ⟨(c 0).val + 2 * (c 1).val + 4 * (c 2).val, by omega⟩
  invFun := dec
  left_inv := by decide
  right_inv := by decide

lemma sumC (G : Col → ℤ) : ∑ d : Col, G d = ∑ k : Fin 8, G (dec k) := by
  rw [← encE.symm.sum_comp]
  rfl

def hh (m : ℕ) (p c : Col) : ℕ := cntc m (fun l => CLp (some p) (c :: l))

lemma hh_succ (m : ℕ) (p c : Col) :
    hh (m + 1) p c = ∑ d : Col, if okO (some p) c (some d) = true then hh m c d else 0 := by
  unfold hh
  rw [cntc_succ]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · exact cntc_congr _ _ _ fun L => by rw [CLp_cons]; simp [h]
  · unfold cntc
    simp [CLp_cons, h]

lemma hh_zero (p c : Col) : hh 0 p c = if okO (some p) c none = true then 1 else 0 := by
  unfold hh
  rw [cntc_zero]
  simp [CLp_one]

def KT (p c : Fin 8) : ℕ := ([[0, 0, 1, 1, 0, 2, 3, 1], [0, 0, 1, 1, 0, 2, 3, 1], [0, 0, 1, 0, 2, 4, 1, 0], [0, 0, 1, 0, 2, 4, 1, 0], [0, 1, 4, 2, 0, 1, 0, 0], [0, 1, 4, 2, 0, 1, 0, 0], [1, 3, 2, 0, 1, 1, 0, 0], [1, 3, 2, 0, 1, 1, 0, 0]] : List (List ℕ)).getD p.val [] |>.getD c.val 0
def FA (k : ℕ) : ℤ := [0, 1, 2, 3, 4].getD k 0
def FB (k : ℕ) : ℤ := [0, 0, 0, 0, -1].getD k 0
def FC (k : ℕ) : ℤ := [0, 0, -1, -2, -3].getD k 0
def tt (p c d : Fin 8) : ℤ := if okO (some (dec p)) (dec c) (some (dec d)) = true then 1 else 0

lemma coefA : ∀ p c : Fin 8, ∑ k : Fin 8, tt p c k * FA (KT c k) = 2 * FA (KT p c) := by decide
lemma coefB : ∀ p c : Fin 8, ∑ k : Fin 8, tt p c k * FB (KT c k) = FB (KT p c) := by decide
lemma coefC : ∀ p c : Fin 8, ∑ k : Fin 8, tt p c k * FC (KT c k) = FB (KT p c) + FC (KT p c) := by
  decide
lemma coef0 : ∀ p c : Fin 8, (if okO (some (dec p)) (dec c) none = true then (1 : ℤ) else 0) =
    FA (KT p c) + FC (KT p c) := by decide

lemma hh_closed (m : ℕ) : ∀ p c : Fin 8,
    (hh m (dec p) (dec c) : ℤ) = FA (KT p c) * 2 ^ m + FB (KT p c) * m + FC (KT p c) := by
  induction m with
  | zero =>
    intro p c
    rw [hh_zero, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, coef0]
    ring
  | succ m ih =>
    intro p c
    rw [hh_succ]
    push_cast
    rw [sumC]
    have e : ∀ k : Fin 8, ((if okO (some (dec p)) (dec c) (some (dec k)) = true then
        (hh m (dec c) (dec k) : ℤ) else 0)) =
        (tt p c k * FA (KT c k)) * 2 ^ m + (tt p c k * FB (KT c k)) * m + tt p c k * FC (KT c k) := by
      intro k
      unfold tt
      split_ifs
      · rw [ih]; ring
      · ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, coefA, coefB, coefC]
    ring

def h0 (m : ℕ) (c : Col) : ℕ := cntc m (fun l => CLp none (c :: l))

lemma h0_succ (m : ℕ) (c : Col) :
    h0 (m + 1) c = ∑ d : Col, if okO none c (some d) = true then hh m c d else 0 := by
  unfold h0
  rw [cntc_succ]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · exact cntc_congr _ _ _ fun L => by rw [CLp_cons]; simp [h]
  · unfold cntc
    simp [CLp_cons, h]

lemma h0_zero (c : Col) : h0 0 c = if okO none c none = true then 1 else 0 := by
  unfold h0
  rw [cntc_zero]
  simp [CLp_one]

def PP (L : List Col) : Prop := (∀ c ∈ L.head?, c 0 = 0) ∧ CLp none L

instance (L : List Col) : Decidable (PP L) := by unfold PP; infer_instance

lemma cnt_PP (m : ℕ) : cntc (m + 1) PP = ∑ c : Col, if c 0 = 0 then h0 m c else 0 := by
  rw [cntc_succ]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · exact cntc_congr _ _ _ fun L => by simp [PP, h]
  · unfold cntc
    simp [PP, h]

def ss (c : Fin 8) : ℤ := if dec c 0 = 0 then 1 else 0
def t0 (c d : Fin 8) : ℤ := if okO none (dec c) (some (dec d)) = true then 1 else 0

lemma sA : ∑ c : Fin 8, ∑ k : Fin 8, ss c * t0 c k * FA (KT c k) = 20 := by decide
lemma sB : ∑ c : Fin 8, ∑ k : Fin 8, ss c * t0 c k * FB (KT c k) = -1 := by decide
lemma sC : ∑ c : Fin 8, ∑ k : Fin 8, ss c * t0 c k * FC (KT c k) = -7 := by decide
lemma s1 : ∑ c : Fin 8, ss c * (if okO none (dec c) none = true then (1 : ℤ) else 0) = 4 := by decide

lemma cnt_closed (m : ℕ) : (cntc (m + 2) PP : ℤ) = 20 * 2 ^ m - m - 7 := by
  rw [cnt_PP]
  push_cast
  rw [sumC]
  have e : ∀ c : Fin 8, ((if dec c 0 = 0 then (h0 (m + 1) (dec c) : ℤ) else 0)) =
      (∑ k : Fin 8, ss c * t0 c k * FA (KT c k)) * 2 ^ m +
        (∑ k : Fin 8, ss c * t0 c k * FB (KT c k)) * m + ∑ k : Fin 8, ss c * t0 c k * FC (KT c k) := by
    intro c
    rw [h0_succ]
    push_cast
    rw [sumC]
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    unfold ss
    split_ifs with hc
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold t0
      split_ifs
      · rw [hh_closed]; ring
      · ring
    · simp
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, sA, sB, sC]
  ring

lemma cnt_one : (cntc 1 PP : ℤ) = 4 := by
  rw [cnt_PP]
  push_cast
  rw [sumC, ← s1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h0_zero]
  unfold ss
  split_ifs <;> simp_all

lemma pf_iff (a b c : Bool) :
    pf a b c = true ↔ ¬(a = true ∧ b = true) ∧ ¬(a = true ∧ c = true) ∧ ¬(b = true ∧ c = true) := by
  revert a b c; decide

lemma abc {n : ℕ} (x : Fin 3 → Fin n → Fin 2) (i : Fin 3) (j : Fin n) :
    eqNbrs x i j ≤ 1 ↔
      ¬((∃ j' : Fin n, j'.val + 1 = j.val ∧ x i j' = x i j) ∧
          (∃ i' : Fin 3, i'.val + 1 = i.val ∧ x i' j = x i j)) ∧
      ¬((∃ j' : Fin n, j'.val + 1 = j.val ∧ x i j' = x i j) ∧
          (∃ i' : Fin 3, ∃ j' : Fin n, i'.val + 1 = i.val ∧ j'.val = j.val + 1 ∧ x i' j' = x i j)) ∧
      ¬((∃ i' : Fin 3, i'.val + 1 = i.val ∧ x i' j = x i j) ∧
          (∃ i' : Fin 3, ∃ j' : Fin n, i'.val + 1 = i.val ∧ j'.val = j.val + 1 ∧ x i' j' = x i j)) := by
  unfold eqNbrs
  rw [Finset.card_le_one]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨⟨j', hj', ex⟩, ⟨i', hi', ex'⟩⟩
      have := h (i, j') ⟨Or.inl ⟨rfl, hj'⟩, ex⟩ (i', j) ⟨Or.inr (Or.inl ⟨hi', rfl⟩), ex'⟩
      simp only [Prod.ext_iff, Fin.ext_iff] at this
      omega
    · rintro ⟨⟨j', hj', ex⟩, ⟨i', j'', hi', hj'', ex'⟩⟩
      have := h (i, j') ⟨Or.inl ⟨rfl, hj'⟩, ex⟩ (i', j'') ⟨Or.inr (Or.inr ⟨hi', hj''⟩), ex'⟩
      simp only [Prod.ext_iff, Fin.ext_iff] at this
      omega
    · rintro ⟨⟨i', hi', ex⟩, ⟨i'', j'', hi'', hj'', ex'⟩⟩
      have := h (i', j) ⟨Or.inr (Or.inl ⟨hi', rfl⟩), ex⟩ (i'', j'') ⟨Or.inr (Or.inr ⟨hi'', hj''⟩), ex'⟩
      simp only [Prod.ext_iff, Fin.ext_iff] at this
      omega
  · rintro ⟨h1, h2, h3⟩ ⟨p1, p2⟩ ⟨hp, ep⟩ ⟨q1, q2⟩ ⟨hq, eq⟩
    simp only at hp hq ep eq
    rcases hp with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases hq with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩
    · apply Prod.ext <;> dsimp only
      · exact a1.trans b1.symm
      · exact Fin.ext (by omega)
    · subst a1 b2; exact absurd ⟨⟨p2, a2, ep⟩, ⟨q1, b1, eq⟩⟩ h1
    · subst a1; exact absurd ⟨⟨p2, a2, ep⟩, ⟨q1, q2, b1, b2, eq⟩⟩ h2
    · subst b1 a2; exact absurd ⟨⟨q2, b2, eq⟩, ⟨p1, a1, ep⟩⟩ h1
    · apply Prod.ext <;> dsimp only
      · exact Fin.ext (by omega)
      · exact a2.trans b2.symm
    · subst a2; exact absurd ⟨⟨p1, a1, ep⟩, ⟨q1, q2, b1, b2, eq⟩⟩ h3
    · subst b1; exact absurd ⟨⟨q2, b2, eq⟩, ⟨p1, p2, a1, a2, ep⟩⟩ h2
    · subst b2; exact absurd ⟨⟨q1, b1, eq⟩, ⟨p1, p2, a1, a2, ep⟩⟩ h3
    · apply Prod.ext <;> dsimp only <;> exact Fin.ext (by omega)

def prevO {n : ℕ} (y : Fin n → Col) (j : Fin n) : Option Col :=
  if h : 1 ≤ j.val then some (y ⟨j.val - 1, by omega⟩) else none

def nextO {n : ℕ} (y : Fin n → Col) (j : Fin n) : Option Col :=
  if h : j.val + 1 < n then some (y ⟨j.val + 1, h⟩) else none

lemma eqo_prev {n : ℕ} (y : Fin n → Col) (j : Fin n) (i : Fin 3) (v : Fin 2) :
    eqo (prevO y j) i v = true ↔ ∃ j' : Fin n, j'.val + 1 = j.val ∧ y j' i = v := by
  unfold prevO
  split_ifs with h
  · simp only [eqo, decide_eq_true_eq]
    constructor
    · intro e; exact ⟨⟨j.val - 1, by omega⟩, by simp; omega, e⟩
    · rintro ⟨j', hj', e⟩
      have : j' = ⟨j.val - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this] at e; exact e
  · simp only [eqo, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j' hj'; omega

lemma eqo_next {n : ℕ} (y : Fin n → Col) (j : Fin n) (i : Fin 3) (v : Fin 2) :
    eqo (nextO y j) i v = true ↔ ∃ j' : Fin n, j'.val = j.val + 1 ∧ y j' i = v := by
  unfold nextO
  split_ifs with h
  · simp only [eqo, decide_eq_true_eq]
    constructor
    · intro e; exact ⟨⟨j.val + 1, h⟩, rfl, e⟩
    · rintro ⟨j', hj', e⟩
      have : j' = ⟨j.val + 1, h⟩ := Fin.ext hj'
      subst this; exact e
  · simp only [eqo, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j' hj'; have := j'.isLt; omega

lemma col_ok {n : ℕ} (y : Fin n → Col) (j : Fin n) :
    (∀ i, eqNbrs (fun i j => y j i) i j ≤ 1) ↔ okO (prevO y j) (y j) (nextO y j) = true := by
  simp only [abc]
  unfold okO
  rw [Bool.and_eq_true, pf_iff, pf_iff]
  simp only [eqo_prev, eqo_next, decide_eq_true_eq, Fin.forall_fin_succ, Fin.exists_fin_succ]
  simp

lemma CL_iff {n : ℕ} (y : Fin n → Col) :
    CLp none (List.ofFn y) ↔ ∀ j : Fin n, okO (prevO y j) (y j) (nextO y j) = true := by
  have hp : ∀ j : Fin n, (if j.val = 0 then none else (List.ofFn y)[j.val - 1]?) = prevO y j := by
    intro j
    unfold prevO
    split_ifs with h1 h2 h2
    · omega
    · rfl
    · simp [List.getElem?_ofFn]
      omega
    · omega
  have hn : ∀ j : Fin n, (List.ofFn y)[j.val + 1]? = nextO y j := by
    intro j
    unfold nextO
    split_ifs with h
    · simp [h]
    · simp [h]
  unfold CLp
  simp only [List.length_ofFn]
  constructor
  · intro h j
    have := h j.val j.isLt
    rw [hp j, hn j] at this
    simpa using this
  · intro h j hj
    have := h ⟨j, hj⟩
    rw [← hp ⟨j, hj⟩, ← hn ⟨j, hj⟩] at this
    simpa using this

lemma rmn_iff {n : ℕ} (y : Fin n → Col) :
    RowMajorNew (fun i j => y j i) ↔ ∀ c ∈ (List.ofFn y).head?, c 0 = 0 := by
  rcases n with _ | m
  · simp only [List.ofFn_zero, List.head?_nil, Option.mem_def, reduceCtorEq, false_implies,
      implies_true, iff_true]
    intro i j; exact j.elim0
  · simp only [List.ofFn_succ, List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
    constructor
    · intro h
      by_contra h0
      have h1 : (0 : Fin 2) < y 0 0 := by
        rcases Fin.exists_fin_two.mp ⟨y 0 0, rfl⟩ with e | e <;> simp_all
      obtain ⟨i', j', hij, -⟩ := h 0 0 0 h1
      rcases hij with h | ⟨-, h⟩
      · exact absurd h (Fin.not_lt_zero _)
      · exact absurd h (Fin.not_lt_zero _)
    · intro h0 i j u hu
      dsimp only at hu ⊢
      refine ⟨0, 0, ?_, ?_⟩
      · by_contra hc
        simp only [not_or, not_and, not_lt] at hc
        have hi : i = 0 := by
          rcases hc with ⟨h1, -⟩
          exact Fin.le_zero_iff.mp h1
        subst hi
        have hj : j = 0 := Fin.le_zero_iff.mp (hc.2 rfl)
        subst hj
        rw [h0] at hu
        exact absurd hu (Fin.not_lt_zero _)
      · have : u = 0 := by
          have := u.isLt
          have h2 : u.val < (y j i).val := hu
          have := (y j i).isLt
          ext; simp; omega
        rw [this, h0]

lemma a_cnt (n : ℕ) : a n = cntc n PP := by
  unfold a cntc
  simp only [Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin n) (_ : Fin 3) => Fin 2)).sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e1 : Cond ((Equiv.piComm (fun (_ : Fin n) (_ : Fin 3) => Fin 2)) y) ↔ CLp none (List.ofFn y) := by
    rw [CL_iff]
    unfold Cond
    rw [forall_comm]
    exact forall_congr' fun j => col_ok y j
  have e2 : RowMajorNew ((Equiv.piComm (fun (_ : Fin n) (_ : Fin 3) => Fin 2)) y) ↔
      ∀ c ∈ (List.ofFn y).head?, c 0 = 0 := rmn_iff y
  have : (Cond ((Equiv.piComm (fun (_ : Fin n) (_ : Fin 3) => Fin 2)) y) ∧
      RowMajorNew ((Equiv.piComm (fun (_ : Fin n) (_ : Fin 3) => Fin 2)) y)) ↔ PP (List.ofFn y) := by
    rw [e1, e2, PP, and_comm]
  simp only [this]

lemma cnum (c : ℕ) [c.AtLeastTwo] (p : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((no_index (OfNat.ofNat c : PowerSeries ℚ)) * p) =
      (OfNat.ofNat c : ℚ) * PowerSeries.coeff n p := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C_mul]

lemma cnum0 (c : ℕ) [c.AtLeastTwo] (n : ℕ) :
    PowerSeries.coeff n (no_index (OfNat.ofNat c : PowerSeries ℚ)) =
      if n = 0 then (OfNat.ofNat c : ℚ) else 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C]

lemma a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 5 * 2 ^ n - n - 5 := by
  rw [a_cnt]
  rcases n with _ | _ | m
  · omega
  · have := cnt_one
    have : (cntc 1 PP : ℚ) = 4 := by exact_mod_cast this
    rw [this]; norm_num
  · have := cnt_closed m
    have : (cntc (m + 2) PP : ℚ) = 20 * 2 ^ m - m - 7 := by exact_mod_cast this
    rw [this]; push_cast; ring

open PowerSeries in
theorem mainP :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X)) =
      X * (4 - 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 5 * 2 ^ n - n - 5 := by
  have hc := a_closed
  generalize a = f at hc ⊢
  refine ⟨?_, hc⟩
  have hL : ∀ S : PowerSeries ℚ, S * ((1 - X) ^ 2 * (1 - 2 * X)) =
      S - 4 * (S * X ^ 1) + 5 * (S * X ^ 2) - 2 * (S * X ^ 3) := fun S => by ring
  have hR : (X * (4 - 3 * X) : PowerSeries ℚ) = X ^ 1 * (4 - 3 * X) := by ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', cnum, coeff_mk, coeff_X_pow_mul']
  rcases lt_or_ge n 4 with hn | hn
  · have v1 := hc 1 (by norm_num)
    have v2 := hc 2 (by norm_num)
    have v3 := hc 3 (by norm_num)
    norm_num at v1 v2 v3
    interval_cases n <;> simp [cnum0, coeff_X, v1, v2, v3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega,
      show m + 4 ≠ 0 by omega, show m + 4 - 1 ≠ 0 by omega, show m + 4 - 2 ≠ 0 by omega,
      show m + 4 - 3 ≠ 0 by omega, if_true, if_false]
    rw [hc (m + 4) (by omega), hc (m + 4 - 1) (by omega), hc (m + 4 - 2) (by omega),
      hc (m + 4 - 3) (by omega)]
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    have hz : coeff (m + 3) (4 : PowerSeries ℚ) - 3 * coeff (m + 3) (X : PowerSeries ℚ) = 0 := by
      simp [cnum0, coeff_X]
    rw [hz]
    push_cast
    ring

end OMA.P_a208638

theorem OMA.solution : type_of% @OMA.S_oeis_a208638.main := OMA.P_a208638.mainP
