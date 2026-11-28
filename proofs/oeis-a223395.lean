import OMAStatements.S_oeis_a223395
import Mathlib

-- Proof of the conjectures in OEIS A223395 (statement by @ivillar).
-- Idea: the conditions involve only consecutive rows, so the count is a walk count on the
-- 16 possible rows (transfer matrix). The states fall into 3 classes such that the number of successors
-- of a state in each class depends only on its own class (checked by a kernel computation, with the
-- class counts of each state packed into one base-32 number). The class-count vectors V(0), V(1), ...
-- then satisfy a linear recurrence with a 4 X 4 matrix, whose first iterates are computed
-- explicitly; they satisfy the conjectured recurrence, and so do all later ones by linearity.
-- The g.f. follows from the recurrence and the first values.

namespace OMAA223395Helpers

open OMA.S_oeis_a223395

abbrev R := Fin 1 → Fin 16

instance (u v : Fin 16) : Decidable (Adj u v) := by unfold Adj; infer_instance

/-- No constraint on a single state. -/
def RowOK (_r : R) : Prop := True

instance : DecidablePred RowOK := fun r => by unfold RowOK; infer_instance

/-- Consecutive rows u, v: all the subblocks they form satisfy the condition. -/
def Compat (u v : R) : Prop := Adj (u 0) (v 0)

instance (u v : R) : Decidable (Compat u v) := by unfold Compat; infer_instance

/-- No constraint on the first state. -/
def Init (_r : R) : Prop := True

instance : DecidablePred Init := fun r => by unfold Init; infer_instance

abbrev ok (r : R) : Prop := RowOK r

abbrev compat (r s : R) : Prop := Compat r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

/-- Number of walks with n+1 states starting at s. -/
def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- Decoding of a state from its index (base 16 digits). -/
def dec (i : ℕ) : R := fun k => ⟨i / 16 ^ (k : ℕ) % 16, Nat.mod_lt _ (by norm_num)⟩

/-- Index of a state. -/
def enc (r : R) : ℕ := (r 0 : ℕ)

theorem dec_enc : ∀ r : R, dec (enc r) = r := by decide +kernel

theorem enc_lt : ∀ r : R, enc r < 16 := by decide +kernel

theorem enc_dec : ∀ i < 16, enc (dec i) = i := by decide +kernel

theorem sum_R (g : R → ℕ) : ∑ t : R, g t = ∑ i ∈ Finset.range 16, g (dec i) := by
  refine Finset.sum_nbij' (fun t => enc t) (fun i => dec i) ?_ ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_range.mpr (enc_lt t)
  · intro i _; exact Finset.mem_univ _
  · intro t _; exact dec_enc t
  · intro i hi; exact enc_dec i (Finset.mem_range.mp hi)
  · intro t _; rw [dec_enc]

/-- Class of the state with index i (a table in base 4): states of one class have the same numbers
of successors in every class. -/
def clsN (i : ℕ) : ℕ := 342452500 / 4 ^ i % 4

def cls (r : R) : ℕ := clsN (enc r)

/-- Class transition counts; the last row (index 3) counts the admissible first states by class. -/
def MXL : List (List ℕ) := [[0, 2, 0, 0],
  [1, 1, 1, 0],
  [0, 2, 2, 0],
  [4, 8, 4, 0]]

def MX (k j : ℕ) : ℕ := (MXL.getD k []).getD j 0

theorem MXL_lt : ∀ row ∈ MXL, ∀ x ∈ row, x < 32 := by decide +kernel

theorem getD_lt (l : List ℕ) (B : ℕ) (hB : 0 < B) (h : ∀ x ∈ l, x < B) (j : ℕ) : l.getD j 0 < B := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem (l := l) (d := 0) hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default (l := l) (d := 0) (by omega)]
    exact hB

theorem MX_lt (k j : ℕ) : MX k j < 32 := by
  unfold MX
  apply getD_lt _ _ (by norm_num)
  by_cases hk : k < MXL.length
  · rw [List.getD_eq_getElem (l := MXL) (d := []) hk]
    exact MXL_lt _ (List.getElem_mem hk)
  · rw [List.getD_eq_default (l := MXL) (d := []) (by omega)]
    intro x hx
    simp at hx

/-- Dot product of two lists (missing entries count as 0). -/
def dot (r : List ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs => r.headD 0 * b + dot r.tail bs

theorem dot_eq : ∀ (v r : List ℕ) (n : ℕ), v.length ≤ n →
    dot r v = ∑ j ∈ Finset.range n, r.getD j 0 * v.getD j 0
  | [], r, n, _ => by simp [dot]
  | b :: bs, r, 0, h => by simp at h
  | b :: bs, r, n + 1, h => by
      rw [Finset.sum_range_succ', dot, dot_eq bs r.tail n (by simpa using h)]
      cases r <;> simp [add_comm]

theorem dot_nil : ∀ v : List ℕ, dot [] v = 0
  | [] => rfl
  | b :: bs => by simp [dot, dot_nil bs]

/-- One transfer step on class vectors, as a list computation. -/
def stepv (v : List ℕ) : List ℕ := MXL.map (fun row => dot row v)

theorem stepv_getD (v : List ℕ) (hv : v.length ≤ 4) (i : ℕ) :
    (stepv v).getD i 0 = ∑ j ∈ Finset.range 4, MX i j * v.getD j 0 := by
  have h1 : (MXL.map (fun row => dot row v)).getD i 0 = dot (MXL.getD i []) v := by
    have h := List.getD_map (l := MXL) (d := ([] : List ℕ)) (n := i) (fun row => dot row v)
    rw [dot_nil] at h
    exact h
  unfold stepv MX
  rw [h1, dot_eq v _ 4 hv]

/-- The powers of 32 and the class rows packed in base 32. -/
def POWL : List ℕ := [1, 32, 1024, 32768]

def HXL : List ℕ := [64, 1057, 2112, 4356]

theorem POW_eq : ∀ j < 4, POWL.getD j 0 = 32 ^ j := by decide +kernel

theorem HX_eq : stepv POWL = HXL := by decide +kernel

theorem HX_sum (k : ℕ) : HXL.getD k 0 = ∑ j ∈ Finset.range 4, MX k j * 32 ^ j := by
  rw [← HX_eq, stepv_getD POWL (by decide) k]
  exact Finset.sum_congr rfl (fun j hj => by rw [POW_eq j (Finset.mem_range.mp hj)])

theorem clsN_lt : ∀ i < 16, clsN i < 3 := by decide +kernel

theorem cls_lt (r : R) : cls r < 4 := by
  have := clsN_lt (enc r) (enc_lt r)
  unfold cls
  omega

/-- The successor classes of state i, packed into one base 32 number, agree with the class table. -/
def HashP (i : ℕ) : Prop :=
  (∑ t ∈ Finset.range 16, if ok (dec i) ∧ compat (dec i) (dec t) then 32 ^ clsN t else 0) =
    HXL.getD (clsN i) 0

instance : DecidablePred HashP := fun i => by unfold HashP; infer_instance

theorem hashS_0 : ∀ i < 16, 0 ≤ i → HashP i := by decide +kernel

theorem hashS : ∀ i < 16, HashP i := by
  intro i hi
  exact hashS_0 i hi (by omega)

theorem hashI0 :
    (∑ t ∈ Finset.range 16, if Init (dec t) then 32 ^ clsN t else 0) = HXL.getD 3 0 := by
  decide +kernel

theorem hashI :
    (∑ t ∈ Finset.range 16, if Init (dec t) then 32 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 4, MX 3 j * 32 ^ j := by
  rw [hashI0, HX_sum]

theorem digits_unique (B : ℕ) (hB : 0 < B) : ∀ (c : ℕ) (n m : ℕ → ℕ), (∀ j < c, n j < B) →
    (∀ j < c, m j < B) →
    ∑ j ∈ Finset.range c, n j * B ^ j = ∑ j ∈ Finset.range c, m j * B ^ j → ∀ j < c, n j = m j := by
  intro c
  induction c with
  | zero => intro n m _ _ _ j hj; omega
  | succ c ih =>
    intro n m hn hm h j hj
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one, pow_succ] at h
    have e1 : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range c, f (k + 1) * (B ^ k * B) =
        B * ∑ k ∈ Finset.range c, f (k + 1) * B ^ k := by
      intro f
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e1 n, e1 m] at h
    have h0 : n 0 = m 0 := by
      have h' := congrArg (fun z => z % B) h
      simp only [Nat.mul_add_mod] at h'
      rwa [Nat.mod_eq_of_lt (hn 0 (by omega)), Nat.mod_eq_of_lt (hm 0 (by omega))] at h'
    have h1 : ∑ k ∈ Finset.range c, n (k + 1) * B ^ k = ∑ k ∈ Finset.range c, m (k + 1) * B ^ k := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hB (Nat.add_right_cancel h)
    rcases j with _ | j
    · exact h0
    · exact ih (fun k => n (k + 1)) (fun k => m (k + 1)) (fun k hk => hn (k + 1) (by omega))
        (fun k hk => hm (k + 1) (by omega)) h1 j (by omega)

theorem sum_cls (P : R → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (∑ t : R, if P t then f (cls t) else 0) =
      ∑ j ∈ Finset.range 4, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j := by
  have h : ∀ j, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j =
      ∑ t : R, if P t ∧ cls t = j then f j else 0 := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hP : P t
  · simp only [hP, true_and, if_true]
    rw [Finset.sum_ite_eq (Finset.range 4) (cls t) f, if_pos (Finset.mem_range.mpr (cls_lt t))]
  · simp [hP]

theorem card_lt (P : R → Prop) [DecidablePred P] : (Finset.univ.filter P).card < 32 := by
  have h1 : (Finset.univ.filter P).card ≤ (Finset.univ : Finset R).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset R).card = 16 := by
    rw [Finset.card_eq_sum_ones, sum_R]
    simp
  omega

/-- From the base 32 encoding to the class counts. -/
theorem counts_of_hash (P : R → Prop) [DecidablePred P] (k : ℕ)
    (h : (∑ t ∈ Finset.range 16, if P (dec t) then 32 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 4, MX k j * 32 ^ j)
    (hk : ∀ j < 4, MX k j < 32) :
    ∀ j < 4, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card = MX k j := by
  have e : (∑ t : R, if P t then 32 ^ cls t else 0) =
      ∑ j ∈ Finset.range 4, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * 32 ^ j :=
    sum_cls P (fun j => 32 ^ j)
  refine digits_unique 32 (by norm_num) 4
    (fun j => (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card) (fun j => MX k j)
    (fun j _ => card_lt _) hk ?_
  rw [← e, sum_R, ← h]
  apply Finset.sum_congr rfl
  intro t ht
  unfold cls
  rw [enc_dec t (Finset.mem_range.mp ht)]

/-- Initial class vector. -/
def L0 : List ℕ := [1, 1, 1, 0]

/-- Walk counts by class; coordinate 3 at time n+1 is the number of admissible walks with n+1 states. -/
def V : ℕ → ℕ → ℕ
  | 0, j => L0.getD j 0
  | n + 1, i => ∑ j ∈ Finset.range 4, MX i j * V n j

theorem V_succ (n i : ℕ) : V (n + 1) i = ∑ j ∈ Finset.range 4, MX i j * V n j := rfl

theorem base_ok : ∀ i < 16, (if ok (dec i) then 1 else 0) = L0.getD (clsN i) 0 := by decide +kernel

theorem hashS' (s : R) :
    (∑ t ∈ Finset.range 16, if ok s ∧ compat s (dec t) then 32 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 4, MX (cls s) j * 32 ^ j := by
  have h := hashS (enc s) (enc_lt s)
  unfold HashP at h
  rw [dec_enc, HX_sum] at h
  exact h

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    have h := base_ok (enc s) (enc_lt s)
    rw [dec_enc] at h
    exact h
  | succ n ih =>
    intro s
    rw [F_succ, V_succ]
    simp only [ih]
    rw [sum_cls (fun t => ok s ∧ compat s t) (V n)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [counts_of_hash (fun t => ok s ∧ compat s t) (cls s) (hashS' s) (fun j _ => MX_lt _ j) j
      (Finset.mem_range.mp hj)]

theorem count_walks (n : ℕ) :
    Nat.card {y : Fin (n + 1) → R // Walk y ∧ Init (y 0)} = V (n + 1) 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ Init (x 0) then 1 else 0) =
      ∑ s : R, if Init s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if Init s then
        (∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0) else 0) =
        ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ Init (y 0) then 1 else 0) else 0 := by
      intro s
      by_cases hs : Init s
      · rw [if_pos hs]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl]
          exact if_congr ⟨fun h => ⟨h.1, hs⟩, fun h => ⟨h.1, rfl⟩⟩ rfl rfl
        · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = s) from fun h => hy h.2)]
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [sum_cls Init (V n), V_succ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [counts_of_hash Init 3 hashI (fun j _ => MX_lt _ j) j (Finset.mem_range.mp hj)]

theorem V_step (n : ℕ) (L L' : List ℕ) (hL : L.length ≤ 4) (h : ∀ j < 4, V n j = L.getD j 0)
    (h' : stepv L = L') : ∀ i < 4, V (n + 1) i = L'.getD i 0 := by
  intro i hi
  rw [V_succ, ← h', stepv_getD L hL i]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])

theorem lit0 : ∀ j < 4, V 0 j = L0.getD j 0 := fun _ _ => rfl

def L1 : List ℕ := [2, 3, 4, 16]
theorem lit1 : ∀ i < 4, V 1 i = L1.getD i 0 := V_step 0 L0 L1 (by decide) lit0 (by decide +kernel)
def L2 : List ℕ := [6, 9, 14, 48]
theorem lit2 : ∀ i < 4, V 2 i = L2.getD i 0 := V_step 1 L1 L2 (by decide) lit1 (by decide +kernel)
def L3 : List ℕ := [18, 29, 46, 152]
theorem lit3 : ∀ i < 4, V 3 i = L3.getD i 0 := V_step 2 L2 L3 (by decide) lit2 (by decide +kernel)
def L4 : List ℕ := [58, 93, 150, 488]
theorem lit4 : ∀ i < 4, V 4 i = L4.getD i 0 := V_step 3 L3 L4 (by decide) lit3 (by decide +kernel)
def L5 : List ℕ := [186, 301, 486, 1576]
theorem lit5 : ∀ i < 4, V 5 i = L5.getD i 0 := V_step 4 L4 L5 (by decide) lit4 (by decide +kernel)
def L6 : List ℕ := [602, 973, 1574, 5096]
theorem lit6 : ∀ i < 4, V 6 i = L6.getD i 0 := V_step 5 L5 L6 (by decide) lit5 (by decide +kernel)

theorem vbase : ∀ i < 4, ((L4.getD i 0 : ℕ) : ℤ) = (-4 : ℤ) * ((L1.getD i 0 : ℕ) : ℤ) + (2 : ℤ) * ((L2.getD i 0 : ℕ) : ℤ) + (3 : ℤ) * ((L3.getD i 0 : ℕ) : ℤ) := by decide +kernel

/-- A linear recurrence for the whole class vector (by linearity of the transfer step). -/
theorem vrec : ∀ n : ℕ, ∀ i < 4, (V (n + 4) i : ℤ) = (-4 : ℤ) * (V (n + 1) i : ℤ) + (2 : ℤ) * (V (n + 2) i : ℤ) + (3 : ℤ) * (V (n + 3) i : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    simp only [Nat.zero_add]
    rw [lit4 i hi, lit1 i hi, lit2 i hi, lit3 i hi]
    exact vbase i hi
  | succ n ih =>
    intro i hi
    have e : ∀ m, (V (n + 1 + m) i : ℤ) = ∑ j ∈ Finset.range 4, (MX i j : ℤ) * (V (n + m) j : ℤ) := by
      intro m
      rw [show n + 1 + m = (n + m) + 1 by omega, V_succ]
      push_cast
      rfl
    simp only [e, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_range.mp hj)]
    ring

theorem a_eq (n : ℕ) : a (n + 1) = V (n + 1) 3 := by
  unfold a
  rw [← count_walks]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    ⟨fun h => ⟨⟨fun _ => trivial, fun i => h i.castSucc (Nat.succ_lt_succ i.isLt)⟩, trivial⟩,
      fun h i hi => h.1.2 ⟨i, by omega⟩⟩))

theorem a_1 : a 1 = 16 := (a_eq 0).trans ((lit1 3 (by norm_num)).trans (by decide))
theorem a_2 : a 2 = 48 := (a_eq 1).trans ((lit2 3 (by norm_num)).trans (by decide))
theorem a_3 : a 3 = 152 := (a_eq 2).trans ((lit3 3 (by norm_num)).trans (by decide))
theorem a_4 : a 4 = 488 := (a_eq 3).trans ((lit4 3 (by norm_num)).trans (by decide))
theorem a_5 : a 5 = 1576 := (a_eq 4).trans ((lit5 3 (by norm_num)).trans (by decide))

theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = (3 : ℤ) * (a (m + 3) : ℤ) + (2 : ℤ) * (a (m + 2) : ℤ) + (-4 : ℤ) * (a (m + 1) : ℤ) := by
  have h := vrec m 3 (by norm_num)
  rw [show V (m + 4) 3 = a (m + 4) from (a_eq (m + 3)).symm, show V (m + 3) 3 = a (m + 3) from (a_eq (m + 2)).symm, show V (m + 2) 3 = a (m + 2) from (a_eq (m + 1)).symm, show V (m + 1) 3 = a (m + 1) from (a_eq (m)).symm] at h
  linear_combination h

theorem closedT : ∀ k : ℕ,
    (5 * (a (k + 1) : ℝ) = 8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 1) + (1 + Real.sqrt 5) ^ (k + 1) * (11 + 5 * Real.sqrt 5)) ∧
    (5 * (a (k + 2) : ℝ) = 8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 2) + (1 + Real.sqrt 5) ^ (k + 2) * (11 + 5 * Real.sqrt 5)) ∧
    (5 * (a (k + 3) : ℝ) = 8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 3) + (1 + Real.sqrt 5) ^ (k + 3) * (11 + 5 * Real.sqrt 5)) := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have r1 : (1 + Real.sqrt 5) ^ 3 = 3 * (1 + Real.sqrt 5) ^ 2 + 2 * (1 + Real.sqrt 5) - 4 := by
    linear_combination (Real.sqrt 5) * hs
  have r2 : (1 - Real.sqrt 5) ^ 3 = 3 * (1 - Real.sqrt 5) ^ 2 + 2 * (1 - Real.sqrt 5) - 4 := by
    linear_combination (-Real.sqrt 5) * hs
  intro k
  induction k with
  | zero =>
    simp only [Nat.zero_add, a_1, a_2, a_3]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (-10 : ℝ) * hs
    · linear_combination (-42 : ℝ) * hs
    · linear_combination (-10 * Real.sqrt 5 ^ 2 - 146) * hs
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have h := a_rec k
    have q := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at q
    rw [show k + 1 + 3 = k + 4 from rfl]
    linear_combination 5 * q + 3 * h3 + 2 * h2 - 4 * h1 -
      (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 1) * r2 - (1 + Real.sqrt 5) ^ (k + 1) * (11 + 5 * Real.sqrt 5) * r1

end OMAA223395Helpers

open OMA.S_oeis_a223395 OMAA223395Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223395.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    have h := a_rec m
    linear_combination h
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2)) = F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F') + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (8 * PowerSeries.X * (2 - 3 * PowerSeries.X ^ 2) : PowerSeries ℚ) = PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (24 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 4
    · interval_cases n <;> norm_num [a_1, a_2, a_3, a_4]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
      have h := a_rec (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega, show j + 1 + 3 = j + 4 by omega, show j + 1 + 4 = j + 5 by omega] at h
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      simp
      linear_combination q
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := (closedT k).1
    rw [eq_div_iff (by norm_num)]
    linear_combination h
