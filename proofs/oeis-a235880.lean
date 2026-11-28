import OMAStatements.S_oeis_a235880
import Mathlib

-- Proof of the conjectures in OEIS A235880 (statement by @ivillar).
-- Idea: the subblock conditions involve only consecutive rows, so the count is a walk count on rows
-- (transfer matrix; the walk lemmas and the class bookkeeping are adapted from the accepted site proof
-- proofs/oeis-a235878.lean, the 3-column sibling). A 2 X 2 block p q / r s satisfies the median condition
-- iff its entries are u, u, v, v, i.e. iff (p = q and r = s) or (p = r and q = s) or (p = s and q = r);
-- for Fin 3 this is: r is p or q when p differs from q, and s = nxt p q r (s = r when p = q, else s is the
-- other one of p, q). So a successor t of a row s is determined by its first entry c (t = gen s c), and
-- checking the 243 x 3 pairs (s, c) by kernel computation:
-- * a constant row has exactly 3 successors (the constant rows);
-- * a row with exactly two distinct values has 2 successors, of the same kind;
-- * a row with three distinct values has 1 successor, of the same kind.
-- There are 3, 90 and 150 rows of these kinds, hence a(n) = 3*3^n + 90*2^n + 150 = 3*(50 + 15*2^(1+n) + 3^n),
-- and the recurrence and the g.f. follow.

namespace OMAA235880Helpers

open OMA.S_oeis_a235880

instance (p q r s : Fin 3) : Decidable (Med4 p q r s) := by
  unfold Med4; infer_instance

instance (u v : Fin 5 → Fin 3) : Decidable (BlockOK u v) := by
  unfold BlockOK; infer_instance

abbrev R := Fin 5 → Fin 3

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblocks they form satisfy the condition. -/
abbrev compat (r s : R) : Prop := BlockOK r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

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

/-! ### The successors of a row -/

/-- The lower right entry of a block with upper row a, b and lower left entry c. -/
def nxt (a b c : Fin 3) : Fin 3 := if a = b then c else if c = a then b else a

/-- The lower left entry c is admissible below the upper row a, b. -/
abbrev okc (a b c : Fin 3) : Prop := a = b ∨ c = a ∨ c = b

theorem med_iff : ∀ a b c d : Fin 3, Med4 a b c d ↔ okc a b c ∧ d = nxt a b c := by
  decide +kernel

def g1 (s : R) (c : Fin 3) : Fin 3 := nxt (s 0) (s 1) c
def g2 (s : R) (c : Fin 3) : Fin 3 := nxt (s 1) (s 2) (g1 s c)
def g3 (s : R) (c : Fin 3) : Fin 3 := nxt (s 2) (s 3) (g2 s c)
def g4 (s : R) (c : Fin 3) : Fin 3 := nxt (s 3) (s 4) (g3 s c)

/-- The row below s that starts with c. -/
def gen (s : R) (c : Fin 3) : R := ![c, g1 s c, g2 s c, g3 s c, g4 s c]

/-- The row gen s c is a successor of s. -/
abbrev valid (s : R) (c : Fin 3) : Prop :=
  okc (s 0) (s 1) c ∧ okc (s 1) (s 2) (g1 s c) ∧ okc (s 2) (s 3) (g2 s c) ∧ okc (s 3) (s 4) (g3 s c)

theorem gen_zero (s : R) (c : Fin 3) : gen s c 0 = c := rfl

theorem compat_iff (s t : R) : compat s t ↔ valid s (t 0) ∧ t = gen s (t 0) := by
  constructor
  · intro h
    have h0 : Med4 (s 0) (s 1) (t 0) (t 1) := h 0
    have h1 : Med4 (s 1) (s 2) (t 1) (t 2) := h 1
    have h2 : Med4 (s 2) (s 3) (t 2) (t 3) := h 2
    have h3 : Med4 (s 3) (s 4) (t 3) (t 4) := h 3
    rw [med_iff] at h0 h1 h2 h3
    have e1 : t 1 = g1 s (t 0) := h0.2
    have e2 : t 2 = g2 s (t 0) := by rw [g2, ← e1]; exact h1.2
    have e3 : t 3 = g3 s (t 0) := by rw [g3, ← e2]; exact h2.2
    have e4 : t 4 = g4 s (t 0) := by rw [g4, ← e3]; exact h3.2
    refine ⟨⟨h0.1, ?_, ?_, ?_⟩, ?_⟩
    · rw [← e1]; exact h1.1
    · rw [← e2]; exact h2.1
    · rw [← e3]; exact h3.1
    · funext i
      fin_cases i
      · rfl
      · exact e1
      · exact e2
      · exact e3
      · exact e4
  · rintro ⟨hv, ht⟩
    rw [ht]
    generalize t 0 = c at hv
    intro j
    fin_cases j
    · exact (med_iff _ _ _ _).2 ⟨hv.1, rfl⟩
    · exact (med_iff _ _ _ _).2 ⟨hv.2.1, rfl⟩
    · exact (med_iff _ _ _ _).2 ⟨hv.2.2.1, rfl⟩
    · exact (med_iff _ _ _ _).2 ⟨hv.2.2.2, rfl⟩

/-- Walk counts by row type: 3^n, 2^n or 1 (each class is closed under succession). -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * f n
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * g n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => h n

abbrev Z (t : R) : Prop := t 0 = t 1 ∧ t 1 = t 2 ∧ t 2 = t 3 ∧ t 3 = t 4
abbrev O (t : R) : Prop := (∀ i, t i ≠ 0) ∨ (∀ i, t i ≠ 1) ∨ (∀ i, t i ≠ 2)

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem sum_compat (n : ℕ) (s : R) :
    (∑ t : R, if ok s ∧ compat s t then V n t else 0) =
      ∑ c : Fin 3, if valid s c then V n (gen s c) else 0 := by
  have h1 : ∀ t : R, (if ok s ∧ compat s t then V n t else 0) =
      ∑ c : Fin 3, if valid s c ∧ t = gen s c then V n t else 0 := by
    intro t
    rw [Finset.sum_eq_single (t 0)]
    · simp only [ok, true_and]
      exact if_congr (compat_iff s t) rfl rfl
    · intro c _ hc
      rw [if_neg]
      rintro ⟨_, ht⟩
      apply hc
      rw [ht, gen_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hv : valid s c
  · have h2 : ∀ t : R, (if valid s c ∧ t = gen s c then V n t else 0) =
        if t = gen s c then V n t else 0 := fun t => if_congr (and_iff_right hv) rfl rfl
    rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
      if_pos hv]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg (fun h => hv h.1)]

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = ((if P ∧ Z t then f n else 0) +
      (if P ∧ ¬ Z t ∧ O t then f.g n else 0)) + (if P ∧ ¬ Z t ∧ ¬ O t then f.h n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.1 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2)]
      by_cases h3 : O t
      · rw [if_pos h3, if_pos (show P ∧ ¬ Z t ∧ O t from ⟨h1, h2, h3⟩),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.2 h3)]
        ring
      · rw [if_neg h3, if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h3 h.2.2),
          if_pos (show P ∧ ¬ Z t ∧ ¬ O t from ⟨h1, h2, h3⟩)]
        ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h1 h.1)]

theorem sum_V {ι : Type} [Fintype ι] (n : ℕ) (g : ι → R) (P : ι → Prop) [DecidablePred P] :
    (∑ i : ι, if P i then V n (g i) else 0) =
      (Finset.univ.filter (fun i => P i ∧ Z (g i))).card * f n +
      (Finset.univ.filter (fun i => P i ∧ ¬ Z (g i) ∧ O (g i))).card * f.g n +
      (Finset.univ.filter (fun i => P i ∧ ¬ Z (g i) ∧ ¬ O (g i))).card * f.h n := by
  rw [Finset.sum_congr rfl (fun i _ => split_V n (P i) (g i)), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero, mul_zero]

theorem cZ : ∀ s : R, (Finset.univ.filter (fun c : Fin 3 => valid s c ∧ Z (gen s c))).card =
    if Z s then 3 else 0 := by
  decide +kernel

theorem cO : ∀ s : R, (Finset.univ.filter (fun c : Fin 3 => valid s c ∧ ¬ Z (gen s c) ∧ O (gen s c))).card =
    if Z s then 0 else if O s then 2 else 0 := by
  decide +kernel

theorem cN : ∀ s : R, (Finset.univ.filter (fun c : Fin 3 => valid s c ∧ ¬ Z (gen s c) ∧ ¬ O (gen s c))).card =
    if Z s then 0 else if O s then 0 else 1 := by
  decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z (id t))).card = 3 := by decide +kernel
theorem tO : (Finset.univ.filter (fun t : R => True ∧ ¬ Z (id t) ∧ O (id t))).card = 90 := by decide +kernel
theorem tN : (Finset.univ.filter (fun t : R => True ∧ ¬ Z (id t) ∧ ¬ O (id t))).card = 150 := by
  decide +kernel

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    simp only [ok, if_true]
    split_ifs <;> rfl
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_compat, sum_V n (gen s) (valid s), cZ s, cO s, cN s]
    unfold V
    split_ifs <;> simp [f, f.g, f.h] <;> ring

theorem a_eq (n : ℕ) : a n = 3 * f n + 90 * f.g n + 150 * f.h n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if True then F n s else 0 := by
    unfold F
    simp only [if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [show (∑ s : R, if True then V n s else 0) = ∑ s : R, if True then V n (id s) else 0 from rfl,
    sum_V n id (fun _ => True), tZ, tO, tN]

theorem f_pow (n : ℕ) : f n = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f, ih]; ring

theorem g_pow (n : ℕ) : f.g n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.g, ih]; ring

theorem h_one (n : ℕ) : f.h n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.h, ih]

theorem a_closed (n : ℕ) : a n = 3 * 3 ^ n + 90 * 2 ^ n + 150 := by
  rw [a_eq, f_pow, g_pow, h_one]
  try ring

end OMAA235880Helpers

open OMA.S_oeis_a235880 OMAA235880Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a235880.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, a_closed, a_closed, a_closed, a_closed]
    push_cast
    ring
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X)) =
        F' - PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * F') +
          PowerSeries.C (11 : ℚ) * (PowerSeries.X ^ 2 * F') -
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (3 * PowerSeries.X * (113 - 499 * PowerSeries.X + 486 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (339 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (1497 : ℚ) * PowerSeries.X ^ 2 +
          PowerSeries.C (1458 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a_closed]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      simp [a_closed]
      ring
  · rw [a_closed]
    ring
