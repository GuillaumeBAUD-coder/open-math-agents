import OMAStatements.S_oeis_a250762
import Mathlib

-- Proof of Barker's conjectures in OEIS A250762 (statement by @marcusbuffett).
-- Idea. For two consecutive columns c (column j-1) and d (column j) of the array, the conditions of all the
-- blocks they form say that delta = d - c is nondecreasing down the column and delta_0 + delta_1 >= 0. Hence
-- d_7 >= c_7, with equality only when d = c (then every delta_i is 0). So in a walk of n + 1 columns at most
-- two steps change the column (c_7 lies in 0..2), and the number of walks from a column c is
-- F(n, c) = 1 + n A(c) + C(n, 2) B(c), where A(c) counts the columns d /= c that may follow c and B(c) the
-- pairs of such proper steps. Summing, a(n) = 3^8 + n SA + C(n, 2) SB. The two constants come from
-- a(1) = 29012 and a(2) = 67356, computed by a transfer matrix along the ROWS (rows of length 2 and 3, 9 and
-- 27 states, 7 steps, a kernel-checked table of walk counts). So a(n) = 6561 + 22451 n + 15893 C(n, 2), and
-- the g.f. and the recurrence follow (third differences vanish).
-- Sources: the walk lemmas (walk_cons, F_zero, F_succ) are adapted from the accepted site proof
-- proofs/oeis-a235878.lean; the coefficient extraction for the g.f. follows proofs/oeis-a221574.lean.

namespace OMAA250762Helpers

/-! ### Columns: walks of columns of length 8 -/

namespace Cols

open OMA.S_oeis_a250762

abbrev R := Fin 8 → Fin 3

/-- Consecutive columns c (left), d (right): every 2 X 2 block they form satisfies `blk`. -/
abbrev compat (c d : R) : Prop :=
  ∀ i : Fin 7, blk (c i.castSucc) (d i.castSucc) (c i.succ) (d i.succ)

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

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

/-- The number of walks is the sum of the walk counts from each start. -/
theorem total (n : ℕ) : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, F n s := by
  unfold F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) =
      if y 0 = s then (if Walk y then 1 else 0) else 0 := by
    intro s
    by_cases h : y 0 = s
    · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
    · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem compat_refl (c : R) : compat c c := by
  intro i
  unfold blk
  constructor <;> omega

/-- Along a step of columns the last entry does not decrease, and it increases unless the column is kept. -/
theorem mono (c d : R) (h : compat c d) : ((c 7 : Fin 3) : ℕ) ≤ d 7 ∧ (c ≠ d → ((c 7 : Fin 3) : ℕ) < d 7) := by
  have h0 : blk (c 0) (d 0) (c 1) (d 1) := h 0
  have h1 : blk (c 1) (d 1) (c 2) (d 2) := h 1
  have h2 : blk (c 2) (d 2) (c 3) (d 3) := h 2
  have h3 : blk (c 3) (d 3) (c 4) (d 4) := h 3
  have h4 : blk (c 4) (d 4) (c 5) (d 5) := h 4
  have h5 : blk (c 5) (d 5) (c 6) (d 6) := h 5
  have h6 : blk (c 6) (d 6) (c 7) (d 7) := h 6
  unfold blk at h0 h1 h2 h3 h4 h5 h6
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  obtain ⟨a3, b3⟩ := h3
  obtain ⟨a4, b4⟩ := h4
  obtain ⟨a5, b5⟩ := h5
  obtain ⟨a6, b6⟩ := h6
  refine ⟨by omega, fun hne => ?_⟩
  by_contra hlt
  apply hne
  funext i
  fin_cases i
  · show c 0 = d 0
    exact Fin.ext (by omega)
  · show c 1 = d 1
    exact Fin.ext (by omega)
  · show c 2 = d 2
    exact Fin.ext (by omega)
  · show c 3 = d 3
    exact Fin.ext (by omega)
  · show c 4 = d 4
    exact Fin.ext (by omega)
  · show c 5 = d 5
    exact Fin.ext (by omega)
  · show c 6 = d 6
    exact Fin.ext (by omega)
  · show c 7 = d 7
    exact Fin.ext (by omega)

/-- There are no three proper steps in a row. -/
theorem no3 (c d e f : R) (h1 : compat c d) (n1 : d ≠ c) (h2 : compat d e) (n2 : e ≠ d)
    (h3 : compat e f) (n3 : f ≠ e) : False := by
  have m1 := (mono c d h1).2 (Ne.symm n1)
  have m2 := (mono d e h2).2 (Ne.symm n2)
  have m3 := (mono e f h3).2 (Ne.symm n3)
  have := (f 7).isLt
  omega

/-- The number of proper successors. -/
def A (c : R) : ℕ := ∑ d : R, if compat c d ∧ d ≠ c then 1 else 0

/-- The number of proper two-step paths. -/
def B (c : R) : ℕ := ∑ d : R, if compat c d ∧ d ≠ c then A d else 0

/-- tri n = n (n - 1) / 2. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n

theorem B_zero (c d : R) (h : compat c d) (hn : d ≠ c) : B d = 0 := by
  unfold B
  apply Finset.sum_eq_zero
  intro e _
  split_ifs with he
  · unfold A
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg]
    rintro ⟨hf, hfn⟩
    exact no3 c d e f h hn he.1 he.2 hf hfn
  · rfl

theorem split_sum (c : R) (g : R → ℕ) :
    (∑ d : R, if ok c ∧ compat c d then g d else 0) =
      g c + ∑ d : R, if compat c d ∧ d ≠ c then g d else 0 := by
  have h : ∀ d : R, (if ok c ∧ compat c d then g d else 0) =
      (if d = c then g d else 0) + (if compat c d ∧ d ≠ c then g d else 0) := by
    intro d
    by_cases hd : d = c
    · subst hd
      rw [if_pos ⟨trivial, compat_refl d⟩, if_pos rfl, if_neg (fun h => h.2 rfl), add_zero]
    · rw [if_neg hd, zero_add]
      exact if_congr ⟨fun h => ⟨h.2, hd⟩, fun h => ⟨trivial, h.1⟩⟩ rfl rfl
  rw [Finset.sum_congr rfl (fun d _ => h d), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]

theorem F_closed (n : ℕ) : ∀ c : R, F n c = 1 + n * A c + tri n * B c := by
  induction n with
  | zero => intro c; rw [F_zero]; simp [tri]
  | succ n ih =>
    intro c
    rw [F_succ]
    simp only [ih]
    rw [split_sum c]
    have h : ∀ d : R, (if compat c d ∧ d ≠ c then 1 + n * A d + tri n * B d else 0) =
        (if compat c d ∧ d ≠ c then 1 else 0) + n * (if compat c d ∧ d ≠ c then A d else 0) +
          tri n * (if compat c d ∧ d ≠ c then B d else 0) := by
      intro d
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun d _ => h d), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hB : (∑ d : R, if compat c d ∧ d ≠ c then B d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      split_ifs with hd
      · exact B_zero c d hd.1 hd.2
      · rfl
    rw [hB]
    show 1 + n * A c + tri n * B c + (A c + n * B c + tri n * 0) = 1 + (n + 1) * A c + tri (n + 1) * B c
    simp only [tri]
    ring

theorem a_cols (n : ℕ) : a n = ∑ y : Fin (n + 1) → R, if Walk y then 1 else 0 := by
  unfold a
  rw [Finset.card_filter, ← (Equiv.piComm (fun (_ : Fin (n + 1)) (_ : Fin 8) => Fin 3)).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  exact if_congr ⟨fun h => ⟨fun _ => trivial, fun j i => h i j⟩, fun h i j => h.2 j i⟩ rfl rfl

theorem card_R : (∑ _c : R, (1 : ℕ)) = 6561 := by
  simp [Finset.card_univ]

theorem a_poly (n : ℕ) : a n = 6561 + n * (∑ c : R, A c) + tri n * (∑ c : R, B c) := by
  rw [a_cols, total]
  simp only [F_closed]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, card_R]

end Cols

/-! ### Rows of length 2: the arrays with 2 columns, by transfer along the rows -/

namespace Rows2

open OMA.S_oeis_a250762

abbrev R := Fin 2 → Fin 3

/-- Consecutive rows u (upper), v (lower): every 2 X 2 block they form satisfies `blk`. -/
abbrev compat (u v : R) : Prop :=
  ∀ j : Fin 1, blk (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

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

/-- The number of walks is the sum of the walk counts from each start. -/
theorem total (n : ℕ) : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, F n s := by
  unfold F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) =
      if y 0 = s then (if Walk y then 1 else 0) else 0 := by
    intro s
    by_cases h : y 0 = s
    · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
    · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The code of a row in base 3. -/
def code (s : R) : ℕ := ((s 0 : Fin 3) : ℕ) + 3 * ((s 1 : Fin 3) : ℕ)

/-- The walk counts F k s for k = 0..7, indexed by the code of s (computed by the transfer recursion). -/
def tab : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1],
    [6, 3, 1, 3, 6, 3, 1, 3, 6],
    [25, 7, 1, 7, 25, 7, 1, 7, 25],
    [90, 15, 1, 15, 90, 15, 1, 15, 90],
    [301, 31, 1, 31, 301, 31, 1, 31, 301],
    [966, 63, 1, 63, 966, 63, 1, 63, 966],
    [3025, 127, 1, 127, 3025, 127, 1, 127, 3025],
    [9330, 255, 1, 255, 9330, 255, 1, 255, 9330]]

def t (k : ℕ) (s : R) : ℕ := (tab.getD k []).getD (code s) 0

theorem t_zero : ∀ s : R, (if ok s then 1 else 0) = t 0 s := by decide +kernel

theorem t_step : ∀ k : Fin 7, ∀ s : R,
    (∑ u : R, if ok s ∧ compat s u then t k u else 0) = t (k + 1) s := by decide +kernel

theorem t_total : (∑ s : R, t 7 s) = 29012 := by decide +kernel

theorem F_t : ∀ k : ℕ, k ≤ 7 → ∀ s : R, F k s = t k s := by
  intro k
  induction k with
  | zero => intro _ s; rw [F_zero]; exact t_zero s
  | succ k ih =>
    intro hk s
    rw [F_succ]
    have h : ∀ u : R, (if ok s ∧ compat s u then F k u else 0) = if ok s ∧ compat s u then t k u else 0 := by
      intro u
      rw [ih (by omega) u]
    rw [Finset.sum_congr rfl (fun u _ => h u)]
    exact t_step ⟨k, by omega⟩ s

theorem walks_total : (∑ x : Fin (7 + 1) → R, if Walk x then 1 else 0) = 29012 := by
  rw [total, Finset.sum_congr rfl (fun s _ => F_t 7 (le_refl 7) s)]
  exact t_total

end Rows2

/-! ### Rows of length 3: the arrays with 3 columns, by transfer along the rows -/

namespace Rows3

open OMA.S_oeis_a250762

abbrev R := Fin 3 → Fin 3

/-- Consecutive rows u (upper), v (lower): every 2 X 2 block they form satisfies `blk`. -/
abbrev compat (u v : R) : Prop :=
  ∀ j : Fin 2, blk (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

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

/-- The number of walks is the sum of the walk counts from each start. -/
theorem total (n : ℕ) : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, F n s := by
  unfold F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) =
      if y 0 = s then (if Walk y then 1 else 0) else 0 := by
    intro s
    by_cases h : y 0 = s
    · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
    · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The code of a row in base 3. -/
def code (s : R) : ℕ := ((s 0 : Fin 3) : ℕ) + 3 * ((s 1 : Fin 3) : ℕ) + 9 * ((s 2 : Fin 3) : ℕ)

/-- The walk counts F k s for k = 0..7, indexed by the code of s (computed by the transfer recursion). -/
def tab : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [10, 4, 1, 1, 4, 1, 0, 0, 1, 4, 1, 0, 4, 10, 4, 0, 1, 4, 1, 0, 0, 1, 4, 1, 1, 4, 10],
    [49, 10, 1, 1, 10, 1, 0, 0, 1, 10, 1, 0, 10, 49, 10, 0, 1, 10, 1, 0, 0, 1, 10, 1, 1, 10, 49],
    [190, 22, 1, 1, 22, 1, 0, 0, 1, 22, 1, 0, 22, 190, 22, 0, 1, 22, 1, 0, 0, 1, 22, 1, 1, 22, 190],
    [661, 46, 1, 1, 46, 1, 0, 0, 1, 46, 1, 0, 46, 661, 46, 0, 1, 46, 1, 0, 0, 1, 46, 1, 1, 46, 661],
    [2170, 94, 1, 1, 94, 1, 0, 0, 1, 94, 1, 0, 94, 2170, 94, 0, 1, 94, 1, 0, 0, 1, 94, 1, 1, 94, 2170],
    [6889, 190, 1, 1, 190, 1, 0, 0, 1, 190, 1, 0, 190, 6889, 190, 0, 1, 190, 1, 0, 0, 1, 190, 1, 1, 190, 6889],
    [21430, 382, 1, 1, 382, 1, 0, 0, 1, 382, 1, 0, 382, 21430, 382, 0, 1, 382, 1, 0, 0, 1, 382, 1, 1, 382, 21430]]

def t (k : ℕ) (s : R) : ℕ := (tab.getD k []).getD (code s) 0

theorem t_zero : ∀ s : R, (if ok s then 1 else 0) = t 0 s := by decide +kernel

theorem t_step : ∀ k : Fin 7, ∀ s : R,
    (∑ u : R, if ok s ∧ compat s u then t k u else 0) = t (k + 1) s := by decide +kernel

theorem t_total : (∑ s : R, t 7 s) = 67356 := by decide +kernel

theorem F_t : ∀ k : ℕ, k ≤ 7 → ∀ s : R, F k s = t k s := by
  intro k
  induction k with
  | zero => intro _ s; rw [F_zero]; exact t_zero s
  | succ k ih =>
    intro hk s
    rw [F_succ]
    have h : ∀ u : R, (if ok s ∧ compat s u then F k u else 0) = if ok s ∧ compat s u then t k u else 0 := by
      intro u
      rw [ih (by omega) u]
    rw [Finset.sum_congr rfl (fun u _ => h u)]
    exact t_step ⟨k, by omega⟩ s

theorem walks_total : (∑ x : Fin (7 + 1) → R, if Walk x then 1 else 0) = 67356 := by
  rw [total, Finset.sum_congr rfl (fun s _ => F_t 7 (le_refl 7) s)]
  exact t_total

end Rows3

open OMA.S_oeis_a250762

theorem a_one : a 1 = 29012 := by
  have h : a 1 = ∑ x : Fin (7 + 1) → Rows2.R, if Rows2.Walk x then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun x _ => if_congr ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩ rfl rfl)
  rw [h, Rows2.walks_total]

theorem a_two : a 2 = 67356 := by
  have h : a 2 = ∑ x : Fin (7 + 1) → Rows3.R, if Rows3.Walk x then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun x _ => if_congr ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩ rfl rfl)
  rw [h, Rows3.walks_total]

theorem tri_one : Cols.tri 1 = 0 := rfl
theorem tri_two : Cols.tri 2 = 1 := rfl

theorem a_closed (n : ℕ) : a n = 6561 + 22451 * n + 15893 * Cols.tri n := by
  have h1 := Cols.a_poly 1
  have h2 := Cols.a_poly 2
  rw [a_one, tri_one] at h1
  rw [a_two, tri_two] at h2
  have hA : (∑ c : Cols.R, Cols.A c) = 22451 := by omega
  have hB : (∑ c : Cols.R, Cols.B c) = 15893 := by omega
  rw [Cols.a_poly n, hA, hB]
  ring

theorem tri_q (n : ℕ) : (Cols.tri n : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp [Cols.tri]
  | succ k ih =>
    simp only [Cols.tri]
    push_cast
    rw [ih]
    ring

theorem q (m : ℕ) : (a m : ℚ) = 6561 + 22451 * m + 15893 * (m * (m - 1) / 2) := by
  rw [a_closed]
  push_cast
  rw [tri_q]

end OMAA250762Helpers

open OMA.S_oeis_a250762 OMAA250762Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a250762.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have q1 : (a 1 : ℚ) = 29012 := by rw [q]; norm_num
    have q2 : (a 2 : ℚ) = 67356 := by rw [q]; norm_num
    have q3 : (a 3 : ℚ) = 121593 := by rw [q]; norm_num
    obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, b = fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) := ⟨_, rfl⟩
    have bk : ∀ k, b (k + 1) = (a (k + 1) : ℚ) := by
      intro k
      rw [hb]
      exact if_neg (Nat.succ_ne_zero k)
    have b0 : b 0 = 0 := by
      rw [hb]
      exact if_pos rfl
    have b1 : b 1 = 29012 := (bk 0).trans q1
    have b2 : b 2 = 67356 := (bk 1).trans q2
    have b3 : b 3 = 121593 := (bk 2).trans q3
    obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk b := ⟨_, rfl⟩
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = A by rw [hA, hb]]
    have cA : ∀ m, PowerSeries.coeff m A = b m := by
      intro m
      rw [hA, PowerSeries.coeff_mk]
    have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
    have e : A * (1 - PowerSeries.X) ^ 3 =
        A - PowerSeries.C (3 : ℚ) * (A * PowerSeries.X ^ 1) +
          PowerSeries.C (3 : ℚ) * (A * PowerSeries.X ^ 2) - A * PowerSeries.X ^ 3 := by
      rw [h3]
      ring
    have e2 : (PowerSeries.X * (29012 - 19680 * PowerSeries.X + 6561 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (29012 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (19680 : ℚ) * PowerSeries.X ^ 2 +
          PowerSeries.C (6561 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    refine e.trans (Eq.trans ?_ e2.symm)
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
        norm_num [b0, b1, b2, b3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have t0 : PowerSeries.coeff (k + 4) A = (a (k + 4) : ℚ) := by
        rw [cA]
        exact bk (k + 3)
      have t1 : PowerSeries.coeff (k + 4) (A * PowerSeries.X ^ 1) = (a (k + 3) : ℚ) := by
        rw [show k + 4 = k + 3 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA]
        exact bk (k + 2)
      have t2 : PowerSeries.coeff (k + 4) (A * PowerSeries.X ^ 2) = (a (k + 2) : ℚ) := by
        rw [show k + 4 = k + 2 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA]
        exact bk (k + 1)
      have t3 : PowerSeries.coeff (k + 4) (A * PowerSeries.X ^ 3) = (a (k + 1) : ℚ) := by
        rw [show k + 4 = k + 1 + 3 by omega, PowerSeries.coeff_mul_X_pow, cA]
        exact bk k
      have u1 : PowerSeries.coeff (k + 4) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 4 = 1) by omega)]
      have u2 : PowerSeries.coeff (k + 4) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 4 = 2) by omega)]
      have u3 : PowerSeries.coeff (k + 4) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 4 = 3) by omega)]
      rw [t0, t1, t2, t3, u1, u2, u3, q (k + 4), q (k + 3), q (k + 2), q (k + 1)]
      push_cast
      ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    have key : ((a (k + 4) : ℤ) : ℚ) = ((3 * (a (k + 3) : ℤ) - 3 * a (k + 2) + a (k + 1) : ℤ) : ℚ) := by
      push_cast
      rw [q (k + 4), q (k + 3), q (k + 2), q (k + 1)]
      push_cast
      ring
    exact_mod_cast key
