import OMAStatements.S_oeis_a022444

-- Problem: A022444: Number of self-avoiding closed walks (from (0,0) to (0,0)) of length 2n in strip {-1, 0, 1} X Z.
-- Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)
-- Method: each cycle is the boundary of a two-column polyomino described by a row word over {L, R, B}
-- (layer-crossing parity plus a local degree rule); the words are counted by a transfer matrix.


/-!
Part C: counting the row words of a ring polymer in the strip, and their generating function.
Letters: 0 = L (only the left cell of the row), 1 = R (only the right cell), 2 = B (both cells).
-/

open PowerSeries Finset

namespace SAWC

abbrev Ltr := Fin 3

/-- cost of a bottom or top cap -/
def e (a : Ltr) : ℕ := if a = 2 then 2 else 1
/-- adjacent rows may not be `L` next to `R` -/
def comp (a b : Ltr) : Bool := !((a == 0 && b == 1) || (a == 1 && b == 0))
/-- two vertical edges per row, plus one horizontal edge when the row pattern changes -/
def stepc (a b : Ltr) : ℕ := if a = b then 2 else 3
/-- the row has its left cell, so its left side lies on the line `x = 0` -/
def lb (a : Ltr) : Bool := a != 1
def hlb : List Ltr → Bool
  | [] => false
  | b :: _ => lb b

theorem stepc_ge (a b : Ltr) : 2 ≤ stepc a b := by unfold stepc; split <;> omega

/-- valid words starting with `a` whose cost (perimeter without the bottom cap) is `p` -/
def S (p : ℕ) (a : Ltr) : Finset (List Ltr) :=
  if p < 3 then ∅ else
  (if p = 2 + e a then {[a]} else ∅) ∪
    (univ.filter (fun b => comp a b = true)).biUnion (fun b =>
      (S (p - stepc a b) b).image (List.cons a))
termination_by p
decreasing_by have := stepc_ge a b; omega

/-- perimeter of the rows `w` without the bottom cap -/
def cost : List Ltr → ℕ
  | [] => 0
  | [a] => 2 + e a
  | a :: b :: w => stepc a b + cost (b :: w)

/-- number of levels whose `x = 0` vertex lies on the polygon -/
def marks : List Ltr → ℕ
  | [] => 0
  | a :: w => (if lb a then 1 else 0) + marks w + (if (lb a && !hlb w) then 1 else 0)

theorem S_lt {p : ℕ} (h : p < 3) (a : Ltr) : S p a = ∅ := by
  rw [S]; simp [h]

theorem S_eq {p : ℕ} (h : 3 ≤ p) (a : Ltr) : S p a =
    (if p = 2 + e a then {[a]} else ∅) ∪
    (univ.filter (fun b => comp a b = true)).biUnion (fun b =>
      (S (p - stepc a b) b).image (List.cons a)) := by
  rw [S]; simp [show ¬ p < 3 by omega]

theorem head_of_mem {p : ℕ} {a : Ltr} {w : List Ltr} (hw : w ∈ S p a) : ∃ t, w = a :: t := by
  by_cases h : p < 3
  · rw [S_lt h] at hw; simp at hw
  · rw [S_eq (by omega)] at hw
    simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and, mem_image] at hw
    rcases hw with hw | ⟨b, _, t, _, rfl⟩
    · split_ifs at hw <;> simp_all
    · exact ⟨t, rfl⟩

theorem sum_S (f : List Ltr → ℤ) {p : ℕ} (h : 3 ≤ p) (a : Ltr) :
    ∑ w ∈ S p a, f w =
      (if p = 2 + e a then f [a] else 0) +
      ∑ b ∈ univ.filter (fun b => comp a b = true),
        ∑ w ∈ S (p - stepc a b) b, f (a :: w) := by
  rw [S_eq h, sum_union, sum_biUnion]
  · congr 1
    · split_ifs <;> simp
    · apply sum_congr rfl
      intro b _
      rw [sum_image]
      intro x _ y _ hxy
      exact List.cons_injective hxy
  · intro b _ b' _ hbb'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨t, ht, rfl⟩ := h1
    obtain ⟨t', ht', heq⟩ := h2
    have : t' = t := List.cons_injective heq
    subst this
    obtain ⟨s, rfl⟩ := head_of_mem ht
    obtain ⟨s', hs'⟩ := head_of_mem ht'
    simp at hs'
    exact hbb' hs'.1
  · rw [Finset.disjoint_left]
    intro w h1 h2
    split_ifs at h1
    · simp only [mem_singleton] at h1
      subst h1
      simp only [mem_biUnion, mem_image] at h2
      obtain ⟨b, _, t, ht, heq⟩ := h2
      have : t = [] := by simpa using heq
      subst this
      obtain ⟨s, hs⟩ := head_of_mem ht
      simp at hs
    · simp at h1

/-- count sequences -/
def Cs (p : ℕ) (a : Ltr) : ℤ := ∑ w ∈ S p a, (1 : ℤ)
def Ms (p : ℕ) (a : Ltr) : ℤ := ∑ w ∈ S p a, (marks w : ℤ)

theorem Cs_lt {p : ℕ} (h : p < 3) (a : Ltr) : Cs p a = 0 := by simp [Cs, S_lt h]
theorem Ms_lt {p : ℕ} (h : p < 3) (a : Ltr) : Ms p a = 0 := by simp [Ms, S_lt h]

theorem Cs_rec {p : ℕ} (h : 3 ≤ p) (a : Ltr) : Cs p a =
    (if p = 2 + e a then 1 else 0) +
    ∑ b ∈ univ.filter (fun b => comp a b = true), Cs (p - stepc a b) b := by
  unfold Cs; rw [sum_S _ h]

theorem marks_cons_of_mem {q : ℕ} {a b : Ltr} {w : List Ltr} (hw : w ∈ S q b) :
    (marks (a :: w) : ℤ) = (if lb a then 1 else 0) + marks w + (if (lb a && !lb b) then 1 else 0) := by
  obtain ⟨t, rfl⟩ := head_of_mem hw
  simp only [marks, hlb]
  push_cast
  split_ifs <;> simp

theorem Ms_rec {p : ℕ} (h : 3 ≤ p) (a : Ltr) : Ms p a =
    (if p = 2 + e a then (marks [a] : ℤ) else 0) +
    ∑ b ∈ univ.filter (fun b => comp a b = true),
      (Ms (p - stepc a b) b +
        ((if lb a then 1 else 0) + (if (lb a && !lb b) then 1 else 0)) * Cs (p - stepc a b) b) := by
  unfold Ms Cs; rw [sum_S _ h]
  congr 1
  apply sum_congr rfl
  intro b _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  rw [marks_cons_of_mem hw]
  ring

/-! Power series. -/

noncomputable def PC (a : Ltr) : PowerSeries ℤ := PowerSeries.mk (fun p => Cs p a)
noncomputable def PM (a : Ltr) : PowerSeries ℤ := PowerSeries.mk (fun p => Ms p a)

theorem coeff_X_pow_mul_mk (j p : ℕ) (f : ℕ → ℤ) :
    coeff p (X ^ j * PowerSeries.mk f) = if j ≤ p then f (p - j) else 0 := by
  rw [mul_comm, coeff_mul_X_pow', coeff_mk]

theorem eqC0 : PC 0 = X ^ 3 + X ^ 2 * PC 0 + X ^ 3 * PC 2 := by
  ext p
  simp only [PC, map_add, coeff_mk, coeff_X_pow, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Cs_lt hp]
    interval_cases p <;> simp [Cs_lt]
  · rw [Cs_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

theorem eqC1 : PC 1 = X ^ 3 + X ^ 2 * PC 1 + X ^ 3 * PC 2 := by
  ext p
  simp only [PC, map_add, coeff_mk, coeff_X_pow, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Cs_lt hp]
    interval_cases p <;> simp [Cs_lt]
  · rw [Cs_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

theorem eqC2 : PC 2 = X ^ 4 + X ^ 3 * PC 0 + X ^ 3 * PC 1 + X ^ 2 * PC 2 := by
  ext p
  simp only [PC, map_add, coeff_mk, coeff_X_pow, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Cs_lt hp]
    interval_cases p <;> simp [Cs_lt]
  · rw [Cs_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

theorem eqM0 : PM 0 = X ^ 3 + X ^ 3 + X ^ 2 * (PM 0 + PC 0) + X ^ 3 * (PM 2 + PC 2) := by
  ext p
  simp only [PC, PM, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms_lt]
  · rw [Ms_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e, lb, marks, hlb]
    split_ifs <;> first | omega | ring_nf

theorem eqM1 : PM 1 = X ^ 2 * PM 1 + X ^ 3 * PM 2 := by
  ext p
  simp only [PC, PM, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms_lt]
  · rw [Ms_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e, lb, marks, hlb]
    split_ifs <;> first | omega | ring_nf

theorem eqM2 : PM 2 = X ^ 4 + X ^ 4 + X ^ 3 * (PM 0 + PC 0) + X ^ 3 * (PM 1 + PC 1 + PC 1)
    + X ^ 2 * (PM 2 + PC 2) := by
  ext p
  simp only [PC, PM, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms_lt]
  · rw [Ms_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e, lb, marks, hlb]
    split_ifs <;> first | omega | ring_nf

/-- generating function of placed, marked words by perimeter -/
noncomputable def Y : PowerSeries ℤ := X * PM 0 + X * PM 1 + X ^ 2 * PM 2

theorem Y_gf_mul :
    Y * ((1 - 2 * X ^ 2) ^ 2 * (1 + X ^ 4) ^ 2) * (1 - X ^ 2) =
      (2 * X ^ 4 - 3 * X ^ 6 + 9 * X ^ 8 - 7 * X ^ 10 + 3 * X ^ 12 - 3 * X ^ 14) * (1 - X ^ 2) := by
  unfold Y
  linear_combination
    (-X^13 + 5*X^11 - 7*X^9 + 5*X^7 - 2*X^5 + X^3) * eqC0
    + (-X^13 + X^11 - 3*X^9 + 2*X^5) * eqC1
    + (-3*X^12 + 4*X^8 - 3*X^6 + 2*X^4) * eqC2
    + (2*X^13 - 5*X^11 + 8*X^9 - 9*X^7 + 7*X^5 - 4*X^3 + X) * eqM0
    + (2*X^13 - 5*X^11 + 8*X^9 - 9*X^7 + 7*X^5 - 4*X^3 + X) * eqM1
    + (2*X^12 - X^10 - 2*X^4 + X^2) * eqM2

theorem Y_gf :
    Y * ((1 - 2 * X ^ 2) ^ 2 * (1 + X ^ 4) ^ 2) =
      2 * X ^ 4 - 3 * X ^ 6 + 9 * X ^ 8 - 7 * X ^ 10 + 3 * X ^ 12 - 3 * X ^ 14 := by
  have h := Y_gf_mul
  have hne : (1 - X ^ 2 : PowerSeries ℤ) ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    simp at this
  exact mul_right_cancel₀ hne h

end SAWC

/-! Part C2: the middle-column marking (A022444). -/

namespace SAWC

open PowerSeries Finset

/-- number of levels whose middle vertex lies on the polygon -/
def marks1 : List Ltr → ℕ
  | [] => 0
  | [_] => 2
  | a :: b :: w => marks1 (b :: w) + (if (a ≠ 2 ∨ b ≠ 2) then 1 else 0)

theorem marks1_cons_of_mem {q : ℕ} {a b : Ltr} {w : List Ltr} (hw : w ∈ S q b) :
    (marks1 (a :: w) : ℤ) = marks1 w + (if (a ≠ 2 ∨ b ≠ 2) then 1 else 0) := by
  obtain ⟨t, rfl⟩ := head_of_mem hw
  simp only [marks1]
  push_cast
  split_ifs <;> simp

def Ms1 (p : ℕ) (a : Ltr) : ℤ := ∑ w ∈ S p a, (marks1 w : ℤ)

theorem Ms1_lt {p : ℕ} (h : p < 3) (a : Ltr) : Ms1 p a = 0 := by simp [Ms1, S_lt h]

theorem Ms1_rec {p : ℕ} (h : 3 ≤ p) (a : Ltr) : Ms1 p a =
    (if p = 2 + e a then (2 : ℤ) else 0) +
    ∑ b ∈ univ.filter (fun b => comp a b = true),
      (Ms1 (p - stepc a b) b + (if (a ≠ 2 ∨ b ≠ 2) then 1 else 0) * Cs (p - stepc a b) b) := by
  unfold Ms1 Cs; rw [sum_S _ h]
  congr 1
  apply sum_congr rfl
  intro b _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  rw [marks1_cons_of_mem hw]
  ring

noncomputable def PM1 (a : Ltr) : PowerSeries ℤ := PowerSeries.mk (fun p => Ms1 p a)

theorem eqN0 : PM1 0 = X ^ 3 + X ^ 3 + X ^ 2 * (PM1 0 + PC 0) + X ^ 3 * (PM1 2 + PC 2) := by
  ext p
  simp only [PC, PM1, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms1_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms1_lt]
  · rw [Ms1_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

theorem eqN1 : PM1 1 = X ^ 3 + X ^ 3 + X ^ 2 * (PM1 1 + PC 1) + X ^ 3 * (PM1 2 + PC 2) := by
  ext p
  simp only [PC, PM1, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms1_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms1_lt]
  · rw [Ms1_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

theorem eqN2 : PM1 2 = X ^ 4 + X ^ 4 + X ^ 3 * (PM1 0 + PC 0) + X ^ 3 * (PM1 1 + PC 1)
    + X ^ 2 * PM1 2 := by
  ext p
  simp only [PC, PM1, map_add, coeff_mk, coeff_X_pow, mul_add, coeff_X_pow_mul_mk]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · rw [Ms1_lt hp]
    interval_cases p <;> simp [Cs_lt, Ms1_lt]
  · rw [Ms1_rec hp]
    simp [Finset.sum_filter, Fin.sum_univ_three, comp, stepc, e]
    split_ifs <;> first | omega | ring_nf

noncomputable def Y1 : PowerSeries ℤ := X * PM1 0 + X * PM1 1 + X ^ 2 * PM1 2

theorem Y1_gf_mul :
    Y1 * ((1 - 2 * X ^ 2) ^ 2 * (1 + X ^ 4) ^ 2) * (1 - X ^ 2) =
      (4 * X ^ 4 - 8 * X ^ 6 + 14 * X ^ 8 - 16 * X ^ 10 + 6 * X ^ 12 - 6 * X ^ 14) * (1 - X ^ 2) := by
  unfold Y1
  linear_combination
    (-2*X^13 + 6*X^11 - 8*X^9 + 5*X^7 - 2*X^5 + X^3) * eqC0
    + (-2*X^13 + 6*X^11 - 8*X^9 + 5*X^7 - 2*X^5 + X^3) * eqC1
    + (-2*X^12 - 2*X^10 + 6*X^8 - 4*X^6 + 2*X^4) * eqC2
    + (2*X^13 - 5*X^11 + 8*X^9 - 9*X^7 + 7*X^5 - 4*X^3 + X) * eqN0
    + (2*X^13 - 5*X^11 + 8*X^9 - 9*X^7 + 7*X^5 - 4*X^3 + X) * eqN1
    + (2*X^12 - X^10 - 2*X^4 + X^2) * eqN2

theorem Y1_gf :
    Y1 * ((1 - 2 * X ^ 2) ^ 2 * (1 + X ^ 4) ^ 2) =
      4 * X ^ 4 - 8 * X ^ 6 + 14 * X ^ 8 - 16 * X ^ 10 + 6 * X ^ 12 - 6 * X ^ 14 := by
  have h := Y1_gf_mul
  have hne : (1 - X ^ 2 : PowerSeries ℤ) ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    simp at this
  exact mul_right_cancel₀ hne h

end SAWC


/-! Part B1: generic graph lemmas — a cycle is fixed by its neighbour sets and its second vertex;
walks and cycles from explicit vertex lists. -/

open SimpleGraph

namespace SAWG

variable {V : Type*} {G : SimpleGraph V}


theorem cycle_three_le {u : V} {c : G.Walk u u} (hc : c.IsCycle) : 3 ≤ c.length := by
  rcases c with _ | ⟨h, p⟩
  · exact absurd rfl hc.ne_nil
  · rcases p with _ | ⟨h', p'⟩
    · exact (h.ne rfl).elim
    · rcases p' with _ | ⟨h'', p''⟩
      · have := hc.edges_nodup
        simp [Sym2.eq_swap] at this
      · simp only [Walk.length_cons]; omega

theorem pair_eq {a b c : V} (h : ({a, b} : Set V) = {a, c}) (hb : b ≠ a) (hc : c ≠ a) : b = c := by
  have : c ∈ ({a, b} : Set V) := by rw [h]; simp
  rcases this with h1 | h1
  · exact absurd h1 hc
  · exact h1.symm

/-- Two cycles from `u` with the same neighbour sets and the same second vertex are equal. -/
theorem cycle_unique {u : V} {c c' : G.Walk u u} (hc : c.IsCycle) (hc' : c'.IsCycle)
    (hN : ∀ v, c.toSubgraph.neighborSet v = c'.toSubgraph.neighborSet v)
    (hs : c.getVert 1 = c'.getVert 1) : c = c' := by
  have h3 := cycle_three_le hc
  have h3' := cycle_three_le hc'
  -- distinctness of `getVert k` and `getVert (k+2)` inside a cycle
  have dist : ∀ {d : G.Walk u u}, d.IsCycle → ∀ k, k + 2 ≤ d.length → d.getVert (k + 1 + 1) ≠ d.getVert k := by
    intro d hd k hk heq
    have h3d := cycle_three_le hd
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e0 : d.getVert 0 = d.getVert d.length := by simp
      have := hd.getVert_injOn (by simp; omega) (by simp; omega) (heq.trans e0)
      omega
    · have := hd.getVert_injOn (by simp; omega) (by simp; omega) heq
      omega
  have P : ∀ k, k ≤ c.length → k ≤ c'.length → c.getVert k = c'.getVert k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hk'
      match k, ih with
      | 0, _ => simp
      | 1, _ => exact hs
      | j + 2, ih =>
        have e0 := ih j (by omega) (by omega) (by omega)
        have e1 := ih (j + 1) (by omega) (by omega) (by omega)
        have n1 := hc.neighborSet_toSubgraph_internal (i := j + 1) (by omega) (by omega)
        have n2 := hc'.neighborSet_toSubgraph_internal (i := j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at n1 n2
        rw [hN, e1, n2, e0] at n1
        exact (pair_eq n1 (dist hc' j hk') (by rw [← e0]; exact dist hc j hk)).symm
  have hlen : c.length = c'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have e := P c.length le_rfl hlt.le
      have e2 : c'.getVert c.length = c'.getVert c'.length := by rw [← e]; simp
      have := hc'.getVert_injOn (by simp; omega) (by simp; omega) e2
      omega
    · have e := P c'.length hlt.le le_rfl
      have e2 : c.getVert c'.length = c.getVert c.length := by rw [e]; simp
      have := hc.getVert_injOn (by simp; omega) (by simp; omega) e2
      omega
  apply Walk.ext_getVert
  intro k
  rcases Nat.lt_or_ge c.length k with hk | hk
  · rw [Walk.getVert_of_length_le c hk.le, Walk.getVert_of_length_le c' (hlen ▸ hk.le)]
  · exact P k hk (hlen ▸ hk)

/-! Walks from vertex lists. -/

/-- `PL G u l w`: `u :: l` is a chain of adjacent vertices ending at `w`. -/
def PL (G : SimpleGraph V) : V → List V → V → Prop
  | u, [], w => u = w
  | u, v :: l, w => G.Adj u v ∧ PL G v l w

def walkOf : (u : V) → (l : List V) → (w : V) → PL G u l w → G.Walk u w
  | u, [], _, h => (Walk.nil : G.Walk u u).copy rfl h
  | u, v :: l, w, h => Walk.cons h.1 (walkOf v l w h.2)

def pairsL : V → List V → List (Sym2 V)
  | _, [] => []
  | u, v :: l => s(u, v) :: pairsL v l

theorem support_walkOf (u : V) (l : List V) (w : V) (h : PL G u l w) :
    (walkOf u l w h).support = u :: l := by
  induction l generalizing u with
  | nil => cases h; simp [walkOf]
  | cons v l ih => simp [walkOf, ih]

theorem edges_walkOf (u : V) (l : List V) (w : V) (h : PL G u l w) :
    (walkOf u l w h).edges = pairsL u l := by
  induction l generalizing u with
  | nil => cases h; simp [walkOf, pairsL]
  | cons v l ih => simp [walkOf, pairsL, ih]

theorem length_walkOf (u : V) (l : List V) (w : V) (h : PL G u l w) :
    (walkOf u l w h).length = l.length := by
  induction l generalizing u with
  | nil => cases h; simp [walkOf]
  | cons v l ih => simp [walkOf, ih]

theorem mem_pairsL {a b x : V} {l : List V} (h : s(a, b) ∈ pairsL x l) : a ∈ x :: l ∧ b ∈ x :: l := by
  induction l generalizing x with
  | nil => simp [pairsL] at h
  | cons v l ih =>
    simp only [pairsL, List.mem_cons] at h
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem PL_last {u w : V} {l : List V} (h : PL G u l w) (hl : l ≠ []) : l.getLast hl = w := by
  induction l generalizing u with
  | nil => exact absurd rfl hl
  | cons v l ih =>
    cases l with
    | nil => simpa [PL] using h.2
    | cons x l => simpa using ih h.2 (by simp)

/-- A closed chain through distinct vertices with at least three steps is a cycle. -/
theorem isCycle_walkOf {u v : V} {l : List V} (h : PL G u (v :: l) u) (hnd : (v :: l).Nodup)
    (hlen : 2 ≤ l.length) : (walkOf u (v :: l) u h).IsCycle := by
  simp only [walkOf]
  rw [Walk.cons_isCycle_iff]
  refine ⟨Walk.IsPath.mk' (by rw [support_walkOf]; exact hnd), ?_⟩
  rw [edges_walkOf]
  cases l with
  | nil => simp at hlen
  | cons y l =>
    simp only [pairsL, List.mem_cons, not_or]
    have hlast : (y :: l).getLast (by simp) = u := PL_last h.2 (by simp)
    have hl : l ≠ [] := by rintro rfl; simp at hlen
    refine ⟨?_, ?_⟩
    · intro heq
      rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact (List.nodup_cons.mp hnd).1 (by rw [h2]; simp)
      · -- `y = u` is both the second vertex and the last one
        have hmem : (y :: l).getLast (by simp) ∈ l := by
          rw [List.getLast_cons hl]; exact List.getLast_mem hl
        rw [hlast, h1] at hmem
        exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hmem
    · intro hm
      exact (List.nodup_cons.mp hnd).1 (mem_pairsL hm).2

end SAWG


open SimpleGraph

namespace SAWS

open PowerSeries

def lattice : SimpleGraph (ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun (p q : ℤ × ℤ) (h : |p.1 - q.1| + |p.2 - q.2| = 1) =>
    show |q.1 - p.1| + |q.2 - p.2| = 1 by rw [abs_sub_comm q.1, abs_sub_comm q.2]; exact h⟩
  loopless := ⟨fun (p : ℤ × ℤ) (h : |p.1 - p.1| + |p.2 - p.2| = 1) => by simp at h⟩

def stripSet : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 2}

def strip : SimpleGraph stripSet := lattice.induce stripSet

def origin : stripSet := ⟨(0, 0), by simp [stripSet]⟩

noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {w : strip.Walk origin origin | w.length = 2 * n ∧ (n = 0 ∨ w.IsCycle)}

end SAWS

namespace SAWB

open SAWS

abbrev V := ↥stripSet

theorem adj_iff {u v : V} : strip.Adj u v ↔ |u.1.1 - v.1.1| + |u.1.2 - v.1.2| = 1 := by
  simp [strip, lattice]

theorem xbd (v : V) : 0 ≤ v.1.1 ∧ v.1.1 ≤ 2 := v.2

def pt (x : Fin 3) (y : ℤ) : V :=
  ⟨(((x : ℕ) : ℤ), y), by simp only [stripSet, Set.mem_setOf_eq]; have := x.isLt; omega⟩

@[simp] theorem pt_fst (x : Fin 3) (y : ℤ) : (pt x y).1.1 = ((x : ℕ) : ℤ) := rfl
@[simp] theorem pt_snd (x : Fin 3) (y : ℤ) : (pt x y).1.2 = y := rfl

theorem pt_inj {x x' : Fin 3} {y y' : ℤ} : pt x y = pt x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h1 := congrArg (fun v : V => v.1.1) h
    have h2 := congrArg (fun v : V => v.1.2) h
    simp only [pt_fst, pt_snd] at h1 h2
    exact ⟨Fin.ext (by exact_mod_cast h1), h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem pt_ne_y {x x' : Fin 3} {y y' : ℤ} (h : y ≠ y') : pt x y ≠ pt x' y' := fun e => h (pt_inj.mp e).2
theorem pt_ne_x {x x' : Fin 3} {y y' : ℤ} (h : x ≠ x') : pt x y ≠ pt x' y' := fun e => h (pt_inj.mp e).1

def xc (v : V) : Fin 3 := ⟨v.1.1.toNat, by have := xbd v; omega⟩

theorem pt_xc (v : V) : pt (xc v) v.1.2 = v := by
  apply Subtype.ext
  have := xbd v
  ext
  · simp [pt, xc]; omega
  · simp [pt]

/-- vertical edge of column `x` between levels `t` and `t+1` -/
def vert (x : Fin 3) (t : ℤ) : Sym2 V := s(pt x t, pt x (t + 1))
def hor0 (y : ℤ) : Sym2 V := s(pt 0 y, pt 1 y)
def hor1 (y : ℤ) : Sym2 V := s(pt 1 y, pt 2 y)

/-! Degrees in a cycle. -/

section deg
variable {u : V} {c : strip.Walk u u}

theorem ncard_nbr (hc : c.IsCycle) (v : V) :
    (c.toSubgraph.neighborSet v).ncard = 0 ∨ (c.toSubgraph.neighborSet v).ncard = 2 := by
  by_cases hv : v ∈ c.support
  · exact Or.inr (hc.ncard_neighborSet_toSubgraph_eq_two hv)
  · left
    have : c.toSubgraph.neighborSet v = ∅ := by
      ext w
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h
      exact hv (by simpa using c.toSubgraph.edge_vert ((Subgraph.mem_neighborSet _ _ _).mp h))
    rw [this, Set.ncard_empty]

theorem mem_nbr {v w : V} : w ∈ c.toSubgraph.neighborSet v ↔ s(v, w) ∈ c.edges := by
  simp [Subgraph.mem_neighborSet, Walk.adj_toSubgraph_iff_mem_edges]

open Classical in
theorem ncard_of_subset {N : Set V} {s : Finset V} (h : N ⊆ s) :
    N.ncard = ∑ w ∈ s, if w ∈ N then 1 else 0 := by
  have : N = ↑(s.filter (· ∈ N)) := by
    ext w; simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun hw => ⟨h hw, hw⟩, fun hw => hw.2⟩
  rw [this, Set.ncard_coe_finset, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro w hw
  simp [hw]

theorem eq_pt (v : V) {x : Fin 3} {y : ℤ} (hx : v.1.1 = ((x : ℕ) : ℤ)) (hy : v.1.2 = y) : v = pt x y := by
  apply Subtype.ext; ext
  · simpa using hx
  · simpa using hy

theorem l1_eq_one {a b : ℤ} (h : |a| + |b| = 1) :
    (a = 0 ∧ (b = 1 ∨ b = -1)) ∨ (b = 0 ∧ (a = 1 ∨ a = -1)) := by
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega

/-- the possible neighbours of `pt x y` -/
theorem nbr_cases {x : Fin 3} {y : ℤ} {w : V} (h : strip.Adj (pt x y) w) :
    w = pt x (y - 1) ∨ w = pt x (y + 1) ∨
      (w.1.2 = y ∧ (w.1.1 = ((x : ℕ) : ℤ) - 1 ∨ w.1.1 = ((x : ℕ) : ℤ) + 1)) := by
  rw [adj_iff] at h
  simp only [pt_fst, pt_snd] at h
  rcases l1_eq_one h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · left; exact eq_pt w (by omega) (by omega)
  · right; left; exact eq_pt w (by omega) (by omega)
  · right; right; exact ⟨by omega, Or.inl (by omega)⟩
  · right; right; exact ⟨by omega, Or.inr (by omega)⟩

end deg

/-! The local constraint at one level: horizontal edges are forced and `L` cannot sit next to `R`. -/

def b2n (b : Bool) : ℕ := if b then 1 else 0

theorem local_bool : ∀ d0 d1 d2 u0 u1 u2 h0 h1 : Bool,
    (b2n d0 + b2n d1 + b2n d2 = 0 ∨ b2n d0 + b2n d1 + b2n d2 = 2) →
    (b2n u0 + b2n u1 + b2n u2 = 0 ∨ b2n u0 + b2n u1 + b2n u2 = 2) →
    (b2n d0 + b2n u0 + b2n h0 = 0 ∨ b2n d0 + b2n u0 + b2n h0 = 2) →
    (b2n d1 + b2n u1 + b2n h0 + b2n h1 = 0 ∨ b2n d1 + b2n u1 + b2n h0 + b2n h1 = 2) →
    (b2n d2 + b2n u2 + b2n h1 = 0 ∨ b2n d2 + b2n u2 + b2n h1 = 2) →
    h0 = (d0 != u0) ∧ h1 = (d2 != u2) ∧
    ¬ (d0 = true ∧ d1 = true ∧ d2 = false ∧ u0 = false ∧ u1 = true ∧ u2 = true) ∧
    ¬ (d0 = false ∧ d1 = true ∧ d2 = true ∧ u0 = true ∧ u1 = true ∧ u2 = false) := by
  intro d0 d1 d2 u0 u1 u2 h0 h1
  cases d0 <;> cases d1 <;> cases d2 <;> cases u0 <;> cases u1 <;> cases u2 <;> cases h0 <;> cases h1 <;>
    simp [b2n]

/-! Crossing parity. -/

/-- an edge crossing between levels `t` and `t+1` -/
def isV (t : ℤ) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u w => decide (u.1.1 = w.1.1 ∧ min u.1.2 w.1.2 = t ∧ max u.1.2 w.1.2 = t + 1),
    fun u w => by simp only [eq_comm (a := u.1.1), min_comm, max_comm]⟩

theorem isV_mk (t : ℤ) (u w : V) :
    isV t s(u, w) = decide (u.1.1 = w.1.1 ∧ min u.1.2 w.1.2 = t ∧ max u.1.2 w.1.2 = t + 1) := rfl

theorem isV_adj (t : ℤ) {u w : V} (h : strip.Adj u w) :
    isV t s(u, w) = (decide (u.1.2 ≤ t) != decide (w.1.2 ≤ t)) := by
  rw [adj_iff] at h
  rw [isV_mk]
  rcases abs_cases (u.1.1 - w.1.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases (u.1.2 - w.1.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h1, h2] at h <;>
  · by_cases ha : u.1.2 ≤ t <;> by_cases hb : w.1.2 ≤ t <;> simp [ha, hb] <;> omega

theorem cross_parity (t : ℤ) : ∀ {u v : V} (p : strip.Walk u v),
    (p.edges.countP (isV t)) % 2 = b2n (decide (u.1.2 ≤ t) != decide (v.1.2 ≤ t))
  | _, _, Walk.nil => by simp [b2n]
  | _, _, Walk.cons h p => by
    rw [Walk.edges_cons, List.countP_cons, isV_adj t h]
    have := cross_parity t p
    rw [← Nat.mod_add_mod, this]
    simp only [b2n]
    split_ifs <;> simp_all <;> omega

end SAWB

/-! Part B5: the explicit ring polymer of a valid word (appended to B1 + B2 in the full file). -/

namespace SAWB

open SAWS SAWG

theorem adj_vert (x : Fin 3) (y : ℤ) : strip.Adj (pt x y) (pt x (y + 1)) := by
  rw [adj_iff]; simp

theorem adj_vert' (x : Fin 3) (y : ℤ) : strip.Adj (pt x (y + 1)) (pt x y) := (adj_vert x y).symm

theorem adj_hor {x x' : Fin 3} (y : ℤ) (h : |((x : ℕ) : ℤ) - ((x' : ℕ) : ℤ)| = 1) :
    strip.Adj (pt x y) (pt x' y) := by
  rw [adj_iff]; simpa using h

/-- left and right columns of a row: `L = 0` covers columns 0..1, `R = 1` covers 1..2, `B = 2` covers 0..2 -/
def xL (a : Fin 3) : Fin 3 := if a = 1 then 1 else 0
def xR (a : Fin 3) : Fin 3 := if a = 0 then 1 else 2

def lst : Fin 3 → List (Fin 3) → Fin 3
  | a, [] => a
  | _, c :: w => lst c w

/-- side chain after its first vertex `pt (f a) y`, for the rows `a :: w` -/
def rt (f : Fin 3 → Fin 3) : Fin 3 → List (Fin 3) → ℤ → List V
  | a, [], y => [pt (f a) (y + 1)]
  | a, c :: w, y => (if f a = f c then [] else [pt (f a) (y + 1)]) ++ (pt (f c) (y + 1) :: rt f c w (y + 1))

/-- the column function moves by at most one between rows -/
def Step1 (f : Fin 3 → Fin 3) : Prop := ∀ a c, f a ≠ f c → |((f a : ℕ) : ℤ) - ((f c : ℕ) : ℤ)| = 1

theorem step1_xL : Step1 xL := by unfold Step1; decide
theorem step1_xR : Step1 xR := by unfold Step1; decide

theorem PL_append {u w : V} {l1 l2 : List V} {m : V} (h1 : PL strip u l1 m) (h2 : PL strip m l2 w) :
    PL strip u (l1 ++ l2) w := by
  induction l1 generalizing u with
  | nil => simp only [PL] at h1; subst h1; simpa using h2
  | cons v l ih => exact ⟨h1.1, ih h1.2⟩

theorem PL_rt (f : Fin 3 → Fin 3) (hf : Step1 f) (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    PL strip (pt (f a) y) (rt f a w y) (pt (f (lst a w)) (y + w.length + 1)) := by
  induction w generalizing a y with
  | nil => exact ⟨adj_vert _ _, by simp [lst, PL]⟩
  | cons c w ih =>
    simp only [rt]
    have hrest : PL strip (pt (f c) (y + 1)) (rt f c w (y + 1)) (pt (f (lst a (c :: w))) (y + (c :: w).length + 1)) := by
      have := ih c (y + 1)
      simp only [lst, List.length_cons] at this ⊢
      convert this using 2
      push_cast; ring
    split_ifs with hac
    · exact ⟨by rw [← hac]; exact adj_vert _ _, hrest⟩
    · exact ⟨adj_vert _ _, adj_hor _ (hf a c hac), hrest⟩

theorem rt_level {f : Fin 3 → Fin 3} {a : Fin 3} {w : List (Fin 3)} {y : ℤ} {v : V}
    (hv : v ∈ rt f a w y) : y + 1 ≤ v.1.2 := by
  induction w generalizing a y with
  | nil => simp [rt] at hv; subst hv; simp
  | cons c w ih =>
    simp only [rt, List.mem_append, List.mem_cons] at hv
    rcases hv with hv | hv | hv
    · split_ifs at hv <;> simp_all
    · subst hv; simp
    · have := ih hv; omega

theorem rt_nodup (f : Fin 3 → Fin 3) (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    (rt f a w y).Nodup := by
  induction w generalizing a y with
  | nil => simp [rt]
  | cons c w ih =>
    simp only [rt]
    have hlev : ∀ v ∈ rt f c w (y + 1), y + 2 ≤ v.1.2 := fun v hv => by
      have := rt_level hv; omega
    split_ifs with hac
    · simp only [List.nil_append, List.nodup_cons]
      exact ⟨fun h => by have := hlev _ h; simp at this, ih c (y + 1)⟩
    · simp only [List.singleton_append, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨fun h => hac ((pt_inj.mp h).1), fun h => by have := hlev _ h; simp at this⟩,
        fun h => by have := hlev _ h; simp at this, ih c (y + 1)⟩

/-- valid row words: `L` never next to `R` -/
def Val : Fin 3 → List (Fin 3) → Prop
  | _, [] => True
  | a, c :: w => SAWC.comp a c = true ∧ Val c w

/-- the two side chains never meet -/
theorem chains_disjoint (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (hv : Val a w) :
    ∀ v, v ∈ pt (xR a) y :: rt xR a w y → v ∉ pt (xL a) y :: rt xL a w y := by
  induction w generalizing a y with
  | nil =>
    intro v hv1 hv2
    simp only [rt, List.mem_cons, List.not_mem_nil, or_false] at hv1 hv2
    rcases hv1 with rfl | rfl <;> rcases hv2 with h | h <;>
      · have := pt_inj.mp h; revert this; fin_cases a <;> simp [xL, xR]
  | cons c w ih =>
    intro v hv1 hv2
    have hrec := ih c (y + 1) hv.2
    have hcomp := hv.1
    simp only [rt, List.mem_cons, List.mem_append] at hv1 hv2
    -- levels: `y` only for the heads, `y + 1` for the row junction, at least `y + 2` beyond
    have lR := fun (h : v ∈ rt xR c w (y + 1)) => rt_level h
    have lL := fun (h : v ∈ rt xL c w (y + 1)) => rt_level h
    rcases hv1 with rfl | h1 | rfl | h1
    · rcases hv2 with h | h | h | h
      · have := pt_inj.mp h; revert this; fin_cases a <;> simp [xL, xR]
      · split_ifs at h <;> simp at h; have := (pt_inj.mp h).2; omega
      · have := (pt_inj.mp h).2; omega
      · have := lL h; simp only [pt_snd] at this; omega
    · split_ifs at h1 with hR
      · simp at h1
      · simp only [List.mem_singleton] at h1
        subst h1
        rcases hv2 with h | h | h | h
        · have := (pt_inj.mp h).2; omega
        · split_ifs at h with hL
          · simp at h
          · have := (pt_inj.mp (List.mem_singleton.mp h)).1
            revert this hR hL hcomp; fin_cases a <;> fin_cases c <;> simp [xL, xR, SAWC.comp]
        · have := (pt_inj.mp h).1
          revert this hR hcomp; fin_cases a <;> fin_cases c <;> simp [xL, xR, SAWC.comp]
        · have := lL h; simp only [pt_snd] at this; omega
    · rcases hv2 with h | h | h | h
      · have := (pt_inj.mp h).2; omega
      · split_ifs at h with hL
        · simp at h
        · have := (pt_inj.mp (List.mem_singleton.mp h)).1
          revert this hL hcomp; fin_cases a <;> fin_cases c <;> simp [xL, xR, SAWC.comp]
      · exact hrec _ (List.mem_cons_self) (h ▸ List.mem_cons_self)
      · exact hrec _ (List.mem_cons_self) (List.mem_cons_of_mem _ h)
    · rcases hv2 with h | h | h | h
      · have := lR h1; rw [h] at this; simp at this
      · split_ifs at h with hL
        · simp at h
        · have := lR h1; rw [List.mem_singleton.mp h] at this; simp at this
      · exact hrec _ (List.mem_cons_of_mem _ h1) (h ▸ List.mem_cons_self)
      · exact hrec _ (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h)

/-- the only vertex of a chain at its top level -/
theorem rt_top {f : Fin 3 → Fin 3} {a : Fin 3} {w : List (Fin 3)} {y : ℤ} {v : V}
    (hv : v ∈ rt f a w y) (htop : v.1.2 = y + w.length + 1) : v = pt (f (lst a w)) (y + w.length + 1) := by
  induction w generalizing a y with
  | nil => simpa [rt, lst] using hv
  | cons c w ih =>
    simp only [rt, List.mem_append, List.mem_cons] at hv
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at htop ⊢
    rcases hv with hv | rfl | hv
    · split_ifs at hv <;> simp at hv; subst hv; simp at htop; omega
    · simp at htop; omega
    · have := ih hv (by rw [htop]; ring)
      simp only [lst]
      rw [this]; congr 1; ring

/-! The vertical edges of a chain. -/

def row (a : Fin 3) (w : List (Fin 3)) (j : ℕ) : Fin 3 := (a :: w).getD j 0

theorem vert_inj {x x' : Fin 3} {t t' : ℤ} : vert x t = vert x' t' ↔ x = x' ∧ t = t' := by
  constructor
  · intro h
    unfold vert at h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact pt_inj.mp h1
    · have a1 := pt_inj.mp h1; have a2 := pt_inj.mp h2; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem vert_ne_flat {x p q : Fin 3} {t y : ℤ} : vert x t ≠ s(pt p y, pt q y) := by
  intro h
  unfold vert at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 := (pt_inj.mp h1).2; have a2 := (pt_inj.mp h2).2; omega
  · have a1 := (pt_inj.mp h1).2; have a2 := (pt_inj.mp h2).2; omega

theorem vert_mem_pairs_rt (f : Fin 3 → Fin 3) (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (x : Fin 3) (t : ℤ) :
    vert x t ∈ pairsL (pt (f a) y) (rt f a w y) ↔
      ∃ j : ℕ, j ≤ w.length ∧ t = y + j ∧ x = f (row a w j) := by
  induction w generalizing a y with
  | nil =>
    simp only [rt, pairsL, List.mem_singleton, List.length_nil, Nat.le_zero]
    rw [show s(pt (f a) y, pt (f a) (y + 1)) = vert (f a) y from rfl, vert_inj]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨0, rfl, by simp, by simp [row]⟩
    · rintro ⟨j, rfl, rfl, rfl⟩; simp [row]
  | cons c w ih =>
    have key : ∀ (j : ℕ), row a (c :: w) (j + 1) = row c w j := fun j => by simp [row]
    simp only [rt]
    split_ifs with hac
    · simp only [List.nil_append, pairsL, List.mem_cons]
      rw [show s(pt (f a) y, pt (f c) (y + 1)) = vert (f a) y by rw [hac]; rfl, vert_inj, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
        · exact ⟨0, by simp, by simp, by simp [row]⟩
        · exact ⟨j + 1, by simp; omega, by push_cast; ring, (key j).symm ▸ rfl⟩
      · rintro ⟨j, hj, rfl, rfl⟩
        rcases j with _ | j
        · left; simp [row]
        · right; exact ⟨j, by simp at hj; omega, by push_cast; ring, by rw [key]⟩
    · simp only [List.singleton_append, pairsL, List.mem_cons]
      rw [show s(pt (f a) y, pt (f a) (y + 1)) = vert (f a) y from rfl, vert_inj, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | h | ⟨j, hj, rfl, rfl⟩)
        · exact ⟨0, by simp, by simp, by simp [row]⟩
        · exact absurd h vert_ne_flat
        · exact ⟨j + 1, by simp; omega, by push_cast; ring, (key j).symm ▸ rfl⟩
      · rintro ⟨j, hj, rfl, rfl⟩
        rcases j with _ | j
        · left; simp [row]
        · right; right; exact ⟨j, by simp at hj; omega, by push_cast; ring, by rw [key]⟩

/-! Top and bottom caps. -/

def topL (l : Fin 3) (t : ℤ) : List V := if l = 2 then [pt 1 t, pt 0 t] else [pt (xL l) t]
def botL (a : Fin 3) (y : ℤ) : List V := if a = 2 then [pt 1 y, pt 2 y] else [pt (xR a) y]

theorem PL_topL (l : Fin 3) (t : ℤ) : PL strip (pt (xR l) t) (topL l t) (pt (xL l) t) := by
  fin_cases l
  · exact ⟨adj_hor t (by decide), rfl⟩
  · exact ⟨adj_hor t (by decide), rfl⟩
  · exact ⟨adj_hor t (by decide), adj_hor t (by decide), rfl⟩

theorem PL_botL (a : Fin 3) (y : ℤ) : PL strip (pt (xL a) y) (botL a y) (pt (xR a) y) := by
  fin_cases a
  · exact ⟨adj_hor y (by decide), rfl⟩
  · exact ⟨adj_hor y (by decide), rfl⟩
  · exact ⟨adj_hor y (by decide), adj_hor y (by decide), rfl⟩

abbrev top (w : List (Fin 3)) (y : ℤ) : ℤ := y + w.length + 1

def Rw (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : strip.Walk (pt (xR a) y) (pt (xR (lst a w)) (top w y)) :=
  walkOf _ (rt xR a w y) _ (PL_rt xR step1_xR a w y)
def Tw (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    strip.Walk (pt (xR (lst a w)) (top w y)) (pt (xL (lst a w)) (top w y)) :=
  walkOf _ (topL (lst a w) (top w y)) _ (PL_topL _ _)
def Lw (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : strip.Walk (pt (xL (lst a w)) (top w y)) (pt (xL a) y) :=
  (walkOf _ (rt xL a w y) _ (PL_rt xL step1_xL a w y)).reverse
def Bw (a : Fin 3) (y : ℤ) : strip.Walk (pt (xL a) y) (pt (xR a) y) :=
  walkOf _ (botL a y) _ (PL_botL a y)

/-- the ring polymer with rows `a :: w` starting at level `y` -/
def poly (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : strip.Walk (pt (xR a) y) (pt (xR a) y) :=
  (Rw a w y).append ((Tw a w y).append ((Lw a w y).append (Bw a y)))

theorem poly_vert (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (x : Fin 3) (t : ℤ) :
    vert x t ∈ (poly a w y).edges ↔
      ∃ j : ℕ, j ≤ w.length ∧ t = y + j ∧ (x = xR (row a w j) ∨ x = xL (row a w j)) := by
  simp only [poly, Walk.edges_append, List.mem_append, Rw, Tw, Lw, Bw, Walk.edges_reverse,
    List.mem_reverse, edges_walkOf]
  rw [vert_mem_pairs_rt, vert_mem_pairs_rt]
  have hT : vert x t ∉ pairsL (pt (xR (lst a w)) (top w y)) (topL (lst a w) (top w y)) := by
    unfold topL; split_ifs <;> simp [pairsL, vert_ne_flat]
  have hB : vert x t ∉ pairsL (pt (xL a) y) (botL a y) := by
    unfold botL; split_ifs <;> simp [pairsL, vert_ne_flat]
  simp only [hT, hB, false_or, or_false]
  constructor
  · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨j, h1, h2, Or.inl h3⟩
    · exact ⟨j, h1, h2, Or.inr h3⟩
  · rintro ⟨j, h1, h2, h3 | h3⟩
    · exact Or.inl ⟨j, h1, h2, h3⟩
    · exact Or.inr ⟨j, h1, h2, h3⟩

/-! Length. -/

theorem rt_length (f : Fin 3 → Fin 3) (a c : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    (rt f a (c :: w) y).length = (if f a = f c then 0 else 1) + 1 + (rt f c w (y + 1)).length := by
  simp only [rt, List.length_append, List.length_cons]
  split_ifs <;> simp <;> ring

theorem rt_length_nil (f : Fin 3 → Fin 3) (a : Fin 3) (y : ℤ) : (rt f a [] y).length = 1 := rfl

theorem len_sides (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (hv : Val a w) :
    (rt xR a w y).length + (rt xL a w y).length + SAWC.e (lst a w) = SAWC.cost (a :: w) := by
  induction w generalizing a y with
  | nil => simp [rt, SAWC.cost, lst]
  | cons c w ih =>
    rw [rt_length, rt_length]
    have := ih c (y + 1) hv.2
    simp only [SAWC.cost, lst] at this ⊢
    have hc := hv.1
    have : (if xR a = xR c then 0 else 1) + (if xL a = xL c then 0 else 1) + 2 = SAWC.stepc a c := by
      revert hc; fin_cases a <;> fin_cases c <;> simp [xR, xL, SAWC.stepc, SAWC.comp]
    omega

theorem topL_length (l : Fin 3) (t : ℤ) : (topL l t).length = SAWC.e l := by
  unfold topL SAWC.e; split_ifs <;> simp
theorem botL_length (a : Fin 3) (y : ℤ) : (botL a y).length = SAWC.e a := by
  unfold botL SAWC.e; split_ifs <;> simp

theorem poly_length (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (hv : Val a w) :
    (poly a w y).length = SAWC.e a + SAWC.cost (a :: w) := by
  simp only [poly, Walk.length_append, Rw, Tw, Lw, Bw, Walk.length_reverse, length_walkOf,
    topL_length, botL_length]
  have := len_sides a w y hv
  omega

end SAWB

/-! Part B6: the local structure of every cycle in the strip. -/

namespace SAWB

open SAWS SAWG

theorem origin_eq : origin = pt 0 0 := rfl

theorem xc_val (v : V) : (((xc v : Fin 3) : ℕ) : ℤ) = v.1.1 := by
  simp [xc, Int.toNat_of_nonneg (xbd v).1]

section cyc
variable {u : V} {c : strip.Walk u u}

theorem nbr_down (x : Fin 3) (y : ℤ) :
    pt x (y - 1) ∈ c.toSubgraph.neighborSet (pt x y) ↔ vert x (y - 1) ∈ c.edges := by
  rw [mem_nbr, vert, sub_add_cancel, Sym2.eq_swap]
theorem nbr_up (x : Fin 3) (y : ℤ) :
    pt x (y + 1) ∈ c.toSubgraph.neighborSet (pt x y) ↔ vert x y ∈ c.edges := by
  rw [mem_nbr, vert]
theorem nbr_01 (y : ℤ) : pt 1 y ∈ c.toSubgraph.neighborSet (pt 0 y) ↔ hor0 y ∈ c.edges := by
  rw [mem_nbr, hor0]
theorem nbr_10 (y : ℤ) : pt 0 y ∈ c.toSubgraph.neighborSet (pt 1 y) ↔ hor0 y ∈ c.edges := by
  rw [mem_nbr, hor0, Sym2.eq_swap]
theorem nbr_12 (y : ℤ) : pt 2 y ∈ c.toSubgraph.neighborSet (pt 1 y) ↔ hor1 y ∈ c.edges := by
  rw [mem_nbr, hor1]
theorem nbr_21 (y : ℤ) : pt 1 y ∈ c.toSubgraph.neighborSet (pt 2 y) ↔ hor1 y ∈ c.edges := by
  rw [mem_nbr, hor1, Sym2.eq_swap]

theorem nbr_adj {v w : V} (h : w ∈ c.toSubgraph.neighborSet v) : strip.Adj v w :=
  c.adj_of_mem_edges (mem_nbr.mp h)

def bE (e : Sym2 V) (c : strip.Walk u u) : ℕ := b2n (decide (e ∈ c.edges))

theorem deg0 (hc : c.IsCycle) (y : ℤ) :
    bE (vert 0 (y - 1)) c + bE (vert 0 y) c + bE (hor0 y) c = 0 ∨
    bE (vert 0 (y - 1)) c + bE (vert 0 y) c + bE (hor0 y) c = 2 := by
  have h := ncard_nbr hc (pt 0 y)
  have hsub : c.toSubgraph.neighborSet (pt 0 y) ⊆
      ↑({pt 0 (y - 1), pt 0 (y + 1), pt 1 y} : Finset V) := by
    intro w hw
    rcases nbr_cases (nbr_adj hw) with h | h | ⟨hy, h | h⟩
    · simp [h]
    · simp [h]
    · have := xbd w; simp at h; omega
    · rw [eq_pt w (x := 1) (by simpa using h) hy]; simp
  rw [ncard_of_subset hsub, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨pt_ne_y (by omega), pt_ne_y (by omega)⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact pt_ne_y (by omega)),
    Finset.sum_singleton] at h
  simp only [nbr_down, nbr_up, nbr_01] at h
  by_cases e1 : vert 0 (y - 1) ∈ c.edges <;> by_cases e2 : vert 0 y ∈ c.edges <;>
    by_cases e3 : hor0 y ∈ c.edges <;> simp [bE, b2n, e1, e2, e3] at h ⊢ <;> omega

theorem deg1 (hc : c.IsCycle) (y : ℤ) :
    bE (vert 1 (y - 1)) c + bE (vert 1 y) c + bE (hor0 y) c + bE (hor1 y) c = 0 ∨
    bE (vert 1 (y - 1)) c + bE (vert 1 y) c + bE (hor0 y) c + bE (hor1 y) c = 2 := by
  have h := ncard_nbr hc (pt 1 y)
  have hsub : c.toSubgraph.neighborSet (pt 1 y) ⊆
      ↑({pt 1 (y - 1), pt 1 (y + 1), pt 0 y, pt 2 y} : Finset V) := by
    intro w hw
    rcases nbr_cases (nbr_adj hw) with h | h | ⟨hy, h | h⟩
    · simp [h]
    · simp [h]
    · rw [eq_pt w (x := 0) (by simpa using h) hy]; simp
    · rw [eq_pt w (x := 2) (by simpa using h) hy]; simp
  rw [ncard_of_subset hsub, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨pt_ne_y (by omega), pt_ne_y (by omega), pt_ne_y (by omega)⟩),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨pt_ne_y (by omega), pt_ne_y (by omega)⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact pt_ne_x (by decide)),
    Finset.sum_singleton] at h
  simp only [nbr_down, nbr_up, nbr_10, nbr_12] at h
  by_cases e1 : vert 1 (y - 1) ∈ c.edges <;> by_cases e2 : vert 1 y ∈ c.edges <;>
    by_cases e3 : hor0 y ∈ c.edges <;> by_cases e4 : hor1 y ∈ c.edges <;>
    simp [bE, b2n, e1, e2, e3, e4] at h ⊢ <;> omega

theorem deg2 (hc : c.IsCycle) (y : ℤ) :
    bE (vert 2 (y - 1)) c + bE (vert 2 y) c + bE (hor1 y) c = 0 ∨
    bE (vert 2 (y - 1)) c + bE (vert 2 y) c + bE (hor1 y) c = 2 := by
  have h := ncard_nbr hc (pt 2 y)
  have hsub : c.toSubgraph.neighborSet (pt 2 y) ⊆
      ↑({pt 2 (y - 1), pt 2 (y + 1), pt 1 y} : Finset V) := by
    intro w hw
    rcases nbr_cases (nbr_adj hw) with h | h | ⟨hy, h | h⟩
    · simp [h]
    · simp [h]
    · rw [eq_pt w (x := 1) (by simpa using h) hy]; simp
    · have := xbd w; simp at h; omega
  rw [ncard_of_subset hsub, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨pt_ne_y (by omega), pt_ne_y (by omega)⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact pt_ne_y (by omega)),
    Finset.sum_singleton] at h
  simp only [nbr_down, nbr_up, nbr_21] at h
  by_cases e1 : vert 2 (y - 1) ∈ c.edges <;> by_cases e2 : vert 2 y ∈ c.edges <;>
    by_cases e3 : hor1 y ∈ c.edges <;> simp [bE, b2n, e1, e2, e3] at h ⊢ <;> omega

/-- the crossing edges of a layer are exactly its vertical edges -/
theorem countP_layer (hc : c.IsCycle) (t : ℤ) :
    c.edges.countP (isV t) = bE (vert 0 t) c + bE (vert 1 t) c + bE (vert 2 t) c := by
  have hnd : c.edges.Nodup := hc.edges_nodup
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  have : (c.edges.filter (fun e => isV t e)).toFinset =
      (Finset.univ.filter (fun x : Fin 3 => vert x t ∈ c.edges)).image (fun x => vert x t) := by
    ext e
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, hv⟩
      induction e using Sym2.ind with
      | _ a b =>
        rw [isV_mk] at hv
        simp only [decide_eq_true_eq] at hv
        obtain ⟨hx, hmin, hmax⟩ := hv
        refine ⟨xc a, ?_⟩
        have ha : a = pt (xc a) a.1.2 := (pt_xc a).symm
        have hb : b = pt (xc a) b.1.2 := eq_pt b (by rw [xc_val]; exact hx.symm) rfl
        rcases le_total a.1.2 b.1.2 with hab | hab
        · rw [min_eq_left hab] at hmin; rw [max_eq_right hab] at hmax
          have e1 : s(a, b) = vert (xc a) t := by rw [ha, hb, hmin, hmax]; rfl
          exact ⟨e1 ▸ he, e1.symm⟩
        · rw [min_eq_right hab] at hmin; rw [max_eq_left hab] at hmax
          have e1 : s(a, b) = vert (xc a) t := by rw [ha, hb, hmin, hmax, Sym2.eq_swap]; rfl
          exact ⟨e1 ▸ he, e1.symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, by rw [vert, isV_mk]; simp⟩
  rw [this, Finset.card_image_of_injective _ (fun x x' h => (vert_inj.mp h).1), Finset.card_filter,
    Fin.sum_univ_three]
  simp only [bE, b2n, decide_eq_true_eq]

theorem layer (hc : c.IsCycle) (t : ℤ) :
    bE (vert 0 t) c + bE (vert 1 t) c + bE (vert 2 t) c = 0 ∨
    bE (vert 0 t) c + bE (vert 1 t) c + bE (vert 2 t) c = 2 := by
  have h1 := cross_parity t c
  rw [countP_layer hc, bne_self_eq_false] at h1
  simp only [b2n] at h1
  rw [if_neg (by decide)] at h1
  have : bE (vert 0 t) c ≤ 1 ∧ bE (vert 1 t) c ≤ 1 ∧ bE (vert 2 t) c ≤ 1 := by
    simp only [bE, b2n]; refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  omega

/-- the local rule at level `y` -/
theorem local_rule (hc : c.IsCycle) (y : ℤ) :
    (hor0 y ∈ c.edges ↔ (vert 0 (y - 1) ∈ c.edges ↔ ¬ vert 0 y ∈ c.edges)) ∧
    (hor1 y ∈ c.edges ↔ (vert 2 (y - 1) ∈ c.edges ↔ ¬ vert 2 y ∈ c.edges)) ∧
    ¬ (vert 0 (y - 1) ∈ c.edges ∧ vert 1 (y - 1) ∈ c.edges ∧ vert 2 (y - 1) ∉ c.edges ∧
        vert 0 y ∉ c.edges ∧ vert 1 y ∈ c.edges ∧ vert 2 y ∈ c.edges) ∧
    ¬ (vert 0 (y - 1) ∉ c.edges ∧ vert 1 (y - 1) ∈ c.edges ∧ vert 2 (y - 1) ∈ c.edges ∧
        vert 0 y ∈ c.edges ∧ vert 1 y ∈ c.edges ∧ vert 2 y ∉ c.edges) := by
  have L := local_bool (decide (vert 0 (y - 1) ∈ c.edges)) (decide (vert 1 (y - 1) ∈ c.edges))
    (decide (vert 2 (y - 1) ∈ c.edges)) (decide (vert 0 y ∈ c.edges)) (decide (vert 1 y ∈ c.edges))
    (decide (vert 2 y ∈ c.edges)) (decide (hor0 y ∈ c.edges)) (decide (hor1 y ∈ c.edges))
    (layer hc (y - 1)) (layer hc y) (deg0 hc y) (by have := deg1 hc y; simpa [bE] using this) (deg2 hc y)
  obtain ⟨h0, h1, h2, h3⟩ := L
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· = true) h0; simp at this; tauto
  · have := congrArg (· = true) h1; simp at this; tauto
  · simpa using h2
  · simpa using h3

end cyc

/-- every edge of the strip is vertical or one of the two horizontal edges of a level -/
theorem edge_cases {v w : V} (h : strip.Adj v w) :
    (∃ x t, s(v, w) = vert x t) ∨ (∃ y, s(v, w) = hor0 y) ∨ (∃ y, s(v, w) = hor1 y) := by
  have hv := pt_xc v
  rw [← hv] at h ⊢
  have hb := xbd w
  have hxv := xc_val v
  rcases nbr_cases h with h1 | h1 | ⟨hy, h1 | h1⟩
  · rw [h1]; left; exact ⟨xc v, v.1.2 - 1, by rw [vert, sub_add_cancel, Sym2.eq_swap]⟩
  · rw [h1]; left; exact ⟨xc v, v.1.2, rfl⟩
  · right
    have : (xc v = 1 ∧ w = pt 0 v.1.2) ∨ (xc v = 2 ∧ w = pt 1 v.1.2) := by
      have := (xc v).isLt
      rcases (by omega : (xc v : ℕ) = 1 ∨ (xc v : ℕ) = 2) with h2 | h2
      · left; exact ⟨Fin.ext h2, eq_pt w (by simp; omega) hy⟩
      · right; exact ⟨Fin.ext h2, eq_pt w (by simp; omega) hy⟩
    rcases this with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3]
    · left; exact ⟨v.1.2, by rw [hor0, Sym2.eq_swap]⟩
    · right; exact ⟨v.1.2, by rw [hor1, Sym2.eq_swap]⟩
  · right
    have : (xc v = 0 ∧ w = pt 1 v.1.2) ∨ (xc v = 1 ∧ w = pt 2 v.1.2) := by
      have := (xc v).isLt
      rcases (by omega : (xc v : ℕ) = 0 ∨ (xc v : ℕ) = 1) with h2 | h2
      · left; exact ⟨Fin.ext h2, eq_pt w (by simp; omega) hy⟩
      · right; exact ⟨Fin.ext h2, eq_pt w (by simp; omega) hy⟩
    rcases this with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3]
    · left; exact ⟨v.1.2, rfl⟩
    · right; exact ⟨v.1.2, rfl⟩

/-- two cycles with the same vertical edges have the same edges -/
theorem edges_iff_of_vert {u1 u2 : V} {c1 : strip.Walk u1 u1} {c2 : strip.Walk u2 u2}
    (h1 : c1.IsCycle) (h2 : c2.IsCycle) (hv : ∀ x t, vert x t ∈ c1.edges ↔ vert x t ∈ c2.edges)
    (v w : V) : s(v, w) ∈ c1.edges ↔ s(v, w) ∈ c2.edges := by
  by_cases hadj : strip.Adj v w
  · rcases edge_cases hadj with ⟨x, t, he⟩ | ⟨y, he⟩ | ⟨y, he⟩ <;> rw [he]
    · exact hv x t
    · rw [(local_rule h1 y).1, (local_rule h2 y).1, hv, hv]
    · rw [(local_rule h1 y).2.1, (local_rule h2 y).2.1, hv, hv]
  · exact ⟨fun h => absurd (c1.adj_of_mem_edges h) hadj, fun h => absurd (c2.adj_of_mem_edges h) hadj⟩

end SAWB

/-! Part B7: the explicit polygon is a cycle; every cycle through the origin is one; counting. -/

namespace SAWG
variable {V : Type*} {G : SimpleGraph V}

theorem path_edge_len {a b : V} (q : G.Walk a b) (hq : q.IsPath) (h : s(a, b) ∈ q.edges) : q.length = 1 := by
  cases q with
  | nil => simp at h
  | cons h' q' =>
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · have := Walk.isPath_iff_eq_nil.mp hq.1
        subst this; simp
      · exact (h'.ne rfl).elim
    · exact absurd (Walk.fst_mem_support_of_mem_edges q' h) hq.2

theorem isCycle_of_tail_nodup {u : V} (c : G.Walk u u) (h : c.support.tail.Nodup) (hl : 3 ≤ c.length) :
    c.IsCycle := by
  cases c with
  | nil => simp at hl
  | cons hadj p =>
    rw [Walk.cons_isCycle_iff]
    have hp : p.IsPath := Walk.IsPath.mk' (by simpa using h)
    refine ⟨hp, fun he => ?_⟩
    have := path_edge_len p hp (by rw [Sym2.eq_swap]; exact he)
    simp only [Walk.length_cons] at hl
    omega

end SAWG

namespace SAWB

open SAWS SAWG

/-! The polygon is a cycle. -/

theorem cost_ge (a : Fin 3) (w : List (Fin 3)) : 2 * w.length + 3 ≤ SAWC.cost (a :: w) := by
  induction w generalizing a with
  | nil => simp [SAWC.cost, SAWC.e]; split_ifs <;> omega
  | cons c w ih =>
    simp only [SAWC.cost, List.length_cons]
    have := SAWC.stepc_ge a c; have := ih c; omega

def topMid (l : Fin 3) (t : ℤ) : List V := if l = 2 then [pt 1 t] else []
def botMid (a : Fin 3) (y : ℤ) : List V := if a = 2 then [pt 1 y] else []

theorem topL_eq (l : Fin 3) (t : ℤ) : topL l t = topMid l t ++ [pt (xL l) t] := by
  unfold topL topMid; split_ifs with h <;> simp [h, xL]
theorem botL_eq (a : Fin 3) (y : ℤ) : botL a y = botMid a y ++ [pt (xR a) y] := by
  unfold botL botMid; split_ifs with h <;> simp [h, xR]

theorem rt_ne_nil (f : Fin 3 → Fin 3) (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : rt f a w y ≠ [] := by
  cases w <;> simp [rt]

theorem rt_split (f : Fin 3 → Fin 3) (hf : Step1 f) (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    rt f a w y = (rt f a w y).dropLast ++ [pt (f (lst a w)) (top w y)] := by
  have hne := rt_ne_nil f a w y
  have hl := PL_last (PL_rt f hf a w y) hne
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [hl]

theorem poly_support_tail (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    (poly a w y).support.tail =
      rt xR a w y ++ topMid (lst a w) (top w y) ++ [pt (xL (lst a w)) (top w y)] ++
        (rt xL a w y).dropLast.reverse ++ [pt (xL a) y] ++ botMid a y ++ [pt (xR a) y] := by
  have hs := rt_split xL step1_xL a w y
  simp only [poly, Walk.support_append, Rw, Tw, Lw, Bw, support_walkOf, Walk.support_reverse,
    List.tail_cons, List.cons_append, topL_eq, botL_eq]
  rw [hs]
  simp

theorem poly_tail_perm (a : Fin 3) (w : List (Fin 3)) (y : ℤ) :
    (poly a w y).support.tail.Perm
      ((pt (xR a) y :: rt xR a w y) ++ (pt (xL a) y :: rt xL a w y) ++ topMid (lst a w) (top w y) ++
        botMid a y) := by
  rw [poly_support_tail]
  conv_rhs => rw [rt_split xL step1_xL a w y]
  rw [List.perm_iff_count]
  intro v
  simp only [List.count_append, List.count_cons, List.count_reverse, List.count_singleton, List.count_nil]
  omega

theorem rt_y_level {f : Fin 3 → Fin 3} {a : Fin 3} {w : List (Fin 3)} {y : ℤ} {v : V}
    (hv : v ∈ rt f a w y) : v.1.2 ≤ top w y := by
  induction w generalizing a y with
  | nil => simp [rt] at hv; subst hv; simp [top]
  | cons c w ih =>
    simp only [rt, List.mem_append, List.mem_cons] at hv
    have h1 := @ih c (y + 1)
    simp only [top, List.length_cons, Nat.cast_add, Nat.cast_one] at h1 ⊢
    rcases hv with hv | rfl | hv
    · split_ifs at hv <;> simp at hv; subst hv; simp; omega
    · simp; omega
    · have := h1 hv; omega

theorem poly_isCycle (a : Fin 3) (w : List (Fin 3)) (y : ℤ) (hv : Val a w) : (poly a w y).IsCycle := by
  apply isCycle_of_tail_nodup
  · rw [(poly_tail_perm a w y).nodup_iff]
    have nR : (pt (xR a) y :: rt xR a w y).Nodup :=
      List.nodup_cons.mpr ⟨fun h => by have := rt_level h; simp at this, rt_nodup _ _ _ _⟩
    have nL : (pt (xL a) y :: rt xL a w y).Nodup :=
      List.nodup_cons.mpr ⟨fun h => by have := rt_level h; simp at this, rt_nodup _ _ _ _⟩
    have dRL := chains_disjoint a w y hv
    -- the cap vertices
    have tR : ∀ v ∈ topMid (lst a w) (top w y), v ∉ pt (xR a) y :: rt xR a w y := by
      intro v hv1 hv2
      unfold topMid at hv1; split_ifs at hv1 with hl
      · simp only [List.mem_singleton] at hv1; subst hv1
        rcases List.mem_cons.mp hv2 with h | h
        · have := (pt_inj.mp h).2; simp [top] at this; omega
        · have := rt_top h (by simp [top])
          have := (pt_inj.mp this).1; rw [hl] at this; simp [xR] at this
      · simp at hv1
    have tL : ∀ v ∈ topMid (lst a w) (top w y), v ∉ pt (xL a) y :: rt xL a w y := by
      intro v hv1 hv2
      unfold topMid at hv1; split_ifs at hv1 with hl
      · simp only [List.mem_singleton] at hv1; subst hv1
        rcases List.mem_cons.mp hv2 with h | h
        · have := (pt_inj.mp h).2; simp [top] at this; omega
        · have := rt_top h (by simp [top])
          have := (pt_inj.mp this).1; rw [hl] at this; simp [xL] at this
      · simp at hv1
    have bR : ∀ v ∈ botMid a y, v ∉ pt (xR a) y :: rt xR a w y := by
      intro v hv1 hv2
      unfold botMid at hv1; split_ifs at hv1 with ha
      · simp only [List.mem_singleton] at hv1; subst hv1
        rcases List.mem_cons.mp hv2 with h | h
        · have := (pt_inj.mp h).1; rw [ha] at this; simp [xR] at this
        · have := rt_level h; simp at this
      · simp at hv1
    have bL : ∀ v ∈ botMid a y, v ∉ pt (xL a) y :: rt xL a w y := by
      intro v hv1 hv2
      unfold botMid at hv1; split_ifs at hv1 with ha
      · simp only [List.mem_singleton] at hv1; subst hv1
        rcases List.mem_cons.mp hv2 with h | h
        · have := (pt_inj.mp h).1; rw [ha] at this; simp [xL] at this
        · have := rt_level h; simp at this
      · simp at hv1
    have tB : ∀ v ∈ topMid (lst a w) (top w y), v ∉ botMid a y := by
      intro v hv1 hv2
      unfold topMid at hv1; unfold botMid at hv2
      split_ifs at hv1 hv2 <;> simp at hv1 hv2
      subst hv1; have := (pt_inj.mp hv2).2; simp [top] at this; omega
    have nT : (topMid (lst a w) (top w y)).Nodup := by unfold topMid; split_ifs <;> simp
    have nB : (botMid a y).Nodup := by unfold botMid; split_ifs <;> simp
    simp only [List.nodup_append]
    refine ⟨⟨⟨nR, nL, ?_⟩, nT, ?_⟩, nB, ?_⟩
    · intro v h1 v' h2 he; subst he; exact dRL v h1 h2
    · intro v h1 v' h2 he; subst he
      rcases List.mem_append.mp h1 with h1 | h1
      · exact tR v h2 h1
      · exact tL v h2 h1
    · intro v h1 v' h2 he; subst he
      rcases List.mem_append.mp h1 with h1 | h1
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact bR v h2 h1
        · exact bL v h2 h1
      · exact tB v h1 h2
  · rw [poly_length a w y hv]
    have := cost_ge a w
    omega


end SAWB

/-! Part B8: every cycle through the origin is a rotated polygon; the count. -/

namespace SAWB

open SAWS SAWG

theorem len_rotate {u v : V} (c : strip.Walk v v) (h : u ∈ c.support) : (c.rotate u h).length = c.length := by
  exact Walk.length_rotate c u h

theorem mem_edges_rotate {u v : V} (c : strip.Walk v v) (h : u ∈ c.support) (e : Sym2 V) :
    e ∈ (c.rotate u h).edges ↔ e ∈ c.edges := (Walk.rotate_edges c u h).mem_iff

/-- a cycle through the origin uses a vertical edge at the origin -/
theorem origin_vert {u : V} {d : strip.Walk u u} (hd : d.IsCycle) (h : origin ∈ d.support) :
    vert 0 (0 - 1) ∈ d.edges ∨ vert 0 0 ∈ d.edges := by
  have h2 : (d.toSubgraph.neighborSet (pt 0 0)).ncard = 2 := hd.ncard_neighborSet_toSubgraph_eq_two h
  have hsub : d.toSubgraph.neighborSet (pt 0 0) ⊆
      ↑({pt 0 (0 - 1), pt 0 (0 + 1), pt 1 0} : Finset V) := by
    intro w hw
    rcases nbr_cases (nbr_adj hw) with h | h | ⟨hy, h | h⟩
    · simp [h]
    · simp [h]
    · have := xbd w; simp at h; omega
    · rw [eq_pt w (x := 1) (by simpa using h) hy]; simp
  rw [ncard_of_subset hsub, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨pt_ne_y (by omega), pt_ne_y (by omega)⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact pt_ne_y (by omega)),
    Finset.sum_singleton] at h2
  simp only [nbr_down, nbr_up, nbr_01] at h2
  by_contra hn
  push_neg at hn
  rw [if_neg hn.1, if_neg (show vert 0 0 ∉ d.edges from by simpa using hn.2)] at h2
  split_ifs at h2 <;> omega

/-- the middle vertex of level 0 -/
def o1 : V := pt 1 0

theorem cycle_has_vert {u : V} {d : strip.Walk u u} (hd : d.IsCycle) : ∃ x t, vert x t ∈ d.edges := by
  have hs : s(u, d.snd) ∈ d.edges := by
    rw [← mem_nbr, hd.neighborSet_toSubgraph_endpoint]; simp
  rcases edge_cases (d.adj_of_mem_edges hs) with ⟨x, t, he⟩ | ⟨y, he⟩ | ⟨y, he⟩
  · exact ⟨x, t, he ▸ hs⟩
  · rw [he] at hs
    have := (local_rule hd y).1.mp hs
    by_cases h : vert 0 (y - 1) ∈ d.edges
    · exact ⟨0, y - 1, h⟩
    · exact ⟨0, y, by tauto⟩
  · rw [he] at hs
    have := (local_rule hd y).2.1.mp hs
    by_cases h : vert 2 (y - 1) ∈ d.edges
    · exact ⟨2, y - 1, h⟩
    · exact ⟨2, y, by tauto⟩

section oc
variable {c : strip.Walk o1 o1}

def ys (c : strip.Walk o1 o1) : Finset ℤ := c.support.toFinset.image (fun v : V => v.1.2)

theorem ys_ne (c : strip.Walk o1 o1) : (ys c).Nonempty :=
  ⟨0, by simp only [ys, Finset.mem_image, List.mem_toFinset]; exact ⟨o1, c.start_mem_support, rfl⟩⟩

def ymin (c : strip.Walk o1 o1) : ℤ := (ys c).min' (ys_ne c)
def ymax (c : strip.Walk o1 o1) : ℤ := (ys c).max' (ys_ne c)

theorem y_mem {v : V} (hv : v ∈ c.support) : v.1.2 ∈ ys c := by
  simp only [ys, Finset.mem_image, List.mem_toFinset]; exact ⟨v, hv, rfl⟩

theorem ymin_le {v : V} (hv : v ∈ c.support) : ymin c ≤ v.1.2 := Finset.min'_le _ _ (y_mem hv)
theorem le_ymax {v : V} (hv : v ∈ c.support) : v.1.2 ≤ ymax c := Finset.le_max' _ _ (y_mem hv)

theorem ex_ymin (c : strip.Walk o1 o1) : ∃ v ∈ c.support, v.1.2 = ymin c := by
  have := Finset.min'_mem (ys c) (ys_ne c)
  simp only [ys, Finset.mem_image, List.mem_toFinset] at this
  exact this
theorem ex_ymax (c : strip.Walk o1 o1) : ∃ v ∈ c.support, v.1.2 = ymax c := by
  have := Finset.max'_mem (ys c) (ys_ne c)
  simp only [ys, Finset.mem_image, List.mem_toFinset] at this
  exact this

theorem ymin_le0 : ymin c ≤ 0 := ymin_le (v := o1) c.start_mem_support
theorem ymax_ge0 : 0 ≤ ymax c := le_ymax (v := o1) c.start_mem_support

theorem vert_range {x : Fin 3} {t : ℤ} (h : vert x t ∈ c.edges) : ymin c ≤ t ∧ t + 1 ≤ ymax c := by
  unfold vert at h
  have h1 := ymin_le (c.fst_mem_support_of_mem_edges h)
  have h2 := le_ymax (c.snd_mem_support_of_mem_edges h)
  simp only [pt_snd] at h1 h2
  exact ⟨h1, h2⟩

theorem same_side (t : ℤ) (h0 : c.edges.countP (isV t) = 0) {v : V} (hv : v ∈ c.support) :
    (v.1.2 ≤ t ↔ (0 : ℤ) ≤ t) := by
  have hsplit := c.take_spec hv
  have hc : (c.takeUntil v hv).edges.countP (isV t) = 0 := by
    have := congrArg (fun p => p.edges.countP (isV t)) hsplit
    simp only [Walk.edges_append, List.countP_append] at this
    omega
  have hp := cross_parity t (c.takeUntil v hv)
  rw [hc] at hp
  have h00 : (o1 : V).1.2 = 0 := rfl
  rw [h00] at hp
  have key : decide ((0 : ℤ) ≤ t) = decide (v.1.2 ≤ t) := by
    by_contra hne
    have hb : (decide ((0 : ℤ) ≤ t) != decide (v.1.2 ≤ t)) = true := by simpa [bne_iff_ne] using hne
    rw [hb] at hp
    simp [b2n] at hp
  exact (decide_eq_decide.mp key).symm

theorem layer_two (hc : c.IsCycle) {t : ℤ} (h1 : ymin c ≤ t) (h2 : t < ymax c) :
    bE (vert 0 t) c + bE (vert 1 t) c + bE (vert 2 t) c = 2 := by
  rcases layer hc t with h | h
  · exfalso
    rw [← countP_layer hc] at h
    obtain ⟨v1, hv1, e1⟩ := ex_ymin c
    obtain ⟨v2, hv2, e2⟩ := ex_ymax c
    have s1 := same_side t h hv1
    have s2 := same_side t h hv2
    have a1 : v1.1.2 ≤ t := by omega
    have a2 : ¬ v2.1.2 ≤ t := by omega
    exact a2 (s2.mpr (s1.mp a1))
  · exact h

def letter (c : strip.Walk o1 o1) (t : ℤ) : Fin 3 :=
  if vert 2 t ∉ c.edges then 0 else if vert 0 t ∉ c.edges then 1 else 2

theorem pattern {t : ℤ} (h2 : bE (vert 0 t) c + bE (vert 1 t) c + bE (vert 2 t) c = 2) (x : Fin 3) :
    vert x t ∈ c.edges ↔ x = xR (letter c t) ∨ x = xL (letter c t) := by
  unfold letter
  unfold bE b2n at h2
  by_cases e0 : vert 0 t ∈ c.edges <;> by_cases e1 : vert 1 t ∈ c.edges <;>
    by_cases e2 : vert 2 t ∈ c.edges <;> simp only [e0, e1, e2, decide_true, decide_false,
      if_true, if_false, Bool.false_eq_true, not_true_eq_false, not_false_eq_true] at h2 ⊢ <;>
    (try omega) <;> fin_cases x <;> simp_all [xR, xL]

def kk (c : strip.Walk o1 o1) : ℕ := (ymax c - ymin c).toNat
def wa (c : strip.Walk o1 o1) : Fin 3 := letter c (ymin c)
def ww (c : strip.Walk o1 o1) : List (Fin 3) :=
  (List.range (kk c - 1)).map (fun j : ℕ => letter c (ymin c + 1 + (j : ℤ)))

theorem ww_length : (ww c).length = kk c - 1 := by simp [ww]

theorem kk_eq : ((kk c : ℕ) : ℤ) = ymax c - ymin c := by
  unfold kk
  have : ymin c ≤ ymax c := le_trans ymin_le0 ymax_ge0
  exact Int.toNat_of_nonneg (by omega)

theorem kk_pos (hc : c.IsCycle) : 1 ≤ kk c := by
  have := kk_eq (c := c)
  obtain ⟨x, t, h⟩ := cycle_has_vert hc
  have := vert_range h; omega

theorem row_ww (j : ℕ) (hj : j ≤ (ww c).length) : row (wa c) (ww c) j = letter c (ymin c + j) := by
  rcases j with _ | j
  · simp [row, wa]
  · rw [ww_length] at hj
    simp only [row, ww, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    push_cast; ring

theorem val_iff (a : Fin 3) (w : List (Fin 3)) :
    Val a w ↔ ∀ j < w.length, SAWC.comp (row a w j) (row a w (j + 1)) = true := by
  induction w generalizing a with
  | nil => simp [Val]
  | cons c w ih =>
    simp only [Val, ih, List.length_cons]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases j with _ | j
      · simpa [row] using h1
      · have := h2 j (by omega); simpa [row] using this
    · intro h
      exact ⟨by simpa [row] using h 0 (by omega), fun j hj => by simpa [row] using h (j + 1) (by omega)⟩

theorem ww_val (hc : c.IsCycle) : Val (wa c) (ww c) := by
  rw [val_iff]
  intro j hj
  have hk := kk_eq (c := c)
  have hl := ww_length (c := c)
  rw [row_ww j (by omega), row_ww (j + 1) (by omega)]
  have L1 := layer_two hc (t := ymin c + j) (by omega) (by omega)
  have L2 := layer_two hc (t := ymin c + ↑(j + 1)) (by push_cast; omega) (by push_cast; omega)
  have P1 := pattern L1
  have P2 := pattern L2
  have R := (local_rule hc (ymin c + ↑(j + 1))).2.2
  rw [show ymin c + ↑(j + 1) - 1 = ymin c + ↑j by push_cast; ring] at R
  generalize ymin c + ↑(j + 1) = t1 at *
  generalize ymin c + ↑j = t0 at *
  by_contra hne
  have : (letter c t0 = 0 ∧ letter c t1 = 1) ∨
      (letter c t0 = 1 ∧ letter c t1 = 0) := by
    revert hne
    generalize letter c t0 = p
    generalize letter c t1 = q
    fin_cases p <;> fin_cases q <;> simp [SAWC.comp]
  rcases this with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact R.1 ⟨(P1 0).mpr (by simp [hp, xR, xL]), (P1 1).mpr (by simp [hp, xR, xL]),
      fun h => by have := (P1 2).mp h; simp [hp, xR, xL] at this,
      fun h => by have := (P2 0).mp h; simp [hq, xR, xL] at this,
      (P2 1).mpr (by simp [hq, xR, xL]), (P2 2).mpr (by simp [hq, xR, xL])⟩
  · exact R.2 ⟨fun h => by have := (P1 0).mp h; simp [hp, xR, xL] at this,
      (P1 1).mpr (by simp [hp, xR, xL]), (P1 2).mpr (by simp [hp, xR, xL]),
      (P2 0).mpr (by simp [hq, xR, xL]), (P2 1).mpr (by simp [hq, xR, xL]),
      fun h => by have := (P2 2).mp h; simp [hq, xR, xL] at this⟩

theorem vert_agree (hc : c.IsCycle) (x : Fin 3) (t : ℤ) :
    vert x t ∈ c.edges ↔ vert x t ∈ (poly (wa c) (ww c) (ymin c)).edges := by
  rw [poly_vert]
  have hk := kk_eq (c := c)
  have hl := ww_length (c := c)
  have hk1 := kk_pos hc
  constructor
  · intro h
    obtain ⟨r1, r2⟩ := vert_range h
    have e := Int.toNat_of_nonneg (show 0 ≤ t - ymin c by omega)
    refine ⟨(t - ymin c).toNat, by omega, by omega, ?_⟩
    rw [row_ww _ (by omega), show ymin c + ((t - ymin c).toNat : ℤ) = t by omega]
    exact (pattern (layer_two hc r1 (by omega)) x).mp h
  · rintro ⟨j, hj, rfl, hx⟩
    rw [row_ww j hj] at hx
    exact (pattern (layer_two hc (by omega) (by omega)) x).mpr hx

/-- the polygon of a cycle through `o1` contains `o1` -/
theorem origin_mem_poly (hc : c.IsCycle) : o1 ∈ (poly (wa c) (ww c) (ymin c)).support := by
  have hE := edges_iff_of_vert hc (poly_isCycle _ _ _ (ww_val hc)) (vert_agree hc)
  have hs : s(o1, c.snd) ∈ c.edges := by
    rw [← mem_nbr, hc.neighborSet_toSubgraph_endpoint]; simp
  exact Walk.fst_mem_support_of_mem_edges _ ((hE _ _).mp hs)

theorem cycle_struct (hc : c.IsCycle) :
    c = (poly (wa c) (ww c) (ymin c)).rotate o1 (origin_mem_poly hc) ∨
    c = ((poly (wa c) (ww c) (ymin c)).rotate o1 (origin_mem_poly hc)).reverse := by
  set P := poly (wa c) (ww c) (ymin c) with hPdef
  have hP : P.IsCycle := poly_isCycle _ _ _ (ww_val hc)
  have hE := edges_iff_of_vert hc hP (vert_agree hc)
  set c1 := P.rotate o1 (origin_mem_poly hc)
  have hc1 : c1.IsCycle := hP.rotate _
  have hN : ∀ v, c.toSubgraph.neighborSet v = c1.toSubgraph.neighborSet v := by
    intro v; rw [Walk.toSubgraph_rotate]; ext w; rw [mem_nbr, mem_nbr, hE]
  have hN' : ∀ v, c.toSubgraph.neighborSet v = c1.reverse.toSubgraph.neighborSet v := by
    intro v; rw [Walk.toSubgraph_reverse]; exact hN v
  have hs : c.snd ∈ c.toSubgraph.neighborSet o1 := by
    rw [hc.neighborSet_toSubgraph_endpoint]; simp
  rw [hN, hc1.neighborSet_toSubgraph_endpoint] at hs
  rcases Set.mem_insert_iff.mp hs with hs | hs
  · left; exact cycle_unique hc hc1 hN hs
  · right
    have hs := Set.mem_singleton_iff.mp hs
    apply cycle_unique hc hc1.reverse hN'
    have : c1.reverse.snd = c1.penultimate := Walk.snd_reverse c1
    exact hs.trans this.symm

end oc

end SAWB

/-! Part B9: the bijection with marked words, and the main theorem. -/

namespace SAWB

open SAWS SAWG PowerSeries

theorem mem_S_iff (p : ℕ) (a : Fin 3) (u : List (Fin 3)) :
    u ∈ SAWC.S p a ↔ ∃ w, u = a :: w ∧ Val a w ∧ SAWC.cost (a :: w) = p := by
  induction p using Nat.strong_induction_on generalizing a u with
  | _ p ih =>
    by_cases hp : p < 3
    · rw [SAWC.S_lt hp]
      constructor
      · intro h; simp at h
      · rintro ⟨w, rfl, _, hc⟩; have := cost_ge a w; omega
    · rw [SAWC.S_eq (by omega)]
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro (h | ⟨b, hb, t, ht, rfl⟩)
        · split_ifs at h with hpe
          · rw [Finset.mem_singleton] at h
            subst h
            exact ⟨[], rfl, trivial, by simp [SAWC.cost, hpe]⟩
          · simp at h
        · have hs := SAWC.stepc_ge a b
          obtain ⟨w', rfl, hv, hc⟩ := (ih (p - SAWC.stepc a b) (by omega) b t).mp ht
          have hcw := cost_ge b w'
          exact ⟨b :: w', rfl, ⟨hb, hv⟩, by simp only [SAWC.cost]; omega⟩
      · rintro ⟨w, rfl, hv, hc⟩
        cases w with
        | nil =>
          left
          have : p = 2 + SAWC.e a := by simp [SAWC.cost] at hc; omega
          simp [this]
        | cons b w' =>
          right
          have hs := SAWC.stepc_ge a b
          simp only [SAWC.cost] at hc
          exact ⟨b, hv.1, b :: w', (ih _ (Nat.sub_lt (by omega) (by omega)) b _).mpr ⟨w', rfl, hv.2, by omega⟩, rfl⟩

/-- level `i` of the word `u` has its middle vertex on the polygon -/
def mk1 (u : List (Fin 3)) (i : ℕ) : Prop :=
  i ≤ u.length ∧ (i = 0 ∨ i = u.length ∨ (1 ≤ i ∧ u.getD (i - 1) 0 ≠ 2) ∨ (i < u.length ∧ u.getD i 0 ≠ 2))

instance (u : List (Fin 3)) : DecidablePred (mk1 u) := fun i => by unfold mk1; infer_instance

theorem mk1_zero (u : List (Fin 3)) : mk1 u 0 := ⟨Nat.zero_le _, Or.inl rfl⟩

theorem mk1_one (a b : Fin 3) (w : List (Fin 3)) : mk1 (a :: b :: w) 1 ↔ (a ≠ 2 ∨ b ≠ 2) := by
  simp only [mk1, List.length_cons, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_self]
  constructor
  · rintro ⟨_, h | h | ⟨_, h⟩ | ⟨_, h⟩⟩
    · omega
    · omega
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))⟩
    · exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, h⟩))⟩

theorem mk1_shift (a b : Fin 3) (w : List (Fin 3)) (i : ℕ) :
    mk1 (a :: b :: w) (i + 1 + 1) ↔ mk1 (b :: w) (i + 1) := by
  simp only [mk1, List.length_cons, Nat.add_sub_cancel, List.getD_cons_succ]
  generalize (b :: w).getD i 0 = p
  generalize (b :: w).getD (i + 1) 0 = q
  generalize w.length = L
  by_cases hp : p = 2 <;> by_cases hq : q = 2 <;> simp [hp, hq] <;> omega

theorem mk1_single (a : Fin 3) (i : ℕ) : mk1 [a] i ↔ i ≤ 1 := by
  simp only [mk1, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨h, -⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

theorem sum_mk1 (a : Fin 3) (w : List (Fin 3)) : ∀ N, w.length + 1 < N →
    ∑ i ∈ Finset.range N, (if mk1 (a :: w) i then 1 else 0) = SAWC.marks1 (a :: w) := by
  induction w generalizing a with
  | nil =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by simp at hN; omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    rw [Finset.sum_eq_zero (fun i _ => if_neg (by rw [mk1_single]; omega))]
    rw [if_pos ((mk1_single a _).mpr (by omega)), if_pos ((mk1_single a _).mpr (by omega))]
    rfl
  | cons b w ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by simp at hN; omega⟩
    have h := ih b (M + 1) (by simp at hN ⊢; omega)
    rw [Finset.sum_range_succ', if_pos (mk1_zero _)] at h
    rw [Finset.sum_range_succ', Finset.sum_range_succ', if_pos (mk1_zero _)]
    simp only [mk1_shift, zero_add, mk1_one, SAWC.marks1]
    split_ifs <;> omega

/-! The bijection. -/

abbrev Idx := (Σ _ : Fin 3, List (Fin 3)) × ℕ × Bool

def Dom (n : ℕ) : Finset Idx :=
  ((Finset.univ.sigma fun a => SAWC.S (2 * n - SAWC.e a) a) ×ˢ
    (Finset.range (2 * n + 1) ×ˢ (Finset.univ : Finset Bool))).filter (fun x => mk1 x.1.2 x.2.1)

def Φ (x : Idx) : strip.Walk o1 o1 :=
  if h : o1 ∈ (poly x.1.1 x.1.2.tail (-(x.2.1 : ℤ))).support then
    (if x.2.2 then ((poly x.1.1 x.1.2.tail (-(x.2.1 : ℤ))).rotate o1 h).reverse
     else (poly x.1.1 x.1.2.tail (-(x.2.1 : ℤ))).rotate o1 h)
  else Walk.nil

theorem ne2_of_one {r : Fin 3} (h : 1 = xR r ∨ 1 = xL r) : r ≠ 2 := by
  revert h; fin_cases r <;> simp [xR, xL]

theorem one_of_ne2 {r : Fin 3} (h : r ≠ 2) : 1 = xR r ∨ 1 = xL r := by
  revert h; fin_cases r <;> simp [xR, xL]

theorem zero_of_two {r : Fin 3} (h : r = 2) : 0 = xR r ∨ 0 = xL r := by
  subst h; simp [xR, xL]

theorem two_of_two {r : Fin 3} (h : r = 2) : 2 = xR r ∨ 2 = xL r := by
  subst h; simp [xR, xL]

theorem bot_mem (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : pt 1 y ∈ (poly a w y).support := by
  apply List.mem_of_mem_tail
  rw [poly_support_tail]
  fin_cases a <;> simp [xR, xL, botMid]

theorem top_mem (a : Fin 3) (w : List (Fin 3)) (y : ℤ) : pt 1 (top w y) ∈ (poly a w y).support := by
  apply List.mem_of_mem_tail
  rw [poly_support_tail]
  have hs := rt_split xR step1_xR a w y
  have : lst a w = 0 ∨ lst a w = 1 ∨ lst a w = 2 := by
    generalize lst a w = l; fin_cases l <;> simp
  rcases this with hl | hl | hl
  · rw [hs]; simp [hl, xR]
  · simp [hl, xL]
  · simp [hl, topMid]

theorem origin_mem_iff (a : Fin 3) (w : List (Fin 3)) (i : ℕ) (hv : Val a w) :
    o1 ∈ (poly a w (-(i : ℤ))).support ↔ mk1 (a :: w) i := by
  have hP := poly_isCycle a w (-(i : ℤ)) hv
  have vv : ∀ (x : Fin 3) (t : ℤ), vert x t ∈ (poly a w (-(i : ℤ))).edges →
      ∃ j : ℕ, j ≤ w.length ∧ t = -(i : ℤ) + j := by
    intro x t ht; rw [poly_vert] at ht; obtain ⟨j, hj, htj, -⟩ := ht; exact ⟨j, hj, htj⟩
  constructor
  · intro h
    have h2 := hP.ncard_neighborSet_toSubgraph_eq_two h
    obtain ⟨w0, hw0⟩ := Set.nonempty_of_ncard_ne_zero
      (by omega : ((poly a w (-(i : ℤ))).toSubgraph.neighborSet o1).ncard ≠ 0)
    have he := mem_nbr.mp hw0
    have hadj : strip.Adj (pt 1 0) w0 := nbr_adj hw0
    -- the generic finish once the column-`x` verticals around level `0` are known to be exclusive
    have finish : ∀ x : Fin 3, x ≠ 1 →
        (vert x (0 - 1) ∈ (poly a w (-(i : ℤ))).edges ↔ ¬ vert x 0 ∈ (poly a w (-(i : ℤ))).edges) →
        (∀ r : Fin 3, r = 2 → x = xR r ∨ x = xL r) → mk1 (a :: w) i := by
      intro x _ lr hx2
      have hb : (1 ≤ i ∧ i ≤ w.length + 1) ∨ i ≤ w.length := by
        by_cases hA : vert x (0 - 1) ∈ (poly a w (-(i : ℤ))).edges
        · obtain ⟨j, hj, htj⟩ := vv _ _ hA; left; omega
        · have hB : vert x 0 ∈ (poly a w (-(i : ℤ))).edges := by tauto
          obtain ⟨j, hj, htj⟩ := vv _ _ hB; right; omega
      by_cases hr1 : 1 ≤ i ∧ (a :: w).getD (i - 1) 0 ≠ 2
      · exact ⟨by simp; omega, Or.inr (Or.inr (Or.inl hr1))⟩
      by_cases hr2 : i < (a :: w).length ∧ (a :: w).getD i 0 ≠ 2
      · exact ⟨by simp; omega, Or.inr (Or.inr (Or.inr hr2))⟩
      by_cases hi0 : i = 0
      · exact ⟨by simp [hi0], Or.inl hi0⟩
      by_cases hiL : i = (a :: w).length
      · exact ⟨le_of_eq hiL, Or.inr (Or.inl hiL)⟩
      exfalso
      simp only [List.length_cons] at hr2 hiL
      have e1 : (a :: w).getD (i - 1) 0 = 2 := by
        by_contra hc; exact hr1 ⟨by omega, hc⟩
      have e2 : (a :: w).getD i 0 = 2 := by
        by_contra hc; exact hr2 ⟨by omega, hc⟩
      have A1 : vert x (0 - 1) ∈ (poly a w (-(i : ℤ))).edges := by
        rw [poly_vert]; exact ⟨i - 1, by omega, by omega, hx2 _ e1⟩
      have A2 : vert x 0 ∈ (poly a w (-(i : ℤ))).edges := by
        rw [poly_vert]; exact ⟨i, by omega, by omega, hx2 _ e2⟩
      exact (lr.mp A1) A2
    rcases nbr_cases hadj with hw | hw | ⟨hy, hw | hw⟩
    · have hv1 : vert 1 (0 - 1) ∈ (poly a w (-(i : ℤ))).edges := by
        rw [hw] at he; rw [vert, sub_add_cancel, Sym2.eq_swap]; exact he
      rw [poly_vert] at hv1
      obtain ⟨j, hj, ht, hx⟩ := hv1
      refine ⟨by simp; omega, Or.inr (Or.inr (Or.inl ⟨by omega, ?_⟩))⟩
      rw [show i - 1 = j by omega]; exact ne2_of_one hx
    · have hv1 : vert 1 0 ∈ (poly a w (-(i : ℤ))).edges := by
        rw [hw] at he; exact he
      rw [poly_vert] at hv1
      obtain ⟨j, hj, ht, hx⟩ := hv1
      refine ⟨by simp; omega, Or.inr (Or.inr (Or.inr ⟨by simp; omega, ?_⟩))⟩
      rw [show i = j by omega]; exact ne2_of_one hx
    · have hw0' : w0 = pt 0 0 := eq_pt w0 (by simp at hw ⊢; omega) hy
      have hh : hor0 0 ∈ (poly a w (-(i : ℤ))).edges := by
        rw [hw0'] at he; rw [hor0, Sym2.eq_swap]; exact he
      exact finish 0 (by decide) ((local_rule hP 0).1.mp hh) (fun r hr => zero_of_two hr)
    · have hw0' : w0 = pt 2 0 := eq_pt w0 (by simp at hw ⊢; omega) hy
      have hh : hor1 0 ∈ (poly a w (-(i : ℤ))).edges := by
        rw [hw0'] at he; exact he
      exact finish 2 (by decide) ((local_rule hP 0).2.1.mp hh) (fun r hr => two_of_two hr)
  · rintro ⟨hi, h0 | hL | ⟨h1, hr⟩ | ⟨h1, hr⟩⟩
    · have e : (pt 1 (-((i : ℕ) : ℤ)) : V) = o1 := by
        simp [h0, o1]
      rw [← e]; exact bot_mem a w _
    · have e : (pt 1 (top w (-((i : ℕ) : ℤ))) : V) = o1 := by
        unfold top o1; congr 1; simp at hL; omega
      rw [← e]; exact top_mem a w _
    · have hv1 : vert 1 (0 - 1) ∈ (poly a w (-(i : ℤ))).edges := by
        rw [poly_vert]; exact ⟨i - 1, by simp at hi; omega, by omega, one_of_ne2 hr⟩
      unfold vert at hv1
      have := Walk.snd_mem_support_of_mem_edges _ hv1
      rwa [sub_add_cancel] at this
    · have hv1 : vert 1 0 ∈ (poly a w (-(i : ℤ))).edges := by
        rw [poly_vert]; exact ⟨i, by simp at h1; omega, by omega, one_of_ne2 hr⟩
      unfold vert at hv1
      exact Walk.fst_mem_support_of_mem_edges _ hv1

theorem dom_spec {n : ℕ} {x : Idx} (hx : x ∈ Dom n) :
    ∃ w, x.1.2 = x.1.1 :: w ∧ Val x.1.1 w ∧ SAWC.e x.1.1 + SAWC.cost (x.1.1 :: w) = 2 * n ∧
      mk1 x.1.2 x.2.1 ∧ x.2.1 < 2 * n + 1 := by
  obtain ⟨⟨a, u⟩, i, d⟩ := x
  simp only [Dom, Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_range, and_true] at hx
  obtain ⟨⟨hu, hi⟩, hm⟩ := hx
  obtain ⟨w, rfl, hv, hc⟩ := (mem_S_iff _ _ _).mp hu
  refine ⟨w, rfl, hv, ?_, hm, hi⟩
  show SAWC.e a + SAWC.cost (a :: w) = 2 * n
  have := cost_ge a w
  have : SAWC.e a ≤ 2 := by unfold SAWC.e; split_ifs <;> omega
  omega

theorem Φ_eq (a : Fin 3) (w : List (Fin 3)) (i : ℕ) (d : Bool)
    (ho : o1 ∈ (poly a w (-(i : ℤ))).support) :
    Φ ⟨⟨a, a :: w⟩, i, d⟩ = (if d then ((poly a w (-(i : ℤ))).rotate o1 ho).reverse
      else (poly a w (-(i : ℤ))).rotate o1 ho) := by
  unfold Φ
  split_ifs with h hd <;> first | rfl | exact absurd ho h

theorem Φ_spec {n : ℕ} {x : Idx} (hx : x ∈ Dom n) : (Φ x).IsCycle ∧ (Φ x).length = 2 * n := by
  obtain ⟨w, hu, hv, hlen, hm, -⟩ := dom_spec hx
  obtain ⟨⟨a, u⟩, i, d⟩ := x
  simp only at hu hv hlen hm ⊢
  subst hu
  have hP := poly_isCycle a w (-(i : ℤ)) hv
  have ho := (origin_mem_iff a w i hv).mpr hm
  have hl := poly_length a w (-(i : ℤ)) hv
  rw [Φ_eq a w i d ho]
  cases d
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨hP.rotate _, by rw [len_rotate]; omega⟩
  · simp only [if_true]
    exact ⟨(hP.rotate _).reverse, by rw [Walk.length_reverse, len_rotate]; omega⟩

theorem Φ_surj {n : ℕ} {c : strip.Walk o1 o1} (hc : c.IsCycle) (hl : c.length = 2 * n) :
    ∃ x ∈ Dom n, Φ x = c := by
  have hv := ww_val hc
  have hm0 := ymin_le0 (c := c)
  have hie : (-(((-(ymin c)).toNat : ℕ) : ℤ)) = ymin c := by
    have := Int.toNat_of_nonneg (show 0 ≤ -(ymin c) by omega); omega
  have hP := poly_isCycle (wa c) (ww c) (ymin c) hv
  have hlenP := poly_length (wa c) (ww c) (ymin c) hv
  have hcl : c.length = SAWC.e (wa c) + SAWC.cost (wa c :: ww c) := by
    rcases cycle_struct hc with h | h
    · have := congrArg Walk.length h; rw [this, len_rotate, hlenP]
    · have := congrArg Walk.length h; rw [this, Walk.length_reverse, len_rotate, hlenP]
  have hcg := cost_ge (wa c) (ww c)
  have he : SAWC.e (wa c) ≤ 2 := by unfold SAWC.e; split_ifs <;> omega
  have hu : (wa c :: ww c) ∈ SAWC.S (2 * n - SAWC.e (wa c)) (wa c) :=
    (mem_S_iff _ _ _).mpr ⟨ww c, rfl, hv, by omega⟩
  have key : ∀ (y : ℤ) (hy : y = ymin c) (h : o1 ∈ (poly (wa c) (ww c) y).support),
      (poly (wa c) (ww c) y).rotate o1 h =
        (poly (wa c) (ww c) (ymin c)).rotate o1 (origin_mem_poly hc) := by
    rintro y rfl h; rfl
  have ho : o1 ∈ (poly (wa c) (ww c) (-(((-(ymin c)).toNat : ℕ) : ℤ))).support := by
    rw [hie]; exact origin_mem_poly hc
  have hm : mk1 (wa c :: ww c) (-(ymin c)).toNat := (origin_mem_iff _ _ _ hv).mp ho
  have hilen : (-(ymin c)).toNat ≤ (ww c).length + 1 := by have := hm.1; simpa using this
  have hdom : ∀ d : Bool, (⟨⟨wa c, wa c :: ww c⟩, (-(ymin c)).toNat, d⟩ : Idx) ∈ Dom n := by
    intro d
    simp only [Dom, Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_range, and_true]
    exact ⟨⟨hu, by omega⟩, hm⟩
  rcases cycle_struct hc with h | h
  · refine ⟨_, hdom false, ?_⟩
    rw [Φ_eq _ _ _ _ ho, key _ hie ho]
    simp only [Bool.false_eq_true, if_false]
    exact h.symm
  · refine ⟨_, hdom true, ?_⟩
    rw [Φ_eq _ _ _ _ ho, key _ hie ho]
    simp only [if_true]
    exact h.symm

theorem pat_inj {r r' : Fin 3} (h : ∀ X : Fin 3, (X = xR r ∨ X = xL r) ↔ (X = xR r' ∨ X = xL r')) :
    r = r' := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  revert h0 h1 h2; fin_cases r <;> fin_cases r' <;> simp [xR, xL]

theorem Φ_inj (n : ℕ) : Set.InjOn Φ ↑(Dom n) := by
  intro x hx x' hx' heq
  obtain ⟨w, hu, hv, hlen, hm, -⟩ := dom_spec hx
  obtain ⟨w', hu', hv', hlen', hm', -⟩ := dom_spec hx'
  obtain ⟨⟨a, u⟩, i, d⟩ := x
  obtain ⟨⟨a', u'⟩, i', d'⟩ := x'
  simp only at hu hv hlen hm hu' hv' hlen' hm' heq ⊢
  subst hu; subst hu'
  have ho := (origin_mem_iff a w i hv).mpr hm
  have ho' := (origin_mem_iff a' w' i' hv').mpr hm'
  rw [Φ_eq a w i d ho, Φ_eq a' w' i' d' ho'] at heq
  have hE : ∀ e, e ∈ (poly a w (-(i : ℤ))).edges ↔ e ∈ (poly a' w' (-(i' : ℤ))).edges := by
    intro e
    have h1 : e ∈ (if d then ((poly a w (-(i : ℤ))).rotate o1 ho).reverse
        else (poly a w (-(i : ℤ))).rotate o1 ho).edges ↔ e ∈ (poly a w (-(i : ℤ))).edges := by
      cases d <;> simp [Walk.edges_reverse, mem_edges_rotate]
    have h2 : e ∈ (if d' then ((poly a' w' (-(i' : ℤ))).rotate o1 ho').reverse
        else (poly a' w' (-(i' : ℤ))).rotate o1 ho').edges ↔ e ∈ (poly a' w' (-(i' : ℤ))).edges := by
      cases d' <;> simp [Walk.edges_reverse, mem_edges_rotate]
    rw [← h1, ← h2, heq]
  have hV : ∀ X T, (∃ j : ℕ, j ≤ w.length ∧ T = -(i : ℤ) + j ∧ (X = xR (row a w j) ∨ X = xL (row a w j))) ↔
      (∃ j : ℕ, j ≤ w'.length ∧ T = -(i' : ℤ) + j ∧ (X = xR (row a' w' j) ∨ X = xL (row a' w' j))) := by
    intro X T; rw [← poly_vert, ← poly_vert]; exact hE _
  have hii : i = i' := by
    obtain ⟨j, -, hj, -⟩ := (hV (xR (row a w 0)) (-(i : ℤ))).mp ⟨0, by omega, by simp, Or.inl rfl⟩
    obtain ⟨j', -, hj', -⟩ := (hV (xR (row a' w' 0)) (-(i' : ℤ))).mpr ⟨0, by omega, by simp, Or.inl rfl⟩
    omega
  subst hii
  have hll : w.length = w'.length := by
    obtain ⟨j, hj1, hj, -⟩ := (hV (xR (row a w w.length)) (-(i : ℤ) + w.length)).mp
      ⟨w.length, le_rfl, rfl, Or.inl rfl⟩
    obtain ⟨j', hj1', hj', -⟩ := (hV (xR (row a' w' w'.length)) (-(i : ℤ) + w'.length)).mpr
      ⟨w'.length, le_rfl, rfl, Or.inl rfl⟩
    omega
  have hrow : ∀ j ≤ w.length, row a w j = row a' w' j := by
    intro j hj
    apply pat_inj
    intro X
    have hX := hV X (-(i : ℤ) + j)
    constructor
    · intro h
      obtain ⟨j1, -, hj1, hX1⟩ := hX.mp ⟨j, hj, rfl, h⟩
      have : j1 = j := by omega
      rw [this] at hX1; exact hX1
    · intro h
      obtain ⟨j1, -, hj1, hX1⟩ := hX.mpr ⟨j, by omega, rfl, h⟩
      have : j1 = j := by omega
      rw [this] at hX1; exact hX1
  have haa : a = a' := by have := hrow 0 (by omega); simpa [row] using this
  subst haa
  have hww : w = w' := by
    apply List.ext_getElem hll
    intro j h1 h2
    have := hrow (j + 1) (by omega)
    simp only [row, List.getD_cons_succ] at this
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  subst hww
  have hc1 : ((poly a w (-(i : ℤ))).rotate o1 ho).IsCycle := (poly_isCycle a w _ hv).rotate _
  have hne : (poly a w (-(i : ℤ))).rotate o1 ho ≠ ((poly a w (-(i : ℤ))).rotate o1 ho).reverse := by
    intro h
    apply hc1.snd_ne_penultimate
    rw [← Walk.snd_reverse, ← h]
  cases d <;> cases d' <;> simp only [Bool.false_eq_true, if_false, if_true] at heq
  · rfl
  · exact absurd heq hne
  · exact absurd heq.symm hne
  · rfl

theorem card_dom (n : ℕ) :
    (Dom n).card = 2 * ∑ a : Fin 3, ∑ u ∈ SAWC.S (2 * n - SAWC.e a) a, SAWC.marks1 u := by
  rw [Dom, Finset.card_filter, Finset.sum_product, Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_product]
  dsimp only
  obtain ⟨w, rfl, hv, hc⟩ := (mem_S_iff _ _ _).mp hu
  have hcg := cost_ge a w
  calc ∑ i ∈ Finset.range (2 * n + 1), ∑ _d : Bool, (if mk1 (a :: w) i then 1 else 0)
      = ∑ i ∈ Finset.range (2 * n + 1), 2 * (if mk1 (a :: w) i then 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => by rw [Fintype.sum_bool]; ring)
    _ = 2 * SAWC.marks1 (a :: w) := by rw [← Finset.mul_sum, sum_mk1 _ _ _ (by omega)]

/-- closed self-avoiding walks from the middle vertex `o1` -/
noncomputable def a1 (n : ℕ) : ℕ :=
  Set.ncard {w : strip.Walk o1 o1 | w.length = 2 * n ∧ (n = 0 ∨ w.IsCycle)}

theorem a_val (n : ℕ) (hn : 1 ≤ n) :
    (a1 n : ℤ) = 2 * (SAWC.Ms1 (2 * n - 1) 0 + SAWC.Ms1 (2 * n - 1) 1 + SAWC.Ms1 (2 * n - 2) 2) := by
  have hX : {w : strip.Walk o1 o1 | w.length = 2 * n ∧ (n = 0 ∨ w.IsCycle)} = Φ '' ↑(Dom n) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨hl, h0 | hc⟩
      · omega
      · exact Φ_surj hc hl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2⟩ := Φ_spec hx
      exact ⟨h2, Or.inr h1⟩
  unfold a1
  rw [hX, Set.ncard_image_of_injOn (Φ_inj n), Set.ncard_coe_finset, card_dom]
  push_cast
  simp [Fin.sum_univ_three, SAWC.Ms1, SAWC.e]

theorem a_zero : a1 0 = 1 := by
  unfold a1
  have : {w : strip.Walk o1 o1 | w.length = 2 * 0 ∧ (0 = 0 ∨ w.IsCycle)} = {Walk.nil} := by
    ext w
    simp [Walk.length_eq_zero_iff]
  rw [this, Set.ncard_singleton]

/-! The generating function. -/

theorem coeff_X_mul_mk (p : ℕ) (f : ℕ → ℤ) :
    coeff p (X * PowerSeries.mk f) = if 1 ≤ p then f (p - 1) else 0 := by
  rw [← SAWC.coeff_X_pow_mul_mk, pow_one]

theorem coeff_Y (p : ℕ) : coeff p SAWC.Y1 =
    (if 1 ≤ p then SAWC.Ms1 (p - 1) 0 + SAWC.Ms1 (p - 1) 1 else 0) + (if 2 ≤ p then SAWC.Ms1 (p - 2) 2 else 0) := by
  unfold SAWC.Y1
  simp only [map_add, SAWC.PM1, coeff_X_mul_mk, SAWC.coeff_X_pow_mul_mk]
  split_ifs <;> ring

theorem a_Y (m : ℕ) (hm : 1 ≤ m) : (a1 m : ℤ) = 2 * coeff (2 * m) SAWC.Y1 := by
  rw [a_val m hm, coeff_Y, if_pos (by omega), if_pos (by omega)]

theorem Y_rel :
    SAWC.Y1 - 4 • (X ^ 2 * SAWC.Y1) + 6 • (X ^ 4 * SAWC.Y1) - 8 • (X ^ 6 * SAWC.Y1) + 9 • (X ^ 8 * SAWC.Y1)
      - 4 • (X ^ 10 * SAWC.Y1) + 4 • (X ^ 12 * SAWC.Y1) =
    4 • X ^ 4 - 8 • X ^ 6 + 14 • X ^ 8 - 16 • X ^ 10 + 6 • X ^ 12 - 6 • (X ^ 14 : PowerSeries ℤ) := by
  have := SAWC.Y1_gf
  simp only [nsmul_eq_mul]
  push_cast
  linear_combination this

noncomputable def E : PowerSeries ℤ := PowerSeries.mk fun m => coeff (2 * m) SAWC.Y1

theorem ite_even (m k j : ℕ) (hj : j = 2 * k) (f : ℕ → ℤ) :
    (if k ≤ m then f (2 * (m - k)) else 0) = (if j ≤ 2 * m then f (2 * m - j) else 0) := by
  subst hj
  by_cases h : k ≤ m
  · rw [if_pos h, if_pos (by omega), show 2 * (m - k) = 2 * m - 2 * k by omega]
  · rw [if_neg h, if_neg (by omega)]

theorem ite_even' (m i j : ℕ) (hj : j = 2 * i) :
    (if 2 * m = j then (1 : ℤ) else 0) = (if m = i then 1 else 0) := by
  subst hj
  by_cases h : m = i
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem E_rel : E * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
    4 * X ^ 2 - 8 * X ^ 3 + 14 * X ^ 4 - 16 * X ^ 5 + 6 * X ^ 6 - 6 * (X ^ 7 : PowerSeries ℤ) := by
  have eL : E * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      X ^ 0 * E - 4 • (X ^ 1 * E) + 6 • (X ^ 2 * E) - 8 • (X ^ 3 * E) + 9 • (X ^ 4 * E)
        - 4 • (X ^ 5 * E) + 4 • (X ^ 6 * E) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  have eR : (4 * X ^ 2 - 8 * X ^ 3 + 14 * X ^ 4 - 16 * X ^ 5 + 6 * X ^ 6 - 6 * (X ^ 7 : PowerSeries ℤ)) =
      4 • X ^ 2 - 8 • X ^ 3 + 14 • X ^ 4 - 16 • X ^ 5 + 6 • X ^ 6 - 6 • (X ^ 7 : PowerSeries ℤ) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [eL, eR]
  ext m
  have hR := congrArg (coeff (2 * m)) Y_rel
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_X_pow] at hR
  simp only [map_add, map_sub, map_nsmul, E, SAWC.coeff_X_pow_mul_mk, coeff_X_pow]
  rw [ite_even m 0 0 rfl (fun p => coeff p SAWC.Y1), ite_even m 1 2 rfl (fun p => coeff p SAWC.Y1),
    ite_even m 2 4 rfl (fun p => coeff p SAWC.Y1), ite_even m 3 6 rfl (fun p => coeff p SAWC.Y1),
    ite_even m 4 8 rfl (fun p => coeff p SAWC.Y1), ite_even m 5 10 rfl (fun p => coeff p SAWC.Y1),
    ite_even m 6 12 rfl (fun p => coeff p SAWC.Y1)]
  rw [ite_even' m 2 4 rfl, ite_even' m 3 6 rfl, ite_even' m 4 8 rfl, ite_even' m 5 10 rfl,
    ite_even' m 6 12 rfl, ite_even' m 7 14 rfl] at hR
  simp only [Nat.sub_zero, zero_le, if_true] at hR ⊢
  simp only [nsmul_eq_mul] at hR ⊢
  linarith

theorem A_eq : (PowerSeries.mk fun n => (a1 n : ℤ)) = 1 + 2 * E := by
  rw [two_mul]
  ext m
  rw [coeff_mk, map_add, map_add, coeff_one, E, coeff_mk]
  rcases m with _ | m
  · rw [a_zero, coeff_Y]; simp
  · rw [a_Y (m + 1) (by omega), if_neg (by omega)]; ring

theorem main_thm :
    (PowerSeries.mk fun n => (a1 n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 14 * X ^ 2 - 24 * X ^ 3 + 37 * X ^ 4 - 36 * X ^ 5 + 16 * X ^ 6
        - 12 * X ^ 7 := by
  rw [A_eq]
  linear_combination (2 : PowerSeries ℤ) * E_rel

end SAWB

/-! Part T44: transport from the strip `{-1, 0, 1} × ℤ` of the statement to the strip `{0, 1, 2} × ℤ`. -/

namespace SAW44

open SimpleGraph SAWB PowerSeries

abbrev V4 := ↥OMA.S_oeis_a022444.stripSet

def sh (p : V4) : V := ⟨(p.1.1 + 1, p.1.2), by
  have h := p.2
  simp only [OMA.S_oeis_a022444.stripSet, Set.mem_setOf_eq] at h
  simp only [SAWS.stripSet, Set.mem_setOf_eq]; omega⟩

def sh' (v : V) : V4 := ⟨(v.1.1 - 1, v.1.2), by
  have h := v.2
  simp only [SAWS.stripSet, Set.mem_setOf_eq] at h
  simp only [OMA.S_oeis_a022444.stripSet, Set.mem_setOf_eq]; omega⟩

theorem adj4 {p q : V4} :
    OMA.S_oeis_a022444.strip.Adj p q ↔ |p.1.1 - q.1.1| + |p.1.2 - q.1.2| = 1 := by
  simp [OMA.S_oeis_a022444.strip, OMA.S_oeis_a022444.lattice]

def φ : OMA.S_oeis_a022444.strip →g SAWS.strip where
  toFun := sh
  map_rel' := fun {p q} h => by
    rw [adj_iff]; rw [adj4] at h
    simp only [sh]
    rw [show p.1.1 + 1 - (q.1.1 + 1) = p.1.1 - q.1.1 by ring]; exact h

def ψ : SAWS.strip →g OMA.S_oeis_a022444.strip where
  toFun := sh'
  map_rel' := fun {p q} h => by
    rw [adj4]; rw [adj_iff] at h
    simp only [sh']
    rw [show p.1.1 - 1 - (q.1.1 - 1) = p.1.1 - q.1.1 by ring]; exact h

theorem φψ (v : V) : φ (ψ v) = v := by
  apply Subtype.ext; ext <;> simp [φ, ψ, sh, sh']
theorem ψφ (p : V4) : ψ (φ p) = p := by
  apply Subtype.ext; ext <;> simp [φ, ψ, sh, sh']

theorem φ_inj : Function.Injective φ := fun p q h => by rw [← ψφ p, ← ψφ q, h]
theorem ψ_inj : Function.Injective ψ := fun p q h => by rw [← φψ p, ← φψ q, h]

theorem h1 : φ OMA.S_oeis_a022444.origin = o1 := by
  apply Subtype.ext; ext <;> simp [φ, sh, o1, pt, OMA.S_oeis_a022444.origin]
theorem h2 : ψ o1 = OMA.S_oeis_a022444.origin := by rw [← h1, ψφ]

theorem a44_eq (n : ℕ) : OMA.S_oeis_a022444.a n = a1 n := by
  unfold OMA.S_oeis_a022444.a a1
  apply Set.ncard_congr (fun w _ => (w.map φ).copy h1 h1)
  · rintro w ⟨hl, hc⟩
    refine ⟨by simp [hl], ?_⟩
    rcases hc with h | h
    · exact Or.inl h
    · right; rw [Walk.isCycle_copy]; exact (Walk.map_isCycle_iff_of_injective φ_inj).mpr h
  · intro w w' _ _ h
    apply Walk.ext_support
    have := congrArg Walk.support h
    simp only [Walk.support_copy, Walk.support_map] at this
    exact List.map_injective_iff.mpr φ_inj this
  · rintro w ⟨hl, hc⟩
    refine ⟨(w.map ψ).copy h2 h2, ⟨by simp [hl], ?_⟩, ?_⟩
    · rcases hc with h | h
      · exact Or.inl h
      · right; rw [Walk.isCycle_copy]; exact (Walk.map_isCycle_iff_of_injective ψ_inj).mpr h
    · apply Walk.ext_support
      simp only [Walk.support_copy, Walk.support_map, List.map_map]
      conv_rhs => rw [← List.map_id w.support]
      apply List.map_congr_left
      intro v _
      exact φψ v

theorem final :
    (PowerSeries.mk fun n => (OMA.S_oeis_a022444.a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 14 * X ^ 2 - 24 * X ^ 3 + 37 * X ^ 4 - 36 * X ^ 5 + 16 * X ^ 6
        - 12 * X ^ 7 := by
  simp only [a44_eq]
  exact main_thm

end SAW44

theorem OMA.solution : type_of% @OMA.S_oeis_a022444.main := SAW44.final
