import OMAStatements.S_oeis_a268967
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on states (row, pairs used in {0,1}); arrays split row by row (Fin.init/Fin.snoc).
-- Dual vectors u1..u4 (tabulated, decide +kernel) satisfy u4 + 81 u2 = 18 u3; recurrence, closed form, g.f. follow.

namespace OMA.S_oeis_a268967

open PowerSeries

abbrev Row := Fin 4 → Fin 3
abbrev St := Row × Fin 2

def hor (r : Row) : ℕ := ∑ j : Fin 3, if (r j.castSucc : ℕ) + (r j.succ : ℕ) = 2 then 1 else 0
def anti (r s : Row) : ℕ := ∑ j : Fin 3, if (r j.succ : ℕ) + (s j.castSucc : ℕ) = 2 then 1 else 0

def okc (p q : St) : Prop := (q.2 : ℕ) = p.2 + anti p.1 q.1 + hor q.1
instance (p q : St) : Decidable (okc p q) := by unfold okc; infer_instance

def w0 (p : St) : ℕ := if hor p.1 = p.2 then 1 else 0

def w : ℕ → St → ℕ
  | 0, p => w0 p
  | k + 1, q => ∑ p : St, if okc p q then w k p else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, p => ∑ q : St, if okc p q then u j q else 0

def pt (k : ℕ) (x : Fin (k + 1) → Row) : ℕ :=
  ∑ i, hor (x i) + ∑ i : Fin k, anti (x i.castSucc) (x i.succ)

lemma pt_eq (k : ℕ) (x : Fin (k + 1) → Row) : pairsTotallingTwo k x = pt k x := by
  unfold pairsTotallingTwo pt hor anti
  simp only [Finset.card_filter, Fintype.sum_prod_type]

lemma pt_succ (k : ℕ) (x : Fin (k + 2) → Row) : pt (k + 1) x =
    pt k (Fin.init x) + hor (x (Fin.last _)) + anti (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
  have h1 : ∑ i : Fin (k + 2), hor (x i) =
      ∑ i : Fin (k + 1), hor (Fin.init x i) + hor (x (Fin.last _)) := Fin.sum_univ_castSucc _
  have h2 : ∑ i : Fin (k + 1), anti (x i.castSucc) (x i.succ) =
      ∑ i : Fin k, anti (Fin.init x i.castSucc) (Fin.init x i.succ)
        + anti (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
    rw [Fin.sum_univ_castSucc]; simp only [Fin.init, Fin.succ_castSucc, Fin.succ_last]
  unfold pt; rw [h1, h2]; ring

lemma pt_zero (x : Fin 1 → Row) : pt 0 x = hor (x 0) := by simp [pt]

def mn (k : ℕ) (g : Fin (k + 1) → Row) : St := (g (Fin.last k), ⟨min (pt k g) 1, by omega⟩)

def cnt (k : ℕ) (p : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (k + 1) → Row => x (Fin.last k) = p.1 ∧ pt k x = p.2)).card

lemma cnt_zero (p : St) : cnt 0 p = w0 p := by
  unfold cnt w0
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => p.1, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pt_zero]
    constructor
    · rintro ⟨h, -⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2⟩
    apply h; rw [pt_zero] at h2; rw [← h1]; exact h2

set_option maxRecDepth 100000 in
lemma cnt_succ (k : ℕ) (q : St) :
    cnt (k + 1) q = ∑ p : St, if okc p q then cnt k p else 0 := by
  have e : cnt (k + 1) q = (Finset.univ.filter
      (fun g : Fin (k + 1) → Row => pt k g + hor q.1 + anti (g (Fin.last k)) q.1 = q.2)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g q.1)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hl, hg⟩ := hf
      rw [pt_succ, hl] at hg
      simpa [Fin.init] using hg
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      refine ⟨by simp, ?_⟩
      rw [pt_succ]
      simpa [Fin.init] using hg
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.1]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := mn k) (t := (Finset.univ : Finset St)) (fun g _ => Finset.mem_univ (mn k g))]
  apply Finset.sum_congr rfl
  rintro ⟨r, c0⟩ _
  rw [Finset.filter_filter]
  have hq := q.2.isLt
  have hc := c0.isLt
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    unfold okc at h
    simp only [mn, Prod.mk.injEq, Fin.ext_iff] at h ⊢
    constructor
    · rintro ⟨hc, rfl, h2⟩; refine ⟨rfl, ?_⟩; omega
    · rintro ⟨rfl, h2⟩; refine ⟨?_, rfl, ?_⟩ <;> omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _
    unfold okc at h
    simp only [mn, Prod.mk.injEq, Fin.ext_iff] at h ⊢
    rintro ⟨hc, rfl, h2⟩; apply h; omega

lemma cnt_eq (k : ℕ) (p : St) : cnt k p = w k p := by
  induction k generalizing p with
  | zero => rw [cnt_zero]; rfl
  | succ k ih =>
    rw [cnt_succ k p, w]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih r]

set_option maxRecDepth 100000 in
lemma a_w (k : ℕ) : a (k + 1) = ∑ p : St, w k p := by
  simp only [a, pt_eq]
  rw [Finset.card_eq_sum_card_fiberwise (f := mn k) (t := (Finset.univ : Finset St)) (fun g _ => Finset.mem_univ (mn k g))]
  apply Finset.sum_congr rfl
  rintro ⟨r, c0⟩ _
  rw [← cnt_eq, cnt, Finset.filter_filter]
  have hc := c0.isLt
  congr 1; apply Finset.filter_congr
  intro x _
  simp only [mn, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro ⟨h1, rfl, h2⟩; exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, h2⟩; exact ⟨by omega, rfl, by omega⟩

lemma dual (j k : ℕ) : ∑ s : St, w (k + j) s = ∑ r : St, w k r * u j r := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

lemma a_u (j : ℕ) : a (j + 1) = ∑ r : St, w0 r * u j r := by
  have h := dual j 0
  rw [zero_add] at h
  rw [a_w, h]; rfl

def tb (L : List ℕ) (p : St) : ℕ :=
  L.getD (((p.1 0).val * 27 + (p.1 1).val * 9 + (p.1 2).val * 3 + (p.1 3).val) * 2 + p.2.val) 0

def T1 : List ℕ := [25, 10, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 30, 4, 29, 6, 29, 6, 30, 8, 25, 10, 29, 6, 29, 6, 30, 4, 29, 6, 29, 6, 25, 10, 30, 8, 29, 6, 29, 6, 30, 4, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 25, 10, 25, 10, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 30, 4, 29, 6, 29, 6, 30, 8, 25, 10, 29, 6, 29, 6, 30, 4, 29, 6, 29, 6, 25, 10, 30, 8, 29, 6, 29, 6, 30, 4, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 25, 10, 25, 10, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 30, 4, 29, 6, 29, 6, 30, 8, 25, 10, 29, 6, 29, 6, 30, 4, 29, 6, 29, 6, 25, 10, 30, 8, 29, 6, 29, 6, 30, 4, 30, 8, 29, 6, 25, 10, 29, 6, 30, 8, 25, 10]
def T2 : List ℕ := [389, 90, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 326, 36, 357, 54, 357, 54, 394, 72, 389, 90, 345, 54, 357, 54, 326, 36, 357, 54, 345, 54, 389, 90, 394, 72, 357, 54, 357, 54, 326, 36, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 389, 90, 389, 90, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 326, 36, 357, 54, 357, 54, 394, 72, 389, 90, 345, 54, 357, 54, 326, 36, 357, 54, 345, 54, 389, 90, 394, 72, 357, 54, 357, 54, 326, 36, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 389, 90, 389, 90, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 326, 36, 357, 54, 357, 54, 394, 72, 389, 90, 345, 54, 357, 54, 326, 36, 357, 54, 345, 54, 389, 90, 394, 72, 357, 54, 357, 54, 326, 36, 394, 72, 345, 54, 389, 90, 345, 54, 394, 72, 389, 90]
def T3 : List ℕ := [4941, 810, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 3510, 324, 4077, 486, 4077, 486, 4698, 648, 4941, 810, 3969, 486, 4077, 486, 3510, 324, 4077, 486, 3969, 486, 4941, 810, 4698, 648, 4077, 486, 4077, 486, 3510, 324, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 4941, 810, 4941, 810, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 3510, 324, 4077, 486, 4077, 486, 4698, 648, 4941, 810, 3969, 486, 4077, 486, 3510, 324, 4077, 486, 3969, 486, 4941, 810, 4698, 648, 4077, 486, 4077, 486, 3510, 324, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 4941, 810, 4941, 810, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 3510, 324, 4077, 486, 4077, 486, 4698, 648, 4941, 810, 3969, 486, 4077, 486, 3510, 324, 4077, 486, 3969, 486, 4941, 810, 4698, 648, 4077, 486, 4077, 486, 3510, 324, 4698, 648, 3969, 486, 4941, 810, 3969, 486, 4698, 648, 4941, 810]
def T4 : List ℕ := [57429, 7290, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 36774, 2916, 44469, 4374, 44469, 4374, 52650, 5832, 57429, 7290, 43497, 4374, 44469, 4374, 36774, 2916, 44469, 4374, 43497, 4374, 57429, 7290, 52650, 5832, 44469, 4374, 44469, 4374, 36774, 2916, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 57429, 7290, 57429, 7290, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 36774, 2916, 44469, 4374, 44469, 4374, 52650, 5832, 57429, 7290, 43497, 4374, 44469, 4374, 36774, 2916, 44469, 4374, 43497, 4374, 57429, 7290, 52650, 5832, 44469, 4374, 44469, 4374, 36774, 2916, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 57429, 7290, 57429, 7290, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 36774, 2916, 44469, 4374, 44469, 4374, 52650, 5832, 57429, 7290, 43497, 4374, 44469, 4374, 36774, 2916, 44469, 4374, 43497, 4374, 57429, 7290, 52650, 5832, 44469, 4374, 44469, 4374, 36774, 2916, 52650, 5832, 43497, 4374, 57429, 7290, 43497, 4374, 52650, 5832, 57429, 7290]


set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y : St, if okc x y then tb T1 y else 0) = tb T2 x := by decide +kernel

lemma hu2 (x : St) : u 2 x = tb T2 x := by
  show (∑ y : St, if okc x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y : St, if okc x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu3 (x : St) : u 3 x = tb T3 x := by
  show (∑ y : St, if okc x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hu4' : ∀ x, (∑ y : St, if okc x y then tb T3 y else 0) = tb T4 x := by decide +kernel

lemma hu4 (x : St) : u 4 x = tb T4 x := by
  show (∑ y : St, if okc x y then u 3 y else 0) = _
  simp only [hu3]; exact hu4' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x : St, tb T4 x + 81 * tb T2 x = 18 * tb T3 x := by decide +kernel

lemma keyW (k : ℕ) :
    (∑ s : St, w (k + 4) s) + 81 * (∑ s : St, w (k + 2) s) = 18 * (∑ s : St, w (k + 3) s) := by
  rw [dual 4 k, dual 2 k, dual 3 k]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  have := hT x
  rw [hu2, hu3, hu4]
  calc w k x * tb T4 x + 81 * (w k x * tb T2 x) = w k x * (tb T4 x + 81 * tb T2 x) := by ring
    _ = w k x * (18 * tb T3 x) := by rw [this]
    _ = 18 * (w k x * tb T3 x) := by ring

lemma arec (k : ℕ) : (a (k + 5) : ℚ) = 18 * a (k + 4) - 81 * a (k + 3) := by
  have key := keyW k
  rw [← a_w (k + 4), ← a_w (k + 2), ← a_w (k + 3)] at key
  have key' : ((a (k + 4 + 1) + 81 * a (k + 2 + 1) : ℕ) : ℚ) = ((18 * a (k + 3 + 1) : ℕ) : ℚ) := by
    rw [key]
  push_cast at key'
  linarith

lemma v0 : a 0 = 0 := rfl
set_option maxRecDepth 100000 in
lemma v1 : a 1 = 60 := by rw [a_u 0]; decide +kernel
set_option maxRecDepth 100000 in
lemma v2 : a 2 = 912 := by rw [a_u 1]; simp only [hu1]; decide +kernel
set_option maxRecDepth 100000 in
lemma v3 : a 3 = 11664 := by rw [a_u 2]; simp only [hu2]; decide +kernel
set_option maxRecDepth 100000 in
lemma v4 : a 4 = 136080 := by rw [a_u 3]; simp only [hu3]; decide +kernel

lemma arec' (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = 18 * a (n - 1) - 81 * a (n - 2) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with h | h
  · subst h; simp only [show 4 - 1 = 3 by rfl, show 4 - 2 = 2 by rfl, v2, v3, v4]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
    exact arec m

def g (n : ℕ) : ℚ := 16 * 9 ^ n * (8 * n + 3) / 27

lemma closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = g n := by
  have key : ∀ m : ℕ, (a (m + 2) : ℚ) = g (m + 2) ∧ (a (m + 3) : ℚ) = g (m + 3) := by
    intro m
    induction m with
    | zero => simp only [zero_add, g, v2, v3]; norm_num
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have := arec' (m + 4) (by omega)
      rw [show m + 1 + 3 = m + 4 by ring, this, show m + 4 - 1 = m + 3 by omega,
        show m + 4 - 2 = m + 2 by omega, h0, h1]
      simp only [g]; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (key m).1

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    (∀ n : ℕ, 4 ≤ n →
      (a n : ℤ) = 18 * a (n - 1) - 81 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 9 * X) ^ 2 =
      12 * X * (1 - X) * (5 - 9 * X)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 16 * 3 ^ (2 * n - 3) * (8 * n + 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have h := arec' n hn
    exact_mod_cast h
  · rw [show ((1 - 9 * X) ^ 2 : PowerSeries ℚ) =
        1 - PowerSeries.C (18:ℚ) * X + PowerSeries.C (81:ℚ) * X ^ 2 by
          simp only [map_ofNat]; ring,
      show (12 * X * (1 - X) * (5 - 9 * X) : PowerSeries ℚ) =
        PowerSeries.C (60:ℚ) * X - PowerSeries.C (168:ℚ) * X ^ 2 + PowerSeries.C (108:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v0, v1, v2, v3] <;> norm_num
    · have hq := arec' n h
      simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega]
      rw [hq]; ring
  · intro n hn
    rw [closed n hn, g]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show 2 * (m + 2) - 3 = 2 * m + 1 by omega,
      show (3:ℚ) ^ (2 * m + 1) = 9 ^ m * 3 by rw [pow_succ, pow_mul]; norm_num,
      show (9:ℚ) ^ (m + 2) = 9 ^ m * 81 by rw [pow_add]; norm_num]
    push_cast; ring

end OMA.S_oeis_a268967

theorem OMA.solution : type_of% @OMA.S_oeis_a268967.main := OMA.S_oeis_a268967.main_proof
