import OMAStatements.S_oeis_a224000

-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Sketch: the columns of the array form a sequence of states with a condition on single states (B) and
-- on adjacent pairs (T). w k y counts valid sequences ending in y (bijection via Fin.init / Fin.snoc,
-- adapted from the merged proof of oeis-a223443 by @sntntHb); the dual vectors u j are tabulated and
-- checked by decide +kernel, together with the coordinatewise relation that gives the recurrence;
-- the g.f. follows coefficientwise from the recurrence and the first values.

namespace OMA.P_oeis_a224000

open Finset

section Gen
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T]

def Gd (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i, B (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd B T n) := fun f => by unfold Gd; infer_instance

def w : ℕ → σ → ℕ
  | 0, y => if B y then 1 else 0
  | k + 1, y => ∑ x, if B y ∧ T x y then w k x else 0

def u : ℕ → σ → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if B y ∧ T x y then u j y else 0

def cnt (k : ℕ) (y : σ) : ℕ :=
  ((univ : Finset (Fin (k + 1) → σ)).filter (fun f => Gd B T (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → σ) :
    Gd B T (k + 2) f ↔ Gd B T (k + 1) (Fin.init f) ∧ B (f (Fin.last (k + 1))) ∧
      T (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨fun i => h0 _, fun i j hij => h _ _ (by simp [hij])⟩, h0 _, h _ _ (by simp)⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · by_cases hi : i.val < k + 1
      · have := h0 ⟨i.val, hi⟩
        simpa [Fin.init] using this
      · have hi' : i = Fin.last (k + 1) := Fin.ext (by simp; omega)
        subst hi'; exact h2
    · by_cases hj : j.val < k + 1
      · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
        simpa [Fin.init] using this
      · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
        have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
        subst hj' hi'; exact h3

lemma cnt_zero (y : σ) : cnt B T 0 y = if B y then 1 else 0 := by
  unfold cnt
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => y, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨⟨fun _ => hy, fun i j hij => by omega⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)

lemma cnt_succ (k : ℕ) (y : σ) :
    cnt B T (k + 1) y = ∑ x, if B y ∧ T x y then cnt B T k x else 0 := by
  by_cases hy : B y
  · have e : cnt B T (k + 1) y = ((univ : Finset (Fin (k + 1) → σ)).filter
        (fun g => Gd B T (k + 1) g ∧ T (g (Fin.last k)) y)).card := by
      unfold cnt
      apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
        obtain ⟨hg, hl⟩ := hf
        rw [gd_succ] at hg
        refine ⟨hg.1, ?_⟩
        have := hg.2.2; rw [hl] at this; simpa [Fin.init] using this
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        refine ⟨?_, by simp⟩
        rw [gd_succ]
        refine ⟨by simpa using hg.1, by simpa using hy, ?_⟩
        simpa using hg.2
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
        rw [← hf.2]; exact Fin.snoc_init_self f
      · intro g _; exact Fin.init_snoc _ _
    rw [e, Finset.card_eq_sum_card_fiberwise
      (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
      (t := univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.filter_filter]
    split_ifs with h
    · unfold cnt; congr 1; apply Finset.filter_congr
      intro g _
      constructor
      · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hg, hx⟩
      · rintro ⟨hg, hx⟩; exact ⟨⟨hg, hx ▸ h.2⟩, hx⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨⟨-, ha⟩, hx⟩; exact h ⟨hy, hx ▸ ha⟩
  · have : cnt B T (k + 1) y = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)
    rw [this]; symm
    apply Finset.sum_eq_zero; intro x _
    rw [if_neg (fun h => hy h.1)]

lemma cnt_eq (k : ℕ) (y : σ) : cnt B T k y = w B T k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma total (k : ℕ) :
    ((univ : Finset (Fin (k + 1) → σ)).filter (Gd B T (k + 1))).card = ∑ y, w B T k y := by
  simp only [← cnt_eq]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]

lemma w_zero_of (k : ℕ) (x : σ) (hx : ¬ B x) : w B T k x = 0 := by
  cases k with
  | zero => simp [w, hx]
  | succ k =>
    simp only [w]
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun h => hx h.1)]

lemma dual (j k : ℕ) : ∑ y, w B T (k + j) y = ∑ x, w B T k x * u B T j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

/-- The count of valid sequences of length k + 1 + j through the dual vectors. -/
lemma total_dual (k j : ℕ) :
    ((univ : Finset (Fin (k + j + 1) → σ)).filter (Gd B T (k + j + 1))).card =
      ∑ x, w B T k x * u B T j x := by
  rw [total, dual]

end Gen

end OMA.P_oeis_a224000

namespace OMA.P_oeis_a224000

open Finset OMA.S_oeis_a224000

abbrev St := Fin 2 → Fin 3

def B (_ : St) : Prop := True

def T (s t : St) : Prop :=
  (∀ i : Fin 2, s i ≤ t i) ∧ ∀ i i' : Fin 2, i'.val = i.val + 1 → s i ≤ t i'

instance : DecidablePred B := fun s => by unfold B; infer_instance
instance : DecidableRel T := fun s t => by unfold T; infer_instance

lemma good_iff {n : ℕ} (x : Fin 2 → Fin n → Fin 3) :
    good x ↔ Gd B T n (fun j i => x i j) := by
  unfold good AntidiagsUnimodal RowsNondecreasing DiagsNondecreasing Gd B T
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun _ => trivial, fun j j' hj => ⟨fun i => h1 i j j' hj, fun i i' hi => h2 i i' j j' hi hj⟩⟩
  · rintro ⟨-, h⟩
    refine ⟨fun i₁ i₂ i₃ _ _ h12 h23 _ => by omega, fun i j j' hj => (h j j' hj).1 i,
      fun i i' j j' hi hj => (h j j' hj).2 i i' hi⟩

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → St)).filter (Gd B T n)).card := by
  unfold a
  apply Finset.card_nbij' (fun x => fun j i => x i j) (fun f => fun i j => f j i)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact (good_iff x).1 hx
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact (good_iff _).2 hf
  · intro x _; rfl
  · intro f _; rfl

lemma aw (k j : ℕ) : a (k + j + 1) = ∑ x, w B T k x * u B T j x := by
  rw [a_eq]; exact total_dual B T k j

def idx (s : St) : ℕ := (s 0).val + 3 * (s 1).val

def tb (L : List ℕ) (s : St) : ℕ := L.getD (idx s) 0

def T1 : List ℕ := [9, 4, 1, 6, 4, 1, 3, 2, 1]
def T2 : List ℕ := [31, 8, 1, 17, 8, 1, 6, 3, 1]
def T3 : List ℕ := [76, 13, 1, 36, 13, 1, 10, 4, 1]
def T4 : List ℕ := [155, 19, 1, 65, 19, 1, 15, 5, 1]
def T5 : List ℕ := [281, 26, 1, 106, 26, 1, 21, 6, 1]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u B T 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hs2 : ∀ x, (∑ y, if B y ∧ T x y then tb T1 y else 0) = tb T2 x := by decide +kernel
set_option maxRecDepth 100000 in
lemma hs3 : ∀ x, (∑ y, if B y ∧ T x y then tb T2 y else 0) = tb T3 x := by decide +kernel
set_option maxRecDepth 100000 in
lemma hs4 : ∀ x, (∑ y, if B y ∧ T x y then tb T3 y else 0) = tb T4 x := by decide +kernel
set_option maxRecDepth 100000 in
lemma hs5 : ∀ x, (∑ y, if B y ∧ T x y then tb T4 y else 0) = tb T5 x := by decide +kernel

lemma hu2 (x : St) : u B T 2 x = tb T2 x := by
  show (∑ y, if B y ∧ T x y then u B T 1 y else 0) = _
  simp only [hu1]; exact hs2 x
lemma hu3 (x : St) : u B T 3 x = tb T3 x := by
  show (∑ y, if B y ∧ T x y then u B T 2 y else 0) = _
  simp only [hu2]; exact hs3 x
lemma hu4 (x : St) : u B T 4 x = tb T4 x := by
  show (∑ y, if B y ∧ T x y then u B T 3 y else 0) = _
  simp only [hu3]; exact hs4 x
lemma hu5 (x : St) : u B T 5 x = tb T5 x := by
  show (∑ y, if B y ∧ T x y then u B T 4 y else 0) = _
  simp only [hu4]; exact hs5 x

set_option maxRecDepth 100000 in
lemma hrel : ∀ x, B x → tb T5 x + 10 * tb T3 x + 5 * tb T1 x = 5 * tb T4 x + 10 * tb T2 x + 1 := by
  decide +kernel

lemma arec (k : ℕ) : (a (k + 6) : ℤ) = 5 * a (k + 5) - 10 * a (k + 4) + 10 * a (k + 3)
    - 5 * a (k + 2) + a (k + 1) := by
  have e5 := aw k 5; have e4 := aw k 4; have e3 := aw k 3; have e2 := aw k 2
  have e1 := aw k 1; have e0 := aw k 0
  have key : ∑ x, w B T k x * u B T 5 x + 10 * ∑ x, w B T k x * u B T 3 x
      + 5 * ∑ x, w B T k x * u B T 1 x = 5 * ∑ x, w B T k x * u B T 4 x
      + 10 * ∑ x, w B T k x * u B T 2 x + ∑ x, w B T k x * u B T 0 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : B x
    · have h := hrel x hx
      rw [hu1, hu2, hu3, hu4, hu5]
      simp only [u]
      calc w B T k x * tb T5 x + 10 * (w B T k x * tb T3 x) + 5 * (w B T k x * tb T1 x)
          = w B T k x * (tb T5 x + 10 * tb T3 x + 5 * tb T1 x) := by ring
        _ = w B T k x * (5 * tb T4 x + 10 * tb T2 x + 1) := by rw [h]
        _ = _ := by ring
    · simp [w_zero_of B T k x hx]
  rw [show k + 6 = k + 5 + 1 by rfl, show k + 4 = k + 3 + 1 by rfl, show k + 2 = k + 1 + 1 by rfl,
    show k + 5 = k + 4 + 1 by rfl, show k + 3 = k + 2 + 1 by rfl, show k + 1 = k + 0 + 1 by rfl,
    e5, e4, e3, e2, e1, e0]
  have := congrArg (fun t : ℕ => (t : ℤ)) key
  push_cast at this ⊢
  linarith

lemma val (j : ℕ) : a (j + 1) = ∑ x, (if B x then 1 else 0) * u B T j x := by
  rw [show j + 1 = 0 + j + 1 by ring, aw]; rfl

set_option maxRecDepth 100000 in
lemma v1 : a 1 = 9 := by rw [val 0]; simp only [u]; decide +kernel
set_option maxRecDepth 100000 in
lemma v2 : a 2 = 31 := by rw [val 1]; simp only [hu1]; decide +kernel
set_option maxRecDepth 100000 in
lemma v3 : a 3 = 76 := by rw [val 2]; simp only [hu2]; decide +kernel
set_option maxRecDepth 100000 in
lemma v4 : a 4 = 155 := by rw [val 3]; simp only [hu3]; decide +kernel
set_option maxRecDepth 100000 in
lemma v5 : a 5 = 281 := by rw [val 4]; simp only [hu4]; decide +kernel

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n - 1) else 0 := by
  rw [← ps, pow_one]

end OMA.P_oeis_a224000

open PowerSeries Finset in
open OMA.S_oeis_a224000 OMA.P_oeis_a224000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224000.main := by
  refine ⟨?_, ?_⟩
  · rw [show ((1 - X) ^ 5 : PowerSeries ℚ) =
        1 - PowerSeries.C (5:ℚ) * X + PowerSeries.C (10:ℚ) * X ^ 2 - PowerSeries.C (10:ℚ) * X ^ 3
          + PowerSeries.C (5:ℚ) * X ^ 4 - X ^ 5 by
          simp only [map_ofNat]; ring,
      show (X * (9 - 14 * X + 11 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : PowerSeries ℚ) =
        PowerSeries.C (9:ℚ) * X - PowerSeries.C (14:ℚ) * X ^ 2 + PowerSeries.C (11:ℚ) * X ^ 3
          - PowerSeries.C (5:ℚ) * X ^ 4 + X ^ 5 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have hq : (a (m + 6) : ℚ) = 5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3)
          - 5 * a (m + 2) + a (m + 1) := by
        exact_mod_cast arec m
      simp [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
        show m + 6 - 5 = m + 1 by omega,
        show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega,
        show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega]
      rw [hq]; ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega]
    exact arec k
