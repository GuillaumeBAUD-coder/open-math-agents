import OMAStatements.S_oeis_a235887
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on the 64 rows (Fin 3 -> Fin 4); arrays counted row by row (Fin.init/Fin.snoc).
-- Dual vectors u satisfy u3 + 14 u1 = 7 u2 + 8 u0 (tabulated, decide +kernel), so a(k+3) = 7a(k+2) - 14a(k+1) + 8a(k);
-- closed form by induction from a0..a2 = 64, 112, 232; g.f. by coefficient comparison.

namespace OMA.S_oeis_a235887

open PowerSeries

abbrev St := Fin 3 → Fin 4

def ok (r s : St) : Prop :=
  medEq (r 0).val (r 1).val (s 0).val (s 1).val = true ∧
    medEq (r 1).val (r 2).val (s 1).val (s 2).val = true

instance (r s : St) : Decidable (ok r s) := by unfold ok; infer_instance

def w : ℕ → St → ℕ
  | 0, _ => 1
  | k + 1, s => ∑ r : St, if ok r s then w k r else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, r => ∑ s : St, if ok r s then u j s else 0

def Gd (k : ℕ) (x : Fin (k + 1) → St) : Prop := ∀ i : Fin k, ok (x i.castSucc) (x i.succ)

instance (k : ℕ) : DecidablePred (Gd k) := fun x => by unfold Gd; infer_instance

lemma hp_iff (k : ℕ) (x : Fin (k + 1) → St) :
    (∀ i i' : Fin (k + 1), i'.val = i.val + 1 → ∀ j j' : Fin 3, j'.val = j.val + 1 →
      medEq (x i j).val (x i j').val (x i' j).val (x i' j').val = true) ↔ Gd k x := by
  unfold Gd ok
  constructor
  · intro h i
    exact ⟨h _ _ (by simp) 0 1 rfl, h _ _ (by simp) 1 2 rfl⟩
  · intro h i i' hij j j' hjj
    have hi : i.val < k := by omega
    have e1 : (⟨i.val, hi⟩ : Fin k).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, hi⟩ : Fin k).succ = i' := Fin.ext (by simp [hij])
    obtain ⟨h1, h2⟩ := h ⟨i.val, hi⟩
    rw [e1, e2] at h1 h2
    fin_cases j <;> fin_cases j' <;> simp at hjj <;> assumption

lemma gd_succ (k : ℕ) (x : Fin (k + 2) → St) :
    Gd (k + 1) x ↔ Gd k (Fin.init x) ∧ ok (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
  unfold Gd
  rw [Fin.forall_fin_succ']
  simp only [Fin.init, Fin.succ_castSucc, Fin.succ_last]

def cnt (k : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (k + 1) → St => x (Fin.last k) = s ∧ Gd k x)).card

lemma cnt_zero (s : St) : cnt 0 s = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
  · rintro rfl; exact ⟨rfl, fun i => i.elim0⟩

lemma cnt_succ (k : ℕ) (s : St) :
    cnt (k + 1) s = ∑ r : St, if ok r s then cnt k r else 0 := by
  have e : cnt (k + 1) s = (Finset.univ.filter
      (fun g : Fin (k + 1) → St => Gd k g ∧ ok (g (Fin.last k)) s)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g s)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hl, hg⟩ := hf
      rw [gd_succ] at hg
      refine ⟨hg.1, ?_⟩
      have := hg.2; rw [hl] at this; simpa [Fin.init] using this
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      obtain ⟨hg, ha⟩ := hg
      refine ⟨by simp, ?_⟩
      rw [gd_succ]
      refine ⟨by simpa using hg, ?_⟩
      simpa using ha
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.1]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hx, hg⟩
    · rintro ⟨hx, hg⟩; exact ⟨⟨hg, hx ▸ h⟩, hx⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨⟨-, ha⟩, hx⟩; exact h (hx ▸ ha)

lemma cnt_eq (k : ℕ) (s : St) : cnt k s = w k s := by
  induction k generalizing s with
  | zero => rw [cnt_zero]; rfl
  | succ k ih =>
    rw [cnt_succ k s, w]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih r]

lemma a_w (k : ℕ) : a k = ∑ s : St, w k s := by
  unfold a
  rw [Finset.filter_congr (fun x _ => hp_iff k x)]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← cnt_eq, cnt, Finset.filter_filter]
  congr 1; apply Finset.filter_congr
  intro x _; exact and_comm

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

def tb (L : List ℕ) (x : St) : ℕ := L.getD ((x 0).val * 16 + (x 1).val * 4 + (x 2).val) 0

def T1 : List ℕ := [4, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def T2 : List ℕ := [16, 4, 4, 4, 4, 4, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4, 4, 4, 1, 1, 4, 16, 4, 4, 1, 4, 4, 1, 1, 4, 1, 4, 4, 1, 4, 1, 1, 4, 4, 1, 4, 4, 16, 4, 1, 1, 4, 4, 4, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4, 4, 4, 4, 4, 16]
def T3 : List ℕ := [64, 8, 8, 8, 8, 8, 1, 1, 8, 1, 8, 1, 8, 1, 1, 8, 8, 8, 1, 1, 8, 64, 8, 8, 1, 8, 8, 1, 1, 8, 1, 8, 8, 1, 8, 1, 1, 8, 8, 1, 8, 8, 64, 8, 1, 1, 8, 8, 8, 1, 1, 8, 1, 8, 1, 8, 1, 1, 8, 8, 8, 8, 8, 64]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y : St, if ok x y then tb T1 y else 0) = tb T2 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y : St, if ok x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu2 (x : St) : u 2 x = tb T2 x := by
  show (∑ y : St, if ok x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

lemma hu3 (x : St) : u 3 x = tb T3 x := by
  show (∑ y : St, if ok x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x : St, tb T3 x + 14 * tb T1 x = 7 * tb T2 x + 8 := by decide +kernel

lemma a_u (j : ℕ) : a j = ∑ r : St, u j r := by
  rw [a_w, show j = 0 + j by ring, dual j 0]
  simp [w]

lemma arec (k : ℕ) : (a (k + 3) : ℤ) = 7 * a (k + 2) - 14 * a (k + 1) + 8 * a k := by
  have key : a (k + 3) + 14 * a (k + 1) = 7 * a (k + 2) + 8 * a k := by
    rw [a_w, a_w, a_w, a_w, dual 3 k, dual 2 k, dual 1 k]
    rw [show (∑ s : St, w k s) = ∑ r : St, w k r * u 0 r by simp [u]]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    have := hT x
    rw [hu1, hu2, hu3]
    rw [show u 0 x = 1 from rfl]
    calc w k x * tb T3 x + 14 * (w k x * tb T1 x)
        = w k x * (tb T3 x + 14 * tb T1 x) := by ring
      _ = w k x * (7 * tb T2 x + 8) := by rw [this]
      _ = 7 * (w k x * tb T2 x) + 8 * (w k x * 1) := by ring
  zify at key
  linarith

set_option maxRecDepth 100000 in
lemma v0 : a 0 = 64 := by rw [a_u]; decide +kernel
set_option maxRecDepth 100000 in
lemma v1 : a 1 = 112 := by rw [a_u]; simp only [hu1]; decide +kernel
set_option maxRecDepth 100000 in
lemma v2 : a 2 = 232 := by rw [a_u]; simp only [hu2]; decide +kernel

lemma closed (n : ℕ) : (a n : ℤ) = 4 * (6 + 9 * 2 ^ n + 4 ^ n) := by
  have key : ∀ m : ℕ, (a m : ℤ) = 4 * (6 + 9 * 2 ^ m + 4 ^ m) ∧
      (a (m + 1) : ℤ) = 4 * (6 + 9 * 2 ^ (m + 1) + 4 ^ (m + 1)) ∧
      (a (m + 2) : ℤ) = 4 * (6 + 9 * 2 ^ (m + 2) + 4 ^ (m + 2)) := by
    intro m
    induction m with
    | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [v0, v1, v2]
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      rw [show m + 1 + 2 = m + 3 by ring, arec m, h0, h1, h2]
      ring
  exact (key n).1

lemma v3 : a 3 = 568 := by
  have h := closed 3
  rw [show (4 * (6 + 9 * 2 ^ 3 + 4 ^ 3) : ℤ) = 568 by norm_num] at h
  exact_mod_cast h

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
        8 * X * (14 - 69 * X + 64 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (6 + 9 * 2 ^ n + 4 ^ n) := by
  refine ⟨?_, ?_⟩
  · rw [show ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) =
        1 - PowerSeries.C (7:ℚ) * X + PowerSeries.C (14:ℚ) * X ^ 2
          - PowerSeries.C (8:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring,
      show (8 * X * (14 - 69 * X + 64 * X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (112:ℚ) * X - PowerSeries.C (552:ℚ) * X ^ 2
          + PowerSeries.C (512:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v1, v2, v3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hq : (a (m + 4) : ℚ) = 7 * a (m + 3) - 14 * a (m + 2) + 8 * a (m + 1) := by
        exact_mod_cast arec (m + 1)
      simp [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        show m + 4 - 3 = m + 1 by omega,
        show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega]
      rw [hq]; ring
  · intro n _
    exact_mod_cast closed n

end OMA.S_oeis_a235887

theorem OMA.solution : type_of% @OMA.S_oeis_a235887.main := OMA.S_oeis_a235887.main_proof
