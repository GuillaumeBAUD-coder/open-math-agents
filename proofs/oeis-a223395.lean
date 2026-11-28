import OMAStatements.S_oeis_a223395
import Mathlib

open OMA.S_oeis_a223395

namespace P223395

open Finset

instance : DecidableRel Adj := fun u v => by unfold Adj; infer_instance

def cls (v : Fin 16) : Fin 3 := ![0, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2, 1, 0, 1, 1, 0] v

def Mt : Fin 3 → Fin 3 → ℕ := ![![0, 2, 0], ![1, 1, 1], ![0, 2, 2]]

def f : ℕ → Fin 3 → ℕ
  | 0, _ => 1
  | m + 1, k => ∑ j, Mt k j * f m j

lemma nb (g : Fin 3 → ℕ) (v : Fin 16) :
    ∑ w : Fin 16, (if Adj v w then g (cls w) else 0) = ∑ k : Fin 3, Mt (cls v) k * g k := by
  fin_cases v <;> simp [Fin.sum_univ_succ, Adj, cls, Mt] <;> ring

def Q (n : ℕ) (y : Fin n → Fin 16) : Prop := ∀ i : Fin n, ∀ h : i.val + 1 < n, Adj (y i) (y ⟨i.val + 1, h⟩)

instance (n : ℕ) : DecidablePred (Q n) := fun y => by unfold Q; infer_instance

lemma Q_one (y : Fin 1 → Fin 16) : Q 1 y := by
  intro i h; exact absurd h (by omega)

lemma Q_cons (n : ℕ) (v : Fin 16) (z : Fin (n + 1) → Fin 16) :
    Q (n + 2) (Fin.cons v z : Fin (n + 2) → Fin 16) ↔ Adj v (z 0) ∧ Q (n + 1) z := by
  have key : ∀ (j : ℕ) (h : j + 1 < n + 2),
      (Fin.cons v z : Fin (n + 2) → Fin 16) ⟨j + 1, h⟩ = z ⟨j, by omega⟩ := by
    intro j h
    rw [show (⟨j + 1, h⟩ : Fin (n + 2)) = Fin.succ ⟨j, by omega⟩ from rfl, Fin.cons_succ]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp)
      simpa using this
    · intro i hi
      have := h i.succ (by simp; omega)
      simpa [Fin.cons_succ, key] using this
  · rintro ⟨h0, h1⟩ i hi
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro _; simpa using h0
    · intro hj
      have := h1 j (by simp at hj; omega)
      simpa [Fin.cons_succ, key] using this

lemma sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 16) → ℕ) :
    ∑ y, F y = ∑ v : Fin 16, ∑ z : Fin n → Fin 16, F (Fin.cons v z) := by
  rw [← (Fin.consEquiv (fun _ => Fin 16)).sum_comp, Fintype.sum_prod_type]
  rfl

def K (n : ℕ) (v : Fin 16) : ℕ := ∑ z : Fin n → Fin 16, if Q (n + 1) (Fin.cons v z) then 1 else 0

lemma K0 (v : Fin 16) : K 0 v = 1 := by
  unfold K
  simp [Q_one]

lemma K_succ (n : ℕ) (v : Fin 16) : K (n + 1) v = ∑ w, if Adj v w then K n w else 0 := by
  rw [K, sum_cons]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : Adj v w
  · rw [if_pos hw, K]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Q_cons, Fin.cons_zero, hw, true_and]
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [Q_cons, Fin.cons_zero, hw]

lemma Kf (n : ℕ) : ∀ v, K n v = f n (cls v) := by
  induction n with
  | zero => intro v; rw [K0]; rfl
  | succ n ih =>
    intro v
    rw [K_succ]
    simp only [ih]
    rw [nb]
    rfl

def t (m : ℕ) : ℕ := 4 * f m 0 + 8 * f m 1 + 4 * f m 2

lemma sum_cls (g : Fin 3 → ℕ) : ∑ v : Fin 16, g (cls v) = 4 * g 0 + 8 * g 1 + 4 * g 2 := by
  simp [Fin.sum_univ_succ, cls]; ring

lemma a_t (m : ℕ) : a (m + 1) = t m := by
  unfold a
  have e : {x : Fin (m + 1) → Fin 1 → Fin 16 //
      ∀ i : Fin (m + 1), ∀ h : (i : ℕ) + 1 < m + 1, Adj (x i 0) (x ⟨(i : ℕ) + 1, h⟩ 0)} ≃
      {y : Fin (m + 1) → Fin 16 // Q (m + 1) y} :=
    Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) (Fin 16)))
      (fun x => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, sum_cons]
  have : ∀ v : Fin 16, (∑ z : Fin m → Fin 16, if Q (m + 1) (Fin.cons v z) then 1 else 0) = f m (cls v) := by
    intro v; rw [← Kf]; rfl
  simp only [this]
  rw [sum_cls]; rfl

lemma fs (m : ℕ) : f (m + 1) 0 = 2 * f m 1 ∧ f (m + 1) 1 = f m 0 + f m 1 + f m 2 ∧
    f (m + 1) 2 = 2 * f m 1 + 2 * f m 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [f, Fin.sum_univ_succ, Mt] <;> ring

lemma trec (m : ℕ) : (t (m + 3) : ℤ) = 3 * t (m + 2) + 2 * t (m + 1) - 4 * t m := by
  obtain ⟨a1, b1, c1⟩ := fs m
  obtain ⟨a2, b2, c2⟩ := fs (m + 1)
  obtain ⟨a3, b3, c3⟩ := fs (m + 2)
  unfold t
  rw [a3, b3, c3, a2, b2, c2, a1, b1, c1]
  push_cast
  ring

lemma t012 : t 0 = 16 ∧ t 1 = 48 ∧ t 2 = 152 := by
  obtain ⟨a1, b1, c1⟩ := fs 0
  obtain ⟨a2, b2, c2⟩ := fs 1
  have h0 : ∀ k, f 0 k = 1 := fun _ => rfl
  unfold t
  rw [a2, b2, c2, a1, b1, c1, h0, h0, h0]
  norm_num

noncomputable def r (n : ℕ) : ℝ :=
  (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n + (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5

lemma hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma rrec (n : ℕ) : r (n + 3) = 3 * r (n + 2) + 2 * r (n + 1) - 4 * r n := by
  unfold r
  linear_combination ((-(11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n * Real.sqrt 5 +
    (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5) * Real.sqrt 5) / 5) * hs

lemma r123 : r 1 = 16 ∧ r 2 = 48 ∧ r 3 = 152 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold r
  · linear_combination 2 * hs
  · linear_combination (42 / 5 : ℝ) * hs
  · linear_combination (146 / 5 + 2 * Real.sqrt 5 ^ 2 : ℝ) * hs

lemma tr (m : ℕ) : (t m : ℝ) = r (m + 1) ∧ (t (m + 1) : ℝ) = r (m + 2) ∧ (t (m + 2) : ℝ) = r (m + 3) := by
  induction m with
  | zero =>
    obtain ⟨h0, h1, h2⟩ := t012
    obtain ⟨r1, r2, r3⟩ := r123
    rw [h0, h1, h2, r1, r2, r3]; norm_num
  | succ m ih =>
    obtain ⟨i0, i1, i2⟩ := ih
    refine ⟨i1, i2, ?_⟩
    have h := trec m
    have h' : (t (m + 3) : ℝ) = 3 * t (m + 2) + 2 * t (m + 1) - 4 * t m := by exact_mod_cast h
    rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, h', i0, i1, i2, rrec (m + 1)]

end P223395

open P223395 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a223395.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 2 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 = m + 3 + 1 by omega, a_t, a_t, a_t, a_t]
    exact trec m
  · have hD : PowerSeries.constantCoeff ((1 - X) * (1 - 2 * X - 4 * X ^ 2) : PowerSeries ℚ) ≠ 0 := by simp
    unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
    have hq : ∀ F : PowerSeries ℚ, F * ((1 - X) * (1 - 2 * X - 4 * X ^ 2)) =
        F - C (3 : ℚ) * (F * X ^ 1) - C (2 : ℚ) * (F * X ^ 2) + C (4 : ℚ) * (F * X ^ 3) := by
      intro F; simp only [map_ofNat]; ring
    have hr : (8 * X * (2 - 3 * X ^ 2) : PowerSeries ℚ) = C (16 : ℚ) * X ^ 1 - C (24 : ℚ) * X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [hq, hr]
    obtain ⟨h0, h1, h2⟩ := t012
    have a1 : (a 1 : ℚ) = 16 := by rw [a_t 0, h0]; norm_num
    have a2 : (a 2 : ℚ) = 48 := by rw [a_t 1, h1]; norm_num
    have a3 : (a 3 : ℚ) = 152 := by rw [a_t 2, h2]; norm_num
    ext n
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk]
    by_cases hn : n < 4
    · interval_cases n <;> simp [a1, a2, a3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hrec := trec m
      rw [← a_t, ← a_t, ← a_t, ← a_t] at hrec
      have hq' : (a (m + 3 + 1) : ℚ) = 3 * a (m + 2 + 1) + 2 * a (m + 1 + 1) - 4 * a (m + 1) := by
        exact_mod_cast hrec
      simp only [show m + 4 - 1 = m + 2 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega,
        show m + 4 - 3 = m + 1 by omega, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega,
        show 3 ≤ m + 4 by omega,
        show m + 4 ≠ 0 by omega, show m + 2 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 0 by omega,
        show m + 1 ≠ 0 by omega, if_true, if_false, coeff_C]
      rw [show m + 4 = m + 3 + 1 by omega, hq']
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [a_t, (tr m).1]
    rfl
