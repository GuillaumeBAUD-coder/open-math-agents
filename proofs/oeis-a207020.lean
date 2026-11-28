import OMAStatements.S_oeis_a207020
import Mathlib

namespace OMA.S_oeis_a207020
section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic
open PowerSeries in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]


def Rel (r s : Row) : Prop := s ∈ rows ∧ (s.val &&& r.val) = s.val
instance : DecidableRel Rel := fun r s => by unfold Rel; infer_instance

theorem lsum {α : Type} (l : List α) (q : α → Bool) (g : α → ℕ) :
    ((l.filter q).map g).sum = (l.map fun t => if q t = true then g t else 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : q x = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem below_eq (r : Row) : below r = (List.finRange 16).filter (fun s => decide (Rel r s)) := by
  revert r; decide +kernel

theorem tails_len (h : ℕ) (r : Row) : (tails h r).length = V Rel h r := by
  induction h generalizing r with
  | zero => simp [tails, V]
  | succ h ih =>
    simp only [tails, V, List.length_flatMap, List.length_map, ih]
    rw [below_eq, lsum, Fin.sum_univ_def]
    simp

theorem a_succ (h : ℕ) : a (h + 1) = ((9 * V Rel h 15 : ℕ) : ℤ) := by
  have h9 : rows.length = 9 := by decide +kernel
  have : a (h + 1) = ((rows.map fun _ => V Rel h 15)).sum := by
    simp only [a, grids, List.length_flatMap, List.length_map, tails_len]
  rw [this, List.map_const', List.sum_replicate, h9, smul_eq_mul]

def cc : ℕ → ℤ := fun j => [0, 1, -4, 6, -4, 1].getD j 0

theorem h0 : ∀ s, ∑ j ∈ Finset.range (5 + 1), cc j * (V Rel j s : ℤ) = 0 := by
  unfold cc; decide +kernel

theorem rec_a1 (n : ℕ) : a (n + 6) = 4 * a (n + 5) - 6 * a (n + 4) + 4 * a (n + 3) - a (n + 2) := by
  have h := rec_gen Rel 5 cc h0 n 15
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 1 := rfl
  have e2 : cc 2 = -4 := rfl
  have e3 : cc 3 = 6 := rfl
  have e4 : cc 4 = -4 := rfl
  have e5 : cc 5 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5] at h
  have s6 : a (n + 6) = ((9 * V Rel (n + 5) 15 : ℕ) : ℤ) := a_succ (n + 5)
  have s5 : a (n + 5) = ((9 * V Rel (n + 4) 15 : ℕ) : ℤ) := a_succ (n + 4)
  have s4 : a (n + 4) = ((9 * V Rel (n + 3) 15 : ℕ) : ℤ) := a_succ (n + 3)
  have s3 : a (n + 3) = ((9 * V Rel (n + 2) 15 : ℕ) : ℤ) := a_succ (n + 2)
  have s2 : a (n + 2) = ((9 * V Rel (n + 1) 15 : ℕ) : ℤ) := a_succ (n + 1)
  rw [s6, s5, s4, s3, s2]
  push_cast
  linarith

theorem a0 : a 0 = 0 := rfl
theorem a1 : a 1 = 9 := by rw [a_succ]; decide +kernel
theorem a2 : a 2 = 81 := by rw [a_succ]; decide +kernel
theorem a3 : a 3 = 252 := by rw [a_succ]; decide +kernel
theorem a4 : a 4 = 558 := by rw [a_succ]; decide +kernel
theorem a5 : a 5 = 1035 := by rw [a_succ]; decide +kernel

theorem rec_a (n : ℕ) : a (n + 5) = 4 * a (n + 4) - 6 * a (n + 3) + 4 * a (n + 2) - a (n + 1) := by
  rcases n with _ | n
  · simp [a1, a2, a3, a4, a5]
  · exact rec_a1 n

theorem gfeq : PowerSeries.mk a * (1 - PowerSeries.X)^4 =
      9 * PowerSeries.X * (1 + 5*PowerSeries.X - 2*PowerSeries.X^2) := by
  have hQ : ((1 - PowerSeries.X) ^ 4 : PowerSeries ℤ) = 1 - PowerSeries.C (4:ℤ) * PowerSeries.X
      + PowerSeries.C (6:ℤ) * PowerSeries.X ^ 2
      - PowerSeries.C (4:ℤ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
    simp only [map_ofNat]; ring
  have hN : (9 * PowerSeries.X * (1 + 5*PowerSeries.X - 2*PowerSeries.X^2) : PowerSeries ℤ)
      = PowerSeries.C (9:ℤ) * PowerSeries.X + PowerSeries.C (45:ℤ) * PowerSeries.X ^ 2
        - PowerSeries.C (18:ℤ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [hQ, hN]
  set A : PowerSeries ℤ := PowerSeries.mk a with hA
  have hex : A * (1 - PowerSeries.C (4:ℤ) * PowerSeries.X
      + PowerSeries.C (6:ℤ) * PowerSeries.X ^ 2
      - PowerSeries.C (4:ℤ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4)
      = A - PowerSeries.C (4:ℤ) * (PowerSeries.X ^ 1 * A) + PowerSeries.C (6:ℤ) * (PowerSeries.X ^ 2 * A)
      - PowerSeries.C (4:ℤ) * (PowerSeries.X ^ 3 * A) + PowerSeries.X ^ 4 * A := by ring
  rw [hex]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, hA, PowerSeries.coeff_mk]
  by_cases h5 : 5 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := rec_a m
    have e1 : m + 5 - 1 = m + 4 := by omega
    have e2 : m + 5 - 2 = m + 3 := by omega
    have e3 : m + 5 - 3 = m + 2 := by omega
    have e4 : m + 5 - 4 = m + 1 := by omega
    simp [e1, e2, e3, e4, h, show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega,
      show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega]
    ring
  · interval_cases n <;> simp [a0, a1, a2, a3, a4] <;> norm_num

end OMA.S_oeis_a207020

theorem OMA.solution : type_of% @OMA.S_oeis_a207020.main :=
  ⟨OMA.S_oeis_a207020.gfeq, OMA.S_oeis_a207020.rec_a⟩
