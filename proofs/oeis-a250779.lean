import OMAStatements.S_oeis_a250779
import Mathlib

namespace OMA.S_oeis_a250779

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

def Rel : (Fin 5 → Fin 2) → (Fin 5 → Fin 2) → Prop :=
  fun u v => ∀ j : Fin 4, CellOK ((u j.castSucc : ℕ) : ℤ) ((u j.succ : ℕ) : ℤ) ((v j.castSucc : ℕ) : ℤ) ((v j.succ : ℕ) : ℤ)

instance : DecidableRel Rel := fun u v => by unfold Rel CellOK; infer_instance

theorem a_eq (n : ℕ) : a n = ∑ s, V Rel n s := by
  unfold a
  have e : {x : Fin (n + 1) → Fin 5 → Fin 2 // ∀ i : Fin n, ∀ j : Fin 4,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)} ≃
      Chain Rel n := Equiv.refl _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(0 : ℤ), (-2 : ℤ), (13 : ℤ), (-36 : ℤ), (55 : ℤ), (-50 : ℤ), (27 : ℤ), (-8 : ℤ), (1 : ℤ)].getD j 0

theorem hrec (k : ℕ) : (a (k + 8) : ℤ) = (2 : ℤ) * a (k + 1) + (-13 : ℤ) * a (k + 2) + (36 : ℤ) * a (k + 3) + (-55 : ℤ) * a (k + 4) + (50 : ℤ) * a (k + 5) + (-27 : ℤ) * a (k + 6) + (8 : ℤ) * a (k + 7) := by
  have h := rec_total Rel 8 cc (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = -2 := rfl
  have e2 : cc 2 = 13 := rfl
  have e3 : cc 3 = -36 := rfl
  have e4 : cc 4 = 55 := rfl
  have e5 : cc 5 = -50 := rfl
  have e6 : cc 6 = 27 := rfl
  have e7 : cc 7 = -8 := rfl
  have e8 : cc 8 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 99 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 238 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 534 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 1152 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 2426 := by rw [a_eq]; decide +kernel
theorem v6 : a 6 = 5028 := by rw [a_eq]; decide +kernel
theorem v7 : a 7 = 10306 := by rw [a_eq]; decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (-288 + 507 * (2 : ℚ) ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 7
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have r : (a (k + 8) : ℚ) = (2 : ℚ) * a (k + 1) + (-13 : ℚ) * a (k + 2) + (36 : ℚ) * a (k + 3) + (-55 : ℚ) * a (k + 4) + (50 : ℚ) * a (k + 5) + (-27 : ℚ) * a (k + 6) + (8 : ℚ) * a (k + 7) := by exact_mod_cast hrec k
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      rw [r, i1, i2, i3, i4, i5, i6, i7]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 5 5 (fun j => [(1 : ℚ), (-6 : ℚ), (14 : ℚ), (-16 : ℚ), (9 : ℚ), (-2 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (99 : ℚ), (-356 : ℚ), (492 : ℚ), (-304 : ℚ), (73 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 6) (by omega)
      have c1 := closed (k + 5) (by omega)
      have c2 := closed (k + 4) (by omega)
      have c3 := closed (k + 3) (by omega)
      have c4 := closed (k + 2) (by omega)
      have c5 := closed (k + 1) (by omega)
      simp [c0, c1, c2, c3, c4, c5]
      ring

end OMA.S_oeis_a250779

theorem OMA.solution : type_of% @OMA.S_oeis_a250779.main := by
  refine ⟨?_, OMA.S_oeis_a250779.gf, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    have e1 : k + 6 - 1 = k + 5 := by omega
    have e2 : k + 6 - 2 = k + 4 := by omega
    have e3 : k + 6 - 3 = k + 3 := by omega
    have e4 : k + 6 - 4 = k + 2 := by omega
    have e5 : k + 6 - 5 = k + 1 := by omega
    rw [e1, e2, e3, e4, e5]
    have : ((OMA.S_oeis_a250779.a (k + 6) : ℤ) : ℚ) = ((6 * (OMA.S_oeis_a250779.a (k + 5) : ℤ) - 14 * (OMA.S_oeis_a250779.a (k + 4) : ℤ) + 16 * (OMA.S_oeis_a250779.a (k + 3) : ℤ) - 9 * (OMA.S_oeis_a250779.a (k + 2) : ℤ) + 2 * (OMA.S_oeis_a250779.a (k + 1) : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [OMA.S_oeis_a250779.closed (k + 6) (by omega), OMA.S_oeis_a250779.closed (k + 5) (by omega), OMA.S_oeis_a250779.closed (k + 4) (by omega), OMA.S_oeis_a250779.closed (k + 3) (by omega), OMA.S_oeis_a250779.closed (k + 2) (by omega), OMA.S_oeis_a250779.closed (k + 1) (by omega)]
      push_cast
      ring
    exact_mod_cast this
  · intro n hn
    exact OMA.S_oeis_a250779.closed n hn
