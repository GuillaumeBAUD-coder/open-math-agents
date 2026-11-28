import OMAStatements.S_oeis_a183586
import Mathlib

namespace OMA.S_oeis_a183586

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

def Rel : (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → Prop := BlockOK

instance : DecidableRel Rel := fun u v => by unfold Rel BlockOK; infer_instance

theorem N_eq (n : ℕ) : N n = ∑ s, V Rel n s := by
  unfold N
  have e : {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)} ≃ Chain Rel n :=
    Equiv.refl _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(-12 : ℤ), -8, 1].getD j 0

theorem hrecN (k : ℕ) : (N (k + 2) : ℤ) = 8 * N (k + 1) + 12 * N k := by
  have h := rec_total Rel 2 cc (by decide +kernel) k
  have e0 : cc 0 = -12 := rfl
  have e1 : cc 1 = -8 := rfl
  have e2 : cc 2 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, Nat.add_zero] at h
  simp only [N_eq]
  push_cast
  linarith

theorem N1 : N 1 = 144 := by rw [N_eq]; decide +kernel
theorem N2 : N 2 = 1344 := by rw [N_eq]; decide +kernel

theorem hdiv (n : ℕ) : N (n + 1) % 24 = 0 ∧ N (n + 2) % 24 = 0 := by
  induction n with
  | zero => rw [N1, N2]; omega
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h : N (n + 1 + 2) = 8 * N (n + 2) + 12 * N (n + 1) := by exact_mod_cast hrecN (n + 1)
    omega

theorem hN (n : ℕ) : N (n + 1) = 24 * a (n + 1) := by
  unfold a
  have := (hdiv n).1
  omega

theorem v1 : a 1 = 6 := by have : N 1 = 24 * a 1 := hN 0; rw [N1] at this; omega
theorem v2 : a 2 = 56 := by have : N 2 = 24 * a 2 := hN 1; rw [N2] at this; omega

theorem hrec (k : ℕ) : a (k + 3) = 8 * a (k + 2) + 12 * a (k + 1) := by
  have h : N (k + 3) = 8 * N (k + 2) + 12 * N (k + 1) := by exact_mod_cast hrecN (k + 1)
  have h1 : N (k + 1) = 24 * a (k + 1) := hN k
  have h2 : N (k + 2) = 24 * a (k + 2) := hN (k + 1)
  have h3 : N (k + 3) = 24 * a (k + 3) := hN (k + 2)
  omega

theorem uform (k : ℕ) : (4 - 2 * Real.sqrt 7) ^ (k + 1) * (-5 + 2 * Real.sqrt 7) +
    (2 * (2 + Real.sqrt 7)) ^ (k + 1) * (5 + 2 * Real.sqrt 7) = 6 * Real.sqrt 7 * (a (k + 1) : ℝ) := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rw [v1]; push_cast; ring
    · rw [v2]; push_cast
      linear_combination (16 * Real.sqrt 7) * hs
    · have i1 := ih (k + 1) (by omega)
      have i0 := ih k (by omega)
      have r : (a (k + 3) : ℝ) = 8 * a (k + 2) + 12 * a (k + 1) := by exact_mod_cast hrec k
      rw [r]
      linear_combination (4 * (4 - 2 * Real.sqrt 7) ^ (k + 1) * (-5 + 2 * Real.sqrt 7) +
        4 * (2 * (2 + Real.sqrt 7)) ^ (k + 1) * (5 + 2 * Real.sqrt 7)) * hs + 8 * i1 + 12 * i0

end OMA.S_oeis_a183586

open PowerSeries OMA.S_oeis_a183586 in
theorem OMA.solution : type_of% @OMA.S_oeis_a183586.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have e1 : k + 3 - 1 = k + 2 := by omega
    have e2 : k + 3 - 2 = k + 1 := by omega
    rw [e1, e2]
    exact hrec k
  · have hQ : ∀ k : ℕ, (a (k + 3) : ℚ) = 8 * a (k + 2) + 12 * a (k + 1) := by
      intro k
      exact_mod_cast hrec k
    unfold G
    apply gf_gen _ 2 2 (fun j => [(1 : ℚ), -8, -12].getD j 0) (fun j => [(0 : ℚ), 6, 8].getD j 0)
    · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    · norm_num
    · intro n hn
      simp only [List.getD_eq_getElem?_getD]
      rcases n with _ | _ | _ | k <;> simp_all
    · intro n
      rcases n with _ | _ | _ | k
      · simp [Finset.sum_range_succ]
      · simp [Finset.sum_range_succ, v1]
      · simp [Finset.sum_range_succ, v1, v2]; norm_num
      · have h := hQ k
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        simp
        linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hs0 : Real.sqrt 7 ≠ 0 := by positivity
    have := uform k
    rw [eq_div_iff (by positivity)]
    linarith
