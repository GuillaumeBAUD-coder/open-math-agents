import OMAStatements.S_oeis_a184688
import Mathlib

namespace OMA.S_oeis_a184688

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

def Rel : (Fin 3 → Fin 3) → (Fin 3 → Fin 3) → Prop :=
  fun u v => ∀ j : Fin 2, ¬(v j.succ = u j.succ ∧ v j.succ = v j.castSucc)

instance : DecidableRel Rel := fun u v => by unfold Rel; infer_instance

theorem N_eq (m : ℕ) : N (m + 1) = ∑ s, V Rel m s := by
  unfold N
  have e : {x : Fin (m + 1) → Fin 3 → Fin 3 // Good x} ≃ Chain Rel m :=
    Equiv.subtypeEquivRight (by
      intro x
      constructor
      · intro h i j
        have := h i.succ i.castSucc j.succ j.castSucc (by simp) (by simp)
        exact this
      · intro h i i' j j' hi hj
        have hi' : i' < m := by have := i.2; omega
        have hj' : (j' : ℕ) < 2 := by have := j.2; omega
        have e1 : (⟨i', hi'⟩ : Fin m).succ = i := Fin.ext (by simp [hi])
        have e2 : (⟨i', hi'⟩ : Fin m).castSucc = i' := Fin.ext (by simp)
        have e3 : (⟨j', hj'⟩ : Fin 2).succ = j := Fin.ext (by simp [hj])
        have e4 : (⟨j', hj'⟩ : Fin 2).castSucc = j' := Fin.ext (by simp)
        have key := h ⟨i', hi'⟩ ⟨j', hj'⟩
        rw [e1, e2, e3, e4] at key
        exact key)
  refine (Nat.card_congr e).trans ?_
  exact Nat.card_eq_fintype_card.trans (cardChain Rel m)

def cc : ℕ → ℤ := fun j => [(16 : ℤ), -22, 1].getD j 0

theorem hrecN (k : ℕ) : (N (k + 3) : ℤ) = 22 * N (k + 2) - 16 * N (k + 1) := by
  have h := rec_total Rel 2 cc (by decide +kernel) k
  have e0 : cc 0 = 16 := rfl
  have e1 : cc 1 = -22 := rfl
  have e2 : cc 2 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, Nat.add_zero] at h
  have e3 : N (k + 3) = ∑ s, V Rel (k + 2) s := N_eq (k + 2)
  have e2 : N (k + 2) = ∑ s, V Rel (k + 1) s := N_eq (k + 1)
  have e1 : N (k + 1) = ∑ s, V Rel k s := N_eq k
  rw [e3, e2, e1]
  push_cast
  linarith

theorem N1 : N 1 = 27 := (N_eq 0).trans (by decide +kernel)
theorem N2 : N 2 = 576 := (N_eq 1).trans (by decide +kernel)

theorem dvd3 (k : ℕ) : 3 ∣ N (k + 1) ∧ 3 ∣ N (k + 2) := by
  induction k with
  | zero =>
    have h1 : N (0 + 1) = 27 := N1
    have h2 : N (0 + 2) = 576 := N2
    rw [h1, h2]; omega
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have h2' : 3 ∣ N (k + 2) := h2
    have e : N (k + 1 + 1) = N (k + 2) := rfl
    have e' : N (k + 1 + 2) = N (k + 3) := rfl
    refine ⟨by rw [e]; exact h2, ?_⟩
    have := hrecN k
    rw [e']
    omega

theorem a_mul (k : ℕ) : 3 * a (k + 1) = N (k + 1) := by
  show 3 * (N (k + 1) / 3) = N (k + 1)
  exact Nat.mul_div_cancel' (dvd3 k).1

theorem a1 : a 1 = 9 := by
  have h : 3 * a 1 = N 1 := a_mul 0
  rw [N1] at h; omega
theorem a2 : a 2 = 192 := by
  have h : 3 * a 2 = N 2 := a_mul 1
  rw [N2] at h; omega

theorem hrec (k : ℕ) : (a (k + 3) : ℤ) = 22 * a (k + 2) - 16 * a (k + 1) := by
  have h := hrecN k
  have h3 : 3 * a (k + 3) = N (k + 3) := a_mul (k + 2)
  have h2 : 3 * a (k + 2) = N (k + 2) := a_mul (k + 1)
  have h1 : 3 * a (k + 1) = N (k + 1) := a_mul k
  omega

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = ((105 - 13 * Real.sqrt 105) * (11 - Real.sqrt 105) ^ n +
      (11 + Real.sqrt 105) ^ n * (105 + 13 * Real.sqrt 105)) / 560 := by
  have hs : Real.sqrt 105 ^ 2 = 105 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 105 with hsdef
  have hA : ∀ n : ℕ, (11 + s) ^ (n + 2) = 22 * (11 + s) ^ (n + 1) - 16 * (11 + s) ^ n := by
    intro n; linear_combination (11 + s) ^ n * hs
  have hB : ∀ n : ℕ, (11 - s) ^ (n + 2) = 22 * (11 - s) ^ (n + 1) - 16 * (11 - s) ^ n := by
    intro n; linear_combination (11 - s) ^ n * hs
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h3 : 3 ≤ n
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have r : (a (k + 3) : ℝ) = 22 * a (k + 2) - 16 * a (k + 1) := by exact_mod_cast hrec k
      have hA' : (11 + s) ^ (k + 3) = 22 * (11 + s) ^ (k + 2) - 16 * (11 + s) ^ (k + 1) := hA (k + 1)
      have hB' : (11 - s) ^ (k + 3) = 22 * (11 - s) ^ (k + 2) - 16 * (11 - s) ^ (k + 1) := hB (k + 1)
      rw [r, ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega), hA', hB']
      ring
    · have h12 : n = 1 ∨ n = 2 := by omega
      rcases h12 with rfl | rfl
      · rw [a1]; push_cast; linear_combination (-26 / 560 : ℝ) * hs
      · rw [a2]; push_cast; linear_combination (-782 / 560 : ℝ) * hs

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 2 2 (fun j => [(1 : ℚ), -22, 16].getD j 0) (fun j => [(0 : ℚ), 9, -6].getD j 0)
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
    · simp [Finset.sum_range_succ, a1]
    · simp [Finset.sum_range_succ, a1, a2] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have r : (a (k + 3) : ℚ) = 22 * a (k + 2) - 16 * a (k + 1) := by exact_mod_cast hrec k
      simp [r]
      ring

end OMA.S_oeis_a184688

theorem OMA.solution : type_of% @OMA.S_oeis_a184688.main := by
  refine ⟨?_, OMA.S_oeis_a184688.gf, OMA.S_oeis_a184688.closed⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have := OMA.S_oeis_a184688.hrec k
  simpa using this
