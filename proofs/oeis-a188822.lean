import OMAStatements.S_oeis_a188822
import Mathlib

namespace OMA.S_oeis_a188822

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

def Rel : (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → Prop :=
  fun r s => ∀ j : Fin 6, ¬ (r j.castSucc = 0 ∧ s j.succ = 1) ∧ ¬ (r j.succ = 0 ∧ s j.castSucc = 1)

instance : DecidableRel Rel := fun u v => by unfold Rel; infer_instance

@[irreducible] def T (n : ℕ) : ℕ := ∑ s, V Rel n s

theorem a_eq (n : ℕ) : T n = ∑ s, V Rel n s := by unfold T; rfl

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  rw [a_eq]
  unfold a
  have e : {l : List (Fin 7 → Fin 2) // l.length = n + 1 ∧ IsSolution l} ≃ Chain Rel n := by
    symm
    refine Equiv.ofBijective (fun y => ⟨List.ofFn y.1, by simp, ?_⟩) ⟨?_, ?_⟩
    · unfold IsSolution
      rw [List.isChain_ofFn]
      intro i hi
      exact y.2 ⟨i, by omega⟩
    · intro y z h
      have := List.ofFn_injective (congrArg Subtype.val h)
      exact Subtype.ext this
    · rintro ⟨l, hl, hc⟩
      refine ⟨⟨fun i => l[i.1]'(by omega), ?_⟩, ?_⟩
      · intro i
        unfold IsSolution at hc
        exact List.isChain_iff_getElem.mp hc i.1 (by omega)
      · apply Subtype.ext
        apply List.ext_getElem
        · simp [hl]
        · intro i h1 h2
          dsimp only
          rw [List.getElem_ofFn]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), (2 : ℤ), (0 : ℤ), (-2 : ℤ), (1 : ℤ)].getD j 0

set_option maxHeartbeats 4000000 in
theorem hrec (k : ℕ) : (T (k + 8) : ℤ) = (1 : ℤ) * T (k + 4) + (-2 : ℤ) * T (k + 5) + (0 : ℤ) * T (k + 6) + (2 : ℤ) * T (k + 7) := by
  have h := rec_total Rel 8 cc (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 0 := rfl
  have e3 : cc 3 = 0 := rfl
  have e4 : cc 4 = -1 := rfl
  have e5 : cc 5 = 2 := rfl
  have e6 : cc 6 = 0 := rfl
  have e7 : cc 7 = -2 := rfl
  have e8 : cc 8 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : T 1 = 1156 := by rw [a_eq]; decide +kernel
theorem v2 : T 2 = 3888 := by rw [a_eq]; decide +kernel
theorem v3 : T 3 = 8836 := by rw [a_eq]; decide +kernel
theorem v4 : T 4 = 15776 := by rw [a_eq]; decide +kernel
theorem v5 : T 5 = 24964 := by rw [a_eq]; decide +kernel
theorem v6 : T 6 = 36000 := by rw [a_eq]; decide +kernel
theorem v7 : T 7 = 49284 := by rw [a_eq]; decide +kernel

theorem closed (n : ℕ) (hn : 4 ≤ n) : (T n : ℚ) = 2 * (578 - 1088 * ((n : ℚ) + 1) + 512 * ((n : ℚ) + 1) ^ 2) - 50 * (1 - (-1 : ℚ) ^ (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 7
    · interval_cases n
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have r : (T (k + 8) : ℚ) = (1 : ℚ) * T (k + 4) + (-2 : ℚ) * T (k + 5) + (0 : ℚ) * T (k + 6) + (2 : ℚ) * T (k + 7) := by exact_mod_cast hrec k
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      rw [r, i4, i5, i6, i7]
      push_cast
      ring


theorem v0 : T 0 = 128 := by rw [a_eq]; decide +kernel

theorem closed3 (n : ℕ) (hn : 3 ≤ n) : (T n : ℚ) = 2 * (578 - 1088 * ((n : ℚ) + 1) + 512 * ((n : ℚ) + 1) ^ 2) - 50 * (1 - (-1 : ℚ) ^ (n + 1)) := by
  by_cases h : n = 3
  · subst h; rw [v3]; norm_num
  · exact closed n (by omega)

theorem gf : PowerSeries.mk (fun n => (T n : ℚ)) = (4 * (32 + 225 * PowerSeries.X + 394 * PowerSeries.X ^ 2 + 329 * PowerSeries.X ^ 3 + 72 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5 - 36 * PowerSeries.X ^ 6)) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X))⁻¹ := by
  apply gf_gen _ 4 6 (fun j => [(1 : ℚ), (-2 : ℚ), (0 : ℚ), (2 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(128 : ℚ), (900 : ℚ), (1576 : ℚ), (1316 : ℚ), (288 : ℚ), (32 : ℚ), (-144 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ, v0]
    · simp [Finset.sum_range_succ, v0, v1] <;> norm_num
    · simp [Finset.sum_range_succ, v0, v1, v2] <;> norm_num
    · simp [Finset.sum_range_succ, v0, v1, v2, v3] <;> norm_num
    · simp [Finset.sum_range_succ, v0, v1, v2, v3, v4] <;> norm_num
    · simp [Finset.sum_range_succ, v0, v1, v2, v3, v4, v5] <;> norm_num
    · simp [Finset.sum_range_succ, v0, v1, v2, v3, v4, v5, v6] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed3 (k + 7) (by omega)
      have c1 := closed3 (k + 6) (by omega)
      have c2 := closed3 (k + 5) (by omega)
      have c3 := closed3 (k + 4) (by omega)
      have c4 := closed3 (k + 3) (by omega)
      simp [c0, c1, c2, c3, c4]
      ring

end OMA.S_oeis_a188822

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a188822.main := by
  refine ⟨?_, ?_, ?_⟩
  · have h := OMA.S_oeis_a188822.gf
    have hD : constantCoeff ((1 - X) ^ 3 * (1 + X) : PowerSeries ℚ) ≠ 0 := by simp
    simp only [OMA.S_oeis_a188822.a_succ] at *
    rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]
  · intro n hn he
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := OMA.S_oeis_a188822.closed3 k (by omega)
    rw [← OMA.S_oeis_a188822.a_succ] at this
    have hp : (-1 : ℚ) ^ (k + 1) = 1 := he.neg_one_pow
    rw [hp] at this
    have h2 : ((OMA.S_oeis_a188822.a (k + 1) : ℤ) : ℚ) = ((2 * (578 - 1088 * ((k + 1 : ℕ) : ℤ) + 512 * ((k + 1 : ℕ) : ℤ) ^ 2) : ℤ) : ℚ) := by
      push_cast at this ⊢
      linarith
    exact_mod_cast h2
  · intro n hn ho
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := OMA.S_oeis_a188822.closed3 k (by omega)
    rw [← OMA.S_oeis_a188822.a_succ] at this
    have hp : (-1 : ℚ) ^ (k + 1) = -1 := ho.neg_one_pow
    rw [hp] at this
    have h2 : ((OMA.S_oeis_a188822.a (k + 1) : ℤ) : ℚ) = ((2 * (528 - 1088 * ((k + 1 : ℕ) : ℤ) + 512 * ((k + 1 : ℕ) : ℤ) ^ 2) : ℤ) : ℚ) := by
      push_cast at this ⊢
      linarith
    exact_mod_cast h2
