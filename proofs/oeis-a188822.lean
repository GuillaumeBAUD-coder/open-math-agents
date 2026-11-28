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

def Rel : (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → Prop := PairOK

instance : DecidableRel Rel := fun u v => by unfold Rel PairOK; infer_instance

@[irreducible] def T (n : ℕ) : ℕ := ∑ s, V Rel n s

theorem a_eq (n : ℕ) : T n = ∑ s, V Rel n s := by unfold T; rfl

def ix (s : Fin 7 → Fin 2) : ℕ := ∑ i : Fin 7, (s i).val * 2 ^ i.val

def tb0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def tb1 : List ℕ := [1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 4, 1, 2, 4, 8, 1, 1, 2, 2, 2, 4, 4, 8, 1, 1, 4, 4, 2, 4, 8, 16, 2, 2, 4, 4, 2, 4, 4, 8, 4, 4, 16, 16, 4, 8, 16, 32, 2, 2, 4, 4, 4, 8, 8, 16, 4, 4, 16, 16, 8, 16, 32, 64, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 4, 1, 2, 4, 8, 2, 2, 4, 4, 4, 8, 8, 16, 2, 2, 8, 8, 4, 8, 16, 32, 2, 2, 4, 4, 2, 4, 4, 8, 4, 4, 16, 16, 4, 8, 16, 32, 4, 4, 8, 8, 8, 16, 16, 32, 8, 8, 32, 32, 16, 32, 64, 128]
def tb2 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 5, 5, 1, 3, 5, 15, 1, 1, 2, 2, 2, 8, 4, 16, 1, 1, 5, 5, 2, 8, 10, 40, 2, 2, 4, 4, 2, 6, 4, 12, 5, 5, 34, 34, 5, 15, 34, 102, 2, 2, 4, 4, 4, 16, 8, 32, 5, 5, 34, 34, 10, 40, 68, 272, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 5, 5, 1, 3, 5, 15, 3, 3, 6, 6, 8, 34, 16, 68, 3, 3, 15, 15, 8, 34, 40, 170, 2, 2, 4, 4, 2, 6, 4, 12, 5, 5, 34, 34, 5, 15, 34, 102, 6, 6, 12, 12, 16, 68, 32, 136, 15, 15, 102, 102, 40, 170, 272, 1156]
def tb3 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 9, 4, 18, 1, 1, 6, 6, 2, 9, 12, 54, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 72, 72, 6, 18, 72, 216, 2, 2, 4, 4, 4, 18, 8, 36, 6, 6, 72, 72, 12, 54, 144, 648, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 9, 54, 18, 108, 3, 3, 18, 18, 9, 54, 54, 324, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 72, 72, 6, 18, 72, 216, 6, 6, 12, 12, 18, 108, 36, 216, 18, 18, 216, 216, 54, 324, 648, 3888]
def tb4 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 10, 4, 20, 1, 1, 6, 6, 2, 10, 12, 60, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 94, 94, 6, 18, 94, 282, 2, 2, 4, 4, 4, 20, 8, 40, 6, 6, 94, 94, 12, 60, 188, 940, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 10, 94, 20, 188, 3, 3, 18, 18, 10, 94, 60, 564, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 94, 94, 6, 18, 94, 282, 6, 6, 12, 12, 20, 188, 40, 376, 18, 18, 282, 282, 60, 564, 940, 8836]
def tb5 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 10, 4, 20, 1, 1, 6, 6, 2, 10, 12, 60, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 136, 136, 6, 18, 136, 408, 2, 2, 4, 4, 4, 20, 8, 40, 6, 6, 136, 136, 12, 60, 272, 1360, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 10, 116, 20, 232, 3, 3, 18, 18, 10, 116, 60, 696, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 136, 136, 6, 18, 136, 408, 6, 6, 12, 12, 20, 232, 40, 464, 18, 18, 408, 408, 60, 696, 1360, 15776]
def tb6 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 10, 4, 20, 1, 1, 6, 6, 2, 10, 12, 60, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 158, 158, 6, 18, 158, 474, 2, 2, 4, 4, 4, 20, 8, 40, 6, 6, 158, 158, 12, 60, 316, 1580, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 10, 158, 20, 316, 3, 3, 18, 18, 10, 158, 60, 948, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 158, 158, 6, 18, 158, 474, 6, 6, 12, 12, 20, 316, 40, 632, 18, 18, 474, 474, 60, 948, 1580, 24964]
def tb7 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 10, 4, 20, 1, 1, 6, 6, 2, 10, 12, 60, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 200, 200, 6, 18, 200, 600, 2, 2, 4, 4, 4, 20, 8, 40, 6, 6, 200, 200, 12, 60, 400, 2000, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 10, 180, 20, 360, 3, 3, 18, 18, 10, 180, 60, 1080, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 200, 200, 6, 18, 200, 600, 6, 6, 12, 12, 20, 360, 40, 720, 18, 18, 600, 600, 60, 1080, 2000, 36000]
def tb8 : List ℕ := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 1, 1, 2, 2, 2, 10, 4, 20, 1, 1, 6, 6, 2, 10, 12, 60, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 222, 222, 6, 18, 222, 666, 2, 2, 4, 4, 4, 20, 8, 40, 6, 6, 222, 222, 12, 60, 444, 2220, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 6, 6, 1, 3, 6, 18, 3, 3, 6, 6, 10, 222, 20, 444, 3, 3, 18, 18, 10, 222, 60, 1332, 2, 2, 4, 4, 2, 6, 4, 12, 6, 6, 222, 222, 6, 18, 222, 666, 6, 6, 12, 12, 20, 444, 40, 888, 18, 18, 666, 666, 60, 1332, 2220, 49284]
def tbl (k : ℕ) : List ℕ := [tb0, tb1, tb2, tb3, tb4, tb5, tb6, tb7, tb8].getD k []

theorem split2 {n : ℕ} {α : Type} (P : (Fin (n + 2) → α) → Prop) (h : ∀ a b (s' : Fin n → α), P (Fin.cons a (Fin.cons b s'))) : ∀ s, P s := by
  intro s
  induction s using Fin.consCases with
  | _ a s =>
    induction s using Fin.consCases with
    | _ b s' => exact h a b s'

theorem Vstep (n : ℕ) (s : Fin 7 → Fin 2) : V Rel (n + 1) s = ∑ t, if Rel s t then V Rel n t else 0 := by simp [V]

theorem L0_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 0 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb0.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 0 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb0.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 0 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb0.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 0 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb0.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0 : ∀ s : Fin 7 → Fin 2, V Rel 0 s = tb0.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 0 s = tb0.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L0_c0_0
  · exact L0_c0_1
  · exact L0_c1_0
  · exact L0_c1_1

theorem L1_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 1 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb1.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 1 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb1.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 1 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb1.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 1 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb1.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1 : ∀ s : Fin 7 → Fin 2, V Rel 1 s = tb1.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 1 s = tb1.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L1_c0_0
  · exact L1_c0_1
  · exact L1_c1_0
  · exact L1_c1_1

theorem L2_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 2 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb2.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 2 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb2.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 2 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb2.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 2 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb2.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2 : ∀ s : Fin 7 → Fin 2, V Rel 2 s = tb2.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 2 s = tb2.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L2_c0_0
  · exact L2_c0_1
  · exact L2_c1_0
  · exact L2_c1_1

theorem L3_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 3 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb3.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 3 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb3.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 3 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb3.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 3 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb3.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3 : ∀ s : Fin 7 → Fin 2, V Rel 3 s = tb3.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 3 s = tb3.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L3_c0_0
  · exact L3_c0_1
  · exact L3_c1_0
  · exact L3_c1_1

theorem L4_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 4 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb4.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L3]
  revert s'
  decide +kernel

theorem L4_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 4 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb4.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L3]
  revert s'
  decide +kernel

theorem L4_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 4 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb4.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L3]
  revert s'
  decide +kernel

theorem L4_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 4 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb4.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L3]
  revert s'
  decide +kernel

theorem L4 : ∀ s : Fin 7 → Fin 2, V Rel 4 s = tb4.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 4 s = tb4.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L4_c0_0
  · exact L4_c0_1
  · exact L4_c1_0
  · exact L4_c1_1

theorem L5_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 5 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb5.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L4]
  revert s'
  decide +kernel

theorem L5_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 5 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb5.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L4]
  revert s'
  decide +kernel

theorem L5_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 5 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb5.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L4]
  revert s'
  decide +kernel

theorem L5_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 5 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb5.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L4]
  revert s'
  decide +kernel

theorem L5 : ∀ s : Fin 7 → Fin 2, V Rel 5 s = tb5.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 5 s = tb5.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L5_c0_0
  · exact L5_c0_1
  · exact L5_c1_0
  · exact L5_c1_1

theorem L6_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 6 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb6.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L5]
  revert s'
  decide +kernel

theorem L6_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 6 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb6.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L5]
  revert s'
  decide +kernel

theorem L6_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 6 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb6.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L5]
  revert s'
  decide +kernel

theorem L6_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 6 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb6.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L5]
  revert s'
  decide +kernel

theorem L6 : ∀ s : Fin 7 → Fin 2, V Rel 6 s = tb6.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 6 s = tb6.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L6_c0_0
  · exact L6_c0_1
  · exact L6_c1_0
  · exact L6_c1_1

theorem L7_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 7 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb7.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L6]
  revert s'
  decide +kernel

theorem L7_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 7 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb7.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L6]
  revert s'
  decide +kernel

theorem L7_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 7 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb7.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L6]
  revert s'
  decide +kernel

theorem L7_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 7 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb7.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L6]
  revert s'
  decide +kernel

theorem L7 : ∀ s : Fin 7 → Fin 2, V Rel 7 s = tb7.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 7 s = tb7.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L7_c0_0
  · exact L7_c0_1
  · exact L7_c1_0
  · exact L7_c1_1

theorem L8_c0_0 : ∀ s' : Fin 5 → Fin 2, V Rel 8 (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb8.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L7]
  revert s'
  decide +kernel

theorem L8_c0_1 : ∀ s' : Fin 5 → Fin 2, V Rel 8 (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb8.getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L7]
  revert s'
  decide +kernel

theorem L8_c1_0 : ∀ s' : Fin 5 → Fin 2, V Rel 8 (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2) = tb8.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L7]
  revert s'
  decide +kernel

theorem L8_c1_1 : ∀ s' : Fin 5 → Fin 2, V Rel 8 (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2) = tb8.getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L7]
  revert s'
  decide +kernel

theorem L8 : ∀ s : Fin 7 → Fin 2, V Rel 8 s = tb8.getD (ix s) 0 := by
  refine split2 (n := 5) (fun s => V Rel 8 s = tb8.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L8_c0_0
  · exact L8_c0_1
  · exact L8_c1_0
  · exact L8_c1_1

theorem key : ∀ j, j ≤ 8 → ∀ s : Fin 7 → Fin 2, V Rel j s = (tbl j).getD (ix s) 0 := by
  intro j hj s
  interval_cases j
  · exact L0 s
  · exact L1 s
  · exact L2 s
  · exact L3 s
  · exact L4 s
  · exact L5 s
  · exact L6 s
  · exact L7 s
  · exact L8 s
def cc : ℕ → ℤ := fun j => [(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), (2 : ℤ), (0 : ℤ), (-2 : ℤ), (1 : ℤ)].getD j 0

theorem h0chk_c0_0 : ∀ s' : Fin 5 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c0_1 : ∀ s' : Fin 5 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix (Fin.cons (0 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c1_0 : ∀ s' : Fin 5 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 2) s') : Fin 7 → Fin 2)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c1_1 : ∀ s' : Fin 5 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix (Fin.cons (1 : Fin 2) (Fin.cons (1 : Fin 2) s') : Fin 7 → Fin 2)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk : ∀ s : Fin 7 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix s) 0 : ℕ) : ℤ) = 0 := by
  refine split2 (n := 5) (fun s => ∑ j ∈ Finset.range 9, cc j * (((tbl j).getD (ix s) 0 : ℕ) : ℤ) = 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact h0chk_c0_0
  · exact h0chk_c0_1
  · exact h0chk_c1_0
  · exact h0chk_c1_1

theorem h0 : ∀ s : Fin 7 → Fin 2, ∑ j ∈ Finset.range 9, cc j * (V Rel j s : ℤ) = 0 := by
  intro s
  rw [Finset.sum_congr rfl (fun j hj => by rw [key j (by have := Finset.mem_range.1 hj; omega) s])]
  exact h0chk s


theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  rw [a_eq]
  unfold a cnt
  show Nat.card (Chain Rel n) = _
  rw [Nat.card_eq_fintype_card, cardChain]

set_option maxHeartbeats 4000000 in
theorem hrec (k : ℕ) : (T (k + 8) : ℤ) = (1 : ℤ) * T (k + 4) + (-2 : ℤ) * T (k + 5) + (0 : ℤ) * T (k + 6) + (2 : ℤ) * T (k + 7) := by
  have h := rec_total Rel 8 cc h0 k
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

theorem v1 : T 1 = 1156 := by rw [a_eq]; simp only [L1]; decide +kernel
theorem v2 : T 2 = 3888 := by rw [a_eq]; simp only [L2]; decide +kernel
theorem v3 : T 3 = 8836 := by rw [a_eq]; simp only [L3]; decide +kernel
theorem v4 : T 4 = 15776 := by rw [a_eq]; simp only [L4]; decide +kernel
theorem v5 : T 5 = 24964 := by rw [a_eq]; simp only [L5]; decide +kernel
theorem v6 : T 6 = 36000 := by rw [a_eq]; simp only [L6]; decide +kernel
theorem v7 : T 7 = 49284 := by rw [a_eq]; simp only [L7]; decide +kernel

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



theorem v0 : T 0 = 128 := by rw [a_eq]; simp only [L0]; decide +kernel

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    by_cases h8 : n = 8
    · subst h8
      have e0 := OMA.S_oeis_a188822.a_succ 7
      have e1 := OMA.S_oeis_a188822.a_succ 6
      have e2 := OMA.S_oeis_a188822.a_succ 4
      have e3 := OMA.S_oeis_a188822.a_succ 3
      show ((OMA.S_oeis_a188822.a 8 : ℕ) : ℤ) = 2 * (OMA.S_oeis_a188822.a 7 : ℤ) - 2 * (OMA.S_oeis_a188822.a 5 : ℤ) + 1 * (OMA.S_oeis_a188822.a 4 : ℤ)
      rw [e0, e1, e2, e3, OMA.S_oeis_a188822.v7, OMA.S_oeis_a188822.v6, OMA.S_oeis_a188822.v4, OMA.S_oeis_a188822.v3]
      norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have h1 : k + 9 - 1 = k + 8 := by omega
      have h3 : k + 9 - 3 = k + 6 := by omega
      have h4 : k + 9 - 4 = k + 5 := by omega
      rw [h1, h3, h4, OMA.S_oeis_a188822.a_succ (k + 8), OMA.S_oeis_a188822.a_succ (k + 7),
        OMA.S_oeis_a188822.a_succ (k + 5), OMA.S_oeis_a188822.a_succ (k + 4)]
      have := OMA.S_oeis_a188822.hrec k
      linarith
  · have h := OMA.S_oeis_a188822.gf
    have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a188822.a n : ℚ)) =
        X * PowerSeries.mk (fun n => (OMA.S_oeis_a188822.T n : ℚ)) := by
      ext n
      rcases n with _ | n
      · simp
      · rw [coeff_succ_X_mul]
        simp [OMA.S_oeis_a188822.a_succ]
    rw [e, h]
    unfold OMA.S_oeis_a188822.G
    ring
  · intro n hn he
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := OMA.S_oeis_a188822.closed3 k (by omega)
    rw [← OMA.S_oeis_a188822.a_succ k] at this
    have hp : (-1 : ℚ) ^ (k + 1) = 1 := he.neg_one_pow
    rw [hp] at this
    push_cast at this ⊢
    linarith
  · intro n hn ho
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := OMA.S_oeis_a188822.closed3 k (by omega)
    rw [← OMA.S_oeis_a188822.a_succ k] at this
    have hp : (-1 : ℚ) ^ (k + 1) = -1 := ho.neg_one_pow
    rw [hp] at this
    push_cast at this ⊢
    linarith
