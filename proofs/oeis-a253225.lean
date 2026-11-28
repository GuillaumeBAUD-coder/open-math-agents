import OMAStatements.S_oeis_a253225
import Mathlib

namespace OMA.S_oeis_a253225

section generic3
variable {V : Type} [Fintype V] [DecidableEq V] (ok : V → V → V → Prop) [∀ u v w, Decidable (ok u v w)]

def cnt3 : ℕ → V → V → ℤ
  | 0, _, _ => 1
  | k + 1, u, v => ∑ w : V, if ok u v w then cnt3 k v w else 0

theorem cnt3_card (m : ℕ) : ∀ u v : V,
    (Fintype.card {x : Fin (m + 2) → V // x 0 = u ∧ x (Fin.succ 0) = v ∧
      ∀ i : Fin m, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} : ℤ)
      = cnt3 ok m u v := by
  induction m with
  | zero =>
    intro u v
    have : Fintype.card {x : Fin (0 + 2) → V // x 0 = u ∧ x (Fin.succ 0) = v ∧
      ∀ i : Fin 0, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨![u, v], rfl, rfl, fun i => i.elim0⟩, ?_⟩
      rintro ⟨x, hx0, hx1, -⟩
      apply Subtype.ext
      funext i
      fin_cases i
      · exact hx0
      · exact hx1
    rw [this]; simp [cnt3]
  | succ m ih =>
    intro u v
    let e : {x : Fin (m + 3) → V // x 0 = u ∧ x (Fin.succ 0) = v ∧
        ∀ i : Fin (m + 1), ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} ≃
        Σ w : {w : V // ok u v w}, {y : Fin (m + 2) → V // y 0 = v ∧ y (Fin.succ 0) = w.1 ∧
          ∀ i : Fin m, ok (y i.castSucc.castSucc) (y i.castSucc.succ) (y i.succ.succ)} :=
      { toFun := fun x => ⟨⟨x.1 (Fin.succ (Fin.succ 0)), by
            have h := x.2.2.2 0
            have h0 : x.1 (Fin.castSucc (Fin.castSucc 0)) = u := x.2.1
            have h1 : x.1 (Fin.succ (Fin.castSucc 0)) = v := x.2.2.1
            rw [h0, h1] at h
            exact h⟩,
          ⟨Fin.tail x.1, x.2.2.1, rfl, fun i => by
            have h := x.2.2.2 i.succ
            simpa [Fin.tail] using h⟩⟩
        invFun := fun p => ⟨Fin.cons u p.2.1, by simp, by
            rw [Fin.cons_succ]; exact p.2.2.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h := p.1.2
            have h1 := p.2.2.1
            have h2 := p.2.2.2.1
            have c2 : (Fin.cons u p.2.1 : Fin (m + 3) → V) (Fin.succ (Fin.succ 0)) = p.1.1 := by rw [Fin.cons_succ]; exact h2
            have c1 : (Fin.cons u p.2.1 : Fin (m + 3) → V) (Fin.succ 0) = v := by rw [Fin.cons_succ]; exact h1
            have c0 : (Fin.cons u p.2.1 : Fin (m + 3) → V) 0 = u := by simp
            have e0 : (Fin.castSucc (Fin.castSucc (0 : Fin (m + 1))) : Fin (m + 3)) = 0 := rfl
            have e1 : (Fin.succ (Fin.castSucc (0 : Fin (m + 1))) : Fin (m + 3)) = Fin.succ 0 := rfl
            show ok ((Fin.cons u p.2.1 : Fin (m + 3) → V) (Fin.castSucc (Fin.castSucc (0 : Fin (m + 1)))))
              ((Fin.cons u p.2.1 : Fin (m + 3) → V) (Fin.succ (Fin.castSucc (0 : Fin (m + 1)))))
              ((Fin.cons u p.2.1 : Fin (m + 3) → V) (Fin.succ (Fin.succ 0)))
            rw [e0, e1, c0, c1, c2]
            exact h
          · have := p.2.2.2.2 j
            rw [Fin.succ_castSucc]
            simpa using this⟩
        left_inv := by
          rintro ⟨x, hx0, hx1, -⟩
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · show (Fin.cons u (Fin.tail x) : Fin (m + 3) → V) 0 = x 0
            rw [Fin.cons_zero, hx0]
          · show (Fin.cons u (Fin.tail x) : Fin (m + 3) → V) j.succ = x j.succ
            rw [Fin.cons_succ]; rfl
        right_inv := by
          rintro ⟨⟨w, hw⟩, ⟨y, hy0, hy1, -⟩⟩
          have : y (Fin.succ 0) = w := hy1
          subst this
          have h2 : (Fin.cons u y : Fin (m + 3) → V) 2 = y 1 := by
            rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          simp [h2]
          exact HEq.rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    push_cast
    simp only [ih]
    rw [cnt3, ← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun w => ok u v w)) (by simp) (fun w => cnt3 ok m v w)).symm

theorem tot3 (m : ℕ) (Q : V → V → Prop) [DecidableRel Q] :
    (Fintype.card {x : Fin (m + 2) → V // Q (x 0) (x (Fin.succ 0)) ∧
      ∀ i : Fin m, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} : ℤ)
      = ∑ u : V, ∑ v : V, if Q u v then cnt3 ok m u v else 0 := by
  let e : {x : Fin (m + 2) → V // Q (x 0) (x (Fin.succ 0)) ∧
      ∀ i : Fin m, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} ≃
      Σ p : V × V, {x : Fin (m + 2) → V // Q p.1 p.2 ∧ x 0 = p.1 ∧ x (Fin.succ 0) = p.2 ∧
        ∀ i : Fin m, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} :=
    { toFun := fun x => ⟨(x.1 0, x.1 (Fin.succ 0)), ⟨x.1, x.2.1, rfl, rfl, x.2.2⟩⟩
      invFun := fun p => ⟨p.2.1, by
        have h1 := p.2.2.1
        have h2 := p.2.2.2.1
        have h3 := p.2.2.2.2.1
        rw [h2, h3]; exact ⟨h1, p.2.2.2.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := by
        rintro ⟨⟨u, v⟩, x, hq, h0, h1, hv⟩
        simp only at hq h0 h1
        subst h0; subst h1
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  by_cases hq : Q u v
  · rw [if_pos hq, ← cnt3_card ok m u v]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hq]))
  · rw [if_neg hq]
    have : IsEmpty {x : Fin (m + 2) → V // Q (u, v).1 (u, v).2 ∧ x 0 = (u, v).1 ∧ x (Fin.succ 0) = (u, v).2 ∧
        ∀ i : Fin m, ok (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)} :=
      ⟨fun x => hq x.2.1⟩
    simp only [Nat.cast_eq_zero]
    exact Fintype.card_eq_zero
end generic3

abbrev V := Fin 2 × Fin 2 × Fin 2

def eqv : (Fin 3 → Fin 2) ≃ V :=
  { toFun := fun r => (r 0, r 1, r 2)
    invFun := fun p => ![p.1, p.2.1, p.2.2]
    left_inv := fun r => by funext i; fin_cases i <;> rfl
    right_inv := fun p => rfl }

def Ap (r s : Fin 3 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 →
    min ((r j).val : ℤ) ((s j').val : ℤ) - min ((r j').val : ℤ) ((s j).val : ℤ) ≤
      min ((r j').val : ℤ) ((s j'').val : ℤ) - min ((r j'').val : ℤ) ((s j').val : ℤ)

def Bp (r s t : Fin 3 → Fin 2) : Prop :=
  ∀ j j' : Fin 3, j'.val = j.val + 1 →
    max ((r j).val : ℤ) ((s j').val : ℤ) - max ((r j').val : ℤ) ((s j).val : ℤ) ≤
      max ((s j).val : ℤ) ((t j').val : ℤ) - max ((s j').val : ℤ) ((t j).val : ℤ)

instance (r s : Fin 3 → Fin 2) : Decidable (Ap r s) := by unfold Ap; infer_instance
instance (r s t : Fin 3 → Fin 2) : Decidable (Bp r s t) := by unfold Bp; infer_instance

def okk (u v w : V) : Prop := Bp (eqv.symm u) (eqv.symm v) (eqv.symm w) ∧ Ap (eqv.symm v) (eqv.symm w)
def Qq (u v : V) : Prop := Ap (eqv.symm u) (eqv.symm v)
instance (u v w : V) : Decidable (okk u v w) := by unfold okk; infer_instance
instance : DecidableRel Qq := fun u v => by unfold Qq; infer_instance

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = ∑ u : V, ∑ v : V, if Qq u v then cnt3 okk m u v else 0 := by
  rw [← tot3 okk m Qq]
  have h1 : a (m + 1) = Fintype.card {x : Fin (m + 2) → Fin 3 → Fin 2 //
      (∀ i i' : Fin (m + 2), i'.val = i.val + 1 → Ap (x i) (x i')) ∧
      ∀ i i' i'' : Fin (m + 2), i'.val = i.val + 1 → i''.val = i'.val + 1 → Bp (x i) (x i') (x i'')} := by
    simp only [a]; exact (Fintype.card_subtype _).symm
  rw [h1]
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl _) eqv) ?_)
  intro x
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_apply_apply, okk, Qq, Function.comp]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
    · exact hA 0 (Fin.succ 0) (by simp)
    · exact hB _ _ _ (by simp) (by simp)
    · exact hA _ _ (by simp)
  · rintro ⟨hQ, hW⟩
    refine ⟨fun i i' hii => ?_, fun i i' i'' h1 h2 => ?_⟩
    · by_cases h0 : i.val = 0
      · have e1 : i = 0 := Fin.ext h0
        have e2 : i' = Fin.succ 0 := Fin.ext (by simp [hii, h0])
        subst e1; subst e2; exact hQ
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, i.val = k + 1 := ⟨i.val - 1, by omega⟩
        have hk2 : k < m := by have := i'.isLt; omega
        have := (hW ⟨k, hk2⟩).2
        have e1 : i = Fin.succ (Fin.castSucc ⟨k, hk2⟩) := Fin.ext (by simp [hk])
        have e2 : i' = Fin.succ (Fin.succ ⟨k, hk2⟩) := Fin.ext (by simp [hii, hk])
        rw [e1, e2]; simpa using this
    · have hk2 : i.val < m := by have := i''.isLt; omega
      have := (hW ⟨i.val, hk2⟩).1
      have e1 : i = Fin.castSucc (Fin.castSucc ⟨i.val, hk2⟩) := Fin.ext (by simp)
      have e2 : i' = Fin.succ (Fin.castSucc ⟨i.val, hk2⟩) := Fin.ext (by simp [h1])
      have e3 : i'' = Fin.succ (Fin.succ ⟨i.val, hk2⟩) := Fin.ext (by simp [h1, h2])
      rw [e1, e2, e3]; simpa using this


theorem cnt_rec : ∀ k : ℕ, ∀ u v : V,
    cnt3 okk (k + 7) u v = 5 * cnt3 okk (k + 6) u v - 8 * cnt3 okk (k + 5) u v + 4 * cnt3 okk (k + 4) u v := by
  intro k
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    intro u v
    have h1 : cnt3 okk (k + 1 + 7) u v = ∑ w : V, if okk u v w then cnt3 okk (k + 7) v w else 0 := rfl
    have h2 : cnt3 okk (k + 1 + 6) u v = ∑ w : V, if okk u v w then cnt3 okk (k + 6) v w else 0 := rfl
    have h3 : cnt3 okk (k + 1 + 5) u v = ∑ w : V, if okk u v w then cnt3 okk (k + 5) v w else 0 := rfl
    have h4 : cnt3 okk (k + 1 + 4) u v = ∑ w : V, if okk u v w then cnt3 okk (k + 4) v w else 0 := rfl
    rw [h1, h2, h3, h4, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs
    · exact ih v w
    · simp

theorem a_vals : (a 1 : ℤ) = 47 ∧ (a 2 : ℤ) = 132 ∧ (a 3 : ℤ) = 306 ∧ (a 4 : ℤ) = 742 ∧ (a 5 : ℤ) = 1775 ∧
    (a 6 : ℤ) = 4158 ∧ (a 7 : ℤ) = 9551 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := a_eq 0; rw [this]; decide +kernel
  · have := a_eq 1; rw [this]; decide +kernel
  · have := a_eq 2; rw [this]; decide +kernel
  · have := a_eq 3; rw [this]; decide +kernel
  · have := a_eq 4; rw [this]; decide +kernel
  · have := a_eq 5; rw [this]; decide +kernel
  · have := a_eq 6; rw [this]; decide +kernel


theorem a_rec (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 4 * a (n - 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [show j + 8 - 1 = j + 6 + 1 by omega, show j + 8 - 2 = j + 5 + 1 by omega,
    show j + 8 - 3 = j + 4 + 1 by omega, show j + 8 = j + 7 + 1 by omega]
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs
  · exact cnt_rec j u v
  · simp

theorem gf_gen (f : ℕ → ℚ) (q0 : f 0 = 0) (q1 : f 1 = 47) (q2 : f 2 = 132) (q3 : f 3 = 306) (q4 : f 4 = 742)
    (q5 : f 5 = 1775) (q6 : f 6 = 4158) (q7 : f 7 = 9551)
    (hrec : ∀ n, 8 ≤ n → f n = 5 * f (n - 1) - 8 * f (n - 2) + 4 * f (n - 3)) :
    PowerSeries.mk f * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) ^ 2) =
      PowerSeries.X * (47 - 103 * PowerSeries.X + 22 * PowerSeries.X ^ 2 + 80 * PowerSeries.X ^ 3
        - 15 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 5 - 7 * PowerSeries.X ^ 6) := by
  open PowerSeries in
  have hP : ((1 - X) * (1 - 2 * X) ^ 2 : PowerSeries ℚ) = 1 - 5 • X + 8 • X ^ 2 - 4 • X ^ 3 := by
    simp only [nsmul_eq_mul]; push_cast; ring
  have hQ : (X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) : PowerSeries ℚ) =
      47 • X - 103 • X ^ 2 + 22 • X ^ 3 + 80 • X ^ 4 - 15 • X ^ 5 - 5 • X ^ 6 - 7 • X ^ 7 := by
    simp only [nsmul_eq_mul]; push_cast; ring
  have e : PowerSeries.mk f * (1 - 5 • X + 8 • X ^ 2 - 4 • X ^ 3) =
      PowerSeries.mk f - 5 • (X ^ 1 * PowerSeries.mk f) + 8 • (X ^ 2 * PowerSeries.mk f)
        - 4 • (X ^ 3 * PowerSeries.mk f) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [hP, hQ, e]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X]
  rcases (by omega : n < 8 ∨ 8 ≤ n) with h | h
  · interval_cases n <;> simp [q0, q1, q2, q3, q4, q5, q6, q7] <;> norm_num
  · have hq := hrec n h
    simp [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show 1 ≤ n by omega,
      show 2 ≤ n by omega, show 3 ≤ n by omega, hq]
    ring

theorem closed : ∀ n : ℕ, 4 < n →
    (a n : ℚ) = 19 + 377 * 2 ^ ((n : ℤ) - 6) + 627 * 2 ^ ((n : ℤ) - 6) * n := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := a_vals
  have hz : ∀ n : ℕ, (2 : ℚ) ^ ((n : ℤ) - 6) = 2 ^ n / 64 := by
    intro n
    rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [hz]
    by_cases h : n ≤ 7
    · interval_cases n
      · have : (a 5 : ℚ) = 1775 := by exact_mod_cast v5
        rw [this]; norm_num
      · have : (a 6 : ℚ) = 4158 := by exact_mod_cast v6
        rw [this]; norm_num
      · have : (a 7 : ℚ) = 9551 := by exact_mod_cast v7
        rw [this]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have hh := a_rec (k + 8) (by omega)
      simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
        show k + 8 - 3 = k + 5 by omega] at hh
      have hh' : (a (k + 8) : ℚ) = 5 * (a (k + 7) : ℚ) - 8 * (a (k + 6) : ℚ) + 4 * (a (k + 5) : ℚ) := by
        exact_mod_cast hh
      have e1 := ih (k + 7) (by omega) (by omega)
      have e2 := ih (k + 6) (by omega) (by omega)
      have e3 := ih (k + 5) (by omega) (by omega)
      rw [hz] at e1 e2 e3
      rw [hh', e1, e2, e3]
      push_cast
      ring

theorem solution_aux : type_of% @OMA.S_oeis_a253225.main := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := a_vals
  refine ⟨?_, closed⟩
  refine gf_gen _ (by simp) (by simpa using (by exact_mod_cast v1 : (a 1 : ℚ) = 47))
    (by simpa using (by exact_mod_cast v2 : (a 2 : ℚ) = 132))
    (by simpa using (by exact_mod_cast v3 : (a 3 : ℚ) = 306))
    (by simpa using (by exact_mod_cast v4 : (a 4 : ℚ) = 742))
    (by simpa using (by exact_mod_cast v5 : (a 5 : ℚ) = 1775))
    (by simpa using (by exact_mod_cast v6 : (a 6 : ℚ) = 4158))
    (by simpa using (by exact_mod_cast v7 : (a 7 : ℚ) = 9551)) ?_
  intro n hn
  have hh := a_rec n hn
  have hh' : (a n : ℚ) = 5 * (a (n - 1) : ℚ) - 8 * (a (n - 2) : ℚ) + 4 * (a (n - 3) : ℚ) := by
    exact_mod_cast hh
  simp only [show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
    if_false]
  exact hh'

end OMA.S_oeis_a253225

theorem OMA.solution : type_of% @OMA.S_oeis_a253225.main := OMA.S_oeis_a253225.solution_aux
