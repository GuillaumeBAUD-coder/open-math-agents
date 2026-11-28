import OMAStatements.S_mo_40662

open Matrix Finset

namespace OMA.P_mo_40662

private def chi (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

private lemma chi_eq_one_iff (z : ZMod 2) : chi z = 1 ↔ z = 0 := by
  fin_cases z <;> simp [chi]

private lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

private lemma sum_chi_mul :
    (∑ ab : ZMod 2 × ZMod 2, chi (ab.1 * ab.2)) = 2 := by
  decide

private lemma sum_chi_quad (p q : ZMod 2) :
    (∑ ab : ZMod 2 × ZMod 2, chi (ab.1 * p + ab.2 * q + ab.1 * ab.2)) = 2 * chi (p * q) := by
  fin_cases p <;> fin_cases q <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

private lemma zmod2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl

/-- Over `ZMod 2`, the quadratic form of a symmetric matrix reduces to its diagonal. -/
private lemma sum_symm_quad {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2))
    (hS : S = Sᵀ) (u : Fin n → ZMod 2) :
    (∑ i : Fin n, ∑ l : Fin n, u i * u l * S i l) = ∑ i : Fin n, u i * S i i := by
  have hS_eq : ∀ i l, S i l = S l i := fun i l => congr_fun (congr_fun hS i) l
  have hsplit : ∀ i : Fin n,
      (∑ l : Fin n, u i * u l * S i l) =
        u i * S i i + ∑ l ∈ univ.filter (· ≠ i), u i * u l * S i l := by
    intro i
    rw [← Finset.add_sum_erase _ _ (mem_univ i)]
    congr 1
    · rw [zmod2_mul_self]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext l; simp [ne_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  suffices hzero : (∑ i : Fin n, ∑ l ∈ univ.filter (· ≠ i), u i * u l * S i l) = 0 by
    rw [hzero, add_zero]
  set E : Finset (Fin n × Fin n) := univ.filter (fun p => p.1 ≠ p.2)
  have hE : (∑ i : Fin n, ∑ l ∈ univ.filter (· ≠ i), u i * u l * S i l) =
      ∑ p ∈ E, u p.1 * u p.2 * S p.1 p.2 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : i = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hE]
  set E1 : Finset (Fin n × Fin n) := univ.filter (fun p => p.1 < p.2)
  set E2 : Finset (Fin n × Fin n) := univ.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint E1 E2 := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1 h2
  have hunion : E = E1 ∪ E2 := by
    ext p
    simp only [E, E1, E2, mem_filter, mem_univ, true_and, mem_union]
    exact ne_iff_lt_or_gt
  have hswap : (∑ p ∈ E2, u p.1 * u p.2 * S p.1 p.2) =
      ∑ p ∈ E1, u p.1 * u p.2 * S p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [E1, E2, mem_filter, mem_univ, true_and] at hp ⊢
      exact hp
    · intro ⟨a, b⟩ _ ⟨c, d⟩ _ h
      cases h; rfl
    · intro p hp
      refine ⟨(p.2, p.1), ?_, by ext <;> rfl⟩
      simp only [E1, E2, mem_filter, mem_univ, true_and] at hp ⊢
      exact hp
    · intro p _
      rw [hS_eq p.1 p.2]
      ring
  rw [hunion, Finset.sum_union hdisj, hswap, zmod2_add_self]

end OMA.P_mo_40662

open OMA.P_mo_40662 in
theorem OMA.solution : type_of% @OMA.S_mo_40662.main := by
  intro n A B C D hM
  have hMT : (fromBlocks A B C D)ᵀ ∈ symplecticGroup (Fin n) (ZMod 2) :=
    SymplecticGroup.transpose_mem hM
  rw [fromBlocks_transpose] at hMT
  obtain ⟨hAB_t, hCD_t, hAD_t⟩ := SymplecticGroup.fromBlocks_mem_iff.mp hMT
  simp only [transpose_transpose] at hAB_t hCD_t hAD_t
  have hAB_symm : A * Bᵀ = (A * Bᵀ)ᵀ := by
    rw [Matrix.transpose_mul, transpose_transpose]; exact hAB_t
  have hCD_symm : C * Dᵀ = (C * Dᵀ)ᵀ := by
    rw [Matrix.transpose_mul, transpose_transpose]; exact hCD_t
  have hAD_plus_BC : A * Dᵀ + B * Cᵀ = 1 := by
    have h1 : -(B * Cᵀ) = B * Cᵀ := by
      ext i j; exact zmod2_neg _
    rw [sub_eq_add_neg, h1] at hAD_t
    exact hAD_t
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) := fromBlocks A B C D
  set MT : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) := Mᵀ
  have hMT_mem : MT ∈ symplecticGroup (Fin n) (ZMod 2) :=
    SymplecticGroup.transpose_mem hM
  set MTinv : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
    (-Matrix.J (Fin n) (ZMod 2)) * MTᵀ * Matrix.J (Fin n) (ZMod 2)
  have hleft : MTinv * MT = 1 := by
    dsimp only [MTinv]
    simpa only [Matrix.neg_mul] using SymplecticGroup.inv_left_mul_aux hMT_mem
  have hright : MT * MTinv = 1 := mul_eq_one_comm.mp hleft
  let pack : (Fin n → ZMod 2 × ZMod 2) ≃ (Fin n ⊕ Fin n → ZMod 2) :=
    { toFun := fun f => Sum.elim (fun i => (f i).1) (fun i => (f i).2)
      invFun := fun v => fun i => (v (Sum.inl i), v (Sum.inr i))
      left_inv := fun f => by ext i <;> rfl
      right_inv := fun v => by ext x; cases x <;> rfl }
  let mulEquiv : (Fin n ⊕ Fin n → ZMod 2) ≃ (Fin n ⊕ Fin n → ZMod 2) :=
    { toFun := fun v => MT.mulVec v
      invFun := fun v => MTinv.mulVec v
      left_inv := fun v => by dsimp only; rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
      right_inv := fun v => by dsimp only; rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec] }
  let e : (Fin n → ZMod 2 × ZMod 2) ≃ (Fin n → ZMod 2 × ZMod 2) :=
    (pack.trans mulEquiv).trans pack.symm
  have hstd : (∑ f : Fin n → ZMod 2 × ZMod 2, chi (∑ j : Fin n, (f j).1 * (f j).2)) =
      (2 : ℤ) ^ n := by
    simp_rw [chi_sum]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (ab : ZMod 2 × ZMod 2) => chi (ab.1 * ab.2))]
    simp only [sum_chi_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hQe : ∀ f : Fin n → ZMod 2 × ZMod 2,
      (∑ j : Fin n, (e f j).1 * (e f j).2) =
        ∑ i : Fin n, ((f i).1 * (A * Bᵀ) i i + (f i).2 * (C * Dᵀ) i i + (f i).1 * (f i).2) := by
    intro f
    set u : Fin n → ZMod 2 := fun i => (f i).1
    set w : Fin n → ZMod 2 := fun i => (f i).2
    have he1 : ∀ j : Fin n, (e f j).1 = ∑ i : Fin n, (u i * A i j + w i * C i j) := by
      intro j
      change (MT.mulVec (Sum.elim u w)) (Sum.inl j) = _
      simp only [MT, M, fromBlocks_transpose, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, transpose_apply, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring
    have he2 : ∀ j : Fin n, (e f j).2 = ∑ l : Fin n, (u l * B l j + w l * D l j) := by
      intro j
      change (MT.mulVec (Sum.elim u w)) (Sum.inr j) = _
      simp only [MT, M, fromBlocks_transpose, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [he1, he2]
    have hexpand :
        (∑ j : Fin n, (∑ i : Fin n, (u i * A i j + w i * C i j)) *
          (∑ l : Fin n, (u l * B l j + w l * D l j))) =
        (∑ i : Fin n, ∑ l : Fin n, u i * u l * (A * Bᵀ) i l) +
        (∑ i : Fin n, ∑ l : Fin n, w i * w l * (C * Dᵀ) i l) +
        (∑ i : Fin n, ∑ l : Fin n, u i * w l * (A * Dᵀ + B * Cᵀ) i l) := by
      have hterm : ∀ j : Fin n,
          (∑ i : Fin n, (u i * A i j + w i * C i j)) *
            (∑ l : Fin n, (u l * B l j + w l * D l j)) =
          (∑ i : Fin n, ∑ l : Fin n, u i * u l * (A i j * B l j)) +
          (∑ i : Fin n, ∑ l : Fin n, w i * w l * (C i j * D l j)) +
          (∑ i : Fin n, ∑ l : Fin n, u i * w l * (A i j * D l j)) +
          (∑ l : Fin n, ∑ i : Fin n, u i * w l * (B i j * C l j)) := by
        intro j
        have hswap :
            (∑ x : Fin n, ∑ y : Fin n, w x * C x j * (u y * B y j)) =
            ∑ y : Fin n, ∑ x : Fin n, u y * w x * (B y j * C x j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
        have h1 : (∑ x : Fin n, ∑ y : Fin n, u x * A x j * (u y * B y j)) =
            ∑ x : Fin n, ∑ y : Fin n, u x * u y * (A x j * B y j) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        have h2 : (∑ x : Fin n, ∑ y : Fin n, w x * C x j * (w y * D y j)) =
            ∑ x : Fin n, ∑ y : Fin n, w x * w y * (C x j * D y j) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        have h3 : (∑ x : Fin n, ∑ y : Fin n, u x * A x j * (w y * D y j)) =
            ∑ x : Fin n, ∑ y : Fin n, u x * w y * (A x j * D y j) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        have hdist : ∀ a b c d : ZMod 2, (a + b) * (c + d) = a * c + b * d + a * d + b * c := by
          intros; ring
        have hlhs :
            (∑ i : Fin n, (u i * A i j + w i * C i j)) *
              (∑ l : Fin n, (u l * B l j + w l * D l j)) =
            (∑ i : Fin n, ∑ l : Fin n, u i * A i j * (u l * B l j)) +
            (∑ i : Fin n, ∑ l : Fin n, w i * C i j * (w l * D l j)) +
            (∑ i : Fin n, ∑ l : Fin n, u i * A i j * (w l * D l j)) +
            (∑ i : Fin n, ∑ l : Fin n, w i * C i j * (u l * B l j)) := by
          simp_rw [Finset.sum_add_distrib]
          rw [hdist]
          simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [hlhs, h1, h2, h3, hswap]
        congr 1
        rw [Finset.sum_comm]
      simp_rw [hterm, Finset.sum_add_distrib]
      have hcomm1 : (∑ j : Fin n, ∑ i : Fin n, ∑ l : Fin n, u i * u l * (A i j * B l j)) =
          ∑ i : Fin n, ∑ l : Fin n, u i * u l * (A * Bᵀ) i l := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.mul_sum, Matrix.mul_apply]
        congr 1
      have hcomm2 : (∑ j : Fin n, ∑ i : Fin n, ∑ l : Fin n, w i * w l * (C i j * D l j)) =
          ∑ i : Fin n, ∑ l : Fin n, w i * w l * (C * Dᵀ) i l := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.mul_sum, Matrix.mul_apply]
        congr 1
      have hcomm3 :
          (∑ j : Fin n, ∑ i : Fin n, ∑ l : Fin n, u i * w l * (A i j * D l j)) +
          (∑ j : Fin n, ∑ l : Fin n, ∑ i : Fin n, u i * w l * (B i j * C l j)) =
          ∑ i : Fin n, ∑ l : Fin n, u i * w l * (A * Dᵀ + B * Cᵀ) i l := by
        have h3a : (∑ j : Fin n, ∑ i : Fin n, ∑ l : Fin n, u i * w l * (A i j * D l j)) =
            ∑ i : Fin n, ∑ l : Fin n, u i * w l * (A * Dᵀ) i l := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum, Matrix.mul_apply]
          congr 1
        have h3b : (∑ j : Fin n, ∑ l : Fin n, ∑ i : Fin n, u i * w l * (B i j * C l j)) =
            ∑ i : Fin n, ∑ l : Fin n, u i * w l * (B * Cᵀ) i l := by
          rw [Finset.sum_comm]
          have h3b' : (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, u i * w l * (B i j * C l j)) =
              ∑ l : Fin n, ∑ i : Fin n, u i * w l * (B * Cᵀ) i l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, Matrix.mul_apply]
            congr 1
          rw [h3b', Finset.sum_comm]
        rw [h3a, h3b, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.add_apply]
        ring
      rw [hcomm1, hcomm2, add_assoc, hcomm3]
    rw [hexpand, sum_symm_quad (A * Bᵀ) hAB_symm u, sum_symm_quad (C * Dᵀ) hCD_symm w,
      hAD_plus_BC]
    have hdiag : (∑ i : Fin n, ∑ l : Fin n, u i * w l * (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i l) =
        ∑ i : Fin n, u i * w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.one_apply]
    rw [hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have htrans : (∑ f : Fin n → ZMod 2 × ZMod 2, chi (∑ j : Fin n, (f j).1 * (f j).2)) =
      (2 : ℤ) ^ n * chi (∑ i : Fin n, (A * Bᵀ) i i * (C * Dᵀ) i i) := by
    rw [← Equiv.sum_comp e]
    simp_rw [hQe, chi_sum]
    rw [← Fintype.prod_sum
      (fun (i : Fin n) (ab : ZMod 2 × ZMod 2) => chi (ab.1 * (A * Bᵀ) i i + ab.2 * (C * Dᵀ) i i + ab.1 * ab.2))]
    simp_rw [sum_chi_quad]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← chi_sum]
  have heq : (2 : ℤ) ^ n * chi (∑ i : Fin n, (A * Bᵀ) i i * (C * Dᵀ) i i) = (2 : ℤ) ^ n * 1 := by
    rw [← htrans, hstd, mul_one]
  have hchi1 : chi (∑ i : Fin n, (A * Bᵀ) i i * (C * Dᵀ) i i) = 1 :=
    mul_left_cancel₀ (by positivity) heq
  have hsum0 : (∑ i : Fin n, (A * Bᵀ) i i * (C * Dᵀ) i i) = 0 :=
    (chi_eq_one_iff _).mp hchi1
  convert hsum0 using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, transpose_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring
