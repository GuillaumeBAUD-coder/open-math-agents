import OMAStatements.S_arxiv_2605_25743
import Mathlib

namespace OMA.P_arxiv_2605_25743

open OMA.S_arxiv_2605_25743

/-! ## Section 1: The 10-weight `S_23`-invariant linear functional `L` -/

/-- Exact integer weight on the multiset of nonzero exponents of a monomial. -/
private def weightOfMs (m : Multiset ℕ) : ℤ :=
  if m = {12} then 8
  else if m = {10, 2} then 8
  else if m = {9, 3} then -8
  else if m = {8, 4} then 8
  else if m = {7, 5} then -8
  else if m = {7, 3, 2} then -8
  else if m = {6, 6} then 8
  else if m = {5, 4, 3} then 4
  else if m = {4, 4, 4} then 8
  else if m = {3, 3, 3, 3} then 1
  else 0

private lemma weightOfMs_eq_zero_of_sum_ne_12 {m : Multiset ℕ} (h : m.sum ≠ 12) :
    weightOfMs m = 0 := by
  unfold weightOfMs
  split_ifs <;> subst_vars <;> simp at h ⊢

private lemma weightOfMs_eq_zero_of_one_mem {m : Multiset ℕ} (h : 1 ∈ m) :
    weightOfMs m = 0 := by
  unfold weightOfMs
  split_ifs <;> subst_vars <;> simp at h ⊢

private lemma weightOfMs_eq_zero_of_card_gt_4 {m : Multiset ℕ} (h : 4 < m.card) :
    weightOfMs m = 0 := by
  unfold weightOfMs
  split_ifs <;> subst_vars <;> simp at h ⊢

/-- Multiset of nonzero entries of an exponent vector `α : Fin 23 →₀ ℕ`. -/
private def nzMs (α : Fin 23 →₀ ℕ) : Multiset ℕ :=
  α.support.val.map α

private lemma nzMs_sum (α : Fin 23 →₀ ℕ) : (nzMs α).sum = α.sum (fun _ k => k) := by
  rw [nzMs, Finsupp.sum, Finset.sum_eq_multiset_sum]

private lemma nzMs_mapDomain (σ : Equiv.Perm (Fin 23)) (α : Fin 23 →₀ ℕ) :
    nzMs (α.mapDomain σ) = nzMs α := by
  unfold nzMs
  have hsupp : (α.mapDomain σ).support = α.support.map σ.toEmbedding := by
    ext i
    simp only [Finsupp.mem_support_iff, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hi
      refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
      rwa [← Finsupp.mapDomain_apply σ.injective α (σ.symm i), σ.apply_symm_apply]
    · rintro ⟨j, hj, rfl⟩
      rwa [Finsupp.mapDomain_apply σ.injective]
  rw [hsupp, Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  exact Finsupp.mapDomain_apply σ.injective α j

private lemma nzMs_add_single_two {α : Fin 23 →₀ ℕ} {v : Fin 23} (hv : α v = 0) :
    nzMs (α + Finsupp.single v 2) = 2 ::ₘ nzMs α := by
  unfold nzMs
  have hv_not : v ∉ α.support := by simp [hv]
  have hsupp : (α + Finsupp.single v 2).support = insert v α.support := by
    ext i
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
    by_cases hi : v = i
    · subst hi; simp [hv]
    · simp [hi, Ne.symm hi]
  rw [hsupp, Finset.insert_val_of_notMem hv_not, Multiset.map_cons]
  have hval : (α + Finsupp.single v 2 : Fin 23 →₀ ℕ) v = 2 := by simp [hv]
  rw [hval]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  have hne : v ≠ i := fun h => hv_not (h ▸ hi)
  simp [hne]

/-- The separating linear functional `L : MvPolynomial (Fin 23) ℝ → ℝ`. -/
private noncomputable def L (f : MvPolynomial (Fin 23) ℝ) : ℝ :=
  ∑ α ∈ f.support, (weightOfMs (nzMs α) : ℝ) * f.coeff α

private lemma L_eq_sum_of_subset {f : MvPolynomial (Fin 23) ℝ} {s : Finset (Fin 23 →₀ ℕ)}
    (hs : f.support ⊆ s) :
    L f = ∑ α ∈ s, (weightOfMs (nzMs α) : ℝ) * f.coeff α := by
  unfold L
  refine Finset.sum_subset hs fun α _ hnot => ?_
  rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]

private lemma L_zero : L 0 = 0 := by simp [L]

private lemma L_add (f g : MvPolynomial (Fin 23) ℝ) : L (f + g) = L f + L g := by
  have hsub : (f + g).support ⊆ f.support ∪ g.support := MvPolynomial.support_add
  rw [L_eq_sum_of_subset hsub, L_eq_sum_of_subset Finset.subset_union_left,
      L_eq_sum_of_subset Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add, mul_add]

private lemma L_C_mul (r : ℝ) (f : MvPolynomial (Fin 23) ℝ) :
    L (MvPolynomial.C r * f) = r * L f := by
  have hsub : (MvPolynomial.C r * f).support ⊆ f.support := by
    intro α hα
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    rw [MvPolynomial.coeff_C_mul] at hα
    exact right_ne_zero_of_mul hα
  rw [L_eq_sum_of_subset hsub]
  unfold L
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_C_mul]; ring

private lemma L_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 23) ℝ) :
    L (∑ i ∈ s, f i) = ∑ i ∈ s, L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, L_add, ih, Finset.sum_insert ha]

private lemma L_monomial (α : Fin 23 →₀ ℕ) (c : ℝ) :
    L (MvPolynomial.monomial α c) = (weightOfMs (nzMs α) : ℝ) * c := by
  by_cases hc : c = 0
  · subst hc; simp [L]
  · unfold L
    rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton, MvPolynomial.coeff_monomial]
    simp

private lemma L_rename (σ : Equiv.Perm (Fin 23)) (f : MvPolynomial (Fin 23) ℝ) :
    L (MvPolynomial.rename σ f) = L f := by
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [MvPolynomial.rename_monomial, L_monomial, L_monomial, nzMs_mapDomain]
  | add p q hp hq =>
      rw [map_add, L_add, L_add, hp, hq]

private lemma L_symSquareGraphPoly (E : List (Fin 23 × Fin 23)) :
    L (symSquareGraphPoly 23 E) =
      (Nat.factorial 23 : ℝ) *
        L ((E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) := by
  unfold symSquareGraphPoly
  rw [L_sum]
  have heach : ∀ σ : Equiv.Perm (Fin 23),
      L ((E.map (fun e => (MvPolynomial.X (σ e.1) - MvPolynomial.X (σ e.2)) ^ 2)).prod) =
      L ((E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) := by
    intro σ
    have hren : (E.map (fun e => (MvPolynomial.X (σ e.1) - MvPolynomial.X (σ e.2) : MvPolynomial (Fin 23) ℝ) ^ 2)).prod =
        MvPolynomial.rename σ ((E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2 : MvPolynomial (Fin 23) ℝ) ^ 2)).prod) := by
      induction E with
      | nil => simp
      | cons e rest ih =>
          simp only [List.map_cons, List.prod_cons, map_mul, map_pow, map_sub, MvPolynomial.rename_X, ih]
    rw [hren, L_rename]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ## Section 2: Pure integer edge evaluator and leaf-collapse reduction -/

private lemma sq_sub_X (u v : Fin 23) :
    (MvPolynomial.X u - MvPolynomial.X v : MvPolynomial (Fin 23) ℝ) ^ 2 =
      MvPolynomial.monomial (Finsupp.single u 2) 1 +
      MvPolynomial.C (-2 : ℝ) * MvPolynomial.monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 +
      MvPolynomial.monomial (Finsupp.single v 2) 1 := by
  have h2u : (MvPolynomial.X u : MvPolynomial (Fin 23) ℝ) ^ 2 =
      MvPolynomial.monomial (Finsupp.single u 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
  have h2v : (MvPolynomial.X v : MvPolynomial (Fin 23) ℝ) ^ 2 =
      MvPolynomial.monomial (Finsupp.single v 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
  have huv : (MvPolynomial.X u : MvPolynomial (Fin 23) ℝ) * MvPolynomial.X v =
      MvPolynomial.monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
  rw [← h2u, ← h2v, ← huv, show MvPolynomial.C (-2 : ℝ) = (-2 : MvPolynomial (Fin 23) ℝ) by
    rw [map_neg, map_ofNat]]
  ring

/-- Pure integer recursive evaluation of `L` on a list of edges with exponent accumulator `α`
and `m2` extra exponent-2 leaves. -/
private noncomputable def evalEdgesM (E : List (Fin 23 × Fin 23)) (α : Fin 23 →₀ ℕ) (m2 : ℕ) : ℤ :=
  match E with
  | [] => weightOfMs (nzMs α + Multiset.replicate m2 2)
  | (u, v) :: rest =>
      evalEdgesM rest (α + Finsupp.single u 2) m2
      - 2 * evalEdgesM rest (α + Finsupp.single u 1 + Finsupp.single v 1) m2
      + evalEdgesM rest (α + Finsupp.single v 2) m2

private lemma L_monomial_mul_prod (E : List (Fin 23 × Fin 23)) :
    ∀ α : Fin 23 →₀ ℕ,
      L (MvPolynomial.monomial α 1 *
          (E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) =
        (evalEdgesM E α 0 : ℝ) := by
  induction E with
  | nil =>
      intro α
      simp [evalEdgesM, L_monomial]
  | cons e rest ih =>
      intro α
      rcases e with ⟨u, v⟩
      simp only [List.map_cons, List.prod_cons, evalEdgesM]
      rw [sq_sub_X u v]
      have hdist : MvPolynomial.monomial α (1 : ℝ) *
          ((MvPolynomial.monomial (Finsupp.single u 2) 1 +
            MvPolynomial.C (-2 : ℝ) * MvPolynomial.monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 +
            MvPolynomial.monomial (Finsupp.single v 2) 1) *
            (rest.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) =
          MvPolynomial.monomial (α + Finsupp.single u 2) 1 *
            (rest.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod +
          MvPolynomial.C (-2 : ℝ) *
            (MvPolynomial.monomial (α + Finsupp.single u 1 + Finsupp.single v 1) 1 *
              (rest.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) +
          MvPolynomial.monomial (α + Finsupp.single v 2) 1 *
            (rest.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod := by
        have h1 : MvPolynomial.monomial α (1 : ℝ) * MvPolynomial.monomial (Finsupp.single u 2) 1 =
            MvPolynomial.monomial (α + Finsupp.single u 2) 1 := by
          rw [MvPolynomial.monomial_mul, mul_one]
        have h2 : MvPolynomial.monomial α (1 : ℝ) *
            MvPolynomial.monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 =
            MvPolynomial.monomial (α + Finsupp.single u 1 + Finsupp.single v 1) 1 := by
          rw [MvPolynomial.monomial_mul, mul_one, add_assoc]
        have h3 : MvPolynomial.monomial α (1 : ℝ) * MvPolynomial.monomial (Finsupp.single v 2) 1 =
            MvPolynomial.monomial (α + Finsupp.single v 2) 1 := by
          rw [MvPolynomial.monomial_mul, mul_one]
        rw [← h1, ← h2, ← h3]; ring
      rw [hdist, L_add, L_add, L_C_mul, ih, ih, ih]
      push_cast; ring

private lemma L_prod_eq_evalEdgesM (E : List (Fin 23 × Fin 23)) :
    L ((E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) =
      (evalEdgesM E 0 0 : ℝ) := by
  have := L_monomial_mul_prod E 0
  have h1 : MvPolynomial.monomial (0 : Fin 23 →₀ ℕ) (1 : ℝ) = 1 := rfl
  rwa [h1, one_mul] at this

private lemma evalEdgesM_eq_zero_of_ne_12 (E : List (Fin 23 × Fin 23)) :
    ∀ (α : Fin 23 →₀ ℕ) (m2 : ℕ),
      α.sum (fun _ k => k) + 2 * m2 + 2 * E.length ≠ 12 →
      evalEdgesM E α m2 = 0 := by
  induction E with
  | nil =>
      intro α m2 hne
      simp only [evalEdgesM, List.length_nil, mul_zero, add_zero] at hne ⊢
      apply weightOfMs_eq_zero_of_sum_ne_12
      rw [Multiset.sum_add, nzMs_sum, Multiset.sum_replicate, smul_eq_mul]
      omega
  | cons e rest ih =>
      intro α m2 hne
      rcases e with ⟨u, v⟩
      simp only [evalEdgesM, List.length_cons] at hne ⊢
      have hsum_add : ∀ (β : Fin 23 →₀ ℕ) (x : Fin 23) (c : ℕ),
          (β + Finsupp.single x c).sum (fun _ k => k) = β.sum (fun _ k => k) + c := by
        intro β x c
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      rw [ih _ m2 (by rw [hsum_add]; omega),
          ih _ m2 (by rw [hsum_add, hsum_add]; omega),
          ih _ m2 (by rw [hsum_add]; omega)]
      ring

private lemma evalEdgesM_swap_head (u v : Fin 23) (rest : List (Fin 23 × Fin 23))
    (α : Fin 23 →₀ ℕ) (m2 : ℕ) :
    evalEdgesM ((u, v) :: rest) α m2 = evalEdgesM ((v, u) :: rest) α m2 := by
  simp only [evalEdgesM]
  have h : α + Finsupp.single u 1 + Finsupp.single v 1 =
      α + Finsupp.single v 1 + Finsupp.single u 1 := by
    rw [add_assoc, add_comm (Finsupp.single u 1), ← add_assoc]
  rw [h]; ring

private lemma evalEdgesM_perm {E1 E2 : List (Fin 23 × Fin 23)} (hp : E1.Perm E2) :
    ∀ (α : Fin 23 →₀ ℕ) (m2 : ℕ), evalEdgesM E1 α m2 = evalEdgesM E2 α m2 := by
  induction hp with
  | nil => intro _ _; rfl
  | cons e _ ih =>
      intro α m2
      rcases e with ⟨u, v⟩
      simp only [evalEdgesM, ih]
  | swap e1 e2 rest =>
      intro α m2
      rcases e1 with ⟨u1, v1⟩
      rcases e2 with ⟨u2, v2⟩
      simp only [evalEdgesM]
      have hcomm : ∀ (a b : Fin 23 →₀ ℕ), α + a + b = α + b + a := fun _ _ => by ac_rfl
      have hcomm3a : ∀ (a b c : Fin 23 →₀ ℕ), α + a + b + c = α + b + c + a := fun _ _ _ => by ac_rfl
      have hcomm3b : ∀ (a b c : Fin 23 →₀ ℕ), α + a + b + c = α + c + a + b := fun _ _ _ => by ac_rfl
      have hcomm4 : ∀ (a b c d : Fin 23 →₀ ℕ),
          α + a + b + c + d = α + c + d + a + b := fun _ _ _ _ => by ac_rfl
      rw [hcomm (Finsupp.single u2 2) (Finsupp.single u1 2),
          hcomm3a (Finsupp.single u2 2) (Finsupp.single u1 1) (Finsupp.single v1 1),
          hcomm (Finsupp.single u2 2) (Finsupp.single v1 2),
          hcomm3b (Finsupp.single u2 1) (Finsupp.single v2 1) (Finsupp.single u1 2),
          hcomm4 (Finsupp.single u2 1) (Finsupp.single v2 1) (Finsupp.single u1 1) (Finsupp.single v1 1),
          hcomm3b (Finsupp.single u2 1) (Finsupp.single v2 1) (Finsupp.single v1 2),
          hcomm (Finsupp.single v2 2) (Finsupp.single u1 2),
          hcomm3a (Finsupp.single v2 2) (Finsupp.single u1 1) (Finsupp.single v1 1),
          hcomm (Finsupp.single v2 2) (Finsupp.single v1 2)]
      ring
  | trans _ _ ih1 ih2 => intro α m2; rw [ih1, ih2]

private lemma evalEdgesM_loop (u : Fin 23) (rest : List (Fin 23 × Fin 23))
    (α : Fin 23 →₀ ℕ) (m2 : ℕ) :
    evalEdgesM ((u, u) :: rest) α m2 = 0 := by
  simp only [evalEdgesM]
  have h : α + Finsupp.single u 1 + Finsupp.single u 1 = α + Finsupp.single u 2 := by
    rw [add_assoc, ← Finsupp.single_add]
  rw [h]; ring

private lemma evalEdgesM_leaf_one (v : Fin 23) (E : List (Fin 23 × Fin 23))
    (hnot : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    ∀ (α : Fin 23 →₀ ℕ) (m2 : ℕ), α v = 1 → evalEdgesM E α m2 = 0 := by
  induction E with
  | nil =>
      intro α m2 hv
      simp only [evalEdgesM]
      apply weightOfMs_eq_zero_of_one_mem
      apply Multiset.mem_add.mpr; left
      unfold nzMs
      exact Multiset.mem_map.mpr ⟨v, by simp [hv], hv⟩
  | cons e rest ih =>
      intro α m2 hv
      rcases e with ⟨a, b⟩
      have hab := hnot (a, b) (List.mem_cons_self ..)
      have hrest : ∀ e' ∈ rest, e'.1 ≠ v ∧ e'.2 ≠ v := fun e' he' =>
        hnot e' (List.mem_cons_of_mem _ he')
      simp only [evalEdgesM]
      rw [ih hrest _ m2 (by simp [hv, hab.1]),
          ih hrest _ m2 (by simp [hv, hab.1, hab.2]),
          ih hrest _ m2 (by simp [hv, hab.2])]
      ring

private lemma evalEdgesM_leaf_two (v : Fin 23) (E : List (Fin 23 × Fin 23))
    (hnot : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    ∀ (α : Fin 23 →₀ ℕ) (m2 : ℕ), α v = 0 →
      evalEdgesM E (α + Finsupp.single v 2) m2 = evalEdgesM E α (m2 + 1) := by
  induction E with
  | nil =>
      intro α m2 hv
      simp only [evalEdgesM]
      rw [nzMs_add_single_two hv, Multiset.replicate_succ, Multiset.cons_add, Multiset.add_cons]
  | cons e rest ih =>
      intro α m2 hv
      rcases e with ⟨a, b⟩
      have hab := hnot (a, b) (List.mem_cons_self ..)
      have hrest : ∀ e' ∈ rest, e'.1 ≠ v ∧ e'.2 ≠ v := fun e' he' =>
        hnot e' (List.mem_cons_of_mem _ he')
      simp only [evalEdgesM]
      have h1 : α + Finsupp.single v 2 + Finsupp.single a 2 =
          (α + Finsupp.single a 2) + Finsupp.single v 2 := by ac_rfl
      have h2 : α + Finsupp.single v 2 + Finsupp.single a 1 + Finsupp.single b 1 =
          (α + Finsupp.single a 1 + Finsupp.single b 1) + Finsupp.single v 2 := by ac_rfl
      have h3 : α + Finsupp.single v 2 + Finsupp.single b 2 =
          (α + Finsupp.single b 2) + Finsupp.single v 2 := by ac_rfl
      rw [h1, h2, h3,
          ih hrest _ m2 (by simp [hv, hab.1]),
          ih hrest _ m2 (by simp [hv, hab.1, hab.2]),
          ih hrest _ m2 (by simp [hv, hab.2])]

private lemma evalEdgesM_pend (u v : Fin 23) (rest : List (Fin 23 × Fin 23))
    (hne : u ≠ v) (hnot : ∀ e ∈ rest, e.1 ≠ v ∧ e.2 ≠ v)
    (α : Fin 23 →₀ ℕ) (m2 : ℕ) (hv : α v = 0) :
    evalEdgesM ((u, v) :: rest) α m2 =
      evalEdgesM rest (α + Finsupp.single u 2) m2 + evalEdgesM rest α (m2 + 1) := by
  simp only [evalEdgesM]
  have hmid : evalEdgesM rest (α + Finsupp.single u 1 + Finsupp.single v 1) m2 = 0 :=
    evalEdgesM_leaf_one v rest hnot _ m2 (by simp [hv, hne])
  rw [hmid, evalEdgesM_leaf_two v rest hnot α m2 hv]
  ring

private lemma evalEdgesM_iso (u v : Fin 23) (rest : List (Fin 23 × Fin 23))
    (hne : u ≠ v)
    (hnot_u : ∀ e ∈ rest, e.1 ≠ u ∧ e.2 ≠ u)
    (hnot_v : ∀ e ∈ rest, e.1 ≠ v ∧ e.2 ≠ v)
    (α : Fin 23 →₀ ℕ) (m2 : ℕ) (hu : α u = 0) (hv : α v = 0) :
    evalEdgesM ((u, v) :: rest) α m2 = 2 * evalEdgesM rest α (m2 + 1) := by
  rw [evalEdgesM_pend u v rest hne hnot_v α m2 hv, evalEdgesM_leaf_two u rest hnot_u α m2 hu]
  ring

/-! ## Section 3: Pure computable `Fin 6` evaluator and exhaustive verification of all 778 configs -/

private def insDesc (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insDesc x ys

private def sortDescList : List ℕ → List ℕ
  | [] => []
  | x :: xs => insDesc x (sortDescList xs)

private lemma insDesc_perm (x : ℕ) (l : List ℕ) : (insDesc x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [insDesc]
      split_ifs
      · exact List.Perm.refl _
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

private lemma sortDescList_perm (l : List ℕ) : (sortDescList l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insDesc_perm x _).trans (List.Perm.cons x ih)

private lemma insDesc_pairwise (x : ℕ) {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) :
    (insDesc x l).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [insDesc]
  | cons y ys ih =>
      simp only [insDesc]
      split_ifs with hxy
      · refine List.pairwise_cons.mpr ⟨?_, hl⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hxy
        · exact le_trans ((List.pairwise_cons.mp hl).1 z hz') hxy
      · refine List.pairwise_cons.mpr ⟨?_, ih (List.pairwise_cons.mp hl).2⟩
        intro z hz
        have hmem : z ∈ x :: ys := (insDesc_perm x ys).subset hz
        rcases List.mem_cons.mp hmem with rfl | hz'
        · omega
        · exact (List.pairwise_cons.mp hl).1 z hz'

private lemma sortDescList_pairwise (l : List ℕ) : (sortDescList l).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [sortDescList]
  | cons x xs ih => exact insDesc_pairwise x ih

private def weightOfSorted (l : List ℕ) : ℤ :=
  if l = [12] then 8
  else if l = [10, 2] then 8
  else if l = [9, 3] then -8
  else if l = [8, 4] then 8
  else if l = [7, 5] then -8
  else if l = [7, 3, 2] then -8
  else if l = [6, 6] then 8
  else if l = [5, 4, 3] then 4
  else if l = [4, 4, 4] then 8
  else if l = [3, 3, 3, 3] then 1
  else 0

private lemma sorted_eq_of_perm {l1 l2 : List ℕ}
    (hp : l1.Perm l2) (h1 : l1.Pairwise (· ≥ ·)) (h2 : l2.Pairwise (· ≥ ·)) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => exact hp.nil_eq
  | cons a as ih =>
      cases l2 with
      | nil => exact absurd hp.symm.nil_eq (by simp)
      | cons b bs =>
          have ha_mem : a ∈ b :: bs := hp.subset (List.mem_cons_self ..)
          have hb_mem : b ∈ a :: as := hp.symm.subset (List.mem_cons_self ..)
          have hab : a = b := by
            have hle1 : a ≤ b := by
              rcases List.mem_cons.mp ha_mem with rfl | h
              · exact le_rfl
              · exact (List.pairwise_cons.mp h2).1 a h
            have hle2 : b ≤ a := by
              rcases List.mem_cons.mp hb_mem with rfl | h
              · exact le_rfl
              · exact (List.pairwise_cons.mp h1).1 b h
            omega
          subst hab
          congr 1
          exact ih (hp.cons_inv) (List.pairwise_cons.mp h1).2 (List.pairwise_cons.mp h2).2

private lemma weightOfSorted_eq_weightOfMs (l : List ℕ) :
    weightOfSorted (sortDescList l) = weightOfMs (l : Multiset ℕ) := by
  have hp := sortDescList_perm l
  have hpw := sortDescList_pairwise l
  have hms : ((sortDescList l : List ℕ) : Multiset ℕ) = (l : Multiset ℕ) :=
    Quotient.sound hp
  rw [← hms]
  set s := sortDescList l
  have hiff : ∀ t : List ℕ, t.Pairwise (· ≥ ·) →
      ((s : Multiset ℕ) = (t : Multiset ℕ) ↔ s = t) := fun t ht =>
    ⟨fun h => sorted_eq_of_perm (Quotient.exact h) hpw ht, fun h => by rw [h]⟩
  unfold weightOfMs
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · rw [(hiff [12] (by decide)).mp h1]; rfl
  · rw [(hiff [10, 2] (by decide)).mp h2]; rfl
  · rw [(hiff [9, 3] (by decide)).mp h3]; rfl
  · rw [(hiff [8, 4] (by decide)).mp h4]; rfl
  · rw [(hiff [7, 5] (by decide)).mp h5]; rfl
  · rw [(hiff [7, 3, 2] (by decide)).mp h6]; rfl
  · rw [(hiff [6, 6] (by decide)).mp h7]; rfl
  · rw [(hiff [5, 4, 3] (by decide)).mp h8]; rfl
  · rw [(hiff [4, 4, 4] (by decide)).mp h9]; rfl
  · rw [(hiff [3, 3, 3, 3] (by decide)).mp h10]; rfl
  · unfold weightOfSorted
    have hneq : ∀ t : List ℕ, (s : Multiset ℕ) ≠ (t : Multiset ℕ) → s ≠ t := fun t ht h => ht (by rw [h])
    rw [if_neg (hneq [12] h1), if_neg (hneq [10, 2] h2), if_neg (hneq [9, 3] h3),
        if_neg (hneq [8, 4] h4), if_neg (hneq [7, 5] h5), if_neg (hneq [7, 3, 2] h6),
        if_neg (hneq [6, 6] h7), if_neg (hneq [5, 4, 3] h8), if_neg (hneq [4, 4, 4] h9),
        if_neg (hneq [3, 3, 3, 3] h10)]

/-- Pure computable weight on 6 vertex exponents `(a0..a5)` plus `m2` extra exponent-2 leaves. -/
private def weight6 (a0 a1 a2 a3 a4 a5 m2 : ℕ) : ℤ :=
  let l := ([a0, a1, a2, a3, a4, a5].filter (· != 0)) ++ List.replicate m2 2
  weightOfSorted (sortDescList l)

private def nzCount6 (a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  (if a0 = 0 then 0 else 1) + (if a1 = 0 then 0 else 1) +
  (if a2 = 0 then 0 else 1) + (if a3 = 0 then 0 else 1) +
  (if a4 = 0 then 0 else 1) + (if a5 = 0 then 0 else 1)

private def addAt6 (u : Fin 6) (d : ℕ) (a0 a1 a2 a3 a4 a5 : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match u.val with
  | 0 => (a0 + d, a1, a2, a3, a4, a5)
  | 1 => (a0, a1 + d, a2, a3, a4, a5)
  | 2 => (a0, a1, a2 + d, a3, a4, a5)
  | 3 => (a0, a1, a2, a3 + d, a4, a5)
  | 4 => (a0, a1, a2, a3, a4 + d, a5)
  | _ => (a0, a1, a2, a3, a4, a5 + d)

/-- Fast structurally recursive evaluator on `intEdges` over `Fin 6` with early `> 4` pruning. -/
private def evalFastInt : List (Fin 6 × Fin 6) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ
  | [], a0, a1, a2, a3, a4, a5, m2 =>
      if 4 < nzCount6 a0 a1 a2 a3 a4 a5 + m2 then 0
      else weight6 a0 a1 a2 a3 a4 a5 m2
  | (u, v) :: rest, a0, a1, a2, a3, a4, a5, m2 =>
      if 4 < nzCount6 a0 a1 a2 a3 a4 a5 + m2 then 0
      else
        let (b0, b1, b2, b3, b4, b5) := addAt6 u 2 a0 a1 a2 a3 a4 a5
        let (c0, c1, c2, c3, c4, c5) := addAt6 u 1 a0 a1 a2 a3 a4 a5
        let (d0, d1, d2, d3, d4, d5) := addAt6 v 1 c0 c1 c2 c3 c4 c5
        let (e0, e1, e2, e3, e4, e5) := addAt6 v 2 a0 a1 a2 a3 a4 a5
        evalFastInt rest b0 b1 b2 b3 b4 b5 m2 -
        2 * evalFastInt rest d0 d1 d2 d3 d4 d5 m2 +
        evalFastInt rest e0 e1 e2 e3 e4 e5 m2

/-- Fast structurally recursive evaluator on `(intEdges, pends)` over `Fin 6` with early `> 4` pruning. -/
private def evalFast (ie : List (Fin 6 × Fin 6)) :
    List (Fin 6) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ
  | [], a0, a1, a2, a3, a4, a5, m2 => evalFastInt ie a0 a1 a2 a3 a4 a5 m2
  | u :: rest, a0, a1, a2, a3, a4, a5, m2 =>
      if 4 < nzCount6 a0 a1 a2 a3 a4 a5 + m2 then 0
      else
        let (b0, b1, b2, b3, b4, b5) := addAt6 u 2 a0 a1 a2 a3 a4 a5
        evalFast ie rest b0 b1 b2 b3 b4 b5 m2 +
        evalFast ie rest a0 a1 a2 a3 a4 a5 (m2 + 1)

/-- Unpruned semantic version of `evalFast` on `Fin 6 → ℕ` for clean bridging to `evalEdgesM`. -/
private def evalSem6 (ie : List (Fin 6 × Fin 6)) (pe : List (Fin 6))
    (a : Fin 6 → ℕ) (m2 : ℕ) : ℤ :=
  match pe with
  | u :: rest =>
      evalSem6 ie rest (Function.update a u (a u + 2)) m2 +
      evalSem6 ie rest a (m2 + 1)
  | [] =>
      match ie with
      | [] => weightOfMs ((((List.finRange 6).map a).filter (· ≠ 0) : Multiset ℕ) +
                            Multiset.replicate m2 2)
      | (u, v) :: rest =>
          evalSem6 rest [] (Function.update a u (a u + 2)) m2 -
          2 * evalSem6 rest []
                (Function.update (Function.update a u (a u + 1)) v
                  ((Function.update a u (a u + 1)) v + 1)) m2 +
          evalSem6 rest [] (Function.update a v (a v + 2)) m2

private lemma nzCount6_eq (a : Fin 6 → ℕ) :
    nzCount6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) =
      (((List.finRange 6).map a).filter (· ≠ 0)).length := by
  have h : ∀ l : List ℕ, (l.filter (· ≠ 0)).length = (l.map fun x => if x = 0 then 0 else 1).sum := by
    intro l; induction l with
    | nil => simp
    | cons x xs ih =>
        rw [List.filter_cons, List.map_cons, List.sum_cons]
        by_cases hx : x = 0
        · rw [if_pos hx, decide_eq_false (not_not.mpr hx)]
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add, ih]
        · rw [if_neg hx, decide_eq_true hx]
          simp only [↓reduceIte, List.length_cons, ih]; omega
  rw [h, List.map_map]
  have hfin : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [hfin]
  simp only [List.map_cons, List.map_nil, Function.comp_apply, List.sum_cons, List.sum_nil,
    add_zero, nzCount6]
  omega

private lemma nzCount6_mono_update (a : Fin 6 → ℕ) (u : Fin 6) (d : ℕ) :
    nzCount6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) ≤
      nzCount6 (Function.update a u (a u + d) 0) (Function.update a u (a u + d) 1)
        (Function.update a u (a u + d) 2) (Function.update a u (a u + d) 3)
        (Function.update a u (a u + d) 4) (Function.update a u (a u + d) 5) := by
  have h1 : ∀ x : ℕ, (if x = 0 then 0 else 1) ≤ (if x + d = 0 then 0 else 1) := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  have hpt : ∀ i : Fin 6,
      (if a i = 0 then 0 else 1) ≤ (if Function.update a u (a u + d) i = 0 then 0 else 1) := by
    intro i
    by_cases hi : i = u
    · subst hi; rw [Function.update_self]; exact h1 (a i)
    · rw [Function.update_of_ne hi]
  unfold nzCount6
  linarith [hpt 0, hpt 1, hpt 2, hpt 3, hpt 4, hpt 5]

private lemma evalSem6_eq_zero_of_gt4 (ie : List (Fin 6 × Fin 6)) (pe : List (Fin 6)) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ),
      4 < nzCount6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) + m2 →
      evalSem6 ie pe a m2 = 0 := by
  induction pe with
  | cons u rest ih =>
      intro a m2 hgt
      simp only [evalSem6]
      have hm := nzCount6_mono_update a u 2
      rw [ih _ m2 (by omega), ih a (m2 + 1) (by omega)]; ring
  | nil =>
      induction ie with
      | nil =>
          intro a m2 hgt
          simp only [evalSem6]
          apply weightOfMs_eq_zero_of_card_gt_4
          rw [Multiset.card_add, Multiset.coe_card, Multiset.card_replicate, ← nzCount6_eq]
          exact hgt
      | cons e rest ih =>
          intro a m2 hgt
          rcases e with ⟨u, v⟩
          simp only [evalSem6]
          have hm1 := nzCount6_mono_update a u 2
          have hm2a := nzCount6_mono_update a u 1
          have hm2b := nzCount6_mono_update (Function.update a u (a u + 1)) v 1
          have hm3 := nzCount6_mono_update a v 2
          rw [ih _ m2 (by omega), ih _ m2 (by omega), ih _ m2 (by omega)]; ring

private lemma addAt6_eq (u : Fin 6) (d : ℕ) (a : Fin 6 → ℕ) :
    addAt6 u d (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) =
      (Function.update a u (a u + d) 0, Function.update a u (a u + d) 1,
       Function.update a u (a u + d) 2, Function.update a u (a u + d) 3,
       Function.update a u (a u + d) 4, Function.update a u (a u + d) 5) := by
  fin_cases u <;> simp [addAt6, Function.update]

private lemma weight6_eq_sem (a : Fin 6 → ℕ) (m2 : ℕ) :
    weight6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) m2 =
      weightOfMs ((((List.finRange 6).map a).filter (· ≠ 0) : Multiset ℕ) +
                    Multiset.replicate m2 2) := by
  unfold weight6
  rw [weightOfSorted_eq_weightOfMs]
  congr 1
  have h1 : ([a 0, a 1, a 2, a 3, a 4, a 5].filter (· != 0)) =
      ((List.finRange 6).map a).filter (· ≠ 0) := by
    have hfin : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
    have hpred : (fun x : ℕ => x != 0) = (fun x : ℕ => decide (x ≠ 0)) := by
      funext x; by_cases hx : x = 0 <;> simp [hx]
    rw [hfin, hpred]
    rfl
  rw [h1, ← Multiset.coe_add, Multiset.coe_replicate]

private lemma evalFastInt_eq_evalSem6 (ie : List (Fin 6 × Fin 6)) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ),
      evalFastInt ie (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) m2 = evalSem6 ie [] a m2 := by
  induction ie with
  | nil =>
      intro a m2
      unfold evalFastInt
      split_ifs with hgt
      · exact (evalSem6_eq_zero_of_gt4 [] [] a m2 hgt).symm
      · unfold evalSem6; exact weight6_eq_sem a m2
  | cons e rest ih =>
      intro a m2
      rcases e with ⟨u, v⟩
      unfold evalFastInt
      split_ifs with hgt
      · exact (evalSem6_eq_zero_of_gt4 ((u, v) :: rest) [] a m2 hgt).symm
      · simp only [addAt6_eq, evalSem6, ih]

private lemma evalFast_eq_evalSem6 (ie : List (Fin 6 × Fin 6)) (pe : List (Fin 6)) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ),
      evalFast ie pe (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) m2 = evalSem6 ie pe a m2 := by
  induction pe with
  | nil =>
      intro a m2
      exact evalFastInt_eq_evalSem6 ie a m2
  | cons u rest ih =>
      intro a m2
      unfold evalFast
      split_ifs with hgt
      · exact (evalSem6_eq_zero_of_gt4 ie (u :: rest) a m2 hgt).symm
      · simp only [addAt6_eq, evalSem6, ih]

private lemma evalSem6_perm_pe {ie : List (Fin 6 × Fin 6)} {p1 p2 : List (Fin 6)} (hp : p1.Perm p2) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ), evalSem6 ie p1 a m2 = evalSem6 ie p2 a m2 := by
  induction hp with
  | nil => intro _ _; rfl
  | cons u _ ih => intro a m2; simp only [evalSem6, ih]
  | swap u v rest =>
      intro a m2
      simp only [evalSem6]
      have hupd : Function.update (Function.update a v (a v + 2)) u
            ((Function.update a v (a v + 2)) u + 2) =
          Function.update (Function.update a u (a u + 2)) v
            ((Function.update a u (a u + 2)) v + 2) := by
        funext x
        by_cases hxu : x = u <;> by_cases hxv : x = v <;> simp_all [Function.update]
      rw [hupd]; ring
  | trans _ _ ih1 ih2 => intro a m2; rw [ih1, ih2]

private lemma evalSem6_swap_ie (u v : Fin 6) (rest : List (Fin 6 × Fin 6))
    (a : Fin 6 → ℕ) (m2 : ℕ) :
    evalSem6 ((u, v) :: rest) [] a m2 = evalSem6 ((v, u) :: rest) [] a m2 := by
  simp only [evalSem6]
  have hupd : Function.update (Function.update a u (a u + 1)) v
        ((Function.update a u (a u + 1)) v + 1) =
      Function.update (Function.update a v (a v + 1)) u
        ((Function.update a v (a v + 1)) u + 1) := by
    funext x
    by_cases hxu : x = u <;> by_cases hxv : x = v <;> simp_all [Function.update]
  rw [hupd]; ring

private lemma evalSem6_perm_ie {i1 i2 : List (Fin 6 × Fin 6)} (hp : i1.Perm i2) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ), evalSem6 i1 [] a m2 = evalSem6 i2 [] a m2 := by
  have hcomm2 : ∀ (a : Fin 6 → ℕ) (x y : Fin 6) (dx dy : ℕ),
      Function.update (Function.update a x (a x + dx)) y
        ((Function.update a x (a x + dx)) y + dy) =
      Function.update (Function.update a y (a y + dy)) x
        ((Function.update a y (a y + dy)) x + dx) := by
    intro a x y dx dy
    funext z
    by_cases hzx : z = x <;> by_cases hzy : z = y
    · subst hzx; subst hzy; simp [Function.update]; omega
    · subst hzx; simp [Function.update, hzy]
    · subst hzy; simp [Function.update, hzx]
    · simp [Function.update, hzx, hzy]
  induction hp with
  | nil => intro _ _; rfl
  | cons e _ ih =>
      intro a m2; rcases e with ⟨u, v⟩; simp only [evalSem6, ih]
  | swap e1 e2 rest =>
      intro a m2
      rcases e1 with ⟨u1, v1⟩; rcases e2 with ⟨u2, v2⟩
      simp only [evalSem6]
      have h11 := hcomm2 a u2 u1 2 2
      have h12 : Function.update (Function.update (Function.update a u2 (a u2 + 2)) u1
            ((Function.update a u2 (a u2 + 2)) u1 + 1)) v1
            ((Function.update (Function.update a u2 (a u2 + 2)) u1
              ((Function.update a u2 (a u2 + 2)) u1 + 1)) v1 + 1) =
          Function.update (Function.update (Function.update a u1 (a u1 + 1)) v1
            ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2
            ((Function.update (Function.update a u1 (a u1 + 1)) v1
              ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2 + 2) := by
        rw [hcomm2 a u2 u1 2 1, hcomm2 _ u2 v1 2 1]
      have h13 := hcomm2 a u2 v1 2 2
      have h21 : Function.update (Function.update (Function.update a u2 (a u2 + 1)) v2
            ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1
            ((Function.update (Function.update a u2 (a u2 + 1)) v2
              ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1 + 2) =
          Function.update (Function.update (Function.update a u1 (a u1 + 2)) u2
            ((Function.update a u1 (a u1 + 2)) u2 + 1)) v2
            ((Function.update (Function.update a u1 (a u1 + 2)) u2
              ((Function.update a u1 (a u1 + 2)) u2 + 1)) v2 + 1) := by
        rw [hcomm2 a u1 u2 2 1, hcomm2 _ u1 v2 2 1]
      have h22 : Function.update (Function.update (Function.update (Function.update a u2 (a u2 + 1)) v2
            ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1
            ((Function.update (Function.update a u2 (a u2 + 1)) v2
              ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1 + 1)) v1
            ((Function.update (Function.update (Function.update a u2 (a u2 + 1)) v2
              ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1
              ((Function.update (Function.update a u2 (a u2 + 1)) v2
                ((Function.update a u2 (a u2 + 1)) v2 + 1)) u1 + 1)) v1 + 1) =
          Function.update (Function.update (Function.update (Function.update a u1 (a u1 + 1)) v1
            ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2
            ((Function.update (Function.update a u1 (a u1 + 1)) v1
              ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2 + 1)) v2
            ((Function.update (Function.update (Function.update a u1 (a u1 + 1)) v1
              ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2
              ((Function.update (Function.update a u1 (a u1 + 1)) v1
                ((Function.update a u1 (a u1 + 1)) v1 + 1)) u2 + 1)) v2 + 1) := by
        rw [hcomm2 (Function.update a u2 (a u2 + 1)) v2 u1 1 1,
            hcomm2 a u2 u1 1 1,
            hcomm2 _ v2 v1 1 1,
            hcomm2 (Function.update a u1 (a u1 + 1)) u2 v1 1 1]
      have h23 : Function.update (Function.update (Function.update a u2 (a u2 + 1)) v2
            ((Function.update a u2 (a u2 + 1)) v2 + 1)) v1
            ((Function.update (Function.update a u2 (a u2 + 1)) v2
              ((Function.update a u2 (a u2 + 1)) v2 + 1)) v1 + 2) =
          Function.update (Function.update (Function.update a v1 (a v1 + 2)) u2
            ((Function.update a v1 (a v1 + 2)) u2 + 1)) v2
            ((Function.update (Function.update a v1 (a v1 + 2)) u2
              ((Function.update a v1 (a v1 + 2)) u2 + 1)) v2 + 1) := by
        rw [hcomm2 a v1 u2 2 1, hcomm2 _ v1 v2 2 1]
      have h31 := hcomm2 a v2 u1 2 2
      have h32 : Function.update (Function.update (Function.update a v2 (a v2 + 2)) u1
            ((Function.update a v2 (a v2 + 2)) u1 + 1)) v1
            ((Function.update (Function.update a v2 (a v2 + 2)) u1
              ((Function.update a v2 (a v2 + 2)) u1 + 1)) v1 + 1) =
          Function.update (Function.update (Function.update a u1 (a u1 + 1)) v1
            ((Function.update a u1 (a u1 + 1)) v1 + 1)) v2
            ((Function.update (Function.update a u1 (a u1 + 1)) v1
              ((Function.update a u1 (a u1 + 1)) v1 + 1)) v2 + 2) := by
        rw [hcomm2 a v2 u1 2 1, hcomm2 _ v2 v1 2 1]
      have h33 := hcomm2 a v2 v1 2 2
      rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]; ring
  | trans _ _ ih1 ih2 => intro a m2; rw [ih1, ih2]

private lemma evalSem6_perm_ie_general {i1 i2 : List (Fin 6 × Fin 6)} (hp : i1.Perm i2)
    (pe : List (Fin 6)) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ), evalSem6 i1 pe a m2 = evalSem6 i2 pe a m2 := by
  induction pe with
  | nil => exact evalSem6_perm_ie hp
  | cons u rest ih => intro a m2; simp only [evalSem6, ih]

private lemma evalSem6_orient_ie (ie : List (Fin 6 × Fin 6)) (pe : List (Fin 6)) :
    ∀ (a : Fin 6 → ℕ) (m2 : ℕ),
      evalSem6 ie pe a m2 =
        evalSem6 (ie.map fun e => if e.1 ≤ e.2 then e else (e.2, e.1)) pe a m2 := by
  induction pe with
  | cons u rest ih => intro a m2; simp only [evalSem6, ih]
  | nil =>
      induction ie with
      | nil => intro _ _; rfl
      | cons e rest ih =>
          intro a m2
          rcases e with ⟨u, v⟩
          simp only [List.map_cons]
          split_ifs
          · simp only [evalSem6, ih]
          · rw [evalSem6_swap_ie u v rest]
            simp only [evalSem6, ih]

/-- Structurally recursive generator for all descending partitions of `S` with parts in `2..maxP`. -/
private def parts2to6Aux : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, 0, _ => [[]]
  | fuel + 1, S + 1, maxP =>
      let hi := min (S + 1) maxP
      (List.range (hi + 1)).reverse.flatMap fun p =>
        if 2 ≤ p then (parts2to6Aux fuel (S + 1 - p) p).map (p :: ·) else []

private def parts2to6 (S maxP : ℕ) : List (List ℕ) :=
  parts2to6Aux (S + 1) S maxP

private lemma mem_parts2to6Aux :
    ∀ (d : List ℕ) (fuel S maxP : ℕ),
      S < fuel → d.sum = S → (∀ x ∈ d, 2 ≤ x ∧ x ≤ maxP) → d.Pairwise (· ≥ ·) →
      d ∈ parts2to6Aux fuel S maxP := by
  intro d
  induction d with
  | nil =>
      intro fuel S maxP hfuel hsum _ _
      simp only [List.sum_nil] at hsum; subst hsum
      cases fuel with
      | zero => omega
      | succ f => simp [parts2to6Aux]
  | cons p rest ih =>
      intro fuel S maxP hfuel hsum hmem hpw
      simp only [List.sum_cons] at hsum
      have hp := hmem p (List.mem_cons_self ..)
      obtain ⟨S', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S ≠ 0)
      obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      simp only [parts2to6Aux, List.mem_flatMap, List.mem_reverse, List.mem_range]
      refine ⟨p, by omega, ?_⟩
      rw [if_pos hp.1, List.mem_map]
      refine ⟨rest, ih f' (S' + 1 - p) p (by omega) (by omega) ?_ (List.pairwise_cons.mp hpw).2, rfl⟩
      intro x hx
      exact ⟨(hmem x (List.mem_cons_of_mem _ hx)).1, (List.pairwise_cons.mp hpw).1 x hx⟩

private lemma mem_parts2to6 (d : List ℕ) (S maxP : ℕ)
    (hsum : d.sum = S) (hmem : ∀ x ∈ d, 2 ≤ x ∧ x ≤ maxP) (hpw : d.Pairwise (· ≥ ·)) :
    d ∈ parts2to6 S maxP :=
  mem_parts2to6Aux d (S + 1) S maxP (Nat.lt_succ_self S) hsum hmem hpw

private def pairs6 : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (2, 5),
   (3, 4), (3, 5),
   (4, 5)]

private def setAt6 (u : Fin 6) (v : ℕ) (r : Fin 6 → ℕ) : Fin 6 → ℕ :=
  Function.update r u v

private def pendsFromRem (r : Fin 6 → ℕ) : List (Fin 6) :=
  (List.finRange 6).flatMap fun u => List.replicate (r u) u

/-- Given remaining degrees `r : Fin 6 → ℕ`, remaining pair list `ps`, and edge budget `eLeft`,
generate all canonical `(intEdges, pends, iso)` tuples. -/
private def genFromPairs :
    List (Fin 6 × Fin 6) → (Fin 6 → ℕ) → ℕ → List (List (Fin 6 × Fin 6) × List (Fin 6) × ℕ)
  | [], r, eLeft =>
      let ePend := r 0 + r 1 + r 2 + r 3 + r 4 + r 5
      if ePend ≤ eLeft then [([], pendsFromRem r, eLeft - ePend)] else []
  | (u, v) :: ps, r, eLeft =>
      let mx := min (min (r u) (r v)) eLeft
      (List.range (mx + 1)).flatMap fun m =>
        let r' := Function.update (Function.update r u (r u - m)) v (r v - m)
        (genFromPairs ps r' (eLeft - m)).map fun (ie, pe, iso) =>
          (List.replicate m (u, v) ++ ie, pe, iso)

private def degFnFromList (d : List ℕ) : Fin 6 → ℕ :=
  fun u => d.getD u.val 0

private def configsOfD (d : List ℕ) : List (List (Fin 6 × Fin 6) × List (Fin 6) × ℕ) :=
  genFromPairs pairs6 (degFnFromList d) 6

private def checkCfg (cfg : List (Fin 6 × Fin 6) × List (Fin 6) × ℕ) : Bool :=
  0 ≤ evalFast cfg.1 cfg.2.1 0 0 0 0 0 0 cfg.2.2

private def checkDList (ds : List (List ℕ)) : Bool :=
  ds.all fun d => (configsOfD d).all checkCfg

private lemma list_all_split {α : Type*} {p : α → Bool} {l : List α} (k : ℕ)
    (h1 : (l.take k).all p = true) (h2 : (l.drop k).all p = true) : l.all p = true := by
  rw [← List.take_append_drop k l, List.all_append, h1, h2]; rfl

-- Exhaustive verification of ALL 778 degree-sorted leaf-collapsed configurations in fast chunks!
private lemma check_S0_8 :
    ((List.range 9).flatMap (fun S => parts2to6 S 6)).all
      (fun d => (configsOfD d).all checkCfg) = true := by decide

private lemma check_S9 :
    checkDList (parts2to6 9 6) = true := by decide

private lemma check_S10_hi :
    checkDList ((parts2to6 10 6).filter fun d => 4 ≤ d.getD 0 0) = true := by decide

private lemma check_S10_3322 : (configsOfD [3, 3, 2, 2]).all checkCfg = true := by decide
private lemma check_S10_22222_1 : ((configsOfD [2, 2, 2, 2, 2]).take 35).all checkCfg = true := by decide
private lemma check_S10_22222_2 : (((configsOfD [2, 2, 2, 2, 2]).drop 35).take 35).all checkCfg = true := by decide
private lemma check_S10_22222_3 : (((configsOfD [2, 2, 2, 2, 2]).drop 70).take 35).all checkCfg = true := by decide
private lemma check_S10_22222_4 : (((configsOfD [2, 2, 2, 2, 2]).drop 105).take 35).all checkCfg = true := by decide
private lemma check_S10_22222_5 : ((configsOfD [2, 2, 2, 2, 2]).drop 140).all checkCfg = true := by decide

private lemma check_S10_22222 : (configsOfD [2, 2, 2, 2, 2]).all checkCfg = true := by
  apply list_all_split 35 check_S10_22222_1
  apply list_all_split 35 check_S10_22222_2
  rw [List.drop_drop]
  apply list_all_split 35 check_S10_22222_3
  rw [List.drop_drop]
  apply list_all_split 35 check_S10_22222_4
  rw [List.drop_drop]
  exact check_S10_22222_5

private lemma check_S10_lo :
    checkDList ((parts2to6 10 6).filter fun d => d.getD 0 0 < 4) = true := by
  have heq : (parts2to6 10 6).filter (fun d => d.getD 0 0 < 4) = [[3, 3, 2, 2], [2, 2, 2, 2, 2]] := by decide
  rw [heq, checkDList]
  simp [check_S10_3322, check_S10_22222]

private lemma check_S11_hi :
    checkDList ((parts2to6 11 6).filter fun d => 5 ≤ d.getD 0 0 ∨ d = [4, 4, 3]) = true := by decide
private lemma check_S11_4322 : (configsOfD [4, 3, 2, 2]).all checkCfg = true := by decide
private lemma check_S11_3332_1 : ((configsOfD [3, 3, 3, 2]).take 11).all checkCfg = true := by decide
private lemma check_S11_3332_2 : ((configsOfD [3, 3, 3, 2]).drop 11).all checkCfg = true := by decide
private lemma check_S11_3332 : (configsOfD [3, 3, 3, 2]).all checkCfg = true :=
  list_all_split 11 check_S11_3332_1 check_S11_3332_2
private lemma check_S11_32222_1 : ((configsOfD [3, 2, 2, 2, 2]).take 30).all checkCfg = true := by decide
private lemma check_S11_32222_2 : (((configsOfD [3, 2, 2, 2, 2]).drop 30).take 30).all checkCfg = true := by decide
private lemma check_S11_32222_3 : ((configsOfD [3, 2, 2, 2, 2]).drop 60).all checkCfg = true := by decide

private lemma check_S11_32222 : (configsOfD [3, 2, 2, 2, 2]).all checkCfg = true := by
  apply list_all_split 30 check_S11_32222_1
  apply list_all_split 30 check_S11_32222_2
  rw [List.drop_drop]
  exact check_S11_32222_3

private lemma check_S11 :
    checkDList (parts2to6 11 6) = true := by
  rw [checkDList, List.all_eq_true]
  intro d hd
  by_cases hhi : 5 ≤ d.getD 0 0 ∨ d = [4, 4, 3]
  · exact List.all_eq_true.mp check_S11_hi d (List.mem_filter.mpr ⟨hd, decide_eq_true hhi⟩)
  · have hrest : (parts2to6 11 6).filter (fun x => !(decide (5 ≤ x.getD 0 0 ∨ x = [4, 4, 3]))) =
        [[4, 3, 2, 2], [3, 3, 3, 2], [3, 2, 2, 2, 2]] := by decide
    have hmem : d ∈ (parts2to6 11 6).filter (fun x => !(decide (5 ≤ x.getD 0 0 ∨ x = [4, 4, 3]))) :=
      List.mem_filter.mpr ⟨hd, by rw [decide_eq_false hhi]; rfl⟩
    rw [hrest] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact check_S11_4322
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact check_S11_3332
      · rw [List.mem_singleton.mp hmem]; exact check_S11_32222

private lemma check_S12_le3 :
    checkDList ((parts2to6 12 6).filter fun d => d.length ≤ 3) = true := by decide
private lemma check_S12_6222 : (configsOfD [6, 2, 2, 2]).all checkCfg = true := by decide
private lemma check_S12_5322 : (configsOfD [5, 3, 2, 2]).all checkCfg = true := by decide
private lemma check_S12_4422 : (configsOfD [4, 4, 2, 2]).all checkCfg = true := by decide
private lemma check_S12_4332 : (configsOfD [4, 3, 3, 2]).all checkCfg = true := by decide
private lemma check_S12_3333 : (configsOfD [3, 3, 3, 3]).all checkCfg = true := by decide
private lemma check_S12_42222 : (configsOfD [4, 2, 2, 2, 2]).all checkCfg = true := by decide
private lemma check_S12_33222_1 : ((configsOfD [3, 3, 2, 2, 2]).take 15).all checkCfg = true := by decide
private lemma check_S12_33222_2 : ((configsOfD [3, 3, 2, 2, 2]).drop 15).all checkCfg = true := by decide
private lemma check_S12_33222 : (configsOfD [3, 3, 2, 2, 2]).all checkCfg = true :=
  list_all_split 15 check_S12_33222_1 check_S12_33222_2
private lemma check_S12_222222_1 : ((configsOfD [2, 2, 2, 2, 2, 2]).take 35).all checkCfg = true := by decide
private lemma check_S12_222222_2 : (((configsOfD [2, 2, 2, 2, 2, 2]).drop 35).take 35).all checkCfg = true := by decide
private lemma check_S12_222222_3 : (((configsOfD [2, 2, 2, 2, 2, 2]).drop 70).take 35).all checkCfg = true := by decide
private lemma check_S12_222222_4 : ((configsOfD [2, 2, 2, 2, 2, 2]).drop 105).all checkCfg = true := by decide

private lemma check_S12_222222 : (configsOfD [2, 2, 2, 2, 2, 2]).all checkCfg = true := by
  apply list_all_split 35 check_S12_222222_1
  apply list_all_split 35 check_S12_222222_2
  rw [List.drop_drop]
  apply list_all_split 35 check_S12_222222_3
  rw [List.drop_drop]
  exact check_S12_222222_4

private lemma check_S12 :
    checkDList (parts2to6 12 6) = true := by
  rw [checkDList, List.all_eq_true]
  intro d hd
  by_cases h3 : d.length ≤ 3
  · exact List.all_eq_true.mp check_S12_le3 d (List.mem_filter.mpr ⟨hd, decide_eq_true h3⟩)
  · have hrest : (parts2to6 12 6).filter (fun x => !(decide (x.length ≤ 3))) =
        [[6, 2, 2, 2], [5, 3, 2, 2], [4, 4, 2, 2], [4, 3, 3, 2], [4, 2, 2, 2, 2],
         [3, 3, 3, 3], [3, 3, 2, 2, 2], [2, 2, 2, 2, 2, 2]] := by decide
    have hmem : d ∈ (parts2to6 12 6).filter (fun x => !(decide (x.length ≤ 3))) :=
      List.mem_filter.mpr ⟨hd, by rw [decide_eq_false h3]; rfl⟩
    rw [hrest] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact check_S12_6222
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact check_S12_5322
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact check_S12_4422
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · exact check_S12_4332
          · rcases List.mem_cons.mp hmem with rfl | hmem
            · exact check_S12_42222
            · rcases List.mem_cons.mp hmem with rfl | hmem
              · exact check_S12_3333
              · rcases List.mem_cons.mp hmem with rfl | hmem
                · exact check_S12_33222
                · rw [List.mem_singleton.mp hmem]; exact check_S12_222222

private lemma check_all_S {S : ℕ} (hS : S ≤ 12) {d : List ℕ} (hd : d ∈ parts2to6 S 6)
    {cfg : List (Fin 6 × Fin 6) × List (Fin 6) × ℕ} (hcfg : cfg ∈ configsOfD d) :
    0 ≤ evalFast cfg.1 cfg.2.1 0 0 0 0 0 0 cfg.2.2 := by
  have hbool : checkCfg cfg = true := by
    have hall : (configsOfD d).all checkCfg = true := by
      by_cases h8 : S ≤ 8
      · exact List.all_eq_true.mp check_S0_8 d
          (List.mem_flatMap.mpr ⟨S, List.mem_range.mpr (by omega), hd⟩)
      · have hcases : S = 9 ∨ S = 10 ∨ S = 11 ∨ S = 12 := by omega
        rcases hcases with rfl | rfl | rfl | rfl
        · exact List.all_eq_true.mp check_S9 d hd
        · by_cases h4 : 4 ≤ d.getD 0 0
          · exact List.all_eq_true.mp check_S10_hi d (List.mem_filter.mpr ⟨hd, decide_eq_true h4⟩)
          · exact List.all_eq_true.mp check_S10_lo d (List.mem_filter.mpr ⟨hd, decide_eq_true (by omega)⟩)
        · exact List.all_eq_true.mp check_S11 d hd
        · exact List.all_eq_true.mp check_S12 d hd
    exact List.all_eq_true.mp hall cfg hcfg
  exact of_decide_eq_true hbool

/-- Completeness of `genFromPairs`: any multiplicity assignment `mfn` on `ps` that fits inside
remaining degree budget `r` and edge budget `eLeft` produces a tuple in `genFromPairs ps r eLeft`. -/
private lemma mem_genFromPairs :
    ∀ (ps : List (Fin 6 × Fin 6)), ps.Nodup →
      (∀ e ∈ ps, e.1 < e.2) →
      ∀ (mfn : Fin 6 × Fin 6 → ℕ) (r : Fin 6 → ℕ) (eLeft : ℕ),
      (∀ u : Fin 6, (ps.map fun e => (if e.1 = u then mfn e else 0) +
                                     (if e.2 = u then mfn e else 0)).sum ≤ r u) →
      (ps.map mfn).sum +
        ((r 0 + r 1 + r 2 + r 3 + r 4 + r 5) - 2 * (ps.map mfn).sum) ≤ eLeft →
      (ps.flatMap (fun e => List.replicate (mfn e) e),
       pendsFromRem (fun u => r u - (ps.map fun e => (if e.1 = u then mfn e else 0) +
                                                     (if e.2 = u then mfn e else 0)).sum),
       eLeft - ((ps.map mfn).sum +
         ((r 0 + r 1 + r 2 + r 3 + r 4 + r 5) - 2 * (ps.map mfn).sum))) ∈
        genFromPairs ps r eLeft := by
  intro ps
  induction ps with
  | nil =>
      intro _ _ mfn r eLeft _ hbud
      simp only [List.map_nil, List.sum_nil, mul_zero, Nat.sub_zero, zero_add,
        List.flatMap_nil, genFromPairs] at hbud ⊢
      rw [if_pos hbud]
      exact List.mem_singleton_self _
  | cons e ps ih =>
      intro hnd hlt mfn r eLeft hdeg hbud
      rcases e with ⟨u, v⟩
      have huv : u < v := hlt (u, v) (List.mem_cons_self ..)
      have hne : u ≠ v := ne_of_lt huv
      have hnd' : ps.Nodup := (List.nodup_cons.mp hnd).2
      have hlt' : ∀ e' ∈ ps, e'.1 < e'.2 := fun e' he' => hlt e' (List.mem_cons_of_mem _ he')
      have hmu : mfn (u, v) ≤ r u := by
        have := hdeg u
        simp only [List.map_cons, List.sum_cons, ↓reduceIte, Ne.symm hne] at this; omega
      have hmv : mfn (u, v) ≤ r v := by
        have := hdeg v
        simp only [List.map_cons, List.sum_cons, ↓reduceIte, hne] at this; omega
      have hmle : mfn (u, v) ≤ eLeft := by
        simp only [List.map_cons, List.sum_cons] at hbud; omega
      let r' := Function.update (Function.update r u (r u - mfn (u, v))) v (r v - mfn (u, v))
      have hr'_val : ∀ x : Fin 6,
          r' x = r x - ((if u = x then mfn (u, v) else 0) + (if v = x then mfn (u, v) else 0)) := by
        intro x
        by_cases hxu : x = u
        · subst hxu; simp [r', hne, Ne.symm hne]
        · by_cases hxv : x = v
          · subst hxv; simp [r', hne]
          · simp [r', hxu, hxv, Ne.symm hxu, Ne.symm hxv]
      have hdeg' : ∀ x : Fin 6,
          (ps.map fun e' => (if e'.1 = x then mfn e' else 0) +
                            (if e'.2 = x then mfn e' else 0)).sum ≤ r' x := by
        intro x
        rw [hr'_val x]
        have := hdeg x
        simp only [List.map_cons, List.sum_cons] at this
        omega
      have hr'_sum : r' 0 + r' 1 + r' 2 + r' 3 + r' 4 + r' 5 =
          (r 0 + r 1 + r 2 + r 3 + r 4 + r 5) - 2 * mfn (u, v) := by
        have hs : ∀ x : Fin 6, r' x + ((if u = x then mfn (u, v) else 0) +
            (if v = x then mfn (u, v) else 0)) = r x := by
          intro x; rw [hr'_val x]
          by_cases hxu : u = x
          · subst hxu; simp [Ne.symm hne]; omega
          · by_cases hxv : v = x
            · subst hxv; simp [hxu]; omega
            · simp [hxu, hxv]
        have hu_sum : (if u = 0 then mfn (u, v) else 0) + (if u = 1 then mfn (u, v) else 0) +
            (if u = 2 then mfn (u, v) else 0) + (if u = 3 then mfn (u, v) else 0) +
            (if u = 4 then mfn (u, v) else 0) + (if u = 5 then mfn (u, v) else 0) = mfn (u, v) := by
          fin_cases u <;> simp
        have hv_sum : (if v = 0 then mfn (u, v) else 0) + (if v = 1 then mfn (u, v) else 0) +
            (if v = 2 then mfn (u, v) else 0) + (if v = 3 then mfn (u, v) else 0) +
            (if v = 4 then mfn (u, v) else 0) + (if v = 5 then mfn (u, v) else 0) = mfn (u, v) := by
          fin_cases v <;> simp
        have h0 := hs 0; have h1 := hs 1; have h2 := hs 2
        have h3 := hs 3; have h4 := hs 4; have h5 := hs 5
        omega
      have h2sum : 2 * (ps.map mfn).sum ≤ r' 0 + r' 1 + r' 2 + r' 3 + r' 4 + r' 5 := by
        have htot : ∀ l : List (Fin 6 × Fin 6),
            (l.map fun e' => (if e'.1 = 0 then mfn e' else 0) + (if e'.2 = 0 then mfn e' else 0)).sum +
            (l.map fun e' => (if e'.1 = 1 then mfn e' else 0) + (if e'.2 = 1 then mfn e' else 0)).sum +
            (l.map fun e' => (if e'.1 = 2 then mfn e' else 0) + (if e'.2 = 2 then mfn e' else 0)).sum +
            (l.map fun e' => (if e'.1 = 3 then mfn e' else 0) + (if e'.2 = 3 then mfn e' else 0)).sum +
            (l.map fun e' => (if e'.1 = 4 then mfn e' else 0) + (if e'.2 = 4 then mfn e' else 0)).sum +
            (l.map fun e' => (if e'.1 = 5 then mfn e' else 0) + (if e'.2 = 5 then mfn e' else 0)).sum =
            2 * (l.map mfn).sum := by
          intro l
          induction l with
          | nil => simp
          | cons e' ls ihs =>
              rcases e' with ⟨a, b⟩
              simp only [List.map_cons, List.sum_cons]
              have ha : (if a = 0 then mfn (a, b) else 0) + (if a = 1 then mfn (a, b) else 0) +
                  (if a = 2 then mfn (a, b) else 0) + (if a = 3 then mfn (a, b) else 0) +
                  (if a = 4 then mfn (a, b) else 0) + (if a = 5 then mfn (a, b) else 0) = mfn (a, b) := by
                fin_cases a <;> simp
              have hb : (if b = 0 then mfn (a, b) else 0) + (if b = 1 then mfn (a, b) else 0) +
                  (if b = 2 then mfn (a, b) else 0) + (if b = 3 then mfn (a, b) else 0) +
                  (if b = 4 then mfn (a, b) else 0) + (if b = 5 then mfn (a, b) else 0) = mfn (a, b) := by
                fin_cases b <;> simp
              omega
        have := htot ps
        have d0 := hdeg' 0; have d1 := hdeg' 1; have d2 := hdeg' 2
        have d3 := hdeg' 3; have d4 := hdeg' 4; have d5 := hdeg' 5
        omega
      have hbud' : (ps.map mfn).sum +
          ((r' 0 + r' 1 + r' 2 + r' 3 + r' 4 + r' 5) - 2 * (ps.map mfn).sum) ≤ eLeft - mfn (u, v) := by
        rw [hr'_sum]
        simp only [List.map_cons, List.sum_cons] at hbud
        omega
      have hrec := ih hnd' hlt' mfn r' (eLeft - mfn (u, v)) hdeg' hbud'
      simp only [genFromPairs, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨mfn (u, v), by omega, _, hrec, ?_⟩
      simp only [List.flatMap_cons, Prod.mk.injEq]
      refine ⟨trivial, ?_, ?_⟩
      · congr 1
        funext x
        rw [hr'_val x]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [hr'_sum]
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Degree of a vertex in an edge list `E` on `Fin 23`. -/
private def deg23 (E : List (Fin 23 × Fin 23)) (v : Fin 23) : ℕ :=
  (E.map fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum

private lemma deg23_cons (e : Fin 23 × Fin 23) (rest : List (Fin 23 × Fin 23)) (v : Fin 23) :
    deg23 (e :: rest) v = (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0) + deg23 rest v := rfl

private lemma sum_deg23 (E : List (Fin 23 × Fin 23)) :
    (∑ v : Fin 23, deg23 E v) = 2 * E.length := by
  induction E with
  | nil => simp [deg23]
  | cons e rest ih =>
      rcases e with ⟨u, v⟩
      simp only [deg23_cons, List.length_cons,
        Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at ih ⊢
      omega

private lemma deg23_eq_zero_iff (E : List (Fin 23 × Fin 23)) (v : Fin 23) :
    deg23 E v = 0 ↔ ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v := by
  induction E with
  | nil => simp [deg23]
  | cons e rest ih =>
      rcases e with ⟨a, b⟩
      simp only [deg23_cons, List.mem_cons, forall_eq_or_imp] at ih ⊢
      constructor
      · intro h
        have h1 : (if a = v then 1 else 0) + (if b = v then 1 else 0) = 0 := by omega
        have h2 : deg23 rest v = 0 := by omega
        refine ⟨⟨?_, ?_⟩, ih.mp h2⟩
        · intro heq; subst heq; simp at h1
        · intro heq; subst heq; simp at h1
      · rintro ⟨⟨ha, hb⟩, hrest⟩
        simp only [ha, hb, ↓reduceIte, add_zero, zero_add]
        exact ih.mpr hrest

private lemma deg23_perm {E1 E2 : List (Fin 23 × Fin 23)} (hp : E1.Perm E2) (v : Fin 23) :
    deg23 E1 v = deg23 E2 v := by
  unfold deg23
  exact (hp.map _).sum_eq

/-- Sort a list of `Fin 23` vertices in non-increasing order of `f : Fin 23 → ℕ`. -/
private def insByDesc (f : Fin 23 → ℕ) (x : Fin 23) : List (Fin 23) → List (Fin 23)
  | [] => [x]
  | y :: ys => if f y ≤ f x then x :: y :: ys else y :: insByDesc f x ys

private def sortByDesc (f : Fin 23 → ℕ) : List (Fin 23) → List (Fin 23)
  | [] => []
  | x :: xs => insByDesc f x (sortByDesc f xs)

private lemma insByDesc_perm (f : Fin 23 → ℕ) (x : Fin 23) (l : List (Fin 23)) :
    (insByDesc f x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [insByDesc]; split_ifs
      · exact List.Perm.refl _
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

private lemma sortByDesc_perm (f : Fin 23 → ℕ) (l : List (Fin 23)) :
    (sortByDesc f l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insByDesc_perm f x _).trans (List.Perm.cons x ih)

private lemma insByDesc_pairwise (f : Fin 23 → ℕ) (x : Fin 23) {l : List (Fin 23)}
    (hl : l.Pairwise (fun a b => f b ≤ f a)) :
    (insByDesc f x l).Pairwise (fun a b => f b ≤ f a) := by
  induction l with
  | nil => simp [insByDesc]
  | cons y ys ih =>
      simp only [insByDesc]; split_ifs with hxy
      · refine List.pairwise_cons.mpr ⟨?_, hl⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hxy
        · exact le_trans ((List.pairwise_cons.mp hl).1 z hz') hxy
      · refine List.pairwise_cons.mpr ⟨?_, ih (List.pairwise_cons.mp hl).2⟩
        intro z hz
        have hmem : z ∈ x :: ys := (insByDesc_perm f x ys).subset hz
        rcases List.mem_cons.mp hmem with rfl | hz'
        · omega
        · exact (List.pairwise_cons.mp hl).1 z hz'

private lemma sortByDesc_pairwise (f : Fin 23 → ℕ) (l : List (Fin 23)) :
    (sortByDesc f l).Pairwise (fun a b => f b ≤ f a) := by
  induction l with
  | nil => simp [sortByDesc]
  | cons x xs ih => exact insByDesc_pairwise f x ih

/-- Bridge from `evalEdgesM` on `V2` (via an injection `emb : Fin 6 → Fin 23` covering all
endpoints) to `evalSem6`! -/
private lemma evalEdgesM_peel_iso_pend
    (V2 : List (Fin 23)) (_hV2_nd : V2.Nodup) (_hV2_le : V2.length ≤ 6)
    (E_iso E_pend E_int : List (Fin 23 × Fin 23))
    (hloop_iso : ∀ e ∈ E_iso, e.1 ≠ e.2)
    (hloop_pend : ∀ e ∈ E_pend, e.1 ≠ e.2)
    (hpend_u : ∀ e ∈ E_pend, e.1 ∈ V2)
    (hpend_v : ∀ e ∈ E_pend, e.2 ∉ V2)
    (hiso_uv : ∀ e ∈ E_iso, e.1 ∉ V2 ∧ e.2 ∉ V2)
    (_hint_uv : ∀ e ∈ E_int, e.1 ∈ V2 ∧ e.2 ∈ V2)
    (hdeg1 : ∀ w : Fin 23, w ∉ V2 → deg23 (E_iso ++ E_pend ++ E_int) w ≤ 1)
    (emb : Fin 6 → Fin 23) (hemb_inj : Function.Injective emb)
    (_hemb_cov : ∀ x ∈ V2, ∃ u : Fin 6, emb u = x)
    (pe6 : List (Fin 6)) (hpe6 : E_pend.map Prod.fst = pe6.map emb)
    (ie6 : List (Fin 6 × Fin 6)) (hie6 : E_int = ie6.map fun e => (emb e.1, emb e.2)) :
    evalEdgesM (E_iso ++ E_pend ++ E_int) 0 0 =
      2 ^ E_iso.length * evalSem6 ie6 pe6 (fun _ => 0) E_iso.length := by
  -- Step 1: Peel off `E_iso`
  have hpeel_iso : ∀ (L1 L2 : List (Fin 23 × Fin 23)) (m2 : ℕ),
      (∀ e ∈ L1, e.1 ≠ e.2) →
      (∀ e ∈ L1, e.1 ∉ V2 ∧ e.2 ∉ V2) →
      (∀ w, w ∉ V2 → deg23 (L1 ++ L2) w ≤ 1) →
      evalEdgesM (L1 ++ L2) 0 m2 = 2 ^ L1.length * evalEdgesM L2 0 (m2 + L1.length) := by
    intro L1
    induction L1 with
    | nil => intro L2 m2 _ _ _; simp
    | cons e rest ih =>
        intro L2 m2 hlp huv hd1
        rcases e with ⟨u, v⟩
        have hne : u ≠ v := hlp (u, v) (List.mem_cons_self ..)
        have hnotV2 := huv (u, v) (List.mem_cons_self ..)
        have hu_rest : ∀ e' ∈ rest ++ L2, e'.1 ≠ u ∧ e'.2 ≠ u := by
          rw [← deg23_eq_zero_iff]
          have hd := hd1 u hnotV2.1
          simp only [List.cons_append, deg23_cons, ↓reduceIte, Ne.symm hne] at hd
          exact Nat.eq_zero_of_le_zero (by omega)
        have hv_rest : ∀ e' ∈ rest ++ L2, e'.1 ≠ v ∧ e'.2 ≠ v := by
          rw [← deg23_eq_zero_iff]
          have hd := hd1 v hnotV2.2
          simp only [List.cons_append, deg23_cons, ↓reduceIte, hne] at hd
          exact Nat.eq_zero_of_le_zero (by omega)
        simp only [List.cons_append, List.length_cons]
        rw [evalEdgesM_iso u v (rest ++ L2) hne hu_rest hv_rest 0 m2 rfl rfl]
        have hd1' : ∀ w, w ∉ V2 → deg23 (rest ++ L2) w ≤ 1 := by
          intro w hw
          have hd := hd1 w hw
          simp only [List.cons_append, deg23_cons] at hd
          omega
        rw [ih L2 (m2 + 1) (fun e' he' => hlp e' (List.mem_cons_of_mem _ he'))
          (fun e' he' => huv e' (List.mem_cons_of_mem _ he')) hd1']
        rw [show m2 + 1 + rest.length = m2 + (rest.length + 1) by omega, pow_succ]
        ring
  rw [List.append_assoc, hpeel_iso E_iso (E_pend ++ E_int) 0 hloop_iso hiso_uv
    (by simpa [List.append_assoc] using hdeg1), zero_add]
  congr 1
  -- Step 2: General bridge from `evalEdgesM (E_pend ++ E_int) (lift α6) m2` to `evalSem6 ie6 pe6 α6 m2`
  let lift : (Fin 6 → ℕ) → (Fin 23 →₀ ℕ) := fun a =>
    ∑ u : Fin 6, Finsupp.single (emb u) (a u)
  have hlift_zero : lift (fun _ => 0) = 0 := by
    simp [lift]
  have hlift_emb : ∀ (a : Fin 6 → ℕ) (u : Fin 6), lift a (emb u) = a u := by
    intro a u
    simp only [lift, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single u]
    · simp
    · intro x _ hxu; simp [hemb_inj.ne hxu]
    · intro h; exact absurd (Finset.mem_univ u) h
  have hlift_not_mem : ∀ (a : Fin 6 → ℕ) (w : Fin 23), (∀ u : Fin 6, emb u ≠ w) → lift a w = 0 := by
    intro a w hw
    simp only [lift, Finsupp.finsetSum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun u _ => by simp [hw u]
  have hlift_update : ∀ (a : Fin 6 → ℕ) (u : Fin 6) (d : ℕ),
      lift (Function.update a u (a u + d)) = lift a + Finsupp.single (emb u) d := by
    intro a u d
    ext x
    by_cases hx : ∃ j : Fin 6, emb j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [hlift_emb, Finsupp.add_apply, hlift_emb, Finsupp.single_apply]
      by_cases hj : u = j
      · subst hj; simp [Function.update]
      · simp [Function.update, Ne.symm hj, hemb_inj.ne hj]
    · push Not at hx
      rw [hlift_not_mem _ x hx, Finsupp.add_apply, hlift_not_mem _ x hx, Finsupp.single_apply,
        if_neg (hx u), add_zero]
  have hlift_nzMs : ∀ a : Fin 6 → ℕ,
      nzMs (lift a) = ((((List.finRange 6).map a).filter (· ≠ 0) : List ℕ) : Multiset ℕ) := by
    intro a
    unfold nzMs
    have hsupp : (lift a).support =
        ((Finset.univ : Finset (Fin 6)).filter (fun u => a u ≠ 0)).map ⟨emb, hemb_inj⟩ := by
      ext x
      simp only [Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.Embedding.coeFn_mk]
      constructor
      · intro hx
        by_contra hnone
        push Not at hnone
        by_cases hex : ∃ u : Fin 6, emb u = x
        · obtain ⟨u, rfl⟩ := hex
          rw [hlift_emb] at hx
          exact hx (by by_contra h; exact hnone u h rfl)
        · push Not at hex
          exact hx (hlift_not_mem a x hex)
      · rintro ⟨u, hu, rfl⟩
        rwa [hlift_emb]
    rw [hsupp, Finset.map_val, Multiset.map_map]
    have hmap : Multiset.map (lift a ∘ (⟨emb, hemb_inj⟩ : Fin 6 ↪ Fin 23))
        ((Finset.univ.filter (fun u : Fin 6 => a u ≠ 0)).val) =
        Multiset.map a ((Finset.univ.filter (fun u : Fin 6 => a u ≠ 0)).val) := by
      refine Multiset.map_congr rfl fun u _ => ?_
      exact hlift_emb a u
    rw [hmap]
    have hfin : ((Finset.univ : Finset (Fin 6)).filter (fun u => a u ≠ 0)).val =
        (((List.finRange 6).filter (fun u => a u ≠ 0) : List (Fin 6)) : Multiset (Fin 6)) := by
      have huniv : (Finset.univ : Finset (Fin 6)).val = ((List.finRange 6 : List (Fin 6)) : Multiset (Fin 6)) := by
        rfl
      rw [Finset.filter_val, huniv, Multiset.filter_coe]
    rw [hfin, Multiset.map_coe, List.filter_map]
    rfl
  -- First prove bridge for `E_int` (no pendant edges)
  have hbridge_int : ∀ (L : List (Fin 6 × Fin 6)) (a : Fin 6 → ℕ) (m2 : ℕ),
      evalEdgesM (L.map fun e => (emb e.1, emb e.2)) (lift a) m2 = evalSem6 L [] a m2 := by
    intro L
    induction L with
    | nil =>
        intro a m2
        simp only [List.map_nil, evalEdgesM, evalSem6, hlift_nzMs]
    | cons e rest ih =>
        intro a m2
        rcases e with ⟨u, v⟩
        simp only [List.map_cons, evalEdgesM, evalSem6]
        rw [← hlift_update a u 2, ← hlift_update a v 2,
            ← hlift_update a u 1, ← hlift_update (Function.update a u (a u + 1)) v 1,
            ih, ih, ih]
  -- Now prove bridge for `E_pend ++ E_int`
  have hd1_pi : ∀ w, w ∉ V2 → deg23 (E_pend ++ E_int) w ≤ 1 := by
    intro w hw
    have hd := hdeg1 w hw
    have hsum : deg23 (E_iso ++ E_pend ++ E_int) w = deg23 E_iso w + deg23 (E_pend ++ E_int) w := by
      simp [deg23, List.append_assoc]
    omega
  have hbridge_pend : ∀ (Lp : List (Fin 23 × Fin 23)) (p6 : List (Fin 6)),
      Lp.map Prod.fst = p6.map emb →
      (∀ e ∈ Lp, e.1 ≠ e.2) →
      (∀ e ∈ Lp, e.1 ∈ V2) →
      (∀ e ∈ Lp, e.2 ∉ V2) →
      (∀ w, w ∉ V2 → deg23 (Lp ++ E_int) w ≤ 1) →
      ∀ (a : Fin 6 → ℕ) (m2 : ℕ),
        (∀ w, w ∉ V2 → lift a w = 0) →
        evalEdgesM (Lp ++ E_int) (lift a) m2 = evalSem6 ie6 p6 a m2 := by
    intro Lp
    induction Lp with
    | nil =>
        intro p6 hp6 _ _ _ _ a m2 _
        cases p6 with
        | nil => rw [List.nil_append, hie6, hbridge_int]
        | cons _ _ => simp at hp6
    | cons e rest ih =>
        intro p6 hp6 hlp hpu hpv hd1 a m2 hlift0
        cases p6 with
        | nil => simp at hp6
        | cons u p6' =>
            rcases e with ⟨x, v⟩
            simp only [List.map_cons, List.cons.injEq] at hp6
            rcases hp6 with ⟨rfl, hp6'⟩
            have hne : emb u ≠ v := hlp (emb u, v) (List.mem_cons_self ..)
            have hu_mem : emb u ∈ V2 := hpu (emb u, v) (List.mem_cons_self ..)
            have hv_not : v ∉ V2 := hpv (emb u, v) (List.mem_cons_self ..)
            have hv_rest : ∀ e' ∈ rest ++ E_int, e'.1 ≠ v ∧ e'.2 ≠ v := by
              rw [← deg23_eq_zero_iff]
              have hd := hd1 v hv_not
              simp only [List.cons_append, deg23_cons, ↓reduceIte, hne] at hd
              exact Nat.eq_zero_of_le_zero (by omega)
            simp only [List.cons_append, evalSem6]
            rw [evalEdgesM_pend (emb u) v (rest ++ E_int) hne hv_rest (lift a) m2 (hlift0 v hv_not)]
            rw [← hlift_update a u 2]
            have hd1' : ∀ w, w ∉ V2 → deg23 (rest ++ E_int) w ≤ 1 := by
              intro w hw
              have hd := hd1 w hw
              simp only [List.cons_append, deg23_cons] at hd
              omega
            have hu_in_V2 : ∀ w, w ∉ V2 → lift (Function.update a u (a u + 2)) w = 0 := by
              intro w hw
              rw [hlift_update, Finsupp.add_apply, hlift0 w hw, zero_add, Finsupp.single_apply]
              have hne_w : emb u ≠ w := fun heq => hw (heq ▸ hu_mem)
              simp [hne_w]
            rw [ih p6' hp6' (fun e' he' => hlp e' (List.mem_cons_of_mem _ he'))
              (fun e' he' => hpu e' (List.mem_cons_of_mem _ he'))
              (fun e' he' => hpv e' (List.mem_cons_of_mem _ he')) hd1' _ m2 hu_in_V2,
                ih p6' hp6' (fun e' he' => hlp e' (List.mem_cons_of_mem _ he'))
              (fun e' he' => hpu e' (List.mem_cons_of_mem _ he'))
              (fun e' he' => hpv e' (List.mem_cons_of_mem _ he')) hd1' a (m2 + 1) hlift0]
  rw [← hlift_zero]
  exact hbridge_pend E_pend pe6 hpe6 hloop_pend hpend_u hpend_v hd1_pi (fun _ => 0) E_iso.length
    (fun w _ => by simp [lift])

/-- Helper: partition an edge list into `(E_iso, E_pend, E_int)` while orienting pendant edges
so `e.1 ∈ V2 ∧ e.2 ∉ V2`, preserving `evalEdgesM`. -/
private def orientAndSplit (V2 : List (Fin 23)) :
    List (Fin 23 × Fin 23) →
      List (Fin 23 × Fin 23) × List (Fin 23 × Fin 23) × List (Fin 23 × Fin 23)
  | [] => ([], [], [])
  | (u, v) :: rest =>
      let (iso, pend, int) := orientAndSplit V2 rest
      if u ∈ V2 then
        if v ∈ V2 then (iso, pend, (u, v) :: int)
        else (iso, (u, v) :: pend, int)
      else
        if v ∈ V2 then (iso, (v, u) :: pend, int)
        else ((u, v) :: iso, pend, int)

private lemma orientAndSplit_eval (V2 : List (Fin 23)) (E : List (Fin 23 × Fin 23)) :
    let r := orientAndSplit V2 E
    (∀ α m2, evalEdgesM E α m2 = evalEdgesM (r.1 ++ r.2.1 ++ r.2.2) α m2) ∧
    (∀ w, deg23 E w = deg23 (r.1 ++ r.2.1 ++ r.2.2) w) ∧
    (E.length = r.1.length + r.2.1.length + r.2.2.length) ∧
    ((∀ e ∈ E, e.1 ≠ e.2) →
      (∀ e ∈ r.1, e.1 ≠ e.2) ∧ (∀ e ∈ r.2.1, e.1 ≠ e.2) ∧ (∀ e ∈ r.2.2, e.1 ≠ e.2)) ∧
    (∀ e ∈ r.1, e.1 ∉ V2 ∧ e.2 ∉ V2) ∧
    (∀ e ∈ r.2.1, e.1 ∈ V2 ∧ e.2 ∉ V2) ∧
    (∀ e ∈ r.2.2, e.1 ∈ V2 ∧ e.2 ∈ V2) := by
  induction E with
  | nil => simp [orientAndSplit]
  | cons e rest ih =>
      rcases e with ⟨u, v⟩
      rcases h : orientAndSplit V2 rest with ⟨iso, pend, int⟩
      rw [h] at ih
      rcases ih with ⟨heval, hdeg, hlen, hloop, hiso, hpend, hint⟩
      simp only at hlen
      simp only [orientAndSplit, h]
      by_cases hu : u ∈ V2 <;> by_cases hv : v ∈ V2
      · simp only [hu, hv, ↓reduceIte]
        have hperm : ((u, v) :: (iso ++ pend ++ int)).Perm (iso ++ pend ++ ((u, v) :: int)) :=
          List.perm_middle.symm
        refine ⟨fun α m2 => ?_, fun w => ?_, by simp; omega, ?_, hiso, hpend, ?_⟩
        · simp only [evalEdgesM, heval]
          exact evalEdgesM_perm hperm α m2
        · rw [← deg23_perm hperm]
          simp only [deg23, List.map_cons, List.sum_cons] at hdeg ⊢; rw [hdeg]
        · intro hl
          have hl' := hloop (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
          refine ⟨hl'.1, hl'.2.1, ?_⟩
          intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact hl (u, v) (List.mem_cons_self ..)
          · exact hl'.2.2 e' h'
        · intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact ⟨hu, hv⟩
          · exact hint e' h'
      · simp only [hu, hv, ↓reduceIte]
        have hperm : ((u, v) :: (iso ++ pend ++ int)).Perm (iso ++ ((u, v) :: pend) ++ int) := by
          rw [List.append_assoc, List.append_assoc]
          exact (List.perm_middle (l₁ := iso) (l₂ := pend ++ int)).symm
        refine ⟨fun α m2 => ?_, fun w => ?_, by simp; omega, ?_, hiso, ?_, hint⟩
        · simp only [evalEdgesM, heval]
          exact evalEdgesM_perm hperm α m2
        · rw [← deg23_perm hperm]
          simp only [deg23, List.map_cons, List.sum_cons] at hdeg ⊢; rw [hdeg]
        · intro hl
          have hl' := hloop (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
          refine ⟨hl'.1, ?_, hl'.2.2⟩
          intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact hl (u, v) (List.mem_cons_self ..)
          · exact hl'.2.1 e' h'
        · intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact ⟨hu, hv⟩
          · exact hpend e' h'
      · simp only [hu, hv, ↓reduceIte]
        have hperm : ((v, u) :: (iso ++ pend ++ int)).Perm (iso ++ ((v, u) :: pend) ++ int) := by
          rw [List.append_assoc, List.append_assoc]
          exact (List.perm_middle (l₁ := iso) (l₂ := pend ++ int)).symm
        refine ⟨fun α m2 => ?_, fun w => ?_, by simp; omega, ?_, hiso, ?_, hint⟩
        · rw [evalEdgesM_swap_head u v rest]
          simp only [evalEdgesM, heval]
          exact evalEdgesM_perm hperm α m2
        · rw [← deg23_perm hperm]
          simp only [deg23, List.map_cons, List.sum_cons] at hdeg ⊢; rw [hdeg]; omega
        · intro hl
          have hl' := hloop (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
          refine ⟨hl'.1, ?_, hl'.2.2⟩
          intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact (hl (u, v) (List.mem_cons_self ..)).symm
          · exact hl'.2.1 e' h'
        · intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact ⟨hv, hu⟩
          · exact hpend e' h'
      · simp only [hu, hv, ↓reduceIte]
        refine ⟨fun α m2 => ?_, fun w => ?_, by simp; omega, ?_, ?_, hpend, hint⟩
        · simp only [List.cons_append, evalEdgesM, heval]
        · simp only [List.cons_append, deg23, List.map_cons, List.sum_cons] at hdeg ⊢; rw [hdeg]
        · intro hl
          have hl' := hloop (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
          refine ⟨?_, hl'.2.1, hl'.2.2⟩
          intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact hl (u, v) (List.mem_cons_self ..)
          · exact hl'.1 e' h'
        · intro e' he'; rcases List.mem_cons.mp he' with rfl | h'
          · exact ⟨hu, hv⟩
          · exact hiso e' h'

private lemma ie6_perm_pairs6 (ie6 : List (Fin 6 × Fin 6))
    (hie6_lt : ∀ e ∈ ie6, e.1 < e.2) :
    ie6.Perm (pairs6.flatMap fun e => List.replicate (ie6.count e) e) := by
  have hpairs_nd : pairs6.Nodup := by decide
  have hpairs_lt : ∀ e ∈ pairs6, e.1 < e.2 := by decide
  have hpairs_cov : ∀ e : Fin 6 × Fin 6, e.1 < e.2 → e ∈ pairs6 := by decide
  rw [List.perm_iff_count]
  intro e
  by_cases hlt : e.1 < e.2
  · have hmem_p : e ∈ pairs6 := hpairs_cov e hlt
    rw [List.count_flatMap]
    have hsum_eq : (pairs6.map fun x => List.count e (List.replicate (ie6.count x) x)).sum = ie6.count e := by
      have hgen : ∀ l : List (Fin 6 × Fin 6), l.Nodup → e ∈ l →
          (l.map fun x => List.count e (List.replicate (ie6.count x) x)).sum = ie6.count e := by
        intro l; induction l with
        | nil => intro _ h; simp at h
        | cons a as ih =>
            intro hnd hmem
            rcases List.nodup_cons.mp hnd with ⟨ha_not, has_nd⟩
            simp only [List.map_cons, List.sum_cons]
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · have h0 : (as.map fun x => List.count e (List.replicate (ie6.count x) x)).sum = 0 := by
                apply List.sum_eq_zero
                intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
                have hne : e ≠ x := fun h => ha_not (h ▸ hx)
                simp [List.count_replicate, Ne.symm hne]
              rw [h0, add_zero, List.count_replicate_self]
            · have hne : a ≠ e := fun h => ha_not (h ▸ hmem')
              rw [ih has_nd hmem']
              simp [List.count_replicate, hne]
      exact hgen pairs6 hpairs_nd hmem_p
    simpa only [Function.comp_def] using hsum_eq.symm
  · have hc1 : ie6.count e = 0 := List.count_eq_zero.mpr (fun h => hlt (hie6_lt e h))
    have hc2 : (pairs6.flatMap fun x => List.replicate (ie6.count x) x).count e = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      obtain ⟨x, hx, hrep⟩ := List.mem_flatMap.mp hmem
      rcases List.mem_replicate.mp hrep with ⟨_, rfl⟩
      exact hlt (hpairs_lt e hx)
    rw [hc1, hc2]

private lemma deg_split6_helper
    (E E_iso E_pend E_int : List (Fin 23 × Fin 23))
    (V2 : List (Fin 23)) (emb : Fin 6 → Fin 23)
    (hemb_inj : Function.Injective emb)
    (hemb_V2 : ∀ (i : Fin 6) (hi : i.val < V2.length), emb i = V2[i.val]'hi)
    (hemb_notV2 : ∀ (i : Fin 6), ¬ i.val < V2.length → emb i ∉ V2)
    (hdeg_sp : ∀ w, deg23 E w = deg23 (E_iso ++ E_pend ++ E_int) w)
    (hiso_sp : ∀ e ∈ E_iso, e.1 ∉ V2 ∧ e.2 ∉ V2)
    (hpend_sp : ∀ e ∈ E_pend, e.1 ∈ V2 ∧ e.2 ∉ V2)
    (hint_sp : ∀ e ∈ E_int, e.1 ∈ V2 ∧ e.2 ∈ V2)
    (pe6 : List (Fin 6)) (ie6_raw ie6 : List (Fin 6 × Fin 6))
    (hpe6_map : E_pend.map Prod.fst = pe6.map emb)
    (hie6_map : E_int = ie6_raw.map (fun e => (emb e.1, emb e.2)))
    (hie6_def : ie6 = ie6_raw.map (fun e => if e.1 ≤ e.2 then e else (e.2, e.1)))
    (hie6_perm : ie6.Perm (pairs6.flatMap fun e => List.replicate (ie6.count e) e))
    (u : Fin 6) :
    degFnFromList (V2.map (deg23 E)) u =
      (pairs6.map fun e => (if e.1 = u then ie6.count e else 0) +
                           (if e.2 = u then ie6.count e else 0)).sum + pe6.count u := by
  have hint_eq : (pairs6.map fun e => (if e.1 = u then ie6.count e else 0) +
                                      (if e.2 = u then ie6.count e else 0)).sum =
      (ie6.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum := by
    rw [(hie6_perm.map _).sum_eq]
    have hfm : ∀ l : List (Fin 6 × Fin 6),
        ((l.flatMap fun e => List.replicate (ie6.count e) e).map
          fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum =
        (l.map fun e => (if e.1 = u then ie6.count e else 0) + (if e.2 = u then ie6.count e else 0)).sum := by
      intro l; induction l with
      | nil => simp
      | cons a as ih =>
          simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons, List.map_replicate, List.sum_replicate, smul_eq_mul, ih]
          by_cases h1 : a.1 = u <;> by_cases h2 : a.2 = u <;> (simp [h1, h2]; try omega)
    exact (hfm pairs6).symm
  have hint_raw : (ie6.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum =
      (ie6_raw.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum := by
    rw [hie6_def, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    simp only [Function.comp_apply]
    split_ifs <;> omega
  have hint_23 : (ie6_raw.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum =
      deg23 E_int (emb u) := by
    rw [hie6_map, deg23, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    simp only [Function.comp_apply, hemb_inj.eq_iff]
  have hpe6_count : pe6.count u = (E_pend.map fun e => if e.1 = emb u then 1 else 0).sum := by
    have hc : pe6.count u = (pe6.map fun x => if x = u then 1 else 0).sum := by
      clear * -; induction pe6 with
      | nil => simp
      | cons a as ih => simp [List.count_cons, ih]; split_ifs <;> omega
    rw [hc]
    have hmap_eq : (pe6.map fun x => if x = u then 1 else 0) =
        (E_pend.map fun e => if e.1 = emb u then 1 else 0) := by
      calc (pe6.map fun x => if x = u then 1 else 0)
          = (pe6.map emb).map (fun y => if y = emb u then 1 else 0) := by
              rw [List.map_map]
              refine List.map_congr_left fun x _ => ?_
              simp only [Function.comp_apply, hemb_inj.eq_iff]
        _ = (E_pend.map Prod.fst).map (fun y => if y = emb u then 1 else 0) := by rw [← hpe6_map]
        _ = E_pend.map (fun e => if e.1 = emb u then 1 else 0) := by rw [List.map_map]; rfl
    rw [hmap_eq]
  rw [hint_eq, hint_raw, hint_23, hpe6_count]
  by_cases hu : u.val < V2.length
  · have hu_V2 : emb u ∈ V2 := by rw [hemb_V2 u hu]; exact List.getElem_mem _
    have hd_get : degFnFromList (V2.map (deg23 E)) u = deg23 E (emb u) := by
      simp only [degFnFromList, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_map, ← hemb_V2 u hu]
    have hiso_zero : deg23 E_iso (emb u) = 0 := by
      rw [deg23_eq_zero_iff]
      intro e he
      exact ⟨fun h => (hiso_sp e he).1 (h ▸ hu_V2), fun h => (hiso_sp e he).2 (h ▸ hu_V2)⟩
    have hpend_eq : (E_pend.map fun e => if e.1 = emb u then 1 else 0).sum = deg23 E_pend (emb u) := by
      rw [deg23]
      refine congrArg List.sum (List.map_congr_left fun e he => ?_)
      have hne : e.2 ≠ emb u := fun h => (hpend_sp e he).2 (h ▸ hu_V2)
      simp [hne]
    rw [hd_get, hpend_eq, hdeg_sp (emb u)]
    have hsum3 : deg23 (E_iso ++ E_pend ++ E_int) (emb u) =
        deg23 E_iso (emb u) + deg23 E_pend (emb u) + deg23 E_int (emb u) := by
      simp [deg23]; omega
    omega
  · have hu_notV2 : emb u ∉ V2 := hemb_notV2 u hu
    have hd_get : degFnFromList (V2.map (deg23 E)) u = 0 := by
      simp only [degFnFromList, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]
    have hint_zero : deg23 E_int (emb u) = 0 := by
      rw [deg23_eq_zero_iff]
      intro e he
      exact ⟨fun h => hu_notV2 (h ▸ (hint_sp e he).1), fun h => hu_notV2 (h ▸ (hint_sp e he).2)⟩
    have hpend_zero : (E_pend.map fun e => if e.1 = emb u then 1 else 0).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have hne : e.1 ≠ emb u := fun h => hu_notV2 (h ▸ (hpend_sp e he).1)
      simp [hne]
    rw [hd_get, hint_zero, hpend_zero]

/-- Main positivity theorem: `L` is nonnegative on EVERY square-graph generator on `Fin 23`! -/
private lemma L_prod_nonneg (E : List (Fin 23 × Fin 23)) :
    0 ≤ L ((E.map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) := by
  rw [L_prod_eq_evalEdgesM]
  by_cases hlen : E.length = 6
  swap
  · rw [evalEdgesM_eq_zero_of_ne_12 E 0 0 (by simp; omega)]; norm_num
  by_cases hloop : ∃ e ∈ E, e.1 = e.2
  · obtain ⟨⟨u, v⟩, hmem, huv⟩ := hloop
    dsimp only at huv
    subst huv
    have hperm : E.Perm ((u, u) :: E.erase (u, u)) := List.perm_cons_erase hmem
    rw [evalEdgesM_perm hperm, evalEdgesM_loop]; norm_num
  push Not at hloop
  -- Construct `V2` = vertices of degree `≥ 2`, sorted descending by `deg23 E`
  let V2_raw : List (Fin 23) := (List.finRange 23).filter (fun v => 2 ≤ deg23 E v)
  let V2 : List (Fin 23) := sortByDesc (deg23 E) V2_raw
  have hV2_perm : V2.Perm V2_raw := sortByDesc_perm _ _
  have hV2_nd : V2.Nodup := hV2_perm.nodup_iff.mpr ((List.nodup_finRange 23).filter _)
  have hV2_mem : ∀ v : Fin 23, v ∈ V2 ↔ 2 ≤ deg23 E v := fun v => by
    rw [hV2_perm.mem_iff]
    simp [V2_raw, List.mem_finRange]
  have hV2_pw : V2.Pairwise (fun a b => deg23 E b ≤ deg23 E a) := sortByDesc_pairwise _ _
  have hV2_sum_le : (V2.map (deg23 E)).sum ≤ 12 := by
    have h1 : (V2.map (deg23 E)).sum = ∑ v ∈ V2.toFinset, deg23 E v := by
      rw [← List.sum_toFinset _ hV2_nd]
    rw [h1]
    calc ∑ v ∈ V2.toFinset, deg23 E v
        ≤ ∑ v : Fin 23, deg23 E v := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = 2 * E.length := sum_deg23 E
      _ = 12 := by omega
  have hV2_le6 : V2.length ≤ 6 := by
    have h2 : 2 * V2.length ≤ (V2.map (deg23 E)).sum := by
      have : ∀ l : List (Fin 23), (∀ x ∈ l, 2 ≤ deg23 E x) → 2 * l.length ≤ (l.map (deg23 E)).sum := by
        intro l; induction l with
        | nil => intro _; simp
        | cons a as ih =>
            intro ha
            simp only [List.length_cons, List.map_cons, List.sum_cons]
            have h1 := ha a (List.mem_cons_self ..)
            have h2 := ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
            omega
      exact this V2 (fun x hx => (hV2_mem x).mp hx)
    omega
  -- Extend `V2` to a nodup list of length 23 to get an injection `emb : Fin 6 → Fin 23`
  let extL : List (Fin 23) := V2 ++ (List.finRange 23).filter (fun v => v ∉ V2)
  have hext_nd : extL.Nodup := by
    rw [List.nodup_append]
    refine ⟨hV2_nd, (List.nodup_finRange 23).filter _, fun x hx y hy hxy => ?_⟩
    subst hxy
    exact (of_decide_eq_true (List.mem_filter.mp hy).2) hx
  have hext_len : extL.length = 23 := by
    have hperm_all : extL.Perm (List.finRange 23) := by
      refine (List.perm_ext_iff_of_nodup hext_nd (List.nodup_finRange 23)).mpr fun x => ?_
      simp only [extL, List.mem_append, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq, iff_true]
      exact em (x ∈ V2)
    rw [hperm_all.length_eq, List.length_finRange]
  let emb : Fin 6 → Fin 23 := fun u => extL[u.val]'(by omega)
  have hemb_inj : Function.Injective emb := by
    intro a b hab
    have h1 : (⟨a.val, by omega⟩ : Fin extL.length) = ⟨b.val, by omega⟩ :=
      (List.nodup_iff_injective_getElem.mp hext_nd) hab
    exact Fin.ext (congrArg (fun z : Fin extL.length => z.val) h1)
  have hemb_V2 : ∀ (i : Fin 6) (hi : i.val < V2.length), emb i = V2[i.val] := by
    intro i hi
    simp only [emb, extL, List.getElem_append_left hi]
  have hemb_cov : ∀ x ∈ V2, ∃ u : Fin 6, emb u = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨⟨i, by omega⟩, hemb_V2 ⟨i, by omega⟩ hi⟩
  -- Split `E` into `(E_iso, E_pend, E_int)`
  rcases hsp : orientAndSplit V2 E with ⟨E_iso, E_pend, E_int⟩
  have hsp_props := orientAndSplit_eval V2 E
  rw [hsp] at hsp_props
  rcases hsp_props with ⟨heval_sp, hdeg_sp, hlen_sp, hloop_sp, hiso_sp, hpend_sp, hint_sp⟩
  rcases hloop_sp hloop with ⟨hl_iso, hl_pend, hl_int⟩
  simp only at heval_sp hdeg_sp hlen_sp hiso_sp hpend_sp hint_sp hl_iso hl_pend hl_int
  -- Pull `E_pend` and `E_int` back to `Fin 6` via `emb`
  have hinv_ex : ∀ x ∈ V2, ∃! u : Fin 6, emb u = x := fun x hx => by
    obtain ⟨u, hu⟩ := hemb_cov x hx
    exact ⟨u, hu, fun v hv => hemb_inj (hv.trans hu.symm)⟩
  let invV2 : Fin 23 → Fin 6 := fun x =>
    if h : ∃ u : Fin 6, emb u = x then Classical.choose h else 0
  have hinv_emb : ∀ x ∈ V2, emb (invV2 x) = x := by
    intro x hx
    have hex : ∃ u : Fin 6, emb u = x := hemb_cov x hx
    simp only [invV2, dif_pos hex]
    exact Classical.choose_spec hex
  let pe6 : List (Fin 6) := E_pend.map (fun e => invV2 e.1)
  let ie6_raw : List (Fin 6 × Fin 6) := E_int.map (fun e => (invV2 e.1, invV2 e.2))
  have hpe6_map : E_pend.map Prod.fst = pe6.map emb := by
    simp only [pe6, List.map_map]
    refine List.map_congr_left fun e he => ?_
    exact (hinv_emb e.1 (hpend_sp e he).1).symm
  have hie6_map : E_int = ie6_raw.map (fun e => (emb e.1, emb e.2)) := by
    simp only [ie6_raw, List.map_map]
    symm
    conv_rhs => rw [← List.map_id E_int]
    refine List.map_congr_left fun e he => ?_
    rcases e with ⟨a, b⟩
    simp only [Function.comp_apply, id_eq, Prod.mk.injEq]
    exact ⟨hinv_emb a (hint_sp (a, b) he).1, hinv_emb b (hint_sp (a, b) he).2⟩
  have hdeg1 : ∀ w : Fin 23, w ∉ V2 → deg23 (E_iso ++ E_pend ++ E_int) w ≤ 1 := by
    intro w hw
    rw [← hdeg_sp w]
    have : ¬ (2 ≤ deg23 E w) := fun h => hw ((hV2_mem w).mpr h)
    omega
  rw [heval_sp 0 0, evalEdgesM_peel_iso_pend V2 hV2_nd hV2_le6 E_iso E_pend E_int
    hl_iso hl_pend (fun e he => (hpend_sp e he).1) (fun e he => (hpend_sp e he).2)
    hiso_sp hint_sp hdeg1 emb hemb_inj hemb_cov pe6 hpe6_map ie6_raw hie6_map]
  -- Orient `ie6_raw` so every edge satisfies `e.1 < e.2`
  let ie6 : List (Fin 6 × Fin 6) := ie6_raw.map fun e => if e.1 ≤ e.2 then e else (e.2, e.1)
  rw [evalSem6_orient_ie ie6_raw pe6]
  have hie6_lt : ∀ e ∈ ie6, e.1 < e.2 := by
    intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp he
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := List.mem_map.mp hab
    have hne_xy : x ≠ y := hl_int (x, y) hxy
    have hab_ne : a ≠ b := by
      intro h; apply hne_xy
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      rw [← hinv_emb x (hint_sp (x, y) hxy).1, ← hinv_emb y (hint_sp (x, y) hxy).2, h]
    split_ifs with hle
    · exact lt_of_le_of_ne hle hab_ne
    · exact lt_of_not_ge hle
  -- Match `(ie6, pe6, E_iso.length)` to its canonical config in `configsOfD d`!
  let d : List ℕ := V2.map (deg23 E)
  have hd_sum_le : d.sum ≤ 12 := hV2_sum_le
  have hd_parts : ∀ x ∈ d, 2 ≤ x ∧ x ≤ 6 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    refine ⟨(hV2_mem v).mp hv, ?_⟩
    -- Since `E` is loopless, each edge contributes at most 1 to `deg23 E v`, so `deg23 E v ≤ E.length = 6`!
    have hle_len : ∀ L : List (Fin 23 × Fin 23), (∀ e ∈ L, e.1 ≠ e.2) → deg23 L v ≤ L.length := by
      intro L; induction L with
      | nil => intro _; simp [deg23]
      | cons e rs ih =>
          intro hl
          rcases e with ⟨a, b⟩
          have hne := hl (a, b) (List.mem_cons_self ..)
          have hih := ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
          simp only [deg23_cons, List.length_cons] at hih ⊢
          by_cases ha : a = v <;> by_cases hb : b = v
          · exact absurd (ha.trans hb.symm) hne
          · simp [ha, hb]; omega
          · simp [ha, hb]; omega
          · simp [ha, hb]; omega
    have := hle_len E hloop; omega
  have hd_pw : d.Pairwise (· ≥ ·) := List.pairwise_map.mpr hV2_pw
  have hd_mem : d ∈ parts2to6 d.sum 6 := mem_parts2to6 d d.sum 6 rfl hd_parts hd_pw
  -- Multiplicity function `mfn` of `ie6` on `pairs6`
  let mfn : Fin 6 × Fin 6 → ℕ := fun e => ie6.count e
  have hpairs_nd : pairs6.Nodup := by decide
  have hpairs_lt : ∀ e ∈ pairs6, e.1 < e.2 := by decide
  have hie6_perm : ie6.Perm (pairs6.flatMap fun e => List.replicate (mfn e) e) :=
    ie6_perm_pairs6 ie6 hie6_lt
  have hemb_notV2 : ∀ (i : Fin 6), ¬ i.val < V2.length → emb i ∉ V2 := by
    intro u hu
    have hmem_ext : emb u = ((List.finRange 23).filter (fun v => v ∉ V2))[u.val - V2.length]'(by
        have : V2.length + ((List.finRange 23).filter (fun v => v ∉ V2)).length = 23 := by
          simpa [extL] using hext_len
        omega) := by
      simp only [emb, extL, List.getElem_append_right (by omega : V2.length ≤ u.val)]
    rw [hmem_ext]
    have hm := List.getElem_mem (l := (List.finRange 23).filter (fun v => v ∉ V2))
      (n := u.val - V2.length) (by
        have : V2.length + ((List.finRange 23).filter (fun v => v ∉ V2)).length = 23 := by
          simpa [extL] using hext_len
        omega)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  -- Degree identity on `Fin 6`: for each `u : Fin 6`, `degFnFromList d u = intDeg u + pe6.count u`!
  have hdeg_split6 : ∀ u : Fin 6,
      degFnFromList d u =
        (pairs6.map fun e => (if e.1 = u then mfn e else 0) +
                             (if e.2 = u then mfn e else 0)).sum + pe6.count u := fun u =>
    deg_split6_helper E E_iso E_pend E_int V2 emb hemb_inj hemb_V2 hemb_notV2
      hdeg_sp hiso_sp hpend_sp hint_sp pe6 ie6_raw ie6 hpe6_map hie6_map rfl hie6_perm u
  -- Apply `mem_genFromPairs`!
  have hmfn_sum : (pairs6.map mfn).sum = E_int.length := by
    have h1 : (pairs6.flatMap fun e => List.replicate (mfn e) e).length = (pairs6.map mfn).sum := by
      rw [List.length_flatMap]
      congr 1
      refine List.map_congr_left fun e _ => List.length_replicate ..
    rw [← h1, ← hie6_perm.length_eq]
    simp [ie6, ie6_raw]
  have hd_sum_6 : degFnFromList d 0 + degFnFromList d 1 + degFnFromList d 2 +
      degFnFromList d 3 + degFnFromList d 4 + degFnFromList d 5 = d.sum := by
    have hlen_d : d.length ≤ 6 := by simpa [d] using hV2_le6
    have hgen : ∀ l : List ℕ, l.length ≤ 6 →
        l.getD 0 0 + l.getD 1 0 + l.getD 2 0 + l.getD 3 0 + l.getD 4 0 + l.getD 5 0 = l.sum := by
      intro l hl
      rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hl ⊢ <;> omega
    exact hgen d hlen_d
  have hpe6_sum : pe6.count 0 + pe6.count 1 + pe6.count 2 + pe6.count 3 + pe6.count 4 + pe6.count 5 =
      E_pend.length := by
    have hc : ∀ l : List (Fin 6),
        l.count 0 + l.count 1 + l.count 2 + l.count 3 + l.count 4 + l.count 5 = l.length := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => fin_cases a <;> simp <;> omega
    rw [hc pe6]; simp [pe6]
  have hdeg_sum_tot : d.sum = 2 * E_int.length + E_pend.length := by
    have h2 : ∀ l : List (Fin 6 × Fin 6),
        (l.map fun e => (if e.1 = 0 then mfn e else 0) + (if e.2 = 0 then mfn e else 0)).sum +
        (l.map fun e => (if e.1 = 1 then mfn e else 0) + (if e.2 = 1 then mfn e else 0)).sum +
        (l.map fun e => (if e.1 = 2 then mfn e else 0) + (if e.2 = 2 then mfn e else 0)).sum +
        (l.map fun e => (if e.1 = 3 then mfn e else 0) + (if e.2 = 3 then mfn e else 0)).sum +
        (l.map fun e => (if e.1 = 4 then mfn e else 0) + (if e.2 = 4 then mfn e else 0)).sum +
        (l.map fun e => (if e.1 = 5 then mfn e else 0) + (if e.2 = 5 then mfn e else 0)).sum =
        2 * (l.map mfn).sum := by
      intro l; induction l with
      | nil => simp
      | cons e ls ih =>
          rcases e with ⟨a, b⟩
          simp only [List.map_cons, List.sum_cons]
          have ha : (if a = 0 then mfn (a, b) else 0) + (if a = 1 then mfn (a, b) else 0) +
              (if a = 2 then mfn (a, b) else 0) + (if a = 3 then mfn (a, b) else 0) +
              (if a = 4 then mfn (a, b) else 0) + (if a = 5 then mfn (a, b) else 0) = mfn (a, b) := by
            fin_cases a <;> simp
          have hb : (if b = 0 then mfn (a, b) else 0) + (if b = 1 then mfn (a, b) else 0) +
              (if b = 2 then mfn (a, b) else 0) + (if b = 3 then mfn (a, b) else 0) +
              (if b = 4 then mfn (a, b) else 0) + (if b = 5 then mfn (a, b) else 0) = mfn (a, b) := by
            fin_cases b <;> simp
          omega
    have h0 := hdeg_split6 0; have h1 := hdeg_split6 1; have h2' := hdeg_split6 2
    have h3 := hdeg_split6 3; have h4 := hdeg_split6 4; have h5 := hdeg_split6 5
    have ht := h2 pairs6
    omega
  have hcfg_mem := mem_genFromPairs pairs6 hpairs_nd hpairs_lt mfn (degFnFromList d) 6
    (fun u => by have := hdeg_split6 u; omega)
    (by rw [hmfn_sum, hd_sum_6, hdeg_sum_tot]; omega)
  -- `pe6` is a permutation of `pendsFromRem (fun u => pe6.count u)`
  have hpe_rem_eq : (fun u => degFnFromList d u -
      (pairs6.map fun e => (if e.1 = u then mfn e else 0) +
                           (if e.2 = u then mfn e else 0)).sum) =
      fun u => pe6.count u := by
    funext u; have := hdeg_split6 u; omega
  have hiso_eq : 6 - ((pairs6.map mfn).sum +
      (degFnFromList d 0 + degFnFromList d 1 + degFnFromList d 2 +
       degFnFromList d 3 + degFnFromList d 4 + degFnFromList d 5 - 2 * (pairs6.map mfn).sum)) =
      E_iso.length := by
    rw [hmfn_sum, hd_sum_6, hdeg_sum_tot]; omega
  rw [hpe_rem_eq, hiso_eq] at hcfg_mem
  have hpe6_perm : pe6.Perm (pendsFromRem fun u => pe6.count u) := by
    rw [List.perm_iff_count]
    intro u
    unfold pendsFromRem
    rw [List.count_flatMap]
    have hgen : ∀ l : List (Fin 6), l.Nodup → u ∈ l →
        (l.map fun x => List.count u (List.replicate (pe6.count x) x)).sum = pe6.count u := by
      intro l; induction l with
      | nil => intro _ h; simp at h
      | cons a as ih =>
          intro hnd hmem
          rcases List.nodup_cons.mp hnd with ⟨ha_not, has_nd⟩
          simp only [List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · have h0 : (as.map fun x => List.count u (List.replicate (pe6.count x) x)).sum = 0 := by
              apply List.sum_eq_zero
              intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
              have hne : u ≠ x := fun h => ha_not (h ▸ hx)
              simp [List.count_replicate, Ne.symm hne]
            rw [h0, add_zero, List.count_replicate_self]
          · have hne : a ≠ u := fun h => ha_not (h ▸ hmem')
            rw [ih has_nd hmem']
            simp [List.count_replicate, hne]
    simpa only [Function.comp_def] using
      (hgen (List.finRange 6) (List.nodup_finRange 6) (List.mem_finRange u)).symm
  rw [evalSem6_perm_ie_general hie6_perm pe6, evalSem6_perm_pe hpe6_perm, ← evalFast_eq_evalSem6]
  have hnonneg : (0 : ℤ) ≤ evalFast (pairs6.flatMap fun e => List.replicate (mfn e) e)
      (pendsFromRem fun u => pe6.count u) 0 0 0 0 0 0 E_iso.length :=
    check_all_S hd_sum_le hd_mem hcfg_mem
  have hpow_pos : (0 : ℤ) ≤ 2 ^ E_iso.length := by positivity
  have hmul : (0 : ℤ) ≤ 2 ^ E_iso.length * evalFast (pairs6.flatMap fun e => List.replicate (mfn e) e)
      (pendsFromRem fun u => pe6.count u) 0 0 0 0 0 0 E_iso.length := mul_nonneg hpow_pos hnonneg
  exact_mod_cast hmul

/-! ## Section 4: Exact evaluation `L (terminalQuarticDisc 23) = -9139578164640000 < 0` -/

private def fin4To23 (i : Fin 4) : Fin 23 := ⟨i.val, by omega⟩

private lemma fin4To23_inj : Function.Injective fin4To23 := fun _ _ h =>
  Fin.ext (congrArg (fun z : Fin 23 => z.val) h)

private noncomputable def spec4 : MvPolynomial (Fin 23) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.aeval (fun i : Fin 23 =>
    if h : i.val < 4 then MvPolynomial.X ⟨i.val, h⟩ else (0 : MvPolynomial (Fin 4) ℝ))

private lemma spec4_esymm (j : ℕ) :
    spec4 (esymmPoly 23 j) = MvPolynomial.esymm (Fin 4) ℝ j := by
  unfold esymmPoly MvPolynomial.esymm
  rw [map_sum]
  let S4 : Finset (Fin 23) := Finset.univ.filter (fun i : Fin 23 => i.val < 4)
  have hzero : ∀ t ∈ (Finset.univ : Finset (Fin 23)).powersetCard j,
      ¬ t ⊆ S4 → spec4 (∏ i ∈ t, MvPolynomial.X i) = 0 := by
    intro t _ hnot
    rw [Finset.not_subset] at hnot
    obtain ⟨i0, hi0, hnot4⟩ := hnot
    have hge : ¬ i0.val < 4 := by
      simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hnot4; exact hnot4
    rw [map_prod]
    exact Finset.prod_eq_zero hi0 (by simp [spec4, hge])
  rw [← Finset.sum_subset (Finset.powersetCard_mono (Finset.subset_univ S4)) (fun t ht hnot => by
    apply hzero t ht
    intro hsub; exact hnot (Finset.mem_powersetCard.mpr ⟨hsub, (Finset.mem_powersetCard.mp ht).2⟩))]
  refine Finset.sum_bij (fun t _ => t.preimage fin4To23 (fin4To23_inj.injOn)) ?_ ?_ ?_ ?_
  · intro t ht
    rcases Finset.mem_powersetCard.mp ht with ⟨hsub, hcard⟩
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    have hmap : (t.preimage fin4To23 (fin4To23_inj.injOn)).map ⟨fin4To23, fin4To23_inj⟩ = t := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx
        have hx4 : x.val < 4 := (Finset.mem_filter.mp (hsub hx)).2
        exact ⟨⟨x.val, hx4⟩, by simpa [fin4To23] using hx, Fin.ext rfl⟩
    rw [← Finset.card_map ⟨fin4To23, fin4To23_inj⟩, hmap, hcard]
  · intro t1 ht1 t2 ht2 heq
    have h1 := (Finset.mem_powersetCard.mp ht1).1
    have h2 := (Finset.mem_powersetCard.mp ht2).1
    ext x
    constructor
    · intro hx
      have hx4 : x.val < 4 := (Finset.mem_filter.mp (h1 hx)).2
      have hmem : (⟨x.val, hx4⟩ : Fin 4) ∈ t1.preimage fin4To23 (fin4To23_inj.injOn) := by
        simpa [fin4To23] using hx
      rw [heq] at hmem
      simpa [fin4To23] using hmem
    · intro hx
      have hx4 : x.val < 4 := (Finset.mem_filter.mp (h2 hx)).2
      have hmem : (⟨x.val, hx4⟩ : Fin 4) ∈ t2.preimage fin4To23 (fin4To23_inj.injOn) := by
        simpa [fin4To23] using hx
      rw [← heq] at hmem
      simpa [fin4To23] using hmem
  · intro s hs
    rcases Finset.mem_powersetCard.mp hs with ⟨_, hcard⟩
    refine ⟨s.map ⟨fin4To23, fin4To23_inj⟩, Finset.mem_powersetCard.mpr ⟨?_, by rw [Finset.card_map, hcard]⟩, ?_⟩
    · intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      simp [S4, fin4To23, a.isLt]
    · ext a; simp
  · intro t ht
    have hsub := (Finset.mem_powersetCard.mp ht).1
    rw [map_prod]
    refine Finset.prod_bij (fun x _ => ⟨x.val, (Finset.mem_filter.mp (hsub (by assumption))).2⟩) ?_ ?_ ?_ ?_
    · intro x hx; simpa [fin4To23] using hx
    · intro x1 _ x2 _ h; exact Fin.ext (congrArg (fun z : Fin 4 => z.val) h)
    · intro a ha; exact ⟨fin4To23 a, Finset.mem_preimage.mp ha, Fin.ext rfl⟩
    · intro x hx
      have hx4 : x.val < 4 := (Finset.mem_filter.mp (hsub hx)).2
      simp [spec4, hx4]

private lemma spec4_coeff (f : MvPolynomial (Fin 23) ℝ) (β : Fin 4 →₀ ℕ) :
    (spec4 f).coeff β = f.coeff (β.mapDomain fin4To23) := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
  | monomial α c =>
      rw [MvPolynomial.coeff_monomial]
      by_cases hsub : ∀ i ∈ α.support, i.val < 4
      · let α4 : Fin 4 →₀ ℕ := α.comapDomain fin4To23 (fin4To23_inj.injOn)
        have hmap_eq : α4.mapDomain fin4To23 = α := by
          ext i
          by_cases hi : i.val < 4
          · have hi_eq : i = fin4To23 ⟨i.val, hi⟩ := Fin.ext rfl
            rw [hi_eq, Finsupp.mapDomain_apply fin4To23_inj]
            simp [α4]
          · have h0 : α i = 0 := by
              by_contra hne; exact hi (hsub i (Finsupp.mem_support_iff.mpr hne))
            rw [h0]
            exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨a, ha⟩; exact hi (ha ▸ a.isLt))
        have hspec_mon : spec4 (MvPolynomial.monomial α c) = MvPolynomial.monomial α4 c := by
          rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
          have hC : spec4 (MvPolynomial.C c) = MvPolynomial.C c := MvPolynomial.aeval_C _ c
          rw [hC]
          have hprod : (∏ x ∈ α.support, spec4 (MvPolynomial.X x ^ α x)) =
              ∏ a ∈ α4.support, MvPolynomial.X a ^ α4 a := by
            refine Finset.prod_bij (fun x hx => ⟨x.val, hsub x hx⟩) ?_ ?_ ?_ ?_
            · intro x hx
              rw [Finsupp.mem_support_iff] at hx ⊢
              simpa [α4, fin4To23] using hx
            · intro x1 _ x2 _ h; exact Fin.ext (congrArg (fun z : Fin 4 => z.val) h)
            · intro a ha
              rw [Finsupp.mem_support_iff] at ha
              refine ⟨fin4To23 a, Finsupp.mem_support_iff.mpr (by simpa [α4] using ha), Fin.ext rfl⟩
            · intro x hx
              have hx4 := hsub x hx
              simp [spec4, hx4, α4, fin4To23]
          rw [hprod, MvPolynomial.monomial_eq, Finsupp.prod]
        rw [hspec_mon, MvPolynomial.coeff_monomial]
        have hiff : α4 = β ↔ α = β.mapDomain fin4To23 := by
          constructor
          · rintro rfl; exact hmap_eq.symm
          · intro h; rw [← hmap_eq] at h; exact Finsupp.mapDomain_injective fin4To23_inj h
        simp [hiff]
      · push Not at hsub
        obtain ⟨i0, hi0, hge⟩ := hsub
        have hnotlt : ¬ i0.val < 4 := by omega
        have hspec_zero : spec4 (MvPolynomial.monomial α c) = 0 := by
          rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
          have h0 : (∏ x ∈ α.support, spec4 (MvPolynomial.X x ^ α x)) = 0 := by
            refine Finset.prod_eq_zero hi0 ?_
            rw [map_pow]
            simp only [spec4, MvPolynomial.aeval_X, dif_neg hnotlt]
            exact zero_pow (Finsupp.mem_support_iff.mp hi0)
          rw [h0, mul_zero]
        have hne : α ≠ β.mapDomain fin4To23 := by
          intro heq
          have h1 : α i0 ≠ 0 := Finsupp.mem_support_iff.mp hi0
          have h2 : (β.mapDomain fin4To23) i0 = 0 :=
            Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨a, ha⟩; exact hnotlt (ha ▸ a.isLt))
          exact h1 (heq ▸ h2)
        rw [hspec_zero, MvPolynomial.coeff_zero, if_neg hne]

private noncomputable def mon4 (k0 k1 k2 k3 : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 k0 + Finsupp.single 1 k1 + Finsupp.single 2 k2 + Finsupp.single 3 k3

private lemma mon4_apply (k0 k1 k2 k3 : ℕ) :
    mon4 k0 k1 k2 k3 0 = k0 ∧ mon4 k0 k1 k2 k3 1 = k1 ∧
    mon4 k0 k1 k2 k3 2 = k2 ∧ mon4 k0 k1 k2 k3 3 = k3 := by
  simp [mon4]

private lemma mon4_add (k0 k1 k2 k3 d0 d1 d2 d3 : ℕ) :
    mon4 k0 k1 k2 k3 + mon4 d0 d1 d2 d3 = mon4 (k0 + d0) (k1 + d1) (k2 + d2) (k3 + d3) := by
  ext i; fin_cases i <;> simp [mon4]

private lemma coeff_mul_mon4 (f : MvPolynomial (Fin 4) ℝ) (d0 d1 d2 d3 k0 k1 k2 k3 : ℕ) :
    (f * MvPolynomial.monomial (mon4 d0 d1 d2 d3) 1).coeff (mon4 k0 k1 k2 k3) =
      if d0 ≤ k0 ∧ d1 ≤ k1 ∧ d2 ≤ k2 ∧ d3 ≤ k3 then
        f.coeff (mon4 (k0 - d0) (k1 - d1) (k2 - d2) (k3 - d3))
      else 0 := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [add_mul, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
      split_ifs <;> simp
  | monomial α c =>
      rw [MvPolynomial.monomial_mul, mul_one, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      by_cases hle : d0 ≤ k0 ∧ d1 ≤ k1 ∧ d2 ≤ k2 ∧ d3 ≤ k3
      · rw [if_pos hle]
        have hiff : α + mon4 d0 d1 d2 d3 = mon4 k0 k1 k2 k3 ↔
            α = mon4 (k0 - d0) (k1 - d1) (k2 - d2) (k3 - d3) := by
          constructor
          · intro h; ext i
            have hi := congrArg (fun g : Fin 4 →₀ ℕ => g i) h
            fin_cases i <;> simp [mon4] at hi ⊢ <;> omega
          · rintro rfl; rw [mon4_add]; congr 1 <;> omega
        simp [hiff]
      · rw [if_neg hle]
        have hne : α + mon4 d0 d1 d2 d3 ≠ mon4 k0 k1 k2 k3 := by
          intro h; apply hle
          have h0 := congrArg (fun g : Fin 4 →₀ ℕ => g 0) h
          have h1 := congrArg (fun g : Fin 4 →₀ ℕ => g 1) h
          have h2 := congrArg (fun g : Fin 4 →₀ ℕ => g 2) h
          have h3 := congrArg (fun g : Fin 4 →₀ ℕ => g 3) h
          simp only [Finsupp.add_apply, mon4_apply] at h0 h1 h2 h3
          omega
        rw [if_neg hne]

private lemma esymm4_1 :
    MvPolynomial.esymm (Fin 4) ℝ 1 =
      MvPolynomial.monomial (mon4 1 0 0 0) 1 + MvPolynomial.monomial (mon4 0 1 0 0) 1 +
      MvPolynomial.monomial (mon4 0 0 1 0) 1 + MvPolynomial.monomial (mon4 0 0 0 1) 1 := by
  unfold MvPolynomial.esymm
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 1 = {{0}, {1}, {2}, {3}} := by decide
  rw [hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.prod_singleton, MvPolynomial.X, mon4, Finsupp.single_zero, add_zero, zero_add]
  ring

private lemma esymm4_2 :
    MvPolynomial.esymm (Fin 4) ℝ 2 =
      MvPolynomial.monomial (mon4 1 1 0 0) 1 + MvPolynomial.monomial (mon4 1 0 1 0) 1 +
      MvPolynomial.monomial (mon4 1 0 0 1) 1 + MvPolynomial.monomial (mon4 0 1 1 0) 1 +
      MvPolynomial.monomial (mon4 0 1 0 1) 1 + MvPolynomial.monomial (mon4 0 0 1 1) 1 := by
  unfold MvPolynomial.esymm
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide
  rw [hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hmul : ∀ i j : Fin 4, i ≠ j →
      (∏ k ∈ ({i, j} : Finset (Fin 4)), (MvPolynomial.X k : MvPolynomial (Fin 4) ℝ)) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
    intro i j hij
    rw [Finset.prod_pair hij, MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
  rw [hmul 0 1 (by decide), hmul 0 2 (by decide), hmul 0 3 (by decide),
    hmul 1 2 (by decide), hmul 1 3 (by decide), hmul 2 3 (by decide)]
  simp only [mon4, Finsupp.single_zero, add_zero, zero_add]
  ring

private lemma esymm4_3 :
    MvPolynomial.esymm (Fin 4) ℝ 3 =
      MvPolynomial.monomial (mon4 1 1 1 0) 1 + MvPolynomial.monomial (mon4 1 1 0 1) 1 +
      MvPolynomial.monomial (mon4 1 0 1 1) 1 + MvPolynomial.monomial (mon4 0 1 1 1) 1 := by
  unfold MvPolynomial.esymm
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 3 =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by decide
  rw [hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hmul : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      (∏ k ∈ ({a, b, c} : Finset (Fin 4)), (MvPolynomial.X k : MvPolynomial (Fin 4) ℝ)) =
      MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1) 1 := by
    intro a b c hab hac hbc
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc,
      MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
      MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, mul_one, mul_one, add_assoc]
  rw [hmul 0 1 2 (by decide) (by decide) (by decide),
    hmul 0 1 3 (by decide) (by decide) (by decide),
    hmul 0 2 3 (by decide) (by decide) (by decide),
    hmul 1 2 3 (by decide) (by decide) (by decide)]
  simp only [mon4, Finsupp.single_zero, add_zero, zero_add]
  ring

private lemma esymm4_4 :
    MvPolynomial.esymm (Fin 4) ℝ 4 = MvPolynomial.monomial (mon4 1 1 1 1) 1 := by
  unfold MvPolynomial.esymm
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 4 = {{0, 1, 2, 3}} := by decide
  rw [hp, Finset.sum_singleton]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3),
    MvPolynomial.X, MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, MvPolynomial.monomial_mul,
    mul_one, mul_one, mul_one]
  congr 1; simp [mon4, add_assoc]

/-- Structurally recursive 4-stage recurrence for `coeff (mon4 k0 k1 k2 k3)` of `e1^a1 * e2^a2 * e3^a3 * e4^a4`. -/
private def ec4_1 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, k0, k1, k2, k3 => if k0 = 0 ∧ k1 = 0 ∧ k2 = 0 ∧ k3 = 0 then 1 else 0
  | a1 + 1, k0, k1, k2, k3 =>
      (if 1 ≤ k0 then ec4_1 a1 (k0 - 1) k1 k2 k3 else 0) +
      (if 1 ≤ k1 then ec4_1 a1 k0 (k1 - 1) k2 k3 else 0) +
      (if 1 ≤ k2 then ec4_1 a1 k0 k1 (k2 - 1) k3 else 0) +
      (if 1 ≤ k3 then ec4_1 a1 k0 k1 k2 (k3 - 1) else 0)

private def ec4_2 (a1 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, k0, k1, k2, k3 => ec4_1 a1 k0 k1 k2 k3
  | a2 + 1, k0, k1, k2, k3 =>
      (if 1 ≤ k0 ∧ 1 ≤ k1 then ec4_2 a1 a2 (k0 - 1) (k1 - 1) k2 k3 else 0) +
      (if 1 ≤ k0 ∧ 1 ≤ k2 then ec4_2 a1 a2 (k0 - 1) k1 (k2 - 1) k3 else 0) +
      (if 1 ≤ k0 ∧ 1 ≤ k3 then ec4_2 a1 a2 (k0 - 1) k1 k2 (k3 - 1) else 0) +
      (if 1 ≤ k1 ∧ 1 ≤ k2 then ec4_2 a1 a2 k0 (k1 - 1) (k2 - 1) k3 else 0) +
      (if 1 ≤ k1 ∧ 1 ≤ k3 then ec4_2 a1 a2 k0 (k1 - 1) k2 (k3 - 1) else 0) +
      (if 1 ≤ k2 ∧ 1 ≤ k3 then ec4_2 a1 a2 k0 k1 (k2 - 1) (k3 - 1) else 0)

private def ec4_3 (a1 a2 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, k0, k1, k2, k3 => ec4_2 a1 a2 k0 k1 k2 k3
  | a3 + 1, k0, k1, k2, k3 =>
      (if 1 ≤ k0 ∧ 1 ≤ k1 ∧ 1 ≤ k2 then ec4_3 a1 a2 a3 (k0 - 1) (k1 - 1) (k2 - 1) k3 else 0) +
      (if 1 ≤ k0 ∧ 1 ≤ k1 ∧ 1 ≤ k3 then ec4_3 a1 a2 a3 (k0 - 1) (k1 - 1) k2 (k3 - 1) else 0) +
      (if 1 ≤ k0 ∧ 1 ≤ k2 ∧ 1 ≤ k3 then ec4_3 a1 a2 a3 (k0 - 1) k1 (k2 - 1) (k3 - 1) else 0) +
      (if 1 ≤ k1 ∧ 1 ≤ k2 ∧ 1 ≤ k3 then ec4_3 a1 a2 a3 k0 (k1 - 1) (k2 - 1) (k3 - 1) else 0)

private def ec4 (a1 a2 a3 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, k0, k1, k2, k3 => ec4_3 a1 a2 a3 k0 k1 k2 k3
  | a4 + 1, k0, k1, k2, k3 =>
      if 1 ≤ k0 ∧ 1 ≤ k1 ∧ 1 ≤ k2 ∧ 1 ≤ k3 then ec4 a1 a2 a3 a4 (k0 - 1) (k1 - 1) (k2 - 1) (k3 - 1)
      else 0

private lemma ec4_1_eq_coeff (a1 : ℕ) :
    ∀ k0 k1 k2 k3 : ℕ,
      (MvPolynomial.esymm (Fin 4) ℝ 1 ^ a1).coeff (mon4 k0 k1 k2 k3) =
        (ec4_1 a1 k0 k1 k2 k3 : ℝ) := by
  induction a1 with
  | zero =>
      intro k0 k1 k2 k3
      simp only [pow_zero, ec4_1]
      have h1 : (1 : MvPolynomial (Fin 4) ℝ) = MvPolynomial.monomial (mon4 0 0 0 0) 1 := by
        simp [mon4]
      rw [h1, MvPolynomial.coeff_monomial]
      have hiff : mon4 0 0 0 0 = mon4 k0 k1 k2 k3 ↔ k0 = 0 ∧ k1 = 0 ∧ k2 = 0 ∧ k3 = 0 := by
        constructor
        · intro h
          have c0 := congrArg (fun g : Fin 4 →₀ ℕ => g 0) h
          have c1 := congrArg (fun g : Fin 4 →₀ ℕ => g 1) h
          have c2 := congrArg (fun g : Fin 4 →₀ ℕ => g 2) h
          have c3 := congrArg (fun g : Fin 4 →₀ ℕ => g 3) h
          simp only [mon4_apply] at c0 c1 c2 c3
          exact ⟨c0.symm, c1.symm, c2.symm, c3.symm⟩
        · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
      rw [if_congr hiff rfl rfl]
      split_ifs <;> simp
  | succ a1 ih1 =>
      intro k0 k1 k2 k3
      rw [pow_succ]; nth_rw 2 [esymm4_1]
      rw [mul_add, mul_add, mul_add]
      simp only [MvPolynomial.coeff_add, coeff_mul_mon4, Nat.zero_le, true_and, and_true,
        Nat.sub_zero, ec4_1, ih1]
      push_cast; rfl

private lemma ec4_2_eq_coeff (a1 a2 : ℕ) :
    ∀ k0 k1 k2 k3 : ℕ,
      (MvPolynomial.esymm (Fin 4) ℝ 1 ^ a1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ a2).coeff
        (mon4 k0 k1 k2 k3) = (ec4_2 a1 a2 k0 k1 k2 k3 : ℝ) := by
  induction a2 with
  | zero => intro k0 k1 k2 k3; simpa [ec4_2] using ec4_1_eq_coeff a1 k0 k1 k2 k3
  | succ a2 ih2 =>
      intro k0 k1 k2 k3
      rw [pow_succ, ← mul_assoc]; nth_rw 2 [esymm4_2]
      rw [mul_add, mul_add, mul_add, mul_add, mul_add]
      simp only [MvPolynomial.coeff_add, coeff_mul_mon4, Nat.zero_le, true_and, and_true,
        Nat.sub_zero, ec4_2, ih2]
      push_cast; rfl

private lemma ec4_3_eq_coeff (a1 a2 a3 : ℕ) :
    ∀ k0 k1 k2 k3 : ℕ,
      (MvPolynomial.esymm (Fin 4) ℝ 1 ^ a1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ a2 *
       MvPolynomial.esymm (Fin 4) ℝ 3 ^ a3).coeff (mon4 k0 k1 k2 k3) =
        (ec4_3 a1 a2 a3 k0 k1 k2 k3 : ℝ) := by
  induction a3 with
  | zero => intro k0 k1 k2 k3; simpa [ec4_3] using ec4_2_eq_coeff a1 a2 k0 k1 k2 k3
  | succ a3 ih3 =>
      intro k0 k1 k2 k3
      rw [pow_succ, ← mul_assoc]; nth_rw 2 [esymm4_3]
      rw [mul_add, mul_add, mul_add]
      simp only [MvPolynomial.coeff_add, coeff_mul_mon4, Nat.zero_le, true_and, and_true,
        Nat.sub_zero, ec4_3, ih3]
      push_cast; rfl

private lemma ec4_eq_coeff (a1 a2 a3 a4 : ℕ) :
    ∀ k0 k1 k2 k3 : ℕ,
      (MvPolynomial.esymm (Fin 4) ℝ 1 ^ a1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ a2 *
       MvPolynomial.esymm (Fin 4) ℝ 3 ^ a3 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ a4).coeff
        (mon4 k0 k1 k2 k3) = (ec4 a1 a2 a3 a4 k0 k1 k2 k3 : ℝ) := by
  induction a4 with
  | zero => intro k0 k1 k2 k3; simpa [ec4] using ec4_3_eq_coeff a1 a2 a3 k0 k1 k2 k3
  | succ a4 ih4 =>
      intro k0 k1 k2 k3
      rw [pow_succ, ← mul_assoc]; nth_rw 2 [esymm4_4]
      rw [coeff_mul_mon4]
      simp only [ec4, ih4, apply_ite (Nat.cast (R := ℝ)), Nat.cast_zero]

/-- Exact integer formula for `coeff (mon4 k0 k1 k2 k3)` of `spec4 (terminalQuarticDisc 23)`. -/
private def discCoeff4 (k0 k1 k2 k3 : ℕ) : ℤ :=
  -151861137120000 * (ec4 4 0 0 2 k0 k1 k2 k3 : ℤ) +
   276111158400000 * (ec4 3 1 1 1 k0 k1 k2 k3 : ℤ) +
  -116872448000000 * (ec4 3 0 3 0 k0 k1 k2 k3 : ℤ) +
   -87853550400000 * (ec4 2 3 0 1 k0 k1 k2 k3 : ℤ) +
    41835024000000 * (ec4 2 2 2 0 k0 k1 k2 k3 : ℤ) +
   635055664320000 * (ec4 2 1 0 2 k0 k1 k2 k3 : ℤ) +
   -50401243200000 * (ec4 2 0 2 1 k0 k1 k2 k3 : ℤ) +
  -962205552000000 * (ec4 1 2 1 1 k0 k1 k2 k3 : ℤ) +
   412373808000000 * (ec4 1 1 3 0 k0 k1 k2 k3 : ℤ) +
  -463691437440000 * (ec4 1 0 1 2 k0 k1 k2 k3 : ℤ) +
   275540680800000 * (ec4 0 4 0 1 k0 k1 k2 k3 : ℤ) +
  -131209848000000 * (ec4 0 3 2 0 k0 k1 k2 k3 : ℤ) +
  -442614553920000 * (ec4 0 2 0 2 k0 k1 k2 k3 : ℤ) +
   948459758400000 * (ec4 0 1 2 1 k0 k1 k2 k3 : ℤ) +
  -338735628000000 * (ec4 0 0 4 0 k0 k1 k2 k3 : ℤ) +
   177748384352000 * (ec4 0 0 0 3 k0 k1 k2 k3 : ℤ)

private lemma terminalQuarticDisc23_coeff_mon4 (k0 k1 k2 k3 : ℕ) :
    (terminalQuarticDisc 23).coeff ((mon4 k0 k1 k2 k3).mapDomain fin4To23) =
      (discCoeff4 k0 k1 k2 k3 : ℝ) := by
  rw [← spec4_coeff]
  have hspec : spec4 (terminalQuarticDisc 23) =
      MvPolynomial.C (-151861137120000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 4 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 2) +
      MvPolynomial.C ( 276111158400000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C (-116872448000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 0) +
      MvPolynomial.C ( -87853550400000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C (  41835024000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 0) +
      MvPolynomial.C ( 635055664320000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 2) +
      MvPolynomial.C ( -50401243200000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C (-962205552000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C ( 412373808000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 0) +
      MvPolynomial.C (-463691437440000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 2) +
      MvPolynomial.C ( 275540680800000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 4 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C (-131209848000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 3 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 0) +
      MvPolynomial.C (-442614553920000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 2) +
      MvPolynomial.C ( 948459758400000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 1 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 2 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 1) +
      MvPolynomial.C (-338735628000000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 4 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 0) +
      MvPolynomial.C ( 177748384352000 : ℝ) * (MvPolynomial.esymm (Fin 4) ℝ 1 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 2 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 3 ^ 0 * MvPolynomial.esymm (Fin 4) ℝ 4 ^ 3) := by
    unfold terminalQuarticDisc quarticDisc
    have hc4 : Nat.choose 23 4 = 8855 := by decide
    have hc3 : Nat.choose (23 - 1) 3 = 1540 := by decide
    have hc2 : Nat.choose (23 - 2) 2 = 210 := by decide
    have hc1 : (23 - 3 : ℕ) = 20 := rfl
    rw [hc4, hc3, hc2, hc1]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      spec4_esymm, Nat.cast_ofNat, MvPolynomial.C_eq_algebraMap]
    ring
  rw [hspec]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, ec4_eq_coeff, discCoeff4]
  push_cast; ring

-- Verify all 10 shape coefficients of `terminalQuarticDisc 23` by `decide`!
private lemma discCoeff4_zero_shapes :
    discCoeff4 12 0 0 0 = 0 ∧ discCoeff4 10 2 0 0 = 0 ∧ discCoeff4 9 3 0 0 = 0 ∧
    discCoeff4 8 4 0 0 = 0 ∧ discCoeff4 7 5 0 0 = 0 ∧ discCoeff4 7 3 2 0 = 0 ∧
    discCoeff4 6 6 0 0 = 0 := by decide

private lemma discCoeff4_nonzero_shapes :
    discCoeff4 5 4 3 0 = 2807112000000 ∧
    discCoeff4 4 4 4 0 = 37417380000000 ∧
    discCoeff4 3 3 3 3 = -74374083168000 := by decide

private lemma rename_esymmPoly (σ : Equiv.Perm (Fin 23)) (j : ℕ) :
    MvPolynomial.rename σ (esymmPoly 23 j) = esymmPoly 23 j := by
  unfold esymmPoly MvPolynomial.esymm
  rw [map_sum]
  refine Finset.sum_bij (fun t _ => t.map σ.toEmbedding) ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by rw [Finset.card_map, (Finset.mem_powersetCard.mp ht).2]⟩
  · intro t1 _ t2 _ h
    ext x; have := Finset.ext_iff.mp h (σ x); simpa using this
  · intro s hs
    refine ⟨s.map σ.symm.toEmbedding,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by rw [Finset.card_map, (Finset.mem_powersetCard.mp hs).2]⟩, ?_⟩
    ext x; simp
  · intro t _
    rw [map_prod, Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ => by simp

private lemma rename_terminalQuarticDisc23 (σ : Equiv.Perm (Fin 23)) :
    MvPolynomial.rename σ (terminalQuarticDisc 23) = terminalQuarticDisc 23 := by
  unfold terminalQuarticDisc quarticDisc
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.rename_C,
    rename_esymmPoly]

private lemma coeff_terminalQuarticDisc23_perm (σ : Equiv.Perm (Fin 23)) (α : Fin 23 →₀ ℕ) :
    (terminalQuarticDisc 23).coeff (α.mapDomain σ) = (terminalQuarticDisc 23).coeff α := by
  have h := congrArg (fun p => p.coeff (α.mapDomain σ)) (rename_terminalQuarticDisc23 σ)
  rw [MvPolynomial.coeff_rename_mapDomain _ σ.injective] at h
  exact h.symm

/-- Any two exponent vectors `α, β : Fin 23 →₀ ℕ` with the same multiset of nonzero entries
are conjugate under some permutation `σ : Equiv.Perm (Fin 23)`. -/
private lemma exists_perm_of_nzMs_eq {α β : Fin 23 →₀ ℕ} (h : nzMs α = nzMs β) :
    ∃ σ : Equiv.Perm (Fin 23), α.mapDomain σ = β := by
  -- Biject `α.support` with `β.support` preserving values (both have the same multiset of values),
  -- then extend to a permutation of `Fin 23`!
  have hcard : α.support.card = β.support.card := by
    have := congrArg Multiset.card h
    simpa [nzMs] using this
  -- Build an explicit value-preserving bijection `e_supp : ↥α.support ≃ ↥β.support` by induction on `k`
  have hbij : ∃ f : Fin 23 → Fin 23, Function.Bijective f ∧ ∀ x ∈ α.support, f x ∈ β.support ∧ β (f x) = α x := by
    -- Match elements of `α.support.toList` and `β.support.toList` via `List.Perm`
    have hperm_val : (α.support.toList.map α).Perm (β.support.toList.map β) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe,
        Finset.coe_toList, Finset.coe_toList]
      exact h
    -- General lemma: if `(l1.map f1).Perm (l2.map f2)`, then `l1` permutes to some `l1'` with `l1'.map f1 = l2.map f2`!
    have hex_perm : ∀ (l1 l2 : List (Fin 23)), (l1.map α).Perm (l2.map β) →
        ∃ l2' : List (Fin 23), l2'.Perm l2 ∧ l1.map α = l2'.map β := by
      intro l1
      induction l1 with
      | nil =>
          intro l2 hp
          have hl2 : l2 = [] := List.map_eq_nil_iff.mp hp.nil_eq.symm
          exact ⟨[], hl2 ▸ List.Perm.refl _, by simp⟩
      | cons a as ih =>
          intro l2 hp
          have hmem : α a ∈ l2.map β := hp.subset (List.mem_cons_self ..)
          obtain ⟨b, hb_mem, hba⟩ := List.mem_map.mp hmem
          have hperm_b : (b :: l2.erase b).Perm l2 := (List.perm_cons_erase hb_mem).symm
          let l2_rest := l2.erase b
          have hp_rest : (as.map α).Perm (l2_rest.map β) := by
            have h1 : (α a :: as.map α).Perm (β b :: l2_rest.map β) :=
              hp.trans (hperm_b.symm.map β)
            rw [hba] at h1
            exact h1.cons_inv
          obtain ⟨l2', hl2'p, hl2'm⟩ := ih l2_rest hp_rest
          exact ⟨b :: l2', (List.Perm.cons b hl2'p).trans hperm_b, by simp [hba, hl2'm]⟩
    obtain ⟨l2', hl2'p, hl2'm⟩ := hex_perm α.support.toList β.support.toList hperm_val
    have hnd1 : α.support.toList.Nodup := Finset.nodup_toList _
    have hnd2 : l2'.Nodup := hl2'p.nodup_iff.mpr (Finset.nodup_toList _)
    have hlen : α.support.toList.length = l2'.length := by
      have := congrArg List.length hl2'm; simpa using this
    -- Extend `α.support.toList ↔ l2'` to a bijection of `Fin 23` using complements!
    let c1 : List (Fin 23) := (Finset.univ \ α.support).toList
    let c2 : List (Fin 23) := (Finset.univ \ β.support).toList
    have hc_len : c1.length = c2.length := by
      simp only [c1, c2, Finset.length_toList, Finset.card_sdiff, Finset.inter_univ, hcard]
    let full1 : List (Fin 23) := α.support.toList ++ c1
    let full2 : List (Fin 23) := l2' ++ c2
    have hnd_f1 : full1.Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd1, Finset.nodup_toList _, fun x hx y hy hxy => ?_⟩
      subst hxy
      exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2 (Finset.mem_toList.mp hx)
    have hnd_f2 : full2.Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd2, Finset.nodup_toList _, fun x hx y hy hxy => ?_⟩
      subst hxy
      exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2 (Finset.mem_toList.mp (hl2'p.subset hx))
    have hlen_f1 : full1.length = 23 := by
      simp only [full1, c1, List.length_append, Finset.length_toList, Finset.card_sdiff,
        Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have : α.support.card ≤ 23 := by simpa using Finset.card_le_univ α.support
      omega
    have hlen_f2 : full2.length = 23 := by
      simp only [full2, c2, List.length_append, hl2'p.length_eq, Finset.length_toList,
        Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have : β.support.card ≤ 23 := by simpa using Finset.card_le_univ β.support
      omega
    have hmem_f1 : ∀ x : Fin 23, x ∈ full1 := fun x => by
      simp only [full1, c1, List.mem_append, Finset.mem_toList, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      exact em (x ∈ α.support)
    let f : Fin 23 → Fin 23 := fun x =>
      let idx := full1.idxOf x
      full2[idx]'(by have := List.idxOf_lt_length_of_mem (hmem_f1 x); omega)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have hx := List.idxOf_lt_length_of_mem (hmem_f1 x)
      have hy := List.idxOf_lt_length_of_mem (hmem_f1 y)
      have hidx_fin : (⟨full1.idxOf x, by omega⟩ : Fin full2.length) = ⟨full1.idxOf y, by omega⟩ :=
        (List.nodup_iff_injective_getElem.mp hnd_f2) hxy
      have hidx : full1.idxOf x = full1.idxOf y := congrArg (fun z : Fin full2.length => z.val) hidx_fin
      have h1 := List.getElem_idxOf hx
      have h2 := List.getElem_idxOf hy
      rw [← h1, ← h2]; simp [hidx]
    refine ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, rfl⟩, ?_⟩
    intro x hx
    have hx_l1 : x ∈ α.support.toList := Finset.mem_toList.mpr hx
    have hidx_lt : α.support.toList.idxOf x < α.support.toList.length :=
      List.idxOf_lt_length_of_mem hx_l1
    have hidx_eq : full1.idxOf x = α.support.toList.idxOf x := by
      simp only [full1, List.idxOf_append_of_mem hx_l1]
    have hfx : f x = l2'[α.support.toList.idxOf x]'(by omega) := by
      simp only [f, hidx_eq, full2, List.getElem_append_left (by omega : α.support.toList.idxOf x < l2'.length)]
    rw [hfx]
    refine ⟨Finset.mem_toList.mp (hl2'p.subset (List.getElem_mem _)), ?_⟩
    have hval := congrArg (fun l : List ℕ => l[α.support.toList.idxOf x]?) hl2'm
    rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem hidx_lt, List.getElem?_eq_getElem (by omega),
      Option.map_some, Option.map_some, List.getElem_idxOf hidx_lt] at hval
    exact (Option.some.inj hval).symm
  obtain ⟨f, hbij_f, hpres⟩ := hbij
  let σ : Equiv.Perm (Fin 23) := Equiv.ofBijective f hbij_f
  refine ⟨σ, ?_⟩
  ext y
  rw [← σ.apply_symm_apply y, Finsupp.mapDomain_apply σ.injective]
  set x := σ.symm y
  by_cases hx : x ∈ α.support
  · exact (hpres x hx).2.symm
  · have hα0 : α x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hα0]
    symm
    by_contra hβne
    have hmem_β : σ x ∈ β.support := Finsupp.mem_support_iff.mpr hβne
    -- Since `f` maps `α.support` injectively into `β.support` of the same card, `σ x ∈ f '' α.support`!
    have him : α.support.image σ = β.support := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz; exact (hpres a ha).1
      · rw [Finset.card_image_of_injective _ σ.injective, hcard]
    rw [← him] at hmem_β
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hmem_β
    exact hx (σ.injective hax ▸ ha)

private lemma coeff_of_nzMs_eq_mon4 {α : Fin 23 →₀ ℕ} {k0 k1 k2 k3 : ℕ}
    (h : nzMs α = nzMs ((mon4 k0 k1 k2 k3).mapDomain fin4To23)) :
    (terminalQuarticDisc 23).coeff α = (discCoeff4 k0 k1 k2 k3 : ℝ) := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_nzMs_eq h.symm
  rw [coeff_terminalQuarticDisc23_perm, terminalQuarticDisc23_coeff_mon4]

private lemma nzMs_mon4_map (k0 k1 k2 k3 : ℕ) :
    nzMs ((mon4 k0 k1 k2 k3).mapDomain fin4To23) =
      (([k0, k1, k2, k3].filter (· ≠ 0) : List ℕ) : Multiset ℕ) := by
  unfold nzMs
  have hsupp : ((mon4 k0 k1 k2 k3).mapDomain fin4To23).support =
      ((Finset.univ : Finset (Fin 4)).filter (fun i => mon4 k0 k1 k2 k3 i ≠ 0)).map
        ⟨fin4To23, fin4To23_inj⟩ := by
    ext x
    simp only [Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      by_cases hi : x.val < 4
      · refine ⟨⟨x.val, hi⟩, ?_, Fin.ext rfl⟩
        have h1 : x = fin4To23 ⟨x.val, hi⟩ := Fin.ext rfl
        rw [h1, Finsupp.mapDomain_apply fin4To23_inj] at hx
        exact hx
      · exfalso
        exact hx (Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨a, ha⟩; exact hi (ha ▸ a.isLt)))
    · rintro ⟨a, ha, rfl⟩
      rwa [Finsupp.mapDomain_apply fin4To23_inj]
  rw [hsupp, Finset.map_val, Multiset.map_map]
  have hcongr : Multiset.map
      (((mon4 k0 k1 k2 k3).mapDomain fin4To23) ∘ (⟨fin4To23, fin4To23_inj⟩ : Fin 4 ↪ Fin 23))
      ((Finset.univ : Finset (Fin 4)).filter (fun i => mon4 k0 k1 k2 k3 i ≠ 0)).val =
      Multiset.map (mon4 k0 k1 k2 k3)
      ((Finset.univ : Finset (Fin 4)).filter (fun i => mon4 k0 k1 k2 k3 i ≠ 0)).val := by
    refine Multiset.map_congr rfl fun a _ => ?_
    exact Finsupp.mapDomain_apply fin4To23_inj _ a
  rw [hcongr]
  have hfin : ((Finset.univ : Finset (Fin 4)).filter (fun i => mon4 k0 k1 k2 k3 i ≠ 0)).val =
      (((List.finRange 4).filter (fun i => mon4 k0 k1 k2 k3 i ≠ 0) : List (Fin 4)) : Multiset (Fin 4)) := by
    rfl
  rw [hfin, Multiset.map_coe]
  congr 1
  simp only [List.finRange, List.ofFn, Fin.foldr_succ, Fin.foldr_zero, List.filter_cons,
    List.filter_nil, mon4_apply]
  by_cases h0 : k0 = 0 <;> by_cases h1 : k1 = 0 <;> by_cases h2 : k2 = 0 <;> by_cases h3 : k3 = 0 <;>
    simp [h0, h1, h2, h3, mon4_apply]

/-- Exact negative value of `L` on `terminalQuarticDisc 23`! -/
private lemma L_disc_neg : L (terminalQuarticDisc 23) < 0 := by
  set f := terminalQuarticDisc 23
  -- Build the 3 explicit finite sets of exponent vectors with `nzMs = {5,4,3}`, `{4,4,4}`, `{3,3,3,3}`
  let S543 : Finset (Fin 23 →₀ ℕ) :=
    ((Finset.univ : Finset (Fin 23 × Fin 23 × Fin 23)).filter
      (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)).image
      (fun p => Finsupp.single p.1 5 + Finsupp.single p.2.1 4 + Finsupp.single p.2.2 3)
  let S444 : Finset (Fin 23 →₀ ℕ) :=
    ((Finset.univ : Finset (Fin 23)).powersetCard 3).image
      (fun t => ∑ i ∈ t, Finsupp.single i 4)
  let S3333 : Finset (Fin 23 →₀ ℕ) :=
    ((Finset.univ : Finset (Fin 23)).powersetCard 4).image
      (fun t => ∑ i ∈ t, Finsupp.single i 3)
  -- Helper: characterize membership in `S543`, `S444`, `S3333` by `nzMs`!
  have hmem_543 : ∀ α : Fin 23 →₀ ℕ, α ∈ S543 ↔ nzMs α = {5, 4, 3} := by
    intro α
    constructor
    · intro h
      obtain ⟨⟨a, b, c⟩, hp, rfl⟩ := Finset.mem_image.mp h
      rcases (Finset.mem_filter.mp hp).2 with ⟨hab, hac, hbc⟩
      unfold nzMs
      have hsupp : (Finsupp.single a 5 + Finsupp.single b 4 + Finsupp.single c 3).support = {a, b, c} := by
        ext x; simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
          Finset.mem_insert, Finset.mem_singleton]
        by_cases hxa : a = x <;> by_cases hxb : b = x <;> by_cases hxc : c = x <;>
          simp [hxa, hxb, hxc, eq_comm]
      rw [hsupp, Finset.insert_val_of_notMem (by simp [hab, hac]),
          Finset.insert_val_of_notMem (by simp [hbc]), Finset.singleton_val,
          Multiset.map_cons, Multiset.map_cons, Multiset.map_singleton]
      simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    · intro hnz
      have h5 : 5 ∈ nzMs α := by rw [hnz]; simp
      have h4 : 4 ∈ nzMs α := by rw [hnz]; simp
      have h3 : 3 ∈ nzMs α := by rw [hnz]; simp
      obtain ⟨a, ha_s, ha⟩ := Multiset.mem_map.mp h5
      obtain ⟨b, hb_s, hb⟩ := Multiset.mem_map.mp h4
      obtain ⟨c, hc_s, hc⟩ := Multiset.mem_map.mp h3
      have hab : a ≠ b := fun h => by rw [h] at ha; omega
      have hac : a ≠ c := fun h => by rw [h] at ha; omega
      have hbc : b ≠ c := fun h => by rw [h] at hb; omega
      have hcard : α.support.card = 3 := by
        have := congrArg Multiset.card hnz; simpa [nzMs] using this
      have hsupp : α.support = {a, b, c} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ha_s
          · rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hb_s
            · rw [Finset.mem_singleton.mp hx]; exact hc_s
        · rw [hcard, Finset.card_insert_of_notMem (by simp [hab, hac]),
            Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      refine Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hac, hbc⟩, ?_⟩
      ext x
      by_cases hxa : x = a
      · subst hxa; simp [ha, hab, hac]
      · by_cases hxb : x = b
        · subst hxb; simp [hb, hbc, Ne.symm hab]
        · by_cases hxc : x = c
          · subst hxc; simp [hc, Ne.symm hac, Ne.symm hbc]
          · have hxnot : x ∉ α.support := by rw [hsupp]; simp [hxa, hxb, hxc]
            simp [Finsupp.notMem_support_iff.mp hxnot, hxa, hxb, hxc]
  have hmem_444 : ∀ α : Fin 23 →₀ ℕ, α ∈ S444 ↔ nzMs α = {4, 4, 4} := by
    intro α
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      rcases Finset.mem_powersetCard.mp ht with ⟨_, htc⟩
      unfold nzMs
      have hval : ∀ x : Fin 23, (∑ i ∈ t, Finsupp.single i 4) x = if x ∈ t then 4 else 0 := by
        intro x; simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
      have hsupp : (∑ i ∈ t, Finsupp.single i 4).support = t := by
        ext x; simp [Finsupp.mem_support_iff, hval]
      rw [hsupp]
      have hmap : t.val.map (fun x => (∑ i ∈ t, Finsupp.single i 4) x) = Multiset.replicate t.card 4 := by
        have : t.val.map (fun x => (∑ i ∈ t, Finsupp.single i 4) x) = t.val.map (fun _ => 4) :=
          Multiset.map_congr rfl fun x hx => by rw [hval x, if_pos (Finset.mem_def.mpr hx)]
        rw [this, Multiset.map_const', Finset.card_def]
      rw [hmap, htc]; rfl
    · intro hnz
      have hcard : α.support.card = 3 := by
        have := congrArg Multiset.card hnz; simpa [nzMs] using this
      have hall4 : ∀ x ∈ α.support, α x = 4 := by
        intro x hx
        have : α x ∈ nzMs α := Multiset.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hnz] at this; simp at this; exact this
      refine Finset.mem_image.mpr ⟨α.support, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
      ext x
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
      by_cases hx : x ∈ α.support
      · rw [if_pos hx, hall4 x hx]
      · rw [if_neg hx, Finsupp.notMem_support_iff.mp hx]
  have hmem_3333 : ∀ α : Fin 23 →₀ ℕ, α ∈ S3333 ↔ nzMs α = {3, 3, 3, 3} := by
    intro α
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      rcases Finset.mem_powersetCard.mp ht with ⟨_, htc⟩
      unfold nzMs
      have hval : ∀ x : Fin 23, (∑ i ∈ t, Finsupp.single i 3) x = if x ∈ t then 3 else 0 := by
        intro x; simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
      have hsupp : (∑ i ∈ t, Finsupp.single i 3).support = t := by
        ext x; simp [Finsupp.mem_support_iff, hval]
      rw [hsupp]
      have hmap : t.val.map (fun x => (∑ i ∈ t, Finsupp.single i 3) x) = Multiset.replicate t.card 3 := by
        have : t.val.map (fun x => (∑ i ∈ t, Finsupp.single i 3) x) = t.val.map (fun _ => 3) :=
          Multiset.map_congr rfl fun x hx => by rw [hval x, if_pos (Finset.mem_def.mpr hx)]
        rw [this, Multiset.map_const', Finset.card_def]
      rw [hmap, htc]; rfl
    · intro hnz
      have hcard : α.support.card = 4 := by
        have := congrArg Multiset.card hnz; simpa [nzMs] using this
      have hall3 : ∀ x ∈ α.support, α x = 3 := by
        intro x hx
        have : α x ∈ nzMs α := Multiset.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hnz] at this; simp at this; exact this
      refine Finset.mem_image.mpr ⟨α.support, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
      ext x
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
      by_cases hx : x ∈ α.support
      · rw [if_pos hx, hall3 x hx]
      · rw [if_neg hx, Finsupp.notMem_support_iff.mp hx]
  -- Exact cardinalities of `S543`, `S444`, `S3333`!
  have hcard_543 : S543.card = 10626 := by
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_filter]
      have hsum : (∑ p : Fin 23 × Fin 23 × Fin 23, if p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 then 1 else 0) =
          ∑ a : Fin 23, ∑ b : Fin 23, ∑ c : Fin 23, if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0 := by
        rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
      rw [hsum]
      have hinner : ∀ a b : Fin 23,
          (∑ c : Fin 23, if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℕ) else 0) = if a ≠ b then 21 else 0 := by
        intro a b
        by_cases hab : a = b
        · simp [hab]
        · rw [if_pos hab]
          have h1 : (∑ c : Fin 23, if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℕ) else 0) =
              (((Finset.univ : Finset (Fin 23)).erase a).erase b).card := by
            rw [← Finset.card_filter]
            refine congrArg Finset.card (Finset.ext fun c => ?_)
            simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
            constructor
            · rintro ⟨_, hac, hbc⟩; exact ⟨fun h => hbc h.symm, fun h => hac h.symm⟩
            · rintro ⟨hcb, hca⟩; exact ⟨hab, fun h => hca h.symm, fun h => hcb h.symm⟩
          rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩),
            Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      have hstep1 : (∑ a : Fin 23, ∑ b : Fin 23, ∑ c : Fin 23, if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℕ) else 0) =
          ∑ a : Fin 23, ∑ b : Fin 23, if a ≠ b then (21 : ℕ) else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hinner a b
      rw [hstep1]
      have hmid : ∀ a : Fin 23, (∑ b : Fin 23, if a ≠ b then (21 : ℕ) else 0) = 22 * 21 := by
        intro a
        have : (∑ b : Fin 23, if a ≠ b then (21 : ℕ) else 0) =
            ∑ b ∈ (Finset.univ : Finset (Fin 23)).erase a, (21 : ℕ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr (Finset.ext fun b => ?_) (fun _ _ => rfl)
          simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
          exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
        rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [Finset.sum_congr rfl fun a _ => hmid a, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    · intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨a1, b1, c1⟩; rcases p2 with ⟨a2, b2, c2⟩
      rcases (Finset.mem_filter.mp hp1).2 with ⟨hab1, hac1, hbc1⟩
      rcases (Finset.mem_filter.mp hp2).2 with ⟨hab2, hac2, hbc2⟩
      have ha : a1 = a2 := by
        have h := congrArg (fun g : Fin 23 →₀ ℕ => g a1) heq
        simp [hab1, hac1] at h
        by_contra hne
        by_cases h1 : b2 = a1 <;> by_cases h2 : c2 = a1
        · exact hbc2 (h1.trans h2.symm)
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
      have hb : b1 = b2 := by
        have h := congrArg (fun g : Fin 23 →₀ ℕ => g b1) heq
        simp [hbc1, Ne.symm hab1] at h
        by_contra hne
        by_cases h1 : a2 = b1 <;> by_cases h2 : c2 = b1
        · exact hac2 (h1.trans h2.symm)
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
      have hc : c1 = c2 := by
        have h := congrArg (fun g : Fin 23 →₀ ℕ => g c1) heq
        simp [Ne.symm hac1, Ne.symm hbc1] at h
        by_contra hne
        by_cases h1 : a2 = c1 <;> by_cases h2 : b2 = c1
        · exact hab2 (h1.trans h2.symm)
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
        · simp [Ne.symm hne, h1, h2] at h
      subst ha; subst hb; subst hc; rfl
  have hcard_444 : S444.card = 1771 := by
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; decide
    · intro t1 _ t2 _ heq
      ext x
      have h := congrArg (fun g : Fin 23 →₀ ℕ => g x) heq
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at h
      by_cases h1 : x ∈ t1 <;> by_cases h2 : x ∈ t2 <;> simp_all
  have hcard_3333 : S3333.card = 8855 := by
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; decide
    · intro t1 _ t2 _ heq
      ext x
      have h := congrArg (fun g : Fin 23 →₀ ℕ => g x) heq
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at h
      by_cases h1 : x ∈ t1 <;> by_cases h2 : x ∈ t2 <;> simp_all
  -- Every term outside `S543 ∪ S444 ∪ S3333` has `(weightOfMs (nzMs α) : ℝ) * f.coeff α = 0`!
  have hzero_out : ∀ α : Fin 23 →₀ ℕ, α ∉ S543 ∪ S444 ∪ S3333 →
      (weightOfMs (nzMs α) : ℝ) * f.coeff α = 0 := by
    intro α hnot
    simp only [Finset.mem_union, not_or, hmem_543, hmem_444, hmem_3333] at hnot
    rcases hnot with ⟨⟨hn543, hn444⟩, hn3333⟩
    unfold weightOfMs
    have hcoeff0 : ∀ k0 k1 k2 k3 : ℕ, discCoeff4 k0 k1 k2 k3 = 0 →
        nzMs α = nzMs ((mon4 k0 k1 k2 k3).mapDomain fin4To23) → f.coeff α = 0 := by
      intro k0 k1 k2 k3 h0 hnz
      rw [coeff_of_nzMs_eq_mon4 hnz, h0]; norm_num
    by_cases h1 : nzMs α = {12}
    · rw [hcoeff0 12 0 0 0 discCoeff4_zero_shapes.1 (by rw [h1, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h1]
    by_cases h2 : nzMs α = {10, 2}
    · rw [hcoeff0 10 2 0 0 discCoeff4_zero_shapes.2.1 (by rw [h2, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h2]
    by_cases h3 : nzMs α = {9, 3}
    · rw [hcoeff0 9 3 0 0 discCoeff4_zero_shapes.2.2.1 (by rw [h3, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h3]
    by_cases h4 : nzMs α = {8, 4}
    · rw [hcoeff0 8 4 0 0 discCoeff4_zero_shapes.2.2.2.1 (by rw [h4, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h4]
    by_cases h5 : nzMs α = {7, 5}
    · rw [hcoeff0 7 5 0 0 discCoeff4_zero_shapes.2.2.2.2.1 (by rw [h5, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h5]
    by_cases h6 : nzMs α = {7, 3, 2}
    · rw [hcoeff0 7 3 2 0 discCoeff4_zero_shapes.2.2.2.2.2.1 (by rw [h6, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h6]
    by_cases h7 : nzMs α = {6, 6}
    · rw [hcoeff0 6 6 0 0 discCoeff4_zero_shapes.2.2.2.2.2.2 (by rw [h7, nzMs_mon4_map]; rfl), mul_zero]
    rw [if_neg h7, if_neg hn543, if_neg hn444, if_neg hn3333]
    simp
  -- Restrict `L f` to `S543 ∪ S444 ∪ S3333`
  have hL_eq : L f = ∑ α ∈ S543 ∪ S444 ∪ S3333, (weightOfMs (nzMs α) : ℝ) * f.coeff α := by
    have h1 : (∑ α ∈ f.support, (weightOfMs (nzMs α) : ℝ) * f.coeff α) =
        ∑ α ∈ f.support ∪ (S543 ∪ S444 ∪ S3333), (weightOfMs (nzMs α) : ℝ) * f.coeff α :=
      Finset.sum_subset Finset.subset_union_left fun α _ hnot => by
        rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]
    have h2 : (∑ α ∈ S543 ∪ S444 ∪ S3333, (weightOfMs (nzMs α) : ℝ) * f.coeff α) =
        ∑ α ∈ f.support ∪ (S543 ∪ S444 ∪ S3333), (weightOfMs (nzMs α) : ℝ) * f.coeff α :=
      Finset.sum_subset Finset.subset_union_right fun α _ hnot => hzero_out α hnot
    exact h1.trans h2.symm
  have hd12 : Disjoint S543 S444 := by
    rw [Finset.disjoint_left]; intro α h1 h2
    rw [hmem_543] at h1; rw [hmem_444] at h2
    have h := h1.symm.trans h2
    exact absurd (show 5 ∈ ({4, 4, 4} : Multiset ℕ) by rw [← h]; simp) (by decide)
  have hd123 : Disjoint (S543 ∪ S444) S3333 := by
    rw [Finset.disjoint_left]; intro α h1 h2
    rw [hmem_3333] at h2
    rcases Finset.mem_union.mp h1 with h1a | h1b
    · rw [hmem_543] at h1a
      have := congrArg Multiset.card (h1a.symm.trans h2); simp at this
    · rw [hmem_444] at h1b
      have := congrArg Multiset.card (h1b.symm.trans h2); simp at this
  rw [hL_eq, Finset.sum_union hd123, Finset.sum_union hd12]
  have hsum543 : (∑ α ∈ S543, (weightOfMs (nzMs α) : ℝ) * f.coeff α) =
      (10626 : ℝ) * (4 * 2807112000000) := by
    have heach : ∀ α ∈ S543, (weightOfMs (nzMs α) : ℝ) * f.coeff α = 4 * 2807112000000 := by
      intro α hα
      have hnz := (hmem_543 α).mp hα
      have hw : weightOfMs (nzMs α) = 4 := by rw [hnz]; decide
      have hc : f.coeff α = 2807112000000 := by
        rw [coeff_of_nzMs_eq_mon4 (k0 := 5) (k1 := 4) (k2 := 3) (k3 := 0)
          (by rw [hnz, nzMs_mon4_map]; rfl), discCoeff4_nonzero_shapes.1]
        norm_num
      rw [hw, hc]; norm_num
    rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard_543, nsmul_eq_mul]; norm_num
  have hsum444 : (∑ α ∈ S444, (weightOfMs (nzMs α) : ℝ) * f.coeff α) =
      (1771 : ℝ) * (8 * 37417380000000) := by
    have heach : ∀ α ∈ S444, (weightOfMs (nzMs α) : ℝ) * f.coeff α = 8 * 37417380000000 := by
      intro α hα
      have hnz := (hmem_444 α).mp hα
      have hw : weightOfMs (nzMs α) = 8 := by rw [hnz]; decide
      have hc : f.coeff α = 37417380000000 := by
        rw [coeff_of_nzMs_eq_mon4 (k0 := 4) (k1 := 4) (k2 := 4) (k3 := 0)
          (by rw [hnz, nzMs_mon4_map]; rfl), discCoeff4_nonzero_shapes.2.1]
        norm_num
      rw [hw, hc]; norm_num
    rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard_444, nsmul_eq_mul]; norm_num
  have hsum3333 : (∑ α ∈ S3333, (weightOfMs (nzMs α) : ℝ) * f.coeff α) =
      (8855 : ℝ) * (1 * (-74374083168000)) := by
    have heach : ∀ α ∈ S3333, (weightOfMs (nzMs α) : ℝ) * f.coeff α = 1 * (-74374083168000) := by
      intro α hα
      have hnz := (hmem_3333 α).mp hα
      have hw : weightOfMs (nzMs α) = 1 := by rw [hnz]; decide
      have hc : f.coeff α = -74374083168000 := by
        rw [coeff_of_nzMs_eq_mon4 (k0 := 3) (k1 := 3) (k2 := 3) (k3 := 3)
          (by rw [hnz, nzMs_mon4_map]; rfl), discCoeff4_nonzero_shapes.2.2]
        norm_num
      rw [hw, hc]; norm_num
    rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard_3333, nsmul_eq_mul]; norm_num
  rw [hsum543, hsum444, hsum3333]
  norm_num

/-- `terminalQuarticDisc 23` does NOT belong to the square-graph cone! -/
theorem not_in_squareGraphCone_23 : ¬ InSquareGraphCone 23 (terminalQuarticDisc 23) := by
  rintro ⟨m, c, E, hc, heq⟩
  have hnonneg : 0 ≤ L (terminalQuarticDisc 23) := by
    rw [heq, L_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [L_C_mul, L_symSquareGraphPoly]
    have h1 : 0 ≤ c i := hc i
    have h2 : (0 : ℝ) ≤ (Nat.factorial 23 : ℝ) := by positivity
    have h3 : 0 ≤ L (((E i).map (fun e => (MvPolynomial.X e.1 - MvPolynomial.X e.2) ^ 2)).prod) :=
      L_prod_nonneg (E i)
    positivity
  linarith [L_disc_neg]

end OMA.P_arxiv_2605_25743

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2605_25743.main) := by
  intro h
  exact OMA.P_arxiv_2605_25743.not_in_squareGraphCone_23 (h 23 (by norm_num))


