import FormalConjectures.Wikipedia.Kakeya

-- Problem: Kakeya problem — kakeya finite
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Kakeya.lean:107 (declaration Kakeya.kakeya_finite)
-- Credit: @iLc0 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Kakeya fini, borne de Bukh–Chao (arXiv 2108.00074).
Aucune `def` auxiliaire : les objets sont écrits en clair.
* développement de Taylor en `p` : `aeval (fun k => C (p k) + X k) P` ;
* dérivée de Hasse d'ordre `i` : `coeff i (aeval (fun k => C (X k) + X k) P)`, prise dans
  `MvPolynomial (Fin n) (MvPolynomial (Fin n) F)` ;
* restriction à la droite `a + t b` : `aeval (fun k => Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X)` ;
* déshomogénéisation `X c ↦ 1` : `aeval (fun k => if k = c then 1 else X k)`. -/

open MvPolynomial

noncomputable section

namespace OMA.BukhChao

variable {F : Type*} [Field F] [Fintype F]

/- ### Dérivées de Hasse -/

private theorem coeff_shift_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (s : Fin n →₀ ℕ) (k : Fin n) (h : s k = 0) (Q : MvPolynomial (Fin n) R) :
    coeff (s + Finsupp.single k 0) (Q * X k) = 0 := by
  classical
  simp [coeff_mul_X', Finsupp.mem_support_iff, h]

private theorem coeff_shift_succ {n : ℕ} {R : Type*} [CommSemiring R]
    (s : Fin n →₀ ℕ) (k : Fin n) (a : ℕ) (Q : MvPolynomial (Fin n) R) :
    coeff (s + Finsupp.single k (a + 1)) (Q * X k) = coeff (s + Finsupp.single k a) Q := by
  rw [Finsupp.single_add, ← add_assoc, coeff_mul_X]

/-- 1. Formule monomiale de la dérivée de Hasse. -/
theorem coeff_hasse {n : ℕ} (i γ : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) F) :
    coeff γ (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)) =
      ((∏ k, ((γ + i) k).choose (i k) : ℕ) : F) * coeff (γ + i) P := by
  classical
  induction P using MvPolynomial.induction_on generalizing i γ with
  | C r =>
    rw [aeval_C]
    change coeff γ (coeff i (C (C r) : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) = _
    by_cases hi : i = 0 <;> by_cases hg : γ = 0 <;>
      simp [hi, hg, coeff_C, eq_comm]
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]
  | mul_X P k ih =>
    let Q := aeval (fun l => (C (X l) + X l : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P
    rw [map_mul, aeval_X, mul_add, coeff_add, coeff_add]
    change coeff γ (coeff i (Q * C (X k))) + coeff γ (coeff i (Q * X k)) = _
    rw [mul_comm Q (C (X k)), coeff_C_mul, mul_comm (X k) (coeff i Q)]
    obtain ⟨g, a, hg, rfl⟩ : ∃ (g : Fin n →₀ ℕ) (a : ℕ),
        g k = 0 ∧ γ = g + Finsupp.single k a :=
      ⟨γ.erase k, γ k, Finsupp.erase_same, (Finsupp.erase_add_single k γ).symm⟩
    obtain ⟨j, b, hj, rfl⟩ : ∃ (j : Fin n →₀ ℕ) (b : ℕ),
        j k = 0 ∧ i = j + Finsupp.single k b :=
      ⟨i.erase k, i k, Finsupp.erase_same, (Finsupp.erase_add_single k i).symm⟩
    let w := ∏ l ∈ Finset.univ.erase k, (g l + j l).choose (j l)
    have hprod (u v : ℕ) :
        (∏ l, ((g + Finsupp.single k u + (j + Finsupp.single k v)) l).choose
          ((j + Finsupp.single k v) l)) = (u + v).choose v * w := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      congr 1
      · simp [hg, hj]
      · apply Finset.prod_congr rfl
        intro l hl
        have hkl := (Finset.mem_erase.mp hl).1
        simp [Finsupp.single_eq_of_ne hkl]
    have hadd (u v : ℕ) : g + Finsupp.single k u + (j + Finsupp.single k v) =
        g + j + Finsupp.single k (u + v) := by rw [Finsupp.single_add]; ac_rfl
    have hih (u v : ℕ) : coeff (g + Finsupp.single k u) (coeff (j + Finsupp.single k v) Q) =
        (((u + v).choose v * w : ℕ) : F) * coeff (g + j + Finsupp.single k (u + v)) P := by
      dsimp only [Q]
      rw [ih, hprod, hadd]
    rw [hprod, hadd]
    have hgj : (g + j) k = 0 := by simp [hg, hj]
    cases a <;> cases b <;>
      simp only [Nat.succ_add, Nat.add_succ,
        coeff_shift_zero g k hg, coeff_shift_zero j k hj, coeff_shift_zero (g + j) k hgj,
        coeff_shift_succ, coeff_zero, hih, Nat.choose_zero_right, Nat.choose_self,
        zero_add, add_zero, mul_zero, one_mul]
    rename_i u v
    conv_rhs => rw [Nat.choose_succ_succ (u + v).succ v, Nat.add_mul, Nat.cast_add, add_mul]
    exact add_comm _ _

/-- 2. La dérivée de Hasse commute au développement de Taylor. -/
theorem taylor_hasse {n : ℕ} (p : Fin n → F) (i : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) F) :
    aeval (fun k => C (p k) + X k) (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)) =
      coeff i (aeval (fun k => (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F)))
        (aeval (fun k => C (p k) + X k) P)) := by
  have key : MvPolynomial.map ((aeval (fun k => C (p k) + X k) :
      MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F) : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F)
      (aeval (fun k => (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P) =
      aeval (fun k => (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F)))
        (aeval (fun k => C (p k) + X k) P) := by
    induction P using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f k hf =>
      simp only [map_mul, hf, aeval_X, map_add, map_X, MvPolynomial.map_C, RingHom.coe_coe, aeval_C,
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, C_add]
      ring
  rw [← key, coeff_map]
  rfl

/-- 3. Valeur d'une dérivée de Hasse = coefficient de Taylor. -/
theorem eval_hasse {n : ℕ} (p : Fin n → F) (i : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) F) :
    eval p (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)) =
      coeff i (aeval (fun k => C (p k) + X k) P) := by
  have key : MvPolynomial.map (eval p)
      (aeval (fun k => (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P) =
      aeval (fun k => C (p k) + X k) P := by
    induction P using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f k hf =>
      simp only [map_mul, hf, aeval_X, map_add, map_X, MvPolynomial.map_C, eval_X]
  rw [← key, coeff_map]

/-- 4. Une dérivée d'ordre `i` fait baisser le degré de `|i|`. -/
theorem totalDegree_hasse {n : ℕ} (i : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) F)
    (h : coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P) ≠ 0) :
    (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)).totalDegree +
      Finsupp.degree i ≤ P.totalDegree := by
  classical
  let D := coeff i (aeval (fun k =>
    (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)
  change D.totalDegree + Finsupp.degree i ≤ P.totalDegree
  obtain ⟨γ, hγ, hmax⟩ := Finset.exists_mem_eq_sup D.support
    (support_nonempty.mpr (show D ≠ 0 from h)) Finsupp.degree
  change D.totalDegree = Finsupp.degree γ at hmax
  have hc := mem_support_iff.mp hγ
  dsimp only [D] at hc
  rw [coeff_hasse] at hc
  have hp : γ + i ∈ P.support := mem_support_iff.mpr (right_ne_zero_of_mul hc)
  rw [hmax, ← map_add]
  exact le_totalDegree hp

/-- 5. Composantes homogènes d'une dérivée de Hasse. -/
theorem hc_hasse {n : ℕ} (e : ℕ) (i : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) F) :
    homogeneousComponent e (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)) =
      coeff i (aeval (fun k => (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F)))
        (homogeneousComponent (e + Finsupp.degree i) P)) := by
  classical
  ext γ
  simp only [coeff_homogeneousComponent, coeff_hasse, map_add, add_left_inj]
  split <;> simp_all

/- ### Restriction à une droite -/

/-- Produit de facteurs linéaires : degré et coefficient de tête. -/
theorem prod_linear_aux (a b : Fin n → F) (s : Finset (Fin n)) (m : Fin n → ℕ) :
    (∏ k ∈ s, (Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) ^ m k).natDegree ≤
      ∑ k ∈ s, m k ∧
    (∏ k ∈ s, (Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) ^ m k).coeff (∑ k ∈ s, m k) =
      ∏ k ∈ s, b k ^ m k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h1 : (Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X).natDegree ≤ 1 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le))
    have hp : ((Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) ^ m k).natDegree ≤ m k :=
      by simpa using Polynomial.natDegree_pow_le_of_le (m k) h1
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]
    refine ⟨(Polynomial.natDegree_mul_le).trans (Nat.add_le_add hp ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp ih.1, ih.2]
    congr 1
    have := Polynomial.coeff_pow_of_natDegree_le (m := m k) h1
    rw [mul_one] at this
    rw [this]
    simp

/-- 6. La restriction à une droite ne fait pas monter le degré. -/
theorem natDegree_lineRes_le {n : ℕ} (a b : Fin n → F) (G : MvPolynomial (Fin n) F) :
    (aeval (fun k => Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) G).natDegree ≤
      G.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun α hα => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (prod_linear_aux a b α.support α).1.trans (le_totalDegree hα)

/-- 7. Coefficient de tête de la restriction. -/
theorem coeff_lineRes_top {n : ℕ} (a b : Fin n → F) (G : MvPolynomial (Fin n) F) (e : ℕ)
    (he : G.totalDegree ≤ e) :
    (aeval (fun k => Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) G).coeff e =
      eval b (homogeneousComponent e G) := by
  classical
  rw [aeval_def, eval₂_eq, homogeneousComponent_apply, map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg : (∑ k ∈ α.support, α k) ≤ e := (le_totalDegree hα).trans he
  obtain ⟨h1, h2⟩ := prod_linear_aux a b α.support α
  rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hdα : Finsupp.degree α = ∑ k ∈ α.support, α k := by
    rw [Finsupp.degree_eq_sum]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simpa using hk)).symm
  split_ifs with h
  · rw [hdα] at h
    rw [← h, h2]
    simp [eval_monomial, Finsupp.prod]
  · have hlt : (∑ k ∈ α.support, α k) < e := lt_of_le_of_ne hdeg (by rwa [hdα] at h)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (h1.trans_lt hlt), mul_zero]

/-- 8. Translater le paramètre de la droite. -/
theorem taylor_lineRes {n : ℕ} (a b : Fin n → F) (t : F) (G : MvPolynomial (Fin n) F) :
    Polynomial.taylor t (aeval (fun k => Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X) G) =
      aeval (fun k => Polynomial.C ((a + t • b) k) + Polynomial.C (b k) * Polynomial.X) G := by
  rw [Polynomial.taylor_apply, Polynomial.comp_eq_aeval]
  have := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := F)
    (fun k => Polynomial.C (a k) + Polynomial.C (b k) * Polynomial.X)
    (Polynomial.aeval (Polynomial.X + Polynomial.C t))) G
  simp only [AlgHom.comp_apply] at this
  rw [this]
  refine congrArg (fun f => aeval f G) ?_
  funext k
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Polynomial.algebraMap_eq, Polynomial.C_add, Polynomial.C_mul]
  ring

/-- 7'. Restriction à une droite issue de l'origine : coefficient d'ordre `j`. -/
theorem coeff_lineRes_zero {n : ℕ} (b : Fin n → F) (G : MvPolynomial (Fin n) F) (j : ℕ) :
    (aeval (fun k => Polynomial.C (b k) * Polynomial.X) G).coeff j =
      eval b (homogeneousComponent j G) := by
  classical
  rw [aeval_def, eval₂_eq, homogeneousComponent_apply, map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hprod : ∏ k ∈ α.support, (Polynomial.C (b k) * Polynomial.X) ^ α k =
      Polynomial.C (∏ k ∈ α.support, b k ^ α k) * Polynomial.X ^ (∑ k ∈ α.support, α k) := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
  have hdα : Finsupp.degree α = ∑ k ∈ α.support, α k := by
    rw [Finsupp.degree_eq_sum]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simpa using hk)).symm
  rw [hprod, Polynomial.coeff_C_mul_X_pow, hdα]
  by_cases h : ∑ k ∈ α.support, α k = j
  · rw [if_pos h.symm, if_pos h]
    simp [eval_monomial, Finsupp.prod]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-- 9. Un coefficient de la restriction d'une dérivée de Hasse ne voit que les coefficients de
Taylor de degré `|i| + j`. -/
theorem coeff_lineRes_hasse {n : ℕ} (p b : Fin n → F) (i : Fin n →₀ ℕ) (j : ℕ)
    (P : MvPolynomial (Fin n) F)
    (h : ∀ β : Fin n →₀ ℕ, Finsupp.degree β ≤ Finsupp.degree i + j →
      coeff β (aeval (fun k => C (p k) + X k) P) = 0) :
    (aeval (fun k => Polynomial.C (p k) + Polynomial.C (b k) * Polynomial.X)
      (coeff i (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P))).coeff j = 0 := by
  classical
  have hcomp : ∀ G : MvPolynomial (Fin n) F,
      aeval (fun k => Polynomial.C (p k) + Polynomial.C (b k) * Polynomial.X) G =
      aeval (fun k => Polynomial.C (b k) * Polynomial.X) (aeval (fun k => C (p k) + X k) G) := by
    intro G
    have := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := F) (fun k => C (p k) + X k)
      (aeval (fun k => Polynomial.C (b k) * Polynomial.X) :
        MvPolynomial (Fin n) F →ₐ[F] Polynomial F)) G
    simp only [AlgHom.comp_apply] at this
    rw [this]
    refine congrArg (fun f => aeval f G) ?_
    funext k
    simp [Polynomial.algebraMap_eq]
  rw [hcomp, taylor_hasse, coeff_lineRes_zero]
  have hz : homogeneousComponent j (coeff i (aeval (fun k =>
      (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F)))
        (aeval (fun k => C (p k) + X k) P))) = 0 := by
    ext γ
    rw [coeff_homogeneousComponent, coeff_zero]
    split_ifs with hγ
    · rw [coeff_hasse, h (γ + i) (by rw [map_add]; omega), mul_zero]
    · rfl
  rw [hz, map_zero]

/-- 10. Racines multiples en tous les points de `F`. -/
theorem natDegree_ge_of_taylor (R : Polynomial F) (hR : R ≠ 0) (c0 N : ℕ)
    (h : ∀ t : F, ∀ j : ℕ, Fintype.card F * j + c0 < N → (Polynomial.taylor t R).coeff j = 0) :
    N ≤ R.natDegree + c0 := by
  classical
  by_cases hN : N ≤ c0
  · omega
  push Not at hN
  set q := Fintype.card F with hq
  have hq0 : 0 < q := Fintype.card_pos
  set m := (N - c0 - 1) / q + 1 with hm
  have hjm : ∀ j < m, q * j + c0 < N := by
    intro j hj
    have : j ≤ (N - c0 - 1) / q := by omega
    have := Nat.mul_le_of_le_div q j (N - c0 - 1) this
    rw [mul_comm] at this
    omega
  have hqm : N - c0 ≤ q * m := by
    have := Nat.lt_div_mul_add (a := N - c0 - 1) hq0
    rw [hm, mul_add, mul_one, mul_comm]
    omega
  have hmult : ∀ t : F, m ≤ R.rootMultiplicity t := by
    intro t
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    refine Polynomial.le_natTrailingDegree ?_ (fun j hj => h t j (hjm j hj))
    intro h0
    exact hR ((Polynomial.taylor_injective t) (by rw [map_zero, Polynomial.taylor_apply, h0]))
  have hsum : ∑ t : F, R.rootMultiplicity t ≤ R.natDegree := by
    calc ∑ t : F, R.rootMultiplicity t = ∑ t : F, R.roots.count t := by
          simp [Polynomial.count_roots]
      _ = Multiset.card R.roots := Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
      _ ≤ R.natDegree := Polynomial.card_roots' R
  have : q * m ≤ R.natDegree := by
    calc q * m = ∑ _t : F, m := by simp [hq, mul_comm]
      _ ≤ ∑ t : F, R.rootMultiplicity t := Finset.sum_le_sum (fun t _ => hmult t)
      _ ≤ R.natDegree := hsum
  omega

/- ### Déshomogénéisation -/

theorem subst_coord_monomial {n : ℕ} (c : Fin n) (v : MvPolynomial (Fin n) F)
    (u : Fin n →₀ ℕ) (r : F) :
    aeval (fun k => if k = c then v else X k) (monomial u r) =
      monomial (u.erase c) r * v ^ u c := by
  classical
  have he : aeval (fun k => if k = c then v else X k) (monomial (u.erase c) r) =
      monomial (u.erase c) r := by
    rw [aeval_monomial, monomial_eq, MvPolynomial.algebraMap_eq]
    congr 1
    apply Finsupp.prod_congr
    intro k hk
    have hkc : k ≠ c := Finset.ne_of_mem_erase (by simpa only [Finsupp.support_erase] using hk)
    simp [hkc]
  calc
    _ = aeval (fun k => if k = c then v else X k)
        (monomial (u.erase c) r * X c ^ u c) := by
          rw [← monomial_add_single, Finsupp.erase_add_single]
    _ = _ := by rw [map_mul, map_pow, he, aeval_X, if_pos rfl]

theorem degree_erase_add_coord {n : ℕ} (c : Fin n) (u : Fin n →₀ ℕ) :
    (u.erase c).degree + u c = u.degree := by
  simpa only [map_add, Finsupp.degree_single] using
    congrArg Finsupp.degree (Finsupp.erase_add_single c u)

theorem dehom_as_sum {n : ℕ} (c : Fin n) (H : MvPolynomial (Fin n) F) :
    aeval (fun k => if k = c then (1 : MvPolynomial (Fin n) F) else X k) H =
      ∑ u ∈ H.support, monomial (u.erase c) (coeff u H) := by
  conv_lhs => rw [H.as_sum, map_sum]
  simp only [subst_coord_monomial, one_pow, mul_one]

/-- 11. -/
theorem dehom_ne_zero {n : ℕ} (c : Fin n) (d : ℕ) (H : MvPolynomial (Fin n) F)
    (hH : H.IsHomogeneous d) (h0 : H ≠ 0) :
    aeval (fun k => if k = c then (1 : MvPolynomial (Fin n) F) else X k) H ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := support_nonempty.mpr h0
  have inj : ∀ j ∈ H.support, j.erase c = u.erase c → j = u := by
    intro j hj he
    have hjd : j.degree = d := (hH.degree_eq_sum_deg_support hj).symm
    have hud : u.degree = d := (hH.degree_eq_sum_deg_support hu).symm
    have hjc := degree_erase_add_coord c j
    have huc := degree_erase_add_coord c u
    rw [he] at hjc
    have hc : j c = u c := by omega
    calc
      j = j.erase c + Finsupp.single c (j c) := (Finsupp.erase_add_single c j).symm
      _ = u.erase c + Finsupp.single c (u c) := by rw [he, hc]
      _ = u := Finsupp.erase_add_single c u
  intro hz
  have he := congrArg (coeff (R := F) (u.erase c)) hz
  rw [dehom_as_sum, coeff_sum, Finset.sum_eq_single u] at he
  · exact (mem_support_iff.mp hu) (by simpa using he)
  · intro j hj hju
    exact (coeff_monomial _ _ _).trans (if_neg (fun e => hju (inj j hj e)))
  · simp [hu]

/-- 12. -/
theorem totalDegree_dehom_lt {n : ℕ} (c : Fin n) (N : ℕ) (hN : 0 < N) (H : MvPolynomial (Fin n) F)
    (h : ∀ α ∈ H.support, Finsupp.degree α - α c < N) :
    (aeval (fun k => if k = c then (1 : MvPolynomial (Fin n) F) else X k) H).totalDegree < N := by
  classical
  rw [dehom_as_sum]
  apply lt_of_le_of_lt (totalDegree_finsetSum _ _)
  apply (Finset.sup_lt_iff hN).mpr
  intro u hu
  have hm : (monomial (u.erase c) (coeff u H)).totalDegree ≤ (u.erase c).degree :=
    totalDegree_monomial_le _ _
  have hd := degree_erase_add_coord c u
  have hlt := h u hu
  omega

theorem coeff_drop_coord {n : ℕ} (c : Fin n) (i : Fin n →₀ ℕ)
    (G : MvPolynomial (Fin n) F) :
    coeff i (aeval (fun k => if k = c then (0 : MvPolynomial (Fin n) F) else X k) G) =
      if i c = 0 then coeff i G else 0 := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [subst_coord_monomial]
    by_cases hu : u c = 0
    · by_cases hui : u = i
      · subst i
        simp [hu]
      · simp [hu, coeff_monomial, hui]
    · by_cases hui : u = i
      · subst i
        simp [hu]
      · simp [hu, coeff_monomial, hui]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp

/-- 13. Les dérivées de la déshomogénéisée en `a` sont celles de `H` en `a` où `a c := 1`. -/
theorem coeff_taylor_dehom {n : ℕ} (c : Fin n) (r : ℕ) (H : MvPolynomial (Fin n) F)
    (h : ∀ b : Fin n → F, b c = 1 → ∀ i : Fin n →₀ ℕ, i c = 0 → Finsupp.degree i < r →
      eval b (coeff i (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) H)) = 0)
    (a : Fin n → F) (i : Fin n →₀ ℕ) (hi : Finsupp.degree i < r) :
    coeff i (aeval (fun k => C (a k) + X k)
      (aeval (fun k => if k = c then (1 : MvPolynomial (Fin n) F) else X k) H)) = 0 := by
  classical
  let b := Function.update a c 1
  have hb : b c = 1 := by simp [b]
  have he : aeval (fun k => C (a k) + X k)
        (aeval (fun k => if k = c then (1 : MvPolynomial (Fin n) F) else X k) H) =
      aeval (fun k => if k = c then (0 : MvPolynomial (Fin n) F) else X k)
        (aeval (fun k => C (b k) + X k) H) := by
    rw [comp_aeval_apply, comp_aeval_apply]
    apply congrArg (fun f : Fin n → MvPolynomial (Fin n) F => aeval f H)
    funext k
    by_cases hk : k = c
    · subst k
      simp [hb, MvPolynomial.algebraMap_eq]
    · simp [b, hk, MvPolynomial.algebraMap_eq]
  rw [he, coeff_drop_coord]
  split_ifs with hic
  · rw [← eval_hasse]
    exact h b hb i hic hi
  · rfl

/-- 13 bis. La composante homogène de tête d'un polynôme non nul est non nulle. -/
theorem hc_top_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) F) (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨α, hα, hαd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP)
    (fun s => s.sum fun _ e => e)
  intro h0
  have hc := congrArg (coeff α) h0
  rw [coeff_homogeneousComponent, coeff_zero] at hc
  have hdα : Finsupp.degree α = P.totalDegree := by
    rw [totalDegree, hαd, Finsupp.degree_eq_sum]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simpa using hk)).symm
  rw [if_pos hdα] at hc
  exact (mem_support_iff.mp hα) hc

/- ### Le cœur : lemme 9 de l'article -/

/-- 14. Un polynôme à support dans `A` qui satisfait les conditions de `K × M` et de
`directions × F × N` est nul. -/
theorem vanish_imp_zero {n : ℕ} (c : Fin n) (q s : ℕ) (hq : Fintype.card F = q) (hs : 0 < s)
    (hSZ : ∀ (r : ℕ) (Q : MvPolynomial (Fin n) F),
      (∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
        coeff i (aeval (fun k => C (a k) + X k) Q) = 0) →
      Q.totalDegree < r * Fintype.card F → Q = 0)
    (K : Finset (Fin n → F)) (a : (Fin n → F) → (Fin n → F))
    (hline : ∀ b : Fin n → F, b c = 1 → ∀ t : F, a b + t • b ∈ K)
    (P : MvPolynomial (Fin n) F)
    (hP : ∀ α ∈ P.support, Finsupp.degree α < (2 * q - 1) * q * s ∧
      Finsupp.degree α - α c < q * q * s)
    (h1 : ∀ p ∈ K, ∀ β : Fin n →₀ ℕ, Finsupp.degree β < (2 * q - 1) * s →
      coeff β (aeval (fun k => C (p k) + X k) P) = 0)
    (h2 : ∀ b : Fin n → F, b c = 1 → ∀ t : F, ∀ (i : Fin n →₀ ℕ) (j : ℕ), i c = 0 →
      Finsupp.degree i < q * s → q * j + Finsupp.degree i < q * ((2 * q - 1) * s) →
      (2 * q - 1) * s ≤ Finsupp.degree i + j →
      (aeval (fun k => Polynomial.C ((a b + t • b) k) + Polynomial.C (b k) * Polynomial.X)
        (coeff i (aeval (fun k =>
          (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P))).coeff j = 0) :
    P = 0 := by
  classical
  by_contra hP0
  have hq2 : 2 ≤ q := hq ▸ Fintype.one_lt_card
  set d := P.totalDegree with hd
  obtain ⟨α0, hα0, hα0d⟩ : ∃ α ∈ P.support, Finsupp.degree α = d := by
    obtain ⟨α, hα, hαd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP0)
      (fun s => s.sum fun _ e => e)
    refine ⟨α, hα, ?_⟩
    rw [hd, totalDegree, hαd, Finsupp.degree_eq_sum]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simpa using hk)).symm
  have hdlt : d < (2 * q - 1) * q * s := by rw [← hα0d]; exact (hP α0 hα0).1
  -- (A) la restriction de chaque dérivée transverse à chaque droite de `K` est nulle
  have stepA : ∀ b : Fin n → F, b c = 1 → ∀ i : Fin n →₀ ℕ, i c = 0 → Finsupp.degree i < q * s →
      aeval (fun k => Polynomial.C (a b k) + Polynomial.C (b k) * Polynomial.X)
        (coeff i (aeval (fun k =>
          (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)) = 0 := by
    intro b hb i hic hi
    by_contra hR
    have key := natDegree_ge_of_taylor _ hR (Finsupp.degree i) ((2 * q - 1) * q * s) (by
      intro t j hj
      rw [taylor_lineRes]
      rw [hq] at hj
      by_cases hij : (2 * q - 1) * s ≤ Finsupp.degree i + j
      · exact h2 b hb t i j hic hi
          (by rw [show q * ((2 * q - 1) * s) = (2 * q - 1) * q * s by ring]; exact hj) hij
      · push Not at hij
        exact coeff_lineRes_hasse _ b i j P
          (fun β hβ => h1 _ (hline b hb t) β (lt_of_le_of_lt hβ hij)))
    have hD : coeff i (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P) ≠ 0 := by
      intro h0; apply hR; rw [h0, map_zero]
    have h4 := totalDegree_hasse i P hD
    have h6 := natDegree_lineRes_le (a b) b (coeff i (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P))
    omega
  -- (B) coefficient de tête : les dérivées transverses de la composante de tête s'annulent
  set H := homogeneousComponent d P with hH
  have stepB : ∀ b : Fin n → F, b c = 1 → ∀ i : Fin n →₀ ℕ, i c = 0 → Finsupp.degree i < q * s →
      eval b (coeff i (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) H)) = 0 := by
    intro b hb i hic hi
    by_cases hid : Finsupp.degree i ≤ d
    · have hA := stepA b hb i hic hi
      have hdeg : (coeff i (aeval (fun k =>
          (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P)).totalDegree ≤
          d - Finsupp.degree i := by
        by_cases hD : coeff i (aeval (fun k =>
            (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) P) = 0
        · rw [hD, totalDegree_zero]; exact Nat.zero_le _
        · have := totalDegree_hasse i P hD; omega
      have htop := coeff_lineRes_top (a b) b _ (d - Finsupp.degree i) hdeg
      rw [hA, Polynomial.coeff_zero, hc_hasse, Nat.sub_add_cancel hid] at htop
      exact htop.symm
    · push Not at hid
      have hz : coeff i (aeval (fun k =>
          (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) H) = 0 := by
        ext γ
        rw [coeff_hasse, coeff_zero, hH, coeff_homogeneousComponent, if_neg, mul_zero]
        rw [map_add]; omega
      rw [hz, map_zero]
  -- (C) la déshomogénéisée contredit Schwartz–Zippel à multiplicités
  have hH0 : H ≠ 0 := hc_top_ne_zero P hP0
  have hHhom : H.IsHomogeneous d := homogeneousComponent_isHomogeneous d P
  have hQ0 := dehom_ne_zero c d H hHhom hH0
  have hsupp : ∀ α ∈ H.support, Finsupp.degree α - α c < q * q * s := by
    intro α hα
    have hαP : α ∈ P.support := by
      rw [mem_support_iff] at hα ⊢
      rw [hH, coeff_homogeneousComponent] at hα
      split_ifs at hα
      · exact hα
      · exact absurd rfl hα
    exact (hP α hαP).2
  have hpos : 0 < q * q * s := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hs
  have hdeg := totalDegree_dehom_lt c (q * q * s) hpos H hsupp
  apply hQ0
  apply hSZ (q * s)
  · intro a' i hi
    exact coeff_taylor_dehom c (q * s) H stepB a' i hi
  · rw [hq]
    calc _ < q * q * s := hdeg
      _ = q * s * q := by ring

/- ### Algèbre linéaire et comptage -/

/-- 15. Il y a `q^(n-1)` directions avec `b c = 1`. -/
theorem card_dirs [DecidableEq F] {n : ℕ} (c : Fin n) :
    (Finset.univ.filter (fun b : Fin n → F => b c = 1)).card = Fintype.card F ^ (n - 1) := by
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset F) c
      (Finset.mem_univ (1 : F))

/-- 16. Dimension : `|A| ≤ |K| |M| + q^n |N|`. -/
theorem main_ineq {n : ℕ} (c : Fin n) (q s : ℕ) (hq : Fintype.card F = q) (hs : 0 < s)
    (hSZ : ∀ (r : ℕ) (Q : MvPolynomial (Fin n) F),
      (∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
        coeff i (aeval (fun k => C (a k) + X k) Q) = 0) →
      Q.totalDegree < r * Fintype.card F → Q = 0)
    (K : Finset (Fin n → F)) (hK : Kakeya.IsKakeyaFinite K) :
    ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * q * s)).filter
        (fun α : Fin n →₀ ℕ => Finsupp.degree α < (2 * q - 1) * q * s ∧
          Finsupp.degree α - α c < q * q * s)).card ≤
      K.card * ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * s)).filter
        (fun β : Fin n →₀ ℕ => Finsupp.degree β < (2 * q - 1) * s)).card +
      q ^ n * (((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => q * s)) ×ˢ
        Finset.range ((2 * q - 1) * s)).filter
        (fun ij : (Fin n →₀ ℕ) × ℕ => ij.1 c = 0 ∧ Finsupp.degree ij.1 < q * s ∧
          q * ij.2 + Finsupp.degree ij.1 < q * ((2 * q - 1) * s) ∧
          (2 * q - 1) * s ≤ Finsupp.degree ij.1 + ij.2)).card := by
  classical
  let box (d : ℕ) : Finset (Fin n →₀ ℕ) :=
    Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d)
  have mem_box {i : Fin n →₀ ℕ} {d : ℕ} (h : Finsupp.degree i < d) : i ∈ box d :=
    Finset.mem_Iic.mpr fun k => (Finsupp.le_degree k i).trans h.le
  let A := (box ((2 * q - 1) * q * s)).filter fun α =>
    Finsupp.degree α < (2 * q - 1) * q * s ∧ Finsupp.degree α - α c < q * q * s
  let M := (box ((2 * q - 1) * s)).filter fun β => Finsupp.degree β < (2 * q - 1) * s
  let N := ((box (q * s)) ×ˢ Finset.range ((2 * q - 1) * s)).filter
    fun ij => ij.1 c = 0 ∧ Finsupp.degree ij.1 < q * s ∧
      q * ij.2 + Finsupp.degree ij.1 < q * ((2 * q - 1) * s) ∧
      (2 * q - 1) * s ≤ Finsupp.degree ij.1 + ij.2
  change A.card ≤ K.card * M.card + q ^ n * N.card
  let D := Finset.univ.filter (fun b : Fin n → F => b c = 1)
  let a (b : Fin n → F) := if hb : b ≠ 0 then (hK b hb).choose else 0
  have hline (b : Fin n → F) (hb : b c = 1) : ∀ t : F, a b + t • b ∈ K := by
    have hn : b ≠ 0 := by rintro rfl; simp at hb
    simpa only [a, dif_pos hn] using (hK b hn).choose_spec
  let P (f : A → F) : MvPolynomial (Fin n) F := AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset A (fun α => if h : α ∈ A then f ⟨α, h⟩ else 0) (by
      intro α hα
      by_contra h
      simp [h] at hα))
  have cf (f : A → F) (α : Fin n →₀ ℕ) :
      coeff α (P f) = if h : α ∈ A then f ⟨α, h⟩ else 0 := rfl
  let I := (↥K × ↥M) ⊕ (↥D × F × ↥N)
  let Φ (f : A → F) : I → F := Sum.elim
    (fun x => coeff x.2.val (aeval (fun k => C (x.1.val k) + X k) (P f)))
    (fun x => (aeval (fun k => Polynomial.C ((a x.1.val + x.2.1 • x.1.val) k) +
      Polynomial.C (x.1.val k) * Polynomial.X) (coeff x.2.2.val.1 (aeval (fun k =>
        (C (X k) + X k : MvPolynomial (Fin n) (MvPolynomial (Fin n) F))) (P f)))).coeff
          x.2.2.val.2)
  have hinj : Function.Injective Φ := by
    intro f g he
    have hz : P f - P g = 0 := by
      apply vanish_imp_zero c q s hq hs hSZ K a hline
      · intro α hα
        have hm : α ∈ A := by
          by_contra h
          exact (MvPolynomial.mem_support_iff.mp hα) (by simp [coeff_sub, cf, h])
        exact (Finset.mem_filter.mp hm).2
      · intro p hp β hβ
        have hm : β ∈ M := Finset.mem_filter.mpr ⟨mem_box hβ, hβ⟩
        rw [map_sub, coeff_sub, sub_eq_zero]
        exact congrFun he (Sum.inl (⟨p, hp⟩, ⟨β, hm⟩) : I)
      · intro b hb t i j hic hi hij hsum
        have hj : j < (2 * q - 1) * s := Nat.lt_of_mul_lt_mul_left
          (lt_of_le_of_lt (Nat.le_add_right _ _) hij)
        have hm : (i, j) ∈ N := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨mem_box hi, Finset.mem_range.mpr hj⟩, hic, hi, hij, hsum⟩
        have hd : b ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
        rw [map_sub, coeff_sub, map_sub, Polynomial.coeff_sub, sub_eq_zero]
        exact congrFun he (Sum.inr (⟨b, hd⟩, t, ⟨(i, j), hm⟩) : I)
    funext α
    have h := congrArg (coeff α.val) (sub_eq_zero.mp hz)
    simpa only [cf, dif_pos α.property] using h
  have hcard := Fintype.card_le_of_injective Φ hinj
  simp only [Fintype.card_fun, Fintype.card_coe] at hcard
  have hdim := (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := F))).mp hcard
  have hD : D.card = q ^ (n - 1) := (card_dirs (F := F) c).trans (by rw [hq])
  have hn : n - 1 + 1 = n := by have := c.isLt; omega
  simpa only [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, hD, hq,
    ← Nat.mul_assoc, ← pow_succ, hn] using hdim

/-- 17. Arithmétique finale. -/
theorem final_arith {n q k : ℕ} (hn : 0 < n) (hq : 2 ≤ q)
    (h : q ^ (2 * n - 1) ≤ k * (2 * q - 1) ^ (n - 1)) :
    (q : ℚ) ^ n / (2 - 1 / (q : ℚ)) ^ (n - 1) ≤ k := by
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℚ) < 2 * q - 1 := by linarith
  have h2 : (2 - 1 / (q : ℚ)) = (2 * q - 1 : ℚ) / q := by field_simp
  have hcast : (q : ℚ) ^ (2 * n - 1) ≤ (k : ℚ) * (2 * q - 1 : ℚ) ^ (n - 1) := by
    have := (Nat.cast_le (α := ℚ)).mpr h
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * q)] at this
    exact this
  rw [h2, div_pow, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (q : ℚ) ^ n * q ^ (n - 1) = q ^ (2 * n - 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := hcast

/-- 18. Transport : il suffit de traiter les corps de `Type`. -/
theorem transport
    (h : ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), 0 < n → ∀ K : Finset (Fin n → F),
      Kakeya.IsKakeyaFinite K →
      (Fintype.card F : ℚ) ^ n / (2 - 1 / (Fintype.card F : ℚ)) ^ (n - 1) ≤ K.card)
    {n : ℕ} (hn : 0 < n) (K : Finset (Fin n → F)) (hK : Kakeya.IsKakeyaFinite K) :
    (Fintype.card F : ℚ) ^ n / (2 - 1 / (Fintype.card F : ℚ)) ^ (n - 1) ≤ K.card := by
  classical
  let e : F ≃+* Shrink.{0} F := (Shrink.ringEquiv.{0} F).symm
  let E : (Fin n → F) ↪ (Fin n → Shrink.{0} F) := e.toEquiv.toEmbedding.arrowCongrRight
  have hK' : Kakeya.IsKakeyaFinite (K.map E) := by
    intro v hv
    have hv' : (fun i => e.symm (v i)) ≠ (0 : Fin n → F) := by
      intro hz
      apply hv
      funext i
      simpa using congrArg e (congrFun hz i)
    obtain ⟨a, ha⟩ := hK _ hv'
    refine ⟨E a, fun t => Finset.mem_map.mpr ⟨_, ha (e.symm t), ?_⟩⟩
    funext i
    change e (a i + e.symm t * e.symm (v i)) = e (a i) + t * v i
    simp
  simpa only [Fintype.card_shrink, Finset.card_map] using h (Shrink.{0} F) n hn (K.map E) hK'

/-- 19. La borne pour un corps donné (assemblage, sans `sorry`). -/
theorem bound_of {n : ℕ} (hn : 0 < n)
    (hSZ : ∀ (r : ℕ) (Q : MvPolynomial (Fin n) F),
      (∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
        coeff i (aeval (fun k => C (a k) + X k) Q) = 0) →
      Q.totalDegree < r * Fintype.card F → Q = 0)
    (h2 : ∀ (n q k : ℕ) (c : Fin n), 2 ≤ q →
        (∀ s : ℕ, 0 < s →
          ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * q * s)).filter
            (fun α : Fin n →₀ ℕ => Finsupp.degree α < (2 * q - 1) * q * s ∧
              Finsupp.degree α - α c < q * q * s)).card ≤
          k * ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * s)).filter
            (fun β : Fin n →₀ ℕ => Finsupp.degree β < (2 * q - 1) * s)).card +
          q ^ n * (((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => q * s)) ×ˢ
            Finset.range ((2 * q - 1) * s)).filter
            (fun ij : (Fin n →₀ ℕ) × ℕ => ij.1 c = 0 ∧ Finsupp.degree ij.1 < q * s ∧
              q * ij.2 + Finsupp.degree ij.1 < q * ((2 * q - 1) * s) ∧
              (2 * q - 1) * s ≤ Finsupp.degree ij.1 + ij.2)).card) →
        q ^ (2 * n - 1) ≤ k * (2 * q - 1) ^ (n - 1))
    (K : Finset (Fin n → F)) (hK : Kakeya.IsKakeyaFinite K) :
    (Fintype.card F : ℚ) ^ n / (2 - 1 / (Fintype.card F : ℚ)) ^ (n - 1) ≤ K.card := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  exact final_arith hn hq (h2 n (Fintype.card F) K.card ⟨0, hn⟩ hq
    (fun s hs => main_ineq ⟨0, hn⟩ _ s rfl hs hSZ K hK))

/-- 20. Assemblage : Schwartz–Zippel à multiplicités, puis comptage, donnent la cible. -/
theorem main :
    (∀ (F : Type) [Field F] [Fintype F] (n r : ℕ) (Q : MvPolynomial (Fin n) F),
        (∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
          coeff i (aeval (fun k => C (a k) + X k) Q) = 0) →
        Q.totalDegree < r * Fintype.card F → Q = 0) →
    (∀ (n q k : ℕ) (c : Fin n), 2 ≤ q →
        (∀ s : ℕ, 0 < s →
          ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * q * s)).filter
            (fun α : Fin n →₀ ℕ => Finsupp.degree α < (2 * q - 1) * q * s ∧
              Finsupp.degree α - α c < q * q * s)).card ≤
          k * ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * s)).filter
            (fun β : Fin n →₀ ℕ => Finsupp.degree β < (2 * q - 1) * s)).card +
          q ^ n * (((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => q * s)) ×ˢ
            Finset.range ((2 * q - 1) * s)).filter
            (fun ij : (Fin n →₀ ℕ) × ℕ => ij.1 c = 0 ∧ Finsupp.degree ij.1 < q * s ∧
              q * ij.2 + Finsupp.degree ij.1 < q * ((2 * q - 1) * s) ∧
              (2 * q - 1) * s ≤ Finsupp.degree ij.1 + ij.2)).card) →
        q ^ (2 * n - 1) ≤ k * (2 * q - 1) ^ (n - 1)) →
    type_of% @Kakeya.kakeya_finite := by
  intro h1 h2 F _ _ n hn K hK
  exact transport (fun F' _ _ n' hn' K' hK' => bound_of hn' (h1 F' n') h2 K' hK') hn K hK

/-- La première variable devient la variable du polynôme univarié translaté. -/
private theorem sz_shift_split {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) F)
    (x : F) (a : Fin n → F) :
    finSuccEquiv F n (aeval (fun k => C ((Fin.cons x a : Fin (n + 1) → F) k) + X k) Q) =
      (finSuccEquiv F n Q).eval₂
        (Polynomial.C.comp (aeval (fun k => C (a k) + X k)).toRingHom)
        (Polynomial.X + Polynomial.C (C x)) := by
  have hC (c : F) : finSuccEquiv F n (C c) = Polynomial.C (C c) := by
    simp [finSuccEquiv_apply]
  induction Q using MvPolynomial.induction_on with
  | C c => simp [hC, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp, aeval_X, map_add, hC]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [finSuccEquiv_X_zero, add_comm]
    · simp [finSuccEquiv_X_succ]

/-- Coefficient de Taylor dans les variables restantes, lu comme polynôme en la première. -/
private theorem sz_slice {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) F)
    (a : Fin n → F) (i : Fin n →₀ ℕ) :
    ∃ R : Polynomial F,
      (∀ k, R.coeff k = coeff i (aeval (fun u => C (a u) + X u)
        ((finSuccEquiv F n Q).coeff k))) ∧
      ∀ (x : F) (j : ℕ), (Polynomial.taylor x R).coeff j =
        coeff (i.cons j) (aeval (fun k => C ((Fin.cons x a : Fin (n + 1) → F) k) + X k) Q) := by
  classical
  let P := finSuccEquiv F n Q
  let T : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F := aeval (fun k => C (a k) + X k)
  let R : Polynomial F := ∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.monomial k (coeff i (T (P.coeff k)))
  refine ⟨R, ?_, ?_⟩
  · intro k
    change R.coeff k = coeff i (T (P.coeff k))
    by_cases hk : k < P.natDegree + 1
    · simp [R, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hk]
    · have h0 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [R, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hk, h0]
  · intro x j
    rw [← finSuccEquiv_coeff_coeff, sz_shift_split, Polynomial.eval₂_eq_sum_range]
    simp only [R, P, T, map_sum, Polynomial.finsetSum_coeff, Polynomial.taylor_monomial,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeff_C_mul,
      coeff_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hpow : ((Polynomial.X + Polynomial.C (C x) : Polynomial (MvPolynomial (Fin n) F)) ^ k).coeff j =
        C (((Polynomial.X + Polynomial.C x) ^ k).coeff j) := by
      rw [← Polynomial.coeff_map, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_C]
    rw [hpow, mul_comm _ (C _), coeff_C_mul, mul_comm]

/-- Schwartz–Zippel à multiplicités sur la grille pleine. -/
theorem sz_mult (n r : ℕ) (Q : MvPolynomial (Fin n) F)
    (h : ∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
      coeff i (aeval (fun k => C (a k) + X k) Q) = 0)
    (hdeg : Q.totalDegree < r * Fintype.card F) : Q = 0 := by
  classical
  induction n generalizing r with
  | zero =>
    have hr : 0 < r := by by_contra! h0; simp [Nat.eq_zero_of_le_zero h0] at hdeg
    have hz := h (fun _ => 0) 0 (by simpa using hr)
    obtain ⟨c, rfl⟩ := C_surjective (Fin 0) Q
    simpa [algebraMap_eq] using congrArg (C : F →+* MvPolynomial (Fin 0) F)
      (show c = 0 by simpa [algebraMap_eq] using hz)
  | succ n ih =>
    by_contra hQ
    let P := finSuccEquiv F n Q
    let t := P.natDegree
    let q := Fintype.card F
    have hq : 0 < q := Fintype.card_pos
    have hP : P ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hQ
    have ht : P.coeff t ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hd : (P.coeff t).totalDegree + t ≤ Q.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le Q t ht
    change Q.totalDegree < r * q at hdeg
    apply ht
    apply ih (r - t / q) (P.coeff t)
    · intro a i hi
      obtain ⟨R, hc, hs⟩ := sz_slice Q a i
      change coeff i (aeval _ ((finSuccEquiv F n Q).coeff t)) = 0
      rw [← hc]
      by_contra hcoeff
      have hR : R ≠ 0 := fun hz => hcoeff (by simp [hz])
      have hdt : R.natDegree ≤ t := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
        intro k hk
        rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < k from hk)]
        simp)
      have hm := natDegree_ge_of_taylor R hR 0 (q * (r - Finsupp.degree i)) (by
        intro x j hj
        change q * j + 0 < q * (r - Finsupp.degree i) at hj
        rw [add_zero, Nat.mul_lt_mul_left hq] at hj
        rw [hs]
        apply h
        change (i.cons j).sum (fun _ e => e) < r
        rw [Finsupp.sum_cons]
        change j + Finsupp.degree i < r
        omega)
      have hl : r - Finsupp.degree i ≤ t / q := (Nat.le_div_iff_mul_le hq).mpr (by
        rw [mul_comm]; omega)
      omega
    · change (P.coeff t).totalDegree < (r - t / q) * q
      rw [Nat.sub_mul]
      have := Nat.div_mul_le_self t q
      omega

/-- Schwartz–Zippel à multiplicités sur la grille pleine (Dvir–Kopparty–Saraf–Sudan, lemme 2.7) :
un polynôme dont toutes les dérivées de Hasse d'ordre `< r` s'annulent en tout point de `F^n` et
de degré total `< r q` est nul. -/
theorem H1_proof :
    ∀ (F : Type) [Field F] [Fintype F] (n r : ℕ) (Q : MvPolynomial (Fin n) F),
      (∀ (a : Fin n → F) (i : Fin n →₀ ℕ), Finsupp.degree i < r →
        coeff i (aeval (fun k => C (a k) + X k) Q) = 0) →
      Q.totalDegree < r * Fintype.card F → Q = 0 := by
  intro F _ _ n r Q h hdeg
  exact sz_mult n r Q h hdeg

open Finset Filter Topology

private theorem htwo_box {n L : ℕ} (x : Fin n →₀ ℕ) (h : x.degree ≤ L) :
    x ∈ Iic (Finsupp.equivFunOnFinite.symm fun _ => L) := by
  exact mem_Iic.mpr fun i => (Finsupp.le_degree i x).trans h

private theorem htwo_off {n : ℕ} (c : Fin n) (x : Fin n →₀ ℕ) (d : ℕ) :
    x ∈ (univ.erase c).finsuppAntidiag d ↔ x c = 0 ∧ x.degree = d := by
  rw [mem_finsuppAntidiag']
  -- Le support ne contient pas la coordonnée distinguée.
  have hs : x.support ⊆ univ.erase c ↔ x c = 0 := by
    simp only [Finset.subset_iff, Finsupp.mem_support_iff, mem_erase, mem_univ, and_true]
    constructor
    · intro h
      by_contra hne
      exact h hne rfl
    · intro hc t ht he
      exact ht (he ▸ hc)
  rw [hs]
  change (x.degree = d ∧ _) ↔ _
  tauto

private theorem htwo_sum_mult (m L : ℕ) (hL : 0 < L) :
    ∑ d ∈ range L, m.multichoose d = (L - 1 + m).choose m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  simpa using Nat.sum_range_multichoose t m

private theorem htwo_simplex (n L : ℕ) (hL : 0 < L) :
    ((Iic (Finsupp.equivFunOnFinite.symm fun _ => L)).filter
      (fun x : Fin n →₀ ℕ => x.degree < L)).card = (L - 1 + n).choose n := by
  rw [← htwo_sum_mult _ _ hL]
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin n →₀ ℕ => x.degree) (t := range L)
    (by intro x hx; exact mem_range.mpr (mem_filter.mp hx).2)]
  apply sum_congr rfl
  intro d hd
  have h : d < L := mem_range.mp hd
  have e : (((Iic (Finsupp.equivFunOnFinite.symm fun _ => L)).filter
      (fun x : Fin n →₀ ℕ => x.degree < L)).filter (fun x => x.degree = d))
      = univ.finsuppAntidiag d := by
    ext x
    simp only [mem_filter, mem_finsuppAntidiag', subset_univ, and_true]
    change (_ ∧ _) ∧ x.degree = d ↔ x.degree = d
    exact ⟨And.right, fun hx => ⟨⟨htwo_box x (hx ▸ h.le), hx ▸ h⟩, hx⟩⟩
  rw [e, card_finsuppAntidiag_nat_eq_multichoose]
  simp

private theorem htwo_sliced {m : ℕ} (c : Fin (m + 1)) (U L : ℕ) :
    ((Iic (Finsupp.equivFunOnFinite.symm fun _ => U)).filter
      (fun x : Fin (m + 1) →₀ ℕ => x.degree < U ∧ x.degree - x c < L)).card
    = ∑ d ∈ range L, m.multichoose d * (U - d) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin (m+1) →₀ ℕ => x.degree - x c)
    (t := range L) (by intro x hx; exact mem_range.mpr (mem_filter.mp hx).2.2)]
  apply sum_congr rfl
  intro d hd
  have h : d < L := mem_range.mp hd
  have hh : ∀ x : Fin (m+1) →₀ ℕ, (x.erase c).degree + x c = x.degree := by
    intro x
    simpa using congrArg Finsupp.degree (Finsupp.erase_add_single c x)
  have e := card_nbij' (s := ((Iic (Finsupp.equivFunOnFinite.symm fun _ => U)).filter
      (fun x : Fin (m + 1) →₀ ℕ => x.degree < U ∧ x.degree - x c < L)).filter
      (fun x => x.degree - x c = d))
      (t := ((univ.erase c).finsuppAntidiag d) ×ˢ range (U - d))
      (fun x => (x.erase c, x c)) (fun p => p.1 + Finsupp.single c p.2)
  rw [← show (((univ.erase c).finsuppAntidiag d) ×ˢ range (U - d)).card =
      m.multichoose d * (U - d) by
    rw [card_product, card_range, card_finsuppAntidiag_nat_eq_multichoose]
    simp]
  apply e
  · intro x hx
    obtain ⟨⟨_, hx, _⟩, he⟩ := mem_filter.mp hx |>.imp_left mem_filter.mp
    dsimp only at he hx ⊢
    have := hh x
    have hdg : (x.erase c).degree = d := by omega
    exact mem_product.mpr ⟨(htwo_off c (x.erase c) d).mpr ⟨by simp, hdg⟩,
      mem_range.mpr (by omega)⟩
  · rintro ⟨x,j⟩ hx
    obtain ⟨hx, hj⟩ := mem_product.mp hx
    obtain ⟨hc, hx⟩ := (htwo_off ..).mp hx
    have hj' := mem_range.mp hj
    have hs : (x + Finsupp.single c j).degree = d + j := by simp [hx]
    have hv : (x + Finsupp.single c j) c = j := by simp [hc]
    have hu : (x + Finsupp.single c j).degree < U := by omega
    dsimp only
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨htwo_box _ hu.le, hu, by omega⟩, by omega⟩
  · intro x _
    exact Finsupp.erase_add_single c x
  · rintro ⟨x,j⟩ hx
    have hc := ((htwo_off ..).mp (mem_product.mp hx).1).1
    change ((x + Finsupp.single c j).erase c, (x + Finsupp.single c j) c) = (x,j)
    rw [← Finsupp.update_eq_add_single hc]
    simp [Finsupp.erase_of_notMem_support (by simpa using hc : c ∉ x.support)]

private theorem htwo_balanced {m : ℕ} (c : Fin (m+1)) (L : ℕ) (hL : 0 < L) :
    ∑ d ∈ range L, m.multichoose d * (L - d) = (L - 1 + (m+1)).choose (m+1) := by
  rw [← htwo_sliced c L L, ← htwo_simplex (m+1) L hL]
  apply congrArg Finset.card
  ext x
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,(Nat.sub_le ..).trans_lt h.2⟩⟩

private theorem htwo_A {m : ℕ} (c : Fin (m+1)) (U L : ℕ) (hL : 0 < L) (hle : L ≤ U) :
    ((Iic (Finsupp.equivFunOnFinite.symm fun _ => U)).filter
      (fun x : Fin (m + 1) →₀ ℕ => x.degree < U ∧ x.degree - x c < L)).card =
    (U - L) * (L - 1 + m).choose m + (L - 1 + (m+1)).choose (m+1) := by
  rw [htwo_sliced, ← htwo_sum_mult _ _ hL, ← htwo_balanced c L hL,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have := mem_range.mp hd
  rw [show U - d = (U - L) + (L - d) by omega]
  ring

private theorem htwo_moment {m : ℕ} (c : Fin (m+1)) (L : ℕ) (hL : 0 < L) :
    (∑ d ∈ range L, m.multichoose d * d) + (L - 1 + (m+1)).choose (m+1) =
    L * (L - 1 + m).choose m := by
  rw [← htwo_balanced c L hL, ← htwo_sum_mult _ _ hL, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [← Nat.mul_add, Nat.add_sub_of_le (mem_range.mp hd).le, mul_comm]

private theorem htwo_N {m : ℕ} (c : Fin (m+1)) (q U L : ℕ) (hq : 0 < q)
    (hL : 0 < L) (hle : L ≤ U) :
    q * (((Iic (Finsupp.equivFunOnFinite.symm fun _ => L)) ×ˢ range U).filter
      (fun p : (Fin (m+1) →₀ ℕ) × ℕ => p.1 c = 0 ∧ p.1.degree < L ∧
        q * p.2 + p.1.degree < q * U ∧ U ≤ p.1.degree + p.2)).card +
      (q-1) * (L - 1 + (m+1)).choose (m+1) ≤
    ((q-1)*L+q) * (L - 1 + m).choose m := by
  classical
  let Z := (((Iic (Finsupp.equivFunOnFinite.symm fun _ => L)) ×ˢ range U).filter
      (fun p : (Fin (m+1) →₀ ℕ) × ℕ => p.1 c = 0 ∧ p.1.degree < L ∧
        q * p.2 + p.1.degree < q * U ∧ U ≤ p.1.degree + p.2))
  change q * Z.card + _ ≤ _
  have hz : q * Z.card ≤ ∑ d ∈ range L, m.multichoose d * ((q-1)*d+q) := by
    rw [card_eq_sum_card_fiberwise (s := Z) (f := fun p => p.1.degree) (t := range L)
      (by intro p hp; exact mem_range.mpr (mem_filter.mp hp).2.2.1), mul_sum]
    apply sum_le_sum
    intro d hd
    have hd' := mem_range.mp hd
    have hsub : (Z.filter fun p => p.1.degree = d) ⊆
        ((univ.erase c).finsuppAntidiag d) ×ˢ Ico (U-d) (U-d/q) := by
      rintro ⟨x,j⟩ hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨hbox, hc, hdeg, hj, hlow⟩ := mem_filter.mp hp
      dsimp only at hc hdeg hj hlow he
      replace hj : q * j + d < q * U := he ▸ hj
      have hju := mem_range.mp (mem_product.mp hbox).2
      have hdiv : d / q < U - j := (Nat.div_lt_iff_lt_mul hq).mpr (by
        rw [Nat.sub_mul, mul_comm U, mul_comm j]
        omega)
      exact mem_product.mpr ⟨(htwo_off ..).mpr ⟨hc, he⟩, mem_Ico.mpr ⟨by omega, by omega⟩⟩
    have hb := card_le_card hsub
    rw [card_product, Nat.card_Ico, card_finsuppAntidiag_nat_eq_multichoose] at hb
    simp only [card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin,
      Nat.add_one_sub_one] at hb
    refine (Nat.mul_le_mul_left q hb).trans ?_
    rw [mul_left_comm]
    apply Nat.mul_le_mul_left
    have hdq := Nat.div_le_self d q
    have ht : (U - d / q - (U - d)) = d - d / q := by omega
    rw [ht, Nat.mul_sub, Nat.sub_mul]
    have he := Nat.mod_add_div d q
    have hm := Nat.mod_lt d hq
    simp only [one_mul]
    omega
  have he : (∑ d ∈ range L, m.multichoose d * ((q-1)*d+q)) =
      (q-1) * (∑ d ∈ range L, m.multichoose d * d) + q * (L - 1 + m).choose m := by
    rw [← htwo_sum_mult _ _ hL, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [he] at hz
  have hm := congrArg ((q-1) * ·) (htwo_moment c L hL)
  simp only [Nat.mul_add] at hm
  rw [Nat.add_mul]
  nlinarith only [hm, hz]

private theorem htwo_lim_asc (a r : ℕ) :
    Tendsto (fun s : ℕ => ((a*s).ascFactorial r : ℝ) * (s : ℝ)⁻¹ ^ r)
      atTop (𝓝 ((a : ℝ)^r)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ht : Tendsto (fun s : ℕ => (a : ℝ) + (r : ℝ) * (s : ℝ)⁻¹)
        atTop (𝓝 (a : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (a : ℝ))).add
        ((tendsto_const_nhds (x := (r : ℝ))).mul tendsto_inv_atTop_nhds_zero_nat)
    rw [pow_succ']
    apply (ht.mul ih).congr'
    filter_upwards [eventually_ge_atTop 1] with s hs
    have h : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    simp only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add, pow_succ]
    field_simp

private theorem htwo_lim (a r : ℕ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => (((a*s - 1+r).choose r : ℝ) * (s : ℝ)⁻¹ ^ r))
      atTop (𝓝 ((a : ℝ)^r / (r.factorial : ℝ))) := by
  apply ((htwo_lim_asc a r).div_const (r.factorial : ℝ)).congr'
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs' : 0 < a*s := Nat.mul_pos ha (by omega)
  rw [Nat.ascFactorial_eq_factorial_mul_choose', show a*s+r-1 = a*s-1+r by omega,
    Nat.cast_mul]
  field_simp

private theorem htwo_take_limit (m q k u b v : ℕ) (hq : 0 < q) (hu : 0 < u) (hb : 0 < b)
    (h : ∀ s : ℕ, 0 < s →
      q * (v*s * ((b*s - 1 + m).choose m) + (b*s - 1 + (m+1)).choose (m+1)) +
        q^(m+1) * (q-1) * ((q*s-1+(m+1)).choose (m+1)) ≤
      q*k * ((u*s-1+(m+1)).choose (m+1)) +
        q^(m+1) * (((q-1)*q*s+q) * ((q*s-1+m).choose m))) :
    (q:ℝ) * ((v:ℝ) * ((b:ℝ)^m / m.factorial) + (b:ℝ)^(m+1) / (m+1).factorial) +
      (q:ℝ)^(m+1) * (q-1) * ((q:ℝ)^(m+1) / (m+1).factorial) ≤
    (q:ℝ)*k * ((u:ℝ)^(m+1) / (m+1).factorial) +
      (q:ℝ)^(m+1) * (((q:ℝ)-1)*q * ((q:ℝ)^m / m.factorial)) := by
  let C (a r s : ℕ) : ℝ := (a*s-1+r).choose r
  let S (a r s : ℕ) : ℝ := C a r s * (s:ℝ)⁻¹ ^ r
  have hS (a r : ℕ) (ha : 0 < a) : Tendsto (S a r) atTop (𝓝 ((a:ℝ)^r / r.factorial)) :=
    htwo_lim a r ha
  have ht : Tendsto (fun s : ℕ => ((q:ℝ)-1)*q+(q:ℝ)*(s:ℝ)⁻¹) atTop
      (𝓝 (((q:ℝ)-1)*q)) := by
    simpa using (tendsto_const_nhds (x := ((q:ℝ)-1)*q)).add
      ((tendsto_const_nhds (x := (q:ℝ))).mul tendsto_inv_atTop_nhds_zero_nat)
  apply le_of_tendsto_of_tendsto
    (((((hS b m hb).const_mul (v:ℝ)).add (hS b (m+1) hb)).const_mul (q:ℝ)).add
      ((hS q (m+1) hq).const_mul ((q:ℝ)^(m+1)*(q-1))))
    ((((hS u (m+1) hu).const_mul ((q:ℝ)*k))).add
      ((ht.mul (hS q m hq)).const_mul ((q:ℝ)^(m+1))))
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs' : 0 < s := by omega
  have hn : (s:ℝ) ≠ 0 := by positivity
  have raw : (q:ℝ) * ((v:ℝ)*s * C b m s + C b (m+1) s) +
      (q:ℝ)^(m+1) * (q-1) * C q (m+1) s ≤
      (q:ℝ)*k * C u (m+1) s + (q:ℝ)^(m+1)*((((q:ℝ)-1)*q*s+q)*C q m s) := by
    unfold C
    rw [show (q:ℝ)-1 = ((q-1 : ℕ):ℝ) by simp [Nat.cast_sub (show 1 ≤ q by omega)]]
    exact_mod_cast h s hs'
  have hc := mul_le_mul_of_nonneg_right raw (by positivity : 0 ≤ (s:ℝ)⁻¹ ^ (m+1))
  change (q:ℝ) * ((v:ℝ)*S b m s + S b (m+1) s) + _ ≤ _
  dsimp only [S]
  simp only [pow_succ (s:ℝ)⁻¹] at hc ⊢
  field_simp [hn] at hc ⊢
  linarith only [hc]

/-- Le comptage de Bukh–Chao : l'inégalité `|A| ≤ k |M| + q^n |N|` pour tout `s` donne, à la limite
`s → ∞`, `q^(2n-1) ≤ k (2q-1)^(n-1)`. -/
theorem H2_proof :
    ∀ (n q k : ℕ) (c : Fin n), 2 ≤ q →
      (∀ s : ℕ, 0 < s →
        ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * q * s)).filter
          (fun α : Fin n →₀ ℕ => Finsupp.degree α < (2 * q - 1) * q * s ∧
            Finsupp.degree α - α c < q * q * s)).card ≤
        k * ((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => (2 * q - 1) * s)).filter
          (fun β : Fin n →₀ ℕ => Finsupp.degree β < (2 * q - 1) * s)).card +
        q ^ n * (((Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => q * s)) ×ˢ
          Finset.range ((2 * q - 1) * s)).filter
          (fun ij : (Fin n →₀ ℕ) × ℕ => ij.1 c = 0 ∧ Finsupp.degree ij.1 < q * s ∧
            q * ij.2 + Finsupp.degree ij.1 < q * ((2 * q - 1) * s) ∧
            (2 * q - 1) * s ≤ Finsupp.degree ij.1 + ij.2)).card) →
      q ^ (2 * n - 1) ≤ k * (2 * q - 1) ^ (n - 1) := by
  intro n q k c hq hh
  cases n with
  | zero => exact Fin.elim0 c
  | succ m =>
    have hqp : 0 < q := by omega
    have hu : 0 < 2*q-1 := by omega
    have hle : q ≤ 2*q-1 := by omega
    have hlim := htwo_take_limit m q k (2*q-1) (q*q) ((q-1)*q) hqp hu
      (Nat.mul_pos hqp hqp) (by
        intro s hs
        have h := hh s hs
        have hN := htwo_N c q ((2*q-1)*s) (q*s) hqp (Nat.mul_pos hqp hs)
          (Nat.mul_le_mul_right s hle)
        have hTL := Nat.mul_le_mul_right s (Nat.mul_le_mul_right q hle)
        have he : (2*q-1)*q*s - q*q*s = (q-1)*q*s := by
          rw [← Nat.sub_mul, ← Nat.sub_mul, show 2*q-1-q = q-1 by omega]
        rw [htwo_A c _ _ (by positivity) hTL, he, htwo_simplex _ _ (Nat.mul_pos hu hs)] at h
        nlinarith only [Nat.mul_le_mul_left q h, Nat.mul_le_mul_left (q^(m+1)) hN])
    have hqR : 0 < (q:ℝ) := by positivity
    have huR : 0 < 2*(q:ℝ)-1 := by exact_mod_cast (show 0 < (2*(q:ℤ)-1) by omega)
    have hf : 0 < (m.factorial:ℝ) := by positivity
    simp only [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_sub (show 1 ≤ 2*q by omega),
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hlim
    field_simp at hlim
    rw [show 2 * (m+1) - 1 = m+m+1 by omega, Nat.add_one_sub_one]
    have goalR : (q:ℝ)^(m+m+1) ≤ (k:ℝ) * (2*(q:ℝ)-1)^m := by
      apply le_of_mul_le_mul_left (a := (2*(q:ℝ)-1)*q) _ (by positivity)
      simp only [pow_succ, pow_add, mul_pow] at hlim ⊢
      simp only [pow_zero, one_pow, one_mul, mul_one, mul_comm (q:ℝ) 2] at hlim
      linarith only [hlim]
    have huCast : (2*(q:ℝ)-1) = ((2*q-1 : ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*q), Nat.cast_mul]; norm_num
    rw [huCast] at goalR
    exact_mod_cast goalR

end OMA.BukhChao

theorem OMA.solution : type_of% @Kakeya.kakeya_finite :=
  OMA.BukhChao.main OMA.BukhChao.H1_proof
    OMA.BukhChao.H2_proof
