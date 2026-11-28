import OMAStatements.S_mo_108300

open CategoryTheory MvPolynomial OMA.S_mo_108300

namespace OMA.Ralph

abbrev F := ZMod 2
abbrev P := MvPolynomial ℕ F

def w (k : ℕ) : ℤ := k + 1

noncomputable def grade (d : ℤ) : AddSubgroup P := (weightedHomogeneousSubmodule F w d).toAddSubgroup

noncomputable abbrev gradedP : GradedRing grade where
  one_mem := isWeightedHomogeneous_one F w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul
  decompose' := (weightedDecomposition F w).decompose'
  left_inv := (weightedDecomposition F w).left_inv
  right_inv := (weightedDecomposition F w).right_inv

/-- Set all variables indexed at least k to zero. -/
noncomputable def truncate (k : ℕ) : P →+* P :=
  eval₂Hom C (fun j => if j < k then X j else 0)

theorem truncate_comp {i j : ℕ} (h : i ≤ j) :
    (truncate i).comp (truncate j) = truncate i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [truncate]
  · intro k
    by_cases hk : k < i
    · have hj := hk.trans_le h
      simp [truncate, hk, hj]
    · by_cases hj : k < j <;> simp [truncate, hk, hj]

theorem truncate_monomial (i : ℕ) (D : ℕ →₀ ℕ) (c : F) :
    truncate i (monomial D c) =
      if ∀ k ∈ D.support, k < i then monomial D c else 0 := by
  classical
  unfold truncate
  rw [eval₂Hom_monomial]
  split_ifs with h
  · rw [show (D.prod fun k a => (if k < i then X k else (0 : P)) ^ a) =
        D.prod (fun k a => (X k : P) ^ a) by
        apply Finset.prod_congr rfl
        intro k hk
        simp [h k hk]]
    have hId : eval₂Hom (C : F →+* P) X = RingHom.id P := by
      apply MvPolynomial.ringHom_ext <;> simp
    rw [← eval₂Hom_monomial, hId]
    rfl
  · push_neg at h
    obtain ⟨k, hk, hik⟩ := h
    have hzero : (if k < i then X k else (0 : P)) ^ D k = 0 := by
      rw [if_neg (not_lt_of_ge hik), zero_pow (Finsupp.mem_support_iff.1 hk)]
    show C c * (∏ k ∈ D.support, (if k < i then X k else (0 : P)) ^ D k) = 0
    rw [Finset.prod_eq_zero hk hzero, mul_zero]

theorem monomial_mem_grade_of_support {p : P} {d : ℤ} (hp : p ∈ grade d)
    {D : ℕ →₀ ℕ} (hD : D ∈ p.support) : monomial D (p.coeff D) ∈ grade d :=
  isWeightedHomogeneous_monomial w D _ (hp (MvPolynomial.mem_support_iff.1 hD))

theorem truncate_grade {p : P} {d : ℤ} (i : ℕ) (hp : p ∈ grade d) :
    truncate i p ∈ grade d := by
  classical
  rw [p.as_sum, map_sum]
  apply AddSubgroup.sum_mem
  intro D hD
  rw [truncate_monomial]
  split_ifs
  · exact monomial_mem_grade_of_support hp hD
  · exact (grade d).zero_mem



/-- A homogeneous component is unaffected once the cutoff reaches its degree. -/
theorem truncate_fix {p : P} {d : ℤ} {j : ℕ} (hj : d.toNat ≤ j) (hp : p ∈ grade d) :
    truncate j p = p := by
  classical
  conv_rhs => rw [p.as_sum]
  conv_lhs => rw [p.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [truncate_monomial, if_pos]
  intro k hk
  have hweight : Finsupp.weight w D = d := hp (MvPolynomial.mem_support_iff.1 hD)
  have hk' := Finsupp.le_weight_of_ne_zero (w := w) (fun n => by dsimp [w]; positivity)
    (Finsupp.mem_support_iff.1 hk)
  rw [hweight] at hk'
  dsimp [w] at hk'
  omega

noncomputable def constantTower : RalphGradedSystem ℕ where
  obj := fun _ => RingCat.of P
  grade := fun _ => grade
  graded := fun _ => gradedP
  map := fun {i j} _ => RingHom.id P
  map_refl := by intros; rfl
  map_trans := by intros; ext <;> rfl
  map_grade := by intros; assumption

noncomputable def bonding (i j : ℕ) : P →+* P :=
  if i = j then RingHom.id P else truncate i

noncomputable def truncatedTower : RalphGradedSystem ℕ where
  obj := fun _ => RingCat.of P
  grade := fun _ => grade
  graded := fun _ => gradedP
  map := fun {i j} _ => bonding i j
  map_refl := fun i => by simp [bonding]
  map_trans := by
    intro i j k hij hjk
    rcases eq_or_lt_of_le hij with rfl | hij
    · simp [bonding]
    rcases eq_or_lt_of_le hjk with rfl | hjk
    · simp [bonding]
    simp [bonding, hij.ne, hjk.ne, (hij.trans hjk).ne, truncate_comp hij.le]
  map_grade := by
    intro i j h d x hx
    by_cases he : i = j
    · simpa [bonding, he] using hx
    · simpa [bonding, he] using (truncate_grade i hx)


noncomputable def degreeIso (d : ℤ) :
    ralphGradeLimit constantTower d ≃+ ralphGradeLimit truncatedTower d where
  toFun x := ⟨⟨fun i => truncate i (x.val.val 0), by
    intro i j hij
    change bonding i j (truncate j (x.val.val 0)) = truncate i (x.val.val 0)
    by_cases he : i = j
    · subst j
      simp [bonding]
    · have h := DFunLike.congr_fun (truncate_comp hij) (x.val.val 0)
      change truncate i (truncate j (x.val.val 0)) = truncate i (x.val.val 0) at h
      simpa [bonding, he] using h⟩, fun i => truncate_grade i (x.property 0)⟩
  invFun y := ⟨⟨fun _ => y.val.val d.toNat, by intro i j hij; rfl⟩, fun _ => y.property d.toNat⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change truncate d.toNat (x.val.val 0) = x.val.val i
    rw [truncate_fix le_rfl (x.property 0)]
    exact (x.val.property 0 i (Nat.zero_le i)).symm
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change truncate i (y.val.val d.toNat) = y.val.val i
    rcases lt_trichotomy i d.toNat with h | he | h
    · have hc := y.val.property i d.toNat h.le
      change bonding i d.toNat (y.val.val d.toNat) = y.val.val i at hc
      simpa [bonding, h.ne] using hc
    · subst i
      exact truncate_fix le_rfl (y.property d.toNat)
    · have hc := y.val.property d.toNat i h.le
      change bonding d.toNat i (y.val.val i) = y.val.val d.toNat at hc
      have hfix : truncate d.toNat (y.val.val i) = y.val.val i :=
        truncate_fix le_rfl (y.property i)
      rw [bonding, if_neg h.ne, hfix] at hc
      rw [← hc]
      exact truncate_fix h.le (y.property i)
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact map_add (truncate i) _ _

theorem degreeIso_mul (d e : ℤ) (x : ralphGradeLimit constantTower d)
    (y : ralphGradeLimit constantTower e) :
    degreeIso (d + e) (ralphGradeMul constantTower x y) =
      ralphGradeMul truncatedTower (degreeIso d x) (degreeIso e y) := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact map_mul (truncate i) _ _

/-- Truncated sums of distinct variables give one compatible section for each set. -/
noncomputable def sectionOf (A : Set ℕ) : ralphLimit truncatedTower := by
  classical
  refine ⟨fun j => ∑ k ∈ Finset.range j, if k ∈ A then X k else 0, ?_⟩
  intro i j hij
  change bonding i j (∑ k ∈ Finset.range j, if k ∈ A then X k else 0) =
    ∑ k ∈ Finset.range i, if k ∈ A then X k else 0
  by_cases he : i = j
  · subst j
    simp [bonding]
  rw [bonding, if_neg he, map_sum]
  have hsub : Finset.range i ⊆ Finset.range j := Finset.range_mono hij
  rw [← Finset.sum_subset hsub (f := fun k => truncate i (if k ∈ A then X k else 0))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hi := Finset.mem_range.1 hk
    by_cases ha : k ∈ A <;> simp [truncate, hi, ha]
  · intro k _ hk
    have hi : ¬k < i := fun h => hk (Finset.mem_range.2 h)
    by_cases ha : k ∈ A <;> simp [truncate, hi, ha]

noncomputable def coord (k : ℕ) : P →+* F :=
  eval₂Hom (RingHom.id F) (fun j => if j = k then 1 else 0)

theorem coord_section (k : ℕ) (A : Set ℕ) :
    coord k ((sectionOf A).val (k + 1)) = Set.indicator A (fun _ => 1) k := by
  classical
  change coord k (∑ j ∈ Finset.range (k + 1), if j ∈ A then X j else 0) = _
  rw [map_sum, Finset.sum_eq_single k]
  · by_cases ha : k ∈ A <;> simp [coord, Set.indicator, ha]
  · intro j _ hj
    by_cases ha : j ∈ A <;> simp [coord, ha, hj]
  · simp

theorem section_injective : Function.Injective sectionOf := by
  classical
  intro A B h
  ext k
  have he := congrArg (fun y : ralphLimit truncatedTower => coord k (y.val (k + 1))) h
  change coord k ((sectionOf A).val (k + 1)) = coord k ((sectionOf B).val (k + 1)) at he
  rw [coord_section, coord_section] at he
  by_cases hA : k ∈ A <;> by_cases hB : k ∈ B <;> simp_all [Set.indicator]

theorem constantCountable : Countable (ralphLimit constantTower) := by
  letI : Countable P :=
    (AddMonoidAlgebra.coeffAddEquiv : P ≃+ ((ℕ →₀ ℕ) →₀ F)).injective.countable
  let eval0 : ralphLimit constantTower → P := fun x => x.val 0
  apply Function.Injective.countable (f := eval0)
  intro x y h
  apply Subtype.ext
  funext i
  have hx := x.property 0 i (Nat.zero_le i)
  have hy := y.property 0 i (Nat.zero_le i)
  change x.val i = x.val 0 at hx
  change y.val i = y.val 0 at hy
  exact hx.trans (h.trans hy.symm)

end OMA.Ralph

open OMA.Ralph

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_108300.main) := by
  intro h
  have hdir : Directed (· ≤ ·) (id : ℕ → ℕ) :=
    fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨E⟩ := h ℕ ℕ hdir hdir constantTower truncatedTower ⟨degreeIso, degreeIso_mul⟩
  letI : Countable (ralphLimit constantTower) := constantCountable
  obtain ⟨encode, hinj⟩ := Countable.exists_injective_nat (ralphLimit constantTower)
  exact Function.cantor_injective (encode ∘ E.symm ∘ sectionOf)
    (hinj.comp (E.symm.injective.comp section_injective))
