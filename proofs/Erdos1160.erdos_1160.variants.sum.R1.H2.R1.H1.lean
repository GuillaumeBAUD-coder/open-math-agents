import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1

-- Step Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H1: hypothesis H1 of reduction Erdos1160.erdos_1160.variants.sum.R1.H2.R1
-- Credit: @chris01-dev
-- H1 := ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m^3) ≤ g (2^m)^27 * 2 ^ (13 * m^2)

/-!
# Higman's lower bound for the number of groups of order 2^m

For a lower triangular matrix with entries in `(ZMod 2)^s`, of size `s + t`, whose first `s`
diagonal entries are the standard basis, we form the biadditive map `β` on `(ZMod 2)^(s+t)` and
the group on `V × W` with product `(v, w) * (v', w') = (v + v', w + w' + β v v')`. It has order
`2^(2s+t)`. An isomorphism between two such groups preserves `0 × W` (the products of squares),
so it induces additive maps `A` on `V` and `B` on `W` with `β' (A v) (A v) = B (β v v)`. The
normalised diagonal makes `B` a function of `A`, and the matrix is a function of `v ↦ β v v`.
Hence each isomorphism class contains at most `2^((s+t)^2)` matrices, which gives
`2^(s * ((s+t)(s+t-1)/2 + t)) ≤ g(2^(2s+t)) * 2^((s+t)^2)` (Higman, 1960).
With `s = m / 3` this is `2^(2m^3/27 - 4m^2/9 + O(m))`.
-/

open Filter CategoryTheory Erdos1160

namespace OMA.Higman

/-- The twisted product of two abelian groups along a biadditive map:
the set `V × W` with `(v, w) * (v', w') = (v + v', w + w' + β v v')`. -/
structure Tw {V W : Type} [AddCommGroup V] [AddCommGroup W] (β : V →+ V →+ W) where
  fst : V
  snd : W

section general

variable {V W : Type} [AddCommGroup V] [AddCommGroup W]

lemma Tw.ext' {β : V →+ V →+ W} {a b : Tw β} (h1 : a.fst = b.fst) (h2 : a.snd = b.snd) :
    a = b := by
  cases a; cases b; simp_all

instance (β : V →+ V →+ W) : Mul (Tw β) :=
  ⟨fun a b => ⟨a.fst + b.fst, a.snd + b.snd + β a.fst b.fst⟩⟩

instance (β : V →+ V →+ W) : One (Tw β) := ⟨⟨0, 0⟩⟩

instance (β : V →+ V →+ W) : Inv (Tw β) :=
  ⟨fun a => ⟨-a.fst, -a.snd + β a.fst a.fst⟩⟩

@[simp] lemma mul_fst {β : V →+ V →+ W} (a b : Tw β) : (a * b).fst = a.fst + b.fst := rfl
@[simp] lemma mul_snd {β : V →+ V →+ W} (a b : Tw β) :
    (a * b).snd = a.snd + b.snd + β a.fst b.fst := rfl
@[simp] lemma one_fst {β : V →+ V →+ W} : (1 : Tw β).fst = 0 := rfl
@[simp] lemma one_snd {β : V →+ V →+ W} : (1 : Tw β).snd = 0 := rfl
@[simp] lemma inv_fst {β : V →+ V →+ W} (a : Tw β) : (a⁻¹).fst = -a.fst := rfl
@[simp] lemma inv_snd {β : V →+ V →+ W} (a : Tw β) :
    (a⁻¹).snd = -a.snd + β a.fst a.fst := rfl

instance (β : V →+ V →+ W) : Group (Tw β) where
  mul_assoc a b c := by
    apply Tw.ext'
    · simp [add_assoc]
    · simp
      abel
  one_mul a := by apply Tw.ext' <;> simp
  mul_one a := by apply Tw.ext' <;> simp
  inv_mul_cancel a := by apply Tw.ext' <;> simp

/-- The underlying set of the twisted product. -/
def Tw.equivProd (β : V →+ V →+ W) : Tw β ≃ V × W where
  toFun a := (a.fst, a.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv a := by cases a; rfl
  right_inv x := rfl

instance (β : V →+ V →+ W) [Finite V] [Finite W] : Finite (Tw β) :=
  Finite.of_equiv _ (Tw.equivProd β).symm

lemma card_tw (β : V →+ V →+ W) : Nat.card (Tw β) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (Tw.equivProd β), Nat.card_prod]

/-- If the values `β v v` generate `W`, a homomorphism of twisted products sends
`0 × W` into `0 × W`: these are the products of squares. -/
lemma fst_zero (hV : ∀ v : V, v + v = 0) (β β' : V →+ V →+ W) (φ : Tw β →* Tw β')
    (hspan : AddSubgroup.closure (Set.range fun v => β v v) = ⊤) (w : W) :
    (φ ⟨0, w⟩).fst = 0 := by
  let S : AddSubgroup W :=
    { carrier := {w | (φ ⟨0, w⟩).fst = 0}
      zero_mem' := by
        have h : (⟨0, 0⟩ : Tw β) = 1 := rfl
        simp [h]
      add_mem' := by
        intro a b ha hb
        have h : (⟨0, a + b⟩ : Tw β) = ⟨0, a⟩ * ⟨0, b⟩ := by apply Tw.ext' <;> simp
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [h, map_mul, mul_fst, ha, hb, add_zero]
      neg_mem' := by
        intro a ha
        have h : (⟨0, -a⟩ : Tw β) = (⟨0, a⟩ : Tw β)⁻¹ := by apply Tw.ext' <;> simp
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [h, map_inv, inv_fst, ha, neg_zero] }
  have hS : AddSubgroup.closure (Set.range fun v => β v v) ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    have h : (⟨0, β v v⟩ : Tw β) = ⟨v, 0⟩ * ⟨v, 0⟩ := by apply Tw.ext' <;> simp [hV]
    change (φ ⟨0, β v v⟩).fst = 0
    rw [h, map_mul, mul_fst, hV]
  have hw : w ∈ S := hS (by rw [hspan]; trivial)
  exact hw

/-- The map induced on the quotient `V` is additive. -/
lemma fst_add (hV : ∀ v : V, v + v = 0) (β β' : V →+ V →+ W) (φ : Tw β →* Tw β')
    (hspan : AddSubgroup.closure (Set.range fun v => β v v) = ⊤) (v v' : V) :
    (φ ⟨v + v', 0⟩).fst = (φ ⟨v, 0⟩).fst + (φ ⟨v', 0⟩).fst := by
  have h : (⟨v, 0⟩ : Tw β) * ⟨v', 0⟩ = ⟨v + v', 0⟩ * ⟨0, β v v'⟩ := by
    apply Tw.ext' <;> simp
  have h2 := congrArg (fun x => (φ x).fst) h
  simp only [map_mul, mul_fst, fst_zero hV β β' φ hspan, add_zero] at h2
  exact h2.symm

/-- The map induced on `W` is additive. -/
lemma snd_add (hV : ∀ v : V, v + v = 0) (β β' : V →+ V →+ W) (φ : Tw β →* Tw β')
    (hspan : AddSubgroup.closure (Set.range fun v => β v v) = ⊤) (w w' : W) :
    (φ ⟨0, w + w'⟩).snd = (φ ⟨0, w⟩).snd + (φ ⟨0, w'⟩).snd := by
  have h : (⟨0, w + w'⟩ : Tw β) = ⟨0, w⟩ * ⟨0, w'⟩ := by apply Tw.ext' <;> simp
  rw [h, map_mul, mul_snd, fst_zero hV β β' φ hspan]
  simp

/-- Squares are respected. -/
lemma snd_sq (hV : ∀ v : V, v + v = 0) (hW : ∀ w : W, w + w = 0) (β β' : V →+ V →+ W)
    (φ : Tw β →* Tw β') (v : V) :
    (φ ⟨0, β v v⟩).snd = β' (φ ⟨v, 0⟩).fst (φ ⟨v, 0⟩).fst := by
  have h : (⟨0, β v v⟩ : Tw β) = ⟨v, 0⟩ * ⟨v, 0⟩ := by apply Tw.ext' <;> simp [hV]
  rw [h, map_mul, mul_snd, hW, zero_add]

/-- Rigidity: two twisted products mapping isomorphically onto a third one, with the same
induced map on `V`, and whose diagonal maps agree on a set of values generating `W`, have the
same diagonal map. -/
lemma rigidity (hV : ∀ v : V, v + v = 0) (hW : ∀ w : W, w + w = 0) (β₀ β₁ β₂ : V →+ V →+ W)
    (φ₁ : Tw β₁ ≃* Tw β₀) (φ₂ : Tw β₂ ≃* Tw β₀)
    (hA : ∀ v, (φ₁ ⟨v, 0⟩).fst = (φ₂ ⟨v, 0⟩).fst)
    (hT : AddSubgroup.closure {w | ∃ v, β₁ v v = w ∧ β₂ v v = w} = ⊤) (v : V) :
    β₁ v v = β₂ v v := by
  have hs1 : AddSubgroup.closure (Set.range fun v => β₁ v v) = ⊤ := by
    apply top_unique
    rw [← hT]
    apply AddSubgroup.closure_mono
    rintro w ⟨v, h1, -⟩
    exact ⟨v, h1⟩
  have hs2 : AddSubgroup.closure (Set.range fun v => β₂ v v) = ⊤ := by
    apply top_unique
    rw [← hT]
    apply AddSubgroup.closure_mono
    rintro w ⟨v, -, h2⟩
    exact ⟨v, h2⟩
  let B₁ : W →+ W := AddMonoidHom.mk' (fun w => (φ₁ ⟨0, w⟩).snd)
    (snd_add hV β₁ β₀ φ₁.toMonoidHom hs1)
  let B₂ : W →+ W := AddMonoidHom.mk' (fun w => (φ₂ ⟨0, w⟩).snd)
    (snd_add hV β₂ β₀ φ₂.toMonoidHom hs2)
  have hB : B₁ = B₂ := by
    have hle : AddSubgroup.closure {w | ∃ v, β₁ v v = w ∧ β₂ v v = w} ≤ AddMonoidHom.eqLocus B₁ B₂ := by
      rw [AddSubgroup.closure_le]
      rintro w ⟨v, h1, h2⟩
      change (φ₁ ⟨0, w⟩).snd = (φ₂ ⟨0, w⟩).snd
      have e1 := snd_sq hV hW β₁ β₀ φ₁.toMonoidHom v
      have e2 := snd_sq hV hW β₂ β₀ φ₂.toMonoidHom v
      rw [h1] at e1
      rw [h2] at e2
      change (φ₁ ⟨0, w⟩).snd = _ at e1
      change (φ₂ ⟨0, w⟩).snd = _ at e2
      rw [e1, e2]
      change β₀ (φ₁ ⟨v, 0⟩).fst (φ₁ ⟨v, 0⟩).fst = β₀ (φ₂ ⟨v, 0⟩).fst (φ₂ ⟨v, 0⟩).fst
      rw [hA]
    rw [hT] at hle
    ext w
    exact hle (AddSubgroup.mem_top w)
  have e1 := snd_sq hV hW β₁ β₀ φ₁.toMonoidHom v
  have e2 := snd_sq hV hW β₂ β₀ φ₂.toMonoidHom v
  change (φ₁ ⟨0, β₁ v v⟩).snd = β₀ (φ₁ ⟨v, 0⟩).fst (φ₁ ⟨v, 0⟩).fst at e1
  change (φ₂ ⟨0, β₂ v v⟩).snd = β₀ (φ₂ ⟨v, 0⟩).fst (φ₂ ⟨v, 0⟩).fst at e2
  rw [hA] at e1
  have e3 : (φ₁ ⟨0, β₁ v v⟩).snd = (φ₂ ⟨0, β₂ v v⟩).snd := e1.trans e2.symm
  have e4 : (φ₂ ⟨0, β₁ v v⟩).snd = (φ₂ ⟨0, β₂ v v⟩).snd := by
    rw [← e3]
    exact (DFunLike.congr_fun hB (β₁ v v)).symm
  have f1 : (φ₂ ⟨0, β₁ v v⟩).fst = 0 := fst_zero hV β₂ β₀ φ₂.toMonoidHom hs2 _
  have f2 : (φ₂ ⟨0, β₂ v v⟩).fst = 0 := fst_zero hV β₂ β₀ φ₂.toMonoidHom hs2 _
  have e5 : φ₂ ⟨0, β₁ v v⟩ = φ₂ ⟨0, β₂ v v⟩ := Tw.ext' (f1.trans f2.symm) e4
  have e6 := φ₂.injective e5
  exact congrArg Tw.snd e6

end general

section concrete

/-- Vectors over the field with two elements. -/
abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

lemma vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

lemma zmod_two_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

lemma closure_eq_top_of_single {n : ℕ} (S : Set (Vec n))
    (h : ∀ k : Fin n, (Pi.single k 1 : Vec n) ∈ S) : AddSubgroup.closure S = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  apply AddSubgroup.sum_mem
  intro k _
  rcases zmod_two_cases (w k) with h0 | h1
  · rw [h0, Pi.single_zero]
    exact AddSubgroup.zero_mem _
  · rw [h1]
    exact AddSubgroup.subset_closure (h k)

/-- Parameters: the entries below the diagonal, and the last `t` diagonal entries. -/
abbrev Par (s t : ℕ) : Type := ((Σ i : Fin (s + t), Fin i) → Vec s) × (Fin t → Vec s)

/-- The matrix of a parameter: lower triangular, with the first `s` diagonal entries equal to
the standard basis of `Vec s`. -/
def mat {s t : ℕ} (p : Par s t) (i j : Fin (s + t)) : Vec s :=
  if h : (j : ℕ) < i then p.1 ⟨i, ⟨j, h⟩⟩
  else if i = j then Fin.append (fun k : Fin s => (Pi.single k 1 : Vec s)) p.2 i else 0

/-- The biadditive map with a given matrix. -/
def form {s t : ℕ} (p : Par s t) : Vec (s + t) →+ Vec (s + t) →+ Vec s :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun v' => ∑ i, ∑ j, (v i * v' j) • mat p i j)
    (by intro a b; simp [mul_add, add_smul, Finset.sum_add_distrib]))
    (by
      intro a b
      apply AddMonoidHom.ext
      intro v'
      simp [add_mul, add_smul, Finset.sum_add_distrib])

lemma form_apply {s t : ℕ} (p : Par s t) (v v' : Vec (s + t)) :
    form p v v' = ∑ i, ∑ j, (v i * v' j) • mat p i j := rfl

lemma form_single {s t : ℕ} (p : Par s t) (k l : Fin (s + t)) :
    form p (Pi.single k 1) (Pi.single l 1) = mat p k l := by
  rw [form_apply]
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Pi.single_apply, hi]
  · simp

lemma form_diag_left {s t : ℕ} (p : Par s t) (k : Fin s) :
    form p (Pi.single (Fin.castAdd t k) 1) (Pi.single (Fin.castAdd t k) 1) = Pi.single k 1 := by
  rw [form_single]
  simp [mat]

lemma common_span {s t : ℕ} (p p' : Par s t) :
    AddSubgroup.closure {w | ∃ v, form p v v = w ∧ form p' v v = w} = ⊤ := by
  apply closure_eq_top_of_single
  intro k
  exact ⟨Pi.single (Fin.castAdd t k) 1, form_diag_left p k, form_diag_left p' k⟩

lemma span {s t : ℕ} (p : Par s t) :
    AddSubgroup.closure (Set.range fun v => form p v v) = ⊤ := by
  apply closure_eq_top_of_single
  intro k
  exact ⟨Pi.single (Fin.castAdd t k) 1, form_diag_left p k⟩

/-- A parameter is determined by the diagonal of its form. -/
lemma par_inj {s t : ℕ} (p p' : Par s t) (h : ∀ v, form p v v = form p' v v) : p = p' := by
  have hdiag : ∀ k, mat p k k = mat p' k k := by
    intro k
    have := h (Pi.single k 1)
    rwa [form_single, form_single] at this
  have hup : ∀ (q : Par s t) (k l : Fin (s + t)), (l : ℕ) < k → mat q l k = 0 := by
    intro q k l hl
    have h1 : ¬ ((k : ℕ) < l) := by omega
    have h2 : l ≠ k := by
      intro e
      rw [e] at hl
      exact lt_irrefl _ hl
    simp [mat, h1, h2]
  have hoff : ∀ k l : Fin (s + t), (l : ℕ) < k → mat p k l = mat p' k l := by
    intro k l hl
    have := h (Pi.single k 1 + Pi.single l 1)
    simp only [map_add, AddMonoidHom.add_apply, form_single, hup p k l hl, hup p' k l hl,
      hdiag k, hdiag l] at this
    rw [add_zero] at this
    exact add_right_cancel (add_left_cancel this)
  apply Prod.ext
  · funext ⟨i, j⟩
    have hl : ((⟨j, lt_trans j.isLt i.isLt⟩ : Fin (s + t)) : ℕ) < i := j.isLt
    have := hoff i ⟨j, lt_trans j.isLt i.isLt⟩ hl
    simpa [mat] using this
  · funext k
    have := hdiag (Fin.natAdd s k)
    simpa [mat] using this

lemma card_par (s t : ℕ) :
    Nat.card (Par s t) = 2 ^ (s * (∑ i ∈ Finset.range (s + t), i + t)) := by
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_sigma, Fintype.card_fin, ZMod.card]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) (s + t)]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- Uniqueness step of the count. -/
lemma inj_aux {s t : ℕ} (p p' z z' : Par s t) (hz : z = z')
    (φ : Tw (form p) ≃* Tw (form z)) (φ' : Tw (form p') ≃* Tw (form z'))
    (hA : ∀ k, (φ ⟨Pi.single k 1, 0⟩).fst = (φ' ⟨Pi.single k 1, 0⟩).fst) : p = p' := by
  subst hz
  apply par_inj
  apply rigidity vec_add_self vec_add_self (form z) (form p) (form p') φ φ'
  · intro v
    let A : Vec (s + t) →+ Vec (s + t) := AddMonoidHom.mk' (fun v => (φ ⟨v, 0⟩).fst)
      (fst_add vec_add_self _ _ φ.toMonoidHom (span p))
    let A' : Vec (s + t) →+ Vec (s + t) := AddMonoidHom.mk' (fun v => (φ' ⟨v, 0⟩).fst)
      (fst_add vec_add_self _ _ φ'.toMonoidHom (span p'))
    have hAA : A = A' := by
      apply AddMonoidHom.functions_ext
      intro i x
      rcases zmod_two_cases x with h0 | h1
      · rw [h0, Pi.single_zero, map_zero, map_zero]
      · rw [h1]
        exact hA i
    exact DFunLike.congr_fun hAA v
  · exact common_span p p'

/-- The isomorphism class of the group attached to a parameter. -/
noncomputable def cls {s t : ℕ} (p : Par s t) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (FiniteGrp.of (Tw (form p)))

lemma finite_classes (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  have : Finite (Group (Fin n)) :=
    Finite.of_injective (fun h : Group (Fin n) => h.mul) (fun _ _ h => Group.ext h)
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let code (h : Group (Fin n)) := let _ := h; q (FiniteGrp.of (Fin n))
  apply (Set.finite_range code).subset
  rintro _ ⟨G, hG, rfl⟩
  have := Fintype.ofFinite G
  have hh : Fintype.card G = n := (Nat.card_eq_fintype_card (α := G)).symm.trans hG
  let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hh).symm
  let h := e.group
  let _ := h
  let K : FiniteGrp := FiniteGrp.of (Fin n)
  let eg : K ≃* G := e.mulEquiv
  exact ⟨h, Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := K.toGrp) (Y := G.toGrp) eg)⟩⟩

lemma mulEquiv_of_iso {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : FiniteGrp.of G ≅ FiniteGrp.of H) : Nonempty (G ≃* H) :=
  ⟨((inducedFunctor FiniteGrp.toGrp).mapIso e).groupIsoToMulEquiv⟩

/-- Higman's count: the parameters give at least `|Par| / |V|^(s+t)` isomorphism classes. -/
lemma count (s t : ℕ) :
    2 ^ (s * (∑ i ∈ Finset.range (s + t), i + t)) ≤
      g (2 ^ (s + t + s)) * 2 ^ ((s + t) * (s + t)) := by
  classical
  have hrange : Set.range (cls (s := s) (t := t)) ⊆
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = 2 ^ (s + t + s)} := by
    rintro _ ⟨p, rfl⟩
    refine ⟨FiniteGrp.of (Tw (form p)), ?_, rfl⟩
    change Nat.card (Tw (form p)) = _
    rw [card_tw]
    simp [pow_add]
  have hle : (Set.range (cls (s := s) (t := t))).ncard ≤ g (2 ^ (s + t + s)) :=
    Set.ncard_le_ncard hrange (finite_classes _)
  let rep : Quotient (isIsomorphicSetoid FiniteGrp.{0}) → Par s t := Function.invFun cls
  have hrep : ∀ p : Par s t, cls (rep (cls p)) = cls p :=
    fun p => Function.invFun_eq ⟨p, rfl⟩
  have key : ∀ p : Par s t, ∃ φ : Tw (form p) ≃* Tw (form (rep (cls p))), True := by
    intro p
    obtain ⟨e⟩ := Quotient.exact (hrep p)
    obtain ⟨f⟩ := mulEquiv_of_iso e
    exact ⟨f.symm, trivial⟩
  choose φ _ using key
  let Ψ : Par s t → Quotient (isIsomorphicSetoid FiniteGrp.{0}) × (Fin (s + t) → Vec (s + t)) :=
    fun p => (cls p, fun k => (φ p ⟨Pi.single k 1, 0⟩).fst)
  have hinj : Function.Injective Ψ := by
    intro p p' h
    have h1 : cls p = cls p' := congrArg Prod.fst h
    have h2 : ∀ k, (φ p ⟨Pi.single k 1, 0⟩).fst = (φ p' ⟨Pi.single k 1, 0⟩).fst :=
      fun k => congrFun (congrArg Prod.snd h) k
    exact inj_aux p p' _ _ (congrArg rep h1) (φ p) (φ p') h2
  have hsub : Set.range Ψ ⊆ Set.range (cls (s := s) (t := t)) ×ˢ Set.univ := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨p, rfl⟩, trivial⟩
  have hc : Nat.card (Par s t) ≤
      (Set.range (cls (s := s) (t := t))).ncard * Nat.card (Fin (s + t) → Vec (s + t)) := by
    calc Nat.card (Par s t) = (Set.range Ψ).ncard := by
          rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
      _ ≤ (Set.range (cls (s := s) (t := t)) ×ˢ Set.univ).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = _ := by rw [Set.ncard_prod, Set.ncard_univ]
  have hV : Nat.card (Fin (s + t) → Vec (s + t)) = 2 ^ ((s + t) * (s + t)) := by
    rw [Nat.card_eq_fintype_card]
    simp [pow_mul]
  rw [card_par, hV] at hc
  exact hc.trans (Nat.mul_le_mul_right _ hle)

lemma arith (s j T : ℕ) (hj : j < 3) (hs : 20 ≤ s)
    (hT : T * 2 = (2 * s + j) * (2 * s + j - 1)) :
    2 * (3 * s + j) ^ 3 + 27 * ((2 * s + j) * (2 * s + j)) ≤
      27 * (s * (T + (s + j))) + 13 * (3 * s + j) ^ 2 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hX : (20 + u) * T * 2 = (20 + u) * ((2 * (20 + u) + j) * (2 * (20 + u) + j - 1)) := by
    rw [mul_assoc, hT]
  have hu : 0 ≤ u * u := Nat.zero_le _
  interval_cases j
  · have e : 2 * (20 + u) + 0 - 1 = 39 + 2 * u := by omega
    rw [e] at hX
    nlinarith [hX, hu]
  · have e : 2 * (20 + u) + 1 - 1 = 40 + 2 * u := by omega
    rw [e] at hX
    nlinarith [hX, hu]
  · have e : 2 * (20 + u) + 2 - 1 = 41 + 2 * u := by omega
    rw [e] at hX
    nlinarith [hX, hu]

end concrete

end OMA.Higman

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1.H1
  filter_upwards [eventually_ge_atTop 60] with m hm
  obtain ⟨s, j, hj, rfl⟩ : ∃ s j, j < 3 ∧ m = 3 * s + j :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hs : 20 ≤ s := by omega
  have hc := OMA.Higman.count s (s + j)
  have e1 : s + (s + j) + s = 3 * s + j := by omega
  have e2 : s + (s + j) = 2 * s + j := by omega
  rw [e1, e2] at hc
  have ha := OMA.Higman.arith s j _ hj hs (Finset.sum_range_id_mul_two (2 * s + j))
  have h27 := Nat.pow_le_pow_left hc 27
  rw [mul_pow, ← pow_mul, ← pow_mul] at h27
  have h3 : 2 ^ (2 * (3 * s + j) ^ 3) * 2 ^ ((2 * s + j) * (2 * s + j) * 27) ≤
      g (2 ^ (3 * s + j)) ^ 27 * 2 ^ (13 * (3 * s + j) ^ 2) *
        2 ^ ((2 * s + j) * (2 * s + j) * 27) := by
    calc 2 ^ (2 * (3 * s + j) ^ 3) * 2 ^ ((2 * s + j) * (2 * s + j) * 27)
        = 2 ^ (2 * (3 * s + j) ^ 3 + 27 * ((2 * s + j) * (2 * s + j))) := by
          rw [pow_add, mul_comm 27]
      _ ≤ 2 ^ (27 * (s * (∑ i ∈ Finset.range (2 * s + j), i + (s + j))) +
            13 * (3 * s + j) ^ 2) := Nat.pow_le_pow_right (by norm_num) ha
      _ = 2 ^ (s * (∑ i ∈ Finset.range (2 * s + j), i + (s + j)) * 27) *
            2 ^ (13 * (3 * s + j) ^ 2) := by
          rw [pow_add, mul_comm 27]
      _ ≤ g (2 ^ (3 * s + j)) ^ 27 * 2 ^ ((2 * s + j) * (2 * s + j) * 27) *
            2 ^ (13 * (3 * s + j) ^ 2) := Nat.mul_le_mul_right _ h27
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)
