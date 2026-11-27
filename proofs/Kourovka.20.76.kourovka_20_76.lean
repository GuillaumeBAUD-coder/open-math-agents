import FormalConjectures.Kourovka.«20_76»

noncomputable section

open Finset Function

abbrev U76 := Fin 59 → ZMod 2

abbrev Z76 := Fin 13 → ZMod 2

abbrev Pair59 := {p : Fin 59 × Fin 59 // p.1 < p.2}

abbrev Coeff76 := Fin 13 → Pair59 → ZMod 2

def A76 (c : Coeff76) (u v : U76) : Z76 :=
  fun h => ∑ p : Pair59, c h p * u p.1.1 * v p.1.2

def weight76 (u v : U76) (p : Pair59) : ZMod 2 :=
  u p.1.1 * v p.1.2 + v p.1.1 * u p.1.2

def S76 (c : Coeff76) (u v : U76) : Z76 :=
  A76 c u v + A76 c v u

def IsCommonIsotropic76 (c : Coeff76) (X : Submodule (ZMod 2) U76) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, S76 c u v = 0

@[simp] lemma A76_add_left (c : Coeff76) (u1 u2 v : U76) :
    A76 c (u1 + u2) v = A76 c u1 v + A76 c u2 v := by
  ext h
  simp only [A76, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

@[simp] lemma A76_add_right (c : Coeff76) (u v1 v2 : U76) :
    A76 c u (v1 + v2) = A76 c u v1 + A76 c u v2 := by
  ext h
  simp only [A76, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

@[simp] lemma A76_zero_left (c : Coeff76) (v : U76) : A76 c 0 v = 0 := by
  ext h
  simp [A76]

@[simp] lemma A76_zero_right (c : Coeff76) (u : U76) : A76 c u 0 = 0 := by
  ext h
  simp [A76]

@[simp] lemma S76_apply (c : Coeff76) (u v : U76) (h : Fin 13) :
    S76 c u v h = ∑ p : Pair59, c h p * weight76 u v p := by
  simp only [S76, A76, Pi.add_apply, weight76]
  rw [← sum_add_distrib]
  refine sum_congr rfl ?_
  intro p _
  ring

lemma S76_add_left (c : Coeff76) (u1 u2 v : U76) :
    S76 c (u1 + u2) v = S76 c u1 v + S76 c u2 v := by
  ext i
  simp only [S76, Pi.add_apply, A76_add_left, A76_add_right]
  abel

lemma S76_add_right (c : Coeff76) (u v1 v2 : U76) :
    S76 c u (v1 + v2) = S76 c u v1 + S76 c u v2 := by
  ext i
  simp only [S76, Pi.add_apply, A76_add_left, A76_add_right]
  abel

lemma card_pair59 : Fintype.card Pair59 = 1711 := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      (univ.filter fun p : Fin 59 × Fin 59 => p.1 < p.2) =
        ((univ : Finset (Fin 59)) ×ˢ univ).filter fun p => p.1 < p.2 := by
    ext p
    simp [mem_product]
  rw [show #{p : Fin 59 × Fin 59 | p.1 < p.2} =
      #{p ∈ (univ : Finset (Fin 59)) ×ˢ univ | p.1 < p.2} from congrArg Finset.card hfilter]
  rw [Finset.card_product_filter_lt, Finset.card_univ, Fintype.card_fin]
  decide

lemma card_coeff76 : Nat.card Coeff76 = 2 ^ 22243 := by
  have hP : Nat.card Pair59 = 1711 := by rw [Nat.card_eq_fintype_card, card_pair59]
  rw [show Coeff76 = (Fin 13 → Pair59 → ZMod 2) from rfl, Nat.card_fun, Nat.card_fun, hP]
  have hZ : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hF : Nat.card (Fin 13) = 13 := by simp
  rw [hZ, hF, ← Nat.pow_mul]

def B9 : ℕ := ∏ i ∈ range 9, (2 ^ 9 - 2 ^ i)

lemma B9_gt : 2 ^ 79 < B9 := by
  decide

def coordProj {n : ℕ} (I : Finset (Fin n)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) where
  toFun u i := u i.1
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def kerCoord {n : ℕ} (X : Submodule (ZMod 2) (Fin n → ZMod 2)) (i : Fin n) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {u | u ∈ X ∧ u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨add_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩
  smul_mem' := by
    intro r u hu
    exact ⟨X.smul_mem r hu.1, by simp [hu.2]⟩

lemma exists_pivot {n : ℕ} (X : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    ∃ I : Finset (Fin n), I.card = Module.finrank (ZMod 2) X ∧
      Injective ((coordProj I).comp X.subtype) := by
  suffices ∀ k, Module.finrank (ZMod 2) X = k →
      ∃ I : Finset (Fin n), I.card = k ∧ Injective ((coordProj I).comp X.subtype) by
    exact this _ rfl
  intro k hk
  induction k generalizing n X with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    have hbot : X = ⊥ := (Submodule.finrank_eq_zero (R := ZMod 2)).mp hk
    haveI : Subsingleton X := by rw [hbot]; infer_instance
    intro x y _
    exact Subsingleton.elim x y
  | succ k ih =>
    have hne : X ≠ ⊥ := by
      intro h
      have : Module.finrank (ZMod 2) X = 0 := (Submodule.finrank_eq_zero (R := ZMod 2)).mpr h
      omega
    obtain ⟨u0, hu0, hu0ne⟩ := (Submodule.ne_bot_iff _).mp hne
    have huFun : (⟨u0, hu0⟩ : X) ≠ 0 := by
      intro h
      apply hu0ne
      simpa using congrArg Subtype.val h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (by
      intro h
      apply huFun
      exact Subtype.ext h)
    let φ : X →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i).comp X.subtype
    have hφ : φ ⟨u0, hu0⟩ ≠ 0 := by simpa [φ] using hi
    have hr : Module.finrank (ZMod 2) (LinearMap.range φ) = 1 := by
      have hneR : LinearMap.range φ ≠ ⊥ := by
        intro hbot
        apply hφ
        have hmem : φ ⟨u0, hu0⟩ ∈ LinearMap.range φ := LinearMap.mem_range_self _ _
        rw [hbot] at hmem
        simpa using hmem
      have hle : Module.finrank (ZMod 2) (LinearMap.range φ) ≤ 1 := by
        simpa [Module.finrank_self] using
          LinearMap.finrank_le_finrank_of_injective
            (f := (LinearMap.range φ).subtype) (Subtype.val_injective)
      have hge : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range φ) :=
        (Submodule.one_le_finrank_iff).mpr hneR
      omega
    have hker : Module.finrank (ZMod 2) (kerCoord X i) = k := by
      let e : LinearMap.ker φ ≃ₗ[ZMod 2] kerCoord X i :=
        { toFun := fun w => ⟨w.1.1, ⟨w.1.2, by
            have h0 : φ w.1 = 0 := w.2
            simp only [φ] at h0
            exact h0⟩⟩
          invFun := fun u => ⟨⟨u.1, u.2.1⟩, by simp [φ, u.2.2]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hsum := LinearMap.finrank_range_add_finrank_ker φ
      rw [hr, hk] at hsum
      have hkerφ : Module.finrank (ZMod 2) (LinearMap.ker φ) = k := by omega
      rw [← hkerφ]
      exact (LinearEquiv.finrank_eq e).symm
    obtain ⟨J, hJ, hinjJ⟩ := ih (kerCoord X i) hker
    have hiJ : i ∉ J := by
      intro hiJ
      let πe : kerCoord X i →ₗ[ZMod 2] (J.erase i → ZMod 2) :=
        { toFun := fun w t => w.1 t.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hinjE : Injective πe := by
        intro w1 w2 h
        apply Subtype.ext
        have hEq : ((coordProj J).comp (kerCoord X i).subtype) w1 =
            ((coordProj J).comp (kerCoord X i).subtype) w2 := by
          ext ⟨j, hj⟩
          by_cases hji : j = i
          · have hw1 : (w1 : Fin n → ZMod 2) j = 0 := by
              rw [hji]
              exact w1.2.2
            have hw2 : (w2 : Fin n → ZMod 2) j = 0 := by
              rw [hji]
              exact w2.2.2
            simp [coordProj, hw1, hw2]
          · have hj' : j ∈ J.erase i := mem_erase.mpr ⟨hji, hj⟩
            have hfun := congr_fun h ⟨j, hj'⟩
            have hcoord : (w1 : Fin n → ZMod 2) j = (w2 : Fin n → ZMod 2) j := by
              simpa [πe] using hfun
            simp [coordProj, hcoord]
        exact congrArg Subtype.val (hinjJ hEq)
      have hle := LinearMap.finrank_le_finrank_of_injective hinjE
      have hcod : Module.finrank (ZMod 2) (J.erase i → ZMod 2) = (J.erase i).card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      rw [hcod, card_erase_of_mem hiJ, hJ] at hle
      have hkpos : 0 < k := by
        have hJpos : 0 < #J := card_pos.mpr ⟨i, hiJ⟩
        simpa [hJ] using hJpos
      have : k ≤ k - 1 := by simpa [hker] using hle
      omega
    refine ⟨insert i J, ?_, ?_⟩
    · rw [card_insert_of_notMem hiJ, hJ]
    · intro x y hxy
      apply Subtype.ext
      have hdi : (x : Fin n → ZMod 2) i = (y : Fin n → ZMod 2) i := by
        have := congr_fun hxy ⟨i, mem_insert_self i J⟩
        simpa [coordProj] using this
      have hxker : (x : Fin n → ZMod 2) - y ∈ kerCoord X i := by
        refine ⟨sub_mem x.2 y.2, ?_⟩
        simp [hdi]
      let d : kerCoord X i := ⟨(x : Fin n → ZMod 2) - y, hxker⟩
      have hdJ : ((coordProj J).comp (kerCoord X i).subtype) d = 0 := by
        ext ⟨j, hj⟩
        have := congr_fun hxy ⟨j, mem_insert_of_mem hj⟩
        simpa [coordProj, d, sub_eq_zero] using this
      have hd0 : d = 0 := by
        apply hinjJ
        simpa using hdJ
      have : (x : Fin n → ZMod 2) - y = 0 := congrArg Subtype.val hd0
      simpa [sub_eq_zero] using this

lemma finite_submodule76 (X : Submodule (ZMod 2) U76) : Finite X :=
  Finite.of_injective (Subtype.val : X → U76) Subtype.val_injective

lemma card_mod76 (X : Submodule (ZMod 2) U76) :
    Nat.card X = 2 ^ Module.finrank (ZMod 2) X := by
  haveI := finite_submodule76 X
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := X)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma natCard_compl {α : Type*} [Finite α] (s : Set α) :
    Nat.card (↥sᶜ) = Nat.card α - Nat.card (↥s) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Finite (↥s) := Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Finite (↥sᶜ) := Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Fintype (↥s) := Fintype.ofFinite (↥s)
  haveI : Fintype (↥sᶜ) := Fintype.ofFinite (↥sᶜ)
  have e : ↥(sᶜ) ≃ {x : α // x ∉ s} :=
    { toFun := fun x => ⟨x.1, (Set.mem_compl_iff s x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (Set.mem_compl_iff s x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_compl (p := fun x => x ∈ s)

lemma card_span_li {k : ℕ} {X : Submodule (ZMod 2) U76} (b : Fin k → X)
    (hb : LinearIndependent (ZMod 2) b) :
    Nat.card (↥(Submodule.span (ZMod 2) (Set.range b))) = 2 ^ k := by
  have hfin : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range b)) = k := by
    rw [finrank_span_eq_card hb, Fintype.card_fin]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hfin]
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma card_li (k : ℕ) (hk : k ≤ 9) (X : Submodule (ZMod 2) U76)
    (hX : Module.finrank (ZMod 2) X = 9) :
    Nat.card {b : Fin k → X // LinearIndependent (ZMod 2) b} =
      ∏ i ∈ range k, (2 ^ 9 - 2 ^ i) := by
  classical
  haveI := finite_submodule76 X
  haveI : Fintype X := Fintype.ofFinite X
  induction k with
  | zero =>
    rw [prod_range_zero]
    have hli : ∀ b : Fin 0 → X, LinearIndependent (ZMod 2) b := fun b =>
      linearIndependent_empty_type (R := ZMod 2) (v := b)
    letI : Unique {b : Fin 0 → X // LinearIndependent (ZMod 2) b} :=
      { default := ⟨fun i => i.elim0, hli _⟩
        uniq := by
          intro a
          apply Subtype.ext
          ext i
          exact i.elim0 }
    exact Nat.card_unique
  | succ k ih =>
    have hk' : k ≤ 9 := by omega
    have hklt : k < 9 := by omega
    rw [Nat.card_congr (equiv_linearIndependent (K := ZMod 2) (V := X) k)]
    haveI : Finite {s : Fin k → X // LinearIndependent (ZMod 2) s} :=
      Finite.of_injective Subtype.val Subtype.val_injective
    haveI : Fintype {s : Fin k → X // LinearIndependent (ZMod 2) s} := Fintype.ofFinite _
    haveI : ∀ s : {s : Fin k → X // LinearIndependent (ZMod 2) s},
        Finite (↥((Submodule.span (ZMod 2) (Set.range (s.1 : Fin k → X)))ᶜ : Set X)) :=
      fun _ => Finite.of_injective Subtype.val Subtype.val_injective
    rw [Nat.card_sigma]
    have hXcard : Nat.card X = 2 ^ 9 := by simpa [hX] using card_mod76 X
    have hfiber : ∀ s : {s : Fin k → X // LinearIndependent (ZMod 2) s},
        Nat.card (↥((Submodule.span (ZMod 2) (Set.range (s.1 : Fin k → X)))ᶜ : Set X)) =
          2 ^ 9 - 2 ^ k := by
      intro s
      let span := Submodule.span (ZMod 2) (Set.range (s.1 : Fin k → X))
      have e : (↥span) ≃ ↥(span : Set X) :=
        { toFun := fun x => ⟨x.1, (SetLike.mem_coe).mpr x.2⟩
          invFun := fun x => ⟨x.1, (SetLike.mem_coe).mp x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [natCard_compl, hXcard, ← Nat.card_congr e, card_span_li s.1 s.2]
    simp_rw [hfiber, sum_const, card_univ]
    rw [← Nat.card_eq_fintype_card, ih hk', prod_range_succ]
    ring

abbrev Gr9 := {X : Submodule (ZMod 2) U76 // Module.finrank (ZMod 2) X = 9}

lemma finite_all_submodules : Finite (Submodule (ZMod 2) U76) := by
  classical
  refine Finite.of_injective (fun X : Submodule (ZMod 2) U76 => (X : Set U76).toFinset) ?_
  intro X Y h
  apply Submodule.ext
  intro x
  simpa [Set.mem_toFinset] using congrArg (fun t : Finset U76 => x ∈ t) h

lemma card_gr9_mul : Nat.card Gr9 * B9 ≤ 2 ^ 531 := by
  classical
  haveI := finite_all_submodules
  haveI : Finite Gr9 := Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Fintype Gr9 := Fintype.ofFinite _
  let Src := Σ X : Gr9, {b : Fin 9 → X.1 // LinearIndependent (ZMod 2) b}
  haveI : ∀ X : Gr9, Finite {b : Fin 9 → X.1 // LinearIndependent (ZMod 2) b} := fun X => by
    haveI := finite_submodule76 X.1
    haveI : Fintype X.1 := Fintype.ofFinite _
    exact Finite.of_injective Subtype.val Subtype.val_injective
  have hsrc : Nat.card Src = Nat.card Gr9 * B9 := by
    rw [Nat.card_sigma]
    have hfiber : ∀ X : Gr9,
        Nat.card {b : Fin 9 → X.1 // LinearIndependent (ZMod 2) b} = B9 := fun X => by
      simpa [B9] using card_li 9 (le_rfl) X.1 X.2
    simp_rw [hfiber, sum_const, card_univ, ← Nat.card_eq_fintype_card]
    ring
  let toU : Src → Fin 9 → U76 := fun p i => (p.2.1 i : U76)
  have hinj : Injective toU := by
    intro p q h
    have hspan (r : Src) :
        Submodule.span (ZMod 2) (Set.range (fun i => (r.2.1 i : U76))) = r.1.1 := by
      have hli : LinearIndependent (ZMod 2) (fun i => (r.2.1 i : U76)) :=
        r.2.2.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have hle : Submodule.span (ZMod 2) (Set.range (fun i => (r.2.1 i : U76))) ≤ r.1.1 := by
        rw [Submodule.span_le]
        intro u hu
        rcases hu with ⟨i, rfl⟩
        exact (r.2.1 i).2
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [finrank_span_eq_card hli, r.1.2, Fintype.card_fin]
    have hXY : p.1.1 = q.1.1 := by
      rw [← hspan p, ← hspan q]
      simp [toU, h]
    cases p with
    | mk Xp bp =>
      cases q with
      | mk Xq bq =>
        have hX : Xp = Xq := Subtype.ext hXY
        subst hX
        have hb : bp = bq := by
          apply Subtype.ext
          funext i
          apply Subtype.ext
          exact congr_fun h i
        rw [hb]
  have hfun : Nat.card (Fin 9 → U76) = 2 ^ 531 := by
    rw [Nat.card_fun]
    have hU : Nat.card U76 = 2 ^ 59 := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
    have h9 : Nat.card (Fin 9) = 9 := by simp
    rw [hU, h9, ← Nat.pow_mul]
  haveI : Finite Src := inferInstance
  have hle := Nat.card_le_card_of_injective toU hinj
  rw [← hsrc]
  calc Nat.card Src ≤ Nat.card (Fin 9 → U76) := hle
    _ = 2 ^ 531 := hfun

lemma card_pivotPairs (I : Finset (Fin 59)) :
    #{p : Pair59 | p.1.1 ∈ I ∧ p.1.2 ∈ I} = I.card.choose 2 := by
  classical
  let s := {q ∈ I ×ˢ I | q.1 < q.2}
  have hs : s.card = I.card.choose 2 := Finset.card_product_filter_lt (s := I)
  have e : {p : Pair59 // p.1.1 ∈ I ∧ p.1.2 ∈ I} ≃ {q // q ∈ s} :=
    { toFun := fun p => ⟨p.1.1, by
        have hp := p.2
        simp only [s, mem_filter, mem_product]
        exact ⟨⟨hp.1, hp.2⟩, p.1.2⟩⟩
      invFun := fun q => ⟨⟨q.1, by
        have hq := q.2
        simp only [s, mem_filter, mem_product] at hq
        exact hq.2⟩, by
        have hq := q.2
        simp only [s, mem_filter, mem_product] at hq
        exact ⟨hq.1.1, hq.1.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_coe, hs]

lemma card_freeCoord (I : Finset (Fin 59)) (hI : I.card = 9) :
    Nat.card {p : Fin 13 × Pair59 // ¬ (p.2.1.1 ∈ I ∧ p.2.1.2 ∈ I)} = 21775 := by
  classical
  have htot : Fintype.card (Fin 13 × Pair59) = 22243 := by
    rw [Fintype.card_prod, Fintype.card_fin, card_pair59]
  have hpiv : Fintype.card {p : Fin 13 × Pair59 // p.2.1.1 ∈ I ∧ p.2.1.2 ∈ I} = 468 := by
    let e : {p : Fin 13 × Pair59 // p.2.1.1 ∈ I ∧ p.2.1.2 ∈ I} ≃
        Fin 13 × {q : Pair59 // q.1.1 ∈ I ∧ q.1.2 ∈ I} :=
      { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]
    have : Fintype.card {q : Pair59 // q.1.1 ∈ I ∧ q.1.2 ∈ I} = 36 := by
      rw [Fintype.card_subtype, card_pivotPairs, hI]
      decide
    rw [this]
  have hcompl := Fintype.card_subtype_compl
    (p := fun p : Fin 13 × Pair59 => p.2.1.1 ∈ I ∧ p.2.1.2 ∈ I)
  rw [Nat.card_eq_fintype_card, hcompl, htot, hpiv]

lemma basisVec_spec (X : Submodule (ZMod 2) U76) (I : Finset (Fin 59))
    (hI : I.card = Module.finrank (ZMod 2) X)
    (hinj : Injective ((coordProj I).comp X.subtype)) (i : I) :
    ∃ x : X, ∀ j : I, (x : U76) j.1 = if j = i then 1 else 0 := by
  let π : X →ₗ[ZMod 2] (I → ZMod 2) := (coordProj I).comp X.subtype
  have hker : LinearMap.ker π = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsum := LinearMap.finrank_range_add_finrank_ker π
  rw [hker, finrank_bot, add_zero] at hsum
  have hcod : Module.finrank (ZMod 2) (I → ZMod 2) = I.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hrange : LinearMap.range π = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq (le_top : LinearMap.range π ≤ ⊤)
    rw [finrank_top, hcod, hI, ← hsum]
  have hsurj : Surjective π := LinearMap.range_eq_top.mp hrange
  obtain ⟨x, hx⟩ := hsurj (Pi.single i 1)
  refine ⟨x, ?_⟩
  intro j
  have := congr_fun hx j
  simpa [π, coordProj, Pi.single_apply] using this

lemma iso_determines (c1 c2 : Coeff76) (X : Submodule (ZMod 2) U76)
    (hX : Module.finrank (ZMod 2) X = 9)
    (h1 : IsCommonIsotropic76 c1 X) (h2 : IsCommonIsotropic76 c2 X)
    (I : Finset (Fin 59)) (hI : I.card = 9)
    (hinj : Injective ((coordProj I).comp X.subtype))
    (hagree : ∀ h : Fin 13, ∀ p : Pair59, ¬ (p.1.1 ∈ I ∧ p.1.2 ∈ I) → c1 h p = c2 h p) :
    c1 = c2 := by
  classical
  ext h p
  by_cases hp : p.1.1 ∈ I ∧ p.1.2 ∈ I
  · obtain ⟨xI, hxI⟩ := basisVec_spec X I (hI.trans hX.symm) hinj ⟨p.1.1, hp.1⟩
    obtain ⟨yI, hyI⟩ := basisVec_spec X I (hI.trans hX.symm) hinj ⟨p.1.2, hp.2⟩
    have hij : (⟨p.1.1, hp.1⟩ : I) ≠ ⟨p.1.2, hp.2⟩ := by
      intro hne
      have heq : p.1.1 = p.1.2 := congrArg Subtype.val hne
      exact lt_irrefl _ (heq ▸ p.2)
    have hS1 : S76 c1 (xI : U76) (yI : U76) = 0 := h1 _ xI.2 _ yI.2
    have hS2' : S76 c2 (xI : U76) (yI : U76) = 0 := h2 _ xI.2 _ yI.2
    have hw0 {q : Pair59} (hqI : q.1.1 ∈ I ∧ q.1.2 ∈ I) (hne : q ≠ p) :
        weight76 (xI : U76) (yI : U76) q = 0 := by
      have hprod1 : (xI : U76) q.1.1 * (yI : U76) q.1.2 = 0 := by
        by_cases hA : (⟨q.1.1, hqI.1⟩ : I) = ⟨p.1.1, hp.1⟩
        · by_cases hB : (⟨q.1.2, hqI.2⟩ : I) = ⟨p.1.2, hp.2⟩
          · exact False.elim <| hne <| Subtype.ext <|
              Prod.ext (congrArg Subtype.val hA) (congrArg Subtype.val hB)
          · have hy0 : (yI : U76) q.1.2 = 0 := by
              have hy := hyI ⟨q.1.2, hqI.2⟩
              rw [if_neg hB] at hy
              exact hy
            rw [hy0, mul_zero]
        · have hx0 : (xI : U76) q.1.1 = 0 := by
            have hx := hxI ⟨q.1.1, hqI.1⟩
            rw [if_neg hA] at hx
            exact hx
          rw [hx0, zero_mul]
      have hprod2 : (yI : U76) q.1.1 * (xI : U76) q.1.2 = 0 := by
        by_cases hC : (⟨q.1.1, hqI.1⟩ : I) = ⟨p.1.2, hp.2⟩
        · by_cases hD : (⟨q.1.2, hqI.2⟩ : I) = ⟨p.1.1, hp.1⟩
          · exact False.elim <| by
              have hlt : q.1.1 < q.1.2 := q.2
              have h1 : q.1.1 = p.1.2 := congrArg Subtype.val hC
              have h2v : q.1.2 = p.1.1 := congrArg Subtype.val hD
              have : p.1.2 < p.1.1 := by
                rw [← h1, ← h2v]
                exact hlt
              exact not_lt_of_gt p.2 this
          · have hx0 : (xI : U76) q.1.2 = 0 := by
              have hx2 := hxI ⟨q.1.2, hqI.2⟩
              rw [if_neg hD] at hx2
              exact hx2
            rw [hx0, mul_zero]
        · have hy0 : (yI : U76) q.1.1 = 0 := by
            have hy2 := hyI ⟨q.1.1, hqI.1⟩
            rw [if_neg hC] at hy2
            exact hy2
          rw [hy0, zero_mul]
      rw [weight76, hprod1, hprod2, zero_add]
    have hwP : weight76 (xI : U76) (yI : U76) p = 1 := by
      have hx : (xI : U76) p.1.1 = 1 := by
        have hx := hxI ⟨p.1.1, hp.1⟩
        rw [if_pos rfl] at hx
        exact hx
      have hy : (yI : U76) p.1.2 = 1 := by
        have hy := hyI ⟨p.1.2, hp.2⟩
        rw [if_pos rfl] at hy
        exact hy
      have hx2 : (xI : U76) p.1.2 = 0 := by
        have hx2 := hxI ⟨p.1.2, hp.2⟩
        have hne : (⟨p.1.2, hp.2⟩ : I) ≠ ⟨p.1.1, hp.1⟩ := fun h => hij h.symm
        rw [if_neg hne] at hx2
        exact hx2
      have hy2 : (yI : U76) p.1.1 = 0 := by
        have hy2 := hyI ⟨p.1.1, hp.1⟩
        rw [if_neg hij] at hy2
        exact hy2
      rw [weight76, hx, hy, hx2, hy2, mul_one, mul_zero, add_zero]
    let freeSum (c : Coeff76) : ZMod 2 :=
      ∑ q : Pair59, if ¬ (q.1.1 ∈ I ∧ q.1.2 ∈ I) then
        c h q * weight76 (xI : U76) (yI : U76) q else 0
    have hw (c : Coeff76) : S76 c (xI : U76) (yI : U76) h = c h p + freeSum c := by
      rw [S76_apply]
      have hfun (q : Pair59) :
          c h q * weight76 (xI : U76) (yI : U76) q =
            (if q.1.1 ∈ I ∧ q.1.2 ∈ I then
              c h q * weight76 (xI : U76) (yI : U76) q else 0) +
            (if ¬ (q.1.1 ∈ I ∧ q.1.2 ∈ I) then
              c h q * weight76 (xI : U76) (yI : U76) q else 0) := by
        by_cases hP : q.1.1 ∈ I ∧ q.1.2 ∈ I
        · rw [if_pos hP, if_neg (not_not_intro hP), add_zero]
        · rw [if_neg hP, if_pos hP, zero_add]
      have hsplit :
          (∑ q : Pair59, c h q * weight76 (xI : U76) (yI : U76) q) =
            ∑ q : Pair59,
              ((if q.1.1 ∈ I ∧ q.1.2 ∈ I then
                  c h q * weight76 (xI : U76) (yI : U76) q else 0) +
                (if ¬ (q.1.1 ∈ I ∧ q.1.2 ∈ I) then
                  c h q * weight76 (xI : U76) (yI : U76) q else 0)) :=
        Finset.sum_congr rfl (fun q _ => hfun q)
      rw [hsplit, Finset.sum_add_distrib]
      have hpivot :
          (∑ q : Pair59, if q.1.1 ∈ I ∧ q.1.2 ∈ I then
            c h q * weight76 (xI : U76) (yI : U76) q else 0) = c h p := by
        refine Eq.trans (Finset.sum_eq_single p ?_ ?_) ?_
        · intro q _ hne
          by_cases hP : q.1.1 ∈ I ∧ q.1.2 ∈ I
          · rw [if_pos hP, hw0 hP hne, mul_zero]
          · rw [if_neg hP]
        · intro hp0
          exact absurd (mem_univ p) hp0
        · rw [if_pos hp, hwP, mul_one]
      rw [hpivot]
    have h1z : S76 c1 (xI : U76) (yI : U76) h = 0 := by
      simpa only [Pi.zero_apply] using congr_fun hS1 h
    have h2z : S76 c2 (xI : U76) (yI : U76) h = 0 := by
      simpa only [Pi.zero_apply] using congr_fun hS2' h
    rw [hw c1] at h1z
    rw [hw c2] at h2z
    have hrest : freeSum c1 = freeSum c2 := by
      refine Finset.sum_congr rfl ?_
      intro q _
      by_cases hP : q.1.1 ∈ I ∧ q.1.2 ∈ I
      · rw [if_neg (not_not_intro hP), if_neg (not_not_intro hP)]
      · rw [if_pos hP, if_pos hP, hagree h q hP]
    have hc1 : c1 h p = freeSum c1 := (CharTwo.add_eq_zero).mp h1z
    have hc2 : c2 h p = freeSum c2 := (CharTwo.add_eq_zero).mp h2z
    rw [hc1, hc2, hrest]
  · exact hagree h p hp

lemma card_iso_le (X : Submodule (ZMod 2) U76) (hX : Module.finrank (ZMod 2) X = 9) :
    Nat.card {c : Coeff76 // IsCommonIsotropic76 c X} ≤ 2 ^ 21775 := by
  classical
  obtain ⟨I, hI, hinj⟩ := exists_pivot X
  have hI9 : I.card = 9 := by rw [hI, hX]
  let Free := {p : Fin 13 × Pair59 // ¬ (p.2.1.1 ∈ I ∧ p.2.1.2 ∈ I)}
  let restr : {c : Coeff76 // IsCommonIsotropic76 c X} → Free → ZMod 2 :=
    fun c p => c.1 p.1.1 p.1.2
  have hinjr : Injective restr := by
    intro c1 c2 h
    apply Subtype.ext
    apply iso_determines c1.1 c2.1 X hX c1.2 c2.2 I hI9 hinj
    intro hcoord p hp
    have := congr_fun h ⟨(hcoord, p), hp⟩
    simpa [restr] using this
  have hfree : Nat.card (Free → ZMod 2) = 2 ^ 21775 := by
    rw [Nat.card_fun, card_freeCoord I hI9]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  haveI : Finite {c : Coeff76 // IsCommonIsotropic76 c X} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Finite (Free → ZMod 2) := by
    haveI : Finite Free := Finite.of_injective Subtype.val Subtype.val_injective
    haveI : Fintype Free := Fintype.ofFinite _
    infer_instance
  haveI : Fintype {c : Coeff76 // IsCommonIsotropic76 c X} := Fintype.ofFinite _
  haveI : Fintype (Free → ZMod 2) := Fintype.ofFinite _
  have hle := Fintype.card_le_of_injective restr hinjr
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hle
  rw [hfree] at hle
  exact hle

lemma finite_gr9 : Finite Gr9 := by
  haveI := finite_all_submodules
  exact Finite.of_injective Subtype.val Subtype.val_injective

lemma card_bad_mul : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} * B9 <
    2 ^ 22243 * B9 := by
  classical
  haveI := finite_gr9
  haveI : Fintype Gr9 := Fintype.ofFinite _
  let BadX := Σ X : Gr9, {c : Coeff76 // IsCommonIsotropic76 c X.1}
  haveI : ∀ X : Gr9, Finite {c : Coeff76 // IsCommonIsotropic76 c X.1} := fun _ =>
    Finite.of_injective Subtype.val Subtype.val_injective
  have hsig : Nat.card BadX ≤ Nat.card Gr9 * 2 ^ 21775 := by
    rw [Nat.card_sigma]
    have hle : ∀ X : Gr9, Nat.card {c : Coeff76 // IsCommonIsotropic76 c X.1} ≤ 2 ^ 21775 :=
      fun X => card_iso_le X.1 X.2
    have : ∑ X : Gr9, Nat.card {c : Coeff76 // IsCommonIsotropic76 c X.1} ≤
        ∑ _ : Gr9, 2 ^ 21775 := Finset.sum_le_sum fun X _ => hle X
    simpa [sum_const, card_univ, ← Nat.card_eq_fintype_card] using this
  let toBad : BadX → {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} :=
    fun p => ⟨p.2.1, p.1, p.2.2⟩
  have hsurj : Surjective toBad := by
    intro c
    obtain ⟨X, hX⟩ := c.2
    exact ⟨⟨X, ⟨c.1, hX⟩⟩, rfl⟩
  haveI : Finite BadX := inferInstance
  haveI : Finite {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Fintype BadX := Fintype.ofFinite _
  haveI : Fintype {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} := Fintype.ofFinite _
  have hcard : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} ≤ Nat.card BadX := by
    have hle := Fintype.card_le_of_surjective toBad hsurj
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hle
    exact hle
  have hmul : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} * B9 ≤
      2 ^ 531 * 2 ^ 21775 := by
    have h1 : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} * B9 ≤
        Nat.card BadX * B9 := Nat.mul_le_mul_right _ hcard
    have h2 : Nat.card BadX * B9 ≤ (Nat.card Gr9 * 2 ^ 21775) * B9 :=
      Nat.mul_le_mul_right _ hsig
    have h3 : (Nat.card Gr9 * 2 ^ 21775) * B9 = (Nat.card Gr9 * B9) * 2 ^ 21775 := by ring
    have h4 : (Nat.card Gr9 * B9) * 2 ^ 21775 ≤ 2 ^ 531 * 2 ^ 21775 :=
      Nat.mul_le_mul_right _ card_gr9_mul
    calc _ ≤ Nat.card BadX * B9 := h1
      _ ≤ (Nat.card Gr9 * 2 ^ 21775) * B9 := h2
      _ = (Nat.card Gr9 * B9) * 2 ^ 21775 := h3
      _ ≤ 2 ^ 531 * 2 ^ 21775 := h4
  have hpow : 2 ^ 531 * 2 ^ 21775 = 2 ^ 22306 := by rw [← Nat.pow_add]
  have hlt1 : 2 ^ 22306 < 2 ^ 22243 * 2 ^ 79 := by
    rw [← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by decide : 22306 < 22243 + 79)
  have hlt2 : 2 ^ 22243 * 2 ^ 79 < 2 ^ 22243 * B9 :=
    Nat.mul_lt_mul_of_pos_left B9_gt
      (Nat.pos_iff_ne_zero.mpr (pow_ne_zero 22243 (by decide : (2 : ℕ) ≠ 0)))
  have : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} * B9 <
      2 ^ 22243 * B9 := by
    calc _ ≤ 2 ^ 531 * 2 ^ 21775 := hmul
      _ = 2 ^ 22306 := hpow
      _ < 2 ^ 22243 * 2 ^ 79 := hlt1
      _ < 2 ^ 22243 * B9 := hlt2
  exact this

lemma exists_good_coeff :
    ∃ c : Coeff76, ∀ X : Submodule (ZMod 2) U76, Module.finrank (ZMod 2) X = 9 →
      ¬ IsCommonIsotropic76 c X := by
  have hlt := card_bad_mul
  have hpos : 0 < B9 := lt_trans (by decide : (0 : ℕ) < 2 ^ 79) B9_gt
  have hbad : Nat.card {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} < 2 ^ 22243 :=
    Nat.lt_of_mul_lt_mul_right hlt
  rw [← card_coeff76] at hbad
  by_contra h
  push Not at h
  let e : Coeff76 ≃ {c : Coeff76 // ∃ X : Gr9, IsCommonIsotropic76 c X.1} :=
    { toFun := fun c => ⟨c, by
        obtain ⟨X, hX, hiso⟩ := h c
        exact ⟨⟨X, hX⟩, hiso⟩⟩
      invFun := fun c => c.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have := Nat.card_congr e
  omega

structure T76 (c : Coeff76) where
  u : U76
  v : U76
  z : Z76
  w : Z76

namespace T76

variable {c : Coeff76}

lemma ext {x y : T76 c} (hu : x.u = y.u) (hv : x.v = y.v) (hz : x.z = y.z) (hw : x.w = y.w) :
    x = y := by
  obtain ⟨xu, xv, xz, xw⟩ := x
  obtain ⟨yu, yv, yz, yw⟩ := y
  simp only at hu hv hz hw
  subst hu hv hz hw
  rfl

@[simp] lemma eta (x : T76 c) : T76.mk x.u x.v x.z x.w = x := rfl

def mul (x y : T76 c) : T76 c :=
  ⟨x.u + y.u, x.v + y.v, x.z + y.z + A76 c x.u y.v, x.w + y.w + A76 c y.v x.u⟩

def one : T76 c := ⟨0, 0, 0, 0⟩

def inv (x : T76 c) : T76 c :=
  ⟨x.u, x.v, x.z + A76 c x.u x.v, x.w + A76 c x.v x.u⟩

instance : Mul (T76 c) := ⟨mul⟩
instance : One (T76 c) := ⟨one⟩
instance : Inv (T76 c) := ⟨inv⟩

@[simp] lemma mul_u (x y : T76 c) : (x * y).u = x.u + y.u := rfl
@[simp] lemma mul_v (x y : T76 c) : (x * y).v = x.v + y.v := rfl
@[simp] lemma mul_z (x y : T76 c) : (x * y).z = x.z + y.z + A76 c x.u y.v := rfl
@[simp] lemma mul_w (x y : T76 c) : (x * y).w = x.w + y.w + A76 c y.v x.u := rfl
@[simp] lemma one_u : (1 : T76 c).u = 0 := rfl
@[simp] lemma one_v : (1 : T76 c).v = 0 := rfl
@[simp] lemma one_z : (1 : T76 c).z = 0 := rfl
@[simp] lemma one_w : (1 : T76 c).w = 0 := rfl
lemma zmod2_add_cancel (a b : ZMod 2) : a + b + a + b = 0 := by
  calc a + b + a + b = a + a + (b + b) := by abel
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

lemma zmod2_add_right_cancel (a b : ZMod 2) : (a + b) + b = a := by
  calc (a + b) + b = a + (b + b) := by abel
    _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma inv_u (x : T76 c) : x⁻¹.u = x.u := by
  cases x
  rfl

lemma inv_v (x : T76 c) : x⁻¹.v = x.v := by
  cases x
  rfl

lemma inv_z (x : T76 c) : x⁻¹.z = x.z + A76 c x.u x.v := by
  cases x
  rfl

lemma inv_w (x : T76 c) : x⁻¹.w = x.w + A76 c x.v x.u := by
  cases x
  rfl

lemma one_mul_T (x : T76 c) : 1 * x = x := by
  apply ext
  · rw [mul_u, one_u, zero_add]
  · rw [mul_v, one_v, zero_add]
  · rw [mul_z, one_z, one_u, zero_add, A76_zero_left, add_zero]
  · rw [mul_w, one_w, one_u, zero_add, A76_zero_right, add_zero]

lemma inv_mul_T (x : T76 c) : x⁻¹ * x = 1 := by
  apply ext
  · rw [mul_u, inv_u, one_u, CharTwo.add_self_eq_zero]
  · rw [mul_v, inv_v, one_v, CharTwo.add_self_eq_zero]
  · rw [mul_z, inv_z, inv_u, one_z]
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_cancel (x.z i) (A76 c x.u x.v i)
  · rw [mul_w, inv_w, inv_u, one_w]
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_cancel (x.w i) (A76 c x.v x.u i)

lemma mul_assoc_T (x y z : T76 c) : x * y * z = x * (y * z) := by
  apply ext
  · simp [add_assoc]
  · simp [add_assoc]
  · simp [A76_add_left, A76_add_right]; abel
  · simp [A76_add_left, A76_add_right]; abel

instance : Group (T76 c) :=
  Group.ofLeftAxioms mul_assoc_T one_mul_T inv_mul_T

def sigmaFun (x : T76 c) : T76 c :=
  ⟨x.v, x.u, x.w + A76 c x.v x.u, x.z + A76 c x.u x.v⟩

@[simp] lemma sigma_u (x : T76 c) : (sigmaFun x).u = x.v := rfl
@[simp] lemma sigma_v (x : T76 c) : (sigmaFun x).v = x.u := rfl
@[simp] lemma sigma_z (x : T76 c) : (sigmaFun x).z = x.w + A76 c x.v x.u := rfl
@[simp] lemma sigma_w (x : T76 c) : (sigmaFun x).w = x.z + A76 c x.u x.v := rfl

lemma sigma_mul (x y : T76 c) : sigmaFun (x * y) = sigmaFun x * sigmaFun y := by
  apply ext
  · rw [sigma_u, mul_v, mul_u, sigma_u, sigma_u]
  · rw [sigma_v, mul_u, mul_v, sigma_v, sigma_v]
  · ext i
    simp only [sigma_z, mul_w, mul_v, mul_u, mul_z, sigma_u, sigma_v, Pi.add_apply,
      A76_add_left, A76_add_right]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_mul]
  · ext i
    simp only [sigma_w, mul_z, mul_u, mul_v, mul_w, sigma_u, sigma_v, Pi.add_apply,
      A76_add_left, A76_add_right]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_mul]

lemma sigma_sigma (x : T76 c) : sigmaFun (sigmaFun x) = x := by
  apply ext
  · rw [sigma_u, sigma_v]
  · rw [sigma_v, sigma_u]
  · rw [sigma_z, sigma_w, sigma_v, sigma_u]
    ext i
    simp only [Pi.add_apply]
    exact zmod2_add_right_cancel (x.z i) (A76 c x.u x.v i)
  · rw [sigma_w, sigma_z, sigma_u, sigma_v]
    ext i
    simp only [Pi.add_apply]
    exact zmod2_add_right_cancel (x.w i) (A76 c x.v x.u i)

def sigmaEquiv : T76 c ≃* T76 c where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv := sigma_sigma
  right_inv := sigma_sigma
  map_mul' := sigma_mul

@[simp] lemma sigmaEquiv_apply (x : T76 c) : sigmaEquiv x = sigmaFun x := rfl

lemma sigma_one : sigmaFun (1 : T76 c) = 1 := by
  apply ext
  · rw [sigma_u, one_v, one_u]
  · rw [sigma_v, one_u, one_v]
  · rw [sigma_z, one_w, one_v, one_u, one_z, A76_zero_left, add_zero]
  · rw [sigma_w, one_z, one_u, one_v, one_w, A76_zero_right, add_zero]

lemma comm_to_one (x y : T76 c) (h : x * y = y * x) : x⁻¹ * y⁻¹ * x * y = 1 := by
  have h1 : x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by simp only [mul_assoc]
  rw [h1, h]
  have h2 : x⁻¹ * y⁻¹ * (y * x) = x⁻¹ * (y⁻¹ * y) * x := by simp only [mul_assoc]
  rw [h2, inv_mul_cancel, mul_one, inv_mul_cancel]

lemma commutator_coords (x y : T76 c) :
    x⁻¹ * y⁻¹ * x * y =
      ⟨0, 0, A76 c x.u y.v + A76 c y.u x.v, A76 c y.v x.u + A76 c x.v y.u⟩ := by
  apply ext
  · rw [mul_u, mul_u, mul_u, inv_u, inv_u]
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_cancel (x.u i) (y.u i)
  · rw [mul_v, mul_v, mul_v, inv_v, inv_v]
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_cancel (x.v i) (y.v i)
  · ext i
    simp only [mul_z, mul_u, inv_z, inv_u, inv_v, Pi.add_apply, A76_add_left, A76_add_right]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_mul, zero_add,
      show (3 : ZMod 2) = 1 from by decide, mul_one]
  · ext i
    simp only [mul_w, mul_u, mul_v, inv_w, inv_u, inv_v, Pi.add_apply, A76_add_left,
      A76_add_right]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_mul, zero_add,
      show (3 : ZMod 2) = 1 from by decide, mul_one]

lemma diag_comm_S (x y : T76 c) (hx : x.v = x.u) (hy : y.v = y.u) (h : x * y = y * x) :
    S76 c x.u y.u = 0 := by
  have hc := comm_to_one x y h
  rw [commutator_coords] at hc
  have hz : A76 c x.u y.v + A76 c y.u x.v = 0 := by
    have hze := congrArg (fun t : T76 c => t.z) hc
    simpa using hze
  rw [hx, hy] at hz
  simpa [S76] using hz

end T76

open T76

lemma zmod2_split (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

def phi76 (c : Coeff76) : Multiplicative (ZMod 2) →* MulAut (T76 c) where
  toFun ε := if ε.toAdd = 0 then 1 else T76.sigmaEquiv
  map_one' := by simp [toAdd_one]
  map_mul' := by
    intro a b
    ext t
    simp only [MulAut.mul_apply]
    have hab : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    rcases eq_or_ne a.toAdd 0 with ha | ha <;> rcases eq_or_ne b.toAdd 0 with hb | hb
    · have ha' : a = 1 := (toAdd_eq_zero).mp ha
      have hb' : b = 1 := (toAdd_eq_zero).mp hb
      simp [ha', hb', hab, toAdd_one]
    · have ha' : a = 1 := (toAdd_eq_zero).mp ha
      have hb1 : b.toAdd = 1 := by
        rcases zmod2_split b.toAdd with h0 | h1
        · exact absurd h0 hb
        · exact h1
      have hb' : b = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa [toAdd_ofAdd] using hb1
      simp [ha', hb', hab, T76.sigmaEquiv_apply, T76.sigma_one, toAdd_ofAdd]
    · have hb' : b = 1 := (toAdd_eq_zero).mp hb
      have ha1 : a.toAdd = 1 := by
        rcases zmod2_split a.toAdd with h0 | h1
        · exact absurd h0 ha
        · exact h1
      have ha' : a = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa [toAdd_ofAdd] using ha1
      simp [ha', hb', hab, T76.sigmaEquiv_apply, T76.sigma_one, toAdd_ofAdd]
    · have ha1 : a.toAdd = 1 := by
        rcases zmod2_split a.toAdd with h0 | h1
        · exact absurd h0 ha
        · exact h1
      have hb1 : b.toAdd = 1 := by
        rcases zmod2_split b.toAdd with h0 | h1
        · exact absurd h0 hb
        · exact h1
      have ha' : a = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa [toAdd_ofAdd] using ha1
      have hb' : b = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa [toAdd_ofAdd] using hb1
      simp [ha', hb', hab, show (1 + 1 : ZMod 2) = 0 from CharTwo.add_self_eq_zero 1,
        T76.sigmaEquiv_apply, T76.sigma_sigma]

@[simp] lemma phi76_apply (c : Coeff76) (ε : Multiplicative (ZMod 2)) (t : T76 c) :
    (phi76 c ε) t = if ε.toAdd = 0 then t else T76.sigmaFun t := by
  dsimp [phi76]
  split_ifs <;> simp [T76.sigmaEquiv_apply]

abbrev G76 (c : Coeff76) := SemidirectProduct (T76 c) (Multiplicative (ZMod 2)) (phi76 c)

namespace G76

variable {c : Coeff76}

def eps76 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

lemma eps_mul_self : eps76 * eps76 = 1 := by
  rw [eps76, ← ofAdd_add, show (1 + 1 : ZMod 2) = 0 from CharTwo.add_self_eq_zero 1, ofAdd_zero]

lemma eps_inv : eps76⁻¹ = eps76 := inv_eq_of_mul_eq_one_left eps_mul_self

lemma eps_toAdd : eps76.toAdd = 1 := by
  simp [eps76]

def equivProd : G76 c ≃ T76 c × Multiplicative (ZMod 2) where
  toFun g := (g.left, g.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (T76 c) :=
  Fintype.ofEquiv (U76 × U76 × Z76 × Z76)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      invFun := fun t => (t.u, t.v, t.z, t.w)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Fintype (G76 c) := Fintype.ofEquiv _ equivProd.symm

lemma card_T : Fintype.card (T76 c) = 2 ^ 144 := by
  let e : T76 c ≃ U76 × U76 × Z76 × Z76 :=
    { toFun := fun t => (t.u, t.v, t.z, t.w)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hU : Fintype.card U76 = 2 ^ 59 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hZ : Fintype.card Z76 = 2 ^ 13 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  calc Fintype.card (T76 c)
      = Fintype.card (U76 × U76 × Z76 × Z76) := Fintype.card_congr e
    _ = Fintype.card U76 * (Fintype.card U76 * (Fintype.card Z76 * Fintype.card Z76)) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
    _ = 2 ^ 59 * (2 ^ 59 * (2 ^ 13 * 2 ^ 13)) := by rw [hU, hZ]
    _ = 2 ^ 59 * (2 ^ 59 * 2 ^ (13 + 13)) := by rw [← Nat.pow_add]
    _ = 2 ^ 59 * 2 ^ (59 + (13 + 13)) := by rw [← Nat.pow_add]
    _ = 2 ^ (59 + (59 + (13 + 13))) := by rw [← Nat.pow_add]
    _ = 2 ^ 144 := by norm_num

lemma card_G : Fintype.card (G76 c) = 2 ^ 145 := by
  rw [Fintype.card_congr (equivProd (c := c)), Fintype.card_prod, card_T]
  have hM : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Fintype.card_congr (Multiplicative.toAdd (α := ZMod 2)), ZMod.card]
  rw [hM]
  norm_num

lemma natCard_G : Nat.card (G76 c) = 2 ^ 145 := by
  rw [Nat.card_eq_fintype_card, card_G]

lemma card_Z : Nat.card Z76 = 2 ^ 13 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

lemma card_U : Nat.card U76 = 2 ^ 59 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

def ofU (u : U76) : G76 c := SemidirectProduct.inl ⟨u, 0, 0, 0⟩

lemma ofU_u (u : U76) : ((ofU u : G76 c).left).u = u := rfl

lemma ofU_v (u : U76) : ((ofU u : G76 c).left).v = 0 := rfl

lemma ofU_right (u : U76) : (ofU u : G76 c).right = 1 := rfl

lemma ofU_inv (u : U76) : (ofU (c := c) u)⁻¹ = ofU (c := c) u := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.inv_left, ofU_right, inv_one, phi76_apply, toAdd_one, if_pos rfl]
    apply T76.ext
    · rw [T76.inv_u]
    · rw [T76.inv_v]
    · rw [T76.inv_z, ofU_v, A76_zero_right, add_zero]
    · rw [T76.inv_w, ofU_v, A76_zero_left, add_zero]
  · rw [SemidirectProduct.inv_right, ofU_right, inv_one]

lemma probe_coords (u : U76) (b : G76 c) (hb : b.right = eps76) :
    ((ofU (c := c) u)⁻¹ * b⁻¹ * ofU (c := c) u * b).right = 1 ∧
      ((ofU (c := c) u)⁻¹ * b⁻¹ * ofU (c := c) u * b).left.u = u ∧
      ((ofU (c := c) u)⁻¹ * b⁻¹ * ofU (c := c) u * b).left.v = u := by
  have hg : (ofU (c := c) u)⁻¹ = ofU (c := c) u := ofU_inv (c := c) u
  have hbInv : b⁻¹.right = eps76 := by rw [SemidirectProduct.inv_right, hb, eps_inv]
  have hbInvU : b⁻¹.left.u = b.left.v := by
    rw [SemidirectProduct.inv_left, hb, eps_inv, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.sigma_u, T76.inv_v]
  have hbInvV : b⁻¹.left.v = b.left.u := by
    rw [SemidirectProduct.inv_left, hb, eps_inv, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.sigma_v, T76.inv_u]
  have hp1r : (ofU (c := c) u * b⁻¹).right = eps76 := by
    rw [SemidirectProduct.mul_right, ofU_right, hbInv, one_mul]
  have hp1u : (ofU (c := c) u * b⁻¹).left.u = u + b.left.v := by
    rw [SemidirectProduct.mul_left, ofU_right, phi76_apply, toAdd_one, if_pos rfl, T76.mul_u,
      ofU_u, hbInvU]
  have hp1v : (ofU (c := c) u * b⁻¹).left.v = b.left.u := by
    rw [SemidirectProduct.mul_left, ofU_right, phi76_apply, toAdd_one, if_pos rfl, T76.mul_v,
      ofU_v, hbInvV, zero_add]
  have hp2r : (ofU (c := c) u * b⁻¹ * ofU (c := c) u).right = eps76 := by
    rw [SemidirectProduct.mul_right, hp1r, ofU_right, mul_one]
  have hp2u : (ofU (c := c) u * b⁻¹ * ofU (c := c) u).left.u = u + b.left.v := by
    rw [SemidirectProduct.mul_left, hp1r, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.mul_u, hp1u, T76.sigma_u, ofU_v, add_zero]
  have hp2v : (ofU (c := c) u * b⁻¹ * ofU (c := c) u).left.v = b.left.u + u := by
    rw [SemidirectProduct.mul_left, hp1r, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.mul_v, hp1v, T76.sigma_v, ofU_u]
  have hassoc : (ofU (c := c) u)⁻¹ * b⁻¹ * ofU (c := c) u * b =
      ofU (c := c) u * b⁻¹ * ofU (c := c) u * b := by rw [hg]
  refine ⟨?_, ?_, ?_⟩
  · rw [hassoc, SemidirectProduct.mul_right, hp2r, hb, eps_mul_self]
  · rw [hassoc, SemidirectProduct.mul_left, hp2r, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.mul_u, hp2u, T76.sigma_u, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · rw [hassoc, SemidirectProduct.mul_left, hp2r, phi76_apply, eps_toAdd,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), T76.mul_v, hp2v, T76.sigma_v, add_assoc,
      add_comm u (b.left.u), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

lemma zmod2_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left
    rfl
  · right
    rfl

lemma right_dichotomy (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = eps76 := by
  rcases zmod2_dichotomy a.toAdd with h0 | h1
  · left
    exact (toAdd_eq_zero).mp h0
  · right
    apply Multiplicative.ext
    simpa [eps_toAdd] using h1

lemma finrank_U : Module.finrank (ZMod 2) U76 = 59 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma mem_right_eq_one {B : Subgroup (G76 c)} (hN : B.Normal) (hC : IsMulCommutative B)
    (hc : ∀ X : Submodule (ZMod 2) U76, Module.finrank (ZMod 2) X = 9 →
      ¬ IsCommonIsotropic76 c X)
    {b : G76 c} (hb : b ∈ B) : b.right = 1 := by
  by_contra hr
  have hbε : b.right = eps76 := by
    rcases right_dichotomy b.right with h1 | hε
    · exact absurd h1 hr
    · exact hε
  have hS : ∀ u v : U76, S76 c u v = 0 := by
    intro u v
    let nu := (ofU (c := c) u)⁻¹ * b⁻¹ * ofU (c := c) u * b
    let nv := (ofU (c := c) v)⁻¹ * b⁻¹ * ofU (c := c) v * b
    have hnuB : nu ∈ B := by
      have hb' : b⁻¹ ∈ B := inv_mem hb
      exact mul_mem (hN.conj_mem' b⁻¹ hb' (ofU (c := c) u)) hb
    have hnvB : nv ∈ B := by
      have hb' : b⁻¹ ∈ B := inv_mem hb
      exact mul_mem (hN.conj_mem' b⁻¹ hb' (ofU (c := c) v)) hb
    have hcomm : nu * nv = nv * nu := by
      let xu : B := ⟨nu, hnuB⟩
      let xv : B := ⟨nv, hnvB⟩
      have := mul_comm' xu xv
      simpa [xu, xv] using congrArg Subtype.val this
    have hpu := probe_coords u b hbε
    have hpv := probe_coords v b hbε
    have hleft : nu.left * nv.left = nv.left * nu.left := by
      have hmul := congrArg SemidirectProduct.left hcomm
      rw [SemidirectProduct.mul_left] at hmul
      conv_rhs at hmul => rw [SemidirectProduct.mul_left]
      rw [hpu.1, hpv.1] at hmul
      simp only [phi76_apply, toAdd_one, if_pos rfl] at hmul
      exact hmul
    have hSu := T76.diag_comm_S nu.left nv.left
      (hpu.2.2.trans hpu.2.1.symm) (hpv.2.2.trans hpv.2.1.symm) hleft
    rw [hpu.2.1, hpv.2.1] at hSu
    exact hSu
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := U76) (n := 9)
    (by rw [finrank_U]; norm_num)
  let X : Submodule (ZMod 2) U76 := Submodule.span (ZMod 2) (Set.range f)
  have hX : Module.finrank (ZMod 2) X = 9 := by
    rw [finrank_span_eq_card hf, Fintype.card_fin]
  exact hc X hX fun x _ y _ => hS x y

def imageL (B : Subgroup (G76 c)) (hR : ∀ g : G76 c, g ∈ B → g.right = 1) :
    Submodule (ZMod 2) (U76 × U76) where
  carrier := {p | ∃ g ∈ B, g.left.u = p.1 ∧ g.left.v = p.2}
  zero_mem' := ⟨1, one_mem B, by simp⟩
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨gp, hgp, hpu, hpv⟩
    rcases hq with ⟨gq, hgq, hqu, hqv⟩
    refine ⟨gp * gq, mul_mem hgp hgq, ?_, ?_⟩
    · have hpr := hR gp hgp
      simp [hpr, hpu, hqu, phi76_apply, toAdd_one]
    · have hpr := hR gp hgp
      simp [hpr, hpv, hqv, phi76_apply, toAdd_one]
  smul_mem' := by
    intro r p hp
    rcases zmod2_dichotomy r with hr | hr
    · subst hr
      refine ⟨1, one_mem B, ?_, ?_⟩
      · rw [zero_smul]
        rfl
      · rw [zero_smul]
        rfl
    · subst hr
      rw [one_smul]
      exact hp

lemma imageL_swap {B : Subgroup (G76 c)} (hN : B.Normal)
    (hR : ∀ g : G76 c, g ∈ B → g.right = 1) {p : U76 × U76}
    (hp : p ∈ imageL B hR) : (p.2, p.1) ∈ imageL B hR := by
  rcases hp with ⟨g, hg, hu, hv⟩
  let s : G76 c := SemidirectProduct.inr eps76
  have hs : s⁻¹ = s := by
    apply SemidirectProduct.ext
    · apply T76.ext <;> simp [s, eps_inv, eps_toAdd, phi76_apply]
    · simp [s, eps_inv]
  have hmem : s⁻¹ * g * s ∈ B := hN.conj_mem' g hg s
  have hleft : (s⁻¹ * g * s).left = T76.sigmaFun g.left := by
    have hgr := hR g hg
    have hφ {t : T76 c} : (phi76 c eps76) t = T76.sigmaFun t := by
      rw [phi76_apply, eps_toAdd, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    rw [hs]
    have hsl : s.left = 1 := by simp [s]
    have hsr : s.right = eps76 := by simp [s]
    have h1l : (s * g).left = T76.sigmaFun g.left := by
      rw [SemidirectProduct.mul_left, hsl, hsr, one_mul, hφ]
    have h1r : (s * g).right = eps76 := by
      rw [SemidirectProduct.mul_right, hsr, hgr, mul_one]
    rw [SemidirectProduct.mul_left, h1l, h1r, hφ, hsl, T76.sigma_one, mul_one]
  refine ⟨s⁻¹ * g * s, hmem, ?_, ?_⟩
  · simp [hleft, hv]
  · simp [hleft, hu]

def diagOf (L : Submodule (ZMod 2) (U76 × U76)) : Submodule (ZMod 2) U76 where
  carrier := {u | (u, u) ∈ L}
  zero_mem' := L.zero_mem
  add_mem' := by
    intro u v hu hv
    have hsum := L.add_mem hu hv
    simpa [Prod.mk_add_mk] using hsum
  smul_mem' := by
    intro r u hu
    have hsm := L.smul_mem r hu
    simpa [Prod.smul_mk] using hsm

lemma diag_isotropic {B : Subgroup (G76 c)} (hC : IsMulCommutative B)
    (hR : ∀ g : G76 c, g ∈ B → g.right = 1) :
    IsCommonIsotropic76 c (diagOf (imageL B hR)) := by
  intro u hu v hv
  rcases hu with ⟨gu, hgu, huu, huv⟩
  rcases hv with ⟨gv, hgv, hvu, hvv⟩
  have hcomm : gu * gv = gv * gu := by
    let a : B := ⟨gu, hgu⟩
    let b0 : B := ⟨gv, hgv⟩
    have := mul_comm' a b0
    simpa [a, b0] using congrArg Subtype.val this
  have hleft : gu.left * gv.left = gv.left * gu.left := by
    have := congrArg SemidirectProduct.left hcomm
    simpa [hR gu hgu, hR gv hgv, phi76_apply, toAdd_one] using this
  have hS := T76.diag_comm_S gu.left gv.left (huv.trans huu.symm) (hvv.trans hvu.symm) hleft
  simpa [huu, hvu] using hS

lemma finrank_diag_le (hc : ∀ X : Submodule (ZMod 2) U76, Module.finrank (ZMod 2) X = 9 →
      ¬ IsCommonIsotropic76 c X)
    {D : Submodule (ZMod 2) U76} (hiso : IsCommonIsotropic76 c D) :
    Module.finrank (ZMod 2) D ≤ 8 := by
  by_contra hgt
  have h9 : 9 ≤ Module.finrank (ZMod 2) D := by omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := D) h9
  have hg : LinearIndependent (ZMod 2) (fun i => (f i : U76)) :=
    hf.map' D.subtype (Submodule.ker_subtype _)
  let X : Submodule (ZMod 2) U76 := Submodule.span (ZMod 2) (Set.range fun i => (f i : U76))
  have hle : X ≤ D := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  have hX : Module.finrank (ZMod 2) X = 9 := by
    rw [finrank_span_eq_card hg, Fintype.card_fin]
  exact hc X hX fun x hx y hy => hiso x (hle hx) y (hle hy)

def sumL (L : Submodule (ZMod 2) (U76 × U76)) : L →ₗ[ZMod 2] U76 where
  toFun x := x.1.1 + x.1.2
  map_add' x y := by simp [add_add_add_comm]
  map_smul' r x := by simp [mul_add]

lemma sumL_apply (L : Submodule (ZMod 2) (U76 × U76)) (x : L) :
    sumL L x = x.1.1 + x.1.2 := rfl

lemma finrank_image_le {B : Subgroup (G76 c)} (hN : B.Normal) (hC : IsMulCommutative B)
    (hc : ∀ X : Submodule (ZMod 2) U76, Module.finrank (ZMod 2) X = 9 →
      ¬ IsCommonIsotropic76 c X)
    (hR : ∀ g : G76 c, g ∈ B → g.right = 1) :
    Module.finrank (ZMod 2) (imageL B hR) ≤ 16 := by
  let L := imageL B hR
  let D := diagOf L
  have hiso : IsCommonIsotropic76 c D := diag_isotropic hC hR
  have hD : Module.finrank (ZMod 2) D ≤ 8 := finrank_diag_le hc hiso
  let φ := sumL L
  let kerTo : LinearMap.ker φ →ₗ[ZMod 2] D :=
    { toFun := fun x => ⟨x.1.1.1, by
        have hx : sumL L x.1 = 0 := by
          simpa [φ, sumL_apply] using (LinearMap.mem_ker φ).mp x.2
        have huv : x.1.1.2 = x.1.1.1 := ((CharTwo.add_eq_zero).mp hx).symm
        have hmem : (x.1.1.1, x.1.1.2) ∈ L := x.1.2
        simpa [D, diagOf, huv] using hmem⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hkerInj : Injective kerTo := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hu : x.1.1.1 = y.1.1.1 := by simpa [kerTo] using congrArg Subtype.val hxy
    have hx : x.1.1.2 = x.1.1.1 := by
      have hsum : sumL L x.1 = 0 := by
        simpa [φ, sumL_apply] using (LinearMap.mem_ker φ).mp x.2
      exact ((CharTwo.add_eq_zero).mp hsum).symm
    have hy : y.1.1.2 = y.1.1.1 := by
      have hsum : sumL L y.1 = 0 := by
        simpa [φ, sumL_apply] using (LinearMap.mem_ker φ).mp y.2
      exact ((CharTwo.add_eq_zero).mp hsum).symm
    exact Prod.ext hu (hx.trans (hu.trans hy.symm))
  have hker : Module.finrank (ZMod 2) (LinearMap.ker φ) ≤ 8 := by
    have hle := LinearMap.finrank_le_finrank_of_injective hkerInj
    exact hle.trans hD
  have hrange : LinearMap.range φ ≤ D := by
    intro w hw
    rcases hw with ⟨x, rfl⟩
    have h1 : (x.1.1, x.1.2) ∈ L := x.2
    have h2 : (x.1.2, x.1.1) ∈ L := imageL_swap hN hR h1
    have hsum := L.add_mem h1 h2
    rw [show (x : U76 × U76) = (x.1.1, x.1.2) from rfl, Prod.mk_add_mk] at hsum
    rw [add_comm x.1.2 x.1.1] at hsum
    show (φ x, φ x) ∈ L
    rw [show φ x = x.1.1 + x.1.2 from sumL_apply L x]
    exact hsum
  have hrge : Module.finrank (ZMod 2) (LinearMap.range φ) ≤ 8 := by
    have hle := Submodule.finrank_mono hrange
    exact hle.trans hD
  show Module.finrank (ZMod 2) L ≤ 16
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  omega

lemma normal_abelian_card {B : Subgroup (G76 c)} (hN : B.Normal) (hC : IsMulCommutative B)
    (hc : ∀ X : Submodule (ZMod 2) U76, Module.finrank (ZMod 2) X = 9 →
      ¬ IsCommonIsotropic76 c X) :
    Nat.card B ≤ 2 ^ 42 := by
  have hR : ∀ g : G76 c, g ∈ B → g.right = 1 := fun g hg => mem_right_eq_one hN hC hc hg
  let L := imageL B hR
  have hfin : Module.finrank (ZMod 2) L ≤ 16 := finrank_image_le hN hC hc hR
  haveI : Finite L := Finite.of_injective (Subtype.val : L → U76 × U76) Subtype.val_injective
  have hcardL : Nat.card L ≤ 2 ^ 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := L)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
    exact Nat.pow_le_pow_right (by decide) hfin
  let emb : B → L × Z76 × Z76 := fun b =>
    (⟨(b.1.left.u, b.1.left.v), ⟨b.1, b.2, rfl, rfl⟩⟩, b.1.left.z, b.1.left.w)
  have hinj : Injective emb := by
    intro a b0 h
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply T76.ext
      · exact congrArg (fun p : L × Z76 × Z76 => p.1.1.1) h
      · exact congrArg (fun p : L × Z76 × Z76 => p.1.1.2) h
      · exact congrArg (fun p : L × Z76 × Z76 => p.2.1) h
      · exact congrArg (fun p : L × Z76 × Z76 => p.2.2) h
    · rw [hR a.1 a.2, hR b0.1 b0.2]
  haveI : Finite B := Finite.of_injective (Subtype.val : B → G76 c) Subtype.val_injective
  haveI : Finite (L × Z76 × Z76) := by infer_instance
  have hle := Nat.card_le_card_of_injective emb hinj
  have hprod : Nat.card (L × Z76 × Z76) = Nat.card L * 2 ^ 13 * 2 ^ 13 := by
    rw [Nat.card_prod, Nat.card_prod]
    try rw [card_Z]
    try rw [card_Z]
    rw [mul_assoc]
  have hpow : (2 : ℕ) ^ 16 * 2 ^ 13 * 2 ^ 13 = 2 ^ 42 := by
    calc (2 : ℕ) ^ 16 * 2 ^ 13 * 2 ^ 13
        = 2 ^ (16 + 13) * 2 ^ 13 := by rw [← Nat.pow_add]
      _ = 2 ^ (16 + 13 + 13) := by rw [← Nat.pow_add]
      _ = 2 ^ 42 := by norm_num
  calc Nat.card B ≤ Nat.card (L × Z76 × Z76) := hle
    _ = Nat.card L * 2 ^ 13 * 2 ^ 13 := hprod
    _ ≤ 2 ^ 16 * 2 ^ 13 * 2 ^ 13 := by
        have := Nat.mul_le_mul_right (2 ^ 13 * 2 ^ 13) hcardL
        simpa [Nat.mul_assoc] using this
    _ = 2 ^ 42 := hpow

def bigH (c : Coeff76) : Subgroup (G76 c) where
  carrier := {g | g.left.v = 0 ∧ g.right = 1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · simp [ha.1, ha.2, hb.1, phi76_apply, toAdd_one]
    · simp [ha.2, hb.2]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, ?_⟩
    · rw [SemidirectProduct.inv_left, ha.2, inv_one, phi76_apply, toAdd_one, if_pos rfl,
        T76.inv_v, ha.1]
    · rw [SemidirectProduct.inv_right, ha.2, inv_one]

lemma bigH_comm (c : Coeff76) : IsMulCommutative (bigH c) := by
  refine IsMulCommutative.of_comm ?_
  intro x y
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply T76.ext
    · simp [add_comm, x.2.2, y.2.2, phi76_apply, toAdd_one]
    · simp [x.2.1, x.2.2, y.2.1, y.2.2, phi76_apply, toAdd_one]
    · simp [x.2.1, x.2.2, y.2.1, y.2.2, phi76_apply, toAdd_one, A76_zero_left,
        A76_zero_right, add_comm]
    · simp [x.2.1, x.2.2, y.2.1, y.2.2, phi76_apply, toAdd_one, A76_zero_left,
        A76_zero_right, add_comm]
  · simp [x.2.2, y.2.2]

def bigEquiv (c : Coeff76) : bigH c ≃ U76 × Z76 × Z76 where
  toFun g := (g.1.left.u, g.1.left.z, g.1.left.w)
  invFun p := ⟨SemidirectProduct.inl ⟨p.1, 0, p.2.1, p.2.2⟩, ⟨rfl, rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply T76.ext
      · rfl
      · exact g.2.1.symm
      · rfl
      · rfl
    · exact g.2.2.symm
  right_inv _ := rfl

lemma card_big (c : Coeff76) : Nat.card (bigH c) = 2 ^ 85 := by
  have : Finite (bigH c) := Finite.of_injective (Subtype.val : bigH c → G76 c) Subtype.val_injective
  rw [Nat.card_congr (bigEquiv c), Nat.card_prod, Nat.card_prod, card_U]
  try rw [card_Z]
  try rw [card_Z]
  rw [← mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
  try norm_num

end G76

theorem OMA.solution : type_of% @Kourovka.«20.76».kourovka_20_76 := by
  intro hall
  obtain ⟨c, hc⟩ := exists_good_coeff
  have hP : IsPGroup 2 (G76 c) := IsPGroup.of_card (n := 145) (by rw [G76.natCard_G])
  have hab : ∀ H : Subgroup (G76 c), H.Normal ∧ IsMulCommutative H → Nat.card H ≤ 2 ^ 42 :=
    fun H hH => G76.normal_abelian_card hH.1 hH.2 hc
  have hle := hall 2 Nat.prime_two (G76 c) inferInstance hP inferInstance 42 hab (G76.bigH c)
    (G76.bigH_comm c)
  rw [G76.card_big c] at hle
  have : ¬ (2 : ℕ) ^ 85 ≤ 2 ^ (2 * 42) := by
    intro h
    have h84 : (2 : ℕ) ^ 85 ≤ 2 ^ 84 := by simpa using h
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h84
    omega
  exact this hle
