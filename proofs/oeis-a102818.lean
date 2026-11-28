import OMAStatements.S_oeis_a102818

/-!
# Eventual periodicity of labeled poset counts

Credit: @grp06.

The eventual periodicity conjecture is recorded at https://oeis.org/A102818.
Its sequence counts partial orders on a labeled set, as in https://oeis.org/A001035.
The result also follows from Corollary 2 of Eldar Fischer and Johann A. Makowsky,
*Extensions and Limits of the Specker–Blatter Theorem*, CSL 2024,
https://doi.org/10.4230/LIPIcs.CSL.2024.26.
We give the specialized proof by counting orbits of independent block translations.
-/

open scoped BigOperators
open Finset

namespace A102818

noncomputable section

/-- A finite intersection of subgroups of a finite p-group can be obtained using
at most as many restrictions as the exponent of p in its index. -/
private theorem retain_restrictions {G I : Type*} [AddGroup G] [Finite G]
    {p b : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ b)
    (E : I → AddSubgroup G) (s : Finset I) :
    ∃ t ⊆ s, ∃ e, t.card ≤ e ∧ t.inf E = s.inf E ∧ (s.inf E).index = p ^ e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨∅, by simp, 0, by simp, rfl, by simp⟩
  | @insert i s his ih =>
      obtain ⟨t, hts, e, hte, htsE, he⟩ := ih
      rw [Finset.inf_insert]
      by_cases h : E i ⊓ s.inf E = s.inf E
      · exact ⟨t, hts.trans (Finset.subset_insert _ _), e, hte, htsE.trans h.symm, by simpa only [h] using he⟩
      · have hlt : E i ⊓ s.inf E < s.inf E := lt_of_le_of_ne inf_le_right h
        have hdvd := (E i ⊓ s.inf E).index_dvd_card
        rw [hG] at hdvd
        obtain ⟨f, _, hf⟩ := (Nat.dvd_prime_pow hp).mp hdvd
        have hef := AddSubgroup.index_strictAnti hlt
        rw [he, hf] at hef
        have hcut : e < f := (pow_right_strictMono₀ hp.one_lt).lt_iff_lt.mp hef
        refine ⟨insert i t, ?_, f, ?_, ?_, hf⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hts hj)
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · rw [Finset.inf_insert, htsE]

private theorem mem_subgroup_inf {I G : Type*} [AddGroup G] (s : Finset I)
    (E : I → AddSubgroup G) (g : G) :
    g ∈ s.inf E ↔ ∀ i ∈ s, g ∈ E i := by
  simp only [Finset.inf_eq_iInf, AddSubgroup.mem_iInf]

/-- Restrictions supported on at most two coordinates force an index divisible
by p^a if their intersection misses a translation in each of 2a−1 coordinates. -/
private theorem restriction_index {G I J : Type*} [AddGroup G] [Finite G]
    [Fintype J] {p b a : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ b)
    (hJ : Fintype.card J = 2 * a - 1) (ha : 0 < a)
    (E : I → AddSubgroup G) (s : Finset I) (support : I → Finset J)
    (hsupport : ∀ i, (support i).card ≤ 2)
    (move : J → G) (hout : ∀ j, move j ∉ s.inf E)
    (hlocal : ∀ i ∈ s, ∀ j ∉ support i, move j ∈ E i) :
    p ^ a ∣ (s.inf E).index := by
  classical
  obtain ⟨t, hts, e, hte, hE, he⟩ := retain_restrictions hp hG E s
  have hcover : t.biUnion support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    apply hout j
    rw [← hE, mem_subgroup_inf]
    intro i hi
    exact hlocal i (hts hi) j (fun h => hj (Finset.mem_biUnion.mpr ⟨i, hi, h⟩))
  have hbound : Fintype.card J ≤ 2 * t.card := calc
    Fintype.card J = (t.biUnion support).card := by simp [hcover]
    _ ≤ ∑ i ∈ t, (support i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ t, 2 := Finset.sum_le_sum fun i _ => hsupport i
    _ = 2 * t.card := by simp [mul_comm]
  rw [hJ] at hbound
  rw [he]
  exact Nat.pow_dvd_pow p (by omega)

/-- Strict partial orders, used so that collapsing or pulling back a block
does not create any comparabilities within the block. -/
private structure SOrder (L : Type*) where
  rel : L → L → Prop
  irrefl : ∀ x, ¬ rel x x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

private theorem SOrder.ext_rel {L : Type*} {r s : SOrder L}
    (h : ∀ x y, r.rel x y ↔ s.rel x y) : r = s := by
  have hr : r.rel = s.rel := funext fun x => funext fun y => propext (h x y)
  cases r with
  | mk rr hri hrt =>
    cases s with
    | mk ss hsi hst =>
      change rr = ss at hr
      subst ss
      rfl

private instance {L : Type*} [Finite L] : Finite (SOrder L) :=
  Finite.of_injective (fun r : SOrder L => r.rel) fun r s h => by
    change r.rel = s.rel at h
    exact SOrder.ext_rel (fun x y => by rw [h])

private abbrev ROrder (L : Type*) :=
  {r : L → L → Prop // (∀ x, r x x) ∧
    (∀ x y, r x y → r y x → x = y) ∧ ∀ x y z, r x y → r y z → r x z}

private def strictEquivReflexive (L : Type*) : SOrder L ≃ ROrder L where
  toFun r := ⟨fun x y => x = y ∨ r.rel x y, by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y hxy hyx
      rcases hxy with hxy | hxy
      · exact hxy
      rcases hyx with hyx | hyx
      · exact hyx.symm
      · exact (r.irrefl x (r.trans hxy hyx)).elim
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (r.trans hxy hyz)⟩
  invFun r := {
    rel := fun x y => r.val x y ∧ x ≠ y
    irrefl := fun _ h => h.2 rfl
    trans := by
      intro x y z hxy hyz
      refine ⟨r.property.2.2 _ _ _ hxy.1 hyz.1, ?_⟩
      rintro rfl
      exact hxy.2 (r.property.2.1 _ _ hxy.1 hyz.1) }
  left_inv r := by
    apply SOrder.ext_rel
    intro x y
    change ((x = y ∨ r.rel x y) ∧ x ≠ y) ↔ r.rel x y
    constructor
    · rintro ⟨h | h, hne⟩
      · exact (hne h).elim
      · exact h
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro rfl
      exact r.irrefl x h
  right_inv r := by
    apply Subtype.ext
    funext x y
    apply propext
    change (x = y ∨ (r.val x y ∧ x ≠ y)) ↔ r.val x y
    constructor
    · rintro (rfl | h)
      · exact r.property.1 _
      · exact h.1
    · intro h
      by_cases e : x = y
      · exact Or.inl e
      · exact Or.inr ⟨h, e⟩

private def pull {L M : Type*} (f : L → M) (r : SOrder M) : SOrder L where
  rel x y := r.rel (f x) (f y)
  irrefl x := r.irrefl (f x)
  trans := r.trans

private def ordersCongr {L M : Type*} (e : L ≃ M) : SOrder L ≃ SOrder M where
  toFun := pull e.symm
  invFun := pull e
  left_inv r := by apply SOrder.ext_rel; intro x y; simp [pull]
  right_inv r := by apply SOrder.ext_rel; intro x y; simp [pull]

private theorem card_orders {L : Type*} [Finite L] {n : ℕ} (h : Nat.card L = n) :
    Nat.card (SOrder L) = OMA.S_oeis_a102818.P n := by
  letI := Fintype.ofFinite L
  let e : L ≃ Fin n := Fintype.equivFinOfCardEq (by simpa [Nat.card_eq_fintype_card] using h)
  unfold OMA.S_oeis_a102818.P
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr ((ordersCongr e).trans (strictEquivReflexive (Fin n)))

private abbrev V (p b : ℕ) := Fin b → ZMod p
private abbrev Label (p b d : ℕ) := (Fin b × ZMod p) ⊕ Fin d

variable {p b d : ℕ}

private def translate (v : V p b) : Label p b d → Label p b d
  | .inl (i, z) => .inl (i, z + v i)
  | .inr x => .inr x

@[simp] private theorem translate_zero (x : Label p b d) : translate (0 : V p b) x = x := by
  rcases x with ⟨i, z⟩ | x <;> simp [translate]

private theorem translate_add (v w : V p b) (x : Label p b d) :
    translate (v + w) x = translate w (translate v x) := by
  rcases x with ⟨i, z⟩ | x <;> simp [translate, add_assoc]

private instance : AddAction (V p b) (SOrder (Label p b d)) where
  vadd v r := pull (translate v) r
  zero_vadd r := by
    apply SOrder.ext_rel
    intro x y
    change r.rel (translate 0 x) (translate 0 y) ↔ r.rel x y
    simp
  add_vadd v w r := by
    apply SOrder.ext_rel
    intro x y
    change r.rel (translate (v + w) x) (translate (v + w) y) ↔
      r.rel (translate w (translate v x)) (translate w (translate v y))
    rw [translate_add, translate_add]

private def block (x : Label p b d) : Option (Fin b) :=
  match x with
  | .inl a => some a.1
  | .inr _ => none

@[simp] private theorem block_translate (v : V p b) (x : Label p b d) :
    block (translate v x) = block x := by
  rcases x with ⟨i, z⟩ | x <;> rfl

private def single (i : Fin b) (z : ZMod p) : V p b := fun j => if j = i then z else 0

private theorem translate_single_other (i : Fin b) (z : ZMod p) (x : Label p b d)
    (h : block x ≠ some i) : translate (single i z) x = x := by
  rcases x with ⟨j, t⟩ | x
  · have hj : j ≠ i := fun e => h (congrArg some e)
    simp [translate, single, hj]
  · rfl

private def matrixStabilizer (r : SOrder (Label p b d))
    (ij : Option (Fin b) × Option (Fin b)) : AddSubgroup (V p b) where
  carrier := {v | ∀ x y, block x = ij.1 → block y = ij.2 →
    (r.rel (translate v x) (translate v y) ↔ r.rel x y)}
  zero_mem' := by
    show ∀ x y, block x = ij.1 → block y = ij.2 →
      (r.rel (translate 0 x) (translate 0 y) ↔ r.rel x y)
    simp
  add_mem' := by
    intro v w hv hw
    intro x y hx hy
    rw [translate_add, translate_add]
    exact (hw _ _ (by simpa using hx) (by simpa using hy)).trans (hv x y hx hy)
  neg_mem' := by
    intro v hv
    intro x y hx hy
    have h := hv (translate (-v) x) (translate (-v) y) (by simpa using hx) (by simpa using hy)
    rw [← translate_add, ← translate_add, neg_add_cancel, translate_zero, translate_zero] at h
    exact h.symm

private theorem matrix_inf_eq (r : SOrder (Label p b d)) :
    Finset.univ.inf (matrixStabilizer r) = AddAction.stabilizer (V p b) r := by
  ext v
  rw [mem_subgroup_inf, AddAction.mem_stabilizer_iff]
  constructor
  · intro hv
    apply SOrder.ext_rel
    intro x y
    exact hv (block x, block y) (Finset.mem_univ _) x y rfl rfl
  · intro hv ij _
    intro x y _ _
    change (v +ᵥ r).rel x y ↔ r.rel x y
    rw [hv]

private def supportPair (ij : Option (Fin b) × Option (Fin b)) : Finset (Fin b) :=
  Finset.univ.filter fun i => some i = ij.1 ∨ some i = ij.2

private theorem supportPair_card (ij : Option (Fin b) × Option (Fin b)) :
    (supportPair ij).card ≤ 2 := by
  rcases ij with ⟨_ | i, _ | j⟩
  · simp [supportPair]
  · have hs : supportPair (none, some j) = {j} := by ext k; simp [supportPair]
    rw [hs]
    simp
  · have hs : supportPair (some i, none) = {i} := by ext k; simp [supportPair]
    rw [hs]
    simp
  · have hs : supportPair (some i, some j) = {i, j} := by ext k; simp [supportPair]
    rw [hs]
    exact Finset.card_le_two

private def BlockFixed (i : Fin b) (r : SOrder (Label p b d)) : Prop :=
  ∀ z : ZMod p, single i z +ᵥ r = r

private theorem blockFixed_iff (i : Fin b) (r : SOrder (Label p b d)) :
    BlockFixed i r ↔ ∀ (z : ZMod p) (x y : Label p b d),
      r.rel (translate (single i z) x) (translate (single i z) y) ↔ r.rel x y := by
  constructor
  · intro h z x y
    change (single i z +ᵥ r).rel x y ↔ r.rel x y
    rw [h z]
  · intro h z
    exact SOrder.ext_rel (h z)

private theorem stabilizer_index [NeZero p] (hp : p.Prime) {a : ℕ}
    (ha : 0 < a) (hb : b = 2 * a - 1) (r : SOrder (Label p b d))
    (hr : ∀ i : Fin b, ¬ BlockFixed i r) :
    p ^ a ∣ (AddAction.stabilizer (V p b) r).index := by
  classical
  let move : Fin b → V p b := fun i => single i (Classical.choose (not_forall.mp (hr i)))
  have hmove (i) : move i ∉ AddAction.stabilizer (V p b) r :=
    Classical.choose_spec (not_forall.mp (hr i))
  have hG : Nat.card (V p b) = p ^ b := by simp [V, Nat.card_fun, Nat.card_fin]
  rw [← matrix_inf_eq r]
  refine restriction_index hp hG (by simpa using hb) ha (matrixStabilizer r)
    Finset.univ supportPair supportPair_card move ?_ ?_
  · intro i
    rw [matrix_inf_eq]
    exact hmove i
  · intro ij _ i hi x y hx hy
    have hne : some i ≠ ij.1 ∧ some i ≠ ij.2 := by
      simpa [supportPair] using hi
    have ex : translate (move i) x = x :=
      translate_single_other _ _ _ (fun h => hne.1 (h.symm.trans hx))
    have ey : translate (move i) y = y :=
      translate_single_other _ _ _ (fun h => hne.2 (h.symm.trans hy))
    rw [ex, ey]

private abbrev Good (p b d : ℕ) :=
  {r : SOrder (Label p b d) // ∀ i : Fin b, ¬ BlockFixed i r}

private theorem good_translate (r : Good p b d) (v : V p b) :
    ∀ i : Fin b, ¬ BlockFixed i (v +ᵥ r.val) := by
  intro i hi
  apply r.property i
  intro z
  have hcomm : single i z +ᵥ (v +ᵥ r.val) = v +ᵥ (single i z +ᵥ r.val) := by
    rw [← add_vadd, ← add_vadd, add_comm (single i z) v]
  have hv := congrArg (fun s : SOrder (Label p b d) => (-v) +ᵥ s)
    (hcomm.symm.trans (hi z))
  simpa only [← add_vadd, ← add_assoc, neg_add_cancel, zero_add, zero_vadd] using hv

private instance : AddAction (V p b) (Good p b d) where
  vadd v r := ⟨v +ᵥ r.val, good_translate r v⟩
  zero_vadd r := Subtype.ext (zero_vadd (V p b) r.val)
  add_vadd v w r := Subtype.ext (add_vadd v w r.val)

private theorem good_stabilizer (r : Good p b d) :
    AddAction.stabilizer (V p b) r = AddAction.stabilizer (V p b) r.val := by
  ext v
  simp only [AddAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hval := congrArg (fun s : Good p b d => s.val) h
    change v +ᵥ r.val = r.val at hval
    exact hval
  · intro h
    apply Subtype.ext
    change v +ᵥ r.val = r.val
    exact h

private theorem card_dvd_of_stabilizers {G X : Type*} [AddGroup G] [AddAction G X]
    [Finite G] [Finite X] {m : ℕ}
    (h : ∀ r : X, m ∣ (AddAction.stabilizer G r).index) :
    m ∣ Nat.card X := by
  classical
  letI := Fintype.ofFinite (AddAction.orbitRel.Quotient G X)
  rw [Nat.card_congr (AddAction.selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
  exact Finset.dvd_sum fun o _ => h o.out

private theorem card_good [NeZero p] {a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hb : b = 2 * a - 1) :
    p ^ a ∣ Nat.card (Good p b d) := by
  apply card_dvd_of_stabilizers (G := V p b)
  intro r
  rw [good_stabilizer]
  exact stabilizer_index hp ha hb r.val r.property

/-- In a strict order preserved by a finite group element, an element
and its translate cannot be strictly comparable in the forward direction. -/
private theorem no_rel_translate [NeZero p] (r : SOrder (Label p b d)) (v : V p b)
    (hv : ∀ x y, r.rel (translate v x) (translate v y) ↔ r.rel x y)
    (x : Label p b d) : ¬ r.rel x (translate v x) := by
  intro h
  have hn (n : ℕ) : r.rel x (translate ((n + 1) • v) x) := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have ht := (hv x (translate ((n + 1) • v) x)).mpr ih
      rw [← translate_add, ← succ_nsmul] at ht
      exact r.trans h ht
  have hk : addOrderOf v - 1 + 1 = addOrderOf v := by
    have hpos := addOrderOf_pos v
    omega
  have hcycle := hn (addOrderOf v - 1)
  rw [hk, addOrderOf_nsmul_eq_zero, translate_zero] at hcycle
  exact r.irrefl x hcycle

private theorem no_rel_in_block [NeZero p] (r : SOrder (Label p b d)) {i : Fin b}
    (hi : BlockFixed i r) (u w : ZMod p) :
    ¬ r.rel (.inl (i, u)) (.inl (i, w)) := by
  have ht : translate (single i (w - u)) (Sum.inl (i, u) : Label p b d) = Sum.inl (i, w) := by
    simp [translate, single, add_comm u (w - u)]
  have hv := no_rel_translate r (single i (w - u))
    ((blockFixed_iff i r).mp hi (w - u)) (.inl (i, u))
  rwa [ht] at hv

private def normalize (J : Finset (Fin b)) : Label p b d → Label p b d
  | .inl (i, z) => .inl (i, if i ∈ J then 0 else z)
  | .inr x => .inr x

private theorem normalize_idem (J : Finset (Fin b)) (x : Label p b d) :
    normalize J (normalize J x) = normalize J x := by
  rcases x with ⟨i, z⟩ | x
  · by_cases hi : i ∈ J <;> simp [normalize, hi]
  · rfl

private theorem normalize_translate (J : Finset (Fin b)) {i : Fin b} (hi : i ∈ J)
    (v : ZMod p) (x : Label p b d) :
    normalize J (translate (single i v) x) = normalize J x := by
  rcases x with ⟨j, z⟩ | x
  · by_cases h : j = i
    · subst j
      simp [normalize, translate, hi]
    · simp [normalize, translate, single, h]
  · rfl

private theorem rel_normalize_one [NeZero p] (J : Finset (Fin b))
    (r : SOrder (Label p b d)) (hr : ∀ i ∈ J, BlockFixed i r) (x y : Label p b d) :
    (r.rel (normalize J x) y ↔ r.rel x y) ∧
    (r.rel y (normalize J x) ↔ r.rel y x) := by
  rcases x with ⟨i, z⟩ | x
  · by_cases hi : i ∈ J
    · by_cases hy : block y = some i
      · obtain ⟨w, rfl⟩ : ∃ w : ZMod p, y = Sum.inl (i, w) := by
          rcases y with ⟨j, w⟩ | y
          · have hji : j = i := Option.some.inj hy
            exact ⟨w, by rw [hji]⟩
          · simp [block] at hy
        have hnone (s t : ZMod p) : ¬ r.rel (.inl (i, s)) (.inl (i, t)) :=
          no_rel_in_block r (hr i hi) s t
        simp [normalize, hi, hnone]
      · have hx : translate (single i (-z)) (Sum.inl (i, z) : Label p b d) =
            normalize J (.inl (i, z)) := by simp [translate, single, normalize, hi]
        have hy' := translate_single_other i (-z) y hy
        have inv := (blockFixed_iff i r).mp (hr i hi) (-z)
        have h₁ := inv (.inl (i, z)) y
        have h₂ := inv y (.inl (i, z))
        rw [hx, hy'] at h₁
        rw [hx, hy'] at h₂
        exact ⟨h₁, h₂⟩
    · simp [normalize, hi]
  · simp [normalize]

private abbrev Reps (p b d : ℕ) (J : Finset (Fin b)) :=
  {x : Label p b d // normalize J x = x}

private def collapse (J : Finset (Fin b)) (x : Label p b d) : Reps p b d J :=
  ⟨normalize J x, normalize_idem J x⟩

private theorem collapse_translate (J : Finset (Fin b)) {i : Fin b} (hi : i ∈ J)
    (z : ZMod p) (x : Label p b d) :
    collapse J (translate (single i z) x) = collapse J x :=
  Subtype.ext (normalize_translate J hi z x)

private abbrev Fixed (p b d : ℕ) (J : Finset (Fin b)) :=
  {r : SOrder (Label p b d) // ∀ i ∈ J, BlockFixed i r}

private def collapseOrders [NeZero p] (J : Finset (Fin b)) :
    Fixed p b d J ≃ SOrder (Reps p b d J) where
  toFun r := pull Subtype.val r.val
  invFun s := ⟨pull (collapse J) s, by
    intro i hi
    apply (blockFixed_iff i (pull (collapse J) s)).mpr
    intro z x y
    change s.rel (collapse J (translate (single i z) x)) (collapse J (translate (single i z) y)) ↔
      s.rel (collapse J x) (collapse J y)
    rw [collapse_translate J hi z x, collapse_translate J hi z y]⟩
  left_inv r := by
    apply Subtype.ext
    apply SOrder.ext_rel
    intro x y
    change r.val.rel (normalize J x) (normalize J y) ↔ r.val.rel x y
    exact ((rel_normalize_one J r.val r.property x (normalize J y)).1).trans
      ((rel_normalize_one J r.val r.property y x).2)
  right_inv s := by
    have h (x : Reps p b d J) : collapse J x.val = x := Subtype.ext x.property
    apply SOrder.ext_rel
    intro x y
    change s.rel (collapse J x.val) (collapse J y.val) ↔ s.rel x y
    rw [h x, h y]

private abbrev Removed (p b d : ℕ) (J : Finset (Fin b)) :=
  {x : Label p b d // normalize J x ≠ x}

private def removedEquiv (J : Finset (Fin b)) :
    (↥J × {z : ZMod p // z ≠ 0}) ≃ Removed p b d J where
  toFun w := ⟨.inl (w.1.val, w.2.val), by
    have h := w.2.property
    simpa [normalize, w.1.property, eq_comm] using h⟩
  invFun x := match x with
    | ⟨.inl (i, z), hx⟩ => by
      have hi : i ∈ J := by
        by_contra hi
        exact hx (by simp [normalize, hi])
      have hz : z ≠ 0 := by
        rintro rfl
        exact hx (by simp [normalize, hi])
      exact (⟨i, hi⟩, ⟨z, hz⟩)
    | ⟨.inr _, hx⟩ => (hx rfl).elim
  left_inv := by rintro ⟨⟨i, hi⟩, ⟨z, hz⟩⟩; rfl
  right_inv := by
    rintro ⟨⟨i, z⟩ | x, hx⟩
    · rfl
    · exact (hx rfl).elim

private theorem card_complement {X : Type*} [Fintype X] (q : X → Prop) :
    Nat.card {x // ¬ q x} = Nat.card X - Nat.card {x // q x} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private theorem card_label [NeZero p] : Nat.card (Label p b d) = b * p + d := by
  rw [Nat.card_sum, Nat.card_prod]
  simp [Nat.card_fin]

private theorem card_reps [NeZero p] (J : Finset (Fin b)) :
    Nat.card (Reps p b d J) = b * p + d - J.card * (p - 1) := by
  have hzero : Nat.card {z : ZMod p // z = 0} = 1 := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
  have hz := card_complement (fun z : ZMod p => z = 0)
  rw [Nat.card_zmod, hzero] at hz
  have hremoved : Nat.card (Removed p b d J) = J.card * (p - 1) := by
    rw [← Nat.card_congr (removedEquiv (p := p) (d := d) J), Nat.card_prod, hz]
    simp [Nat.card_eq_fintype_card]
  calc
    Nat.card (Reps p b d J)
        = Nat.card {x : Label p b d // ¬ normalize J x ≠ x} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ => not_not.symm))
    _ = _ := by
      rw [card_complement, card_label, hremoved]

private theorem card_fixed [NeZero p] (J : Finset (Fin b)) :
    Nat.card (Fixed p b d J) = OMA.S_oeis_a102818.P (b * p + d - J.card * (p - 1)) :=
  (Nat.card_congr (collapseOrders J)).trans (card_orders (card_reps J))

private theorem mem_finset_inf {I X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset I) (f : I → Finset X) (x : X) :
    x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s _ ih =>
      rw [Finset.inf_insert]
      change x ∈ f i ∩ s.inf f ↔ ∀ j ∈ insert i s, x ∈ f j
      rw [Finset.mem_inter, ih]
      simp only [Finset.mem_insert, or_imp, forall_and, forall_eq]

private theorem card_as_finset {X : Type*} [Finite X] {q : X → Prop}
    (s : Finset X) (hs : ∀ x, x ∈ s ↔ q x) :
    s.card = Nat.card {x // q x} := by
  letI := Fintype.ofFinite {x // q x}
  exact (Fintype.card_of_subtype s hs).symm.trans Nat.card_eq_fintype_card.symm

open OMA.S_oeis_a102818 (P)

private theorem count_sum [NeZero p] {a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hb : b = 2 * a - 1) (d : ℕ) :
    (∑ J ∈ (Finset.univ : Finset (Fin b)).powerset,
      (-1 : ZMod (p ^ a)) ^ J.card * (P (b * p + d - J.card * (p - 1)) : ZMod (p ^ a))) =
      0 := by
  classical
  letI := Fintype.ofFinite (SOrder (Label p b d))
  let S (i : Fin b) : Finset (SOrder (Label p b d)) :=
    Finset.univ.filter (BlockFixed i)
  let I : Finset (Fin b) := Finset.univ
  have hfixed (J : Finset (Fin b)) : (J.inf S).card = Nat.card (Fixed p b d J) := by
    apply card_as_finset
    intro r
    simp only [mem_finset_inf, S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgood : (I.inf fun i => (S i)ᶜ).card = Nat.card (Good p b d) := by
    apply card_as_finset
    intro r
    simp [mem_finset_inf, I, S]
  have hz : ((I.inf fun i => (S i)ᶜ).card : ZMod (p ^ a)) = 0 := by
    rw [hgood, ZMod.natCast_eq_zero_iff]
    exact card_good hp ha hb
  have hIE :
      ((I.inf fun i => (S i)ᶜ).card : ZMod (p ^ a)) =
        ∑ J ∈ I.powerset, (-1 : ZMod (p ^ a)) ^ J.card * ((J.inf S).card : ZMod (p ^ a)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using
      (Finset.inclusion_exclusion_sum_inf_compl I S (fun _ => (1 : ZMod (p ^ a))))
  calc
    _ = ∑ J ∈ I.powerset, (-1 : ZMod (p ^ a)) ^ J.card * ((J.inf S).card : ZMod (p ^ a)) := by
      apply Finset.sum_congr rfl
      intro J _
      rw [hfixed J, card_fixed]
    _ = _ := hIE.symm.trans hz

private theorem count_recurrence [NeZero p] {a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hb : b = 2 * a - 1) {n : ℕ} (hn : b * p ≤ n) :
    (∑ J ∈ ((Finset.univ : Finset (Fin b)).powerset.erase ∅),
      (-1 : ZMod (p ^ a)) ^ J.card * (P (n - J.card * (p - 1)) : ZMod (p ^ a))) +
        (P n : ZMod (p ^ a)) = 0 := by
  classical
  have h := count_sum hp ha hb (n - b * p)
  rw [Nat.add_sub_of_le hn] at h
  rw [← Finset.sum_erase_add _ _
    (show (∅ : Finset (Fin b)) ∈ (Finset.univ : Finset (Fin b)).powerset by simp)] at h
  simpa only [Finset.card_empty, pow_zero, zero_mul, Nat.sub_zero, one_mul] using h

/-- A finite-valued sequence whose next term is determined by a fixed-length
window of earlier terms is eventually periodic. -/
private theorem periodic_of_windows {X : Type*} [Finite X] (f : ℕ → X) (B w : ℕ)
    (step : ∀ x y, B ≤ x → B ≤ y → (∀ j < w, f (x + j) = f (y + j)) →
      f (x + w) = f (y + w)) :
    ∃ N T : ℕ, 0 < T ∧ ∀ k ≥ N, f (k + T) = f k := by
  classical
  letI := Fintype.ofFinite (Fin w → X)
  let M := Fintype.card (Fin w → X) + 1
  let win (x : ℕ) (j : Fin w) := f (x + j.val)
  obtain ⟨s, t, hst, he⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin M => win (B + i.val)) (by simp [M])
  have hne : s.val ≠ t.val := fun h => hst (Fin.ext h)
  obtain ⟨x, y, hx, hxy, hwin⟩ : ∃ x y : ℕ, B ≤ x ∧ x < y ∧ win x = win y := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨B + s.val, B + t.val, by omega, by omega, he⟩
    · exact ⟨B + t.val, B + s.val, by omega, by omega, he.symm⟩
  have hall (q : ℕ) : win (x + q) = win (y + q) := by
    induction q with
    | zero => simpa using hwin
    | succ q ih =>
      funext i
      change f (x + (q + 1) + i.val) = f (y + (q + 1) + i.val)
      by_cases h : i.val + 1 < w
      · have hh := congrFun ih (⟨i.val + 1, h⟩ : Fin w)
        change f (x + q + (i.val + 1)) = f (y + q + (i.val + 1)) at hh
        have hx' : x + (q + 1) + i.val = x + q + (i.val + 1) := by omega
        have hy' : y + (q + 1) + i.val = y + q + (i.val + 1) := by omega
        rwa [hx', hy']
      · have hi := i.isLt
        have hh := step (x + q) (y + q) (by omega) (by omega)
          (fun j hj => congrFun ih (⟨j, hj⟩ : Fin w))
        have hx' : x + (q + 1) + i.val = x + q + w := by omega
        have hy' : y + (q + 1) + i.val = y + q + w := by omega
        rwa [hx', hy']
  refine ⟨x + w, y - x, by omega, ?_⟩
  intro k hk
  let q := k - (x + w)
  have hk₁ : x + q + w = k := by dsimp [q]; omega
  have hk₂ : y + q + w = k + (y - x) := by dsimp [q]; omega
  have hext := step (x + q) (y + q) (by omega) (by omega)
    (fun j hj => congrFun (hall q) (⟨j, hj⟩ : Fin w))
  rw [hk₁, hk₂] at hext
  exact hext.symm

private def PeriodicMod (m : ℕ) : Prop :=
  ∃ N T : ℕ, 0 < T ∧ ∀ k ≥ N, P (k + T) ≡ P k [MOD m]

private theorem periodic_prime_power (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    PeriodicMod (p ^ a) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let b := 2 * a - 1
  let w := b * (p - 1)
  let f (n : ℕ) : ZMod (p ^ a) := P n
  obtain ⟨N, T, hT, h⟩ := periodic_of_windows f (b * p) w (by
    intro x y hx hy hprev
    have hx' := count_recurrence hp ha (b := b) rfl (n := x + w) (by omega)
    have hy' := count_recurrence hp ha (b := b) rfl (n := y + w) (by omega)
    have hsum :
        (∑ J ∈ ((Finset.univ : Finset (Fin b)).powerset.erase ∅),
          (-1 : ZMod (p ^ a)) ^ J.card * f (x + w - J.card * (p - 1))) =
        ∑ J ∈ ((Finset.univ : Finset (Fin b)).powerset.erase ∅),
          (-1 : ZMod (p ^ a)) ^ J.card * f (y + w - J.card * (p - 1)) := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hJ0 : 0 < J.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1)
      have hpos : 0 < J.card * (p - 1) := Nat.mul_pos hJ0 (by have := hp.one_lt; omega)
      have hJle : J.card ≤ b := by
        simpa only [Fintype.card_fin] using J.card_le_univ
      have hle : J.card * (p - 1) ≤ w :=
        Nat.mul_le_mul_right _ hJle
      have hj : w - J.card * (p - 1) < w := by omega
      rw [Nat.add_sub_assoc hle, Nat.add_sub_assoc hle, hprev _ hj]
    dsimp only [f] at hsum ⊢
    rw [hsum] at hx'
    exact add_left_cancel (hx'.trans hy'.symm))
  exact ⟨N, T, hT, fun k hk => (ZMod.natCast_eq_natCast_iff _ _ _).mp (h k hk)⟩

private theorem mod_period_multiple {m N T : ℕ}
    (h : ∀ k ≥ N, P (k + T) ≡ P k [MOD m]) (q k : ℕ) (hk : N ≤ k) :
    P (k + T * q) ≡ P k [MOD m] := by
  induction q with
  | zero =>
    simpa only [Nat.mul_zero, Nat.add_zero] using (Nat.ModEq.rfl : P k ≡ P k [MOD m])
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact (h (k + T * q) (by omega)).trans ih

private theorem periodic_mul {u v : ℕ} (huv : u.Coprime v)
    (hu : PeriodicMod u) (hv : PeriodicMod v) : PeriodicMod (u * v) := by
  obtain ⟨Nu, Tu, hTu, hu⟩ := hu
  obtain ⟨Nv, Tv, hTv, hv⟩ := hv
  refine ⟨max Nu Nv, Tu * Tv, Nat.mul_pos hTu hTv, ?_⟩
  intro k hk
  apply (Nat.modEq_and_modEq_iff_modEq_mul huv).mp
  refine ⟨mod_period_multiple hu Tv k ((le_max_left _ _).trans hk), ?_⟩
  rw [Nat.mul_comm Tu Tv]
  exact mod_period_multiple hv Tu k ((le_max_right _ _).trans hk)

theorem periodic_pos (m : ℕ) (hm : 1 ≤ m) : PeriodicMod m := by
  revert hm
  refine Nat.recOnPosPrimePosCoprime (motive := fun n => 1 ≤ n → PeriodicMod n)
    (fun p a hp ha _ => periodic_prime_power p a hp ha) ?_ ?_ ?_ m
  · omega
  · exact fun _ => ⟨0, 1, Nat.one_pos, fun _ _ => Nat.modEq_one⟩
  · intro u v hu hv huv hpu hpv _
    exact periodic_mul huv (hpu (by omega)) (hpv (by omega))

end

end A102818

theorem OMA.solution : type_of% @OMA.S_oeis_a102818.main :=
  A102818.periodic_pos
