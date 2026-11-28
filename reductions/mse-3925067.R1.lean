import OMAStatements.S_mse_3925067

/-!
# Prime-power roots of inner automorphisms

Reduction mse-3925067.R1. Credit: @yuka30240.

If the full automorphism group is the additive real line, then a prime-power
root of some conjugation acts on the center with prime order. At this prime p
the center has no p-torsion, and a commutator has no central root of the same
prime-power degree. The two steps ask for an additional automorphism in the
dyadic and odd-prime cases.

The abelian case follows the basis-swap argument of diracdeltafunk in the
discussion of Math Stack Exchange question 3925067.
-/
open scoped commutatorElement

namespace OMA.R_mse_3925067_R1

/-- An involution on the center coming from a prime-power root of conjugation
forces a faithful real action containing the inner automorphisms to miss an automorphism. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] (a : Multiplicative ℝ →* MulAut G),
    Function.Injective a → (∀ x : G, MulAut.conj x ∈ a.range) →
    ∀ (t : Multiplicative ℝ) (k : ℕ) (x y : G),
    (a t) ^ (2 ^ k) = MulAut.conj x →
    (∀ z : Subgroup.center G, z ^ 2 = 1 → z = 1) →
    (∀ z : Subgroup.center G, (z : G) ^ (2 ^ k) ≠ ⁅x, y⁆) →
    orderOf (Subgroup.centerCongr (a t)) = 2 → a.range ≠ ⊤

/-- An odd-prime-order action on the center coming from a prime-power root of conjugation
forces a faithful real action containing the inner automorphisms to miss an automorphism. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] (a : Multiplicative ℝ →* MulAut G),
    Function.Injective a → (∀ x : G, MulAut.conj x ∈ a.range) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : Multiplicative ℝ) (k : ℕ) (x y : G),
    (a t) ^ (p ^ k) = MulAut.conj x →
    (∀ z : Subgroup.center G, z ^ p = 1 → z = 1) →
    (∀ z : Subgroup.center G, (z : G) ^ (p ^ k) ≠ ⁅x, y⁆) →
    orderOf (Subgroup.centerCongr (a t)) = p → a.range ≠ ⊤

theorem no_involution {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    {f : MulAut G} (hf : f * f = 1) : f = 1 := by
  have h := congrArg Multiplicative.toAdd (congrArg e hf)
  simp only [map_mul, map_one] at h
  change (e f).toAdd + (e f).toAdd = 0 at h
  apply e.injective
  rw [map_one]
  change (e f).toAdd = 0
  linarith

private theorem commutative_case {G : Type} [CommGroup G]
    (e : MulAut G ≃* Multiplicative ℝ) : False := by
  classical
  have hi : MulEquiv.inv G = 1 := no_involution e (by ext x; exact inv_inv x)
  have hs (x : G) : x * x = 1 := by
    have hx : x⁻¹ = x := DFunLike.congr_fun hi x
    exact eq_inv_iff_mul_eq_one.mp hx.symm
  let V := Additive G
  let : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) fun x ↦ by
    rw [two_nsmul]
    exact hs x.toMul
  let b := Module.Free.chooseBasis (ZMod 2) V
  let I := Module.Free.ChooseBasisIndex (ZMod 2) V
  by_cases hI : Nontrivial I
  · obtain ⟨i, j, hij⟩ := @exists_pair_ne I hI
    let L := b.equiv b (Equiv.swap i j)
    let f : MulAut G := AddEquiv.toMultiplicative L.toAddEquiv
    have hL : L.trans L = LinearEquiv.refl (ZMod 2) V := by
      apply b.ext'
      intro k
      simp [L]
    have hf : f = 1 := no_involution e (by
      ext x
      exact DFunLike.congr_fun hL (Additive.ofMul x))
    have hfix : L (b i) = b i := DFunLike.congr_fun hf (b i).toMul
    have heq : b j = b i := by simpa [L, Module.Basis.equiv_apply] using hfix
    exact hij (b.injective heq).symm
  · have : Subsingleton I := not_nontrivial_iff_subsingleton.mp hI
    have : Finite G := Finite.of_injective b.equivFun b.equivFun.injective
    have : Finite (MulAut G) := Finite.of_injective (fun f : MulAut G ↦ (⇑f : G → G))
      DFunLike.coe_injective
    have : Finite ℝ := Finite.of_surjective e e.surjective
    exact not_finite ℝ

private theorem conj_trivial_iff {G : Type} [Group G] (x : G) :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h y
    have he : x * y * x⁻¹ = y := DFunLike.congr_fun h y
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  · intro h
    ext y
    change x * y * x⁻¹ = y
    rw [← h, mul_inv_cancel_right]

private theorem conj_invariant {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    (f : MulAut G) (x : G) : MulAut.conj (f x) = MulAut.conj x := by
  have he : f * MulAut.conj x = MulAut.conj x * f := by
    apply e.injective
    simp only [map_mul, mul_comm]
  ext y
  obtain ⟨z, rfl⟩ := f.surjective y
  simpa [MulAut.mul_apply, MulAut.conj_apply] using DFunLike.congr_fun he z

private theorem displacements_central {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    (f : MulAut G) (x : G) : f x * x⁻¹ ∈ Subgroup.center G := by
  apply (conj_trivial_iff _).mp
  rw [map_mul, map_inv, conj_invariant e, mul_inv_cancel]

/-- Rational multiples of conjugation by x supply compatible roots. If all roots
of inner automorphisms fix the center, their displacements at y form a homomorphism. -/
private theorem commutator_path {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    (hfix : ∀ (f : MulAut G) (n : ℕ), 0 < n →
      f ^ n ∈ (MulAut.conj : G →* MulAut G).range →
      ∀ z : Subgroup.center G, f (z : G) = z) (x y : G) :
    ∃ c : Multiplicative ℚ →* Subgroup.center G, (c (Multiplicative.ofAdd 1) : G) = ⁅x, y⁆ := by
  let r := (e (MulAut.conj x)).toAdd
  let line : ℚ →+ ℝ :=
    { toFun := fun q ↦ (q : ℝ) * r
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul] }
  let a := e.symm.toMonoidHom.comp line.toMultiplicative
  have ha (q : ℚ) : e (a (Multiplicative.ofAdd q)) = Multiplicative.ofAdd ((q : ℝ) * r) := by
    exact e.apply_symm_apply _
  have hr (q : Multiplicative ℚ) (z : Subgroup.center G) : a q (z : G) = z := by
    let u := q.toAdd
    apply hfix _ u.den u.den_pos
    refine ⟨x ^ u.num, ?_⟩
    apply e.injective
    rw [map_zpow, map_zpow, map_pow]
    change _ = e (a (Multiplicative.ofAdd u)) ^ u.den
    rw [ha]
    change u.num • r = u.den • ((u : ℝ) * r)
    rw [zsmul_eq_mul, nsmul_eq_mul, Rat.cast_def]
    have hn : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_ne_zero
    field_simp
  let d (q : Multiplicative ℚ) : Subgroup.center G :=
    ⟨a q y * y⁻¹, displacements_central e _ _⟩
  refine ⟨{ toFun := d, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp [d]
  · intro p q
    apply Subtype.ext
    have h := hr p (d q)
    change a p (a q y * y⁻¹) = a q y * y⁻¹ at h
    rw [map_mul, map_inv] at h
    change a (p * q) y * y⁻¹ = (a p y * y⁻¹) * (a q y * y⁻¹)
    rw [map_mul, MulAut.mul_apply, mul_inv_eq_iff_eq_mul.mp h]
    have hc := Subgroup.mem_center_iff.mp (d q).property (a p y * y⁻¹)
    simpa only [d, mul_assoc] using hc.symm
  · have h : a (Multiplicative.ofAdd 1) = MulAut.conj x := by
      apply e.injective
      simpa [r] using ha 1
    change a (Multiplicative.ofAdd 1) y * y⁻¹ = _
    rw [h, MulAut.conj_apply, commutatorElement_def]

private theorem central_normal {G : Type} [Group G] {D : Subgroup G}
    (hc : D ≤ Subgroup.center G) : D.Normal where
  conj_mem x hx g := by
    rw [Subgroup.mem_center_iff.mp (hc hx) g, mul_inv_cancel_right]
    exact hx

private theorem shift_commutator {G : Type} [Group G] (x y d e : G)
    (hd : d ∈ Subgroup.center G) (he : e ∈ Subgroup.center G)
    (hxy : ⁅x, y⁆ ∈ Subgroup.center G) : ⁅x⁻¹ * d, y⁻¹ * e⁆ = ⁅x, y⁆ := by
  have hd' : ⁅d, y⁻¹ * e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hd _).symm
  have he' : ⁅x⁻¹, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp he _)
  rw [commutatorElement_mul_left_eq_conj_mul, hd', mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, he', mul_one, mul_assoc, mul_inv_cancel, mul_one,
    commutatorElement_inv_left, commutatorElement_inv_left]
  rw [Subgroup.mem_center_iff.mp hxy y⁻¹, inv_mul_cancel_right,
    Subgroup.mem_center_iff.mp hxy x⁻¹, inv_mul_cancel_right]

private theorem divisible_retract {D B : Type} [CommGroup D] [CommGroup B]
    (hd : ∀ (n : ℤ), n ≠ 0 → Function.Surjective (fun d : D ↦ d ^ n))
    (i : D →* B) (hi : Function.Injective i) : ∃ r : B →* D, ∀ d, r (i d) = d := by
  let : DivisibleBy (Additive D) ℤ :=
    divisibleByOfSMulRightSurj _ _ fun {n} hn ↦ hd n hn
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible (Additive D)).extension_property_addMonoidHom
    i.toAdditive hi (AddMonoidHom.id (Additive D))
  exact ⟨r.toMultiplicative, fun d ↦ DFunLike.congr_fun hr (Additive.ofMul d)⟩

/-- In a central extension of an abelian group by a divisible group D, inversion
on the quotient lifts to an automorphism fixing D. P consists of pairs whose
product lies in D. The quotient of P by the diagonal copy of D is abelian.
A retraction onto the remaining copy of D makes its kernel in P the graph
of the desired automorphism. -/
theorem lift_from_divisible {G : Type} [Group G] (D : Subgroup G)
    (hc : D ≤ Subgroup.center G) (hcom : ∀ x y : G, ⁅x, y⁆ ∈ D)
    (hd : ∀ (n : ℤ), n ≠ 0 → Function.Surjective (fun d : D ↦ d ^ n)) :
    ∃ f : MulAut G, ∀ x, f x * x ∈ Subgroup.center G := by
  classical
  let : D.Normal := central_normal hc
  let : CommGroup D := { (inferInstance : Group D) with
    mul_comm x y := Subtype.ext (Subgroup.mem_center_iff.mp (hc y.property) x) }
  have hder : commutator G ≤ D := Subgroup.commutator_le.mpr fun x _ y _ ↦ hcom x y
  have : IsMulCommutative (G ⧸ D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder
  let : CommGroup (G ⧸ D) := { (inferInstance : Group (G ⧸ D)) with mul_comm := mul_comm' }
  let π : G →* G ⧸ D := QuotientGroup.mk' D
  -- The two coordinates are inverse modulo D.
  let P : Subgroup (G × G) :=
    ((π.comp (MonoidHom.fst G G)) * (π.comp (MonoidHom.snd G G))).ker
  have memP (x y : G) : (x, y) ∈ P ↔ x * y ∈ D := by
    change π x * π y = 1 ↔ _
    rw [← map_mul]
    exact QuotientGroup.eq_one_iff _
  let j : D →* P :=
    { toFun := fun d ↦ ⟨(1, d), (memP _ _).mpr (by simp)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp) }
  let δ : D →* P :=
    { toFun := fun d ↦ ⟨(d, d), (memP _ _).mpr (D.mul_mem d.property d.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hδ : δ.range ≤ Subgroup.center P := by
    rintro _ ⟨d, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro p
    exact Subtype.ext (Prod.ext (Subgroup.mem_center_iff.mp (hc d.property) p.val.1)
      (Subgroup.mem_center_iff.mp (hc d.property) p.val.2))
  let : δ.range.Normal := central_normal hδ
  have hderP : commutator P ≤ δ.range := by
    apply Subgroup.commutator_le.mpr
    intro p _ s _
    obtain ⟨⟨x, y⟩, hp⟩ := p
    obtain ⟨⟨v, w⟩, hs⟩ := s
    refine ⟨⟨⁅x, v⁆, hcom x v⟩, Subtype.ext (Prod.ext rfl ?_)⟩
    change ⁅x, v⁆ = ⁅y, w⁆
    have h := shift_commutator x v (x * y) (v * w)
      (hc ((memP _ _).mp hp)) (hc ((memP _ _).mp hs)) (hc (hcom x v))
    simpa using h.symm
  let B := P ⧸ δ.range
  have : IsMulCommutative B := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderP
  let : CommGroup B := { (inferInstance : Group B) with mul_comm := mul_comm' }
  let b : P →* B := QuotientGroup.mk' δ.range
  have hj : Function.Injective (b.comp j) := by
    apply (injective_iff_map_eq_one _).mpr
    intro d he
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp he
    have hfirst : (z : G) = 1 := congrArg (fun u : P ↦ u.val.1) hz
    have hsecond : (z : G) = d := congrArg (fun u : P ↦ u.val.2) hz
    exact Subtype.ext (hsecond.symm.trans hfirst)
  obtain ⟨r, hr⟩ := divisible_retract hd (b.comp j) hj
  let R := r.comp b
  have hjR (d : D) : R (j d) = d := hr d
  have hδR (d : D) : R (δ d) = 1 := by
    change r (b (δ d)) = 1
    rw [show b (δ d) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩, map_one]
  let k := R.ker
  let fst : k →* G := ((MonoidHom.fst G G).comp P.subtype).comp k.subtype
  let snd : k →* G := ((MonoidHom.snd G G).comp P.subtype).comp k.subtype
  have hfst : Function.Bijective fst := by
    constructor
    · apply (injective_iff_map_eq_one _).mpr
      rintro ⟨p, hp⟩ h
      change p.val.1 = 1 at h
      have hm := (memP _ _).mp p.property
      rw [h, one_mul] at hm
      let d : D := ⟨p.val.2, hm⟩
      have hjp : j d = p := Subtype.ext (Prod.ext h.symm rfl)
      have hd1 : d = 1 := by
        rw [← hjR d, hjp]
        exact hp
      exact Subtype.ext (Subtype.ext (Prod.ext h (congrArg Subtype.val hd1)))
    · intro x
      let p : P := ⟨(x, x⁻¹), (memP _ _).mpr (by simp)⟩
      refine ⟨⟨p * j (R p)⁻¹, ?_⟩, by change x * 1 = x; simp⟩
      change R (p * j (R p)⁻¹) = 1
      rw [map_mul, hjR, mul_inv_cancel]
  -- The first projection identifies the kernel with G. The second gives the lift.
  let s := (MulEquiv.ofBijective fst hfst).symm
  let f := snd.comp s.toMonoidHom
  have hfstS (x : G) : fst (s x) = x := (MulEquiv.ofBijective fst hfst).apply_symm_apply x
  have hfix (d : D) : f d = d := by
    let u : k := ⟨δ d, hδR d⟩
    have hsu : s d = u := hfst.injective (hfstS d)
    exact congrArg snd hsu
  have hm (x : G) : x * f x ∈ D := by
    have h := (memP _ _).mp (s x).val.property
    change fst (s x) * f x ∈ D at h
    rwa [hfstS] at h
  have hinv (x : G) : f (f x) = x := by
    have h := hfix ⟨_, hm x⟩
    change f (x * f x) = x * f x at h
    rw [map_mul] at h
    have hxc := Subgroup.mem_center_iff.mp (hc (hm x)) x
    have hx : f x * x = x * f x := by
      apply mul_left_cancel (a := x)
      simpa only [mul_assoc] using hxc.symm
    rw [← hx] at h
    exact mul_left_cancel h
  refine ⟨MulEquiv.ofBijective f ⟨Function.LeftInverse.injective hinv,
    Function.RightInverse.surjective hinv⟩, fun x ↦ ?_⟩
  exact hc (by
    have h := hm (f x)
    rwa [hinv] at h)

/-- Evaluation at one on all rational paths in the center has divisible image. -/
private theorem lift_from_paths {G : Type} [Group G]
    (h : ∀ x y : G, ∃ c : Multiplicative ℚ →* Subgroup.center G,
      (c (Multiplicative.ofAdd 1) : G) = ⁅x, y⁆) :
    ∃ f : MulAut G, ∀ x, f x * x ∈ Subgroup.center G := by
  let : CommGroup (Subgroup.center G) := { (inferInstance : Group (Subgroup.center G)) with
    mul_comm x y := Subtype.ext (Subgroup.mem_center_iff.mp y.property x) }
  let v := (Subgroup.center G).subtype.comp
    (MonoidHom.eval (N := Subgroup.center G) (Multiplicative.ofAdd (1 : ℚ)))
  apply lift_from_divisible v.range
  · rintro _ ⟨c, rfl⟩
    exact (c _).property
  · intro x y
    exact h x y
  · intro n hn d
    obtain ⟨c, hc⟩ := d.property
    let scale : ℚ →+ ℚ :=
      { toFun := fun t ↦ t / n
        map_zero' := by simp
        map_add' := fun _ _ ↦ add_div _ _ _ }
    let c' := c.comp scale.toMultiplicative
    refine ⟨⟨v c', c', rfl⟩, Subtype.ext ?_⟩
    change (c (Multiplicative.ofAdd (1 / (n : ℚ))) : G) ^ n = d
    rw [← Subgroup.coe_zpow, ← map_zpow, ← hc]
    change (c (Multiplicative.ofAdd (n • (1 / (n : ℚ)))) : G) = c (Multiplicative.ofAdd 1)
    rw [zsmul_eq_mul]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    simp [hn']

private theorem field_quotient (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] : ∃ l : V →+ K, Function.Surjective l := by
  let b := Module.Basis.ofVectorSpace K V
  let i := b.index_nonempty.some
  refine ⟨(b.coord i).toAddMonoidHom, fun t ↦ ⟨t • b i, ?_⟩⟩
  change b.coord i (t • b i) = t
  simp [Module.Basis.coord_apply]

private theorem cyclic_quotient_of_not_divisible {A : Type} [AddCommGroup A]
    {p : ℕ} (hp : p.Prime) (h : ¬ Function.Surjective (fun x : A ↦ p • x)) :
    ∃ l : A →+ ZMod p, Function.Surjective l := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let P : AddSubgroup A := (p • AddMonoidHom.id A).range
  let Q : Type := A ⧸ P
  let modQ : Module (ZMod p) Q := QuotientAddGroup.zmodModule (n := p) (H := P) fun x ↦ ⟨x, rfl⟩
  have hQ : Nontrivial Q := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply h
    intro x
    exact (QuotientAddGroup.eq_zero_iff x).mp (hs.elim (QuotientAddGroup.mk x) 0)
  obtain ⟨f, hf⟩ := field_quotient (ZMod p) Q
  exact ⟨f.comp (QuotientAddGroup.mk' P), hf.comp (QuotientAddGroup.mk'_surjective P)⟩

private theorem central_shear {G : Type} [Group G] (d : G →* Subgroup.center G)
    (hfix : ∀ z : Subgroup.center G, d z = 1) :
    ∃ f : MulAut G, ∀ (n : ℕ) (y : G), (f ^ n) y = y * (d y : G) ^ n := by
  let f : MulAut G :=
    { toFun := fun y ↦ y * d y
      invFun := fun y ↦ y * (d y : G)⁻¹
      left_inv := by
        intro y
        simp [map_mul, hfix, mul_assoc]
      right_inv := by
        intro y
        have hz := hfix (d y)⁻¹
        change d ((d y : G)⁻¹) = 1 at hz
        simp [map_mul, hz, mul_assoc]
      map_mul' := by
        intro y z
        simp only [map_mul, Subgroup.coe_mul]
        rw [mul_assoc y z, ← mul_assoc z, Subgroup.mem_center_iff.mp (d y).property z]
        group }
  have hpow (n : ℕ) (y : G) : (f ^ n) y = y * (d y : G) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih]
      change (y * (d y : G) ^ n) * (d (y * (d y : G) ^ n) : G) = _
      rw [map_mul, map_pow, hfix, one_pow, mul_one, pow_succ, mul_assoc]
  exact ⟨f, hpow⟩

/-- A nonzero central character of prime exponent gives a finite-order shear. -/
private theorem no_central_character {G : Type} [Group G]
    (e : MulAut G ≃* Multiplicative ℝ) (d : G →* Subgroup.center G)
    (hfix : ∀ z : Subgroup.center G, d z = 1)
    {p : ℕ} (hp : 0 < p) (hexp : ∀ x : G, d x ^ p = 1) (x : G) : d x = 1 := by
  obtain ⟨f, hpow⟩ := central_shear d hfix
  have hfp : f ^ p = 1 := by
    ext y
    simp [hpow, ← Subgroup.coe_pow, hexp]
  have hfp' := congrArg e hfp
  rw [map_pow, map_one] at hfp'
  change p • (e f).toAdd = 0 at hfp'
  have h0 : (e f).toAdd = 0 := by
    rw [nsmul_eq_mul, mul_eq_zero] at hfp'
    exact hfp'.resolve_left (by exact_mod_cast hp.ne')
  have hf : f = 1 := e.injective (by rw [map_one]; exact h0)
  have hy : x * (d x : G) = x := by simpa [hf] using (hpow 1 x).symm
  exact Subtype.ext (mul_eq_left.mp hy)

/-- If the center has p-torsion, the group of inner automorphisms is p-divisible.
Otherwise its quotient modulo p would give a central character of exponent p. -/
private theorem inner_divisible_of_torsion {G : Type} [Group G]
    (e : MulAut G ≃* Multiplicative ℝ) {p : ℕ} (hp : p.Prime)
    (z : Subgroup.center G) (hz : z ^ p = 1) (hne : z ≠ 1) :
    Function.Surjective (fun u : (MulAut.conj : G →* MulAut G).range ↦ u ^ p) := by
  let π := (MulAut.conj : G →* MulAut G).rangeRestrict
  let I := (MulAut.conj : G →* MulAut G).range
  let : CommGroup I := { (inferInstance : Group I) with
    mul_comm x y := Subtype.ext (e.injective (by simp [mul_comm])) }
  by_contra h
  obtain ⟨l, hl⟩ := cyclic_quotient_of_not_divisible (A := Additive I) hp h
  let m := zmultiplesHom (Additive (Subgroup.center G)) (Additive.ofMul z)
  have hm : m (p : ℤ) = 0 := by
    change z ^ (p : ℤ) = 1
    simpa using hz
  let v := ZMod.lift p ⟨m, hm⟩
  let d := (v.comp l).toMultiplicative.comp π
  have hd (y : Subgroup.center G) : d y = 1 := by
    have hπ : π y = 1 := by
      apply Subtype.ext
      ext t
      change (y : G) * t * (y : G)⁻¹ = t
      rw [← Subgroup.mem_center_iff.mp y.property t, mul_inv_cancel_right]
    change (v.comp l).toMultiplicative (π y) = 1
    rw [hπ]
    exact (v.comp l).toMultiplicative.map_one
  have hexp (y : G) : d y ^ p = 1 := by
    let t := l (Additive.ofMul (π y))
    change p • v t = 0
    rw [← map_nsmul]
    simp [nsmul_eq_mul]
  obtain ⟨i, hi⟩ := hl 1
  obtain ⟨x, hx⟩ := MulAut.conj.rangeRestrict_surjective i.toMul
  have hdx := no_central_character e d hd hp.pos hexp x
  apply hne
  change v (l (Additive.ofMul (π x))) = 0 at hdx
  rw [show Additive.ofMul (π x) = i from hx, hi] at hdx
  have hv : v 1 = Additive.ofMul z := by
    have hv' := ZMod.lift_coe p (⟨m, hm⟩ : { k : ℤ →+ Additive (Subgroup.center G) // k p = 0 }) 1
    simpa [v, m] using hv'
  exact hv.symm.trans hdx

private theorem real_aut_pow_injective {G : Type} [Group G]
    (e : MulAut G ≃* Multiplicative ℝ) {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun f : MulAut G ↦ f ^ n) := by
  intro f g he
  have h := congrArg e he
  simp only [map_pow] at h
  change n • (e f).toAdd = n • (e g).toAdd at h
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  apply e.injective
  change (e f).toAdd = (e g).toAdd
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') h

/-- A root moving the center detects failure of divisibility of a commutator.
With no central p-torsion, any available central roots of the commutators
are unique, giving a central shear whose power is the original conjugation. -/
theorem prime_root_obstruction {G : Type} [Group G]
    (e : MulAut G ≃* Multiplicative ℝ) (p k : ℕ) (hp : p.Prime)
    (u : MulAut G) (x : G) (hinner : u ^ (p ^ k) = MulAut.conj x)
    (hmove : Subgroup.centerCongr u ≠ 1) :
    (∀ z : Subgroup.center G, z ^ p = 1 → z = 1) ∧
    ∃ y : G, ∀ z : Subgroup.center G, (z : G) ^ (p ^ k) ≠ ⁅x, y⁆ := by
  classical
  let N := p ^ k
  have hN : 0 < N := pow_pos hp.pos _
  have hfree (z : Subgroup.center G) (hz : z ^ p = 1) : z = 1 := by
    by_contra hne
    have hd := inner_divisible_of_torsion e hp z hz hne
    have hd' (l : ℕ) : Function.Surjective
        (fun f : (MulAut.conj : G →* MulAut G).range ↦ f ^ (p ^ l)) := by
      induction l with
      | zero => intro v; exact ⟨v, by simp⟩
      | succ l ih =>
        intro v
        obtain ⟨w, hw⟩ := hd v
        obtain ⟨t, ht⟩ := ih w
        refine ⟨t, ?_⟩
        change t ^ (p ^ (l + 1)) = v
        change t ^ (p ^ l) = w at ht
        rw [pow_succ, pow_mul, ht]
        exact hw
    obtain ⟨v, hv⟩ := hd' k (MulAut.conj.rangeRestrict x)
    obtain ⟨y, hy⟩ := v.property
    have hu : u = MulAut.conj y := real_aut_pow_injective e hN
      (hinner.trans (by simpa [hy] using (congrArg Subtype.val hv).symm))
    apply hmove
    rw [hu]
    ext z
    change y * (z : G) * y⁻¹ = (z : G)
    rw [Subgroup.mem_center_iff.mp z.property, mul_inv_cancel_right]
  refine ⟨hfree, ?_⟩
  by_contra! hall
  let : CommGroup (Subgroup.center G) := { (inferInstance : Group (Subgroup.center G)) with
    mul_comm a b := Subtype.ext (Subgroup.mem_center_iff.mp b.property a) }
  have hpI : Function.Injective (fun z : Subgroup.center G ↦ z ^ p) := by
    intro a b hab
    change a ^ p = b ^ p at hab
    apply div_eq_one.mp
    exact hfree _ (by simp [div_pow, hab])
  have hNI (l : ℕ) : Function.Injective (fun z : Subgroup.center G ↦ z ^ (p ^ l)) := by
    induction l with
    | zero => intro a b h; simpa using h
    | succ l ih =>
      intro a b hab
      simp only [pow_succ p, pow_mul] at hab
      exact ih (hpI hab)
  choose d hd using hall
  have hd' (y : G) : ((d y : Subgroup.center G) : G) ^ N = ⁅x, y⁆ := hd y
  have hcent (y : G) : ⁅x, y⁆ ∈ Subgroup.center G := hd' y ▸
    (Subgroup.center G).pow_mem (d y).property N
  let D : G →* Subgroup.center G :=
    { toFun := d
      map_one' := by
        apply hNI k
        apply Subtype.ext
        simpa [commutatorElement_def] using hd' 1
      map_mul' := by
        intro y z
        apply hNI k
        apply Subtype.ext
        change (d (y * z) : G) ^ N = ↑((d y * d z) ^ N)
        rw [mul_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hd', hd', hd',
          commutatorElement_mul_right_eq_mul_conj]
        rw [mul_assoc ⁅x, y⁆ y, Subgroup.mem_center_iff.mp (hcent z) y]
        group }
  have hdD (z : Subgroup.center G) : D z = 1 := by
    apply hNI k
    apply Subtype.ext
    have h := hd' (z : G)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp z.property x)] at h
    simpa [D, N] using h
  obtain ⟨f, hf⟩ := central_shear D hdD
  have hfN : f ^ N = MulAut.conj x := by
    ext y
    rw [hf]
    change y * (d y : G) ^ N = _
    rw [hd', Subgroup.mem_center_iff.mp (hcent y) y, ← conj_eq_commutatorElement_mul]
  have hu : u = f := real_aut_pow_injective e hN (hinner.trans hfN.symm)
  apply hmove
  ext z
  change u (z : G) = (z : G)
  rw [hu]
  simpa [hdD z] using hf 1 (z : G)

/-- Take a power so the action on the center has prime order. Bézout combines
the conclusions for relatively prime factors of an arbitrary exponent. -/
private theorem fix_from_prime_roots {G : Type} [Group G]
    (e : MulAut G ≃* Multiplicative ℝ) (h₂ : H1) (hodd : H2)
    (f : MulAut G) (n : ℕ) (hn : 0 < n)
    (h : f ^ n ∈ (MulAut.conj : G →* MulAut G).range) :
    ∀ z : Subgroup.center G, f (z : G) = z := by
  let a := e.symm.toMonoidHom
  have htop : a.range = ⊤ := MonoidHom.range_eq_top.mpr e.symm.surjective
  let C : MulAut G →* MulAut (Subgroup.center G) :=
    { toFun := Subgroup.centerCongr
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hinner (g : MulAut G) (hg : g ∈ (MulAut.conj : G →* MulAut G).range) : C g = 1 := by
    obtain ⟨x, rfl⟩ := hg
    ext z
    change x * (z : G) * x⁻¹ = (z : G)
    rw [Subgroup.mem_center_iff.mp z.property, mul_inv_cancel_right]
  have hprimary (p k : ℕ) (hp : p.Prime) (g : MulAut G)
      (hg : g ^ (p ^ k) ∈ (MulAut.conj : G →* MulAut G).range) : C g = 1 := by
    by_contra hne
    have hpow : C g ^ (p ^ k) = 1 := (map_pow C g _).symm.trans (hinner _ hg)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hpow)
    cases j with
    | zero => exact hne (orderOf_eq_one_iff.mp (by simpa using hj))
    | succ j =>
      let u := g ^ (p ^ j)
      have horder : orderOf (C u) = p := by
        rw [show C u = C g ^ (p ^ j) from map_pow C _ _, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
          (by rw [hj, pow_succ]; exact dvd_mul_right _ _), hj, pow_succ,
          Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
      have hu : u ^ (p ^ k) ∈ (MulAut.conj : G →* MulAut G).range := by
        change (g ^ (p ^ j)) ^ (p ^ k) ∈ _
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        exact Subgroup.pow_mem _ hg _
      have he : a (e u) = u := e.symm_apply_apply _
      have hc : ∀ x : G, MulAut.conj x ∈ a.range := by simp [htop]
      obtain ⟨x, hx⟩ := hu
      have hm : Subgroup.centerCongr u ≠ 1 := by
        intro htriv
        change orderOf (Subgroup.centerCongr u) = p at horder
        rw [htriv, orderOf_one] at horder
        exact hp.ne_one horder.symm
      obtain ⟨hfree, y, hy⟩ := prime_root_obstruction e p k hp u x hx.symm hm
      by_cases hp2 : p = 2
      · exact h₂ G a e.symm.injective hc (e u) k x y (by rw [he, ← hp2]; exact hx.symm)
          (hp2 ▸ hfree) (hp2 ▸ hy) (by rw [he, ← hp2]; exact horder) htop
      · exact hodd G a e.symm.injective hc p hp hp2 (e u) k x y (by rw [he]; exact hx.symm)
          hfree hy (by rw [he]; exact horder) htop
  have hall (m : ℕ) : 0 < m → ∀ g : MulAut G,
      g ^ m ∈ (MulAut.conj : G →* MulAut G).range → C g = 1 := by
    induction m using Nat.recOnPrimeCoprime with
    | zero => omega
    | prime_pow p k hp => exact fun _ ↦ hprimary p k hp
    | coprime u v hu hv huv ihu ihv =>
      intro _ g hg
      apply (pow_eq_one_iff_of_coprime huv).mp
      rw [← map_pow, ← map_pow]
      constructor
      · apply ihv (by omega)
        rwa [← pow_mul]
      · apply ihu (by omega)
        rwa [← pow_mul, Nat.mul_comm]
  exact fun z ↦ congrArg Subtype.val (DFunLike.congr_fun (hall n hn f h) z)

theorem main : H1 → H2 → type_of% @OMA.S_mse_3925067.main := by
  rintro h₂ hodd ⟨G, _, ⟨e⟩⟩
  obtain ⟨f, hf⟩ := lift_from_paths (commutator_path e (fix_from_prime_roots e h₂ hodd))
  have hcenter : Subgroup.center G = ⊤ := by
    apply top_unique
    intro x _
    have h := (conj_trivial_iff _).mpr (hf x)
    rw [map_mul, conj_invariant e] at h
    exact (conj_trivial_iff _).mp (no_involution e h)
  let _ := Group.commGroupOfCenterEqTop hcenter
  exact commutative_case e

/-- Conversely, the nonexistence conjecture implies both prime-order obstructions. -/
theorem converse (h : type_of% @OMA.S_mse_3925067.main) : H1 ∧ H2 := by
  constructor <;> intro G inst a hi <;> intros <;> intro htop <;>
    exact h ⟨G, inst, ⟨(MulEquiv.ofBijective a ⟨hi, MonoidHom.range_eq_top.mp htop⟩).symm⟩⟩

end OMA.R_mse_3925067_R1
