import FormalConjectures.Wikipedia.AndrewsCurtis

/-!
# A rank induction for ordinary Andrews–Curtis moves

Erase the generator in slot zero. H1 asks for the projected tail to normally generate
the smaller free group. This holds unconditionally in rank two by Euclidean division.
Induction then gives a path on the projected tail. We lift it while holding the first
relator fixed, after correcting that relator to project to the identity.

H2 concerns only tuples with this prescribed projection. It asks for one relator
to agree with the erased generator modulo the other relators. The M-transformation
argument realizes that agreement by ordinary moves. A second application of the
lower-rank induction and the kernel calculation then clear the remaining relators.

For M-transformations see R. G. Burns et al., *Recalcitrance in groups* (1999),
https://doi.org/10.1017/S0004972700036388.
-/

-- Credit: @desenyon

open AndrewsCurtis Function Relation

namespace OMA.R_AndrewsCurtis_andrews_curtis_conjecture_R1

private theorem step {n} {r s : RelatorTuple n} (h : Move r s) : Equivalent r s :=
  EqvGen.rel _ _ h

private theorem chain {n} {r s t : RelatorTuple n} (h : Equivalent r s)
    (k : Equivalent s t) : Equivalent r t := EqvGen.trans _ _ _ h k

private theorem back {n} {r s : RelatorTuple n} (h : Equivalent r s) : Equivalent s r :=
  EqvGen.symm _ _ h

/-- Every elementary move preserves containment of all relators in a normal subgroup. -/
private theorem move_mem {n} {r s : RelatorTuple n} (h : Move r s)
    (N : Subgroup (FreeGroup (Fin n))) [hn : N.Normal] :
    (∀ k, r k ∈ N) ↔ (∀ k, s k ∈ N) := by
  have upd (a : RelatorTuple n) (i : Fin n) (v : FreeGroup (Fin n)) :
      (∀ k, update a i v k ∈ N) ↔ v ∈ N ∧ ∀ k, k ≠ i → a k ∈ N := by
    constructor
    · intro h
      exact ⟨by simpa using h i, fun k hk => by simpa [hk] using h k⟩
    · rintro ⟨hv, h⟩ k
      by_cases hk : k = i
      · simpa [hk] using hv
      · simpa [hk] using h k hk
  cases h with
  | invert i =>
    rw [upd]
    simp only [Subgroup.inv_mem_iff]
    grind
  | multiply i j hij =>
    rw [upd]
    constructor
    · intro hr
      exact ⟨N.mul_mem (hr i) (hr j), fun k _ => hr k⟩
    · rintro ⟨hp, ho⟩ k
      by_cases hk : k = i
      · subst k
        simpa using N.mul_mem hp (N.inv_mem (ho j hij.symm))
      · exact ho k hk
  | swap i j => exact (Equiv.swap i j).surjective.forall
  | conjugate i w =>
    rw [upd]
    have hc : w * r i * w⁻¹ ∈ N ↔ r i ∈ N := by
      constructor
      · intro h
        simpa [mul_assoc] using hn.conj_mem _ h w⁻¹
      · intro h
        exact hn.conj_mem _ h w
    rw [hc]
    grind

private theorem normal_eq {n} {r s : RelatorTuple n} (h : Equivalent r s) :
    Subgroup.normalClosure (Set.range r) = Subgroup.normalClosure (Set.range s) := by
  induction h with
  | rel r s h =>
    apply le_antisymm <;> apply Subgroup.normalClosure_le_normal <;> rintro _ ⟨k, rfl⟩
    · exact ((move_mem h (Subgroup.normalClosure (Set.range s))).mpr (fun j => Subgroup.subset_normalClosure ⟨j, rfl⟩)) k
    · exact ((move_mem h (Subgroup.normalClosure (Set.range r))).mp (fun j => Subgroup.subset_normalClosure ⟨j, rfl⟩)) k
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ik => exact ih.trans ik

/-- Realize an M-transformation by the four moves of the pinned definition. -/
theorem replace_mod_others {n} (r : RelatorTuple n) (i : Fin n)
    (v : FreeGroup (Fin n))
    (hv : (r i)⁻¹ * v ∈ Subgroup.normalClosure (r '' {j | j ≠ i})) :
    Equivalent r (update r i v) := by
  have shifts (a) (ha : a ∈ Subgroup.normalClosure (r '' {j | j ≠ i})) :
      ∀ x, Equivalent (update r i x) (update r i (x * a)) := by
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨_, ⟨j, hj, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp ha
      obtain ⟨w, rfl⟩ := isConj_iff.mp hconj
      change j ≠ i at hj
      intro x
      let u := update r i x
      let b := w * r j * w⁻¹
      have h₁ : Equivalent u (update u j b) := by
        simpa [u, b, hj] using step (Move.conjugate u j w)
      have h₂ := step (Move.multiply (update u j b) i j hj.symm)
      have h₃ := step (Move.conjugate (update r i (x * b)) j w)
      apply chain h₁
      apply chain _ (back (by simpa [b, hj] using h₃))
      simpa [u, hj, hj.symm, update_comm hj.symm] using h₂
    | one => intro x; rw [mul_one]; exact .refl _
    | mul a b _ _ ia ib =>
      intro x
      simpa [mul_assoc] using chain (ia x) (ib (x * a))
    | inv a _ ia =>
      intro x
      simpa using back (ia (x * a⁻¹))
  simpa using shifts _ hv (r i)

/-- Read a path as a list of forward moves. Undoing multiplication temporarily
inverts the multiplier and restores it after the multiplication. -/
private theorem forward_path {n} {r s : RelatorTuple n} (h : Equivalent r s) :
    ReflTransGen Move r s := by
  have undo {u v : RelatorTuple n} (m : Move u v) : ReflTransGen Move v u := by
    cases m with
    | invert i =>
      simpa using ReflTransGen.single (Move.invert (update u i (u i)⁻¹) i)
    | swap i j =>
      simpa using ReflTransGen.single (Move.swap (fun k => u (Equiv.swap i j k)) i j)
    | conjugate i w =>
      simpa [mul_assoc] using ReflTransGen.single
        (Move.conjugate (update u i (w * u i * w⁻¹)) i w⁻¹)
    | multiply i j hij =>
      let v := update u i (u i * u j)
      have h₁ := ReflTransGen.single (Move.invert v j)
      have h₂ := h₁.tail (Move.multiply _ i j hij)
      have h₃ := h₂.tail (Move.invert _ j)
      simpa [v, hij, hij.symm, update_comm hij] using h₃
  suffices ReflTransGen Move r s ∧ ReflTransGen Move s r from this.1
  induction h with
  | rel _ _ m => exact ⟨.single m, undo m⟩
  | refl => exact ⟨.refl, .refl⟩
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ik => exact ⟨ih.1.trans ik.1, ik.2.trans ih.2⟩

/-- Any path on the projected tail lifts, with the zeroth relator held fixed. -/
theorem lift_tail {n} (p : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin n))
    (hp : Surjective p) (r : RelatorTuple (n + 1)) {u : RelatorTuple n}
    (h : Equivalent (fun i => p (r i.succ)) u) :
    ∃ s, Equivalent r s ∧ s 0 = r 0 ∧ ∀ i, p (s i.succ) = u i := by
  have path := forward_path h
  clear h
  induction path with
  | refl => exact ⟨r, .refl _, rfl, fun _ => rfl⟩
  | tail path m ih =>
    obtain ⟨s, hs, hz, ht⟩ := ih
    have at_succ (i : Fin n) (v : FreeGroup (Fin (n + 1))) (k : Fin n) :
        p (update s i.succ v k.succ) = update (fun j => p (s j.succ)) i (p v) k := by
      by_cases hk : k = i <;> simp_all
    cases m with
    | invert i =>
      refine ⟨_, chain hs (step (Move.invert s i.succ)), by simpa [Ne.symm (Fin.succ_ne_zero i)] using hz, ?_⟩
      intro k
      rw [at_succ]
      simp only [ht, map_inv]
    | multiply i j hij =>
      refine ⟨_, chain hs (step (Move.multiply s i.succ j.succ (by simpa using hij))),
        by simpa [Ne.symm (Fin.succ_ne_zero i)] using hz, ?_⟩
      intro k
      rw [at_succ]
      simp only [ht, map_mul]
    | conjugate i w =>
      obtain ⟨v, rfl⟩ := hp w
      refine ⟨_, chain hs (step (Move.conjugate s i.succ v)), by simpa [Ne.symm (Fin.succ_ne_zero i)] using hz, ?_⟩
      intro k
      rw [at_succ]
      simp only [ht, map_mul, map_inv]
    | swap i j =>
      refine ⟨_, chain hs (step (Move.swap s i.succ j.succ)), by simpa [Equiv.swap_apply_def, Ne.symm (Fin.succ_ne_zero i), Ne.symm (Fin.succ_ne_zero j)] using hz, ?_⟩
      intro k
      by_cases hi : k = i
      · subst k
        simpa using ht j
      by_cases hj : k = j
      · subst k
        simpa using ht i
      simpa [Equiv.swap_apply_def, hi, hj] using ht k

private theorem projected_generates {n} (p : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin n))
    (hp : Surjective p) {r : RelatorTuple (n + 1)} (hr : NormallyGenerates r)
    (hz : p (r 0) = 1) : NormallyGenerates (fun i : Fin n => p (r i.succ)) := by
  have htop : (Subgroup.normalClosure (Set.range r)).map p = ⊤ := by
    rw [hr, Subgroup.map_top_of_surjective _ hp]
  rw [NormallyGenerates, ← top_le_iff, ← htop, Subgroup.map_normalClosure _ _ hp]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  refine Fin.cases ?_ (fun j => Subgroup.subset_normalClosure ⟨j, rfl⟩) i
  rw [hz]
  exact Subgroup.one_mem _

/-- With the missing generator fixed in slot zero, equality of projected
words is enough to replace each of the other relators by its generator. -/
theorem clear_kernel {n} (r : RelatorTuple (n + 1))
    (p : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin n))
    (pzero : p (FreeGroup.of 0) = 1)
    (psucc : ∀ j : Fin n, p (FreeGroup.of j.succ) = FreeGroup.of j)
    (hz : r 0 = FreeGroup.of 0)
    (ht : ∀ j : Fin n, p (r j.succ) = FreeGroup.of j) :
    Equivalent r (standardRelators _) := by
  let N := Subgroup.normalClosure ({FreeGroup.of (0 : Fin (n + 1))} : Set _)
  let q := QuotientGroup.mk' N
  let e := FreeGroup.map (Fin.succ : Fin n → Fin (n + 1))
  have factor : (q.comp e).comp p = q := by
    apply FreeGroup.ext_hom
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [MonoidHom.comp_apply, pzero, map_one]
      exact ((QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))).symm
    · simp [e, psucc]
  have hker (a) (ha : p a = 1) : a ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q a = 1
    rw [← factor, MonoidHom.comp_apply, ha, map_one]
  have clear_set (A : Finset (Fin (n + 1))) :
      Equivalent r (fun k => if k ∈ A then FreeGroup.of k else r k) := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty, if_false] using (show Equivalent r r from .refl _)
    | @insert i A hi ih =>
      let u : RelatorTuple (n + 1) := fun k => if k ∈ A then FreeGroup.of k else r k
      have u0 : u 0 = FreeGroup.of 0 := by simp [u, hz]
      have hnew : (fun k => if k ∈ insert i A then FreeGroup.of k else r k) =
          update u i (FreeGroup.of i) := by
        funext k
        by_cases hk : k = i <;> simp_all [u]
      rw [hnew]
      apply chain ih
      by_cases h0 : i = 0
      · subst i
        rw [← u0, update_eq_self]
        exact .refl _
      apply replace_mod_others
      have incl : ({FreeGroup.of (0 : Fin (n + 1))} : Set _) ⊆ u '' {j | j ≠ i} := by
        rintro _ ⟨⟩
        exact ⟨0, Ne.symm h0, u0⟩
      apply Subgroup.normalClosure_mono incl
      apply hker
      have heq : ∀ k, p (r k) = p (FreeGroup.of k) := by
        intro k
        exact Fin.cases (by rw [hz]) (fun j => (ht j).trans (psucc j).symm) k
      simp [hi, heq]
  change Equivalent r (fun k => FreeGroup.of k)
  simpa only [Finset.mem_univ, if_true] using clear_set Finset.univ

private theorem rank_one (r : RelatorTuple 1) (hr : NormallyGenerates r) :
    Equivalent r (standardRelators 1) := by
  let g := FreeGroup.of (0 : Fin 1)
  have hgen : Subgroup.zpowers g = ⊤ := by
    apply top_unique
    intro x _
    exact ⟨FreeGroup.equivIntOfUnique x, FreeGroup.equivIntOfUnique.left_inv x⟩
  have hrgen : Subgroup.zpowers (r 0) = ⊤ := by
    rw [← top_le_iff, ← hr]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    rw [Subsingleton.elim i 0]
    exact Subgroup.mem_zpowers _
  have hinj : Injective (fun k : ℤ => g ^ k) := FreeGroup.equivIntOfUnique.symm.injective
  rcases (Subgroup.zpowers_eq_zpowers_iff (injective_zpow_iff_not_isOfFinOrder.mp hinj)).mp
      (hgen.trans hrgen.symm) with h | h
  · have heq : r = standardRelators 1 := by
      funext i
      rw [Subsingleton.elim i 0]
      exact h.symm
    rw [heq]
    exact .refl _
  · have heq : update r 0 (r 0)⁻¹ = standardRelators 1 := by
      funext i
      rw [Subsingleton.elim i 0, update_self, ← h, inv_inv]
      rfl
    rw [← heq]
    exact step (Move.invert r 0)

/-- The rank-two projection step is unconditional. Multiply the second
relator by an integral power of the first, then interchange them. The
absolute value of the first projected exponent decreases by Euclidean division. -/
theorem zero_exponent (f : FreeGroup (Fin 2) →* Multiplicative ℤ)
    (r : RelatorTuple 2) : ∃ s, Equivalent r s ∧ (f (s 0)).toAdd = 0 := by
  let a := (f (r 0)).toAdd
  let b := (f (r 1)).toAdd
  by_cases ha : a = 0
  · exact ⟨r, .refl _, ha⟩
  let k := -(b / a)
  let t := update r 1 (r 1 * r 0 ^ k)
  have ht : Equivalent r t := by
    apply replace_mod_others
    simp only [inv_mul_cancel_left]
    apply Subgroup.zpow_mem
    exact Subgroup.subset_normalClosure ⟨0, by decide, rfl⟩
  let u := fun j => t (Equiv.swap 0 1 j)
  have hu : Equivalent r u := chain ht (step (Move.swap t 0 1))
  have he : (f (u 0)).toAdd = b % a := by
    simp only [u, t, Equiv.swap_apply_left, update_self, map_mul, map_zpow,
      toAdd_mul, Int.toAdd_zpow]
    change b + a * -(b / a) = b % a
    rw [Int.emod_def]
    ring
  have hlt : (f (u 0)).toAdd.natAbs < (f (r 0)).toAdd.natAbs := by
    change _ < a.natAbs
    rw [he]
    have h := (Int.emod_lt_abs b ha).trans_eq (Int.abs_eq_natAbs a)
    have hn := Int.emod_nonneg b ha
    omega
  obtain ⟨s, hus, hs⟩ := zero_exponent f u
  exact ⟨s, chain hu hus, hs⟩
termination_by (f (r 0)).toAdd.natAbs
decreasing_by exact hlt

/-- After erasing the first generator, the remaining relators can be made
to normally generate the smaller free group. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ r : RelatorTuple (n + 1), NormallyGenerates r →
    ∃ s, Equivalent r s ∧ NormallyGenerates
      (fun j : Fin n => FreeGroup.lift (Fin.cons 1 FreeGroup.of) (s j.succ))

/-- Suppose erasing the first generator already gives the tuple
`(1, x₁, …, xₙ)`. Find a representative whose first relator equals
the first generator in the group presented by the other relators. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ r : RelatorTuple (n + 1), NormallyGenerates r →
    (∀ i, FreeGroup.lift (Fin.cons 1 FreeGroup.of : Fin (n + 1) → FreeGroup (Fin n)) (r i) =
      (Fin.cons 1 FreeGroup.of : Fin (n + 1) → FreeGroup (Fin n)) i) →
    ∃ s, Equivalent r s ∧ (s 0)⁻¹ * FreeGroup.of 0 ∈
      Subgroup.normalClosure (Set.range (fun j : Fin n => s j.succ))

theorem main : H1 → H2 → type_of% @AndrewsCurtis.andrews_curtis_conjecture := by
  intro puncture extract n
  induction n with
  | zero =>
    intro r _
    have h : r = standardRelators 0 := funext (fun i => Fin.elim0 i)
    rw [h]
    exact .refl _
  | succ n ih =>
    intro r hr
    by_cases hn : n = 0
    · subst n
      exact rank_one r hr
    let p := FreeGroup.lift (Fin.cons 1 FreeGroup.of : Fin (n + 1) → FreeGroup (Fin n))
    have pzero : p (FreeGroup.of 0) = 1 := by simp [p]
    have psucc (j : Fin n) : p (FreeGroup.of j.succ) = FreeGroup.of j := by simp [p]
    have hp : Surjective p := by
      have h : p.comp (FreeGroup.map Fin.succ) = MonoidHom.id _ := by
        apply FreeGroup.ext_hom
        intro j
        simpa using psucc j
      exact fun w => ⟨_, DFunLike.congr_fun h w⟩
    obtain ⟨s, hrs, hs⟩ : ∃ s, Equivalent r s ∧
        NormallyGenerates (fun j : Fin n => p (s j.succ)) := by
      by_cases hone : n = 1
      · subst n
        let e : FreeGroup (Fin 1) ≃* Multiplicative ℤ := FreeGroup.mulEquivIntOfUnique
        obtain ⟨s, hrs, hzero⟩ := zero_exponent (e.toMonoidHom.comp p) r
        have hz : p (s 0) = 1 := by
          apply e.injective
          rw [map_one]
          exact Multiplicative.toAdd.injective hzero
        exact ⟨s, hrs, projected_generates p hp ((normal_eq hrs).symm.trans hr) hz⟩
      · exact puncture n (by omega) r hr
    let S := Set.range (fun j : Fin n => s j.succ)
    have others (t : RelatorTuple (n + 1)) :
        Set.range (fun j : Fin n => t j.succ) ⊆ t '' {j | j ≠ 0} := by
      rintro _ ⟨j, rfl⟩
      exact ⟨j.succ, Fin.succ_ne_zero _, rfl⟩
    have himage : (Subgroup.normalClosure S).map p = ⊤ := by
      rw [Subgroup.map_normalClosure _ _ hp, show S = Set.range (fun j : Fin n => s j.succ) from rfl, ← Set.range_comp']
      exact hs
    have hmem : (p (s 0))⁻¹ ∈ (Subgroup.normalClosure S).map p := by
      rw [himage]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwp⟩ := hmem
    let a := update s 0 (s 0 * w)
    have hsa : Equivalent s a := replace_mod_others s 0 _ (by
      simpa using Subgroup.normalClosure_mono (others s) hw)
    have ha0 : p (a 0) = 1 := by simp [a, hwp]
    have hat : NormallyGenerates (fun j : Fin n => p (a j.succ)) := by simpa [a] using hs
    obtain ⟨b, hab, hb0, hbt⟩ := lift_tail p hp a (ih _ hat)
    have hrb := chain hrs (chain hsa hab)
    have hb : NormallyGenerates b := (normal_eq hrb).symm.trans hr
    have hbp (i : Fin (n + 1)) : p (b i) = (Fin.cons 1 FreeGroup.of : Fin (n + 1) → FreeGroup (Fin n)) i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hb0] using ha0
      · simpa [standardRelators] using hbt j
    obtain ⟨t, hbt', ht⟩ := extract n (by omega) b hb hbp
    let c := update t 0 (FreeGroup.of 0)
    have htc : Equivalent t c := replace_mod_others t 0 _ (Subgroup.normalClosure_mono (others t) ht)
    have hrc := chain hrb (chain hbt' htc)
    have hc : NormallyGenerates c := (normal_eq hrc).symm.trans hr
    have hc0 : c 0 = FreeGroup.of 0 := update_self ..
    have hct := projected_generates p hp hc (by rw [hc0, pzero])
    obtain ⟨d, hcd, hd0, hdt⟩ := lift_tail p hp c (ih _ hct)
    exact chain hrc (chain hcd (clear_kernel d p pzero psucc (hd0.trans hc0) hdt))

end OMA.R_AndrewsCurtis_andrews_curtis_conjecture_R1
