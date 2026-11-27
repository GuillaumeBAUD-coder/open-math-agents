import OMAReductions.R_Green87_green_87_variants_exists_tendsto_R1

/-! # Conditioning on the orbit of a distinguished point -/
-- Credit: @steveDOTdigital
namespace OMA.PermutationCycles
open Equiv Finset
open scoped Classical

private def Stable {α : Type*} (p : Perm α) (s : Finset α) := ∀ x, p x ∈ s ↔ x ∈ s
private def Good {α : Type*} (p : Perm α) (k : ℕ) := ∃ s : Finset α, s.card = k ∧ Stable p s

private lemma image_iff {α : Type*} [DecidableEq α] (p : Perm α) (s : Finset α) :
    s.image p = s ↔ Stable p s := by
  constructor
  · intro e x
    calc
      p x ∈ s ↔ p x ∈ s.image p := by rw [e]
      _ ↔ _ := p.injective.mem_finset_image
  · intro h
    ext x
    constructor
    · rintro hx
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      exact (h a).mpr ha
    · intro hx
      exact mem_image.mpr ⟨p.symm x,(h (p.symm x)).mp (by simpa),p.apply_symm_apply x⟩

private lemma good_fin {n k : ℕ} (p : Perm (Fin n)) : Green87.FixesSet p k ↔ Good p k := by
  simp only [Green87.FixesSet,Good,image_iff]

private lemma good_map {U V : Type*} (f : U ≃ V) (g : Perm U) {k : ℕ}
    (h : Good g k) : Good (f.permCongr g) k := by
  classical
  obtain ⟨s,hc,hs⟩ := h
  refine ⟨s.map f.toEmbedding,by simpa,?_⟩
  intro v
  obtain ⟨a,rfl⟩ := f.surjective v
  simpa [Equiv.permCongr_apply] using hs a

private lemma good_congr {α β : Type*} (e : α ≃ β) (p : Perm α) (k : ℕ) :
    Good (e.permCongr p) k ↔ Good p k :=
  by
    have back : e.symm.permCongr (e.permCongr p) = p := by ext x; simp [Equiv.permCongr_apply]
    exact ⟨fun h => back ▸ good_map e.symm (e.permCongr p) h,good_map e p⟩

private noncomputable def orbit {α : Type*} [Fintype α] (p : Perm α) (a : α) : Finset α :=
  univ.filter fun x => p.SameCycle a x

private lemma orbit_mem {α : Type*} [Fintype α] (p : Perm α) (a x : α) :
    x ∈ orbit p a ↔ p.SameCycle a x := by simp [orbit]

private lemma orbit_cycle {α : Type*} [Fintype α] (p : Perm α) (a : α) :
    p.IsCycleOn (orbit p a : Set α) := by
  refine ⟨p.bijOn (fun x => ?_),?_⟩
  · change p x ∈ orbit p a ↔ x ∈ orbit p a
    simp only [orbit_mem,Perm.sameCycle_apply_right]
  · intro x hx y hy
    exact ((orbit_mem p a x).mp hx).symm.trans ((orbit_mem p a y).mp hy)

private lemma cycle_orbit {α : Type*} [Fintype α] (p : Perm α) (s : Finset α) (a : α)
    (ha : a ∈ s) (h : p.IsCycleOn (s : Set α)) : orbit p a = s := by
  ext x
  rw [orbit_mem]
  constructor
  · rintro ⟨i,rfl⟩
    exact (h.1.perm_zpow i).mapsTo ha
  · exact fun hx => h.2 ha hx

private noncomputable def leftPerm {α : Type*} (p : Perm α) (s : Finset α) (h : Stable p s) :
    Perm {x // x ∈ s} := p.subtypePerm h
private noncomputable def rightPerm {α : Type*} (p : Perm α) (s : Finset α) (h : Stable p s) :
    Perm {x // x ∉ s} := p.subtypePerm (fun x => (h x).not)

private lemma left_join {α : Type*} (s : Finset α)
    (p : Perm {x // x ∈ s}) (q : Perm {x // x ∉ s}) :
    Stable (p.subtypeCongr q) s := by
  intro x
  by_cases hx : x ∈ s
  · rw [Perm.subtypeCongr.left_apply p q hx]
    exact iff_of_true (p ⟨x,hx⟩).property hx
  · rw [Perm.subtypeCongr.right_apply p q hx]
    exact iff_of_false (q ⟨x,hx⟩).property hx

private lemma left_eq {α : Type*} (s : Finset α)
    (p : Perm {x // x ∈ s}) (q : Perm {x // x ∉ s}) :
    leftPerm (p.subtypeCongr q) s (left_join s p q) = p := by
  ext x
  exact Perm.subtypeCongr.left_apply_subtype p q x

private lemma right_eq {α : Type*} (s : Finset α)
    (p : Perm {x // x ∈ s}) (q : Perm {x // x ∉ s}) :
    rightPerm (p.subtypeCongr q) s (left_join s p q) = q := by
  ext x
  exact Perm.subtypeCongr.right_apply_subtype p q x

private lemma join_eq {α : Type*} (p : Perm α) (s : Finset α) (h : Stable p s) :
    (leftPerm p s h).subtypeCongr (rightPerm p s h) = p := by
  ext x
  by_cases hx : x ∈ s
  · rw [Perm.subtypeCongr.left_apply _ _ hx]; rfl
  · rw [Perm.subtypeCongr.right_apply _ _ hx]; rfl

private def Full {α : Type*} (p : Perm α) := ∀ x y : α, p.SameCycle x y

private lemma joined_cycle {α : Type*} (s : Finset α)
    (p : Perm {x // x ∈ s}) (q : Perm {x // x ∉ s}) (h : Full p) :
    (p.subtypeCongr q).IsCycleOn (s : Set α) := by
  refine ⟨(p.subtypeCongr q).bijOn (left_join s p q),?_⟩
  intro x hx y hy
  have hh := h ⟨x,hx⟩ ⟨y,hy⟩
  rw [← left_eq s p q] at hh
  exact Perm.sameCycle_subtypePerm.mp hh

set_option maxHeartbeats 1200000 in
private noncomputable def fiberEquiv {α : Type*} [Fintype α] (a : α) (s : Finset α) (ha : a ∈ s) :
    {p : Perm α // orbit p a = s} ≃
      {p : Perm {x // x ∈ s} // Full p} × Perm {x // x ∉ s} where
  toFun pp := by
    have cyc : pp.val.IsCycleOn (s : Set α) :=
      (congrArg (fun t : Finset α => pp.val.IsCycleOn (t : Set α)) pp.property).mp (orbit_cycle pp.val a)
    let h : Stable pp.val s := fun _ => cyc.apply_mem_iff
    exact (⟨leftPerm pp.val s h,fun x y => (cyc.2 x.property y.property).subtypePerm⟩,rightPerm pp.val s h)
  invFun d := ⟨d.1.val.subtypeCongr d.2,cycle_orbit _ s a ha (joined_cycle _ _ _ d.1.property)⟩
  left_inv pp := by
    apply Subtype.ext
    have cyc : pp.val.IsCycleOn (s : Set α) :=
      (congrArg (fun t : Finset α => pp.val.IsCycleOn (t : Set α)) pp.property).mp (orbit_cycle pp.val a)
    exact join_eq pp.val s (fun _ => cyc.apply_mem_iff)
  right_inv d := Prod.ext (Subtype.ext (left_eq s d.1.val d.2)) (right_eq s d.1.val d.2)

private lemma card_full {α : Type*} [Fintype α] [Nonempty α] :
    Nat.card {p : Perm α // Full p} = (Fintype.card α - 1).factorial := by
  classical
  by_cases nontr : Nontrivial α
  · let _ := nontr
    have equiv (p : Perm α) : Full p ↔ p.cycleType = {Fintype.card α} := by
      constructor
      · intro h
        have cycle : p.IsCycleOn Set.univ := ⟨p.bijOn (by simp),fun x _ y _ => h x y⟩
        have moved (x : α) : p x ≠ x := cycle.apply_ne Set.nontrivial_univ (Set.mem_univ x)
        have cyc : p.IsCycle := by
          obtain ⟨x⟩ := ‹Nonempty α›
          exact ⟨x,moved x,fun y _ => h x y⟩
        have supp : p.support = univ := by ext x; simp [Perm.mem_support,moved]
        rw [cyc.cycleType,supp,card_univ]
      · intro ht
        have cyc : p.IsCycle := Perm.card_cycleType_eq_one.mp (by rw [ht]; simp)
        have sc := cyc.cycleType
        rw [ht] at sc
        have num : p.support.card = Fintype.card α := by simpa using sc.symm
        have full := Finset.eq_univ_of_card p.support num
        intro x y
        apply cyc.sameCycle
        · apply Perm.mem_support.mp; rw [full]; simp
        · apply Perm.mem_support.mp; rw [full]; simp
    have e : {p : Perm α // Full p} ≃ ↥(univ.filter (fun p : Perm α => p.cycleType = {Fintype.card α})) :=
      Equiv.subtypeEquivRight (by intro p; simp [equiv])
    rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
    simpa using Perm.card_of_cycleType_singleton (α := α) (n := Fintype.card α)
      Fintype.one_lt_card le_rfl
  · have : Subsingleton α := not_nontrivial_iff_subsingleton.mp nontr
    have : Nonempty {p : Perm α // Full p} := ⟨⟨1,fun x y => (Subsingleton.elim x y).sameCycle _⟩⟩
    rw [Nat.card_unique,← Nat.card_eq_fintype_card,Nat.card_unique]; rfl

private lemma good_right {α : Type*} [Fintype α] (p : Perm α) (s : Finset α) (h : Stable p s)
    (k : ℕ) (g : Good (rightPerm p s h) k) : Good p k := by
  classical
  obtain ⟨U,hc,hs⟩ := g
  let e : {x // x ∉ s} ↪ α := Function.Embedding.subtype _
  refine ⟨U.map e,by simpa,?_⟩
  intro x
  by_cases hx : x ∈ s
  · have hp := (h x).mpr hx
    have outside (z : α) (hz : z ∈ s) : z ∉ U.map e := by
      intro hz'
      obtain ⟨v,_,rfl⟩ := mem_map.mp hz'
      exact v.property hz
    exact iff_of_false (outside _ hp) (outside x hx)
  · let v : {x // x ∉ s} := ⟨x,hx⟩
    change e (rightPerm p s h v) ∈ U.map e ↔ e v ∈ U.map e
    simpa only [Finset.mem_map'] using hs v

private lemma good_right_of_long {α : Type*} [Fintype α] (p : Perm α) (s : Finset α)
    (cyc : p.IsCycleOn (s : Set α)) (k : ℕ) (long : k < s.card)
    (g : Good p k) : Good (rightPerm p s (fun _ => cyc.apply_mem_iff)) k := by
  classical
  obtain ⟨U,hc,hs⟩ := g
  have dis : Disjoint s U := by
    refine disjoint_left.mpr ?_
    intro x hx hU
    have stable : Set.BijOn p (U : Set α) U := p.bijOn hs
    have sub : s ⊆ U := by
      intro y hy
      obtain ⟨z,rfl⟩ := cyc.2 hx hy
      exact (stable.perm_zpow z).mapsTo hU
    have := card_le_card sub
    omega
  let e : {x // x ∉ s} ↪ α := Function.Embedding.subtype _
  let T : Finset {x // x ∉ s} := univ.filter (fun x => x.val ∈ U)
  have eq : T.map e = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact (mem_filter.mp hv).2
    · intro hx
      exact mem_map.mpr ⟨⟨x,fun h => disjoint_left.mp dis h hx⟩,by simpa [T],rfl⟩
  refine ⟨T,by rw [←hc,←eq,card_map],?_⟩
  intro x
  simpa [T,rightPerm] using hs x.val

private noncomputable def goodCount (α : Type*) (k : ℕ) : ℕ :=
  Nat.card {p : Perm α // Good p k}

private lemma count_transport {α : Type*} [Fintype α] (k : ℕ) :
    goodCount α k = goodCount (Fin (Fintype.card α)) k := by
  classical
  let e := Fintype.equivFin α
  exact Nat.card_congr (e.permCongr.subtypeEquiv (fun p => (good_congr e p k).symm))

private lemma fraction (n k : ℕ) : Green87.i n k = (goodCount (Fin n) k : ℝ) / n.factorial := by
  classical
  have eq := Nat.card_congr (Equiv.subtypeEquivRight (fun p => @good_fin n k p))
  unfold Green87.i goodCount
  rw [eq,show Nat.card (Perm (Fin n)) = n.factorial by rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]]

private noncomputable def part {α : Type*} [Fintype α] (a : α) (s : Finset α) (k : ℕ) :
    Finset (Perm α) := univ.filter fun p => Good p k ∧ orbit p a = s

set_option maxHeartbeats 1000000 in
private lemma part_estimate {α : Type*} [Fintype α] (a : α) (s : Finset α) (ha : a ∈ s) (k : ℕ) :
    let L := (s.card - 1).factorial * goodCount (Fin (Fintype.card α - s.card)) k
    L ≤ (part a s k).card ∧ (part a s k).card ≤
      L + if s.card ≤ k then (s.card-1).factorial * (Fintype.card α - s.card).factorial else 0 := by
  classical
  let A := {p : Perm {x // x ∈ s} // Full p}
  let B := Perm {x // x ∉ s}
  let E := fiberEquiv a s ha
  let P (d : A × B) := Good (d.1.val.subtypeCongr d.2) k
  let Q (d : A × B) := Good d.2 k
  have rep : ↥(part a s k) ≃ {d : A × B // P d} := {
    toFun := fun w => by
      have h := (mem_filter.mp w.property).2
      let f : {p : Perm α // orbit p a = s} := ⟨w.val,h.2⟩
      refine ⟨E f,?_⟩
      change Good (E.symm (E f)).val k
      rw [E.symm_apply_apply]
      exact h.1
    invFun := fun d => ⟨(E.symm d.val).val,mem_filter.mpr ⟨mem_univ _,d.property,(E.symm d.val).property⟩⟩
    left_inv := fun w => by
      let f : {p : Perm α // orbit p a = s} := ⟨w.val,(mem_filter.mp w.property).2.2⟩
      apply Subtype.ext
      exact congrArg (fun t : {p : Perm α // orbit p a = s} => t.val) (E.symm_apply_apply f)
    right_inv := fun d => Subtype.ext (E.apply_symm_apply d.val) }
  have prodEquiv : {d : A × B // Q d} ≃ (A × {q : B // Good q k}) := {
    toFun := fun d => (d.val.1,⟨d.val.2,d.property⟩)
    invFun := fun d => ⟨(d.1,d.2.val),d.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have : Nonempty {x // x ∈ s} := ⟨⟨a,ha⟩⟩
  have ac : Nat.card A = (s.card-1).factorial := by simpa [A] using (card_full (α := ↥s))
  have bc : Fintype.card {x // x ∉ s} = Fintype.card α - s.card := by
    rw [Fintype.card_subtype_compl,Fintype.card_coe]
  have qc : Nat.card {d : A × B // Q d} = (s.card-1).factorial *
      goodCount (Fin (Fintype.card α - s.card)) k := by
    rw [Nat.card_congr prodEquiv,Nat.card_prod,ac]
    change _ * goodCount {x // x ∉ s} _ = _
    rw [count_transport (α := {x // x ∉ s}),bc]
  have pc : (part a s k).card = Nat.card {d : A × B // P d} := by
    rw [← Nat.card_congr rep,Nat.card_eq_fintype_card,Fintype.card_coe]
  have tot : Nat.card (A × B) = (s.card-1).factorial * (Fintype.card α - s.card).factorial := by
    rw [Nat.card_prod,ac,show Nat.card B = (Fintype.card {x // x ∉ s}).factorial by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_perm,bc]
  have incl (d : A × B) (h : Q d) : P d := by
    apply good_right (d.1.val.subtypeCongr d.2) s (left_join s _ _) k
    rw [right_eq]
    exact h
  have mono (S T : A × B → Prop) (h : ∀ d, S d → T d) :
      Nat.card {d // S d} ≤ Nat.card {d // T d} :=
    Nat.card_le_card_of_injective (fun d => (⟨d.val,h _ d.property⟩ : {d // T d}))
      (fun _ _ e => Subtype.ext (congrArg (fun t : {d // T d} => t.val) e))
  change _ ≤ _ ∧ _ ≤ _
  rw [pc,← qc]
  refine ⟨mono Q P incl,?_⟩
  split_ifs with short
  · have cap := Nat.card_le_card_of_injective (Subtype.val : {d // P d} → A × B) Subtype.val_injective
    rw [tot] at cap
    omega
  · rw [Nat.add_zero]
    apply mono P Q
    intro d h
    have exactOn := good_right_of_long (d.1.val.subtypeCongr d.2) s
      (joined_cycle _ _ _ d.1.property) k (by omega) h
    simpa only [right_eq] using exactOn

-- Partition by the other points in the pivot cycle, then by their number.
private noncomputable def layer {α : Type*} [Fintype α] [DecidableEq α] (a : α) (k l : ℕ) : ℕ :=
  ∑ T ∈ ((univ : Finset α).erase a).powersetCard l, (part a (insert a T) k).card

private lemma sum_layers {α : Type*} [Fintype α] [DecidableEq α] (a : α) (k : ℕ) :
    goodCount α k = ∑ l ∈ range (Fintype.card α), layer a k l := by
  classical
  let B := (univ : Finset α).erase a
  let D := univ.filter (fun p : Perm α => Good p k)
  let f := fun p : Perm α => (orbit p a).erase a
  have inB (p : Perm α) : f p ⊆ B := by
    intro x hx
    exact mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_univ _⟩
  have dc : goodCount α k = D.card := by
    let e : {p : Perm α // Good p k} ≃ ↥D := Equiv.subtypeEquivRight (by intro p; simp [D])
    rw [goodCount,Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
  have parts (T : Finset α) (ht : T ∈ B.powerset) :
      D.filter (fun p => f p = T) = part a (insert a T) k := by
    have sub := mem_powerset.mp ht
    have na : a ∉ T := fun ha => notMem_erase a _ (sub ha)
    ext p
    have o : a ∈ orbit p a := (orbit_mem _ _ _).mpr (Perm.SameCycle.refl _ _)
    have iff' : f p = T ↔ orbit p a = insert a T := by
      constructor
      · intro h
        rw [← h,show insert a (f p) = orbit p a from insert_erase o]
      · intro h
        simp [f,h,na]
    simp [D,part,iff']
  have groups (T : Finset α) (h : T ∈ B.powerset) : T.card ∈ range (Fintype.card α) := by
    have hle := card_le_card (mem_powerset.mp h)
    have bcard : B.card + 1 = Fintype.card α := by simpa [B] using card_erase_add_one (s := (univ : Finset α)) (mem_univ a)
    exact mem_range.mpr (by omega)
  have block (l : ℕ) : B.powerset.filter (fun T => T.card = l) = B.powersetCard l := by
    ext T
    simp
  rw [dc,card_eq_sum_card_fiberwise (f := f) (t := B.powerset) (fun p _ => mem_powerset.mpr (inB p))]
  calc
    _ = ∑ T ∈ B.powerset, (part a (insert a T) k).card := sum_congr rfl (fun T h => congrArg Finset.card (parts T h))
    _ = _ := by
      rw [← sum_fiberwise_of_maps_to groups (fun T => (part a (insert a T) k).card)]
      simp only [block]
      rfl

private lemma layer_bounds (n k l : ℕ) (hl : l ≤ n) :
    let N := n.choose l * l.factorial * goodCount (Fin (n-l)) k
    N ≤ layer (0 : Fin (n+1)) k l ∧ layer (0 : Fin (n+1)) k l ≤
      N + if l < k then n.factorial else 0 := by
  classical
  let a : Fin (n+1) := 0
  let B := (univ : Finset (Fin (n+1))).erase a
  let S := B.powersetCard l
  let base := l.factorial * goodCount (Fin (n-l)) k
  let extra := if l < k then l.factorial * (n-l).factorial else 0
  have bcard : B.card = n := by simp [B]
  have sc : S.card = n.choose l := by simp [S,bcard]
  have block (T : Finset (Fin (n+1))) (h : T ∈ S) :
      base ≤ (part a (insert a T) k).card ∧ (part a (insert a T) k).card ≤ base + extra := by
    obtain ⟨sub,eq⟩ := mem_powersetCard.mp h
    have na : a ∉ T := fun ha => notMem_erase a _ (sub ha)
    have c : (insert a T).card = l+1 := by rw [card_insert_of_notMem na,eq]
    simpa [base,extra,c,Nat.succ_le_iff] using part_estimate a (insert a T) (mem_insert_self ..) k
  have sums := And.intro (sum_le_sum (fun T (h : T ∈ S) => (block T h).1))
    (sum_le_sum (fun T (h : T ∈ S) => (block T h).2))
  have ef : S.card * extra = if l < k then n.factorial else 0 := by
    rw [sc]
    dsimp only [extra]
    split_ifs
    · rw [←Nat.mul_assoc,Nat.choose_mul_factorial_mul_factorial hl]
    · simp
  change _ ≤ ∑ T ∈ S, _ ∧ (∑ T ∈ S, _) ≤ _
  rw [sc] at ef
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_add,sc,ef,base,Nat.mul_assoc] using sums

private lemma probability_layer (n k l : ℕ) (hl : l ≤ n) :
    Green87.i (n-l) k ≤ (layer (0 : Fin (n+1)) k l : ℝ) / n.factorial ∧
    (layer (0 : Fin (n+1)) k l : ℝ) / n.factorial ≤ Green87.i (n-l) k + if l < k then 1 else 0 := by
  let L := n.choose l * l.factorial * goodCount (Fin (n-l)) k
  have norm : (L : ℝ) / n.factorial = Green87.i (n-l) k := by
    rw [fraction]
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have h : L * (n-l).factorial = goodCount (Fin (n-l)) k * n.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hl]
      dsimp [L]
      ring
    exact_mod_cast h
  obtain ⟨low,high⟩ := layer_bounds n k l hl
  change L ≤ _ at low
  change _ ≤ L + _ at high
  rw [← norm]
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast low) (by positivity)
  · split_ifs with small
    · rw [show (1:ℝ) = (n.factorial : ℝ)/n.factorial by exact (div_self (by positivity)).symm,← add_div]
      simp only [if_pos small] at high
      exact div_le_div_of_nonneg_right (by exact_mod_cast high) (by positivity)
    · simp only [if_neg small,Nat.add_zero] at high
      rw [add_zero]
      exact div_le_div_of_nonneg_right (by exact_mod_cast high) (by positivity)

private lemma condition (k n : ℕ) : |(n : ℝ) * Green87.i n k - ∑ j ∈ range n, Green87.i j k| ≤ k := by
  cases n with
  | zero => simp
  | succ n =>
    let b (l : ℕ) := (layer (0 : Fin (n+1)) k l : ℝ) / n.factorial
    have scale : ((n+1 : ℕ) : ℝ) * Green87.i (n+1) k = ∑ l ∈ range (n+1), b l := by
      rw [fraction,show goodCount (Fin (n+1)) k = ∑ l ∈ range (n+1), layer (0 : Fin (n+1)) k l by
        simpa only [Fintype.card_fin] using sum_layers (0 : Fin (n+1)) k]
      simp only [b,Nat.cast_sum,←sum_div,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      field_simp
    have reflect : (∑ l ∈ range (n+1), Green87.i (n-l) k) = ∑ j ∈ range (n+1), Green87.i j k := by
      simpa only [Nat.add_sub_cancel] using sum_range_reflect (fun j => Green87.i j k) (n+1)
    have lo : (∑ j ∈ range (n+1), Green87.i j k) ≤ ∑ l ∈ range (n+1), b l := by
      rw [← reflect]
      exact sum_le_sum (fun l hl => (probability_layer n k l (by simpa using hl)).1)
    have hi : (∑ l ∈ range (n+1), b l) ≤ ∑ l ∈ range (n+1), (Green87.i (n-l) k + if l < k then 1 else 0) :=
      sum_le_sum (fun l hl => (probability_layer n k l (by simpa using hl)).2)
    rw [sum_add_distrib,reflect] at hi
    have short : (∑ l ∈ range (n+1), if l < k then (1:ℝ) else 0) ≤ k := by
      rw [←sum_filter]
      simp only [sum_const,nsmul_eq_mul,mul_one]
      have subset : (range (n+1)).filter (fun l => l < k) ⊆ range k :=
        fun _ h => mem_range.mpr (mem_filter.mp h).2
      exact_mod_cast (show ((range (n+1)).filter (fun l => l < k)).card ≤ k by simpa using card_le_card subset)
    rw [scale,abs_of_nonneg (sub_nonneg.mpr lo)]
    linarith

end OMA.PermutationCycles

theorem OMA.solution : OMA.R_Green87_green_87_variants_exists_tendsto_R1.H1 := OMA.PermutationCycles.condition
