import OMAReductions.R_Erdos626_erdos_626_variants_h_odd_conjecture_R1

/-! This proof reuses the finite sparse-graph lemma from Erdős #667,
proved by steveDOTdigital in proofs/Erdos667.erdos_667.variants.ramsey_bounds.R1.H2.R1.H1.lean.
The parameter bounds here hold for every sufficiently large number of vertices. -/

namespace OMA.SparseRamsey
open Finset
open scoped Classical

private noncomputable def mass {Ω : Type*} (P : Ω → Prop) : ℝ := Nat.card {a // P a}
private def fixed {E C : Type*} (D : Finset E) (L : Finset C) (f : E → C) :=
  ∀ e ∈ D, f e ∈ L

-- Split a coloring into its coordinates on D and the other coordinates. The condition P
-- is determined by the latter. Every allowed assignment on D has the same number of extensions.
private lemma independent {E C : Type*} [Fintype E] [Fintype C] [Inhabited C]
    (D : Finset E) (L : Finset C) (P : (E → C) → Prop)
    (determined : ∀ f g, (∀ i ∉ D, f i=g i) → (P f ↔ P g)) :
    mass (fun f => P f ∧ fixed D L f) * (Fintype.card C : ℝ)^D.card =
      mass P * (L.card : ℝ)^D.card := by
  classical
  let A := {i // i ∈ D}
  let B := {i // i ∉ D}
  let fill (h : B → C) (i : E) := if hm : i ∈ D then default else h ⟨i,hm⟩
  let tail := {h : B → C // P (fill h)}
  have count (K : Finset C) :
      Nat.card {f : E → C // P f ∧ fixed D K f} = K.card^D.card * Nat.card tail := by
    let equiv : {f : E → C // P f ∧ fixed D K f} ≃ (A → ↥K) × tail := {
      toFun := fun f => (fun e => ⟨f.val e,f.property.2 e e.property⟩,
        ⟨fun i => f.val i,(determined f.val _ (by intro i hi; simp [fill,hi])).mp f.property.1⟩)
      invFun := fun x => by
        let f (i : E) := if hi : i ∈ D then (x.1 ⟨i,hi⟩).val else x.2.val ⟨i,hi⟩
        refine ⟨f,(determined f (fill x.2.val) (by intro i hi; simp [f,fill,hi])).mpr x.2.property,?_⟩
        intro i hi; simpa [f,hi] using (x.1 ⟨i,hi⟩).property
      left_inv := fun f => by apply Subtype.ext; funext i; by_cases h : i ∈ D <;> simp [h]
      right_inv := fun x => by
        apply Prod.ext
        · funext i; apply Subtype.ext; simp [i.property]
        · apply Subtype.ext; funext i; simp [i.property] }
    rw [Nat.card_congr equiv,Nat.card_prod,Nat.card_eq_fintype_card (α := A → ↥K),Fintype.card_fun]
    simp [A]
  have eq : Nat.card {f : E → C // P f ∧ fixed D univ f} = Nat.card {f // P f} :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro f; simp [fixed]))
  have pt := count univ
  rw [eq,card_univ] at pt
  unfold mass
  rw [count L,pt]
  push_cast
  ring

private def avoid {I Ω : Type*} (A : I → Ω → Prop) (S : Finset I) (w : Ω) := ∀ i ∈ S, ¬A i w

private lemma mass_le {Ω : Type*} [Finite Ω] {P Q : Ω → Prop} (incl : ∀ w, P w → Q w) :
    mass P ≤ mass Q := by
  unfold mass
  exact_mod_cast Nat.card_le_card_of_injective
    (fun z : {w // P w} => (⟨z.val,incl _ z.property⟩ : {w // Q w}))
    (fun _ _ h => Subtype.ext (congrArg (fun a : {w // Q w} => a.val) h))

private lemma mass_split {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    mass (fun w => P w ∧ Q w) + mass (fun w => P w ∧ ¬Q w) = mass P := by
  classical
  let e : {w // P w ∧ Q w} ⊕ {w // P w ∧ ¬Q w} ≃ {w // P w} := {
    toFun := Sum.elim (fun w => ⟨w.val,w.property.1⟩) (fun w => ⟨w.val,w.property.1⟩)
    invFun := fun w => if h : Q w.val then .inl ⟨w.val,w.property,h⟩ else .inr ⟨w.val,w.property,h⟩
    left_inv := by rintro (w|w) <;> simp [w.property.2]
    right_inv := by intro w; by_cases h : Q w.val <;> simp [h] }
  have := Nat.card_congr e
  rw [Nat.card_sum] at this
  unfold mass
  exact_mod_cast this

private lemma avoid_insert {I Ω : Type*} [Fintype Ω] [DecidableEq I] (A : I → Ω → Prop) (i : I) (S : Finset I) :
    mass (fun w => avoid A S w ∧ A i w) + mass (avoid A (insert i S)) = mass (avoid A S) := by
  have e : avoid A (insert i S) = fun w => avoid A S w ∧ ¬A i w := by
    funext w; apply propext; simp [avoid,and_comm]
  rw [e]
  exact mass_split _ _

-- Restore the events of K one by one. Each restored condition keeps fraction c.
private lemma extend_mass {I : Type*} [DecidableEq I] (W : Finset I → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (T K : Finset I) (dis : Disjoint T K)
    (step : ∀ U, U ⊂ T ∪ K → ∀ i ∉ U, c*W U ≤ W (insert i U)) :
    c^K.card*W T ≤ W (T ∪ K) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
    have di := Finset.disjoint_insert_right.mp dis
    have ni : i ∉ T ∪ K := by simp [di.1,hi]
    have eq : T ∪ insert i K = insert i (T ∪ K) := by ext; simp
    have st : T ∪ K ⊂ T ∪ insert i K := by rw [eq]; exact Finset.ssubset_insert ni
    have old := ih di.2 (fun U hu => step U (hu.trans st))
    rw [Finset.card_insert_of_notMem hi,pow_succ,eq]
    calc
      _ = c*(c^K.card*W T) := by ring
      _ ≤ c*W (T ∪ K) := mul_le_mul_of_nonneg_left old hc
      _ ≤ _ := step _ st i ni

-- For i outside S, condition first on the events of S not meeting i, where i is
-- independent. Induction bounds the cost of restoring the events that do meet i.
private lemma conditional {I Ω : Type*} [Fintype Ω] [DecidableEq I] (A : I → Ω → Prop)
    (near : I → I → Bool) (D : ℕ) (x β : ℝ) (hx : 0≤x) (hx' : x<1)
    (cap : β ≤ x*(1-x)^D) (count : ∀ i (S : Finset I), i ∉ S → (S.filter (fun j => near i j)).card ≤ D)
    (indep : ∀ i (S : Finset I), i ∉ S →
      mass (fun w => avoid A S w ∧ A i w) ≤ β * mass (avoid A (S.filter fun j => !(near i j)))):
    ∀ (S : Finset I) i, i ∉ S → (1-x)*mass (avoid A S) ≤ mass (avoid A (insert i S)) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    let T := S.filter (fun j => !(near i j))
    let K := S.filter (fun j => near i j)
    have dis : Disjoint T K := by
      apply disjoint_left.mpr
      intro j ht hk
      have a := (mem_filter.mp ht).2
      have b := (mem_filter.mp hk).2
      simp [b] at a
    have both : T ∪ K = S := by ext j; by_cases a : near i j <;> simp [T,K,a]
    have c0 : 0 ≤ 1-x := by linarith
    have restore := extend_mass (fun s => mass (avoid A s)) c0 T K dis
      (fun U hu j hj => ih U (both ▸ hu) j hj)
    rw [both] at restore
    have pD : (1-x)^D ≤ (1-x)^K.card := pow_le_pow_of_le_one c0 (by linarith) (count i S hi)
    have cap' := cap.trans (mul_le_mul_of_nonneg_left pD hx)
    have tn : 0 ≤ mass (avoid A T) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right cap' tn
    have h2 := mul_le_mul_of_nonneg_left restore hx
    have prob := indep i S hi
    change _ ≤ β * mass (avoid A T) at prob
    have split := avoid_insert A i S
    nlinarith only [h1,h2,prob,split]

private noncomputable def touch {E : Type*} (D T : Finset E) : Bool :=
  decide (¬Disjoint D T)

private lemma color_bound {E C I : Type*} [Fintype E] [Fintype C] [Inhabited C]
    (support : I → Finset E) (labels : I → Finset C) (S : Finset I) (D : Finset E) (L : Finset C) :
    let A := fun i => fixed (support i) (labels i)
    let T := S.filter (fun j => !(touch D (support j)))
    mass (fun f => avoid A S f ∧ fixed D L f) * (Fintype.card C : ℝ)^D.card ≤
      mass (avoid A T) * (L.card : ℝ)^D.card := by
  classical
  let A := fun i => fixed (support i) (labels i)
  let T := S.filter (fun j => !(touch D (support j)))
  have det (f g : E → C) (eq : ∀ i ∉ D, f i=g i) : avoid A T f ↔ avoid A T g := by
    have same (j : I) (hj : j ∈ T) : A j f ↔ A j g := by
      have dis : Disjoint D (support j) := by simpa [touch] using (mem_filter.mp hj).2
      have v (i : E) (hi : i ∈ support j) : f i=g i := eq i (fun h => disjoint_left.mp dis h hi)
      constructor <;> intro h i hi
      · rw [←v i hi]; exact h i hi
      · rw [v i hi]; exact h i hi
    exact ⟨fun h j hj => (same j hj).not.mp (h j hj),fun h j hj => (same j hj).not.mpr (h j hj)⟩
  have sub : mass (fun f => avoid A S f ∧ fixed D L f) ≤ mass (fun f => avoid A T f ∧ fixed D L f) :=
    mass_le (fun _ h => ⟨fun j hj => h.1 j (mem_filter.mp hj).1,h.2⟩)
  exact (mul_le_mul_of_nonneg_right sub (by positivity)).trans_eq (independent D L _ det)

private lemma overlap_count {n p : ℕ} (U : Finset (Fin n)) (S : Finset {s : Finset (Fin n) // s.card=p}) :
    (S.filter fun j => touch (U.powersetCard 2) (j.val.powersetCard 2)).card ≤ U.card^2*n^(p-2) := by
  classical
  let K := S.filter (fun j => touch (U.powersetCard 2) (j.val.powersetCard 2))
  let pairs := U.powersetCard 2
  let rest := (univ : Finset (Fin n)).powersetCard (p-2)
  let union := fun et : Finset (Fin n) × Finset (Fin n) => et.1 ∪ et.2
  have sub : K.image Subtype.val ⊆ (pairs ×ˢ rest).image union := by
    rintro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    have ov : ¬Disjoint (U.powersetCard 2) (j.val.powersetCard 2) := by simpa [touch] using (mem_filter.mp hj).2
    obtain ⟨v,hv,hjv⟩ := not_disjoint_iff.mp ov
    obtain ⟨vj,vc⟩ := mem_powersetCard.mp hjv
    have rem : j.val \ v ∈ rest := mem_powersetCard.mpr ⟨subset_univ _,by rw [card_sdiff_of_subset vj,j.property,vc]⟩
    exact mem_image.mpr ⟨(v,j.val \ v),mem_product.mpr ⟨hv,rem⟩,Finset.union_sdiff_of_subset vj⟩
  calc
    _ = (K.image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((pairs ×ˢ rest).image union).card := card_le_card sub
    _ ≤ pairs.card*rest.card := by rw [←card_product]; exact card_image_le
    _ ≤ _ := by simpa [pairs,rest] using Nat.mul_le_mul (Nat.choose_le_pow U.card 2) (Nat.choose_le_pow n (p-2))

private lemma blank {Ω I : Type*} [Fintype Ω] [Nonempty Ω] (A : I → Ω → Prop) :
    0 < mass (avoid A ∅) := by
  have : Nonempty {w // avoid A ∅ w} := ⟨⟨Classical.arbitrary Ω,by simp [avoid]⟩⟩
  unfold mass
  exact_mod_cast (Nat.card_pos (α := {w // avoid A ∅ w}))

private lemma union_bound {Ω I : Type*} [Fintype Ω] (A : I → Ω → Prop) (P : Ω → Prop) (S : Finset I) :
    mass (fun w => P w ∧ ∃ i ∈ S, A i w) ≤ ∑ i ∈ S, mass (fun w => P w ∧ A i w) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : IsEmpty {w // P w ∧ ∃ i ∈ (∅ : Finset I), A i w} :=
      ⟨fun w => by simpa using w.property.2⟩
    simp [mass]
  | @insert i T hi ih =>
    rw [sum_insert hi]
    let Q := fun w => P w ∧ ∃ j ∈ insert i T, A j w
    have eq := mass_split Q (A i)
    have a : mass (fun w => Q w ∧ A i w) ≤ mass (fun w => P w ∧ A i w) := mass_le (fun _ h => ⟨h.1.1,h.2⟩)
    have b : mass (fun w => Q w ∧ ¬A i w) ≤ mass (fun w => P w ∧ ∃ j ∈ T, A j w) := by
      apply mass_le
      rintro w ⟨⟨pw,j,hj,aj⟩,na⟩
      exact ⟨pw,j,(mem_insert.mp hj).resolve_left (fun e => na (e ▸ aj)),aj⟩
    exact eq.ge.trans (add_le_add a (b.trans ih))

private lemma bernoulli (c : ℝ) (_hc : 0≤c) (hc' : c≤1) (k : ℕ) : 1-(k:ℝ)*c ≤ (1-c)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Nat.cast_succ]
    nlinarith only [mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hc'),mul_nonneg (Nat.cast_nonneg k) (sq_nonneg c)]

private lemma log_keep (x : ℝ) (hx : 0≤x) (half : x≤1/2) : -2*x ≤ Real.log (1-x) := by
  have pos : 0<1-x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [Real.log_inv] at h
  have inv : (1-x)⁻¹ ≤ 1+2*x := (inv_le_iff_one_le_mul₀ pos).mpr (by
    nlinarith [mul_nonneg hx (show 0≤1-2*x by linarith)])
  linarith

private lemma estimates (p n B m : ℕ) (hp : 3≤p) (pn : p≤n) (hb : 2≤B) (hm : 3≤ m)
    (degree : 64*p^2*n^(p-2) ≤ B^(p.choose 2-1))
    (size : 32*(B:ℝ)*(Real.log n+1) ≤ m) :
    let β := 1/(B:ℝ)^(p.choose 2)
    0<β ∧ 2*β≤1/2 ∧ β ≤ 2*β*(1-2*β)^(p^2*n^(p-2)) ∧
    ∀ k : ℕ, k≤ m^2*n^(p-2) →
      (n:ℝ)^m * (((B:ℝ)-1)/B)^(m.choose 2) < (1-2*β)^k := by
  let z := (B:ℝ)^(p.choose 2)
  let a := (n:ℝ)^(p-2)
  let d := p^2*n^(p-2)
  have B2 : (2:ℝ)≤B := by exact_mod_cast hb
  have p3 : (3:ℝ)≤p := by exact_mod_cast hp
  have m3 : (3:ℝ)≤ m := by exact_mod_cast hm
  have a1 : 1≤a := one_le_pow₀ (by exact_mod_cast (show 1≤n by omega))
  have bz : 0<(B:ℝ) := by linarith
  have zpos : 0<z := pow_pos bz _
  have hdeg : 64*(p:ℝ)^2*a ≤ (B:ℝ)^(p.choose 2-1) := by dsimp [a]; exact_mod_cast degree
  have rpos := Nat.choose_pos (show 2≤p by omega)
  have eq : (B:ℝ)^(p.choose 2-1)*(B:ℝ)=z := by rw [←pow_succ,Nat.sub_add_cancel rpos]
  have total : 64*(p:ℝ)^2*a*B ≤ z := (mul_le_mul_of_nonneg_right hdeg bz.le).trans_eq eq
  have dre : (d:ℝ)=(p:ℝ)^2*a := by simp [d,a]
  have p1 : 1≤(p:ℝ)^2 := one_le_pow₀ (by linarith)
  have d1 : 1≤(d:ℝ) := by rw [dre]; exact one_le_mul_of_one_le_of_one_le p1 a1
  have rel : 64*(d:ℝ)*B≤z := by rw [dre]; linarith only [total]
  have h4 : 4≤z := by nlinarith [mul_le_mul_of_nonneg_left B2 (by positivity : 0≤(d:ℝ))]
  have hz : 0 < 1/z := by positivity
  have half : 2*(1/z) ≤ 1/2 := by rw [←mul_div_assoc, mul_one]; apply (div_le_iff₀ zpos).mpr; linarith
  have tiny : (d:ℝ)*(2*(1/z)) ≤ 1/2 := by
    rw [show (d:ℝ)*(2*(1/z))=2*d/z by ring]
    apply (div_le_iff₀ zpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left B2 (by positivity : 0≤(d:ℝ))]
  change 0<1/z ∧ _ ∧ _ ∧ _
  refine ⟨hz,half,?_,?_⟩
  · have bern := bernoulli (2*(1/z)) (by positivity) (by linarith) d
    change 1/z ≤ 2*(1/z)*(1-2*(1/z))^d
    have hh : (1:ℝ)/2 ≤ (1-2*(1/z))^d := by linarith only [bern,tiny]
    nlinarith only [mul_le_mul_of_nonneg_left hh hz.le]
  · intro k hk
    have cap : (k:ℝ)≤(m:ℝ)^2*a := by dsimp [a]; exact_mod_cast hk
    have un : 0<((B:ℝ)-1)/B := div_pos (by linarith) bz
    have keep : 0<1-2*(1/z) := by linarith
    have nn : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    apply (Real.log_lt_log_iff (mul_pos (pow_pos nn _) (pow_pos un _)) (pow_pos keep _)).mp
    rw [Real.log_mul (pow_pos nn _).ne' (pow_pos un _).ne',Real.log_pow,Real.log_pow,Real.log_pow]
    have lb := log_keep (2*(1/z)) (by positivity) half
    have lu := Real.log_le_sub_one_of_pos un
    have eu : ((B:ℝ)-1)/B-1 = -(1/B) := by field_simp; ring
    rw [eu] at lu
    have right := mul_le_mul_of_nonneg_left lb (Nat.cast_nonneg k)
    have left := mul_le_mul_of_nonneg_left lu (Nat.cast_nonneg (m.choose 2))
    have mpos : 0<(m:ℝ) := by linarith
    have term : 32*(m:ℝ)*Real.log n*B ≤ (m:ℝ)^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left size mpos.le,mul_nonneg mpos.le bz.le]
    have cb : 64*a*B ≤ z := by
      have da : a ≤ (d:ℝ) := by rw [dre]; nlinarith only [mul_le_mul_of_nonneg_right p1 (le_trans (by norm_num) a1)]
      nlinarith only [mul_le_mul_of_nonneg_right da bz.le,rel]
    have err : 64*(k:ℝ)*B/z ≤ (m:ℝ)^2 := by
      apply (div_le_iff₀ zpos).mpr
      nlinarith only [mul_le_mul_of_nonneg_right cap bz.le,mul_le_mul_of_nonneg_left cb (sq_nonneg (m:ℝ))]
    have comb := Nat.add_one_mul_choose_eq (m-1) 1
    rw [Nat.sub_add_cancel (by omega : 1≤ m),Nat.choose_one_right] at comb
    have mc : (m:ℝ)*((m:ℝ)-1) = (m.choose 2 : ℝ)*2 := by
      have hcast := congrArg (fun v : ℕ => (v:ℝ)) comb
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1≤ m by omega),Nat.cast_one,Nat.reduceAdd,Nat.cast_ofNat] using hcast
    have gap : (m:ℝ)*Real.log n*B + 4*(k:ℝ)*B/z < m.choose 2 := by
      rw [div_eq_mul_inv] at err ⊢
      nlinarith only [term,err,mc,m3,mul_le_mul_of_nonneg_left m3 mpos.le]
    have final : (m:ℝ)*Real.log n + (m.choose 2 : ℝ)*(-(1/B)) < (k:ℝ)*(-2*(2*(1/z))) := by
      apply (mul_lt_mul_iff_left₀ bz).mp
      field_simp [bz.ne',zpos.ne'] at gap ⊢
      nlinarith only [gap]
    linarith only [left,right,final]

private lemma coloring (p n B m : ℕ)
    (hp : 3 ≤ p) (pn : p ≤ n) (hb : 2 ≤ B) (hm : 3 ≤ m) (mn : m ≤ n)
    (degree : 64*p^2*n^(p-2) ≤ B^(p.choose 2-1))
    (size : 32*(B:ℝ)*(Real.log n+1) ≤ m) :
    ∃ G : SimpleGraph (Fin n), (∀ s : Finset (Fin n), s.card = p → 1 ≤ (G.induce s).edgeSet.ncard) ∧ G.CliqueFree (m+1) := by
  classical
  have : NeZero B := ⟨by omega⟩
  let E := Finset (Fin n)
  let Ω := E → Fin B
  let I := {s : E // s.card=p}
  let support (j : I) := j.val.powersetCard 2
  let red := ({0} : Finset (Fin B))
  let blue := (univ : Finset (Fin B)).erase 0
  let A (j : I) := fixed (support j) red
  let adjacent (i j : I) := touch (support i) (support j)
  let W (S : Finset I) := mass (avoid A S)
  let β := 1/(B:ℝ)^(p.choose 2)
  let x := 2*β
  let d := p^2*n^(p-2)
  have Bpos : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  obtain ⟨βpos,half,redEst,blueEst⟩ := estimates p n B m hp pn hb hm degree size
  change 0<β at βpos
  change x ≤ 1/2 at half
  have x0 : 0 ≤ x := by dsimp [x]; linarith
  have x1 : x < 1 := by linarith
  have nearby (i : I) (S : Finset I) (_ : i ∉ S) :
      (S.filter (fun j => adjacent i j)).card ≤ d := by
    simpa [d,i.property] using overlap_count i.val S
  have ind (i : I) (S : Finset I) (_ : i ∉ S) :
      mass (fun f => avoid A S f ∧ A i f) ≤ β * W (S.filter fun j => !(adjacent i j)) := by
    let T := S.filter fun j => !(adjacent i j)
    have ev := color_bound support (fun _ => red) S (support i) red
    change mass (fun f => avoid A S f ∧ A i f) * (Fintype.card (Fin B) : ℝ)^(support i).card ≤
      W T * (red.card : ℝ)^(support i).card at ev
    have sc : (support i).card = p.choose 2 := by simp [support,i.property]
    simp only [Fintype.card_fin,sc,red,card_singleton,Nat.cast_one,one_pow,mul_one] at ev
    have bd := (le_div_iff₀ (pow_pos Bpos _)).mpr ev
    exact bd.trans_eq (by dsimp [β,T]; ring)
  have step := conditional A adjacent d x β x0 x1 redEst nearby ind
  let S := (univ : Finset I)
  have total : 0<W S := by
    have h := extend_mass W (sub_nonneg.mpr x1.le) ∅ S (by simp) (fun U _ i hi => step U i hi)
    simpa using lt_of_lt_of_le (mul_pos (pow_pos (sub_pos.mpr x1) _) (blank A)) h
  let family := (univ : Finset (Fin n)).powersetCard m
  let event (U : E) := fixed (U.powersetCard 2) blue
  have per (U : E) (hU : U ∈ family) :
      mass (fun f => avoid A S f ∧ event U f) < W S / (n:ℝ)^m := by
    let K := S.filter (fun j => touch (U.powersetCard 2) (support j))
    let T := S.filter (fun j => !(touch (U.powersetCard 2) (support j)))
    have dis : Disjoint T K := by
      apply disjoint_left.mpr; intro j ht hk
      have a := (mem_filter.mp ht).2
      simp [(mem_filter.mp hk).2] at a
    have both : T ∪ K = S := by ext j; by_cases h : touch (U.powersetCard 2) (support j) <;> simp [T,K,h]
    have restore := extend_mass W (sub_nonneg.mpr x1.le) T K dis (fun V _ j hj => step V j hj)
    rw [both] at restore
    have wt : 0 < W T := by
      have u := mass_le (fun (w : Ω) (h : avoid A S w) => (show avoid A T w from fun j hj => h j (mem_filter.mp hj).1))
      exact total.trans_le u
    have cardU := (mem_powersetCard.mp hU).2
    have cap : K.card ≤ m^2*n^(p-2) := by simpa [K,support,cardU] using overlap_count U S
    have gb := blueEst K.card cap
    change (n:ℝ)^m*(((B:ℝ)-1)/B)^(m.choose 2) < (1-x)^K.card at gb
    have raw := color_bound support (fun _ => red) S (U.powersetCard 2) blue
    let bad := mass (fun f => avoid A S f ∧ event U f)
    change bad * (Fintype.card (Fin B):ℝ)^((U.powersetCard 2).card) ≤ W T * (blue.card:ℝ)^((U.powersetCard 2).card) at raw
    have bc : (blue.card:ℝ)=(B:ℝ)-1 := by
      simp [blue,Nat.cast_sub (by omega : 1≤B)]
    simp only [Fintype.card_fin,card_powersetCard,cardU,bc] at raw
    have bd : bad ≤ W T * (((B:ℝ)-1)/B)^(m.choose 2) := by
      rw [div_pow,←mul_div_assoc]; exact (le_div_iff₀ (pow_pos Bpos _)).mpr raw
    have np : 0<(n:ℝ)^m := pow_pos (by exact_mod_cast (show 0<n by omega)) _
    apply (lt_div_iff₀ np).mpr
    calc
      bad * (n:ℝ)^m ≤ (W T*(((B:ℝ)-1)/B)^(m.choose 2))*(n:ℝ)^m := mul_le_mul_of_nonneg_right bd np.le
      _ = ((n:ℝ)^m*(((B:ℝ)-1)/B)^(m.choose 2))*W T := by ring
      _ < _ := mul_lt_mul_of_pos_right gb wt
      _ ≤ _ := restore
  have upper := union_bound event (avoid A S) family
  have fam : family.Nonempty := by
    obtain ⟨s,h,c⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using mn)
    exact ⟨s,mem_powersetCard.mpr ⟨h,c⟩⟩
  have fc : (family.card : ℝ) ≤ (n:ℝ)^m := by
    exact_mod_cast (show family.card ≤ n^m by simpa [family] using Nat.choose_le_pow n m)
  have npos : 0<(n:ℝ)^m := pow_pos (by exact_mod_cast (show 0<n by omega)) _
  have bound : mass (fun w => avoid A S w ∧ ∃ U ∈ family, event U w) < W S := by
    have strict := Finset.sum_lt_sum_of_nonempty fam per
    apply upper.trans_lt (lt_of_lt_of_le strict ?_)
    rw [sum_const,nsmul_eq_mul,←mul_div_assoc]
    apply (div_le_iff₀ npos).mpr
    nlinarith only [mul_le_mul_of_nonneg_right fc total.le]
  have ex : ∃ w : Ω, avoid A S w ∧ ¬∃ U ∈ family, event U w := by
    by_contra! h
    have incl : mass (avoid A S) ≤ mass (fun w => avoid A S w ∧ ∃ U ∈ family, event U w) :=
      mass_le (fun w hw => ⟨hw,h w hw⟩)
    exact (not_lt_of_ge incl) bound
  obtain ⟨w,redFree,blueFree⟩ := ex
  let G : SimpleGraph (Fin n) := {
    Adj := fun a b => a≠b ∧ w {a,b}≠0
    symm := ⟨fun a b h => ⟨h.1.symm,by simpa [Finset.pair_comm b a] using h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨G,?_,?_⟩
  · intro s hs
    have no := redFree (⟨s,hs⟩ : I) (mem_univ _)
    change ¬∀ v ∈ s.powersetCard 2, w v ∈ red at no
    push Not at no
    obtain ⟨v,hv,un⟩ := no
    obtain ⟨sub,two⟩ := mem_powersetCard.mp hv
    obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp two
    have a' : a ∈ s := sub (by simp)
    have b' : b ∈ s := sub (by simp)
    have pair : (G.induce s).Adj ⟨a,a'⟩ ⟨b,b'⟩ := ⟨ne,by simpa [red] using un⟩
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨s((⟨a,a'⟩ : ↥s),(⟨b,b'⟩ : ↥s)),pair⟩
  · apply SimpleGraph.CliqueFree.mono (m:=m) (by omega)
    intro s hs
    obtain ⟨cl,sz⟩ := G.isNClique_iff.mp hs
    apply blueFree
    refine ⟨s,mem_powersetCard.mpr ⟨subset_univ _,sz⟩,?_⟩
    intro v hv
    obtain ⟨sub,two⟩ := mem_powersetCard.mp hv
    obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp two
    have adj := cl (show a ∈ (s:Set _) from sub (by simp)) (show b ∈ (s:Set _) from sub (by simp)) ne
    exact mem_erase.mpr ⟨adj.2,mem_univ _⟩

end OMA.SparseRamsey

namespace Erdos626TriangleFree

open Filter Finset SimpleGraph
open scoped BigOperators Topology

/-- A fixed positive power eventually dominates the logarithmic term. -/
private lemma eventually_log_bound {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, 801 * (Real.log n + 1) ≤ (n : ℝ) ^ d := by
  have hd' : 0 < d / 2 := by linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (d / 2)) atTop atTop :=
    (tendsto_rpow_atTop hd').comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop (801 * (1 / (d / 2) + 1)),
    eventually_ge_atTop (1 : ℕ)] with n hlarge hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let w := (n : ℝ) ^ (d / 2)
  change 801 * (1 / (d / 2) + 1) ≤ w at hlarge
  have hw : 1 ≤ w := Real.one_le_rpow hnR hd'.le
  have hl := Real.log_le_sub_one_of_pos (show 0 < w by dsimp [w]; positivity)
  change Real.log ((n : ℝ) ^ (d / 2)) ≤ w - 1 at hl
  rw [Real.log_rpow hn0] at hl
  have hlog : Real.log n ≤ w / (d / 2) := (le_div_iff₀ hd').mpr (by linarith)
  calc
    801 * (Real.log n + 1) ≤ 801 * (w / (d / 2) + w) := by gcongr
    _ = (801 * (1 / (d / 2) + 1)) * w := by ring
    _ ≤ w * w := mul_le_mul_of_nonneg_right hlarge (by linarith)
    _ = (n : ℝ) ^ d := by rw [← Real.rpow_add hn0]; congr 1; ring

/-- For every sufficiently large n there are parameters for the sparse
random graph construction, with the independence bound at most n^(1/2+d). -/
private lemma parameters {d : ℝ} (hd : 0 < d) (hdMax : d ≤ 1 / 4) :
    ∀ᶠ n : ℕ in atTop, ∃ B m : ℕ, 3 ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
      576 * n ≤ B ^ 2 ∧ 32 * (B : ℝ) * (Real.log n + 1) ≤ m ∧
      (m : ℝ) ≤ (n : ℝ) ^ (1 / 2 + d) := by
  filter_upwards [eventually_log_bound hd, eventually_ge_atTop (3 : ℕ)] with n hlogN hn
  let x : ℝ := n
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 < x := by linarith
  let r := Real.sqrt x
  have hr : 1 ≤ r := by
    change 1 ≤ Real.sqrt x
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx1
  have hrsq : r ^ 2 = x := Real.sq_sqrt hx.le
  have hl : 1 ≤ Real.log x + 1 := by linarith [Real.log_nonneg hx1]
  let B := ⌈24 * r⌉₊
  have hB : 24 * r ≤ (B : ℝ) := Nat.le_ceil _
  have hB2 : (2 : ℝ) ≤ B := by linarith
  have hB2N : 2 ≤ B := by exact_mod_cast hB2
  have hBup : (B : ℝ) ≤ 25 * r := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 24 * r by linarith)
    change (B : ℝ) < 24 * r + 1 at hc
    linarith
  have hEdgeR : 576 * x ≤ (B : ℝ)^2 := by
    have hsq := pow_le_pow_left₀ (show 0 ≤ 24 * r by linarith) hB 2
    nlinarith only [hsq, hrsq]
  have hEdge : 576 * n ≤ B^2 := by
    change 576 * (n : ℝ) ≤ (B : ℝ)^2 at hEdgeR
    exact_mod_cast hEdgeR
  let Q := 32 * (B : ℝ) * (Real.log x + 1)
  let m := ⌈Q⌉₊
  have hQ : Q ≤ m := Nat.le_ceil _
  have hQ3 : 3 ≤ Q := by
    have t := mul_le_mul_of_nonneg_left hl (show 0 ≤ 32 * (B : ℝ) by positivity)
    dsimp [Q]
    linarith
  have hm3 : 3 ≤ m := by exact_mod_cast (show (3 : ℝ) ≤ m from hQ3.trans hQ)
  have hQup : (m : ℝ) ≤ Q + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ Q)).le
  have hmCap : (m : ℝ) ≤ x ^ (1 / 2 + d) := by
    have ht := mul_le_mul_of_nonneg_right hBup (show 0 ≤ Real.log x + 1 by linarith)
    have hrLog : 1 ≤ r * (Real.log x + 1) := by
      simpa only [one_mul] using
        mul_le_mul hr hl (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ r by linarith)
    calc
      (m : ℝ) ≤ Q + 1 := hQup
      _ ≤ r * (801 * (Real.log x + 1)) := by dsimp [Q]; nlinarith only [ht, hrLog]
      _ ≤ r * x ^ d := mul_le_mul_of_nonneg_left hlogN (by linarith)
      _ = x ^ (1 / 2 + d) := by rw [Real.rpow_add hx]; dsimp [r]; rw [Real.sqrt_eq_rpow]
  have hmn : m ≤ n := by
    have hpow : x ^ (1 / 2 + d) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_one] at hpow
    have hle : (m : ℝ) ≤ (n : ℝ) := hmCap.trans hpow
    exact_mod_cast hle
  exact ⟨B, m, hn, hB2N, hm3, hmn, hEdge, hQ, hmCap⟩

/-- Local (3,1) density says exactly that the complement has no triangle. -/
private lemma girth_of_dense {n : ℕ} (G : SimpleGraph (Fin n))
    (dense : ∀ s : Finset (Fin n), s.card = 3 → 1 ≤ (G.induce s).edgeSet.ncard) :
    (3 : ℕ∞) < Gᶜ.egirth := by
  classical
  apply lt_of_lt_of_le (show (3 : ℕ∞) < 4 by decide)
  apply SimpleGraph.le_egirth.mpr
  intro a w hw
  by_cases h3 : w.length = 3
  · obtain ⟨s, hs⟩ := SimpleGraph.is3Clique_iff_exists_cycle_length_three.mpr ⟨a, w, hw, h3⟩
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp (dense s hs.card_eq)
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u.val v.val := (G.induce (s : Set (Fin n))).mem_edgeSet.mp he
      exact False.elim ((hs.isClique u.property v.property huv.ne).2 huv)
  · exact_mod_cast (show 4 ≤ w.length by have := hw.three_le_length; omega)

/-- All colour classes in the complement are cliques in the original graph. -/
private lemma coloring_lower_bound {n m : ℕ} (G : SimpleGraph (Fin n))
    (free : G.CliqueFree (m + 1)) (k : ℕ) (C : Gᶜ.Coloring (Fin k)) :
    n ≤ k * m := by
  classical
  have hClass (i : Fin k) : (Finset.univ.filter fun v => C v = i).card ≤ m := by
    let S : Finset (Fin n) := Finset.univ.filter (fun v => C v = i)
    have hclique : G.IsClique (S : Set (Fin n)) := by
      apply G.isIndepSet_compl.mp
      have h : Gᶜ.IsIndepSet (C.colorClass i) := C.isIndepSet_colorClass i
      simpa [S, SimpleGraph.Coloring.colorClass, Set.preimage] using h
    by_contra! hbig
    change m < S.card at hbig
    have hm : m + 1 ≤ S.card := by omega
    obtain ⟨T, hT, hCard⟩ := Finset.exists_subset_card_eq hm
    exact free T ⟨hclique.subset (Finset.coe_subset.mpr hT), hCard⟩
  calc
    n = ∑ i : Fin k, (Finset.univ.filter fun v => C v = i).card := by
      simpa using (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin k)) (fun v => C v)).symm
    _ ≤ ∑ _ : Fin k, m := Finset.sum_le_sum fun i _ => hClass i
    _ = k * m := by simp

end Erdos626TriangleFree

open Filter in
theorem OMA.solution : OMA.R_Erdos626_erdos_626_variants_h_odd_conjecture_R1.H3 := by
  intro ε hε
  let d : ℝ := min (ε / 2) (1 / 4)
  have hd : 0 < d := by dsimp [d]; exact lt_min (by linarith) (by norm_num)
  have hdMax : d ≤ 1 / 4 := min_le_right _ _
  have hdε : d ≤ ε := (min_le_left _ _).trans (by linarith)
  filter_upwards [Erdos626TriangleFree.parameters hd hdMax] with n hn
  obtain ⟨B, m, hn, hB, hm, hmn, hDegree, hSize, hCap⟩ := hn
  have hDegree' : 64*3^2*n^(3-2) ≤ B^(Nat.choose 3 2-1) := by
    convert hDegree using 1 <;> norm_num
  obtain ⟨G, dense, free⟩ := OMA.SparseRamsey.coloring 3 n B m
    (by decide) hn hB hm hmn hDegree' hSize
  have hg := Erdos626TriangleFree.girth_of_dense G dense
  let k := ENat.toNat Gᶜ.chromaticNumber
  obtain ⟨C⟩ : Gᶜ.Colorable k := Gᶜ.colorable_chromaticNumber_of_fintype
  have hnkm := Erdos626TriangleFree.coloring_lower_bound G free k C
  have htop : Gᶜ.chromaticNumber ≠ ⊤ := (SimpleGraph.chromaticNumber_ne_top_iff_exists).mpr
    ⟨k, ⟨C⟩⟩
  have hk : Gᶜ.chromaticNumber = k := (ENat.natCast_toNat htop).symm
  have hkh : k ≤ Erdos626.h 3 n := by
    unfold Erdos626.h
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro t ⟨A, _, hA⟩
      have hBound := A.chromaticNumber_le_card
      rw [hA, Fintype.card_fin] at hBound
      exact_mod_cast hBound
    · exact ⟨Gᶜ, hg, hk⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnkmR : (n : ℝ) ≤ (k : ℝ) * m := by exact_mod_cast hnkm
  have hBound : (n : ℝ) ^ ((1 : ℝ) / 2 - ε) * m ≤ (k : ℝ) * m := by
    calc
      _ ≤ (n : ℝ) ^ (1 - (1 / 2 + d)) * (n : ℝ) ^ (1 / 2 + d) := by
        apply mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
          hCap hm0.le (by positivity)
      _ = n := by
        rw [← Real.rpow_add hn0, show 1 - (1 / 2 + d) + (1 / 2 + d) = 1 by ring,
          Real.rpow_one]
      _ ≤ (k : ℝ) * m := hnkmR
  have hkhR : (k : ℝ) ≤ (Erdos626.h 3 n : ℝ) := by exact_mod_cast hkh
  exact ((mul_le_mul_iff_left₀ hm0).mp hBound).trans hkhR
