import OMAReductions.R_Erdos101_erdos_101_R2_H1_R1

/-!
# Two cycle conditions for lifting marked triples

Write z = ax + by, a+b=1. The z-to-x graph carries the gain a and
the x-to-y graph carries b/a. Balance means that the signed product
along every closed walk is one. The two graphs can be integrated
independently. A single rescaling in the second graph then makes the
two potentials compatible at every center.
-/

namespace OMA.R_Erdos101_erdos_101_R2_H1_R1_H1_R1

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles
open scoped Classical

/-- In the graph of pairs (vertex, accumulated gain), two paths from a
component root to a fixed vertex must have the same final gain. This
gives a potential, including on components with no distinguished vertex. -/
theorem potential (E : ℝ² → ℝ² → ℝˣ → Prop)
    (bal : ∀ x i j, Relation.EqvGen (fun p q : ℝ² × ℝˣ =>
      E p.1 q.1 (q.2 / p.2)) (x,i) (x,j) → i = j) :
    ∃ f : ℝ² → ℝˣ, ∀ x y g, E x y g → f y = f x * g := by
  classical
  let R (p q : ℝ² × ℝˣ) := E p.1 q.1 (q.2 / p.2)
  have step {x y g} (he : E x y g) (t : ℝˣ) : Relation.EqvGen R (x,t) (y,t*g) := by
    apply Relation.EqvGen.rel
    simpa [R] using he
  let C (v : ℝ²) : Set ℝ² := {u | ∃ g, Relation.EqvGen R (u,1) (v,g)}
  have nonemptyC v : (C v).Nonempty := ⟨v,1,.refl _⟩
  let pick (s : Set ℝ²) := if h : s.Nonempty then h.choose else 0
  have path v : ∃ g, Relation.EqvGen R (pick (C v),1) (v,g) := by
    change pick (C v) ∈ C v
    simpa only [pick,dif_pos (nonemptyC v)] using (nonemptyC v).choose_spec
  refine ⟨fun v => (path v).choose,?_⟩
  intro x y g he
  have same : C x = C y := by
    ext u
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨_,.trans _ _ _ hk (step he k)⟩
    · rintro ⟨k,hk⟩
      have back : Relation.EqvGen R (x,k/g) (y,k) := by simpa using step he (k/g)
      exact ⟨_,.trans _ _ _ hk (.symm _ _ back)⟩
  have hy : Relation.EqvGen R (pick (C x),1) (y,(path y).choose) :=
    (congrArg (fun r => Relation.EqvGen R (r,1) (y,(path y).choose))
      (congrArg pick same)).mpr (path y).choose_spec
  exact bal y _ _ (.trans _ _ _ (.symm _ _ hy)
    (.trans _ _ _ (path x).choose_spec (step he _)))

/-- Extract triples with balanced products of the first barycentric coefficient. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ*(S.card : ℝ)^2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ T : Finset (S × S × S), ∃ a b : (S × S × S) → ℝˣ, (ExplicitDisjoint T ∧
      (T : Set (S × S × S)).InjOn (fun e => line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)]) ∧
      (∀ e ∈ T, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
        line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²)) ∧
      (∃ c : ℝ² → Fin 3, ∀ e ∈ T, c e.1 = 0 ∧ c e.2.1 = 1 ∧ c e.2.2 = 2) ∧
      (∀ e ∈ T, (a e : ℝ) + (b e : ℝ) = 1 ∧
        (e.2.2 : ℝ²) = (a e : ℝ) • (e.1 : ℝ²) + (b e : ℝ) • (e.2.1 : ℝ²))) ∧
      ρ*(S.card : ℝ)^2 ≤ T.card ∧ (∀ x i j, Relation.EqvGen (fun p q : ℝ² × ℝˣ =>
        ∃ e ∈ T, (e.2.2 : ℝ²) = p.1 ∧ (e.1 : ℝ²) = q.1 ∧ a e = q.2 / p.2)
        (x,i) (x,j) → i = j)

/-- On a dense first-balanced family, find a dense subsystem on which
the affine odds b/a have trivial products around center-to-endpoint cycles. -/
def H2 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ (T : Finset (S × S × S)) (a b : (S × S × S) → ℝˣ), (ExplicitDisjoint T ∧
      (T : Set (S × S × S)).InjOn (fun e => line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)]) ∧
      (∀ e ∈ T, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
        line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²)) ∧
      (∃ c : ℝ² → Fin 3, ∀ e ∈ T, c e.1 = 0 ∧ c e.2.1 = 1 ∧ c e.2.2 = 2) ∧
      (∀ e ∈ T, (a e : ℝ) + (b e : ℝ) = 1 ∧
        (e.2.2 : ℝ²) = (a e : ℝ) • (e.1 : ℝ²) + (b e : ℝ) • (e.2.1 : ℝ²))) →
    ρ*(S.card : ℝ)^2 ≤ T.card → (∀ x i j, Relation.EqvGen (fun p q : ℝ² × ℝˣ =>
        ∃ e ∈ T, (e.2.2 : ℝ²) = p.1 ∧ (e.1 : ℝ²) = q.1 ∧ a e = q.2 / p.2)
        (x,i) (x,j) → i = j) →
    ∃ U ⊆ T, η*(S.card : ℝ)^2 ≤ U.card ∧ (∀ x i j, Relation.EqvGen (fun p q : ℝ² × ℝˣ =>
        ∃ e ∈ U, (e.1 : ℝ²) = p.1 ∧ (e.2.1 : ℝ²) = q.1 ∧ b e / a e = q.2 / p.2)
        (x,i) (x,j) → i = j)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R2_H1_R1.H1 := by
  classical
  intro first second δ hδ
  obtain ⟨ρ,hρ,N,extract₁⟩ := first δ hδ
  obtain ⟨η,hη,M,extract₂⟩ := second ρ hρ
  refine ⟨η,hη,max N M,?_⟩
  intro S hn cap dense
  obtain ⟨T,a,b,marked,size,bal₁⟩ := extract₁ S ((le_max_left ..).trans hn) cap dense
  obtain ⟨U,sub,usize,bal₂⟩ := extract₂ S ((le_max_right ..).trans hn) cap T a b marked size bal₁
  obtain ⟨A,hA⟩ := potential (fun z x g => ∃ e ∈ T,
    (e.2.2 : ℝ²) = z ∧ (e.1 : ℝ²) = x ∧ a e = g) bal₁
  obtain ⟨B,hB⟩ := potential (fun x y g => ∃ e ∈ U,
    (e.1 : ℝ²) = x ∧ (e.2.1 : ℝ²) = y ∧ b e / a e = g) bal₂
  obtain ⟨hd,lines,points,⟨c,hc⟩,coords⟩ := marked
  obtain ⟨r,hr⟩ := Infinite.exists_notMem_finset (insert (0 : ℝ)
    (S.image (fun x => ((A x / B x : ℝˣ) : ℝ))))
  let k := Units.mk0 r (fun he => hr (Finset.mem_insert.mpr (Or.inl he)))
  have hk : k ∉ S.image (fun x => A x / B x) := by
    rintro hmem
    obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp hmem
    exact hr (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,congrArg Units.val eq⟩))
  let s (x : ℝ²) := A x / (k * B x)
  have hs (x : ℝ²) (hx : x ∈ S) : s x ≠ 1 := by
    intro he
    have eq := div_eq_one.mp he
    apply hk
    exact Finset.mem_image.mpr ⟨x,hx,by rw [eq,mul_div_cancel_right]⟩
  let q (x : ℝ²) := if hx : x ∈ S then Units.mk0 (1-(s x : ℝ))
      (sub_ne_zero.mpr (fun eq => hs x hx (Units.ext eq.symm))) else 1
  let h (x : ℝ²) := if c x = 0 then A x / q x else if c x = 1 then k * B x else A x
  refine ⟨U,⟨fun _ _ _ _ i j => hd.inj₀ (sub i) (sub j),
    fun _ _ _ _ i j => hd.inj₁ (sub i) (sub j),fun _ _ _ _ i j => hd.inj₂ (sub i) (sub j)⟩,
    usize,lines.mono (Finset.coe_subset.mpr sub),fun e he => points e (sub he),
    h,s,hs,?_⟩
  intro X e he
  obtain ⟨cx,cy,cz⟩ := hc e (sub he)
  have ax := hA _ _ _ ⟨e,sub he,rfl,rfl,rfl⟩
  have by' := hB _ _ _ ⟨e,he,rfl,rfl,rfl⟩
  obtain ⟨sum,vec⟩ := coords e (sub he)
  have left : (1-(s e.1 : ℝ)) * (h e.1 : ℝ) = (h e.2.2 : ℝ) * (a e : ℝ) := by
    have hnz : 1-(s e.1 : ℝ) ≠ 0 :=
      sub_ne_zero.mpr (fun eq => hs e.1 e.1.property (Units.ext eq.symm))
    simp [h,cx,cz,q,e.1.property,ax]
    field_simp
  have right : (s e.1 : ℝ) * (h e.2.1 : ℝ) = (h e.2.2 : ℝ) * (b e : ℝ) := by
    simp [h,cy,cz,s,by',ax]
    field_simp
  apply Prod.ext
  · change (h e.2.2 : ℝ) = (1-(s e.1 : ℝ)) * (h e.1 : ℝ) + (s e.1 : ℝ) * (h e.2.1 : ℝ)
    rw [left,right,← mul_add,sum,mul_one]
  · change (h e.2.2 : ℝ) • (e.2.2 : ℝ²) = _
    change _ = (1-(s e.1 : ℝ)) • ((h e.1 : ℝ) • (e.1 : ℝ²)) +
      (s e.1 : ℝ) • ((h e.2.1 : ℝ) • (e.2.1 : ℝ²))
    rw [smul_smul,smul_smul,left,right,← smul_smul,← smul_smul,← smul_add,← vec]

end OMA.R_Erdos101_erdos_101_R2_H1_R1_H1_R1
