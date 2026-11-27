import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1

/-! Four distinct points in a parallelogram, or at positions 0,1,2,4 in an
arithmetic progression, have at most nine signed differences. Two different
completions of the same pair to a progression always give one of these patterns. -/

open Finset
open scoped Classical Pointwise

namespace APStructure757
private def Local (A : Finset ℝ) := ∀ B : Set ℝ, B ⊆ (A : Set ℝ) →
  B.ncard=4 → 11 ≤ (B-B).ncard

private theorem nine {A B : Finset ℝ} (loc : Local A) (sub : B ⊆ A) (size : B.card=4)
    (D : List ℝ) (len : D.length ≤ 9) (covers : ∀ x ∈ B, ∀ y ∈ B, x-y ∈ D) : False := by
  have lo := loc (B : Set ℝ) sub (by simpa using size)
  have hi : ((B:Set ℝ)-(B:Set ℝ)) ⊆ (D.toFinset : Set ℝ) := by
    rintro _ ⟨x,hx,y,hy,rfl⟩
    exact List.mem_toFinset.mpr (covers _ hx _ hy)
  have bound := Set.ncard_le_ncard hi (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at bound
  have ds := D.toFinset_card_le
  omega

private theorem para {A : Finset ℝ} (loc : Local A) (a b c d : ℝ)
    (sub : ({a,b,c,d}:Finset ℝ) ⊆ A) (size : ({a,b,c,d}:Finset ℝ).card=4)
    (eq : a+d=b+c) : False := by
  apply nine loc sub size [0,b-a,a-b,c-a,a-c,d-a,a-d,b-c,c-b] (by simp)
  intro x hx y hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] <;> grind

private theorem doubled {A : Finset ℝ} (loc : Local A) (a b c d : ℝ)
    (sub : ({a,b,c,d}:Finset ℝ) ⊆ A) (size : ({a,b,c,d}:Finset ℝ).card=4)
    (e : a+c=2*b) (f : a+d=2*c) : False := by
  apply nine loc sub size [0,b-a,a-b,c-a,a-c,d-b,b-d,d-a,a-d] (by simp)
  intro x hx y hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] <;> grind

private theorem complete {a b c x y : ℝ} (ab : a<b) (bc : b<c) (eq : a+c=2*b)
    (hx : x ∈ ({a,b,c}:Finset ℝ)) (hy : y ∈ ({a,b,c}:Finset ℝ)) (ne : x ≠ y) :
    ∃ z, ({a,b,c}:Finset ℝ)={x,y,z} ∧ x ≠ z ∧ y ≠ z ∧
      (x+y=2*z ∨ x+z=2*y ∨ y+z=2*x) := by
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
  all_goals first | exact (ne rfl).elim | skip
  all_goals first
    | (refine ⟨a,?_,?_,?_,?_⟩ <;> first | (ext t; simp only [mem_insert,mem_singleton]; tauto) | grind)
    | (refine ⟨b,?_,?_,?_,?_⟩ <;> first | (ext t; simp only [mem_insert,mem_singleton]; tauto) | grind)
    | (refine ⟨c,?_,?_,?_,?_⟩ <;> first | (ext t; simp only [mem_insert,mem_singleton]; tauto) | grind)


private theorem unique_completion {A : Finset ℝ} (loc : Local A) {x y z w : ℝ}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) (xw : x ≠ w) (yw : y ≠ w)
    (ez : x+y=2*z ∨ x+z=2*y ∨ y+z=2*x)
    (ew : x+y=2*w ∨ x+w=2*y ∨ y+w=2*x) : z=w := by
  by_contra zw
  let T : Finset ℝ := {x,y,z,w}
  have sub : T ⊆ A := by simp [T,insert_subset_iff,singleton_subset_iff,hx,hy,hz,hw]
  have size : T.card=4 := by simp [T,xy,xz,yz,xw,yw,zw]
  have ban (a b c d : ℝ) (sort : ({a,b,c,d}:Finset ℝ)=T)
      (eq : a+d=b+c ∨ (a+c=2*b ∧ a+d=2*c)) : False := by
    rcases eq with e|⟨e,f⟩
    · apply para loc a b c d (by rwa [sort]) (by rwa [sort]) e
    · apply doubled loc a b c d (by rwa [sort]) (by rwa [sort]) e f
  rcases ez with e|e|e <;> rcases ew with f|f|f
  · exact zw (by linarith)
  · apply ban x z y w
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · right; constructor <;> linarith
  · apply ban y z x w
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · right; constructor <;> linarith
  · apply ban x w y z
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · right; constructor <;> linarith
  · exact zw (by linarith)
  · apply ban x z w y
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · left; linarith
  · apply ban y w x z
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · right; constructor <;> linarith
  · apply ban x z w y
    · ext u; simp only [T,mem_insert,mem_singleton]; tauto
    · left; linarith
  · exact zw (by linarith)

end APStructure757

open APStructure757 in
theorem OMA.solution : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1.H1 := by
  classical
  intro A loc
  dsimp only
  constructor
  · intro e he f hf ef
    obtain ⟨a,b,c,ab,bc,abc,rfl⟩ := (mem_filter.mp he).2
    obtain ⟨d,t,u,dt,tu,dtu,rfl⟩ := (mem_filter.mp hf).2
    have sub1 := mem_powerset.mp (mem_filter.mp he).1
    have sub2 := mem_powerset.mp (mem_filter.mp hf).1
    apply card_le_one.mpr
    intro x hx y hy
    by_contra xy
    obtain ⟨z,form,xz,yz,ze⟩ := complete ab bc abc (mem_inter.mp hx).1 (mem_inter.mp hy).1 xy
    obtain ⟨w,form',xw,yw,we⟩ := complete dt tu dtu (mem_inter.mp hx).2 (mem_inter.mp hy).2 xy
    have hz : z ∈ A := sub1 (by rw [form]; simp)
    have hw : w ∈ A := sub2 (by rw [form']; simp)
    have zw := unique_completion loc (sub1 (mem_inter.mp hx).1) (sub1 (mem_inter.mp hy).1)
      hz hw xy xz yz xw yw ze we
    exact ef (by rw [form,form',zw])
  · intro a b c d t ab bc db bt eq fe he hf
    by_contra ne
    have sub1 := mem_powerset.mp (mem_filter.mp he).1
    have sub2 := mem_powerset.mp (mem_filter.mp hf).1
    apply para loc a d t c
    · simp only [insert_subset_iff,singleton_subset_iff] at sub1 sub2 ⊢
      exact ⟨sub1.1,sub2.1,sub2.2.2,sub1.2.2⟩
    · have tc : t ≠ c := by intro h; apply ne; linarith
      simp [ne,(ab.trans bt).ne,(ab.trans bc).ne,(db.trans bt).ne,(db.trans bc).ne,tc]
    · linarith

