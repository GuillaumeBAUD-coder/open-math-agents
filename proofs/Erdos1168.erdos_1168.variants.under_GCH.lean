import FormalConjectures.ErdosProblems.«1168»
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Erdős–Hajnal–Rado's negative partition relation at aleph_(omega+1)

Under GCH we can enumerate the subsets of size aleph_omega. For each
vertex, cover the earlier requirements by countably many smaller buckets.
A free transversal hits each bucket while avoiding the earlier edges of
its color. This prevents monochromatic triangles in each positive color,
and the enumeration ensures that color zero has no homogeneous set of
the full cardinality.

See Erdős, Hajnal, and Rado (1965), Theorem 10,
https://www.renyi.hu/~p_erdos/1965-14.pdf.
-/

/-
# Free transversals of bounded set maps

Closure of small sets provides disjoint layers. A greedy coloring of the layer graph
has a large class from which to pick a transversal.
-/

open Cardinal Ordinal Set

namespace EHRTransversal

theorem union_le {α ι : Type} {κ μ : Cardinal} (A : ι → Set α)
    (hι : #ι ≤ κ) (hA : ∀ i, #(A i) ≤ μ) :
    #(⋃ i, A i) ≤ κ*μ := by
  exact (Cardinal.mk_iUnion_le A).trans
    (mul_le_mul' hι (ciSup_le' hA))

theorem union_le_self {α ι : Type} {μ : Cardinal} (hμ : ℵ₀ ≤ μ)
    (A : ι → Set α) (hι : #ι ≤ μ) (hA : ∀ i, #(A i) ≤ μ) :
    #(⋃ i, A i) ≤ μ := by
  exact (union_le A hι hA).trans_eq (Cardinal.mul_eq_self hμ)

def step {α : Type} (f : α → Set α) (S : Set α) : Set α := S ∪ ⋃ x ∈ S, f x

def closure {α : Type} (f : α → Set α) (S : Set α) : Set α :=
  ⋃ n : ℕ, (step f)^[n] S

theorem subset_closure {α : Type} (f : α → Set α) (S : Set α) : S ⊆ closure f S := by
  intro x hx
  apply Set.mem_iUnion.2
  exact ⟨0, hx⟩

theorem closure_closed {α : Type} (f : α → Set α) (S : Set α) :
    ∀ x ∈ closure f S, f x ⊆ closure f S := by
  intro x hx y hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  apply Set.mem_iUnion.2
  refine ⟨n+1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hn, hy⟩⟩)

theorem closure_card {α : Type} {μ : Cardinal} (hμ : ℵ₀ ≤ μ)
    (f : α → Set α) (hf : ∀ x, #(f x) ≤ μ) (S : Set α) (hS : #S ≤ μ) :
    #(closure f S) ≤ μ := by
  apply union_le_self hμ _ (by simpa using hμ)
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold step
    refine (Cardinal.mk_union_le _ _).trans ?_
    have h' : #(⋃ x ∈ (step f)^[n] S, f x) ≤ μ := by
      rw [Set.biUnion_eq_iUnion]
      exact union_le_self hμ _ ih (fun x => hf x.1)
    exact (add_le_add ih h').trans_eq (by rw [Cardinal.add_eq_max hμ, max_self])

theorem exists_outside {α : Type} {μ : Cardinal} (R S : Set α)
    (hS : #S ≤ μ) (hR : μ < #R) : (R \ S).Nonempty := by
  by_contra h
  apply hR.not_ge
  apply (Cardinal.mk_le_mk_of_subset _).trans hS
  intro x hx
  by_contra hx'
  exact h ⟨x, hx, hx'⟩

theorem greedy {α : Type} [LinearOrder α] [WellFoundedLT α] {μ : Cardinal}
    (N : α → Set α) (hN : ∀ x, #(N x) ≤ μ) :
    ∃ c : α → (Order.succ μ).ord.ToType, ∀ x y, y < x → y ∈ N x → c x ≠ c y := by
  classical
  let C := (Order.succ μ).ord.ToType
  let forbidden (x : α) (prev : ∀ y, y < x → C) : Set C :=
    Set.range (fun y : {y // y < x ∧ y ∈ N x} => prev y.1 y.2.1)
  have hforb (x : α) (prev : ∀ y, y < x → C) : #(forbidden x prev) ≤ μ :=
    Cardinal.mk_range_le.trans ((Cardinal.mk_le_mk_of_subset (fun _ hx => hx.2)).trans (hN x))
  have hGap : μ < #(Set.univ : Set C) := by
    simp [C]
  let select (x : α) (prev : ∀ y, y < x → C) : C :=
    (exists_outside Set.univ (forbidden x prev) (hforb x prev) hGap).choose
  let c := wellFounded_lt.fix select
  refine ⟨c, ?_⟩
  intro x y hlt hy
  have hc : c x = select x (fun y _ => c y) :=
    WellFounded.fix_eq _ _ _
  rw [hc]
  intro he
  have hh := (exists_outside Set.univ (forbidden x (fun y _ => c y))
    (hforb x (fun y _ => c y)) hGap).choose_spec
  apply hh.2
  exact ⟨⟨y, hlt, hy⟩, he.symm⟩


theorem exists_layers {α ι : Type} {μ : Cardinal} (hμ : ℵ₀ ≤ μ) (hι : #ι ≤ μ)
    (f : α → Set α) (hf : ∀ x, #(f x) ≤ μ) (A : ι → Set α)
    (hA : ∀ i, Order.succ μ < #(A i)) :
    ∃ L : (Order.succ (Order.succ μ)).ord.ToType → Set α,
      (∀ i, #(L i) ≤ μ) ∧ (∀ j i, (L j ∩ A i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (L i) (L j)) ∧
      (∀ i j, i < j → ∀ x ∈ L i, ∀ y ∈ L j, y ∉ f x) := by
  classical
  let X := (Order.succ (Order.succ μ)).ord.ToType
  let Small := {S : Set α // #S ≤ μ ∧ ∀ x ∈ S, f x ⊆ S}
  let old (i : X) (p : ∀ j, j < i → Small) : Set α :=
    ⋃ j : Set.Iio i, (p j.1 j.2).1
  have hOld (i : X) (p : ∀ j, j < i → Small) : #(old i p) ≤ Order.succ μ := by
    have hX : (#X).ord = typeLT X := by simp [X]
    have hi' : #(Set.Iio i) < Order.succ (Order.succ μ) := by
      simpa [X] using Cardinal.mk_Iio_lt i hX
    have hi : #(Set.Iio i) ≤ Order.succ μ := Order.le_of_lt_succ hi'
    exact (union_le _ hi (fun j => (p j.1 j.2).2.1)).trans
      ((mul_le_mul' (le_refl (Order.succ μ)) (Order.le_succ μ)).trans_eq
        (Cardinal.mul_eq_self (hμ.trans (Order.le_succ μ))))
  let point (i : X) (p : ∀ j, j < i → Small) (k : ι) : α :=
    (exists_outside (A k) (old i p) (hOld i p) (hA k)).choose
  have hpoint (i : X) (p : ∀ j, j < i → Small) (k : ι) :
      point i p k ∈ A k \ old i p :=
    (exists_outside (A k) (old i p) (hOld i p) (hA k)).choose_spec
  let build (i : X) (p : ∀ j, j < i → Small) : Small :=
    ⟨closure f (Set.range (point i p)),
      closure_card hμ f hf _ (Cardinal.mk_range_le.trans hι), closure_closed f _⟩
  let sequence : X → Small := wellFounded_lt.fix build
  have hseq (i : X) : sequence i = build i (fun j _ => sequence j) :=
    WellFounded.fix_eq _ _ _
  let L (i : X) : Set α := (sequence i).1 \ old i (fun j _ => sequence j)
  have hleft (i : X) : L i ⊆ (sequence i).1 := Set.sdiff_subset
  have hIncl {i j : X} (hij : i < j) :
      (sequence i).1 ⊆ old j (fun j _ => sequence j) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨i, hij⟩, hx⟩
  have hDisjoint {i j : X} (hij : i < j) : Disjoint (L i) (L j) := by
    apply Set.disjoint_left.2
    intro x hxi hxj
    exact hxj.2 (hIncl hij (hleft i hxi))
  refine ⟨L, fun i => (Cardinal.mk_le_mk_of_subset (hleft i)).trans (sequence i).2.1,
    ?_, ?_, ?_⟩
  · intro j i
    let p : ∀ k, k < j → Small := fun k _ => sequence k
    refine ⟨point j p i, ⟨?_, (hpoint j p i).2⟩, (hpoint j p i).1⟩
    rw [hseq]
    exact subset_closure _ _ (Set.mem_range_self i)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hDisjoint h
    · exact (hDisjoint h).symm
  · intro i j hij x hxi y hyj h
    exact hyj.2 (hIncl hij ((sequence i).2.2 x (hleft i hxi) h))

theorem exists_free_transversal {α ι : Type} {μ : Cardinal}
    (hμ : ℵ₀ ≤ μ) (hι : #ι ≤ μ) (f : α → Set α) (hf : ∀ x, #(f x) ≤ μ)
    (A : ι → Set α) (hA : ∀ i, Order.succ μ < #(A i)) :
    ∃ B : Set α, #B ≤ μ ∧ (∀ i, (B ∩ A i).Nonempty) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∉ f x) := by
  classical
  obtain ⟨L, hL, hMeet, hDisjoint, hBackward⟩ := exists_layers hμ hι f hf A hA
  let X := (Order.succ (Order.succ μ)).ord.ToType
  let S (i : X) := ⋃ x ∈ L i, f x
  have hS (i : X) : #(S i) ≤ μ := by
    unfold S
    rw [Set.biUnion_eq_iUnion]
    exact union_le_self hμ _ (hL i) (fun x => hf x.1)
  let N (i : X) : Set X := {j | (L j ∩ S i).Nonempty}
  have hN (i : X) : #(N i) ≤ μ := by
    let w (j : N i) : S i := ⟨j.2.choose, j.2.choose_spec.2⟩
    have hw : Function.Injective w := by
      intro j k he
      apply Subtype.ext
      by_contra hn
      have h₁ : (w j).1 ∈ L j.1 := j.2.choose_spec.1
      have h₂ : (w k).1 ∈ L k.1 := k.2.choose_spec.1
      rw [← he] at h₂
      exact Set.disjoint_left.1 (hDisjoint hn) h₁ h₂
    exact (Cardinal.mk_le_of_injective hw).trans (hS i)
  obtain ⟨c, hc⟩ := greedy N hN
  have hcc : #((Order.succ μ).ord.ToType) < #X := by simp [X]
  have hX : ℵ₀ ≤ #X := by
    simpa [X] using (hμ.trans ((Order.le_succ μ).trans (Order.le_succ (Order.succ μ))))
  obtain ⟨q,hq⟩ := Cardinal.infinite_pigeonhole_card_lt c hcc hX
  have hge : #ι ≤ #(c ⁻¹' {q}) :=
    hι.trans ((Order.le_succ μ).trans (by simpa using hq.le))
  let e : ι ↪ (c ⁻¹' {q}) := Classical.choice ((Cardinal.le_def _ _).1 hge)
  let point (i : ι) : α := (hMeet (e i).1 i).choose
  have hp (i : ι) : point i ∈ L (e i).1 ∧ point i ∈ A i := (hMeet (e i).1 i).choose_spec
  refine ⟨Set.range point, Cardinal.mk_range_le.trans hι, ?_, ?_⟩
  · intro i
    exact ⟨point i, Set.mem_range_self i, (hp i).2⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hn h
    have hij : (e i).1 ≠ (e j).1 := by
      intro he
      exact hn (congrArg point (e.injective (Subtype.ext he)))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hBackward _ _ hlt _ (hp i).1 _ (hp j).1 h
    · have hmem : (e j).1 ∈ N (e i).1 := by
        refine ⟨point j, (hp j).1, Set.mem_iUnion.2 ⟨point i, ?_⟩⟩
        exact Set.mem_iUnion.2 ⟨(hp i).1, h⟩
      have hei : c (e i).1 = q := (e i).2
      have hej : c (e j).1 = q := (e j).2
      exact hc _ _ hgt hmem (hei.trans hej.symm)

end EHRTransversal

/- Constructing a countable edge coloring from free transversals. -/

open Cardinal Ordinal Set
open scoped Cardinal

namespace EHRColoring

variable {V : Type} [LinearOrder V]

private def Row (μ : ℕ → Cardinal) (b : V) :=
  (n : ℕ) → {B : Set V // #B ≤ μ n ∧ B ⊆ Iio b}

private def predecessors (μ : ℕ → Cardinal) (b : V)
    (rows : ∀ x, x < b → Row μ x) (n : ℕ) (x : V) : Set V :=
  if h : x < b then (rows x h n).val else ∅

theorem exists_rows [WellFoundedLT V] (μ : ℕ → Cardinal) (I : V → ℕ → Type)
    (A : ∀ b n, I b n → Set V)
    (hbelow : ∀ b n i, A b n i ⊆ Iio b)
    (hStep : ∀ (b : V) (n : ℕ) (f : V → Set V), (∀ x, #(f x) ≤ μ n) →
      ∃ B : Set V, #B ≤ μ n ∧ (∀ i, (B ∩ A b n i).Nonempty) ∧
        ∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∉ f x) :
    ∃ R : V → ℕ → Set V,
      (∀ b n, #(R b n) ≤ μ n ∧ R b n ⊆ Iio b) ∧
      (∀ b n i, (R b n ∩ A b n i).Nonempty) ∧
      ∀ b n x, x ∈ R b n → ∀ y ∈ R b n, x ≠ y → y ∉ R x n := by
  classical
  have hp (b : V) (prev : ∀ x, x < b → Row μ x) (n : ℕ) (x : V) :
      #(predecessors μ b prev n x) ≤ μ n := by
    unfold predecessors
    split
    · exact (prev x ‹x < b› n).property.1
    · simp
  let B (b : V) (prev : ∀ x, x < b → Row μ x) (n : ℕ) : Set V :=
    (hStep b n (predecessors μ b prev n) (hp b prev n)).choose
  have hB (b : V) (prev : ∀ x, x < b → Row μ x) (n : ℕ) :
      #(B b prev n) ≤ μ n ∧ (∀ i, (B b prev n ∩ A b n i).Nonempty) ∧
        ∀ x ∈ B b prev n, ∀ y ∈ B b prev n, x ≠ y → y ∉ predecessors μ b prev n x :=
    (hStep b n (predecessors μ b prev n) (hp b prev n)).choose_spec
  let F (b : V) (prev : ∀ x, x < b → Row μ x) : Row μ b :=
    fun n => ⟨B b prev n ∩ Iio b,
      (mk_le_mk_of_subset inter_subset_left).trans (hB b prev n).1,
      inter_subset_right⟩
  let rows (b : V) : Row μ b := wellFounded_lt.fix F b
  have hFix (b : V) : rows b = F b (fun x _ => rows x) :=
    WellFounded.fix_eq wellFounded_lt F b
  let R (b : V) (n : ℕ) : Set V := (rows b n).val
  refine ⟨R, fun b n => (rows b n).property, ?_, ?_⟩
  · intro b n i
    change ((rows b n).val ∩ A b n i).Nonempty
    rw [hFix]
    obtain ⟨x, hx, hxi⟩ := (hB b (fun x _ => rows x) n).2.1 i
    exact ⟨x, ⟨hx, hbelow b n i hxi⟩, hxi⟩
  · intro b n x hx y hy hxy
    change x ∈ (rows b n).val at hx
    change y ∈ (rows b n).val at hy
    rw [hFix] at hx hy
    change x ∈ B b (fun x _ => rows x) n ∩ Iio b at hx
    change y ∈ B b (fun x _ => rows x) n ∩ Iio b at hy
    have h := (hB b (fun x _ => rows x) n).2.2 x hx.1 y hy.1 hxy
    have hxb : x < b := hx.2
    rw [predecessors, dif_pos hxb] at h
    exact h

private noncomputable def edgeValue (R : V → ℕ → Set V) (x y : V) : ℕ := by
  classical
  exact if h : ∃ n, x ∈ R y n then Nat.find h + 1 else 0

private noncomputable def coloring (R : V → ℕ → Set V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => edgeValue R (min x y) (max x y), fun x y => by
    change edgeValue R (min x y) (max x y) = edgeValue R (min y x) (max y x)
    rw [min_comm x y, max_comm x y]⟩

private theorem coloring_comm (R : V → ℕ → Set V) (x y : V) :
    coloring R s(x,y) = coloring R s(y,x) := by
  change edgeValue R (min x y) (max x y) = edgeValue R (min y x) (max y x)
  rw [min_comm x y, max_comm x y]

private theorem coloring_pos {R : V → ℕ → Set V} {x y : V} (hxy : x < y)
    (h : ∃ n, x ∈ R y n) : 0 < coloring R s(x,y) := by
  change 0 < edgeValue R (min x y) (max x y)
  rw [min_eq_left hxy.le, max_eq_right hxy.le]
  simp [edgeValue, h]

private theorem mem_of_color {R : V → ℕ → Set V} {x y : V} (hxy : x < y) {n : ℕ}
    (h : coloring R s(x,y) = n + 1) : x ∈ R y n := by
  classical
  change edgeValue R (min x y) (max x y) = n+1 at h
  rw [min_eq_left hxy.le, max_eq_right hxy.le, edgeValue] at h
  split at h
  · have hn : Nat.find ‹∃ j, x ∈ R y j› = n := by omega
    exact hn ▸ Nat.find_spec ‹∃ j, x ∈ R y j›
  · omega

private theorem no_sorted_triangle {R : V → ℕ → Set V}
    (hfree : ∀ b n x, x ∈ R b n → ∀ y ∈ R b n, x ≠ y → y ∉ R x n)
    {x y z : V} {n : ℕ} (hxy : x < y) (hyz : y < z)
    (h₁ : coloring R s(x,y) = n+1) (h₂ : coloring R s(x,z) = n+1)
    (h₃ : coloring R s(y,z) = n+1) : False :=
  (hfree z n y (mem_of_color hyz h₃) x (mem_of_color (hxy.trans hyz) h₂) hxy.ne')
    (mem_of_color hxy h₁)

private theorem no_triangle {R : V → ℕ → Set V}
    (hfree : ∀ b n x, x ∈ R b n → ∀ y ∈ R b n, x ≠ y → y ∉ R x n)
    {x y z : V} {n : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : coloring R s(x,y) = n+1) (h₂ : coloring R s(x,z) = n+1)
    (h₃ : coloring R s(y,z) = n+1) : False := by
  have h₁' : coloring R s(y,x) = n+1 := (coloring_comm R y x).trans h₁
  have h₂' : coloring R s(z,x) = n+1 := (coloring_comm R z x).trans h₂
  have h₃' : coloring R s(z,y) = n+1 := (coloring_comm R z y).trans h₃
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · rcases lt_or_gt_of_ne hyz with hyz | hzy
    · exact no_sorted_triangle hfree hxy hyz h₁ h₂ h₃
    · rcases lt_or_gt_of_ne hxz with hxz | hzx
      · exact no_sorted_triangle hfree hxz hzy h₂ h₁ h₃'
      · exact no_sorted_triangle hfree hzx hxy h₂' h₃' h₁
  · rcases lt_or_gt_of_ne hxz with hxz | hzx
    · exact no_sorted_triangle hfree hyx hxz h₁' h₃ h₂
    · rcases lt_or_gt_of_ne hyz with hyz | hzy
      · exact no_sorted_triangle hfree hyz hzx h₃ h₁' h₂'
      · exact no_sorted_triangle hfree hzy hyx h₃' h₂' h₁'

theorem exists_coloring [WellFoundedLT V] (μ : ℕ → Cardinal) (I : V → ℕ → Type)
    (A : ∀ b n, I b n → Set V)
    (hbelow : ∀ b n i, A b n i ⊆ Iio b)
    (hStep : ∀ (b : V) (n : ℕ) (f : V → Set V), (∀ x, #(f x) ≤ μ n) →
      ∃ B : Set V, #B ≤ μ n ∧ (∀ i, (B ∩ A b n i).Nonempty) ∧
        ∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∉ f x)
    {κLarge : Cardinal}
    (hCover : ∀ X : Set V, #X = κLarge →
      ∃ b ∈ X, ∃ n i, A b n i ⊆ X) :
    ∃ col : Sym2 V → ℕ,
      (∀ X : Set V, #X = κLarge → ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ 0 < col s(x,y)) ∧
      ∀ (n : ℕ) (x y z : V), x ≠ y → x ≠ z → y ≠ z →
        col s(x,y) = n+1 → col s(x,z) = n+1 → col s(y,z) ≠ n+1 := by
  obtain ⟨R, hR, hhit, hfree⟩ := exists_rows μ I A hbelow hStep
  refine ⟨coloring R, ?_, fun n x y z hxy hxz hyz h₁ h₂ h₃ =>
    no_triangle hfree hxy hxz hyz h₁ h₂ h₃⟩
  intro X hX
  obtain ⟨b, hb, n, i, hi⟩ := hCover X hX
  obtain ⟨x, hx, hxi⟩ := hhit b n i
  have hxb := (hR b n).2 hx
  exact ⟨x, hi hxi, b, hb, (show x < b from hxb).ne, coloring_pos hxb ⟨n,hx⟩⟩

end EHRColoring

noncomputable section

namespace EHRPartition

open Cardinal Ordinal Set
open scoped Cardinal

private abbrev baseCard : Cardinal.{0} := ℵ_ ω
private abbrev targetCard : Cardinal.{0} := Order.succ baseCard
private abbrev Vertices := targetCard.ord.ToType

private abbrev Requirement := {S : Set Vertices // #S = baseCard}

private def layerCard (n : ℕ) : Cardinal.{0} := ℵ_ (n : Ordinal)

private theorem base_infinite : ℵ₀ ≤ baseCard := aleph0_le_aleph _

private theorem layer_smaller (n : ℕ) : Order.succ (layerCard n) < baseCard := by
  rw [layerCard, succ_aleph, aleph_lt_aleph, ← Nat.cast_add_one]
  exact Ordinal.natCast_lt_omega0 _

private theorem vertices_card : #Vertices = targetCard := by
  rw [Cardinal.mk_toType, card_ord]

private theorem enumerate_requirements (hGCH : GCH) : Nonempty (Requirement ↪ Vertices) := by
  classical
  let e (S : Requirement) : baseCard.out ≃ S.val :=
    (Cardinal.eq.mp (by rw [mk_out, S.property])).some
  let f (S : Requirement) (x : baseCard.out) : Vertices := (e S x).val
  have hr (S : Requirement) : range (f S) = S.val := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e S a).property
    · intro hx
      obtain ⟨a, ha⟩ := (e S).surjective ⟨x, hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hi : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    rw [← hr S, ← hr T, h]
  have hpow : (2 : Cardinal) ^ baseCard = targetCard := by
    change (2 : Cardinal.{0}) ^ ℵ_ (ω : Ordinal.{0}) = Order.succ (ℵ_ (ω : Ordinal.{0}))
    rw [succ_aleph, ← Order.succ_eq_add_one]
    exact hGCH ω
  have hfCard : #(baseCard.out → Vertices) = targetCard := by
    rw [mk_arrow, Cardinal.lift_id, Cardinal.lift_id, mk_out, vertices_card, ← hpow, ← power_mul,
      mul_eq_self base_infinite]
  exact (Cardinal.le_def _ _).mp
    ((Cardinal.mk_le_of_injective hi).trans_eq (hfCard.trans vertices_card.symm))

private abbrev Eligible (index : Requirement ↪ Vertices) (b : Vertices) :=
  {S : Requirement // index S < b ∧ S.val ⊆ Iio b}

private theorem eligible_card (index : Requirement ↪ Vertices) (b : Vertices) :
    #(Eligible index b) ≤ baseCard := by
  have hi : #(Eligible index b) ≤ #(Iio b) :=
    Cardinal.mk_le_of_injective
      (f := fun S : Eligible index b => (⟨index S.val, S.property.1⟩ : Iio b))
      (fun S T h => Subtype.ext (index.injective (congrArg Subtype.val h)))
  have hb : #(Iio b) < targetCard := by
    have h := Cardinal.mk_Iio_lt b (by rw [vertices_card, type_toType])
    rwa [vertices_card] at h
  exact hi.trans (Order.lt_succ_iff.mp hb)

private noncomputable def enumerate_eligible (index : Requirement ↪ Vertices) (b : Vertices) :
    Eligible index b ↪ baseCard.ord.ToType :=
  ((Cardinal.le_def _ _).mp (by
    rw [Cardinal.mk_toType, card_ord]
    exact eligible_card index b)).some

private abbrev Bucket (index : Requirement ↪ Vertices) (b : Vertices) (n : ℕ) :=
  {S : Eligible index b // ((enumerate_eligible index b S).toOrd : Ordinal) < (layerCard n).ord}

private theorem bucket_card (index : Requirement ↪ Vertices) (b : Vertices) (n : ℕ) :
    #(Bucket index b n) ≤ layerCard n := by
  let f (i : Bucket index b n) : (layerCard n).ord.ToType :=
    Ordinal.ToType.mk ⟨(enumerate_eligible index b i.val).toOrd, i.property⟩
  have hi : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply (enumerate_eligible index b).injective
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    exact congrArg (fun t : Iio (layerCard n).ord => (t : Ordinal))
      ((Ordinal.ToType.mk (o := (layerCard n).ord)).injective h)
  simpa only [Cardinal.mk_toType, card_ord] using Cardinal.mk_le_of_injective hi

private theorem buckets_cover (index : Requirement ↪ Vertices) (b : Vertices) (S : Eligible index b) :
    ∃ n : ℕ, ((enumerate_eligible index b S).toOrd : Ordinal) < (layerCard n).ord := by
  let v := (enumerate_eligible index b S).toOrd
  have hv : v.val.card < baseCard := Cardinal.lt_ord.mp v.property
  have hs : baseCard ≤ ⨆ o : Iio (ω : Ordinal.{0}), ℵ_ o.val :=
    (aleph_limit Ordinal.isSuccLimit_omega0).le
  obtain ⟨o, ho⟩ := exists_lt_of_lt_ciSup' (hv.trans_le hs)
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp o.property
  exact ⟨n, Cardinal.lt_ord.mpr (by simpa only [layerCard, ← hn] using ho)⟩

private theorem cover (index : Requirement ↪ Vertices) (X : Set Vertices) (hX : #X = targetCard) :
    ∃ b ∈ X, ∃ (n : ℕ) (S : Bucket index b n), S.val.val.val ⊆ X := by
  obtain ⟨e⟩ := (Cardinal.le_def baseCard.out X).mp (by
    rw [mk_out, hX]
    exact (Order.lt_succ _).le)
  let f (x : baseCard.out) : Vertices := (e x).val
  let S : Requirement := ⟨range f, (Cardinal.mk_range_eq f
      (fun x y he => e.injective (Subtype.ext he))).trans (mk_out _)⟩
  have hSub : S.val ⊆ X := by
    rintro _ ⟨a, rfl⟩
    exact (e a).property
  let g (s : S.val) : Ordinal := s.val.toOrd
  have hcof : #S.val < targetCard.ord.cof := by
    rw [(Cardinal.isRegular_succ base_infinite).cof_ord, S.property]
    exact Order.lt_succ _
  have hsup : (⨆ j, g j) < targetCard.ord :=
    Ordinal.iSup_lt_of_lt_cof hcof (fun j => j.val.toOrd.property)
  let z : Vertices := Ordinal.ToType.mk ⟨⨆ j, g j, hsup⟩
  have hz (x : Vertices) (hx : x ∈ S.val) : x ≤ z := by
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    dsimp only [z]
    rw [OrderIso.symm_apply_apply]
    exact Ordinal.le_iSup g ⟨x, hx⟩
  let t := max (index S) z
  have ht : #(Iic t) < targetCard := by
    have h := Cardinal.mk_Iic_lt t (by rw [vertices_card, type_toType])
      (by rw [vertices_card]; exact base_infinite.trans (Order.lt_succ _).le)
    rwa [vertices_card] at h
  have hx : ∃ b ∈ X, t < b := by
    by_contra! hn
    have hle : #X ≤ #(Iic t) := mk_le_mk_of_subset (fun b hb => hn b hb)
    rw [hX] at hle
    exact (not_le_of_gt ht) hle
  obtain ⟨b, hb, htb⟩ := hx
  let S' : Eligible index b := ⟨S, (le_max_left _ _).trans_lt htb,
    fun x hx => ((hz x hx).trans (le_max_right _ _)).trans_lt htb⟩
  obtain ⟨n, hn⟩ := buckets_cover index b S'
  exact ⟨b, hb, n, ⟨S', hn⟩, hSub⟩

theorem negative (hGCH : GCH) : ¬ CardinalCountableColorRamsey targetCard := by
  obtain ⟨index⟩ := enumerate_requirements hGCH
  let I (b : Vertices) (n : ℕ) := Bucket index b n
  let A (b : Vertices) (n : ℕ) (S : I b n) : Set Vertices := S.val.val.val
  have hbelow (b : Vertices) (n : ℕ) (S : I b n) : A b n S ⊆ Iio b := S.val.property.2
  have hStep (b : Vertices) (n : ℕ) (f : Vertices → Set Vertices)
      (hf : ∀ x, #(f x) ≤ layerCard n) :
      ∃ B : Set Vertices, #B ≤ layerCard n ∧ (∀ i, (B ∩ A b n i).Nonempty) ∧
        ∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∉ f x := by
    exact EHRTransversal.exists_free_transversal (aleph0_le_aleph _) (bucket_card index b n) f hf
      (A b n) (fun S => S.val.val.property ▸ layer_smaller n)
  obtain ⟨col, hRed, hTriangle⟩ := EHRColoring.exists_coloring layerCard I A hbelow hStep (cover index)
  intro h
  obtain ⟨X, hX, hCard⟩ | ⟨n, x, y, z, hxy, hxz, hyz, h₁, h₂, h₃⟩ := h col
  · obtain ⟨x, hx, y, hy, hxy, hp⟩ := hRed X hCard
    exact (Nat.ne_of_gt hp) (hX x hx y hy hxy)
  · exact hTriangle n x y z hxy hxz hyz h₁ h₂ h₃

universe u

theorem negative_lift {c : Cardinal.{0}} (h : ¬ CardinalCountableColorRamsey c) :
    ¬ CardinalCountableColorRamsey (Cardinal.lift.{u} c) := by
  let C := Cardinal.lift.{u} c
  have heq : Cardinal.lift.{0} #(C.ord.ToType) = Cardinal.lift.{u} #(c.ord.ToType) := by
    simp only [Cardinal.mk_ord_toType, Cardinal.lift_uzero, C]
  let e : C.ord.ToType ≃ c.ord.ToType := (Cardinal.lift_mk_eq'.mp heq).some
  intro hLarge
  apply h
  intro col
  rcases hLarge (col ∘ Sym2.map e) with ⟨X,hX,hCard⟩ |
    ⟨n,x,y,z,hxy,hxz,hyz,h₁,h₂,h₃⟩
  · refine Or.inl ⟨e '' X, ?_, ?_⟩
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hn
      exact hX x hx y hy (fun hxy => hn (congrArg e hxy))
    · have H := Cardinal.mk_image_eq_lift e X e.injective
      have hs : Cardinal.lift.{u} #(e '' X) = Cardinal.lift.{u} c := by
        simpa only [hCard, Cardinal.lift_uzero, C] using H
      exact Cardinal.lift_injective hs
  · exact Or.inr ⟨n, e x, e y, e z, fun he => hxy (e.injective he),
      fun he => hxz (e.injective he), fun he => hyz (e.injective he), h₁,h₂,h₃⟩

end EHRPartition

theorem OMA.solution : type_of% @Erdos1168.erdos_1168.variants.under_GCH := by
  intro hGCH
  rw [← succ_aleph]
  have h := EHRPartition.negative_lift (EHRPartition.negative hGCH)
  simpa only [EHRPartition.targetCard, EHRPartition.baseCard,
    Cardinal.lift_succ, Cardinal.lift_aleph, Ordinal.lift_omega0] using h