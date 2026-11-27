import FormalConjectures.ErdosProblems.«596»
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Combinatorics.Pigeonhole

namespace OMA.Folkman

open Finset

private theorem triangle_ramsey_succ (n : ℕ) : ∃ m : ℕ, ∀ C : Fin m × Fin m → Fin (n+1),
    ∃ a b c : Fin m, a < b ∧ b < c ∧ C (a,b) = C (a,c) ∧ C (a,b) = C (b,c) := by
  classical
  induction n with
  | zero =>
    have same (i j : Fin 1) : i = j := Fin.ext (by omega)
    exact ⟨3,fun C => ⟨0,1,2,by decide,by decide,same _ _,same _ _⟩⟩
  | succ n ih =>
    obtain ⟨m,hm⟩ := ih
    let N := (n+2)*m
    refine ⟨N+1,?_⟩
    intro C
    let row (i : Fin N) := C (0,i.succ)
    obtain ⟨q,_,hq⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (univ : Finset (Fin N))) (t := (univ : Finset (Fin (n+2)))) (f := row)
      (fun _ _ => mem_univ _) univ_nonempty (show _ * m ≤ _ by simp [N])
    obtain ⟨T,hT,hcard⟩ := exists_subset_card_eq hq
    let f (i : Fin m) : Fin (N+1) := (T.orderEmbOfFin hcard i).succ
    have hf : StrictMono f := fun _ _ h => Fin.succ_lt_succ_iff.mpr ((T.orderEmbOfFin hcard).strictMono h)
    have from_zero (i : Fin m) : C (0,f i) = q :=
      (mem_filter.mp (hT (T.orderEmbOfFin_mem hcard i))).2
    by_cases hex : ∃ i j : Fin m, i < j ∧ C (f i,f j) = q
    · obtain ⟨i,j,hij,he⟩ := hex
      exact ⟨0,f i,f j,Fin.succ_pos _,hf hij,(from_zero i).trans (from_zero j).symm,(from_zero i).trans he.symm⟩
    · let U := (univ : Finset (Fin (n+2))).erase q
      have hU : U.card = n+1 := by simp [U]
      let lower (d : Fin (n+2)) : Fin (n+1) :=
        if h : d ∈ U then U.equivFinOfCardEq hU ⟨d,h⟩ else 0
      have allowed {i j : Fin m} (h : i < j) : C (f i,f j) ∈ U :=
        mem_erase_of_ne_of_mem (fun eq => hex ⟨i,j,h,eq⟩) (mem_univ _)
      have decode {d e : Fin (n+2)} (hd : d ∈ U) (he : e ∈ U) (eq : lower d = lower e) : d = e := by
        simpa [lower,hd,he] using eq
      obtain ⟨a,b,c,hab,hbc,h1,h2⟩ := hm fun ij => lower (C (f ij.1,f ij.2))
      exact ⟨f a,f b,f c,hf hab,hf hbc,decode (allowed hab) (allowed (hab.trans hbc)) h1,
        decode (allowed hab) (allowed hbc) h2⟩

theorem triangle_ramsey {n : ℕ} (hn : 0 < n) : ∃ m : ℕ, ∀ C : Fin m × Fin m → Fin n,
    ∃ a b c : Fin m, a < b ∧ b < c ∧ C (a,b) = C (a,c) ∧ C (a,b) = C (b,c) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact triangle_ramsey_succ n

end OMA.Folkman

/-! The Nešetřil–Rödl partite construction for Folkman's edge-triangle theorem. -/

namespace OMA.Folkman
open SimpleGraph Combinatorics
open scoped Classical

/-- A finite multipartite graph with no four pairwise adjacent vertices. -/
structure System (P : Type) where
  V : Type
  finite : Finite V
  G : SimpleGraph V
  part : V → P
  proper : ∀ {x y}, G.Adj x y → part x ≠ part y
  four : ∀ f : Fin 4 → V, ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)

private instance {P : Type} (S : System P) : Finite S.V := S.finite

variable {P : Type} [DecidableEq P] (S : System P) (a b : P)

private abbrev Alphabet := {e : S.V × S.V //
  S.part e.1 = a ∧ S.part e.2 = b ∧ S.G.Adj e.1 e.2}

private abbrev Lines (ι : Type) := Line (Alphabet S a b) ι

private instance linesFinite {ι : Type} [Finite ι] : Finite (Lines S a b ι) :=
  Finite.of_injective Line.idxFun (fun _ _ h => Line.ext h)

/-- Inside the two distinguished parts, a vertex is a word. Outside them, each
line has its own disjoint copy of the remaining vertices. -/
private abbrev Vertex (ι : Type) := (Bool × (ι → S.V)) ⊕ (Lines S a b ι × S.V)

variable {S a b} {ι : Type}

private def part : Vertex S a b ι → P
  | .inl (left, _) => if left then a else b
  | .inr (_, v) => S.part v

private def tag : Vertex S a b ι → Option (Lines S a b ι)
  | .inl _ => none
  | .inr (l, _) => some l

private def fits (l : Lines S a b ι) (x : Vertex S a b ι) :=
  tag x = none ∨ tag x = some l

private noncomputable def readAt (l : Lines S a b ι) : Vertex S a b ι → S.V
  | .inl (_, w) => w l.proper.choose
  | .inr (_, v) => v

private def liftedGraph : SimpleGraph (Vertex S a b ι) where
  Adj x y := part x ≠ part y ∧ (∃ l, fits l x ∧ fits l y) ∧
    ∀ l, fits l x → fits l y → S.G.Adj (readAt l x) (readAt l y)
  symm := ⟨fun _ _ ⟨hne, ⟨l, hx, hy⟩, h⟩ =>
    ⟨hne.symm, ⟨l, hy, hx⟩, fun k hk ht => (h k ht hk).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def liftSystem (S : System P) (a b : P) (ι : Type) [Finite ι]
    (l₀ : Lines S a b ι) : System P where
  V := Vertex S a b ι
  finite := inferInstance
  G := liftedGraph
  part := part
  proper := fun h => h.1
  four := by
    intro f hf
    obtain ⟨l, hl⟩ : ∃ l : Lines S a b ι, ∀ i, fits l (f i) := by
      by_cases htag : ∃ i l, tag (f i) = some l
      · obtain ⟨i,l,hi⟩ := htag
        refine ⟨l, fun j => ?_⟩
        by_cases hij : i = j
        · subst j; exact Or.inr hi
        obtain ⟨k,hki,hkj⟩ := (hf i j hij).2.1
        have heq : k = l := by simpa [fits,hi,eq_comm] using hki
        exact heq ▸ hkj
      · refine ⟨l₀, fun i => Or.inl ?_⟩
        cases h : tag (f i) with
        | none => rfl
        | some l => exact (htag ⟨i,l,h⟩).elim
    exact S.four (fun i => readAt l (f i)) (fun i j hij =>
      (hf i j hij).2.2 l (hl i) (hl j))

private def place (l : Lines S a b ι) (v : S.V) : Vertex S a b ι :=
  if S.part v = a then .inl (true, l.map (fun e => e.val.1) v)
  else if S.part v = b then .inl (false, l.map (fun e => e.val.2) v)
  else .inr (l,v)

private lemma part_place (l : Lines S a b ι) (v : S.V) : part (place l v) = S.part v := by
  by_cases ha : S.part v = a <;> by_cases hb : S.part v = b <;> simp_all [place, part]

private lemma fits_place (l : Lines S a b ι) (v : S.V) : fits l (place l v) := by
  by_cases ha : S.part v = a <;> by_cases hb : S.part v = b <;> simp_all [fits,tag,place]

private lemma read_place (l : Lines S a b ι) (v : S.V) : readAt l (place l v) = v := by
  unfold place
  split
  · simp [readAt, Line.map, l.proper.choose_spec]
  split
  · simp [readAt, Line.map, l.proper.choose_spec]
  · rfl

private lemma place_adj (hab : a ≠ b) (l : Lines S a b ι) {v w : S.V}
    (h : S.G.Adj v w) : liftedGraph.Adj (place l v) (place l w) := by
  refine ⟨by simpa only [part_place] using S.proper h,
    ⟨l,fits_place l v,fits_place l w⟩, ?_⟩
  intro k hv hw
  by_cases hkl : k = l
  · subst k; simpa only [read_place] using h
  have special (x : S.V) (hx : fits k (place l x)) : S.part x = a ∨ S.part x = b := by
    by_contra! hn
    simp [fits,tag,place,hn.1,hn.2,Ne.symm hkl] at hx
  have hvw := S.proper h
  rcases special v hv with hva | hvb <;> rcases special w hw with hwa | hwb
  · exact (hvw (hva.trans hwa.symm)).elim
  · cases hi : l.idxFun k.proper.choose with
    | none => simpa [readAt,place,hva,hwb,Ne.symm hab,Line.map,hi] using h
    | some e => simpa [readAt,place,hva,hwb,Ne.symm hab,Line.map,hi] using e.2.2.2
  · cases hi : l.idxFun k.proper.choose with
    | none => simpa [readAt,place,hvb,hwa,Ne.symm hab,Line.map,hi] using h
    | some e => simpa [readAt,place,hvb,hwa,Ne.symm hab,Line.map,hi] using e.2.2.2.symm
  · exact (hvw (hvb.trans hwb.symm)).elim


private def Preserves (S T : System P) (f : S.V → T.V) : Prop :=
  (∀ x, T.part (f x) = S.part x) ∧ ∀ {x y}, S.G.Adj x y → T.G.Adj (f x) (f y)

/-- A Hales–Jewett line makes every edge between a specified ordered pair
of parts have the same color in one copy of the original system. -/
private theorem focus (S : System P) (a b : P) {n : ℕ} (hn : 0 < n) :
    ∃ T : System P, ∀ C : T.V → T.V → Fin n, ∃ f : S.V → T.V,
      Preserves S T f ∧ ∃ d, ∀ x y, S.part x = a → S.part y = b → S.G.Adj x y →
        C (f x) (f y) = d := by
  classical
  let zero : Fin n := ⟨0, hn⟩
  by_cases hab : a = b
  · refine ⟨S, fun _ => ⟨id, ⟨fun _ => rfl, fun h => h⟩, zero, ?_⟩⟩
    intro x y hx hy hadj
    exact (S.proper hadj (hx.trans (hab.trans hy.symm))).elim
  obtain ⟨ι, hι, lines⟩ := Line.exists_mono_in_high_dimension (Alphabet S a b) (Fin n)
  let l₀ := (lines (fun _ => zero)).choose
  let T := liftSystem S a b ι l₀
  refine ⟨T, fun C => ?_⟩
  let words (w : ι → Alphabet S a b) : Fin n :=
    C (.inl (true, fun i => (w i).val.1)) (.inl (false, fun i => (w i).val.2))
  obtain ⟨l, d, hd⟩ := lines words
  refine ⟨place l, ⟨part_place l, place_adj hab l⟩, d, ?_⟩
  intro x y hx hy hxy
  let e : Alphabet S a b := ⟨(x,y),hx,hy,hxy⟩
  have hleft : (l.map (fun e : Alphabet S a b => e.val.1)) x =
      (fun i => (l e i).val.1) := Line.map_apply _ l e
  have hright : (l.map (fun e : Alphabet S a b => e.val.2)) y =
      (fun i => (l e i).val.2) := Line.map_apply _ l e
  simpa only [place,hx,hy,if_true,if_pos,Ne.symm hab,if_false,hleft,hright,words] using hd e

private theorem canonical (S : System P) {n : ℕ} (hn : 0 < n) (pairs : Finset (P × P)) :
    ∃ T : System P, ∀ C : T.V → T.V → Fin n, ∃ f : S.V → T.V,
      Preserves S T f ∧ ∃ d : P × P → Fin n, ∀ x y, S.G.Adj x y →
        (S.part x, S.part y) ∈ pairs → C (f x) (f y) = d (S.part x, S.part y) := by
  classical
  induction pairs using Finset.induction_on with
  | empty =>
    exact ⟨S,fun _ => ⟨id, ⟨fun _ => rfl, fun h => h⟩, fun _ => ⟨0,hn⟩,
      fun _ _ _ h => (Finset.notMem_empty _ h).elim⟩⟩
  | @insert p pairs _ ih =>
    obtain ⟨U,hu⟩ := ih
    obtain ⟨T,ht⟩ := focus U p.1 p.2 hn
    refine ⟨T,fun C => ?_⟩
    obtain ⟨g,hg,col,hcol⟩ := ht C
    obtain ⟨f,hf,d,hd⟩ := hu (fun x y => C (g x) (g y))
    refine ⟨g ∘ f, ⟨fun x => (hg.1 _).trans (hf.1 x), fun h => hg.2 (hf.2 h)⟩,
      fun q => if q = p then col else d q, ?_⟩
    intro x y hxy hp
    change C (g (f x)) (g (f y)) = if (S.part x,S.part y) = p then col else d _
    by_cases he : (S.part x, S.part y) = p
    · rw [if_pos he]
      exact hcol _ _ ((hf.1 _).trans (congrArg Prod.fst he))
        ((hf.1 _).trans (congrArg Prod.snd he)) (hf.2 hxy)
    · rw [if_neg he]
      exact hd _ _ hxy ((Finset.mem_insert.mp hp).resolve_left he)


/-- One isolated triangle over each triple of distinct template vertices.
Repeated parts simply suppress the corresponding edge. -/
private def seeds (P : Type) [Finite P] : System P where
  V := (Fin 3 → P) × Fin 3
  finite := inferInstance
  part := fun (t,i) => t i
  G := {
    Adj := fun (t,i) (u,j) => t = u ∧ t i ≠ u j
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }
  proper := fun h => h.2
  four := by
    intro f hf
    have inj : Function.Injective (fun i => (f i).2) := by
      intro i j hij
      by_contra hne
      obtain ⟨ht,hv⟩ := hf i j hne
      exact hv (congr ht hij)
    have h := Fintype.card_le_of_injective _ inj
    simp at h

private theorem folkman_of_indices {n : ℕ} (hn : 0 < n) {m : ℕ}
    (ramsey : ∀ C : Fin m × Fin m → Fin n, ∃ a b c, a < b ∧ b < c ∧
      C (a,b) = C (a,c) ∧ C (a,b) = C (b,c)) :
    ∃ (V : Type) (_ : Finite V) (H : SimpleGraph V), (completeGraph (Fin 4)).Free H ∧
      ∀ K : Fin n → SimpleGraph V, H = ⨆ i, K i → ∃ i, completeGraph (Fin 3) ⊑ K i := by
  classical
  let S := seeds (Fin m)
  obtain ⟨T,ht⟩ := canonical S hn Finset.univ
  refine ⟨T.V,T.finite,T.G,?_,?_⟩
  · rintro ⟨f⟩
    exact T.four f (fun _ _ hij => f.toHom.map_adj hij)
  intro K hK
  have cover {x y} (h : T.G.Adj x y) : ∃ i, (K i).Adj x y := by
    rwa [hK, SimpleGraph.iSup_adj] at h
  let C (x y : T.V) : Fin n := if h : T.G.Adj x y then (cover h).choose else ⟨0,hn⟩
  have covered {x y} (h : T.G.Adj x y) : (K (C x y)).Adj x y := by
    simpa only [C,dif_pos h] using (cover h).choose_spec
  obtain ⟨f,hf,d,hd⟩ := ht C
  obtain ⟨a,b,c,hab,hbc,hac,hbc'⟩ := ramsey d
  let t : Fin 3 → Fin m := ![a,b,c]
  let u (i : Fin 3) : S.V := (t,i)
  have g01 : S.G.Adj (u 0) (u 1) := ⟨rfl,hab.ne⟩
  have g02 : S.G.Adj (u 0) (u 2) := ⟨rfl,(hab.trans hbc).ne⟩
  have g12 : S.G.Adj (u 1) (u 2) := ⟨rfl,hbc.ne⟩
  have edge {x y : S.V} (h : S.G.Adj x y) : (K (d (S.part x,S.part y))).Adj (f x) (f y) :=
    (hd x y h (Finset.mem_univ _)) ▸ covered (hf.2 h)
  have e01 : (K (d (a,b))).Adj (f (u 0)) (f (u 1)) := edge g01
  have e02 : (K (d (a,b))).Adj (f (u 0)) (f (u 2)) := hac ▸ edge g02
  have e12 : (K (d (a,b))).Adj (f (u 1)) (f (u 2)) := hbc' ▸ edge g12
  have edges (i j : Fin 3) (hne : i ≠ j) : (K (d (a,b))).Adj (f (u i)) (f (u j)) := by
    fin_cases i <;> fin_cases j <;> first
      | exact (hne rfl).elim
      | exact e01
      | exact e02
      | exact e12
      | exact e01.symm
      | exact e02.symm
      | exact e12.symm
  refine ⟨d (a,b), ⟨⟨⟨fun i => f (u i), fun h => edges _ _ h⟩, ?_⟩⟩⟩
  intro i j hij
  by_contra hne
  exact (edges i j hne).ne hij

end OMA.Folkman

theorem OMA.solution : type_of% @Erdos596.erdos_596.variants.K4_K3_finite_ramsey := by
  intro n hn
  obtain ⟨m, hm⟩ := OMA.Folkman.triangle_ramsey hn
  obtain ⟨V, _, G, free, mono⟩ := OMA.Folkman.folkman_of_indices hn hm
  exact ⟨V, G, free, fun K hK => mono K hK.1⟩
