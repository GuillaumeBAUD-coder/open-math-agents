import FormalConjectures.ErdosProblems.«593»

/-! Increasing tuples with the one-place shift give a hypergraph of uncountable
chromatic cardinal whose small subhypergraphs admit a two-coloring. -/

namespace TupleShift593

open Cardinal Set

def Step {B : Type} [LinearOrder B] (n : ℕ) (u v : List B) : Prop :=
  ∃ x l y, l.length = n ∧ (x :: (l ++ [y])).Pairwise (· < ·) ∧
    u = x :: l ∧ v = l ++ [y]

lemma equal_step (n : ℕ) (C : Type) : ∃ (B : Type) (_ : LinearOrder B),
    ∀ c : List B → C, ∃ u v, Step n u v ∧ c u = c v := by
  induction n generalizing C with
  | zero =>
    let κ := Order.succ (#C)
    let B := κ.ord.ToType
    refine ⟨B, inferInstance, fun c => ?_⟩
    have hn : ¬ Function.Injective (fun x : B => c [x]) := by
      intro hi
      have h := Cardinal.mk_le_of_injective hi
      change #κ.ord.ToType ≤ #C at h
      simp [κ] at h
    rw [Function.Injective] at hn
    push Not at hn
    obtain ⟨x, y, he, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨[x], [y], ⟨x, [], y, rfl, by simpa using h, rfl, rfl⟩, he⟩
    · exact ⟨[y], [x], ⟨y, [], x, rfl, by simpa using h, rfl, rfl⟩, he.symm⟩
  | succ n ih =>
    obtain ⟨B, inst, hB⟩ := ih (Set C)
    refine ⟨B, inst, fun c => ?_⟩
    let g (u : List B) : Set C := {a | ∃ z, (∀ b ∈ u, b < z) ∧ c (u ++ [z]) = a}
    obtain ⟨_, _, ⟨x, l, y, hl, hxy, rfl, rfl⟩, he⟩ := hB g
    have hlast : ∀ b ∈ x :: l, b < y := by
      have hp : ((x :: l) ++ [y]).Pairwise (· < ·) := hxy
      exact fun b hb => (List.pairwise_append.mp hp).2.2 b hb y (by simp)
    have hm : c ((x :: l) ++ [y]) ∈ g (x :: l) := ⟨y, hlast, rfl⟩
    rw [he] at hm
    obtain ⟨z, hz, hez⟩ := hm
    have hxz : x < z := lt_trans (hlast x (by simp)) (hz y (by simp))
    refine ⟨_, _, ⟨x, l ++ [y], z, by simp [hl], ?_, rfl, rfl⟩, hez.symm⟩
    change ((x :: (l ++ [y])) ++ [z]).Pairwise (· < ·)
    apply List.pairwise_append.mpr
    refine ⟨hxy, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    rcases List.mem_cons.mp ha with rfl | h
    · exact hxz
    · exact hz _ h

lemma head_lt {B : Type} [LinearOrder B] {n u v} (h : @Step B _ n u v) :
    ∀ d : B, u.headD d < v.headD d := by
  obtain ⟨x, l, y, _, hp, rfl, rfl⟩ := h
  intro d
  cases l with
  | nil => simpa using (List.pairwise_cons.mp hp).1 y (by simp)
  | cons z l => simpa using (List.pairwise_cons.mp hp).1 z (by simp)

def triples (B : Type) [LinearOrder B] (n : ℕ) : UniformHypergraph (List B) 3 where
  vertexSet := Set.univ
  edgeSet := {e | ∃ a b c, Step n a b ∧ Step n b c ∧ e = {a,b,c}}
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := by
    rintro _ ⟨a,b,c,hab,hbc,rfl⟩
    obtain ⟨d, hd⟩ := hab
    have hab' : Step n a b := ⟨d, hd⟩
    have h₁ := head_lt hab' d
    have h₂ := head_lt hbc d
    have h₃ := lt_trans h₁ h₂
    have ab : a ≠ b := fun h => h₁.ne (congrArg (fun l : List B => l.headD d) h)
    have ac : a ≠ c := fun h => h₃.ne (congrArg (fun l : List B => l.headD d) h)
    have bc : b ≠ c := fun h => h₂.ne (congrArg (fun l : List B => l.headD d) h)
    norm_num [Set.encard_insert_of_notMem, ab, ac, bc]

lemma large_chrom {B : Type} [LinearOrder B] {n : ℕ}
    (hm : ∀ c : List B → ℕ × Bool, ∃ u v, Step n u v ∧ c u = c v) :
    ℵ₀ < (triples B n).chromaticCardinal := by
  classical
  let H := triples B n
  by_contra! hle
  let colors : Set Cardinal.{0} :=
    {κ | ∃ C : Type, #C = κ ∧ ∃ f : List B → C, H.IsProperColoring f}
  have hn : colors.Nonempty := ⟨_, List B, rfl, id,
    H.isProperColoring_of_injective (by decide) Function.injective_id⟩
  have hmem : H.chromaticCardinal ∈ colors := csInf_mem hn
  obtain ⟨C, rfl', f, hf⟩ := hmem
  have hc : #C ≤ ℵ₀ := rfl'.trans_le hle
  have : Countable C := Cardinal.mk_le_aleph0_iff.mp hc
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat C
  let seen (v : List B) : Prop := ∃ u, Step n u v ∧ f u = f v
  obtain ⟨v,w,hvw,he⟩ := hm (fun v => (j (f v), decide (seen v)))
  have hvw' : f v = f w := hj (congrArg Prod.fst he)
  have hw : seen w := ⟨v,hvw,hvw'⟩
  have hv : seen v := by
    have hs := congrArg Prod.snd he
    simpa [hw] using hs
  obtain ⟨u,huv,huv'⟩ := hv
  have hmemb : {u,v,w} ∈ H.edgeSet := ⟨u,v,w,huv,hvw,rfl⟩
  obtain ⟨a,ha,b,hb,hab⟩ := hf _ hmemb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

lemma local_color {B W : Type} [LinearOrder B] [Fintype W] (f : W → List B) :
    ∃ color : W → Fin 2, ∀ a b, Step (Fintype.card W + 1) (f a) (f b) →
      color a ≠ color b := by
  classical
  let heads := Finset.univ.image (fun w : W => (f w).head?)
  let miss (b : B) := decide (some b ∉ heads)
  let color (a : W) : Fin 2 := ⟨(f a).findIdx miss % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨color, ?_⟩
  rintro a b ⟨x,l,y,hl,hp,ha,hb⟩ he
  have hm : some x ∈ heads := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [ha]⟩
  have hnod : l.Nodup := by
    have := (List.pairwise_append.mp (List.pairwise_cons.mp hp).2).1
    exact this.imp (fun h => ne_of_lt h)
  have hex : ∃ z ∈ l, some z ∉ heads := by
    by_contra! h
    have hcard := Finset.card_le_card_of_injOn (s := l.toFinset) (t := heads) some
      (fun z hz => h z (by simpa using hz)) (fun _ _ _ _ eq => Option.some.inj eq)
    rw [List.toFinset_card_of_nodup hnod, hl] at hcard
    have hle : heads.card ≤ Fintype.card W := Finset.card_image_le.trans_eq (Finset.card_univ)
    omega
  obtain ⟨z,hz,hz'⟩ := hex
  have hidx : l.findIdx miss < l.length :=
    List.findIdx_lt_length_of_exists ⟨z, hz, by simp [miss, hz']⟩
  have eq := congrArg Fin.val he
  change (f a).findIdx miss % 2 = (f b).findIdx miss % 2 at eq
  rw [ha,hb,List.findIdx_cons,List.findIdx_append] at eq
  have hx : miss x = false := by simp [miss, hm]
  simp only [hx, Bool.cond_false, hidx, if_true] at eq
  omega

end TupleShift593

theorem OMA.solution : type_of% @Erdos593.erdos_593.variants.obligatory_implies_two_colorable := by
  classical
  intro W _ F ho
  obtain ⟨B, inst, hm⟩ := TupleShift593.equal_step (Fintype.card W + 1) (ℕ × Bool)
  obtain ⟨f, _, hf⟩ := ho _ (TupleShift593.triples B _) (TupleShift593.large_chrom hm)
  obtain ⟨c, hc⟩ := TupleShift593.local_color f
  refine ⟨c, fun e he => ?_⟩
  have him := hf (show f '' e ∈ (F.toHypergraph.image f).edgeSet from ⟨e, he, rfl⟩)
  obtain ⟨a,b,d,hab,_,heq⟩ := him
  obtain ⟨x,hx,hfx⟩ : a ∈ f '' e := heq.symm ▸ Set.mem_insert _ _
  obtain ⟨y,hy,hfy⟩ : b ∈ f '' e := heq.symm ▸ (by simp)
  exact ⟨x,hx,y,hy,hc x y (hfx ▸ hfy ▸ hab)⟩
