import FormalConjectures.ErdosProblems.«111»

/-! The shift-graph method of Erdős, Hajnal and Szemerédi, "On almost bipartite
large chromatic graphs" (1982), Theorem 3(a), yields the finite deletion estimate.
To obtain chromatic cardinal exactly aleph-one, label arcs by the level of a
coordinate on which their endpoints differ and retain only adjacencies between
different labels. A countable coloring would encode every subset of the coordinate
domain by its incoming colors, a countable cutoff, and its restriction below that
cutoff. The beth blocks ensure there are too few such codes. -/

namespace OMA.Almost111

open Cardinal Ordinal Set Filter SimpleGraph
open scoped Cardinal Ordinal

abbrev Level := (ω₁ : Ordinal.{0}).ToType
noncomputable def firstLevel : Level := Ordinal.ToType.mk ⟨0,Ordinal.omega_pos _⟩
noncomputable def nextLevel (i : Level) : Level :=
  Ordinal.ToType.mk ⟨Order.succ i.toOrd.val,by
    change Order.succ i.toOrd.val < (ω₁ : Ordinal.{0})
    exact (Cardinal.isSuccLimit_omega 1).succ_lt
      (show i.toOrd.val < (ω₁ : Ordinal.{0}) from i.toOrd.property)⟩

lemma next_index (i : Level) : (nextLevel i).toOrd.val = Order.succ i.toOrd.val := by
  simp [nextLevel, Ordinal.ToType.toOrd]

lemma bounded_levels (f : ℕ → Level) : ∃ b : Level, ∀ n, f n ≤ b := by
  let b : Set.Iio (ω₁ : Ordinal.{0}) := ⟨⨆ n, (f n).toOrd.val,
    Ordinal.iSup_lt_omega_one (fun n => (f n).toOrd.property)⟩
  refine ⟨Ordinal.ToType.mk b,fun n => ?_⟩
  apply Ordinal.ToType.mk.symm.le_iff_le.mp
  rw [OrderIso.symm_apply_apply]
  change (f n).toOrd.val ≤ ⨆ i, (f i).toOrd.val
  exact le_ciSup Ordinal.bddAbove_of_small n

def Block (i : Level) := (ℶ_ i.toOrd.val).out
abbrev Domain := (i : Level) × Block i
abbrev Prefix (i : Level) := {d : Domain // d.1 ≤ i}

lemma block_size (i : Level) : #(Block i) = ℶ_ i.toOrd.val := Cardinal.mk_out _
lemma level_size : #Level = ℵ₁ := by rw [Cardinal.mk_toType,Ordinal.card_omega]

lemma block_le_domain (i : Level) : ℶ_ i.toOrd.val ≤ #Domain := by
  rw [← block_size]
  exact Cardinal.mk_le_of_injective (sigma_mk_injective (i := i))

lemma omega_one_le_next (i : Level) : ℵ₁ ≤ ℶ_ (nextLevel i).toOrd.val := by
  rw [next_index]
  apply (Cardinal.aleph_le_beth 1).trans (Cardinal.beth_le_beth.mpr ?_)
  simp

lemma prefix_size (i : Level) : #(Prefix i) ≤ ℶ_ (nextLevel i).toOrd.val := by
  classical
  have hle {j : Level} (hj : j ≤ i) : #(Block j) ≤ #(Block i) := by
    rw [block_size,block_size]
    exact Cardinal.beth_le_beth.mpr (Ordinal.ToType.mk.symm.monotone hj)
  let emb {j : Level} (hj : j ≤ i) : Block j ↪ Block i := Classical.choice ((Cardinal.le_def _ _).mp (hle hj))
  let f (x : Prefix i) : Level × Block i := (x.val.1,emb x.property x.val.2)
  have inj : Function.Injective f := by
    rintro ⟨⟨j,x⟩,hx⟩ ⟨⟨k,y⟩,hy⟩ eq
    obtain rfl : j = k := congrArg Prod.fst eq
    have eq' : x = y := (emb hx).injective (congrArg Prod.snd eq)
    subst y
    rfl
  apply (Cardinal.mk_le_of_injective inj).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_id, level_size, block_size]
  apply (mul_le_mul' (omega_one_le_next i)
    (Cardinal.beth_le_beth.mpr (show i.toOrd.val ≤ (nextLevel i).toOrd.val by rw [next_index]; exact Order.le_succ _))).trans
  exact (Cardinal.mul_eq_self (Cardinal.aleph0_le_beth _)).le

lemma prefix_sets_le (i : Level) : #(Set (Prefix i)) ≤ #Domain := by
  rw [Cardinal.mk_set]
  calc (2 : Cardinal) ^ #(Prefix i) ≤ 2 ^ ℶ_ (nextLevel i).toOrd.val :=
        Cardinal.power_le_power_left two_ne_zero (prefix_size i)
       _ = ℶ_ (nextLevel (nextLevel i)).toOrd.val := by rw [next_index (nextLevel i),Cardinal.beth_succ]
       _ ≤ _ := block_le_domain _

noncomputable def piece (x y : Set Domain) (h : x ≠ y) : Domain :=
  Classical.choose (Set.ext_iff.not.mp h |> Classical.not_forall.mp)

lemma piece_diff (x y : Set Domain) (h : x ≠ y) : ¬ (piece x y h ∈ x ↔ piece x y h ∈ y) :=
  Classical.choose_spec (Set.ext_iff.not.mp h |> Classical.not_forall.mp)

abbrev Arc := {p : Set Domain × Set Domain // p.1 ≠ p.2}
noncomputable def label (e : Arc) : Level := (piece e.val.1 e.val.2 e.property).1

lemma large_difference (pattern : Set Domain → Set ℕ) (cut : Set Domain → Level) :
    ∃ e : Arc, pattern e.val.1 = pattern e.val.2 ∧ cut e.val.1 < label e := by
  classical
  by_contra! no
  let enc (i : Level) : Set (Prefix i) ↪ Domain := Classical.choice ((Cardinal.le_def _ _).mp (prefix_sets_le i))
  let f (x : Set Domain) : Set ℕ × Level × Domain :=
    (pattern x,cut x,enc (cut x) (Subtype.val ⁻¹' x))
  have inj : Function.Injective f := by
    intro x y eq
    by_contra ne
    let e : Arc := ⟨(x,y),ne⟩
    have hp : pattern x = pattern y := congrArg Prod.fst eq
    have hc : cut x = cut y := congrArg (Prod.fst ∘ Prod.snd) eq
    have codes : enc (cut x) (Subtype.val ⁻¹' x) = enc (cut y) (Subtype.val ⁻¹' y) :=
      congrArg (Prod.snd ∘ Prod.snd) eq
    rw [← hc] at codes
    have hs := (enc (cut x)).injective codes
    have leq : (piece x y ne).1 ≤ cut x := no e hp
    exact piece_diff x y ne (Set.ext_iff.mp hs ⟨piece x y ne,leq⟩)
  have hD : ℵ₁ ≤ #Domain := (omega_one_le_next firstLevel).trans (block_le_domain _)
  have hN : #(Set ℕ) ≤ #Domain := by
    rw [Cardinal.mk_set,Cardinal.mk_nat]
    change 𝔠 ≤ #Domain
    rw [← Cardinal.beth_one]
    apply (Cardinal.beth_le_beth.mpr (show 1 ≤ (nextLevel firstLevel).toOrd.val by
      rw [next_index]; simp)).trans (block_le_domain _)
  have hinfinite : ℵ₀ ≤ #Domain := aleph0_lt_aleph_one.le.trans hD
  apply (Cardinal.cantor #Domain).not_ge
  rw [← Cardinal.mk_set]
  apply (Cardinal.mk_le_of_injective inj).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_id,level_size]
  calc #(Set ℕ) * (ℵ₁ * #Domain) ≤ #Domain * (#Domain * #Domain) := by gcongr
       _ = #Domain := by rw [Cardinal.mul_eq_self hinfinite,Cardinal.mul_eq_self hinfinite]

noncomputable def graph : SimpleGraph Arc where
  Adj e f := (e.val.2 = f.val.1 ∨ f.val.2 = e.val.1) ∧ label e ≠ label f
  symm := ⟨fun _ _ h => ⟨h.1.elim (fun h => Or.inr h) (fun h => Or.inl h),h.2.symm⟩⟩
  loopless := ⟨by intro e h; exact h.2 rfl⟩

lemma not_colorable_nat (c : graph.Coloring ℕ) : False := by
  classical
  let pattern (x : Set Domain) := {n : ℕ | ∃ e : Arc, e.val.2 = x ∧ c e = n}
  let chosen (x : Set Domain) (n : ℕ) : Level :=
    if h : n ∈ pattern x then label (Classical.choose h) else firstLevel
  choose cut hcut using fun x => bounded_levels (chosen x)
  obtain ⟨e,he,hh⟩ := large_difference pattern cut
  have hn : c e ∈ pattern e.val.1 := he ▸ ⟨e,rfl,rfl⟩
  let a := Classical.choose hn
  have ha : a.val.2 = e.val.1 ∧ c a = c e := Classical.choose_spec hn
  have hlabel : label a = label e := by
    by_contra h
    exact c.valid (show graph.Adj a e from ⟨Or.inl ha.1,h⟩) ha.2
  have hl := hcut e.val.1 (c e)
  rw [show chosen e.val.1 (c e) = label a by simp [chosen,hn,a],hlabel] at hl
  exact hh.not_ge hl

lemma chromatic_graph : graph.chromaticCardinal = ℵ₁ := by
  classical
  let proper : graph.Coloring Level := SimpleGraph.Coloring.mk label (fun h => h.2)
  have hn : ({κ : Cardinal | ∃ (C : Type) (_ : #C = κ), Nonempty (graph.Coloring C)}).Nonempty :=
    ⟨_,Level,rfl,⟨proper⟩⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) ⟨Level,level_size,⟨proper⟩⟩
  · apply le_csInf hn
    rintro _ ⟨C,rfl,⟨c⟩⟩
    by_contra! h
    have hC : #C ≤ ℵ₀ := by simpa [Cardinal.aleph_one_le_iff] using not_le.mpr h
    obtain ⟨g⟩ := (Cardinal.le_def C ℕ).mp (by simpa using hC)
    exact not_colorable_nat (SimpleGraph.Coloring.mk (g ∘ c) (fun h he => c.valid h (g.injective he)))

/- In a finite set of arcs, color an arc by whether the indegree of its tail is large.
At a light junction there are few incoming arcs. At a heavy junction, a monochromatic
predecessor is determined by its heavy tail, and there are few heavy tails. -/

lemma deletion_bound (S : Set Arc) [Fintype S] :
    Erdos111.bipartiteDistance (graph.induce S) ≤ Fintype.card S * ((Fintype.card S).sqrt + 1) := by
  classical
  let n := Fintype.card S
  let t := n.sqrt + 1
  let head (a : S) := a.val.val.2
  let tail (a : S) := a.val.val.1
  let inc (x : Set Domain) := Finset.univ.filter (fun a : S => head a = x)
  let L := (Finset.univ.image head).filter (fun x => t ≤ (inc x).card)
  have heavy (x : Set Domain) : x ∈ L ↔ t ≤ (inc x).card := by
    refine ⟨fun hx => (Finset.mem_filter.mp hx).2, fun hx => Finset.mem_filter.mpr ⟨?_,hx⟩⟩
    have hp : 0 < (inc x).card := lt_of_lt_of_le (Nat.succ_pos _) hx
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  have hLt : L.card ≤ t := by
    have hsum : L.card * t ≤ n := calc
      L.card * t = ∑ _ ∈ L, t := by simp
      _ ≤ ∑ x ∈ L, (inc x).card := Finset.sum_le_sum (fun x hx => (heavy x).mp hx)
      _ = (Finset.univ.filter (fun a : S => head a ∈ L)).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ n := by simpa [n] using Finset.card_filter_le Finset.univ (fun a : S => head a ∈ L)
    have hsq : n < t * t := Nat.sqrt_lt.mp (Nat.lt_succ_self n.sqrt)
    by_contra! h
    exact (hsq.not_ge ((Nat.mul_le_mul_right t h.le).trans hsum))
  let color (a : S) : Fin 2 := if tail a ∈ L then 1 else 0
  let bad (b : S) := Finset.univ.filter (fun a : S => head a = tail b ∧ color a = color b)
  have bad_le (b : S) : (bad b).card ≤ t := by
    by_cases hb : tail b ∈ L
    · refine (Finset.card_le_card_of_injOn tail (t := L) ?_ ?_).trans hLt
      · intro a ha
        have hc := (Finset.mem_filter.mp ha).2.2
        simpa [color,hb] using hc
      · intro a ha d hd eq
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext eq ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp hd).2.1.symm)
    · refine (Finset.card_le_card (show bad b ⊆ inc (tail b) from ?_)).trans (le_of_lt ?_)
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2.1⟩
      · exact lt_of_not_ge (fun hc => hb ((heavy _).mpr hc))
  let G := graph.induce S
  let H : SimpleGraph S :=
    { Adj := fun a b => G.Adj a b ∧ color a ≠ color b
      symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
      loopless := ⟨fun _ h => h.2 rfl⟩ }
  let pairs (b : S) := (bad b).image (fun a => s(a,b))
  let U := Finset.univ.biUnion pairs
  have contains : G.edgeSet \ H.edgeSet ⊆ (U : Set (Sym2 S)) := by
    intro p
    induction p using Sym2.inductionOn with
    | _ a b =>
      rintro ⟨hg,hh⟩
      have hc : color a = color b := by
        by_contra h
        exact hh (show H.Adj a b from ⟨hg,h⟩)
      have dir : head a = tail b ∨ head b = tail a := (show graph.Adj a.val b.val from hg).1
      rcases dir with hd | hd
      · exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,
          Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,hc⟩,rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,
          Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,hc.symm⟩,Sym2.eq_swap⟩⟩
  have count : (G.edgeSet \ H.edgeSet).ncard ≤ n*t := calc
    _ ≤ (U : Set (Sym2 S)).ncard := Set.ncard_le_ncard contains
    _ = U.card := Set.ncard_coe_finset _
    _ ≤ ∑ b : S, (pairs b).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : S, t := Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (bad_le b))
    _ = n*t := by simp [n]
  apply le_trans (b := (G.edgeSet \ H.edgeSet).ncard) _ count
  unfold Erdos111.bipartiteDistance
  apply Nat.sInf_le
  exact ⟨H,fun _ _ h => h.1,⟨SimpleGraph.Coloring.mk color (fun h => h.2)⟩,rfl⟩

lemma bound_hG (n : ℕ) (hn : 1 ≤ n) : Erdos111.hG graph n ≤ n*(n.sqrt+1) := by
  unfold Erdos111.hG
  apply csSup_le'
  rintro k ⟨S,hS,rfl⟩
  let : Fintype S := (Set.finite_of_ncard_pos (show 0 < S.ncard by omega)).fintype
  simpa [Set.fintypeCard_eq_ncard,hS] using deletion_bound S

lemma asymp : (fun n : ℕ => (Erdos111.hG graph n : ℝ)) =O[atTop]
    (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have h₁ : (1:ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hr : (n.sqrt:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have cast_bound : (Erdos111.hG graph n : ℝ) ≤ (n:ℝ)*((n.sqrt:ℝ)+1) := by
    exact_mod_cast bound_hG n hn
  calc (Erdos111.hG graph n : ℝ) ≤ _ := cast_bound
       _ ≤ (n:ℝ) * (Real.sqrt n + Real.sqrt n) := by gcongr
       _ = 2 * ((n:ℝ) * Real.sqrt n) := by ring
       _ = 2 * (n:ℝ) ^ (3/2:ℝ) := by
         rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hnpos, Real.rpow_one, Real.sqrt_eq_rpow]

end OMA.Almost111

theorem OMA.solution : type_of% @Erdos111.erdos_111.variants.upper_bound_existence :=
  ⟨OMA.Almost111.Arc, OMA.Almost111.graph, OMA.Almost111.chromatic_graph, OMA.Almost111.asymp⟩
