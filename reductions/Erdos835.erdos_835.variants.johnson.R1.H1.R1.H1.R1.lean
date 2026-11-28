import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

/-!
# Two-choice extension for the punctured Johnson graph
-/

open Finset
open Relation

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1

/-- A coloring after deleting a third point, with the two missing colors at each
boundary vertex and a reachability test on those choices. -/
def H1 : Prop :=
  ∃ (k : ℕ) (x y z : Fin (2 * k)), 3 ≤ k ∧ Even k ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ∃ (c : Finset (Fin (2 * k)) → Fin (k + 1))
      (p : Finset (Fin (2 * k)) → Bool → Fin (k + 1)),
      let B := fun s : Finset (Fin (2 * k)) => s.card + 1 = k ∧ x ∈ s ∧ y ∉ s ∧ z ∉ s
      let r := fun u v : Finset (Fin (2 * k)) × Bool =>
        B u.1 ∧ B v.1 ∧ (u.1 ∩ v.1).card + 2 = k ∧ p u.1 u.2 = p v.1 (!v.2)
      (∀ s, B s → ∀ a ∉ s, ∀ b ∉ s, a ≠ y → b ≠ y → a ≠ z → b ≠ z → a ≠ b →
        c (insert a s) ≠ c (insert b s)) ∧
      (∀ s, B s → Function.Injective (p s) ∧
        ∀ a ∉ s, a ≠ y → a ≠ z → ∀ i, p s i ≠ c (insert a s)) ∧
      (∀ s, ¬ (ReflTransGen r (s, false) (s, true) ∧ ReflTransGen r (s, true) (s, false)))

/-- The reachability criterion for satisfiability of binary implications with
their contrapositives. -/
def H2 : Prop :=
  ∀ (α : Type) [Fintype α] (r : α × Bool → α × Bool → Prop),
    (∀ u v, r u v → r (v.1, !v.2) (u.1, !u.2)) →
    (∀ s, ¬ (ReflTransGen r (s, false) (s, true) ∧ ReflTransGen r (s, true) (s, false))) →
    ∃ f : α → Bool, ∀ u v, r u v → f u.1 = u.2 → f v.1 = v.2

theorem main : H1 → H2 → OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H1 := by
  classical
  rintro ⟨k, x, y, z, hk, he, hxy, hxz, hyz, c, p, hbase, hpal, hpath⟩ hsat
  let B := fun s : Finset (Fin (2 * k)) => s.card + 1 = k ∧ x ∈ s ∧ y ∉ s ∧ z ∉ s
  let r := fun u v : Finset (Fin (2 * k)) × Bool =>
    B u.1 ∧ B v.1 ∧ (u.1 ∩ v.1).card + 2 = k ∧ p u.1 u.2 = p v.1 (!v.2)
  obtain ⟨f, hf⟩ := hsat _ r (by
    rintro ⟨s, i⟩ ⟨t, j⟩ ⟨hs, ht, hcard, heq⟩
    exact ⟨ht, hs, by simpa only [inter_comm] using hcard, by simpa using heq.symm⟩) hpath
  let C (v : Finset (Fin (2 * k))) :=
    if z ∈ v then p (v.erase z) (f (v.erase z)) else c v
  refine ⟨k, x, y, hk, he, hxy, C, ?_⟩
  intro s hs hxs hys a ha b hb hay hby hab
  by_cases hzs : z ∈ s
  · let t := s.erase z
    have htpos := Finset.card_pos.mpr ⟨z, hzs⟩
    have htcard : t.card + 2 = k := by
      simp only [t, Finset.card_erase_of_mem hzs]
      omega
    have hzfree : z ∉ t := notMem_erase _ _
    have hxt : x ∈ t := Finset.mem_erase.mpr ⟨hxz, hxs⟩
    have hyt : y ∉ t := fun h => hys (erase_subset _ _ h)
    have hat : a ∉ t := fun h => ha (erase_subset _ _ h)
    have hbt : b ∉ t := fun h => hb (erase_subset _ _ h)
    have haz : a ≠ z := fun h => ha (h ▸ hzs)
    have hbz : b ≠ z := fun h => hb (h ▸ hzs)
    have hB (u : Fin (2 * k)) (hut : u ∉ t) (huy : u ≠ y) (huz : u ≠ z) :
        B (insert u t) := by
      refine ⟨?_, mem_insert_of_mem hxt, ?_, ?_⟩
      · simpa only [card_insert_of_notMem hut, Nat.add_assoc] using htcard
      · simpa [Ne.symm huy] using hyt
      · simpa [Ne.symm huz] using hzfree
    have hInt : insert a t ∩ insert b t = t := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    have hColor : p (insert a t) (f (insert a t)) ≠ p (insert b t) (f (insert b t)) := by
      intro hEq
      have hAdj : (insert a t ∩ insert b t).card + 2 = k := by rwa [hInt]
      have hEdge : r (insert a t, f (insert a t)) (insert b t, !(f (insert b t))) :=
        ⟨hB a hat hay haz, hB b hbt hby hbz, hAdj, by simpa using hEq⟩
      have hOpp := hf _ _ hEdge rfl
      cases f (insert b t) <;> simp at hOpp
    simpa [C, hzs, erase_insert_of_ne haz, erase_insert_of_ne hbz, t] using hColor
  · have hsB : B s := ⟨hs, hxs, hys, hzs⟩
    by_cases haz : a = z
    · subst a
      simpa [C, hzs, hab, Ne.symm hab, erase_insert hzs] using
        (hpal s hsB).2 b hb hby hab.symm (f s)
    · by_cases hbz : b = z
      · subst b
        simpa [C, hzs, hab, Ne.symm hab, erase_insert hzs] using
          ((hpal s hsB).2 a ha hay hab (f s)).symm
      · simpa [C, hzs, Ne.symm haz, Ne.symm hbz] using
          hbase s hsB a ha b hb hay hby haz hbz hab

/-- A maximal consistent set of literals closed under reachability assigns
every variable, since at least one choice can be added at each unassigned variable. -/
lemma binary_implications : H2 := by
  classical
  intro α _ r hr hnocycle
  let neg (u : α × Bool) : α × Bool := (u.1, !u.2)
  have invol : Function.Involutive neg := by
    rintro ⟨a, b⟩
    cases b <;> rfl
  have neg_neg (v : α × Bool) : neg (neg v) = v := invol v
  have reverse_path {u v : α × Bool} (h : ReflTransGen r u v) :
      ReflTransGen r (neg v) (neg u) := by
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact (ReflTransGen.single (hr _ _ hstep)).trans ih
  let valid (T : Finset (α × Bool)) :=
    (∀ u ∈ T, neg u ∉ T) ∧ (∀ u ∈ T, ∀ v, ReflTransGen r u v → v ∈ T)
  let sets := (univ : Finset (Finset (α × Bool))).filter valid
  have hempty : (∅ : Finset (α × Bool)) ∈ sets := by simp [sets, valid]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image sets Finset.card ⟨∅, hempty⟩
  have hv : valid T := (Finset.mem_filter.mp hT).2
  have total (a : α) : (a, false) ∈ T ∨ (a, true) ∈ T := by
    by_contra! h
    have extend (u : α × Bool) (hu : u ∉ T) (hnu : neg u ∉ T)
        (hp : ¬ ReflTransGen r u (neg u)) : False := by
      let reach := (univ : Finset (α × Bool)).filter (ReflTransGen r u)
      have hreach (v : α × Bool) : v ∈ reach ↔ ReflTransGen r u v := by simp [reach]
      let U := T ∪ reach
      have hU : valid U := by
        constructor
        · intro v hvU hnvU
          rcases Finset.mem_union.mp hvU with hvt | hvr <;>
            rcases Finset.mem_union.mp hnvU with hnvt | hnvr
          · exact hv.1 v hvt hnvt
          · exact hnu (hv.2 v hvt _ (by simpa only [neg_neg] using reverse_path ((hreach _).1 hnvr)))
          · exact hnu (hv.2 _ hnvt _ (reverse_path ((hreach _).1 hvr)))
          · exact hp (((hreach _).1 hvr).trans
              (by simpa only [neg_neg] using reverse_path ((hreach _).1 hnvr)))
        · intro v hvU w hvw
          rcases Finset.mem_union.mp hvU with hvt | hvr
          · exact Finset.mem_union_left _ (hv.2 v hvt w hvw)
          · exact Finset.mem_union_right _ ((hreach _).2 (((hreach _).1 hvr).trans hvw))
      have hstrict : T ⊂ U := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_union_left, fun heq =>
          hu (heq ▸ Finset.mem_union_right T ((hreach _).2 .refl))⟩
      exact (Finset.card_lt_card hstrict).not_ge (hmax U (Finset.mem_filter.mpr ⟨mem_univ _, hU⟩))
    by_cases hft : ReflTransGen r (a, false) (a, true)
    · exact extend (a, true) h.2 h.1 (fun htf => hnocycle a ⟨hft, htf⟩)
    · exact extend (a, false) h.1 h.2 hft
  let f (a : α) : Bool := if (a, true) ∈ T then true else false
  have hf (a : α) (b : Bool) : f a = b ↔ (a, b) ∈ T := by
    cases b
    · by_cases h : (a, true) ∈ T
      · have hn : (a, false) ∉ T := hv.1 (a, true) h
        simp [f, h, hn]
      · have hm := (total a).resolve_right h
        simp [f, h, hm]
    · simp [f]
  refine ⟨f, ?_⟩
  rintro ⟨a, b⟩ ⟨c, d⟩ hab hf'
  exact (hf c d).2 (hv.2 _ ((hf a b).1 hf') _ (.single hab))

lemma missing_pair {k : ℕ} {y z : Fin (2 * k)} {s : Finset (Fin (2 * k))}
    {c : Finset (Fin (2 * k)) → Fin (k + 1)}
    (hs : s.card + 1 = k) (hy : y ∉ s) (hz : z ∉ s) (hyz : y ≠ z) :
    ∃ m : Fin (k + 1), m ≠ c (insert z s) ∧
      ∀ a ∉ s, a ≠ y → a ≠ z → m ≠ c (insert a s) := by
  classical
  let allowed := (insert y s)ᶜ
  let used := allowed.image (fun a => c (insert a s))
  have ha : allowed.card = k := by
    change ((insert y s)ᶜ : Finset (Fin (2 * k))).card = k
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hy, hs]
    omega
  have hlt : used.card < (univ : Finset (Fin (k + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact ((Finset.card_image_le : used.card ≤ allowed.card).trans_eq ha).trans_lt
      (Nat.lt_succ_self k)
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have absent (a : Fin (2 * k)) (ha : a ∉ s) (hay : a ≠ y) : m ≠ c (insert a s) := by
    intro he
    exact hm (Finset.mem_image.mpr ⟨a, by simpa [allowed, hay] using ha, he.symm⟩)
  exact ⟨m, absent z hz hyz.symm, fun a ha hay _ => absent a ha hay⟩

/-- Restricting a full coloring gives a partial coloring whose implication
graph satisfies the reachability criterion. -/
lemma restrict_coloring : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H1 → H1 := by
  classical
  rintro ⟨k, x, y, hk, he, hxy, c, hc⟩
  have hlt : ({x, y} : Finset (Fin (2 * k))).card < (univ : Finset (Fin (2 * k))).card := by
    rw [card_insert_of_notMem (by simpa using hxy), card_singleton, card_univ, Fintype.card_fin]
    omega
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hxz : x ≠ z := fun h => hz (h ▸ mem_insert_self _ _)
  have hyz : y ≠ z := fun h => hz (h ▸ mem_insert_of_mem (mem_singleton_self _))
  let B := fun s : Finset (Fin (2 * k)) => s.card + 1 = k ∧ x ∈ s ∧ y ∉ s ∧ z ∉ s
  let p (s : Finset (Fin (2 * k))) (b : Bool) : Fin (k + 1) :=
    if b then c (insert z s) else
      if h : B s then (missing_pair (c := c) h.1 h.2.2.1 h.2.2.2 hyz).choose else 0
  refine ⟨k, x, y, z, hk, he, hxy, hxz, hyz, c, p, ?_, ?_, ?_⟩
  · intro s hs a ha b hb hay hby _ _ hab
    exact hc s hs.1 hs.2.1 hs.2.2.1 a ha b hb hay hby hab
  · intro s hs
    change B s at hs
    have pfalse : p s false = (missing_pair (c := c) hs.1 hs.2.2.1 hs.2.2.2 hyz).choose := by
      simp only [p, Bool.false_eq_true, ↓reduceIte, dif_pos hs]
    have ptrue : p s true = c (insert z s) := rfl
    have other := (missing_pair (c := c) hs.1 hs.2.2.1 hs.2.2.2 hyz).choose_spec
    have hd : p s false ≠ p s true := by
      rw [pfalse, ptrue]
      exact other.1
    constructor
    · intro a b h
      cases a <;> cases b
      · rfl
      · exact (hd h).elim
      · exact (hd h.symm).elim
      · rfl
    · intro a ha hay haz i
      cases i
      · rw [pfalse]
        exact other.2 a ha hay haz
      · rw [ptrue]
        exact hc s hs.1 hs.2.1 hs.2.2.1 z hs.2.2.2 a ha hyz.symm hay haz.symm
  · let r := fun u v : Finset (Fin (2 * k)) × Bool =>
      B u.1 ∧ B v.1 ∧ (u.1 ∩ v.1).card + 2 = k ∧ p u.1 u.2 = p v.1 (!v.2)
    change ∀ s, ¬ (ReflTransGen r (s, false) (s, true) ∧ ReflTransGen r (s, true) (s, false))
    have step {u v : Finset (Fin (2 * k)) × Bool} (h : r u v) (hu : u.2 = true) : v.2 = true := by
      by_contra! hv
      have hfalse : v.2 = false := Bool.eq_false_iff.mpr hv
      rcases h with ⟨hU, hV, hcard, heq⟩
      have hcolors : c (insert z u.1) = c (insert z v.1) := by simpa [p, hu, hfalse] using heq
      let w := insert z (u.1 ∩ v.1)
      have hwc : w.card + 1 = k := by
        change (insert z (u.1 ∩ v.1)).card + 1 = k
        rw [card_insert_of_notMem (fun ht => hU.2.2.2 (mem_inter.mp ht).1)]
        omega
      have hwx : x ∈ w := mem_insert_of_mem (mem_inter.mpr ⟨hU.2.1, hV.2.1⟩)
      have hwy : y ∉ w := by simp [w, hyz, hU.2.2.1]
      have hsub {v₀ : Finset (Fin (2 * k))} (hsub : u.1 ∩ v.1 ⊆ v₀) :
          w ⊆ insert z v₀ := insert_subset_insert _ hsub
      obtain ⟨a, ha, hea⟩ :=
        OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.insert_repr
          (hsub inter_subset_left) (by rwa [card_insert_of_notMem hU.2.2.2, hU.1])
      obtain ⟨b, hb, heb⟩ :=
        OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.insert_repr
          (hsub inter_subset_right) (by rwa [card_insert_of_notMem hV.2.2.2, hV.1])
      have hay : a ≠ y := by
        intro h
        have hm : y ∈ insert z u.1 := hea ▸ h ▸ mem_insert_self _ _
        simp [hyz, hU.2.2.1] at hm
      have hby : b ≠ y := by
        intro h
        have hm : y ∈ insert z v.1 := heb ▸ h ▸ mem_insert_self _ _
        simp [hyz, hV.2.2.1] at hm
      have hab : a ≠ b := by
        intro he
        have heq' : insert z u.1 = insert z v.1 := by rw [hea, heb, he]
        have hr : u.1 = v.1 := by
          simpa only [erase_insert hU.2.2.2, erase_insert hV.2.2.2] using
            congrArg (fun S : Finset (Fin (2 * k)) => S.erase z) heq'
        rw [← hr, inter_self] at hcard
        have := hU.1
        omega
      apply hc w hwc hwx hwy a ha b hb hay hby hab
      rwa [hea, heb] at hcolors
    have path {u v : Finset (Fin (2 * k)) × Bool} (h : ReflTransGen r u v)
        (hu : u.2 = true) : v.2 = true := by
      induction h with
      | refl => exact hu
      | tail _ he ih => exact step he ih
    exact fun s h => Bool.false_ne_true (path h.2 rfl)

theorem coloring_iff : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H1 ↔ H1 :=
  ⟨restrict_coloring, fun h => main h binary_implications⟩

end OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1
