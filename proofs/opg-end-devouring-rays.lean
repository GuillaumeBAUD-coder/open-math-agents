import OMAStatements.S_opg_end_devouring_rays
import Mathlib

/-!
We use the finite-prefix construction of Gollin and Heuer, arXiv:1704.06577.
A maximal disjoint family gives a countable set of vertices that every end ray visits
arbitrarily far along its tail. The prefix construction preserves the starting vertices
and makes each of those vertices inaccessible to any end ray avoiding the final family.
-/

namespace EndRaysDraft

open SimpleGraph Set OMA.S_opg_end_devouring_rays

variable {V : Type} {G : SimpleGraph V} {r₀ r s t : ℕ → V}

private theorem tail_avoids (hr : IsRay G r) (S : Finset V) :
    ∃ a, ∀ n ≥ a, r n ∉ S := by
  have hfin : (r ⁻¹' (↑S : Set V)).Finite :=
    S.finite_toSet.preimage hr.1.injOn
  obtain ⟨a, ha⟩ := hfin.bddAbove
  refine ⟨a + 1, ?_⟩
  intro n hn hm
  have hh : n ≤ a := ha hm
  omega

private theorem tail_reachable {S : Finset V} {a i j : ℕ}
    (hr : IsRay G r) (hS : ∀ n ≥ a, r n ∉ S) (hai : a ≤ i) (haj : a ≤ j) :
    (G.induce {v | v ∉ S}).Reachable ⟨r i, hS i hai⟩ ⟨r j, hS j haj⟩ := by
  have forward (u v : ℕ) (hau : a ≤ u) (huv : u ≤ v) :
      (G.induce {v | v ∉ S}).Reachable ⟨r u, hS u hau⟩
        ⟨r v, hS v (hau.trans huv)⟩ := by
    induction v, huv using Nat.le_induction with
    | base => exact SimpleGraph.Reachable.rfl
    | succ v huv ih =>
      exact ih.trans (SimpleGraph.Adj.reachable (G := G.induce {v | v ∉ S}) (hr.2 v))
  rcases le_total i j with hij | hji
  · exact forward i j hai hij
  · exact (forward j i haj hji).symm

private theorem sameEnd_symm (h : SameEnd G r s) : SameEnd G s r := by
  intro S
  obtain ⟨m, n, hm, hn, hmt, hnt, hlink⟩ := h S
  exact ⟨n, m, hn, hm, hnt, hmt, hlink.symm⟩

private theorem sameEnd_trans (hs : IsRay G s) (hrs : SameEnd G r s) (hst : SameEnd G s t) :
    SameEnd G r t := by
  intro S
  obtain ⟨i, j, hi, hj, hit, hjt, h₁⟩ := hrs S
  obtain ⟨k, l, hk, hl, hkt, hlt, h₂⟩ := hst S
  let u := max j k
  have h₃ := tail_reachable hs hjt (le_refl j) (show j ≤ u by exact le_max_left _ _)
  have h₄ := tail_reachable hs hkt (le_refl k) (show k ≤ u by exact le_max_right _ _)
  exact ⟨i, l, hi, hl, hit, hlt, h₁.trans (h₃.trans (h₄.symm.trans h₂))⟩

private def shiftRay (r : ℕ → V) (i : ℕ) : ℕ → V := fun n => r (i + n)

private theorem shift_isRay (hr : IsRay G r) (i : ℕ) : IsRay G (shiftRay r i) := by
  refine ⟨fun a b h => ?_, fun n => hr.2 (i + n)⟩
  have he := hr.1 h
  omega

private theorem shift_sameEnd (hr : IsRay G r) (i : ℕ) : SameEnd G r (shiftRay r i) := by
  intro S
  obtain ⟨a, ha⟩ := tail_avoids hr S
  have hx : ∀ n ≥ i + a, r n ∉ S := fun n h => ha n (by omega)
  have hy : ∀ n ≥ a, shiftRay r i n ∉ S := fun n h => ha _ (by omega)
  exact ⟨i + a, a, hx _ le_rfl, hy _ le_rfl, hx, hy, SimpleGraph.Reachable.rfl⟩

private theorem shift_endRay (hr : IsEndRay G r₀ r) (i : ℕ) :
    IsEndRay G r₀ (shiftRay r i) :=
  ⟨shift_isRay hr.1 i, sameEnd_trans hr.1 hr.2 (shift_sameEnd hr.1 i)⟩

private def rayVertices (K : Set (ℕ → V)) : Set V :=
  ⋃ r ∈ K, Set.range r

private theorem mem_rayVertices {K : Set (ℕ → V)} {v : V} :
    v ∈ rayVertices K ↔ ∃ r ∈ K, ∃ n, r n = v := by
  simp [rayVertices]

private theorem rayVertices_countable {K : Set (ℕ → V)} (hK : K.Countable) :
    (rayVertices K).Countable :=
  hK.biUnion (fun r _ => Set.countable_range r)

private theorem packing_countable {C K : Set (ℕ → V)} (hC : C.Countable)
    (hdev : Devours G r₀ C) (hK : ∀ r ∈ K, IsEndRay G r₀ r)
    (hdis : PairwiseDisjointRays K) : K.Countable := by
  classical
  have hw : ∀ r : K, ∃ v ∈ rayVertices C, v ∈ Set.range r.val := by
    intro r
    obtain ⟨s, hs, m, n, he⟩ := hdev r.val (hK r.val r.property)
    exact ⟨s n, mem_rayVertices.mpr ⟨s, hs, n, rfl⟩, m, he⟩
  choose f hf_C hf_range using hw
  let e : K → rayVertices C := fun r => ⟨f r, hf_C r⟩
  have h_e : Function.Injective e := by
    intro r s he
    by_contra hne
    obtain ⟨m, hm⟩ := hf_range r
    obtain ⟨n, hn⟩ := hf_range s
    exact hdis _ r.property _ s.property (fun h => hne (Subtype.ext h)) m n
      (hm.trans ((congrArg Subtype.val he).trans hn.symm))
  let : Countable ↑(rayVertices C) := (rayVertices_countable hC).to_subtype
  exact h_e.countable

private theorem maximal_packing (r₀ : ℕ → V) :
    ∃ R : Set (ℕ → V), (∀ r ∈ R, IsEndRay G r₀ r) ∧
      PairwiseDisjointRays R ∧ Devours G r₀ R := by
  classical
  let pack := {K : Set (ℕ → V) | (∀ r ∈ K, IsEndRay G r₀ r) ∧ PairwiseDisjointRays K}
  obtain ⟨R, hR⟩ := zorn_subset pack (by
    intro chain hchain htotal
    refine ⟨⋃₀ chain, ⟨?_, ?_⟩, fun _ h => Set.subset_sUnion_of_mem h⟩
    · intro r hr
      obtain ⟨P, hP, hrP⟩ := Set.mem_sUnion.mp hr
      exact (hchain hP).1 r hrP
    · intro r hr s hs hne m n
      obtain ⟨P, hP, hrP⟩ := Set.mem_sUnion.mp hr
      obtain ⟨Q, hQ, hsQ⟩ := Set.mem_sUnion.mp hs
      rcases htotal.total hP hQ with h | h
      · exact (hchain hQ).2 r (h hrP) s hsQ hne m n
      · exact (hchain hP).2 r hrP s (h hsQ) hne m n)
  have hrays : ∀ r ∈ R, IsEndRay G r₀ r := hR.prop.1
  have hdis : PairwiseDisjointRays R := hR.prop.2
  refine ⟨R, hrays, hdis, ?_⟩
  intro r hr
  by_contra hmiss
  push Not at hmiss
  have hinsert : insert r R ∈ pack := by
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact hr
      · exact hrays s hs
    · intro s hs t ht hne m n
      rcases Set.mem_insert_iff.mp hs with he | hs
      · subst s
        exact hmiss t ((Set.mem_insert_iff.mp ht).resolve_left (Ne.symm hne)) m n
      · rcases Set.mem_insert_iff.mp ht with he | ht
        · subst t
          exact (hmiss s hs n m).symm
        · exact hdis s hs t ht hne m n
  have hrR : r ∈ R :=
    hR.le_of_ge hinsert (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hmiss r hrR 0 0 rfl

private theorem recurrent_vertices {R : Set (ℕ → V)} (hR : Devours G r₀ R)
    (hr : IsEndRay G r₀ r) (a : ℕ) :
    ∃ n ≥ a, r n ∈ rayVertices R := by
  obtain ⟨s, hs, m, n, he⟩ := hR (shiftRay r a) (shift_endRay hr a)
  exact ⟨a + m, Nat.le_add_right _ _, mem_rayVertices.mpr ⟨s, hs, n, he.symm⟩⟩

private theorem endRay_of_recurrent {R : Set (ℕ → V)}
    (hR : ∀ s ∈ R, IsEndRay G r₀ s) (hdis : PairwiseDisjointRays R)
    (hr : IsRay G r) (hrec : ∀ a, ∃ n ≥ a, r n ∈ rayVertices R) :
    IsEndRay G r₀ r := by
  classical
  refine ⟨hr, ?_⟩
  intro S
  let cutHits : R → Set V := fun s => Set.range s.val ∩ (↑S : Set V)
  have hdisj : Pairwise fun s t : R => Disjoint (cutHits s) (cutHits t) := by
    intro s t hne
    refine Set.disjoint_left.mpr ?_
    intro v hs ht
    obtain ⟨m, hm⟩ := hs.1
    obtain ⟨n, hn⟩ := ht.1
    exact hdis _ s.property _ t.property (fun he => hne (Subtype.ext he)) m n
      (hm.trans hn.symm)
  have hunion : (⋃ s, cutHits s).Finite := S.finite_toSet.subset (by
    intro v hv
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hv
    exact hs.2)
  have hbad : {s : R | (cutHits s).Nonempty}.Finite :=
    ((Set.finite_iUnion_iff hdisj).mp hunion).2
  have htail : ∀ s : R, ∃ a, ∀ n ≥ a, s.val n ∉ S :=
    fun s => tail_avoids (hR s.val s.property).1 S
  choose a ha using htail
  let E : Set V := ⋃ s ∈ {s : R | (cutHits s).Nonempty}, s.val '' {n | n < a s}
  have hE : E.Finite := hbad.biUnion (fun s _ => (Set.finite_lt_nat _).image s.val)
  obtain ⟨b, hb⟩ := tail_avoids hr S
  obtain ⟨c, hc⟩ := tail_avoids hr hE.toFinset
  obtain ⟨j, hj, hv⟩ := hrec (max b c)
  obtain ⟨s, hs, k, hk⟩ := mem_rayVertices.mp hv
  let q : R := ⟨s, hs⟩
  have hkc : ∀ n ≥ k, s n ∉ S := by
    by_cases hq : (cutHits q).Nonempty
    · have hka : a q ≤ k := by
        by_contra! hlt
        have he : r j ∈ E :=
          Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, k, hlt, hk⟩⟩
        exact hc j ((le_max_right b c).trans hj) (hE.mem_toFinset.mpr he)
      exact fun n hn => ha q n (hka.trans hn)
    · intro n _ hsn
      exact hq ⟨s n, ⟨⟨n, rfl⟩, hsn⟩⟩
  obtain ⟨i, l, hi, hl, hit, hlt, hlink⟩ := (hR s hs).2 S
  have hmove := tail_reachable (hR s hs).1 hlt (le_refl l)
    (show l ≤ max l k by exact le_max_left _ _)
  have hback := tail_reachable (hR s hs).1 hkc (le_refl k)
    (show k ≤ max l k by exact le_max_right _ _)
  have hbj : b ≤ j := (le_max_left b c).trans hj
  have hend := (hlink.trans (hmove.trans hback.symm))
  have heq : (⟨s k, hkc k le_rfl⟩ : {v // v ∉ S}) = ⟨r j, hb j hbj⟩ :=
    Subtype.ext hk
  exact ⟨i, j, hi, hb j hbj, hit, fun n hn => hb n (hbj.trans hn), heq ▸ hend⟩

private def splice (head tail : ℕ → V) (k : ℕ) : ℕ → V :=
  fun n => if n < k then head n else tail (n - k)

private theorem splice_prefix {head tail : ℕ → V} {k n : ℕ}
    (hjoint : head k = tail 0) (hn : n ≤ k) :
    splice head tail k n = head n := by
  rcases lt_or_eq_of_le hn with h | rfl
  · simp [splice, h]
  · simp [splice, hjoint]

private theorem splice_tail {head tail : ℕ → V} {k : ℕ} :
    shiftRay (splice head tail k) k = tail := by
  funext n
  have hnk : ¬ k + n < k := by omega
  simp only [shiftRay, splice, hnk, if_false, Nat.add_sub_cancel_left]

private theorem splice_isRay {head tail : ℕ → V} {k : ℕ}
    (hHead : Set.InjOn head {n | n < k})
    (hAdj : ∀ n < k, G.Adj (head n) (head (n + 1)))
    (hJoint : head k = tail 0) (hTail : IsRay G tail)
    (hSep : ∀ n < k, ∀ m, head n ≠ tail m) :
    IsRay G (splice head tail k) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    by_cases hi : i < k <;> by_cases hj : j < k
    · exact hHead hi hj (by simpa [splice, hi, hj] using h)
    · exact (hSep i hi (j - k) (by simpa [splice, hi, hj] using h)).elim
    · exact (hSep j hj (i - k) (by simpa [splice, hi, hj] using h.symm)).elim
    · have he := hTail.1 (show tail (i - k) = tail (j - k) by simpa [splice, hi, hj] using h)
      omega
  · intro i
    by_cases hi : i < k
    · rw [splice_prefix hJoint (by omega : i ≤ k), splice_prefix hJoint (by omega : i + 1 ≤ k)]
      exact hAdj i hi
    · have hn : ¬ i + 1 < k := by omega
      simp only [splice, hi, hn, if_false]
      rw [show i + 1 - k = i - k + 1 by omega]
      exact hTail.2 _

private theorem splice_endRay {head tail : ℕ → V} {k : ℕ}
    (hHead : Set.InjOn head {n | n < k})
    (hAdj : ∀ n < k, G.Adj (head n) (head (n + 1)))
    (hJoint : head k = tail 0) (hTail : IsEndRay G r₀ tail)
    (hSep : ∀ n < k, ∀ m, head n ≠ tail m) :
    IsEndRay G r₀ (splice head tail k) := by
  have hr := splice_isRay hHead hAdj hJoint hTail.1 hSep
  have ht := shift_sameEnd hr k
  rw [splice_tail] at ht
  exact ⟨hr, sameEnd_trans hTail.1 hTail.2 (sameEnd_symm ht)⟩

private theorem backward_endRay {initial : ℕ → V} {i j : ℕ}
    (hij : i ≤ j) (hr : IsRay G r)
    (ht : IsEndRay G r₀ initial) (hstart : initial 0 = r i)
    (hdis : ∀ k, i < k → k ≤ j → ∀ n, r k ≠ initial n) :
    IsEndRay G r₀ (splice (fun n => r (j - n)) initial (j - i)) := by
  refine splice_endRay ?_ ?_ ?_ ht ?_
  · intro a ha b hb he
    have h := hr.1 he
    change a < j - i at ha
    change b < j - i at hb
    omega
  · intro n hn
    have he : j - n = j - (n + 1) + 1 := by omega
    change G.Adj (r (j - n)) (r (j - (n + 1)))
    rw [he]
    exact (hr.2 _).symm
  · rw [hstart, show j - (j - i) = i by omega]
  · intro n hn m
    exact hdis (j - n) (by omega) (Nat.sub_le _ _) m

private structure Bridge (G : SimpleGraph V) (A B cut : Set V) where
  length : ℕ
  vertex : ℕ → V
  positive : 0 < length
  injective : Set.InjOn vertex {n | n ≤ length}
  adjacent : ∀ n < length, G.Adj (vertex n) (vertex (n + 1))
  start_mem : vertex 0 ∈ A
  end_mem : vertex length ∈ B
  after_start : ∀ n, 0 < n → n ≤ length → vertex n ∉ A
  before_end : ∀ n < length, vertex n ∉ B
  avoids : ∀ n ≤ length, vertex n ∉ cut

private theorem bridge_of_segment {A B cut : Set V} (hdis : Disjoint A B)
    (f : ℕ → V) (len : ℕ) (hinj : Set.InjOn f {n | n ≤ len})
    (hadj : ∀ n < len, G.Adj (f n) (f (n + 1)))
    (ha : f 0 ∈ A) (hb : f len ∈ B) (hcut : ∀ n ≤ len, f n ∉ cut) :
    Nonempty (Bridge G A B cut) := by
  classical
  have hexB : ∃ n, f n ∈ B := ⟨len, hb⟩
  let e := Nat.find hexB
  have heB : f e ∈ B := Nat.find_spec hexB
  have hel : e ≤ len := Nat.find_min' hexB hb
  have hexA : ∃ n, n ≤ e ∧ f (e - n) ∈ A := ⟨e, le_rfl, by simpa using ha⟩
  let d := Nat.find hexA
  obtain ⟨hde, hstart⟩ := Nat.find_spec hexA
  let start := e - d
  have hstartA : f start ∈ A := hstart
  have hsum : start + d = e := by dsimp [start]; omega
  have hd : 0 < d := by
    by_contra! h
    have hd0 : d = 0 := by omega
    have hse : start = e := by omega
    exact (Set.disjoint_left.mp hdis) hstartA (hse ▸ heB)
  refine ⟨⟨d, fun n => f (start + n), hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi j hj h
    change i ≤ d at hi
    change j ≤ d at hj
    have heq := hinj (show start + i ≤ len by omega) (show start + j ≤ len by omega) h
    omega
  · intro n hn
    exact hadj _ (by omega)
  · simpa only [Nat.add_zero] using hstartA
  · rwa [hsum]
  · intro n hn hnd hA
    have hlt : e - (start + n) < d := by omega
    have hle : e - (start + n) ≤ e := Nat.sub_le _ _
    have heq : e - (e - (start + n)) = start + n := by omega
    apply Nat.find_min hexA hlt
    refine ⟨hle, ?_⟩
    rwa [heq]
  · intro n hn hB
    exact (Nat.find_min hexB (show start + n < e by omega)) hB
  · intro n hn
    exact hcut _ (by omega)

private theorem bridge_of_reachable {A B : Set V} {S : Finset V}
    (hdis : Disjoint A B) {x y : {v // v ∉ S}} (hx : x.val ∈ A) (hy : y.val ∈ B)
    (h : (G.induce {v | v ∉ S}).Reachable x y) :
    Nonempty (Bridge G A B (↑S : Set V)) := by
  classical
  obtain ⟨w⟩ := h
  let p := w.toPath
  let f : ℕ → V := fun n => (p.val.getVert n).val
  apply bridge_of_segment hdis f p.val.length
  · intro i hi j hj heq
    exact p.property.getVert_injOn hi hj (Subtype.ext heq)
  · intro n hn
    exact p.val.adj_getVert_succ hn
  · simpa [f]
  · simpa [f]
  · intro n _
    exact (p.val.getVert n).property

private def indexedVertices (F : ℕ → ℕ → V) : Set V :=
  {v | ∃ i n, F i n = v}

private def fixedVertices (F : ℕ → ℕ → V) (d : ℕ → ℕ) : Set V :=
  {v | ∃ i n, n ≤ d i ∧ F i n = v}

private def activeVertices (F : ℕ → ℕ → V) (d : ℕ → ℕ) : Set V :=
  ⋃ i ∈ {i | d i ≠ 0}, F i '' {n | n ≤ d i}

private theorem active_finite {F : ℕ → ℕ → V} {d : ℕ → ℕ}
    (hd : {i | d i ≠ 0}.Finite) : (activeVertices F d).Finite := by
  refine hd.biUnion (fun i _ => ?_)
  exact ((Set.finite_lt_nat (d i + 1)).subset (fun n hn => Nat.lt_succ_of_le hn)).image _

private theorem active_fixed (F : ℕ → ℕ → V) (d : ℕ → ℕ) :
    activeVertices F d ⊆ fixedVertices F d := by
  intro v hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_, n, hn, he⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, n, hn, he⟩

private def Avoids (r : ℕ → V) (A : Set V) : Prop := ∀ n, r n ∉ A

private theorem disjoint_range_iff_avoids {A : Set V} :
    Disjoint (Set.range r) A ↔ Avoids r A := by
  constructor
  · intro h n hn
    exact (Set.disjoint_left.mp h) ⟨n, rfl⟩ hn
  · intro h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ hn
    exact h n hn

private structure Packing (G : SimpleGraph V) (r₀ : ℕ → V) (start : ℕ → V) where
  ray : ℕ → ℕ → V
  endRay : ∀ i, IsEndRay G r₀ (ray i)
  disjoint : ∀ i j, i ≠ j → ∀ m n, ray i m ≠ ray j n
  starting : ∀ i, ray i 0 = start i

private theorem connected_bridge {start : ℕ → V} (F : Packing G r₀ start)
    (hanchor : IsRay G r₀) (hr : IsEndRay G r₀ r) (havoid : Avoids r (indexedVertices F.ray)) (S : Finset V) :
    Nonempty (Bridge G (Set.range r) (indexedVertices F.ray) (↑S : Set V)) := by
  have hlink : SameEnd G r (F.ray 0) :=
    sameEnd_trans hanchor (sameEnd_symm hr.2) (F.endRay 0).2
  obtain ⟨i, j, hi, hj, _, _, h⟩ := hlink S
  exact bridge_of_reachable (disjoint_range_iff_avoids.mpr havoid)
    (x := ⟨r i, hi⟩) (y := ⟨F.ray 0 j, hj⟩) ⟨i, rfl⟩ ⟨0, j, rfl⟩ h

private def bridgeAfter {A B cut : Set V} (b : Bridge G A B cut) : Set V :=
  b.vertex '' {n | 0 < n ∧ n ≤ b.length}

private def attachment (r : ℕ → V) (U C : Set V) (p a : ℕ) : Prop :=
  ∃ w : ℕ → V, IsEndRay G r₀ w ∧ w 0 = r a ∧
    Avoids w (U ∪ C) ∧ ∀ k, a < k → k ≤ p → ∀ n, r k ≠ w n

private theorem earlier_attachment {U C : Set V} {p a : ℕ}
    (hr : IsRay G r) (hz : IsEndRay G r₀ s) (hs₀ : s 0 = r 0)
    (hs : Avoids s (U ∪ C)) (ha : 0 < a)
    (hseg : ∀ n k, a ≤ k → k ≤ p → s n ≠ r k) :
    ∃ k < a, attachment (G := G) (r₀ := r₀) r U C p k := by
  classical
  let A := r '' {i | i < a}
  have hA : A.Finite := (Set.finite_lt_nat _).image _
  have H : (s ⁻¹' A).Finite := hA.preimage hz.1.1.injOn
  have hnon : H.toFinset.Nonempty := ⟨0, H.mem_toFinset.mpr ⟨0, ha, hs₀.symm⟩⟩
  let n := H.toFinset.max' hnon
  have hn : s n ∈ A := H.mem_toFinset.mp (Finset.max'_mem _ _)
  obtain ⟨k, hk, hkn⟩ := hn
  refine ⟨k, hk, shiftRay s n, shift_endRay hz n, ?_, ?_, ?_⟩
  · simpa [shiftRay] using hkn.symm
  · intro m
    exact hs (n + m)
  · intro j hj hjp m h
    by_cases hja : j < a
    · have hm : n + m ∈ s ⁻¹' A := ⟨j, hja, h⟩
      have hle : n + m ≤ n := Finset.le_max' _ _ (H.mem_toFinset.mpr hm)
      have hm0 : m = 0 := by omega
      have heq : r j = r k := by simpa [shiftRay, hm0, ← hkn] using h
      exact (Nat.ne_of_gt hj) (hr.1 heq)
    · exact hseg _ j (by omega) hjp h.symm

private def Bridge.relaxCut {A B cut cut' : Set V} (b : Bridge G A B cut)
    (h : cut' ⊆ cut) : Bridge G A B cut' :=
  ⟨b.length, b.vertex, b.positive, b.injective, b.adjacent, b.start_mem, b.end_mem,
    b.after_start, b.before_end, fun n hn hmem => b.avoids n hn (h hmem)⟩

private theorem ray_avoids_bridgeAfter {U cut : Set V}
    (b : Bridge G (Set.range r) U cut) : Avoids r (bridgeAfter b) := by
  intro n hn
  obtain ⟨j, hj, he⟩ := hn
  exact b.after_start j hj.1 hj.2 ⟨n, he.symm⟩

private theorem cannot_avoid_bridge {U cut : Set V} {p a : ℕ}
    (hr : IsEndRay G r₀ r) (hrU : Avoids r U)
    (b : Bridge G (Set.range r) U cut)
    (hminP : ∀ q < p, ¬ ∃ c : Bridge G (Set.range r) U cut, c.vertex 0 = r q)
    (hminA : ∀ k < a, ¬ attachment (G := G) (r₀ := r₀) r U (bridgeAfter b) p k)
    (hs : IsEndRay G r₀ s) (hstart : s 0 = r 0) (hsCut : Avoids s cut)
    (hsBridge : Avoids s (bridgeAfter b))
    (hsSeg : ∀ n k, a ≤ k → k ≤ p → s n ≠ r k) (ha : a ≤ p) : False := by
  classical
  have haPos : 0 < a := by
    by_contra! h
    exact hsSeg 0 0 h (Nat.zero_le _) hstart
  let target := U ∪ Set.range (shiftRay r p)
  by_cases hh : ∃ n, s n ∈ target
  · let j := Nat.find hh
    have hj : s j ∈ target := Nat.find_spec hh
    have hbefore : ∀ n < j, s n ∉ target := fun n hn => Nat.find_min hh hn
    rcases hj with hU | hR
    · have hav : ∀ n ≤ j, s n ∉ cut ∪ Set.range (shiftRay r p) := by
        intro n hn hv
        rcases hv with hv | hv
        · exact hsCut n hv
        · rcases lt_or_eq_of_le hn with hj' | hj'
          · exact hbefore n hj' (Or.inr hv)
          · subst n
            obtain ⟨k, hk⟩ := hv
            rw [← hk] at hU
            exact hrU (p + k) hU
      obtain ⟨c⟩ := bridge_of_segment (disjoint_range_iff_avoids.mpr hrU) s j
        hs.1.1.injOn (fun n _ => hs.1.2 n) ⟨0, hstart.symm⟩ hU hav
      obtain ⟨q, hq⟩ := c.start_mem
      have hqp : q < p := by
        by_contra! h
        apply c.avoids 0 (Nat.zero_le _)
        exact Or.inr ⟨q - p, by simpa only [shiftRay, Nat.add_sub_of_le h] using hq⟩
      exact hminP q hqp ⟨c.relaxCut (fun _ h => Or.inl h), hq.symm⟩
    · obtain ⟨m, hm⟩ := hR
      have hmp : p < p + m := by
        by_contra! h
        have hm' : p + m = p := by omega
        exact hsSeg j p ha le_rfl (by simpa only [shiftRay, hm'] using hm.symm)
      let tail := shiftRay r (p + m)
      have hjoin : s j = tail 0 := by simpa [tail, shiftRay] using hm.symm
      let z := splice s tail j
      have hz : IsEndRay G r₀ z := by
        refine splice_endRay hs.1.1.injOn (fun n _ => hs.1.2 n) hjoin
          (shift_endRay hr (p + m)) ?_
        intro n hn k he
        exact hbefore n hn (Or.inr ⟨m + k, by simpa [tail, shiftRay, Nat.add_assoc] using he.symm⟩)
      have hz₀ : z 0 = r 0 := (splice_prefix hjoin (Nat.zero_le _)).trans hstart
      have hz1 : Avoids z (U ∪ bridgeAfter b) := by
        intro n hn
        by_cases h : n < j
        · have he : z n = s n := by simp [z, splice, h]
          rw [he] at hn
          rcases hn with hn | hn
          · exact hbefore n h (Or.inl hn)
          · exact hsBridge n hn
        · have he : z n = r (p + m + (n - j)) := by simp [z, splice, h, tail, shiftRay]
          rw [he] at hn
          rcases hn with hn | hn
          · exact hrU _ hn
          · exact ray_avoids_bridgeAfter b _ hn
      have hz2 : ∀ n k, a ≤ k → k ≤ p → z n ≠ r k := by
        intro n k hka hkp he
        by_cases h : n < j
        · exact hsSeg n k hka hkp (by simpa [z, splice, h] using he)
        · have he' := hr.1.1 (show r (p + m + (n - j)) = r k from by
            simpa [z, splice, h, tail, shiftRay] using he)
          omega
      obtain ⟨k, hk, hatt⟩ := earlier_attachment hr.1 hz hz₀ hz1 haPos hz2
      exact hminA k hk hatt
  · have hs' : Avoids s (U ∪ bridgeAfter b) := by
      intro n hn
      rcases hn with hn | hn
      · exact hh ⟨n, Or.inl hn⟩
      · exact hsBridge n hn
    obtain ⟨k, hk, hatt⟩ := earlier_attachment hr.1 hs hstart hs' haPos hsSeg
    exact hminA k hk hatt

private structure PrefixState (G : SimpleGraph V) (r₀ : ℕ → V) (start : ℕ → V) where
  packing : Packing G r₀ start
  depth : ℕ → ℕ
  finite : {i | depth i ≠ 0}.Finite

private def PrefixState.vertices {start : ℕ → V} (P : PrefixState G r₀ start) : Set V :=
  fixedVertices P.packing.ray P.depth

private def Extends {start : ℕ → V} (P Q : PrefixState G r₀ start) : Prop :=
  ∀ i, P.depth i ≤ Q.depth i ∧
    ∀ n ≤ P.depth i, P.packing.ray i n = Q.packing.ray i n

private theorem Extends.refl {start : ℕ → V} (P : PrefixState G r₀ start) : Extends P P :=
  fun _ => ⟨le_rfl, fun _ _ => rfl⟩

private theorem Extends.trans {start : ℕ → V} {P Q T : PrefixState G r₀ start}
    (hPQ : Extends P Q) (hQT : Extends Q T) : Extends P T :=
  fun i => ⟨(hPQ i).1.trans (hQT i).1,
    fun n hn => ((hPQ i).2 n hn).trans ((hQT i).2 n (hn.trans (hPQ i).1))⟩

private def Blocks {start : ℕ → V} (P : PrefixState G r₀ start) (v : V) : Prop :=
  ∀ s, IsEndRay G r₀ s → s 0 = v → ∃ n, s n ∈ P.vertices

private def replaceRay {start : ℕ → V} (F : Packing G r₀ start) (i : ℕ) (z : ℕ → V)
    (hz : IsEndRay G r₀ z) (hs : z 0 = start i)
    (hgap : ∀ j, i ≠ j → ∀ m n, z m ≠ F.ray j n) : Packing G r₀ start where
  ray := Function.update F.ray i z
  endRay j := by
    obtain rfl | hj := eq_or_ne j i
    · simpa using hz
    · simpa [Function.update_of_ne hj] using F.endRay j
  disjoint j k hjk m n := by
    obtain rfl | hj := eq_or_ne j i
    · simpa [Function.update_of_ne (Ne.symm hjk)] using hgap k hjk m n
    · obtain rfl | hk := eq_or_ne k i
      · simpa [Function.update_of_ne hj] using (hgap j hj.symm n m).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.disjoint j k hjk m n
  starting j := by
    obtain rfl | hj := eq_or_ne j i
    · simpa using hs
    · simpa [Function.update_of_ne hj] using F.starting j

/-- An unused ray yields a finite extension that intersects every end ray from its first vertex. -/
private theorem block_extension {start : ℕ → V} (F : Packing G r₀ start) (d : ℕ → ℕ)
    (hd : {i | d i ≠ 0}.Finite) (hanchor : IsRay G r₀)
    (hr : IsEndRay G r₀ r) (hrU : Avoids r (indexedVertices F.ray)) :
    ∃ Q, Extends (⟨F, d, hd⟩ : PrefixState G r₀ start) Q ∧ Blocks Q (r 0) := by
  classical
  let U := indexedVertices F.ray
  let cut := activeVertices F.ray d
  let hcut : cut.Finite := active_finite hd
  let A := Set.range r
  have hex : ∃ p, ∃ b : Bridge G A U cut, b.vertex 0 = r p := by
    obtain ⟨b⟩ := connected_bridge F hanchor hr hrU hcut.toFinset
    obtain ⟨p, hp⟩ := b.start_mem
    exact ⟨p, b.relaxCut (fun v hv => hcut.mem_toFinset.mpr hv), hp.symm⟩
  let p := Nat.find hex
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  have hpmin (q : ℕ) (hq : q < p) :
      ¬ ∃ c : Bridge G A U cut, c.vertex 0 = r q := Nat.find_min hex hq
  have hexA : ∃ a, a ≤ p ∧ attachment (G := G) (r₀ := r₀) r U (bridgeAfter b) p a := by
    refine ⟨p, le_rfl, shiftRay r p, shift_endRay hr p, by simp [shiftRay], ?_, ?_⟩
    · intro n hn
      rcases hn with hn | hn
      · exact hrU (p + n) hn
      · exact ray_avoids_bridgeAfter b (p + n) hn
    · intro k hk hkp
      omega
  let a := Nat.find hexA
  obtain ⟨hap, w, hw, hw₀, hwU, hwRep⟩ := Nat.find_spec hexA
  have hamin (k : ℕ) (hk : k < a) :
      ¬ attachment (G := G) (r₀ := r₀) r U (bridgeAfter b) p k :=
    fun he => Nat.find_min hexA hk ⟨hk.le.trans hap, he⟩
  obtain ⟨i, j, hij⟩ := b.end_mem
  have hj : d i ≤ j := by
    by_contra! hh
    apply b.avoids b.length le_rfl
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨?_, j, hh.le, hij⟩⟩
    change d i ≠ 0
    omega
  let back := splice (fun n => r (p - n)) w (p - a)
  have hback := backward_endRay hap hr.1 hw hw₀ hwRep
  have hbjoin : r (p - (p - a)) = w 0 := by
    rw [hw₀, show p - (p - a) = a by omega]
  have hback₀ : back 0 = r p := by
    simpa [back] using splice_prefix (head := fun n => r (p - n)) (k := p - a)
      hbjoin (Nat.zero_le (p - a))
  have hbackAvoid : Avoids back (U ∪ bridgeAfter b) := by
    intro n hn
    by_cases hh : n < p - a
    · have he : back n = r (p - n) := by simp [back, splice, hh]
      rw [he] at hn
      rcases hn with hn | hn
      · exact hrU (p - n) hn
      · exact ray_avoids_bridgeAfter b (p - n) hn
    · exact hwU (n - (p - a)) (by simpa [back, splice, hh] using hn)
  let via := splice (fun n => b.vertex (b.length - n)) back b.length
  have hvjoin : b.vertex (b.length - b.length) = back 0 := by
    simpa only [Nat.sub_self, hback₀] using hb
  have hvia : IsEndRay G r₀ via := by
    refine splice_endRay ?_ ?_ hvjoin hback ?_
    · intro k hk l hl he
      change k < b.length at hk
      change l < b.length at hl
      have hkl := b.injective (show b.length - k ≤ b.length by omega)
        (show b.length - l ≤ b.length by omega) he
      omega
    · intro n hn
      have he : b.length - n = b.length - (n + 1) + 1 := by omega
      change G.Adj (b.vertex (b.length - n)) (b.vertex (b.length - (n + 1)))
      rw [he]
      exact (b.adjacent _ (by omega)).symm
    · intro n hn m he
      apply hbackAvoid m
      exact Or.inr ⟨b.length - n, ⟨by omega, Nat.sub_le _ _⟩, he⟩
  have hvia₀ : via 0 = F.ray i j := by
    have h := splice_prefix (head := fun n => b.vertex (b.length - n))
      (k := b.length) hvjoin (Nat.zero_le b.length)
    simpa [via, ← hij] using h
  have hviaU (n : ℕ) (hn : via n ∈ U) : via n = F.ray i j := by
    by_cases hh : n < b.length
    · by_cases hn0 : n = 0
      · simpa [hn0] using hvia₀
      · have he : via n = b.vertex (b.length - n) := by simp [via, splice, hh]
        rw [he] at hn
        exact (b.before_end _ (by omega) hn).elim
    · have he : via n = back (n - b.length) := by simp [via, splice, hh]
      exact (hbackAvoid _ (Or.inl (he ▸ hn))).elim
  let z := splice (F.ray i) via j
  have hz := splice_endRay (F.endRay i).1.1.injOn
    (fun n _ => (F.endRay i).1.2 n) hvia₀.symm hvia (by
      intro n hn m he
      have hmem : via m ∈ U := ⟨i, n, he⟩
      exact (Nat.ne_of_lt hn) ((F.endRay i).1.1 (he.trans (hviaU m hmem))))
  have hstart : z 0 = start i :=
    (splice_prefix hvia₀.symm (Nat.zero_le j)).trans (F.starting i)
  let F' := replaceRay F i z hz hstart (by
    intro l hil m n he
    by_cases h : m < j
    · exact F.disjoint i l hil m n (by simpa [z, splice, h] using he)
    · have he' : via (m - j) = F.ray l n := by simpa [z, splice, h] using he
      have hm : via (m - j) ∈ U := ⟨l, n, he'.symm⟩
      exact F.disjoint i l hil j n ((hviaU _ hm).symm.trans he'))
  let depth := j + b.length + (p - a)
  let d' := Function.update d i depth
  have hd' : {i | d' i ≠ 0}.Finite := (hd.insert i).subset (by
    intro l hl
    rcases eq_or_ne l i with rfl | hli
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (by simpa [d', Function.update_of_ne hli] using hl))
  let Q : PrefixState G r₀ start := ⟨F', d', hd'⟩
  have hExt : Extends ⟨F, d, hd⟩ Q := by
    intro l
    rcases eq_or_ne l i with rfl | hli
    · refine ⟨?_, ?_⟩
      · change d l ≤ d' l
        simp only [d', Function.update_self]
        dsimp [depth]
        omega
      · intro n hn
        change F.ray l n = F'.ray l n
        simp only [F', replaceRay, Function.update_self]
        exact (splice_prefix hvia₀.symm (hn.trans hj)).symm
    · simp [Q, d', F', replaceRay, Function.update_of_ne hli]
  have hfixed : fixedVertices F.ray d ⊆ Q.vertices := by
    rintro v ⟨l, n, hn, he⟩
    exact ⟨l, n, hn.trans (hExt l).1, ((hExt l).2 n hn).symm.trans he⟩
  have hzSplice (n : ℕ) : z (j + n) = via n :=
    congrFun splice_tail n
  have hViaSplice (n : ℕ) : via (b.length + n) = back n :=
    congrFun splice_tail n
  have hview (n : ℕ) (hn : n ≤ depth) : z n ∈ Q.vertices := by
    refine ⟨i, n, ?_, ?_⟩
    · simpa [Q, d'] using hn
    · simp [Q, F', replaceRay]
  have hbridge : bridgeAfter b ⊆ Q.vertices := by
    rintro v ⟨n, hn, he⟩
    have hviaN : via (b.length - n) = b.vertex (b.length - (b.length - n)) :=
      splice_prefix (head := fun k => b.vertex (b.length - k))
        (k := b.length) hvjoin (Nat.sub_le _ _)
    have hx := (hzSplice (b.length - n)).trans hviaN
    have hnBound : n ≤ b.length := hn.2
    have hnn : b.length - (b.length - n) = n := by omega
    rw [hnn, he] at hx
    rw [← hx]
    exact hview _ (by dsimp [depth]; omega)
  have hsegment (n : ℕ) (hna : a ≤ n) (hnp : n ≤ p) : r n ∈ Q.vertices := by
    have hbackN : back (p - n) = r (p - (p - n)) :=
      splice_prefix (head := fun k => r (p - k)) (k := p - a)
        hbjoin (by omega : p - n ≤ p - a)
    have hx := (hzSplice (b.length + (p - n))).trans ((hViaSplice _).trans hbackN)
    have he : p - (p - n) = n := by omega
    rw [he] at hx
    rw [← hx]
    exact hview _ (by dsimp [depth]; omega)
  refine ⟨Q, hExt, ?_⟩
  intro s hs hs₀
  by_contra! havoid
  exact cannot_avoid_bridge hr hrU b hpmin hamin hs hs₀
    (fun n hv => havoid n (hfixed (active_fixed _ _ hv)))
    (fun n hv => havoid n (hbridge hv))
    (fun n k hka hkp he => havoid n (he.symm ▸ hsegment k hka hkp)) hap

private def Grows {start : ℕ → V} (W : Set V) (stage : ℕ)
    (P Q : PrefixState G r₀ start) : Prop :=
  ∀ i ≤ stage, ∃ n, P.depth i < n ∧ n ≤ Q.depth i ∧ Q.packing.ray i n ∈ W

private theorem Grows.mono {start : ℕ → V} {W : Set V} {stage : ℕ}
    {P Q T : PrefixState G r₀ start} (h : Grows W stage P Q) (ht : Extends Q T) :
    Grows W stage P T := by
  intro i hi
  obtain ⟨n, hn, hq, hw⟩ := h i hi
  refine ⟨n, hn, hq.trans (ht i).1, ?_⟩
  rwa [← (ht i).2 n hq]

private theorem growth_extension {start : ℕ → V} {R : Set (ℕ → V)}
    (hR : Devours G r₀ R) (P : PrefixState G r₀ start) (j : ℕ) :
    ∃ Q, Extends P Q ∧ Grows (rayVertices R) j P Q := by
  classical
  have htail : ∀ i, ∃ n ≥ P.depth i + 1, P.packing.ray i n ∈ rayVertices R :=
    fun i => recurrent_vertices hR (P.packing.endRay i) (P.depth i + 1)
  choose point hpoint hmem using htail
  let depth : ℕ → ℕ := fun i => if i ≤ j then point i else P.depth i
  have hf : {i | depth i ≠ 0}.Finite := by
    apply (P.finite.union (Set.finite_lt_nat (j + 1))).subset
    intro i hi
    by_cases hij : i ≤ j
    · exact Or.inr (Nat.lt_succ_of_le hij)
    · exact Or.inl (by simpa [depth, hij] using hi)
  let Q : PrefixState G r₀ start := ⟨P.packing, depth, hf⟩
  refine ⟨Q, ?_, ?_⟩
  · intro i
    refine ⟨?_, fun _ _ => rfl⟩
    change P.depth i ≤ depth i
    by_cases h : i ≤ j
    · simpa only [depth, if_pos h] using (Nat.le_succ (P.depth i)).trans (hpoint i)
    · simp [depth, h]
  · intro i hi
    refine ⟨point i, hpoint i, ?_, hmem i⟩
    simp [Q, depth, hi]

private theorem next_exists {start : ℕ → V} {R : Set (ℕ → V)}
    (hR : Devours G r₀ R) (P : PrefixState G r₀ start) (j : ℕ) (v : V) :
    ∃ Q, Extends P Q ∧ Grows (rayVertices R) j P Q ∧
      (∀ T, Extends P T → Grows (rayVertices R) j P T → Blocks T v → Blocks Q v) := by
  classical
  by_cases h : ∃ Q, Extends P Q ∧ Grows (rayVertices R) j P Q ∧ Blocks Q v
  · obtain ⟨Q, hQ, hg, hb⟩ := h
    exact ⟨Q, hQ, hg, fun _ _ _ _ => hb⟩
  · obtain ⟨Q, hQ, hg⟩ := growth_extension hR P j
    exact ⟨Q, hQ, hg, fun T he ht hb => (h ⟨T, he, ht, hb⟩).elim⟩

/-- Keep the fixed prefixes coherent while meeting the countably many vertex requirements. -/
private theorem end_ray_packing_fusion {start : ℕ → V} {R : Set (ℕ → V)}
    (hanchor : IsRay G r₀) (F : Packing G r₀ start)
    (hR : ∀ r ∈ R, IsEndRay G r₀ r) (hRdis : PairwiseDisjointRays R)
    (hRdev : Devours G r₀ R) (enum : ℕ → V)
    (henum : rayVertices R ⊆ Set.range enum) :
    ∃ FL : Packing G r₀ start, ∀ s, IsEndRay G r₀ s →
      ∃ i m n, s m = FL.ray i n := by
  classical
  let init : PrefixState G r₀ start := ⟨F, fun _ => 0, by simp⟩
  let next := fun (k : ℕ) (P : PrefixState G r₀ start) =>
    (next_exists hRdev P k (enum k)).choose
  let stage : ℕ → PrefixState G r₀ start := Nat.rec init next
  have hNext (k : ℕ) :
      Extends (stage k) (stage (k + 1)) ∧ Grows (rayVertices R) k (stage k) (stage (k + 1)) ∧
        (∀ T, Extends (stage k) T → Grows (rayVertices R) k (stage k) T →
          Blocks T (enum k) → Blocks (stage (k + 1)) (enum k)) :=
    (next_exists hRdev (stage k) k (enum k)).choose_spec
  have hMono (a b : ℕ) (hab : a ≤ b) : Extends (stage a) (stage b) := by
    induction b, hab using Nat.le_induction with
    | base => exact Extends.refl _
    | succ b _ ih => exact ih.trans (hNext b).1
  have hBound (i j : ℕ) : j ≤ (stage (i + j)).depth i := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      obtain ⟨n, hn, hb, _⟩ := (hNext (i + j)).2.1 i (Nat.le_add_right _ _)
      exact (Nat.succ_le_of_lt (ih.trans_lt hn)).trans hb
  let rays : ℕ → ℕ → V := fun i n => (stage (i + n)).packing.ray i n
  have hAgree (k i n : ℕ) (hn : n ≤ (stage k).depth i) :
      rays i n = (stage k).packing.ray i n := by
    let b := max k (i + n)
    have h₁ := (hMono (i + n) b (le_max_right _ _) i).2 n (hBound i n)
    have h₂ := (hMono k b (le_max_left _ _) i).2 n hn
    exact h₁.trans h₂.symm
  have arbitrary_bound (i n K : ℕ) (hK : i + n ≤ K) : n ≤ (stage K).depth i :=
    (hBound i n).trans (hMono _ K hK i).1
  let FL : Packing G r₀ start := {
    ray := rays
    endRay := by
      intro i
      refine endRay_of_recurrent hR hRdis ⟨?_, ?_⟩ ?_
      · intro m n he
        let k := max (i + m) (i + n)
        have hm := hAgree k i m (arbitrary_bound i m k (le_max_left _ _))
        have hn := hAgree k i n (arbitrary_bound i n k (le_max_right _ _))
        exact ((stage k).packing.endRay i).1.1 (hm.symm.trans (he.trans hn))
      · intro n
        let k := i + (n + 1)
        have hm := hAgree k i n (arbitrary_bound i n k (by dsimp [k]; omega))
        have hn := hAgree k i (n + 1) (hBound i (n + 1))
        rw [hm, hn]
        exact ((stage k).packing.endRay i).1.2 n
      · intro a
        obtain ⟨n, hn, hq, hw⟩ := (hNext (i + a)).2.1 i (Nat.le_add_right _ _)
        exact ⟨n, (hBound i a).trans hn.le,
          (hAgree (i + a + 1) i n hq).symm ▸ hw⟩
    disjoint := by
      intro i j hij m n he
      let k := max (i + m) (j + n)
      have hm := hAgree k i m (arbitrary_bound i m k (le_max_left _ _))
      have hn := hAgree k j n (arbitrary_bound j n k (le_max_right _ _))
      exact (stage k).packing.disjoint i j hij m n (hm.symm.trans (he.trans hn))
    starting := fun i => (stage (i + 0)).packing.starting i }
  refine ⟨FL, ?_⟩
  intro s hs
  by_contra! hMiss
  obtain ⟨m, _, hw⟩ := recurrent_vertices hRdev hs 0
  obtain ⟨k, hk⟩ := henum hw
  let s' := shiftRay s m
  have hs' : IsEndRay G r₀ s' := shift_endRay hs m
  have hs₀ : s' 0 = enum k := by simpa [s', shiftRay] using hk.symm
  have hav : Avoids s' (indexedVertices FL.ray) := by
    intro n hn
    obtain ⟨i, l, he⟩ := hn
    exact hMiss i (m + n) l he.symm
  let P := stage k
  let Q := stage (k + 1)
  let L : PrefixState G r₀ start := ⟨FL, Q.depth, Q.finite⟩
  have hQL : Extends Q L := by
    intro i
    refine ⟨le_rfl, ?_⟩
    intro n hn
    exact (hAgree (k + 1) i n hn).symm
  obtain ⟨T, hLT, hBT⟩ := block_extension FL Q.depth Q.finite hanchor hs' hav
  have hQT := hQL.trans hLT
  have hPQ : Extends P Q := (hNext k).1
  have hGrow : Grows (rayVertices R) k P T := (hNext k).2.1.mono hQT
  have hB : Blocks Q (enum k) :=
    (hNext k).2.2 T (hPQ.trans hQT) hGrow (by simpa [hs₀] using hBT)
  obtain ⟨n, i, l, hl, he⟩ := hB s' hs' hs₀
  exact hMiss i (m + n) l (((hQL i).2 l hl).symm.trans he).symm

theorem end_rays_main :
    ∀ (V : Type) (G : SimpleGraph V) (r₀ : ℕ → V), IsRay G r₀ →
      (∃ C : Set (ℕ → V), C.Countable ∧ (∀ r ∈ C, IsRay G r) ∧ Devours G r₀ C) →
      ∀ K : Set (ℕ → V), K.Infinite → (∀ r ∈ K, IsEndRay G r₀ r) → PairwiseDisjointRays K →
        ∃ K' : Set (ℕ → V), (∀ r ∈ K', IsEndRay G r₀ r) ∧ PairwiseDisjointRays K' ∧
          Devours G r₀ K' ∧ (fun r => r 0) '' K' = (fun r => r 0) '' K := by
  classical
  intro V G r₀ hanchor hcount K hInf hEnd hDis
  obtain ⟨C, hC, _, hDev⟩ := hcount
  let : Countable K := (packing_countable hC hDev hEnd hDis).to_subtype
  let : Infinite K := hInf.to_subtype
  let e : ℕ ≃ K := Classical.choice (inferInstance : Nonempty (ℕ ≃ K))
  let start : ℕ → V := fun i => (e i).val 0
  let F : Packing G r₀ start := {
    ray := fun i => (e i).val
    endRay := fun i => hEnd _ (e i).property
    disjoint := fun i j hij m n =>
      hDis _ (e i).property _ (e j).property (fun he => hij (e.injective (Subtype.ext he))) m n
    starting := fun _ => rfl }
  obtain ⟨R, hRend, hRdis, hRdev⟩ := maximal_packing (G := G) r₀
  have hW := rayVertices_countable (packing_countable hC hDev hRend hRdis)
  have hWne : (rayVertices R).Nonempty := by
    obtain ⟨n, _, hn⟩ := recurrent_vertices hRdev (F.endRay 0) 0
    exact ⟨F.ray 0 n, hn⟩
  obtain ⟨enum, he⟩ := hW.exists_eq_range hWne
  obtain ⟨FL, hFL⟩ := end_ray_packing_fusion hanchor F hRend hRdis hRdev enum he.subset
  refine ⟨Set.range FL.ray, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact FL.endRay i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne m n
    exact FL.disjoint i j (fun hij => hne (congrArg FL.ray hij)) m n
  · intro s hs
    obtain ⟨i, m, n, hn⟩ := hFL s hs
    exact ⟨FL.ray i, ⟨i, rfl⟩, m, n, hn⟩
  · ext v
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, he⟩
      exact ⟨(e i).val, (e i).property, (FL.starting i).symm.trans he⟩
    · rintro ⟨s, hs, hv⟩
      let i := e.symm ⟨s, hs⟩
      have he : e i = ⟨s, hs⟩ := e.apply_symm_apply _
      exact ⟨FL.ray i, ⟨i, rfl⟩, (FL.starting i).trans
        ((congrArg (fun r : K => r.val 0) he).trans hv)⟩

end EndRaysDraft

theorem OMA.solution : type_of% @OMA.S_opg_end_devouring_rays.main := by
  exact EndRaysDraft.end_rays_main
