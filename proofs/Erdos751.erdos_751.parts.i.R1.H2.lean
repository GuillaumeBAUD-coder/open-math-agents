import OMAReductions.R_Erdos751_erdos_751_parts_i_R1

-- Step Erdos751.erdos_751.parts.i.R1.H2: hypothesis H2 of reduction Erdos751.erdos_751.parts.i.R1
-- Credit: @LordMike
-- H2 := ∀ (W : Type) [Finite W] (H : SimpleGraph W), 2 < Nat.card W →     (∀ x : W, (H.induce {x}ᶜ).Connected) →     (∀ x : W, 3 ≤ Nat.card (H.neighborSet x)) →     ∃ m ∈ H.cycleLengths, ∃ m' ∈ H.cycleLengths, m < m' ∧ m' ≤ m + 2

open SimpleGraph

namespace OMA

namespace BV

variable {W : Type} {G : SimpleGraph W}

/-- Closing a walk with an edge that is not on it gives a cycle. -/
lemma nbg {u v : W} (w : G.Walk u v) (h : G.Adj v u) (hw : s(v, u) ∉ w.edges) :
    ∃ c : G.Walk v v, c.IsCycle ∧ ∀ a ∈ c.support, a = v ∨ a ∈ w.support := by
  classical
  refine ⟨Walk.cons h w.bypass, (Walk.cons_isCycle_iff _ h).mpr
    ⟨w.bypass_isPath, fun he => hw (w.edges_bypass_subset_edges he)⟩, ?_⟩
  intro a ha
  rw [Walk.support_cons, List.mem_cons] at ha
  exact ha.imp id (fun h' => w.support_bypass_subset_support h')

/-- A path starting at `e` has at most one edge at `e`. -/
lemma firstedge {e t : W} (r : G.Walk e t) (hr : r.IsPath) {w w' : W}
    (h1 : s(e, w) ∈ r.edges) (h2 : s(e, w') ∈ r.edges) : w = w' := by
  cases r with
  | nil => simp at h1
  | cons h r' =>
    rename_i x
    rw [Walk.cons_isPath_iff] at hr
    have key : ∀ y, s(e, y) ∈ (Walk.cons h r').edges → y = x := by
      intro y hy
      rw [Walk.edges_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · rcases Sym2.eq_iff.mp hy with ⟨_, h'⟩ | ⟨h', _⟩
        · exact h'
        · exact (h.ne h').elim
      · exact absurd (r'.fst_mem_support_of_mem_edges hy) hr.2
    rw [key w h1, key w' h2]

/-- A path whose end has two further neighbours on the path gives a cycle inside the path. -/
lemma cyc1 {t e : W} (q : G.Walk t e) (hq : q.IsPath) {w w' : W} (hne : w ≠ w')
    (hw : G.Adj e w) (hw' : G.Adj e w') (hws : w ∈ q.support) (hws' : w' ∈ q.support) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ ∀ a ∈ c.support, a ∈ q.support := by
  classical
  have aux : ∀ x, G.Adj e x → ∀ hxs : x ∈ q.support, s(e, x) ∉ q.edges →
      ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ ∀ a ∈ c.support, a ∈ q.support := by
    intro x hx hxs hxe
    obtain ⟨c, hc, hcs⟩ := nbg (q.dropUntil x hxs) hx
      (fun he => hxe (q.edges_dropUntil_subset_edges hxs he))
    refine ⟨e, c, hc, fun a ha => ?_⟩
    rcases hcs a ha with rfl | h'
    · exact q.end_mem_support
    · exact q.support_dropUntil_subset_support hxs h'
  by_cases h1 : s(e, w) ∈ q.edges
  · by_cases h2 : s(e, w') ∈ q.edges
    · exfalso
      have h1' : s(e, w) ∈ q.reverse.edges := by
        rw [Walk.edges_reverse]; exact List.mem_reverse.mpr h1
      have h2' : s(e, w') ∈ q.reverse.edges := by
        rw [Walk.edges_reverse]; exact List.mem_reverse.mpr h2
      exact hne (firstedge q.reverse hq.reverse h1' h2')
    · exact aux w' hw' hws' h2
  · exact aux w hw hws h1

/-- Every path inside `P` extends to one whose end has all its `P`-neighbours on the path. -/
lemma lpx [Fintype W] (P : W → Prop) {t : W} :
    ∀ (n : ℕ) {e : W} (q : G.Walk t e), q.IsPath → (∀ a ∈ q.support, P a) →
      Fintype.card W - q.length ≤ n →
      ∃ (e' : W) (q' : G.Walk t e'), q'.IsPath ∧ (∀ a ∈ q'.support, P a) ∧
        ∀ w, G.Adj e' w → P w → w ∈ q'.support := by
  intro n
  induction n with
  | zero =>
    intro e q hq _ hn
    have := hq.length_lt
    omega
  | succ n ih =>
    intro e q hq hX hn
    by_cases hmax : ∀ w, G.Adj e w → P w → w ∈ q.support
    · exact ⟨e, q, hq, hX, hmax⟩
    · push_neg at hmax
      obtain ⟨w, hw, hwX, hws⟩ := hmax
      refine ih (q.concat hw) (hq.concat hws hw) ?_ ?_
      · intro a ha
        rw [Walk.support_concat] at ha
        rcases List.mem_append.mp ha with h | h
        · exact hX a h
        · rw [List.mem_singleton] at h
          exact h ▸ hwX
      · rw [Walk.length_concat]
        have := hq.length_lt
        omega

lemma n3 [Finite W] {v : W} (hdeg : 3 ≤ Nat.card (G.neighborSet v)) (F : Finset W)
    (hF : F.card ≤ 2) : ∃ w, G.Adj v w ∧ w ∉ F := by
  by_contra hcon
  push_neg at hcon
  have hsub : G.neighborSet v ⊆ (F : Set W) := fun w hw => hcon w hw
  have h1 : (G.neighborSet v).ncard ≤ (F : Set W).ncard :=
    Set.ncard_le_ncard hsub F.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  rw [Nat.card_coe_set_eq] at hdeg
  omega

/-- Joined by a walk all of whose vertices satisfy `P`. -/
def RA (G : SimpleGraph W) (P : W → Prop) (x y : W) : Prop :=
  ∃ w : G.Walk x y, ∀ a ∈ w.support, P a

lemma RA.symm {P : W → Prop} {x y : W} (h : RA G P x y) : RA G P y x := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w.reverse, fun a ha => hw a ?_⟩
  rw [Walk.support_reverse] at ha
  exact List.mem_reverse.mp ha

lemma RA.trans {P : W → Prop} {x y z : W} (h : RA G P x y) (h' : RA G P y z) : RA G P x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  refine ⟨w.append w', fun a ha => ?_⟩
  rcases (Walk.mem_support_append_iff _ _).mp ha with h1 | h1
  · exact hw a h1
  · exact hw' a h1

lemma RA.mono {P Q : W → Prop} {x y : W} (h : RA G P x y) (hPQ : ∀ a, P a → Q a) :
    RA G Q x y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, fun a ha => hPQ a (hw a ha)⟩

lemma conn_insert [DecidableEq W] {B : Finset W}
    (hB : ∀ u ∈ B, ∀ v ∈ B, RA G (· ∈ B) u v) {s b : W} (hb : b ∈ B) (hsb : G.Adj s b) :
    ∀ u ∈ insert s B, ∀ v ∈ insert s B, RA G (· ∈ insert s B) u v := by
  have key : ∀ v ∈ insert s B, RA G (· ∈ insert s B) s v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨Walk.nil, by simp⟩
    · obtain ⟨w, hw⟩ := hB b hb v hv
      refine ⟨Walk.cons hsb w, fun a ha => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hw a ha)
  intro u hu v hv
  exact (key u hu).symm.trans (key v hv)

/-- A cycle minus one of its vertices is still connected. -/
lemma arc0 {z : W} (p : G.Walk z z) (hp : p.IsCycle) :
    ∃ b, ∀ c ∈ p.support, c ≠ z → RA G (fun a => a ∈ p.support ∧ a ≠ z) b c := by
  classical
  cases p with
  | nil => exact absurd hp (by simp)
  | cons h q =>
    have hq := ((Walk.cons_isCycle_iff q h).mp hp).1
    obtain ⟨b, hb, r, hr⟩ := Walk.exists_eq_cons_of_ne h.ne q.reverse
    have hqr : q.reverse.IsPath := hq.reverse
    rw [hr, Walk.cons_isPath_iff] at hqr
    have hrq : ∀ a, a ∈ r.support → a ∈ q.support := by
      intro a ha
      have : a ∈ q.reverse.support := by
        rw [hr, Walk.support_cons]; exact List.mem_cons_of_mem _ ha
      rw [Walk.support_reverse] at this
      exact List.mem_reverse.mp this
    refine ⟨b, fun c hc hcz => ?_⟩
    have hcq : c ∈ q.support := by
      rw [Walk.support_cons, List.mem_cons] at hc
      exact hc.resolve_left hcz
    have hcr : c ∈ r.support := by
      have : c ∈ q.reverse.support := by
        rw [Walk.support_reverse]; exact List.mem_reverse.mpr hcq
      rw [hr, Walk.support_cons, List.mem_cons] at this
      exact this.resolve_left hcz
    refine ⟨r.takeUntil c hcr, fun a ha => ?_⟩
    have har := r.support_takeUntil_subset_support hcr ha
    refine ⟨?_, fun haz => hqr.2 (haz ▸ har)⟩
    rw [Walk.support_cons]
    exact List.mem_cons_of_mem _ (hrq a har)

lemma arc {u : W} (p : G.Walk u u) (hp : p.IsCycle) {z : W} (hz : z ∈ p.support) :
    ∃ b, ∀ c ∈ p.support, c ≠ z → RA G (fun a => a ∈ p.support ∧ a ≠ z) b c := by
  classical
  obtain ⟨b, hb⟩ := arc0 (p.rotate z hz) (hp.rotate hz)
  refine ⟨b, fun c hc hcz => ?_⟩
  refine (hb c ((p.mem_support_rotate_iff z hz).mpr hc) hcz).mono (fun a ha => ?_)
  exact ⟨(p.mem_support_rotate_iff z hz).mp ha.1, ha.2⟩

lemma chord_aux {v : W} (p : G.Walk v v) (hp : p.IsCycle) {w : W} (hw : w ∈ p.support)
    (hvw : G.Adj v w) (hE : s(v, w) ∉ p.edges) :
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length < p.length ∧ ∀ a ∈ c.support, a ∈ p.support := by
  classical
  cases p with
  | nil => exact absurd hp (by simp)
  | cons h q =>
    rename_i a
    have hq := ((Walk.cons_isCycle_iff q h).mp hp).1
    have hwq : w ∈ q.support := by
      rw [Walk.support_cons, List.mem_cons] at hw
      exact hw.resolve_left hvw.ne.symm
    have hE' : s(v, w) ∉ q.edges := fun he => hE (by
      rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
    refine ⟨Walk.cons hvw (q.dropUntil w hwq), (Walk.cons_isCycle_iff _ hvw).mpr
      ⟨hq.dropUntil hwq, fun he => hE' (q.edges_dropUntil_subset_edges hwq he)⟩, ?_, ?_⟩
    · have hspec := congrArg Walk.length (q.take_spec hwq)
      rw [Walk.length_append] at hspec
      have hpos : 0 < (q.takeUntil w hwq).length := by
        rcases Nat.eq_zero_or_pos (q.takeUntil w hwq).length with h0 | h0
        · exfalso
          have haw : a = w := Walk.eq_of_length_eq_zero h0
          subst haw
          apply hE
          rw [Walk.edges_cons]
          exact List.mem_cons_self
        · exact h0
      rw [Walk.length_cons, Walk.length_cons]
      omega
    · intro x hx
      rw [Walk.support_cons, List.mem_cons] at hx ⊢
      exact hx.imp id (fun h' => q.support_dropUntil_subset_support hwq h')

lemma chordless {u : W} (p : G.Walk u u) (hp : p.IsCycle)
    (hmin : ∀ (v : W) (c : G.Walk v v), c.IsCycle → (∀ a ∈ c.support, a ∈ p.support) →
      p.length ≤ c.length)
    {v w : W} (hv : v ∈ p.support) (hw : w ∈ p.support) (hvw : G.Adj v w) :
    s(v, w) ∈ p.edges := by
  classical
  by_contra hE
  have hE' : s(v, w) ∉ (p.rotate v hv).edges := fun he =>
    hE ((p.rotate_edges v hv).mem_iff.mp he)
  obtain ⟨c, hc, hlt, hcs⟩ := chord_aux (p.rotate v hv) (hp.rotate hv)
    ((p.mem_support_rotate_iff v hv).mpr hw) hvw hE'
  have := hmin v c hc (fun a ha => (p.mem_support_rotate_iff v hv).mp (hcs a ha))
  rw [Walk.length_rotate] at hlt
  omega

lemma out [Finite W] {u : W} (p : G.Walk u u) (hp : p.IsCycle)
    (hind : ∀ v ∈ p.support, ∀ w ∈ p.support, G.Adj v w → s(v, w) ∈ p.edges)
    {v : W} (hv : v ∈ p.support) (hdeg : 3 ≤ Nat.card (G.neighborSet v)) :
    ∃ w, G.Adj v w ∧ w ∉ p.support := by
  by_contra hcon
  push_neg at hcon
  have hsub : G.neighborSet v ⊆ p.toSubgraph.neighborSet v := by
    intro w hw
    exact Walk.adj_toSubgraph_iff_mem_edges.mpr (hind v hv w (hcon w hw) hw)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hp.ncard_neighborSet_toSubgraph_eq_two hv] at h1
  rw [Nat.card_coe_set_eq] at hdeg
  omega

lemma cyc2 {u x' y : W} (R : G.Walk x' y) (hR : R.IsPath) (A : G.Walk y u) (hA : A.IsPath)
    (hdis : ∀ a ∈ R.support, a ∈ A.support → a = y) (hadj : G.Adj u x')
    (hx' : x' ∉ A.support) (hu : u ∉ R.support) : (Walk.cons hadj (R.append A)).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.isPath_def, Walk.support_append]
    refine List.Nodup.append hR.support_nodup
      (hA.support_nodup.sublist (List.tail_sublist _)) ?_
    intro a ha ha'
    have := hdis a ha (List.mem_of_mem_tail ha')
    subst this
    have hn := hA.support_nodup
    rw [Walk.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1 ha'
  · intro he
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact hu (R.fst_mem_support_of_mem_edges he)
    · exact hx' (A.snd_mem_support_of_mem_edges he)

lemma split {a u : W} (q : G.Walk a u) : ∀ j ≤ q.length,
    ∃ (y : W) (q1 : G.Walk a y) (q2 : G.Walk y u), q = q1.append q2 ∧ q1.length = j := by
  induction q with
  | nil =>
    intro j hj
    exact ⟨_, Walk.nil, Walk.nil, rfl, (Nat.le_zero.mp hj).symm⟩
  | cons h q ih =>
    intro j hj
    cases j with
    | zero => exact ⟨_, Walk.nil, Walk.cons h q, rfl, rfl⟩
    | succ j =>
      obtain ⟨y, q1, q2, hq, hl⟩ := ih j (by simpa using hj)
      exact ⟨y, Walk.cons h q1, q2, by rw [hq]; rfl, by simp [hl]⟩

lemma exists_cycle [Fintype W] [Nonempty W]
    (hdeg : ∀ x : W, 3 ≤ Nat.card (G.neighborSet x)) :
    ∃ (u : W) (p : G.Walk u u), p.IsCycle := by
  classical
  obtain ⟨t⟩ := ‹Nonempty W›
  obtain ⟨e, q, hq, -, hmax⟩ := lpx (G := G) (fun _ => True) (Fintype.card W)
    (Walk.nil : G.Walk t t) (by simp) (by simp) (by simp)
  obtain ⟨w, hw, -⟩ := n3 (hdeg e) ∅ (by simp)
  obtain ⟨w', hw', hF⟩ := n3 (hdeg e) {w} (by simp)
  have hne : w ≠ w' := fun h => hF (by simp [h])
  obtain ⟨v, c, hc, -⟩ := cyc1 q hq hne hw hw' (hmax w hw trivial) (hmax w' hw' trivial)
  exact ⟨v, c, hc⟩

lemma heart [Fintype W] (hdeg : ∀ x : W, 3 ≤ Nat.card (G.neighborSet x)) (B : Finset W)
    {u : W} (p : G.Walk u u) (hp : p.IsCycle) (hpB : ∀ a ∈ p.support, a ∉ B) {z : W}
    (hz : z ∈ p.support)
    (hS : ∀ s, s ∉ B → s ∉ p.support → ∀ b ∈ B, ¬ G.Adj s b)
    {s : W} (hsB : s ∉ B) (hsp : s ∉ p.support) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ ∀ a ∈ c.support, a ∉ B ∧ a ≠ z := by
  classical
  by_contra hT
  have hnbr : ∀ t, G.Adj s t → t ∉ B → t ≠ z →
      ∃ c ∈ p.support, c ≠ z ∧ RA G (fun a => a ∉ B ∧ a ≠ z ∧ a ≠ s) t c := by
    intro t hst htB htz
    obtain ⟨e, q, hq, hqP, hmax⟩ := lpx (G := G) (fun a => a ∉ B ∧ a ≠ z ∧ a ≠ s)
      (Fintype.card W) (Walk.nil : G.Walk t t) (by simp)
      (by
        intro a ha
        rw [Walk.support_nil, List.mem_singleton] at ha
        subst ha
        exact ⟨htB, htz, hst.ne.symm⟩) (by simp)
    have heP := hqP e q.end_mem_support
    by_cases hep : e ∈ p.support
    · exact ⟨e, hep, heP.2.1, q, hqP⟩
    · exfalso
      have hnb : ∀ w, G.Adj e w → w ∉ B := fun w hw hwB => hS e heP.1 hep w hwB hw
      obtain ⟨w, hw, hwF⟩ := n3 (hdeg e) {z, s} Finset.card_le_two
      have hwz : w ≠ z := fun h => hwF (by simp [h])
      have hws : w ≠ s := fun h => hwF (by simp [h])
      have hwq : w ∈ q.support := hmax w hw ⟨hnb w hw, hwz, hws⟩
      obtain ⟨w2, hw2, hw2F⟩ := n3 (hdeg e) {z, w} Finset.card_le_two
      have hw2z : w2 ≠ z := fun h => hw2F (by simp [h])
      have hw2w : w2 ≠ w := fun h => hw2F (by simp [h])
      by_cases hw2s : w2 = s
      · rw [hw2s] at hw2
        by_cases het : e = t
        · subst het
          have hnil := Walk.isPath_iff_eq_nil.mp hq
          rw [hnil, Walk.support_nil, List.mem_singleton] at hwq
          exact hw.ne hwq.symm
        · obtain ⟨c, hc, hcs⟩ := nbg (q.concat hw2) hst (by
            intro he
            rw [Walk.edges_concat, List.concat_eq_append, List.mem_append,
              List.mem_singleton] at he
            rcases he with he | he
            · exact (hqP s (q.fst_mem_support_of_mem_edges he)).2.2 rfl
            · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact heP.2.2 h1.symm
              · exact het h2.symm)
          apply hT
          refine ⟨s, c, hc, fun a ha => ?_⟩
          rcases hcs a ha with rfl | h'
          · exact ⟨hsB, fun h => hsp (h ▸ hz)⟩
          · rw [Walk.support_concat] at h'
            rcases List.mem_append.mp h' with h'' | h''
            · exact ⟨(hqP a h'').1, (hqP a h'').2.1⟩
            · rw [List.mem_singleton] at h''
              subst h''
              exact ⟨hsB, fun h => hsp (h ▸ hz)⟩
      · have hw2q : w2 ∈ q.support := hmax w2 hw2 ⟨hnb w2 hw2, hw2z, hw2s⟩
        obtain ⟨v, c, hc, hcs⟩ := cyc1 q hq (Ne.symm hw2w) hw hw2 hwq hw2q
        exact hT ⟨v, c, hc, fun a ha => ⟨(hqP a (hcs a ha)).1, (hqP a (hcs a ha)).2.1⟩⟩
  have hsnb : ∀ t, G.Adj s t → t ∉ B := fun t ht htB => hS s hsB hsp t htB ht
  obtain ⟨t1, ht1, ht1F⟩ := n3 (hdeg s) {z} (by simp)
  have ht1z : t1 ≠ z := fun h => ht1F (by simp [h])
  obtain ⟨t2, ht2, ht2F⟩ := n3 (hdeg s) {z, t1} Finset.card_le_two
  have ht2z : t2 ≠ z := fun h => ht2F (by simp [h])
  have ht21 : t2 ≠ t1 := fun h => ht2F (by simp [h])
  obtain ⟨c1, hc1, hc1z, r1⟩ := hnbr t1 ht1 (hsnb t1 ht1) ht1z
  obtain ⟨c2, hc2, hc2z, r2⟩ := hnbr t2 ht2 (hsnb t2 ht2) ht2z
  obtain ⟨b, hb⟩ := arc p hp hz
  have hmono : ∀ a, (a ∈ p.support ∧ a ≠ z) → (a ∉ B ∧ a ≠ z ∧ a ≠ s) :=
    fun a ha => ⟨hpB a ha.1, ha.2, fun h => hsp (h ▸ ha.1)⟩
  have a1 := (hb c1 hc1 hc1z).mono hmono
  have a2 := (hb c2 hc2 hc2z).mono hmono
  obtain ⟨w, hw⟩ := (r1.trans a1.symm).trans (a2.trans r2.symm)
  obtain ⟨c, hc, hcs⟩ := nbg (w.concat ht2.symm) ht1 (by
    intro he
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact (hw s (w.fst_mem_support_of_mem_edges he)).2.2 rfl
    · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ht2.ne h1
      · exact ht21 h2.symm)
  apply hT
  refine ⟨s, c, hc, fun a ha => ?_⟩
  rcases hcs a ha with rfl | h'
  · exact ⟨hsB, fun h => hsp (h ▸ hz)⟩
  · rw [Walk.support_concat] at h'
    rcases List.mem_append.mp h' with h'' | h''
    · exact ⟨(hw a h'').1, (hw a h'').2.1⟩
    · rw [List.mem_singleton] at h''
      subst h''
      exact ⟨hsB, fun h => hsp (h ▸ hz)⟩

lemma final [Finite W] (hdeg : ∀ x : W, 3 ≤ Nat.card (G.neighborSet x)) (B : Finset W)
    (hB : ∀ u ∈ B, ∀ v ∈ B, RA G (· ∈ B) u v) {u : W} (p : G.Walk u u) (hp : p.IsCycle)
    (hpB : ∀ a ∈ p.support, a ∉ B)
    (hind : ∀ v ∈ p.support, ∀ w ∈ p.support, G.Adj v w → s(v, w) ∈ p.edges)
    (hall : ∀ a, a ∈ B ∨ a ∈ p.support) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  classical
  cases p with
  | nil => exact absurd hp (by simp)
  | cons h q =>
    have hq := (Walk.cons_isCycle_iff q h).mp hp
    have h3 := hp.three_le_length
    rw [Walk.length_cons] at h3
    obtain ⟨y, q1, q2, hq12, hl⟩ := split q ((q.length - 2) / 2) (by omega)
    subst hq12
    have hq1 : q1.IsPath := hq.1.of_append_left
    have hq2 : q2.IsPath := hq.1.of_append_right
    have hl2 : (q1.append q2).length = q1.length + q2.length := Walk.length_append _ _
    have hq2pos : 0 < q2.length := by omega
    have hu1 : u ∉ q1.support := by
      have hn := hq.1.support_nodup
      rw [Walk.support_append] at hn
      have hd := (List.nodup_append.mp hn).2.2
      have hut : u ∈ q2.support.tail := by
        apply q2.end_mem_tail_support
        intro hnil
        have := Walk.nil_iff_length_eq.mp hnil
        omega
      intro hu
      exact hd u hu u hut rfl
    have hsub1 : ∀ a ∈ q1.support, a ∈ (Walk.cons h (q1.append q2)).support := by
      intro a ha
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ ((Walk.mem_support_append_iff _ _).mpr (Or.inl ha))
    have hsub2 : ∀ a ∈ q2.support, a ∈ (Walk.cons h (q1.append q2)).support := by
      intro a ha
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ ((Walk.mem_support_append_iff _ _).mpr (Or.inr ha))
    have hyp : y ∈ (Walk.cons h (q1.append q2)).support := hsub1 y q1.end_mem_support
    have hup : u ∈ (Walk.cons h (q1.append q2)).support := Walk.start_mem_support _
    have hyu : y ≠ u := fun hh => hu1 (hh ▸ q1.end_mem_support)
    obtain ⟨x', hx', hx'p⟩ := out _ hp hind hup (hdeg u)
    obtain ⟨y', hy', hy'p⟩ := out _ hp hind hyp (hdeg y)
    have hx'B : x' ∈ B := (hall x').resolve_right hx'p
    have hy'B : y' ∈ B := (hall y').resolve_right hy'p
    obtain ⟨wB, hwB⟩ := hB x' hx'B y' hy'B
    have hbyB : ∀ a ∈ wB.bypass.support, a ∈ B :=
      fun a ha => hwB a (wB.support_bypass_subset_support ha)
    have hR : (wB.bypass.concat hy'.symm).IsPath :=
      (wB.bypass_isPath).concat (fun hy => hpB y hyp (hbyB y hy)) hy'.symm
    have hRs : ∀ a ∈ (wB.bypass.concat hy'.symm).support, a ∈ B ∨ a = y := by
      intro a ha
      rw [Walk.support_concat] at ha
      rcases List.mem_append.mp ha with h' | h'
      · exact Or.inl (hbyB a h')
      · exact Or.inr (List.mem_singleton.mp h')
    have huR : u ∉ (wB.bypass.concat hy'.symm).support := by
      intro hu
      rcases hRs u hu with h' | h'
      · exact hpB u hup h'
      · exact hyu h'.symm
    have hA1 : (Walk.cons h q1).reverse.IsPath :=
      ((Walk.cons_isPath_iff h q1).mpr ⟨hq1, hu1⟩).reverse
    have hA1s : ∀ a ∈ (Walk.cons h q1).reverse.support,
        a ∈ (Walk.cons h (q1.append q2)).support := by
      intro a ha
      rw [Walk.support_reverse] at ha
      have ha' := List.mem_reverse.mp ha
      rw [Walk.support_cons, List.mem_cons] at ha'
      rcases ha' with rfl | ha'
      · exact hup
      · exact hsub1 a ha'
    have hc1 := cyc2 (wB.bypass.concat hy'.symm) hR (Walk.cons h q1).reverse hA1
      (by
        intro a ha ha'
        rcases hRs a ha with h' | h'
        · exact absurd h' (hpB a (hA1s a ha'))
        · exact h')
      hx' (fun hh => hpB x' (hA1s x' hh) hx'B) huR
    have hc2 := cyc2 (wB.bypass.concat hy'.symm) hR q2 hq2
      (by
        intro a ha ha'
        rcases hRs a ha with h' | h'
        · exact absurd h' (hpB a (hsub2 a ha'))
        · exact h')
      hx' (fun hh => hpB x' (hsub2 x' hh) hx'B) huR
    refine ⟨_, ⟨u, _, hc1, rfl⟩, _, ⟨u, _, hc2, rfl⟩, ?_, ?_⟩
    · simp only [Walk.length_cons, Walk.length_append, Walk.length_reverse, Walk.length_concat]
      omega
    · simp only [Walk.length_cons, Walk.length_append, Walk.length_reverse, Walk.length_concat]
      omega

/-- A connected vertex set that misses some cycle. -/
def Good (G : SimpleGraph W) (B : Finset W) : Prop :=
  (∀ u ∈ B, ∀ v ∈ B, RA G (· ∈ B) u v) ∧
    ∃ (u : W) (p : G.Walk u u), p.IsCycle ∧ ∀ a ∈ p.support, a ∉ B

theorem main_bv (W : Type) [Finite W] (G : SimpleGraph W) (hcard : 2 < Nat.card W)
    (hcon : ∀ x : W, (G.induce {x}ᶜ).Connected)
    (hdeg : ∀ x : W, 3 ≤ Nat.card (G.neighborSet x)) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Nonempty W := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hcard
  have hwalk : ∀ u v : W, Nonempty (G.Walk u v) := by
    intro u v
    obtain ⟨x, hxu, hxv⟩ : ∃ x : W, x ≠ u ∧ x ≠ v := by
      by_contra hcon'
      push_neg at hcon'
      have hsub : (Finset.univ : Finset W) ⊆ {u, v} := fun x _ => by
        by_cases hxu : x = u
        · simp [hxu]
        · simp [hcon' x hxu]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
      have h2 := Finset.card_le_two (a := u) (b := v)
      omega
    have hr := (hcon x).preconnected ⟨u, by simpa using hxu.symm⟩ ⟨v, by simpa using hxv.symm⟩
    exact hr.map (Embedding.induce _).toHom
  obtain ⟨u0, p0, hp0⟩ := exists_cycle (G := G) hdeg
  have hG0 : Good G ∅ := ⟨by simp, u0, p0, hp0, by simp⟩
  obtain ⟨B, hBgood, hBmax⟩ : ∃ B, Good G B ∧ ∀ B', Good G B' → B'.card ≤ B.card := by
    obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (Good G)) Finset.card
      ⟨∅, by simp [hG0]⟩
    exact ⟨B, (Finset.mem_filter.mp hB).2, fun B' hB' =>
      hmax B' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB'⟩)⟩
  obtain ⟨hBconn, hBcyc⟩ := hBgood
  have hex : ∃ n, ∃ (u : W) (p : G.Walk u u), p.IsCycle ∧ (∀ a ∈ p.support, a ∉ B) ∧
      p.length = n := by
    obtain ⟨u, p, hp, hpB⟩ := hBcyc
    exact ⟨_, u, p, hp, hpB, rfl⟩
  obtain ⟨u, p, hp, hpB, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (v : W) (c : G.Walk v v), c.IsCycle → (∀ a ∈ c.support, a ∈ p.support) →
      p.length ≤ c.length := by
    intro v c hc hcs
    rw [hlen]
    exact Nat.find_min' hex ⟨v, c, hc, fun a ha => hpB a (hcs a ha), rfl⟩
  have hind : ∀ v ∈ p.support, ∀ w ∈ p.support, G.Adj v w → s(v, w) ∈ p.edges :=
    fun v hv w hw hvw => chordless p hp hmin hv hw hvw
  have hS : ∀ s, s ∉ B → s ∉ p.support → ∀ b ∈ B, ¬ G.Adj s b := by
    intro s hsB hsp b hb hsb
    have hgood : Good G (insert s B) := ⟨conn_insert hBconn hb hsb, u, p, hp, fun a ha => by
      rw [Finset.mem_insert]
      rintro (rfl | h')
      · exact hsp ha
      · exact hpB a ha h'⟩
    have := hBmax _ hgood
    rw [Finset.card_insert_of_notMem hsB] at this
    omega
  have hall : ∀ a, a ∈ B ∨ a ∈ p.support := by
    intro s
    by_contra hcon'
    push_neg at hcon'
    obtain ⟨hsB, hsp⟩ := hcon'
    have hBne : B.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hgood : Good G {s} := by
        refine ⟨?_, u, p, hp, ?_⟩
        · intro a ha b hb
          rw [Finset.mem_singleton] at ha hb
          subst ha
          subst hb
          exact ⟨Walk.nil, by simp⟩
        · intro a ha
          rw [Finset.mem_singleton]
          rintro rfl
          exact hsp ha
      have := hBmax _ hgood
      simp [hne] at this
    obtain ⟨b0, hb0⟩ := hBne
    obtain ⟨w0⟩ := hwalk b0 u
    obtain ⟨d, -, hd1, hd2⟩ := w0.exists_boundary_dart (B : Set W) (Finset.mem_coe.mpr hb0)
      (fun hh => hpB u p.start_mem_support (Finset.mem_coe.mp hh))
    have hd1' : d.fst ∈ B := Finset.mem_coe.mp hd1
    have hd2' : d.snd ∉ B := fun hh => hd2 (Finset.mem_coe.mpr hh)
    have hzp : d.snd ∈ p.support := by
      by_contra hh
      exact hS d.snd hd2' hh d.fst hd1' d.adj.symm
    obtain ⟨v, c, hc, hcs⟩ := heart hdeg B p hp hpB hzp hS hsB hsp
    have hgood : Good G (insert d.snd B) :=
      ⟨conn_insert hBconn hd1' d.adj.symm, v, c, hc, fun a ha => by
        rw [Finset.mem_insert]
        rintro (rfl | h')
        · exact (hcs _ ha).2 rfl
        · exact (hcs a ha).1 h'⟩
    have := hBmax _ hgood
    rw [Finset.card_insert_of_notMem hd2'] at this
    omega
  exact final hdeg B hBconn p hp hpB hind hall

end BV

end OMA

theorem OMA.solution : OMA.R_Erdos751_erdos_751_parts_i_R1.H2 := by
  intro W _ H hcard hcon hdeg
  exact OMA.BV.main_bv W H hcard hcon hdeg
