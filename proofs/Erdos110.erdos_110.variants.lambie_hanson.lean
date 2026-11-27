import FormalConjectures.ErdosProblems.«110»
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
Lambie-Hanson's quantitative theorem on finite subgraphs of uncountably chromatic
graphs, arXiv:1902.08177, Theorem A. The proof uses the prefix construction of
Section 4, the Specker relations of Erdős–Hajnal, and Shelah's club-guessing theorem
(Theorem 3.2). The type-realization step uses a club closed under witness choices
and upper bounds for finite prefixes.
-/

noncomputable section

open Set

namespace LambieHansonTree

variable {A : Type*} [LinearOrder A] [WellFoundedLT A]

abbrev Vertex (A : Type*) [Preorder A] := Σ a : A, Set.Iio a → ℕ

def restrictNode (t : Vertex A) {a : A} (h : a < t.1) : Vertex A :=
  ⟨a, fun x => t.2 ⟨x, x.2.trans h⟩⟩

def Eligible (R : ℕ → A → A → Prop) (t : Vertex A) (k : ℕ) (a : A) : Prop :=
  ∃ h : a < t.1, t.2 ⟨a, h⟩ = k ∧ ∀ j ≤ k, R j a t.1

def Parent (R : ℕ → A → A → Prop) (k : ℕ) (t s : Vertex A) : Prop :=
  ∃ h : s.1 < t.1,
    s = restrictNode t h ∧ Eligible R t k s.1 ∧ ∀ a, Eligible R t k a → s.1 ≤ a

omit [WellFoundedLT A] in
theorem Parent.rank_lt {R : ℕ → A → A → Prop} {k : ℕ} {t s : Vertex A}
    (h : Parent R k t s) : s.1 < t.1 := h.choose

omit [WellFoundedLT A] in
theorem Parent.unique {R : ℕ → A → A → Prop} {k : ℕ} {t s u : Vertex A}
    (hs : Parent R k t s) (hu : Parent R k t u) : s = u := by
  obtain ⟨hslt, hs, hse, hsmin⟩ := hs
  obtain ⟨hult, hu, hue, humin⟩ := hu
  obtain ⟨a, sa⟩ := s
  obtain ⟨b, ub⟩ := u
  have h : a = b := le_antisymm (hsmin _ hue) (humin _ hse)
  subst b
  exact hs.trans hu.symm

theorem exists_parent (R : ℕ → A → A → Prop) (k : ℕ) (t : Vertex A)
    (he : ∃ a, Eligible R t k a) : ∃ s, Parent R k t s := by
  let S := {a | Eligible R t k a}
  have hS : S.Nonempty := he
  let a := wellFounded_lt.min S hS
  have ha : Eligible R t k a := wellFounded_lt.min_mem S hS
  have hlt : a < t.1 := ha.choose
  exact ⟨restrictNode t hlt, hlt, rfl, ha,
    fun b hb => le_of_not_gt (wellFounded_lt.not_lt_min S hb)⟩

def graph (R : ℕ → A → A → Prop) : SimpleGraph (Vertex A) where
  Adj s t := ∃ k, Parent R k s t ∨ Parent R k t s
  symm := ⟨fun _ _ ⟨k, h⟩ => ⟨k, h.symm⟩⟩
  loopless := ⟨fun s ⟨_, h⟩ => h.elim
    (fun h => lt_irrefl s.1 h.rank_lt) (fun h => lt_irrefl s.1 h.rank_lt)⟩

def branch (ρ : A → ℕ) (a : A) : Vertex A := ⟨a, fun i => ρ i⟩

def branchColors {R : ℕ → A → A → Prop} (c : (graph R).Coloring ℕ) : A → ℕ :=
  wellFounded_lt.fix (fun a prev => c ⟨a, fun i => prev i i.2⟩)

theorem branchColors_eq {R : ℕ → A → A → Prop} (c : (graph R).Coloring ℕ) (a : A) :
    branchColors c a = c (branch (branchColors c) a) := by
  unfold branchColors
  rw [WellFounded.fix_eq]
  rfl

/-- The monochromatic pair property of the ladder relations rules out countable colorings. -/
theorem no_countable_coloring (R : ℕ → A → A → Prop)
    (realize : ∀ ρ : A → ℕ, ∃ a b k, a < b ∧ ρ a = k ∧ ρ b = k ∧
      ∀ j ≤ k, R j a b) : IsEmpty ((graph R).Coloring ℕ) := by
  refine ⟨fun c => ?_⟩
  let ρ := branchColors c
  obtain ⟨a, b, k, hab, hak, hbk, hR⟩ := realize ρ
  have he : ∃ i, Eligible R (branch ρ b) k i := ⟨a, hab, hak, hR⟩
  obtain ⟨s, hs⟩ := exists_parent R k (branch ρ b) he
  have ⟨hlt, hprefix, ⟨_, hsk, _⟩, _⟩ := hs
  have heq : s = branch ρ s.1 := hprefix
  have hc : c s = c (branch ρ b) := by
    calc
      c s = ρ s.1 := (congrArg c heq).trans (branchColors_eq c s.1).symm
      _ = k := hsk
      _ = ρ b := hbk.symm
      _ = c (branch ρ b) := branchColors_eq c b
  exact c.valid (show (graph R).Adj s (branch ρ b) from ⟨k, Or.inr hs⟩) hc

private abbrev Colors := Set.Iio (Ordinal.omega.{0} 1)

private theorem colors_uncountable : ¬ (Set.univ : Set Colors).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, ← Cardinal.lt_aleph_one_iff, Cardinal.mk_univ]
  change ¬ Cardinal.mk (Set.Iio (Ordinal.omega.{0} 1)) < Cardinal.aleph 1
  rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega, Cardinal.lift_aleph, Ordinal.lift_one]
  exact lt_irrefl (Cardinal.aleph 1)

/-- Recursively color each node with a countable ordinal omitted by its lower neighbors. -/
theorem countable_ordinal_coloring (R : ℕ → A → A → Prop) :
    Nonempty ((graph R).Coloring Colors) := by
  classical
  have wf : WellFounded (fun s t : Vertex A => s.1 < t.1) :=
    InvImage.wf Sigma.fst wellFounded_lt
  let prior (t : Vertex A) (prev : ∀ s : Vertex A, s.1 < t.1 → Colors) : Set Colors :=
    {a | ∃ (k : ℕ) (s : Vertex A) (h : Parent R k t s), a = prev s h.rank_lt}
  have exists_omitted (t : Vertex A) (prev : ∀ s : Vertex A, s.1 < t.1 → Colors) :
      ∃ a : Colors, a ∉ prior t prev := by
    have hcount : (prior t prev).Countable := by
      let C (k : ℕ) := {a | ∃ (s : Vertex A) (h : Parent R k t s), a = prev s h.rank_lt}
      suffices h : (⋃ k, C k).Countable by
        apply h.mono
        rintro a ⟨k, s, hs, ha⟩
        exact mem_iUnion.mpr ⟨k, show a ∈ C k from ⟨s, hs, ha⟩⟩
      refine Set.countable_iUnion (fun k => ?_)
      refine Set.Subsingleton.countable (fun a ⟨s, hs, ha⟩ b ⟨u, hu, hb⟩ => ?_)
      cases hs.unique hu
      exact ha.trans hb.symm
    by_contra! h
    exact colors_uncountable (hcount.mono (fun a _ => h a))
  let step (t : Vertex A) (prev : ∀ s : Vertex A, s.1 < t.1 → Colors) : Colors :=
    (exists_omitted t prev).choose
  let c := wf.fix step
  have hne (k : ℕ) {t s : Vertex A} (h : Parent R k t s) : c t ≠ c s := by
    intro he
    have hn : step t (fun u _ => c u) ∉ prior t (fun u _ => c u) :=
      (exists_omitted t (fun u _ => c u)).choose_spec
    apply hn
    exact ⟨k, s, h, (WellFounded.fix_eq wf step t).symm.trans he⟩
  exact ⟨SimpleGraph.Coloring.mk c (fun ⟨k, h⟩ =>
    h.elim (hne k) (fun h => (hne k h).symm))⟩

theorem chromaticNumberAlephOne (R : ℕ → A → A → Prop)
    (realize : ∀ ρ : A → ℕ, ∃ a b k, a < b ∧ ρ a = k ∧ ρ b = k ∧
      ∀ j ≤ k, R j a b) : Erdos737.ChromaticNumberAlephOne (graph R) :=
  ⟨countable_ordinal_coloring R, no_countable_coloring R realize⟩

private theorem no_odd_closed_walk_of_bounded {V : Type*} [Finite V] (G : SimpleGraph V)
    {m : ℕ} (hm : Nat.card V ≤ m)
    (h : ∀ (v : V) (p : G.Walk v v), p.length ≤ m → ¬ Odd p.length) :
    ∀ (v : V) (p : G.Walk v v), ¬ Odd p.length := by
  intro v p hp
  classical
  let has (n : ℕ) := ∃ (v : V) (p : G.Walk v v), p.length = n ∧ Odd n
  have hex : ∃ n, has n := ⟨p.length, v, p, rfl, hp⟩
  obtain ⟨u, w, hw, ho⟩ := Nat.find_spec hex
  have hmin (v : V) (p : G.Walk v v) (ht : p.length < w.length) : ¬ Odd p.length := by
    intro hop
    exact (not_lt_of_ge (Nat.find_min' hex (show has p.length from ⟨v, p, rfl, hop⟩)))
      (hw ▸ ht)
  have hinj : Function.Injective (fun i : Fin w.length => w.getVert i) := by
    have hnot (i j : ℕ) (hij : i < j) (hj : j < w.length)
        (hvw : w.getVert i = w.getVert j) : False := by
      let inner := (w.drop i).take (j - i)
      have hin : (w.drop i).getVert (j - i) = w.getVert i := by
        rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij.le]
        exact hvw.symm
      let closed := inner.copy rfl hin
      let outer := (w.take i).append ((w.drop j).copy hvw.symm rfl)
      have hc : closed.length = j - i := by
        simp [closed, inner, min_eq_left (show j - i ≤ w.length - i by omega)]
      have hoa : outer.length = i + (w.length - j) := by
        simp [outer, min_eq_left (show i ≤ w.length by omega)]
      have hinner := hmin _ closed (by omega)
      have houter := hmin _ outer (by omega)
      rw [hc] at hinner
      rw [hoa] at houter
      have hodd : Odd w.length := hw.symm ▸ ho
      rw [Nat.odd_iff] at hinner houter hodd
      omega
    intro i j he
    exact Fin.ext (by
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact (hnot i j hlt j.isLt he).elim
      · exact heq
      · exact (hnot j i hgt i.isLt he.symm).elim)
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at hc
  exact h u w (hc.trans hm) (hw.symm ▸ ho)

private theorem two_colorable_of_no_odd_closed_walk {V : Type*} (G : SimpleGraph V)
    (h : ∀ (v : V) (p : G.Walk v v), ¬ Odd p.length) : G.Colorable 2 := by
  classical
  let root (c : G.ConnectedComponent) := c.nonempty_supp.some
  have hr (v : V) : G.Reachable (root (G.connectedComponentMk v)) v :=
    SimpleGraph.ConnectedComponent.exact (G.connectedComponentMk v).nonempty_supp.some_mem
  let p (v : V) : G.Walk (root (G.connectedComponentMk v)) v := (hr v).some
  let c (v : V) : Fin 2 := ⟨(p v).length % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro u v huv hcv
  let q := ((p u).concat huv).append
    ((p v).reverse.copy rfl (congrArg root (SimpleGraph.ConnectedComponent.sound huv.reachable).symm))
  have hlen : q.length = (p u).length + 1 + (p v).length := by simp [q]
  have hpar := congrArg Fin.val hcv
  change (p u).length % 2 = (p v).length % 2 at hpar
  exact h _ q (Nat.odd_iff.mpr (by omega))

/-- Each label has a two-coloring, by alternating along its unique parent. -/
theorem label_coloring (R : ℕ → A → A → Prop) (k : ℕ) :
    ∃ c : Vertex A → Bool, ∀ t s, Parent R k t s → c t ≠ c s := by
  classical
  have wf : WellFounded (fun s t : Vertex A => s.1 < t.1) :=
    InvImage.wf Sigma.fst wellFounded_lt
  let step (t : Vertex A) (prev : ∀ s : Vertex A, s.1 < t.1 → Bool) : Bool :=
    if h : ∃ s, Parent R k t s then !(prev h.choose h.choose_spec.rank_lt) else false
  let c := wf.fix step
  refine ⟨c, fun t s h => ?_⟩
  have hex : ∃ s, Parent R k t s := ⟨s, h⟩
  have hatt : c t = !(c s) := by
    have he := WellFounded.fix_eq wf step t
    change c t = step t (fun u _ => c u) at he
    rw [he]
    simp only [step, dif_pos hex, hex.choose_spec.unique h]
  rw [hatt]
  cases c s <;> decide

/-- Symmetrization of an oriented relation which increases rank. -/
def levelGraph (R : ℕ → A → A → Prop) (inc : ∀ j a b, R j a b → a < b)
    (k : ℕ) : SimpleGraph A where
  Adj a b := R k a b ∨ R k b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun a h => lt_irrefl a (inc k a a (h.elim id id))⟩

/-- A finite subgraph small enough for level k has at most 2^(k+1) colors. -/
theorem finite_color_bound (R : ℕ → A → A → Prop)
    (inc : ∀ j a b, R j a b → a < b)
    (g : ℕ → ℕ)
    (girth : ∀ (k : ℕ) (a : A) (w : (levelGraph R inc k).Walk a a),
      w.length ≤ g k → ¬ Odd w.length)
    (H : (graph R).Subgraph) (hfin : H.verts.Finite) (k : ℕ)
    (hsmall : H.verts.ncard ≤ g k) : H.coe.Colorable (2 ^ (k + 1)) := by
  classical
  let T : SimpleGraph H.verts :=
    { Adj := fun x y => H.coe.Adj x y ∧ ∃ j ≥ k,
        Parent R j x.val y.val ∨ Parent R j y.val x.val
      symm := ⟨fun _ _ ⟨h, j, hj, hp⟩ => ⟨h.symm, j, hj, hp.symm⟩⟩
      loopless := ⟨fun _ h => H.coe.loopless.irrefl _ h.1⟩ }
  let φ : T →g levelGraph R inc k :=
    ⟨fun x => x.val.1, fun {x y} ⟨_, j, hj, hp⟩ =>
      hp.elim (fun h => Or.inr (h.choose_spec.2.1.choose_spec.2 k hj))
        (fun h => Or.inl (h.choose_spec.2.1.choose_spec.2 k hj))⟩
  let : Finite H.verts := hfin.to_subtype
  have hcard : Nat.card H.verts ≤ g k := by
    simpa only [Nat.card_coe_set_eq] using hsmall
  obtain ⟨c⟩ := two_colorable_of_no_odd_closed_walk T
    (no_odd_closed_walk_of_bounded T hcard (fun v w hw => by
      simpa only [SimpleGraph.Walk.length_map] using
        girth k (φ v) (w.map φ) (by simpa only [SimpleGraph.Walk.length_map] using hw)))
  choose d hd using label_coloring R
  let colors (x : H.verts) : (Fin k → Bool) × Fin 2 :=
    (fun i => d i x.val, c x)
  have hcolors : ∀ {x y}, H.coe.Adj x y → colors x ≠ colors y := by
    intro x y hxy he
    obtain ⟨j, hp⟩ := (H.adj_sub hxy : (graph R).Adj x.val y.val)
    by_cases hj : j < k
    · have heq : d j x.val = d j y.val :=
        congrFun (congrArg Prod.fst he) ⟨j,hj⟩
      exact hp.elim (fun h => hd j _ _ h heq) (fun h => hd j _ _ h heq.symm)
    · exact c.valid (show T.Adj x y from ⟨hxy, j, le_of_not_gt hj, hp⟩)
        (congrArg Prod.snd he)
  have ncolors : Fintype.card ((Fin k → Bool) × Fin 2) = 2 ^ (k + 1) := by
    simp [pow_succ]
  rw [← ncolors]
  exact ⟨SimpleGraph.Coloring.mk (fun x => Fintype.equivFin _ (colors x))
    (fun h he => hcolors h ((Fintype.equivFin _).injective he))⟩

/-- Translate the dyadic finite-color bound to an arbitrary requested lower-growth function. -/
theorem sufficient_data (f : ℕ → ℕ) {A : Type 1} [LinearOrder A] [WellFoundedLT A]
    (R : ℕ → A → A → Prop) (inc : ∀ j a b, R j a b → a < b)
    (realize : ∀ ρ : A → ℕ, ∃ a b k, a < b ∧ ρ a = k ∧ ρ b = k ∧
      ∀ j ≤ k, R j a b)
    (girth : ∀ (k : ℕ) (a : A) (w : (levelGraph R inc k).Walk a a),
      w.length ≤ (Finset.range (2 ^ (k + 2) + 1)).sup f → ¬ Odd w.length) :
    ∃ (V : Type 1) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G ∧
      ∀ k : ℕ, 3 ≤ k → ∀ H : G.Subgraph, H.verts.Finite → H.verts.ncard < f k →
        H.coe.chromaticNumber < (k : ℕ∞) := by
  classical
  let g (j : ℕ) := (Finset.range (2 ^ (j + 2) + 1)).sup f
  refine ⟨Vertex A, graph R, chromaticNumberAlephOne R realize, ?_⟩
  intro k hk H hfin hsmall
  have hex : ∃ j : ℕ, k ≤ 2 ^ (j + 2) := ⟨k, by
    have h := Nat.lt_two_pow_self (n := k + 2)
    omega⟩
  let j := Nat.find hex
  have hj : k ≤ 2 ^ (j + 2) := Nat.find_spec hex
  have hlt : 2 ^ (j + 1) < k := by
    rcases Nat.eq_zero_or_pos j with he | hjp
    · simpa [he] using (show 2 < k by omega)
    · have hmin := Nat.find_min hex (m := j - 1) (by omega : j - 1 < j)
      have he : j - 1 + 2 = j + 1 := by omega
      rwa [he, not_le] at hmin
  have hg : f k ≤ g j := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
  exact (finite_color_bound R inc g girth H hfin j (hsmall.le.trans hg)).chromaticNumber_le.trans_lt
    (by exact_mod_cast hlt)

end LambieHansonTree

namespace LambieHansonSpecker

open Finset

variable {X : Type*} [LinearOrder X]

/-- Order inequalities of the Specker type for the first n terms of two sequences. -/
def Forward (s n : ℕ) (a b : ℕ → X) : Prop :=
  (∀ i, s + i < n → a (s + i) < b i) ∧
    ∀ i, s + i + 1 < n → b i < a (s + i + 1)

theorem first_lt {s n : ℕ} {a b : ℕ → X} (hsn : s < n) (ha : Monotone a)
    (h : Forward s n a b) : a 0 < b 0 :=
  (ha (Nat.zero_le _)).trans_lt (h.1 0 (by simpa using hsn))

private def count (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  ((range n).filter P).card

private theorem count_mono (P : ℕ → Prop) [DecidablePred P] : Monotone (count P) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  rw [mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1.trans_le hij, hx.2⟩

private theorem count_step (P : ℕ → Prop) [DecidablePred P] (i : ℕ) :
    count P (i + 1) = count P i + if P i then 1 else 0 := by
  unfold count
  rw [range_add_one, filter_insert]
  split_ifs with hi
  · rw [card_insert_of_notMem (by simp)]
  · simp

private theorem count_total (P : ℕ → Prop) [DecidablePred P] (i : ℕ) :
    count P i + count (fun j => ¬P j) i = i := by
  simpa [count] using card_filter_add_card_filter_not (s := range i) P

private theorem count_pos_of_mem (P : ℕ → Prop) [DecidablePred P] {i L : ℕ}
    (h : i < L) (hp : P i) : 0 < count P L :=
  Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨Finset.mem_range.mpr h, hp⟩⟩

/-- Choose coordinates staying in range along a closed walk with a forward majority.
Each chosen value strictly increases, while the final coordinate is at most the initial one. -/
private theorem majority_forward {s n L : ℕ} (hs : 0 < s) (hn : 2*s*s < n)
    (hL : L ≤ 2*s+1) (hLpos : 0 < L)
    (V : ℕ → ℕ → X) (hmono : ∀ i, Monotone (V i)) (hclosed : V L = V 0)
    (P : ℕ → Prop) [DecidablePred P]
    (hfor : ∀ i < L, P i → Forward s n (V i) (V (i+1)))
    (hback : ∀ i < L, ¬P i → Forward s n (V (i+1)) (V i))
    (hmajor : count (fun i => ¬ P i) L < count P L) : False := by
  let F := count P
  let B := count (fun i => ¬P i)
  have htot : F L + B L = L := count_total P L
  change B L < F L at hmajor
  by_cases hmixed : B L = 0
  · have step (i : ℕ) (hi : i < L) : V i 0 < V (i+1) 0 := by
      apply first_lt (s := s) (n := n) (by nlinarith) (hmono i)
      exact hfor i hi (by
        by_contra h
        exact (Nat.ne_of_gt (count_pos_of_mem (fun i => ¬P i) hi h)) hmixed)
    have ht : V 0 0 < V L 0 := by
      exact (strictMonoOn_Iic_of_lt_succ (fun i hi => step i hi))
        (Set.mem_Iic.mpr hLpos.le) (Set.mem_Iic.mpr le_rfl) hLpos
    exact lt_irrefl _ (hclosed ▸ ht)
  have hF : F L ≤ 2*s := by omega
  have hB : B L ≤ s := by omega
  have hFroom : (s : ℤ) * (F L : ℤ) < n := by
    have h := Nat.mul_le_mul_left s hF
    exact_mod_cast (show s * F L < n by nlinarith only [h, hn])
  have hBroom : ((s : ℤ)+1) * (B L : ℤ) < n := by
    have h := Nat.mul_le_mul_left (s+1) hB
    exact_mod_cast (show (s+1) * B L < n by nlinarith only [h, hn, hs])
  let z (i : ℕ) : ℤ := ((s : ℤ)+1) * (B i : ℤ) - s * (F i : ℤ)
  have hz0 : z 0 = 0 := by simp [z, F, B, count]
  have hzL : z L ≤ 0 := by
    have hc := Nat.mul_le_mul_left s (show B L + 1 ≤ F L by omega)
    apply sub_nonpos.mpr
    exact_mod_cast (show (s+1) * B L ≤ s * F L by nlinarith only [hc, hB])
  have width (i j : ℕ) (hi : i ≤ L) (hj : j ≤ L) : z i - z j < n := by
    rcases le_total i j with hij | hji
    · have h1 := mul_le_mul_of_nonneg_left
        (Int.ofNat_le.mpr (count_mono (fun i => ¬P i) hij))
        (show 0 ≤ (s : ℤ)+1 by positivity)
      have h2 := mul_le_mul_of_nonneg_left
        (Int.ofNat_le.mpr (count_mono P hj)) (show 0 ≤ (s : ℤ) by positivity)
      have h3 : 0 ≤ (s : ℤ) * (F i : ℤ) := by positivity
      change ((s : ℤ)+1) * (B i : ℤ) ≤ ((s : ℤ)+1) * (B j : ℤ) at h1
      change (s : ℤ) * (F j : ℤ) ≤ (s : ℤ) * (F L : ℤ) at h2
      dsimp only [z]
      linarith only [hFroom, h1, h2, h3]
    · have h1 := mul_le_mul_of_nonneg_left
        (Int.ofNat_le.mpr (count_mono P hji)) (show 0 ≤ (s : ℤ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left
        (Int.ofNat_le.mpr (count_mono (fun i => ¬P i) hi))
        (show 0 ≤ (s : ℤ)+1 by positivity)
      have h3 : 0 ≤ ((s : ℤ)+1) * (B j : ℤ) := by positivity
      change (s : ℤ) * (F j : ℤ) ≤ (s : ℤ) * (F i : ℤ) at h1
      change ((s : ℤ)+1) * (B i : ℤ) ≤ ((s : ℤ)+1) * (B L : ℤ) at h2
      dsimp only [z]
      linarith only [hBroom, h1, h2, h3]
  let S := (range (L+1)).image z
  have hmem (i : ℕ) (hi : i ≤ L) : z i ∈ S :=
    mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hS : S.Nonempty := ⟨z 0, hmem 0 (by omega)⟩
  let m := S.min' hS
  obtain ⟨j, hj, (he : z j = m)⟩ := mem_image.mp (S.min'_mem hS)
  have hj' : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  let index (i : ℕ) : ℕ := (z i - m).toNat
  have hindex {i : ℕ} (hi : i ≤ L) : (index i : ℤ) = z i - m := by
    apply Int.toNat_of_nonneg
    exact sub_nonneg.mpr (S.min'_le _ (hmem i hi))
  have inrange {i : ℕ} (hi : i ≤ L) : index i < n := by
    have h := width i j hi hj'
    rwa [he, ← hindex hi, Int.ofNat_lt] at h
  have step (i : ℕ) (hi : i < L) : V i (index i) < V (i+1) (index (i+1)) := by
    have hix := hindex hi.le
    have hiy := hindex (i := i+1) (by omega)
    by_cases hp : P i
    · have hf : F (i+1) = F i + 1 := by simpa [F, hp] using count_step P i
      have hb : B (i+1) = B i := by simpa [B, hp] using count_step (fun i => ¬P i) i
      have hzi : z (i+1) = z i - s := by
        simp only [z, hf, hb, Nat.cast_add, Nat.cast_one]
        ring
      have heq : s + index (i+1) = index i := by omega
      rw [← heq]
      exact (hfor i hi hp).1 _ (heq.symm ▸ inrange hi.le)
    · have hf : F (i+1) = F i := by simpa [F, hp] using count_step P i
      have hb : B (i+1) = B i + 1 := by simpa [B, hp] using count_step (fun i => ¬P i) i
      have hzi : z (i+1) = z i + s + 1 := by
        simp only [z, hf, hb, Nat.cast_add, Nat.cast_one]
        ring
      have heq : s + index i + 1 = index (i+1) := by omega
      rw [← heq]
      exact (hback i hi hp).2 _ (heq.symm ▸ inrange hi)
  have ht : V 0 (index 0) < V L (index L) := by
    exact (strictMonoOn_Iic_of_lt_succ (fun i hi => step i hi))
      (Set.mem_Iic.mpr hLpos.le) (Set.mem_Iic.mpr le_rfl) hLpos
  have hi : index L ≤ index 0 := by
    have hi0 := hindex (i := 0) (Nat.zero_le L)
    have hiL := hindex (i := L) le_rfl
    omega
  rw [hclosed] at ht
  exact (not_lt_of_ge ((hmono 0) hi)) ht

/-- Reflect indices and reverse the ambient order to exchange the orientations. -/
private theorem reflect_forward {s n : ℕ} {a b : ℕ → X} (h : Forward s n a b) :
    Forward (X := Xᵒᵈ) s n
      (fun i => OrderDual.toDual (b (n-1-i))) (fun i => OrderDual.toDual (a (n-1-i))) := by
  constructor
  · intro i hi
    have hpos : s + (n - 1 - (s+i)) < n := by omega
    have he : s + (n - 1 - (s+i)) = n - 1 - i := by omega
    change a (n-1-i) < b (n-1-(s+i))
    simpa only [he] using h.1 _ hpos
  · intro i hi
    have hpos : s + (n - 1 - (s+i+1)) + 1 < n := by omega
    have he : s + (n - 1 - (s+i+1)) + 1 = n - 1 - i := by omega
    change b (n-1-(s+i+1)) < a (n-1-i)
    simpa only [he] using h.2 _ hpos

/-- The Specker relation admits no odd closed walk of length at most 2s+1. -/
theorem no_short_odd_closed_sequence {s n L : ℕ} (hs : 0 < s) (hn : 2*s*s < n)
    (hL : L ≤ 2*s+1) (ho : Odd L)
    (V : ℕ → ℕ → X) (hmono : ∀ i, Monotone (V i)) (hclosed : V L = V 0)
    (hstep : ∀ i < L, Forward s n (V i) (V (i+1)) ∨ Forward s n (V (i+1)) (V i)) :
    False := by
  classical
  let P (i : ℕ) := Forward s n (V i) (V (i+1))
  have hpos : 0 < L := by rw [Nat.odd_iff] at ho; omega
  have htot := count_total P L
  have huneven : count P L ≠ count (fun i => ¬P i) L := by
    rw [Nat.odd_iff] at ho
    omega
  rcases lt_or_gt_of_ne huneven with hb | hf
  · let W (i j : ℕ) : Xᵒᵈ := OrderDual.toDual (V i (n-1-j))
    have hm (i : ℕ) : Monotone (W i) := fun _ _ h => hmono i (by omega)
    have hc : W L = W 0 := by simp only [W, hclosed]
    apply majority_forward hs hn hL hpos W hm hc (fun i => ¬P i)
    · intro i hi hnP
      exact reflect_forward ((hstep i hi).resolve_left hnP)
    · intro i _ hnnP
      exact reflect_forward (not_not.mp hnnP)
    · simpa only [not_not] using hb
  · exact majority_forward hs hn hL hpos V hmono hclosed P
      (fun _ _ h => h) (fun i hi h => (hstep i hi).resolve_left h) hf

theorem no_short_odd_closed_walk {V : Type*} (G : SimpleGraph V)
    {s n : ℕ} (hs : 0 < s) (hn : 2*s*s < n) (f : V → ℕ → X) (hmono : ∀ v, Monotone (f v))
    (hmap : ∀ {u v}, G.Adj u v → Forward s n (f u) (f v) ∨ Forward s n (f v) (f u))
    {v : V} (w : G.Walk v v) (hw : w.length ≤ 2*s+1) : ¬ Odd w.length := by
  intro ho
  exact no_short_odd_closed_sequence hs hn hw ho (f ∘ w.getVert)
    (fun _ => hmono _) (by simp)
    (fun _ hi => hmap (w.adj_getVert_succ hi))

end LambieHansonSpecker

open Set Order Cardinal

namespace LambieHansonGuess

universe u v

variable {A : Type u} [LinearOrder A] [WellFoundedLT A] [Nonempty A]

local instance orderBot : OrderBot A := WellFoundedLT.toOrderBot A
local instance completeOrderBot : ConditionallyCompleteLinearOrderBot A :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot A

abbrev Point (A : Type*) [LinearOrder A] :=
  {a : A // ∃ l : ℕ → A, StrictMono l ∧ (∀ n, l n < a) ∧
    ∀ x < a, ∃ n, x < l n}

structure ClubZero (A : Type*) [LinearOrder A] [OrderBot A] where
  carrier : Set A
  isClub : IsClub carrier
  zero_mem : ⊥ ∈ carrier

def Acc (E : ClubZero A) (a : A) : Prop :=
  ∀ x < a, ∃ e ∈ E.carrier, x < e ∧ e < a

abbrev Domain (E : ClubZero A) := {a : Point A // Acc E a.val}

private def ladder (a : Point A) : ℕ → A := a.2.choose

private theorem ladder_spec (a : Point A) :
    StrictMono (ladder a) ∧ (∀ n, ladder a n < a.val) ∧
      ∀ x < a.val, ∃ n, x < ladder a n := a.2.choose_spec

private theorem bottom_lt_point (a : Point A) : ⊥ < a.val :=
  bot_le.trans_lt ((ladder_spec a).2.1 0)

private def dropAt (E : ClubZero A) (x : A) : A := sSup (E.carrier ∩ Iio x)

private theorem bddAbove_drop (E : ClubZero A) (x : A) :
    BddAbove (E.carrier ∩ Iio x) := ⟨x, fun _ h => h.2.le⟩

private theorem drop_le (E : ClubZero A) (x : A) : dropAt E x ≤ x :=
  (isLUB_csSup' (bddAbove_drop E x)).2 (fun _ h => h.2.le)

private theorem le_drop {E : ClubZero A} {e x : A} (he : e ∈ E.carrier) (hx : e < x) :
    e ≤ dropAt E x := le_csSup (bddAbove_drop E x) ⟨he, hx⟩

private theorem drop_mem (E : ClubZero A) (x : A) : dropAt E x ∈ E.carrier := by
  rcases (E.carrier ∩ Iio x).eq_empty_or_nonempty with hh | hh
  · simpa only [dropAt, hh, csSup_empty] using E.zero_mem
  · exact E.isClub.csSup_mem inter_subset_left hh (bddAbove_drop E x)

private theorem drop_mono {E D : ClubZero A} (h : E.carrier ⊆ D.carrier) (x : A) :
    dropAt E x ≤ dropAt D x :=
  (isLUB_csSup' (bddAbove_drop E x)).2 (fun _ hz => le_drop (h hz.1) hz.2)

private theorem exists_drop_gt (E : ClubZero A) (a : Domain E) (x : Set.Iio a.val.val) :
    ∃ n, x.val < dropAt E (ladder a.val n) := by
  obtain ⟨e, he, hxe, hea⟩ := a.2 x x.2
  obtain ⟨n, hen⟩ := (ladder_spec a.val).2.2 e hea
  exact ⟨n, hxe.trans_le (le_drop he hen)⟩

private def liftDrop (E : ClubZero A) (a : Domain E) (n : ℕ) : Set.Iio a.val.val :=
  ⟨dropAt E (ladder a.val n), (drop_le E _).trans_lt ((ladder_spec a.val).2.1 n)⟩

private def dropSeq (E : ClubZero A) (a : Domain E) : ℕ → Set.Iio a.val.val
  | 0 => liftDrop E a (exists_drop_gt E a ⟨⊥, bottom_lt_point a.val⟩).choose
  | n + 1 =>
    let x := max (dropSeq E a n) ⟨ladder a.val n, (ladder_spec a.val).2.1 n⟩
    liftDrop E a (exists_drop_gt E a x).choose

def normalized (E : ClubZero A) (a : Domain E) (n : ℕ) : A := dropSeq E a n

theorem normalized_strictMono (E : ClubZero A) (a : Domain E) :
    StrictMono (normalized E a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (le_max_left (normalized E a n) (ladder a.val n)).trans_lt
    (exists_drop_gt E a
      (max (dropSeq E a n) ⟨ladder a.val n, (ladder_spec a.val).2.1 n⟩)).choose_spec

theorem normalized_below (E : ClubZero A) (a : Domain E) (n : ℕ) :
    normalized E a n < a.val.val := (dropSeq E a n).2

theorem normalized_cofinal (E : ClubZero A) (a : Domain E) (x : A) (hx : x < a.val.val) :
    ∃ n, x < normalized E a n := by
  obtain ⟨n, hn⟩ := (ladder_spec a.val).2.2 x hx
  exact ⟨n+1, lt_trans (hn.trans_le (le_max_right (normalized E a n) (ladder a.val n)))
    (exists_drop_gt E a
      (max (dropSeq E a n) ⟨ladder a.val n, (ladder_spec a.val).2.1 n⟩)).choose_spec⟩

theorem normalized_pos (E : ClubZero A) (a : Domain E) (n : ℕ) : ⊥ < normalized E a n :=
  ((exists_drop_gt E a ⟨⊥, bottom_lt_point a.val⟩).choose_spec).trans_le
    ((normalized_strictMono E a).monotone (Nat.zero_le n))

private theorem normalized_is_drop (E : ClubZero A) (a : Domain E) (n : ℕ) :
    ∃ i, normalized E a n = dropAt E (ladder a.val i) := by
  cases n with
  | zero => exact ⟨_, rfl⟩
  | succ n => exact ⟨_, rfl⟩

private theorem nat_range_bounded (hA : ℵ₀ < cof A) (f : ℕ → A) : BddAbove (range f) := by
  refine BddAbove.of_not_isCofinal fun h => hA.not_ge ((cof_le h).trans ?_)
  simpa using (mk_range_le_lift (f := f))

private theorem exists_acc [NoMaxOrder A] (hA : ℵ₀ < cof A) (E : ClubZero A) : Nonempty (Domain E) := by
  choose f hf using fun x : A => E.isClub.isCofinal x
  choose g hg using (exists_gt : ∀ x : A, ∃ y, x < y)
  let seq : ℕ → A := Nat.rec ⊥ (fun _ x => f (g x))
  have hstrict : StrictMono seq := strictMono_nat_of_lt_succ
    (fun i => (hg (seq i)).trans_le (hf _).2)
  have hmem : ∀ i, seq i ∈ E.carrier := fun i => by
    cases i with
    | zero => exact E.zero_mem
    | succ i => exact (hf _).1
  let δ : A := sSup (range seq)
  have hlub : IsLUB (range seq) δ := isLUB_csSup (range_nonempty _) (nat_range_bounded hA seq)
  have hlt (i : ℕ) : seq i < δ := (hstrict (Nat.lt_succ_self i)).trans_le (hlub.1 ⟨i+1,rfl⟩)
  have hco (x : A) (h : x < δ) : ∃ n, x < seq n := by
    by_contra! hn
    exact h.not_ge (hlub.2 (by rintro _ ⟨i,rfl⟩; exact hn i))
  exact ⟨⟨⟨δ, seq, hstrict, hlt, hco⟩, fun x hx => by
    obtain ⟨n, hn⟩ := hco x hx
    exact ⟨seq n, hmem n, hn, hlt n⟩⟩⟩

/-- An antitone sequence in a well-order stabilizes above an index attaining its minimum. -/
private theorem antitone_stabilizes {I : Type v} [LinearOrder I] (s : I → A)
    [Nonempty I] (hs : Antitone s) : ∃ i, ∀ j ≥ i, s j = s i := by
  let a := wellFounded_lt.min (range s) (range_nonempty _)
  obtain ⟨i, hi⟩ := wellFounded_lt.min_mem (range s) (range_nonempty _)
  refine ⟨i, fun j hj => le_antisymm (hs hj) ?_⟩
  rw [hi]
  exact le_of_not_gt (wellFounded_lt.not_lt_min (range s) ⟨j, rfl⟩)

private def interClubs {I : Type v} (hA : ℵ₀ < cof A)
    (hI : Cardinal.lift.{u} #I < Cardinal.lift.{v} (cof A))
    (E : I → ClubZero A) : ClubZero A :=
  ⟨⋂ i, (E i).carrier, IsClub.iInter hA.ne' hI (fun i => (E i).isClub),
    mem_iInter.mpr (fun i => (E i).zero_mem)⟩

/-- A countable club guesser whenever a smaller intermediate index order has
uncountable cofinality. In the intended application the two orders are ω₂ and ω₁. -/
theorem exists_club_guesser [NoMaxOrder A] (hA : ℵ₀ < cof A)
    (I : Type v) [LinearOrder I] [WellFoundedLT I] [Nonempty I] [NoMaxOrder I]
    (hI : ℵ₀ < cof I)
    (hIA : Cardinal.lift.{u} #I < Cardinal.lift.{v} (cof A)) :
    ∃ E : ClubZero A, ∀ D : ClubZero A,
      ∃ a : Domain E, range (normalized E a) ⊆ D.carrier := by
  classical
  by_contra! h
  choose bad hbad using h
  let Prereq (i : I) := ∀ j : I, j < i → ClubZero A
  let cut (i : I) (prev : Prereq i) : ClubZero A :=
    interClubs hA ((Cardinal.lift_le.mpr (Cardinal.mk_subtype_le (· ∈ Iio i))).trans_lt hIA)
      (fun j : Set.Iio i => prev j j.2)
  let step (i : I) (prev : Prereq i) : ClubZero A := bad (cut i prev)
  let D : I → ClubZero A := wellFounded_lt.fix step
  let E (i : I) : ClubZero A := cut i (fun j _ => D j)
  have eqD (i : I) : D i = bad (E i) := WellFounded.fix_eq wellFounded_lt step i
  have cut_mem (i : I) (x : A) : x ∈ (E i).carrier ↔ ∀ j < i, x ∈ (D j).carrier := by
    change x ∈ (⋂ j : Set.Iio i, (D j).carrier) ↔ _
    simp only [mem_iInter, Subtype.forall, mem_Iio]
  let common : ClubZero A := interClubs hA hIA D
  have sub_common (i : I) : common.carrier ⊆ (E i).carrier :=
    fun x hx => (cut_mem i x).mpr (fun j _ => (mem_iInter.mp hx) j)
  have ant : ∀ {i j : I}, i ≤ j → (E j).carrier ⊆ (E i).carrier :=
    fun {i j} h x hx => (cut_mem i x).mpr (fun k hk => (cut_mem j x).mp hx k (hk.trans_le h))
  obtain ⟨a⟩ := exists_acc hA common
  let δ : Point A := a.val
  let q (i : I) : Domain (E i) :=
    ⟨δ, fun x hx => by
      obtain ⟨e, he, hlt, hgt⟩ := a.2 x hx
      exact ⟨e, sub_common i he, hlt, hgt⟩⟩
  let d (n : ℕ) (i : I) : A := dropAt (E i) (ladder δ n)
  have hstable (n : ℕ) : ∃ i : I, ∀ j ≥ i, d n j = d n i :=
    antitone_stabilizes (d n) (fun _ _ h => drop_mono (ant h) _)
  choose i₀ hi₀ using hstable
  obtain ⟨i, hi⟩ := nat_range_bounded hI i₀
  obtain ⟨j, hij⟩ := exists_gt i
  have same (n : ℕ) : d n i = d n j :=
    (hi₀ n i (hi ⟨n,rfl⟩)).trans ((hi₀ n j ((hi ⟨n,rfl⟩).trans hij.le)).symm)
  apply hbad (E i) (q i)
  rw [← eqD]
  rintro x ⟨m, rfl⟩
  obtain ⟨n, hn⟩ := normalized_is_drop (E i) (q i) m
  have he : normalized (E i) (q i) m = d n j := hn.trans (same n)
  rw [he]
  exact (cut_mem j (d n j)).mp (drop_mem (E j) _) i hij

/-- A countable partition of the ladder indices preserves club guessing in one cell. -/
theorem exists_guessing_color (hA : ℵ₀ < cof A)
    (E : ClubZero A)
    (guess : ∀ D : ClubZero A, ∃ a : Domain E, range (normalized E a) ⊆ D.carrier)
    (ρ : Domain E → ℕ) : ∃ k : ℕ, ∀ D : ClubZero A,
      ∃ a : Domain E, ρ a = k ∧ range (normalized E a) ⊆ D.carrier := by
  classical
  by_contra! h
  choose D hD using h
  let C : ClubZero A :=
    ⟨⋂ k, (D k).carrier, IsClub.iInter_of_countable hA.ne' (fun k => (D k).isClub),
      mem_iInter.mpr (fun k => (D k).zero_mem)⟩
  obtain ⟨a, ha⟩ := guess C
  exact (hD (ρ a) a rfl) (fun x hx => mem_iInter.mp (ha hx) (ρ a))

section TypeRealization

variable [NoMaxOrder A]

omit [NoMaxOrder A] in
private theorem finite_upper {T : Set A} (hn : T.Nonempty) (p : List A)
    (h : ∀ x ∈ p, ∃ y ∈ T, x < y) : ∃ y ∈ T, ∀ x ∈ p, x < y := by
  induction p with
  | nil => obtain ⟨y, hy⟩ := hn; exact ⟨y, hy, by simp⟩
  | cons x p ih =>
    obtain ⟨y, hy, hxy⟩ := h x (by simp)
    obtain ⟨z, hz, hpz⟩ := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    refine ⟨max y z, ?_, ?_⟩
    · rcases le_total y z with h | h
      · simpa only [max_eq_right h] using hz
      · simpa only [max_eq_left h] using hy
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hxy.trans_le (le_max_left _ _)
      · exact (hpz u hu).trans_le (le_max_right _ _)

omit [NoMaxOrder A] in
private theorem finite_upper_lub {T : Set A} (hn : T.Nonempty) {x : A} (hlub : IsLUB T x)
    (p : List A) (h : ∀ y ∈ p, y < x) : ∃ y ∈ T, ∀ z ∈ p, z < y :=
  finite_upper hn p (fun y hy => (lt_isLUB_iff hlub).mp (h y hy))

private def closureSet (F : List A → A → A) : Set A :=
  {x | x = ⊥ ∨ ∀ (p : List A) (y : A), (∀ z ∈ p, z < x) → y < x → F p y < x}

/-- A club of initial segments closed under the given finite-arity choice function. -/
private theorem isClub_closureSet (hA : ℵ₀ < cof A) (small : ∀ x : A, # (Iic x) < cof A)
    (F : List A → A → A) : IsClub (closureSet F) := by
  classical
  constructor
  · intro T hT hn _ x hlub
    refine Or.inr (fun p y hp hy => ?_)
    obtain ⟨z, hz, hlt⟩ := finite_upper_lub hn hlub (y :: p) (by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hy
      · exact hp e he)
    have hyz := hlt y (by simp)
    have hz' := hT hz
    change z = ⊥ ∨ _ at hz'
    obtain hz' | hz' := hz'
    · exact (not_lt_of_ge bot_le (hz' ▸ hyz)).elim
    · exact (hz' p y (fun e he => hlt e (List.mem_cons_of_mem _ he)) hyz).trans_le (hlub.1 hz)
  · intro a
    let T (x : A) := range (fun z : List (Iic x) × Iic x => F (z.1.map Subtype.val) z.2)
    have hT (x : A) : BddAbove (T x) := by
      refine BddAbove.of_not_isCofinal fun h => ((cof_le h).trans_lt ?_).false
      refine mk_range_le.trans_lt ?_
      rw [mk_prod, lift_id, lift_id]
      exact Cardinal.mul_lt_of_lt hA.le
        ((mk_list_le_max _).trans_lt (max_lt hA (small x))) (small x)
    let cap (x : A) : A := sSup (T x)
    have hcap (x : A) (p : List A) (y : A) (hp : ∀ z ∈ p, z ≤ x) (hy : y ≤ x) :
        F p y ≤ cap x := by
      apply le_csSup (hT x)
      have hp' : ∀ z ∈ p, z ∈ Iic x := fun z hz => mem_Iic.mpr (hp z hz)
      let q : List (Iic x) := p.attachWith (· ∈ Iic x) hp'
      refine ⟨(q, ⟨y,hy⟩), ?_⟩
      change F q.unattach y = F p y
      rw [show q.unattach = p from List.unattach_attachWith]
    choose g hg using (exists_gt : ∀ x : A, ∃ y, x < y)
    let seq : ℕ → A := Nat.rec a (fun _ x => g (max x (cap x)))
    have hc (n : ℕ) : cap (seq n) < seq (n+1) := (le_max_right _ _).trans_lt (hg _)
    have hlub : IsLUB (range seq) (sSup (range seq)) :=
      isLUB_csSup (range_nonempty _) (nat_range_bounded hA seq)
    refine ⟨sSup (range seq), Or.inr (fun p y hp hy => ?_), hlub.1 ⟨0,rfl⟩⟩
    obtain ⟨z, ⟨n, rfl⟩, hlt⟩ := finite_upper_lub (range_nonempty _) hlub (y :: p) (by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hy
      · exact hp e he)
    exact ((hcap _ p y (fun z hz => (hlt z (List.mem_cons_of_mem _ hz)).le)
      (hlt y (by simp)).le).trans_lt (hc n)).trans_le (hlub.1 ⟨n+1,rfl⟩)

private def closureClub (hA : ℵ₀ < cof A) (small : ∀ x : A, # (Iic x) < cof A)
    (F : List A → A → A) : ClubZero A :=
  ⟨closureSet F, isClub_closureSet hA small F, Or.inl rfl⟩

omit [NoMaxOrder A] in
private theorem closure_lt {F : List A → A → A} {x : A} (hx : x ∈ closureSet F)
    (hpos : ⊥ < x) {p : List A} (hp : ∀ z ∈ p, z < x) {y : A} (hy : y < x) :
    F p y < x := hx.elim (fun he => (hpos.ne' he).elim) (fun h => h p y hp hy)

private def head (l : ℕ → A) (m : ℕ) : List A := List.ofFn (fun i : Fin m => l i)

omit [LinearOrder A] [WellFoundedLT A] [Nonempty A] [NoMaxOrder A] in
private theorem head_length (l : ℕ → A) (m : ℕ) : (head l m).length = m := by simp [head]

omit [LinearOrder A] [WellFoundedLT A] [Nonempty A] [NoMaxOrder A] in
private theorem head_succ (l : ℕ → A) (m : ℕ) : head l (m+1) = head l m ++ [l m] := by
  unfold head
  rw [List.ofFn_succ_last]
  rfl

omit [LinearOrder A] [WellFoundedLT A] [Nonempty A] [NoMaxOrder A] in
private theorem head_get (l : ℕ → A) {m i : ℕ} (hi : i < (head l m).length) :
    (head l m)[i] = l i := by simp [head]

private def Alive {E : ClubZero A} (Y : Set (Domain E)) : ℕ → List A → Prop
  | 0, p => ∃ b ∈ Y, ∀ i (hi : i < p.length), normalized E b i = p[i]
  | r+1, p => IsCofinal {x | Alive Y r (p ++ [x])}

private def Children {E : ClubZero A} (Y : Set (Domain E)) (N : ℕ) (p : List A) : Set A :=
  {x | Alive Y (N-p.length) (p ++ [x])}

omit [NoMaxOrder A] in
private theorem alive_step {E : ClubZero A} {Y : Set (Domain E)} {N : ℕ} {p : List A}
    (hp : p.length ≤ N) :
    Alive Y (N+1-p.length) p ↔ IsCofinal (Children Y N p) := by
  rw [show N+1-p.length = N-p.length+1 by omega]
  rfl

/-- Realize any finite list of consecutive intervals between terms of the first ladder.
The second rank can be chosen larger than the first. -/
theorem realize_intervals (hA : ℵ₀ < cof A) (small : ∀ x : A, # (Iic x) < cof A)
    (E : ClubZero A) (Y : Set (Domain E))
    (guess : ∀ D : ClubZero A, ∃ a ∈ Y, range (normalized E a) ⊆ D.carrier)
    (N : ℕ) (lo : ℕ → ℕ) (hlo : Monotone lo) :
    ∃ a ∈ Y, ∃ b ∈ Y, a < b ∧ ∀ i < N,
      normalized E a (lo i) < normalized E b i ∧
      normalized E b i < normalized E a (lo i + 1) := by
  classical
  let K := Children Y N
  have many (p : List A) (h : IsCofinal (K p)) (x : A) : ∃ y ∈ K p, x < y := by
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz, hyz⟩ := h y
    exact ⟨z, hz, hy.trans_le hyz⟩
  let next (p : List A) (x : A) : A :=
    if h : IsCofinal (K p) then (many p h x).choose else ⊥
  let bound (p : List A) : A :=
    if h : ¬ IsCofinal (K p) then (BddAbove.of_not_isCofinal h).choose else ⊥
  let F (p : List A) (x : A) : A := max (next p x) (bound p)
  let D := closureClub hA small F
  obtain ⟨a, ha, hDa⟩ := guess D
  let l := normalized E a
  have close (i : ℕ) (p : List A) (x : A) (hp : ∀ z ∈ p, z < l i) (hx : x < l i) :
      F p x < l i :=
    closure_lt (hDa ⟨i,rfl⟩) (normalized_pos E a i) hp hx
  have mono_l : StrictMono l := normalized_strictMono E a
  have alive_a (r : ℕ) (hr : r ≤ N+1) : Alive Y r (head l (N+1-r)) := by
    induction r with
    | zero =>
      exact ⟨a, ha, fun i hi => (head_get l hi).symm⟩
    | succ r ih =>
      let m := N-r
      have hlen : N+1-(r+1) = m := by dsimp [m]; omega
      have hprev : N+1-r = m+1 := by dsimp [m]; omega
      have hdep : N-(head l m).length = r := by rw [head_length]; dsimp [m]; omega
      have hk : l m ∈ K (head l m) := by
        change Alive Y (N-(head l m).length) (head l m ++ [l m])
        rw [hdep, ← head_succ, ← hprev]
        exact ih (by omega)
      rw [hlen]
      change IsCofinal {x | Alive Y r (head l m ++ [x])}
      rw [← hdep]
      change IsCofinal (K (head l m))
      by_contra hbad
      have hupper : l m ≤ bound (head l m) := by
        simpa only [bound, dif_pos hbad] using (BddAbove.of_not_isCofinal hbad).choose_spec hk
      have hp (z : A) (hz : z ∈ head l m) : z < l m := by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        rw [head_get]
        exact mono_l (head_length l m ▸ hi)
      exact (not_lt_of_ge (hupper.trans (le_max_right _ _)))
        (close m (head l m) ⊥ hp (normalized_pos E a m))
  have alive_nil : Alive Y (N+1) [] := by
    simpa [head] using alive_a (N+1) le_rfl
  let Fits (p : List A) : Prop := ∀ i (hi : i < p.length),
    l (lo i) < p[i] ∧ p[i] < l (lo i+1)
  have fit_prefix (m : ℕ) (hm : m ≤ N) :
      ∃ p : List A, p.length = m ∧ Alive Y (N+1-m) p ∧ Fits p := by
    induction m with
    | zero => exact ⟨[], rfl, alive_nil, by simp [Fits]⟩
    | succ m ih =>
      obtain ⟨p, hp, hAlive, hfit⟩ := ih (by omega)
      have hgood : IsCofinal (K p) :=
        (alive_step (show p.length ≤ N by omega)).mp (hp.symm ▸ hAlive)
      let x := next p (l (lo m))
      have hx : x ∈ K p ∧ l (lo m) < x := by
        simpa only [x, next, dif_pos hgood] using (many p hgood (l (lo m))).choose_spec
      have hprev : ∀ z ∈ p, z < l (lo m+1) := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        exact (hfit i hi).2.trans_le (mono_l.monotone (Nat.add_le_add_right (hlo (by omega)) 1))
      have hbelow : x < l (lo m+1) :=
        (le_max_left _ _).trans_lt (close _ p _ hprev (mono_l (Nat.lt_succ_self (lo m))))
      have hlen : (p ++ [x]).length = m+1 := by simp [hp]
      refine ⟨p ++ [x], hlen, ?_, ?_⟩
      · have hchild := hx.1
        change Alive Y (N-p.length) (p ++ [x]) at hchild
        rw [show N+1-(m+1) = N-p.length by omega]
        exact hchild
      · intro i hi
        by_cases hi' : i < p.length
        · rw [List.getElem_append_left hi']
          exact hfit i hi'
        · have hieq : i = m := by omega
          subst i
          have he : (p ++ [x])[m] = x := by
            rw [List.getElem_append_right (by omega)]
            simp [hp]
          rw [he]
          exact ⟨hx.2, hbelow⟩
  obtain ⟨p, hp, hpAlive, hpfit⟩ := fit_prefix N le_rfl
  have hco : IsCofinal (K p) := (alive_step (show p.length ≤ N by omega)).mp (hp.symm ▸ hpAlive)
  obtain ⟨x, hx, hax⟩ := many p hco a.val.val
  have hb : Alive Y 0 (p ++ [x]) := by
    change Alive Y (N-p.length) (p ++ [x]) at hx
    simpa [hp] using hx
  obtain ⟨b, hb, hb_match⟩ := hb
  have hlen : (p ++ [x]).length = N+1 := by simp [hp]
  have hbx : normalized E b N = x := by
    have he := hb_match N (by omega)
    rw [List.getElem_append_right (by omega)] at he
    simpa [hp] using he
  have hab : a < b := by
    change a.val.val < b.val.val
    exact lt_trans hax (hbx ▸ normalized_below E b N)
  refine ⟨a, ha, b, hb, hab, fun i hi => ?_⟩
  have he := hb_match i (by omega)
  have hip : i < p.length := by omega
  rw [List.getElem_append_left hip] at he
  rw [he]
  exact hpfit i hip

end TypeRealization
end LambieHansonGuess

namespace LambieHansonAssembly

open Set Ordinal Cardinal Order
open LambieHansonGuess LambieHansonTree LambieHansonSpecker

private abbrev Ranks := (ω_ (2 : Ordinal.{1})).ToType
private abbrev Stages := (ω_ (1 : Ordinal.{1})).ToType

private theorem cof_ranks : cof Ranks = ℵ_ (2 : Ordinal.{1}) := by
  have h := Cardinal.cof_omega_add_one (1 : Ordinal.{1})
  rw [show (1 : Ordinal.{1}) + 1 = 2 by norm_num] at h
  simpa only [Ranks, Ordinal.cof_toType] using h

private theorem cof_stages : cof Stages = ℵ_ (1 : Ordinal.{1}) := by
  exact (Ordinal.cof_toType _).trans Cardinal.isRegular_aleph_one.cof_omega_eq

private theorem noMax_omega_toType (o : Ordinal.{1}) : NoMaxOrder (ω_ o).ToType := by
  apply Ordinal.isSuccPrelimit_type_lt_iff.mp
  rw [Ordinal.type_toType]
  exact (Cardinal.isSuccLimit_omega _).isSuccPrelimit

private theorem card_ranks : #Ranks = ℵ_ (2 : Ordinal.{1}) :=
  (Cardinal.mk_toType _).trans (Ordinal.card_omega _)

private theorem small_initial (x : Ranks) : # (Iic x) < cof Ranks := by
  rw [cof_ranks, ← card_ranks]
  apply Cardinal.mk_Iic_lt x
  · rw [card_ranks, Cardinal.ord_aleph]
    exact (Ordinal.type_toType _).symm
  · rw [card_ranks]
    exact Cardinal.aleph0_le_aleph _

private def requestSize (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  (Finset.range (2 ^ (k + 2) + 1)).sup f

private def steps (f : ℕ → ℕ) (k : ℕ) : ℕ := requestSize f k + 1

private theorem steps_mono (f : ℕ → ℕ) : Monotone (steps f) := by
  intro i j hij
  unfold steps requestSize
  apply Nat.add_le_add_right
  apply Finset.sup_mono
  apply Finset.range_subset_range.mpr
  exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (by omega)) 1

private def width (f : ℕ → ℕ) (k : ℕ) : ℕ := 2 * steps f k * steps f k + 1

private def offset (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => offset f k + width f k

private theorem offset_strictMono (f : ℕ → ℕ) : StrictMono (offset f) := by
  apply strictMono_nat_of_lt_succ
  intro i
  change offset f i < offset f i + width f i
  unfold width
  omega

private theorem le_offset (f : ℕ → ℕ) (i : ℕ) : i ≤ offset f i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih => exact (Nat.succ_le_succ ih).trans ((offset_strictMono f) (Nat.lt_succ_self i))

private theorem block_exists (f : ℕ → ℕ) (i : ℕ) : ∃ k, i < offset f (k+1) :=
  ⟨i, (Nat.lt_succ_self i).trans_le (le_offset f (i+1))⟩

private def block (f : ℕ → ℕ) (i : ℕ) := Nat.find (block_exists f i)

private theorem block_mono (f : ℕ → ℕ) : Monotone (block f) := by
  intro i j hij
  exact Nat.find_min' (block_exists f i) (hij.trans_lt (Nat.find_spec (block_exists f j)))

private theorem block_eq {f : ℕ → ℕ} {i k : ℕ} (hlo : offset f k ≤ i)
    (hhi : i < offset f (k+1)) : block f i = k := by
  apply le_antisymm (Nat.find_min' (block_exists f i) hhi)
  by_contra! h
  have hbound := Nat.find_spec (block_exists f i)
  exact (hbound.trans_le ((offset_strictMono f).monotone h)).not_ge hlo

private theorem exists_graph (f : ℕ → ℕ) :
    ∃ (V : Type 1) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G ∧
      ∀ k : ℕ, 3 ≤ k → ∀ H : G.Subgraph, H.verts.Finite → H.verts.ncard < f k →
        H.coe.chromaticNumber < (k : ℕ∞) := by
  classical
  let : Nonempty Ranks := Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos _).ne'
  let : Nonempty Stages := Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos _).ne'
  let : NoMaxOrder Ranks := noMax_omega_toType 2
  let : NoMaxOrder Stages := noMax_omega_toType 1
  have hRanks : ℵ₀ < cof Ranks := by
    rw [cof_ranks, ← Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  have hStages : ℵ₀ < cof Stages := cof_stages ▸ Cardinal.aleph0_lt_aleph_one
  have hSizes : Cardinal.lift.{1} #Stages < Cardinal.lift.{1} (cof Ranks) := by
    simpa only [Cardinal.lift_id, cof_ranks, Stages, Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.aleph_lt_aleph.mpr (show (1 : Ordinal.{1}) < 2 by norm_num))
  obtain ⟨E, hGuess⟩ := exists_club_guesser hRanks Stages hStages hSizes
  let L := normalized E
  let R (j : ℕ) (a b : Domain E) : Prop :=
    a < b ∧ Forward (steps f j) (width f j) (fun i => L a (offset f j+i))
      (fun i => L b (offset f j+i))
  have inc : ∀ j a b, R j a b → a < b := fun _ _ _ h => h.1
  apply sufficient_data f R inc
  · intro ρ
    obtain ⟨k, hk⟩ := exists_guessing_color hRanks E hGuess ρ
    let lo (i : ℕ) := i + steps f (block f i)
    have hlo : Monotone lo := fun _ _ h =>
      Nat.add_le_add h (steps_mono f (block_mono f h))
    obtain ⟨a, ha, b, hb, hab, hInter⟩ :=
      realize_intervals hRanks small_initial E {a | ρ a = k} hk (offset f (k+1)) lo hlo
    refine ⟨a, b, k, hab, ha, hb, fun j hj => ⟨hab, ?_⟩⟩
    have hblock (i : ℕ) (hi : i < width f j) : block f (offset f j+i) = j :=
      block_eq (Nat.le_add_right _ _) (by change offset f j + i < offset f j + width f j; omega)
    have hIn (i : ℕ) (hi : i < width f j) : offset f j+i < offset f (k+1) := by
      have h1 : offset f j+i < offset f (j+1) := by
        change offset f j+i < offset f j + width f j
        omega
      exact h1.trans_le ((offset_strictMono f).monotone (Nat.succ_le_succ hj))
    constructor
    · intro i hi
      have hi' : i < width f j := by omega
      have h := (hInter (offset f j+i) (hIn i hi')).1
      simp only [lo, hblock i hi'] at h
      simpa only [L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro i hi
      have hi' : i < width f j := by omega
      have h := (hInter (offset f j+i) (hIn i hi')).2
      simp only [lo, hblock i hi'] at h
      simpa only [L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · intro k v w hw
    refine no_short_odd_closed_walk (levelGraph R inc k) (s := steps f k) (n := width f k)
      (by unfold steps; omega) (by unfold width; omega)
      (fun a i => L a (offset f k+i))
      (fun a _ _ h => (normalized_strictMono E a).monotone (Nat.add_le_add_left h _)) ?_ w ?_
    · intro a b h
      exact h.elim (fun hh => Or.inl hh.2) (fun hh => Or.inr hh.2)
    · change w.length ≤ requestSize f k at hw
      unfold steps
      omega

end LambieHansonAssembly

/-- Lambie-Hanson's quantitative form of the Erdős–Hajnal graph problem.
See https://arxiv.org/abs/1902.08177, Theorem A. -/
theorem OMA.solution : type_of% @Erdos110.erdos_110.variants.lambie_hanson := by
  intro f
  exact LambieHansonAssembly.exists_graph f