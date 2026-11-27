import FormalConjectures.WrittenOnTheWallII.GraphConjecture16

-- Problem: Written on the Wall II - Conjecture 16
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture16.lean:45 (declaration WrittenOnTheWallII.GraphConjecture16.conjecture16)
-- Credit: @divo12 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Contract the closed neighbourhood of a vertex `c` into `c`: the radius drops by at most
one, and an induced two-coloured set through `c` in the contracted graph lifts back, with
any independent set of neighbours of `c` added. Strong induction on the number of vertices
gives a two-coloured set of size `2 r - 2 + |I|` through `c`, and of size `2 r` when `c`
is simplicial (by moving to a neighbour with two non-adjacent neighbours). -/

open SimpleGraph

namespace OMA.WOWII16

universe u

/-- `c` lies in a properly two-coloured vertex set of at least `k` vertices. -/
def Good {β : Type u} (H : SimpleGraph β) (c : β) (k : ℕ) : Prop :=
  ∃ S : Finset β, ∃ col : β → Bool, c ∈ S ∧ k ≤ S.card ∧
    ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → col x ≠ col y

/-- Every vertex has eccentricity at least `r`. -/
def Radial {β : Type u} (H : SimpleGraph β) (r : ℕ) : Prop := ∀ v, ∃ w, r ≤ H.dist v w

section
variable {β : Type u} {H : SimpleGraph β}

lemma Good.mono {c : β} {k m : ℕ} (h : Good H c k) (hm : m ≤ k) : Good H c m := by
  obtain ⟨S, col, hc, hk, hS⟩ := h
  exact ⟨S, col, hc, hm.trans hk, hS⟩

lemma descend (hc : H.Connected) (a x : β) (hx : x ≠ a) :
    ∃ y, H.Adj x y ∧ H.dist a y + 1 = H.dist a x := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a x
  have hpos : 0 < p.length := by
    rw [hp]; exact Nat.pos_of_ne_zero fun h => hx ((hc.dist_eq_zero_iff.mp h).symm)
  let i := p.length - 1
  have hi : i + 1 = p.length := by dsimp [i]; omega
  have he := p.adj_getVert_succ (show i < p.length by omega)
  rw [hi, p.getVert_length] at he
  refine ⟨_,he.symm,?_⟩
  have hv := length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  rw [Walk.take_length, Nat.min_eq_left (by omega)] at hv
  simp [← hv,hi,hp]

lemma exists_dist_two (hc : H.Connected) (c y : β) (h : 2 ≤ H.dist c y) :
    ∃ z, H.dist c z = 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist c y
  refine ⟨p.getVert 2, ?_⟩
  simpa [Walk.take_length, Nat.min_eq_left (show 2 ≤ p.length by omega)] using
    (length_eq_dist_of_subwalk hp (p.isSubwalk_take 2)).symm

lemma mid (hc : H.Connected) (c y : β) (hy : H.dist c y = 2) :
    ∃ k, H.Adj c k ∧ H.Adj k y := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist c y
  refine ⟨p.getVert 1, ?_, ?_⟩
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · have := p.adj_getVert_succ (i := 1) (by omega)
    rwa [show 1 + 1 = p.length by omega, p.getVert_length] at this

lemma pair_indep [DecidableEq β] {a b : β} (h : ¬ H.Adj a b) :
    ∀ i ∈ ({a, b} : Finset β), ∀ j ∈ ({a, b} : Finset β), ¬ H.Adj i j := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro i (rfl | rfl) j (rfl | rfl)
  · exact H.irrefl
  · exact h
  · exact fun h' => h h'.symm
  · exact H.irrefl

/-- The vertices that survive contracting the closed neighbourhood of `c` into `c`. -/
abbrev Kp (H : SimpleGraph β) (c : β) : Type u := {x : β // x = c ∨ ¬ H.Adj c x}

/-- Contract the closed neighbourhood of `c`: `c` becomes adjacent to the second layer. -/
def con (H : SimpleGraph β) (c : β) : SimpleGraph (Kp H c) :=
  SimpleGraph.fromRel fun x y => H.Adj x.1 y.1 ∨ (x.1 = c ∧ H.dist c y.1 = 2)

/-- The contracted vertex. -/
def root (H : SimpleGraph β) (c : β) : Kp H c := ⟨c, Or.inl rfl⟩

open Classical in
/-- Layer index in the contracted graph, with the contracted ball on layer one. -/
noncomputable def lev (H : SimpleGraph β) (c : β) (z : Kp H c) : ℕ :=
  if z.1 = c then 1 else H.dist c z.1

lemma kp_ne_of_adj {c : β} (z w : Kp H c) (h : H.Adj z.1 w.1) : z.1 ≠ c := by
  intro e
  rcases w.2 with e' | e'
  · rw [e, e'] at h; exact H.irrefl h
  · rw [e] at h; exact e' h

lemma lev_of_eq {c : β} (z : Kp H c) (h : z.1 = c) : lev H c z = 1 := by
  simp [lev, h]

lemma lev_of_ne {c : β} (z : Kp H c) (h : z.1 ≠ c) : lev H c z = H.dist c z.1 := by
  simp [lev, h]

lemma lev_bounds {c : β} (z : Kp H c) :
    H.dist c z.1 ≤ lev H c z ∧ lev H c z ≤ H.dist c z.1 + 1 := by
  by_cases h : z.1 = c
  · rw [lev_of_eq z h, h]; simp
  · rw [lev_of_ne z h]; omega

lemma con_connected (hc : H.Connected) (c : β) : (con H c).Connected := by
  have key : ∀ n, ∀ x : Kp H c, H.dist c x.1 = n → (con H c).Reachable (root H c) x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro x hx
    by_cases hxc : x.1 = c
    · have : x = root H c := Subtype.ext hxc
      subst this; rfl
    · obtain ⟨m, hxm, hm⟩ := descend hc c x.1 hxc
      have hx2 : 2 ≤ n := by
        have := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm hxc) (x.2.resolve_left hxc)
        omega
      by_cases hn2 : n = 2
      · apply Adj.reachable
        rw [con, fromRel_adj]
        refine ⟨fun h => hxc (congrArg Subtype.val h).symm, Or.inl (Or.inr ⟨rfl, ?_⟩)⟩
        omega
      · have hmc : m ≠ c := by rintro rfl; simp at hm; omega
        have hmk : m = c ∨ ¬ H.Adj c m := Or.inr fun h => by
          rw [dist_eq_one_iff_adj.mpr h] at hm; omega
        refine (ih (H.dist c m) (by omega) ⟨m, hmk⟩ rfl).trans (Adj.reachable ?_)
        rw [con, fromRel_adj]
        exact ⟨fun h => hxm.ne (congrArg Subtype.val h).symm, Or.inr (Or.inl hxm)⟩
  have : Nonempty (Kp H c) := ⟨root H c⟩
  exact ⟨fun x y => (key _ x rfl).symm.trans (key _ y rfl)⟩

lemma walk_bound (hc : H.Connected) (c : β) {u v : Kp H c} (p : (con H c).Walk u v) :
    H.dist u.1 v.1 ≤ p.length ∨ lev H c u + lev H c v ≤ p.length + 2 := by
  induction p with
  | nil => left; simp
  | @cons u w v hadj p ih =>
    simp only [Walk.length_cons]
    rw [con, fromRel_adj] at hadj
    obtain ⟨-, h⟩ := hadj
    have hv : (lev H c v = 1 ∧ H.dist c v.1 = 0) ∨ lev H c v = H.dist c v.1 := by
      by_cases hvc : v.1 = c
      · left; rw [lev_of_eq v hvc, hvc]; simp
      · right; exact lev_of_ne v hvc
    have tri := hc.dist_triangle (u := u.1) (v := w.1) (w := v.1)
    have tri2 := hc.dist_triangle (u := c) (v := w.1) (w := v.1)
    rcases h with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩)
    · have huc := kp_ne_of_adj u w h
      have hwc := kp_ne_of_adj w u h.symm
      have hd := dist_eq_one_iff_adj.mpr h
      have hd' := (h.diff_dist_adj (u := c))
      rw [lev_of_ne u huc, lev_of_ne w hwc] at *
      omega
    · have hwc : w.1 ≠ c := by intro e; rw [e] at h2; simp at h2
      rw [lev_of_eq u h1, lev_of_ne w hwc] at *
      right; omega
    · have huc := kp_ne_of_adj u w h.symm
      have hwc := kp_ne_of_adj w u h
      have hd := dist_eq_one_iff_adj.mpr h.symm
      have hd' := (h.symm.diff_dist_adj (u := c))
      rw [lev_of_ne u huc, lev_of_ne w hwc] at *
      omega
    · rw [lev_of_eq w h1] at ih
      rw [h1] at ih
      have huc : u.1 ≠ c := by intro e; rw [e] at h2; simp at h2
      rw [lev_of_ne u huc]
      right
      rcases ih with ih | ih <;> omega

lemma con_radial (hc : H.Connected) (c : β) (r : ℕ) (hr : Radial H r) :
    Radial (con H c) (r - 1) := by
  have hcc := con_connected hc c
  intro x
  by_contra hx
  push Not at hx
  have hb : ∀ y, H.dist x.1 y.1 ≤ r - 2 ∨ lev H c x + lev H c y ≤ r := by
    intro y
    obtain ⟨p, hp⟩ := hcc.exists_walk_length_eq_dist x y
    have := walk_bound hc c p
    have := hx y
    omega
  have hr2 : 2 ≤ r := by have := hx x; omega
  by_cases hxc : x.1 = c
  · obtain ⟨w, hw⟩ := hr c
    by_cases hwk : H.Adj c w
    · rw [dist_eq_one_iff_adj.mpr hwk] at hw; omega
    · have h := hb ⟨w, Or.inr hwk⟩
      have bw := lev_bounds (⟨w, Or.inr hwk⟩ : Kp H c)
      rw [lev_of_eq x hxc, hxc] at h
      change H.dist c w ≤ r - 2 ∨ 1 + lev H c ⟨w, Or.inr hwk⟩ ≤ r at h
      change H.dist c w ≤ _ ∧ _ at bw
      omega
  · obtain ⟨m, hxm, hm⟩ := descend hc c x.1 hxc
    obtain ⟨w, hw⟩ := hr m
    have hroot := hb (root H c)
    rw [lev_of_eq (root H c) rfl, lev_of_ne x hxc] at hroot
    simp only [root] at hroot
    rw [SimpleGraph.dist_comm] at hroot
    have hmx := dist_eq_one_iff_adj.mpr hxm.symm
    have t1 := hc.dist_triangle (u := m) (v := x.1) (w := w)
    have t2 := hc.dist_triangle (u := m) (v := c) (w := w)
    rw [SimpleGraph.dist_comm (u := m) (v := c)] at t2
    by_cases hwk : w = c ∨ ¬ H.Adj c w
    · have h := hb ⟨w, hwk⟩
      have bw := lev_bounds (⟨w, hwk⟩ : Kp H c)
      rw [lev_of_ne x hxc] at h
      change H.dist x.1 w ≤ r - 2 ∨ H.dist c x.1 + lev H c ⟨w, hwk⟩ ≤ r at h
      change H.dist c w ≤ _ ∧ _ at bw
      omega
    · push Not at hwk
      have := dist_eq_one_iff_adj.mpr hwk.2
      omega

lemma lift [DecidableEq β] (hc : H.Connected) (c : β) (k : ℕ) (I : Finset β)
    (hI : ∀ i ∈ I, H.Adj c i) (hind : ∀ i ∈ I, ∀ j ∈ I, ¬ H.Adj i j)
    (h : Good (con H c) (root H c) k) : Good H c (k + I.card) := by
  obtain ⟨S, col, hcS, hk, hS⟩ := h
  classical
  let κ := col (root H c)
  let col' : β → Bool := fun x => if x = c then !κ else if x ∈ I then κ else
    if hx : x = c ∨ ¬ H.Adj c x then col ⟨x, hx⟩ else false
  have hIK : ∀ i ∈ I, ∀ z : Kp H c, z.1 ≠ i := by
    intro i hi z e
    have := hI i hi
    rw [← e] at this
    rcases z.2 with e' | e'
    · rw [e'] at this; exact H.irrefl this
    · exact e' this
  have colI : ∀ i ∈ I, col' i = κ := by
    intro i hi
    simp [col', (hI i hi).ne', hi]
  have colc : col' c = !κ := by simp [col']
  have colz : ∀ z : Kp H c, z.1 ≠ c → col' z.1 = col z := by
    intro z hz
    have hzI : z.1 ∉ I := fun h => hIK _ h z rfl
    simp only [col', if_neg hz, if_neg hzI, dif_pos z.2]
  refine ⟨S.map (Function.Embedding.subtype _) ∪ I, col', ?_, ?_, ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨root H c, hcS, rfl⟩)
  · rw [Finset.card_union_of_disjoint, Finset.card_map]
    · omega
    · rw [Finset.disjoint_left]
      intro x hx hxI
      obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hx
      exact hIK _ hxI z rfl
  · have side : ∀ i ∈ I, ∀ z ∈ S, H.Adj i z.1 → col' i ≠ col' z.1 := by
      intro i hi z hz hiz
      by_cases hzc : z.1 = c
      · rw [colI i hi, hzc, colc]; simp
      · rw [colI i hi, colz z hzc]
        have hzk := z.2.resolve_left hzc
        have h2 : H.dist c z.1 = 2 := by
          have t := hc.dist_triangle (u := c) (v := i) (w := z.1)
          rw [dist_eq_one_iff_adj.mpr (hI i hi), dist_eq_one_iff_adj.mpr hiz] at t
          have := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm hzc) hzk
          omega
        have hadj : (con H c).Adj (root H c) z := by
          rw [con, fromRel_adj]
          exact ⟨fun h => hzc (congrArg Subtype.val h).symm, Or.inl (Or.inr ⟨rfl, h2⟩)⟩
        exact hS _ hcS _ hz hadj
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp hy
      simp only [Function.Embedding.coe_subtype] at hxy ⊢
      have hzc := kp_ne_of_adj z z' hxy
      have hzc' := kp_ne_of_adj z' z hxy.symm
      rw [colz z hzc, colz z' hzc']
      apply hS _ hz _ hz'
      rw [con, fromRel_adj]
      exact ⟨fun h => hxy.ne (congrArg Subtype.val h), Or.inl (Or.inl hxy)⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      exact (side y hy z hz hxy.symm).symm
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
      exact side x hx z hz hxy
    · exact absurd hxy (hind x hx y hy)

lemma swap [DecidableEq β] (c k : β) (hk : H.Adj c k)
    (hcl : ∀ a b, H.Adj c a → H.Adj c b → a ≠ b → H.Adj a b) (m : ℕ)
    (h : Good H k m) : Good H c m := by
  classical
  obtain ⟨S, col, hkS, hm, hS⟩ := h
  by_cases hcS : c ∈ S
  · exact ⟨S, col, hcS, hm, hS⟩
  let T := S.filter (fun x => ¬ (H.Adj c x ∧ x ≠ k))
  let col' : β → Bool := fun x => if x = c then !col k else col x
  refine ⟨insert c T, col', Finset.mem_insert_self _ _, ?_, ?_⟩
  · have h1 : (S.filter (fun x => H.Adj c x ∧ x ≠ k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      simp only [Finset.mem_filter] at ha hb
      have e1 := hS _ ha.1 _ hb.1 (hcl a b ha.2.1 hb.2.1 hab)
      have e2 := hS _ ha.1 _ hkS (hcl a k ha.2.1 hk ha.2.2)
      have e3 := hS _ hb.1 _ hkS (hcl b k hb.2.1 hk hb.2.2)
      revert e1 e2 e3
      cases col a <;> cases col b <;> cases col k <;> simp
    have := S.card_filter_add_card_filter_not (fun x => H.Adj c x ∧ x ≠ k)
    rw [Finset.card_insert_of_notMem (by simp [T, hcS])]
    have hT' : T.card = (S.filter (fun x => ¬ (H.Adj c x ∧ x ≠ k))).card := rfl
    omega
  · have hT : ∀ x ∈ T, x ≠ c := fun x hx e => hcS (e ▸ (Finset.mem_filter.mp hx).1)
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
    · exact absurd hxy H.irrefl
    · have hyk : y = k := by
        by_contra h'
        exact (Finset.mem_filter.mp hy).2 ⟨hxy, h'⟩
      subst hyk
      simp [col', hT _ hy]
    · have hxk : x = k := by
        by_contra h'
        exact (Finset.mem_filter.mp hx).2 ⟨hxy.symm, h'⟩
      subst hxk
      simp [col', hT _ hx]
    · simp only [col', hT _ hx, hT _ hy, if_false]
      exact hS _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 hxy

lemma star [DecidableEq β] (c : β) (I : Finset β) (hI : ∀ i ∈ I, H.Adj c i)
    (hind : ∀ i ∈ I, ∀ j ∈ I, ¬ H.Adj i j) : Good H c (I.card + 1) := by
  have hcI : c ∉ I := fun h => H.irrefl (hI c h)
  refine ⟨insert c I, fun x => decide (x = c), Finset.mem_insert_self _ _,
    by rw [Finset.card_insert_of_notMem hcI], ?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hx | hx <;> rcases Finset.mem_insert.mp hy with hy | hy
  · rw [hx, hy] at hxy; exact absurd hxy H.irrefl
  · rw [hx]; simp [(hI y hy).ne']
  · rw [hy]; simp [(hI x hx).ne']
  · exact absurd hxy (hind x hx y hy)

end

theorem main (n : ℕ) : ∀ (β : Type u) [Fintype β] [DecidableEq β], Fintype.card β = n →
    ∀ H : SimpleGraph β, H.Connected → ∀ r, Radial H r → ∀ c, Good H c (2 * r) ∧
      ∀ I : Finset β, (∀ i ∈ I, H.Adj c i) → (∀ i ∈ I, ∀ j ∈ I, ¬ H.Adj i j) →
        2 ≤ I.card → Good H c (2 * r + I.card - 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro β _ _ hn H hc r hr
  classical
  have A2 : ∀ c (I : Finset β), (∀ i ∈ I, H.Adj c i) → (∀ i ∈ I, ∀ j ∈ I, ¬ H.Adj i j) →
      2 ≤ I.card → Good H c (2 * r + I.card - 2) := by
    intro c I hI hind h2
    by_cases hD : ∃ y, H.dist c y = 2
    · obtain ⟨i, hi⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
      have hlt : Fintype.card (Kp H c) < n := by
        rw [← hn]
        apply Fintype.card_subtype_lt (x := i)
        push Not
        exact ⟨(hI i hi).ne', hI i hi⟩
      obtain ⟨hB, -⟩ := ih _ hlt (Kp H c) rfl (con H c) (con_connected hc c) (r - 1)
        (con_radial hc c r hr) (root H c)
      exact (lift hc c _ I hI hind hB).mono (by omega)
    · push Not at hD
      have hr1 : r ≤ 1 := by
        obtain ⟨w, hw⟩ := hr c
        by_contra h
        obtain ⟨z, hz⟩ := exists_dist_two hc c w (by omega)
        exact hD z hz
      exact (star c I hI hind).mono (by omega)
  refine fun c => ⟨?_, A2 c⟩
  by_cases hpair : ∃ a b, H.Adj c a ∧ H.Adj c b ∧ a ≠ b ∧ ¬ H.Adj a b
  · obtain ⟨a, b, ha, hb, hab, hnab⟩ := hpair
    have h := A2 c {a, b} (by simp [ha, hb]) (pair_indep hnab)
      (by simp [Finset.card_pair hab])
    rw [Finset.card_pair hab] at h
    exact h.mono (by omega)
  · push Not at hpair
    by_cases hD : ∃ y, H.dist c y = 2
    · obtain ⟨y, hy⟩ := hD
      obtain ⟨k, hck, hky⟩ := mid hc c y hy
      have hcy : c ≠ y := by rintro rfl; simp at hy
      have hnadj : ¬ H.Adj c y := by
        intro h; rw [dist_eq_one_iff_adj.mpr h] at hy; omega
      have h := A2 k {c, y} (by simp [hck.symm, hky]) (pair_indep hnadj)
        (by simp [Finset.card_pair hcy])
      rw [Finset.card_pair hcy] at h
      exact swap c k hck hpair _ (h.mono (by omega))
    · push Not at hD
      obtain ⟨w, hw⟩ := hr c
      have hw2 : H.dist c w ≤ 1 := by
        by_contra h
        obtain ⟨z, hz⟩ := exists_dist_two hc c w (by omega)
        exact hD z hz
      rcases Nat.lt_or_ge (H.dist c w) 1 with h0 | h1
      · exact (star c ∅ (by simp) (by simp)).mono (by omega)
      · have hadj : H.Adj c w := dist_eq_one_iff_adj.mp (by omega)
        exact (star c {w} (by simp [hadj]) (by simp)).mono (by simp; omega)

end OMA.WOWII16

open OMA.WOWII16 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture16.conjecture16 := by
  intro α _ _ _ G hc
  classical
  let vals := Finset.univ.image (fun v => indepNeighborsCard G v)
  have hn : vals.Nonempty := by simp [vals]
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (vals.max'_mem hn)
  obtain ⟨N, hN⟩ := (G.induce (G.neighborSet x)).exists_isNIndepSet_indepNum
  let M : Finset α := N.map (Function.Embedding.subtype _)
  have size : M.card = G.indepNeighborsCard x := by
    simpa [M, indepNeighborsCard] using hN.card_eq
  have adj (v) (hv : v ∈ M) : G.Adj x v := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hv
    exact y.prop
  have independent : ∀ i ∈ M, ∀ j ∈ M, ¬ G.Adj i j := by
    intro v hv w hw he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
    exact hN.isIndepSet hu hz (fun h => he.ne (congrArg Subtype.val h)) he
  have hrad : Radial G G.radius.toNat := by
    intro v
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
    refine ⟨w, ?_⟩
    have : G.radius ≤ G.edist v w := hw ▸ G.radius_le_eccent
    exact ENat.toNat_le_toNat this (edist_ne_top_iff_reachable.mpr (hc v w))
  obtain ⟨hB, hA⟩ := main _ α rfl G hc _ hrad x
  have key : ∃ S : Finset α, ∃ col : α → Bool,
      2 * G.radius.toNat + M.card ≤ S.card + 2 ∧
        ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → col x ≠ col y := by
    by_cases h2 : 2 ≤ M.card
    · obtain ⟨S, col, -, hk, hS⟩ := hA M adj independent h2
      exact ⟨S, col, by omega, hS⟩
    · obtain ⟨S, col, -, hk, hS⟩ := hB
      exact ⟨S, col, by omega, hS⟩
  obtain ⟨S, col, hk, hS⟩ := key
  have bip : (G.induce (↑S : Set α)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring _ _).mpr
    refine ⟨fun v => if col v then 1 else 0, ?_⟩
    intro u hu v hv huv
    have := hS u hu v hv huv
    cases hcu : col u <;> cases hcv : col v <;> simp_all
  have sz : S.card ≤ G.largestInducedBipartiteSubgraphSize := by
    apply le_csSup
    · exact ⟨Fintype.card α, fun _ ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
    · exact ⟨_, bip, rfl⟩
  rw [size, hx] at hk
  unfold b
  have h1 : (2 * G.radius.toNat + vals.max' hn : ℝ) ≤ S.card + 2 := by exact_mod_cast hk
  have h2 : (S.card : ℝ) ≤ G.largestInducedBipartiteSubgraphSize := by exact_mod_cast sz
  linarith
