import FormalConjectures.Paper.BurningNumberConjecture

-- Problem: Norin–Turcotte (2024): the burning number conjecture holds asymptotically.
-- Upstream: formal-conjectures FormalConjectures/Paper/BurningNumberConjecture.lean:98 (declaration BurningNumberConjecture.burning_number_conjecture.variants.norin_turcotte)
-- Credit: @fecheteluca (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace NTB

open Finset

/-! ### Part A: tree metrics, and the tree metric of a breadth-first tree -/

structure IsTM {V : Type} (d : V → V → ℕ) : Prop where
  eq0 : ∀ x y, d x y = 0 ↔ x = y
  symm : ∀ x y, d x y = d y x
  geo : ∀ x y s, s ≤ d x y → ∃ p, d x p = s ∧ d p y + s = d x y
  four : ∀ x y z w, d x y + d z w ≤ d x z + d y w ∨ d x y + d z w ≤ d x w + d y z
  even3 : ∀ x y z, ∃ k, d x y + d y z + d x z = 2 * k

structure IsPD {V : Type} (par : V → V) (dep : V → ℕ) : Prop where
  hd : ∀ v, dep (par v) = dep v - 1
  h0 : ∀ u v, dep u = 0 → dep v = 0 → u = v

section Model

variable {V : Type}

def anc (par : V → V) (dep : V → ℕ) (v : V) (j : ℕ) : V := par^[dep v - j] v

noncomputable def gp (par : V → V) (dep : V → ℕ) (x y : V) : ℕ :=
  @Nat.findGreatest (fun j => anc par dep x j = anc par dep y j)
    (fun _ => Classical.propDecidable _) (min (dep x) (dep y))

noncomputable def dT (par : V → V) (dep : V → ℕ) (x y : V) : ℕ :=
  dep x + dep y - 2 * gp par dep x y

variable {par : V → V} {dep : V → ℕ}

lemma dep_iter (h : IsPD par dep) (i : ℕ) (v : V) : dep (par^[i] v) = dep v - i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', h.hd, ih]; omega

lemma anc_low (h : IsPD par dep) (x : V) {j j' : ℕ} (hj : j ≤ dep x) (hjj : j' ≤ j) :
    anc par dep (anc par dep x j) j' = anc par dep x j' := by
  unfold anc
  rw [dep_iter h, ← Function.iterate_add_apply]
  congr 1
  omega

lemma anc_zero (h : IsPD par dep) (x y : V) : anc par dep x 0 = anc par dep y 0 := by
  apply h.h0
  · unfold anc; rw [dep_iter h]; omega
  · unfold anc; rw [dep_iter h]; omega

lemma gp_le_left (x y : V) : gp par dep x y ≤ dep x := by
  unfold gp
  classical
  exact le_trans (Nat.findGreatest_le _) (min_le_left _ _)

lemma gp_le_right (x y : V) : gp par dep x y ≤ dep y := by
  unfold gp
  classical
  exact le_trans (Nat.findGreatest_le _) (min_le_right _ _)

lemma gp_spec (h : IsPD par dep) (x y : V) :
    anc par dep x (gp par dep x y) = anc par dep y (gp par dep x y) := by
  unfold gp
  classical
  exact Nat.findGreatest_spec (P := fun j => anc par dep x j = anc par dep y j)
    (Nat.zero_le _) (anc_zero h x y)

lemma gp_agree (h : IsPD par dep) (x y : V) {j : ℕ} (hj : j ≤ gp par dep x y) :
    anc par dep x j = anc par dep y j := by
  rw [← anc_low h x (gp_le_left x y) hj, ← anc_low h y (gp_le_right x y) hj, gp_spec h]

lemma le_gp (x y : V) {j : ℕ} (hx : j ≤ dep x) (hy : j ≤ dep y)
    (hj : anc par dep x j = anc par dep y j) : j ≤ gp par dep x y := by
  unfold gp
  classical
  exact Nat.le_findGreatest (P := fun j => anc par dep x j = anc par dep y j) (le_min hx hy) hj

lemma gp_comm (h : IsPD par dep) (x y : V) : gp par dep x y = gp par dep y x := by
  apply le_antisymm
  · exact le_gp y x (gp_le_right x y) (gp_le_left x y) (gp_spec h x y).symm
  · exact le_gp x y (gp_le_right y x) (gp_le_left y x) (gp_spec h y x).symm

lemma gp_self (x : V) : gp par dep x x = dep x :=
  le_antisymm (gp_le_left x x) (le_gp x x le_rfl le_rfl rfl)

lemma gp_iso (h : IsPD par dep) (x y z : V) :
    gp par dep x y ≤ gp par dep x z ∨ gp par dep y z ≤ gp par dep x z := by
  rcases le_total (gp par dep x y) (gp par dep y z) with hle | hle
  · left
    exact le_gp x z (gp_le_left x y) (le_trans hle (gp_le_right y z))
      ((gp_agree h x y le_rfl).trans (gp_agree h y z hle))
  · right
    exact le_gp x z (le_trans hle (gp_le_left x y)) (gp_le_right y z)
      ((gp_agree h x y hle).trans (gp_agree h y z le_rfl))

lemma dT_add (x y : V) : dT par dep x y + 2 * gp par dep x y = dep x + dep y := by
  have h1 := gp_le_left (par := par) (dep := dep) x y
  have h2 := gp_le_right (par := par) (dep := dep) x y
  unfold dT; omega

lemma dT_symm (h : IsPD par dep) (x y : V) : dT par dep x y = dT par dep y x := by
  unfold dT; rw [gp_comm h x y]; omega

lemma dT_eq0 (h : IsPD par dep) (x y : V) : dT par dep x y = 0 ↔ x = y := by
  constructor
  · intro hz
    have h1 := gp_le_left (par := par) (dep := dep) x y
    have h2 := gp_le_right (par := par) (dep := dep) x y
    have h3 := dT_add (par := par) (dep := dep) x y
    have e1 : dep x - gp par dep x y = 0 := by omega
    have e2 : dep y - gp par dep x y = 0 := by omega
    have h4 := gp_spec h x y
    unfold anc at h4
    rw [e1, e2] at h4
    simpa using h4
  · rintro rfl
    have h3 := dT_add (par := par) (dep := dep) x x
    rw [gp_self] at h3
    omega

lemma four_aux (a b c e f k : ℕ)
    (h1 : a ≤ c ∨ k ≤ c) (h2 : a ≤ k ∨ c ≤ k) (h3 : c ≤ a ∨ k ≤ a)
    (h4 : a ≤ f ∨ e ≤ f) (h5 : a ≤ e ∨ f ≤ e) (h6 : f ≤ a ∨ e ≤ a)
    (h7 : c ≤ f ∨ b ≤ f) (h8 : c ≤ b ∨ f ≤ b) (h9 : f ≤ c ∨ b ≤ c)
    (h10 : k ≤ e ∨ b ≤ e) (h11 : k ≤ b ∨ e ≤ b) (h12 : e ≤ k ∨ b ≤ k) :
    c + e ≤ a + b ∨ f + k ≤ a + b := by
  omega

lemma dT_four (h : IsPD par dep) (x y z w : V) :
    dT par dep x y + dT par dep z w ≤ dT par dep x z + dT par dep y w ∨
    dT par dep x y + dT par dep z w ≤ dT par dep x w + dT par dep y z := by
  have h1 := gp_iso h x y z
  have h2 := gp_iso h y x z
  have h3 := gp_iso h x z y
  have h4 := gp_iso h x y w
  have h5 := gp_iso h y x w
  have h6 := gp_iso h x w y
  have h7 := gp_iso h x z w
  have h8 := gp_iso h z x w
  have h9 := gp_iso h x w z
  have h10 := gp_iso h y z w
  have h11 := gp_iso h z y w
  have h12 := gp_iso h y w z
  rw [gp_comm h y x] at h2 h5
  rw [gp_comm h z y] at h3 h11
  rw [gp_comm h w y] at h6
  rw [gp_comm h z x] at h8
  rw [gp_comm h w z] at h9 h12
  have key := four_aux _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have a1 := dT_add (par := par) (dep := dep) x y
  have a2 := dT_add (par := par) (dep := dep) z w
  have a3 := dT_add (par := par) (dep := dep) x z
  have a4 := dT_add (par := par) (dep := dep) y w
  have a5 := dT_add (par := par) (dep := dep) x w
  have a6 := dT_add (par := par) (dep := dep) y z
  omega

lemma dT_geo_up (h : IsPD par dep) (x y : V) (s : ℕ) (hs : s + gp par dep x y ≤ dep x) :
    dT par dep x (par^[s] x) = s ∧ dT par dep (par^[s] x) y + s = dT par dep x y := by
  have hdp : dep (par^[s] x) = dep x - s := dep_iter h s x
  have hpe : par^[s] x = anc par dep x (dep x - s) := by
    unfold anc; congr 1; omega
  have hanc : ∀ j, j ≤ dep (par^[s] x) → anc par dep (par^[s] x) j = anc par dep x j := by
    intro j hj
    rw [hpe]
    exact anc_low h x (by omega) (by omega)
  have hpp : anc par dep (par^[s] x) (dep (par^[s] x)) = par^[s] x := by
    unfold anc; simp
  have hgxp : gp par dep x (par^[s] x) = dep (par^[s] x) :=
    le_antisymm (gp_le_right _ _)
      (le_gp _ _ (by omega) le_rfl (hanc _ le_rfl).symm)
  have hgpy : gp par dep (par^[s] x) y = gp par dep x y := by
    apply le_antisymm
    · have hl := gp_le_left (par := par) (dep := dep) (par^[s] x) y
      exact le_gp x y (by omega) (gp_le_right _ y)
        ((hanc _ hl).symm.trans (gp_spec h _ y))
    · exact le_gp _ y (by omega) (gp_le_right x y)
        ((hanc _ (by omega)).trans (gp_spec h x y))
  have a1 := dT_add (par := par) (dep := dep) x (par^[s] x)
  have a2 := dT_add (par := par) (dep := dep) (par^[s] x) y
  have a3 := dT_add (par := par) (dep := dep) x y
  have l1 := gp_le_left (par := par) (dep := dep) x y
  have l2 := gp_le_right (par := par) (dep := dep) x y
  rw [hgxp] at a1
  rw [hgpy] at a2
  constructor <;> omega

lemma dT_geo (h : IsPD par dep) (x y : V) (s : ℕ) (hs : s ≤ dT par dep x y) :
    ∃ p, dT par dep x p = s ∧ dT par dep p y + s = dT par dep x y := by
  have h1 := gp_le_left (par := par) (dep := dep) x y
  have h2 := gp_le_right (par := par) (dep := dep) x y
  have h3 := dT_add (par := par) (dep := dep) x y
  by_cases hc : s + gp par dep x y ≤ dep x
  · exact ⟨_, dT_geo_up h x y s hc⟩
  · have hc' : (dT par dep x y - s) + gp par dep y x ≤ dep y := by
      rw [gp_comm h y x]; omega
    obtain ⟨e1, e2⟩ := dT_geo_up h y x _ hc'
    have s1 := dT_symm h x (par^[dT par dep x y - s] y)
    have s2 := dT_symm h y x
    have s3 := dT_symm h (par^[dT par dep x y - s] y) y
    refine ⟨par^[dT par dep x y - s] y, ?_, ?_⟩ <;> omega

lemma isTM_dT (h : IsPD par dep) : IsTM (dT par dep) where
  eq0 := dT_eq0 h
  symm := dT_symm h
  geo := dT_geo h
  four := dT_four h
  even3 := by
    intro x y z
    have a1 := dT_add (par := par) (dep := dep) x y
    have a2 := dT_add (par := par) (dep := dep) y z
    have a3 := dT_add (par := par) (dep := dep) x z
    have l1 := gp_le_left (par := par) (dep := dep) x y
    have l2 := gp_le_right (par := par) (dep := dep) y z
    have l3 := gp_le_left (par := par) (dep := dep) x z
    have l4 := gp_le_right (par := par) (dep := dep) x y
    have l5 := gp_le_left (par := par) (dep := dep) y z
    have l6 := gp_le_right (par := par) (dep := dep) x z
    refine ⟨dep x + dep y + dep z - (gp par dep x y + gp par dep y z + gp par dep x z), ?_⟩
    omega

end Model

lemma exists_par {V : Type} (G : SimpleGraph V) (hG : G.Connected) (ρ v : V) :
    ∃ u, G.dist ρ u = G.dist ρ v - 1 ∧ G.dist u v ≤ 1 := by
  by_cases hv : G.dist ρ v = 0
  · exact ⟨v, by omega, by simp⟩
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist ρ v
    have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
    have e : p.length - 1 + 1 = p.length := by omega
    rw [e, p.getVert_length] at hadj
    have h1 : G.dist ρ (p.getVert (p.length - 1)) ≤ p.length - 1 := by
      have h := SimpleGraph.dist_le (p.take (p.length - 1))
      rw [SimpleGraph.Walk.take_length] at h
      exact le_trans h (min_le_left _ _)
    have h2 : G.dist (p.getVert (p.length - 1)) v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have h3 := hG.dist_triangle (u := ρ) (v := p.getVert (p.length - 1)) (w := v)
    exact ⟨p.getVert (p.length - 1), by omega, by omega⟩

theorem exists_tm {V : Type} (G : SimpleGraph V) (hG : G.Connected) :
    ∃ d : V → V → ℕ, IsTM d ∧ ∀ x y, G.dist x y ≤ d x y := by
  obtain ⟨ρ⟩ := hG.nonempty
  choose par hpar using exists_par G hG ρ
  have hPD : IsPD par (G.dist ρ) := ⟨fun v => (hpar v).1, fun u v hu hv => by
    rw [hG.dist_eq_zero_iff] at hu hv
    rw [← hu, ← hv]⟩
  refine ⟨dT par (G.dist ρ), isTM_dT hPD, ?_⟩
  have hit : ∀ (i : ℕ) (v : V), G.dist (par^[i] v) v ≤ i := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [Function.iterate_succ_apply']
      have t1 := hG.dist_triangle (u := par (par^[i] v)) (v := par^[i] v) (w := v)
      have t2 := (hpar (par^[i] v)).2
      have t3 := ih v
      omega
  intro x y
  have hs := gp_spec hPD x y
  unfold anc at hs
  have h1 := hit (G.dist ρ x - gp par (G.dist ρ) x y) x
  have h2 := hit (G.dist ρ y - gp par (G.dist ρ) x y) y
  rw [← hs] at h2
  rw [SimpleGraph.dist_comm] at h1
  have h3 := hG.dist_triangle (u := x) (v := par^[G.dist ρ x - gp par (G.dist ρ) x y] x) (w := y)
  have a1 := dT_add (par := par) (dep := G.dist ρ) x y
  have l1 := gp_le_left (par := par) (dep := G.dist ρ) x y
  have l2 := gp_le_right (par := par) (dep := G.dist ρ) x y
  omega

/-! ### Part B: convex sets of a tree metric, and their decompositions -/

section Pieces

variable {V : Type} [DecidableEq V] {d : V → V → ℕ}

lemma IsTM.self (h : IsTM d) (x : V) : d x x = 0 := (h.eq0 x x).mpr rfl

lemma IsTM.tri (h : IsTM d) (x y z : V) : d x z ≤ d x y + d y z := by
  have h1 := h.four x z y y
  have h2 := h.self y
  have h3 := h.symm z y
  omega

lemma IsTM.geo' (h : IsTM d) (x y : V) :
    ∃ f : ℕ → V, ∀ s, s ≤ d x y → d x (f s) = s ∧ d (f s) y + s = d x y := by
  have hex : ∀ s, ∃ p, s ≤ d x y → (d x p = s ∧ d p y + s = d x y) := by
    intro s
    by_cases hs : s ≤ d x y
    · obtain ⟨p, hp⟩ := h.geo x y s hs
      exact ⟨p, fun _ => hp⟩
    · exact ⟨x, fun h' => absurd h' hs⟩
  choose f hf using hex
  exact ⟨f, hf⟩

lemma IsTM.geo_unique (h : IsTM d) {x y p q : V} (hp1 : d x p = d x q) (hp2 : d p y = d q y)
    (hp : d x p + d p y = d x y) : p = q := by
  have h1 := h.four p q x y
  have h2 := h.symm p x
  have h3 := h.symm q x
  rw [← h.eq0]
  omega

lemma IsTM.gromov (h : IsTM d) (a b c : V) :
    ∃ A B C, d a b = A + B ∧ d a c = A + C ∧ d b c = B + C := by
  obtain ⟨k, hk⟩ := h.even3 a b c
  have t1 := h.tri a b c
  have t2 := h.tri a c b
  have t3 := h.tri b a c
  have s1 := h.symm c b
  have s2 := h.symm b a
  refine ⟨k - d b c, k - d a c, k - d a b, ?_, ?_, ?_⟩ <;> omega

def Cvx (d : V → V → ℕ) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ p, d a p + d p b = d a b → p ∈ S

lemma cvx_card (h : IsTM d) {S : Finset V} (hS : Cvx d S) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    d x y + 1 ≤ S.card := by
  obtain ⟨f, hf⟩ := h.geo' x y
  have hc := Finset.card_le_card_of_injOn (s := Finset.range (d x y + 1)) (t := S) f ?_ ?_
  · simpa using hc
  · intro s hs
    have hs' : s ≤ d x y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    obtain ⟨e1, e2⟩ := hf s hs'
    exact hS x hx y hy (f s) (by omega)
  · intro s hs s' hs' he
    have hs1 : s ≤ d x y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hs2 : s' ≤ d x y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs')
    have e1 := (hf s hs1).1
    have e2 := (hf s' hs2).1
    rw [he] at e1
    omega

def Dn (d : V → V → ℕ) (S : Finset V) (o v : V) : Finset V :=
  S.filter (fun u => d o v + d v u = d o u)

lemma mem_Dn {S : Finset V} {o v u : V} : u ∈ Dn d S o v ↔ u ∈ S ∧ d o v + d v u = d o u := by
  simp [Dn]

lemma cvx_Dn (h : IsTM d) {S : Finset V} (hS : Cvx d S) (o v : V) : Cvx d (Dn d S o v) := by
  intro a ha b hb p hp
  rw [mem_Dn] at ha hb ⊢
  refine ⟨hS a ha.1 b hb.1 p hp, ?_⟩
  have f1 := h.four v p o a
  have f2 := h.four v p o b
  have t1 := h.tri o v p
  have t2 := h.tri a v b
  have s1 := h.symm v o
  have s2 := h.symm p a
  have s3 := h.symm p o
  have s4 := h.symm a v
  by_cases hz : d v p = 0
  · have e := (h.eq0 v p).mp hz
    subst e
    rw [h.self, Nat.add_zero]
  · omega

lemma Dn_seg (h : IsTM d) {o c p a b : V} (h1 : d o c + d c p = d o p)
    (h2 : d a p + d p b = d a b) : d o c + d c a = d o a ∨ d o c + d c b = d o b := by
  have f := h.four o p a b
  have t1 := h.tri o c a
  have t2 := h.tri o c b
  have t3 := h.tri c p a
  have t4 := h.tri c p b
  have s := h.symm p a
  omega

lemma Dn_trans (h : IsTM d) {o v c u : V} (h1 : d o v + d v c = d o c)
    (h2 : d o c + d c u = d o u) : d o v + d v u = d o u := by
  have t1 := h.tri v c u
  have t2 := h.tri o v u
  omega

lemma Dn_child (h : IsTM d) {S : Finset V} (hS : Cvx d S) {o v u : V} (hv : v ∈ S)
    (hu : u ∈ Dn d S o v) (hne : u ≠ v) :
    ∃ c, c ∈ Dn d S o v ∧ d v c = 1 ∧ u ∈ Dn d S o c := by
  rw [mem_Dn] at hu
  have hpos : 1 ≤ d v u := by
    rcases Nat.eq_zero_or_pos (d v u) with h0 | h0
    · exact absurd ((h.eq0 v u).mp h0).symm hne
    · exact h0
  obtain ⟨c, hc1, hc2⟩ := h.geo v u 1 hpos
  have hcS : c ∈ S := hS v hv u hu.1 c (by omega)
  have t1 := h.tri o v c
  have t2 := h.tri o c u
  refine ⟨c, ?_, hc1, ?_⟩
  · rw [mem_Dn]; exact ⟨hcS, by omega⟩
  · rw [mem_Dn]; exact ⟨hu.1, by omega⟩

def Chd (d : V → V → ℕ) (S : Finset V) (o v : V) : Finset V :=
  (Dn d S o v).filter (fun c => d v c = 1)

lemma mem_Chd {S : Finset V} {o v c : V} :
    c ∈ Chd d S o v ↔ c ∈ S ∧ d o v + d v c = d o c ∧ d v c = 1 := by
  simp [Chd, Dn, and_assoc]

lemma chd_disj (h : IsTM d) {S : Finset V} {o v c c' u : V} (hc : c ∈ Chd d S o v)
    (hc' : c' ∈ Chd d S o v) (hu : u ∈ Dn d S o c) (hu' : u ∈ Dn d S o c') : c = c' := by
  rw [mem_Chd] at hc hc'
  rw [mem_Dn] at hu hu'
  exact h.geo_unique (x := o) (y := u) (by omega) (by omega) hu.2

def UU (d : V → V → ℕ) (S : Finset V) (o v : V) (C : Finset V) : Finset V :=
  insert v (C.biUnion (Dn d S o))

lemma mem_UU {S : Finset V} {o v u : V} {C : Finset V} :
    u ∈ UU d S o v C ↔ u = v ∨ ∃ c ∈ C, u ∈ Dn d S o c := by
  simp [UU]

lemma UU_sub_Dn (h : IsTM d) {S : Finset V} {o v : V} (hv : v ∈ S) {C : Finset V}
    (hC : C ⊆ Chd d S o v) {u : V} (hu : u ∈ UU d S o v C) : u ∈ Dn d S o v := by
  rw [mem_UU] at hu
  rcases hu with rfl | ⟨c, hc, hu⟩
  · rw [mem_Dn]; exact ⟨hv, by rw [h.self, Nat.add_zero]⟩
  · have hc' := mem_Chd.mp (hC hc)
    rw [mem_Dn] at hu ⊢
    exact ⟨hu.1, Dn_trans h hc'.2.1 hu.2⟩

lemma UU_cvx (h : IsTM d) {S : Finset V} (hS : Cvx d S) {o v : V} (hv : v ∈ S) {C : Finset V}
    (hC : C ⊆ Chd d S o v) : Cvx d (UU d S o v C) := by
  intro a ha b hb p hp
  have hpD : p ∈ Dn d S o v :=
    cvx_Dn h hS o v a (UU_sub_Dn h hv hC ha) b (UU_sub_Dn h hv hC hb) p hp
  by_cases hpv : p = v
  · rw [mem_UU]; exact Or.inl hpv
  · obtain ⟨c', hc'D, hc'1, hpc'⟩ := Dn_child h hS hv hpD hpv
    have hc'Ch : c' ∈ Chd d S o v := by
      rw [mem_Dn] at hc'D
      rw [mem_Chd]; exact ⟨hc'D.1, hc'D.2, hc'1⟩
    have key : ∀ x ∈ UU d S o v C, d o c' + d c' x = d o x → c' ∈ C := by
      intro x hx hxc
      have hxS : x ∈ S := (mem_Dn.mp (UU_sub_Dn h hv hC hx)).1
      rw [mem_UU] at hx
      rcases hx with rfl | ⟨c'', hc'', hxc''⟩
      · exfalso
        have e := mem_Chd.mp hc'Ch
        have s1 := h.symm c' x
        omega
      · have e : c' = c'' := chd_disj h hc'Ch (hC hc'') (mem_Dn.mpr ⟨hxS, hxc⟩) hxc''
        rw [e]; exact hc''
    have hpc := (mem_Dn.mp hpc').2
    rcases Dn_seg h hpc hp with hx | hx
    · rw [mem_UU]; exact Or.inr ⟨c', key a ha hx, hpc'⟩
    · rw [mem_UU]; exact Or.inr ⟨c', key b hb hx, hpc'⟩

lemma UU_card (h : IsTM d) {S : Finset V} {o v : V} {C : Finset V} (hC : C ⊆ Chd d S o v) :
    (UU d S o v C).card = 1 + ∑ c ∈ C, (Dn d S o c).card := by
  have hnot : v ∉ C.biUnion (Dn d S o) := by
    intro hv
    obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hv
    have e := mem_Chd.mp (hC hc)
    rw [mem_Dn] at hvc
    have s1 := h.symm c v
    omega
  have hdisj : (C : Set V).PairwiseDisjoint (Dn d S o) := by
    intro x hx y hy hxy
    exact Finset.disjoint_left.mpr (fun u hu hu' => hxy (chd_disj h (hC hx) (hC hy) hu hu'))
  unfold UU
  rw [Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj]
  omega

lemma Dn_eq_UU (h : IsTM d) {S : Finset V} (hS : Cvx d S) {o v : V} (hv : v ∈ S) :
    Dn d S o v = UU d S o v (Chd d S o v) := by
  ext u
  constructor
  · intro hu
    by_cases huv : u = v
    · rw [mem_UU]; exact Or.inl huv
    · obtain ⟨c, hcD, hc1, huc⟩ := Dn_child h hS hv hu huv
      rw [mem_UU]
      refine Or.inr ⟨c, ?_, huc⟩
      rw [mem_Dn] at hcD
      rw [mem_Chd]; exact ⟨hcD.1, hcD.2, hc1⟩
  · intro hu
    exact UU_sub_Dn h hv (Finset.Subset.refl _) hu

lemma sdiff_cvx (h : IsTM d) {S : Finset V} (hS : Cvx d S) (o : V) (C : Finset V) :
    Cvx d (S \ C.biUnion (Dn d S o)) := by
  intro a ha b hb p hp
  rw [Finset.mem_sdiff] at ha hb ⊢
  refine ⟨hS a ha.1 b hb.1 p hp, ?_⟩
  intro hpc
  obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hpc
  rcases Dn_seg h (mem_Dn.mp hpc).2 hp with hx | hx
  · exact ha.2 (Finset.mem_biUnion.mpr ⟨c, hc, mem_Dn.mpr ⟨ha.1, hx⟩⟩)
  · exact hb.2 (Finset.mem_biUnion.mpr ⟨c, hc, mem_Dn.mpr ⟨hb.1, hx⟩⟩)

lemma sub_select (Ch : Finset V) (wt : V → ℕ) (l : ℕ) (hl : 1 ≤ l)
    (hsum : l ≤ ∑ c ∈ Ch, wt c) :
    ∃ C, C ⊆ Ch ∧ ∃ c0, c0 ∈ C ∧ l ≤ ∑ c ∈ C, wt c ∧ ∑ c ∈ C.erase c0, wt c + 1 ≤ l := by
  have hne : (Ch.powerset.filter (fun C => l ≤ ∑ c ∈ C, wt c)).Nonempty :=
    ⟨Ch, by simp [hsum]⟩
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ (fun C : Finset V => C.card) hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hC
  have hCne : C.Nonempty := by
    rcases Finset.eq_empty_or_nonempty C with rfl | hne'
    · simp at hC; omega
    · exact hne'
  obtain ⟨c0, hc0⟩ := hCne
  refine ⟨C, hC.1, c0, hc0, hC.2, ?_⟩
  by_contra hcon
  have hmem : C.erase c0 ∈ Ch.powerset.filter (fun C => l ≤ ∑ c ∈ C, wt c) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset _ _).trans hC.1, by omega⟩
  have h2 := hmin _ hmem
  simp only [Finset.card_erase_of_mem hc0] at h2
  have h3 : 0 < C.card := Finset.card_pos.mpr ⟨c0, hc0⟩
  omega

def LMin (d : V → V → ℕ) (S : Finset V) (l : ℕ) : Prop :=
  ∃ P1 P2 : Finset V, ∃ v, Cvx d P1 ∧ Cvx d P2 ∧ S = P1 ∪ P2 ∧ v ∈ P1 ∧ v ∈ P2 ∧
    P1.card ≤ l + 1 ∧ P2.card ≤ l + 1

lemma LMin.card_le {S : Finset V} {l : ℕ} (hm : LMin d S l) : S.card ≤ 2 * l + 1 := by
  obtain ⟨P1, P2, v, -, -, rfl, h1, h2, c1, c2⟩ := hm
  have e := Finset.card_union_add_card_inter P1 P2
  have hpos : 0 < (P1 ∩ P2).card := Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
  omega

lemma LMin.ball (h : IsTM d) {S : Finset V} {l : ℕ} (hm : LMin d S l) :
    ∃ v, v ∈ S ∧ ∀ u ∈ S, d v u ≤ l := by
  obtain ⟨P1, P2, v, k1, k2, rfl, h1, h2, c1, c2⟩ := hm
  refine ⟨v, Finset.mem_union_left _ h1, ?_⟩
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · have e := cvx_card h k1 h1 hu
    omega
  · have e := cvx_card h k2 h2 hu
    omega

lemma LMin.three (h : IsTM d) {S : Finset V} {l : ℕ} (hm : LMin d S l) {a b c : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : d a b ≤ l ∨ d a c ≤ l ∨ d b c ≤ l := by
  obtain ⟨P1, P2, v, k1, k2, rfl, h1, h2, c1, c2⟩ := hm
  have key : ∀ (P : Finset V), Cvx d P → P.card ≤ l + 1 → ∀ x ∈ P, ∀ y ∈ P, d x y ≤ l := by
    intro P kP cP x hx y hy
    have e := cvx_card h kP hx hy
    omega
  rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb <;>
    rcases Finset.mem_union.mp hc with hc | hc
  · exact Or.inl (key P1 k1 c1 a ha b hb)
  · exact Or.inl (key P1 k1 c1 a ha b hb)
  · exact Or.inr (Or.inl (key P1 k1 c1 a ha c hc))
  · exact Or.inr (Or.inr (key P2 k2 c2 b hb c hc))
  · exact Or.inr (Or.inr (key P1 k1 c1 b hb c hc))
  · exact Or.inr (Or.inl (key P2 k2 c2 a ha c hc))
  · exact Or.inl (key P2 k2 c2 a ha b hb)
  · exact Or.inl (key P2 k2 c2 a ha b hb)

lemma partition1 (h : IsTM d) {S : Finset V} (hS : Cvx d S) {l : ℕ} (hl : 1 ≤ l)
    (hcard : l + 1 ≤ S.card) :
    ∃ S0 S1 : Finset V, Cvx d S0 ∧ Cvx d S1 ∧ S0 ∪ S1 = S ∧ S0.card + S1.card = S.card + 1 ∧
      S0.Nonempty ∧ l + 1 ≤ S1.card ∧ LMin d S1 l := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨o, ho⟩ := hne
  have hDo : Dn d S o o = S := by
    ext u
    rw [mem_Dn, h.self]
    constructor
    · exact fun hu => hu.1
    · exact fun hu => ⟨hu, by omega⟩
  have hne2 : (S.filter (fun v => l + 1 ≤ (Dn d S o v).card)).Nonempty :=
    ⟨o, Finset.mem_filter.mpr ⟨ho, by rw [hDo]; exact hcard⟩⟩
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image _ (fun v => d o v) hne2
  obtain ⟨hvS, hvl⟩ := Finset.mem_filter.mp hv
  have hsmall : ∀ c ∈ Chd d S o v, (Dn d S o c).card ≤ l := by
    intro c hc
    by_contra hcon
    have hc' := mem_Chd.mp hc
    have hmem : c ∈ S.filter (fun v => l + 1 ≤ (Dn d S o v).card) :=
      Finset.mem_filter.mpr ⟨hc'.1, by omega⟩
    have h2 := hvmax c hmem
    omega
  have hsum : l ≤ ∑ c ∈ Chd d S o v, (Dn d S o c).card := by
    have e1 := UU_card h (S := S) (o := o) (v := v) (Finset.Subset.refl (Chd d S o v))
    rw [← Dn_eq_UU h hS hvS] at e1
    omega
  obtain ⟨C, hCsub, c0, hc0, hCl, hCe⟩ :=
    sub_select (Chd d S o v) (fun c => (Dn d S o c).card) l hl hsum
  have hXsub : C.biUnion (Dn d S o) ⊆ S := by
    intro u hu
    obtain ⟨c, -, huc⟩ := Finset.mem_biUnion.mp hu
    exact (mem_Dn.mp huc).1
  have hvX : v ∉ C.biUnion (Dn d S o) := by
    intro hv'
    obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hv'
    have e := mem_Chd.mp (hCsub hc)
    rw [mem_Dn] at hvc
    have s1 := h.symm c v
    omega
  have hXcard : (C.biUnion (Dn d S o)).card = ∑ c ∈ C, (Dn d S o c).card := by
    apply Finset.card_biUnion
    intro x hx y hy hxy
    exact Finset.disjoint_left.mpr
      (fun u hu hu' => hxy (chd_disj h (hCsub hx) (hCsub hy) hu hu'))
  have hS1card := UU_card h (S := S) (o := o) (v := v) hCsub
  refine ⟨S \ C.biUnion (Dn d S o), UU d S o v C, sdiff_cvx h hS o C, UU_cvx h hS hvS hCsub,
    ?_, ?_, ⟨v, Finset.mem_sdiff.mpr ⟨hvS, hvX⟩⟩, by omega, ?_⟩
  · ext u
    rw [Finset.mem_union, Finset.mem_sdiff, mem_UU]
    constructor
    · rintro (hu | rfl | ⟨c, hc, hu⟩)
      · exact hu.1
      · exact hvS
      · exact (mem_Dn.mp hu).1
    · intro hu
      by_cases hux : u ∈ C.biUnion (Dn d S o)
      · obtain ⟨c, hc, huc⟩ := Finset.mem_biUnion.mp hux
        exact Or.inr (Or.inr ⟨c, hc, huc⟩)
      · exact Or.inl ⟨hu, hux⟩
  · have e := Finset.card_sdiff_add_card_eq_card hXsub
    omega
  · have hsub1 : ({c0} : Finset V) ⊆ Chd d S o v := by
      intro c hc
      rw [Finset.mem_singleton] at hc
      rw [hc]; exact hCsub hc0
    have hsub2 : C.erase c0 ⊆ Chd d S o v := (Finset.erase_subset _ _).trans hCsub
    refine ⟨UU d S o v {c0}, UU d S o v (C.erase c0), v, UU_cvx h hS hvS hsub1,
      UU_cvx h hS hvS hsub2, ?_, mem_UU.mpr (Or.inl rfl), mem_UU.mpr (Or.inl rfl), ?_, ?_⟩
    · ext u
      rw [Finset.mem_union, mem_UU, mem_UU, mem_UU]
      constructor
      · rintro (hu | ⟨c, hc, hu⟩)
        · exact Or.inl (Or.inl hu)
        · by_cases hcc : c = c0
          · exact Or.inl (Or.inr ⟨c0, Finset.mem_singleton_self _, hcc ▸ hu⟩)
          · exact Or.inr (Or.inr ⟨c, Finset.mem_erase.mpr ⟨hcc, hc⟩, hu⟩)
      · rintro ((hu | ⟨c, hc, hu⟩) | (hu | ⟨c, hc, hu⟩))
        · exact Or.inl hu
        · rw [Finset.mem_singleton] at hc
          exact Or.inr ⟨c0, hc0, hc ▸ hu⟩
        · exact Or.inl hu
        · exact Or.inr ⟨c, Finset.mem_of_mem_erase hc, hu⟩
    · rw [UU_card h hsub1, Finset.sum_singleton]
      have e := hsmall c0 (hCsub hc0)
      omega
    · rw [UU_card h hsub2]
      omega

lemma partition3 (h : IsTM d) {l : ℕ} (hl : 1 ≤ l) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → Cvx d S → l + 1 ≤ S.card →
      ∃ Ts : List (Finset V), (∀ T ∈ Ts, Cvx d T ∧ l + 1 ≤ T.card ∧ T.card ≤ 3 * l) ∧
        (∀ u, u ∈ S ↔ ∃ T ∈ Ts, u ∈ T) ∧ (Ts.map (fun T => T.card - 1)).sum = S.card - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hcard
    obtain ⟨S0, S1, c0, c1, hU, hc, hne, hl1, hmin⟩ := partition1 h hS hl hcard
    have h1 : S1.card ≤ 2 * l + 1 := hmin.card_le
    by_cases hbig : l + 1 ≤ S0.card
    · obtain ⟨Ts, hT1, hT2, hT3⟩ := ih S0.card (by omega) S0 rfl c0 hbig
      refine ⟨S1 :: Ts, ?_, ?_, ?_⟩
      · intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact ⟨c1, hl1, by omega⟩
        · exact hT1 T hT
      · intro u
        rw [← hU, Finset.mem_union, hT2]
        constructor
        · rintro (⟨T, hT, hu⟩ | hu)
          · exact ⟨T, List.mem_cons_of_mem _ hT, hu⟩
          · exact ⟨S1, List.mem_cons_self, hu⟩
        · rintro ⟨T, hT, hu⟩
          rcases List.mem_cons.mp hT with rfl | hT
          · exact Or.inr hu
          · exact Or.inl ⟨T, hT, hu⟩
      · rw [List.map_cons, List.sum_cons, hT3]; omega
    · refine ⟨[S], ?_, ?_, ?_⟩
      · intro T hT
        rw [List.mem_singleton] at hT
        subst hT
        exact ⟨hS, hcard, by omega⟩
      · intro u; simp
      · simp

def Cov (d : V → V → ℕ) (S : Finset V) (bs : List (V × ℕ)) : Prop :=
  ∀ u ∈ S, ∃ b ∈ bs, d b.1 u ≤ b.2

def Rz (d : V → V → ℕ) (S : Finset V) (rs : List ℕ) : Prop :=
  ∃ bs : List (V × ℕ), bs.map Prod.snd = rs ∧ Cov d S bs

lemma largeeps (h : IsTM d) : ∀ (rs : List ℕ) (S : Finset V), Cvx d S → S.Nonempty → rs ≠ [] →
    S.card - 1 ≤ rs.sum → Rz d S rs := by
  intro rs
  induction rs with
  | nil => intro S _ _ hne; exact absurd rfl hne
  | cons ρ rs ih =>
    intro S hS hne _ hsum
    obtain ⟨v0, hv0⟩ := hne
    rw [List.sum_cons] at hsum
    by_cases h1 : S.card - 1 ≤ ρ
    · refine ⟨(v0, ρ) :: rs.map (fun r => (v0, r)), ?_, ?_⟩
      · simp [List.map_map, Function.comp_def]
      · intro u hu
        refine ⟨(v0, ρ), List.mem_cons_self, ?_⟩
        have e := cvx_card h hS hv0 hu
        simp only
        omega
    · have hrs : rs ≠ [] := by
        rintro rfl
        simp at hsum; omega
      by_cases h0 : ρ = 0
      · obtain ⟨bs, hb1, hb2⟩ := ih S hS ⟨v0, hv0⟩ hrs (by omega)
        refine ⟨(v0, ρ) :: bs, by simp [hb1], ?_⟩
        intro u hu
        obtain ⟨b, hb, hbu⟩ := hb2 u hu
        exact ⟨b, List.mem_cons_of_mem _ hb, hbu⟩
      · obtain ⟨S0, S1, c0, c1, hU, hc, hne0, hl1, hmin⟩ :=
          partition1 h hS (l := ρ) (by omega) (by omega)
        obtain ⟨v1, -, hv1⟩ := hmin.ball h
        obtain ⟨bs, hb1, hb2⟩ := ih S0 c0 hne0 hrs (by omega)
        refine ⟨(v1, ρ) :: bs, by simp [hb1], ?_⟩
        intro u hu
        rw [← hU, Finset.mem_union] at hu
        rcases hu with hu | hu
        · obtain ⟨b, hb, hbu⟩ := hb2 u hu
          exact ⟨b, List.mem_cons_of_mem _ hb, hbu⟩
        · exact ⟨(v1, ρ), List.mem_cons_self, hv1 u hu⟩

end Pieces

/-! ### Part B, continued: a convex set of small size is covered by two well placed balls -/

section Perim

variable {V : Type} [DecidableEq V] {d : V → V → ℕ}

lemma max_triple (h : IsTM d) {S : Finset V} (hne : S.Nonempty) :
    ∃ w1 ∈ S, ∃ w2 ∈ S, ∃ w3 ∈ S,
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
        d a b + d a c + d b c ≤ d w1 w2 + d w1 w3 + d w2 w3) ∧
      d w1 w2 ≤ d w1 w3 ∧ d w1 w3 ≤ d w2 w3 := by
  have hne3 : (S ×ˢ S ×ˢ S).Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨(v, v, v), by simp [hv]⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (S ×ˢ S ×ˢ S)
    (fun t : V × V × V => d t.1 t.2.1 + d t.1 t.2.2 + d t.2.1 t.2.2) hne3
  obtain ⟨a, b, c⟩ := t
  simp only [Finset.mem_product] at ht
  obtain ⟨ha, hb, hc⟩ := ht
  have hm : ∀ a' ∈ S, ∀ b' ∈ S, ∀ c' ∈ S,
      d a' b' + d a' c' + d b' c' ≤ d a b + d a c + d b c := by
    intro a' ha' b' hb' c' hc'
    exact hmax (a', b', c') (by simp [ha', hb', hc'])
  have s1 := h.symm a b
  have s2 := h.symm a c
  have s3 := h.symm b c
  rcases le_total (d a b) (d a c) with h1 | h1 <;>
    rcases le_total (d a c) (d b c) with h2 | h2 <;>
    rcases le_total (d a b) (d b c) with h3 | h3
  · exact ⟨a, ha, b, hb, c, hc, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨a, ha, b, hb, c, hc, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨b, hb, a, ha, c, hc, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨b, hb, c, hc, a, ha, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨a, ha, c, hc, b, hb, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨c, hc, a, ha, b, hb, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨c, hc, b, hb, a, ha, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩
  · exact ⟨c, hc, b, hb, a, ha, fun x hx y hy z hz => by
      have := hm x hx y hy z hz; omega, by omega, by omega⟩

lemma geo_ext (h : IsTM d) {a b q t : V} (hq : d a q + d q b = d a b)
    (ht : d b a + d a t = d b t) : d q t = d a q + d a t := by
  have t1 := h.tri q a t
  have t2 := h.tri b q t
  have s1 := h.symm q a
  have s2 := h.symm b a
  have s3 := h.symm b q
  omega

lemma tripod_count (h : IsTM d) {S : Finset V} (hS : Cvx d S) {x y w1 : V} {L1 L2 L3 : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hw : w1 ∈ S) (e12 : d w1 x = L1 + L2)
    (e13 : d w1 y = L1 + L3) (e23 : d x y = L2 + L3) {z ts : ℕ} (hts : ts ≠ L2)
    (hz : z = 0 ∨ ∃ us ∈ S, d us x = z + ts ∧ d us y + ts = z + (L2 + L3)) :
    L2 + L3 + 1 + L1 + z ≤ S.card := by
  obtain ⟨pos, hpos⟩ := h.geo' x y
  have hposS : ∀ s, s ≤ L2 + L3 → pos s ∈ S := by
    intro s hs
    obtain ⟨e1, e2⟩ := hpos s (by omega)
    exact hS x hx y hy (pos s) (by omega)
  obtain ⟨m1, m2⟩ := hpos L2 (by omega)
  have hmw : d (pos L2) w1 = L1 := by
    have f := h.four w1 (pos L2) x y
    have t := h.tri w1 (pos L2) x
    have s1 := h.symm (pos L2) x
    have s2 := h.symm (pos L2) w1
    omega
  obtain ⟨qf, hqf⟩ := h.geo' (pos L2) w1
  have key : ∀ j, ∃ u, j < L2 + L3 + 1 + L1 + z → (u ∈ S ∧
      ((j ≤ L2 + L3 ∧ d u x = j ∧ d u y + j = L2 + L3) ∨
       (L2 + L3 < j ∧ j ≤ L2 + L3 + L1 ∧ d u x = L2 + (j - (L2 + L3)) ∧
          d u y = L3 + (j - (L2 + L3))) ∨
       (L2 + L3 + L1 < j ∧ d u x = ts + (j - (L2 + L3 + L1)) ∧
          d u y + ts = L2 + L3 + (j - (L2 + L3 + L1))))) := by
    intro j
    by_cases hj1 : j ≤ L2 + L3
    · refine ⟨pos j, fun _ => ⟨hposS j hj1, Or.inl ?_⟩⟩
      obtain ⟨e1, e2⟩ := hpos j (by omega)
      have s := h.symm (pos j) x
      exact ⟨hj1, by omega, by omega⟩
    · by_cases hj2 : j ≤ L2 + L3 + L1
      · obtain ⟨e1, e2⟩ := hqf (j - (L2 + L3)) (by omega)
        have s1 := h.symm (pos L2) x
        have s2 := h.symm w1 (pos L2)
        have g1 := geo_ext h (a := pos L2) (b := w1) (q := qf (j - (L2 + L3))) (t := x)
          (by omega) (by omega)
        have g2 := geo_ext h (a := pos L2) (b := w1) (q := qf (j - (L2 + L3))) (t := y)
          (by omega) (by omega)
        refine ⟨qf (j - (L2 + L3)), fun _ =>
          ⟨hS _ (hposS L2 (by omega)) w1 hw _ (by omega), Or.inr (Or.inl ?_)⟩⟩
        exact ⟨by omega, hj2, by omega, by omega⟩
      · by_cases hj3 : j < L2 + L3 + 1 + L1 + z
        · rcases hz with hz | ⟨us, hus, eu1, eu2⟩
          · omega
          · have hts2 : ts ≤ L2 + L3 := by
              have t := h.tri us y x
              have s := h.symm y x
              omega
            obtain ⟨p1, p2⟩ := hpos ts (by omega)
            have s1 := h.symm (pos ts) x
            have s2 := h.symm us (pos ts)
            have hpu : d (pos ts) us = z := by
              have f := h.four us (pos ts) x y
              have t := h.tri us (pos ts) x
              omega
            obtain ⟨cf, hcf⟩ := h.geo' (pos ts) us
            obtain ⟨e1, e2⟩ := hcf (j - (L2 + L3 + L1)) (by omega)
            have g1 := geo_ext h (a := pos ts) (b := us) (q := cf (j - (L2 + L3 + L1)))
              (t := x) (by omega) (by omega)
            have g2 := geo_ext h (a := pos ts) (b := us) (q := cf (j - (L2 + L3 + L1)))
              (t := y) (by omega) (by omega)
            refine ⟨cf (j - (L2 + L3 + L1)), fun _ =>
              ⟨hS _ (hposS ts hts2) us hus _ (by omega), Or.inr (Or.inr ?_)⟩⟩
            exact ⟨by omega, by omega, by omega⟩
        · exact ⟨x, fun hc => absurd hc hj3⟩
  choose F hF using key
  have hc := Finset.card_le_card_of_injOn (s := Finset.range (L2 + L3 + 1 + L1 + z)) (t := S) F
    ?_ ?_
  · simpa using hc
  · intro j hj
    exact (hF j (Finset.mem_range.mp hj)).1
  · intro j hj j' hj' he
    have a1 := (hF j (Finset.mem_range.mp hj)).2
    have a2 := (hF j' (Finset.mem_range.mp hj')).2
    rw [he] at a1
    clear hz hF
    omega

lemma cover_aux2 (hh tt L1 L2 L3 z r1 r2 x1 x2 s1 s2 : ℕ)
    (hc : hh ≤ L1) (h12 : L1 ≤ L2) (h23 : L2 ≤ L3) (htD : tt ≤ L2 + L3)
    (ht : L2 ≤ tt ∨ hh ≤ tt) (ht' : tt ≤ L2 ∨ hh + tt ≤ L2 + L3) (hz : tt = L2 ∨ hh ≤ z)
    (hzL : z ≤ L1) (ha : L1 + L2 ≤ 2 * r1) (hb : L2 + L3 + 2 * z ≤ 2 * (r1 + r2) + 1)
    (hs1 : s1 = min r1 (L2 + L3)) (hs2 : s2 = L2 + L3 - min r2 (L2 + L3))
    (hx1 : x1 + s1 ≤ hh + tt ∨ x1 + tt ≤ hh + s1)
    (hx2 : x2 + s2 ≤ hh + tt ∨ x2 + tt ≤ hh + s2) :
    x1 ≤ r1 ∨ x2 ≤ r2 := by
  omega

lemma cover_aux1 (hh tt L1 L2 L3 z r1 x1 s1 : ℕ)
    (hc : hh ≤ L1) (h12 : L1 ≤ L2) (h23 : L2 ≤ L3) (htD : tt ≤ L2 + L3)
    (ht : L2 ≤ tt ∨ hh ≤ tt) (ht' : tt ≤ L2 ∨ hh + tt ≤ L2 + L3) (hz : tt = L2 ∨ hh ≤ z)
    (hzL : z ≤ L1) (ha : L1 + L2 ≤ 2 * r1) (hb : L2 + L3 + 2 * z ≤ 2 * r1)
    (hs1 : s1 = min r1 (L2 + L3))
    (hx1 : x1 + s1 ≤ hh + tt ∨ x1 + tt ≤ hh + s1) :
    x1 ≤ r1 := by
  omega

lemma two_cover (h : IsTM d) {S : Finset V} (hS : Cvx d S) {l : ℕ} (hmin : LMin d S l) :
    ∃ (b : ℕ) (p1 p2 : ℕ → V), 3 * b ≤ S.card - 1 ∧ S.card - 1 + b ≤ 2 * l ∧
      (∀ r1 r2, S.card - 1 + b ≤ 4 * r1 → S.card - 1 ≤ b + 2 * (r1 + r2) + 1 →
        ∀ u ∈ S, d (p1 r1) u ≤ r1 ∨ d (p2 r2) u ≤ r2) ∧
      (∀ r1, S.card - 1 ≤ b + 2 * r1 → ∀ u ∈ S, d (p1 r1) u ≤ r1) := by
  have hne : S.Nonempty := by
    obtain ⟨P1, P2, v, -, -, rfl, h1, -⟩ := hmin
    exact ⟨v, Finset.mem_union_left _ h1⟩
  obtain ⟨w1, hw1, w2, hw2, w3, hw3, hmax, hle1, hle2⟩ := max_triple h hne
  obtain ⟨L1, L2, L3, e12, e13, e23⟩ := h.gromov w1 w2 w3
  have hL12 : L1 ≤ L2 := by omega
  have hL23 : L2 ≤ L3 := by omega
  choose hh tt cc hg1 hg2 hg3 using fun u => h.gromov u w2 w3
  have hP : ∀ u ∈ S, hh u ≤ L1 ∧ (L2 ≤ tt u ∨ hh u ≤ tt u) ∧
      (tt u ≤ L2 ∨ hh u + tt u ≤ L2 + L3) := by
    intro u hu
    have m1 := hmax u hu w2 hw2 w3 hw3
    have m2 := hmax w1 hw1 u hu w3 hw3
    have m3 := hmax w1 hw1 w2 hw2 u hu
    have f1 := h.four u w3 w1 w2
    have f2 := h.four u w2 w1 w3
    have s1 := h.symm w3 w2
    have s2 := h.symm w3 w1
    have s3 := h.symm w1 u
    have s4 := h.symm w2 w1
    have s5 := h.symm w2 u
    have g1 := hg1 u
    have g2 := hg2 u
    have g3 := hg3 u
    refine ⟨by omega, by omega, by omega⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = (S.filter (fun u => tt u ≠ L2)).sup hh := ⟨_, rfl⟩
  have hzle : ∀ u ∈ S, tt u = L2 ∨ hh u ≤ z := by
    intro u hu
    by_cases ht : tt u = L2
    · exact Or.inl ht
    · rw [hzdef]
      exact Or.inr (Finset.le_sup (f := hh) (Finset.mem_filter.mpr ⟨hu, ht⟩))
  have hzL : z ≤ L1 := by
    rw [hzdef]
    exact Finset.sup_le (fun u hu => (hP u (Finset.mem_filter.mp hu).1).1)
  have hzat : ∃ ts, ts ≠ L2 ∧
      (z = 0 ∨ ∃ us ∈ S, d us w2 = z + ts ∧ d us w3 + ts = z + (L2 + L3)) := by
    rcases Finset.eq_empty_or_nonempty (S.filter (fun u => tt u ≠ L2)) with he | hne'
    · exact ⟨L2 + 1, by omega, Or.inl (by rw [hzdef, he]; simp)⟩
    · obtain ⟨us, hus, hsup⟩ := Finset.exists_mem_eq_sup _ hne' hh
      obtain ⟨husS, hust⟩ := Finset.mem_filter.mp hus
      have g1 := hg1 us
      have g2 := hg2 us
      have g3 := hg3 us
      rw [← hzdef] at hsup
      exact ⟨tt us, hust, Or.inr ⟨us, husS, by omega, by omega⟩⟩
  obtain ⟨ts, hts, hzz⟩ := hzat
  have hcount := tripod_count h hS hw2 hw3 hw1 e12 e13 e23 hts hzz
  obtain ⟨pos, hpos⟩ := h.geo' w2 w3
  have hproj : ∀ u σ, σ ≤ L2 + L3 →
      (d (pos σ) u + σ ≤ hh u + tt u ∨ d (pos σ) u + tt u ≤ hh u + σ) := by
    intro u σ hσ
    obtain ⟨q1, q2⟩ := hpos σ (by omega)
    have f := h.four u (pos σ) w2 w3
    have s1 := h.symm (pos σ) w2
    have s2 := h.symm (pos σ) u
    have g1 := hg1 u
    have g2 := hg2 u
    have g3 := hg3 u
    omega
  refine ⟨2 * (L1 + L2) - (S.card - 1), fun r1 => pos (min r1 (L2 + L3)),
    fun r2 => pos (L2 + L3 - min r2 (L2 + L3)), ?_, ?_, ?_, ?_⟩
  · omega
  · have c1 := hmin.card_le
    have c2 := hmin.three h hw1 hw2 hw3
    omega
  · intro r1 r2 h1 h2 u hu
    obtain ⟨a1, a2, a3⟩ := hP u hu
    have a4 := hzle u hu
    have g3 := hg3 u
    have x1 := hproj u (min r1 (L2 + L3)) (min_le_right _ _)
    have x2 := hproj u (L2 + L3 - min r2 (L2 + L3)) (Nat.sub_le _ _)
    exact cover_aux2 (hh u) (tt u) L1 L2 L3 z r1 r2 _ _ _ _ a1 hL12 hL23 (by omega) a2 a3 a4
      hzL (by omega) (by omega) rfl rfl x1 x2
  · intro r1 h1 u hu
    obtain ⟨a1, a2, a3⟩ := hP u hu
    have a4 := hzle u hu
    have g3 := hg3 u
    have x1 := hproj u (min r1 (L2 + L3)) (min_le_right _ _)
    exact cover_aux1 (hh u) (tt u) L1 L2 L3 z r1 _ _ a1 hL12 hL23 (by omega) a2 a3 a4
      hzL (by omega) (by omega) rfl x1

end Perim

/-! ### Part C: fractional covers -/

section Frac

variable {V : Type} [DecidableEq V] {d : V → V → ℕ}

open Pointwise

noncomputable def hist (rs : List ℕ) : ℕ → ℝ := fun ρ => (rs.count ρ : ℝ)

lemma hist_append (a b : List ℕ) : hist (a ++ b) = hist a + hist b := by
  funext ρ
  simp [hist, List.count_append]

lemma hist_pair (a b ρ : ℕ) :
    hist [a, b] ρ = (if a = ρ then (1 : ℝ) else 0) + (if b = ρ then (1 : ℝ) else 0) := by
  by_cases h1 : a = ρ <;> by_cases h2 : b = ρ <;> simp [hist, List.count_cons, h1, h2] <;>
    norm_num

lemma hist_replicate (j x ρ : ℕ) :
    hist (List.replicate j x) ρ = if x = ρ then (j : ℝ) else 0 := by
  by_cases h1 : x = ρ <;> simp [hist, List.count_replicate, h1]

def CVr (d : V → V → ℕ) (S : Finset V) (r : ℕ) : Set (ℕ → ℝ) :=
  {f | ∃ bs : List (V × ℕ), Cov d S bs ∧ (∀ b ∈ bs, b.2 < r) ∧ f = hist (bs.map Prod.snd)}

def FC (d : V → V → ℕ) (S : Finset V) (r : ℕ) : Set (ℕ → ℝ) := convexHull ℝ (CVr d S r)

lemma FC_of_Rz {S : Finset V} {r : ℕ} {rs : List ℕ} (hc : Rz d S rs) (hr : ∀ x ∈ rs, x < r) :
    hist rs ∈ FC d S r := by
  obtain ⟨bs, rfl, hcov⟩ := hc
  refine subset_convexHull ℝ _ ⟨bs, hcov, ?_, rfl⟩
  intro b hb
  exact hr b.2 (List.mem_map.mpr ⟨b, hb, rfl⟩)

lemma FC_union {S S1 S2 : Finset V} {r : ℕ} (hS : S ⊆ S1 ∪ S2) {f1 f2 : ℕ → ℝ}
    (h1 : f1 ∈ FC d S1 r) (h2 : f2 ∈ FC d S2 r) : f1 + f2 ∈ FC d S r := by
  have hsub : CVr d S1 r + CVr d S2 r ⊆ CVr d S r := by
    rintro _ ⟨_, ⟨bs1, c1, r1, rfl⟩, _, ⟨bs2, c2, r2, rfl⟩, rfl⟩
    refine ⟨bs1 ++ bs2, ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp (hS hu) with hu | hu
      · obtain ⟨b, hb, hbu⟩ := c1 u hu
        exact ⟨b, List.mem_append_left _ hb, hbu⟩
      · obtain ⟨b, hb, hbu⟩ := c2 u hu
        exact ⟨b, List.mem_append_right _ hb, hbu⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact r1 b hb
      · exact r2 b hb
    · rw [List.map_append, hist_append]
  have h3 := Set.add_mem_add h1 h2
  unfold FC at h3 ⊢
  rw [← convexHull_add] at h3
  exact convexHull_mono hsub h3

lemma FC_mono {S : Finset V} {r r' : ℕ} (hr : r ≤ r') : FC d S r ⊆ FC d S r' := by
  apply convexHull_mono
  rintro _ ⟨bs, c, hb, rfl⟩
  exact ⟨bs, c, fun b hb' => lt_of_lt_of_le (hb b hb') hr, rfl⟩

lemma FC_vanish {S : Finset V} {r : ℕ} {f : ℕ → ℝ} (hf : f ∈ FC d S r) {ρ : ℕ} (hρ : r ≤ ρ) :
    f ρ = 0 := by
  have hconv : Convex ℝ {g : ℕ → ℝ | g ρ = 0} := by
    intro x hx y hy a b _ _ _
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [hx, hy]
  have hsub : CVr d S r ⊆ {g : ℕ → ℝ | g ρ = 0} := by
    rintro _ ⟨bs, c, hb, rfl⟩
    simp only [Set.mem_setOf_eq, hist]
    have h0 : (bs.map Prod.snd).count ρ = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      obtain ⟨b, hb', hbe⟩ := List.mem_map.mp hmem
      have := hb b hb'
      omega
    rw [h0]; simp
  exact convexHull_min hsub hconv hf

lemma FC_avg {S : Finset V} {r : ℕ} {N : ℕ} (hN : 0 < N) (F : ℕ → (ℕ → ℝ))
    (hF : ∀ i < N, F i ∈ FC d S r) :
    (fun ρ => (∑ i ∈ Finset.range N, F i ρ) / (N : ℝ)) ∈ FC d S r := by
  have hconv : Convex ℝ (FC d S r) := convex_convexHull ℝ _
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have key := hconv.sum_mem (t := Finset.range N) (w := fun _ => 1 / (N : ℝ)) (z := F)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
    (fun i hi => hF i (Finset.mem_range.mp hi))
  have he : (fun ρ => (∑ i ∈ Finset.range N, F i ρ) / (N : ℝ)) =
      ∑ i ∈ Finset.range N, (1 / (N : ℝ)) • F i := by
    funext ρ
    rw [Finset.sum_apply, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp [div_eq_inv_mul]
  rw [he]; exact key

def Ctl (d : V → V → ℕ) (S : Finset V) (r lam m : ℕ) (w : ℝ) : Prop :=
  ∃ f ∈ FC d S r, ∃ β : ℕ → ℝ, (∀ a, 0 ≤ β a) ∧ (∀ a, a < m → β a = 0) ∧
    (∀ ρ, f ρ ≤ ∑ a ∈ Finset.range (lam + 1), if a ≤ ρ then β a else 0) ∧
    ∑ a ∈ Finset.range (lam + 1), β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) ≤ w

lemma Ctl.mono {S : Finset V} {r lam m : ℕ} {w w' : ℝ} (h : Ctl d S r lam m w) (hw : w ≤ w') :
    Ctl d S r lam m w' := by
  obtain ⟨f, hf, β, b1, b2, b3, b4⟩ := h
  exact ⟨f, hf, β, b1, b2, b3, le_trans b4 hw⟩

lemma Ctl.union {S S1 S2 : Finset V} {r lam m : ℕ} {w1 w2 : ℝ} (hS : S ⊆ S1 ∪ S2)
    (h1 : Ctl d S1 r lam m w1) (h2 : Ctl d S2 r lam m w2) : Ctl d S r lam m (w1 + w2) := by
  obtain ⟨f1, hf1, β1, a1, a2, a3, a4⟩ := h1
  obtain ⟨f2, hf2, β2, b1, b2, b3, b4⟩ := h2
  refine ⟨f1 + f2, FC_union hS hf1 hf2, fun a => β1 a + β2 a,
    fun a => add_nonneg (a1 a) (b1 a), fun a ha => by
      show β1 a + β2 a = 0
      rw [a2 a ha, b2 a ha, add_zero], ?_, ?_⟩
  · intro ρ
    have e : ∑ a ∈ Finset.range (lam + 1), (if a ≤ ρ then β1 a + β2 a else 0) =
        (∑ a ∈ Finset.range (lam + 1), if a ≤ ρ then β1 a else 0) +
        ∑ a ∈ Finset.range (lam + 1), if a ≤ ρ then β2 a else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h3 : a ≤ ρ <;> simp [h3]
    rw [e]
    exact add_le_add (a3 ρ) (b3 ρ)
  · have e : ∑ a ∈ Finset.range (lam + 1), (β1 a + β2 a) * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) =
        (∑ a ∈ Finset.range (lam + 1), β1 a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2)) +
        ∑ a ∈ Finset.range (lam + 1), β2 a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [e]
    exact add_le_add a4 b4

lemma sum_dl (n ρ a : ℕ) (w : ℝ) (ha : a < n) :
    (∑ x ∈ Finset.range n, if x ≤ ρ then (if x = a then w else 0) else 0) =
      if a ≤ ρ then w else 0 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa; simp [hxa]
  · intro hna; exact absurd (Finset.mem_range.mpr ha) hna

lemma sum_dl_mul (n a : ℕ) (w : ℝ) (g : ℕ → ℝ) (ha : a < n) :
    (∑ x ∈ Finset.range n, (if x = a then w else 0) * g x) = w * g a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa; simp [hxa]
  · intro hna; exact absurd (Finset.mem_range.mpr ha) hna

lemma Ctl_level {S : Finset V} {r lam m a : ℕ} (j : ℕ) (ha1 : m ≤ a) (ha2 : a ≤ lam)
    (har : a < r) (hcov : ∀ x, a ≤ x → x < r → Rz d S (List.replicate j x)) :
    Ctl d S r lam m ((j : ℝ) * ((r : ℝ) + (a : ℝ))) := by
  have hN : 0 < r - a := by omega
  have hNr : (0 : ℝ) < ((r - a : ℕ) : ℝ) := by exact_mod_cast hN
  have hmem := FC_avg (d := d) (S := S) (r := r) hN
    (fun i => hist (List.replicate j (a + i)))
    (fun i hi => FC_of_Rz (hcov (a + i) (by omega) (by omega)) (fun x hx => by
      rw [List.eq_of_mem_replicate hx]; omega))
  refine ⟨_, hmem, fun x => if x = a then (j : ℝ) / ((r - a : ℕ) : ℝ) else 0, ?_, ?_, ?_, ?_⟩
  · intro x
    beta_reduce
    split_ifs
    · positivity
    · exact le_rfl
  · intro x hx
    beta_reduce
    rw [if_neg (by omega)]
  · intro ρ
    show (∑ i ∈ Finset.range (r - a), hist (List.replicate j (a + i)) ρ) /
      ((r - a : ℕ) : ℝ) ≤ _
    rw [sum_dl (lam + 1) ρ a _ (by omega)]
    by_cases haρ : a ≤ ρ
    · rw [if_pos haρ]
      have hL : ∑ i ∈ Finset.range (r - a), hist (List.replicate j (a + i)) ρ ≤ (j : ℝ) := by
        calc ∑ i ∈ Finset.range (r - a), hist (List.replicate j (a + i)) ρ
            = ∑ i ∈ Finset.range (r - a), if i = ρ - a then (j : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hist_replicate]
              by_cases hc : i = ρ - a
              · rw [if_pos hc, if_pos (by omega)]
              · rw [if_neg hc, if_neg (by omega)]
          _ ≤ (j : ℝ) := by
              rw [Finset.sum_ite_eq']
              split_ifs
              · exact le_rfl
              · positivity
      exact div_le_div_of_nonneg_right hL hNr.le
    · rw [if_neg haρ]
      have hL : ∑ i ∈ Finset.range (r - a), hist (List.replicate j (a + i)) ρ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hist_replicate, if_neg (by omega)]
      rw [hL, zero_div]
  · rw [sum_dl_mul (lam + 1) a _ (fun x => (r : ℝ) ^ 2 - (x : ℝ) ^ 2) (by omega)]
    have hNe : ((r - a : ℕ) : ℝ) = (r : ℝ) - a := by
      rw [Nat.cast_sub (by omega)]
    have hne : (r : ℝ) - a ≠ 0 := by rw [← hNe]; exact hNr.ne'
    rw [hNe]
    apply le_of_eq
    rw [div_mul_eq_mul_div, div_eq_iff hne]
    ring

lemma card_fib_le (N n q : ℕ) (hn : 0 < n) :
    ((Finset.range N).filter (fun i => i / n = q)).card ≤ n := by
  have hsub : (Finset.range N).filter (fun i => i / n = q) ⊆
      Finset.Ico (q * n) (q * n + n) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_Ico]
    have h1 := Nat.div_add_mod i n
    have h2 := Nat.mod_lt i hn
    rw [hi.2] at h1
    rw [Nat.mul_comm q n]
    omega
  calc ((Finset.range N).filter (fun i => i / n = q)).card
      ≤ (Finset.Ico (q * n) (q * n + n)).card := Finset.card_le_card hsub
    _ = n := by simp

lemma Ctl_two {S : Finset V} {r lam m lo c : ℕ} (hm : m ≤ lo) (hloc : lo < c) (hc : c ≤ lam)
    (hcr : c < r) (hJ : r - c ≤ c - lo)
    (hcov : ∀ x1 x2, c ≤ x1 → x1 < r → lo ≤ x2 → x2 < c → r - 1 + lo ≤ x1 + x2 →
      Rz d S [x1, x2]) :
    Ctl d S r lam m ((r : ℝ) + 2 * (c : ℝ) + (lo : ℝ)) := by
  obtain ⟨J1, hJ1⟩ : ∃ J1, J1 = r - c := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J2, J2 = c - lo := ⟨_, rfl⟩
  have hJ1p : 0 < J1 := by omega
  have hJ2p : 0 < J2 := by omega
  have hJ12 : J1 ≤ J2 := by omega
  have hN : 0 < J1 * J2 := Nat.mul_pos hJ1p hJ2p
  have hx : ∀ i, i < J1 * J2 → i / J2 < J1 ∧ i / J1 < J2 ∧ i / J2 ≤ i / J1 := by
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
    · exact Nat.div_lt_of_lt_mul hi
    · exact Nat.div_le_div_left hJ12 hJ1p
  have hmem := FC_avg (d := d) (S := S) (r := r) hN
    (fun i => hist [r - 1 - i / J2, lo + i / J1])
    (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hx i hi
      show hist [r - 1 - i / J2, lo + i / J1] ∈ FC d S r
      generalize i / J2 = q2 at h1 h3 ⊢
      generalize i / J1 = q1 at h2 h3 ⊢
      refine FC_of_Rz (hcov _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
      intro x hx'
      simp at hx'
      rcases hx' with rfl | rfl <;> omega)
  have hJ1R : (0 : ℝ) < (J1 : ℝ) := by exact_mod_cast hJ1p
  have hJ2R : (0 : ℝ) < (J2 : ℝ) := by exact_mod_cast hJ2p
  have hJ12R : (J1 : ℝ) ≤ (J2 : ℝ) := by exact_mod_cast hJ12
  have hβc : 0 ≤ 1 / (J1 : ℝ) - 1 / (J2 : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hJ1R hJ12R)
  refine ⟨_, hmem, fun x => (if x = lo then 1 / (J2 : ℝ) else 0) +
    (if x = c then 1 / (J1 : ℝ) - 1 / (J2 : ℝ) else 0), ?_, ?_, ?_, ?_⟩
  · intro x
    have h2 : (0 : ℝ) ≤ 1 / (J2 : ℝ) := by positivity
    beta_reduce
    split_ifs <;> linarith
  · intro x hx'
    beta_reduce
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  · intro ρ
    show (∑ i ∈ Finset.range (J1 * J2), hist [r - 1 - i / J2, lo + i / J1] ρ) /
      ((J1 * J2 : ℕ) : ℝ) ≤ _
    have hR : (∑ x ∈ Finset.range (lam + 1), if x ≤ ρ then
        ((if x = lo then 1 / (J2 : ℝ) else 0) +
          (if x = c then 1 / (J1 : ℝ) - 1 / (J2 : ℝ) else 0)) else 0) =
        (if lo ≤ ρ then 1 / (J2 : ℝ) else 0) +
          (if c ≤ ρ then 1 / (J1 : ℝ) - 1 / (J2 : ℝ) else 0) := by
      rw [← sum_dl (lam + 1) ρ lo (1 / (J2 : ℝ)) (by omega),
        ← sum_dl (lam + 1) ρ c (1 / (J1 : ℝ) - 1 / (J2 : ℝ)) (by omega),
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h3 : x ≤ ρ <;> simp [h3]
    rw [hR]
    have hC1 : ((Finset.range (J1 * J2)).filter (fun i => r - 1 - i / J2 = ρ)).card ≤
        if c ≤ ρ then J2 else 0 := by
      by_cases hcρ : c ≤ ρ
      · rw [if_pos hcρ]
        refine le_trans (Finset.card_le_card ?_) (card_fib_le (J1 * J2) J2 (r - 1 - ρ) hJ2p)
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        obtain ⟨h1, h2, h3⟩ := hx i (Finset.mem_range.mp hi.1)
        obtain ⟨hi1, hi2⟩ := hi
        refine ⟨hi1, ?_⟩
        clear h2 h3
        generalize i / J2 = q2 at h1 hi2 ⊢
        omega
      · rw [if_neg hcρ, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi hne
        obtain ⟨h1, h2, h3⟩ := hx i (Finset.mem_range.mp hi)
        clear h2 h3
        generalize i / J2 = q2 at h1 hne
        omega
    have hC2 : ((Finset.range (J1 * J2)).filter (fun i => lo + i / J1 = ρ)).card ≤
        if lo ≤ ρ ∧ ρ < c then J1 else 0 := by
      by_cases hcρ : lo ≤ ρ ∧ ρ < c
      · rw [if_pos hcρ]
        refine le_trans (Finset.card_le_card ?_) (card_fib_le (J1 * J2) J1 (ρ - lo) hJ1p)
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        obtain ⟨hi1, hi2⟩ := hi
        refine ⟨hi1, ?_⟩
        generalize i / J1 = q1 at hi2 ⊢
        omega
      · rw [if_neg hcρ, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi hne
        obtain ⟨h1, h2, h3⟩ := hx i (Finset.mem_range.mp hi)
        clear h1 h3
        generalize i / J1 = q1 at h2 hne
        omega
    obtain ⟨k1, hk1⟩ : ∃ k1, k1 =
      ((Finset.range (J1 * J2)).filter (fun i => r - 1 - i / J2 = ρ)).card := ⟨_, rfl⟩
    obtain ⟨k2, hk2⟩ : ∃ k2, k2 =
      ((Finset.range (J1 * J2)).filter (fun i => lo + i / J1 = ρ)).card := ⟨_, rfl⟩
    rw [← hk1] at hC1
    rw [← hk2] at hC2
    have hsum : ∑ i ∈ Finset.range (J1 * J2), hist [r - 1 - i / J2, lo + i / J1] ρ =
        (k1 : ℝ) + (k2 : ℝ) := by
      rw [hk1, hk2, ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => hist_pair _ _ _)
    rw [hsum, Nat.cast_mul]
    by_cases h1 : c ≤ ρ
    · rw [if_pos (show lo ≤ ρ by omega), if_pos h1]
      rw [if_pos h1] at hC1
      rw [if_neg (by omega)] at hC2
      have a1 : (k1 : ℝ) ≤ (J2 : ℝ) := by exact_mod_cast hC1
      have a2 : (k2 : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp hC2
      rw [a2, add_zero]
      have e : (1 : ℝ) / J2 + (1 / J1 - 1 / J2) = (J2 : ℝ) / ((J1 : ℝ) * (J2 : ℝ)) := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right a1 (by positivity)
    · rw [if_neg h1] at hC1
      have a1 : (k1 : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp hC1
      rw [if_neg h1, add_zero, a1, zero_add]
      by_cases h2 : lo ≤ ρ
      · rw [if_pos h2]
        rw [if_pos ⟨h2, by omega⟩] at hC2
        have a2 : (k2 : ℝ) ≤ (J1 : ℝ) := by exact_mod_cast hC2
        have e : (1 : ℝ) / J2 = (J1 : ℝ) / ((J1 : ℝ) * (J2 : ℝ)) := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right a2 (by positivity)
      · rw [if_neg h2]
        rw [if_neg (by omega)] at hC2
        have a2 : (k2 : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp hC2
        rw [a2, zero_div]
  · have e' : ∀ x ∈ Finset.range (lam + 1),
        ((if x = lo then 1 / (J2 : ℝ) else 0) +
          (if x = c then 1 / (J1 : ℝ) - 1 / (J2 : ℝ) else 0)) * ((r : ℝ) ^ 2 - (x : ℝ) ^ 2) =
        (if x = lo then 1 / (J2 : ℝ) else 0) * ((r : ℝ) ^ 2 - (x : ℝ) ^ 2) +
          (if x = c then 1 / (J1 : ℝ) - 1 / (J2 : ℝ) else 0) * ((r : ℝ) ^ 2 - (x : ℝ) ^ 2) :=
      fun x _ => add_mul _ _ _
    rw [Finset.sum_congr rfl e', Finset.sum_add_distrib,
      sum_dl_mul (lam + 1) lo _ (fun x => (r : ℝ) ^ 2 - (x : ℝ) ^ 2) (by omega),
      sum_dl_mul (lam + 1) c _ (fun x => (r : ℝ) ^ 2 - (x : ℝ) ^ 2) (by omega)]
    have e1 : (J1 : ℝ) = (r : ℝ) - c := by rw [hJ1, Nat.cast_sub (by omega)]
    have e2 : (J2 : ℝ) = (c : ℝ) - lo := by rw [hJ2, Nat.cast_sub (by omega)]
    have n1 : (r : ℝ) - c ≠ 0 := by rw [← e1]; exact hJ1R.ne'
    have n2 : (c : ℝ) - lo ≠ 0 := by rw [← e2]; exact hJ2R.ne'
    rw [e1, e2]
    apply le_of_eq
    field_simp
    ring

end Frac

section Frac2

variable {V : Type} [DecidableEq V] {d : V → V → ℕ}

lemma FC_mix {S : Finset V} {r : ℕ} {f : ℕ → ℝ} (hf : f ∈ FC d S r) (n : ℕ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ a, G a ∈ FC d S r) (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a) :
    (fun ρ => (f ρ + ∑ a ∈ Finset.range n, q a * G a ρ) / (1 + ∑ a ∈ Finset.range n, q a)) ∈
      FC d S r := by
  have hconv : Convex ℝ (FC d S r) := convex_convexHull ℝ _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ a ∈ Finset.range n, q a := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg (fun a _ => hq a)
  have hQ1 : (0 : ℝ) < 1 + Q := by linarith
  rw [← hQ]
  have key := hconv.sum_mem (t := Finset.range (n + 1))
    (w := fun i => if i < n then q i / (1 + Q) else 1 / (1 + Q))
    (z := fun i => if i < n then G i else f)
    (fun i _ => by
      beta_reduce
      split_ifs
      · exact div_nonneg (hq i) hQ1.le
      · exact div_nonneg zero_le_one hQ1.le)
    (by
      beta_reduce
      rw [Finset.sum_range_succ, if_neg (lt_irrefl n)]
      have e : ∑ i ∈ Finset.range n, (if i < n then q i / (1 + Q) else 1 / (1 + Q)) =
          ∑ i ∈ Finset.range n, q i / (1 + Q) :=
        Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
      rw [e, ← Finset.sum_div, ← hQ, ← add_div]
      exact (div_eq_one_iff_eq hQ1.ne').mpr (add_comm Q 1))
    (fun i _ => by
      beta_reduce
      split_ifs
      · exact hG i
      · exact hf)
  have he : (fun ρ => (f ρ + ∑ a ∈ Finset.range n, q a * G a ρ) / (1 + Q)) =
      ∑ i ∈ Finset.range (n + 1), (if i < n then q i / (1 + Q) else 1 / (1 + Q)) •
        (if i < n then G i else f) := by
    funext ρ
    rw [Finset.sum_apply, Finset.sum_range_succ, if_neg (lt_irrefl n), if_neg (lt_irrefl n)]
    have e : ∑ i ∈ Finset.range n, ((if i < n then q i / (1 + Q) else 1 / (1 + Q)) •
        (if i < n then G i else f)) ρ = ∑ i ∈ Finset.range n, q i * G i ρ / (1 + Q) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi), if_pos (Finset.mem_range.mp hi)]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, ← Finset.sum_div]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact key

lemma Ctl.sumB {S : Finset V} {r lam m : ℕ} {w : ℝ} (hc : Ctl d S r lam m w) (hlr : lam < r) :
    ∃ f ∈ FC d S r, ∀ ρ, f ρ ≤ w / ((r : ℝ) ^ 2 - (lam : ℝ) ^ 2) := by
  obtain ⟨f, hf, β, b1, b2, b3, b4⟩ := hc
  refine ⟨f, hf, fun ρ => ?_⟩
  have hl0 : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
  have hlrR : (lam : ℝ) < (r : ℝ) := by exact_mod_cast hlr
  have hpos : (0 : ℝ) < (r : ℝ) ^ 2 - (lam : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < (r : ℝ) - (lam : ℝ) := by linarith
    have h2 : (0 : ℝ) < (r : ℝ) + (lam : ℝ) := by linarith
    nlinarith [mul_pos h1 h2]
  rw [le_div_iff₀ hpos]
  calc f ρ * ((r : ℝ) ^ 2 - (lam : ℝ) ^ 2)
      ≤ (∑ a ∈ Finset.range (lam + 1), if a ≤ ρ then β a else 0) *
          ((r : ℝ) ^ 2 - (lam : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (b3 ρ) hpos.le
    _ = ∑ a ∈ Finset.range (lam + 1), (if a ≤ ρ then β a else 0) *
          ((r : ℝ) ^ 2 - (lam : ℝ) ^ 2) := Finset.sum_mul _ _ _
    _ ≤ ∑ a ∈ Finset.range (lam + 1), β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' : (a : ℝ) ≤ (lam : ℝ) := by
          exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        have hsq : (a : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 := pow_le_pow_left₀ h0 ha' 2
        split_ifs
        · exact mul_le_mul_of_nonneg_left (by linarith) (b1 a)
        · rw [zero_mul]
          exact mul_nonneg (b1 a) (by linarith)
    _ ≤ w := b4

lemma controlled1 (h : IsTM d) {T : Finset V} (hT : Cvx d T) {r lam m : ℕ} (hlr : lam + 2 ≤ r)
    (hm : r + m ≤ 2 * lam + 2) (hmin : LMin d T (2 * lam)) (hn : 2 * lam ≤ T.card - 1) :
    Ctl d T r (lam + 1) m
      (((T.card - 1 : ℕ) : ℝ) + 2 * ((r : ℝ) - (lam : ℝ)) + 2 * (m : ℝ) + 1) := by
  obtain ⟨b, p1, p2, hb3, hb2, hTwo, hOne⟩ := two_cover h hT hmin
  obtain ⟨n, hn'⟩ : ∃ n, n = T.card - 1 := ⟨_, rfl⟩
  rw [← hn'] at hb3 hb2 hTwo hOne hn ⊢
  have hlrR : ((lam : ℝ) + 2) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hnR : (2 * (lam : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  by_cases hA : n ≤ b + 2 * (lam + 1)
  · have hc := Ctl_level (d := d) (S := T) (r := r) (lam := lam + 1) (m := m) (a := lam + 1) 1
      (by omega) le_rfl (by omega) (fun x hx1 hx2 => ⟨[(p1 x, x)], rfl, fun u hu =>
        ⟨(p1 x, x), List.mem_cons_self, hOne x (by omega) u hu⟩⟩)
    refine hc.mono ?_
    push_cast
    linarith
  · obtain ⟨s, hs⟩ : ∃ s, s = (n - b) / 2 := ⟨_, rfl⟩
    obtain ⟨c0, hc0⟩ : ∃ c0, c0 = (n + b + 3) / 4 := ⟨_, rfl⟩
    obtain ⟨lo, hlo⟩ : ∃ lo, lo = max m (s + 1 - r) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = max c0 ((r + lo + 1) / 2) := ⟨_, rfl⟩
    have hct := Ctl_two (d := d) (S := T) (r := r) (lam := lam + 1) (m := m) (lo := lo) (c := c)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun x1 x2 h1 h2 h3 h4 h5 => ⟨[(p1 x1, x1), (p2 x2, x2)], rfl, fun u hu => by
        rcases hTwo x1 x2 (by omega) (by omega) u hu with h6 | h6
        · exact ⟨(p1 x1, x1), List.mem_cons_self, h6⟩
        · exact ⟨(p2 x2, x2), List.mem_cons_of_mem _ List.mem_cons_self, h6⟩⟩)
    refine hct.mono ?_
    have hN : r + 2 * c + lo + 2 * lam ≤ n + 2 * r + 2 * m + 1 := by omega
    have hR : ((r + 2 * c + lo + 2 * lam : ℕ) : ℝ) ≤ ((n + 2 * r + 2 * m + 1 : ℕ) : ℝ) := by
      exact_mod_cast hN
    push_cast at hR
    linarith

lemma controlled2 (h : IsTM d) {r lam m : ℕ} (hlam : 1 ≤ lam) (hlr : lam + 2 ≤ r)
    (hm : r + m ≤ 2 * lam + 2) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : 2 * ((r : ℝ) - (lam : ℝ)) + 2 * (m : ℝ) + 1 ≤ 2 * (lam : ℝ) * ξ) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → Cvx d S → S.Nonempty →
      Ctl d S r (lam + 1) m (((S.card - 1 : ℕ) : ℝ) * (1 + ξ) + 4 * (r : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hSn hS hne
    have hlrR : ((lam : ℝ) + 2) ≤ (r : ℝ) := by exact_mod_cast hlr
    by_cases hsmall : S.card ≤ 2 * lam
    · have hc := Ctl_level (d := d) (S := S) (r := r) (lam := lam + 1) (m := m) (a := lam + 1) 2
        (by omega) le_rfl (by omega) (fun x hx1 hx2 => largeeps h (List.replicate 2 x) S hS hne
          (by simp) (by rw [List.sum_replicate, smul_eq_mul]; omega))
      refine hc.mono ?_
      have h2 : (0 : ℝ) ≤ ((S.card - 1 : ℕ) : ℝ) * (1 + ξ) :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      push_cast
      linarith
    · obtain ⟨S0, S1, hS0, hS1, hU, hcard, hne0, hS1c, hmin⟩ :=
        partition1 h hS (l := 2 * lam) (by omega) (by omega)
      have ih0 := ih S0.card (by omega) S0 rfl hS0 hne0
      have c1 := controlled1 h hS1 hlr hm hmin (by omega)
      have hu := Ctl.union (S := S) (by intro x hx; rw [hU]; exact hx) ih0 c1
      refine hu.mono ?_
      have e1 : (S0.card - 1) + (S1.card - 1) = S.card - 1 := by
        have := Finset.card_pos.mpr hne0
        omega
      have e2 : 2 * lam ≤ S1.card - 1 := by omega
      have e1R : ((S0.card - 1 : ℕ) : ℝ) + ((S1.card - 1 : ℕ) : ℝ) = ((S.card - 1 : ℕ) : ℝ) := by
        exact_mod_cast e1
      have e2R : 2 * (lam : ℝ) ≤ ((S1.card - 1 : ℕ) : ℝ) := by exact_mod_cast e2
      have e3 : 2 * (lam : ℝ) * ξ ≤ ((S1.card - 1 : ℕ) : ℝ) * ξ :=
        mul_le_mul_of_nonneg_right e2R hξ0
      rw [← e1R]
      nlinarith [e3, hξ]

end Frac2

section PKS

lemma step_arith (e N r B A D : ℝ) (he0 : 0 < e) (he4 : e ≤ 4) (hN : 0 < N) (hr : 0 < r)
    (hA : 0 ≤ A) (hD1 : D ≤ N * (1 + e / 4)) (hD2 : e / 8 * A ≤ D) (hD3 : D = r ^ 2 * B - A) :
    B / (1 + A / ((1 + e) * N)) ≤ (1 + e - e ^ 2 / 32) * N / r ^ 2 := by
  have h1e : 0 < 1 + e := by linarith
  have h1e' : (1 + e) ≠ 0 := h1e.ne'
  have hNe : N ≠ 0 := hN.ne'
  have hden : 0 < 1 + A / ((1 + e) * N) := by
    have : 0 ≤ A / ((1 + e) * N) := div_nonneg hA (mul_pos h1e hN).le
    linarith
  have hr2 : 0 < r ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hr2]
  have hB : B * r ^ 2 = D + A := by rw [hD3]; ring
  have hx : (1 + e - e ^ 2 / 32) * N * (1 + A / ((1 + e) * N)) =
      (1 + e - e ^ 2 / 32) * N + (1 + e - e ^ 2 / 32) * A / (1 + e) := by
    rw [mul_add, mul_one]
    congr 1
    rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero h1e' hNe) h1e']
    ring
  rw [hB, hx]
  have h2 : e ^ 2 / 32 * A ≤ e / 4 * D := by
    have h := mul_le_mul_of_nonneg_left hD2 (show (0 : ℝ) ≤ e / 4 by linarith)
    calc e ^ 2 / 32 * A = e / 4 * (e / 8 * A) := by ring
      _ ≤ e / 4 * D := h
  have h3 : (1 + 5 * e / 4) * D ≤ (1 + 5 * e / 4) * (N * (1 + e / 4)) :=
    mul_le_mul_of_nonneg_left hD1 (by linarith)
  have h4 : (1 + 5 * e / 4) * (1 + e / 4) ≤ (1 + e - e ^ 2 / 32) * (1 + e) := by
    nlinarith [mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he4), sq_nonneg e]
  have h5 := mul_le_mul_of_nonneg_right h4 hN.le
  have h6 : (1 + e) * (D + A) ≤
      (1 + e - e ^ 2 / 32) * (1 + e) * N + (1 + e - e ^ 2 / 32) * A := by
    nlinarith [h2, h3, h5]
  have h9 : D + A - (1 + e - e ^ 2 / 32) * N ≤ (1 + e - e ^ 2 / 32) * A / (1 + e) := by
    rw [le_div_iff₀ h1e]
    nlinarith [h6]
  linarith

lemma step_par (e r m L : ℝ) (he0 : 0 < e) (he4 : e ≤ 4) (hm0 : 0 ≤ m) (hr8 : 8 ≤ r)
    (hrR : 16 * (2 * m + 5) ≤ e * r) (hL1 : L ≤ (1 - e / 16) * r)
    (hL2 : (1 - e / 16) * r < L + 1) :
    L + 5 ≤ r ∧ r + m < 2 * L ∧
      2 * (r - (L - 1)) + 2 * m + 1 ≤ 2 * (L - 1) * (3 * e / 16) := by
  have her : e * r ≤ 4 * r := mul_le_mul_of_nonneg_right he4 (by linarith)
  have h1 : (1 - e / 16) * r = r - e * r / 16 := by ring
  have hL1' : L ≤ r - e * r / 16 := le_trans hL1 (le_of_eq h1)
  have hL2' : r - e * r / 16 < L + 1 := lt_of_eq_of_lt h1.symm hL2
  refine ⟨by linarith, by linarith, ?_⟩
  have h2 : r / 2 ≤ L - 1 := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 he0.le
  have h4 : 2 * (L - 1) * (3 * e / 16) = 3 / 8 * (e * (L - 1)) := by ring
  have h5 : e * (r / 2) = e * r / 2 := by ring
  rw [h4]
  rw [h5] at h3
  linarith

lemma step_delta (e r a : ℝ) (he0 : 0 < e) (he4 : e ≤ 4) (ha0 : 0 ≤ a)
    (ha : a ≤ (1 - e / 16) * r) : e / 8 * a ^ 2 ≤ r ^ 2 - a ^ 2 := by
  have hδ : (1 + e / 8) * (1 - e / 16) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg (e / 16)) (show (0 : ℝ) ≤ 3 - 2 * (e / 16) by linarith)]
  have hsq : a ^ 2 ≤ ((1 - e / 16) * r) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have h2 := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 1 + e / 8 by linarith)
  have h3 := mul_le_mul_of_nonneg_right hδ (sq_nonneg r)
  have h4 : (1 + e / 8) * ((1 - e / 16) * r) ^ 2 = (1 + e / 8) * (1 - e / 16) ^ 2 * r ^ 2 := by
    ring
  rw [h4] at h2
  linarith

def PK (K : ℝ) : Prop :=
  ∃ R C : ℕ, ∀ (V : Type) [DecidableEq V] (d : V → V → ℕ), IsTM d → ∀ r, R ≤ r →
    ∀ S : Finset V, Cvx d S → C * r + 1 ≤ S.card →
      ∃ g ∈ FC d S r, ∀ ρ, g ρ ≤ K * ((S.card - 1 : ℕ) : ℝ) / (r : ℝ) ^ 2

theorem PK_mono {K K' : ℝ} (hK : K ≤ K') (hP : PK K) : PK K' := by
  obtain ⟨R, C, hP⟩ := hP
  refine ⟨R, C, ?_⟩
  intro V _ d h r hr S hS hcard
  obtain ⟨g, hg, hgb⟩ := hP V d h r hr S hS hcard
  refine ⟨g, hg, fun ρ => le_trans (hgb ρ) ?_⟩
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)

theorem PK_base : PK 5 := by
  refine ⟨10, 4, ?_⟩
  intro V _ d h r hr S hS hcard
  obtain ⟨N, hN⟩ : ∃ N, N = S.card - 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = (r + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = N / a + 1 := ⟨_, rfl⟩
  rw [← hN]
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have ha0 : 0 < a := by omega
  have h1 := Nat.div_add_mod N a
  have h2 := Nat.mod_lt N ha0
  have h3 := Nat.div_mul_le_self N a
  have hjN : N ≤ j * a := by
    rw [hj, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  have hj1 : (j - 1) * a ≤ N := by
    rw [hj, Nat.add_sub_cancel]
    exact h3
  have hj0 : 1 ≤ j := by rw [hj]; exact Nat.le_add_left 1 _
  have hc := Ctl_level (d := d) (S := S) (r := r) (lam := a) (m := 0) (a := a) j
    (Nat.zero_le _) le_rfl (by omega) (fun x hx1 hx2 => largeeps h (List.replicate j x) S hS hne
      (by
        intro hh
        have h4 := congrArg List.length hh
        rw [List.length_replicate, List.length_nil] at h4
        omega)
      (by
        rw [List.sum_replicate, smul_eq_mul]
        have h4 := Nat.mul_le_mul_left j hx1
        omega))
  obtain ⟨f, hf, hfb⟩ := hc.sumB (by omega)
  refine ⟨f, hf, fun ρ => le_trans (hfb ρ) ?_⟩
  have hR10 : (10 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn4 : 4 * (r : ℝ) ≤ (N : ℝ) := by
    have h4 : 4 * r ≤ N := by omega
    exact_mod_cast h4
  have hx1 : (r : ℝ) ≤ 2 * (a : ℝ) := by
    have h4 : r ≤ 2 * a := by omega
    exact_mod_cast h4
  have hx2 : 2 * (a : ℝ) ≤ (r : ℝ) + 1 := by
    have h4 : 2 * a ≤ r + 1 := by omega
    exact_mod_cast h4
  have hJ1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have hJa : ((j : ℝ) - 1) * (a : ℝ) ≤ (N : ℝ) := by
    have h5 : (((j - 1 : ℕ) : ℝ)) * (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj1
    rwa [Nat.cast_sub hj0, Nat.cast_one] at h5
  have ha0R : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hpos : (0 : ℝ) < (r : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
    have h4 : (0 : ℝ) < (r : ℝ) - (a : ℝ) := by linarith
    have h5 : (0 : ℝ) < (r : ℝ) + (a : ℝ) := by linarith
    nlinarith [mul_pos h4 h5]
  have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos hr2]
  have e1 : ((j : ℝ) - 1) * (r : ℝ) ≤ 2 * (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hx1 (sub_nonneg.mpr hJ1)]
  have e2 : (j : ℝ) * (r : ℝ) ^ 2 ≤ 2 * (N : ℝ) * (r : ℝ) + (r : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right e1 (show (0 : ℝ) ≤ (r : ℝ) by linarith)]
  have e3 : 2 * (r : ℝ) ^ 2 + 5 * (N : ℝ) ≤ (N : ℝ) * (r : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn4) (show (0 : ℝ) ≤ (r : ℝ) - 5 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (r : ℝ) by linarith) (show (0 : ℝ) ≤ (r : ℝ) - 10 by linarith)]
  have e4 : (j : ℝ) * (r : ℝ) ^ 2 ≤ 5 * (N : ℝ) * ((r : ℝ) - (a : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show ((r : ℝ) - 1) / 2 ≤ (r : ℝ) - (a : ℝ) by linarith)
      (show (0 : ℝ) ≤ 5 * (N : ℝ) by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right e4 (show (0 : ℝ) ≤ (r : ℝ) + (a : ℝ) by linarith)]

theorem PK_step (e : ℝ) (he0 : 0 < e) (he4 : e ≤ 4) (hP : PK (1 + e)) :
    PK (1 + e - e ^ 2 / 32) := by
  obtain ⟨R', C', hP⟩ := hP
  obtain ⟨m, hm⟩ : ∃ m, m = max R' 1 := ⟨_, rfl⟩
  refine ⟨max 8 ⌈16 * (2 * (m : ℝ) + 5) / e⌉₊, max C' ⌈64 / e⌉₊, ?_⟩
  intro V _ d h r hr S hS hcard
  obtain ⟨N, hN⟩ : ∃ N, N = S.card - 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = max C' ⌈64 / e⌉₊ := ⟨_, rfl⟩
  rw [← hC] at hcard
  rw [← hN]
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hr8 : 8 ≤ r := le_trans (le_max_left _ _) hr
  have hrc : ⌈16 * (2 * (m : ℝ) + 5) / e⌉₊ ≤ r := le_trans (le_max_right _ _) hr
  have hrR : 16 * (2 * (m : ℝ) + 5) / e ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hrc)
  have hCC : C' ≤ C := by rw [hC]; exact le_max_left _ _
  have hCc : ⌈64 / e⌉₊ ≤ C := by rw [hC]; exact le_max_right _ _
  have hC64 : 64 / e ≤ (C : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hCc)
  have hNC : C * r ≤ N := by omega
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hr8' : (8 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr8
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hrR' : 16 * (2 * (m : ℝ) + 5) ≤ e * (r : ℝ) := by
    rw [div_le_iff₀ he0] at hrR
    linarith
  have her : e * (r : ℝ) ≤ 4 * (r : ℝ) := mul_le_mul_of_nonneg_right he4 hr0
  have hNR : (C : ℝ) * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNC
  have h64 : 64 * (r : ℝ) ≤ e * (N : ℝ) := by
    rw [div_le_iff₀ he0] at hC64
    have h1 := mul_le_mul_of_nonneg_right hC64 hr0
    have h2 := mul_le_mul_of_nonneg_left hNR he0.le
    have h3 : (C : ℝ) * e * (r : ℝ) = e * ((C : ℝ) * (r : ℝ)) := by ring
    rw [h3] at h1
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0] at h64
      linarith
  obtain ⟨L, hL⟩ : ∃ L, L = ⌊(1 - e / 16) * (r : ℝ)⌋₊ := ⟨_, rfl⟩
  have hx0 : 0 ≤ (1 - e / 16) * (r : ℝ) := mul_nonneg (by linarith) hr0
  have hL1 : (L : ℝ) ≤ (1 - e / 16) * (r : ℝ) := by rw [hL]; exact Nat.floor_le hx0
  have hL2 : (1 - e / 16) * (r : ℝ) < (L : ℝ) + 1 := by rw [hL]; exact Nat.lt_floor_add_one _
  obtain ⟨hp1, hp2, hp3⟩ := step_par e r m L he0 he4 hm0 hr8' hrR' hL1 hL2
  have hLr : L + 5 ≤ r := by exact_mod_cast hp1
  have hLm : r + m < 2 * L := by exact_mod_cast hp2
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = L - 1 := ⟨_, rfl⟩
  have hlamL : lam + 1 = L := by omega
  have hlamR : (lam : ℝ) = (L : ℝ) - 1 := by
    have h1 : (lam : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hlamL
    linarith
  have hξ : 2 * ((r : ℝ) - (lam : ℝ)) + 2 * (m : ℝ) + 1 ≤ 2 * (lam : ℝ) * (3 * e / 16) := by
    rw [hlamR]
    exact hp3
  have hc := controlled2 (r := r) (lam := lam) (m := m) (ξ := 3 * e / 16) h (by omega) (by omega)
    (by omega) (by linarith) hξ S.card S rfl hS hne
  obtain ⟨f, hf, β, b1, b2, b3, b4⟩ := hc
  rw [← hN] at b4
  have hG : ∀ a, ∃ g : ℕ → ℝ, g ∈ FC d S r ∧ (m ≤ a → a ≤ lam + 1 →
      (∀ ρ, g ρ ≤ (1 + e) * (N : ℝ) / (a : ℝ) ^ 2) ∧ ∀ ρ, a ≤ ρ → g ρ = 0) := by
    intro a
    by_cases ha : m ≤ a ∧ a ≤ lam + 1
    · have h4 := Nat.mul_le_mul hCC (show a ≤ r by omega)
      obtain ⟨g, hg, hgb⟩ := hP V d h a (by omega) S hS (by omega)
      rw [← hN] at hgb
      exact ⟨g, FC_mono (by omega) hg, fun _ _ => ⟨hgb, fun ρ hρ => FC_vanish hg hρ⟩⟩
    · exact ⟨f, hf, fun h1 h2 => absurd ⟨h1, h2⟩ ha⟩
  choose G hG1 hG2 using hG
  have h1e : (0 : ℝ) < 1 + e := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ a, q a = β a * (a : ℝ) ^ 2 / ((1 + e) * (N : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hq0 : ∀ a, 0 ≤ q a := by
    intro a
    rw [hq a]
    exact div_nonneg (mul_nonneg (b1 a) (sq_nonneg _)) (mul_pos h1e hNpos).le
  refine ⟨_, FC_mix hf (lam + 1 + 1) G hG1 q hq0, fun ρ => ?_⟩
  beta_reduce
  have hnum : f ρ + ∑ a ∈ Finset.range (lam + 1 + 1), q a * G a ρ ≤
      ∑ a ∈ Finset.range (lam + 1 + 1), β a := by
    have hterm : ∀ a ∈ Finset.range (lam + 1 + 1),
        q a * G a ρ ≤ (if a ≤ ρ then 0 else β a) := by
      intro a ha
      have ha' : a ≤ lam + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hma : m ≤ a
      · obtain ⟨g1, g2⟩ := hG2 a hma ha'
        by_cases haρ : a ≤ ρ
        · rw [if_pos haρ, g2 ρ haρ, mul_zero]
        · rw [if_neg haρ]
          have hapos : (0 : ℝ) < (a : ℝ) := by
            have h4 : 0 < a := by omega
            exact_mod_cast h4
          have ha2 : ((a : ℝ) ^ 2) ≠ 0 := (pow_pos hapos 2).ne'
          have hNe : ((1 + e) * (N : ℝ)) ≠ 0 := (mul_pos h1e hNpos).ne'
          calc q a * G a ρ ≤ q a * ((1 + e) * (N : ℝ) / (a : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left (g1 ρ) (hq0 a)
            _ = β a * ((a : ℝ) ^ 2 / (a : ℝ) ^ 2) *
                  (((1 + e) * (N : ℝ)) / ((1 + e) * (N : ℝ))) := by
                rw [hq a]; ring
            _ = β a := by rw [div_self ha2, div_self hNe, mul_one, mul_one]
      · have hβ : β a = 0 := b2 a (by omega)
        have hq' : q a = 0 := by rw [hq a, hβ, zero_mul, zero_div]
        rw [hq', zero_mul]
        split_ifs
        · exact le_rfl
        · rw [hβ]
    calc f ρ + ∑ a ∈ Finset.range (lam + 1 + 1), q a * G a ρ
        ≤ (∑ a ∈ Finset.range (lam + 1 + 1), if a ≤ ρ then β a else 0) +
            ∑ a ∈ Finset.range (lam + 1 + 1), (if a ≤ ρ then 0 else β a) :=
          add_le_add (b3 ρ) (Finset.sum_le_sum hterm)
      _ = ∑ a ∈ Finset.range (lam + 1 + 1), β a := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ a ∈ Finset.range (lam + 1 + 1), β a := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ a ∈ Finset.range (lam + 1 + 1), β a * (a : ℝ) ^ 2 := ⟨_, rfl⟩
  have hQA : ∑ a ∈ Finset.range (lam + 1 + 1), q a = A / ((1 + e) * (N : ℝ)) := by
    rw [hA, Finset.sum_div]
    exact Finset.sum_congr rfl (fun a _ => hq a)
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (b1 a) (sq_nonneg _))
  have hden : 0 < 1 + A / ((1 + e) * (N : ℝ)) := by
    have h4 : 0 ≤ A / ((1 + e) * (N : ℝ)) := div_nonneg hA0 (mul_pos h1e hNpos).le
    linarith
  have hD1 : ∑ a ∈ Finset.range (lam + 1 + 1), β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + e / 4) := by
    have h5 : (N : ℝ) * (1 + 3 * e / 16) + 4 * (r : ℝ) ≤ (N : ℝ) * (1 + e / 4) := by
      have h6 : (N : ℝ) * (1 + e / 4) - (N : ℝ) * (1 + 3 * e / 16) = e * (N : ℝ) / 16 := by ring
      linarith
    exact le_trans b4 h5
  have hD2 : e / 8 * A ≤
      ∑ a ∈ Finset.range (lam + 1 + 1), β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
    rw [hA, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have ha' : a ≤ L := by
      have h4 := Finset.mem_range.mp ha
      omega
    have haR : (a : ℝ) ≤ (1 - e / 16) * (r : ℝ) := le_trans (by exact_mod_cast ha') hL1
    have h4 := step_delta e r a he0 he4 (Nat.cast_nonneg a) haR
    calc e / 8 * (β a * (a : ℝ) ^ 2) = β a * (e / 8 * (a : ℝ) ^ 2) := by ring
      _ ≤ β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h4 (b1 a)
  have hD3 : ∑ a ∈ Finset.range (lam + 1 + 1), β a * ((r : ℝ) ^ 2 - (a : ℝ) ^ 2) =
      (r : ℝ) ^ 2 * B - A := by
    rw [hB, hA, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hQA]
  refine le_trans (div_le_div_of_nonneg_right hnum hden.le) ?_
  rw [← hB]
  exact step_arith e N r B A _ he0 he4 hNpos (by linarith) hA0 hD1 hD2 hD3

theorem PK_seq (n : ℕ) : PK (1 + 32 / ((n : ℝ) + 8)) := by
  induction n with
  | zero =>
    have h0 : (1 : ℝ) + 32 / (((0 : ℕ) : ℝ) + 8) = 5 := by norm_num
    rw [h0]
    exact PK_base
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h8 : (0 : ℝ) < (n : ℝ) + 8 := by linarith
    have h9 : (0 : ℝ) < (n : ℝ) + 1 + 8 := by linarith
    have he0 : (0 : ℝ) < 32 / ((n : ℝ) + 8) := div_pos (by norm_num) h8
    have he4 : 32 / ((n : ℝ) + 8) ≤ 4 := by
      rw [div_le_iff₀ h8]
      linarith
    have hs := PK_step _ he0 he4 ih
    refine PK_mono ?_ hs
    push_cast
    have e1 : (32 / ((n : ℝ) + 8)) ^ 2 / 32 = 32 / ((n : ℝ) + 8) ^ 2 := by
      rw [div_pow, div_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    have e2 : 32 / ((n : ℝ) + 8) - 32 / ((n : ℝ) + 8) ^ 2 ≤ 32 / ((n : ℝ) + 1 + 8) := by
      rw [div_sub_div _ _ h8.ne' (pow_pos h8 2).ne', div_le_div_iff₀ (by positivity) h9]
      nlinarith [sq_nonneg ((n : ℝ) + 8), pow_pos h8 3]
    rw [e1]
    linarith

theorem PK_all (η : ℝ) (hη : 0 < η) : PK (1 + η) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (32 / η)
  refine PK_mono ?_ (PK_seq n)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 32 / ((n : ℝ) + 8) ≤ η := by
    rw [div_le_iff₀ (by linarith)]
    rw [div_lt_iff₀ hη] at hn
    nlinarith
  linarith

end PKS


/-! ### Part D: from fractional covers to a burning sequence -/

section Round

lemma rounding {V : Type} [DecidableEq V] (d : V → V → ℕ) (c0 : V) :
    ∀ (k : ℕ) (bs : List (V × ℕ)),
      (∀ t, bs.countP (fun b => decide (t ≤ b.2)) ≤ k - t) →
      ∃ c : ℕ → V, ∀ v, (∃ b ∈ bs, d b.1 v ≤ b.2) → ∃ i, i < k ∧ d (c i) v ≤ i := by
  intro k
  induction k with
  | zero =>
    intro bs hcnt
    refine ⟨fun _ => c0, ?_⟩
    rintro v ⟨b, hb, _⟩
    exfalso
    have h0 := hcnt 0
    have hpos : 0 < bs.countP (fun b => decide (0 ≤ b.2)) :=
      List.countP_pos_iff.mpr ⟨b, hb, by simp⟩
    omega
  | succ k ih =>
    intro bs hcnt
    by_cases hbs : bs = []
    · refine ⟨fun _ => c0, ?_⟩
      rintro v ⟨b, hb, _⟩
      rw [hbs] at hb
      exact absurd hb List.not_mem_nil
    · obtain ⟨b0, hb0⟩ := List.exists_mem_of_ne_nil bs hbs
      obtain ⟨bm, hbm, hmax⟩ := bs.toFinset.exists_max_image (fun b => b.2)
        ⟨b0, List.mem_toFinset.mpr hb0⟩
      have hbm' : bm ∈ bs := List.mem_toFinset.mp hbm
      have hmax' : ∀ b ∈ bs, b.2 ≤ bm.2 := fun b hb => hmax b (List.mem_toFinset.mpr hb)
      have hperm := List.perm_cons_erase hbm'
      have hc : ∀ t, bs.countP (fun b => decide (t ≤ b.2)) =
          (bs.erase bm).countP (fun b => decide (t ≤ b.2)) + (if t ≤ bm.2 then 1 else 0) := by
        intro t
        rw [List.Perm.countP_eq _ hperm, List.countP_cons]
        simp
      have hbmk : bm.2 ≤ k := by
        have h1 := hcnt bm.2
        have h2 := hc bm.2
        rw [if_pos le_rfl] at h2
        omega
      have hcnt' : ∀ t, (bs.erase bm).countP (fun b => decide (t ≤ b.2)) ≤ k - t := by
        intro t
        by_cases ht : t ≤ bm.2
        · have h1 := hcnt t
          have h2 := hc t
          rw [if_pos ht] at h2
          omega
        · have h0 : (bs.erase bm).countP (fun b => decide (t ≤ b.2)) = 0 := by
            rw [List.countP_eq_zero]
            intro b hb
            have h3 := hmax' b (List.mem_of_mem_erase hb)
            simp only [decide_eq_true_eq]
            omega
          omega
      obtain ⟨c', hc'⟩ := ih (bs.erase bm) hcnt'
      refine ⟨Function.update c' k bm.1, ?_⟩
      rintro v ⟨b, hb, hbv⟩
      by_cases hbb : b = bm
      · refine ⟨k, Nat.lt_succ_self k, ?_⟩
        rw [Function.update_self]
        rw [hbb] at hbv
        omega
      · obtain ⟨i, hi, hiv⟩ := hc' v ⟨b, (List.mem_erase_of_ne hbb).mpr hb, hbv⟩
        have hik : i ≠ k := by omega
        refine ⟨i, by omega, ?_⟩
        rw [Function.update_of_ne hik]
        exact hiv

lemma round_tail {V : Type} [DecidableEq V] (d : V → V → ℕ) (c0 : V) (k r w B E : ℕ)
    (hw : 1 ≤ w) (hk : r + w + E ≤ k) (hB : r ≤ B * w) (bs : List (V × ℕ))
    (hr : ∀ b ∈ bs, b.2 < r)
    (hH : ∀ j, j < B → bs.countP (fun b => decide (j * w ≤ b.2)) ≤ r - j * w + E) :
    ∃ c : ℕ → V, ∀ v, (∃ b ∈ bs, d b.1 v ≤ b.2) → ∃ i, i < k ∧ d (c i) v ≤ i := by
  apply rounding d c0 k bs
  intro t
  by_cases ht : t < r
  · have hj : t / w < B := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have h1 := hH (t / w) hj
    have h2 : t / w * w ≤ t := Nat.div_mul_le_self t w
    have h3 : t < t / w * w + w := Nat.lt_div_mul_add (by omega)
    have h4 : bs.countP (fun b => decide (t ≤ b.2)) ≤
        bs.countP (fun b => decide (t / w * w ≤ b.2)) := by
      apply List.countP_mono_left
      intro b _ hb
      simp only [decide_eq_true_eq] at hb ⊢
      omega
    generalize t / w * w = q at h1 h2 h3 h4
    omega
  · have h0 : bs.countP (fun b => decide (t ≤ b.2)) = 0 := by
      rw [List.countP_eq_zero]
      intro b hb
      have h3 := hr b hb
      simp only [decide_eq_true_eq]
      omega
    omega

lemma hist_nonneg (rs : List ℕ) (ρ : ℕ) : 0 ≤ hist rs ρ := Nat.cast_nonneg _

lemma tail_count {V : Type} (bs : List (V × ℕ)) (a r : ℕ) (hr : ∀ b ∈ bs, b.2 < r) :
    ∑ ρ ∈ Finset.Ico a r, hist (bs.map Prod.snd) ρ =
      (bs.countP (fun b => decide (a ≤ b.2)) : ℝ) := by
  induction bs with
  | nil => simp [hist]
  | cons b bs ih =>
    have hx : b.2 < r := hr b List.mem_cons_self
    have ih' := ih (fun y hy => hr y (List.mem_cons_of_mem _ hy))
    have h1 : ∀ ρ, hist ((b :: bs).map Prod.snd) ρ =
        hist (bs.map Prod.snd) ρ + (if b.2 = ρ then 1 else 0) := by
      intro ρ
      by_cases hxρ : b.2 = ρ <;> simp [hist, List.count_cons, hxρ]
    rw [Finset.sum_congr rfl (fun ρ _ => h1 ρ), Finset.sum_add_distrib, ih', List.countP_cons,
      Finset.sum_ite_eq]
    by_cases hax : a ≤ b.2
    · simp [hax, hx]
    · simp [hax]

noncomputable def tailL (B w r : ℕ) : (ℕ → ℝ) →ₗ[ℝ] (Fin B → ℝ) where
  toFun f := fun j => ∑ ρ ∈ Finset.Ico (j.val * w) r, f ρ
  map_add' := by
    intro f g
    funext j
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext j
    simp [Finset.mul_sum]

lemma tailL_apply (B w r : ℕ) (f : ℕ → ℝ) (j : Fin B) :
    tailL B w r f j = ∑ ρ ∈ Finset.Ico (j.val * w) r, f ρ := rfl

lemma concat_lists {ι α : Type} [DecidableEq ι] (I : Finset ι) (cov : ι → List α) :
    ∃ bs : List α, (∀ i ∈ I, ∀ b ∈ cov i, b ∈ bs) ∧ (∀ b ∈ bs, ∃ i ∈ I, b ∈ cov i) ∧
      ∀ p : α → Bool, bs.countP p = ∑ i ∈ I, (cov i).countP p := by
  induction I using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨bs, h1, h2, h3⟩ := ih
    refine ⟨cov a ++ bs, ?_, ?_, ?_⟩
    · intro i hi b hb
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact List.mem_append_left _ hb
      · exact List.mem_append_right _ (h1 i hi b hb)
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨a, Finset.mem_insert_self a s, hb⟩
      · obtain ⟨i, hi, hbi⟩ := h2 b hb
        exact ⟨i, Finset.mem_insert_of_mem hi, hbi⟩
    · intro p
      rw [List.countP_append, h3 p, Finset.sum_insert ha]

lemma tail_bound (m : ℕ) (g : Fin m → ℕ → ℝ) (nn : Fin m → ℕ) (η : ℝ) (r a N : ℕ) (hr : 0 < r)
    (hg : ∀ i ρ, g i ρ ≤ (1 + η) * (nn i : ℝ) / (r : ℝ) ^ 2) (hsum : ∑ i, nn i = N)
    (harea : (1 + η) * (N : ℝ) ≤ (r : ℝ) ^ 2) :
    ∑ i, ∑ ρ ∈ Finset.Ico a r, g i ρ ≤ ((r - a : ℕ) : ℝ) := by
  have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have h1 : ∀ i, ∑ ρ ∈ Finset.Ico a r, g i ρ ≤
      ((r - a : ℕ) : ℝ) * ((1 + η) * (nn i : ℝ) / (r : ℝ) ^ 2) := by
    intro i
    have h2 := Finset.sum_le_card_nsmul (Finset.Ico a r) (g i) _ (fun ρ _ => hg i ρ)
    rw [Nat.card_Ico, nsmul_eq_mul] at h2
    exact h2
  calc ∑ i, ∑ ρ ∈ Finset.Ico a r, g i ρ
      ≤ ∑ i, ((r - a : ℕ) : ℝ) * ((1 + η) * (nn i : ℝ) / (r : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = ((r - a : ℕ) : ℝ) * ((1 + η) * (N : ℝ) / (r : ℝ) ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, ← hsum, Nat.cast_sum]
    _ ≤ ((r - a : ℕ) : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [div_le_one hr2]
        exact harea
    _ = ((r - a : ℕ) : ℝ) := mul_one _

lemma bad_arith (C1 r n : ℕ) (hr : 2 ≤ r) (hn : n ≤ 3 * (C1 * r)) :
    n - 1 ≤ 6 * C1 * (r - 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  have e1 : C1 * (r' + 2) = C1 * r' + 2 * C1 := by ring
  have e2 : 6 * C1 * (r' + 2 - 1) = 6 * (C1 * r') + 6 * C1 := by
    have e3 : r' + 2 - 1 = r' + 1 := by omega
    rw [e3]
    ring
  rw [e2]
  rw [e1] at hn
  omega

lemma cover_par (η : ℝ) (hη0 : 0 < η) (hη4 : η ≤ 1 / 4) (R1 E B : ℕ) (hB : 4 / η ≤ (B : ℝ))
    (k : ℕ) (hk1 : 4 * ((E : ℝ) + 1) / η ≤ (k : ℝ)) (hk2 : 2 * R1 ≤ k) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 - 4 * η) * (k : ℝ) ^ 2) :
    ∃ w r : ℕ, 1 ≤ w ∧ r + w + E ≤ k ∧ r ≤ B * w ∧ R1 ≤ r ∧
      (1 + η) * ((n - 1 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg E
  have hk1' : 4 * ((E : ℝ) + 1) ≤ (k : ℝ) * η := (div_le_iff₀ hη0).mp hk1
  have hkpos : (0 : ℝ) < (k : ℝ) := by nlinarith
  obtain ⟨w, hwdef⟩ : ∃ w : ℕ, w = ⌈η * (k : ℝ) / 4⌉₊ := ⟨_, rfl⟩
  have hw1 : η * (k : ℝ) / 4 ≤ (w : ℝ) := by rw [hwdef]; exact Nat.le_ceil _
  have hw2 : (w : ℝ) < η * (k : ℝ) / 4 + 1 := by
    rw [hwdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hwE : (w : ℝ) + (E : ℝ) ≤ η * (k : ℝ) / 2 := by linarith
  have hle : w + E ≤ k := by
    have h1 : (w : ℝ) + (E : ℝ) ≤ (k : ℝ) := by nlinarith
    exact_mod_cast h1
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  have hrR : (k : ℝ) = (w : ℝ) + (E : ℝ) + (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 - η / 2) * (k : ℝ) ≤ (r : ℝ) := by linarith
  refine ⟨w, r, ?_, by omega, ?_, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (w : ℝ) := by linarith
    exact_mod_cast h1
  · have h1 : (4 / η) * (η * (k : ℝ) / 4) ≤ (B : ℝ) * (w : ℝ) :=
      mul_le_mul hB hw1 (by positivity) (le_trans (by positivity) hB)
    have h2 : (4 / η) * (η * (k : ℝ) / 4) = (k : ℝ) := by field_simp
    have h3 : (r : ℝ) ≤ ((B * w : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  · have h1 : (2 : ℝ) * (R1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have h2 : (R1 : ℝ) ≤ (r : ℝ) := by nlinarith
    exact_mod_cast h2
  · have h1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
    have h2 : ((1 - η / 2) * (k : ℝ)) ^ 2 ≤ (r : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) hr1 2
    have h3 : (1 + η) * ((1 - 4 * η) * (k : ℝ) ^ 2) ≤ ((1 - η / 2) * (k : ℝ)) ^ 2 := by
      have h4 : 0 ≤ (2 * η + 17 / 4 * η ^ 2) * (k : ℝ) ^ 2 := by positivity
      nlinarith [h4]
    have h5 : (1 + η) * ((n - 1 : ℕ) : ℝ) ≤ (1 + η) * ((1 - 4 * η) * (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans h1 hn) (by linarith)
    linarith

end Round

section SF

theorem shapley_folkman {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (C : Fin m → Set E) (x : Fin m → E) (hx : ∀ i, x i ∈ convexHull ℝ (C i)) :
    ∃ y : Fin m → E, (∀ i, y i ∈ convexHull ℝ (C i)) ∧ ∑ i, y i = ∑ i, x i ∧
      ∃ bad : Finset (Fin m), bad.card ≤ Module.finrank ℝ E + 1 ∧
        ∀ i, i ∉ bad → y i ∈ C i := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨x, hx, rfl, ∅, by simp, fun i => i.elim0⟩
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmm : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  obtain ⟨Z, hZ⟩ : ∃ Z : Set (E × (Fin m → ℝ)),
      Z = {q | ∃ i, q.1 ∈ C i ∧ q.2 = Pi.single i 1} := ⟨_, rfl⟩
  have hlift : ∀ i, (x i, (Pi.single i 1 : Fin m → ℝ)) ∈ convexHull ℝ Z := by
    intro i
    have hsub : C i ⊆ {e : E | (e, (Pi.single i 1 : Fin m → ℝ)) ∈ convexHull ℝ Z} := by
      intro e he
      apply subset_convexHull ℝ Z
      rw [hZ]
      exact ⟨i, he, rfl⟩
    have hconv : Convex ℝ {e : E | (e, (Pi.single i 1 : Fin m → ℝ)) ∈ convexHull ℝ Z} := by
      intro e1 he1 e2 he2 a b ha hb hab
      have h := (convex_convexHull ℝ Z) he1 he2 ha hb hab
      have heq : a • (e1, (Pi.single i 1 : Fin m → ℝ)) + b • (e2, (Pi.single i 1 : Fin m → ℝ)) =
          (a • e1 + b • e2, (Pi.single i 1 : Fin m → ℝ)) := by
        refine Prod.ext ?_ ?_
        · simp
        · simp only [Prod.snd_add, Prod.smul_snd]
          rw [← add_smul, hab, one_smul]
      show (a • e1 + b • e2, (Pi.single i 1 : Fin m → ℝ)) ∈ convexHull ℝ Z
      rw [← heq]
      exact h
    exact convexHull_min hsub hconv (hx i)
  have hP : ∑ i : Fin m, (1 / (m : ℝ)) • (x i, (Pi.single i 1 : Fin m → ℝ)) ∈
      convexHull ℝ Z := by
    apply (convex_convexHull ℝ Z).sum_mem
    · intro i _
      positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact hmm
    · intro i _
      exact hlift i
  obtain ⟨ι, hι, z, w, hz, hai, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hP
  have hzZ : ∀ p, ∃ i, (z p).1 ∈ C i ∧ (z p).2 = Pi.single i 1 := by
    intro p
    have h1 := hz (Set.mem_range_self p)
    rw [hZ] at h1
    exact h1
  choose idx hidx1 hidx2 using hzZ
  have hsnd : ∀ i : Fin m, ∑ p ∈ Finset.univ.filter (fun p => idx p = i), w p = 1 / (m : ℝ) := by
    intro i
    have hL : (∑ p, w p • z p).2 i = ∑ p ∈ Finset.univ.filter (fun p => idx p = i), w p := by
      rw [Prod.snd_sum, Finset.sum_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Prod.smul_snd, Pi.smul_apply, hidx2 p, smul_eq_mul]
      by_cases h : idx p = i
      · rw [if_pos h, h, Pi.single_eq_same, mul_one]
      · rw [if_neg h, Pi.single_eq_of_ne (fun h' => h h'.symm), mul_zero]
    have hR : (∑ i' : Fin m, (1 / (m : ℝ)) • (x i', (Pi.single i' 1 : Fin m → ℝ))).2 i =
        1 / (m : ℝ) := by
      rw [Prod.snd_sum, Finset.sum_apply, Finset.sum_eq_single i]
      · show (1 / (m : ℝ)) • (Pi.single i 1 : Fin m → ℝ) i = 1 / (m : ℝ)
        rw [Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        show (1 / (m : ℝ)) • (Pi.single b 1 : Fin m → ℝ) i = 0
        rw [Pi.single_eq_of_ne (fun h' => hb h'.symm), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← hL, hsum, hR]
  have hne : ∀ i : Fin m, 1 ≤ (Finset.univ.filter (fun p => idx p = i)).card := by
    intro i
    by_contra hcon
    have h0 : Finset.univ.filter (fun p => idx p = i) = ∅ := by
      rw [← Finset.card_eq_zero]
      omega
    have h1 := hsnd i
    rw [h0, Finset.sum_empty] at h1
    have h2 : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  obtain ⟨y, hy⟩ : ∃ y : Fin m → E, y = fun i =>
      ∑ p ∈ Finset.univ.filter (fun p => idx p = i), ((m : ℝ) * w p) • (z p).1 := ⟨_, rfl⟩
  have hyi : ∀ i, y i =
      ∑ p ∈ Finset.univ.filter (fun p => idx p = i), ((m : ℝ) * w p) • (z p).1 := by
    intro i
    rw [hy]
  refine ⟨y, ?_, ?_,
    Finset.univ.filter (fun i => 2 ≤ (Finset.univ.filter (fun p => idx p = i)).card), ?_, ?_⟩
  · intro i
    rw [hyi]
    apply (convex_convexHull ℝ (C i)).sum_mem
    · intro p _
      exact (mul_pos hmR (hw0 p)).le
    · rw [← Finset.mul_sum, hsnd i]
      exact hmm
    · intro p hp
      have hpi : idx p = i := (Finset.mem_filter.mp hp).2
      rw [← hpi]
      exact subset_convexHull ℝ _ (hidx1 p)
  · have hfst : ∑ p, w p • (z p).1 = (1 / (m : ℝ)) • ∑ i, x i := by
      have h1 := congrArg Prod.fst hsum
      rw [Prod.fst_sum, Prod.fst_sum] at h1
      rw [Finset.smul_sum]
      exact h1
    calc ∑ i, y i
        = ∑ i, ∑ p ∈ Finset.univ.filter (fun p => idx p = i), ((m : ℝ) * w p) • (z p).1 :=
          Finset.sum_congr rfl (fun i _ => hyi i)
      _ = ∑ p, ((m : ℝ) * w p) • (z p).1 := Finset.sum_fiberwise _ _ _
      _ = (m : ℝ) • ∑ p, w p • (z p).1 := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [mul_smul]
      _ = ∑ i, x i := by
          rw [hfst, smul_smul, hmm, one_smul]
  · have hcard1 : Fintype.card ι =
        ∑ i : Fin m, (Finset.univ.filter (fun p => idx p = i)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (idx p))
    have hcard2 : ∑ i : Fin m,
        (1 + if 2 ≤ (Finset.univ.filter (fun p => idx p = i)).card then 1 else 0) ≤
        ∑ i : Fin m, (Finset.univ.filter (fun p => idx p = i)).card := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 := hne i
      split_ifs <;> omega
    have hcard3 : ∑ i : Fin m,
        (1 + if 2 ≤ (Finset.univ.filter (fun p => idx p = i)).card then 1 else 0) =
        m + (Finset.univ.filter
          (fun i : Fin m => 2 ≤ (Finset.univ.filter (fun p => idx p = i)).card)).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one, Finset.card_filter]
    have hcard4 : Fintype.card ι ≤ Module.finrank ℝ E + m + 1 := by
      have h1 := hai.card_le_finrank_succ
      have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      have h3 : Module.finrank ℝ (E × (Fin m → ℝ)) = Module.finrank ℝ E + m := by
        rw [Module.finrank_prod, Module.finrank_fin_fun]
      omega
    omega
  · intro i hi
    have hlt : (Finset.univ.filter (fun p => idx p = i)).card = 1 := by
      have h1 := hne i
      have h2 : ¬ 2 ≤ (Finset.univ.filter (fun p => idx p = i)).card := by
        intro h
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hlt
    have hw : w p = 1 / (m : ℝ) := by
      have h1 := hsnd i
      rw [hp, Finset.sum_singleton] at h1
      exact h1
    have hpi : idx p = i := by
      have h1 : p ∈ Finset.univ.filter (fun p => idx p = i) := by
        rw [hp]
        exact Finset.mem_singleton_self p
      exact (Finset.mem_filter.mp h1).2
    rw [hyi, hp, Finset.sum_singleton, hw, hmm, one_smul, ← hpi]
    exact hidx1 p

end SF

section IntCover

theorem int_cover (η : ℝ) (hη0 : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℕ), IsTM d →
      Nonempty V → (Fintype.card V : ℝ) ≤ (1 - 4 * η) * (k : ℝ) ^ 2 →
      ∃ c : ℕ → V, ∀ v, ∃ i, i < k ∧ d (c i) v ≤ i := by
  obtain ⟨R, C, hP⟩ := PK_all η hη0
  obtain ⟨C1, hC1⟩ : ∃ C1, C1 = max C 1 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = max R 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ⌈4 / η⌉₊ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = 6 * C1 * (B + 1) := ⟨_, rfl⟩
  refine ⟨max ⌈4 * ((E : ℝ) + 1) / η⌉₊ (2 * R1), ?_⟩
  intro k hk V _ _ d h hV hn
  have hBR : 4 / η ≤ (B : ℝ) := by rw [hB]; exact Nat.le_ceil _
  have hk1 : 4 * ((E : ℝ) + 1) / η ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hk)
  have hk2 : 2 * R1 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨w, r, hw1, hkr, hrB, hrR1, harea⟩ :=
    cover_par η hη0 hη4 R1 E B hBR k hk1 hk2 (Fintype.card V) hn
  have hrR : R ≤ r := le_trans (by rw [hR1]; exact le_max_left _ _) hrR1
  have hr2 : 2 ≤ r := le_trans (by rw [hR1]; exact le_max_right _ _) hrR1
  have hCC : C ≤ C1 := by rw [hC1]; exact le_max_left _ _
  have hC1' : 1 ≤ C1 := by rw [hC1]; exact le_max_right _ _
  have h6E : 6 * C1 ≤ E := by rw [hE]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos B)
  have hcu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  obtain ⟨c0⟩ := hV
  have hcvx : Cvx d (Finset.univ : Finset V) := fun _ _ _ _ _ _ => Finset.mem_univ _
  suffices hbs : ∃ bs : List (V × ℕ), (∀ b ∈ bs, b.2 < r) ∧ (∀ v, ∃ b ∈ bs, d b.1 v ≤ b.2) ∧
      ∀ j, j < B → bs.countP (fun b => decide (j * w ≤ b.2)) ≤ r - j * w + E by
    obtain ⟨bs, hbr, hbc, hbH⟩ := hbs
    obtain ⟨c, hc⟩ := round_tail d c0 k r w B E hw1 hkr hrB bs hbr hbH
    exact ⟨c, fun v => hc v (hbc v)⟩
  have hrep : List.replicate (6 * C1) (r - 1) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_replicate]; omega)
  by_cases hsmall : C1 * r + 1 ≤ (Finset.univ : Finset V).card
  swap
  · have hcard : (Finset.univ : Finset V).card ≤ 3 * (C1 * r) := by omega
    obtain ⟨bs, hmap, hcov⟩ := largeeps h (List.replicate (6 * C1) (r - 1)) Finset.univ hcvx
      ⟨c0, Finset.mem_univ c0⟩ hrep
      (by rw [List.sum_replicate, smul_eq_mul]; exact bad_arith C1 r _ hr2 hcard)
    have hrad : ∀ b ∈ bs, b.2 = r - 1 := by
      intro b hb
      have hb' : b.2 ∈ bs.map Prod.snd := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [hmap] at hb'
      exact List.eq_of_mem_replicate hb'
    have hlen : bs.length = 6 * C1 := by
      have h1 := congrArg List.length hmap
      rw [List.length_map, List.length_replicate] at h1
      exact h1
    refine ⟨bs, ?_, ?_, ?_⟩
    · intro b hb
      rw [hrad b hb]
      omega
    · intro v
      exact hcov v (Finset.mem_univ v)
    · intro j _
      have h1 := List.countP_le_length (p := fun b : V × ℕ => decide (j * w ≤ b.2)) (l := bs)
      omega
  · have hl : 1 ≤ C1 * r := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    obtain ⟨Ts, hTs1, hTs2, hTs3⟩ := partition3 h hl _ Finset.univ rfl hcvx hsmall
    rw [hcu] at hTs3
    obtain ⟨T, hTdef⟩ : ∃ T : Fin Ts.length → Finset V, T = fun i => Ts[i.1] := ⟨_, rfl⟩
    have hTmem : ∀ i, T i ∈ Ts := by
      intro i
      rw [hTdef]
      exact List.getElem_mem i.2
    have hTex : ∀ T' ∈ Ts, ∃ i, T i = T' := by
      intro T' hT'
      obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hT'
      exact ⟨⟨i, hi⟩, by rw [hTdef]; exact hiT⟩
    have hTsum : ∑ i : Fin Ts.length, ((T i).card - 1) = Fintype.card V - 1 := by
      rw [hTdef, ← hTs3]
      exact Fin.sum_univ_fun_getElem Ts (fun T => T.card - 1)
    have hpiece : ∀ i : Fin Ts.length, ∃ g ∈ FC d (T i) r,
        ∀ ρ, g ρ ≤ (1 + η) * (((T i).card - 1 : ℕ) : ℝ) / (r : ℝ) ^ 2 := by
      intro i
      obtain ⟨hT1, hT2, hT3⟩ := hTs1 (T i) (hTmem i)
      have h1 := Nat.mul_le_mul_right r hCC
      exact hP V d h r hrR (T i) hT1 (by omega)
    choose g hg1 hg2 using hpiece
    obtain ⟨y, hy1, hy2, bad, hbad, hgood⟩ := shapley_folkman
      (fun i : Fin Ts.length => (tailL B w r) '' CVr d (T i) r)
      (fun i => tailL B w r (g i)) (by
        intro i
        show tailL B w r (g i) ∈ convexHull ℝ ((tailL B w r) '' CVr d (T i) r)
        rw [← LinearMap.image_convexHull]
        exact Set.mem_image_of_mem _ (hg1 i))
    have hbad' : bad.card ≤ B + 1 := by
      have h1 : Module.finrank ℝ (Fin B → ℝ) = B := Module.finrank_fin_fun ℝ
      omega
    have hcovex : ∀ i : Fin Ts.length, ∃ cv : List (V × ℕ), Cov d (T i) cv ∧
        (∀ b ∈ cv, b.2 < r) ∧
        ∀ j : Fin B, (cv.countP (fun b => decide (j.val * w ≤ b.2)) : ℝ) ≤
          y i j + (if i ∈ bad then ((6 * C1 : ℕ) : ℝ) else 0) := by
      intro i
      obtain ⟨hT1, hT2, hT3⟩ := hTs1 (T i) (hTmem i)
      by_cases hi : i ∈ bad
      · have hTne : (T i).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨cv, hmap, hcov⟩ := largeeps h (List.replicate (6 * C1) (r - 1)) (T i) hT1 hTne
          hrep (by rw [List.sum_replicate, smul_eq_mul]; exact bad_arith C1 r _ hr2 hT3)
        have hrad : ∀ b ∈ cv, b.2 = r - 1 := by
          intro b hb
          have hb' : b.2 ∈ cv.map Prod.snd := List.mem_map.mpr ⟨b, hb, rfl⟩
          rw [hmap] at hb'
          exact List.eq_of_mem_replicate hb'
        have hlen : cv.length = 6 * C1 := by
          have h1 := congrArg List.length hmap
          rw [List.length_map, List.length_replicate] at h1
          exact h1
        refine ⟨cv, hcov, fun b hb => by rw [hrad b hb]; omega, ?_⟩
        intro j
        rw [if_pos hi]
        have h1 : (cv.countP (fun b => decide (j.val * w ≤ b.2)) : ℝ) ≤ ((6 * C1 : ℕ) : ℝ) := by
          rw [← hlen]
          exact_mod_cast List.countP_le_length
        have h2 : 0 ≤ y i j := by
          have hsub : (tailL B w r) '' CVr d (T i) r ⊆ {v : Fin B → ℝ | 0 ≤ v j} := by
            rintro _ ⟨f, ⟨bs, _, _, rfl⟩, rfl⟩
            show 0 ≤ tailL B w r (hist (bs.map Prod.snd)) j
            rw [tailL_apply]
            exact Finset.sum_nonneg (fun ρ _ => hist_nonneg _ ρ)
          have hconv : Convex ℝ {v : Fin B → ℝ | 0 ≤ v j} := by
            intro u hu v hv a b ha hb _
            have hu' : 0 ≤ u j := hu
            have hv' : 0 ≤ v j := hv
            show 0 ≤ (a • u + b • v) j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            exact add_nonneg (mul_nonneg ha hu') (mul_nonneg hb hv')
          exact convexHull_min hsub hconv (hy1 i)
        linarith
      · obtain ⟨f, ⟨cv, hcov, hlt, rfl⟩, hfy⟩ := hgood i hi
        refine ⟨cv, hcov, hlt, ?_⟩
        intro j
        exact le_of_eq (by
          rw [if_neg hi, add_zero, ← hfy, tailL_apply, tail_count cv _ r hlt])
    choose cov hcov1 hcov2 hcov3 using hcovex
    obtain ⟨bs, hbs1, hbs2, hbs3⟩ := concat_lists (Finset.univ : Finset (Fin Ts.length)) cov
    refine ⟨bs, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨i, _, hbi⟩ := hbs2 b hb
      exact hcov2 i b hbi
    · intro v
      obtain ⟨T', hT', hvT⟩ := (hTs2 v).mp (Finset.mem_univ v)
      obtain ⟨i, rfl⟩ := hTex T' hT'
      obtain ⟨b, hb, hbv⟩ := hcov1 i v hvT
      exact ⟨b, hbs1 i (Finset.mem_univ i) b hb, hbv⟩
    · intro j hj
      have e1 : (∑ i, y i) ⟨j, hj⟩ = ∑ i, ∑ ρ ∈ Finset.Ico (j * w) r, g i ρ := by
        rw [hy2, Finset.sum_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rfl
      have h1 := tail_bound Ts.length g (fun i => (T i).card - 1) η r (j * w)
        (Fintype.card V - 1) (by omega) hg2 hTsum harea
      have h2 : (bad.card : ℝ) * ((6 * C1 : ℕ) : ℝ) ≤ (E : ℝ) := by
        have h3 : bad.card * (6 * C1) ≤ E := by
          rw [hE, Nat.mul_comm]
          exact Nat.mul_le_mul_left _ hbad'
        exact_mod_cast h3
      have hcount : (bs.countP (fun b => decide (j * w ≤ b.2)) : ℝ) ≤
          ((r - j * w : ℕ) : ℝ) + (E : ℝ) := by
        rw [hbs3, Nat.cast_sum]
        calc ∑ i, ((cov i).countP (fun b => decide (j * w ≤ b.2)) : ℝ)
            ≤ ∑ i, (y i ⟨j, hj⟩ + (if i ∈ bad then ((6 * C1 : ℕ) : ℝ) else 0)) :=
              Finset.sum_le_sum (fun i _ => hcov3 i ⟨j, hj⟩)
          _ = (∑ i, y i) ⟨j, hj⟩ + (bad.card : ℝ) * ((6 * C1 : ℕ) : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_ite_mem, Finset.univ_inter,
                Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((r - j * w : ℕ) : ℝ) + (E : ℝ) := by
              rw [e1]
              linarith
      exact_mod_cast hcount

end IntCover

section FinalAr

lemma final_arith (e s k : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) (hs0 : 0 ≤ s) (hse : 2 / e ≤ s)
    (hk1 : (1 + e / 2) * s ≤ k) (hk2 : k < (1 + e / 2) * s + 1) :
    s ^ 2 ≤ (1 - 4 * (e / 8)) * k ^ 2 ∧ k ≤ (1 + e) * s := by
  have h2 : 2 ≤ s * e := (div_le_iff₀ he0).mp hse
  constructor
  · have h3 : ((1 + e / 2) * s) ^ 2 ≤ k ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hs0) hk1 2
    have h5 : (1 - 4 * (e / 8)) * ((1 + e / 2) * s) ^ 2 - s ^ 2 =
        (e / 2) * (1 - e / 2 - (e / 2) ^ 2) * s ^ 2 := by ring
    have h6 : 0 ≤ (e / 2) * (1 - e / 2 - (e / 2) ^ 2) * s ^ 2 := by
      refine mul_nonneg (mul_nonneg (by linarith) ?_) (sq_nonneg s)
      nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1)]
    have h7 := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ 1 - 4 * (e / 8) by linarith)
    linarith
  · have h8 : (1 + e) * s = (1 + e / 2) * s + s * e / 2 := by ring
    rw [h8]
    linarith

end FinalAr

end NTB

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.norin_turcotte := by
  intro ε hε
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min ε 1 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact lt_min hε one_pos
  have he1 : e ≤ 1 := by rw [he]; exact min_le_right _ _
  have heε : e ≤ ε := by rw [he]; exact min_le_left _ _
  obtain ⟨k0, hk0⟩ := NTB.int_cover (e / 8) (by linarith) (by linarith)
  refine ⟨max (k0 ^ 2) (max ⌈4 / e ^ 2⌉₊ 1), ?_⟩
  intro V _ G hG hn
  classical
  have hn1 : k0 ^ 2 ≤ Fintype.card V := le_trans (le_max_left _ _) hn
  have hn2 : ⌈4 / e ^ 2⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 1 ≤ Fintype.card V :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hV : Nonempty V := Fintype.card_pos_iff.mp hn3
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (Fintype.card V) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hss : s ^ 2 = (Fintype.card V : ℝ) := by
    rw [hs]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hsk0 : (k0 : ℝ) ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hn1
  have hse : 2 / e ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    have h1 : (4 / e ^ 2 : ℝ) ≤ (Fintype.card V : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
    have h2 : (2 / e) ^ 2 = 4 / e ^ 2 := by
      rw [div_pow]
      norm_num
    rw [h2]
    exact h1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈(1 + e / 2) * s⌉₊ := ⟨_, rfl⟩
  have hpos : 0 ≤ (1 + e / 2) * s := mul_nonneg (by linarith) hs0
  have hk1 : (1 + e / 2) * s ≤ (k : ℝ) := by
    rw [hk]
    exact Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 + e / 2) * s + 1 := by
    rw [hk]
    exact Nat.ceil_lt_add_one hpos
  obtain ⟨ha1, ha2⟩ := NTB.final_arith e s (k : ℝ) he0 he1 hs0 hse hk1 hk2
  have hkk0 : k0 ≤ k := by
    have h1 : s ≤ (1 + e / 2) * s := by nlinarith [mul_nonneg he0.le hs0]
    have h2 : (k0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h2
  obtain ⟨d, hd, hdist⟩ := NTB.exists_tm G hG
  obtain ⟨c, hc⟩ := hk0 k hkk0 V d hd hV (by rw [← hss]; exact ha1)
  have hbn : BurningNumberConjecture.burningNumber G ≤ k := by
    unfold BurningNumberConjecture.burningNumber
    apply Nat.sInf_le
    show ∃ x : Fin k → V, BurningNumberConjecture.IsBurningSequence G x
    refine ⟨fun i : Fin k => c (k - 1 - i.val), ?_⟩
    intro v
    obtain ⟨i, hi, hiv⟩ := hc v
    refine ⟨⟨k - 1 - i, by omega⟩, hG.preconnected _ _, ?_⟩
    have h1 := hdist (c i) v
    have h2 : k - 1 - (k - 1 - i) = i := by omega
    show G.dist (c (k - 1 - (k - 1 - i))) v + (k - 1 - i) < k
    rw [h2]
    omega
  have h9 := mul_le_mul_of_nonneg_right heε hs0
  calc (BurningNumberConjecture.burningNumber G : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbn
    _ ≤ (1 + e) * s := ha2
    _ ≤ (1 + ε) * s := by linarith
    _ = (1 + ε) * Real.sqrt (Fintype.card V) := by rw [hs]
