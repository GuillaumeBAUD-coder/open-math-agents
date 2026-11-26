import FormalConjectures.Wikipedia.HedetniemiConjecture
import Mathlib

-- ===== Basic =====
open SimpleGraph

namespace Hedet

/-! ### File 1: Basic -/

/-- The blow-up `F[K_q]`: replace every vertex by a `q`-clique. -/
def blowup {V : Type*} (F : SimpleGraph V) (q : ℕ) : SimpleGraph (V × Fin q) where
  Adj x y := F.Adj x.1 y.1 ∨ (x.1 = y.1 ∧ x.2 ≠ y.2)
  symm := ⟨fun _ _ h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩)⟩
  loopless := ⟨fun _ h => h.elim (fun h => F.irrefl h) (fun h => h.2 rfl)⟩

/-- Adjacency of the exponential graph `K_C^G`, loops allowed. -/
def expRel {W : Type*} (G : SimpleGraph W) (C : Type*) (f g : W → C) : Prop :=
  ∀ x y, G.Adj x y → f x ≠ g y

/-- The exponential graph `K_C^G` with loops removed. -/
def expGraph {W : Type*} (G : SimpleGraph W) (C : Type*) : SimpleGraph (W → C) where
  Adj f g := f ≠ g ∧ expRel G C f g
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun x y hxy => (h.2 y x hxy.symm).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Colour type with `3q+2` colours: `2q+1` low colours and `q+1` high colours. -/
abbrev Col (q : ℕ) : Type := Option (Fin q ⊕ Fin q) ⊕ Fin (q + 1)

theorem card_col (q : ℕ) : Fintype.card (Col q) = 3 * q + 2 := by
  simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
  omega

theorem expRel_symm {W C : Type*} {G : SimpleGraph W} {f g : W → C}
    (h : expRel G C f g) : expRel G C g f :=
  fun x y hxy => (h y x hxy.symm).symm

theorem expRel_const_of_forall_ne {W C : Type*} {G : SimpleGraph W} {f : W → C} {b : C}
    (h : ∀ x, f x ≠ b) : expRel G C f (fun _ => b) :=
  fun x _ _ => h x

theorem expGraph_adj_of_expRel {W C : Type*} {G : SimpleGraph W}
    (hG : IsEmpty (G.Coloring C)) {f g : W → C} (h : expRel G C f g) :
    (expGraph G C).Adj f g := by
  refine ⟨?_, h⟩
  rintro rfl
  exact hG.false (SimpleGraph.Coloring.mk f (fun {x y} hxy => h x y hxy))

theorem exists_suited {W C : Type*} [Finite C] {G : SimpleGraph W}
    (hG : IsEmpty (G.Coloring C)) (Ψ : (expGraph G C).Coloring C) :
    ∃ Ψ' : (expGraph G C).Coloring C, ∀ a : C, Ψ' (fun _ => a) = a := by
  classical
  let σ : C → C := fun a => Ψ (fun _ => a)
  have hσ : Function.Injective σ := by
    intro a b hab
    by_contra hne
    have hadj : (expGraph G C).Adj (fun _ => a) (fun _ => b) :=
      expGraph_adj_of_expRel hG (fun _ _ _ => hne)
    exact Ψ.valid hadj hab
  let e : C ≃ C := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)
  refine ⟨SimpleGraph.Coloring.mk (fun f => e.symm (Ψ f)) ?_, ?_⟩
  · intro f g hfg heq
    exact Ψ.valid hfg (e.symm.injective heq)
  · intro a
    show e.symm (σ a) = a
    exact e.symm_apply_apply a

theorem suited_mem_range {W C : Type*} {G : SimpleGraph W}
    (hG : IsEmpty (G.Coloring C)) (Ψ : (expGraph G C).Coloring C)
    (hΨ : ∀ a : C, Ψ (fun _ => a) = a) (f : W → C) : ∃ x, f x = Ψ f := by
  by_contra hne
  have hne' : ∀ x, f x ≠ Ψ f := fun x hx => hne ⟨x, hx⟩
  have hadj : (expGraph G C).Adj f (fun _ => Ψ f) :=
    expGraph_adj_of_expRel hG (expRel_const_of_forall_ne hne')
  exact Ψ.valid hadj (hΨ (Ψ f)).symm

end Hedet

-- ===== Blowup =====
open SimpleGraph

namespace Hedet

/-! ### File 2: Blowup counting -/

theorem card_mul_le_of_blowup_coloring {V C : Type*} [Fintype V] [Fintype C]
    (F : SimpleGraph V) (q m : ℕ)
    (hm : ∀ I : Finset V, F.IsIndepSet (I : Set V) → I.card ≤ m)
    (κ : (blowup F q).Coloring C) : Fintype.card V * q ≤ Fintype.card C * m := by
  classical
  have hK : ∀ a : C, (Finset.univ.filter fun p : V × Fin q => κ p = a).card ≤ m := by
    intro a
    set K := Finset.univ.filter fun p : V × Fin q => κ p = a
    have hinj : Set.InjOn Prod.fst (K : Set (V × Fin q)) := by
      intro p hp p' hp' he
      simp only [K, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
      by_contra hne
      have hj : p.2 ≠ p'.2 := fun hj => hne (Prod.ext he hj)
      exact κ.valid (Or.inr ⟨he, hj⟩) (hp.trans hp'.symm)
    rw [← Finset.card_image_of_injOn hinj]
    apply hm
    intro x hx y hy hxy hadj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, K, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨p', hp', rfl⟩ := hy
    exact κ.valid (Or.inl hadj) (hp.trans hp'.symm)
  calc Fintype.card V * q = Fintype.card (V × Fin q) := by simp
    _ = ∑ a : C, (Finset.univ.filter fun p : V × Fin q => κ p = a).card :=
        (Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (κ p))).trans rfl
    _ ≤ ∑ _a : C, m := Finset.sum_le_sum fun a _ => hK a
    _ = Fintype.card C * m := by simp

end Hedet

-- ===== Zhu =====
open SimpleGraph

namespace Hedet

/-! ### File 3: Zhu's argument -/

/-- The low colours other than the name of `v`: `zhu_lo ι v (inl j)` is Zhu's `a_j`,
`zhu_lo ι v (inr j)` is `b_j`. -/
def zhu_lo {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    (s : Fin q ⊕ Fin q) : Col q :=
  Sum.inl (Equiv.swap (ι v) none (some s))

/-- The `2q+1` colours available far away from `v`. -/
def zhu_far {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) :
    Fin q ⊕ Fin (q + 1) → Col q
  | Sum.inl j => zhu_lo ι v (Sum.inr j)
  | Sum.inr k => Sum.inr k

theorem zhu_lo_inj {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    {s s' : Fin q ⊕ Fin q} (h : zhu_lo ι v s = zhu_lo ι v s') : s = s' :=
  Option.some.inj ((Equiv.swap (ι v) none).injective (Sum.inl.inj h))

theorem zhu_lo_ne_name {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    (s : Fin q ⊕ Fin q) : zhu_lo ι v s ≠ Sum.inl (ι v) := by
  intro h
  have h1 : Equiv.swap (ι v) none (some s) = Equiv.swap (ι v) none none := by
    rw [Equiv.swap_apply_right]
    exact Sum.inl.inj h
  exact Option.some_ne_none s ((Equiv.swap (ι v) none).injective h1)

theorem zhu_lo_ne_inr {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    (s : Fin q ⊕ Fin q) (k : Fin (q + 1)) : zhu_lo ι v s ≠ Sum.inr k := by
  intro h
  cases h

theorem zhu_far_inj {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    {t t' : Fin q ⊕ Fin (q + 1)} (h : zhu_far ι v t = zhu_far ι v t') : t = t' := by
  rcases t with j | k <;> rcases t' with j' | k'
  · have := zhu_lo_inj ι v h
    rw [Sum.inr.inj this]
  · exact absurd h (zhu_lo_ne_inr ι v _ _)
  · exact absurd h.symm (zhu_lo_ne_inr ι v _ _)
  · have : k = k' := Sum.inr.inj h
    rw [this]

theorem zhu_far_ne_lo_inl {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V)
    (t : Fin q ⊕ Fin (q + 1)) (j : Fin q) : zhu_far ι v t ≠ zhu_lo ι v (Sum.inl j) := by
  intro h
  rcases t with j' | k
  · have := zhu_lo_inj ι v h
    cases this
  · exact zhu_lo_ne_inr ι v _ _ h.symm

/-- Distance at most two from `v`. -/
def zhu_near {V : Type*} (F : SimpleGraph V) (v x : V) : Prop :=
  x = v ∨ F.Adj v x ∨ ∃ w, F.Adj v w ∧ F.Adj w x

theorem zhu_near_of_adj {V : Type*} (F : SimpleGraph V) {v x : V} (h : F.Adj v x) :
    zhu_near F v x := Or.inr (Or.inl h)

theorem zhu_near_of_adj_adj {V : Type*} (F : SimpleGraph V) {v x y : V} (h : F.Adj v x)
    (hxy : F.Adj x y) : zhu_near F v y := Or.inr (Or.inr ⟨x, h, hxy⟩)

theorem zhu_not_adj_of_adj {V : Type*} (F : SimpleGraph V)
    (h3 : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False) {v x y : V}
    (hx : F.Adj v x) (hy : F.Adj v y) : ¬F.Adj x y :=
  fun hxy => h3 v x y hx hxy hy.symm

theorem zhu_not_adj_of_mid {V : Type*} (F : SimpleGraph V)
    (h5 : ∀ a b c d e, F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d e → F.Adj e a → False)
    {v x y : V} (hx : ¬F.Adj v x) (hx' : zhu_near F v x) (hy : ¬F.Adj v y)
    (hy' : zhu_near F v y) : ¬F.Adj x y := by
  intro hxy
  rcases hx' with rfl | hx' | ⟨w, hw, hwx⟩
  · exact hy hxy
  · exact hx hx'
  · rcases hy' with rfl | hy' | ⟨w', hw', hwy⟩
    · exact hx hxy.symm
    · exact hy hy'
    · exact h5 v w x y w' hw hwx hxy hwy.symm hw'.symm

open Classical in
/-- Zhu's maps `μ_{v,t}`: neighbours of `v` get the colours `b_j`, the other vertices at
distance at most two get `a_j`, everything else gets the single colour `zhu_far ι v t`. -/
noncomputable def zhu_mu {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (t : Fin q ⊕ Fin (q + 1)) (p : V × Fin q) : Col q :=
  if F.Adj v p.1 then zhu_lo ι v (Sum.inr p.2)
  else if zhu_near F v p.1 then zhu_lo ι v (Sum.inl p.2) else zhu_far ι v t

open Classical in
/-- Zhu's maps `θ_{v,k}`. -/
noncomputable def zhu_theta {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (k : Fin (q + 1)) (p : V × Fin q) : Col q :=
  if p.1 = v ∨ F.Adj v p.1 then Sum.inr k else Sum.inl (ι v)

/-- The map naming the base vertex. -/
def zhu_phi {V : Type*} {q : ℕ} (ι : V ↪ Option (Fin q ⊕ Fin q)) (p : V × Fin q) : Col q :=
  Sum.inl (ι p.1)

theorem zhu_mu_of_adj {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (t : Fin q ⊕ Fin (q + 1)) {p : V × Fin q}
    (h : F.Adj v p.1) : zhu_mu F ι v t p = zhu_lo ι v (Sum.inr p.2) := by
  unfold zhu_mu
  rw [if_pos h]

theorem zhu_mu_of_mid {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (t : Fin q ⊕ Fin (q + 1)) {p : V × Fin q}
    (h : ¬F.Adj v p.1) (h' : zhu_near F v p.1) :
    zhu_mu F ι v t p = zhu_lo ι v (Sum.inl p.2) := by
  unfold zhu_mu
  rw [if_neg h, if_pos h']

theorem zhu_mu_of_far {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (t : Fin q ⊕ Fin (q + 1)) {p : V × Fin q}
    (h : ¬zhu_near F v p.1) : zhu_mu F ι v t p = zhu_far ι v t := by
  unfold zhu_mu
  rw [if_neg (fun h' => h (zhu_near_of_adj F h')), if_neg h]

theorem zhu_cls {V : Type*} (F : SimpleGraph V) (v x : V) :
    F.Adj v x ∨ (¬F.Adj v x ∧ zhu_near F v x) ∨ ¬zhu_near F v x := by
  by_cases h : F.Adj v x
  · exact Or.inl h
  · by_cases h' : zhu_near F v x
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')

theorem zhu_mu_range {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (t : Fin q ⊕ Fin (q + 1)) (p : V × Fin q) :
    zhu_mu F ι v t p = zhu_far ι v t ∨ ∃ s, zhu_mu F ι v t p = zhu_lo ι v s := by
  rcases zhu_cls F v p.1 with h | ⟨h, h'⟩ | h
  · exact Or.inr ⟨_, zhu_mu_of_adj F ι v t h⟩
  · exact Or.inr ⟨_, zhu_mu_of_mid F ι v t h h'⟩
  · exact Or.inl (zhu_mu_of_far F ι v t h)

theorem zhu_theta_range {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (k : Fin (q + 1)) (p : V × Fin q) :
    zhu_theta F ι v k p = Sum.inr k ∨ zhu_theta F ι v k p = Sum.inl (ι v) := by
  unfold zhu_theta
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- C3: the maps `μ_{v,t}` are pairwise adjacent in the exponential graph. -/
theorem zhu_mu_expRel {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q))
    (h3 : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    (h5 : ∀ a b c d e, F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d e → F.Adj e a → False)
    (v : V) {t t' : Fin q ⊕ Fin (q + 1)} (htt : t ≠ t') :
    expRel (blowup F q) (Col q) (zhu_mu F ι v t) (zhu_mu F ι v t') := by
  rintro ⟨x, j⟩ ⟨y, j'⟩ hadj heq
  have hadj' : F.Adj x y ∨ (x = y ∧ j ≠ j') := hadj
  rcases zhu_cls F v x with hx | ⟨hx, hx'⟩ | hx
  · rw [zhu_mu_of_adj F ι v t (p := (x, j)) hx] at heq
    rcases zhu_cls F v y with hy | ⟨hy, hy'⟩ | hy
    · rw [zhu_mu_of_adj F ι v t' (p := (y, j')) hy] at heq
      have hj : j = j' := Sum.inr.inj (zhu_lo_inj ι v heq)
      rcases hadj' with h | ⟨_, h⟩
      · exact zhu_not_adj_of_adj F h3 hx hy h
      · exact h hj
    · rw [zhu_mu_of_mid F ι v t' (p := (y, j')) hy hy'] at heq
      have := zhu_lo_inj ι v heq
      cases this
    · rcases hadj' with h | ⟨h, _⟩
      · exact hy (zhu_near_of_adj_adj F hx h)
      · exact hy (zhu_near_of_adj F (h ▸ hx))
  · rw [zhu_mu_of_mid F ι v t (p := (x, j)) hx hx'] at heq
    rcases zhu_cls F v y with hy | ⟨hy, hy'⟩ | hy
    · rw [zhu_mu_of_adj F ι v t' (p := (y, j')) hy] at heq
      have := zhu_lo_inj ι v heq
      cases this
    · rw [zhu_mu_of_mid F ι v t' (p := (y, j')) hy hy'] at heq
      have hj : j = j' := Sum.inl.inj (zhu_lo_inj ι v heq)
      rcases hadj' with h | ⟨_, h⟩
      · exact zhu_not_adj_of_mid F h5 hx hx' hy hy' h
      · exact h hj
    · rw [zhu_mu_of_far F ι v t' (p := (y, j')) hy] at heq
      exact zhu_far_ne_lo_inl ι v t' j heq.symm
  · rw [zhu_mu_of_far F ι v t (p := (x, j)) hx] at heq
    rcases zhu_cls F v y with hy | ⟨hy, hy'⟩ | hy
    · rcases hadj' with h | ⟨h, _⟩
      · exact hx (zhu_near_of_adj_adj F hy h.symm)
      · exact hx (zhu_near_of_adj F (h ▸ hy))
    · rw [zhu_mu_of_mid F ι v t' (p := (y, j')) hy hy'] at heq
      exact zhu_far_ne_lo_inl ι v t j' heq
    · rw [zhu_mu_of_far F ι v t' (p := (y, j')) hy] at heq
      exact htt (zhu_far_inj ι v heq)

/-- C4: `θ_{v,k}` is adjacent to `μ_{v,inr k}`. -/
theorem zhu_theta_expRel_mu {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (k : Fin (q + 1)) :
    expRel (blowup F q) (Col q) (zhu_theta F ι v k) (zhu_mu F ι v (Sum.inr k)) := by
  rintro ⟨x, j⟩ ⟨y, j'⟩ hadj heq
  have hadj' : F.Adj x y ∨ (x = y ∧ j ≠ j') := hadj
  by_cases hx : x = v ∨ F.Adj v x
  · have hth : zhu_theta F ι v k (x, j) = Sum.inr k := by
      unfold zhu_theta
      rw [if_pos hx]
    rw [hth] at heq
    rcases zhu_cls F v y with hy | ⟨hy, hy'⟩ | hy
    · rw [zhu_mu_of_adj F ι v _ (p := (y, j')) hy] at heq
      exact zhu_lo_ne_inr ι v _ _ heq.symm
    · rw [zhu_mu_of_mid F ι v _ (p := (y, j')) hy hy'] at heq
      exact zhu_lo_ne_inr ι v _ _ heq.symm
    · apply hy
      rcases hadj' with h | ⟨h, _⟩
      · rcases hx with rfl | hx
        · exact zhu_near_of_adj F h
        · exact zhu_near_of_adj_adj F hx h
      · subst h
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact zhu_near_of_adj F hx
  · have hth : zhu_theta F ι v k (x, j) = Sum.inl (ι v) := by
      unfold zhu_theta
      rw [if_neg hx]
    rw [hth] at heq
    rcases zhu_cls F v y with hy | ⟨hy, hy'⟩ | hy
    · rw [zhu_mu_of_adj F ι v _ (p := (y, j')) hy] at heq
      exact zhu_lo_ne_name ι v _ heq.symm
    · rw [zhu_mu_of_mid F ι v _ (p := (y, j')) hy hy'] at heq
      exact zhu_lo_ne_name ι v _ heq.symm
    · rw [zhu_mu_of_far F ι v _ (p := (y, j')) hy] at heq
      cases heq

/-- C5: `θ_{v,k}` is adjacent to `φ`. -/
theorem zhu_theta_expRel_phi {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q)) (v : V) (k : Fin (q + 1)) :
    expRel (blowup F q) (Col q) (zhu_theta F ι v k) (zhu_phi ι) := by
  rintro ⟨x, j⟩ ⟨y, j'⟩ hadj heq
  have hadj' : F.Adj x y ∨ (x = y ∧ j ≠ j') := hadj
  by_cases hx : x = v ∨ F.Adj v x
  · have hth : zhu_theta F ι v k (x, j) = Sum.inr k := by
      unfold zhu_theta
      rw [if_pos hx]
    rw [hth] at heq
    cases heq
  · have hth : zhu_theta F ι v k (x, j) = Sum.inl (ι v) := by
      unfold zhu_theta
      rw [if_neg hx]
    rw [hth] at heq
    have hvy : v = y := ι.injective (Sum.inl.inj heq)
    subst hvy
    rcases hadj' with h | ⟨h, _⟩
    · exact hx (Or.inr h.symm)
    · exact hx (Or.inl h)

/-- C6: the pigeonhole step. -/
theorem zhu_pigeon {V : Type*} {q : ℕ} (F : SimpleGraph V)
    (ι : V ↪ Option (Fin q ⊕ Fin q))
    (h3 : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    (h5 : ∀ a b c d e, F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d e → F.Adj e a → False)
    (hG : IsEmpty ((blowup F q).Coloring (Col q)))
    (Ψ : (expGraph (blowup F q) (Col q)).Coloring (Col q))
    (hΨ : ∀ a : Col q, Ψ (fun _ => a) = a) (v : V) :
    ∃ k : Fin (q + 1), Ψ (zhu_mu F ι v (Sum.inr k)) = Sum.inr k := by
  by_contra H
  have hall : ∀ t : Fin q ⊕ Fin (q + 1), ∃ s, Ψ (zhu_mu F ι v t) = zhu_lo ι v s := by
    intro t
    obtain ⟨p, hp⟩ := suited_mem_range hG Ψ hΨ (zhu_mu F ι v t)
    rcases zhu_mu_range F ι v t p with h | ⟨s, hs⟩
    · rcases t with j | k
      · exact ⟨Sum.inr j, hp.symm.trans h⟩
      · exact absurd ⟨k, hp.symm.trans h⟩ H
    · exact ⟨s, hp.symm.trans hs⟩
  choose s hs using hall
  have hinj : Function.Injective s := by
    intro t t' hst
    by_contra htt
    have hadj := expGraph_adj_of_expRel hG (zhu_mu_expRel F ι h3 h5 v htt)
    apply Ψ.valid hadj
    rw [hs t, hs t', hst]
  have hle := Fintype.card_le_of_injective s hinj
  simp only [Fintype.card_sum, Fintype.card_fin] at hle
  omega

theorem isEmpty_coloring_expGraph {V : Type*} [Fintype V] (F : SimpleGraph V) (q : ℕ)
    (hcard : Fintype.card V ≤ 2 * q + 1)
    (h3 : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    (h5 : ∀ a b c d e, F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d e → F.Adj e a → False)
    (hG : IsEmpty ((blowup F q).Coloring (Col q))) :
    IsEmpty ((expGraph (blowup F q) (Col q)).Coloring (Col q)) := by
  refine ⟨fun Ψ0 => ?_⟩
  have hc : Fintype.card V ≤ Fintype.card (Option (Fin q ⊕ Fin q)) := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨ι⟩ : Nonempty (V ↪ Option (Fin q ⊕ Fin q)) :=
    Function.Embedding.nonempty_of_card_le hc
  obtain ⟨Ψ, hΨ⟩ := exists_suited hG Ψ0
  obtain ⟨p, hp⟩ := suited_mem_range hG Ψ hΨ (zhu_phi ι)
  obtain ⟨k, hk⟩ := zhu_pigeon F ι h3 h5 hG Ψ hΨ p.1
  obtain ⟨p', hp'⟩ := suited_mem_range hG Ψ hΨ (zhu_theta F ι p.1 k)
  have h1 := Ψ.valid (expGraph_adj_of_expRel hG (zhu_theta_expRel_mu F ι p.1 k))
  have h2 := Ψ.valid (expGraph_adj_of_expRel hG (zhu_theta_expRel_phi F ι p.1 k))
  rcases zhu_theta_range F ι p.1 k p' with h | h
  · exact h1 (hp'.symm.trans (h.trans hk.symm))
  · exact h2 (hp'.symm.trans (h.trans hp))

end Hedet

-- ===== GolayGraph =====
open SimpleGraph

namespace Hedet

/-! ### File 4: the Golay coset graph -/
namespace Golay

/-- Columns of a parity-check matrix of the binary Golay code, as 11-bit masks:
`hm i = x^i mod (x^11+x^9+x^7+x^6+x^5+x+1)`. -/
def hm : Fin 23 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 739, 1478, 367, 734, 1468, 411, 822, 1644,
    1595, 1685, 1993, 1393]

abbrev Vec : Type := Fin 11 → ZMod 2

def toVec (n : ℕ) : Vec := fun k => if n.testBit k then 1 else 0

def h (i : Fin 23) : Vec := toVec (hm i)

theorem golay_toVec_xor (a b : ℕ) : toVec (a ^^^ b) = toVec a + toVec b := by
  funext k
  simp only [toVec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem golay_toVec_inj {a b : ℕ} (ha : a < 2 ^ 11) (hb : b < 2 ^ 11)
    (hab : toVec a = toVec b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · have e := congrFun hab ⟨i, hi⟩
    simp only [toVec] at e
    revert e
    cases a.testBit i <;> cases b.testBit i <;> decide
  · have h2 : 2 ^ 11 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h2), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h2)]

theorem golay_toVec_zero : toVec 0 = 0 := by
  funext k
  simp [toVec]

theorem golay_exists_toVec (u : Vec) : ∃ n : Fin 2048, toVec n = u := by
  refine ⟨⟨Nat.ofBits fun k : Fin 11 => decide (u k = 1), Nat.ofBits_lt_two_pow _⟩, ?_⟩
  funext k
  simp only [toVec, Nat.testBit_ofBits_lt _ _ k.isLt]
  generalize u k = x
  revert x
  decide

theorem golay_hm_lt : ∀ i : Fin 23, hm i < 2 ^ 11 := by decide

/-- Bit-set of all XORs of two masks. -/
def golay_pairSet : ℕ := (List.finRange 23).foldl (fun acc l =>
  (List.finRange 23).foldl (fun acc m => acc ||| (1 <<< (hm l ^^^ hm m))) acc) 0

set_option maxRecDepth 100000 in
theorem golay_pairSet_pair : ∀ l m : Fin 23, golay_pairSet.testBit (hm l ^^^ hm m) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem golay_pairSet_triple :
    ∀ i j k : Fin 23, golay_pairSet.testBit (hm i ^^^ hm j ^^^ hm k) = false := by
  decide +kernel

theorem no_five (i j k l m : Fin 23) : h i + h j + h k + h l + h m ≠ 0 := by
  intro hs
  have e : h i + h j + h k = h l + h m := by
    rw [← sub_eq_zero, CharTwo.sub_eq_add, ← hs]; abel
  simp only [h, ← golay_toVec_xor] at e
  have lt3 : hm i ^^^ hm j ^^^ hm k < 2 ^ 11 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (golay_hm_lt i) (golay_hm_lt j)) (golay_hm_lt k)
  have lt2 : hm l ^^^ hm m < 2 ^ 11 := Nat.xor_lt_two_pow (golay_hm_lt l) (golay_hm_lt m)
  have t := golay_pairSet_triple i j k
  rw [golay_toVec_inj lt3 lt2 e, golay_pairSet_pair l m] at t
  exact Bool.noConfusion t

theorem no_three (i j k : Fin 23) : h i + h j + h k ≠ 0 := by
  intro hs
  apply no_five i j k i i
  rw [hs, zero_add, CharTwo.add_self_eq_zero]

theorem h_ne_zero (i : Fin 23) : h i ≠ 0 := by
  intro e
  apply no_three i i i
  rw [e, add_zero, add_zero]

/-- Cayley graph of `(ZMod 2)^11` with connection set `{h 0, …, h 22}`. -/
def graph : SimpleGraph Vec where
  Adj x y := ∃ i, x + y = h i
  symm := ⟨fun x y ⟨i, hi⟩ => ⟨i, by rw [add_comm]; exact hi⟩⟩
  loopless := ⟨fun x ⟨i, hi⟩ => h_ne_zero i (by rw [← hi]; exact CharTwo.add_self_eq_zero x)⟩


theorem no_triangle (a b c : Vec) : graph.Adj a b → graph.Adj b c → graph.Adj c a → False := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩
  apply no_three i j k
  rw [← hi, ← hj, ← hk]
  have e : a + b + (b + c) + (c + a) = (a + a) + (b + b) + (c + c) := by abel
  rw [e]
  simp only [CharTwo.add_self_eq_zero]
theorem no_pentagon (a b c d e : Vec) : graph.Adj a b → graph.Adj b c → graph.Adj c d →
    graph.Adj d e → graph.Adj e a → False := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨l, hl⟩ ⟨m, hm'⟩
  apply no_five i j k l m
  rw [← hi, ← hj, ← hk, ← hl, ← hm']
  have e : a + b + (b + c) + (c + d) + (d + e) + (e + a) =
      (a + a) + (b + b) + (c + c) + (d + d) + (e + e) := by abel
  rw [e]
  simp only [CharTwo.add_self_eq_zero]

end Golay

end Hedet

-- ===== GolayHoffman =====
open SimpleGraph

namespace Hedet

namespace Golay

/-- `±1`-valued characters. -/
def chi (u z : Vec) : ℤ := if u ⬝ᵥ z = 0 then 1 else -1

/-! ### Characters -/

theorem golay_hoff_chi_add_right (u z z' : Vec) : chi u (z + z') = chi u z * chi u z' := by
  unfold chi
  rw [dotProduct_add]
  generalize u ⬝ᵥ z = a
  generalize u ⬝ᵥ z' = b
  revert a b
  decide

theorem golay_hoff_chi_add_left (u u' z : Vec) : chi (u + u') z = chi u z * chi u' z := by
  unfold chi
  rw [add_dotProduct]
  generalize u ⬝ᵥ z = a
  generalize u' ⬝ᵥ z = b
  revert a b
  decide

theorem golay_hoff_chi_zero_left (z : Vec) : chi 0 z = 1 := by simp [chi]

theorem golay_hoff_chi_zero_right (u : Vec) : chi u 0 = 1 := by simp [chi]

theorem golay_hoff_card : Fintype.card Vec = 2048 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; norm_num

theorem sum_chi (z : Vec) : ∑ u : Vec, chi u z = if z = 0 then 2048 else 0 := by
  split_ifs with hz
  · subst hz
    simp only [golay_hoff_chi_zero_right, Finset.sum_const, Finset.card_univ, golay_hoff_card]
    norm_num
  · obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra hc
      exact hz (funext fun k => by_contra fun hk => hc ⟨k, hk⟩)
    have hk1 : z k = 1 := by
      revert hk
      generalize z k = a
      revert a
      decide
    have he : chi (Pi.single k 1) z = -1 := by
      simp [chi, single_dotProduct, hk1]
    have e := Equiv.sum_comp (Equiv.addRight (Pi.single k (1 : ZMod 2))) (fun u => chi u z)
    simp only [Equiv.coe_addRight, golay_hoff_chi_add_left, he] at e
    rw [← Finset.sum_mul] at e
    linarith

/-! ### Eigenvalue bound: kernel computation over the 2048 dual words -/

/-- Parity of the number of set bits of a number below `2 ^ 12`. -/
def golay_hoff_par (m : ℕ) : Bool := (27030 >>> ((m ^^^ (m >>> 4) ^^^ (m >>> 8)) % 16)) % 2 == 1

/-- Weight of the dual word with index mask `n`. -/
def golay_hoff_wt (n : ℕ) : ℕ := (List.finRange 23).countP fun i => golay_hoff_par (n &&& hm i)

set_option maxRecDepth 100000 in
theorem golay_hoff_wt_le : ∀ n : Fin 2048, golay_hoff_wt n ≤ 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem golay_hoff_par_eq : ∀ m : Fin 2048, golay_hoff_par m =
    (((List.finRange 11).countP fun k : Fin 11 => (m : ℕ).testBit k) % 2 == 1) := by
  decide +kernel

theorem golay_hoff_sum_ite {α R : Type*} [Semiring R] (p : α → Bool) (l : List α) :
    (l.map fun k => if p k then (1 : R) else 0).sum = (l.countP p : R) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases p a <;> simp [add_comm]

theorem golay_hoff_dot (n a : ℕ) : toVec n ⬝ᵥ toVec a =
    (((List.finRange 11).countP fun k : Fin 11 => (n &&& a).testBit k : ℕ) : ZMod 2) := by
  rw [← golay_hoff_sum_ite, dotProduct, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  simp only [toVec, Nat.testBit_and]
  cases n.testBit k <;> cases a.testBit k <;> simp

theorem golay_hoff_chi_toVec (n : ℕ) (hn : n < 2048) (i : Fin 23) :
    chi (toVec n) (h i) = if golay_hoff_par (n &&& hm i) then -1 else 1 := by
  have lt : n &&& hm i < 2048 := lt_of_le_of_lt Nat.and_le_left hn
  have e := golay_hoff_par_eq ⟨n &&& hm i, lt⟩
  simp only at e
  rw [e, chi, h, golay_hoff_dot]
  generalize (List.finRange 11).countP _ = c
  rcases Nat.even_or_odd c with hc | hc
  · have h2 : c % 2 = 0 := Nat.even_iff.mp hc
    rw [if_pos (ZMod.natCast_eq_zero_iff_even.mpr hc)]
    simp [h2]
  · have h2 : c % 2 = 1 := Nat.odd_iff.mp hc
    rw [if_neg (fun hz => Nat.not_even_iff_odd.mpr hc (ZMod.natCast_eq_zero_iff_even.mp hz))]
    simp [h2]

theorem golay_hoff_lam_toVec (n : ℕ) (hn : n < 2048) :
    ∑ i : Fin 23, chi (toVec n) (h i) = 23 - 2 * (golay_hoff_wt n : ℤ) := by
  have e : ∀ i : Fin 23, chi (toVec n) (h i) =
      1 - 2 * (if golay_hoff_par (n &&& hm i) then (1 : ℤ) else 0) := by
    intro i
    rw [golay_hoff_chi_toVec n hn i]
    cases golay_hoff_par (n &&& hm i) <;> simp
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_def (fun i => if golay_hoff_par (n &&& hm i) then (1 : ℤ) else 0),
    golay_hoff_sum_ite]
  simp [golay_hoff_wt]

/-- Eigenvalue bound (dual weights of the Golay code are `0, 8, 12, 16`). -/
theorem neg_nine_le_lam (u : Vec) : -9 ≤ ∑ i : Fin 23, chi u (h i) := by
  obtain ⟨n, rfl⟩ := golay_exists_toVec u
  rw [golay_hoff_lam_toVec n n.isLt]
  have hw : (golay_hoff_wt n : ℤ) ≤ 16 := by exact_mod_cast golay_hoff_wt_le n
  linarith

/-! ### Hoffman bound -/

theorem golay_hoff_key (I : Finset Vec) (c : Vec) :
    ∑ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) * chi u c =
      ∑ x ∈ I, ∑ y ∈ I, if x + y + c = 0 then (2048 : ℤ) else 0 := by
  have e : ∀ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) * chi u c =
      ∑ x ∈ I, ∑ y ∈ I, chi u (x + y + c) := by
    intro u
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [golay_hoff_chi_add_right, golay_hoff_chi_add_right]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact sum_chi _

theorem indep_card_le (I : Finset Vec) (hI : graph.IsIndepSet (I : Set Vec)) : I.card ≤ 576 := by
  have h1 : ∑ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) = 2048 * (I.card : ℤ) := by
    have k := golay_hoff_key I 0
    simp only [golay_hoff_chi_zero_right, mul_one, add_zero] at k
    rw [k]
    have e : ∀ x ∈ I, (∑ y ∈ I, if x + y = 0 then (2048 : ℤ) else 0) = 2048 := by
      intro x hx
      have e2 : ∀ y : Vec, (x + y = 0) ↔ (x = y) := fun y => CharTwo.add_eq_zero
      simp only [e2, Finset.sum_ite_eq, hx, if_true]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h2 : ∀ i : Fin 23,
      ∑ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) * chi u (h i) = 0 := by
    intro i
    rw [golay_hoff_key I (h i)]
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
    rw [if_neg]
    intro hxy
    have adj : graph.Adj x y := ⟨i, by rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact hxy⟩
    exact hI hx hy (graph.ne_of_adj adj) adj
  have h3 : ∑ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) *
      (∑ i : Fin 23, chi u (h i) + 9) = 9 * 2048 * (I.card : ℤ) := by
    have e : ∀ u : Vec, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) *
        (∑ i : Fin 23, chi u (h i) + 9) =
        ∑ i : Fin 23, (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) * chi u (h i) +
          9 * ((∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y)) := by
      intro u
      rw [mul_add, Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_add_distrib, Finset.sum_comm,
      Finset.sum_eq_zero (fun i _ => h2 i), ← Finset.mul_sum, h1]
    ring
  have h4 := Finset.single_le_sum
    (f := fun u : Vec => (∑ x ∈ I, chi u x) * (∑ y ∈ I, chi u y) *
      (∑ i : Fin 23, chi u (h i) + 9))
    (fun u _ => mul_nonneg (mul_self_nonneg _) (by linarith [neg_nine_le_lam u]))
    (Finset.mem_univ (0 : Vec))
  simp only [golay_hoff_chi_zero_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h4
  rw [h3] at h4
  push_cast at h4
  have h5 : (I.card : ℤ) ≤ 576 := by
    by_contra hc
    replace hc := not_le.mp hc
    nlinarith [mul_pos (sub_pos.mpr hc) (show (0 : ℤ) < I.card by linarith)]
  exact_mod_cast h5

end Golay

end Hedet

-- ===== assembly =====
open SimpleGraph

namespace Hedet

/-- `(x, f) ↦ f x` is a proper colouring of `G × K_C^G`. -/
def prodColoring {W : Type} (G : SimpleGraph W) (C : Type) :
    (HedetniemiConjecture.tensorProd G (expGraph G C)).Coloring C :=
  Coloring.mk (fun p => p.2 p.1) (fun {_ _} h => h.2.2 _ _ h.1)

/-! ### File 5: assembly -/
open HedetniemiConjecture in
theorem counterexample_of {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V) (q m : ℕ)
    (hcard : Fintype.card V ≤ 2 * q + 1)
    (h3 : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    (h5 : ∀ a b c d e, F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d e → F.Adj e a → False)
    (hm : ∀ I : Finset V, F.IsIndepSet (I : Set V) → I.card ≤ m)
    (hbig : (3 * q + 2) * m < Fintype.card V * q) :
    ∃ (α β : Type) (_ : Fintype α) (_ : Fintype β) (G : SimpleGraph α) (H : SimpleGraph β),
      (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber := by
  have key : ∀ {W : Type} (K : SimpleGraph W), IsEmpty (K.Coloring (Col q)) →
      ((3 * q + 2 : ℕ) : ℕ∞) < K.chromaticNumber := fun K hK =>
    lt_of_not_ge fun hle =>
      hK.elim ((chromaticNumber_le_iff_colorable.mp hle).toColoring (card_col q).ge)
  have hG : IsEmpty ((blowup F q).Coloring (Col q)) := ⟨fun κ => by
    have := card_mul_le_of_blowup_coloring F q m hm κ
    rw [card_col] at this
    omega⟩
  have hH := isEmpty_coloring_expGraph F q hcard h3 h5 hG
  have hprod : (tensorProd (blowup F q) (expGraph (blowup F q) (Col q))).chromaticNumber
      ≤ ((3 * q + 2 : ℕ) : ℕ∞) := by
    have := (prodColoring (blowup F q) (Col q)).colorable
    rw [card_col] at this
    exact chromaticNumber_le_iff_colorable.mpr this
  exact ⟨_, _, inferInstance, inferInstance, blowup F q, expGraph (blowup F q) (Col q),
    lt_min (lt_of_le_of_lt hprod (key _ hG)) (lt_of_le_of_lt hprod (key _ hH))⟩

theorem main : ∃ (α β : Type) (_ : Fintype α) (_ : Fintype β) (G : SimpleGraph α)
    (H : SimpleGraph β), (HedetniemiConjecture.tensorProd G H).chromaticNumber
      < min G.chromaticNumber H.chromaticNumber := by
  have hc : Fintype.card Golay.Vec = 2048 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; norm_num
  exact counterexample_of Golay.graph 1024 576 (by rw [hc]; norm_num) Golay.no_triangle Golay.no_pentagon
    Golay.indep_card_le (by rw [hc]; norm_num)

end Hedet

theorem OMA.solution : type_of% @HedetniemiConjecture.hedetniemi_conjecture := by
  intro h
  obtain ⟨α, β, i1, i2, G, H, hlt⟩ := Hedet.main
  exact (ne_of_lt hlt) (@h α β i1 i2 G H)
