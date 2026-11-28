import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1

/-!
Step `SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R1.H1`: every star satisfies
the tournament anti-Sidorenko inequality for finite tournaments.

For the star `K_{1,k}` relabel the vertices as `Fin (k+1)` with centre `0`, orient the first
`⌈k/2⌉` leaves out of the centre and the others into it. A homomorphism into a tournament `G` is
an image `x` of the centre with an out-neighbour of `x` for each out-leaf and an in-neighbour
for each in-leaf, so there are `Σ_x d⁺(x)^{⌈k/2⌉} d⁻(x)^{⌊k/2⌋}` of them. Since
`d⁺(x) + d⁻(x) = |G| - 1` gives `d⁺ d⁻ ≤ |G|^2/4`, and `Σ_x d⁺(x) = |G|(|G|-1)/2`
(each pair of vertices carries one arc), the count is at most `|G|^{k+1} / 2^k`.
-/

namespace OMA.SidFinH1

open scoped Classical

lemma hom_ext {V W : Type*} {D : Digraph V} {G : Digraph W} {f g : D →g G}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Relabelling the source digraph does not change the hom count. -/
lemma homCount_comap {V V' W : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    [Fintype W] [DecidableEq W] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) (G : Digraph W) [DecidableRel D.Adj]
    [DecidableRel D'.Adj] [DecidableRel G.Adj] :
    Digraph.homCount D G = Digraph.homCount D' G := by
  unfold Digraph.homCount
  refine Fintype.card_congr
    { toFun := fun f => ⟨fun v' => f.toFun (e.symm v'), fun {u v} h => f.map_adj' ((hD _ _).2
        (by simpa using h))⟩
      invFun := fun g => ⟨fun v => g.toFun (e v), fun {u v} h => g.map_adj' ((hD _ _).1 h)⟩
      left_inv := fun f => hom_ext (by funext v; simp)
      right_inv := fun g => hom_ext (by funext v; simp) }

/-- Relabelling the host digraph does not change the hom count. -/
lemma homCount_map {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] (σ : W ≃ W') (G : Digraph W) (G' : Digraph W')
    (hG : ∀ x y, G.Adj x y ↔ G'.Adj (σ x) (σ y)) (D : Digraph V) [DecidableRel D.Adj]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Digraph.homCount D G = Digraph.homCount D G' := by
  unfold Digraph.homCount
  refine Fintype.card_congr
    { toFun := fun f => ⟨fun v => σ (f.toFun v), fun {u v} h => (hG _ _).1 (f.map_adj' h)⟩
      invFun := fun g => ⟨fun v => σ.symm (g.toFun v), fun {u v} h => (hG _ _).2
        (by simpa using g.map_adj' h)⟩
      left_inv := fun f => hom_ext (by funext v; simp)
      right_inv := fun g => hom_ext (by funext v; simp) }

lemma homDensity_comap {V V' W : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    [Fintype W] [DecidableEq W] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) (G : Digraph W) [DecidableRel D.Adj]
    [DecidableRel D'.Adj] [DecidableRel G.Adj] :
    Digraph.homDensity D G = Digraph.homDensity D' G := by
  unfold Digraph.homDensity
  rw [homCount_comap e D' D hD G, Fintype.card_congr e]

lemma homDensity_map {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] (σ : W ≃ W') (G : Digraph W) (G' : Digraph W')
    (hG : ∀ x y, G.Adj x y ↔ G'.Adj (σ x) (σ y)) (D : Digraph V) [DecidableRel D.Adj]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Digraph.homDensity D G = Digraph.homDensity D G' := by
  unfold Digraph.homDensity
  rw [homCount_map σ G G' hG D, Fintype.card_congr σ]

/-- In- or out-orientation of leaf `t`. -/
def out (n : ℕ) (t : Fin n) : Prop := (t : ℕ) < (n + 1) / 2

/-- The balanced star orientation on `Fin (n+1)` with centre `0`. -/
def Dstar (n : ℕ) : Digraph (Fin (n + 1)) where
  Adj i j := (i = 0 ∧ ∃ t : Fin n, j = t.succ ∧ out n t) ∨
    (j = 0 ∧ ∃ t : Fin n, i = t.succ ∧ ¬ out n t)

/-- Homomorphisms from the star: an image of the centre and a compatible image of each leaf. -/
def homEquiv (n : ℕ) {W : Type*} (G : Digraph W) :
    (Dstar n →g G) ≃ Σ x : W, ∀ t : Fin n, {y : W // if out n t then G.Adj x y else G.Adj y x} where
  toFun f := ⟨f.toFun 0, fun t => ⟨f.toFun t.succ, by
    split_ifs with h
    · exact f.map_adj' (Or.inl ⟨rfl, t, rfl, h⟩)
    · exact f.map_adj' (Or.inr ⟨rfl, t, rfl, h⟩)⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun t => (p.2 t).1), by
    intro u v h
    rcases h with ⟨rfl, t, rfl, ho⟩ | ⟨rfl, t, rfl, ho⟩
    · have := (p.2 t).2
      rw [if_pos ho] at this
      simpa using this
    · have := (p.2 t).2
      rw [if_neg ho] at this
      simpa using this⟩
  left_inv f := hom_ext (by
    funext i
    refine Fin.cases ?_ (fun t => ?_) i <;> simp)
  right_inv p := by
    rcases p with ⟨x, g⟩
    rfl


/-- Out-degree. -/
noncomputable def od {W : Type*} [Fintype W] (G : Digraph W) (x : W) : ℕ :=
  (Finset.univ.filter (fun y => G.Adj x y)).card

/-- In-degree. -/
noncomputable def idg {W : Type*} [Fintype W] (G : Digraph W) (x : W) : ℕ :=
  (Finset.univ.filter (fun y => G.Adj y x)).card

lemma homCount_star (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W] (G : Digraph W)
    [DecidableRel G.Adj] [DecidableRel (Dstar n).Adj] :
    Digraph.homCount (Dstar n) G = ∑ x, od G x ^ ((n + 1) / 2) * idg G x ^ (n / 2) := by
  unfold Digraph.homCount
  rw [Fintype.card_congr (homEquiv n G), Fintype.card_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.card_pi]
  have h : ∀ t : Fin n, Fintype.card {y : W // if out n t then G.Adj x y else G.Adj y x} =
      if out n t then od G x else idg G x := by
    intro t
    split_ifs with h
    · rw [od, ← Fintype.card_subtype]
    · rw [idg, ← Fintype.card_subtype]
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have ha : (Finset.univ.filter (fun t : Fin n => out n t)).card = (n + 1) / 2 := by
    calc _ = min n ((n + 1) / 2) := by unfold out; convert Fin.card_filter_val_lt (n := n)
      _ = _ := by omega
  have hb : (Finset.univ.filter (fun t : Fin n => ¬ out n t)).card = n / 2 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun t : Fin n => out n t)
    rw [ha, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [ha, hb]

lemma od_add_idg {W : Type*} [Fintype W] [DecidableEq W] (G : Digraph W) (hG : G.IsTournament)
    (x : W) : od G x + (idg G x + 1) = Fintype.card W := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun y => G.Adj x y)
  rw [Finset.card_univ] at h1
  rw [od, ← h1]
  congr 1
  have : Finset.univ.filter (fun y => ¬ G.Adj x y) =
      insert x (Finset.univ.filter (fun y => G.Adj y x)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hy : y = x
    · subst hy; simp [hG.1 y]
    · rw [hG.2 x y (Ne.symm hy)]; simp [hy]
  rw [this, Finset.card_insert_of_notMem (by simp [hG.1 x]), idg]

lemma sum_od_eq_sum_idg {W : Type*} [Fintype W] (G : Digraph W) :
    ∑ x, od G x = ∑ x, idg G x := by
  simp only [od, idg, Finset.card_filter]
  exact Finset.sum_comm

lemma two_sum_od {W : Type*} [Fintype W] [DecidableEq W] (G : Digraph W) (hG : G.IsTournament) :
    2 * ∑ x, od G x + Fintype.card W = Fintype.card W * Fintype.card W := by
  have h : ∑ x, (od G x + (idg G x + 1)) = ∑ _x : W, Fintype.card W :=
    Finset.sum_congr rfl (fun x _ => od_add_idg G hG x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_od_eq_sum_idg] at h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  linarith

lemma arith_even (N : ℝ) (k : ℕ) :
    N * (N ^ 2 / 4) ^ k = (1 / 2 : ℝ) ^ (k + k) * N ^ (k + k + 1) := by
  rw [div_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, one_div_pow,
    show k + k = 2 * k by ring, pow_succ]
  field_simp

lemma arith_odd (N : ℝ) (k : ℕ) :
    (N ^ 2 / 4) ^ k * (N ^ 2 / 2) = (1 / 2 : ℝ) ^ (2 * k + 1) * N ^ (2 * k + 1 + 1) := by
  rw [div_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, one_div_pow,
    pow_succ, pow_succ, pow_succ]
  field_simp
  ring

theorem star_core (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)
    [DecidableRel G.Adj] [DecidableRel (Dstar n).Adj] (hG : G.IsTournament) :
    Digraph.homDensity (Dstar n) G ≤ (1 / 2 : ℝ) ^ n := by
  unfold Digraph.homDensity
  rw [homCount_star, Fintype.card_fin]
  set N : ℕ := Fintype.card W with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hoi : ∀ x, (od G x : ℝ) * idg G x ≤ (N : ℝ) ^ 2 / 4 := by
    intro x
    have h := od_add_idg G hG x
    have h' : (od G x : ℝ) + idg G x + 1 = N := by exact_mod_cast (by omega : od G x + idg G x + 1 = N)
    nlinarith [sq_nonneg ((od G x : ℝ) - idg G x)]
  rw [div_le_iff₀ (by positivity)]
  push_cast
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h1 : (n + 1) / 2 = k := by omega
    have h2 : n / 2 = k := by omega
    rw [h1, h2]
    calc ∑ x, (od G x : ℝ) ^ k * (idg G x : ℝ) ^ k ≤ ∑ _x : W, ((N : ℝ) ^ 2 / 4) ^ k := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (hoi x) k
      _ = (1 / 2 : ℝ) ^ n * (N : ℝ) ^ (n + 1) := by
          rw [Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul, hk]
          exact arith_even _ k
  · have h1 : (n + 1) / 2 = k + 1 := by omega
    have h2 : n / 2 = k := by omega
    rw [h1, h2]
    have hsum : (∑ x, (od G x : ℝ)) ≤ (N : ℝ) ^ 2 / 2 := by
      have := two_sum_od G hG
      have h' : 2 * (∑ x, (od G x : ℝ)) + N = N * N := by exact_mod_cast this
      nlinarith
    calc ∑ x, (od G x : ℝ) ^ (k + 1) * (idg G x : ℝ) ^ k
        ≤ ∑ x, ((N : ℝ) ^ 2 / 4) ^ k * (od G x : ℝ) := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          calc (od G x : ℝ) ^ (k + 1) * (idg G x : ℝ) ^ k
              = ((od G x : ℝ) * idg G x) ^ k * od G x := by ring
            _ ≤ ((N : ℝ) ^ 2 / 4) ^ k * od G x :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hoi x) k)
                  (by positivity)
      _ = ((N : ℝ) ^ 2 / 4) ^ k * ∑ x, (od G x : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) ^ 2 / 4) ^ k * ((N : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (1 / 2 : ℝ) ^ n * (N : ℝ) ^ (n + 1) := by
          rw [hk]
          exact arith_odd _ k


lemma Dstar_zero_succ (n : ℕ) (t : Fin n) : (Dstar n).Adj 0 t.succ ↔ out n t := by
  simp only [Dstar, Fin.succ_ne_zero, false_and, or_false, true_and, Fin.succ_inj,
    exists_eq_left']

lemma Dstar_succ_zero (n : ℕ) (t : Fin n) : (Dstar n).Adj t.succ 0 ↔ ¬ out n t := by
  simp only [Dstar, Fin.succ_ne_zero, false_and, false_or, true_and, Fin.succ_inj,
    exists_eq_left']

lemma Dstar_ne (n : ℕ) (i j : Fin (n + 1)) (h : (Dstar n).Adj i j) :
    (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0) := by
  rcases h with ⟨h0, t, ht, _⟩ | ⟨h0, t, ht, _⟩
  · exact Or.inl ⟨h0, ht ▸ Fin.succ_ne_zero t⟩
  · exact Or.inr ⟨h0, ht ▸ Fin.succ_ne_zero t⟩

theorem stars : OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.H1 := by
  intro V _ _ T _ hT hstar
  obtain ⟨c, hc⟩ := hstar
  have leaf : ∀ v, v ≠ c → T.Adj v c := by
    intro v hv
    obtain ⟨p⟩ := hT.connected.preconnected v c
    cases p with
    | nil => exact absurd rfl hv
    | cons h _ =>
      rcases hc _ _ h with h1 | h1
      · exact absurd h1 hv
      · exact h1 ▸ h
  have hadj : ∀ u v, T.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c) := by
    intro u v
    constructor
    · intro h
      rcases hc u v h with rfl | rfl
      · exact Or.inl ⟨rfl, (T.ne_of_adj h).symm⟩
      · exact Or.inr ⟨rfl, T.ne_of_adj h⟩
    · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
      · exact (leaf v hv).symm
      · exact leaf u hu
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨c⟩
  set n := Fintype.card V - 1 with hn
  let e0 : V ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by omega)
  let e : V ≃ Fin (n + 1) := e0.trans (Equiv.swap (e0 c) 0)
  have hec : e c = 0 := by simp [e]
  have he0 : ∀ u, e u = 0 ↔ u = c := fun u => by rw [← hec]; exact e.injective.eq_iff
  refine ⟨⟨fun u v => (Dstar n).Adj (e u) (e v)⟩, ⟨?_, ?_⟩, ?_⟩
  · intro u v h
    rw [hadj]
    rcases Dstar_ne n _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(he0 u).1 h1, fun h => h2 ((he0 v).2 h)⟩
    · exact Or.inr ⟨(he0 v).1 h1, fun h => h2 ((he0 u).2 h)⟩
  · intro u v h
    show (Dstar n).Adj (e u) (e v) ↔ ¬ (Dstar n).Adj (e v) (e u)
    rcases (hadj u v).1 h with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · obtain ⟨t, ht⟩ := Fin.exists_succ_eq.2 (fun h => hv ((he0 v).1 h))
      rw [hec, ← ht, Dstar_zero_succ, Dstar_succ_zero, not_not]
    · obtain ⟨t, ht⟩ := Fin.exists_succ_eq.2 (fun h => hu ((he0 u).1 h))
      rw [hec, ← ht, Dstar_zero_succ, Dstar_succ_zero]
  · intro W _ _ _ G _ hG
    rw [homDensity_comap e (Dstar n) _ (fun _ _ => Iff.rfl) G]
    have hcard : T.edgeFinset.card = n := by have := hT.card_edgeFinset; omega
    rw [hcard]
    exact star_core n G hG
end OMA.SidFinH1

theorem OMA.solution : OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.H1 :=
  OMA.SidFinH1.stars
