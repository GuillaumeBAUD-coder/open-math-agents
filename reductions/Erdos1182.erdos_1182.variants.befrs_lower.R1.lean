import FormalConjectures.ErdosProblems.«1182»

-- Reduction Erdos1182.erdos_1182.variants.befrs_lower.R1 of Erdős Problem 1182 — befrs lower
-- Credit: @dk8827
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! Reduce the sparse Ramsey bound to a small core and two general embedding lemmas.
The argument follows https://www.renyi.hu/~p_erdos/1980-04.pdf. -/

namespace OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1

open SimpleGraph

/-- The sparse core obtained by deleting leaves and shortening suspended paths
in the proof of Burr, Erdős, Faudree, Rousseau and Schelp, Theorem 1(a).
The degree-two vertices allow a further reduction to fewer than `4 * k` vertices. -/
def H1 : Prop :=
  ∀ {n : ℕ}, 4 ≤ n →
    ∀ (G : SimpleGraph (Fin n)), G.Connected → G.edgeSet.ncard ≤ n + (2 * n + 1) / 15 →
    ∀ (C : SimpleGraph (Fin (2 * n - 1))), C.CliqueFree 3 → ¬ G.IsContained Cᶜ →
    ∃ (l k : ℕ) (H : SimpleGraph (Fin l)) (D : Finset (Fin l)),
      15 * k ≤ 2 * n + 1 ∧ l ≤ 5 * k ∧ l - D.card < 4 * k ∧
      (H.induce (↑Dᶜ : Set (Fin l))).edgeSet.ncard ≤ l - D.card + k ∧
      (∀ x ∈ D, (H.neighborSet x).ncard ≤ 2) ∧ ¬ H.IsContained Cᶜ

/-- The general linear upper bound in the order and size of the blue graph
(Burr, Erdős, Faudree, Rousseau and Schelp, Lemma 1.2). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V) {m : ℕ} (C : SimpleGraph (Fin m)),
    C.CliqueFree 3 → Fintype.card V + 2 * H.edgeSet.ncard ≤ m → H.IsContained Cᶜ

/-- When the host has at least `3 * l - 2` vertices, a blue copy of
the induced graph with low-degree vertices removed extends to a blue copy of the graph.
A red neighborhood of size at least `l` can also give a full blue copy directly. -/
def H3 : Prop :=
  ∀ {l m : ℕ} (H : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),
    C.CliqueFree 3 → 3 * l - 2 ≤ m →
    ∀ (D : Finset (Fin l)), (∀ x ∈ D, (H.neighborSet x).ncard ≤ 2) →
    (H.induce (↑Dᶜ : Set (Fin l))).IsContained Cᶜ → H.IsContained Cᶜ

/-- The standard complete bipartite obstruction. This argument adapts the
project proof of the Ramsey lower bound by @ldy985. -/
lemma bipartite_obstruction {n b : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hlt : b < 2 * n - 1)
    (hb : ∀ C : SimpleGraph (Fin b), (⊤ : SimpleGraph (Fin 3)).IsContained C ∨
      G.IsContained Cᶜ) : False := by
  classical
  obtain ⟨v0⟩ := hG.nonempty
  have hn : 1 ≤ n := by have := v0.isLt; omega
  let bip : SimpleGraph (Fin b) := {
    Adj := fun i j => ¬ (i.1 < n - 1 ↔ j.1 < n - 1)
    symm := ⟨fun _ _ h h' => h h'.symm⟩
    loopless := ⟨fun _ h => h Iff.rfl⟩ }
  have bip_adj (i j : Fin b) : bip.Adj i j ↔ ¬ (i.1 < n - 1 ↔ j.1 < n - 1) := Iff.rfl
  rcases hb bip with h | h
  · obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp h
    have h01 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by simp)
    have h12 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by simp)
    have h02 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by simp)
    rw [comap_adj, bip_adj] at h01 h12 h02
    tauto
  · obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp h
    have key : ∀ u v : Fin n, G.Walk u v → ((f u).1 < n - 1 ↔ (f v).1 < n - 1) := by
      intro u v p
      induction p with
      | nil => exact Iff.rfl
      | cons hadj p ih =>
        have h1 := hf hadj
        rw [comap_adj, compl_adj, bip_adj] at h1
        exact (not_not.mp h1.2).trans ih
    have side : ∀ v : Fin n, ((f v0).1 < n - 1 ↔ (f v).1 < n - 1) := by
      intro v
      obtain ⟨p⟩ := hG.preconnected v0 v
      exact key v0 v p
    by_cases h0 : (f v0).1 < n - 1
    · let g : Fin n → Fin (n - 1) := fun v => ⟨(f v).1, (side v).mp h0⟩
      have hg : Function.Injective g := by
        intro x y hxy
        apply f.injective
        exact Fin.ext (by simpa [g] using hxy)
      have := Fintype.card_le_of_injective g hg
      simp at this
      omega
    · let g : Fin n → Fin (n - 1) := fun v =>
        ⟨(f v).1 - (n - 1), by
          have h1 := (f v).2
          have h2 : ¬ (f v).1 < n - 1 := fun h => h0 ((side v).mpr h)
          omega⟩
      have hg : Function.Injective g := by
        intro x y hxy
        have hx : ¬ (f x).1 < n - 1 := fun h => h0 ((side x).mpr h)
        have hy : ¬ (f y).1 < n - 1 := fun h => h0 ((side y).mpr h)
        have hxy' : (f x).1 - (n - 1) = (f y).1 - (n - 1) := by
          simpa [g] using hxy
        apply f.injective
        exact Fin.ext (by omega)
      have := Fintype.card_le_of_injective g hg
      simp at this
      omega


theorem main : H1 → H2 → H3 → type_of% @Erdos1182.erdos_1182.variants.befrs_lower := by
  classical
  intro hcore hlinear hext n hn
  apply Erdos1182.le_F
  · rw [Nat.choose_two_right]
    have hp : 3 * n ≤ n * (n - 1) := by
      simpa only [Nat.mul_comm 3 n] using Nat.mul_le_mul_left n (show 3 ≤ n - 1 by omega)
    omega
  intro G hG hedge
  have hramsey : ∀ (C : SimpleGraph (Fin (2 * n - 1))),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ := by
    intro C
    by_cases htriangle : C.CliqueFree 3
    · right
      by_contra hnot
      obtain ⟨l, k, H, D, hk, hl, hD, hH, hdeg, hbad⟩ := hcore hn G hG hedge C htriangle hnot
      let U := (↑Dᶜ : Set (Fin l))
      have hcard : Fintype.card U = l - D.card := by
        change Fintype.card ↥Dᶜ = _
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
      have hsparse : Fintype.card U + 2 * (H.induce U).edgeSet.ncard ≤ 2 * n - 1 := by
        have hle : (H.induce U).edgeSet.ncard ≤ l - D.card + k := hH
        omega
      exact hbad (hext H C htriangle (by omega) D hdeg
        (hlinear U (H.induce U) C htriangle hsparse))
    · exact Or.inl ((not_cliqueFree_iff_top_isContained 3).mp htriangle)
  unfold Erdos1182.IsTriangleGood SimpleGraph.graphRamsey
  exact le_antisymm (Nat.sInf_le hramsey)
    (le_csInf ⟨2 * n - 1, hramsey⟩ (fun b hb => by
      by_contra! hlt
      exact bipartite_obstruction G hG hlt hb))

end OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1
