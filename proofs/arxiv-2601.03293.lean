import OMAStatements.S_arxiv_2601_03293

-- Problem: arxiv-2601.03293, the parity conjecture for real-rootedness of the independence
-- polynomial of the generalized Petersen graph GP(n,k).
--
-- The conjecture fails at n = 7. Since 2 * 3 = 6 = -1 mod 7, the graphs GP(7,2) and GP(7,3)
-- are isomorphic: swap the outer and inner rims and send index i to 3 * i mod 7. Isomorphic
-- graphs have the same independence polynomial, so the claimed equivalence would give
-- (real-rooted iff 2 is even) and (real-rooted iff 3 is even) for one and the same polynomial,
-- hence 3 would be even. The same happens for every n = 3 mod 4, where GP(n,2) is isomorphic to
-- GP(n,(n-1)/2) and (n-1)/2 is odd.

namespace OMA.D_arxiv_2601_03293

open OMA.S_arxiv_2601_03293

theorem indep_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (s : Finset V) (hs : ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v) :
    ∀ u ∈ s.map e.toEquiv.toEmbedding, ∀ v ∈ s.map e.toEquiv.toEmbedding, ¬ H.Adj u v := by
  intro x hx y hy hadj
  simp only [Finset.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact hs a ha b hb (e.map_adj_iff.mp hadj)

theorem indepPoly_eq_of_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    indepPoly G = indepPoly H := by
  classical
  unfold indepPoly
  refine Finset.sum_nbij' (fun s => s.map e.toEquiv.toEmbedding)
    (fun s => s.map e.toEquiv.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact indep_map e s hs
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact indep_map e.symm s hs
  · intro s _
    rw [Finset.map_map]
    convert Finset.map_refl (s := s)
    ext v
    exact e.toEquiv.symm_apply_apply v
  · intro s _
    ext v
    simp
  · intro s _
    simp

def phi : Fin 7 ⊕ Fin 7 ≃ Fin 7 ⊕ Fin 7 where
  toFun
    | Sum.inl i => Sum.inr (3 * i)
    | Sum.inr i => Sum.inl (3 * i)
  invFun
    | Sum.inl i => Sum.inr (5 * i)
    | Sum.inr i => Sum.inl (5 * i)
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

def iso : genPetersen 7 2 ≃g genPetersen 7 3 where
  toEquiv := phi
  map_rel_iff' := by
    rintro (a | a) (b | b) <;>
      simp only [genPetersen, phi, Equiv.coe_fn_mk] <;> revert a b <;> decide

end OMA.D_arxiv_2601_03293

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2601_03293.main) := by
  intro h
  have hp := OMA.D_arxiv_2601_03293.indepPoly_eq_of_iso OMA.D_arxiv_2601_03293.iso
  have h2 := (h 7 2 (by norm_num) (by norm_num) (by norm_num)).mpr (by decide)
  rw [hp] at h2
  have h3 := (h 7 3 (by norm_num) (by norm_num) (by norm_num)).mp h2
  exact absurd h3 (by decide)
