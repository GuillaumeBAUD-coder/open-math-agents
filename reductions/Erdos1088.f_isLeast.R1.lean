import FormalConjectures.ErdosProblems.«1088»

-- Credit: @steveDOTdigital
namespace OMA.R_Erdos1088_f_isLeast_R1

open Erdos1088 Finset
open scoped EuclideanGeometry

-- Repeated coordinatewise monotone subsequence extraction yields an ordered chain.
def H1 : Prop :=
  ∀ d k : ℕ, ∃ m ≥ k, ∀ S : Finset (ℝ^d), S.card = m →
    ∃ p : Fin k ↪ (ℝ^d), (∀ i, p i ∈ S) ∧
      (∀ i j l : Fin k, i < j → j < l →
      dist (p i) (p j) < dist (p i) (p l) ∧ dist (p j) (p l) < dist (p i) (p l))

-- Along a chain, new edges at a fixed vertex have strictly increasing lengths.
-- Each previous length therefore excludes at most one candidate per vertex.
def H2 : Prop :=
  ∀ n : ℕ, ∃ k ≥ n, ∀ (d : ℕ) (p : Fin k ↪ (ℝ^d)),
    (∀ i j l : Fin k, i < j → j < l →
      dist (p i) (p j) < dist (p i) (p l) ∧ dist (p j) (p l) < dist (p i) (p l)) →
    HasSubsetWithDistinctDistances n (Finset.univ.map p)

theorem main : H1 → H2 → type_of% @Erdos1088.f_isLeast := by
  classical
  intro chains thin d n
  obtain ⟨k, hnk, hk⟩ := thin n
  obtain ⟨m, hkm, hm⟩ := chains d k
  have feasible : m ∈ cardSet d n := by
    refine ⟨hnk.trans hkm, ?_⟩
    intro S hS
    obtain ⟨p, hp, hchain⟩ := hm S hS
    obtain ⟨A, hA, hcard, hdist⟩ := hk d p hchain
    refine ⟨A, hA.trans ?_, hcard, hdist⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact hp i
  exact ⟨Nat.sInf_mem ⟨m, feasible⟩, fun _ hx => Nat.sInf_le hx⟩

end OMA.R_Erdos1088_f_isLeast_R1
