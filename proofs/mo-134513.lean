import OMAStatements.S_mo_134513
import Mathlib

-- Problem mo-134513: the statement claims that a finite graph in which the degrees of any two adjacent vertices
-- differ by the same constant k is either regular or isomorphic to the path on three vertices.
-- Upstream: statements/mo-134513.lean (declaration OMA.S_mo_134513.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: the star with one centre and three leaves. The centre has degree 3 and each leaf has degree 1, so
-- the degrees of adjacent vertices always differ by 2. The star is not regular, and it has four vertices, so it
-- is not isomorphic to the path on three vertices.

private def starAdj (a b : Fin 4) : Prop := a ≠ b ∧ (a = 0 ∨ b = 0)

private instance : DecidableRel starAdj := fun a b => by
  unfold starAdj
  infer_instance

private def star : SimpleGraph (Fin 4) where
  Adj := starAdj
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel star.Adj := fun a b => inferInstanceAs (Decidable (starAdj a b))

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_134513.main) := by
  intro h
  have hyp' : ∀ p : Fin 4 × Fin 4, star.Adj p.1 p.2 →
      Nat.dist (star.degree p.1) (star.degree p.2) = 2 := by decide
  have hyp : ∃ k : ℕ, ∀ u v : Fin 4, star.Adj u v → Nat.dist (star.degree u) (star.degree v) = k :=
    ⟨2, fun u v huv => hyp' (u, v) huv⟩
  rcases h (Fin 4) star hyp with ⟨d, hd⟩ | hne
  · have h0 := hd 0
    have h1 := hd 1
    have e0 : star.degree 0 = 3 := by decide
    have e1 : star.degree 1 = 1 := by decide
    omega
  · obtain ⟨e⟩ := hne
    have hcard := Fintype.card_congr e.toEquiv
    simp at hcard
