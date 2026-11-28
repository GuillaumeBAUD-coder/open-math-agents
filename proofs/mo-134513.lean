import OMAStatements.S_mo_134513
import Mathlib

/-!
# MathOverflow 134513: the claw `K_{1,3}` is a counterexample

Take the star with centre `0` and leaves `1, 2, 3`. Every edge joins the centre (degree `3`) to
a leaf (degree `1`), so the degree difference is `2` on every edge. But the graph is not regular
(degrees `3` and `1` both occur), and it is not the path on three vertices because it has four
vertices.
-/

namespace OMA.MO134513

/-- The claw: vertex `0` is joined to `1, 2, 3`. -/
def claw : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun u v => u = 0 ∧ v ≠ 0

instance : DecidableRel claw.Adj := by
  unfold claw
  infer_instance

end OMA.MO134513

open OMA.MO134513 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_134513.main) := by
  intro h
  have hk : ∃ k : ℕ, ∀ u v : Fin 4, claw.Adj u v →
      Nat.dist (claw.degree u) (claw.degree v) = k := ⟨2, by decide⟩
  rcases h (Fin 4) claw hk with ⟨d, hd⟩ | ⟨⟨e⟩⟩
  · -- not regular: degrees `3` and `1`
    have h0 : claw.degree 0 = d := hd 0
    have h1 : claw.degree 1 = d := hd 1
    have e0 : claw.degree 0 = 3 := by decide
    have e1 : claw.degree 1 = 1 := by decide
    omega
  · -- not the path on three vertices: four vertices
    have := Fintype.card_congr e.toEquiv
    simp at this
