import OMAStatements.S_mo_462989
import Mathlib

/-!
MathOverflow 462989: an 8-vertex graph `G` with `G \ 0 ≅ G \ 1` but no automorphism mapping `0`
to `1` (vertex `1` has a neighbour adjacent to a leaf; vertex `0` does not).
-/

namespace OMA.P462989

/-- The edge list of an 8-vertex graph. -/
def L : List (Fin 8 × Fin 8) :=
  [(0, 3), (0, 5), (0, 7), (1, 4), (1, 6), (1, 7), (2, 6), (3, 5), (4, 7)]

def G : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun x y => (x, y) ∈ L)

instance : DecidableRel G.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ((x, y) ∈ L ∨ (y, x) ∈ L)))

/-- A bijection of `Fin 8` with `π 0 = 1` that restricts to `G \ 0 ≅ G \ 1`. -/
def π : Fin 8 ≃ Fin 8 where
  toFun := ![1, 0, 4, 6, 3, 2, 7, 5]
  invFun := ![1, 0, 5, 4, 2, 7, 3, 6]
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

lemma π_mem : ∀ x : Fin 8, x ≠ 0 ↔ π x ≠ 1 := by decide

lemma π_adj : ∀ x y : Fin 8, x ≠ 0 → y ≠ 0 → (G.Adj (π x) (π y) ↔ G.Adj x y) := by decide

def iso : G.induce {x | x ≠ 0} ≃g G.induce {x | x ≠ 1} where
  toEquiv := Equiv.subtypeEquiv π (fun x => π_mem x)
  map_rel_iff' := fun {a b} => π_adj a.1 b.1 a.2 b.2

lemma leaf : ∀ u c : Fin 8, (∀ x, G.Adj u x ↔ x = c) → c = 6 := by decide

lemma nbr0 : ∀ c : Fin 8, G.Adj 0 c → c ≠ 6 := by decide

lemma adj2 : ∀ y : Fin 8, G.Adj 2 y ↔ y = 6 := by decide

lemma adj16 : G.Adj 1 6 := by decide

/-- No automorphism of `G` maps `0` to `1`. -/
lemma no_aut (σ : G ≃g G) (h : σ 0 = 1) : False := by
  have hτ : σ.symm 1 = 0 := by rw [← h, RelIso.symm_apply_apply]
  have hu : ∀ x, G.Adj (σ.symm 2) x ↔ x = σ.symm 6 := by
    intro x
    rw [← σ.map_rel_iff, RelIso.apply_symm_apply, adj2]
    constructor
    · intro hx; rw [← hx, RelIso.symm_apply_apply]
    · intro hx; rw [hx, RelIso.apply_symm_apply]
  have h6 := leaf _ _ hu
  have h06 : G.Adj (σ.symm 1) (σ.symm 6) := σ.symm.map_rel_iff.2 adj16
  rw [hτ, h6] at h06
  exact nbr0 6 h06 rfl

theorem disproof_aux :
    ¬ ∀ (V : Type) (G : SimpleGraph V) (v w : V),
      Nonempty (G.induce {x | x ≠ v} ≃g G.induce {x | x ≠ w}) →
        ∃ σ : G ≃g G, σ v = w ∧ σ w = v := by
  intro h
  obtain ⟨σ, h1, -⟩ := h (Fin 8) G 0 1 ⟨iso⟩
  exact no_aut σ h1

end OMA.P462989

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_462989.main) := OMA.P462989.disproof_aux
