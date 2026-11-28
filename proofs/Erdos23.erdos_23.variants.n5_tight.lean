import FormalConjectures.ErdosProblems.«23»
import Mathlib.Logic.Equiv.Fin.Basic

/-! Twenty-five edge-disjoint pentagons in the balanced blow-up of the five-cycle.
The Latin-square labeling follows the general blowupC5_tight proof by @steveDOTdigital. -/
namespace OMA.AffinePentagons

open SimpleGraph

abbrev Parameters := Fin 5 × Fin 5

def encode : Parameters ≃ Fin 25 := finProdFinEquiv

def layer (x : Fin 25) : Fin 5 := (encode.symm x).1

def pentagonGraph : SimpleGraph (Fin 25) :=
  fromRel fun x y => layer x + 1 = layer y

def vertex (p : Parameters) (i : Fin 5) : Fin 25 :=
  encode (i, ![p.1, p.2, p.1, p.2, p.1 + p.2] i)

lemma layers_triangleFree : pentagonGraph.CliqueFree 3 := by
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.mp ht
  simp only [pentagonGraph, fromRel_adj] at hxy hxz hyz
  have incompatible : ∀ a b c : Fin 5,
      (a + 1 = b ∨ b + 1 = a) → (a + 1 = c ∨ c + 1 = a) →
      ¬ (b + 1 = c ∨ c + 1 = b) := by decide +kernel
  exact incompatible _ _ _ hxy.2 hxz.2 hyz.2

lemma adjacent : ∀ (p : Parameters) (i : Fin 5),
    pentagonGraph.Adj (vertex p i) (vertex p (i + 1)) := by
  simp only [pentagonGraph, fromRel_adj]
  decide +kernel

lemma recover {p q : Parameters} {i j : Fin 5}
    (h : s(vertex p i, vertex p (i + 1)) = s(vertex q j, vertex q (j + 1))) : p = q := by
  rcases Sym2.eq_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  all_goals
    have h₁ := encode.injective hx
    have h₂ := encode.injective hy
    fin_cases i <;> fin_cases j <;> simp_all [vertex, Prod.ext_iff]

lemma oddCycle : ∀ c : Fin 5 → Fin 2, ∃ i, c i = c (i + 1) := by decide +kernel

end OMA.AffinePentagons

open SimpleGraph OMA.AffinePentagons

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n5_tight := by
  classical
  refine ⟨pentagonGraph, layers_triangleFree, ?_⟩
  intro H _ hBip
  obtain ⟨c⟩ := hBip
  let missing := pentagonGraph.edgeFinset \ H.edgeFinset
  have omitted (p : Parameters) : ∃ i : Fin 5, s(vertex p i, vertex p (i + 1)) ∈ missing := by
    obtain ⟨i, hi⟩ := oddCycle (fun j => c (vertex p j))
    refine ⟨i, Finset.mem_sdiff.mpr ⟨mem_edgeFinset.mpr (adjacent p i), ?_⟩⟩
    exact fun h => c.valid (mem_edgeFinset.mp h) hi
  choose idx hidx using omitted
  let pick (p : Parameters) : ↥missing :=
    ⟨s(vertex p (idx p), vertex p (idx p + 1)), hidx p⟩
  have inj : Function.Injective pick := fun _ _ h => recover (congrArg Subtype.val h)
  simpa only [Parameters, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective pick inj
