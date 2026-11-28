import FormalConjectures.ErdosProblems.«23»
import Mathlib.Logic.Equiv.Fin.Basic

/-! Pack the 125 edges into 25 pentagons, indexed by intercept and slope modulo five. -/
namespace OMA.AffinePentagons

open SimpleGraph

abbrev Parameters := Fin 5 × Fin 5

def encode : Parameters ≃ Fin 25 := finProdFinEquiv

def layer (x : Fin 25) : Fin 5 := (encode.symm x).1

def pentagonGraph : SimpleGraph (Fin 25) :=
  fromRel fun x y => layer x + 1 = layer y

def vertex (p : Parameters) (i : Fin 5) : Fin 25 := encode (i, p.1 + i * p.2)

-- Orient a side by its layers; its two positions then recover the slope and intercept.
def readSide (x y : Fin 25) : Parameters :=
  let (u, v) := if layer x + 1 = layer y then (encode.symm x, encode.symm y)
                else (encode.symm y, encode.symm x)
  let d := v.2 - u.2
  (u.2 - u.1 * d, d)

lemma layers_triangleFree : pentagonGraph.CliqueFree 3 := by
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.mp ht
  let adjacent (a b : Fin 5) := a + 1 = b ∨ b + 1 = a
  have step {a b : Fin 25} (h : pentagonGraph.Adj a b) : adjacent (layer a) (layer b) :=
    ((fromRel_adj (fun u v : Fin 25 => layer u + 1 = layer v) a b).mp h).2
  have ht' : ∀ a b c : Fin 5, adjacent a b → adjacent a c → ¬ adjacent b c := by
    dsimp only [adjacent]
    decide +kernel
  exact ht' _ _ _ (step hxy) (step hxz) (step hyz)

lemma side_mem (p : Parameters) (i : Fin 5) :
    pentagonGraph.Adj (vertex p i) (vertex p (i + 1)) := by
  have facts : ∀ (q : Parameters) (j : Fin 5), vertex q j ≠ vertex q (j + 1) ∧
      layer (vertex q j) + 1 = layer (vertex q (j + 1)) := by decide +kernel
  exact (fromRel_adj _ _ _).mpr ⟨(facts p i).1, Or.inl (facts p i).2⟩

set_option maxRecDepth 4096 in
lemma read_both : ∀ (p : Parameters) (i : Fin 5),
    readSide (vertex p i) (vertex p (i + 1)) = p ∧
    readSide (vertex p (i + 1)) (vertex p i) = p := by decide +kernel

lemma recover {p q : Parameters} {i j : Fin 5}
    (h : s(vertex p i, vertex p (i + 1)) = s(vertex q j, vertex q (j + 1))) : p = q := by
  have hp := (read_both p i).1.symm
  rcases Sym2.eq_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy] at hp
    exact hp.trans (read_both q j).1
  · rw [hx, hy] at hp
    exact hp.trans (read_both q j).2

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
    refine ⟨i, Finset.mem_sdiff.mpr ⟨mem_edgeFinset.mpr (side_mem p i), ?_⟩⟩
    exact fun h => c.valid (mem_edgeFinset.mp h) hi
  choose idx hidx using omitted
  let pick (p : Parameters) : ↥missing :=
    ⟨s(vertex p (idx p), vertex p (idx p + 1)), hidx p⟩
  have inj : Function.Injective pick := fun _ _ h => recover (congrArg Subtype.val h)
  simpa only [Parameters, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective pick inj
