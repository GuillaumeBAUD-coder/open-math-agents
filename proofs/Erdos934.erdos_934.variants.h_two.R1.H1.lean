import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace OMA.CycleFiveBlowup
open SimpleGraph

def adjacent (i j : Fin 5) : Prop := (i.val+1)%5=j.val ∨ (j.val+1)%5=i.val

instance : DecidableRel adjacent := by
  intro i j
  unfold adjacent
  infer_instance

def graph (s : ℕ) : SimpleGraph (Fin 5 × Fin s) where
  Adj u v := adjacent u.1 v.1
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := by
    constructor
    intro v
    dsimp [adjacent]
    have h := v.1.isLt
    omega

instance (s : ℕ) : DecidableRel (graph s).Adj := by
  intro u v
  change Decidable (adjacent u.1 v.1)
  unfold adjacent
  infer_instance

lemma base_degree (i : Fin 5) : Fintype.card {j : Fin 5 // adjacent i j} = 2 := by
  fin_cases i <;> decide

lemma degree (s : ℕ) (v : Fin 5 × Fin s) : (graph s).degree v = 2*s := by
  let e : {w : Fin 5 × Fin s // (graph s).Adj v w} ≃
      {j : Fin 5 // adjacent v.1 j} × Fin s :=
    { toFun := fun w => (⟨w.val.1,w.property⟩,w.val.2)
      invFun := fun w => ⟨(w.1.val,w.2),w.1.property⟩
      left_inv := by rintro ⟨⟨i,j⟩,h⟩; rfl
      right_inv := by rintro ⟨⟨i,h⟩,j⟩; rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  change Fintype.card {w : Fin 5 × Fin s // (graph s).Adj v w} = 2*s
  rw [Fintype.card_congr e, Fintype.card_prod, base_degree, Fintype.card_fin]

lemma edges (s : ℕ) : (graph s).edgeFinset.card = 5*s^2 := by
  have h := (graph s).sum_degrees_eq_twice_card_edges
  simp_rw [degree] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith

lemma cross : ∀ i j k l : Fin 5, adjacent i j → adjacent k l →
    adjacent i k ∨ adjacent i l ∨ adjacent j k ∨ adjacent j l := by decide

lemma crossing {s : ℕ} (u v w x : Fin 5 × Fin s)
    (huv : (graph s).Adj u v) (hwx : (graph s).Adj w x) :
    (graph s).Adj u w ∨ (graph s).Adj u x ∨ (graph s).Adj v w ∨ (graph s).Adj v x :=
  cross u.1 v.1 w.1 x.1 huv hwx

end OMA.CycleFiveBlowup

open SimpleGraph

-- Step Erdos934.erdos_934.variants.h_two.R1.H1: hypothesis H1 of reduction Erdos934.erdos_934.variants.h_two.R1
-- Credit: @DeepDuke
-- H1 := ∀ d : ℕ, Even d → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),     (∀ v, (G.neighborSet v).ncard ≤ d) ∧ 5 * d ^ 2 / 4 ≤ G.edgeSet.ncard ∧ ¬ HasFarEdges G 2  /-- Chung–Gyárfás–Tuza–Trotter: maximum degree at most `d` and at least `⌊(5d² + 4)/4⌋` edges force two edges at distance at least `2`. -/

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 := by
  intro d hd
  classical
  obtain ⟨s,rfl⟩ := hd
  let G := OMA.CycleFiveBlowup.graph s
  have hc : Fintype.card (Fin 5 × Fin s) = 5*s := by simp
  let H := G.overFin hc
  let e : G ≃g H := G.overFinIso hc
  refine ⟨5*s,H,?_,?_,?_⟩
  · intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree,
      e.degree_eq, OMA.CycleFiveBlowup.degree]
    omega
  · rw [← H.coe_edgeFinset, Set.ncard_coe_finset, ← e.card_edgeFinset_eq,
      OMA.CycleFiveBlowup.edges]
    rw [show 5*(s+s)^2=4*(5*s^2) by ring]
    simp
  · rintro ⟨u,v,w,x,h1,h2,hdist⟩
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    obtain ⟨w,rfl⟩ := e.surjective w
    obtain ⟨x,rfl⟩ := e.surjective x
    have hu : G.Adj u v := e.map_rel_iff.mp h1
    have hw : G.Adj w x := e.map_rel_iff.mp h2
    have bad (a b : Fin 5 × Fin s) (ha : a=u ∨ a=v) (hb : b=w ∨ b=x)
        (hab : G.Adj a b) : False := by
      have hh := hdist (e a) (by rcases ha with rfl | rfl <;> simp)
        (e b) (by rcases hb with rfl | rfl <;> simp)
      have he : H.edist (e a) (e b) = 1 := H.edist_eq_one_iff_adj.mpr (e.map_rel_iff.mpr hab)
      rw [he] at hh
      norm_num at hh
    rcases OMA.CycleFiveBlowup.crossing u v w x hu hw with h | h | h | h
    · exact bad u w (Or.inl rfl) (Or.inl rfl) h
    · exact bad u x (Or.inl rfl) (Or.inr rfl) h
    · exact bad v w (Or.inr rfl) (Or.inl rfl) h
    · exact bad v x (Or.inr rfl) (Or.inr rfl) h

