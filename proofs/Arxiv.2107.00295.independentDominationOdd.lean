import FormalConjectures.Arxiv.«2107.00295».IndependentDomination
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.BigOperators

/-!
The proof of Corollary 1.3 in [Cho, Kim, Kim and Oum](https://arxiv.org/abs/2202.09594)
separates the subcubic bound from the argument for larger odd degree bounds,
and lifts connected-component bounds to arbitrary isolate-free graphs.
-/

namespace OMA.OddDomination

/-- The independent domination bound for isolate-free subcubic graphs. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    0 < G.minDegree → G.maxDegree ≤ 3 →
    2 * G.indepDominationNumber ≤ Fintype.card V

/-- The connected case of Corollary 1.3 for an odd degree bound of at least five. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ), 5 ≤ D → Odd D → 0 < G.minDegree → G.maxDegree ≤ D → G.Connected →
    let m := (D + 2)^2 / 4
    m * G.indepDominationNumber ≤ (m - D) * Fintype.card V

/-- A uniform linear bound for connected graphs extends to their disjoint unions. -/
def H3 : Prop :=
  ∀ (D A B : ℕ),
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < G.minDegree → G.maxDegree ≤ D → G.Connected →
      A * G.indepDominationNumber ≤ B * Fintype.card V) →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < G.minDegree → G.maxDegree ≤ D →
      A * G.indepDominationNumber ≤ B * Fintype.card V

section Subcubic

open Finset SimpleGraph

private def nbSub {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) := S.filter (G.Adj v)

private def lostSub {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :=
  S.filter fun x ↦ x ≠ v ∧ nbSub G S x ⊆ nbSub G S v

private lemma goodSub {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : S.Nonempty)
    (hn : ∀ v ∈ S, (nbSub G S v).Nonempty) (hdeg : ∀ v ∈ S, (nbSub G S v).card ≤ 3) :
    ∃ v ∈ S, (lostSub G S v).card < (nbSub G S v).card := by
  classical
  let N := nbSub G S
  let Z := lostSub G S
  have nmem (x y : V) : y ∈ N x ↔ y ∈ S ∧ G.Adj x y := mem_filter
  have zmem (x y : V) : y ∈ Z x ↔ y ∈ S ∧ y ≠ x ∧ N y ⊆ N x := mem_filter
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun x ↦ (N x).card) hS
  by_cases hgood : (Z v).card < (N v).card
  · exact ⟨v, hv, hgood⟩
  let T := insert v (Z v)
  have hTcard : T.card = (Z v).card + 1 := card_insert_of_notMem (by simp [Z, lostSub])
  have htwin {t : V} (ht : t ∈ T) : t ∈ S ∧ N t = N v := by
    rcases mem_insert.mp ht with rfl | ht
    · exact ⟨hv, rfl⟩
    obtain ⟨hts, _, hs⟩ := (zmem _ _).mp ht
    exact ⟨hts, eq_of_subset_of_card_le hs (hmin t hts)⟩
  obtain ⟨w, hw⟩ := hn v hv
  change w ∈ N v at hw
  have hws := ((nmem _ _).mp hw).1
  have hsub : T ⊆ N w := by
    intro t ht
    obtain ⟨hts, heq⟩ := htwin ht
    exact (nmem _ _).mpr ⟨hts, (((nmem _ _).mp (heq.symm ▸ hw)).2).symm⟩
  have hcount := card_le_card hsub
  have hwdeg := hdeg w hws
  have hpos := card_pos.mpr (hn v hv)
  change 0 < (N v).card at hpos
  change (N w).card ≤ 3 at hwdeg
  have touch {x t : V} (hx : x ∈ S) (ht : t ∈ T) (hxt : G.Adj x t) : x ∈ N v := by
    rw [← (htwin ht).2]
    exact (nmem _ _).mpr ⟨hx, hxt.symm⟩
  refine ⟨w, hws, ?_⟩
  change (Z w).card < (N w).card
  by_cases hall : T = N w
  · have hsubset : Z w ⊆ (N v).erase w := by
      intro x hx
      obtain ⟨hxs, hxw, hxn⟩ := (zmem _ _).mp hx
      obtain ⟨t, ht⟩ := hn x hxs
      exact mem_erase.mpr ⟨hxw, touch hxs (hall.symm ▸ hxn ht) ((nmem _ _).mp ht).2⟩
    have h := card_le_card hsubset
    rw [card_erase_of_mem hw] at h
    omega
  · have hlt : T.card < (N w).card :=
      lt_of_not_ge (fun h ↦ hall (eq_of_subset_of_card_le hsub h))
    have hc : ((N w) \ T).card = 1 := by rw [card_sdiff_of_subset hsub]; omega
    obtain ⟨y, hy⟩ := card_eq_one.mp hc
    have hyw : y ∈ N w := (mem_sdiff.mp (show y ∈ N w \ T by simp [hy])).1
    have hys := ((nmem _ _).mp hyw).1
    have hwy := (nmem y w).mpr ⟨hws, ((nmem _ _).mp hyw).2.symm⟩
    have hvnum : (N v).card ≤ 1 := by omega
    have hvone : N v = {w} := eq_of_subset_of_card_le (singleton_subset_iff.mpr hw)
      (by simpa only [card_singleton] using hvnum) |>.symm
    have hsubset : Z w ⊆ (N y).erase w := by
      intro x hx
      obtain ⟨hxs, hxw, hxn⟩ := (zmem _ _).mp hx
      obtain ⟨t, ht⟩ := hn x hxs
      have ha := ((nmem _ _).mp ht).2
      have hnot : t ∉ T := by
        intro h
        have h' := touch hxs h ha
        exact hxw (by simpa [hvone] using h')
      have hty : t = y := by
        have h := mem_sdiff.mpr ⟨hxn ht, hnot⟩
        simpa [hy] using h
      subst t
      exact mem_erase.mpr ⟨hxw, (nmem _ _).mpr ⟨hxs, ha.symm⟩⟩
    have h := card_le_card hsubset
    have hydeg := hdeg y hys
    change (N y).card ≤ 3 at hydeg
    rw [card_erase_of_mem hwy] at h
    omega

private lemma solveSub {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hn : ∀ v ∈ S, (nbSub G S v).Nonempty)
    (hdeg : ∀ v ∈ S, (nbSub G S v).card ≤ 3) :
    ∃ D ⊆ S, G.IsIndepSet (D : Set V) ∧
      (∀ x ∈ S, x ∈ D ∨ ∃ y ∈ D, G.Adj x y) ∧ 2 * D.card ≤ S.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    case neg =>
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], by simp, by simp⟩
    obtain ⟨v, hv, hgood⟩ := goodSub G hS hn hdeg
    let N := nbSub G S v
    let Z := lostSub G S v
    let A := insert v N
    let R := (S \ A) \ Z
    change Z.card < N.card at hgood
    have nmem {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj v x := mem_filter
    have zmem {x : V} : x ∈ Z ↔ x ∈ S ∧ x ≠ v ∧ nbSub G S x ⊆ N := mem_filter
    have vn : v ∉ N := fun h ↦ G.loopless.irrefl v (nmem.mp h).2
    have vz : v ∉ Z := fun h ↦ (zmem.mp h).2.1 rfl
    have nadj {x y : V} (hx : x ∈ Z) (hy : y ∈ S) (ha : G.Adj x y) : y ∈ N :=
      (zmem.mp hx).2.2 (mem_filter.mpr ⟨hy, ha⟩)
    have zn {x : V} (hx : x ∈ Z) : x ∉ N := fun h ↦
      vn (nadj hx hv (nmem.mp h).2.symm)
    have amem {x : V} : x ∈ A ↔ x = v ∨ x ∈ N := mem_insert
    have asub : A ⊆ S := fun x hx ↦ (amem.mp hx).elim (fun h ↦ h ▸ hv) (fun h ↦ (nmem.mp h).1)
    have zsub : Z ⊆ S \ A := fun x hx ↦ mem_sdiff.mpr
      ⟨(zmem.mp hx).1, fun h ↦ (amem.mp h).elim (zmem.mp hx).2.1 (zn hx)⟩
    have rmem {x : V} : x ∈ R ↔ x ∈ S ∧ x ≠ v ∧ x ∉ N ∧ x ∉ Z := by
      simp [R, A, and_assoc, not_or]
    have rsub : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨fun x hx ↦ (rmem.mp hx).1, fun h ↦ (rmem.mp (h.symm ▸ hv)).2.1 rfl⟩
    have rnb : ∀ x ∈ R, (nbSub G R x).Nonempty := by
      intro x hx
      obtain ⟨hxs, hxv, hxn, hxz⟩ := rmem.mp hx
      have hnot : ¬ nbSub G S x ⊆ N := fun h ↦ hxz (zmem.mpr ⟨hxs, hxv, h⟩)
      obtain ⟨y, hy, hyN⟩ := Finset.not_subset.mp hnot
      obtain ⟨hys, hxy⟩ := mem_filter.mp hy
      have hyv : y ≠ v := by
        rintro rfl
        exact hxn (nmem.mpr ⟨hxs, hxy.symm⟩)
      have hyz : y ∉ Z := fun h ↦ hxn (nadj h hxs hxy.symm)
      exact ⟨y, mem_filter.mpr ⟨rmem.mpr ⟨hys, hyv, hyN, hyz⟩, hxy⟩⟩
    have rdeg : ∀ x ∈ R, (nbSub G R x).card ≤ 3 := by
      intro x hx
      exact (card_le_card (filter_subset_filter _ (Finset.ssubset_iff_subset_ne.mp rsub).1)).trans
        (hdeg x (rmem.mp hx).1)
    obtain ⟨D, hd, hi, hdom, hcard⟩ := ih R rsub rnb rdeg
    let C := insert v (Z ∪ D)
    have cmem {x : V} : x ∈ C ↔ x = v ∨ x ∈ Z ∨ x ∈ D := by simp [C]
    have dmem {x : V} (hx : x ∈ D) := rmem.mp (hd hx)
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases cmem.mp hx with rfl | h | h
      · exact hv
      · exact (zmem.mp h).1
      · exact (dmem h).1
    · intro x hx y hy hne hxy
      change x ∈ C at hx
      change y ∈ C at hy
      rcases cmem.mp hx with rfl | hxZ | hxD <;> rcases cmem.mp hy with rfl | hyZ | hyD
      · exact hne rfl
      · exact zn hyZ (nmem.mpr ⟨(zmem.mp hyZ).1, hxy⟩)
      · exact (dmem hyD).2.2.1 (nmem.mpr ⟨(dmem hyD).1, hxy⟩)
      · exact zn hxZ (nmem.mpr ⟨(zmem.mp hxZ).1, hxy.symm⟩)
      · exact zn hyZ (nadj hxZ (zmem.mp hyZ).1 hxy)
      · exact (dmem hyD).2.2.1 (nadj hxZ (dmem hyD).1 hxy)
      · exact (dmem hxD).2.2.1 (nmem.mpr ⟨(dmem hxD).1, hxy.symm⟩)
      · exact (dmem hxD).2.2.1 (nadj hyZ (dmem hxD).1 hxy.symm)
      · exact hi hxD hyD hne hxy
    · intro x hxs
      by_cases hx : x ∈ C
      · exact Or.inl hx
      right
      by_cases hn : x ∈ N
      · exact ⟨v, cmem.mpr (Or.inl rfl), (nmem.mp hn).2.symm⟩
      have hxv : x ≠ v := fun h ↦ hx (cmem.mpr (Or.inl h))
      have hxz : x ∉ Z := fun h ↦ hx (cmem.mpr (Or.inr (Or.inl h)))
      rcases hdom x (rmem.mpr ⟨hxs, hxv, hn, hxz⟩) with h | ⟨y, hy, hxy⟩
      · exact False.elim (hx (cmem.mpr (Or.inr (Or.inr h))))
      · exact ⟨y, cmem.mpr (Or.inr (Or.inr hy)), hxy⟩
    · have hc : C.card ≤ (Z ∪ D).card + 1 := card_insert_le _ _
      have hu := card_union_le Z D
      have ha : A.card = N.card + 1 := card_insert_of_notMem vn
      have hz : R.card + Z.card = (S \ A).card := card_sdiff_add_card_eq_card zsub
      have hrest := card_sdiff_add_card_eq_card asub
      omega

lemma subcubic_bound : H1 := by
  intro V _ _ G _ hmin hmax
  classical
  have hnb (x : V) : nbSub G univ x = G.neighborFinset x := by
    ext y
    simp [nbSub]
  have hn : ∀ x ∈ (univ : Finset V), (nbSub G univ x).Nonempty := by
    intro x _
    rw [hnb, ← card_pos, card_neighborFinset_eq_degree]
    exact hmin.trans_le (G.minDegree_le_degree _)
  have hd : ∀ x ∈ (univ : Finset V), (nbSub G univ x).card ≤ 3 := by
    intro x _
    rw [hnb, card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree x).trans hmax
  obtain ⟨D, _, hi, hdom, hc⟩ := solveSub G univ hn hd
  have hD : G.IsNIndepDominatingSet D.card D := ⟨hi, fun x ↦ hdom x (mem_univ x), rfl⟩
  have hle : G.indepDominationNumber ≤ D.card := Nat.sInf_le ⟨D, hD⟩
  simpa using (Nat.mul_le_mul_left 2 hle).trans hc

end Subcubic

section DominationBound

open Finset SimpleGraph

private def nb {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) := S.filter (G.Adj v)

private def lost {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :=
  S.filter fun x ↦ x ≠ v ∧ nb G S x ⊆ nb G S v

private def Result {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (D B : ℕ) : Prop :=
  ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
    (∀ x ∈ S, x ∈ I ∨ ∃ y ∈ I, G.Adj x y) ∧ (B + D) * I.card ≤ B * S.card

private lemma extend {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {D B : ℕ} {v : V} (hv : v ∈ S)
    (hgood : D * ((lost G S v).card + 1) ≤ B * (nb G S v).card)
    (hr : ∀ R ⊂ S, (∀ x ∈ R, (nb G R x).Nonempty) → Result G R D B) :
    Result G S D B := by
  classical
  let N := nb G S v
  let Z := lost G S v
  let A := insert v N
  let R := (S \ A) \ Z
  change D * (Z.card + 1) ≤ B * N.card at hgood
  have nmem {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj v x := mem_filter
  have zmem {x : V} : x ∈ Z ↔ x ∈ S ∧ x ≠ v ∧ nb G S x ⊆ N := mem_filter
  have vn : v ∉ N := fun h ↦ G.loopless.irrefl v (nmem.mp h).2
  have vz : v ∉ Z := fun h ↦ (zmem.mp h).2.1 rfl
  have nadj {x y : V} (hx : x ∈ Z) (hy : y ∈ S) (ha : G.Adj x y) : y ∈ N :=
    (zmem.mp hx).2.2 (mem_filter.mpr ⟨hy, ha⟩)
  have zn {x : V} (hx : x ∈ Z) : x ∉ N := fun h ↦
    vn (nadj hx hv (nmem.mp h).2.symm)
  have amem {x : V} : x ∈ A ↔ x = v ∨ x ∈ N := mem_insert
  have asub : A ⊆ S := fun x hx ↦ (amem.mp hx).elim (fun h ↦ h ▸ hv) (fun h ↦ (nmem.mp h).1)
  have zsub : Z ⊆ S \ A := fun x hx ↦ mem_sdiff.mpr
    ⟨(zmem.mp hx).1, fun h ↦ (amem.mp h).elim (zmem.mp hx).2.1 (zn hx)⟩
  have rmem {x : V} : x ∈ R ↔ x ∈ S ∧ x ≠ v ∧ x ∉ N ∧ x ∉ Z := by
    simp [R, A, and_assoc, not_or]
  have rsub : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr
    ⟨fun x hx ↦ (rmem.mp hx).1, fun h ↦ (rmem.mp (h.symm ▸ hv)).2.1 rfl⟩
  have rnb : ∀ x ∈ R, (nb G R x).Nonempty := by
    intro x hx
    obtain ⟨hxs, hxv, hxn, hxz⟩ := rmem.mp hx
    have hnot : ¬ nb G S x ⊆ N := fun h ↦ hxz (zmem.mpr ⟨hxs, hxv, h⟩)
    obtain ⟨y, hy, hyN⟩ := Finset.not_subset.mp hnot
    obtain ⟨hys, hxy⟩ := mem_filter.mp hy
    have hyv : y ≠ v := by
      rintro rfl
      exact hxn (nmem.mpr ⟨hxs, hxy.symm⟩)
    have hyz : y ∉ Z := fun h ↦ hxn (nadj h hxs hxy.symm)
    exact ⟨y, mem_filter.mpr ⟨rmem.mpr ⟨hys, hyv, hyN, hyz⟩, hxy⟩⟩
  obtain ⟨I, hd, hi, hdom, hcard⟩ := hr R rsub rnb
  let C := insert v (Z ∪ I)
  have cmem {x : V} : x ∈ C ↔ x = v ∨ x ∈ Z ∨ x ∈ I := by simp [C]
  have dmem {x : V} (hx : x ∈ I) := rmem.mp (hd hx)
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases cmem.mp hx with rfl | h | h
    · exact hv
    · exact (zmem.mp h).1
    · exact (dmem h).1
  · intro x hx y hy hne hxy
    change x ∈ C at hx
    change y ∈ C at hy
    rcases cmem.mp hx with rfl | hxZ | hxD <;> rcases cmem.mp hy with rfl | hyZ | hyD
    · exact hne rfl
    · exact zn hyZ (nmem.mpr ⟨(zmem.mp hyZ).1, hxy⟩)
    · exact (dmem hyD).2.2.1 (nmem.mpr ⟨(dmem hyD).1, hxy⟩)
    · exact zn hxZ (nmem.mpr ⟨(zmem.mp hxZ).1, hxy.symm⟩)
    · exact zn hyZ (nadj hxZ (zmem.mp hyZ).1 hxy)
    · exact (dmem hyD).2.2.1 (nadj hxZ (dmem hyD).1 hxy)
    · exact (dmem hxD).2.2.1 (nmem.mpr ⟨(dmem hxD).1, hxy.symm⟩)
    · exact (dmem hxD).2.2.1 (nadj hyZ (dmem hxD).1 hxy.symm)
    · exact hi hxD hyD hne hxy
  · intro x hxs
    by_cases hx : x ∈ C
    · exact Or.inl hx
    right
    by_cases hn : x ∈ N
    · exact ⟨v, cmem.mpr (Or.inl rfl), (nmem.mp hn).2.symm⟩
    have hxv : x ≠ v := fun h ↦ hx (cmem.mpr (Or.inl h))
    have hxz : x ∉ Z := fun h ↦ hx (cmem.mpr (Or.inr (Or.inl h)))
    rcases hdom x (rmem.mpr ⟨hxs, hxv, hn, hxz⟩) with h | ⟨y, hy, hxy⟩
    · exact False.elim (hx (cmem.mpr (Or.inr (Or.inr h))))
    · exact ⟨y, cmem.mpr (Or.inr (Or.inr hy)), hxy⟩
  · have hc : C.card ≤ (Z ∪ I).card + 1 := card_insert_le _ _
    have hu := card_union_le Z I
    have ha : A.card = N.card + 1 := card_insert_of_notMem vn
    have hz : R.card + Z.card = (S \ A).card := card_sdiff_add_card_eq_card zsub
    have hrest := card_sdiff_add_card_eq_card asub
    have hci : C.card ≤ Z.card + I.card + 1 := by omega
    have hc' := Nat.mul_le_mul_left (B + D) hci
    have hsc : R.card + Z.card + (N.card + 1) = S.card := by omega
    rw [← hsc]
    nlinarith

private def leaves {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :=
  (nb G S v).filter fun w ↦ (nb G S w).card = 1

private lemma loss_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hn : ∀ x ∈ S, (nb G S x).Nonempty)
    (hl : ∀ x ∈ S, 2 ≤ (nb G S x).card → (leaves G S x).Nonempty)
    {v : V} (hv : v ∈ S) (hmax : ∀ x ∈ S, (leaves G S x).card ≤ (leaves G S v).card) :
    (lost G S v).card ≤ ((nb G S v).card - (leaves G S v).card) * (leaves G S v).card := by
  classical
  let N := nb G S
  let L := leaves G S
  let Z := lost G S v
  have nm {x y : V} : y ∈ N x ↔ y ∈ S ∧ G.Adj x y := mem_filter
  have lm {x y : V} : y ∈ L x ↔ y ∈ N x ∧ (N y).card = 1 := mem_filter
  have sub : Z ⊆ ((N v) \ L v).biUnion L := by
    intro x hx
    obtain ⟨hxs, hxv, hsub⟩ : x ∈ S ∧ x ≠ v ∧ N x ⊆ N v := mem_filter.mp hx
    have deg2 {y : V} (hy : y ∈ N x) : 2 ≤ (N y).card := by
      have hys := (nm.mp hy).1
      have hyx := nm.mpr ⟨hxs, (nm.mp hy).2.symm⟩
      have hyv := nm.mpr ⟨hv, (nm.mp (hsub hy)).2.symm⟩
      have h : ({x, v} : Finset V) ⊆ N y := by
        intro a ha
        rcases mem_insert.mp ha with rfl | h
        · exact hyx
        · exact mem_singleton.mp h ▸ hyv
      simpa [card_pair hxv] using card_le_card h
    have hxc : (N x).card = 1 := by
      have hp := card_pos.mpr (hn x hxs)
      change 0 < (N x).card at hp
      by_contra! h
      obtain ⟨y, hy⟩ := hl x hxs (by change 2 ≤ (N x).card; omega)
      obtain ⟨hy', hc⟩ := lm.mp hy
      have := deg2 hy'
      omega
    obtain ⟨y, hy⟩ := hn x hxs
    have hnot : y ∉ L v := fun h ↦ (by have := deg2 hy; have := (lm.mp h).2; omega)
    exact mem_biUnion.mpr ⟨y, mem_sdiff.mpr ⟨hsub hy, hnot⟩,
      lm.mpr ⟨nm.mpr ⟨hxs, (nm.mp hy).2.symm⟩, hxc⟩⟩
  have hle : L v ⊆ N v := filter_subset _ _
  change Z.card ≤ ((N v).card - (L v).card) * (L v).card
  calc Z.card ≤ _ := card_le_card sub
       _ ≤ ∑ x ∈ (N v) \ L v, (L x).card := card_biUnion_le
       _ ≤ ∑ _x ∈ (N v) \ L v, (L v).card :=
         sum_le_sum fun x hx ↦ hmax x (nm.mp (mem_sdiff.mp hx).1).1
       _ = _ := by rw [sum_const, smul_eq_mul, card_sdiff_of_subset hle]

private lemma ratio {D d t k : ℕ} (hD : D = 2 * k + 1) (hk : 2 ≤ k)
    (hd : 1 ≤ d) (hdD : d ≤ D) (htd : t ≤ d) :
    D * ((d - t) * t + 1) ≤ (k * (k + 1) + 1) * d := by
  let B := k * (k + 1) + 1
  have hb : D ≤ B := by dsimp [B]; nlinarith
  by_cases ht : t = 0
  · subst t; simp; exact hb.trans (by simpa using Nat.mul_le_mul_left B hd)
  have hmax : (D - t) * t ≤ k * (k + 1) := by
    have he : D - t + t = D := Nat.sub_add_cancel (htd.trans hdD)
    zify at he hD ⊢
    rcases le_or_gt t k with h | h
    · have h₁ : (0 : ℤ) ≤ (k : ℤ) - t := by omega
      nlinarith [mul_nonneg h₁ (show (0 : ℤ) ≤ (k : ℤ) + 1 - t by omega),
        congrArg (fun z : ℤ ↦ z * t) he, congrArg (fun z : ℤ ↦ z * t) hD]
    · have h₁ : (0 : ℤ) ≤ (t : ℤ) - (k + 1) := by omega
      nlinarith [mul_nonneg h₁ (show (0 : ℤ) ≤ (t : ℤ) - k by omega),
        congrArg (fun z : ℤ ↦ z * t) he, congrArg (fun z : ℤ ↦ z * t) hD]
  have he : d - t + t = d := Nat.sub_add_cancel htd
  have he' : D - t + t = D := Nat.sub_add_cancel (htd.trans hdD)
  have hr : D - d + d = D := Nat.sub_add_cancel hdD
  change D * ((d - t) * t + 1) ≤ B * d
  by_cases h : D * t ≤ B
  · have h₁ := Nat.mul_le_mul_right (d - t) h
    have h₂ := Nat.mul_le_mul_left B (show 1 ≤ t by omega)
    nlinarith
  · have h₁ := Nat.mul_le_mul_right (D - d) (show B ≤ D * t by omega)
    have h₂ : D * ((D - t) * t + 1) ≤ D * B := Nat.mul_le_mul_left D (by dsimp [B]; omega)
    nlinarith

private def cut {V : Type*} (G : SimpleGraph V) (v w : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x = v → y = w) ∧ (y = v → x = w)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1.ne rfl⟩

private lemma lift_cut {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {v w : V} {S : Finset V} {D B : ℕ} (hw : w ∈ S) :
    Result (cut G v w) S D B → Result G S D B := by
  classical
  rintro ⟨I, hI, hi, hdom, hcard⟩
  have domG (x : V) (hx : x ∈ S) : x ∈ I ∨ ∃ y ∈ I, G.Adj x y :=
    (hdom x hx).imp_right fun ⟨y, hy, h⟩ ↦ ⟨y, hy, h.1⟩
  by_cases hind : G.IsIndepSet (I : Set V)
  · exact ⟨I, hI, hind, domG, hcard⟩
  let E := I.erase v
  have emem {x : V} : x ∈ E ↔ x ≠ v ∧ x ∈ I := mem_erase
  have ie : G.IsIndepSet (E : Set V) := by
    intro x hx y hy hne h
    exact hi (emem.mp hx).2 (emem.mp hy).2 hne
      ⟨h, fun h ↦ False.elim ((emem.mp hx).1 h), fun h ↦ False.elim ((emem.mp hy).1 h)⟩
  have hvI : v ∈ I := by
    by_contra hv
    apply hind
    simpa [E, erase_eq_of_notMem hv] using ie
  obtain ⟨q, hq, hvq⟩ : ∃ q ∈ E, G.Adj v q := by
    by_contra! h
    apply hind
    intro x hx y hy hne ha
    by_cases hxv : x = v
    · subst x
      exact h y (emem.mpr ⟨hne.symm, hy⟩) ha
    by_cases hyv : y = v
    · subst y
      exact h x (emem.mpr ⟨hne, hx⟩) ha.symm
    exact ie (emem.mpr ⟨hxv, hx⟩) (emem.mpr ⟨hyv, hy⟩) hne ha
  have esub : E ⊆ S := (erase_subset v I).trans hI
  have ec : E.card + 1 = I.card := card_erase_add_one hvI
  have edom (x : V) (hx : x ∈ S) (hxw : x ≠ w) : x ∈ E ∨ ∃ y ∈ E, G.Adj x y := by
    by_cases hxv : x = v
    · subst x; exact Or.inr ⟨q, hq, hvq⟩
    rcases hdom x hx with h | ⟨y, hy, ha⟩
    · exact Or.inl (emem.mpr ⟨hxv, h⟩)
    · exact Or.inr ⟨y, emem.mpr ⟨fun h ↦ hxw (ha.2.2 h), hy⟩, ha.1⟩
  by_cases h : w ∈ E ∨ ∃ y ∈ E, G.Adj w y
  · refine ⟨E, esub, ie, ?_, (Nat.mul_le_mul_left _ (by omega : E.card ≤ I.card)).trans hcard⟩
    intro x hx
    by_cases he : x = w
    · simpa [he] using h
    · exact edom x hx he
  · refine ⟨insert w E, insert_subset hw esub, ?_, ?_, ?_⟩
    · intro x hx y hy hne hxy
      rcases mem_insert.mp hx with rfl | hxE <;> rcases mem_insert.mp hy with rfl | hyE
      · exact hne rfl
      · exact h (Or.inr ⟨y, hyE, hxy⟩)
      · exact h (Or.inr ⟨x, hxE, hxy.symm⟩)
      · exact ie hxE hyE hne hxy
    · intro x hx
      by_cases he : x = w
      · exact Or.inl (mem_insert.mpr (Or.inl he))
      rcases edom x hx he with h | ⟨y, hy, hxy⟩
      · exact Or.inl (mem_insert_of_mem h)
      · exact Or.inr ⟨y, mem_insert_of_mem hy, hxy⟩
    · exact (Nat.mul_le_mul_left _ ((card_insert_le w E).trans_eq ec)).trans hcard

private noncomputable def measure {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  S.card + G.edgeSet.ncard

private lemma solve {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype V] (D k : ℕ) (hD : D = 2 * k + 1) (hk : 2 ≤ k)
    (S : Finset V) (hn : ∀ x ∈ S, (nb G S x).Nonempty)
    (hd : ∀ x ∈ S, (nb G S x).card ≤ D) : Result G S D (k * (k + 1) + 1) := by
  classical
  let B := k * (k + 1) + 1
  by_cases hS : S.Nonempty
  case neg =>
    rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], by simp, by simp⟩
  by_cases hl : ∀ x ∈ S, 2 ≤ (nb G S x).card → (leaves G S x).Nonempty
  · obtain ⟨v, hv, hm⟩ := S.exists_max_image (fun x ↦ (leaves G S x).card) hS
    have h₁ := loss_bound G hn hl hv hm
    have h₂ := ratio hD hk (card_pos.mpr (hn v hv)) (hd v hv)
      (card_le_card (show leaves G S v ⊆ nb G S v from filter_subset _ _))
    apply extend G hv ((Nat.mul_le_mul_left D (Nat.add_le_add_right h₁ 1)).trans h₂)
    intro R hR hr
    have hlt : measure G R < measure G S := by
      dsimp [measure]; exact Nat.add_lt_add_right (card_lt_card hR) _
    apply solve G D k hD hk R hr
    intro x hx
    exact (card_le_card (filter_subset_filter _ (Finset.ssubset_iff_subset_ne.mp hR).1)).trans
      (hd x ((Finset.ssubset_iff_subset_ne.mp hR).1 hx))
  · push Not at hl
    obtain ⟨v, hv, hvc, hvl⟩ := hl
    obtain ⟨w, hw⟩ := hn v hv
    let K := cut G v w
    have nm {x y : V} : y ∈ nb G S x ↔ y ∈ S ∧ G.Adj x y := mem_filter
    have km {x y : V} : y ∈ nb K S x ↔ y ∈ S ∧ G.Adj x y ∧
        (x = v → y = w) ∧ (y = v → x = w) := mem_filter
    have hws := (nm.mp hw).1
    have hvw := (nm.mp hw).2
    have hnonleaf {y : V} (hy : y ∈ nb G S v) : 2 ≤ (nb G S y).card := by
      have hpos := card_pos.mpr (hn y (nm.mp hy).1)
      by_contra! hh
      have hyL : y ∈ leaves G S v := mem_filter.mpr ⟨hy, by omega⟩
      simp_all
    have hK : ∀ x ∈ S, (nb K S x).Nonempty := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        exact ⟨w, km.mpr ⟨hws, hvw, fun _ ↦ rfl, fun h ↦ h.symm⟩⟩
      by_cases hxa : G.Adj v x
      · have hc := hnonleaf (nm.mpr ⟨hx, hxa⟩)
        have hh := card_erase_of_mem (nm.mpr ⟨hv, hxa.symm⟩)
        obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((nb G S x).erase v).card by omega)
        obtain ⟨hyv, hy'⟩ := mem_erase.mp hy
        exact ⟨y, km.mpr ⟨(nm.mp hy').1, (nm.mp hy').2, fun h ↦ False.elim (hxv h),
          fun h ↦ False.elim (hyv h)⟩⟩
      · obtain ⟨y, hy⟩ := hn x hx
        obtain ⟨hys, hxy⟩ := nm.mp hy
        exact ⟨y, km.mpr ⟨hys, hxy, fun h ↦ False.elim (hxv h),
          fun h ↦ False.elim (hxa (h ▸ hxy.symm))⟩⟩
    have hle : K ≤ G := fun _ _ h ↦ h.1
    have hstrict : K < G := by
      refine lt_iff_le_not_ge.mpr ⟨hle, ?_⟩
      intro hback
      have he := card_erase_of_mem hw
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < ((nb G S v).erase w).card by omega)
      obtain ⟨hzw, hz'⟩ := mem_erase.mp hz
      exact hzw ((hback (nm.mp hz').2).2.1 rfl)
    have hlt : measure K S < measure G S := by
      dsimp [measure]
      apply Nat.add_lt_add_left
      exact Set.ncard_lt_ncard (edgeSet_strict_mono hstrict)
    apply lift_cut G (v := v) hws
    apply solve K D k hD hk S hK
    intro x hx
    exact (card_le_card (show nb K S x ⊆ nb G S x from
      fun y hy ↦ nm.mpr ⟨(km.mp hy).1, (km.mp hy).2.1⟩)).trans (hd x hx)
termination_by measure G S
decreasing_by all_goals assumption

lemma connected_bound : H2 := by
  intro V _ _ G _ D hD hodd hmin hmax _
  obtain ⟨k, he⟩ := hodd
  have hk : 2 ≤ k := by omega
  let B := k * (k + 1) + 1
  have hnb (x : V) : nb G univ x = G.neighborFinset x := by
    ext y
    simp [nb]
  have hn : ∀ x ∈ (univ : Finset V), (nb G univ x).Nonempty := by
    intro x _
    rw [hnb, ← card_pos, card_neighborFinset_eq_degree]
    exact hmin.trans_le (G.minDegree_le_degree _)
  have hd : ∀ x ∈ (univ : Finset V), (nb G univ x).card ≤ D := by
    intro x _
    rw [hnb, card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree x).trans hmax
  obtain ⟨I, _, hi, hdom, hc⟩ := solve G D k (by omega) hk univ hn hd
  have hI : G.IsNIndepDominatingSet I.card I := ⟨hi, fun x ↦ hdom x (mem_univ x), rfl⟩
  have hle : G.indepDominationNumber ≤ I.card := Nat.sInf_le ⟨I, hI⟩
  have hm : (D + 2)^2 = 4 * (B + D) + 1 := by dsimp [B]; rw [he]; ring
  have hh : (D + 2)^2 / 4 = B + D := by omega
  dsimp only
  rw [hh, Nat.add_sub_cancel]
  simpa [B] using (Nat.mul_le_mul_left (B + D) hle).trans hc

end DominationBound

section Components

lemma exists_minimal_independent_dominating_set {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsNIndepDominatingSet G.indepDominationNumber s := by
  classical
  obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
  have hmax := hs.isMaximalIndepSet s
  have hdom : G.IsDominating s := by
    intro v
    by_cases hv : v ∈ (s : Set V)
    · exact Or.inl hv
    · right
      by_contra hmissing
      have hins : G.IsIndepSet (insert v (s : Set V)) := by
        apply Set.Pairwise.insert_of_notMem hv hs.isIndepSet
        intro w hw
        exact ⟨fun h ↦ hmissing ⟨w, hw, h⟩, fun h ↦ hmissing ⟨w, hw, h.symm⟩⟩
      have hsub : insert v (s : Set V) ⊆ s := hmax.2 hins (Set.subset_insert _ _)
      exact hv (hsub (Set.mem_insert _ _))
  have hnonempty : {n | ∃ s : Finset V, G.IsNIndepDominatingSet n s}.Nonempty :=
    ⟨s.card, s, hs.isIndepSet, hdom, rfl⟩
  exact Nat.sInf_mem hnonempty

lemma degree_in_component {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) [Fintype ↥c] [DecidableRel c.toSimpleGraph.Adj] (v : ↥c) :
    c.toSimpleGraph.degree v = G.degree v.val := by
  classical
  let e : c.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun w ↦ ⟨w.val.val, w.property⟩
      invFun := fun w ↦ ⟨⟨w.val, c.mem_supp_of_adj_mem_supp v.property w.property⟩, w.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e

set_option maxHeartbeats 1000000 in
lemma components_lift : H3 := by
  intro D A B bound V _ _ G _ hmin hmax
  classical
  have hcomponent (c : G.ConnectedComponent) :
      A * c.toSimpleGraph.indepDominationNumber ≤ B * Fintype.card (↥c) := by
    have hconn := c.connected_toSimpleGraph
    have : Nonempty (↥c) := hconn.nonempty
    have hpos : 0 < c.toSimpleGraph.minDegree := by
      apply c.toSimpleGraph.le_minDegree_of_forall_le_degree 1
      intro v
      rw [degree_in_component G c v]
      exact hmin.trans_le (G.minDegree_le_degree v.val)
    have hdegree : c.toSimpleGraph.maxDegree ≤ D := by
      apply c.toSimpleGraph.maxDegree_le_of_forall_degree_le
      intro v
      rw [degree_in_component G c v]
      exact (G.degree_le_maxDegree v.val).trans hmax
    exact bound (↥c) c.toSimpleGraph hpos hdegree hconn
  choose sets hsets using
    fun c : G.ConnectedComponent ↦ exists_minimal_independent_dominating_set c.toSimpleGraph
  let e : (Σ c : G.ConnectedComponent, ↥c) ≃ V :=
    Equiv.sigmaFiberEquiv G.connectedComponentMk
  let s : Finset V := (Finset.univ.sigma sets).map e.toEmbedding
  have hmem (c : G.ConnectedComponent) (v : ↥c) : v.val ∈ s ↔ v ∈ sets c := by
    change e ⟨c, v⟩ ∈ (Finset.univ.sigma sets).map e.toEmbedding ↔ _
    rw [Finset.mem_map_equiv, e.symm_apply_apply]
    simp
  have hindep : G.IsIndepSet s := by
    intro v hv w hw hne hadj
    let c := G.connectedComponentMk v
    let v' : ↥c := ⟨v, rfl⟩
    let w' : ↥c := ⟨w, c.mem_supp_of_adj_mem_supp v'.property hadj⟩
    have hv' : v' ∈ sets c := (hmem c v').mp hv
    have hw' : w' ∈ sets c := (hmem c w').mp hw
    exact (hsets c).isIndep hv' hw' (fun h ↦ hne (congrArg Subtype.val h)) hadj
  have hdom : G.IsDominating s := by
    intro v
    let c := G.connectedComponentMk v
    let v' : ↥c := ⟨v, rfl⟩
    rcases (hsets c).isDominating v' with hv | ⟨w, hw, hadj⟩
    · exact Or.inl ((hmem c v').mpr hv)
    · exact Or.inr ⟨w.val, (hmem c w).mpr hw, hadj⟩
  have hle : G.indepDominationNumber ≤ s.card :=
    Nat.sInf_le ⟨s, hindep, hdom, rfl⟩
  have hcard : s.card = ∑ c : G.ConnectedComponent, c.toSimpleGraph.indepDominationNumber := by
    simp only [s, Finset.card_map, Finset.card_sigma, fun c ↦ (hsets c).card_eq]
  have hpartition : (∑ c : G.ConnectedComponent, Fintype.card (↥c)) = Fintype.card V := by
    rw [← Fintype.card_sigma, Fintype.card_congr e]
  calc
    _ ≤ A * s.card := Nat.mul_le_mul_left A hle
    _ = ∑ c : G.ConnectedComponent, A * c.toSimpleGraph.indepDominationNumber := by
      rw [hcard, Finset.mul_sum]
    _ ≤ ∑ c : G.ConnectedComponent, B * Fintype.card (↥c) :=
      Finset.sum_le_sum (fun c _ ↦ hcomponent c)
    _ = _ := by rw [← Finset.mul_sum, hpartition]

end Components

lemma map_indep_dominating_set {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) {n : ℕ} {s : Finset V} (hs : G.IsNIndepDominatingSet n s) :
    K.IsNIndepDominatingSet n (s.map e.toEquiv.toEmbedding) := by
  have hmem {x : W} : x ∈ s.map e.toEquiv.toEmbedding ↔ e.symm x ∈ s := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  refine ⟨?_, ?_, (Finset.card_map _).trans hs.card_eq⟩
  · intro x hx y hy hne hadj
    exact hs.isIndep (hmem.mp hx) (hmem.mp hy) (fun h ↦ hne (e.symm.injective h))
      (e.symm.map_rel_iff.mpr hadj)
  · intro x
    rcases hs.isDominating (e.symm x) with hx | ⟨y, hy, hxy⟩
    · exact Or.inl (hmem.mpr hx)
    · refine Or.inr ⟨e y, hmem.mpr (by simpa using hy), e.symm.map_rel_iff.mp ?_⟩
      simpa using hxy

lemma indep_domination_number_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) : G.indepDominationNumber = K.indepDominationNumber := by
  unfold SimpleGraph.indepDominationNumber
  congr 1
  ext n
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨_, map_indep_dominating_set e hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨_, map_indep_dominating_set e.symm hs⟩

lemma combine_bounds
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hIso : 0 < G.minDegree) (hOdd : Odd G.maxDegree) :
    (G.maxDegree + 1) * (G.maxDegree + 3) * G.indepDominationNumber ≤
      (G.maxDegree^2 + 3) * Fintype.card V := by
  let D := G.maxDegree
  let m := (D + 2)^2 / 4
  change (D + 1) * (D + 3) * G.indepDominationNumber ≤ (D^2 + 3) * Fintype.card V
  by_cases hsmall : D ≤ 3
  · have hbound := subcubic_bound V G hIso hsmall
    obtain ⟨k, hk⟩ := hOdd
    change D = 2 * k + 1 at hk
    have hc : D = 1 ∨ D = 3 := by omega
    rcases hc with hc | hc <;> rw [hc] <;> norm_num <;> omega
  · have hlarge : 5 ≤ D := by
      obtain ⟨k, hk⟩ := hOdd
      change D = 2 * k + 1 at hk
      omega
    have hconnected (W : Type) [Fintype W] [DecidableEq W] (K : SimpleGraph W)
        [DecidableRel K.Adj] (hpos : 0 < K.minDegree) (hmax : K.maxDegree ≤ D)
        (hconn : K.Connected) :
        m * K.indepDominationNumber ≤ (m - D) * Fintype.card W :=
      connected_bound W K D hlarge hOdd hpos hmax hconn
    have hbound := components_lift D m (m - D) hconnected V G hIso le_rfl
    obtain ⟨k, hk⟩ := hOdd
    change D = 2 * k + 1 at hk
    have hsq : (D + 2)^2 = 4 * ((k + 1) * (k + 2)) + 1 := by rw [hk]; ring
    have hm : m = (k + 1) * (k + 2) := by
      change (D + 2)^2 / 4 = _
      omega
    have hDm : D ≤ m := by rw [hm, hk]; nlinarith
    have hleft : (D + 1) * (D + 3) = 4 * m := by rw [hm, hk]; ring
    have hright_add : D^2 + 3 + 4 * D = 4 * m := by rw [hm, hk]; ring
    have hright : D^2 + 3 = 4 * (m - D) := by omega
    rw [hleft, hright, mul_assoc, mul_assoc]
    exact Nat.mul_le_mul_left 4 hbound

end OMA.OddDomination

theorem OMA.solution : type_of% @Arxiv.«2107.00295».independentDominationOdd := by
  intro V _ _ G _ hIso hOdd
  classical
  let e := Fintype.equivFin V
  let K := G.map e.toEmbedding
  have eK : G ≃g K := SimpleGraph.Iso.map e G
  have hmin := eK.minDegree_eq
  have hmax := eK.maxDegree_eq
  have hi := OMA.OddDomination.indep_domination_number_eq_of_iso eK
  have hpos : 0 < K.minDegree := hmin ▸ hIso
  have hodd : Odd K.maxDegree := hmax ▸ hOdd
  have hbound := OMA.OddDomination.combine_bounds _ K hpos hodd
  change (G.maxDegree + 1) * (G.maxDegree + 3) * G.indepDominationNumber ≤
    (G.maxDegree^2 + 3) * Fintype.card V
  rw [hmax, hi]
  simpa only [K, Fintype.card_fin] using hbound
