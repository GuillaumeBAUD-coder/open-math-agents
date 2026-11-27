import FormalConjectures.WrittenOnTheWallII.GraphConjecture96
import Mathlib.Tactic

-- Problem: Written on the Wall II - Conjecture 96
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean:56 (declaration WrittenOnTheWallII.GraphConjecture96.conjecture96)
-- Credit: @jagong-cmu (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA96

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_parent (G : SimpleGraph V) (hG : G.Connected) (v x : V) (hx : x ≠ v) :
    ∃ y, G.Adj x y ∧ G.dist v y + 1 = G.dist v x := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x v
  cases p with
  | nil => exact absurd rfl hx
  | @cons _ y _ h q =>
    refine ⟨y, h, ?_⟩
    have h1 : G.dist y v ≤ q.length := dist_le q
    have h2 : 0 < G.dist x v := hG.pos_dist_of_ne hx
    have h3 := h.diff_dist_adj (u := v)
    rw [dist_comm (u := y) (v := v)] at h1
    rw [dist_comm (u := x) (v := v)] at hp h2
    simp only [Walk.length_cons] at hp
    omega

lemma card_le_indepNeighborsCard (G : SimpleGraph V) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, G.Adj u x) (hI : G.IsIndepSet (S : Set V)) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard
  let T : Finset (G.neighborSet u) := S.subtype (fun x => x ∈ G.neighborSet u)
  have hT : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hS x hx)
  rw [← hT]
  apply IsIndepSet.card_le_indepNum
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
  simp only [comap_adj, Function.Embedding.subtype_apply]
  exact hI ha hb (fun h => hab (Subtype.ext h))

lemma not_adj_of_gap (G : SimpleGraph V) {v a b : V} (h : G.dist v a + 2 ≤ G.dist v b) :
    ¬ G.Adj a b := by
  intro hab
  have := hab.diff_dist_adj (u := v)
  omega

lemma main_bound (G : SimpleGraph V) (hG : G.Connected) (v : V) (L : ℕ)
    (hL : ∀ u, indepNeighborsCard G u ≤ L) (hL1 : 1 ≤ L)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    I.card + distEven G v ≤ 1 + distEven G v * L := by
  classical
  have hpar : ∀ x, x ≠ v → ∃ y, G.Adj x y ∧ G.dist v y + 1 = G.dist v x :=
    fun x hx => exists_parent G hG v x hx
  choose! par hpar1 hpar2 using hpar
  have hpos : ∀ x, x ≠ v → 0 < G.dist v x := fun x hx => hG.pos_dist_of_ne (Ne.symm hx)
  unfold distEven
  set E := Finset.univ.filter (fun w => Even (G.dist v w)) with hE
  let f : V → V := fun x => if Even (G.dist v x) then x else par x
  have hvE : v ∈ E := by simp [hE]
  have hfE : ∀ x ∈ I, f x ∈ E := by
    intro x _
    by_cases hx : Even (G.dist v x)
    · simp [f, hx, hE]
    · have hxv : x ≠ v := by
        rintro rfl
        simp at hx
      have h2 := hpar2 x hxv
      simp only [f, hx, if_false, hE, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h2, Nat.even_add_one] at hx
      exact not_not.mp hx
  have hsum : I.card = ∑ u ∈ E, (I.filter (fun x => f x = u)).card :=
    Finset.card_eq_sum_card_fiberwise hfE
  have hmemF : ∀ u ∈ E, ∀ x ∈ I.filter (fun x => f x = u),
      x = u ∨ (G.Adj u x ∧ G.dist v x = G.dist v u + 1) := by
    intro u _ x hx
    rw [Finset.mem_filter] at hx
    by_cases hxe : Even (G.dist v x)
    · left
      simpa [f, hxe] using hx.2
    · right
      have hxv : x ≠ v := by
        rintro rfl
        simp at hxe
      have hfx : par x = u := by simpa [f, hxe] using hx.2
      rw [← hfx]
      exact ⟨(hpar1 x hxv).symm, (hpar2 x hxv).symm⟩
  have hfib : ∀ u ∈ E, (I.filter (fun x => f x = u)).card + (if u = v then 0 else 1) ≤ L := by
    intro u hu
    have hue : Even (G.dist v u) := by simpa [hE] using hu
    set F := I.filter (fun x => f x = u) with hF
    have hFI : F ⊆ I := Finset.filter_subset _ _
    by_cases huF : u ∈ F
    · -- F = {u}
      have hF1 : F.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        have hu' : u ∈ I := hFI huF
        rcases hmemF u hu a ha with rfl | ⟨haa, _⟩
        · rcases hmemF a hu b hb with rfl | ⟨hbb, _⟩
          · rfl
          · exact absurd hbb (hI hu' (hFI hb) (fun h => by
              subst h
              exact G.irrefl hbb))
        · exfalso
          exact hI hu' (hFI ha) (fun h => by subst h; exact G.irrefl haa) haa
      by_cases huv : u = v
      · simp only [huv, if_true]
        omega
      · simp only [huv, if_false]
        -- need L ≥ 2
        have hdu := hpos u huv
        have hdu2 : 2 ≤ G.dist v u := by
          obtain ⟨k, hk⟩ := hue
          omega
        have hp1 := hpar1 u huv
        have hp2 := hpar2 u huv
        generalize par u = p at hp1 hp2
        have hpv : p ≠ v := by
          intro hpv
          rw [hpv, dist_self] at hp2
          omega
        have hq1 := hpar1 p hpv
        have hq2 := hpar2 p hpv
        generalize par p = q at hq1 hq2
        have hS : ∀ x ∈ ({u, q} : Finset V), G.Adj p x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hp1.symm
          · rw [Finset.mem_singleton.mp hx]
            exact hq1
        have hqu : q ≠ u := by
          intro h
          rw [h] at hq2
          omega
        have hind : G.IsIndepSet ((({u, q} : Finset V)) : Set V) := by
          intro a ha b hb hab
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · intro h
            exact not_adj_of_gap G (v := v) (a := b) (b := a) (by omega) h.symm
          · exact not_adj_of_gap G (v := v) (a := a) (b := b) (by omega)
          · exact absurd rfl hab
        have h2 := card_le_indepNeighborsCard G p _ hS hind
        rw [Finset.card_pair hqu.symm] at h2
        have := hL p
        omega
    · have hFN : ∀ x ∈ F, G.Adj u x ∧ G.dist v x = G.dist v u + 1 := by
        intro x hx
        rcases hmemF u hu x hx with rfl | h
        · exact absurd hx huF
        · exact h
      have hFind : G.IsIndepSet (F : Set V) := hI.mono (by exact_mod_cast hFI)
      by_cases huv : u = v
      · simp only [huv, if_true, add_zero]
        have := card_le_indepNeighborsCard G u F (fun x hx => (hFN x hx).1) hFind
        have := hL u
        omega
      · simp only [huv, if_false]
        have hp1 := hpar1 u huv
        have hp2 := hpar2 u huv
        generalize par u = p at hp1 hp2
        have hpF : p ∉ F := by
          intro hp
          have := (hFN p hp).2
          omega
        have hS : ∀ x ∈ insert p F, G.Adj u x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hp1
          · exact (hFN x hx).1
        have hind : G.IsIndepSet ((insert p F : Finset V) : Set V) := by
          intro a ha b hb hab
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · have := (hFN b hb).2
            exact not_adj_of_gap G (v := v) (by omega)
          · have := (hFN a ha).2
            intro h
            exact not_adj_of_gap G (v := v) (a := b) (b := a) (by omega) h.symm
          · exact hFind ha hb hab
        have h2 := card_le_indepNeighborsCard G u _ hS hind
        rw [Finset.card_insert_of_notMem hpF] at h2
        have := hL u
        omega
  have hle := Finset.sum_le_sum hfib
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← hsum] at hle
  have hcnt : ∑ u ∈ E, (if u = v then 0 else 1) + 1 = E.card := by
    rw [← Finset.add_sum_erase E _ hvE, if_pos rfl, zero_add,
      Finset.sum_congr rfl (g := fun _ => 1) (fun x hx => if_neg (Finset.ne_of_mem_erase hx)),
      Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hvE]
    have := Finset.card_pos.mpr ⟨v, hvE⟩
    omega
  have hE1 : 1 ≤ E.card := Finset.card_pos.mpr ⟨v, hvE⟩
  nlinarith

end OMA96

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  intro α _ _ _ G h minDistEven maxL
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image (SimpleGraph.distEven G))
    (Finset.univ_nonempty.image _))
  have hL : ∀ u, SimpleGraph.indepNeighborsCard G u ≤ maxL := fun u =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hL1 : 1 ≤ maxL := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    obtain ⟨y, hy, -⟩ := OMA96.exists_parent G h b a hab
    have := OMA96.card_le_indepNeighborsCard G a {y} (by simpa using hy)
      (by simp [SimpleGraph.IsIndepSet])
    simp only [Finset.card_singleton] at this
    exact this.trans (hL a)
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hnat := OMA96.main_bound G h v maxL hL hL1 s hs.isIndepSet
  rw [hs.card_eq, hv] at hnat
  have hR : ((G.indepNum + minDistEven : ℕ) : ℝ) ≤ ((1 + minDistEven * maxL : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  push_cast at hR
  linarith
