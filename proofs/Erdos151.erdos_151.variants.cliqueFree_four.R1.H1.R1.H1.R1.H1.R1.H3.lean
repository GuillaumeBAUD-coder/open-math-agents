import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-!
# A 46-vertex witness for the lower bound on R(3,11)

This extracts the certificate for Geoffrey Exoo's graph from the accepted proof by
@mythintios in open-math-agents PR 9753. The search and extremal-size lemmas in that proof
are credited to @princek0. Adapted to the threshold in this reduction by @connoranderson.
-/

namespace ExooRamsey

open SimpleGraph

theorem independent_at_threshold (n : ℕ) (F : SimpleGraph (Fin n)) (tf : F.CliqueFree 3) :
    ∃ T, F.IsNIndepSet (Erdos151.H n) T := by
  let sizes : Set ℕ := {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ T, G.IsNIndepSet k T}
  have zero : 0 ∈ sizes := fun G _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  have limited : sizes ⊆ Set.Iic n := by
    intro k hk
    obtain ⟨T,hT⟩ := hk F tf
    simpa [hT.card_eq] using Finset.card_le_univ T
  have member : Erdos151.H n ∈ sizes := (show sizes.Nonempty from ⟨0,zero⟩).csSup_mem ((Set.finite_Iic n).subset limited)
  exact member F tf


/-- Branch on whether an independent set contains the first candidate. -/
def bounded {V : Type*} (adj : V → V → Bool) : ℕ → ℕ → List V → Bool
  | 0, cap, xs => decide (xs.length ≤ cap)
  | fuel + 1, cap, xs =>
    if xs.length ≤ cap then true else
      match cap, xs with
      | k + 1, a :: tail =>
        bounded adj fuel (k + 1) tail && bounded adj fuel k (tail.filter fun b => !adj a b)
      | _, _ => false

theorem bounded_sound {V : Type*} [DecidableEq V] (adj : V → V → Bool)
    (fuel cap : ℕ) (xs : List V) (s : Finset V) (checked : bounded adj fuel cap xs = true)
    (mem : ∀ x ∈ s, x ∈ xs) (ind : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → adj x y = false) :
    s.card ≤ cap := by
  have size_bound {t : Finset V} {ys : List V} (incl : ∀ x ∈ t, x ∈ ys) : t.card ≤ ys.length := by
    refine (Finset.card_le_card (show t ⊆ ys.toFinset from ?_)).trans ys.toFinset_card_le
    exact fun x hx => List.mem_toFinset.mpr (incl x hx)
  induction fuel generalizing cap xs s with
  | zero => exact (size_bound mem).trans (by simpa [bounded] using checked)
  | succ fuel ih =>
    by_cases short : xs.length ≤ cap
    · exact (size_bound mem).trans short
    cases xs with
    | nil => simp at short
    | cons a tail =>
      cases cap with
      | zero => simp [bounded] at checked
      | succ k =>
        have both : bounded adj fuel (k+1) tail = true ∧
            bounded adj fuel k (tail.filter fun b => !adj a b) = true := by
          have long : ¬ tail.length ≤ k := by simpa using short
          simpa [bounded, long] using checked
        by_cases ha : a ∈ s
        · have hsmall : (s.erase a).card ≤ k := by
            apply ih k _ (s.erase a) both.2
            · intro x hx
              obtain ⟨hxa, hs⟩ := Finset.mem_erase.mp hx
              apply List.mem_filter.mpr
              exact ⟨(List.mem_cons.mp (mem x hs)).resolve_left hxa, by simp [ind a ha x hs hxa.symm]⟩
            · intro x hx y hy hxy
              exact ind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
          have := Finset.card_erase_add_one ha
          omega
        · apply ih (k+1) tail s both.1 _ ind
          intro x hx
          exact (List.mem_cons.mp (mem x hx)).resolve_left (fun he => ha (he ▸ hx))


-- Zero off-diagonal entries in Exoo's r3.11.46 coloring, in bit-mask form.
private def exooNeighbors : Array Nat := #[
  11683385853442, 275457048785, 6608915021848, 601295461540,
  10449924002822, 2336533725960, 24192494355458, 45093264424970,
  4975753728032, 17592465502241, 35193129861209, 3588722130952,
  2406256493336, 13489569792512, 1409026101349, 8796519137544,
  9931307615266, 121333909680, 53957741289474, 1546259530564,
  21990304059393, 1475388408320, 101470208032, 48395825728002,
  35880727257152, 18764796003590, 9346691629088, 2886226453632,
  85966572176, 23125265743874, 4832047173, 35356177082692,
  4433520101520, 34383072644, 2336745464072, 2214593249288,
  13744204025856, 22009711431713, 52776560781314, 17661123625241,
  573393040, 35236045920357, 210999714116, 17660981125265,
  9758737433152, 2476074075264 ]

private def exooAdj (a b : Fin 46) : Bool := (exooNeighbors[a.val]!).testBit b.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem exoo_symm : ∀ a b : Fin 46, exooAdj a b = exooAdj b a := by
  decide +kernel

private theorem exoo_loopless : ∀ a : Fin 46, exooAdj a a = false := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem exoo_no_triangle :
    ∀ a b : Fin 46, exooAdj a b = true →
      ∀ c : Fin 46, exooAdj a c = true → exooAdj b c = false := by
  decide +kernel

-- Split the certificate by the least vertex of a nonempty independent set,
-- so the kernel checks smaller searches individually.
private def exooTail (i : Fin 46) : List (Fin 46) :=
  (List.finRange 46).filter fun j => decide (i < j) && !exooAdj i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem exoo_tail_cap (i : Fin 46) :
    bounded exooAdj 46 9 (exooTail i) = true := by
  fin_cases i <;> decide +kernel

private theorem exoo_indep_cap (T : Finset (Fin 46))
    (hind : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → exooAdj a b = false) : T.card ≤ 10 := by
  classical
  by_cases hT : T.Nonempty
  · let i := T.min' hT
    have hi : i ∈ T := T.min'_mem hT
    have hcard : (T.erase i).card ≤ 9 := by
      apply bounded_sound exooAdj 46 9 (exooTail i) _ (exoo_tail_cap i)
      · intro j hj
        obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
        have hlt : i < j := lt_of_le_of_ne (T.min'_le j hjT) hji.symm
        have hnj := hind i hi j hjT hji.symm
        exact List.mem_filter.mpr ⟨List.mem_finRange j, by simp [hlt, hnj]⟩
      · intro a ha b hb hne
        exact hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hne
    have heq := Finset.card_erase_add_one hi
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]

/-- Exoo's 46-vertex triangle-free Ramsey witness also bounds all smaller orders. -/
theorem at_most_ten_of_order_le_46 {n : ℕ} (hn : n ≤ 46) : Erdos151.H n ≤ 10 := by
  let e := Fin.castLEEmb hn
  let L : SimpleGraph (Fin n) :=
    { Adj := fun a b => exooAdj (e a) (e b) = true
      symm := ⟨by intro a b h; rwa [exoo_symm]⟩
      loopless := ⟨by
        intro a h
        exact Bool.noConfusion ((exoo_loopless (e a)).symm.trans h)⟩ }
  have free : L.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp ht
    exact Bool.noConfusion ((exoo_no_triangle (e a) (e b) hab (e c) hac).symm.trans hbc)
  obtain ⟨s, hs⟩ := independent_at_threshold n L free
  have hbound : (s.map e).card ≤ 10 := by
    apply exoo_indep_cap
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact Bool.eq_false_iff.mpr (hs.isIndepSet ha hb (fun he => hxy (congrArg e he)))
  simpa only [Finset.card_map, hs.card_eq] using hbound

end ExooRamsey

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1.H3 := by
  intro n h
  by_contra! hn
  have := ExooRamsey.at_most_ten_of_order_le_46 (n := n) (by omega)
  omega
