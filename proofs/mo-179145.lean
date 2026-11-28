import OMAStatements.S_mo_179145
import Mathlib



open OMA.S_mo_179145

private theorem independent_extension {V : Type} (G : SimpleGraph V) (S : Set V)
    (hs : Independent G S) :
    ∃ T : Set V, MaximalIndependent G T ∧ S ⊆ T := by
  classical
  let X := {T : Set V | Independent G T}
  obtain ⟨T,hST,hT⟩ := zorn_subset_nonempty X (by
    intro C hCX hChain _
    refine ⟨⋃₀ C,?_,fun U hU x hx => Set.mem_sUnion_of_mem hx hU⟩
    intro x hx y hy hxy
    obtain ⟨A,hA,hxA⟩ := Set.mem_sUnion.mp hx
    obtain ⟨B,hB,hyB⟩ := Set.mem_sUnion.mp hy
    rcases hChain.total hA hB with hAB | hBA
    · exact hCX hB (hAB hxA) hyB hxy
    · exact hCX hA hxA (hBA hyB) hxy) S hs
  refine ⟨T,⟨hT.1,?_⟩,hST⟩
  intro U hu hTU
  exact hTU.antisymm (hT.2 hu hTU)

private def incompatibilityGraph {V : Type} (H : Set (Set V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ¬ Cooccur H x y
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun ⟨E,hE,hy,hx⟩ => h.2 ⟨E,hE,hx,hy⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem covered_iff_indep {V : Type} (H : Set (Set V)) (S : Set V) :
    Covered H S ↔ Independent (incompatibilityGraph H) S := by
  classical
  constructor
  · intro h x hx y hy hne hn
    exact hn.2 (h hx hy hne)
  · intro h x hx y hy hne
    by_contra hn
    exact h hx hy hne ⟨hne,hn⟩

theorem OMA.solution : type_of% @OMA.S_mo_179145.main := by
  intro V H
  constructor
  · rintro ⟨G,hG⟩
    constructor
    · intro E he F hf hEF
      exact ((hG E).mp he).2 F ((hG F).mp hf).1 hEF
    · intro S hs
      have hi : Independent G S := by
        intro x hx y hy hne
        obtain ⟨E,hE,hxE,hyE⟩ := hs hx hy hne
        exact ((hG E).mp hE).1 hxE hyE hne
      obtain ⟨T,hT,hST⟩ := independent_extension G S hi
      exact ⟨T,(hG T).mpr hT,hST⟩
  · rintro ⟨hAnti,hConf⟩
    refine ⟨incompatibilityGraph H,fun S => ?_⟩
    constructor
    · intro hS
      have hC : Covered H S := fun _ hx _ hy _ => ⟨S,hS,hx,hy⟩
      refine ⟨(covered_iff_indep H S).mp hC,?_⟩
      intro T hT hST
      obtain ⟨E,hE,hTE⟩ := hConf T ((covered_iff_indep H T).mpr hT)
      have he : S = E := hAnti S hS E hE (hST.trans hTE)
      exact hST.antisymm (by simpa only [he] using hTE)
    · intro hS
      obtain ⟨E,hE,hSE⟩ := hConf S ((covered_iff_indep H S).mpr hS.1)
      have hEc : Covered H E := fun _ hx _ hy _ => ⟨E,hE,hx,hy⟩
      have he := hS.2 E ((covered_iff_indep H E).mp hEc) hSE
      simpa only [he] using hE
