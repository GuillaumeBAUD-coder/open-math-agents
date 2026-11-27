import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Perm

/-! Double-count the incidences between sets and colorings that give them distinct colors. -/

namespace RainbowCounting

private noncomputable def extendColor {α : Type} {n : ℕ} (s : Finset α)
    (fallback : Fin n) (c : s → Fin n) (x : α) : Fin n := by
  classical
  exact if hx : x ∈ s then c ⟨x, hx⟩ else fallback

-- Choose a bijection on A and independently color all the remaining points.
open scoped Classical in
private lemma count_colorings {α : Type} {n : ℕ} (s A : Finset α) (hA : A ⊆ s)
    (hsize : A.card = n) (fallback : Fin n) :
    n.factorial * n ^ (s.card - n) ≤
      Fintype.card {c : s → Fin n // Function.Bijective (fun x : A => extendColor s fallback c x)} := by
  classical
  let Choices := (A ≃ Fin n) × (↥(s \ A) → Fin n)
  let paint (b : Choices) (x : s) : Fin n :=
    if hx : x.val ∈ A then b.1 ⟨x.val, hx⟩
    else b.2 ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
  have inside (b : Choices) (x : A) : paint b ⟨x.val, hA x.property⟩ = b.1 x := by
    simp [paint, x.property]
  have outside (b : Choices) (x : ↥(s \ A)) :
      paint b ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩ = b.2 x := by
    simp [paint, (Finset.mem_sdiff.mp x.property).2]
  let pack (b : Choices) : {c : s → Fin n //
      Function.Bijective (fun x : A => extendColor s fallback c x)} :=
    ⟨paint b, by
      have h : (fun x : A => extendColor s fallback (paint b) x) = b.1 := by
        funext x
        simpa [extendColor, hA x.property] using inside b x
      rw [h]
      exact b.1.bijective⟩
  have hinj : Function.Injective pack := by
    intro b d h
    have he : paint b = paint d := congrArg Subtype.val h
    apply Prod.ext
    · apply Equiv.ext
      intro x
      simpa only [inside] using congrFun he ⟨x.val, hA x.property⟩
    · funext x
      simpa only [outside] using congrFun he ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩
  let e : A ≃ Fin n := Fintype.equivOfCardEq (by simpa using hsize)
  simpa [Choices, Fintype.card_equiv e, Finset.card_sdiff_of_subset hA, hsize]
    using Fintype.card_le_of_injective pack hinj

end RainbowCounting

open RainbowCounting

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  classical
  intro α n hn F hF
  by_cases hne : F.Nonempty
  · let s := F.biUnion id
    let fallback : Fin n := ⟨0, hn⟩
    let rainbow (A : Finset α) (c : s → Fin n) :=
      Function.Bijective (fun x : A => extendColor s fallback c x)
    let colors : Finset (s → Fin n) := Finset.univ
    let family (c : s → Fin n) := F.bipartiteBelow rainbow c
    have hsub {A : Finset α} (ha : A ∈ F) : A ⊆ s := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨A, ha, hx⟩
    have hcount (A : Finset α) (ha : A ∈ F) :
        n.factorial * n ^ (s.card - n) ≤ (colors.bipartiteAbove rainbow A).card := by
      simpa [colors, Finset.bipartiteAbove, rainbow, Fintype.card_subtype] using
        count_colorings s A (hsub ha) (hF A ha) fallback
    -- A coloring maximizing the number of rainbow sets reaches the average.
    obtain ⟨c, _, hmax⟩ := colors.exists_max_image (fun c => (family c).card)
      ⟨fun _ => fallback, Finset.mem_univ _⟩
    refine ⟨extendColor s fallback c, family c, Finset.filter_subset _ _, ?_, ?_⟩
    · intro A ha
      exact ((Finset.mem_bipartiteBelow rainbow).mp ha).2
    · have total := Finset.card_mul_le_card_mul rainbow hcount hmax
      have hcolors : colors.card = n ^ s.card := by simp [colors]
      obtain ⟨A, ha⟩ := hne
      have hnS : n ≤ s.card := hF A ha ▸ Finset.card_le_card (hsub ha)
      have hpow : n ^ s.card = n ^ n * n ^ (s.card - n) := by
        rw [← pow_add, Nat.add_sub_of_le hnS]
      rw [hcolors, hpow] at total
      refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hn (s.card - n))
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using total
  · exact ⟨fun _ => ⟨0, hn⟩, ∅, Finset.empty_subset _, by simp,
      by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩
