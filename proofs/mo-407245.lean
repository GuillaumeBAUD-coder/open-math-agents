import OMAStatements.S_mo_407245
import Mathlib

open Finset OMA.S_mo_407245

theorem OMA.solution : type_of% @OMA.S_mo_407245.main := by
  intro k n _ _
  have hmt {r} (h : hasOrthogonal k n r = false) (P : Family k n r) (hP : valid P) :
      ∃ x y, x ≠ y ∧ 2 ≤ (meetings P x y).card := by
    by_contra hc
    exact of_decide_eq_false h ⟨P, hP, fun x y hxy => by by_contra hlt; exact hc ⟨x, y, hxy, by omega⟩⟩
  by_cases h3 : hasOrthogonal k n 3 = true
  · by_cases h4 : hasOrthogonal k n 4 = true
    · simp only [threshold, h3, h4, ↓reduceIte]
      intro r hr hf
      obtain ⟨P, hP, horth⟩ := of_decide_eq_true h4
      obtain ⟨x, y, hxy, hle⟩ := hf (fun i => P ⟨i.1 % 4, Nat.mod_lt _ (by decide)⟩) fun i b => hP _ b
      obtain ⟨j, hj⟩ := card_le_one_iff_subset_singleton.1 (horth x y hxy)
      let F := univ.filter fun i : Fin r => i.1 % 4 = j.1
      have hsub : meetings (fun i : Fin r => P ⟨i.1 % 4, Nat.mod_lt _ (by decide)⟩) x y ⊆ F := fun i hi => by
        have hm : (⟨i.1 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) ∈ meetings P x y := by simpa [meetings] using hi
        simpa [F] using congrArg Fin.val (mem_singleton.1 (hj hm))
      have hinj : Set.InjOn (fun i : Fin r => i.1 / 4) (F : Set (Fin r)) := fun a ha b hb hab =>
        Fin.ext (by have := (mem_filter.1 ha).2; have := (mem_filter.1 hb).2; dsimp at hab; omega)
      have himg : F.image (fun i : Fin r => i.1 / 4) ⊆ range ((r + 3) / 4) := fun q hq => by
        obtain ⟨i, _, rfl⟩ := mem_image.1 hq; rw [mem_range]; have := i.2; omega
      have h1 := (card_le_card hsub).trans ((card_image_of_injOn hinj).symm.trans_le ((card_le_card himg).trans_eq (card_range _)))
      omega
    · simp only [threshold, h3, h4, ↓reduceIte]
      refine ⟨⟨by decide, fun P hP => let ⟨x, y, hxy, hc⟩ := hmt (Bool.eq_false_iff.2 h4) P hP; ⟨x, y, hxy, by omega⟩⟩, ?_⟩
      rintro r ⟨hr, hf⟩
      by_contra hlt
      have r3 : r = 3 := by omega
      subst r3
      obtain ⟨P, hP, horth⟩ := of_decide_eq_true h3
      obtain ⟨x, y, hxy, hle⟩ := hf P hP
      have := horth x y hxy; omega
  · simp only [threshold, h3, ↓reduceIte]
    exact ⟨⟨le_rfl, fun P hP => let ⟨x, y, hxy, hc⟩ := hmt (Bool.eq_false_iff.2 h3) P hP; ⟨x, y, hxy, by omega⟩⟩, fun _ h => h.1⟩
