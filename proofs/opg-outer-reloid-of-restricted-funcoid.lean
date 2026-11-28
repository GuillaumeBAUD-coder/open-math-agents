import OMAStatements.S_opg_outer_reloid_of_restricted_funcoid
import Mathlib

/-!
Disproof. Take A = B = Nat, f X Y := X.Nonempty and Y.Nonempty, both filters cofinite.
Then rldOut f = top, so the right side is cofinite x cofinite, which is not bot.
On the left, the restricted funcoid only relates infinite sets, so both
{p | p.1 < p.2} and {p | p.2 ≤ p.1} are generators, and their intersection is empty.
-/

open Filter Set

namespace OMA.S_opg_outer_reloid_of_restricted_funcoid

theorem inf_of_meet {f : Set ℕ → Set ℕ → Prop} {X Y : Set ℕ}
    (h : fcdMeet f (fcdProd cofinite cofinite) X Y) : X.Infinite ∧ Y.Infinite := by
  obtain ⟨g, -, -, hg, hXY⟩ := h
  obtain ⟨h1, h2⟩ := hg X Y hXY
  constructor
  · intro hfin
    exact h1 (Filter.inf_principal_eq_bot.2 hfin.compl_mem_cofinite)
  · intro hfin
    exact h2 (Filter.inf_principal_eq_bot.2 hfin.compl_mem_cofinite)

end OMA.S_opg_outer_reloid_of_restricted_funcoid

open OMA.S_opg_outer_reloid_of_restricted_funcoid in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_outer_reloid_of_restricted_funcoid.main) := by
  intro H
  have hf : IsFuncoid (fun (X : Set ℕ) (Y : Set ℕ) => X.Nonempty ∧ Y.Nonempty) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Y h; exact Set.not_nonempty_empty h.1
    · intro X h; exact Set.not_nonempty_empty h.2
    · intro X X' Y; simp only [Set.union_nonempty]; tauto
    · intro X Y Y'; simp only [Set.union_nonempty]; tauto
  have h := H ℕ ℕ _ cofinite cofinite hf
  have htop : rldOut (fun (X : Set ℕ) (Y : Set ℕ) => X.Nonempty ∧ Y.Nonempty) = ⊤ := by
    rw [rldOut, ← top_le_iff, Filter.le_generate_iff]
    intro K hK
    have : K = Set.univ := by
      ext ⟨a, b⟩
      simp only [Set.mem_univ, iff_true]
      obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hk⟩ := hK {a} {b} ⟨Set.singleton_nonempty a, Set.singleton_nonempty b⟩
      simp only [Set.mem_singleton_iff] at hx hy
      subst hx; subst hy; exact hk
    rw [this]; exact Filter.univ_mem
  rw [htop, top_inf_eq] at h
  have h1 : {p : ℕ × ℕ | p.1 < p.2} ∈
      rldOut (fcdMeet (fun (X : Set ℕ) (Y : Set ℕ) => X.Nonempty ∧ Y.Nonempty)
        (fcdProd cofinite cofinite)) := by
    apply Filter.mem_generate_of_mem
    intro X Y hXY
    obtain ⟨hX, hY⟩ := inf_of_meet hXY
    obtain ⟨a, ha⟩ := hX.nonempty
    obtain ⟨b, hb, hab⟩ := hY.exists_gt a
    exact ⟨(a, b), ⟨ha, hb⟩, hab⟩
  have h2 : {p : ℕ × ℕ | p.2 ≤ p.1} ∈
      rldOut (fcdMeet (fun (X : Set ℕ) (Y : Set ℕ) => X.Nonempty ∧ Y.Nonempty)
        (fcdProd cofinite cofinite)) := by
    apply Filter.mem_generate_of_mem
    intro X Y hXY
    obtain ⟨hX, hY⟩ := inf_of_meet hXY
    obtain ⟨b, hb⟩ := hY.nonempty
    obtain ⟨a, ha, hab⟩ := hX.exists_gt b
    exact ⟨(a, b), ⟨ha, hb⟩, le_of_lt hab⟩
  have h3 := Filter.inter_mem h1 h2
  have hempty : ({p : ℕ × ℕ | p.1 < p.2} ∩ {p : ℕ × ℕ | p.2 ≤ p.1}) = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    omega
  rw [hempty, h] at h3
  have hne : (cofinite ×ˢ cofinite : Filter (ℕ × ℕ)).NeBot := inferInstance
  exact hne.ne (Filter.empty_mem_iff_bot.1 h3)
