import OMAReductions.R_Erdos963_erdos_963_parts_ii_R1

/-!
# Proof of `Erdos963.erdos_963.parts.ii.R1.H3`

Classifies every 7-element integer set `X` having no 5-element affinely dissociated subset:
writing the sorted elements of `X` as `y 0 < y 1 < y 2 < y 3 < y 4 < y 5 < y 6`, every 5-element
subset of `X` fails the equal-size disjoint subset-sum condition, which forces a 4-element subset
`{u < v < w < z}` with `u + z = v + w`. An exact finite case analysis on the 6 positive consecutive
gaps forces `y 1 - y 0 = y 3 - y 2 = y 4 - y 3 = y 6 - y 5` and `y 2 - y 1 = y 5 - y 4`, so setting
`x = y 3`, `a = y 4 - y 3 > 0`, and `b = y 5 - y 3 > a` gives
`X = {x, x - a, x + a, x - b, x + b, x - (a + b), x + (a + b)}`.
-/

open Finset

namespace Erdos963H3Proof

private def Aff (M : Finset ℤ) : Prop :=
  ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S

private lemma parallelogram_of_not_aff_five {y : Fin 7 → ℤ} (hmono : StrictMono y)
    {i0 i1 i2 i3 i4 : Fin 7} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) (h34 : i3 < i4)
    (hnot : ¬ Aff ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ)) :
    y i0 + y i3 = y i1 + y i2 ∨
    y i0 + y i4 = y i1 + y i2 ∨
    y i0 + y i4 = y i1 + y i3 ∨
    y i0 + y i4 = y i2 + y i3 ∨
    y i1 + y i4 = y i2 + y i3 := by
  unfold Aff at hnot
  push Not at hnot
  obtain ⟨T, hT, S, hS, hdisj, hcard, hsum, hne⟩ := hnot
  have hy01 : y i0 < y i1 := hmono h01
  have hy12 : y i1 < y i2 := hmono h12
  have hy23 : y i2 < y i3 := hmono h23
  have hy34 : y i3 < y i4 := hmono h34
  have hFcard : ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ).card = 5 := by
    have h0 : y i0 ≠ y i1 ∧ y i0 ≠ y i2 ∧ y i0 ≠ y i3 ∧ y i0 ≠ y i4 := by omega
    have h1 : y i1 ≠ y i2 ∧ y i1 ≠ y i3 ∧ y i1 ≠ y i4 := by omega
    have h2 : y i2 ≠ y i3 ∧ y i2 ≠ y i4 := by omega
    have h3 : y i3 ≠ y i4 := by omega
    simp [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, h1.1, h1.2.1, h1.2.2, h2.1, h2.2, h3]
  have hsum_le : T.card + S.card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hFcard]
    exact Finset.card_le_card (Finset.union_subset hT hS)
  have hTne0 : T.card ≠ 0 := by
    intro h0
    have hT0 : T = ∅ := Finset.card_eq_zero.mp h0
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    exact hne (hT0.trans hS0.symm)
  have hTne1 : T.card ≠ 1 := by
    intro h1
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
    simp only [Finset.sum_singleton, id_eq] at hsum
    exact hne (by rw [hsum])
  have hT2 : T.card = 2 := by omega
  have hS2 : S.card = 2 := by omega
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT2
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hS2
  have haF : a ∈ ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ) := hT (by simp)
  have hbF : b ∈ ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ) := hT (by simp)
  have hcF : c ∈ ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ) := hS (by simp)
  have hdF : d ∈ ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ) := hS (by simp)
  have hac : a ≠ c := fun h =>
    Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a {b}) (h ▸ Finset.mem_insert_self c {d})
  have had : a ≠ d := fun h =>
    Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a {b}) (by rw [h]; simp)
  have hbc : b ≠ c := fun h =>
    Finset.disjoint_left.mp hdisj (by simp : b ∈ ({a, b} : Finset ℤ)) (h ▸ Finset.mem_insert_self c {d})
  have hbd : b ≠ d := fun h =>
    Finset.disjoint_left.mp hdisj (by simp : b ∈ ({a, b} : Finset ℤ)) (by rw [h]; simp)
  simp only [Finset.sum_pair hab, Finset.sum_pair hcd, id_eq] at hsum
  simp only [Finset.mem_insert, Finset.mem_singleton] at haF hbF hcF hdF
  by_contra hneg
  push Not at hneg
  rcases hneg with ⟨hn1, hn2, hn3, hn4, hn5⟩
  rcases haF with rfl | rfl | rfl | rfl | rfl <;>
  rcases hbF with rfl | rfl | rfl | rfl | rfl <;>
  rcases hcF with rfl | rfl | rfl | rfl | rfl <;>
  rcases hdF with rfl | rfl | rfl | rfl | rfl <;>
  omega

private lemma gaps_forced (y : Fin 7 → ℤ) (hmono : StrictMono y)
    (h5 : ∀ i0 i1 i2 i3 i4 : Fin 7, i0 < i1 → i1 < i2 → i2 < i3 → i3 < i4 →
      y i0 + y i3 = y i1 + y i2 ∨
      y i0 + y i4 = y i1 + y i2 ∨
      y i0 + y i4 = y i1 + y i3 ∨
      y i0 + y i4 = y i2 + y i3 ∨
      y i1 + y i4 = y i2 + y i3) :
    y 1 - y 0 = y 3 - y 2 ∧
    y 1 - y 0 = y 4 - y 3 ∧
    y 1 - y 0 = y 6 - y 5 ∧
    y 2 - y 1 = y 5 - y 4 := by
  have g0 : y 0 < y 1 := hmono (by decide)
  have g1 : y 1 < y 2 := hmono (by decide)
  have g2 : y 2 < y 3 := hmono (by decide)
  have g3 : y 3 < y 4 := hmono (by decide)
  have g4 : y 4 < y 5 := hmono (by decide)
  have g5 : y 5 < y 6 := hmono (by decide)
  rcases h5 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide) with h0 | h0 | h0 | h0 | h0
  · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · exact ⟨by omega, by omega, by omega, by omega⟩
        · omega
        · omega
      · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
    · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · rcases h5 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
          · omega
      · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · exact ⟨by omega, by omega, by omega, by omega⟩
      · omega
  · rcases h5 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
      · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
    · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h5 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
  · rcases h5 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · exact ⟨by omega, by omega, by omega, by omega⟩
          · omega
          · omega
        · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
        · exact ⟨by omega, by omega, by omega, by omega⟩
        · omega
    · omega
    · omega
    · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
        · exact ⟨by omega, by omega, by omega, by omega⟩
        · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases h5 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
      · omega
      · omega
  · rcases h5 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
        · rcases h5 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · rcases h5 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases h5 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
        · omega
        · omega
    · omega
    · omega
    · omega
    · omega
  · rcases h5 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases h5 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · exact ⟨by omega, by omega, by omega, by omega⟩
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases h5 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · rcases h5 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases h5 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases h5 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases h5 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases h5 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
      · rcases h5 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases h5 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · exact ⟨by omega, by omega, by omega, by omega⟩
        · rcases h5 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · rcases h5 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
      · omega
      · omega

end Erdos963H3Proof

theorem OMA.solution : OMA.R_Erdos963_erdos_963_parts_ii_R1.H3 := by
  intro X hcard hno
  let e : Fin 7 ≃o X := X.orderIsoOfFin hcard
  let y : Fin 7 → ℤ := fun i => (e i).val
  have hmono : StrictMono y := fun i j hij => e.strictMono hij
  have hy_mem : ∀ i : Fin 7, y i ∈ X := fun i => (e i).property
  have h5 : ∀ i0 i1 i2 i3 i4 : Fin 7, i0 < i1 → i1 < i2 → i2 < i3 → i3 < i4 →
      y i0 + y i3 = y i1 + y i2 ∨
      y i0 + y i4 = y i1 + y i2 ∨
      y i0 + y i4 = y i1 + y i3 ∨
      y i0 + y i4 = y i2 + y i3 ∨
      y i1 + y i4 = y i2 + y i3 := by
    intro i0 i1 i2 i3 i4 h01 h12 h23 h34
    apply Erdos963H3Proof.parallelogram_of_not_aff_five hmono h01 h12 h23 h34
    have hFsub : ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ) ⊆ X := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> exact hy_mem _
    have hFcard : ({y i0, y i1, y i2, y i3, y i4} : Finset ℤ).card = 5 := by
      have hy01 : y i0 < y i1 := hmono h01
      have hy12 : y i1 < y i2 := hmono h12
      have hy23 : y i2 < y i3 := hmono h23
      have hy34 : y i3 < y i4 := hmono h34
      have h0 : y i0 ≠ y i1 ∧ y i0 ≠ y i2 ∧ y i0 ≠ y i3 ∧ y i0 ≠ y i4 := by omega
      have h1 : y i1 ≠ y i2 ∧ y i1 ≠ y i3 ∧ y i1 ≠ y i4 := by omega
      have h2 : y i2 ≠ y i3 ∧ y i2 ≠ y i4 := by omega
      have h3 : y i3 ≠ y i4 := by omega
      simp [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, h1.1, h1.2.1, h1.2.2, h2.1, h2.2, h3]
    exact hno _ hFsub hFcard
  obtain ⟨hg1, hg2, hg3, hg4⟩ := Erdos963H3Proof.gaps_forced y hmono h5
  have g0 : y 0 < y 1 := hmono (by decide)
  have g1 : y 1 < y 2 := hmono (by decide)
  have g2 : y 2 < y 3 := hmono (by decide)
  have g3 : y 3 < y 4 := hmono (by decide)
  have g4 : y 4 < y 5 := hmono (by decide)
  have g5 : y 5 < y 6 := hmono (by decide)
  refine ⟨y 3, y 4 - y 3, y 5 - y 3, by omega, by omega, ?_⟩
  ext z
  constructor
  · intro hz
    have hidx : ∃ i : Fin 7, y i = z := ⟨e.symm ⟨z, hz⟩, by simp [y]⟩
    obtain ⟨i, rfl⟩ := hidx
    fin_cases i <;> simp only [Finset.mem_insert, Finset.mem_singleton]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by change y 0 = _; omega))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by change y 1 = _; omega))))
    · exact Or.inr (Or.inl (by change y 2 = _; omega))
    · exact Or.inl (by change y 3 = _; rfl)
    · exact Or.inr (Or.inr (Or.inl (by change y 4 = _; omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by change y 5 = _; omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by change y 6 = _; omega))))))
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hy_mem 3
    · have : y 3 - (y 4 - y 3) = y 2 := by omega
      rw [this]; exact hy_mem 2
    · have : y 3 + (y 4 - y 3) = y 4 := by omega
      rw [this]; exact hy_mem 4
    · have : y 3 - (y 5 - y 3) = y 1 := by omega
      rw [this]; exact hy_mem 1
    · have : y 3 + (y 5 - y 3) = y 5 := by omega
      rw [this]; exact hy_mem 5
    · have : y 3 - (y 4 - y 3 + (y 5 - y 3)) = y 0 := by omega
      rw [this]; exact hy_mem 0
    · have : y 3 + (y 4 - y 3 + (y 5 - y 3)) = y 6 := by omega
      rw [this]; exact hy_mem 6
