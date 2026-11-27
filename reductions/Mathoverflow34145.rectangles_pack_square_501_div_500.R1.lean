import FormalConjectures.Mathoverflow.«34145»

-- Credit: @steveDOTdigital
namespace OMA.R_Mathoverflow34145_rectangles_pack_square_501_div_500_R1

open Mathoverflow34145 Set

private theorem in_square (p : ℝ × ℝ) (hx : p.1 ∈ Icc 0 (501/500))
    (hy : p.2 ∈ Icc 0 (501/500)) :
    p ∈ Rectangle.toSet ⟨501/500, 501/500, (0, 0), 0⟩ := by
  let s : ℝ := 501/500
  have hs : 0 < s := by norm_num [s]
  refine ⟨scale s s (p.1/s, p.2/s), ⟨(p.1/s, p.2/s), ?_, rfl⟩, ?_⟩
  · exact ⟨div_nonneg hx.1 hs.le, (div_le_one hs).2 hx.2,
      div_nonneg hy.1 hs.le, (div_le_one hs).2 hy.2⟩
  · ext <;> simp [rigidMotion, scale, s] <;> ring

-- Finite packing certificate for rectangles with denominators 1 through 1023.
def H1 : Prop :=
  ∃ f : Configuration, (∀ n < 1023, (f.rect n).toSet ⊆ Icc 0 1 ×ˢ Icc 0 1) ∧
    ∀ m < 1023, ∀ n < 1023, m ≠ n →
      interior (f.rect m).toSet ∩ interior (f.rect n).toSet = ∅

-- The infinite tail fits across shelves of heights 1/1024, 1/2048, ...
-- above the unit square.
def H2 : Prop :=
  ∃ t : Configuration, (∀ n ≥ 1023, (t.rect n).toSet ⊆ Icc 0 1 ×ˢ Icc 1 (501/500)) ∧
    ∀ m ≥ 1023, ∀ n ≥ 1023, m ≠ n →
      interior (t.rect m).toSet ∩ interior (t.rect n).toSet = ∅

theorem main : H1 → H2 → type_of% @Mathoverflow34145.rectangles_pack_square_501_div_500 := by
  rintro ⟨f, fbox, fdis⟩ ⟨t, tbox, tdis⟩
  let c : Configuration := {
    rect := fun n => if n < 1023 then f.rect n else t.rect n
    rect_width := fun n => by split <;> simp [Configuration.rect_width]
    rect_height := fun n => by split <;> simp [Configuration.rect_height] }
  have apart {m n : ℕ} (hm : m < 1023) (hn : 1023 ≤ n) :
      interior (f.rect m).toSet ∩ interior (t.rect n).toSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro p hp
    have hf := interior_mono (fbox m hm) hp.1
    have ht := interior_mono (tbox n hn) hp.2
    simp only [interior_prod_eq, interior_Icc] at hf ht
    exact hf.2.2.not_gt ht.2.1
  refine ⟨c, ?_, ?_⟩
  · intro n p hp
    change p ∈ (if n < 1023 then f.rect n else t.rect n).toSet at hp
    split at hp
    · rename_i h
      obtain ⟨hx, hy⟩ := fbox n h hp
      exact in_square p ⟨hx.1, hx.2.trans (by norm_num)⟩ ⟨hy.1, hy.2.trans (by norm_num)⟩
    · rename_i h
      obtain ⟨hx, hy⟩ := tbox n (by omega) hp
      exact in_square p ⟨hx.1, hx.2.trans (by norm_num)⟩ ⟨le_trans (by norm_num) hy.1, hy.2⟩
  · intro m n hmn
    by_cases hm : m < 1023 <;> by_cases hn : n < 1023 <;> simp only [c, hm, hn, if_true, if_false]
    · exact fdis m hm n hn hmn
    · exact apart hm (by omega)
    · rw [inter_comm]
      exact apart hn (by omega)
    · exact tdis m (by omega) n (by omega) hmn

end OMA.R_Mathoverflow34145_rectangles_pack_square_501_div_500_R1
