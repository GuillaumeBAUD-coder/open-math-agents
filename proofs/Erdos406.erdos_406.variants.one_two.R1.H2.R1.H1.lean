import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1
import Mathlib

/-!
Every `2^k` with `k < 4096` has a zero among its 32 lowest ternary digits (counting leading
zeros). This is a finite check of 4096 cases, done by kernel evaluation of a Boolean table.
-/
namespace Erdos406Seed

/-- The Boolean table: for each `k < 4096`, some digit `i < 32` of `2^k` in base 3 is zero. -/
def table : Bool :=
  (List.range 4096).all fun k => (List.range 32).any fun i => (2 ^ k / 3 ^ i) % 3 == 0

theorem table_eq : table = true := by
  decide +kernel

theorem seed : OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1.H1 := by
  intro a b
  have hk : 64 * a.val + b.val ∈ List.range 4096 := by
    rw [List.mem_range]; have := a.isLt; have := b.isLt; omega
  have h := List.all_eq_true.mp table_eq _ hk
  obtain ⟨i, hi, hz⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hi
  exact ⟨⟨i, hi⟩, by simpa using hz⟩

end Erdos406Seed

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1.H1 := Erdos406Seed.seed
