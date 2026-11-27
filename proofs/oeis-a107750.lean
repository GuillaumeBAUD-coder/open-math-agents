import OMAStatements.S_oeis_a107750
import Mathlib

/-!
Refutation of the recurrence at n = 6. The binary zero counts of 0, 1, ..., 7 are
1, 0, 1, 0, 2, 1, 1, 0, so a(1..6) = 1, 2, 3, 4, 5, 7 (6 is skipped: it has as many zeros as 5).
Then a(6) = 7 while a(5) + a(3) - a(2) = 6.
-/

namespace R107750
open OMA.S_oeis_a107750

theorem step (n u v : ℕ) (hu : a n = u) (hlt : u < v) (hz : zeros v ≠ zeros u)
    (hmin : ∀ m, u < m → m < v → zeros m = zeros u) : a (n + 1) = v := by
  show sInf {m | a n < m ∧ zeros m ≠ zeros (a n)} = v
  rw [hu]
  have hv : v ∈ {m | u < m ∧ zeros m ≠ zeros u} := ⟨hlt, hz⟩
  apply le_antisymm (Nat.sInf_le hv)
  apply le_csInf ⟨v, hv⟩
  rintro b ⟨hb1, hb2⟩
  by_contra hlt'
  exact hb2 (hmin b hb1 (by omega))

theorem z0 : zeros 0 = 1 := rfl

theorem z1 : zeros 1 = 0 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z2 : zeros 2 = 1 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z3 : zeros 3 = 0 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z4 : zeros 4 = 2 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z5 : zeros 5 = 1 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z6 : zeros 6 = 1 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem z7 : zeros 7 = 0 := by
  first | (norm_num [zeros]; done) | (simp [zeros]; done) | decide

theorem a1 : a 1 = 1 :=
  step 0 0 1 rfl (by norm_num) (by rw [z1, z0]; norm_num) (fun m h1 h2 => by omega)

theorem a2 : a 2 = 2 :=
  step 1 1 2 a1 (by norm_num) (by rw [z2, z1]; norm_num) (fun m h1 h2 => by omega)

theorem a3 : a 3 = 3 :=
  step 2 2 3 a2 (by norm_num) (by rw [z3, z2]; norm_num) (fun m h1 h2 => by omega)

theorem a4 : a 4 = 4 :=
  step 3 3 4 a3 (by norm_num) (by rw [z4, z3]; norm_num) (fun m h1 h2 => by omega)

theorem a5 : a 5 = 5 :=
  step 4 4 5 a4 (by norm_num) (by rw [z5, z4]; norm_num) (fun m h1 h2 => by omega)

theorem a6 : a 6 = 7 :=
  step 5 5 7 a5 (by norm_num) (by rw [z7, z5]; norm_num) (fun m h1 h2 => by
    obtain rfl : m = 6 := by omega
    rw [z6, z5])

end R107750

open OMA.S_oeis_a107750 R107750 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107750.main) := by
  intro h
  have h6 := h.2 6 (by norm_num)
  rw [show 6 - 1 = 5 from rfl, show 6 - 3 = 3 from rfl, show 6 - 4 = 2 from rfl, a6, a5, a3,
    a2] at h6
  norm_num at h6
