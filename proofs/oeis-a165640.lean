import OMAStatements.S_oeis_a165640
import Mathlib

namespace OMA.A165640Proof

open OMA.S_oeis_a165640

def g (n t : ℕ) : ℕ × ℕ × ℕ :=
  (2 * t + (n + 1) % 2, (3 * n - 5 * (2 * t + (n + 1) % 2) - 3) / 2,
    (3 * (2 * t + (n + 1) % 2) + 3 - n) / 2)

theorem g_inj (n : ℕ) : Function.Injective (g n) := by
  intro s t h
  have := congrArg Prod.fst h
  simp only [g] at this
  omega

theorem S_eq (n : ℕ) (hn : 1 ≤ n) :
    S n = (Finset.Ico ((n - (3 + 3 * ((n + 1) % 2)) + 5) / 6)
      ((3 * n + 7 - 5 * ((n + 1) % 2)) / 10)).image (g n) := by
  ext ⟨x, y, z⟩
  simp only [S, g, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
    Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, hy, hz⟩, hs, he⟩
    have hpar : x % 2 = (n + 1) % 2 := by omega
    have h2 : 2 * (x / 2) + (n + 1) % 2 = x := by omega
    have hy2 : 2 * y = 3 * n - 5 * x - 3 := by omega
    have hz2 : 2 * z = 3 * x + 3 - n := by omega
    refine ⟨x / 2, ⟨by omega, by omega⟩, h2, ?_, ?_⟩
    · rw [h2]; omega
    · rw [h2]; omega
  · rintro ⟨t, ⟨h1, h2⟩, rfl, rfl, rfl⟩
    refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩

end OMA.A165640Proof

open OMA.S_oeis_a165640 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165640.main := by
  intro n hn
  unfold a
  rw [OMA.A165640Proof.S_eq n hn, Finset.card_image_of_injective _ (OMA.A165640Proof.g_inj n),
    Nat.card_Ico]
  have h := Nat.mod_add_div n 30
  generalize n / 30 = q at h
  have hr : n % 30 < 30 := Nat.mod_lt _ (by norm_num)
  generalize n % 30 = r at h hr
  subst h
  interval_cases r <;> omega
