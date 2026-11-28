import OMAReductions.R_Erdos141_erdos_141_R1_H2_R1
import Mathlib

open Erdos141

theorem OMA.cnt (a : ℕ) (ha : a.Prime) : ∀ b, a + 1 ≤ b → (∀ m, a < m → m < b → ¬ m.Prime) →
    Nat.count Nat.Prime b = Nat.count Nat.Prime a + 1 := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => intro _; rw [Nat.count_succ, if_pos ha]
  | succ m hm ih =>
    intro h
    rw [Nat.count_succ, if_neg (h m (by omega) (by omega)), add_zero]
    exact ih fun x h1 h2 => h x h1 (by omega)

theorem OMA.solution : OMA.R_Erdos141_erdos_141_R1_H2_R1.H2 := by
  intro p d k hd hp hg
  have hc : ∀ n, n < k → Nat.count Nat.Prime (p + n * d) = Nat.count Nat.Prime p + n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [OMA.cnt (p + n * d) (hp n (by omega)) _ (by nlinarith) (hg n hn), ih (by omega)]
      ring
  have hnth : ∀ n, n < k → Nat.nth Nat.Prime (Nat.count Nat.Prime p + n) = p + n * d := by
    intro n hn
    rw [← hc n hn, Nat.nth_count (hp n hn)]
  have hinj : Function.Injective (fun n : ℕ => p + n * d) := by
    intro a b h
    have : a * d = b * d := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hcard : ENat.card (↑(((Finset.range k).image (fun n : ℕ => p + n * d) : Finset ℕ)) : Set ℕ) = k := by
    rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  refine ⟨↑((Finset.range k).image (fun n : ℕ => p + n * d)), ⟨p, d, hcard, ?_⟩, ⟨Nat.count Nat.Prime p, hcard, ?_⟩⟩
  · ext x
    simp [eq_comm]
  · ext x
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_setOf_eq,
      Nat.cast_lt, exists_prop]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, hnth n hn⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, (hnth n hn).symm⟩

