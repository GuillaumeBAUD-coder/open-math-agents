import OMAStatements.S_oeis_a225563
import Mathlib

namespace OMA.S_oeis_a225563

open Finset

lemma half_tot : ∀ m : ℕ, 2 * Nat.totient (2 * m) ≤ 2 * m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    by_cases h2 : 2 ∣ m
    · obtain ⟨k, rfl⟩ := h2
      have := ih k (by omega)
      rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two (by simp)]
      have h3 : 2 * Nat.totient (2 * k) ≤ 2 * k := this
      have h4 : Nat.totient (2 * k) ≤ 2 * k := Nat.totient_le _
      omega
    · rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2)]
      have := Nat.totient_le m
      simp [Nat.totient_two]
      omega

def Tn (n N : ℕ) : Finset ℕ := (range N).image fun i => Nat.totient^[i] n

lemma sum_insert_le' (n : ℕ) (s : Finset ℕ) : ∑ x ∈ insert n s, x ≤ n + ∑ x ∈ s, x := by
  by_cases h : n ∈ s
  · rw [Finset.insert_eq_of_mem h]; omega
  · rw [Finset.sum_insert h]

lemma Tn_succ_sub (n N : ℕ) : Tn n (N + 1) ⊆ insert n (Tn (Nat.totient n) N) := by
  intro x hx
  simp only [Tn, mem_image, mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rcases i with _ | j
  · simp
  · apply Finset.mem_insert_of_mem
    simp only [Tn, mem_image, mem_range]
    exact ⟨j, by omega, by rw [Function.iterate_succ_apply]⟩

lemma bound : ∀ n : ℕ, 1 ≤ n → (n = 1 ∨ 2 ∣ n) → ∀ N, ∑ x ∈ Tn n N, x ≤ 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hev N
    rcases N with _ | N
    · simp [Tn]
    rcases hev with rfl | ⟨m, rfl⟩
    · have : Tn 1 (N + 1) ⊆ {1} := by
        intro x hx
        simp only [Tn, mem_image, mem_range] at hx
        obtain ⟨i, _, rfl⟩ := hx
        have : ∀ i, Nat.totient^[i] 1 = 1 := fun i => Function.iterate_fixed (by simp) i
        simp [this]
      calc ∑ x ∈ Tn 1 (N + 1), x ≤ ∑ x ∈ ({1} : Finset ℕ), x := Finset.sum_le_sum_of_subset this
        _ ≤ 2 * 1 := by simp
    · have hm : 1 ≤ m := by omega
      have hh := half_tot m
      have hlt : Nat.totient (2 * m) < 2 * m := Nat.totient_lt _ (by omega)
      have hpos : 1 ≤ Nat.totient (2 * m) := Nat.totient_pos.2 (by omega)
      have hev' : Nat.totient (2 * m) = 1 ∨ 2 ∣ Nat.totient (2 * m) := by
        by_cases h : 2 < 2 * m
        · right; exact (Nat.totient_even h).two_dvd
        · left
          have : m = 1 := by omega
          subst this; simp
      have := ih _ hlt hpos hev' N
      calc ∑ x ∈ Tn (2 * m) (N + 1), x
          ≤ ∑ x ∈ insert (2 * m) (Tn (Nat.totient (2 * m)) N), x :=
            Finset.sum_le_sum_of_subset (Tn_succ_sub _ _)
        _ ≤ 2 * m + ∑ x ∈ Tn (Nat.totient (2 * m)) N, x := sum_insert_le' _ _
        _ ≤ 2 * (2 * m) := by omega

lemma bound_all (m : ℕ) (hm : 1 ≤ m) : ∑ x ∈ trajectory m, x < 3 * m := by
  have h := fun (n : ℕ) (hn : 1 ≤ n) (h2 : n = 1 ∨ 2 ∣ n) => bound n hn h2 (n + 1)
  show ∑ x ∈ Tn m (m + 1), x < 3 * m
  by_cases hev : m = 1 ∨ 2 ∣ m
  · have := h m hm hev; omega
  · have hodd : 3 ≤ m := by omega
    have hlt : Nat.totient m < m := Nat.totient_lt _ (by omega)
    have hpos : 1 ≤ Nat.totient m := Nat.totient_pos.2 (by omega)
    have hev' : 2 ∣ Nat.totient m := (Nat.totient_even (by omega)).two_dvd
    have h1 := bound _ hpos (Or.inr hev') m
    calc ∑ x ∈ Tn m (m + 1), x
        ≤ ∑ x ∈ insert m (Tn (Nat.totient m) m), x := Finset.sum_le_sum_of_subset (Tn_succ_sub _ _)
      _ ≤ m + ∑ x ∈ Tn (Nat.totient m) m, x := sum_insert_le' _ _
      _ < 3 * m := by omega

end OMA.S_oeis_a225563

theorem OMA.solution : type_of% @OMA.S_oeis_a225563.main := by
  intro m hm k _ hk3 ⟨c, hc⟩
  have hmem : m ∈ OMA.S_oeis_a225563.trajectory m := by
    simp only [OMA.S_oeis_a225563.trajectory, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, rfl⟩
  have hb := OMA.S_oeis_a225563.bound_all m hm
  set S := ∑ x ∈ (OMA.S_oeis_a225563.trajectory m).filter (fun x => c x = c m), x with hS
  have hSm : m ≤ S := by
    apply Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _)
    simp [hmem]
  have htot : ∑ x ∈ OMA.S_oeis_a225563.trajectory m, x = ∑ j : Fin k, ∑ x ∈ (OMA.S_oeis_a225563.trajectory m).filter (fun x => c x = j), x := by
    rw [Finset.sum_fiberwise_of_maps_to (g := c) (s := OMA.S_oeis_a225563.trajectory m) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have heq : ∀ j : Fin k, ∑ x ∈ (OMA.S_oeis_a225563.trajectory m).filter (fun x => c x = j), x = S :=
    fun j => hc j (c m)
  rw [htot, Finset.sum_congr rfl (fun j _ => heq j)] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
  nlinarith
