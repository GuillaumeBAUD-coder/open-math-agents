import OMAStatements.S_oeis_a045797

namespace OMA.P_oeis_a045797

open OMA.S_oeis_a045797

theorem coprime10 (k : ℕ) : Nat.Coprime k 10 ↔ k % 2 = 1 ∧ k % 5 ≠ 0 := by
  rw [show (10 : ℕ) = 2 * 5 by rfl, Nat.coprime_mul_iff_right, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd (by norm_num), Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  omega

theorem char (k : ℕ) : evenish k ↔
    (k % 20 = 1 ∨ k % 20 = 3 ∨ k % 20 = 7 ∨ k % 20 = 9) := by
  unfold evenish
  rw [coprime10]
  omega

/-- Offsets of the four residues mod 20. -/
def g (r : ℕ) : ℕ := if r = 0 then 1 else if r = 1 then 3 else if r = 2 then 7 else 9

/-- The explicit enumeration (0-indexed). -/
def f (i : ℕ) : ℕ := 20 * (i / 4) + g (i % 4)

theorem f_mono : StrictMono f := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  unfold f g
  split_ifs <;> omega

theorem f_mem (i : ℕ) : evenish (f i) := by
  rw [char]
  unfold f g
  split_ifs <;> omega

theorem f_surj (k : ℕ) (hk : evenish k) : ∃ i, f i = k := by
  rw [char] at hk
  refine ⟨4 * (k / 20) + (if k % 20 = 1 then 0 else if k % 20 = 3 then 1
    else if k % 20 = 7 then 2 else 3), ?_⟩
  unfold f g
  split_ifs <;> omega

theorem nth_eq (i : ℕ) : Nat.nth evenish i = f i := by
  have hinf : (Set.ofPred evenish).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_mem
  have hdom : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred evenish),
      n < hf.toFinset.card } := fun n hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hdom i)).symm
  · intro k hk
    obtain ⟨j, rfl⟩ := f_surj k hk
    exact ⟨j, hdom j, rfl⟩
  · intro j _
    exact f_mem j
  · exact f_mono.strictMonoOn _

end OMA.P_oeis_a045797

open OMA.P_oeis_a045797 in
theorem OMA.solution : type_of% @OMA.S_oeis_a045797.main := by
  intro n hn
  unfold OMA.S_oeis_a045797.a
  simp only [nth_eq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 5 - 1 = m + 4 := by omega
  have e3 : m + 6 - 4 - 1 = m + 1 := by omega
  have e4 : m + 6 - 5 - 1 = m := by omega
  rw [e1, e2, e3, e4]
  have h1 : f (m + 5) = f (m + 1) + 20 := by
    unfold f g
    split_ifs <;> omega
  have h2 : f (m + 4) = f m + 20 := by
    unfold f g
    split_ifs <;> omega
  rw [h1, h2]
  push_cast
  ring
