import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

/-!
# Two small divisors for the repeated-prime 257 case

Graham's path weights can be tightened at 7 because the first prime whose
successor is divisible by 7 is 13, and the first for 13 is 103. Combined
with the registered estimate for leaves supported on 2 and 257, this forces
5 or 11 to divide every number in the branch whose 2-adic valuation is at
least 10. The two steps bound the valuation under these additional conditions.
The leaf estimate is from reduction #13718. Desk note #189937 identifies
the small sources of 3 as the remaining obstacle in the related branch.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (one_add_le_B step_ge facts)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (kernel_balance_one zleaf_form B_nonneg)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2 (master_leaf zmass_257)

/-- Bound the branch when 5 occurs as a simple prime factor. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) → 5 ∣ n → padicValNat 2 n ≤ A

/-- Bound the branch when 11 occurs as a simple prime factor. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) → 11 ∣ n → padicValNat 2 n ≤ A

/-- Without either small divisor the valuation is at most 9, for any exponent of 257. -/
theorem small_divisor {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (unique : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257)
    (h5 : ¬5 ∣ n) (h11 : ¬11 ∣ n) : padicValNat 2 n ≤ 9 := by
  by_contra! high
  let weight (p : ℕ) : ℚ :=
    if p = 3 then 16/11 else if p = 7 then 64/51 else if p = 13 then 56/51
    else ((p : ℚ) + 1) / (p - 1)
  have weight_bounds {p : ℕ} (hp : p.Prime) :
      1 + 1 / (p : ℚ) ≤ weight p ∧ weight p ≤ ((p : ℚ) + 1) / (p - 1) := by
    dsimp only [weight]
    split_ifs with h3 h7 h13
    · subst p; norm_num
    · subst p; norm_num
    · subst p; norm_num
    · exact ⟨one_add_le_B hp.two_le, le_rfl⟩
  have hz : Nat.Prime 257 := by norm_num
  obtain ⟨hd, hs⟩ := simple_of_unique_repeated hn.2.ne' unique
  obtain ⟨hp, balance⟩ := kernel_balance_one hn
    (Nat.mem_primeFactors.mpr ⟨hz, hd, hn.2.ne'⟩) (by decide) hs
  let P := (n.primeFactors.erase 2).filter (fun r => ¬r ∈ ({257} : Finset ℕ))
  have to_dvd (p : ℕ) (h : p ∈ P) : p ∣ n :=
    Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1)
  have hK (q : ℕ) (hq : q.Prime) (h : q ∣ 257 ^ n.factorization 257) : q ∈ ({257} : Finset ℕ) :=
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hq hz).mp (hq.dvd_of_dvd_pow h))
  have sq := (facts hp hK balance).2.2.2.2.2.1 3 (by decide) (by decide) (by decide)
  have val : 10 ≤ n.factorization 2 := by rwa [Nat.factorization_def n Nat.prime_two]
  apply master_leaf hp (N := {257}) (by simp [hz]) hK ⟨Nat.le_add_left _ _, ?_⟩ balance
    val weight (fun p h => weight_bounds (hp p h).1) ?_ (by norm_num [weight]) (by norm_num [weight])
  · intro L hL hroot
    have he := (hz.pow_dvd_iff_le_factorization hn.2.ne').mp ((unique 257).mpr rfl).2.2
    have hpow : (257 : ℚ)^2 ≤ 257 ^ n.factorization 257 := pow_le_pow_right₀ (by norm_num) he
    have ratio : ((1 + 257 ^ n.factorization 257 : ℕ) : ℚ) / (257 ^ n.factorization 257 : ℕ) ≤
        1 + 1 / (257 : ℚ)^2 := by
      push_cast
      apply (div_le_iff₀ (by positivity)).mpr
      norm_num at hpow ⊢
      linarith
    apply (mul_le_mul_of_nonneg_right ratio (Finset.prod_nonneg fun q hq =>
      B_nonneg (hp q (hL hq)).1.one_lt.le)).trans
    exact zmass_257 L fun q hq => ⟨(hp q (hL hq)).1, zleaf_form hz (by decide)
      (hp q (hL hq)).1 (hp q (hL hq)).2 (hroot q hq).1 (hroot q hq).2⟩
  · intro p hpP c _ hdvd _ hne
    have prime := (hp p hpP).1
    have upper := (weight_bounds prime).2
    by_cases h3 : c = 3
    · subst c
      have far : 23 ≤ p := by
        by_contra! near
        have n5 : p ≠ 5 := fun e => h5 (e ▸ to_dvd p hpP)
        have n11 : p ≠ 11 := fun e => h11 (e ▸ to_dvd p hpP)
        have n17 : p ≠ 17 := by rintro rfl; exact sq 17 hpP (by decide)
        have candidates : ∀ j : Fin 23, j.val.Prime → 3 ∣ j.val + 1 →
            j.val = 2 ∨ j.val = 5 ∨ j.val = 11 ∨ j.val = 17 := by decide +kernel
        exact (candidates ⟨p, near⟩ prime hdvd).elim (hp p hpP).2
          (fun h => h.elim n5 (fun h' => h'.elim n11 n17))
      exact step_ge (t := 23) (by decide) far upper (by norm_num [weight])
    by_cases h7 : c = 7
    · subst c
      by_cases eq : p = 13
      · subst p; norm_num [weight]
      have far : 27 ≤ p := by
        by_contra! near
        exact eq ((by decide +kernel : ∀ j : Fin 27, j.val.Prime → 7 ∣ j.val + 1 →
          j.val = 13) ⟨p, near⟩ prime hdvd)
      exact step_ge (t := 27) (by decide) far upper (by norm_num [weight])
    by_cases h13 : c = 13
    · subst c
      have far : 103 ≤ p := by
        by_contra! near
        exact (by decide +kernel : ∀ j : Fin 103, j.val.Prime → ¬ 13 ∣ j.val + 1)
          ⟨p, near⟩ prime hdvd
      exact step_ge (t := 103) (by decide) far upper (by norm_num [weight])
    exact hne (by simp [weight, h3, h7, h13]) |>.elim

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H1 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max 9 (max A B), fun n hn huniq ha he => ?_⟩
  by_cases h5 : 5 ∣ n
  · exact (hA n hn huniq ha he h5).trans (by omega)
  by_cases h11 : 11 ∣ n
  · exact (hB n hn huniq ha he h11).trans (by omega)
  exact (small_divisor hn huniq h5 h11).trans (by omega)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1
