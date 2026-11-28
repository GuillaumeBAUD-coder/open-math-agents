import OMAStatements.S_oeis_a056793
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

namespace OMA.P_oeis_a056793

open OMA.S_oeis_a056793

private lemma lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  unfold lcmUpTo
  apply Nat.pos_of_ne_zero
  intro h0
  rw [Finset.lcm_eq_zero_iff] at h0
  rcases h0 with ⟨x, hx, hx0⟩
  rw [Finset.mem_Icc] at hx
  simp only [id_eq] at hx0
  omega

private lemma dvd_lcmUpTo_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    m ∣ lcmUpTo n ↔ maxPrimePower m ≤ n := by
  have hm0 : m ≠ 0 := by omega
  have hL0 : lcmUpTo n ≠ 0 := (lcmUpTo_pos n).ne'
  constructor
  · intro hdvd
    unfold maxPrimePower
    rw [max_le_iff]
    refine ⟨hn, ?_⟩
    rw [Finset.sup_le_iff]
    intro p hp
    have hpp_dvd_m : p ^ (m.factorization p) ∣ m := Nat.ordProj_dvd m p
    have hpp_dvd_L : p ^ (m.factorization p) ∣ lcmUpTo n := dvd_trans hpp_dvd_m hdvd
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos_e : 0 < m.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hp))
    -- Since p^e | lcm(1..n), p^e must divide some x in Icc 1 n (because p is prime!)
    have hex : ∃ x ∈ Finset.Icc 1 n, p ^ (m.factorization p) ∣ x := by
      have hgen : ∀ s : Finset ℕ, (∀ x ∈ s, x ≠ 0) →
          p ^ (m.factorization p) ∣ s.lcm id → ∃ x ∈ s, p ^ (m.factorization p) ∣ x := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          intro _ hd
          simp only [Finset.lcm_empty] at hd
          have h1 : p ^ (m.factorization p) = 1 := Nat.eq_one_of_dvd_one hd
          have hgt : 1 < p ^ (m.factorization p) := one_lt_pow₀ hp_prime.one_lt hpos_e.ne'
          omega
        | @insert a s ha ih =>
          intro hnz hd
          rw [Finset.lcm_insert] at hd
          have ha0 : a ≠ 0 := hnz a (Finset.mem_insert_self a s)
          have hs0 : s.lcm id ≠ 0 := by
            intro hs
            rw [Finset.lcm_eq_zero_iff] at hs
            rcases hs with ⟨x, hx, hx0⟩
            exact hnz x (Finset.mem_insert_of_mem hx) hx0
          have hfa : (Nat.lcm a (s.lcm id)).factorization p =
              max (a.factorization p) ((s.lcm id).factorization p) := by
            rw [Nat.factorization_lcm ha0 hs0]; rfl
          have hle_lcm : m.factorization p ≤ (Nat.lcm a (s.lcm id)).factorization p := by
            have := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp_prime.ne_zero)
              (Nat.lcm_ne_zero ha0 hs0)).mpr hd p
            simpa [hp_prime.factorization_pow] using this
          rw [hfa, le_max_iff] at hle_lcm
          rcases hle_lcm with h1 | h2
          · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
            exact dvd_trans (Nat.pow_dvd_pow p h1) (Nat.ordProj_dvd a p)
          · have hd2 : p ^ (m.factorization p) ∣ s.lcm id :=
              dvd_trans (Nat.pow_dvd_pow p h2) (Nat.ordProj_dvd (s.lcm id) p)
            rcases ih (fun x hx => hnz x (Finset.mem_insert_of_mem hx)) hd2 with ⟨x, hx, hxd⟩
            exact ⟨x, Finset.mem_insert_of_mem hx, hxd⟩
      exact hgen (Finset.Icc 1 n) (fun x hx => by rw [Finset.mem_Icc] at hx; omega) hpp_dvd_L
    rcases hex with ⟨x, hx, hxd⟩
    rw [Finset.mem_Icc] at hx
    have hle : p ^ (m.factorization p) ≤ x := Nat.le_of_dvd (by omega) hxd
    omega
  · intro hle
    unfold maxPrimePower at hle
    rw [max_le_iff] at hle
    have hsup : ∀ p ∈ m.primeFactors, p ^ (m.factorization p) ≤ n := Finset.sup_le_iff.mp hle.2
    rw [← Nat.factorization_le_iff_dvd hm0 hL0]
    intro p
    by_cases hp : p ∈ m.primeFactors
    · have hp_le : p ^ (m.factorization p) ≤ n := hsup p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpos : 1 ≤ p ^ (m.factorization p) := Nat.one_le_pow _ _ hp_prime.pos
      have hmem : p ^ (m.factorization p) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hpos, hp_le⟩
      have hdvd : p ^ (m.factorization p) ∣ lcmUpTo n := Finset.dvd_lcm hmem
      have hfac := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp_prime.ne_zero) hL0).mpr hdvd p
      simpa [hp_prime.factorization_pow] using hfac
    · have hz : m.factorization p = 0 := by
        by_contra hne
        exact hp (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
      rw [hz]; exact Nat.zero_le _

private lemma maxPrimePower_ge_one (m : ℕ) : 1 ≤ maxPrimePower m := by
  unfold maxPrimePower
  exact le_max_left 1 _

private lemma a101207_eq_filter_card (k n : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    a101207 k = ((lcmUpTo n).divisors.filter (fun m => maxPrimePower m = k)).card := by
  unfold a101207
  have hn : 1 ≤ n := by omega
  have hL0 : lcmUpTo n ≠ 0 := (lcmUpTo_pos n).ne'
  set S := (lcmUpTo n).divisors.filter (fun m => maxPrimePower m = k)
  have heq : {m : ℕ // 1 ≤ m ∧ maxPrimePower m = k} ≃ {m : ℕ // m ∈ S} :=
    { toFun := fun ⟨m, hm1, hmk⟩ =>
        ⟨m, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(dvd_lcmUpTo_iff m n hm1 hn).mpr (by omega), hL0⟩, hmk⟩⟩
      invFun := fun ⟨m, hmS⟩ => by
        have hf := Finset.mem_filter.mp hmS
        have hd := Nat.mem_divisors.mp hf.1
        have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (fun h => by subst h; exact hL0 (zero_dvd_iff.mp hd.1))
        exact ⟨m, hm1, hf.2⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_coe]

private lemma prove_main :
    ∀ n : ℕ, 1 ≤ n → a056793 n = ∑ k ∈ Finset.Icc 1 n, a101207 k := by
  intro n hn
  unfold a056793
  have hL0 : lcmUpTo n ≠ 0 := (lcmUpTo_pos n).ne'
  have hpart := Finset.card_eq_sum_card_fiberwise (f := maxPrimePower)
    (s := (lcmUpTo n).divisors) (t := Finset.Icc 1 n)
    (fun m hm => by
      have hd := Nat.mem_divisors.mp (Finset.mem_coe.mp hm)
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (fun h => by subst h; exact hL0 (zero_dvd_iff.mp hd.1))
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨maxPrimePower_ge_one m,
        (dvd_lcmUpTo_iff m n hm1 hn).mp hd.1⟩))
  rw [hpart]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact (a101207_eq_filter_card k n hk.1 hk.2).symm

end OMA.P_oeis_a056793

theorem OMA.solution : type_of% @OMA.S_oeis_a056793.main :=
  OMA.P_oeis_a056793.prove_main
