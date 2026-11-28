import OMAStatements.S_mo_455020
import Mathlib

namespace OMA.S_mo_455020_Proof

open OMA.S_mo_455020

private lemma entry_add_mirror {m n i : ℕ} (hm : 3 ≤ m) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    entry m i 2 + entry m (n + 1 - i) 2 = target m n 2 := by
  unfold entry target
  have h1 : 2 ≤ m * (i + 1) := by nlinarith
  have h2 : 2 ≤ m * (n + 1 - i + 1) := by nlinarith
  have h3 : 4 ≤ m * (n + 3) := by nlinarith
  have hsum : (i + 1) + (n + 1 - i + 1) = n + 3 := by omega
  have hmul : m * (i + 1) + m * (n + 1 - i + 1) = m * (n + 3) := by
    rw [← mul_add, hsum]
  omega

private lemma entry_succ_add_mirror {m n i : ℕ} (hm : 3 ≤ m) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (entry m i 2 + 1) + (entry m (n + 1 - i) 2 + 1) = target m n 1 := by
  unfold entry target
  have h1 : 2 ≤ m * (i + 1) := by nlinarith
  have h2 : 2 ≤ m * (n + 1 - i + 1) := by nlinarith
  have h3 : 2 ≤ m * (n + 3) := by nlinarith
  have hsum : (i + 1) + (n + 1 - i + 1) = n + 3 := by omega
  have hmul : m * (i + 1) + m * (n + 1 - i + 1) = m * (n + 3) := by
    rw [← mul_add, hsum]
  omega

private lemma even_of_twins {m n : ℕ} (hm : 3 ≤ m) (hm_odd : Odd m) (hn : 1 ≤ n)
    (ht : twins m n) : Even n := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · exfalso
    have hP_prime : (target m n 2).Prime := ht.1
    have hP_even : 2 ∣ target m n 2 := by
      rcases hodd with ⟨k, rfl⟩
      unfold target
      have h1 : m * (2 * k + 1 + 3) = 2 * (m * (k + 2)) := by ring
      have h2 : 4 ≤ 2 * (m * (k + 2)) := by nlinarith
      rw [h1]
      exact ⟨m * (k + 2) - 2, by omega⟩
    have hP_eq2 : target m n 2 = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hP_prime).mp hP_even).symm
    unfold target at hP_eq2
    have hmul : 12 ≤ m * (n + 3) := by nlinarith
    omega

private lemma even_of_passes {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (hp : passes m n) : Even n := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · exfalso
    rcases hodd with ⟨k, rfl⟩
    let i := k + 1
    have hi_mem : i ∈ Finset.Icc 1 (2 * k + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfe := hp i hi_mem
    unfold finalEntry entry at hfe
    have hij : i = 2 * k + 1 + 1 - i := by dsimp [i]; omega
    simp only [← hij, ↓reduceIte, Nat.gcd_self] at hfe
    have hx : 6 ≤ m * (i + 1) := by dsimp [i]; nlinarith
    have hx_ge : 4 ≤ m * (i + 1) - 2 := by omega
    omega

private lemma twins_imp_passes {m n : ℕ} (hm : 3 ≤ m) (hm_odd : Odd m) (hn : 1 ≤ n)
    (ht : twins m n) : passes m n := by
  have hev := even_of_twins hm hm_odd hn ht
  intro i hi
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi1, hin⟩ := hi
  unfold finalEntry
  have hij : i ≠ n + 1 - i := by
    rcases hev with ⟨k, rfl⟩
    omega
  rw [if_neg hij]
  let x := entry m i 2
  let y := entry m (n + 1 - i) 2
  have hxy : x + y = target m n 2 := entry_add_mirror hm hi1 hin
  have hxy1 : (x + 1) + (y + 1) = target m n 1 := entry_succ_add_mirror hm hi1 hin
  have hx_pos : 0 < x := by
    unfold x entry
    have : 6 ≤ m * (i + 1) := by nlinarith
    omega
  have hy_pos : 0 < y := by
    unfold y entry
    have h2 : 2 ≤ n + 1 - i + 1 := by omega
    have : 6 ≤ m * (n + 1 - i + 1) := by nlinarith
    omega
  have hx_lt_P : x < target m n 2 := by omega
  have hx1_lt_Q : x + 1 < target m n 1 := by omega
  have hg : x.gcd y = 1 := by
    have h1 : x.gcd y = x.gcd (x + y) := (Nat.gcd_self_add_right x y).symm
    rw [h1, hxy, Nat.gcd_comm]
    exact ht.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hx_pos hx_lt_P)
  have hg1 : (x + 1).gcd (y + 1) = 1 := by
    have h1 : (x + 1).gcd (y + 1) = (x + 1).gcd ((x + 1) + (y + 1)) :=
      (Nat.gcd_self_add_right (x + 1) (y + 1)).symm
    rw [h1, hxy1, Nat.gcd_comm]
    exact ht.2.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hx1_lt_Q)
  change x + x.gcd y + (x + x.gcd y).gcd (y + x.gcd y) = m * (i + 1)
  rw [hg, hg1]
  unfold x entry
  have : 2 ≤ m * (i + 1) := by nlinarith
  omega

private lemma exists_index_dvd {m p c : ℕ} (hp : p.Prime) (hcop : Nat.Coprime m p) (hc : c ≤ 2)
    (hm : 3 ≤ m) : ∃ i : ℕ, 1 ≤ i ∧ i ≤ p ∧ p ∣ (m * (i + 1) - c) := by
  -- Work in ZMod p where m is a unit
  haveI : Fact p.Prime := ⟨hp⟩
  let u : ZMod p := (m : ZMod p)
  have hu : u ≠ 0 := by
    intro h0
    have hdvd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp h0
    exact (hp.coprime_iff_not_dvd.mp hcop.symm) hdvd
  let s : ZMod p := u⁻¹ * (c : ZMod p) - 1
  let r : ℕ := s.val
  let i : ℕ := if r = 0 then p else r
  have hr_lt : r < p := ZMod.val_lt s
  have hi1 : 1 ≤ i := by dsimp [i]; split_ifs <;> omega
  have hip : i ≤ p := by dsimp [i]; split_ifs <;> omega
  have hi_mod : (i : ZMod p) = s := by
    dsimp [i]
    split_ifs with hr0
    · rw [ZMod.natCast_self]
      have h0 : s.val = 0 := hr0
      have := ZMod.natCast_zmod_val s
      rw [h0, Nat.cast_zero] at this
      exact this
    · exact ZMod.natCast_zmod_val s
  have hcong : ((m * (i + 1) - c : ℕ) : ZMod p) = 0 := by
    have hle : c ≤ m * (i + 1) := by nlinarith
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hi_mod]
    dsimp [s, u]
    have h1 : (m : ZMod p) * ((m : ZMod p)⁻¹ * (c : ZMod p) - 1 + 1) - (c : ZMod p) =
        ((m : ZMod p) * (m : ZMod p)⁻¹) * (c : ZMod p) - (c : ZMod p) := by ring
    rw [h1, mul_inv_cancel₀ hu, one_mul, sub_self]
  exact ⟨i, hi1, hip, (ZMod.natCast_eq_zero_iff _ p).mp hcong⟩

private lemma passes_imp_twins {m n : ℕ} (hm : 3 ≤ m) (hm_odd : Odd m) (hn : 2 * m + 4 ≤ n)
    (hp : passes m n) : twins m n := by
  have hn1 : 1 ≤ n := by omega
  have hev := even_of_passes hm hn1 hp
  -- Extract gcd conditions for every i ∈ [1, n]
  have hgcd : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (entry m i 2).gcd (target m n 2) = 1 ∧ (entry m i 2 + 1).gcd (target m n 1) = 1 := by
    intro i hi1 hin
    have hfe := hp i (Finset.mem_Icc.mpr ⟨hi1, hin⟩)
    unfold finalEntry at hfe
    have hij : i ≠ n + 1 - i := by rcases hev with ⟨k, rfl⟩; omega
    rw [if_neg hij] at hfe
    let x := entry m i 2
    let y := entry m (n + 1 - i) 2
    let g := x.gcd y
    have hx_pos : 0 < x := by
      unfold x entry
      have : 6 ≤ m * (i + 1) := by nlinarith
      omega
    have hg_pos : 1 ≤ g := Nat.pos_of_ne_zero (by intro h; have := Nat.gcd_eq_zero_iff.mp h; omega)
    have hg2_pos : 1 ≤ (x + g).gcd (y + g) :=
      Nat.pos_of_ne_zero (by intro h; have := Nat.gcd_eq_zero_iff.mp h; omega)
    have hx_eq : m * (i + 1) = x + 2 := by
      unfold x entry
      have : 2 ≤ m * (i + 1) := by nlinarith
      omega
    have hsum2 : g + (x + g).gcd (y + g) = 2 := by
      change x + g + (x + g).gcd (y + g) = m * (i + 1) at hfe
      omega
    have hg1 : g = 1 := by omega
    have hg2 : (x + 1).gcd (y + 1) = 1 := by
      have h : (x + g).gcd (y + g) = 1 := by omega
      rwa [hg1] at h
    have hxy := entry_add_mirror hm hi1 hin
    have hxy1 := entry_succ_add_mirror hm hi1 hin
    constructor
    · rw [← hxy, Nat.gcd_self_add_right]
      exact hg1
    · rw [← hxy1, Nat.gcd_self_add_right]
      exact hg2
  -- Prove both targets are prime
  have hmul_le_sq : m * (n + 3) ≤ n * n := by nlinarith
  have hmul_ge6 : 6 ≤ m * (n + 3) := by nlinarith
  have hsq_bound : target m n 1 ≤ n * n := by unfold target; omega
  have hsq_bound2 : target m n 2 ≤ n * n := by unfold target; omega
  have hP_ge2 : 2 ≤ target m n 2 := by unfold target; omega
  have hQ_ge2 : 2 ≤ target m n 1 := by unfold target; omega
  constructor
  · -- target m n 2 is prime
    by_contra hnot
    let p := (target m n 2).minFac
    have hp_prime : p.Prime := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ target m n 2 := Nat.minFac_dvd _
    have hp_sq : p * p ≤ target m n 2 := by
      have := Nat.minFac_sq_le_self (by omega) hnot
      simpa [sq] using this
    have hp_le_n : p ≤ n := by nlinarith
    have hcop : Nat.Coprime m p := by
      rw [Nat.coprime_comm]
      refine hp_prime.coprime_iff_not_dvd.mpr fun hpm => ?_
      have h4 : p ∣ 4 := by
        unfold target at hp_dvd
        have hmul : p ∣ m * (n + 3) := dvd_mul_of_dvd_left hpm _
        have hle : 4 ≤ m * (n + 3) := by nlinarith
        have hsub := Nat.dvd_sub hmul hp_dvd
        have : m * (n + 3) - (m * (n + 3) - 4) = 4 := by omega
        rwa [this] at hsub
      have hp2 : p = 2 := by
        have := hp_prime.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
        exact (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp this
      rw [hp2] at hpm
      exact Nat.not_even_iff_odd.mpr hm_odd (even_iff_two_dvd.mpr hpm)
    obtain ⟨i, hi1, hip, hi_dvd⟩ := exists_index_dvd hp_prime hcop (by omega : 2 ≤ 2) hm
    have hg1 := (hgcd i hi1 (le_trans hip hp_le_n)).1
    have hdvd_gcd : p ∣ (entry m i 2).gcd (target m n 2) := Nat.dvd_gcd hi_dvd hp_dvd
    rw [hg1] at hdvd_gcd
    exact hp_prime.not_dvd_one hdvd_gcd
  · -- target m n 1 is prime
    by_contra hnot
    let p := (target m n 1).minFac
    have hp_prime : p.Prime := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ target m n 1 := Nat.minFac_dvd _
    have hp_sq : p * p ≤ target m n 1 := by
      have := Nat.minFac_sq_le_self (by omega) hnot
      simpa [sq] using this
    have hp_le_n : p ≤ n := by nlinarith
    have hcop : Nat.Coprime m p := by
      rw [Nat.coprime_comm]
      refine hp_prime.coprime_iff_not_dvd.mpr fun hpm => ?_
      have h2 : p ∣ 2 := by
        unfold target at hp_dvd
        have hmul : p ∣ m * (n + 3) := dvd_mul_of_dvd_left hpm _
        have hle : 2 ≤ m * (n + 3) := by nlinarith
        have hsub := Nat.dvd_sub hmul hp_dvd
        have : m * (n + 3) - (m * (n + 3) - 2) = 2 := by omega
        rwa [this] at hsub
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h2
      rw [hp2] at hpm
      exact Nat.not_even_iff_odd.mpr hm_odd (even_iff_two_dvd.mpr hpm)
    obtain ⟨i, hi1, hip, hi_dvd⟩ := exists_index_dvd hp_prime hcop (by omega : 1 ≤ 2) hm
    have hg2 := (hgcd i hi1 (le_trans hip hp_le_n)).2
    have hentry1 : entry m i 2 + 1 = m * (i + 1) - 1 := by
      unfold entry
      have : 2 ≤ m * (i + 1) := by nlinarith
      omega
    rw [hentry1] at hg2
    have hdvd_gcd : p ∣ (m * (i + 1) - 1).gcd (target m n 1) := Nat.dvd_gcd hi_dvd hp_dvd
    rw [hg2] at hdvd_gcd
    exact hp_prime.not_dvd_one hdvd_gcd

theorem main_proof : ∀ m : ℕ, 3 ≤ m → Odd m →
    (∀ n : ℕ, 1 ≤ n → twins m n → passes m n) ∧
    (∃ N : ℕ, ∀ n ≥ N, passes m n ↔ twins m n) := by
  intro m hm hm_odd
  refine ⟨fun n hn ht => twins_imp_passes hm hm_odd hn ht, ⟨2 * m + 4, fun n hn => ?_⟩⟩
  exact ⟨passes_imp_twins hm hm_odd hn, twins_imp_passes hm hm_odd (by omega)⟩

end OMA.S_mo_455020_Proof

theorem OMA.solution : type_of% @OMA.S_mo_455020.main :=
  OMA.S_mo_455020_Proof.main_proof
