import OMAReductions.R_oeis_a079390_R1

-- Step oeis-a079390.R1.H1: hypothesis H1 of reduction oeis-a079390.R1
-- Credit: @Ciphore
-- The classical parts of the A079390 conjecture: twin prime pairs give record
-- values of a(n) = lpf(n) lpf(n+1) lpf(n+2), and records sit at odd n.

open OMA.S_oeis_a079390

theorem OMA.solution : OMA.R_oeis_a079390_R1.H1 := by
  intro n hn
  constructor
  · -- twin primes give records
    rintro ⟨hnp, hn2p⟩
    -- n is an odd prime, so minFac n = n, minFac (n+2) = n+2, minFac (n+1) = 2
    have hnodd : Odd n := by
      rcases hnp.eq_two_or_odd' with h2 | hodd
      · omega
      · exact hodd
    have h2dvd1 : 2 ∣ n + 1 := by
      obtain ⟨t, ht⟩ := hnodd
      omega
    have hmfn : n.minFac = n := Nat.Prime.minFac_eq hnp
    have hmfn2 : (n + 2).minFac = n + 2 := Nat.Prime.minFac_eq hn2p
    have hmfn1 : (n + 1).minFac = 2 := (Nat.minFac_eq_two_iff (n + 1)).mpr h2dvd1
    have han : a n = n * 2 * (n + 2) := by
      unfold a
      rw [hmfn, hmfn1, hmfn2]
    intro m hm1 hmn
    rcases Nat.even_or_odd m with heven | hodd
    · -- m even : a m = 4 * minFac (m+1) ≤ 4 * (m+1) < a n
      have h2m : 2 ∣ m := heven.two_dvd
      have h2m2 : 2 ∣ m + 2 := by omega
      have hmfm : m.minFac = 2 := (Nat.minFac_eq_two_iff m).mpr h2m
      have hmfm2 : (m + 2).minFac = 2 := (Nat.minFac_eq_two_iff (m + 2)).mpr h2m2
      have ham : a m = 4 * (m + 1).minFac := by
        unfold a
        rw [hmfm, hmfm2]
        ring
      have hm1pos : 0 < m + 1 := by omega
      have hmfm1le : (m + 1).minFac ≤ m + 1 := Nat.le_of_dvd hm1pos (Nat.minFac_dvd (m + 1))
      have h1 : a m ≤ 4 * (m + 1) := by
        rw [ham]
        exact Nat.mul_le_mul_left 4 hmfm1le
      have h2 : 4 * (m + 1) ≤ 4 * n := Nat.mul_le_mul_left 4 (by omega)
      have h3 : 4 * n < n * 2 * (n + 2) := by nlinarith [hn]
      rw [han]
      exact lt_of_le_of_lt (le_trans h1 h2) h3
    · -- m odd : a m ≤ 2 m (m+2) < 2 n (n+2) = a n
      obtain ⟨t, ht⟩ := hodd
      have h2m1 : 2 ∣ m + 1 := by omega
      have hmfm1 : (m + 1).minFac = 2 := (Nat.minFac_eq_two_iff (m + 1)).mpr h2m1
      have hmpos : 0 < m := by omega
      have hm2pos : 0 < m + 2 := by omega
      have hmfmle : m.minFac ≤ m := Nat.le_of_dvd hmpos (Nat.minFac_dvd m)
      have hmfm2le : (m + 2).minFac ≤ m + 2 := Nat.le_of_dvd hm2pos (Nat.minFac_dvd (m + 2))
      have ham : a m = m.minFac * 2 * (m + 2).minFac := by
        unfold a
        rw [hmfm1]
      have h1 : a m ≤ m * 2 * (m + 2) := by
        rw [ham]
        gcongr
      have h2 : m * 2 * (m + 2) < n * 2 * (n + 2) := by nlinarith [hmn]
      rw [han]
      exact lt_of_le_of_lt h1 h2
  · -- records sit at odd n
    intro hrec
    by_contra hne
    have hneven : 2 ∣ n := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hw⟩ := hneven
    have hm3 : 3 ≤ m := by omega
    -- the record hypothesis applied at m
    have hmr := hrec m (by omega) (by omega)
    -- divisibility facts from m + 1 = 2 * w
    have h2m1 : 2 ∣ m + 1 := ⟨w, hw⟩
    have h2m3 : 2 ∣ m + 3 := ⟨w + 1, by omega⟩
    have hmfm1 : (m + 1).minFac = 2 := (Nat.minFac_eq_two_iff (m + 1)).mpr h2m1
    have hmfm3 : (m + 3).minFac = 2 := (Nat.minFac_eq_two_iff (m + 3)).mpr h2m3
    have han : a (m + 1) = 4 * (m + 2).minFac := by
      unfold a
      have e1 : m + 1 + 1 = m + 2 := by omega
      have e2 : m + 1 + 2 = m + 3 := by omega
      rw [e1, e2, hmfm1, hmfm3]
      ring
    -- a m = minFac m * 2 * minFac (m+2) with 3 ≤ minFac m
    have hmodd : Odd m := ⟨w - 1, by omega⟩
    have hmne1 : m ≠ 1 := by omega
    have hmfmp : Nat.Prime m.minFac := Nat.minFac_prime hmne1
    have hmfmge2 : 2 ≤ m.minFac := hmfmp.two_le
    have hmfmne2 : m.minFac ≠ 2 := by
      intro h2
      have h2m : 2 ∣ m := (Nat.minFac_eq_two_iff m).mp h2
      obtain ⟨t, ht⟩ := hmodd
      obtain ⟨s, hs⟩ := h2m
      omega
    have hmfmge3 : 3 ≤ m.minFac := by omega
    have ham : a m = m.minFac * 2 * (m + 2).minFac := by
      unfold a
      rw [hmfm1]
    -- chain the contradiction
    have hmf2pos : 0 < (m + 2).minFac := Nat.minFac_pos (m + 2)
    have hge : 4 * (m + 2).minFac < a m := by
      rw [ham]
      nlinarith [hmfmge3, hmf2pos]
    rw [han] at hmr
    omega
