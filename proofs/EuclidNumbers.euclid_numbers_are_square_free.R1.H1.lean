import OMAReductions.R_EuclidNumbers_euclid_numbers_are_square_free_R1

/-!
# Proof of `EuclidNumbers.euclid_numbers_are_square_free.R1.H1`

Classical argument of Euclid: every prime factor `q` of the `n`-th Euclid number
`E n = 1 + ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i` satisfies `Nat.nth Nat.Prime n ≤ q`.
-/

-- Step EuclidNumbers.euclid_numbers_are_square_free.R1.H1: hypothesis H1 of reduction EuclidNumbers.euclid_numbers_are_square_free.R1
-- Credit: @LiJiaHua1024

theorem OMA.solution : OMA.R_EuclidNumbers_euclid_numbers_are_square_free_R1.H1 := by
  intro n q hq hdvd
  by_contra hlt
  push Not at hlt
  have hcount_lt : Nat.count Nat.Prime q < n := by
    by_contra hge
    push Not at hge
    have hmono : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hge
    rw [Nat.nth_count hq] at hmono
    omega
  have hmem : Nat.count Nat.Prime q ∈ Finset.range n := Finset.mem_range.mpr hcount_lt
  have hq_dvd_prod : q ∣ ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i := by
    have h := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i) hmem
    rwa [Nat.nth_count hq] at h
  rw [EuclidNumbers.Euclid] at hdvd
  have hq_dvd_one : q ∣ 1 := (Nat.dvd_add_left hq_dvd_prod).mp hdvd
  exact hq.not_dvd_one hq_dvd_one
