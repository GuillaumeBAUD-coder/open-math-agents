import OMAReductions.R_Erdos647_erdos_647_R2

/-! The divisor bound (σ 0 m)^8 ≤ 45197^8 * m, by bounding (a+1)^8 / p^a at each prime p. -/

open ArithmeticFunction.sigma

namespace OMA.Erdos647R2H1

def L : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
  179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251}

def e (p : ℕ) : ℕ :=
  if p ∈ L then
    (if p = 2 then 11 else if p = 3 then 6 else if p = 5 then 4 else if p = 7 then 3
      else if p ≤ 23 then 2 else 1)
  else 0

theorem L2 : ∀ q ∈ L, 2 ≤ q := by decide +kernel

theorem smallA : ∀ p ∈ L, ∀ a ∈ Finset.range 12, (a+1)^8 * p^(e p) ≤ (e p+1)^8 * p^a := by
  decide +kernel

theorem numA : ∏ p ∈ L, (e p+1)^8 ≤ 45197^8 * ∏ p ∈ L, p^(e p) := by
  decide +kernel

theorem memL : ∀ p, p.Prime → p < 256 → p ∈ L := by
  intro p hp hlt
  interval_cases p <;> first | decide +kernel | (exfalso; norm_num at hp)

theorem stepA (a : ℕ) (ha : 11 ≤ a) : (a+2)^8 ≤ 2*(a+1)^8 := by
  have h1 : 12 * (a+2) ≤ 13 * (a+1) := by omega
  have h2 := Nat.pow_le_pow_left h1 8
  rw [mul_pow, mul_pow] at h2
  have h3 : 12^8 * (a+2)^8 ≤ 12^8 * (2 * (a+1)^8) := by
    calc _ ≤ 13^8 * (a+1)^8 := h2
      _ ≤ (2 * 12^8) * (a+1)^8 := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

theorem perP (p : ℕ) (hp : p ∈ L ∨ p.Prime) (a : ℕ) :
    (a+1)^8 * p^(e p) ≤ (e p+1)^8 * p^a := by
  by_cases hL : p ∈ L
  · have hp2 := L2 p hL
    rcases Nat.lt_or_ge a 12 with ha | ha
    · exact smallA p hL a (Finset.mem_range.mpr ha)
    · have ha' : 11 ≤ a := by omega
      clear ha
      induction a, ha' using Nat.le_induction with
      | base => exact smallA p hL 11 (by simp)
      | succ n hn ih =>
        calc (n+1+1)^8 * p^(e p) ≤ (2*(n+1)^8) * p^(e p) :=
              Nat.mul_le_mul_right _ (stepA n hn)
          _ ≤ (p*(n+1)^8) * p^(e p) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hp2)
          _ = p * ((n+1)^8 * p^(e p)) := by ring
          _ ≤ p * ((e p+1)^8 * p^n) := Nat.mul_le_mul_left _ ih
          _ = (e p+1)^8 * p^(n+1) := by ring
  · have hpr : p.Prime := hp.resolve_left hL
    have h256 : 256 ≤ p := by
      by_contra h
      exact hL (memL p hpr (by omega))
    have he : e p = 0 := by simp [e, hL]
    rw [he, pow_zero, mul_one, zero_add, one_pow, one_mul]
    have h1 : a + 1 ≤ 2^a := Nat.lt_two_pow_self
    calc (a+1)^8 ≤ (2^a)^8 := Nat.pow_le_pow_left h1 8
      _ = 256^a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p^a := Nat.pow_le_pow_left h256 a

theorem bound : ∀ m : ℕ, (σ 0 m) ^ 8 ≤ 45197 ^ 8 * m := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hm : m ≠ 0 := hm0.ne'
  have hSU : m.primeFactors ⊆ m.primeFactors ∪ L := Finset.subset_union_left
  have hLU : L ⊆ m.primeFactors ∪ L := Finset.subset_union_right
  have hf0 : ∀ p, p ∉ m.primeFactors → m.factorization p = 0 := by
    intro p hpS
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hpS
    exact hpS
  have hτ : σ 0 m = ∏ p ∈ m.primeFactors ∪ L, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]
    exact Finset.prod_subset hSU (fun p _ hpS => by simp [hf0 p hpS])
  have hmU : ∏ p ∈ m.primeFactors ∪ L, p ^ (m.factorization p) = m := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod, Nat.support_factorization]
    exact (Finset.prod_subset hSU (fun p _ hpS => by rw [hf0 p hpS, pow_zero])).symm
  have he0 : ∀ p, p ∉ L → e p = 0 := fun p h => by simp [e, h]
  have hA : ∏ p ∈ m.primeFactors ∪ L, (e p + 1)^8 = ∏ p ∈ L, (e p + 1)^8 :=
    (Finset.prod_subset hLU (fun p _ hpL => by rw [he0 p hpL]; rfl)).symm
  have hB : ∏ p ∈ m.primeFactors ∪ L, p^(e p) = ∏ p ∈ L, p^(e p) :=
    (Finset.prod_subset hLU (fun p _ hpL => by rw [he0 p hpL, pow_zero])).symm
  have hBpos : 0 < ∏ p ∈ L, p^(e p) :=
    Finset.prod_pos (fun p hp => pow_pos (by have := L2 p hp; omega) _)
  have key : (σ 0 m)^8 * ∏ p ∈ L, p^(e p) ≤ (∏ p ∈ L, (e p+1)^8) * m := by
    rw [hτ, ← hA, ← hB, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    have hm' : (∏ p ∈ m.primeFactors ∪ L, (e p+1)^8) * m =
        ∏ p ∈ m.primeFactors ∪ L, ((e p+1)^8 * p^(m.factorization p)) := by
      rw [Finset.prod_mul_distrib, hmU]
    rw [hm']
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro p hp
    apply perP
    rcases Finset.mem_union.mp hp with h | h
    · exact Or.inr (Nat.prime_of_mem_primeFactors h)
    · exact Or.inl h
  have h2 : (σ 0 m)^8 * ∏ p ∈ L, p^(e p) ≤ (45197^8 * m) * ∏ p ∈ L, p^(e p) :=
    calc _ ≤ (∏ p ∈ L, (e p+1)^8) * m := key
      _ ≤ (45197^8 * ∏ p ∈ L, p^(e p)) * m := Nat.mul_le_mul_right _ numA
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h2 hBpos

end OMA.Erdos647R2H1

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2.H1 := OMA.Erdos647R2H1.bound
