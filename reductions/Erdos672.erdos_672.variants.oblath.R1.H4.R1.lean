import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1
import Mathlib

-- Step Erdos672.erdos_672.variants.oblath.R1.H4: hypothesis H4 of reduction
-- Erdos672.erdos_672.variants.oblath.R1
--
-- `Erdos672.Erdos672With 3 5`: for positive `n`, `d` with `gcd n d = 1`, the product
-- `n * (n + d) * (n + 2 * d)` is never a perfect fifth power.
--
-- The reduction below is unconditional. It splits on the parity of `n` and produces
--   `H1`  : the odd branch, `x ^ 5 + y ^ 5 = 2 * z ^ 5` has no nontrivial solution
--                (no three distinct fifth powers in arithmetic progression),
--   `H2` : the even branch, `g ^ 5 + 8 * b ^ 5 = s ^ 5` has no solution with `b`, `g`
--                positive.
-- The theorem `h4_of_cores` derives `Erdos672With 3 5` from those two propositions.

/-!
# H4 of Erdős 672 (Obláth), `k = 3`, `l = 5`

Suppose `n * (n + d) * (n + 2 * d) = q ^ 5` with `n`, `d` positive and `gcd n d = 1`.

The three terms have small pairwise gcds: `gcd n (n + d)` and `gcd (n + d) (n + 2 * d)` are `1`,
and `gcd n (n + 2 * d)` divides `2`.

* `n` odd: all three terms are odd, so they are pairwise coprime and each of them is a fifth
  power, say `n = a ^ 5`, `n + d = b ^ 5`, `n + 2 * d = c ^ 5`. Then `a ^ 5 + c ^ 5 = 2 * b ^ 5`
  with `a ≠ c` and `b ≠ 0`, which is `H1`.
* `n` even: then `d` is odd and `gcd n (n + 2 * d) = 2`. Write `n = 2 * A` and `C = A + d`, so
  `n + d = A + C` and `n + 2 * d = 2 * C`. Exactly one of `A`, `C` is even, so the three
  pairwise coprime numbers `4 * A`, `C`, `A + C` multiply to `q ^ 5` (the factor `4` sits on the
  even one, and `A + C` is odd). Each is a fifth power; `4 * A = y ^ 5` forces `A = 8 * b ^ 5`,
  `C = g ^ 5` and `A + C = s ^ 5` give `g ^ 5 + 8 * b ^ 5 = s ^ 5` with `b`, `g` positive, which
  is `H2`.
-/

namespace OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1

/- ## Splitting coprime products of fifth powers -/

/-- A factor of a fifth power coprime to the rest is itself a fifth power. -/
lemma pow5_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 5) :
    ∃ u, a = u ^ 5 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

/-- If `4 * X` is a fifth power then `X` is eight times a fifth power. -/
lemma eq_eight_mul_pow5 {X : ℕ} {y : ℕ} (h : 4 * X = y ^ 5) : ∃ u, X = 8 * u ^ 5 := by
  have h2 : 2 ∣ y := by
    refine Nat.prime_two.dvd_of_dvd_pow (n := 5) ?_
    rw [← h]
    exact ⟨2 * X, by ring⟩
  obtain ⟨u, rfl⟩ := h2
  refine ⟨u, ?_⟩
  have hy : 4 * X = 32 * u ^ 5 := by rw [h]; ring
  omega

/- ## The gcd structure of a three term progression -/

/-- The first and second term of the progression are coprime. -/
lemma coprime_n_naddd {n d : ℕ} (hnd : n.gcd d = 1) : Nat.Coprime n (n + d) := by
  rw [Nat.coprime_self_add_right]
  exact hnd

/-- The second and third term of the progression are coprime. -/
lemma coprime_naddd_n2d {n d : ℕ} (hnd : n.gcd d = 1) : Nat.Coprime (n + d) (n + 2 * d) := by
  have h : n + 2 * d = (n + d) + d := by ring
  rw [h, Nat.coprime_self_add_right, Nat.coprime_add_self_left]
  exact hnd

/-- The outer terms of the progression have gcd dividing `2`. -/
lemma gcd_n_n2d_dvd_two {n d : ℕ} (hnd : n.gcd d = 1) : Nat.gcd n (n + 2 * d) ∣ 2 := by
  have h1 : Nat.gcd n (n + 2 * d) = Nat.gcd n (2 * d) := by
    rw [Nat.gcd_self_add_right]
  rw [h1]
  have hcop : Nat.Coprime (Nat.gcd n (2 * d)) d := by
    rw [Nat.Coprime, Nat.gcd_assoc]
    rw [show Nat.gcd (2 * d) d = d from
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd (Nat.dvd_mul_left d 2) dvd_rfl)]
    exact hnd
  exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right n (2 * d))

/-- With `n` odd the outer terms of the progression are coprime. -/
lemma coprime_n_n2d_of_odd {n d : ℕ} (hnd : n.gcd d = 1) (hodd : Odd n) :
    Nat.Coprime n (n + 2 * d) := by
  rw [Nat.coprime_self_add_right]
  exact hodd.coprime_two_right.mul_right hnd

/- ## The two remaining classical statements -/

/-- No three distinct fifth powers are in arithmetic progression, in the integral form
`x ^ 5 + y ^ 5 = 2 * z ^ 5`. -/
def H1 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0

/-- The shifted equation `g ^ 5 + 8 * b ^ 5 = s ^ 5` has no solution with `b`, `g` positive. -/
def H2 : Prop := ∀ b g s : ℕ, 0 < b → 0 < g → g ^ 5 + 8 * b ^ 5 ≠ s ^ 5

/- ## The odd branch -/

/-- If `n` is odd and `n * (n + d) * (n + 2 * d)` is a fifth power, then the three terms are
fifth powers `a ^ 5`, `b ^ 5`, `c ^ 5` in arithmetic progression, with `a ≠ c` and `b ≠ 0`. -/
theorem odd_branch {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (hodd : Odd n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) :
    ∃ a b c : ℕ, n = a ^ 5 ∧ n + d = b ^ 5 ∧ n + 2 * d = c ^ 5 ∧
      a ^ 5 + c ^ 5 = 2 * b ^ 5 ∧ a ≠ c ∧ b ≠ 0 := by
  have c1 : Nat.Coprime (n + d) n := (coprime_n_naddd hnd).symm
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := coprime_naddd_n2d hnd
  have c3 : Nat.Coprime n (n + 2 * d) := coprime_n_n2d_of_odd hnd hodd
  obtain ⟨b, hb⟩ := pow5_of_coprime (c1.mul_right c2) (by rw [← hq]; ring)
  obtain ⟨a, ha⟩ := pow5_of_coprime (c1.symm.mul_right c3) hq
  obtain ⟨c, hc⟩ := pow5_of_coprime (c3.symm.mul_right c2.symm) (by rw [← hq]; ring)
  have hsum : a ^ 5 + c ^ 5 = 2 * b ^ 5 := by
    rw [← ha, ← hb, ← hc]
    ring
  refine ⟨a, b, c, ha, hb, hc, hsum, ?_, ?_⟩
  · intro h
    subst h
    omega
  · intro h
    subst h
    simp at hb
    omega

/-- On the odd branch, `H1` gives a contradiction. -/
theorem false_of_odd (hcore : H1) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) (hodd : Odd n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) : False := by
  obtain ⟨a, b, c, ha, hb, hc, hsum, hac, hb0⟩ := odd_branch hn hd hnd hodd hq
  have hkey : ((a : ℤ)) ^ 5 + ((c : ℤ)) ^ 5 = 2 * ((b : ℤ)) ^ 5 := by
    exact_mod_cast hsum
  rcases hcore a c b hkey with h | h
  · exact hac (by exact_mod_cast h)
  · exact hb0 (by exact_mod_cast h)

/- ## The even branch -/

/-- From `4 * A * C * (A + C)` a fifth power, with `A`, `C` positive and coprime and `A + C`
odd, one gets positive `b`, `g`, `s` with `g ^ 5 + 8 * b ^ 5 = s ^ 5`. -/
theorem exists_eight_of_even {A C q : ℕ} (hA : 0 < A) (hC : 0 < C) (hcop : Nat.Coprime A C)
    (hodd : Odd (A + C)) (hq : 4 * (A * C * (A + C)) = q ^ 5) :
    ∃ b g s : ℕ, 0 < b ∧ 0 < g ∧ g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
  have h2 : Nat.Coprime 2 (A + C) := hodd.coprime_two_left
  have hAAC : Nat.Coprime A (A + C) := by
    rw [Nat.coprime_self_add_right]
    exact hcop
  have hCAC : Nat.Coprime C (A + C) := by
    have h : Nat.Coprime C (C + A) := by
      rw [Nat.coprime_self_add_right]
      exact hcop.symm
    rwa [add_comm C A] at h
  rcases Nat.even_or_odd A with hAe | hAo
  · -- `A` even and `C` odd: the coprime triple is `4 * A`, `C`, `A + C`
    have hCodd : Odd C := by
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨k, hk⟩ := hAe
      exact ⟨j - k, by omega⟩
    have h4C : Nat.Coprime (2 * 2) C := hCodd.coprime_two_left.mul_left hCodd.coprime_two_left
    have h4AC : Nat.Coprime (4 * A) C := by
      have h := h4C.mul_left hcop
      rwa [show 2 * 2 = 4 from rfl] at h
    have h4AAC : Nat.Coprime (4 * A) (A + C) := by
      have h2A : Nat.Coprime (2 * A) (A + C) := h2.mul_left hAAC
      have h := h2.mul_left h2A
      rwa [show 2 * (2 * A) = 4 * A from by ring] at h
    have hp1 : (4 * A) * (C * (A + C)) = q ^ 5 := by rw [← hq]; ring
    have hp2 : C * ((A + C) * (4 * A)) = q ^ 5 := by rw [← hq]; ring
    have hp3 : (A + C) * (C * (4 * A)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨y, hy⟩ := pow5_of_coprime (h4AC.mul_right h4AAC) hp1
    obtain ⟨g, hg⟩ := pow5_of_coprime (hCAC.mul_right h4AC.symm) hp2
    obtain ⟨s, hs⟩ := pow5_of_coprime (hCAC.symm.mul_right h4AAC.symm) hp3
    obtain ⟨b, hb⟩ := eq_eight_mul_pow5 hy
    refine ⟨b, g, s, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0] at hb
        simp at hb
        omega
      · exact h0
    · rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hg
        simp at hg
        omega
      · exact h0
    · have h : g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
        rw [← hg, ← hb]
        omega
      exact h
  · -- `A` odd and `C` even: the coprime triple is `A`, `4 * C`, `A + C`
    have hCe : Even C := by
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨k, hk⟩ := hAo
      exact ⟨j - k, by omega⟩
    have hAodd : Odd A := hAo
    have h4A : Nat.Coprime (2 * 2) A := hAodd.coprime_two_left.mul_left hAodd.coprime_two_left
    have h4CA : Nat.Coprime (4 * C) A := by
      have h := h4A.mul_left hcop.symm
      rwa [show 2 * 2 = 4 from rfl] at h
    have hA4C : Nat.Coprime A (4 * C) := h4CA.symm
    have h4CAC : Nat.Coprime (4 * C) (A + C) := by
      have h2C : Nat.Coprime (2 * C) (A + C) := h2.mul_left hCAC
      have h := h2.mul_left h2C
      rwa [show 2 * (2 * C) = 4 * C from by ring] at h
    have hp1 : A * ((A + C) * (4 * C)) = q ^ 5 := by rw [← hq]; ring
    have hp2 : (4 * C) * (A * (A + C)) = q ^ 5 := by rw [← hq]; ring
    have hp3 : (A + C) * (A * (4 * C)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨g, hg⟩ := pow5_of_coprime (hAAC.mul_right hA4C) hp1
    obtain ⟨y, hy⟩ := pow5_of_coprime (h4CA.mul_right h4CAC) hp2
    obtain ⟨s, hs⟩ := pow5_of_coprime (hAAC.symm.mul_right h4CAC.symm) hp3
    obtain ⟨b, hb⟩ := eq_eight_mul_pow5 hy
    refine ⟨b, g, s, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0] at hb
        simp at hb
        omega
      · exact h0
    · rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hg
        simp at hg
        omega
      · exact h0
    · have h : g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
        rw [← hg, ← hb]
        omega
      exact h

/-- If `n` is even and `n * (n + d) * (n + 2 * d)` is a fifth power, then one gets a solution
of `g ^ 5 + 8 * b ^ 5 = s ^ 5` with `b`, `g` positive. -/
theorem even_branch {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (hev : Even n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) :
    ∃ b g s : ℕ, 0 < b ∧ 0 < g ∧ g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
  obtain ⟨A, hA⟩ := hev
  have hA' : n = 2 * A := by omega
  subst hA'
  have hdodd : Odd d := by
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, by ring⟩ ⟨k, by omega⟩
      rw [hnd] at h2
      omega
    · exact h
  have hApos : 0 < A := by omega
  have hAC : Nat.Coprime A (A + d) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.Coprime.coprime_mul_left hnd
  have hoddAC : Odd (A + (A + d)) := by
    have he : A + (A + d) = 2 * A + d := by ring
    rw [he]
    obtain ⟨k, hk⟩ := hdodd
    exact ⟨A + k, by omega⟩
  have hq' : 4 * (A * (A + d) * (A + (A + d))) = q ^ 5 := by
    have h1 : 2 * A + d = A + (A + d) := by ring
    have h2 : 2 * A + 2 * d = 2 * (A + d) := by ring
    rw [h1, h2] at hq
    have he : 4 * (A * (A + d) * (A + (A + d))) = 2 * A * ((A + (A + d)) * (2 * (A + d))) := by
      ring
    rw [he]
    exact hq
  exact exists_eight_of_even hApos (by omega) hAC hoddAC hq'

/-- On the even branch, `H2` gives a contradiction. -/
theorem false_of_even (hcore : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) (hev : Even n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) : False := by
  obtain ⟨b, g, s, hb0, hg0, heq⟩ := even_branch hn hd hnd hev hq
  exact hcore b g s hb0 hg0 heq

/- ## The arithmetic progression -/

/-- The product of a three term arithmetic progression with coprime first term and difference is
never a perfect fifth power, assuming the two fifth power cores. -/
theorem ap3_ne_pow5 (ho : H1) (he : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 5 := by
  intro hq
  rcases Nat.even_or_odd n with hev | hodd
  · exact false_of_even he hn hd hnd hev hq
  · exact false_of_odd ho hn hd hnd hodd hq

/-- `Erdos672With 3 5` follows from the two fifth power cores. -/
theorem h4_of_cores (ho : H1) (he : H2) : Erdos672.Erdos672With 3 5 := by
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact ap3_ne_pow5 ho he hn hd hnd hq

/-- The same statement in the shape of the step statement `H4` of the reduction. -/
theorem main : H1 → H2 → OMA.R_Erdos672_erdos_672_variants_oblath_R1.H4 :=
  h4_of_cores

end OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1
