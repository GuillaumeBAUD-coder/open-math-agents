import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1

-- A set of eight primes with the cofactor congruences and reciprocal sum below one:
-- 2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519, the prime factors of the eighth primary pseudoperfect
-- number 8490421583559688410706771261086 (OEIS A054377; found by Butske, Jaje and Mayernik, On the equation
-- sum over p | N of 1/p + 1/N = 1, pseudoperfect numbers, and perfectly weighted graphs, Math. Comp. 69 (2000)).
-- The witness is from the literature; the proof here is original: the two large primes are certified by the
-- Lucas test (Mathlib's lucas_primality) with a kernel-evaluated modular power, recursively for the large prime
-- factor of p - 1, and the congruences follow from the product.
-- This is a known example, not progress on the open question whether such sets exist with nine or more primes.

open Finset

namespace OMA.E313

/-- Modular power by repeated squaring, with fuel. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | f + 1, b, e, m =>
      if e = 0 then 1
      else if e % 2 = 1 then (b * pm f (b * b % m) (e / 2) m) % m
      else pm f (b * b % m) (e / 2) m

lemma pm_spec : ∀ (f b e m : ℕ), e < 2 ^ f → pm f b e m ≡ b ^ e [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro b e m he
    have h0 : e = 0 := by simpa using he
    subst h0
    simp [pm, Nat.ModEq]
  | succ f ih =>
    intro b e m he
    rw [pm]
    by_cases h0 : e = 0
    · subst h0
      simp [Nat.ModEq]
    rw [if_neg h0]
    have hlt : e / 2 < 2 ^ f := by
      rw [pow_succ] at he
      omega
    have ih' := ih (b * b % m) (e / 2) m hlt
    have hsq : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
    have ih2 : pm f (b * b % m) (e / 2) m ≡ (b * b) ^ (e / 2) [MOD m] := ih'.trans hsq
    by_cases h1 : e % 2 = 1
    · rw [if_pos h1]
      have hb : b ^ e = b * (b * b) ^ (e / 2) := by
        conv_lhs => rw [show e = 2 * (e / 2) + 1 by omega]
        rw [pow_succ, pow_mul, pow_two]
        ring
      rw [hb]
      exact (Nat.mod_modEq _ _).trans ((Nat.ModEq.refl b).mul ih2)
    · rw [if_neg h1]
      have hb : b ^ e = (b * b) ^ (e / 2) := by
        conv_lhs => rw [show e = 2 * (e / 2) by omega]
        rw [pow_mul, pow_two]
      rw [hb]
      exact ih2

lemma zpow_eq (p a e : ℕ) (he : e < 2 ^ 64) :
    ((a : ZMod p)) ^ e = ((pm 64 a e p : ℕ) : ZMod p) := by
  rw [← Nat.cast_pow]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr (pm_spec 64 a e p he)).symm

lemma mem_of_dvd_prod {q : ℕ} (hq : q.Prime) (L : List ℕ) (hL : ∀ a ∈ L, a.Prime)
    (h : q ∣ L.prod) : q ∈ L := by
  obtain ⟨a, ha, hda⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hq)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hL a ha)).mp hda]

/-- The Lucas test with the prime factors of `p - 1` given as a list. -/
lemma lucas_list (p a : ℕ) (L : List ℕ) (hp1 : 1 < p) (hlt : p - 1 < 2 ^ 64)
    (hprod : L.prod = p - 1) (hL : ∀ x ∈ L, x.Prime) (h1 : pm 64 a (p - 1) p % p = 1)
    (hq : ∀ x ∈ L, pm 64 a ((p - 1) / x) p % p ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rw [zpow_eq p a (p - 1) hlt]
    have h : ((pm 64 a (p - 1) p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by
        unfold Nat.ModEq
        rw [h1, Nat.mod_eq_of_lt hp1])
    simpa using h
  · intro q hqp hqd
    rw [zpow_eq p a ((p - 1) / q) (lt_of_le_of_lt (Nat.div_le_self _ _) hlt)]
    intro hc
    have hmem : q ∈ L := mem_of_dvd_prod hqp L hL (hprod ▸ hqd)
    have h : pm 64 a ((p - 1) / q) p ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using hc)
    apply hq q hmem
    unfold Nat.ModEq at h
    rw [h, Nat.mod_eq_of_lt hp1]

theorem prime_r1 : Nat.Prime 100788283 := by
  refine lucas_list 100788283 7 [2, 3, 3, 7, 29, 27583] (by norm_num) (by norm_num) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_p1 : Nat.Prime 2217342227 := by
  refine lucas_list 2217342227 2 [2, 11, 100788283] (by norm_num) (by norm_num) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact prime_r1

theorem prime_r2 : Nat.Prime 78595501069 := by
  refine lucas_list 78595501069 2 [2, 2, 3, 3, 3, 3, 3, 7, 29, 398323] (by norm_num) (by norm_num) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_p2 : Nat.Prime 1729101023519 := by
  refine lucas_list 1729101023519 11 [2, 11, 78595501069] (by norm_num) (by norm_num) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact prime_r2

/-- The eight primes. -/
def S : Finset ℕ := {2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519}

lemma hN : ∏ q ∈ S, q = 8490421583559688410706771261086 := by
  simp [S]

theorem witness : 8 ≤ S.card ∧ S.Nonempty ∧ (∀ p ∈ S, p.Prime) ∧
    (∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) + 1) ∧ (∑ p ∈ S, (1 : ℚ) / p) < 1 := by
  refine ⟨by simp [S], ⟨2, by simp [S]⟩, ?_, ?_, ?_⟩
  · intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_p1
    · exact prime_p2
  · intro p hp
    have hp' := hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := Finset.mul_prod_erase S (fun q => q) (show 2 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 3 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 11 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 23 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 31 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 47059 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 2217342227 ∈ S by simp [S])
      rw [hN] at h
      omega
    · have h := Finset.mul_prod_erase S (fun q => q) (show 1729101023519 ∈ S by simp [S])
      rw [hN] at h
      omega
  · simp only [S]
    norm_num [Finset.sum_insert]

end OMA.E313

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H1 :=
  ⟨OMA.E313.S, OMA.E313.witness⟩
