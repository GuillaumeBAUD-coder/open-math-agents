import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

/-! Extend the known Fermat-level obstructions for the sole repeated odd prime 3.
All levels 21 through 32 except 24 are excluded by explicit prime-factor chains.
The remaining exponent tail splits into levels 20, 24 and exponents divisible by 2^33.
Force and square lemmas follow @adammcarter’s reduction; Fermat factors follow
the Keller factor table as recorded in oeis-a000215.R2. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H3_R1
namespace UnitaryFermatLevels
open Finset

theorem S_mem {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N)
    (hd : c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1)) : c ∈ P := by
  rw [E] at hd
  rcases (Nat.Prime.dvd_mul hc).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hc (hP p hp).1).mp hcp]

theorem S_sq {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N) :
    ¬ c * c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by
  intro hd
  have hcP : c ∈ P := S_mem hP hK E hc hc2 hcz ((dvd_mul_right c c).trans hd)
  rw [E, ← Finset.mul_prod_erase P (fun p => p) hcP, mul_left_comm] at hd
  have h1 : c ∣ 2 ^ (m + 1) * K * ∏ p ∈ P.erase c, p := Nat.dvd_of_mul_dvd_mul_left hc.pos hd
  rcases (Nat.Prime.dvd_mul hc).mp h1 with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hc (hP p (Finset.mem_of_mem_erase hp)).1).mp hcp
    exact (Finset.ne_of_mem_erase hp) this.symm

theorem facts {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) :
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, c ∣ p + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p') ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → ∀ p ∈ P, ¬ c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ¬ c * c ∣ 2 ^ m + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ¬ c * c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → ∀ p ∈ P, ¬ c ∣ p + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hc2 hcz p hp hd
    exact S_mem hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp p' hp' hd hd'
    by_contra hne
    apply S_sq hP hK E hc hc2 hcz
    have hsub : ({p, p'} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton.mp hx]; exact hp'
    have h1 : (p + 1) * (p' + 1) ∣ ∏ x ∈ P, (x + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hsub
      rwa [Finset.prod_pair hne] at this
    exact ((mul_dvd_mul hd hd').trans h1).mul_left _
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left K'
    have e : K' * ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) = (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by ring
    rwa [e] at h
  · intro c hc hc2 hcz hd
    exact S_sq hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp hd
    exact S_sq hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_left _).mul_right _)
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left
      (2 ^ m + 1)
    rwa [← mul_assoc] at h


private theorem prime_10487 : Nat.Prime 10487 := by
  refine lucas_primality 10487 (5 : ZMod 10487) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 10487 - 1 = [2^1, 7^2, 107^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 107 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_81281 : Nat.Prime 81281 := by
  refine lucas_primality 81281 (3 : ZMod 81281) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 81281 - 1 = [2^7, 5^1, 127^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_27647 : Nat.Prime 27647 := by
  refine lucas_primality 27647 (5 : ZMod 27647) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 27647 - 1 = [2^1, 23^1, 601^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 601 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_165883 : Nat.Prime 165883 := by
  refine lucas_primality 165883 (2 : ZMod 165883) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 165883 - 1 = [2^1, 3^1, 27647^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 27647 := (Nat.prime_dvd_prime_iff_eq hq prime_27647).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_30091 : Nat.Prime 30091 := by
  refine lucas_primality 30091 (21 : ZMod 30091) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 30091 - 1 = [2^1, 3^1, 5^1, 17^1, 59^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_662003 : Nat.Prime 662003 := by
  refine lucas_primality 662003 (2 : ZMod 662003) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 662003 - 1 = [2^1, 11^1, 30091^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 30091 := (Nat.prime_dvd_prime_iff_eq hq prime_30091).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_3972019 : Nat.Prime 3972019 := by
  refine lucas_primality 3972019 (2 : ZMod 3972019) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 3972019 - 1 = [2^1, 3^1, 662003^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 662003 := (Nat.prime_dvd_prime_iff_eq hq prime_662003).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_16149761 : Nat.Prime 16149761 := by
  refine lucas_primality 16149761 (6 : ZMod 16149761) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 16149761 - 1 = [2^8, 5^1, 11^1, 31^1, 37^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 37 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_26114321 : Nat.Prime 26114321 := by
  refine lucas_primality 26114321 (3 : ZMod 26114321) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 26114321 - 1 = [2^4, 5^1, 197^1, 1657^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 197 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1657 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_291271 : Nat.Prime 291271 := by
  refine lucas_primality 291271 (15 : ZMod 291271) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 291271 - 1 = [2^1, 3^1, 5^1, 7^1, 19^1, 73^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 73 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_3495253 : Nat.Prime 3495253 := by
  refine lucas_primality 3495253 (2 : ZMod 3495253) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 3495253 - 1 = [2^2, 3^1, 291271^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 291271 := (Nat.prime_dvd_prime_iff_eq hq prime_291271).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_13981013 : Nat.Prime 13981013 := by
  refine lucas_primality 13981013 (2 : ZMod 13981013) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 13981013 - 1 = [2^2, 3495253^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3495253 := (Nat.prime_dvd_prime_iff_eq hq prime_3495253).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_27962027 : Nat.Prime 27962027 := by
  refine lucas_primality 27962027 (2 : ZMod 27962027) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 27962027 - 1 = [2^1, 13981013^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 13981013 := (Nat.prime_dvd_prime_iff_eq hq prime_13981013).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_167772161 : Nat.Prime 167772161 := by
  refine lucas_primality 167772161 (3 : ZMod 167772161) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 167772161 - 1 = [2^25, 5^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_1685033089 : Nat.Prime 1685033089 := by
  refine lucas_primality 1685033089 (14 : ZMod 1685033089) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 1685033089 - 1 = [2^7, 3^1, 19^1, 41^1, 43^1, 131^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 41 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 131 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_22807 : Nat.Prime 22807 := by
  refine lucas_primality 22807 (3 : ZMod 22807) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 22807 - 1 = [2^1, 3^2, 7^1, 181^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 181 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_4789471 : Nat.Prime 4789471 := by
  refine lucas_primality 4789471 (6 : ZMod 4789471) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 4789471 - 1 = [2^1, 3^1, 5^1, 7^1, 22807^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 22807 := (Nat.prime_dvd_prime_iff_eq hq prime_22807).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_2404314443 : Nat.Prime 2404314443 := by
  refine lucas_primality 2404314443 (2 : ZMod 2404314443) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 2404314443 - 1 = [2^1, 251^1, 4789471^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 251 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 4789471 := (Nat.prime_dvd_prime_iff_eq hq prime_4789471).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_14425886659 : Nat.Prime 14425886659 := by
  refine lucas_primality 14425886659 (2 : ZMod 14425886659) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 14425886659 - 1 = [2^1, 3^1, 2404314443^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 2404314443 := (Nat.prime_dvd_prime_iff_eq hq prime_2404314443).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_28851773317 : Nat.Prime 28851773317 := by
  refine lucas_primality 28851773317 (5 : ZMod 28851773317) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 28851773317 - 1 = [2^2, 3^1, 2404314443^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 2404314443 := (Nat.prime_dvd_prime_iff_eq hq prime_2404314443).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_4485296422913 : Nat.Prime 4485296422913 := by
  refine lucas_primality 4485296422913 (3 : ZMod 4485296422913) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 4485296422913 - 1 = [2^23, 503^1, 1063^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 503 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1063 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_12704513261569 : Nat.Prime 12704513261569 := by
  refine lucas_primality 12704513261569 (11 : ZMod 12704513261569) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 12704513261569 - 1 = [2^33, 3^1, 17^1, 29^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 29 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_27536591 : Nat.Prime 27536591 := by
  refine lucas_primality 27536591 (11 : ZMod 27536591) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 27536591 - 1 = [2^1, 5^1, 431^1, 6389^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 431 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 6389 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_12810187352747 : Nat.Prime 12810187352747 := by
  refine lucas_primality 12810187352747 (2 : ZMod 12810187352747) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 12810187352747 - 1 = [2^1, 7^2, 47^1, 101^1, 27536591^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 47 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 101 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 27536591 := (Nat.prime_dvd_prime_iff_eq hq prime_27536591).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_25409026523137 : Nat.Prime 25409026523137 := by
  refine lucas_primality 25409026523137 (5 : ZMod 25409026523137) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 25409026523137 - 1 = [2^34, 3^1, 17^1, 29^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 29 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_48413 : Nat.Prime 48413 := by
  refine lucas_primality 48413 (2 : ZMod 48413) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 48413 - 1 = [2^2, 7^2, 13^1, 19^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_25991531462657 : Nat.Prime 25991531462657 := by
  refine lucas_primality 25991531462657 (3 : ZMod 25991531462657) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 25991531462657 - 1 = [2^29, 48413^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 48413 := (Nat.prime_dvd_prime_iff_eq hq prime_48413).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_76861124116481 : Nat.Prime 76861124116481 := by
  refine lucas_primality 76861124116481 (7 : ZMod 76861124116481) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 76861124116481 - 1 = [2^29, 5^1, 11^1, 19^1, 137^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 137 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_30941 : Nat.Prime 30941 := by
  refine lucas_primality 30941 (2 : ZMod 30941) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 30941 - 1 = [2^2, 5^1, 7^1, 13^1, 17^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_38222840587 : Nat.Prime 38222840587 := by
  refine lucas_primality 38222840587 (3 : ZMod 38222840587) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 38222840587 - 1 = [2^1, 3^1, 7^1, 67^1, 439^1, 30941^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 67 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 439 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 30941 := (Nat.prime_dvd_prime_iff_eq hq prime_30941).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_133627050692153 : Nat.Prime 133627050692153 := by
  refine lucas_primality 133627050692153 (3 : ZMod 133627050692153) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 133627050692153 - 1 = [2^3, 19^1, 23^1, 38222840587^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 38222840587 := (Nat.prime_dvd_prime_iff_eq hq prime_38222840587).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_151413703311361 : Nat.Prime 151413703311361 := by
  refine lucas_primality 151413703311361 (33 : ZMod 151413703311361) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 151413703311361 - 1 = [2^30, 3^1, 5^1, 7^1, 17^1, 79^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 79 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_640126220763137 : Nat.Prime 640126220763137 := by
  refine lucas_primality 640126220763137 (3 : ZMod 640126220763137) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 640126220763137 - 1 = [2^32, 103^1, 1447^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 103 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1447 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_2405286912458753 : Nat.Prime 2405286912458753 := by
  refine lucas_primality 2405286912458753 (3 : ZMod 2405286912458753) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 2405286912458753 - 1 = [2^31, 7^1, 53^1, 3019^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 53 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3019 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_274069 : Nat.Prime 274069 := by
  refine lucas_primality 274069 (2 : ZMod 274069) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 274069 - 1 = [2^2, 3^2, 23^1, 331^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 331 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_9318347 : Nat.Prime 9318347 := by
  refine lucas_primality 9318347 (2 : ZMod 9318347) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 9318347 - 1 = [2^1, 17^1, 274069^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 274069 := (Nat.prime_dvd_prime_iff_eq hq prime_274069).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_1766730974551267606529 : Nat.Prime 1766730974551267606529 := by
  refine lucas_primality 1766730974551267606529 (11 : ZMod 1766730974551267606529) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 1766730974551267606529 - 1 = [2^36, 31^1, 89^1, 9318347^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 89 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 9318347 := (Nat.prime_dvd_prime_iff_eq hq prime_9318347).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_22433 : Nat.Prime 22433 := by
  refine lucas_primality 22433 (3 : ZMod 22433) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 22433 - 1 = [2^5, 701^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 701 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_314063 : Nat.Prime 314063 := by
  refine lucas_primality 314063 (5 : ZMod 314063) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 314063 - 1 = [2^1, 7^1, 22433^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 22433 := (Nat.prime_dvd_prime_iff_eq hq prime_22433).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_628127 : Nat.Prime 628127 := by
  refine lucas_primality 628127 (5 : ZMod 628127) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 628127 - 1 = [2^1, 314063^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 314063 := (Nat.prime_dvd_prime_iff_eq hq prime_314063).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_5736551 : Nat.Prime 5736551 := by
  refine lucas_primality 5736551 (7 : ZMod 5736551) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 5736551 - 1 = [2^1, 5^2, 31^1, 3701^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3701 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_1009632977 : Nat.Prime 1009632977 := by
  refine lucas_primality 1009632977 (3 : ZMod 1009632977) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 1009632977 - 1 = [2^4, 11^1, 5736551^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5736551 := (Nat.prime_dvd_prime_iff_eq hq prime_5736551).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_3352259691276003929527 : Nat.Prime 3352259691276003929527 := by
  refine lucas_primality 3352259691276003929527 (3 : ZMod 3352259691276003929527) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 3352259691276003929527 - 1 = [2^1, 3^1, 7^1, 127^1, 991^1, 628127^1, 1009632977^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 991 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 628127 := (Nat.prime_dvd_prime_iff_eq hq prime_628127).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1009632977 := (Nat.prime_dvd_prime_iff_eq hq prime_1009632977).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_536699 : Nat.Prime 536699 := by
  refine lucas_primality 536699 (2 : ZMod 536699) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 536699 - 1 = [2^1, 149^1, 1801^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 149 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1801 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_140091319777 : Nat.Prime 140091319777 := by
  refine lucas_primality 140091319777 (10 : ZMod 140091319777) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 140091319777 - 1 = [2^5, 3^1, 2719^1, 536699^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 2719 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 536699 := (Nat.prime_dvd_prime_iff_eq hq prime_536699).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_46931635677864055013377 : Nat.Prime 46931635677864055013377 := by
  refine lucas_primality 46931635677864055013377 (5 : ZMod 46931635677864055013377) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 46931635677864055013377 - 1 = [2^33, 3^1, 13^1, 140091319777^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 140091319777 := (Nat.prime_dvd_prime_iff_eq hq prime_140091319777).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_2252461 : Nat.Prime 2252461 := by
  refine lucas_primality 2252461 (2 : ZMod 2252461) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 2252461 - 1 = [2^2, 3^1, 5^1, 7^1, 31^1, 173^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 173 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_15377 : Nat.Prime 15377 := by
  refine lucas_primality 15377 (3 : ZMod 15377) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 15377 - 1 = [2^4, 31^2].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_57223 : Nat.Prime 57223 := by
  refine lucas_primality 57223 (3 : ZMod 57223) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 57223 - 1 = [2^1, 3^2, 11^1, 17^2].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_52795084261 : Nat.Prime 52795084261 := by
  refine lucas_primality 52795084261 (11 : ZMod 52795084261) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 52795084261 - 1 = [2^2, 3^1, 5^1, 15377^1, 57223^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 15377 := (Nat.prime_dvd_prime_iff_eq hq prime_15377).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 57223 := (Nat.prime_dvd_prime_iff_eq hq prime_57223).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_295319 : Nat.Prime 295319 := by
  refine lucas_primality 295319 (13 : ZMod 295319) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 295319 - 1 = [2^1, 149^1, 991^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 149 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 991 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_1045429261 : Nat.Prime 1045429261 := by
  refine lucas_primality 1045429261 (6 : ZMod 1045429261) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 1045429261 - 1 = [2^2, 3^1, 5^1, 59^1, 295319^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 295319 := (Nat.prime_dvd_prime_iff_eq hq prime_295319).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

private theorem prime_64658705994591851009055774868504577 : Nat.Prime 64658705994591851009055774868504577 := by
  refine lucas_primality 64658705994591851009055774868504577 (3 : ZMod 64658705994591851009055774868504577) (by reduce_mod_char) (fun q hq hd => ?_)
  have fact : 64658705994591851009055774868504577 - 1 = [2^24, 31^1, 2252461^1, 52795084261^1, 1045429261^1].prod := by norm_num
  rw [fact] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 2252461 := (Nat.prime_dvd_prime_iff_eq hq prime_2252461).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 52795084261 := (Nat.prime_dvd_prime_iff_eq hq prime_52795084261).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide
  · have h : q = 1045429261 := (Nat.prime_dvd_prime_iff_eq hq prime_1045429261).mp (hq.dvd_of_dvd_pow hqx)
    subst h
    reduce_mod_char
    decide

theorem exclude_21 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 4485296422913 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g4485296422913 : 4485296422913 ∈ P := S2 4485296422913 prime_4485296422913 (by norm_num) (hnz (by norm_num)) seed
  have g10487 : 10487 ∈ P := S1 10487 prime_10487 (by norm_num) (hnz (by norm_num)) 4485296422913 g4485296422913 (by norm_num)
  have g81281 : 81281 ∈ P := S1 81281 prime_81281 (by norm_num) (hnz (by norm_num)) 4485296422913 g4485296422913 (by norm_num)
  exact (by norm_num : 10487 ≠ 81281) (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 10487 g10487 81281 g81281 (by norm_num) (by norm_num))

theorem exclude_22 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 64658705994591851009055774868504577 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g64658705994591851009055774868504577 : 64658705994591851009055774868504577 ∈ P := S2 64658705994591851009055774868504577 prime_64658705994591851009055774868504577 (by norm_num) (hnz (by norm_num)) seed
  have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 64658705994591851009055774868504577 g64658705994591851009055774868504577 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
  have g16149761 : 16149761 ∈ P := S1 16149761 prime_16149761 (by norm_num) (hnz (by norm_num)) 64658705994591851009055774868504577 g64658705994591851009055774868504577 (by norm_num)
  have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 16149761 g16149761 (by norm_num)
  exact (by norm_num : 19 ≠ 89) (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 89 g89 (by norm_num) (by norm_num))

theorem exclude_23 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 167772161 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g167772161 : 167772161 ∈ P := S2 167772161 prime_167772161 (by norm_num) (hnz (by norm_num)) seed
  have g27962027 : 27962027 ∈ P := S1 27962027 prime_27962027 (by norm_num) (hnz (by norm_num)) 167772161 g167772161 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 27962027 g27962027 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have g7541 : 7541 ∈ P := S1 7541 (by norm_num) (by norm_num) (hnz (by norm_num)) 27962027 g27962027 (by norm_num)
  have g419 : 419 ∈ P := S1 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 7541 g7541 (by norm_num)
  exact (by norm_num : 13 ≠ 419) (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 419 g419 (by norm_num) (by norm_num))

theorem exclude_25 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 25991531462657 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g25991531462657 : 25991531462657 ∈ P := S2 25991531462657 prime_25991531462657 (by norm_num) (hnz (by norm_num)) seed
  have g26114321 : 26114321 ∈ P := S1 26114321 prime_26114321 (by norm_num) (hnz (by norm_num)) 25991531462657 g25991531462657 (by norm_num)
  have g165883 : 165883 ∈ P := S1 165883 prime_165883 (by norm_num) (hnz (by norm_num)) 25991531462657 g25991531462657 (by norm_num)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 165883 g165883 (by norm_num)
  exact (by norm_num : 26114321 ≠ 113) (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 26114321 g26114321 113 g113 (by norm_num) (by norm_num))

theorem exclude_26 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 76861124116481 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g76861124116481 : 76861124116481 ∈ P := S2 76861124116481 prime_76861124116481 (by norm_num) (hnz (by norm_num)) seed
  have g12810187352747 : 12810187352747 ∈ P := S1 12810187352747 prime_12810187352747 (by norm_num) (hnz (by norm_num)) 76861124116481 g76861124116481 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 12810187352747 g12810187352747 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have g28851773317 : 28851773317 ∈ P := S1 28851773317 prime_28851773317 (by norm_num) (hnz (by norm_num)) 12810187352747 g12810187352747 (by norm_num)
  have g14425886659 : 14425886659 ∈ P := S1 14425886659 prime_14425886659 (by norm_num) (hnz (by norm_num)) 28851773317 g28851773317 (by norm_num)
  exact (by norm_num : 19 ≠ 14425886659) (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 14425886659 g14425886659 (by norm_num) (by norm_num))

theorem exclude_27 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 151413703311361 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g151413703311361 : 151413703311361 ∈ P := S2 151413703311361 prime_151413703311361 (by norm_num) (hnz (by norm_num)) seed
  have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 151413703311361 g151413703311361 (by norm_num)
  have g1685033089 : 1685033089 ∈ P := S1 1685033089 prime_1685033089 (by norm_num) (hnz (by norm_num)) 151413703311361 g151413703311361 (by norm_num)
  exact (by norm_num : 179 ≠ 1685033089) (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 1685033089 g1685033089 (by norm_num) (by norm_num))

theorem exclude_28 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 1766730974551267606529 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g1766730974551267606529 : 1766730974551267606529 ∈ P := S2 1766730974551267606529 prime_1766730974551267606529 (by norm_num) (hnz (by norm_num)) seed
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 1766730974551267606529 g1766730974551267606529 (by norm_num)
  exact (by norm_num : 1766730974551267606529 ≠ 139) (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1766730974551267606529 g1766730974551267606529 139 g139 (by norm_num) (by norm_num))

theorem exclude_29 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 2405286912458753 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g2405286912458753 : 2405286912458753 ∈ P := S2 2405286912458753 prime_2405286912458753 (by norm_num) (hnz (by norm_num)) seed
  have g133627050692153 : 133627050692153 ∈ P := S1 133627050692153 prime_133627050692153 (by norm_num) (hnz (by norm_num)) 2405286912458753 g2405286912458753 (by norm_num)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 133627050692153 g133627050692153 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

theorem exclude_30 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 640126220763137 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g640126220763137 : 640126220763137 ∈ P := S2 640126220763137 prime_640126220763137 (by norm_num) (hnz (by norm_num)) seed
  have g3972019 : 3972019 ∈ P := S1 3972019 prime_3972019 (by norm_num) (hnz (by norm_num)) 640126220763137 g640126220763137 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 640126220763137 g640126220763137 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact (by norm_num : 3972019 ≠ 19) (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3972019 g3972019 19 g19 (by norm_num) (by norm_num))

theorem exclude_31 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 46931635677864055013377 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g46931635677864055013377 : 46931635677864055013377 ∈ P := S2 46931635677864055013377 prime_46931635677864055013377 (by norm_num) (hnz (by norm_num)) seed
  have g3352259691276003929527 : 3352259691276003929527 ∈ P := S1 3352259691276003929527 prime_3352259691276003929527 (by norm_num) (hnz (by norm_num)) 46931635677864055013377 g46931635677864055013377 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 3352259691276003929527 g3352259691276003929527 (by norm_num)
  exact (by norm_num : 46931635677864055013377 ≠ 41) (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 46931635677864055013377 g46931635677864055013377 41 g41 (by norm_num) (by norm_num))

theorem exclude_32 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (seed : 25409026523137 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^e → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have eq := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd)
    simpa [eq]
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, _, _, S6, _, _⟩ := facts hP hK E
  have g25409026523137 : 25409026523137 ∈ P := S2 25409026523137 prime_25409026523137 (by norm_num) (hnz (by norm_num)) seed
  have g12704513261569 : 12704513261569 ∈ P := S1 12704513261569 prime_12704513261569 (by norm_num) (hnz (by norm_num)) 25409026523137 g25409026523137 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 12704513261569 g12704513261569 (by norm_num)
  have g167 : 167 ∈ P := S1 167 (by norm_num) (by norm_num) (hnz (by norm_num)) 12704513261569 g12704513261569 (by norm_num)
  exact (by norm_num : 13 ≠ 167) (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 167 g167 (by norm_num) (by norm_num))

private theorem odd_multiple {d m : ℕ} (h : m % (2*d) = d) :
    2^d+1 ∣ 2^m+1 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = d*(2*t+1) := ⟨m/(2*d), by
    have hdiv := Nat.div_add_mod m (2*d)
    rw [h] at hdiv
    nlinarith [hdiv]⟩
  simpa [← pow_mul] using (show Odd (2*t+1) from ⟨t,rfl⟩).nat_add_dvd_pow_add_pow (2^d) 1

private lemma iter_sq_mod (p k : ℕ) :
    (fun r => r ^ 2 % p)^[k] (2 % p) = 2 ^ (2 ^ k) % p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← Nat.pow_mod, ← pow_mul, ← pow_succ]

private lemma dvd_of_iter (p n : ℕ)
    (h : (fun r => r ^ 2 % p)^[n] (2 % p) + 1 = p) :
    p ∣ 2 ^ (2 ^ n) + 1 := by
  rw [iter_sq_mod] at h
  have split := Nat.div_add_mod (2 ^ (2 ^ n)) p
  refine ⟨2 ^ (2 ^ n) / p + 1, ?_⟩
  rw [mul_add, mul_one]
  omega

theorem excluded_levels {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p) :
    ∀ level ∈ ({21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ), m % (2 * 2^level) ≠ 2^level := by
  intro level mem h
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply exclude_21 hP E
    have divisor : 4485296422913 ∣ 2 ^ (2^21) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_22 hP E
    have divisor : 64658705994591851009055774868504577 ∣ 2 ^ (2^22) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_23 hP E
    have divisor : 167772161 ∣ 2 ^ (2^23) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_25 hP E
    have divisor : 25991531462657 ∣ 2 ^ (2^25) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_26 hP E
    have divisor : 76861124116481 ∣ 2 ^ (2^26) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_27 hP E
    have divisor : 151413703311361 ∣ 2 ^ (2^27) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_28 hP E
    have divisor : 1766730974551267606529 ∣ 2 ^ (2^28) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_29 hP E
    have divisor : 2405286912458753 ∣ 2 ^ (2^29) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_30 hP E
    have divisor : 640126220763137 ∣ 2 ^ (2^30) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_31 hP E
    have divisor : 46931635677864055013377 ∣ 2 ^ (2^31) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)
  · apply exclude_32 hP E
    have divisor : 25409026523137 ∣ 2 ^ (2^32) + 1 :=
      dvd_of_iter _ _ (by decide +kernel)
    exact divisor.trans (odd_multiple h)

end UnitaryFermatLevels

def H1 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 → padicValNat 2 n % 2^21 = 2^20 → padicValNat 2 n ≤ A

def H2 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 → padicValNat 2 n % 2^25 = 2^24 → padicValNat 2 n ≤ A

def H3 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 → 2^33 ∣ padicValNat 2 n → padicValNat 2 n ≤ A

private theorem double_zero {m d : ℕ} (hm : m % d = 0)
    (hn : m % (2*d) ≠ d) : m % (2*d) = 0 := by
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
  have remainder : m % (2*d) = d * (t % 2) := by
    rw [ht, Nat.mul_comm 2 d, Nat.mul_mod_mul_left]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · simpa [h] using remainder
  · exact (hn (by simpa [h] using remainder)).elim

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he hd => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have simple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have prime := Nat.prime_of_mem_primeFactors hr
    have positive := prime.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have upper : ¬ 2 ≤ n.factorization r := fun htwo =>
      hr3 ((hiff r).mp ⟨prime, hr2, (prime.pow_dvd_iff_le_factorization hn0).mpr htwo⟩)
    omega
  have three : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  obtain ⟨hP, balance⟩ :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one h three (by decide) simple
  rw [he, Nat.factorization_def n Nat.prime_two] at balance
  have blocked := UnitaryFermatLevels.excluded_levels hP balance
  let m := padicValNat 2 n
  change 1048576 ∣ m at hd
  have c20 : m % 1048576 = 0 := Nat.mod_eq_zero_of_dvd hd
  by_cases l20 : m % 2097152 = 1048576
  · have bound := h1 n h hiff he (by change m % 2097152 = 1048576; exact l20)
    exact bound.trans (le_max_left _ _)
  have c21 : m % 2097152 = 0 := double_zero c20 l20
  have c22 : m % 4194304 = 0 := by
    apply double_zero c21
    simpa using blocked 21 (by decide)
  have c23 : m % 8388608 = 0 := by
    apply double_zero c22
    simpa using blocked 22 (by decide)
  have c24 : m % 16777216 = 0 := by
    apply double_zero c23
    simpa using blocked 23 (by decide)
  by_cases l24 : m % 33554432 = 16777216
  · have bound := h2 n h hiff he (by change m % 33554432 = 16777216; exact l24)
    exact bound.trans ((le_max_left _ _).trans (le_max_right _ _))
  have c25 : m % 33554432 = 0 := double_zero c24 l24
  have c26 : m % 67108864 = 0 := by
    apply double_zero c25
    simpa using blocked 25 (by decide)
  have c27 : m % 134217728 = 0 := by
    apply double_zero c26
    simpa using blocked 26 (by decide)
  have c28 : m % 268435456 = 0 := by
    apply double_zero c27
    simpa using blocked 27 (by decide)
  have c29 : m % 536870912 = 0 := by
    apply double_zero c28
    simpa using blocked 28 (by decide)
  have c30 : m % 1073741824 = 0 := by
    apply double_zero c29
    simpa using blocked 29 (by decide)
  have c31 : m % 2147483648 = 0 := by
    apply double_zero c30
    simpa using blocked 30 (by decide)
  have c32 : m % 4294967296 = 0 := by
    apply double_zero c31
    simpa using blocked 31 (by decide)
  have c33 : m % 8589934592 = 0 := by
    apply double_zero c32
    simpa using blocked 32 (by decide)
  have bound := h3 n h hiff he (Nat.dvd_of_mod_eq_zero c33)
  exact bound.trans ((le_max_right _ _).trans (le_max_right _ _))
end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H3_R1
