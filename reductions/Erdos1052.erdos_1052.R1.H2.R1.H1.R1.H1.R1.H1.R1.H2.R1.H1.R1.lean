import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1

-- From 3^7 + 1 = 4 * 547 the simple primes include 547, 137 and 23.
-- If 9 divides a, the factor 19 of 2^9 + 1 also forces 5. Remove these
-- chains. The residual prime set Q determines a by its two-adic weight,
-- while LTE gives its exact three-adic weight (4, 3, or 1).
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

def H1 : Prop :=
  ∃ B : ℕ, ∀ Q : Finset ℕ,
    (∀ p ∈ Q, p.Prime ∧ p ∉ ({2, 3, 23, 137, 547} : Finset ℕ)) →
    let b := ∑ p ∈ Q, (p + 1).factorization 2
    Odd (b + 7) → (b + 7).factorization 3 = 0 →
    (∑ p ∈ Q, (p + 1).factorization 3) = 4 →
    (2 ^ (b + 7) + 1) * (∏ p ∈ Q, (p + 1)) = 2 ^ b * 243 * (∏ p ∈ Q, p) →
    b + 7 ≤ B

def H2 : Prop :=
  ∃ B : ℕ, ∀ Q : Finset ℕ,
    (∀ p ∈ Q, p.Prime ∧ p ∉ ({2, 3, 23, 137, 547} : Finset ℕ)) →
    let b := ∑ p ∈ Q, (p + 1).factorization 2
    Odd (b + 7) → (b + 7).factorization 3 = 1 →
    (∑ p ∈ Q, (p + 1).factorization 3) = 3 →
    (2 ^ (b + 7) + 1) * (∏ p ∈ Q, (p + 1)) = 2 ^ b * 243 * (∏ p ∈ Q, p) →
    b + 7 ≤ B

def H3 : Prop :=
  ∃ B : ℕ, ∀ Q : Finset ℕ,
    (∀ p ∈ Q, p.Prime ∧ p ∉ ({2, 3, 5, 19, 23, 137, 547} : Finset ℕ)) →
    let b := ∑ p ∈ Q, (p + 1).factorization 2
    Odd (b + 10) → (b + 10).factorization 3 = 2 →
    (∑ p ∈ Q, (p + 1).factorization 3) = 1 →
    (2 ^ (b + 10) + 1) * (∏ p ∈ Q, (p + 1)) = 2 ^ b * 1539 * (∏ p ∈ Q, p) →
    b + 10 ≤ B

theorem residual_weights {a c K : ℕ} {Q : Finset ℕ}
    (ha : 0 < a) (ho : Odd a)
    (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ p ≠ 3) (hK : 0 < K) (hKo : ¬ 2 ∣ K)
    (E : 2^c * (2^a+1) * (∏ p ∈ Q, (p+1)) = 2^a * K * (∏ p ∈ Q, p)) :
    (∑ p ∈ Q, (p+1).factorization 2) + c = a ∧
    1 + a.factorization 3 + (∑ p ∈ Q, (p+1).factorization 3) = K.factorization 3 := by
  have V : 0 < ∏ p ∈ Q, p := Finset.prod_pos (fun p hp => (hQ p hp).1.pos)
  have U : 0 < ∏ p ∈ Q, (p+1) := Finset.prod_pos (fun p _ => Nat.succ_pos p)
  have vf (r : ℕ) (hr : r.Prime) (hn : ∀ p ∈ Q, p ≠ r) :
      (∏ p ∈ Q, p).factorization r = 0 := by
    rw [Nat.factorization_prod_apply (fun p hp => (hQ p hp).1.ne_zero)]
    apply Finset.sum_eq_zero
    intro p hp
    apply Nat.factorization_eq_zero_of_not_dvd
    exact fun hd => hn p hp ((Nat.prime_dvd_prime_iff_eq hr (hQ p hp).1).mp hd).symm
  have calcWeight (r : ℕ) :
      ((2:ℕ)^c).factorization r + ((2:ℕ)^a+1).factorization r + (∑ p ∈ Q, (p+1).factorization r) =
      ((2:ℕ)^a).factorization r + K.factorization r + (∏ p ∈ Q, p).factorization r := by
    have eq := congrArg (fun x : ℕ => x.factorization r) E
    change (2^c * (2^a+1) * (∏ p ∈ Q, (p+1))).factorization r = (2^a * K * (∏ p ∈ Q, p)).factorization r at eq
    rw [Nat.factorization_mul (a := 2^c * (2^a+1)) (by positivity) U.ne',
        Nat.factorization_mul (a := 2^a * K) (by positivity) V.ne',
        Nat.factorization_mul (a := 2^c) (b := 2^a+1) (by positivity) (by positivity),
        Nat.factorization_mul (a := 2^a) (b := K) (by positivity) hK.ne'] at eq
    simpa only [Finsupp.add_apply, Nat.factorization_prod_apply (g := fun p : ℕ => p+1)
      (fun p _ => Nat.succ_ne_zero p)] using eq
  have e2 : ¬ 2 ∣ 2^a+1 := by
    have hd : 2 ∣ (2:ℕ)^a := dvd_pow_self 2 ha.ne'
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e3 : ((2:ℕ)^a+1).factorization 3 = 1 + a.factorization 3 := by
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three]
    simpa only [one_pow, show (2:ℕ)+1 = 3 by decide, padicValNat_self] using
      (padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide) (by decide) (by decide) ho)
  have h2 := calcWeight 2
  have h3 := calcWeight 3
  rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd e2, Nat.factorization_eq_zero_of_not_dvd hKo,
    vf 2 Nat.prime_two (fun p hp => (hQ p hp).2.1)] at h2
  have z (i : ℕ) : ((2:ℕ)^i).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  rw [z, z, e3,
    vf 3 Nat.prime_three (fun p hp => (hQ p hp).2.2)] at h3
  exact ⟨by omega, by omega⟩

theorem strip_chains {a c K D : ℕ} {P S : Finset ℕ} (hS : S ⊆ P)
    (hL : (1 + 3^7) * (∏ p ∈ S, (p+1)) = 2^c * D * 2)
    (hR : 3^7 * (∏ p ∈ S, p) = K * D) (hD : 0 < D)
    (E : (2^a+1) * (1+3^7) * (∏ p ∈ P, (p+1)) = 2^(a+1) * 3^7 * (∏ p ∈ P, p)) :
    2^c * (2^a+1) * (∏ p ∈ P \ S, (p+1)) = 2^a * K * (∏ p ∈ P \ S, p) := by
  rw [← Finset.prod_sdiff (f := fun p : ℕ => p+1) hS,
      ← Finset.prod_sdiff (f := fun p : ℕ => p) hS, pow_succ (2:ℕ) a] at E
  apply Nat.eq_of_mul_eq_mul_right (show 0 < D * 2 by positivity)
  calc
    _ = (2^a+1) * ((1+3^7) * (∏ p ∈ S, (p+1))) * (∏ p ∈ P \ S, (p+1)) := by rw [hL]; ring
    _ = 2^a * 2 * (3^7 * (∏ p ∈ S, p)) * (∏ p ∈ P \ S, p) := by linear_combination E
    _ = _ := by rw [hR]; ring

theorem odd_multiple_mod {a d : ℕ} (hd : 0 < d) (ho : Odd a) (h : d ∣ a) :
    a % (2*d) = d := by
  obtain ⟨t, rfl⟩ := h
  rcases Nat.even_or_odd' t with ⟨j, rfl | rfl⟩
  · rw [show d * (2*j) = 2*(d*j) by ring] at ho
    have := Nat.odd_iff.mp ho
    omega
  · rw [show d * (2*j+1) = d + (2*d)*j by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

theorem residual_bound {a c K v e B : ℕ} {Q : Finset ℕ}
    (ha : 0 < a) (ho : Odd a) (hv : a.factorization 3 = v)
    (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ p ≠ 3) (hK : 0 < K) (hKo : ¬ 2 ∣ K)
    (hk₃ : K.factorization 3 = 1 + v + e)
    (E : 2^c * (2^a+1) * (∏ p ∈ Q, (p+1)) = 2^a * K * (∏ p ∈ Q, p))
    (h : let b := ∑ p ∈ Q, (p+1).factorization 2
         Odd (b+c) → (b+c).factorization 3 = v → (∑ p ∈ Q, (p+1).factorization 3) = e →
         (2^(b+c)+1) * (∏ p ∈ Q, (p+1)) = 2^b * K * (∏ p ∈ Q, p) → b+c ≤ B) :
    a ≤ B := by
  obtain ⟨w₂, w₃⟩ := residual_weights ha ho hQ hK hKo E
  have budget : (∑ p ∈ Q, (p+1).factorization 3) = e := by omega
  let b := ∑ p ∈ Q, (p+1).factorization 2
  change b+c = a at w₂
  rw [← w₂] at E ho hv ⊢
  apply h ho hv budget
  rw [pow_add] at E ⊢
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2:ℕ)^c by positivity)
  linear_combination E

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨B₁, h₁⟩ ⟨B₂, h₂⟩ ⟨B₃, h₃⟩
  refine ⟨max B₁ (max B₂ B₃), fun n h hiff he hlo hodd hs _ _ => ?_⟩
  let a := padicValNat 2 n
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ))
  change a ≤ _
  have hn0 := h.2.ne'
  have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun hle =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr hle⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨hP, E⟩ := kernel_balance_one h (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩)
    (by norm_num) hsimple
  change ∀ p ∈ P, p.Prime ∧ p ≠ 2 at hP
  rw [he, Nat.factorization_def n Nat.prime_two] at E
  change (2^a+1) * (1+3^7) * (∏ p ∈ P, (p+1)) = 2^(a+1) * 3^7 * (∏ p ∈ P, p) at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^7 → c ∈ ({3} : Finset ℕ) := prime_dvd_prime_pow (by norm_num)
  obtain ⟨nextPrime, rootPrime, _, _, _, _, fixedPrime, _⟩ := facts hP hK E
  have g547 : 547 ∈ P := fixedPrime 547 (by norm_num) (by decide) (by decide) (by decide)
  have g137 : 137 ∈ P := nextPrime 137 (by norm_num) (by decide) (by decide) 547 g547 (by decide)
  have g23 : 23 ∈ P := nextPrime 23 (by norm_num) (by decide) (by decide) 137 g137 (by decide)
  have good {S : Finset ℕ} {p : ℕ} (hp : p ∈ P \ S) : p.Prime ∧ p ≠ 2 ∧ p ≠ 3 := by
    have hpP := (Finset.mem_sdiff.mp hp).1
    exact ⟨(hP p hpP).1, (hP p hpP).2, by simpa using (Finset.mem_filter.mp hpP).2⟩
  change 262 ≤ a at hlo
  change a % 2 = 1 at hodd
  have ho : Odd a := Nat.odd_iff.mpr hodd
  have h27 := hs 27 (by decide) (by decide) (by decide)
  change a % 54 ≠ 27 at h27
  have hvlt : a.factorization 3 < 3 := by
    by_contra! hle
    have hd := (Nat.prime_three.pow_dvd_iff_le_factorization (by omega : a ≠ 0)).mpr hle
    change 27 ∣ a at hd
    exact h27 (odd_multiple_mod (by decide) ho hd)
  have fixed : ({23, 137, 547} : Finset ℕ) ⊆ P := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have standard := strip_chains (c := 7) (K := 243) (D := 15512373) fixed
    (by decide) (by decide) (by decide) E
  rcases (show a.factorization 3 = 0 ∨ a.factorization 3 = 1 ∨ a.factorization 3 = 2 by omega) with hv | hv | hv
  · refine le_trans ?_ (le_max_left _ _)
    apply residual_bound (e := 4) (by omega) ho hv (fun _ hp => good hp)
      (by decide) (by decide) (Nat.factorization_pow_self (n := 5) Nat.prime_three) standard
    apply h₁
    intro p hp
    obtain ⟨hpr, hn2, hn3⟩ := good hp
    exact ⟨hpr, by simpa [hn2, hn3] using (Finset.mem_sdiff.mp hp).2⟩
  · refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    apply residual_bound (e := 3) (by omega) ho hv (fun _ hp => good hp)
      (by decide) (by decide) (Nat.factorization_pow_self (n := 5) Nat.prime_three) standard
    apply h₂
    intro p hp
    obtain ⟨hpr, hn2, hn3⟩ := good hp
    exact ⟨hpr, by simpa [hn2, hn3] using (Finset.mem_sdiff.mp hp).2⟩
  · have hd := (Nat.prime_three.pow_dvd_iff_le_factorization (by omega : a ≠ 0)).mpr hv.ge
    change 9 ∣ a at hd
    have h19 : 19 ∣ 2^a+1 := (by decide : 19 ∣ 2^9+1).trans
      (two_pow_add_one_dvd_of_odd_mul (odd_multiple_mod (by decide) ho hd))
    have g19 := rootPrime 19 (by norm_num) (by decide) (by decide) h19
    have g5 := nextPrime 5 (by norm_num) (by decide) (by decide) 19 g19 (by decide)
    have full : ({5, 19, 23, 137, 547} : Finset ℕ) ⊆ P := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
    have expanded := strip_chains (c := 10) (K := 1539) (D := 232685595) full
      (by decide) (by decide) (by decide) E
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    apply residual_bound (e := 1) (by omega) ho hv (fun _ hp => good hp)
      (by decide) (by decide) (by
        rw [show (1539:ℕ) = 3^4 * 19 by decide, Nat.factorization_mul (by decide) (by decide),
          Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 19)]
      ) expanded
    apply h₃
    intro p hp
    obtain ⟨hpr, hn2, hn3⟩ := good hp
    exact ⟨hpr, by simpa [hn2, hn3] using (Finset.mem_sdiff.mp hp).2⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1
