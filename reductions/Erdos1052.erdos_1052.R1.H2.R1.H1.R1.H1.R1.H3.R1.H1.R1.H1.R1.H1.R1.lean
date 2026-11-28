import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
The ternary seed forces 5 when e is 2 mod 4. Any prime r that is 4 mod 5 in either
seed would force a second source of 5 through r+1. Euler’s criterion and quadratic
reciprocity give two infinite families of excluded progressions. Dirichlet’s theorem
shows that for every fixed odd M and every cutoff L, the first family excludes some
e>L coprime to M. These exclusions are not limited to multiples of finitely many
fixed odd divisors.

The two remaining bounds concern the power of two and the odd part of the binary
exponent a among candidates surviving the old finite and the new infinite sieves.
-/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H1
-- Credit: @AlfredMelson

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

theorem avoid_four {n r : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hsimple : ∀ p, p.Prime ∧ p≠2 ∧ p^2 ∣ n ↔ p=3)
    (he : n.factorization 3 % 4=2) (hr : r.Prime) (hr5 : r%5=4) :
    (¬r ∣ 1+3^(n.factorization 3)) ∧ (¬r ∣ 1+2^(padicValNat 2 n)) := by
  let e := n.factorization 3
  have h3n := (dvd_pow_self 3 two_ne_zero).trans ((hsimple 3).mpr rfl).2.2
  have h3mem := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),h3n,hn.2.ne'⟩
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hm h2 h3
    have hp := Nat.prime_of_mem_primeFactors hm
    have hpos := hp.factorization_pos_of_dvd hn.2.ne' (Nat.dvd_of_mem_primeFactors hm)
    by_contra hne
    have hd : r^2 ∣ n := (hp.pow_dvd_iff_le_factorization hn.2.ne').mpr (by omega)
    exact h3 ((hsimple r).mp ⟨hp,h2,hd⟩)
  obtain ⟨hP,E⟩ := kernel_balance_one hn h3mem (by decide) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  obtain ⟨_,s2,_,_,_,_,s7,s8⟩ := facts hP (prime_dvd_prime_pow (z:=3) (e:=e) (by decide)) E
  have hd5 : 5 ∣ 1+3^(n.factorization 3) :=
    (show 5 ∣ 1+3^2 by decide).trans (one_add_pow_dvd_of_odd_mul (e0:=2) he)
  have hblock := s8 5 (by decide) (by decide) (by decide) hd5
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ∉ ({3} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hsucc : 5 ∣ r+1 := by omega
  constructor
  · intro h
    exact hblock r (s7 r hr hr2 hr3 h) hsucc
  · intro h
    exact hblock r (s2 r hr hr2 hr3 (by simpa [add_comm] using h)) hsucc

theorem odd_multiple {r b k : ℕ} [Fact r.Prime] (hr : r%2=1)
    (hnr : legendreSym r b = -1) (hk : k % (r-1)=r/2) :
    r ∣ 1+b^k := by
  have hp := legendreSym.eq_pow r (b:ℤ)
  rw [hnr] at hp
  have hd : r ∣ 1+b^(r/2) := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast at hp ⊢
    rw [←hp]; simp
  exact hd.trans (one_add_pow_dvd_of_odd_mul (by rwa [show 2*(r/2) = r-1 by omega]))

theorem progression_sieves {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p≠2 ∧ p^2 ∣ n ↔ p=3)
    (he : n.factorization 3 % 4=2) :
    (∀ r : ℕ, r.Prime → r%120=29 → n.factorization 3 % (r-1) ≠ r/2) ∧
    (∀ r : ℕ, r.Prime → r%40=19 → padicValNat 2 n % (r-1) ≠ r/2) := by
  constructor
  · intro r hr hres hk
    let : Fact r.Prime := ⟨hr⟩
    have h4 : r%4=1 := by omega
    have h3 : (r:ℤ)%3=2 := by omega
    have hqr : legendreSym r 3 = -1 := by
      have qr := legendreSym.quadratic_reciprocity_one_mod_four (p:=r) (q:=3) h4 (by decide)
      norm_num1 at qr
      rw [←qr]
      rw [legendreSym.mod 3 (r:ℤ)]
      change legendreSym 3 ((r:ℤ)%3) = -1
      rw [h3, legendreSym.at_two (p:=3) (by decide)]
      norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
    exact (avoid_four hn hS he hr (by omega)).1 (odd_multiple (b:=3) (by omega) hqr hk)
  · intro r hr hres hk
    let : Fact r.Prime := ⟨hr⟩
    have hqr : legendreSym r 2 = -1 := by
      rw [legendreSym.at_two (by omega),ZMod.χ₈_nat_eq_if_mod_eight]
      simp [show r%2=1 by omega, show r%8=3 by omega]
    exact (avoid_four hn hS he hr (by omega)).2 (odd_multiple (b:=2) (by omega) hqr hk)
theorem rough_primes (M L : ℕ) (hM : Odd M) :
    ∃ r : ℕ, r.Prime ∧ L < r/2 ∧ r%120=29 ∧ (r/2).Coprime M := by
  let R := 30*M^2-1
  obtain ⟨k,hk⟩ := hM
  have hs : 30*M^2 = 120*(k^2+k)+30 := by rw [hk]; ring
  have hR : R%120=29 := by dsimp [R]; omega
  have hRM : M ∣ R+1 := by
    refine ⟨30*M, ?_⟩
    calc R+1 = 30*M^2 := by dsimp [R]; omega
         _ = M*(30*M) := by ring
  have hc120 : R.Coprime 120 := by
    change R.gcd 120 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec 120 R, hR]
    decide
  have hcM : R.Coprime M := by
    by_contra hc
    obtain ⟨q,hq,hr,hm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact hq.not_dvd_one ((Nat.dvd_add_iff_right hr).mpr (hm.trans hRM))
  obtain ⟨r,hL,hr,hcon⟩ := Nat.forall_exists_prime_gt_and_modEq (2*L+2)
    (q:=120*M) (a:=R) (by omega) (Nat.coprime_mul_iff_right.mpr ⟨hc120,hcM⟩)
  have hres : r%120=29 := Eq.trans (hcon.of_dvd (dvd_mul_right 120 M) : r%120 = R%120) hR
  have h1 : r+1 ≡ R+1 [MOD M] := (hcon.of_dvd (dvd_mul_left M 120)).add_right 1
  have hMr : M ∣ r+1 := Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hRM))
  refine ⟨r, hr, by omega, hres, ?_⟩
  by_contra hc
  obtain ⟨q,hq,hq2,hqM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hd : q ∣ 2*(r/2) := hq2.mul_left _
  have h2 : q ∣ 2 := (Nat.dvd_add_iff_right hd).mpr (by rw [show 2*(r/2)+2 = r+1 by omega]; exact hqM.trans hMr)
  have hqeq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
  subst q
  omega
/-- The ternary progression exclusions detect arbitrarily large e avoiding any fixed odd M. -/
theorem fresh_forbidden (M L : ℕ) (hM : Odd M) :
    ∃ e : ℕ, L < e ∧ e%4=2 ∧ e.Coprime M ∧
      ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
        (∀ p, p.Prime ∧ p≠2 ∧ p^2 ∣ n ↔ p=3) → n.factorization 3 ≠ e := by
  obtain ⟨r,hr,hl,hres,hc⟩ := rough_primes M L hM
  refine ⟨r/2,hl,by omega,hc,?_⟩
  intro n hn hS he
  have hf : n.factorization 3 % 4 = 2 := by omega
  exact (progression_sieves hn hS hf).1 r hr hres (by rw [he, Nat.mod_eq_of_lt (by omega)])

/-- Bound powers of two dividing a surviving binary exponent. -/
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ,
    let e := n.factorization 3
    let a := padicValNat 2 n
    Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < e →
    e % 4 = 2 →
    (∀ d ∈ ({502,503,508,509,512,514,521,523,524,526,538,541,542,547,548,554,556,557,562,563,566,569,571,586,587,593,596,599,601,604,607,613,614,617,619,622,626,628,631,634,641,643,647,652,653,659,661,662,668,673,674,677,683,691,692,694,698,701,706,709,716,718,719,724,727,733,734,739,743,746,751,757,758,761,766,769,772,773,778,787,788,794,796,797} : Finset ℕ),
      e % (2 * d) ≠ d) →
    (∀ d ∈ ({10,12,14,18,20,22,24,25,26,27,28,29,32,33,34,35,37,38,39,45,46,48,51,52,55,56,57,59,62,63,64,65,67,68,69,74,76,77,80,82,83,85,86,91,94,95,97,106,112,115,116,118,119,121,122,123,124,131,133,134,141,142,143,146,147,149,152,155,157} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ d ∈ ({31,40,41,43,44,47,49,53,58,61,71,73,79,88,89,92,93,101,103,104,107,109,113,127,128,129,136,137,139,148,151,159,161,163,164,166,167,172,173,174,176,178,179,181,183,184,187,188,191,193,194,197,199,200} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ d ∈ ({2,6,9,11,13,21,23,158,169,219,272,302,332,356,373} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ r : ℕ, r.Prime → r % 120 = 29 → e % (r-1) ≠ r/2) →
    (∀ r : ℕ, r.Prime → r % 40 = 19 → a % (r-1) ≠ r/2) →
    ∀ t : ℕ, 2^t ∣ a → 2^t ≤ B

/-- Bound the odd divisors of a surviving binary exponent. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ,
    let e := n.factorization 3
    let a := padicValNat 2 n
    Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < e →
    e % 4 = 2 →
    (∀ d ∈ ({502,503,508,509,512,514,521,523,524,526,538,541,542,547,548,554,556,557,562,563,566,569,571,586,587,593,596,599,601,604,607,613,614,617,619,622,626,628,631,634,641,643,647,652,653,659,661,662,668,673,674,677,683,691,692,694,698,701,706,709,716,718,719,724,727,733,734,739,743,746,751,757,758,761,766,769,772,773,778,787,788,794,796,797} : Finset ℕ),
      e % (2 * d) ≠ d) →
    (∀ d ∈ ({10,12,14,18,20,22,24,25,26,27,28,29,32,33,34,35,37,38,39,45,46,48,51,52,55,56,57,59,62,63,64,65,67,68,69,74,76,77,80,82,83,85,86,91,94,95,97,106,112,115,116,118,119,121,122,123,124,131,133,134,141,142,143,146,147,149,152,155,157} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ d ∈ ({31,40,41,43,44,47,49,53,58,61,71,73,79,88,89,92,93,101,103,104,107,109,113,127,128,129,136,137,139,148,151,159,161,163,164,166,167,172,173,174,176,178,179,181,183,184,187,188,191,193,194,197,199,200} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ d ∈ ({2,6,9,11,13,21,23,158,169,219,272,302,332,356,373} : Finset ℕ),
      a % (2 * d) ≠ d) →
    (∀ r : ℕ, r.Prime → r % 120 = 29 → e % (r-1) ≠ r/2) →
    (∀ r : ℕ, r.Prime → r % 40 = 19 → a % (r-1) ≠ r/2) →
    ∀ u : ℕ, Odd u → u ∣ a → u ≤ B

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1.H1 := by
  intro hp ho
  obtain ⟨B, hB⟩ := hp
  obtain ⟨C, hC⟩ := ho
  refine ⟨B*C, ?_⟩
  intro n hn hS heLarge he se s₁ s₂ s₃
  obtain ⟨hE,hA⟩ := progression_sieves hn hS he
  have hb := hB n hn hS heLarge he se s₁ s₂ s₃ hE hA
  have hc := hC n hn hS heLarge he se s₁ s₂ s₃ hE hA
  by_cases hz : padicValNat 2 n = 0
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨t,u,hu,heq⟩ := Nat.exists_eq_two_pow_mul_odd hz
  have htd : 2^t ∣ padicValNat 2 n := ⟨u, heq⟩
  have hud : u ∣ padicValNat 2 n := ⟨2^t, by rwa [mul_comm]⟩
  rw [heq]
  exact Nat.mul_le_mul (hb t htd) (hc u hu hud)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1
