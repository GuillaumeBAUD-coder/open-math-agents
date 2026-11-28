import FormalConjectures.ErdosProblems.«364»

-- Reduction Erdos364.erdos_364.R2 of Erdős Problem 364
-- Credit: @kmcooke22
-- The square-center descent reduces any triple with powerful square root
-- to a smaller triple, even without the upper neighbor once parity is known.
-- This leaves a nonsquare branch and a square branch with non-powerful root.
-- Both use the classical congruences also recorded in the first reduction.

namespace OMA.R_Erdos364_erdos_364_R2

theorem full_mul_iff_of_coprime {k a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) :
    k.Full (a * b) ↔ k.Full a ∧ k.Full b := by
  constructor
  · intro hf
    constructor
    · intro p hp
      obtain ⟨pp, hpa, _⟩ := Nat.mem_primeFactors.mp hp
      have hpb : ¬ p ∣ b := fun h ↦ pp.ne_one (Nat.eq_one_of_dvd_coprimes hab hpa h)
      have hc : (p ^ k).Coprime b := (pp.coprime_pow_of_not_dvd hpb).symm
      exact hc.dvd_mul_right.mp (hf p (Nat.mem_primeFactors.mpr
        ⟨pp, dvd_mul_of_dvd_left hpa _, mul_ne_zero ha hb⟩))
    · intro p hp
      obtain ⟨pp, hpb, _⟩ := Nat.mem_primeFactors.mp hp
      have hpa : ¬ p ∣ a := fun h ↦ pp.ne_one (Nat.eq_one_of_dvd_coprimes hab h hpb)
      have hc : (p ^ k).Coprime a := (pp.coprime_pow_of_not_dvd hpa).symm
      exact hc.dvd_mul_left.mp (hf p (Nat.mem_primeFactors.mpr
        ⟨pp, dvd_mul_of_dvd_right hpb _, mul_ne_zero ha hb⟩))
  · rintro ⟨hfa, hfb⟩ p hp
    obtain ⟨pp, hpab, _⟩ := Nat.mem_primeFactors.mp hp
    rcases pp.dvd_mul.mp hpab with hpa | hpb
    · exact dvd_mul_of_dvd_left (hfa p (Nat.mem_primeFactors.mpr ⟨pp, hpa, ha⟩)) _
    · exact dvd_mul_of_dvd_right (hfb p (Nat.mem_primeFactors.mpr ⟨pp, hpb, hb⟩)) _

theorem coprime_add_two_of_odd {a : ℕ} (ha : a % 2 = 1) : a.Coprime (a + 2) := by
  have h : Nat.Coprime 2 a := by
    by_contra hn
    obtain ⟨b, hb⟩ := Nat.prime_two.dvd_iff_not_coprime.mpr hn
    omega
  exact Nat.coprime_self_add_right.mpr h.symm

theorem middle_even_of_full_triple {a : ℕ}
    (ha : (2 : ℕ).Full a) (hc : (2 : ℕ).Full (a + 2)) :
    2 ∣ a + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra h
  have hmod : a % 4 = 2 ∨ (a + 2) % 4 = 2 := by omega
  rcases hmod with hmod | hmod
  · exact (Nat.not_full_of_prime_mod_prime_sq a 1 Nat.prime_two (by simpa using hmod)) ha
  · exact (Nat.not_full_of_prime_mod_prime_sq (a + 2) 1 Nat.prime_two
      (by simpa using hmod)) hc

theorem four_dvd_middle_of_full_triple {a : ℕ}
    (ha : (2 : ℕ).Full a) (hb : (2 : ℕ).Full (a + 1)) (hc : (2 : ℕ).Full (a + 2)) :
    4 ∣ a + 1 := by
  have he := Nat.dvd_iff_mod_eq_zero.mp (middle_even_of_full_triple ha hc)
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hn
  have hm : (a + 1) % 4 = 2 := by omega
  exact (Nat.not_full_of_prime_mod_prime_sq (a + 1) 1 Nat.prime_two
    (by simpa using hm)) hb

theorem powerful_pow {b k : ℕ} (hk : 2 ≤ k) : Nat.Powerful (b ^ k) := by
  intro p hp
  obtain ⟨hprime, hd, _⟩ := Nat.mem_primeFactors.mp hp
  exact dvd_trans (pow_dvd_pow p hk) (pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow hd) k)

/-- The lower neighbor of an even square splits into coprime factors.
If its square root is powerful, these factors already give a smaller
triple without any assumption on the upper neighbor of the square. -/
theorem triple_of_powerful_even_square_predecessor {m : ℕ} (hm₂ : 2 ≤ m) (hme : 2 ∣ m)
    (hm : Nat.Powerful m) (hlo : Nat.Powerful (m ^ 2 - 1)) :
    Nat.Powerful (m - 1) ∧ Nat.Powerful m ∧ Nat.Powerful (m + 1) := by
  let a := m - 1
  have heqa : a + 1 = m := by dsimp [a]; omega
  have ha : 0 < a := by dsimp [a]; omega
  have he := Nat.dvd_iff_mod_eq_zero.mp hme
  have haodd : a % 2 = 1 := by omega
  have hab := coprime_add_two_of_odd haodd
  have heq : m ^ 2 - 1 = a * (a + 2) := by
    rw [← heqa]
    have hr : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  rw [heq] at hlo
  have h := (full_mul_iff_of_coprime ha.ne' (by omega) hab).mp hlo
  exact ⟨h.1, hm, by rw [← heqa]; exact h.2⟩

/-- A square-center triple descends whenever its square root is powerful. -/
theorem powerful_square_center_descent {n m : ℕ} (hn : Nat.Powerful n)
    (_hm : Nat.Powerful (n + 1)) (hu : Nat.Powerful (n + 2))
    (hmp : Nat.Powerful m) (hm₂ : 2 ≤ m) (hms : n + 1 = m ^ 2) :
    ∃ a < n, a + 1 = m ∧ Nat.Powerful a ∧ Nat.Powerful (a + 1) ∧
      Nat.Powerful (a + 2) := by
  have hme : 2 ∣ m := by
    have hh := middle_even_of_full_triple hn hu
    rw [hms] at hh
    exact Nat.prime_two.dvd_of_dvd_pow hh
  have hlo : Nat.Powerful (m ^ 2 - 1) := by
    rw [← hms, Nat.add_sub_cancel]
    exact hn
  obtain ⟨hl, hc, hr⟩ :=
    triple_of_powerful_even_square_predecessor hm₂ hme hmp hlo
  have ha : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have haq : m - 1 + 2 = m + 1 := by omega
  have hlt : m < m ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) (by omega : 0 < m)
  exact ⟨m - 1, by omega, ha, hl, by rwa [ha], by rwa [haq]⟩


/-- The nonsquare-center branch of the remaining congruence classes. -/
def H1 : Prop :=
  ∀ n : ℕ, (n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35) →
    (∀ m : ℕ, n + 1 ≠ m ^ 2) →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

/-- The square-center branch, with a non-powerful square root. -/
def H2 : Prop :=
  ∀ n m : ℕ, (n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35) →
    n + 1 = m ^ 2 → ¬ Nat.Powerful m →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

lemma nine_dvd_if_three_dvd {a : ℕ} (ha : Nat.Powerful a) (h3 : 3 ∣ a) : 9 ∣ a := by
  by_cases hz : a = 0
  · simp [hz]
  · have hp : Nat.Prime 3 := by decide
    exact ha 3 (Nat.mem_primeFactors.mpr ⟨hp, h3, hz⟩)

lemma triple_residue {n : ℕ} (h1 : Nat.Powerful n) (h2 : Nat.Powerful (n + 1))
    (h3 : Nat.Powerful (n + 2)) : n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  have h4 := Nat.dvd_iff_mod_eq_zero.mp (four_dvd_middle_of_full_triple h1 h2 h3)
  have cases : n % 3 = 0 ∨ n % 3 = 2 ∨ n % 3 = 1 := by omega
  rcases cases with hn | hn | hn
  · have h9 := Nat.dvd_iff_mod_eq_zero.mp (nine_dvd_if_three_dvd h1
      (Nat.dvd_iff_mod_eq_zero.mpr hn))
    omega
  · have h9 := Nat.dvd_iff_mod_eq_zero.mp (nine_dvd_if_three_dvd h2
      (Nat.dvd_iff_mod_eq_zero.mpr (by omega : (n+1) % 3 = 0)))
    omega
  · have h9 := Nat.dvd_iff_mod_eq_zero.mp (nine_dvd_if_three_dvd h3
      (Nat.dvd_iff_mod_eq_zero.mpr (by omega : (n+2) % 3 = 0)))
    omega

theorem main : H1 → H2 → type_of% @Erdos364.erdos_364 := by
  classical
  intro hA hB hex
  let n := Nat.find hex
  obtain ⟨h₁, h₂, h₃⟩ := Nat.find_spec hex
  have hmod := triple_residue h₁ h₂ h₃
  by_cases hs : ∃ m : ℕ, n + 1 = m ^ 2
  · obtain ⟨m, hm⟩ := hs
    by_cases hp : Nat.Powerful m
    · have hm₂ : 2 ≤ m := by
        have hc := Nat.dvd_iff_mod_eq_zero.mp (four_dvd_middle_of_full_triple h₁ h₂ h₃)
        by_contra hh
        have hsmall : m = 0 ∨ m = 1 := by omega
        rcases hsmall with rfl | rfl <;> simp_all
        omega
      obtain ⟨a, ha, _, ha₁, ha₂, ha₃⟩ :=
        powerful_square_center_descent h₁ h₂ h₃ hp hm₂ hm
      exact Nat.find_min hex ha ⟨ha₁, ha₂, ha₃⟩
    · exact hB n m hmod hm hp ⟨h₁, h₂, h₃⟩
  · exact hA n hmod (fun m he => hs ⟨m, he⟩) ⟨h₁, h₂, h₃⟩

end OMA.R_Erdos364_erdos_364_R2
