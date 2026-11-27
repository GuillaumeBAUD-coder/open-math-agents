import FormalConjectures.ErdosProblems.«317»
import Mathlib.NumberTheory.Chebyshev

/-! Assemble local prime-power residues and then lift through the grid supplied by smooth denominators. -/
namespace OMA.R_Erdos317_erdos_317_R1

open Finset

/-- A small positive integer passes all the local tests. Each test uses only
weights which vanish at every other primary component of the modulus. -/
def H1 : Prop :=
  ∃ C N : ℕ, ∀ n ≥ N,
    let L := Nat.lcmUpto n
    let B := Nat.lcmUpto n.sqrt
    let P := L / B
    let Q := fun p : ℕ => p ^ P.factorization p
    ∃ a : ℕ, 0 < a ∧ a ≤ L ∧ 2^n * a ≤ C * L ∧
      ∀ p ∈ P.primeFactors, ∃ d : Fin n → ℤ,
        (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
        (∀ i, d i ≠ 0 → ¬(i.val+1) ∣ B ∧ ¬Q p ∣ L/(i.val+1) ∧
          ∀ q ∈ P.primeFactors, q ≠ p → Q q ∣ L/(i.val+1)) ∧
        (Q p : ℤ) ∣ (a : ℤ) - ∑ i, d i * (L/(i.val+1) : ℕ)

/-- The divisors of B that are available as denominators fill a central interval
of the grid with spacing 1/B. The required radius depends only on the harmonic
mass of the complementary denominators. -/
def H2 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    let B := Nat.lcmUpto n.sqrt
    ∀ z : ℤ, |(z : ℚ) / B| ≤ 1 +
        ∑ i : Fin n with ¬(i.val+1) ∣ B, (1 : ℚ) / (i.val+1) →
      ∃ d : Fin n → ℤ,
        (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
        (∀ i, ¬(i.val+1) ∣ B → d i = 0) ∧
        ∑ i, (d i : ℚ) / (i.val+1) = (z : ℚ) / B

lemma dvd_of_primary {P : ℕ} (hP : P ≠ 0) {x : ℤ}
    (h : ∀ p ∈ P.primeFactors, ((p ^ P.factorization p : ℕ) : ℤ) ∣ x) :
    (P : ℤ) ∣ x := by
  apply Int.natCast_dvd.mpr
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p j hp hj
  by_cases hmem : p ∈ P.primeFactors
  · exact (pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hP).mp hj)).trans
      (Int.natCast_dvd.mp (h p hmem))
  · have hj0 : j = 0 := by
      by_contra hj0
      have hpdiv := (dvd_pow_self p hj0).trans hj
      exact hmem (Nat.mem_primeFactors.mpr ⟨hp,hpdiv,hP⟩)
    simp [hj0]

/-- The off-diagonal divisibilities let us use all the local coefficient choices
at once, preserving ternary coefficients, and lift their congruences to P. -/
lemma combine {ι : Type*} [Fintype ι] (P : ℕ) (hP : P ≠ 0)
    (w : ι → ℕ) (core : ι → Prop) (a : ℤ)
    (h : ∀ p ∈ P.primeFactors, ∃ d : ι → ℤ,
      (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
      (∀ i, d i ≠ 0 → ¬core i ∧ ¬p ^ P.factorization p ∣ w i ∧
        ∀ q ∈ P.primeFactors, q ≠ p → q ^ P.factorization q ∣ w i) ∧
      ((p ^ P.factorization p : ℕ) : ℤ) ∣ a - ∑ i, d i * w i) :
    ∃ e : ι → ℤ, (∀ i, e i = -1 ∨ e i = 0 ∨ e i = 1) ∧
      (∀ i, core i → e i = 0) ∧ (P : ℤ) ∣ a - ∑ i, e i * w i := by
  classical
  let J := ↥P.primeFactors
  choose f hf hs hr using (fun p : J => h p p.property)
  let e (i : ι) := ∑ p : J, f p i
  let W (p : J) := ∑ i, f p i * w i
  have hW : ∑ i, e i * w i = ∑ p, W p := by
    simp only [e, W, sum_mul]
    exact sum_comm
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    by_cases hn : ∃ p, f p i ≠ 0
    · obtain ⟨p,hpi⟩ := hn
      have he : e i = f p i := by
        apply sum_eq_single_of_mem p (mem_univ _)
        intro q _ hqp
        by_contra hqi
        exact (hs p i hpi).2.1 ((hs q i hqi).2.2 p p.property
          (fun hx => hqp (Subtype.ext hx.symm)))
      rw [he]
      exact hf p i
    · push Not at hn
      simp [e, hn]
  · intro i hcore
    apply sum_eq_zero
    intro p _
    by_contra hpi
    exact (hs p i hpi).1 hcore
  · rw [hW]
    apply dvd_of_primary hP
    intro p hp
    let u : J := ⟨p,hp⟩
    let M := ((p ^ P.factorization p : ℕ) : ℤ)
    have hrest : M ∣ ∑ v ∈ (univ : Finset J).erase u, W v := by
      apply dvd_sum
      intro v hv
      apply dvd_sum
      intro i _
      by_cases hf0 : f v i = 0
      · simp [hf0]
      · have hne : p ≠ (v : ℕ) := fun eq => (mem_erase.mp hv).1 (Subtype.ext eq.symm)
        have := (hs v i hf0).2.2 p hp hne
        exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr this) _
    have hu : M ∣ a - W u := hr u
    rw [← sum_erase_add univ W (mem_univ u)]
    have heq : a - ((∑ v ∈ (univ : Finset J).erase u, W v) + W u) =
        (a - W u) - ∑ v ∈ (univ : Finset J).erase u, W v := by ring
    rw [heq]
    exact dvd_sub hu hrest

lemma scaled_sum (n : ℕ) (d : Fin n → ℤ) :
    ((∑ i, d i * (Nat.lcmUpto n / (i.val+1) : ℕ) : ℤ) : ℚ) =
      (Nat.lcmUpto n : ℚ) * ∑ i, (d i : ℚ) / (i.val+1) := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hd : i.val+1 ∣ Nat.lcmUpto n :=
    Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hh : ((Nat.lcmUpto n / (i.val+1) : ℕ) : ℚ) * (i.val+1) = Nat.lcmUpto n := by
    exact_mod_cast Nat.div_mul_cancel hd
  field_simp
  linear_combination (d i : ℚ) * hh

lemma mass_bound {n B : ℕ} (d : Fin n → ℤ)
    (hd : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1)
    (hz : ∀ i, (i.val+1) ∣ B → d i = 0) :
    |∑ i, (d i : ℚ) / (i.val+1)| ≤
      ∑ i : Fin n with ¬(i.val+1) ∣ B, (1 : ℚ) / (i.val+1) := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_filter]
  apply sum_le_sum
  intro i _
  by_cases h : (i.val+1) ∣ B
  · simp [h, hz i h]
  · have hnon : (0 : ℚ) ≤ (i.val : ℚ) + 1 := by positivity
    rcases hd i with h' | h' | h' <;> simp [h, h', abs_div, abs_of_nonneg hnon, hnon]

lemma assemble {n C a : ℕ} (ha : 0 < a) (hal : a ≤ Nat.lcmUpto n)
    (hab : 2^n * a ≤ C * Nat.lcmUpto n)
    (h₁ : let L := Nat.lcmUpto n
          let B := Nat.lcmUpto n.sqrt
          let P := L/B
          let Q := fun p : ℕ => p ^ P.factorization p
          ∀ p ∈ P.primeFactors, ∃ d : Fin n → ℤ,
            (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
            (∀ i, d i ≠ 0 → ¬(i.val+1) ∣ B ∧ ¬Q p ∣ L/(i.val+1) ∧
              ∀ q ∈ P.primeFactors, q ≠ p → Q q ∣ L/(i.val+1)) ∧
            (Q p : ℤ) ∣ (a : ℤ) - ∑ i, d i * (L/(i.val+1) : ℕ))
    (h₂ : let B := Nat.lcmUpto n.sqrt
          ∀ z : ℤ, |(z : ℚ)/B| ≤ 1 + ∑ i : Fin n with ¬(i.val+1) ∣ B, (1:ℚ)/(i.val+1) →
            ∃ d : Fin n → ℤ, (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧
              (∀ i, ¬(i.val+1) ∣ B → d i = 0) ∧
              ∑ i, (d i : ℚ)/(i.val+1) = (z:ℚ)/B) :
    ∃ δ : Fin n → ℚ, Set.range δ ⊆ {-1,0,1} ∧
      0 < |∑ i, (δ i : ℝ) / (i.val+1)| ∧ |∑ i, (δ i : ℝ)/(i.val+1)| ≤ C/2^n := by
  classical
  let L := Nat.lcmUpto n
  let B := Nat.lcmUpto n.sqrt
  let P := L/B
  have hBL : B ∣ L := Finset.lcm_mono (f := id) (show Icc 1 n.sqrt ⊆ Icc 1 n from
    fun k hk => mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans (Nat.sqrt_le_self n)⟩)
  have hP : P ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) hBL) (Nat.lcmUpto_pos _)).ne'
  have hPB : P*B=L := Nat.div_mul_cancel hBL
  obtain ⟨e, htern, hcore, z, hz⟩ := combine P hP (fun i : Fin n => L/(i.val+1))
    (fun i => (i.val+1) ∣ B) a h₁
  let s : ℚ := ∑ i, (e i : ℚ)/(i.val+1)
  have hZ : (a : ℚ) - L*s = P*(z : ℚ) := by
    rw [← show _ = (L:ℚ)*s from scaled_sum n e]
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using congrArg (fun x : ℤ => (x : ℚ)) hz
  have bpos : 0 < (B : ℚ) := by exact_mod_cast Nat.lcmUpto_pos n.sqrt
  have lpos : 0 < (L : ℚ) := by exact_mod_cast Nat.lcmUpto_pos n
  have hPB' : (P : ℚ)*B=L := by exact_mod_cast hPB
  have hdiff : (z : ℚ)/B = a/L - s := by
    field_simp
    linear_combination -(B : ℚ)*hZ - (z : ℚ)*hPB'
  have ha1 : |(a : ℚ)/L| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ lpos, one_mul]
    exact_mod_cast hal
  have hradius : |(z : ℚ)/B| ≤ 1 + ∑ i : Fin n with ¬(i.val+1) ∣ B, (1:ℚ)/(i.val+1) := by
    rw [hdiff]
    exact (abs_sub _ _).trans (add_le_add ha1 (mass_bound e htern hcore))
  obtain ⟨d, hd, hrough, hval⟩ := h₂ z hradius
  let δ (i : Fin n) : ℚ := (d i : ℚ) + (e i : ℚ)
  have hsum : ∑ i, δ i / (i.val+1) = (a : ℚ)/L := by
    simp only [δ, add_div, sum_add_distrib]
    rw [hval, hdiff]
    change _ - s + s = _
    ring
  have hre : ∑ i, (δ i : ℝ)/(i.val+1) = (a : ℝ)/L := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using
      congrArg (fun x : ℚ => (x : ℝ)) hsum
  refine ⟨δ, ?_, ?_⟩
  · rintro _ ⟨i,rfl⟩
    by_cases hi : (i.val+1) ∣ B
    · rcases hd i with h | h | h <;> simp [δ, hcore i hi, h]
    · rcases htern i with h | h | h <;> simp [δ, hrough i hi, h]
  · have hL : 0 < (L : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
    have hapos : 0 < (a : ℝ)/L := by positivity
    rw [hre, abs_of_pos hapos]
    refine ⟨hapos, (div_le_div_iff₀ hL (by positivity)).mpr ?_⟩
    simpa [mul_comm] using (show (2:ℝ)^n * a ≤ C*L by exact_mod_cast hab)

theorem main : H1 → H2 → type_of% @Erdos317.erdos_317 := by
  classical
  rintro ⟨C,N,h₁⟩ ⟨M,h₂⟩
  let K := max N M
  let c : ℝ := C + 2^K + 1
  refine ⟨c, by dsimp [c]; positivity, fun n hn => ?_⟩
  by_cases hk : K ≤ n
  · obtain ⟨a,ha,hal,hab,hloc⟩ := h₁ n ((le_max_left _ _).trans hk)
    obtain ⟨δ,hd,hp,hu⟩ := assemble ha hal hab hloc (h₂ n ((le_max_right _ _).trans hk))
    refine ⟨δ,hd,hp,hu.trans_lt ?_⟩
    apply div_lt_div_of_pos_right _ (by positivity)
    dsimp [c]
    linarith [show (0:ℝ)<2^K by positivity]
  · let i₀ : Fin n := ⟨0,hn⟩
    let δ (i : Fin n) : ℚ := if i = i₀ then 1 else 0
    refine ⟨δ, ?_, ?_⟩
    · rintro _ ⟨i,rfl⟩
      by_cases h : i = i₀ <;> simp [δ,h]
    · have he : ∑ i, (δ i : ℝ) / (i.val+1) = 1 := by
        simp [δ, apply_ite, ite_div, i₀]
      change 0 < |∑ i, (δ i : ℝ) / (i.val+1)| ∧ |∑ i, (δ i : ℝ) / (i.val+1)| < c/2^n
      rw [he, abs_one]
      refine ⟨zero_lt_one, (lt_div_iff₀ (by positivity)).mpr ?_⟩
      have hp : (2:ℝ)^n ≤ 2^K := pow_le_pow_right₀ (by norm_num) (by omega)
      dsimp [c]
      linarith [show (0:ℝ) ≤ C by positivity]

end OMA.R_Erdos317_erdos_317_R1
