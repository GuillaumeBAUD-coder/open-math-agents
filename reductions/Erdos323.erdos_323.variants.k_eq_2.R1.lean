import FormalConjectures.ErdosProblems.«323»

/-!
The leading term for a multiplicative set satisfying Condition B is taken from
Pieter Moree, *Counting numbers in multiplicative sets: Landau versus Ramanujan*,
Theorem 2, https://archive.mpim-bonn.mpg.de/id/eprint/3346/.
The other analytic input is the prime number theorem for the class 1 modulo 4,
with the prime 2 included in the count. The reduction proves the arithmetic and
counting comparisons needed to apply these results.
-/

open Filter Asymptotics
open scoped Asymptotics

namespace OMA.R_Erdos323_erdos_323_variants_k_eq_2_R1

/-- The leading-term consequence of Moree's Theorem 2 at prime density one half. -/
def H1 : Prop :=
  ∀ A : Set ℕ, 1 ∈ A →
    (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) →
    (fun x : ℕ => ({p : ℕ | p ≤ x ∧ p.Prime ∧ p ∈ A}.ncard : ℝ) -
      (1 / 2 : ℝ) * (∫ t in (2 : ℝ)..(x : ℝ), 1 / Real.log t))
      =O[atTop] (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ) ^ 3) →
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℕ => ({n : ℕ | 0 < n ∧ n ≤ x ∧ n ∈ A}.ncard : ℝ)) ~[atTop]
        (fun x : ℕ => c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ)))

/-- The prime number theorem for primes that can be sums of two squares. -/
def H2 : Prop :=
  (fun x : ℕ => ({p : ℕ | p ≤ x ∧ p.Prime ∧ p % 4 ≠ 3}.ncard : ℝ) -
    (1 / 2 : ℝ) * (∫ t in (2 : ℝ)..(x : ℝ), 1 / Real.log t))
    =O[atTop] (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ) ^ 3)

lemma representable_iff (n : ℕ) :
    (∃ v : Fin 2 → ℕ, n = ∑ i, v i ^ 2) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  have hpair : (∃ v : Fin 2 → ℕ, n = ∑ i, v i ^ 2) ↔
      ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
    simp only [Fin.sum_univ_two]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v 0, v 1, hv⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨![a, b], by simpa using hab⟩
  rw [hpair, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hp4
    by_cases hp' : p ∈ n.primeFactors
    · rw [Nat.factorization_def n hp]
      exact h p hp' hp4
    · have hzero : n.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      rw [hzero]
      exact Even.zero
  · intro h p hp hp4
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [← Nat.factorization_def n hprime]
    exact h p hprime hp4

lemma even_factorization_mul_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) {p : ℕ} (hp : p.Prime) :
    Even ((m * n).factorization p) ↔ Even (m.factorization p) ∧ Even (n.factorization p) := by
  rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply]
  by_cases hpm : p ∣ m
  · have hpn : ¬ p ∣ n := by
      intro hpn
      have hpgcd := Nat.dvd_gcd hpm hpn
      rw [hmn.gcd_eq_one] at hpgcd
      exact hp.not_dvd_one hpgcd
    simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  · simp [Nat.factorization_eq_zero_of_not_dvd hpm]

lemma prime_even_factorizations_iff {p : ℕ} (hp : p.Prime) :
    (∀ q : ℕ, q.Prime → q % 4 = 3 → Even (p.factorization q)) ↔ p % 4 ≠ 3 := by
  constructor
  · intro h hmod
    have hself := h p hp hmod
    simp [hp.factorization_self] at hself
  · intro h q hq hmod
    have hne : q ≠ p := fun heq => h (heq ▸ hmod)
    simp [hp.factorization, hne]

lemma count_insert_zero (x : ℕ) :
    Erdos323.f 2 2 x =
      {n : ℕ | 0 < n ∧ n ≤ x ∧
        ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)}.ncard + 1 := by
  let B : Set ℕ := {n : ℕ | 0 < n ∧ n ≤ x ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)}
  have hBfin : B.Finite := (Set.finite_le_nat x).subset fun _ hx => hx.2.1
  have hB0 : 0 ∉ B := fun h => Nat.lt_irrefl 0 h.1
  have hset : {n : ℕ | n ≤ x ∧ ∃ v : Fin 2 → ℕ, n = ∑ i, v i ^ 2} = insert 0 B := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    obtain rfl | hn := n.eq_zero_or_pos
    · exact iff_of_true ⟨Nat.zero_le _, ⟨fun _ => 0, by simp⟩⟩ (Or.inl rfl)
    · simp only [hn.ne', false_or, B, Set.mem_ofPred_eq, hn, true_and, representable_iff]
  unfold Erdos323.f
  rw [hset, Set.ncard_insert_of_notMem hB0 hBfin]

lemma one_isLittleO_scale {c : ℝ} (hc : 0 < c) :
    (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      (fun x : ℕ => c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  apply (isLittleO_const_left_of_ne one_ne_zero).2
  have hsqrt : Tendsto (fun x : ℕ => c * Real.sqrt (x : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hsqrt
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hx' : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
  have hspos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 (Real.log_pos hx')
  have hcomparison : c * Real.sqrt (x : ℝ) ≤ c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) := by
    apply (le_div_iff₀ hspos).2
    calc
      _ ≤ c * Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.log_le_self hx0)) (by positivity)
      _ = c * (x : ℝ) := by rw [mul_assoc, Real.mul_self_sqrt hx0]
  exact hcomparison.trans (le_abs_self _)

theorem main : H1 → H2 → type_of% @Erdos323.erdos_323.variants.k_eq_2 := by
  intro h₁ h₂
  let A : Set ℕ := {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)}
  have hAone : 1 ∈ A := by simp [A]
  have hAmul : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n →
      (m * n ∈ A ↔ m ∈ A ∧ n ∈ A) := by
    intro m n hm hn hmn
    have hlocal (p : ℕ) (hp : p.Prime) := even_factorization_mul_iff hm hn hmn hp
    constructor
    · intro h
      exact ⟨fun p hp hmod => ((hlocal p hp).mp (h p hp hmod)).1,
        fun p hp hmod => ((hlocal p hp).mp (h p hp hmod)).2⟩
    · rintro ⟨hₘ, hₙ⟩ p hp hmod
      exact (hlocal p hp).mpr ⟨hₘ p hp hmod, hₙ p hp hmod⟩
  have hprimes (x : ℕ) : {p : ℕ | p ≤ x ∧ p.Prime ∧ p ∈ A} =
      {p : ℕ | p ≤ x ∧ p.Prime ∧ p % 4 ≠ 3} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hp₁, hp₂, hp₃⟩
      exact ⟨hp₁, hp₂, (prime_even_factorizations_iff hp₂).mp hp₃⟩
    · rintro ⟨hp₁, hp₂, hp₃⟩
      exact ⟨hp₁, hp₂, (prime_even_factorizations_iff hp₂).mpr hp₃⟩
  have hpnt := h₂
  unfold H2 at hpnt
  obtain ⟨c, hc, hcount⟩ := h₁ A hAone hAmul (by simpa only [hprimes] using hpnt)
  refine ⟨c, hc, (hcount.add_isLittleO (one_isLittleO_scale hc)).congr_left ?_⟩
  exact Filter.Eventually.of_forall fun x => by
    change ({n : ℕ | 0 < n ∧ n ≤ x ∧ n ∈ A}.ncard : ℝ) + 1 = Erdos323.f 2 2 x
    simp only [count_insert_zero, Nat.cast_add, Nat.cast_one, A, Set.mem_ofPred_eq]

end OMA.R_Erdos323_erdos_323_variants_k_eq_2_R1
