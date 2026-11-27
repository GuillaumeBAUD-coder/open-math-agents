import FormalConjectures.ErdosProblems.«950»

/-! # Brun-Titchmarsh for short windows plus a partial-summation counting lemma -/
-- Reduction Erdos950.erdos_950.variants.weaker_pi_implies_f.R1 of Erdős Problem 950
-- Credit: @senamakel

open Filter
open scoped Asymptotics Nat.Prime

namespace OMA.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1

-- Brun-Titchmarsh: an interval of length t holds O(t / log t) primes.
def H1 : Prop := ∃ K₀ > (0 : ℝ), ∀ x t : ℕ, 2 ≤ t →
    (π x : ℝ) - (π (x - t) : ℝ) ≤ K₀ * t / Real.log t

-- Counting lemma: a set of integers whose counting function is O(t / log t) up to
-- (log n)^C and O(t / log n) beyond has reciprocal sum O(log log log n).
def H2 : Prop := ∀ K K₀ C : ℝ, 0 < K → 0 < K₀ → 0 < C → ∃ M : ℝ, ∀ᶠ n : ℕ in atTop,
    ∀ S : Finset ℕ, (∀ s ∈ S, 1 ≤ s ∧ s ≤ n) →
    (∀ t : ℕ, 2 ≤ t → (t : ℝ) ≤ Real.log n ^ C →
      ((S.filter (· ≤ t)).card : ℝ) ≤ K₀ * t / Real.log t) →
    (∀ t : ℕ, Real.log n ^ C < t → t ≤ n →
      ((S.filter (· ≤ t)).card : ℝ) ≤ K * t / Real.log n) →
    ∑ s ∈ S, (1 : ℝ) / s ≤ M * Real.log (Real.log (Real.log n))

lemma window (a t : ℕ) :
    ((Finset.range (a+1)).filter (fun p => p.Prime ∧ a < p + t)).card + π (a - t) ≤ π a := by
  have e1 : ∀ b, π b = ((Finset.range (b+1)).filter Nat.Prime).card := by
    intro b
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
    rfl
  rw [e1, e1, ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hp ⊢
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨by omega, h2⟩
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_range] at hp hq
    have := hp.2.1.two_le
    omega

theorem main : H1 → H2 → type_of% @Erdos950.erdos_950.variants.weaker_pi_implies_f := by
  rintro ⟨K₀, hK₀, bt⟩ dy ⟨C, hC, K, hK, hev⟩
  obtain ⟨M, hM⟩ := dy (2*K) K₀ C (by positivity) hK₀ hC
  have l3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [hM, hev, l3.eventually (eventually_ge_atTop 0), eventually_ge_atTop 2]
    with n hn hx hl hn2
  set S : Finset ℕ := ((Finset.range n).filter Prime).image (fun p => n - p) with hS
  have hf : Erdos950.f n = ∑ s ∈ S, (1:ℝ) / s := by
    rw [hS, Finset.sum_image]
    · unfold Erdos950.f
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      rw [Nat.cast_sub hp.1.le]
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hp hq
      simp only at hpq
      omega
  have hf0 : 0 ≤ Erdos950.f n := by
    unfold Erdos950.f
    apply Finset.sum_nonneg
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have : (p:ℝ) < n := by exact_mod_cast hp.1
    have : 0 < (n:ℝ) - p := by linarith
    positivity
  have hA : ∀ t : ℕ, ((S.filter (· ≤ t)).card : ℝ) ≤ (π (n-1) : ℝ) - π (n - 1 - t) := by
    intro t
    have hsub : S.filter (· ≤ t) ⊆ ((Finset.range (n-1+1)).filter
        (fun p => p.Prime ∧ n - 1 < p + t)).image (fun p => n - p) := by
      intro s hs
      simp only [hS, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hs ⊢
      obtain ⟨⟨p, ⟨hp1, hp2⟩, rfl⟩, hst⟩ := hs
      exact ⟨p, ⟨by omega, hp2.nat_prime, by omega⟩, rfl⟩
    have c1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    have c2 := window (n-1) t
    have : ((S.filter (· ≤ t)).card) + π (n-1-t) ≤ π (n-1) := by omega
    have : (((S.filter (· ≤ t)).card + π (n-1-t) : ℕ) : ℝ) ≤ π (n-1) := by exact_mod_cast this
    push_cast at this
    linarith
  have hS1 : ∀ s ∈ S, 1 ≤ s ∧ s ≤ n := by
    intro s hs
    simp only [hS, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hs
    obtain ⟨p, ⟨hp1, _⟩, rfl⟩ := hs
    omega
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have key := hn S hS1 (fun t ht2 _ => (hA t).trans (bt (n-1) t ht2)) (by
    intro t hLt htn
    have hy : ((n - 1 - t : ℕ) : ℝ) < n - Real.log n ^ C := by
      have : n - 1 - t + t ≤ n := by omega
      have : ((n - 1 - t : ℕ) : ℝ) + t ≤ n := by exact_mod_cast this
      linarith
    have h1 := hx (n-1-t) hy
    have hmono : (π (n-1) : ℝ) ≤ π n := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.sub_le n 1)
    have hny : (n:ℝ) - ((n-1-t : ℕ):ℝ) ≤ t + 1 := by
      have : n ≤ n - 1 - t + t + 1 := by omega
      have : (n:ℝ) ≤ ((n - 1 - t : ℕ):ℝ) + t + 1 := by exact_mod_cast this
      linarith
    have ht1 : (1:ℝ) ≤ t := by
      have : (0:ℝ) ≤ Real.log n ^ C := Real.rpow_nonneg hlogn.le C
      have : (0:ℝ) < t := by linarith
      exact Nat.one_le_cast.mpr (Nat.cast_pos.mp this)
    have : K * (((n:ℝ) - ((n-1-t : ℕ):ℝ)) / Real.log n) ≤ 2 * K * t / Real.log n := by
      rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hlogn.le
      nlinarith
    linarith [hA t])
  rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg hl, hf]
  exact key

end OMA.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1
