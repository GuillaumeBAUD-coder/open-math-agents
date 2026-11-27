import FormalConjectures.ErdosProblems.«375»

-- Credit: @marcusbuffett
/-!
Following Laishram and Murty, *Grimm's conjecture and smooth numbers*,
Michigan Math. J. 61 (2012), Lemmas 2.3–2.4. A long prime-free interval would
assign distinct small primes to more smooth numbers than there are such primes.
-/
namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1

open Filter Finset

/-- The Friedlander–Lagarias short-interval smooth-number lower bound
in the form of Laishram–Murty, Lemma 2.3. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
    let k := ⌊(x : ℝ) ^ a⌋₊
    c * k ≤ (((univ : Finset (Fin k)).filter
      (fun i : Fin k => x + (i : ℕ) + 1 ∈ Nat.smoothNumbers (k + 1))).card : ℝ)

/-- The primes have relative density zero among the natural numbers. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ᶠ k : ℕ in atTop,
  ((k + 1).primesBelow.card : ℝ) < c * k

theorem main : H1 → H2 → type_of% @Erdos375.erdos_375.variants.bounded_gap := by
  classical
  rintro ⟨a, ha, ha', c, hc, hSmooth⟩ hPrimes hGrimm
  let p := Nat.nth Nat.Prime
  have hpTop : Tendsto p atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  let k (x : ℕ) := ⌊(x : ℝ) ^ a⌋₊
  have hkTop : Tendsto k atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmooth
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hPrimes c hc)
  refine ⟨(1 / 2 - a) / 2, by linarith, ?_⟩
  filter_upwards [hpTop.eventually_ge_atTop N, (hkTop.comp hpTop).eventually_ge_atTop M] with n hn hm
  have hp : 1 < p n := by have := Nat.add_two_le_nth_prime n; dsimp [p]; omega
  have hg : p (n + 1) ≤ p n + k (p n) := by
    by_contra! hgap
    have hcomp : ∀ i < k (p n), ¬(p n + i + 1).Prime := by
      intro i hi hiPrime
      have hlt : p n + i + 1 < p (n + 1) := by omega
      have := Nat.le_nth_of_lt_nth_succ hlt hiPrime
      change p n + i + 1 ≤ p n at this
      omega
    obtain ⟨q, hq, hd⟩ := hGrimm (p n) hp.le (k (p n)) hcomp
    let S := (univ : Finset (Fin (k (p n)))).filter
      (fun i : Fin (k (p n)) => p n + (i : ℕ) + 1 ∈ Nat.smoothNumbers (k (p n) + 1))
    have hsub : S.image q ⊆ (k (p n) + 1).primesBelow := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      have hs := (mem_filter.mp hi).2
      exact Nat.mem_primesBelow.mpr ⟨Nat.mem_smoothNumbers'.mp hs _ (hd i).1 (hd i).2, (hd i).1⟩
    have hcard := card_le_card hsub
    rw [card_image_of_injective _ hq] at hcard
    have hcardR : (S.card : ℝ) ≤ ((k (p n) + 1).primesBelow.card : ℝ) := by exact_mod_cast hcard
    have hlow : c * k (p n) ≤ (S.card : ℝ) := hN _ hn
    exact (hM _ hm).not_ge (hlow.trans hcardR)
  change (p (n + 1) : ℝ) - p n < (p n : ℝ) ^ _
  have hgR : (p (n+1) : ℝ) ≤ (p n : ℝ) + k (p n) := by exact_mod_cast hg
  calc (p (n+1) : ℝ) - p n ≤ k (p n) := by linarith
    _ ≤ (p n : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp) (by linarith)

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1
