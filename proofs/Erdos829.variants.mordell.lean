import FormalConjectures.ErdosProblems.«829»

-- Problem: Erdős Problem 829 — mordell
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/829.lean:95 (declaration Erdos829.variants.mordell)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof outline (the classical tangent construction, as in Hardy and Wright).  If
`x ^ 3 + y ^ 3 = c * z ^ 3` with `x ≥ 4 * y > 0`, two tangent steps give a new solution
`x' ^ 3 + y' ^ 3 = c * z' ^ 3` in positive integers whose ratio `x' / y'` is strictly smaller
than `x / y` but at least `(x / y) / 8`.  Starting from `(4 * 8 ^ m, 1)` and iterating `K` times
gives `K + 1` solutions with pairwise distinct ratios; clearing denominators gives one integer
with `K + 1` representations as a sum of two cubes.
-/

namespace OMA829

open Finset

/-- Two tangent steps on the curve `X ^ 3 + Y ^ 3 = c`. -/
theorem double_step (x y : ℕ) (hy : 0 < y) (hxy : 4 * y ≤ x) :
    ∃ x' y' z' : ℕ, 0 < y' ∧ 0 < z' ∧ x' ^ 3 + y' ^ 3 = (x ^ 3 + y ^ 3) * z' ^ 3 ∧
      x' * y < x * y' ∧ x * y' ≤ 8 * (x' * y) := by
  have hx : 0 < x := by omega
  have hyx : y < x := by omega
  -- first step
  obtain ⟨u, hu⟩ : ∃ u, u = x * (x ^ 3 + 2 * y ^ 3) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = y * (2 * x ^ 3 + y ^ 3) := ⟨_, rfl⟩
  have hy3 : y ^ 3 < x ^ 3 := Nat.pow_lt_pow_left hyx (by norm_num)
  obtain ⟨d1, hd1⟩ : ∃ d1, x ^ 3 = y ^ 3 + d1 := ⟨x ^ 3 - y ^ 3, by omega⟩
  have hd1pos : 0 < d1 := by omega
  have hx3 : 0 < x ^ 3 := by positivity
  have hy3pos : 0 < y ^ 3 := by positivity
  have hupos : 0 < u := by rw [hu]; positivity
  have hvpos : 0 < v := by rw [hv]; positivity
  -- u ≥ 2 v
  have huv : 2 * v ≤ u := by
    rw [hu, hv]
    have h1 : 4 * y * (x ^ 3 + 2 * y ^ 3) ≤ x * (x ^ 3 + 2 * y ^ 3) :=
      Nat.mul_le_mul_right _ hxy
    have h2 : 2 * (y * (2 * x ^ 3 + y ^ 3)) ≤ 4 * y * (x ^ 3 + 2 * y ^ 3) := by
      have e1 : 2 * (y * (2 * x ^ 3 + y ^ 3)) = 4 * (y * x ^ 3) + 2 * (y * y ^ 3) := by ring
      have e2 : 4 * y * (x ^ 3 + 2 * y ^ 3) = 4 * (y * x ^ 3) + 8 * (y * y ^ 3) := by ring
      rw [e1, e2]
      omega
    omega
  have hu3 : 8 * v ^ 3 ≤ u ^ 3 := by
    have h1 : (2 * v) ^ 3 ≤ u ^ 3 := Nat.pow_le_pow_left huv 3
    have e1 : (2 * v) ^ 3 = 8 * v ^ 3 := by ring
    omega
  have hv3pos : 0 < v ^ 3 := by positivity
  obtain ⟨d2, hd2⟩ : ∃ d2, u ^ 3 = 2 * v ^ 3 + d2 := ⟨u ^ 3 - 2 * v ^ 3, by omega⟩
  obtain ⟨d3, hd3⟩ : ∃ d3, 2 * u ^ 3 = v ^ 3 + d3 := ⟨2 * u ^ 3 - v ^ 3, by omega⟩
  have hd2pos : 0 < d2 := by omega
  have hd3pos : 0 < d3 := by omega
  -- ratio comparisons for the first step
  have hA1 : u * y < x * v := by
    rw [hu, hv]
    have e1 : x * (x ^ 3 + 2 * y ^ 3) * y = (x * y) * (x ^ 3 + 2 * y ^ 3) := by ring
    have e2 : x * (y * (2 * x ^ 3 + y ^ 3)) = (x * y) * (2 * x ^ 3 + y ^ 3) := by ring
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos hx hy)
  have hA2 : x * v ≤ 2 * (u * y) := by
    rw [hu, hv]
    have e1 : 2 * (x * (x ^ 3 + 2 * y ^ 3) * y) = (x * y) * (2 * (x ^ 3 + 2 * y ^ 3)) := by ring
    have e2 : x * (y * (2 * x ^ 3 + y ^ 3)) = (x * y) * (2 * x ^ 3 + y ^ 3) := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul_left _ (by omega)
  -- second step
  refine ⟨u * d2, v * d3, d1 * (u ^ 3 + v ^ 3), by positivity, by positivity, ?_, ?_, ?_⟩
  · -- the identity, proved over the integers
    have hd1z : (d1 : ℤ) = (x : ℤ) ^ 3 - (y : ℤ) ^ 3 := by
      have := congrArg (Nat.cast (R := ℤ)) hd1
      push_cast at this
      linarith
    have hd2z : (d2 : ℤ) = (u : ℤ) ^ 3 - 2 * (v : ℤ) ^ 3 := by
      have := congrArg (Nat.cast (R := ℤ)) hd2
      push_cast at this
      linarith
    have hd3z : (d3 : ℤ) = 2 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3 := by
      have := congrArg (Nat.cast (R := ℤ)) hd3
      push_cast at this
      linarith
    have huz : (u : ℤ) = (x : ℤ) * ((x : ℤ) ^ 3 + 2 * (y : ℤ) ^ 3) := by
      rw [hu]; push_cast; ring
    have hvz : (v : ℤ) = (y : ℤ) * (2 * (x : ℤ) ^ 3 + (y : ℤ) ^ 3) := by
      rw [hv]; push_cast; ring
    have hAz : (u : ℤ) ^ 3 - (v : ℤ) ^ 3 = ((x : ℤ) ^ 3 + (y : ℤ) ^ 3) * (d1 : ℤ) ^ 3 := by
      rw [huz, hvz, hd1z]
      ring
    have hBz : ((u : ℤ) * (d2 : ℤ)) ^ 3 + ((v : ℤ) * (d3 : ℤ)) ^ 3 =
        ((u : ℤ) ^ 3 - (v : ℤ) ^ 3) * ((u : ℤ) ^ 3 + (v : ℤ) ^ 3) ^ 3 := by
      rw [hd2z, hd3z]
      ring
    have hgoal : (((u * d2) ^ 3 + (v * d3) ^ 3 : ℕ) : ℤ) =
        (((x ^ 3 + y ^ 3) * (d1 * (u ^ 3 + v ^ 3)) ^ 3 : ℕ) : ℤ) := by
      push_cast
      rw [hBz, hAz]
      ring
    exact_mod_cast hgoal
  · -- x' * y < x * y'
    have hB1 : (u * d2) * v < u * (v * d3) := by
      have e1 : (u * d2) * v = (u * v) * d2 := by ring
      have e2 : u * (v * d3) = (u * v) * d3 := by ring
      rw [e1, e2]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos hupos hvpos)
    have h1 : ((u * d2) * v) * (u * y) < (u * (v * d3)) * (x * v) :=
      Nat.mul_lt_mul'' hB1 hA1
    have e1 : ((u * d2) * v) * (u * y) = (u * v) * ((u * d2) * y) := by ring
    have e2 : (u * (v * d3)) * (x * v) = (u * v) * (x * (v * d3)) := by ring
    rw [e1, e2] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  · -- x * y' ≤ 8 * (x' * y)
    have hB2 : u * (v * d3) ≤ 4 * ((u * d2) * v) := by
      have e1 : u * (v * d3) = (u * v) * d3 := by ring
      have e2 : 4 * ((u * d2) * v) = (u * v) * (4 * d2) := by ring
      rw [e1, e2]
      exact Nat.mul_le_mul_left _ (by omega)
    have h1 : (u * (v * d3)) * (x * v) ≤ (4 * ((u * d2) * v)) * (2 * (u * y)) :=
      Nat.mul_le_mul hB2 hA2
    have e1 : (u * (v * d3)) * (x * v) = (u * v) * (x * (v * d3)) := by ring
    have e2 : (4 * ((u * d2) * v)) * (2 * (u * y)) = (u * v) * (8 * ((u * d2) * y)) := by ring
    rw [e1, e2] at h1
    exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hupos hvpos)

/-- For every `K` there is an integer with `K + 1` representations as a sum of two cubes; the
extra data (a representation of smallest ratio, with a lower bound on that ratio) drives the
induction. -/
theorem many (K : ℕ) : ∀ m : ℕ, ∃ n : ℕ, 0 < n ∧ ∃ s : Finset (ℕ × ℕ), s.card = K + 1 ∧
    (∀ p ∈ s, p.1 ^ 3 + p.2 ^ 3 = n) ∧
    ∃ a b : ℕ, (a, b) ∈ s ∧ 0 < b ∧ 4 * 8 ^ m * b ≤ a ∧
      ∀ p ∈ s, p ≠ (a, b) → a * p.2 < p.1 * b := by
  induction K with
  | zero =>
    intro m
    refine ⟨(4 * 8 ^ m) ^ 3 + 1 ^ 3, by positivity, {(4 * 8 ^ m, 1)}, by simp, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton] at hp
      rw [hp]
    · refine ⟨4 * 8 ^ m, 1, by simp, by norm_num, by omega, ?_⟩
      intro p hp hne
      rw [Finset.mem_singleton] at hp
      exact absurd hp hne
  | succ K ih =>
    intro m
    obtain ⟨n, hn, s, hcard, hsum, a, b, hab, hb, hratio, hmin⟩ := ih (m + 1)
    have h8 : 0 < 8 ^ (m + 1) := by positivity
    have e8 : 8 ^ (m + 1) = 8 * 8 ^ m := by ring
    have h4 : 4 * b ≤ a := by
      have h1 : 4 * 1 * b ≤ 4 * 8 ^ (m + 1) * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h8)
      omega
    obtain ⟨x', y', z', hy', hz', hid, hlt, hle⟩ := double_step a b hb h4
    have hn' : a ^ 3 + b ^ 3 = n := hsum (a, b) hab
    rw [hn'] at hid
    -- every old point has ratio strictly larger than the new one
    have hall : ∀ p ∈ s, x' * p.2 < p.1 * y' := by
      intro p hp
      by_cases hpe : p = (a, b)
      · rw [hpe]
        exact hlt
      · have h1 := hmin p hp hpe
        have h2 : (x' * b) * p.2 ≤ (a * y') * p.2 := Nat.mul_le_mul_right _ hlt.le
        have h3 : (a * p.2) * y' < (p.1 * b) * y' := Nat.mul_lt_mul_of_pos_right h1 hy'
        have e1 : (x' * b) * p.2 = b * (x' * p.2) := by ring
        have e2 : (a * y') * p.2 = (a * p.2) * y' := by ring
        have e3 : (p.1 * b) * y' = b * (p.1 * y') := by ring
        rw [e1, e2] at h2
        rw [e3] at h3
        exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 h3)
    have hinj : Function.Injective (fun p : ℕ × ℕ => (z' * p.1, z' * p.2)) := by
      intro p p' hpp
      simp only [Prod.mk.injEq] at hpp
      obtain ⟨h1, h2⟩ := hpp
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hz' h1) (Nat.eq_of_mul_eq_mul_left hz' h2)
    have hnotin : (x', y') ∉ s.image (fun p : ℕ × ℕ => (z' * p.1, z' * p.2)) := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨p, hp, hpe⟩ := hmem
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨h1, h2⟩ := hpe
      have h3 := hall p hp
      rw [← h1, ← h2] at h3
      have e1 : z' * p.1 * p.2 = p.1 * (z' * p.2) := by ring
      rw [e1] at h3
      exact lt_irrefl _ h3
    refine ⟨n * z' ^ 3, by positivity,
      insert (x', y') (s.image (fun p : ℕ × ℕ => (z' * p.1, z' * p.2))), ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnotin, Finset.card_image_of_injective _ hinj, hcard]
    · intro p hp
      rw [Finset.mem_insert, Finset.mem_image] at hp
      rcases hp with hp | ⟨p0, hp0, hpe⟩
      · rw [hp]
        exact hid
      · rw [← hpe]
        have := hsum p0 hp0
        have e1 : (z' * p0.1) ^ 3 + (z' * p0.2) ^ 3 = (p0.1 ^ 3 + p0.2 ^ 3) * z' ^ 3 := by ring
        rw [e1, this]
    · refine ⟨x', y', Finset.mem_insert_self _ _, hy', ?_, ?_⟩
      · -- ratio bound
        rw [e8] at hratio
        have h1 : (4 * (8 * 8 ^ m) * b) * y' ≤ a * y' := Nat.mul_le_mul_right _ hratio
        have h2 : (4 * (8 * 8 ^ m) * b) * y' ≤ 8 * (x' * b) := h1.trans hle
        have e1 : (4 * (8 * 8 ^ m) * b) * y' = (8 * b) * (4 * 8 ^ m * y') := by ring
        have e2 : 8 * (x' * b) = (8 * b) * x' := by ring
        rw [e1, e2] at h2
        exact Nat.le_of_mul_le_mul_left h2 (by omega)
      · intro p hp hne
        rw [Finset.mem_insert, Finset.mem_image] at hp
        rcases hp with hp | ⟨p0, hp0, hpe⟩
        · exact absurd hp hne
        · rw [← hpe]
          have h3 := hall p0 hp0
          have e1 : x' * (z' * p0.2) = z' * (x' * p0.2) := by ring
          have e2 : z' * p0.1 * y' = z' * (p0.1 * y') := by ring
          show x' * (z' * p0.2) < z' * p0.1 * y'
          rw [e1, e2]
          exact Nat.mul_lt_mul_of_pos_left h3 hz'

/-- A finite set of pairs with a fixed sum of cubes bounds `sumRep` from below. -/
theorem rep_lower (n : ℕ) (s : Finset (ℕ × ℕ)) (h : ∀ p ∈ s, p.1 ^ 3 + p.2 ^ 3 = n) :
    s.card ≤ AdditiveCombinatorics.sumRep Erdos829.cubes n := by
  rw [AdditiveCombinatorics.sumRep_def]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1 ^ 3, p.2 ^ 3))
  · intro p hp
    have hp' := h p (Finset.mem_coe.mp hp)
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr hp', ⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩
  · intro p _ p' _ hpp
    simp only [Prod.mk.injEq] at hpp
    obtain ⟨h1, h2⟩ := hpp
    exact Prod.ext (Nat.pow_left_injective (by norm_num) h1)
      (Nat.pow_left_injective (by norm_num) h2)

/-- Arbitrarily large integers have at least `K` representations. -/
theorem frequently_rep (K M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ K ≤ AdditiveCombinatorics.sumRep Erdos829.cubes N := by
  obtain ⟨n, hn, s, hcard, hsum, _⟩ := many K 0
  have hinj : Function.Injective (fun p : ℕ × ℕ => ((M + 1) * p.1, (M + 1) * p.2)) := by
    intro p p' hpp
    simp only [Prod.mk.injEq] at hpp
    obtain ⟨h1, h2⟩ := hpp
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos M) h1)
      (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos M) h2)
  refine ⟨n * (M + 1) ^ 3, ?_, ?_⟩
  · have h1 : 1 * (M + 1) ≤ n * (M + 1) ^ 3 :=
      Nat.mul_le_mul hn (Nat.le_self_pow (by norm_num) (M + 1))
    omega
  · have hrep := rep_lower (n * (M + 1) ^ 3)
      (s.image (fun p : ℕ × ℕ => ((M + 1) * p.1, (M + 1) * p.2))) (by
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨p0, hp0, hpe⟩ := hp
        rw [← hpe]
        have := hsum p0 hp0
        have e1 : ((M + 1) * p0.1) ^ 3 + ((M + 1) * p0.2) ^ 3 =
            (p0.1 ^ 3 + p0.2 ^ 3) * (M + 1) ^ 3 := by ring
        rw [e1, this])
    rw [Finset.card_image_of_injective _ hinj, hcard] at hrep
    omega

end OMA829

open Filter in
theorem OMA.solution : type_of% @Erdos829.variants.mordell := by
  rw [ENat.eq_top_iff_forall_ge]
  intro K
  apply Filter.le_limsup_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨N, hN, hK⟩ := OMA829.frequently_rep K M
  exact ⟨N, hN, by exact_mod_cast hK⟩
