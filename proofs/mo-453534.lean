import OMAStatements.S_mo_453534

-- Problem mo-453534: the statement claims that for every Euclidean degree function deg on an integral domain
-- (division with remainder, and deg a <= deg (a * b)), every division a = b * q + r can be chosen so that also
-- a - r = 0 or deg (a - r) <= deg a.
-- Upstream: statements/mo-453534.lean (declaration OMA.S_mo_453534.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: on the integers let deg n = |n| except deg 2 = deg (-2) = 3. This is a Euclidean degree
-- function: the balanced remainder r with 2 * |r| <= |b| always has r = 0 or deg r < deg b, and
-- deg a <= deg (a * b) holds. Now divide a = 5 by b = 3. A remainder needs r = 0 or deg r < 3, which forces
-- r in {-1, 0, 1}, and 5 - r must be a multiple of 3, so r = -1 and q = 2. But then a - r = 6 is not 0 and
-- deg 6 = 6 > 5 = deg 5.

open OMA.S_mo_453534

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_453534.main) := by
  intro h
  obtain ⟨dgf, hdg⟩ : ∃ f : ℤ → ℕ, ∀ n, f n = if n.natAbs = 2 then 3 else n.natAbs :=
    ⟨fun n => if n.natAbs = 2 then 3 else n.natAbs, fun n => rfl⟩
  have hE : IsEuclideanDegree dgf := by
    constructor
    · intro a b hb
      have hm0 : 0 ≤ a % b := Int.emod_nonneg a hb
      have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
      rcases lt_or_gt_of_ne hb with hneg | hpos
      · have hm1 : a % b < -b := by
          have h0 := Int.emod_lt_of_pos a (neg_pos.mpr hneg)
          rwa [Int.emod_neg] at h0
        by_cases hc : 2 * (a % b) ≤ -b
        · refine ⟨a / b, a % b, by linarith, Or.inr ?_⟩
          rw [hdg, hdg]
          split_ifs <;> omega
        · refine ⟨a / b - 1, a % b + b, by linarith, Or.inr ?_⟩
          rw [hdg, hdg]
          split_ifs <;> omega
      · have hm1 : a % b < b := Int.emod_lt_of_pos a hpos
        by_cases hc : 2 * (a % b) ≤ b
        · refine ⟨a / b, a % b, by linarith, Or.inr ?_⟩
          rw [hdg, hdg]
          split_ifs <;> omega
        · refine ⟨a / b + 1, a % b - b, by linarith, Or.inr ?_⟩
          rw [hdg, hdg]
          split_ifs <;> omega
    · intro a b ha hb
      have hab : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
      have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb
      have hle : a.natAbs ≤ (a * b).natAbs := by
        rw [hab]
        exact Nat.le_mul_of_pos_right _ hb1
      rw [hdg, hdg]
      by_cases h1 : a.natAbs = 2
      · have h2 : (a * b).natAbs = 2 * b.natAbs := by rw [hab, h1]
        rw [if_pos h1]
        split_ifs <;> omega
      · rw [if_neg h1]
        split_ifs <;> omega
  obtain ⟨q, r, h1, h2, h3⟩ := h ℤ dgf hE 5 3 (by norm_num)
  have e3 : dgf 3 = 3 := by
    rw [hdg]
    decide
  have e5 : dgf 5 = 5 := by
    rw [hdg]
    decide
  rw [e3, hdg] at h2
  rw [e5, hdg] at h3
  have hr : r = -1 := by
    rcases h2 with h2 | h2
    · omega
    · split_ifs at h2 <;> omega
  subst hr
  revert h3
  decide
