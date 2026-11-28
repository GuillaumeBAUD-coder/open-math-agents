import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3

-- Step H1 of reduction AgohGiuga.agoh_giuga.variants.giuga.R3: from q D + m = m q k + 1 with
-- m, q > 1, the residue r = D mod m satisfies q (m - r) = m - 1.
-- Writing D = m t + r gives q r + m - 1 = m q (k - t); the left side lies in [m - 1, (q+1)(m-1)],
-- which forces k - t = 1.
-- Credit: @GiridhariPradeep (agent: Claude Code)

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3.H1 := by
  intro m D q k hm hq h
  have hr : D % m < m := Nat.mod_lt _ (by omega)
  have hD : m * (D / m) + D % m = D := Nat.div_add_mod D m
  set r := D % m with hrdef
  set t := D / m with htdef
  -- q r + m - 1 = m q (k - t), over ℤ
  have key : (q : ℤ) * r + m - 1 = (m : ℤ) * q * ((k : ℤ) - t) := by
    have h' : (q : ℤ) * D + m = (m : ℤ) * q * k + 1 := by exact_mod_cast h
    have hD' : (m : ℤ) * t + r = D := by exact_mod_cast hD
    rw [← hD'] at h'
    linarith
  set u : ℤ := (k : ℤ) - t with hu
  have hmz : (1 : ℤ) < m := by exact_mod_cast hm
  have hqz : (1 : ℤ) < q := by exact_mod_cast hq
  have hrz : (r : ℤ) < m := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hu1 : 1 ≤ u := by
    by_contra hc
    push_neg at hc
    have : u ≤ 0 := by omega
    have : (m : ℤ) * q * u ≤ 0 := by
      have : (0 : ℤ) ≤ (m : ℤ) * q := by positivity
      nlinarith
    nlinarith
  have hu2 : u ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : (2 : ℤ) ≤ u := by omega
    have : (m : ℤ) * q * 2 ≤ (m : ℤ) * q * u := by
      have : (0 : ℤ) ≤ (m : ℤ) * q := by positivity
      nlinarith
    nlinarith
  have hu' : u = 1 := le_antisymm hu2 hu1
  rw [hu', mul_one] at key
  have hle : r ≤ m := hr.le
  zify [hle, (by omega : 1 ≤ m)]
  linarith
