import OMAStatements.S_oeis_a003067

-- Problem: A003067: Problimes (second definition).
-- Upstream: formal-conjectures statements/oeis-a003067.lean:0 (declaration OMA.S_oeis_a003067.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: compute st 0, ..., st 20 step by step (each step: the rounding by Int.floor_eq_iff
-- and the new running product, both by norm_num on explicit rationals). This gives a(19) = 79,
-- a(20) = 84, a(21) = 90. The coefficient of X^20 in (sum a(n+1) X^n) * (X - 1)^2 is
-- a(19) - 2 a(20) + a(21) = 1, while that of X^2 + 2 + X^9 + X^5 is 0.

open OMA.S_oeis_a003067 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003067.main := by
  have step : ∀ (k k' : ℕ) (A : ℤ) (P : ℚ) (v : ℤ) (P' : ℚ), k + 1 = k' → st k = (A, P) →
      (v : ℚ) ≤ (A : ℚ) + 1 / P + 1 / 2 → (A : ℚ) + 1 / P + 1 / 2 < (v : ℚ) + 1 →
      P * (1 - 1 / (v : ℚ)) = P' → st k' = (v, P') := by
    intro k k' A P v P' hk h h1 h2 h3
    subst hk
    have hr : round ((A : ℚ) + 1 / P) = v := by
      rw [round_eq, Int.floor_eq_iff]
      exact ⟨h1, h2⟩
    have e : st (k + 1) = (round (((st k).1 : ℚ) + 1 / (st k).2),
        (st k).2 * (1 - 1 / ((round (((st k).1 : ℚ) + 1 / (st k).2) : ℤ) : ℚ))) := rfl
    rw [e, h]
    simp only [hr, h3]
  have s0 : st 0 = (2, 1 / 2) := rfl
  have s1 : st 1 = (4, 3 / 8) :=
    step 0 1 2 (1 / 2) 4 (3 / 8) rfl s0 (by norm_num) (by norm_num) (by norm_num)
  have s2 : st 2 = (7, 9 / 28) :=
    step 1 2 4 (3 / 8) 7 (9 / 28) rfl s1 (by norm_num) (by norm_num) (by norm_num)
  have s3 : st 3 = (10, 81 / 280) :=
    step 2 3 7 (9 / 28) 10 (81 / 280) rfl s2 (by norm_num) (by norm_num) (by norm_num)
  have s4 : st 4 = (13, 243 / 910) :=
    step 3 4 10 (81 / 280) 13 (243 / 910) rfl s3 (by norm_num) (by norm_num) (by norm_num)
  have s5 : st 5 = (17, 1944 / 7735) :=
    step 4 5 13 (243 / 910) 17 (1944 / 7735) rfl s4 (by norm_num) (by norm_num) (by norm_num)
  have s6 : st 6 = (21, 2592 / 10829) :=
    step 5 6 17 (1944 / 7735) 21 (2592 / 10829) rfl s5 (by norm_num) (by norm_num) (by norm_num)
  have s7 : st 7 = (25, 62208 / 270725) :=
    step 6 7 21 (2592 / 10829) 25 (62208 / 270725) rfl s6 (by norm_num) (by norm_num) (by norm_num)
  have s8 : st 8 = (29, 248832 / 1121575) :=
    step 7 8 25 (62208 / 270725) 29 (248832 / 1121575) rfl s7 (by norm_num) (by norm_num) (by norm_num)
  have s9 : st 9 = (34, 4105728 / 19066775) :=
    step 8 9 29 (248832 / 1121575) 34 (4105728 / 19066775) rfl s8 (by norm_num) (by norm_num) (by norm_num)
  have s10 : st 10 = (39, 52005888 / 247868075) :=
    step 9 10 34 (4105728 / 19066775) 39 (52005888 / 247868075) rfl s9 (by norm_num) (by norm_num) (by norm_num)
  have s11 : st 11 = (44, 50823936 / 247868075) :=
    step 10 11 39 (52005888 / 247868075) 44 (50823936 / 247868075) rfl s10 (by norm_num) (by norm_num) (by norm_num)
  have s12 : st 12 = (49, 2439548928 / 12145535675) :=
    step 11 12 44 (50823936 / 247868075) 49 (2439548928 / 12145535675) rfl s11 (by norm_num) (by norm_num) (by norm_num)
  have s13 : st 13 = (54, 2394372096 / 12145535675) :=
    step 12 13 49 (2439548928 / 12145535675) 54 (2394372096 / 12145535675) rfl s12 (by norm_num) (by norm_num) (by norm_num)
  have s14 : st 14 = (59, 4788744192 / 24709882925) :=
    step 13 14 54 (2394372096 / 12145535675) 59 (4788744192 / 24709882925) rfl s13 (by norm_num) (by norm_num) (by norm_num)
  have s15 : st 15 = (64, 673417152 / 3529983275) :=
    step 14 15 59 (4788744192 / 24709882925) 64 (673417152 / 3529983275) rfl s14 (by norm_num) (by norm_num) (by norm_num)
  have s16 : st 16 = (69, 897889536 / 4775859725) :=
    step 15 16 64 (673417152 / 3529983275) 69 (897889536 / 4775859725) rfl s15 (by norm_num) (by norm_num) (by norm_num)
  have s17 : st 17 = (74, 32772968064 / 176706809825) :=
    step 16 17 69 (897889536 / 4775859725) 74 (32772968064 / 176706809825) rfl s16 (by norm_num) (by norm_num) (by norm_num)
  have s18 : st 18 = (79, 196637808384 / 1073833690475) :=
    step 17 18 74 (32772968064 / 176706809825) 79 (196637808384 / 1073833690475) rfl s17 (by norm_num) (by norm_num) (by norm_num)
  have s19 : st 19 = (84, 1360078174656 / 7516835833325) :=
    step 18 19 79 (196637808384 / 1073833690475) 84 (1360078174656 / 7516835833325) rfl s18 (by norm_num) (by norm_num) (by norm_num)
  have s20 : st 20 = (90, 6724830974688 / 37584179166625) :=
    step 19 20 84 (1360078174656 / 7516835833325) 90 (6724830974688 / 37584179166625) rfl s19 (by norm_num) (by norm_num) (by norm_num)
  have a19 : a 19 = 79 := by
    show (st 18).1 = 79
    rw [s18]
  have a20 : a 20 = 84 := by
    show (st 19).1 = 84
    rw [s19]
  have a21 : a 21 = 90 := by
    show (st 20).1 = 90
    rw [s20]
  intro h
  have eL : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (PowerSeries.X - 1) ^ 2 =
      PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 2 -
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 1) +
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have eR : (PowerSeries.X ^ 2 + 2 + PowerSeries.X ^ 9 + PowerSeries.X ^ 5 : PowerSeries ℚ) =
      PowerSeries.X ^ 2 + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 + PowerSeries.X ^ 9 +
        PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
  rw [eL, eR] at h
  have h20 := congrArg (fun p : PowerSeries ℚ => PowerSeries.coeff 20 p) h
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow] at h20
  norm_num [a19, a20, a21] at h20
