import OMAReductions.R_oeis_a303233_R1

-- Step oeis-a303233.R1.H1: hypothesis H1 of reduction oeis-a303233.R1
-- Credit: @nnkostov

/-!
We characterize when `m = n - (2^c + 2^d)` is a sum of two triangular numbers:
`m = a(a+1)/2 + b(b+1)/2` holds iff `4m + 1 = (a + b + 1)^2 + (a - b)^2` is a
sum of two squares, which by Fermat's theorem on sums of two squares holds iff
every prime `q ≡ 3 (mod 4)` has even `q`-adic valuation in `4m + 1`.
-/

private lemma two_mul_tri (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
  Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))

theorem OMA.solution : OMA.R_oeis_a303233_R1.H1 := by
  intro n c d hle
  dsimp only
  set m := n - (2 ^ c + 2 ^ d)
  rw [← Nat.eq_sq_add_sq_iff]
  constructor
  · rintro ⟨a, b, hab⟩
    have hm : a * (a + 1) / 2 + b * (b + 1) / 2 = m := by omega
    have ha := two_mul_tri a
    have hb := two_mul_tri b
    have h4m : 4 * m = 2 * (a * (a + 1)) + 2 * (b * (b + 1)) := by omega
    by_cases hba : b ≤ a
    · refine ⟨a + b + 1, a - b, ?_⟩
      zify [hba] at h4m ⊢
      calc
        4 * (m : ℤ) + 1 = 2 * ((a : ℤ) * (↑a + 1)) + 2 * ((b : ℤ) * (↑b + 1)) + 1 := by
          rw [h4m]
        _ = ((a : ℤ) + ↑b + 1) ^ 2 + ((a : ℤ) - ↑b) ^ 2 := by ring
    · have hab_le : a ≤ b := by omega
      refine ⟨a + b + 1, b - a, ?_⟩
      zify [hab_le] at h4m ⊢
      calc
        4 * (m : ℤ) + 1 = 2 * ((a : ℤ) * (↑a + 1)) + 2 * ((b : ℤ) * (↑b + 1)) + 1 := by
          rw [h4m]
        _ = ((a : ℤ) + ↑b + 1) ^ 2 + ((b : ℤ) - ↑a) ^ 2 := by ring
  · rintro ⟨x, y, hxy⟩
    set u := max x y
    set v := min x y
    have hvu : v ≤ u := min_le_max
    have huv : 4 * m + 1 = u ^ 2 + v ^ 2 := by
      rcases le_total x y with h | h
      · simpa [u, v, h, add_comm] using hxy
      · simpa [u, v, h] using hxy
    have hpar : u % 2 ≠ v % 2 := by
      intro heq
      have hmod : (4 * m + 1) % 2 = (u ^ 2 + v ^ 2) % 2 := congrArg (· % 2) huv
      have h1 : (4 * m + 1) % 2 = 1 := by omega
      have h2 : (u ^ 2 + v ^ 2) % 2 = 0 := by
        rw [Nat.add_mod, sq, sq, Nat.mul_mod u u, Nat.mul_mod v v, ← heq]
        rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h]
      omega
    have hvlt : v < u := by omega
    set a := (u + v - 1) / 2
    set b := (u - v - 1) / 2
    have ha_eq : 2 * a + 1 = u + v := by omega
    have hb_eq : 2 * b + 1 = u - v := by omega
    set ta := a * (a + 1) / 2
    set tb := b * (b + 1) / 2
    have ha : 2 * ta = a * (a + 1) := two_mul_tri a
    have hb : 2 * tb = b * (b + 1) := two_mul_tri b
    have hsum : ta + tb = m := by
      have hz : 8 * (ta : ℤ) + 8 * (tb : ℤ) + 2 = 8 * (m : ℤ) + 2 := by
        have ha_z : 2 * (ta : ℤ) = (a : ℤ) * ((a : ℤ) + 1) := by exact_mod_cast ha
        have hb_z : 2 * (tb : ℤ) = (b : ℤ) * ((b : ℤ) + 1) := by exact_mod_cast hb
        have ha' : (2 * (a : ℤ) + 1) ^ 2 = 8 * (ta : ℤ) + 1 := by
          calc
            (2 * (a : ℤ) + 1) ^ 2 = 4 * ((a : ℤ) * ((a : ℤ) + 1)) + 1 := by ring
            _ = 4 * (2 * (ta : ℤ)) + 1 := by rw [← ha_z]
            _ = 8 * (ta : ℤ) + 1 := by ring
        have hb' : (2 * (b : ℤ) + 1) ^ 2 = 8 * (tb : ℤ) + 1 := by
          calc
            (2 * (b : ℤ) + 1) ^ 2 = 4 * ((b : ℤ) * ((b : ℤ) + 1)) + 1 := by ring
            _ = 4 * (2 * (tb : ℤ)) + 1 := by rw [← hb_z]
            _ = 8 * (tb : ℤ) + 1 := by ring
        have ha_eq_z : 2 * (a : ℤ) + 1 = (u : ℤ) + (v : ℤ) := by exact_mod_cast ha_eq
        have hb_eq_z : 2 * (b : ℤ) + 1 = (u : ℤ) - (v : ℤ) := by
          zify [hvu] at hb_eq ⊢
          exact hb_eq
        have huv_z : 4 * (m : ℤ) + 1 = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by exact_mod_cast huv
        calc
          8 * (ta : ℤ) + 8 * (tb : ℤ) + 2
              = (2 * (a : ℤ) + 1) ^ 2 + (2 * (b : ℤ) + 1) ^ 2 := by linarith
          _ = ((u : ℤ) + (v : ℤ)) ^ 2 + ((u : ℤ) - (v : ℤ)) ^ 2 := by rw [ha_eq_z, hb_eq_z]
          _ = 2 * ((u : ℤ) ^ 2 + (v : ℤ) ^ 2) := by ring
          _ = 2 * (4 * (m : ℤ) + 1) := by rw [← huv_z]
          _ = 8 * (m : ℤ) + 2 := by ring
      omega
    refine ⟨a, b, ?_⟩
    change ta + tb + 2 ^ c + 2 ^ d = n
    omega
