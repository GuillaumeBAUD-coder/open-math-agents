import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: hypothesis H2 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @carterleffen
-- The counting argument follows the sketch in the reduction by @OrangeHeadz.
-- The multiplicities f(u) sum to n(n-1)/2 (sum_distanceMultiplicity, Formal Conjectures).
-- Odd n: each f(u) is at most n, so the sum of f(u)^2 is at most n times the sum of f(u).
-- Even n: write f = e + c with c in {0, n} and |e| at most n/2. Then f^2 is at most
-- n f - (n/2)|e|, and the sum of e is n(n-1)/2 - nK, of absolute value at least n/2.

namespace OMA.Erdos94H2

/-- A multiplicity between 0 and n, reduced modulo n to the nearest residue. -/
lemma pointwise (n F : ℝ) (h0 : 0 ≤ F) (h1 : F ≤ n) :
    F ^ 2 ≤ n * F - n / 2 * |F - (if 2 * F ≤ n then 0 else n)| := by
  split_ifs with h
  · rw [sub_zero, abs_of_nonneg h0]
    nlinarith
  · rw [abs_of_nonpos (by linarith)]
    nlinarith

/-- An integer multiple of an odd integer: the distance from n(n-1)/2 to nZ is at least n/2. -/
lemma far (t K : ℕ) :
    (t : ℝ) ≤ |(2 * t : ℝ) * (2 * t - 1) / 2 - 2 * t * K| := by
  have hz : (1 : ℤ) ≤ |(2 * (t : ℤ) - 1 - 2 * K)| := by
    rcases le_or_gt 0 (2 * (t : ℤ) - 1 - 2 * K) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have hr : (1 : ℝ) ≤ |(2 * (t : ℝ) - 1 - 2 * K)| := by exact_mod_cast hz
  have he : (2 * t : ℝ) * (2 * t - 1) / 2 - 2 * t * K = t * (2 * t - 1 - 2 * K) := by ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg t)]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

end OMA.Erdos94H2

open OMA.Erdos94H2 in
theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  intro n P hP hle
  set D := distanceSet P with hD
  have hsum : ∑ u ∈ D, (distanceMultiplicity P u : ℝ) = n * (n - 1) / 2 := by
    have h := sum_distanceMultiplicity P
    rw [hP] at h
    rw [← Nat.cast_choose_two ℝ n, ← h, Nat.cast_sum]
  have hF0 : ∀ u ∈ D, (0 : ℝ) ≤ distanceMultiplicity P u := fun u _ => Nat.cast_nonneg _
  have hFn : ∀ u ∈ D, (distanceMultiplicity P u : ℝ) ≤ n := fun u hu => by
    exact_mod_cast hle u hu
  split_ifs with hpar
  · calc ∑ u ∈ D, (distanceMultiplicity P u : ℝ) ^ 2
        ≤ ∑ u ∈ D, (n : ℝ) * distanceMultiplicity P u := by
          apply Finset.sum_le_sum
          intro u hu
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hFn u hu) (hF0 u hu)
      _ = (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2 := by
          rw [← Finset.mul_sum, hsum]
          ring
  · obtain ⟨t, ht⟩ : ∃ t, n = 2 * t := ⟨n / 2, by omega⟩
    let c : ℝ → ℝ := fun F => if 2 * F ≤ n then 0 else n
    have hc : ∑ u ∈ D, c (distanceMultiplicity P u) =
        (n : ℝ) * ((D.filter fun u => ¬ 2 * (distanceMultiplicity P u : ℝ) ≤ n).card : ℕ) := by
      simp only [c]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_comm]
    set K := (D.filter fun u => ¬ 2 * (distanceMultiplicity P u : ℝ) ≤ n).card
    have h1 : ∑ u ∈ D, (distanceMultiplicity P u : ℝ) ^ 2 ≤
        ∑ u ∈ D, ((n : ℝ) * distanceMultiplicity P u -
          n / 2 * |(distanceMultiplicity P u : ℝ) - c (distanceMultiplicity P u)|) :=
      Finset.sum_le_sum fun u hu => pointwise n _ (hF0 u hu) (hFn u hu)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum] at h1
    have h2 : |∑ u ∈ D, ((distanceMultiplicity P u : ℝ) - c (distanceMultiplicity P u))| ≤
        ∑ u ∈ D, |(distanceMultiplicity P u : ℝ) - c (distanceMultiplicity P u)| :=
      Finset.abs_sum_le_sum_abs _ _
    rw [Finset.sum_sub_distrib, hsum, hc] at h2
    have h3 := far t K
    have hn : (n : ℝ) = 2 * t := by exact_mod_cast ht
    rw [hn] at h1 h2
    rw [hn]
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith [mul_le_mul_of_nonneg_left (h3.trans h2) ht0]
