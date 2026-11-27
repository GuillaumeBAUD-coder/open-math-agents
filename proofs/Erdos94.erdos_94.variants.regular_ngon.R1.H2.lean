import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1
import Mathlib

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: hypothesis H2 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @ivillar
--
-- Proof. Write f(u) for the multiplicities; they sum to n (n - 1) / 2 and each lies in [0, n].
-- Then sum f^2 = n * sum f - sum f (n - f). For odd n drop the last (nonnegative) sum.
-- For even n = 2k we show sum f (n - f) >= k^2: by induction over the distances there is an
-- integer q with n * |sum f - q n| <= 2 * sum f (n - f) (add f to the running sum, and move q
-- up by one when 2 f > n), while sum f - q n = k (2k - 1 - 2q) has absolute value at least k.

namespace OMA.Erdos94H2

theorem core_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ) (n : ℝ) (hn : 0 ≤ n)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ n) :
    ∃ q : ℤ, n * |∑ i ∈ s, f i - q * n| ≤ 2 * ∑ i ∈ s, f i * (n - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨q, hq⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨h0, h1⟩ := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    by_cases hm : 2 * f a ≤ n
    · refine ⟨q, ?_⟩
      have habs : |f a + ∑ i ∈ s, f i - q * n| ≤ |∑ i ∈ s, f i - q * n| + f a := by
        have := abs_add_le (∑ i ∈ s, f i - q * n) (f a)
        rw [abs_of_nonneg h0] at this
        calc |f a + ∑ i ∈ s, f i - q * n| = |(∑ i ∈ s, f i - q * n) + f a| := by
              congr 1; ring
          _ ≤ _ := this
      have h2 := mul_le_mul_of_nonneg_left habs hn
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr hm)]
    · refine ⟨q + 1, ?_⟩
      push_neg at hm
      have habs : |f a + ∑ i ∈ s, f i - ((q + 1 : ℤ) : ℝ) * n| ≤
          |∑ i ∈ s, f i - q * n| + (n - f a) := by
        have := abs_add_le (∑ i ∈ s, f i - q * n) (f a - n)
        rw [abs_sub_comm (f a) n, abs_of_nonneg (sub_nonneg.mpr h1)] at this
        calc |f a + ∑ i ∈ s, f i - ((q + 1 : ℤ) : ℝ) * n|
            = |(∑ i ∈ s, f i - q * n) + (f a - n)| := by
              congr 1; push_cast; ring
          _ ≤ _ := this
      have h2 := mul_le_mul_of_nonneg_left habs hn
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0:ℝ) ≤ 2 * f a - n)]

end OMA.Erdos94H2

open EuclideanGeometry Erdos94 in
theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  unfold OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2
  intro n P hP hle
  have hsum : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [← Nat.cast_sum, sum_distanceMultiplicity P, hP, Nat.cast_choose_two]
  have hf : ∀ u ∈ distanceSet P, 0 ≤ (distanceMultiplicity P u : ℝ) ∧
      (distanceMultiplicity P u : ℝ) ≤ n :=
    fun u hu => ⟨Nat.cast_nonneg _, by exact_mod_cast hle u hu⟩
  have hsq : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 =
      n * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) -
        ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) * (n - distanceMultiplicity P u) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  have hX0 : 0 ≤ ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) * (n - distanceMultiplicity P u) :=
    Finset.sum_nonneg (fun u hu => mul_nonneg (hf u hu).1 (sub_nonneg.mpr (hf u hu).2))
  obtain ⟨q, hq⟩ := OMA.Erdos94H2.core_aux (distanceSet P)
    (fun u => (distanceMultiplicity P u : ℝ)) n (Nat.cast_nonneg n) hf
  beta_reduce at hq
  set X := ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) * (n - distanceMultiplicity P u)
    with hXdef
  set T := ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) with hTdef
  rw [hsq, hsum]
  split_ifs with hodd
  · nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have hkR : (n : ℝ) = 2 * k := by exact_mod_cast hk
    have hz : (k : ℝ) ≤ |T - q * n| := by
      rw [hsum, hkR]
      have h1 : (1 : ℤ) ≤ |2 * (k : ℤ) - 1 - 2 * q| := Int.one_le_abs (by omega)
      have h2 : (1 : ℝ) ≤ |((2 * (k : ℤ) - 1 - 2 * q : ℤ) : ℝ)| := by
        have := (Int.cast_le (R := ℝ)).mpr h1
        rw [Int.cast_abs] at this
        simpa using this
      push_cast at h2
      have h3 : (2 * (k : ℝ)) * (2 * k - 1) / 2 - q * (2 * k) = k * (2 * k - 1 - 2 * q) := by ring
      rw [h3, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h4 := le_trans (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg (α := ℝ) n)) hq
    rw [hkR] at h4 ⊢
    nlinarith
