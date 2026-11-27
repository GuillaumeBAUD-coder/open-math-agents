import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-!
# Proof of `Erdos94.erdos_94.variants.regular_ngon.R1.H2`

For any `n`-point set `P ⊆ ℝ²` in which every distance occurs at most `n` times,
the sum of squared distance multiplicities is at most `B(n)`, where
`B(n) = n^2 (n - 1) / 2` for odd `n` and `B(n) = n^3 / 2 - 3 n^2 / 4` for even `n`.
-/

open EuclideanGeometry

namespace Erdos94R1H2Proof

private lemma subadd_mod (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    ((a + b) % n) * (n - (a + b) % n) ≤ a * (n - a) + b * (n - b) := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hlt : a + b < 2 * n ∨ a + b = 2 * n := by omega
    rcases hlt with hlt | heq
    · by_cases hsum : a + b < n
      · rw [Nat.mod_eq_of_lt hsum]
        zify [ha, hb, le_of_lt hsum]
        nlinarith
      · have hmod : (a + b) % n = a + b - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have hle1 : a + b - n ≤ n := by omega
        zify [ha, hb, hle1]
        have h1 : ((a + b - n : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) - (n : ℤ) := by omega
        rw [h1]
        nlinarith
    · rw [heq, Nat.mul_mod_left]
      simp

private lemma sum_mul_sub_ge_mod {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α)
    (f : α → ℕ) (hf : ∀ u ∈ S, f u ≤ n) :
    ((∑ u ∈ S, f u) % n) * (n - (∑ u ∈ S, f u) % n) ≤ ∑ u ∈ S, f u * (n - f u) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hfx : f x ≤ n := hf x (Finset.mem_insert_self x s)
    have hfs : ∀ u ∈ s, f u ≤ n := fun u hu => hf u (Finset.mem_insert_of_mem hu)
    have ihs := ih hfs
    by_cases hn : n = 0
    · subst hn; simp
    · have hmod_le : (∑ u ∈ s, f u) % n ≤ n := le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
      have hmod_eq : (f x + ∑ u ∈ s, f u) % n = (f x + (∑ u ∈ s, f u) % n) % n :=
        (Nat.add_mod_mod (f x) (∑ u ∈ s, f u) n).symm
      rw [hmod_eq]
      exact (subadd_mod n (f x) ((∑ u ∈ s, f u) % n) hfx hmod_le).trans (Nat.add_le_add_left ihs _)

private lemma choose_two_mod_even (m : ℕ) (hm : 1 ≤ m) :
    (2 * m).choose 2 % (2 * m) = m := by
  have hch : (2 * m).choose 2 = (m - 1) * (2 * m) + m := by
    rw [Nat.choose_two_right]
    have h1 : 2 * m * (2 * m - 1) = 2 * ((m - 1) * (2 * m) + m) := by
      zify [hm, show 1 ≤ 2 * m by omega]
      ring
    omega
  rw [hch, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

end Erdos94R1H2Proof

open Erdos94R1H2Proof in
theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  intro n P hP hle
  have hsum_nat : ∑ u ∈ distanceSet P, distanceMultiplicity P u = n.choose 2 := by
    rw [sum_distanceMultiplicity, hP]
  have hsum_real : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have hcast : (∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ)) = (n.choose 2 : ℝ) := by
      exact_mod_cast hsum_nat
    rw [hcast, Nat.cast_choose_two]
  split_ifs with hodd
  · calc
      ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2
          ≤ ∑ u ∈ distanceSet P, (n : ℝ) * (distanceMultiplicity P u : ℝ) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have h1 : (distanceMultiplicity P u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (hle u hu)
            have h0 : (0 : ℝ) ≤ (distanceMultiplicity P u : ℝ) := Nat.cast_nonneg _
            nlinarith
      _ = (n : ℝ) * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) := by
            rw [← Finset.mul_sum]
      _ = (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2 := by
            rw [hsum_real]; ring
  · have heven : n % 2 = 0 := by omega
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · have hPe : P = ∅ := Finset.card_eq_zero.mp hP
      subst hPe
      simp [distanceSet]
    · obtain ⟨m, hm_eq⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hm_pos : 1 ≤ m := by omega
      have hsub_nat : m * m ≤
          ∑ u ∈ distanceSet P, distanceMultiplicity P u * (n - distanceMultiplicity P u) := by
        have h1 := sum_mul_sub_ge_mod n (distanceSet P) (distanceMultiplicity P) hle
        rw [hsum_nat, hm_eq, choose_two_mod_even m hm_pos] at h1
        have h2 : 2 * m - m = m := by omega
        rw [h2] at h1
        simpa [hm_eq] using h1
      have hsub_real : ((n : ℝ) ^ 2 / 4) ≤
          ∑ u ∈ distanceSet P,
            ((distanceMultiplicity P u : ℝ) * ((n : ℝ) - (distanceMultiplicity P u : ℝ))) := by
        have hcast : ((m * m : ℕ) : ℝ) ≤
            (∑ u ∈ distanceSet P,
              (distanceMultiplicity P u * (n - distanceMultiplicity P u) : ℕ) : ℝ) := by
          exact_mod_cast hsub_nat
        have hsum_eq :
            (∑ u ∈ distanceSet P,
              ((distanceMultiplicity P u * (n - distanceMultiplicity P u) : ℕ) : ℝ)) =
            ∑ u ∈ distanceSet P,
              ((distanceMultiplicity P u : ℝ) * ((n : ℝ) - (distanceMultiplicity P u : ℝ))) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [Nat.cast_mul, Nat.cast_sub (hle u hu)]
        rw [hsum_eq] at hcast
        have hm_real : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hm_eq
        have hlhs : ((m * m : ℕ) : ℝ) = (n : ℝ) ^ 2 / 4 := by
          push_cast; rw [hm_real]; ring
        linarith
      have hident :
          ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 =
            (n : ℝ) * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) -
            ∑ u ∈ distanceSet P,
              ((distanceMultiplicity P u : ℝ) * ((n : ℝ) - (distanceMultiplicity P u : ℝ))) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun u _ => by ring
      rw [hident, hsum_real]
      linarith
