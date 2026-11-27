import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: if no distance occurs more than n
-- times, then sum of squared multiplicities is at most B(n). Pure counting:
-- sum f = choose 2 n, f u <= n, and the fusion inequality g a + g b >= g ((a+b) % n)
-- for g x = x * (n - x) give sum f (n - f) >= g (choose 2 n % n), which is 0 for odd n
-- and n^2 / 4 for even n.

open Finset

namespace Erdos94H2

private def g (n x : ℕ) : ℕ := x * (n - x)

private lemma g_add_mod_le {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    g n ((a + b) % n) ≤ g n a + g n b := by
  rcases Nat.lt_or_ge (a + b) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    have key : ((g n (a + b) : ℕ) : ℤ) + 2 * (a : ℤ) * (b : ℤ) = ((g n a + g n b : ℕ) : ℤ) := by
      simp only [g, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub hb,
        Nat.cast_sub (Nat.le_of_lt h)]
      ring
    have hnn : (0 : ℤ) ≤ 2 * (a : ℤ) * (b : ℤ) := by positivity
    have h2 : ((g n (a + b) : ℕ) : ℤ) ≤ ((g n a + g n b : ℕ) : ℤ) := by linarith
    exact_mod_cast h2
  · have hab : a + b ≤ 2 * n := by omega
    set s := a + b - n with hs
    have hs_le : s ≤ n := by omega
    have ha_s : s ≤ a := by omega
    have hmod : (a + b) % n = s % n := by
      have : a + b = s + n := by omega
      rw [this, Nat.add_mod_right]
    have hgs : g n (s % n) = g n s := by
      rcases Nat.lt_or_ge s n with hs' | hs'
      · rw [Nat.mod_eq_of_lt hs']
      · have : s = n := by omega
        rw [this, Nat.mod_self]
        simp [g]
    rw [hmod, hgs]
    have hbz : (b : ℤ) = (n : ℤ) + s - a := by omega
    have key : ((g n s : ℕ) : ℤ) + 2 * ((n : ℤ) - a) * ((a : ℤ) - s) = ((g n a + g n b : ℕ) : ℤ) := by
      simp only [g, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub hb,
        Nat.cast_sub hs_le]
      rw [hbz]
      ring
    have h2 : ((g n s : ℕ) : ℤ) ≤ ((g n a + g n b : ℕ) : ℤ) := by
      have : (0 : ℤ) ≤ 2 * ((n : ℤ) - a) * ((a : ℤ) - s) := by
        apply mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
      linarith
    exact_mod_cast h2

private lemma sum_g_ge {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≤ n) :
    g n ((∑ i ∈ s, f i) % n) ≤ ∑ i ∈ s, g n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g]
  | insert i s hi ih =>
      have hfi : f i ≤ n := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, f j ≤ n := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi]
      have e1 : (f i + ∑ j ∈ s, f j) % n = (f i + (∑ j ∈ s, f j) % n) % n := by
        simp only [Nat.add_mod, Nat.mod_mod]
      have hmod_le : (∑ j ∈ s, f j) % n ≤ n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have h0 : ∑ j ∈ s, f j = 0 :=
            Finset.sum_eq_zero fun j hj => Nat.eq_zero_of_le_zero (hfs j hj)
          simp [h0]
        · exact Nat.le_of_lt (Nat.mod_lt _ hn)
      rw [e1]
      calc g n ((f i + (∑ j ∈ s, f j) % n) % n)
          ≤ g n (f i) + g n ((∑ j ∈ s, f j) % n) :=
            g_add_mod_le hfi hmod_le
        _ ≤ g n (f i) + ∑ j ∈ s, g n (f j) := Nat.add_le_add (le_refl _) (ih hfs)
        _ = ∑ j ∈ insert i s, g n (f j) := by rw [Finset.sum_insert hi]

private lemma choose_two_mod_two_mul (m : ℕ) : (2 * m).choose 2 % (2 * m) = m := by
  cases m with
  | zero => simp
  | succ m =>
      have h1 : (2 * (m + 1)).choose 2 = (m + 1) * (2 * m + 1) := by
        rw [Nat.choose_two_right]
        have e : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [e]
        have h2 : 2 * (m + 1) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) := by ring
        rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h1]
      have h2 : (m + 1) * (2 * m + 1) = (m + 1) + (2 * (m + 1)) * m := by ring
      rw [h2]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private lemma choose_two_mod_two_mul_add_one (m : ℕ) :
    (2 * m + 1).choose 2 % (2 * m + 1) = 0 := by
  have h1 : (2 * m + 1).choose 2 = (2 * m + 1) * m := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have h2 : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h1]
  exact Nat.mul_mod_right _ _

private lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h2 : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨n * k, by rw [hk]; ring⟩
    · have hn : n = 2 * k + 2 := by omega
      refine ⟨(k + 1) * (2 * k + 1), ?_⟩
      rw [hn]
      have e : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      rw [e]
      ring
  rw [Nat.choose_two_right, Nat.mul_div_cancel' h2]

end Erdos94H2

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  intro n P hcard hf
  have hsum : ∑ u ∈ distanceSet P, distanceMultiplicity P u = n.choose 2 := by
    rw [sum_distanceMultiplicity, hcard]
  have hsumR : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) = (n.choose 2 : ℝ) := by
    exact_mod_cast hsum
  have hg : Erdos94H2.g n (n.choose 2 % n)
      ≤ ∑ u ∈ distanceSet P, Erdos94H2.g n (distanceMultiplicity P u) := by
    have h := Erdos94H2.sum_g_ge n (distanceSet P) (distanceMultiplicity P) hf
    rwa [hsum] at h
  have hgR : (Erdos94H2.g n (n.choose 2 % n) : ℝ)
      ≤ ∑ u ∈ distanceSet P, (Erdos94H2.g n (distanceMultiplicity P u) : ℝ) := by
    exact_mod_cast hg
  have hsq : ∀ u ∈ distanceSet P, ((distanceMultiplicity P u : ℝ)) ^ 2
      = (n : ℝ) * (distanceMultiplicity P u : ℝ)
        - (Erdos94H2.g n (distanceMultiplicity P u) : ℝ) := by
    intro u hu
    have hle : distanceMultiplicity P u ≤ n := hf u hu
    have hcast : (Erdos94H2.g n (distanceMultiplicity P u) : ℝ)
        = (distanceMultiplicity P u : ℝ) * ((n : ℝ) - (distanceMultiplicity P u : ℝ)) := by
      simp only [Erdos94H2.g, Nat.cast_mul, Nat.cast_sub hle]
    rw [hcast]
    ring
  have hsplit : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2
      = (n : ℝ) * (n.choose 2 : ℝ)
        - ∑ u ∈ distanceSet P, (Erdos94H2.g n (distanceMultiplicity P u) : ℝ) := by
    calc ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2
        = ∑ u ∈ distanceSet P, ((n : ℝ) * (distanceMultiplicity P u : ℝ)
            - (Erdos94H2.g n (distanceMultiplicity P u) : ℝ)) :=
          Finset.sum_congr rfl (fun u hu => hsq u hu)
      _ = (∑ u ∈ distanceSet P, (n : ℝ) * (distanceMultiplicity P u : ℝ))
          - ∑ u ∈ distanceSet P, (Erdos94H2.g n (distanceMultiplicity P u) : ℝ) :=
          Finset.sum_sub_distrib _ _
      _ = (n : ℝ) * (n.choose 2 : ℝ)
          - ∑ u ∈ distanceSet P, (Erdos94H2.g n (distanceMultiplicity P u) : ℝ) := by
          rw [← Finset.mul_sum, hsumR]
  have hmain : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2
      ≤ (n : ℝ) * (n.choose 2 : ℝ) - (Erdos94H2.g n (n.choose 2 % n) : ℝ) := by
    rw [hsplit]
    exact sub_le_sub_left hgR _
  have hC2 : 2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    have hN := Erdos94H2.two_mul_choose_two n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      calc 2 * (n.choose 2 : ℝ) = ((2 * n.choose 2 : ℕ) : ℝ) := by norm_num
        _ = ((n * (n - 1) : ℕ) : ℝ) := by rw [hN]
        _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := Nat.cast_mul n (n - 1)
        _ = (n : ℝ) * ((n : ℝ) - 1) := by rw [hsub]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hmod : n.choose 2 % n = m := by
      rw [hm, show m + m = 2 * m by ring]
      exact Erdos94H2.choose_two_mod_two_mul m
    have hgval : (Erdos94H2.g n m : ℝ) = (m : ℝ) * ((n : ℝ) - (m : ℝ)) := by
      simp only [Erdos94H2.g, Nat.cast_mul, Nat.cast_sub (show m ≤ n by omega)]
    rw [hmod, hgval] at hmain
    rw [hm] at hmain hC2 ⊢
    have hpar : ¬ (m + m) % 2 = 1 := by omega
    rw [if_neg hpar]
    have hX : ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    nlinarith [hmain, hC2, hX]
  · have hmod : n.choose 2 % n = 0 := by
      rw [hm]; exact Erdos94H2.choose_two_mod_two_mul_add_one m
    rw [hmod] at hmain
    simp only [Erdos94H2.g, Nat.zero_mul] at hmain
    rw [hm] at hmain hC2 ⊢
    have hpar : (2 * m + 1) % 2 = 1 := by omega
    rw [if_pos hpar]
    have hX : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    nlinarith [hmain, hC2, hX]
