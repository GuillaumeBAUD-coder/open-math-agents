import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: hypothesis H2 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @OrangeHeadz
-- Pure counting. Write f(u) for the multiplicities; they sum to n (n-1) / 2 and each is at most n.
-- With g(x) = x (n - x) one has g((a + b) mod n) <= g(a) + g(b), hence
-- g((sum of f) mod n) <= sum of g(f), and sum of f^2 = n * (sum of f) - sum of g(f).

namespace OMA94H2

theorem arith (n a b : ℕ) (ha : a ≤ n) (hb : b < n) :
    ((a + b) % n) * (n - (a + b) % n) ≤ a * (n - a) + b * (n - b) := by
  rcases lt_or_ge (a + b) n with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, n = a + b + d := ⟨n - (a + b), by omega⟩
    rw [Nat.mod_eq_of_lt h]
    have e1 : a + b + d - (a + b) = d := by omega
    have e2 : a + b + d - a = b + d := by omega
    have e3 : a + b + d - b = a + d := by omega
    rw [e1, e2, e3]
    nlinarith [Nat.zero_le (a * b)]
  · obtain ⟨c, rfl⟩ : ∃ c, n = a + c := ⟨n - a, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, b = c + e := ⟨b - c, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, a = e + t := ⟨a - e, by omega⟩
    have hmod : (e + t + (c + e)) % (e + t + c) = e := by
      have : e + t + (c + e) = e + (e + t + c) := by ring
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have e1 : e + t + c - e = t + c := by omega
    have e2 : e + t + c - (e + t) = c := by omega
    have e3 : e + t + c - (c + e) = t := by omega
    rw [e1, e2, e3]
    nlinarith [Nat.zero_le (t * c)]

theorem key (n : ℕ) (hn : 0 < n) (s : Finset ℝ) (f : ℝ → ℕ) (hf : ∀ u ∈ s, f u ≤ n) :
    ((∑ u ∈ s, f u) % n) * (n - (∑ u ∈ s, f u) % n) ≤ ∑ u ∈ s, f u * (n - f u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := ih (fun u hu => hf u (Finset.mem_insert_of_mem hu))
    have h2 := arith n (f a) ((∑ u ∈ s, f u) % n) (hf a (Finset.mem_insert_self a s))
      (Nat.mod_lt _ hn)
    rw [Nat.add_mod_mod] at h2
    exact h2.trans (Nat.add_le_add_left h1 _)

end OMA94H2

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  unfold OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2
  intro n P hP hle
  have hsum : ∑ u ∈ distanceSet P, distanceMultiplicity P u = n.choose 2 := by
    rw [← hP]
    exact sum_distanceMultiplicity P
  have hsumR : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [← Nat.cast_sum, hsum, Nat.cast_choose_two]
  -- sum of f^2 = n * sum f - sum of f (n - f)
  have hsplit : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2) -
        ((∑ u ∈ distanceSet P, distanceMultiplicity P u * (n - distanceMultiplicity P u) : ℕ) : ℝ) := by
    rw [← hsumR, Finset.mul_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Nat.cast_mul, Nat.cast_sub (hle u hu)]
    ring
  rw [hsplit]
  by_cases hodd : n % 2 = 1
  · rw [if_pos hodd]
    have : (0 : ℝ) ≤
        ((∑ u ∈ distanceSet P, distanceMultiplicity P u * (n - distanceMultiplicity P u) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  · rw [if_neg hodd]
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have hk := OMA94H2.key (2 * m) (by omega) (distanceSet P) (distanceMultiplicity P) hle
      rw [hsum] at hk
      have hT : (2 * m).choose 2 % (2 * m) = m := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [Nat.choose_two_right]
        have e : 2 * (k + 1) * (2 * (k + 1) - 1) / 2 = k * (2 * (k + 1)) + (k + 1) := by
          have : 2 * (k + 1) * (2 * (k + 1) - 1) = 2 * (k * (2 * (k + 1)) + (k + 1)) := by
            have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
            rw [this]
            ring
          rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
        rw [e, Nat.mul_add_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hT] at hk
      have e2 : 2 * m - m = m := by omega
      rw [e2] at hk
      have hkR : ((m * m : ℕ) : ℝ) ≤
          ((∑ u ∈ distanceSet P, distanceMultiplicity P u * (2 * m - distanceMultiplicity P u) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hk
      push_cast at hkR ⊢
      nlinarith
