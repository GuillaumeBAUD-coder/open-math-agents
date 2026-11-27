import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-! A modular deficit bound sharpens the elementary multiplicity estimate. -/

open Finset

namespace OMA.DistanceDeficit

lemma add_bound (N a b : ℕ) (_hN : 0 < N) (ha : a ≤ N) (hb : b < N) :
    (((a + b) % N : ℕ) : ℝ) * ((N : ℝ) - ((a + b) % N : ℕ)) ≤
      (a : ℝ) * ((N : ℝ) - a) + (b : ℝ) * ((N : ℝ) - b) := by
  have ha' : (a : ℝ) ≤ N := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ N := by exact_mod_cast hb.le
  by_cases h : a + b < N
  · rw [Nat.mod_eq_of_lt h]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  · have hle : N ≤ a + b := by omega
    have hmod : (a + b) % N = a + b - N := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, Nat.cast_sub hle, Nat.cast_add]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')]

lemma sum_bound {ι : Type} (s : Finset ι) (f : ι → ℕ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ i ∈ s, f i ≤ N) :
    (((∑ i ∈ s, f i) % N : ℕ) : ℝ) *
        ((N : ℝ) - ((∑ i ∈ s, f i) % N : ℕ)) ≤
      ∑ i ∈ s, (f i : ℝ) * ((N : ℝ) - f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (mem_insert_self _ _)
    have hfs : ∀ j ∈ s, f j ≤ N := fun j hj => hf j (mem_insert_of_mem hj)
    have hsum := ih hfs
    rw [sum_insert hi, sum_insert hi]
    have hmod : (f i + ∑ j ∈ s, f j) % N =
        (f i + (∑ j ∈ s, f j) % N) % N := by
      simp only [Nat.add_mod, Nat.mod_mod]
    rw [hmod]
    exact (add_bound N (f i) ((∑ j ∈ s, f j) % N) hN hfi
      (Nat.mod_lt _ hN)).trans (add_le_add le_rfl hsum)

lemma choose_mod_even (k : ℕ) (hk : 0 < k) : (2 * k).choose 2 % (2 * k) = k := by
  have he : 2 * k * (2 * k - 1) = 2 * ((k - 1) * (2 * k) + k) := by
    have h1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have h2 : 2 * k - 1 + 1 = 2 * k := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [Nat.choose_two_right, he]
  simp [Nat.mod_eq_of_lt (by omega : k < 2 * k)]

end OMA.DistanceDeficit

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: hypothesis H2 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @DeepDuke
-- H2 := ∀ (n : ℕ) (P : Finset ℝ²), P.card = n →     (∀ u ∈ distanceSet P, distanceMultiplicity P u ≤ n) →     ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤       (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2         else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4)  -- The open core: convex n-gons in which some distance occurs more than n times.

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  classical
  intro n P hP hm
  by_cases hn : n = 0
  · have he : P = ∅ := Finset.card_eq_zero.mp (hP.trans hn)
    subst P
    simp [hn, distanceSet]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have htotal : (∑ u ∈ distanceSet P, distanceMultiplicity P u) = n.choose 2 := by
    rw [sum_distanceMultiplicity, hP]
  have htotalR : 2 * (∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    rw [← Nat.cast_sum, htotal, Nat.cast_choose_two]
    ring
  split_ifs with hodd
  · have hb : (∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2) ≤
        (n : ℝ) * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro u hu
      have hmu : (distanceMultiplicity P u : ℝ) ≤ n := by exact_mod_cast hm u hu
      nlinarith [Nat.cast_nonneg (distanceMultiplicity P u) (α := ℝ)]
    nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) htotalR]
  · have heven : n % 2 = 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero heven
    have hk : 0 < k := by omega
    have hgap := OMA.DistanceDeficit.sum_bound (distanceSet P)
      (distanceMultiplicity P) (2 * k) hnpos hm
    rw [htotal, OMA.DistanceDeficit.choose_mod_even k hk] at hgap
    have heq : (∑ u ∈ distanceSet P,
        (distanceMultiplicity P u : ℝ) * ((2 * k : ℕ) - (distanceMultiplicity P u : ℝ))) =
        (2 * k : ℝ) * (∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ)) -
          ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro u hu
      push_cast
      ring
    rw [heq] at hgap
    push_cast at hgap htotalR ⊢
    nlinarith [congrArg (fun x : ℝ => (2 * k : ℝ) * x) htotalR]

