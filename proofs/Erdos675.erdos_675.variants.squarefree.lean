import FormalConjectures.ErdosProblems.«675»

/-! Preserve the small prime squares by a common period and count the large-square exceptions. -/

lemma OMA.square_shift_bad_card (M a p K : ℕ) (hp : Nat.Prime p) (hc : (p * p).Coprime M) :
    (((Finset.Icc 1 K).filter (fun k => p * p ∣ a + M * k)).card : ℝ) ≤
      (K : ℝ) / (p : ℝ) ^ 2 + 1 := by
  let S := (Finset.Icc 1 K).filter fun k => p * p ∣ a + M * k
  have hcard : S.card ≤ (Finset.range (K / (p * p) + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / (p * p))
    · intro k hk
      have hkS : k ∈ S := hk
      have hle := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkS).1).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hle))
    · intro k hk l hl heq
      have hkS : k ∈ S := hk
      have hlS : l ∈ S := hl
      have hk' := (Finset.mem_filter.mp hkS).2
      have hl' := (Finset.mem_filter.mp hlS).2
      have hmod : k ≡ l [MOD p * p] := by
        apply Nat.ModEq.cancel_left_of_coprime hc
        exact Nat.ModEq.add_left_cancel' a (hk'.modEq_zero_nat.trans hl'.zero_modEq_nat)
      have hrem : k % (p * p) = l % (p * p) := hmod
      change k / (p * p) = l / (p * p) at heq
      calc
        k = k % (p * p) + (p * p) * (k / (p * p)) := (Nat.mod_add_div _ _).symm
        _ = l % (p * p) + (p * p) * (l / (p * p)) := by rw [hrem, heq]
        _ = l := Nat.mod_add_div _ _
  rw [Finset.card_range] at hcard
  have hcard' : (S.card : ℝ) ≤ ((K / (p * p) : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  have hdiv : ((K / (p * p) : ℕ) : ℝ) ≤ (K : ℝ) / (p : ℝ) ^ 2 := by
    have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply (le_div_iff₀ (pow_pos hpos 2)).mpr
    rw [pow_two]
    exact_mod_cast (Nat.div_mul_le_self K (p * p))
  exact hcard'.trans (add_le_add hdiv le_rfl)

theorem OMA.solution : type_of% @Erdos675.erdos_675.variants.squarefree := by
  classical
  intro n
  let P : ℕ := 4 * (n + 1)
  let M : ℕ := P.factorial ^ 2
  let Q : ℕ := M + n + 1
  let R : ℕ := P * Q
  let K : ℕ := R ^ 2
  let J : ℕ := Q * R
  have hP : 0 < P := by dsimp only [P]; positivity
  have hM : 0 < M := pow_pos (Nat.factorial_pos _) 2
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hR : 0 < R := Nat.mul_pos hP hQ
  have hK : 0 < K := pow_pos hR 2
  have hPJ : P ≤ J := (Nat.le_mul_of_pos_right P hQ).trans (Nat.le_mul_of_pos_left R hQ)
  let Ps := (Finset.Ioc P J).filter Nat.Prime
  let As := Finset.Icc 1 n
  let Ks := Finset.Icc 1 K
  let bad (p a : ℕ) := Ks.filter fun k => p * p ∣ a + M * k
  let badFor (p : ℕ) := As.biUnion (bad p)
  let badAll := Ps.biUnion badFor
  let bound (p : ℕ) : ℝ := (K : ℝ) / (p : ℝ) ^ 2 + 1
  have hprime_sum : ∑ p ∈ Ps, bound p ≤ (K : ℝ) / P + J := by
    have htail : (∑ p ∈ Ps, ((p : ℝ) ^ 2)⁻¹) ≤ (P : ℝ)⁻¹ := by
      calc
        _ ≤ ∑ p ∈ Finset.Ioc P J, ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
        _ ≤ (P : ℝ)⁻¹ - (J : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hP.ne' hPJ
        _ ≤ _ := sub_le_self _ (by positivity)
    have hcard : Ps.card ≤ J := by
      have hs := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Ioc P J))
      rw [Nat.card_Ioc] at hs
      exact hs.trans (Nat.sub_le _ _)
    calc
      (∑ p ∈ Ps, bound p) = (K : ℝ) * (∑ p ∈ Ps, ((p : ℝ) ^ 2)⁻¹) + Ps.card := by
        simp only [bound, div_eq_mul_inv, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (K : ℝ) / P + J := by
        rw [div_eq_mul_inv]
        exact add_le_add (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _))
          (by exact_mod_cast hcard)
  have hbadFor (p : ℕ) (hp : p ∈ Ps) : ((badFor p).card : ℝ) ≤ (n : ℝ) * bound p := by
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    have hpP := (Finset.mem_Ioc.mp hpI).1
    have hcop : (p * p).Coprime M := by
      simpa only [pow_two, M] using ((hprime.coprime_factorial_of_lt hpP).pow_left 2).pow_right 2
    calc
      _ ≤ ∑ a ∈ As, ((bad p a).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := As) (t := bad p))
      _ ≤ ∑ a ∈ As, bound p :=
        Finset.sum_le_sum fun a _ => OMA.square_shift_bad_card M a p K hprime hcop
      _ = _ := by simp [As, Nat.card_Icc, nsmul_eq_mul]
  have hbad : (badAll.card : ℝ) ≤ (n : ℝ) * ((K : ℝ) / P + J) := by
    calc
      _ ≤ ∑ p ∈ Ps, ((badFor p).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Ps) (t := badFor))
      _ ≤ ∑ p ∈ Ps, (n : ℝ) * bound p := Finset.sum_le_sum hbadFor
      _ = (n : ℝ) * ∑ p ∈ Ps, bound p := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hprime_sum (Nat.cast_nonneg _)
  have hquota1 : (n : ℝ) * ((K : ℝ) / P) ≤ (K : ℝ) / 4 := by
    have hP' : (0 : ℝ) < P := by exact_mod_cast hP
    have hratio : (n : ℝ) / P ≤ 1 / 4 := by
      apply (div_le_iff₀ hP').mpr
      dsimp only [P]
      push_cast
      linarith
    calc
      _ = ((n : ℝ) / P) * (K : ℝ) := by ring
      _ ≤ (1 / 4 : ℝ) * (K : ℝ) := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
      _ = _ := by ring
  have hquota2 : (n : ℝ) * J ≤ (K : ℝ) / 4 := by
    have hK_eq : K = 4 * (n + 1) * J := by dsimp only [K, J, R, P]; ring
    have hK_eq' : (K : ℝ) = 4 * ((n : ℝ) + 1) * (J : ℝ) := by exact_mod_cast hK_eq
    rw [hK_eq']
    nlinarith only [Nat.cast_nonneg (α := ℝ) J]
  have hlt : badAll.card < K := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    rw [mul_add] at hbad
    have hlt' : (badAll.card : ℝ) < K := by linarith
    exact_mod_cast hlt'
  have hnot_subset : ¬ Ks ⊆ badAll := by
    intro h
    have hle := Finset.card_le_card h
    have hKs : Ks.card = K := by simp [Ks]
    rw [hKs] at hle
    exact hlt.not_ge hle
  obtain ⟨k, hk, hnot⟩ := Finset.not_subset.mp hnot_subset
  have hk' : 1 ≤ k ∧ k ≤ K := Finset.mem_Icc.mp hk
  have hsmall (p : ℕ) (hp : Nat.Prime p) (hpP : p ≤ P) : p * p ∣ M * k := by
    have hd : p ^ 2 ∣ M := pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpP) 2
    simpa only [pow_two] using dvd_mul_of_dvd_left hd k
  have hlarge (a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) (p : ℕ) (hp : Nat.Prime p)
      (hpP : P < p) : ¬ p * p ∣ a + M * k := by
    intro hd
    have hsize : a + M * k ≤ J ^ 2 := by
      calc
        _ ≤ n + M * K := Nat.add_le_add han (Nat.mul_le_mul_left M hk'.2)
        _ ≤ (n + M) * K := by
          rw [Nat.add_mul]
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right n hK) _
        _ ≤ Q ^ 2 * K := by
          apply Nat.mul_le_mul_right
          have hsub : n + M ≤ Q := by dsimp only [Q]; omega
          exact hsub.trans (by rw [pow_two]; exact Nat.le_mul_of_pos_right Q hQ)
        _ = J ^ 2 := by dsimp only [K, J]; ring
    have hdiv := Nat.le_of_dvd (show 0 < a + M * k by positivity) hd
    have hpJ : p ≤ J := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      simpa only [pow_two] using hdiv.trans hsize
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpP, hpJ⟩, hp⟩,
      Finset.mem_biUnion.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha, han⟩, Finset.mem_filter.mpr ⟨hk, hd⟩⟩⟩
  refine ⟨M * k, Nat.mul_pos hM (by omega), ?_⟩
  intro a ha han
  change Squarefree a ↔ Squarefree (a + M * k)
  rw [Nat.squarefree_iff_prime_squarefree, Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro hs p hp hd
    by_cases hpP : p ≤ P
    · exact hs p hp ((Nat.dvd_add_iff_left (hsmall p hp hpP)).mpr hd)
    · exact hlarge a ha han p hp (lt_of_not_ge hpP) hd
  · intro hs p hp hd
    have hpP : p ≤ P := by
      have hle : p ≤ a :=
        (Nat.le_mul_of_pos_right p hp.pos).trans (Nat.le_of_dvd (by omega) hd)
      dsimp only [P]
      omega
    exact hs p hp (dvd_add hd (hsmall p hp hpP))