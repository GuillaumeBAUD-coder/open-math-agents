import OMAStatements.S_mo_215301

-- Problem: mo-215301, integer sum of distinct reciprocals with no integer proper subset sum.
-- Credit: @GarnetCullet
-- Construction. Let B be a set of odd primes with n - 1 < sum 1/p < n, and V their product,
-- so n - sum 1/p = U/V with gcd(U, V) = 1. Pick an odd t >= 3 with U*t = 1 (mod V), put
-- m = V*t and w = (U*t - 1)/V < t, and write w/t as a sum of reciprocals of numbers 2^i and
-- 2^j*t (binary digits of w*2^a). Then S = B u C u {m} sums to n. A = B u C has no nonempty
-- subset with an integer sum: a subset containing a prime p of B has p in its denominator
-- (p divides no other element of A), and any subset of C sums to less than 1. Removing any
-- nonempty part of A from S therefore never leaves an integer sum.

namespace OMA.P_mo_215301

open Finset

theorem key (A : Finset ℕ) (m n : ℕ) (hm : m ∉ A)
    (hfree : ∀ U ⊆ A, U.Nonempty → ∀ z : ℤ, ∑ k ∈ U, (1 / (k : ℚ)) ≠ z)
    (hsum : ∑ k ∈ insert m A, (1 / (k : ℚ)) = n) :
    ∀ T ⊂ insert m A, ∀ z : ℕ, 0 < z → ∑ k ∈ T, (1 / (k : ℚ)) ≠ z := by
  intro T hT z hz h
  obtain ⟨hTS, hne⟩ := Finset.ssubset_iff_subset_ne.mp hT
  by_cases hmT : m ∈ T
  · have hUA : insert m A \ T ⊆ A := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_insert.mp hx.1 with rfl | h'
      · exact absurd hmT hx.2
      · exact h'
    have hUne : (insert m A \ T).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun h' => hne (Finset.Subset.antisymm hTS h')
    have hsplit := Finset.sum_sdiff hTS (f := fun k : ℕ => (1 / (k : ℚ)))
    apply hfree _ hUA hUne ((n : ℤ) - z)
    push_cast
    rw [← hsum, ← hsplit, h]
    ring
  · have hTA : T ⊆ A := (Finset.subset_insert_iff_of_notMem hmT).mp hTS
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp at h
      exact absurd h (by exact_mod_cast hz.ne)
    · exact hfree T hTA hTne z (by exact_mod_cast h)

theorem not_int_of_prime (U : Finset ℕ) (p : ℕ) (hp : p.Prime) (hpU : p ∈ U)
    (hdiv : ∀ k ∈ U, k ≠ p → ¬ p ∣ k) (hpos : ∀ k ∈ U, 0 < k) (z : ℤ) :
    ∑ k ∈ U, (1 / (k : ℚ)) ≠ z := by
  intro h
  have hD : ¬ p ∣ ∏ k ∈ U.erase p, k := by
    intro hd
    obtain ⟨k, hk, hpk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
    exact hdiv k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) hpk
  have hX : ((∏ k ∈ U.erase p, k : ℕ) : ℚ) * ∑ k ∈ U.erase p, (1 / (k : ℚ)) =
      ((∑ k ∈ U.erase p, ∏ j ∈ (U.erase p).erase k, j : ℕ) : ℚ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_prod_erase (U.erase p) (fun j => (j : ℚ)) hk]
    have : (k : ℚ) ≠ 0 := by
      have := hpos k (Finset.mem_of_mem_erase hk)
      positivity
    field_simp
  have hsplit : ∑ k ∈ U, (1 / (k : ℚ)) = 1 / p + ∑ k ∈ U.erase p, 1 / (k : ℚ) :=
    (Finset.add_sum_erase U _ hpU).symm
  set D := ∏ k ∈ U.erase p, k
  set X := ∑ k ∈ U.erase p, ∏ j ∈ (U.erase p).erase k, j
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have key1 : (z : ℚ) * p * D = D + p * X := by
    rw [← hX, ← h, hsplit]
    field_simp
  have key2 : z * p * (D : ℤ) = D + p * X := by exact_mod_cast key1
  have : (p : ℤ) ∣ (D : ℤ) := ⟨z * D - X, by linear_combination -key2⟩
  exact hD (Int.natCast_dvd_natCast.mp this)

theorem int_free (B C : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime ∧ ∀ k ∈ B ∪ C, k ≠ p → ¬ p ∣ k)
    (hpos : ∀ k ∈ B ∪ C, 0 < k) (hC : ∑ k ∈ C, (1 / (k : ℚ)) < 1) :
    ∀ U ⊆ B ∪ C, U.Nonempty → ∀ z : ℤ, ∑ k ∈ U, (1 / (k : ℚ)) ≠ z := by
  intro U hU hne z
  by_cases hb : ∃ p ∈ U, p ∈ B
  · obtain ⟨p, hpU, hpB⟩ := hb
    exact not_int_of_prime U p (hB p hpB).1 hpU
      (fun k hk hkp => (hB p hpB).2 k (hU hk) hkp) (fun k hk => hpos k (hU hk)) z
  · push_neg at hb
    have hUC : U ⊆ C := fun k hk => by
      rcases Finset.mem_union.mp (hU hk) with h | h
      · exact absurd h (hb k hk)
      · exact h
    intro h
    have h1 : ∑ k ∈ U, (1 / (k : ℚ)) < 1 :=
      lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg hUC
        (fun _ _ _ => by positivity)) hC
    have h0 : 0 < ∑ k ∈ U, (1 / (k : ℚ)) :=
      Finset.sum_pos (fun k hk => by have := hpos k (hU hk); positivity) hne
    rw [h] at h1 h0
    have : (0 : ℤ) < z := by exact_mod_cast h0
    have : z < 1 := by exact_mod_cast h1
    omega

/-- Sum of `1/p` over odd primes below `N`. -/
def f (N : ℕ) : ℚ := ∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ p ≠ 2), (1 / (p : ℚ))

theorem f_unbounded (x : ℚ) : ∃ N, x < f N := by
  have hns := not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg] at hns
  · obtain ⟨N, hN⟩ := (hns.eventually_gt_atTop ((x : ℝ) + 1)).exists
    refine ⟨N, ?_⟩
    have hle : ∑ i ∈ Finset.range N,
        Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i ≤ (f N : ℝ) + 1 := by
      have e1 : ∑ i ∈ Finset.range N,
          Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
          ∑ i ∈ (Finset.range N).filter (fun p => p.Prime), (1 : ℝ) / i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        simp [Set.indicator_apply]
      rw [e1, ← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≠ 2)]
      have e2 : ((Finset.range N).filter (fun p => p.Prime)).filter (fun p => p ≠ 2) =
          (Finset.range N).filter (fun p => p.Prime ∧ p ≠ 2) := by
        rw [Finset.filter_filter]
      have e3 : ∑ i ∈ ((Finset.range N).filter (fun p => p.Prime)).filter (fun p => ¬ p ≠ 2),
          (1 : ℝ) / i ≤ 1 := by
        calc _ ≤ ∑ i ∈ ({2} : Finset ℕ), (1 : ℝ) / i := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro i hi
                simp only [Finset.mem_filter, not_not] at hi
                simp [hi.2]
              · intro _ _ _; positivity
          _ ≤ 1 := by norm_num
      rw [e2]
      have e4 : (f N : ℝ) = ∑ i ∈ (Finset.range N).filter (fun p => p.Prime ∧ p ≠ 2),
          (1 : ℝ) / i := by
        simp [f]
      linarith
    have : (x : ℝ) < f N := by linarith
    exact_mod_cast this
  · intro k
    apply Set.indicator_nonneg
    intro _ _
    positivity

theorem block (n : ℕ) (hn : 0 < n) : ∃ N, (n : ℚ) - 1 < f N ∧ f N < n := by
  classical
  have hex : ∃ N, (n : ℚ) - 1 < f N := f_unbounded _
  have h0 : (n : ℚ) - 1 < f (Nat.find hex) := Nat.find_spec hex
  have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at h0
    simp [f] at h0
    linarith
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ (n : ℚ) - 1 < f M := Nat.find_min hex (by omega)
  have hstep : f (M + 1) ≤ f M + 1 / 3 := by
    rw [f, f, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.sum_insert (by simp)]
      have h3 : (3 : ℚ) ≤ M := by
        have := h.1.two_le
        have := h.2
        exact_mod_cast (show 3 ≤ M by omega)
      have : 1 / (M : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
      linarith
    · linarith
  refine ⟨Nat.find hex, h0, ?_⟩
  rw [hM]
  push_neg at hmin
  linarith

theorem coprime_U (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (n U : ℕ)
    (hU : U + ∑ p ∈ B, ∏ q ∈ B.erase p, q = n * ∏ q ∈ B, q) :
    Nat.Coprime U (∏ q ∈ B, q) := by
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  rw [Nat.coprime_comm, (hB p hp).coprime_iff_not_dvd]
  intro hpU
  have hpV : p ∣ U + ∑ p ∈ B, ∏ q ∈ B.erase p, q := by
    rw [hU]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hp) _
  have hpY := (Nat.dvd_add_right hpU).mp hpV
  rw [← Finset.add_sum_erase B _ hp] at hpY
  have hrest : p ∣ ∑ p' ∈ B.erase p, ∏ q ∈ B.erase p', q := by
    apply Finset.dvd_sum
    intro p' hp'
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hp').symm, hp⟩
  have hfirst := (Nat.dvd_add_left hrest).mp hpY
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (hB p hp).prime _).mp hfirst
  have := (Nat.prime_dvd_prime_iff_eq (hB p hp) (hB q (Finset.mem_of_mem_erase hq))).mp hpq
  exact Finset.ne_of_mem_erase hq this.symm

theorem construct (n : ℕ) (hn : 0 < n) : ∃ (B C : Finset ℕ) (m : ℕ),
    (∀ p ∈ B, p.Prime ∧ ∀ k ∈ B ∪ C, k ≠ p → ¬ p ∣ k) ∧ (∀ k ∈ B ∪ C, 0 < k) ∧
    ∑ k ∈ C, (1 / (k : ℚ)) < 1 ∧ m ∉ B ∪ C ∧ 0 < m ∧
    ∑ k ∈ insert m (B ∪ C), (1 / (k : ℚ)) = n := by
  obtain ⟨N, hN1, hN2⟩ := block n hn
  set B := (Finset.range N).filter (fun p => p.Prime ∧ p ≠ 2) with hBdef
  have hBp : ∀ p ∈ B, p.Prime ∧ p ≠ 2 := fun p hp => (Finset.mem_filter.mp hp).2
  set s := ∑ p ∈ B, (1 / (p : ℚ)) with hs
  have hsf : f N = s := rfl
  rw [hsf] at hN1 hN2
  set V := ∏ q ∈ B, q with hV
  set Y := ∑ p ∈ B, ∏ q ∈ B.erase p, q with hY
  have hVpos : 0 < V := Finset.prod_pos (fun p hp => (hBp p hp).1.pos)
  have hVs : (V : ℚ) * s = Y := by
    rw [hV, hY, hs]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.mul_prod_erase B (fun q => (q : ℚ)) hp]
    have : (p : ℚ) ≠ 0 := by exact_mod_cast (hBp p hp).1.ne_zero
    field_simp
  have hVq : (0 : ℚ) < V := by exact_mod_cast hVpos
  have hYlt : Y < n * V := by
    have : (Y : ℚ) < n * V := by rw [← hVs]; nlinarith
    exact_mod_cast this
  set U := n * V - Y with hUdef
  have hUY : U + Y = n * V := Nat.sub_add_cancel hYlt.le
  have hUY' : (U : ℚ) + Y = n * V := by exact_mod_cast hUY
  have hUpos : 0 < U := by omega
  have hUV : U < V := by
    have : (U : ℚ) < V := by nlinarith
    exact_mod_cast this
  have hcop : Nat.Coprime U V := coprime_U B (fun p hp => (hBp p hp).1) n U hUY
  have hV1 : 1 < V := by omega
  have hV2 : ¬ 2 ∣ V := by
    intro h2
    obtain ⟨q, hq, h2q⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hBp q hq).1).mp h2q
    exact (hBp q hq).2 this.symm
  have hVodd : V % 2 = 1 := by omega
  obtain ⟨t0, -, ht0⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hV1
  set t := if t0 % 2 = 1 then t0 + 2 * V else t0 + 3 * V with htdef
  have ht_mod : U * t % V = 1 := by
    rw [htdef]
    split_ifs
    · rw [Nat.mul_add, show U * (2 * V) = (2 * U) * V by ring, Nat.add_mul_mod_self_right, ht0]
    · rw [Nat.mul_add, show U * (3 * V) = (3 * U) * V by ring, Nat.add_mul_mod_self_right, ht0]
  have ht_odd : t % 2 = 1 := by
    rw [htdef]
    split_ifs with h <;> omega
  have ht3 : 3 ≤ t := by
    rw [htdef]
    split_ifs <;> omega
  have htpos : 0 < t := by omega
  set w := U * t / V with hwdef
  have hw : V * w + 1 = U * t := by
    have := Nat.div_add_mod (U * t) V
    rw [ht_mod] at this
    exact this
  have hwt : w < t := by
    have h1 : U * t < V * t := Nat.mul_lt_mul_of_pos_right hUV htpos
    have h2 : V * w < V * t := by omega
    exact Nat.lt_of_mul_lt_mul_left h2
  set a := t with hadef
  have hta : t < 2 ^ a := Nat.lt_two_pow_self
  set W := w * 2 ^ a with hWdef
  set Q := W / t with hQdef
  set R := W % t with hRdef
  have hQR : Q * t + R = W := Nat.div_add_mod' W t
  have hQ : Q < 2 ^ a := by
    have h1 : Q * t ≤ W := by omega
    have h2 : W < 2 ^ a * t := by
      rw [hWdef, mul_comm (2 ^ a) t]
      exact Nat.mul_lt_mul_of_pos_right hwt (by positivity)
    have h3 : Q * t < 2 ^ a * t := lt_of_le_of_lt h1 h2
    exact Nat.lt_of_mul_lt_mul_right h3
  have hR : R < t := Nat.mod_lt _ htpos
  set I := Q.bitIndices.toFinset with hIdef
  set J := R.bitIndices.toFinset with hJdef
  have hI : ∀ i ∈ I, i < a := by
    intro i hi
    have h1 := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    have h2 : 2 ^ i < 2 ^ a := lt_of_le_of_lt h1 hQ
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  have hJ : ∀ j ∈ J, j < a := by
    intro j hj
    have h1 := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hj)
    have h2 : 2 ^ j < 2 ^ a := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  set C1 := I.image (fun i => 2 ^ (a - i)) with hC1def
  set C2 := J.image (fun j => 2 ^ (a - j) * t) with hC2def
  set C := C1 ∪ C2 with hCdef
  have hsumIn : ∑ i ∈ I, 2 ^ i = Q := by
    rw [hIdef, List.sum_toFinset _ Nat.bitIndices_nodup]
    exact Nat.sum_map_two_pow_bitIndices Q
  have hsumJn : ∑ j ∈ J, 2 ^ j = R := by
    rw [hJdef, List.sum_toFinset _ Nat.bitIndices_nodup]
    exact Nat.sum_map_two_pow_bitIndices R
  have hsumI : ∑ i ∈ I, (2 : ℚ) ^ i = Q := by
    rw [← hsumIn]; push_cast; rfl
  have hsumJ : ∑ j ∈ J, (2 : ℚ) ^ j = R := by
    rw [← hsumJn]; push_cast; rfl
  have hpow : ∀ i, i < a → (2 : ℚ) ^ a = 2 ^ (a - i) * 2 ^ i := by
    intro i hi
    rw [← pow_add]
    congr 1
    omega
  have hinj1 : Set.InjOn (fun i => 2 ^ (a - i)) (I : Set ℕ) := by
    intro i hi j hj hij
    have := Nat.pow_right_injective (le_refl 2) hij
    have := hI i hi
    have := hI j hj
    omega
  have hinj2 : Set.InjOn (fun j => 2 ^ (a - j) * t) (J : Set ℕ) := by
    intro i hi j hj hij
    have h' : 2 ^ (a - i) = 2 ^ (a - j) := Nat.eq_of_mul_eq_mul_right htpos hij
    have := Nat.pow_right_injective (le_refl 2) h'
    have := hJ i hi
    have := hJ j hj
    omega
  have hC1 : ∑ k ∈ C1, (1 / (k : ℚ)) = Q / 2 ^ a := by
    rw [hC1def, Finset.sum_image hinj1]
    have : ∀ i ∈ I, 1 / (((2 ^ (a - i) : ℕ)) : ℚ) = (2 : ℚ) ^ i / 2 ^ a := by
      intro i hi
      push_cast
      rw [hpow i (hI i hi)]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, hsumI]
  have hC2 : ∑ k ∈ C2, (1 / (k : ℚ)) = R / (2 ^ a * t) := by
    rw [hC2def, Finset.sum_image hinj2]
    have htq : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    have : ∀ j ∈ J, 1 / (((2 ^ (a - j) * t : ℕ)) : ℚ) = (2 : ℚ) ^ j / (2 ^ a * t) := by
      intro j hj
      push_cast
      rw [hpow j (hJ j hj)]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, hsumJ]
  have htcop2 : Nat.Coprime t 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hdisj12 : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk1
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hk2
    have hdvd : t ∣ 2 ^ (a - i) := ⟨2 ^ (a - j), by rw [← hij]; ring⟩
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right (a - i) htcop2) hdvd
    omega
  -- every element of C is even
  have hCeven : ∀ k ∈ C, 2 ∣ k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      have := hI i hi
      exact dvd_pow_self 2 (by omega)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have := hJ j hj
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro k hkB hkC
    have h2 := hCeven k hkC
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hBp k hkB).1).mp h2
    exact (hBp k hkB).2 this.symm
  set m := V * t with hmdef
  have hmodd : ¬ 2 ∣ m := by
    rw [hmdef]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hV2 h
    · omega
  have hmB : m ∉ B := by
    intro hmB
    have hprime := (hBp m hmB).1
    rw [hmdef] at hprime
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hmC : m ∉ C := fun hmC => hmodd (hCeven m hmC)
  have hmBC : m ∉ B ∪ C := by
    rw [Finset.mem_union]
    tauto
  have hpos : ∀ k ∈ B ∪ C, 0 < k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (hBp k hk).1.pos
    · rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        positivity
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
        positivity
  have hcopVt : Nat.Coprime V t := by
    have h1 : t * U ≡ 1 [MOD V] := by
      unfold Nat.ModEq
      rw [mul_comm, ht_mod, Nat.mod_eq_of_lt hV1]
    exact (Nat.coprime_of_mul_modEq_one U h1).symm
  have hprivate : ∀ p ∈ B, p.Prime ∧ ∀ k ∈ B ∪ C, k ≠ p → ¬ p ∣ k := by
    intro p hp
    refine ⟨(hBp p hp).1, ?_⟩
    intro k hk hkp hpk
    have hpV : p ∣ V := Finset.dvd_prod_of_mem _ hp
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hkp ((Nat.prime_dvd_prime_iff_eq (hBp p hp).1 (hBp k hk).1).mp hpk).symm
    · rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        have := (Nat.prime_dvd_prime_iff_eq (hBp p hp).1 Nat.prime_two).mp
          ((hBp p hp).1.dvd_of_dvd_pow hpk)
        exact (hBp p hp).2 this
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
        rcases (Nat.Prime.dvd_mul (hBp p hp).1).mp hpk with h | h
        · have := (Nat.prime_dvd_prime_iff_eq (hBp p hp).1 Nat.prime_two).mp
            ((hBp p hp).1.dvd_of_dvd_pow h)
          exact (hBp p hp).2 this
        · have h1 := Nat.dvd_gcd hpV h
          rw [Nat.Coprime.gcd_eq_one hcopVt] at h1
          exact (hBp p hp).1.not_dvd_one h1
  have hCsum : ∑ k ∈ C, (1 / (k : ℚ)) = w / t := by
    rw [hCdef, Finset.sum_union hdisj12, hC1, hC2]
    have hQR' : (Q : ℚ) * t + R = w * 2 ^ a := by exact_mod_cast hQR
    have htq : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    field_simp
    linear_combination hQR'
  have hw' : (V : ℚ) * w + 1 = U * t := by exact_mod_cast hw
  refine ⟨B, C, m, hprivate, hpos, ?_, hmBC, by positivity, ?_⟩
  · rw [hCsum, div_lt_one (by exact_mod_cast htpos)]
    exact_mod_cast hwt
  · rw [Finset.sum_insert hmBC, Finset.sum_union hdisjBC, hCsum]
    have htq : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    have hVq' : (V : ℚ) ≠ 0 := hVq.ne'
    rw [hmdef]
    push_cast
    field_simp
    linear_combination hw' + (t : ℚ) * hVs + (t : ℚ) * hUY'
end OMA.P_mo_215301

open OMA.P_mo_215301 in
theorem OMA.solution : type_of% @OMA.S_mo_215301.main := by
  intro n hn
  obtain ⟨B, C, m, hB, hpos, hC, hm, hm0, hsum⟩ := construct n hn
  refine ⟨insert m (B ∪ C), ?_, hsum, ?_⟩
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hm0
    · exact hpos k hk
  · exact key (B ∪ C) m n hm (int_free B C hB hpos hC) hsum
