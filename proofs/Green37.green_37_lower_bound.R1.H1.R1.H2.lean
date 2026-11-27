import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

-- Step Green37.green_37_lower_bound.R1.H1.R1.H2
-- Credit: @caa1982

namespace Green37Compress

private lemma apCover_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨(Finset.range (k * N + 1)).card, Finset.range (k * N + 1), rfl, ?_⟩
  intro d ⟨hd1, hdN⟩
  refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < (k : ℕ∞))}, ?_, ?_, rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio, zero_add, smul_eq_mul]
    have hn' : n < k := by exact_mod_cast hn
    have hmul : n * d < k * d := Nat.mul_lt_mul_of_pos_right hn' (by omega)
    have hle : k * d ≤ k * N := Nat.mul_le_mul_left k hdN
    omega
  · have hinj : Function.Injective (fun n : Fin k => 0 + n.val • d) := by
      intro i j hij
      simp only [zero_add, smul_eq_mul] at hij
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hij)
    have hset : {0 + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} =
        Set.range (fun n : Fin k => 0 + n.val • d) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
      · rintro ⟨⟨n, hn⟩, rfl⟩
        exact ⟨n, by exact_mod_cast hn, rfl⟩
    rw [hset, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_natCard, Nat.card_fin]

private lemma containsAP_shift_down {A B : Finset ℕ} {k d : ℕ} (hd : 1 ≤ d)
    (hAP : Set.ContainsAP (A : Set ℕ) k d)
    (hshift : ∀ x ∈ A, 1 ≤ x ∧ x - 1 ∈ B) :
    Set.ContainsAP (B : Set ℕ) k d := by
  obtain ⟨a, s, hsA, _, hseq⟩ := hAP
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, ∅, Set.empty_subset _, by simp, ?_⟩
    ext x; simp
  · have haA : a ∈ A := hsA (by rw [hseq]; exact ⟨0, by exact_mod_cast hk, by simp⟩)
    have ha1 : 1 ≤ a := (hshift a haA).1
    refine ⟨a - 1, {(a - 1) + n • d | (n : ℕ) (_ : n < (k : ℕ∞))}, ?_, ?_, rfl⟩
    · rintro x ⟨n, hn, rfl⟩
      have hmem : a + n • d ∈ A := hsA (by rw [hseq]; exact ⟨n, hn, rfl⟩)
      have heq : a - 1 + n • d = (a + n • d) - 1 := by simp [smul_eq_mul]; omega
      rw [heq]
      exact (hshift (a + n • d) hmem).2
    · have hinj : Function.Injective (fun n : Fin k => (a - 1) + n.val • d) := by
        intro i j hij
        simp only [smul_eq_mul] at hij
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_left_cancel hij))
      have hset : {(a - 1) + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} =
          Set.range (fun n : Fin k => (a - 1) + n.val • d) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_range]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
        · rintro ⟨⟨n, hn⟩, rfl⟩
          exact ⟨n, by exact_mod_cast hn, rfl⟩
      rw [hset, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_natCard, Nat.card_fin]

private lemma finset_bound_of_no_large_gap {A : Finset ℕ} {N : ℕ}
    (h0 : ∀ x ∈ A, x = 0 ∨ ∃ y ∈ A, y < x ∧ x ≤ y + N) :
    ∀ x ∈ A, x ≤ A.card * N := by
  have hchain : ∀ m : ℕ, ∀ x ∈ A, (A.filter (· < x)).card ≤ m → x ≤ m * N := by
    intro m
    induction m with
    | zero =>
      intro x hx hlt0
      rcases h0 x hx with rfl | ⟨y, hy, hyx, _⟩
      · simp
      · exfalso
        have hpos : 0 < (A.filter (· < x)).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩
        omega
    | succ m ih =>
      intro x hx hltm
      rcases h0 x hx with rfl | ⟨y, hy, hyx, hxy⟩
      · simp
      · have hsub : insert y (A.filter (· < y)) ⊆ A.filter (· < x) := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨hy, hyx⟩
          · obtain ⟨hzA, hzy⟩ := Finset.mem_filter.mp hz'
            exact Finset.mem_filter.mpr ⟨hzA, lt_trans hzy hyx⟩
        have hynot : y ∉ A.filter (· < y) := by
          rw [Finset.mem_filter]; intro h; omega
        have hcard : (A.filter (· < y)).card + 1 ≤ (A.filter (· < x)).card := by
          rw [← Finset.card_insert_of_notMem hynot]
          exact Finset.card_le_card hsub
        have hy_le : y ≤ m * N := ih y hy (by omega)
        calc x ≤ y + N := hxy
          _ ≤ m * N + N := Nat.add_le_add_right hy_le N
          _ = (m + 1) * N := by ring
  intro x hx
  exact hchain A.card x hx (Finset.card_filter_le _ _)

end Green37Compress

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H2 := by
  classical
  intro N k hN hk
  set m := Green37.m N k
  have hex : ∃ s : ℕ, ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k ∧ ∑ x ∈ A, x = s := by
    obtain ⟨A, hAc, hAcov⟩ := Nat.sInf_mem (Green37Compress.apCover_nonempty N k)
    exact ⟨∑ x ∈ A, x, A, hAc, hAcov, rfl⟩
  let s := Nat.find hex
  obtain ⟨A, hAc, hAcov, hAsum⟩ := Nat.find_spec hex
  have hmin : ∀ B : Finset ℕ, B.card = m → Green37.IsAPCover (B : Set ℕ) N k → s ≤ ∑ x ∈ B, x :=
    fun B hBc hBcov => Nat.find_min' hex ⟨B, hBc, hBcov, rfl⟩
  refine ⟨A, hAc, hAcov, ?_⟩
  have hgap : ∀ x ∈ A, x = 0 ∨ ∃ y ∈ A, y < x ∧ x ≤ y + N := by
    intro x hx
    by_contra hcontra
    push Not at hcontra
    obtain ⟨hx0, hno⟩ := hcontra
    let Al := A.filter (· < x)
    let Ah := A.filter (x ≤ ·)
    have hAh_nonempty : Ah.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩
    have hAh_pos : ∀ z ∈ Ah, 1 ≤ z := by
      intro z hz
      have hxz := (Finset.mem_filter.mp hz).2
      omega
    let Ah' := Ah.image (· - 1)
    let B := Al ∪ Ah'
    have hdisj : Disjoint Al Ah' := by
      rw [Finset.disjoint_left]
      intro w hwAl hwAh'
      obtain ⟨hwA, hwx⟩ := Finset.mem_filter.mp hwAl
      obtain ⟨z, hzAh, hzw⟩ := Finset.mem_image.mp hwAh'
      have hxz := (Finset.mem_filter.mp hzAh).2
      have hno_w := hno w hwA hwx
      omega
    have hinj : Set.InjOn (· - 1) (Ah : Set ℕ) := by
      intro u hu v hv heq
      dsimp only at heq
      have hu1 := hAh_pos u hu
      have hv1 := hAh_pos v hv
      omega
    have hpart : Al ∪ Ah = A := by
      ext z
      simp only [Al, Ah, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hz; by_cases h : z < x
        · left; exact ⟨hz, h⟩
        · right; exact ⟨hz, by omega⟩
    have hdisj0 : Disjoint Al Ah := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    have hBcard : B.card = m := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
          ← Finset.card_union_of_disjoint hdisj0, hpart, hAc]
    have hBcov : Green37.IsAPCover (B : Set ℕ) N k := by
      intro d ⟨hd1, hdN⟩
      obtain ⟨a, sAP, hsA, hscard, hseq⟩ := hAcov d ⟨hd1, hdN⟩
      by_cases hcross : ∀ z ∈ sAP, z < x
      · refine ⟨a, sAP, ?_, hscard, hseq⟩
        intro z hz
        exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hsA hz, hcross z hz⟩))
      · have hall_ge : ∀ z ∈ sAP, x ≤ z := by
          push Not at hcross
          obtain ⟨z₀, hz₀, hz₀ge⟩ := hcross
          rw [hseq] at hz₀
          obtain ⟨n₀, hn₀, rfl⟩ := hz₀
          intro z hz
          rw [hseq] at hz
          obtain ⟨n, hn, rfl⟩ := hz
          by_contra hlt
          push Not at hlt
          -- Walk up from n to n₀; some step must jump from < x to ≥ x with step d ≤ N
          have hex_jump : ∃ j, j < n₀ ∧ a + j • d < x ∧ x ≤ a + (j + 1) • d := by
            have hn_lt : n < n₀ := by
              by_contra hge
              simp only [smul_eq_mul] at hlt hz₀ge
              have : n₀ * d ≤ n * d := Nat.mul_le_mul_right d (by omega)
              omega
            have hP : ∀ t, n ≤ t → t ≤ n₀ → x ≤ a + t * d →
                ∃ j, n ≤ j ∧ j < t ∧ a + j * d < x ∧ x ≤ a + (j + 1) * d := by
              intro t
              induction t with
              | zero =>
                intro h1 _ h2
                have hn0 : n = 0 := by omega
                subst hn0
                simp only [smul_eq_mul, zero_mul, add_zero] at hlt h2
                omega
              | succ t ih =>
                intro hnt htno hge'
                by_cases hprev : x ≤ a + t * d
                · have hnt' : n ≤ t := by
                    by_contra hlt'
                    have hnt_eq : n = t + 1 := by omega
                    subst hnt_eq
                    simp only [smul_eq_mul] at hlt
                    nlinarith
                  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih hnt' (by omega) hprev
                  exact ⟨j, hj1, by omega, hj3, hj4⟩
                · have hnt' : n ≤ t := by
                    by_contra hlt'
                    have hnt_eq : n = t + 1 := by omega
                    subst hnt_eq
                    simp only [smul_eq_mul] at hlt
                    omega
                  exact ⟨t, hnt', by omega, by omega, hge'⟩
            obtain ⟨j, _, hj2, hj3, hj4⟩ := hP n₀ (le_of_lt hn_lt) le_rfl (by simpa [smul_eq_mul] using hz₀ge)
            exact ⟨j, hj2, by simpa [smul_eq_mul] using hj3, by simpa [smul_eq_mul] using hj4⟩
          obtain ⟨j, hjlt, hj1, hj2⟩ := hex_jump
          have hj_mem : a + j • d ∈ A :=
            hsA (by rw [hseq]; exact ⟨j, lt_trans (by exact_mod_cast hjlt) hn₀, rfl⟩)
          have hno_j := hno (a + j • d) hj_mem hj1
          simp only [smul_eq_mul] at hj1 hj2 hno_j
          nlinarith
        have hAP_Ah : Set.ContainsAP (Ah : Set ℕ) k d :=
          ⟨a, sAP, fun z hz => Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hsA hz, hall_ge z hz⟩),
            hscard, hseq⟩
        exact Green37Compress.containsAP_shift_down hd1 hAP_Ah fun z hz =>
          ⟨hAh_pos z hz, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz)⟩
    have hBsum : ∑ z ∈ B, z < s := by
      have h1 : ∑ z ∈ B, z = ∑ z ∈ Al, z + ∑ z ∈ Ah', z := Finset.sum_union hdisj
      have h2 : ∑ z ∈ Ah', z = ∑ z ∈ Ah, (z - 1) := Finset.sum_image hinj
      have h3 : ∑ z ∈ Ah, (z - 1) < ∑ z ∈ Ah, z := by
        apply Finset.sum_lt_sum
        · intro z _; omega
        · obtain ⟨z, hz⟩ := hAh_nonempty
          exact ⟨z, hz, by have := hAh_pos z hz; omega⟩
      have h4 : ∑ z ∈ Al, z + ∑ z ∈ Ah, z = s := by
        rw [← Finset.sum_union hdisj0, hpart, hAsum]
      omega
    have := hmin B hBcard hBcov
    omega
  intro x hx
  have hres := Green37Compress.finset_bound_of_no_large_gap hgap x hx
  simpa [hAc] using hres
