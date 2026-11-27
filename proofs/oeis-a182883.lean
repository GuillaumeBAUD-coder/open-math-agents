import OMAStatements.S_oeis_a182883

section Proof

open Finset

private lemma paths_card (j l : ℕ) :
    (OMA.S_oeis_a182883.paths j l).card = (2 * j + l).choose j * (j + l).choose j := by
  unfold OMA.S_oeis_a182883.paths
  rw [Finset.card_sigma]
  have hsum :
      ∀ up ∈ (Finset.range (2 * j + l)).powersetCard j,
        ((Finset.range (2 * j + l) \ up).powersetCard j).card = (j + l).choose j := by
    intro up hup
    rw [Finset.mem_powersetCard] at hup
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hup.1, Finset.card_range, hup.2,
      show 2 * j + l - j = j + l by omega]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_powersetCard, Finset.card_range,
    smul_eq_mul]

private lemma a_eq_sum (n : ℕ) :
    OMA.S_oeis_a182883.a n = ∑ k ∈ range (n / 2 + 1),
      (n - k).choose k * k.choose (n - 2 * k) := by
  unfold OMA.S_oeis_a182883.a
  have hcard :
      ∑ p ∈ OMA.S_oeis_a182883.multiplicities n, (OMA.S_oeis_a182883.paths p.1 p.2).card =
        ∑ p ∈ OMA.S_oeis_a182883.multiplicities n,
          (2 * p.1 + p.2).choose p.1 * (p.1 + p.2).choose p.1 :=
    Finset.sum_congr rfl fun p _ => paths_card p.1 p.2
  rw [hcard]
  have hfilt :
      ∑ k ∈ (range (n / 2 + 1)).filter (fun k => n ≤ 3 * k),
          (n - k).choose k * k.choose (n - 2 * k) =
        ∑ k ∈ range (n / 2 + 1), (n - k).choose k * k.choose (n - 2 * k) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hknot => ?_
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range] at hknot
    have hlt : k < n - 2 * k := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [← hfilt]
  refine Finset.sum_bij' (fun p _ => p.1 + p.2) (fun k _ => (n - 2 * k, 3 * k - n))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [OMA.S_oeis_a182883.multiplicities, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    omega
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [OMA.S_oeis_a182883.multiplicities, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_range]
    omega
  · intro p hp
    rw [OMA.S_oeis_a182883.multiplicities, Finset.mem_filter] at hp
    exact Prod.ext (by omega) (by omega)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro p hp
    rw [OMA.S_oeis_a182883.multiplicities, Finset.mem_filter] at hp
    have hsym : (2 * p.1 + p.2).choose p.1 = (n - (p.1 + p.2)).choose (p.1 + p.2) := by
      rw [show 2 * p.1 + p.2 = n - (p.1 + p.2) by omega]
      have := Nat.choose_symm (show p.1 + p.2 ≤ n - (p.1 + p.2) by omega)
      rwa [show n - (p.1 + p.2) - (p.1 + p.2) = p.1 by omega] at this
    have hr : (p.1 + p.2).choose p.1 = (p.1 + p.2).choose (n - 2 * (p.1 + p.2)) := by
      congr 1
      omega
    rw [hsym, hr]

private def fBin (m k : ℕ) : ℚ :=
  if 2 * k ≤ m then ((m - k).choose k : ℚ) * (k.choose (m - 2 * k) : ℚ) else 0

private lemma fBin_eq_fact (j l : ℕ) :
    fBin (3 * j + 2 * l) (j + l) =
      ((2 * j + l).factorial : ℚ) / ((j.factorial : ℚ) ^ 2 * (l.factorial : ℚ)) := by
  have hle : 2 * (j + l) ≤ 3 * j + 2 * l := by omega
  simp only [fBin, hle, ↓reduceIte, show 3 * j + 2 * l - (j + l) = 2 * j + l by omega,
    show 3 * j + 2 * l - 2 * (j + l) = j by omega]
  have h1 := Nat.choose_mul_factorial_mul_factorial (show j + l ≤ 2 * j + l by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + l by omega)
  rw [show 2 * j + l - (j + l) = j by omega] at h1
  rw [show j + l - j = l by omega] at h2
  have h1q : ((2 * j + l).choose (j + l) : ℚ) * ((j + l).factorial : ℚ) * (j.factorial : ℚ) =
      ((2 * j + l).factorial : ℚ) := by exact_mod_cast h1
  have h2q : ((j + l).choose j : ℚ) * (j.factorial : ℚ) * (l.factorial : ℚ) =
      ((j + l).factorial : ℚ) := by exact_mod_cast h2
  rw [eq_div_iff (by positivity)]
  calc
    ((2 * j + l).choose (j + l) : ℚ) * ((j + l).choose j : ℚ) *
        ((j.factorial : ℚ) ^ 2 * (l.factorial : ℚ))
      = ((2 * j + l).choose (j + l) : ℚ) *
          (((j + l).choose j : ℚ) * (j.factorial : ℚ) * (l.factorial : ℚ)) *
          (j.factorial : ℚ) := by ring
    _ = ((2 * j + l).choose (j + l) : ℚ) * ((j + l).factorial : ℚ) * (j.factorial : ℚ) := by
          rw [h2q]
    _ = ((2 * j + l).factorial : ℚ) := h1q

private lemma fBin_zero (m k : ℕ) (h : m < 2 * k ∨ 3 * k < m) : fBin m k = 0 := by
  unfold fBin
  rcases h with hlt | hgt
  · simp [show ¬ (2 * k ≤ m) by omega]
  · split_ifs with hle
    · rw [Nat.choose_eq_zero_of_lt (show k < m - 2 * k by omega), Nat.cast_zero, mul_zero]
    · rfl

private lemma a_eq_sum_fBin_shift (m n s : ℕ) (hm : m / 2 + 1 + s ≤ n / 2 + 1) :
    (OMA.S_oeis_a182883.a m : ℚ) =
      ∑ k ∈ range (n / 2 + 1), if s ≤ k then fBin m (k - s) else 0 := by
  rw [a_eq_sum]
  push_cast
  have h0 :
      (∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℚ) * (k.choose (m - 2 * k) : ℚ)) =
        ∑ k ∈ range (m / 2 + 1), fBin m k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 2 * k ≤ m := by rw [Finset.mem_range] at hk; omega
    simp [fBin, hk']
  rw [h0]
  have hshift :
      ∑ k ∈ range (m / 2 + 1), fBin m k =
        ∑ k ∈ Finset.Ico s (m / 2 + 1 + s), fBin m (k - s) := by
    rw [Finset.sum_Ico_eq_sum_range, show m / 2 + 1 + s - s = m / 2 + 1 by omega]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_sub_cancel_left]
  rw [hshift]
  have hsub : Finset.Ico s (m / 2 + 1 + s) ⊆ range (n / 2 + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  have hIco :
      ∑ k ∈ Finset.Ico s (m / 2 + 1 + s), fBin m (k - s) =
        ∑ k ∈ Finset.Ico s (m / 2 + 1 + s), (if s ≤ k then fBin m (k - s) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    simp [hk.1]
  rw [hIco]
  refine Finset.sum_subset hsub fun k hk hknot => ?_
  rw [Finset.mem_range] at hk
  rw [Finset.mem_Ico] at hknot
  split_ifs with hsk
  · exact fBin_zero m (k - s) (Or.inl (by omega))
  · rfl

private lemma step_jl (j l : ℕ) (hjl : 4 ≤ 3 * j + 2 * l) :
    ((3 * j + 2 * l : ℕ) : ℚ) * fBin (3 * j + 2 * l) (j + l) -
      (2 * ((3 * j + 2 * l : ℕ) : ℚ) - 2) *
        (if 1 ≤ j + l then fBin (3 * j + 2 * l - 2) (j + l - 1) else 0) -
      (4 * ((3 * j + 2 * l : ℕ) : ℚ) - 6) *
        (if 1 ≤ j + l then fBin (3 * j + 2 * l - 3) (j + l - 1) else 0) +
      (((3 * j + 2 * l : ℕ) : ℚ) - 2) *
        (if 2 ≤ j + l then fBin (3 * j + 2 * l - 4) (j + l - 2) else 0) = 0 := by
  have h1 : 1 ≤ j + l := by omega
  have h2 : 2 ≤ j + l := by omega
  simp only [h1, h2, ↓reduceIte]
  rcases j with _ | j'
  · have hl2 : 2 ≤ l := by omega
    have ha : fBin (3 * 0 + 2 * l - 2) (0 + l - 1) = fBin (3 * 0 + 2 * (l - 1)) (0 + (l - 1)) :=
      congrArg₂ fBin (by omega) (by omega)
    have hb : fBin (3 * 0 + 2 * l - 3) (0 + l - 1) = 0 :=
      fBin_zero (3 * 0 + 2 * l - 3) (0 + l - 1) (Or.inl (by omega))
    have hc : fBin (3 * 0 + 2 * l - 4) (0 + l - 2) = fBin (3 * 0 + 2 * (l - 2)) (0 + (l - 2)) :=
      congrArg₂ fBin (by omega) (by omega)
    rw [ha, hb, hc, fBin_eq_fact, fBin_eq_fact, fBin_eq_fact]
    have hfl0 : (l.factorial : ℚ) ≠ 0 := by positivity
    have hfl1 : ((l - 1).factorial : ℚ) ≠ 0 := by positivity
    have hfl2 : ((l - 2).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul]
    rw [div_self hfl0, div_self hfl1, div_self hfl2]
    push_cast
    ring
  · rcases l with _ | _ | l'
    · have ha : fBin (3 * (j' + 1) + 2 * 0 - 2) (j' + 1 + 0 - 1) = 0 :=
        fBin_zero _ _ (Or.inr (by omega))
      have hb : fBin (3 * (j' + 1) + 2 * 0 - 3) (j' + 1 + 0 - 1) =
          fBin (3 * j' + 2 * 0) (j' + 0) :=
        congrArg₂ fBin (by omega) (by omega)
      have hc : fBin (3 * (j' + 1) + 2 * 0 - 4) (j' + 1 + 0 - 2) = 0 :=
        fBin_zero _ _ (Or.inr (by omega))
      rw [ha, hb, hc, fBin_eq_fact, fBin_eq_fact]
      have hfj : (j'.factorial : ℚ) ≠ 0 := by positivity
      have h2j : (2 * (j' + 1) + 0).factorial =
          (2 * j' + 2) * (2 * j' + 1) * (2 * j').factorial := by
        rw [show 2 * (j' + 1) + 0 = (2 * j' + 1) + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        ring
      have hfj_s : (j' + 1).factorial = (j' + 1) * j'.factorial := Nat.factorial_succ j'
      simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one] at h2j ⊢
      rw [show (2 * (j' + 1)).factorial = (2 * j' + 2) * (2 * j' + 1) * (2 * j').factorial by
          simpa using h2j,
        hfj_s]
      push_cast
      have hjne : (j' : ℚ) + 1 ≠ 0 := by positivity
      field_simp [hfj, hjne]
      ring
    · have ha : fBin (3 * (j' + 1) + 2 * 1 - 2) (j' + 1 + 1 - 1) =
          fBin (3 * (j' + 1) + 2 * 0) ((j' + 1) + 0) :=
        congrArg₂ fBin (by omega) (by omega)
      have hb : fBin (3 * (j' + 1) + 2 * 1 - 3) (j' + 1 + 1 - 1) =
          fBin (3 * j' + 2 * 1) (j' + 1) :=
        congrArg₂ fBin (by omega) (by omega)
      have hc : fBin (3 * (j' + 1) + 2 * 1 - 4) (j' + 1 + 1 - 2) = 0 :=
        fBin_zero _ _ (Or.inr (by omega))
      rw [ha, hb, hc, fBin_eq_fact, fBin_eq_fact, fBin_eq_fact]
      have hfj : (j'.factorial : ℚ) ≠ 0 := by positivity
      have h2j1 : (2 * (j' + 1) + 1).factorial =
          (2 * j' + 3) * (2 * j' + 2) * (2 * j' + 1).factorial := by
        rw [show 2 * (j' + 1) + 1 = (2 * j' + 2) + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        ring
      have h2j0 : (2 * (j' + 1) + 0).factorial = (2 * j' + 2) * (2 * j' + 1).factorial := by
        rw [show 2 * (j' + 1) + 0 = (2 * j' + 1) + 1 by ring, Nat.factorial_succ]
      have hfj_s : (j' + 1).factorial = (j' + 1) * j'.factorial := Nat.factorial_succ j'
      rw [h2j1, h2j0, hfj_s]
      push_cast
      have hjne : (j' : ℚ) + 1 ≠ 0 := by positivity
      field_simp [hfj, hjne]
      ring
    · have ha : fBin (3 * (j' + 1) + 2 * (l' + 2) - 2) (j' + 1 + (l' + 2) - 1) =
          fBin (3 * (j' + 1) + 2 * (l' + 1)) ((j' + 1) + (l' + 1)) :=
        congrArg₂ fBin (by omega) (by omega)
      have hb : fBin (3 * (j' + 1) + 2 * (l' + 2) - 3) (j' + 1 + (l' + 2) - 1) =
          fBin (3 * j' + 2 * (l' + 2)) (j' + (l' + 2)) :=
        congrArg₂ fBin (by omega) (by omega)
      have hc : fBin (3 * (j' + 1) + 2 * (l' + 2) - 4) (j' + 1 + (l' + 2) - 2) =
          fBin (3 * (j' + 1) + 2 * l') ((j' + 1) + l') :=
        congrArg₂ fBin (by omega) (by omega)
      rw [ha, hb, hc, fBin_eq_fact, fBin_eq_fact, fBin_eq_fact, fBin_eq_fact]
      have hfj : (j'.factorial : ℚ) ≠ 0 := by positivity
      have hfl : (l'.factorial : ℚ) ≠ 0 := by positivity
      have hfj_s : (j' + 1).factorial = (j' + 1) * j'.factorial := Nat.factorial_succ j'
      have hfl1_s : (l' + 1).factorial = (l' + 1) * l'.factorial := Nat.factorial_succ l'
      have hfl2_s : (l' + 2).factorial = (l' + 2) * (l' + 1) * l'.factorial := by
        rw [Nat.factorial_succ (l' + 1), hfl1_s]
        ring
      have hf0_s : (2 * (j' + 1) + (l' + 2)).factorial =
          (2 * j' + l' + 4) * (2 * j' + l' + 3) * (2 * j' + (l' + 2)).factorial := by
        rw [show 2 * (j' + 1) + (l' + 2) = (2 * j' + l' + 3) + 1 by ring, Nat.factorial_succ,
          show 2 * j' + l' + 3 = (2 * j' + (l' + 2)) + 1 by ring, Nat.factorial_succ]
        ring
      have hf2_s : (2 * (j' + 1) + (l' + 1)).factorial =
          (2 * j' + l' + 3) * (2 * j' + (l' + 2)).factorial := by
        rw [show 2 * (j' + 1) + (l' + 1) = (2 * j' + (l' + 2)) + 1 by ring, Nat.factorial_succ]
        ring
      have hf4_s : (2 * (j' + 1) + l').factorial = (2 * j' + (l' + 2)).factorial := by
        ring_nf
      rw [hf0_s, hf2_s, hf4_s, hfj_s, hfl2_s, hfl1_s]
      push_cast
      have hjne : (j' : ℚ) + 1 ≠ 0 := by positivity
      have hl1ne : (l' : ℚ) + 1 ≠ 0 := by positivity
      have hl2ne : (l' : ℚ) + 2 ≠ 0 := by positivity
      field_simp [hfj, hfl, hjne, hl1ne, hl2ne]
      ring

private lemma step_identity (n k : ℕ) (hn : 4 ≤ n) :
    (n : ℚ) * fBin n k -
      (2 * (n : ℚ) - 2) * (if 1 ≤ k then fBin (n - 2) (k - 1) else 0) -
      (4 * (n : ℚ) - 6) * (if 1 ≤ k then fBin (n - 3) (k - 1) else 0) +
      ((n : ℚ) - 2) * (if 2 ≤ k then fBin (n - 4) (k - 2) else 0) = 0 := by
  by_cases hrange : 2 * k ≤ n ∧ n ≤ 3 * k
  · have hn_eq : n = 3 * (n - 2 * k) + 2 * (3 * k - n) := by omega
    have hk_eq : k = (n - 2 * k) + (3 * k - n) := by omega
    have h := step_jl (n - 2 * k) (3 * k - n) (by omega)
    simpa [← hn_eq, ← hk_eq] using h
  · have h0 : fBin n k = 0 := by
      refine fBin_zero n k ?_
      omega
    have h2 : (if 1 ≤ k then fBin (n - 2) (k - 1) else 0) = 0 := by
      split_ifs with hk1
      · exact fBin_zero (n - 2) (k - 1) (by omega)
      · rfl
    have h3 : (if 1 ≤ k then fBin (n - 3) (k - 1) else 0) = 0 := by
      split_ifs with hk1
      · exact fBin_zero (n - 3) (k - 1) (by omega)
      · rfl
    have h4 : (if 2 ≤ k then fBin (n - 4) (k - 2) else 0) = 0 := by
      split_ifs with hk2
      · exact fBin_zero (n - 4) (k - 2) (by omega)
      · rfl
    rw [h0, h2, h3, h4]
    ring

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182883.main := by
  refine ⟨a_eq_sum, fun n hn => ?_⟩
  have hQ :
      (n : ℚ) * (OMA.S_oeis_a182883.a n : ℚ) -
        (2 * (n : ℚ) - 2) * (OMA.S_oeis_a182883.a (n - 2) : ℚ) -
        (4 * (n : ℚ) - 6) * (OMA.S_oeis_a182883.a (n - 3) : ℚ) +
        ((n : ℚ) - 2) * (OMA.S_oeis_a182883.a (n - 4) : ℚ) = 0 := by
    rw [a_eq_sum_fBin_shift n n 0 (by omega),
      a_eq_sum_fBin_shift (n - 2) n 1 (by omega),
      a_eq_sum_fBin_shift (n - 3) n 1 (by omega),
      a_eq_sum_fBin_shift (n - 4) n 2 (by omega)]
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    exact step_identity n k hn
  have hQ' :
      (n : ℚ) * (OMA.S_oeis_a182883.a n : ℚ) =
        (2 * (n : ℚ) - 2) * (OMA.S_oeis_a182883.a (n - 2) : ℚ) +
          (4 * (n : ℚ) - 6) * (OMA.S_oeis_a182883.a (n - 3) : ℚ) -
          ((n : ℚ) - 2) * (OMA.S_oeis_a182883.a (n - 4) : ℚ) := by linarith
  exact_mod_cast hQ'
