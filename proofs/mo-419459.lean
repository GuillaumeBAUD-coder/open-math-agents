import OMAStatements.S_mo_419459

private def coprimePart (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => if p ∣ n + 1 then coprimePart p n else (n + 1) * coprimePart p n

private lemma not_dvd_coprimePart {p : ℕ} (hp : p.Prime) (n : ℕ) : ¬ p ∣ coprimePart p n := by
  induction n with
  | zero => exact hp.not_dvd_one
  | succ n ih =>
    simp only [coprimePart]
    split_ifs with hdiv
    · exact ih
    · exact hp.not_dvd_mul hdiv ih

private lemma factorial_eq_pow_mul_factorial_mul_coprimePart {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n.factorial = p ^ (n / p) * (n / p).factorial * coprimePart p n := by
  induction n with
  | zero => simp [coprimePart]
  | succ n ih =>
    rw [Nat.factorial_succ, ih]
    simp only [coprimePart]
    split_ifs with hdiv
    · have hdiv_eq : (n + 1) / p = n / p + 1 := by
        rw [Nat.succ_div]
        simp [hdiv]
      have hmul : n + 1 = p * (n / p + 1) := by
        rcases hdiv with ⟨t, ht⟩
        have htp : (n + 1) / p = t := by
          rw [ht, Nat.mul_div_right _ hp.pos]
        rw [← hdiv_eq, htp, ht]
      rw [hdiv_eq, Nat.pow_succ, Nat.factorial_succ]
      conv_lhs => rw [hmul]
      simp only [Nat.mul_assoc]
      rw [Nat.mul_left_comm (n / p + 1) (p ^ (n / p)) _,
        Nat.mul_left_comm p (p ^ (n / p)) _]
    · have hdiv_eq : (n + 1) / p = n / p := by
        rw [Nat.succ_div]
        simp [hdiv]
      rw [hdiv_eq]
      simp only [Nat.mul_assoc]
      rw [Nat.mul_left_comm (n + 1) (p ^ (n / p)) _,
        Nat.mul_left_comm (n + 1) (n / p).factorial _]

private lemma central_choose_step {p m : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ (m + m).choose m) :
    2 * (m % p) < p ∧ ¬ p ∣ (m / p + m / p).choose (m / p) := by
  set r := m % p
  set q := m / p
  have hm_eq : m = p * q + r := (Nat.div_add_mod m p).symm
  have hr : r < p := Nat.mod_lt m hp.pos
  have hcomb : (m + m).choose m * (m.factorial * m.factorial) = (m + m).factorial := by
    simpa [Nat.mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial m m
  have hfac_m : m.factorial = p ^ q * q.factorial * coprimePart p m :=
    factorial_eq_pow_mul_factorial_mul_coprimePart hp m
  have hfac_2m : (m + m).factorial =
      p ^ ((m + m) / p) * ((m + m) / p).factorial * coprimePart p (m + m) :=
    factorial_eq_pow_mul_factorial_mul_coprimePart hp (m + m)
  have hpos_cancel : 0 < p ^ (q + q) * (q.factorial * q.factorial) :=
    Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.mul_pos (Nat.factorial_pos q) (Nat.factorial_pos q))
  have hnot_cp : ¬ p ∣ coprimePart p m := not_dvd_coprimePart hp m
  by_cases hcarry : p ≤ r + r
  · have hdiv_2m : (m + m) / p = q + q + 1 := by
      have h2m : m + m = p * (q + q + 1) + (r + r - p) := by
        calc
          m + m = (p * q + r) + (p * q + r) := by rw [← hm_eq]
          _ = p * (q + q + 1) + (r + r - p) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            omega
      rw [h2m, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have h2q1 : (q + q + 1).factorial =
        (q + q + 1) * ((q + q).choose q * (q.factorial * q.factorial)) := by
      rw [Nat.factorial_succ]
      congr 1
      simpa [Nat.mul_assoc] using (Nat.add_choose_mul_factorial_mul_factorial q q).symm
    have heq :
        p ^ (q + q) * (q.factorial * q.factorial) *
            ((m + m).choose m * (coprimePart p m * coprimePart p m)) =
          p ^ (q + q) * (q.factorial * q.factorial) *
            (p * (q + q + 1) * (q + q).choose q * coprimePart p (m + m)) := by
      calc
        p ^ (q + q) * (q.factorial * q.factorial) *
            ((m + m).choose m * (coprimePart p m * coprimePart p m))
          = (m + m).choose m * (p ^ (q + q) * (q.factorial * q.factorial) *
              (coprimePart p m * coprimePart p m)) := by
            rw [Nat.mul_left_comm _ ((m + m).choose m) _]
        _ = (m + m).choose m * ((p ^ q * q.factorial * coprimePart p m) *
              (p ^ q * q.factorial * coprimePart p m)) := by
            congr 1
            symm
            rw [mul_mul_mul_comm (p ^ q * q.factorial), mul_mul_mul_comm (p ^ q), ← Nat.pow_add]
        _ = (m + m).choose m * (m.factorial * m.factorial) := by
            rw [← hfac_m]
        _ = (m + m).factorial := hcomb
        _ = p ^ (q + q + 1) * (q + q + 1).factorial * coprimePart p (m + m) := by
            rw [hfac_2m, hdiv_2m]
        _ = p ^ (q + q) * (q.factorial * q.factorial) *
              (p * (q + q + 1) * (q + q).choose q * coprimePart p (m + m)) := by
            rw [h2q1, Nat.pow_succ]
            simp only [Nat.mul_assoc]
            rw [Nat.mul_left_comm ((q + q).choose q) q.factorial _,
              Nat.mul_left_comm ((q + q).choose q) q.factorial _,
              Nat.mul_left_comm (q + q + 1) q.factorial _,
              Nat.mul_left_comm (q + q + 1) q.factorial _,
              Nat.mul_left_comm p q.factorial _,
              Nat.mul_left_comm p q.factorial _]
    have hcancel := Nat.eq_of_mul_eq_mul_left hpos_cancel heq
    have hdvd_lhs : p ∣ (m + m).choose m * (coprimePart p m * coprimePart p m) := by
      rw [hcancel]
      exact ⟨(q + q + 1) * (q + q).choose q * coprimePart p (m + m), by
        simp only [Nat.mul_assoc]⟩
    have hdvd_m : p ∣ (m + m).choose m := by
      rcases hp.dvd_mul.mp hdvd_lhs with h | h
      · exact h
      · exact absurd h (hp.not_dvd_mul hnot_cp hnot_cp)
    exact absurd hdvd_m hnd
  · have hlt : 2 * r < p := by omega
    refine ⟨hlt, fun hdvd_q => ?_⟩
    have hdiv_2m : (m + m) / p = q + q := by
      have h2m : m + m = p * (q + q) + (r + r) := by
        calc
          m + m = (p * q + r) + (p * q + r) := by rw [← hm_eq]
          _ = p * (q + q) + (r + r) := by
            rw [Nat.mul_add]
            omega
      rw [h2m, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have h2q : (q + q).factorial = (q + q).choose q * (q.factorial * q.factorial) := by
      simpa [Nat.mul_assoc] using (Nat.add_choose_mul_factorial_mul_factorial q q).symm
    have heq :
        p ^ (q + q) * (q.factorial * q.factorial) *
            ((m + m).choose m * (coprimePart p m * coprimePart p m)) =
          p ^ (q + q) * (q.factorial * q.factorial) *
            ((q + q).choose q * coprimePart p (m + m)) := by
      calc
        p ^ (q + q) * (q.factorial * q.factorial) *
            ((m + m).choose m * (coprimePart p m * coprimePart p m))
          = (m + m).choose m * (p ^ (q + q) * (q.factorial * q.factorial) *
              (coprimePart p m * coprimePart p m)) := by
            rw [Nat.mul_left_comm _ ((m + m).choose m) _]
        _ = (m + m).choose m * ((p ^ q * q.factorial * coprimePart p m) *
              (p ^ q * q.factorial * coprimePart p m)) := by
            congr 1
            symm
            rw [mul_mul_mul_comm (p ^ q * q.factorial), mul_mul_mul_comm (p ^ q), ← Nat.pow_add]
        _ = (m + m).choose m * (m.factorial * m.factorial) := by
            rw [← hfac_m]
        _ = (m + m).factorial := hcomb
        _ = p ^ (q + q) * (q + q).factorial * coprimePart p (m + m) := by
            rw [hfac_2m, hdiv_2m]
        _ = p ^ (q + q) * (q.factorial * q.factorial) *
              ((q + q).choose q * coprimePart p (m + m)) := by
            rw [h2q]
            simp only [Nat.mul_assoc]
            rw [Nat.mul_left_comm ((q + q).choose q) q.factorial _,
              Nat.mul_left_comm ((q + q).choose q) q.factorial _]
    have hcancel := Nat.eq_of_mul_eq_mul_left hpos_cancel heq
    have hdvd_lhs : p ∣ (m + m).choose m * (coprimePart p m * coprimePart p m) := by
      rw [hcancel]
      exact Nat.dvd_mul_right_of_dvd hdvd_q _
    have hdvd_m : p ∣ (m + m).choose m := by
      rcases hp.dvd_mul.mp hdvd_lhs with h | h
      · exact h
      · exact absurd h (hp.not_dvd_mul hnot_cp hnot_cp)
    exact hnd hdvd_m

private def goodSet (p k : ℕ) : Finset ℕ :=
  (Finset.range (p ^ k)).filter (fun m => ¬ p ∣ (m + m).choose m)

private lemma zero_mem_goodSet {p k : ℕ} (hp : p.Prime) : 0 ∈ goodSet p k := by
  simp only [goodSet, Finset.mem_filter, Finset.mem_range, Nat.zero_add, Nat.choose_zero_right]
  exact ⟨Nat.pow_pos hp.pos, hp.not_dvd_one⟩

private lemma card_goodSet_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (goodSet p k).card ≤ ((p + 1) / 2) ^ k := by
  induction k with
  | zero =>
    simp only [goodSet, Nat.pow_zero]
    exact (Finset.card_filter_le _ _).trans (by simp)
  | succ k ih =>
    have hsub : (goodSet p (k + 1)).image (fun m => (m % p, m / p)) ⊆
        Finset.range ((p + 1) / 2) ×ˢ goodSet p k := by
      intro xy hxy
      rcases Finset.mem_image.mp hxy with ⟨m, hm, rfl⟩
      simp only [goodSet, Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨hm_lt, hm_nd⟩ := hm
      obtain ⟨hr, hq_nd⟩ := central_choose_step hp hm_nd
      simp only [Finset.mem_product, Finset.mem_range, goodSet, Finset.mem_filter]
      refine ⟨by omega, ?_, hq_nd⟩
      rw [Nat.pow_succ'] at hm_lt
      exact Nat.div_lt_of_lt_mul hm_lt
    have hinj : Set.InjOn (fun m => (m % p, m / p)) ↑(goodSet p (k + 1)) := by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      have ha : p * (a / p) + a % p = a := Nat.div_add_mod a p
      have hb : p * (b / p) + b % p = b := Nat.div_add_mod b p
      rw [← ha, ← hb, hab.1, hab.2]
    calc
      (goodSet p (k + 1)).card
        = ((goodSet p (k + 1)).image (fun m => (m % p, m / p))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range ((p + 1) / 2) ×ˢ goodSet p k).card := Finset.card_le_card hsub
      _ = ((p + 1) / 2) * (goodSet p k).card := by simp [Finset.card_product]
      _ ≤ ((p + 1) / 2) * ((p + 1) / 2) ^ k := Nat.mul_le_mul_left _ ih
      _ = ((p + 1) / 2) ^ (k + 1) := Nat.pow_succ'.symm

theorem OMA.solution : type_of% @OMA.S_mo_419459.main := by
  intro p M X k hp hM hX hMX
  have hex : (OMA.S_mo_419459.exceptional p M X).card + 1 ≤ ((p + 1) / 2) ^ k := by
    have hinj : Set.InjOn (fun n => n * M) ↑(OMA.S_mo_419459.exceptional p M X) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hM hab
    have hsub : (OMA.S_mo_419459.exceptional p M X).image (fun n => n * M) ⊆ goodSet p k := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      simp only [OMA.S_mo_419459.exceptional, Finset.mem_filter, Finset.mem_Ico] at hn
      simp only [goodSet, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hn.2⟩
      have h1 : n * M < X * M := Nat.mul_lt_mul_of_pos_right hn.1.2 hM
      have h2 : X * M = M * X := Nat.mul_comm X M
      omega
    have hzero_not_mem : 0 ∉ (OMA.S_mo_419459.exceptional p M X).image (fun n => n * M) := by
      simp only [Finset.mem_image, OMA.S_mo_419459.exceptional, Finset.mem_filter, Finset.mem_Ico]
      rintro ⟨n, ⟨⟨hn1, _⟩, _⟩, hn0⟩
      have hpos : 0 < n * M := Nat.mul_pos (by omega) hM
      omega
    have hinsert_sub :
        insert 0 ((OMA.S_mo_419459.exceptional p M X).image (fun n => n * M)) ⊆ goodSet p k := by
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm'
      · exact zero_mem_goodSet hp
      · exact hsub hm'
    calc
      (OMA.S_mo_419459.exceptional p M X).card + 1
        = ((OMA.S_mo_419459.exceptional p M X).image (fun n => n * M)).card + 1 := by
          rw [Finset.card_image_of_injOn hinj]
      _ = (insert 0 ((OMA.S_mo_419459.exceptional p M X).image (fun n => n * M))).card :=
          (Finset.card_insert_of_notMem hzero_not_mem).symm
      _ ≤ (goodSet p k).card := Finset.card_le_card hinsert_sub
      _ ≤ ((p + 1) / 2) ^ k := card_goodSet_le hp k
  refine ⟨hex, ?_⟩
  have hunion : OMA.S_mo_419459.exceptional p M X ∪ OMA.S_mo_419459.divisible p M X =
      Finset.Ico 1 X := by
    ext n
    simp only [OMA.S_mo_419459.exceptional, OMA.S_mo_419459.divisible,
      Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    tauto
  have hdisj : Disjoint (OMA.S_mo_419459.exceptional p M X)
      (OMA.S_mo_419459.divisible p M X) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [OMA.S_mo_419459.exceptional, OMA.S_mo_419459.divisible, Finset.mem_filter] at hn1 hn2
    exact hn1.2 hn2.2
  have hcard : (OMA.S_mo_419459.exceptional p M X).card +
      (OMA.S_mo_419459.divisible p M X).card = X - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Nat.card_Ico]
  omega
