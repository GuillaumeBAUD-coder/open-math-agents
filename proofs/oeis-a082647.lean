import OMAStatements.S_oeis_a082647

-- Problem: A082647: Number of ways n can be expressed as the sum of d consecutive positive integers where d>0 is a divisor of n.
-- Upstream: formal-conjectures statements/oeis-a082647.lean (declaration OMA.S_oeis_a082647.main)
-- Credit: @doubao

open OMA.S_oeis_a082647

private lemma sum_consec (d s : ℕ) :
    ∑ i ∈ Finset.range d, (s + i) = d * s + d * (d - 1) / 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    Finset.sum_range_id]
  simp

private lemma consec_iff (n d : ℕ) (hn : 1 ≤ n) (hd : d ∣ n) :
    IsConsecSum n d ↔ Odd d ∧ d * d < 2 * n := by
  constructor
  · rintro ⟨s, hs, hsum⟩
    have h : ∑ i ∈ Finset.range d, (s + i) = d * s + ∑ i ∈ Finset.range d, i := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      simp
    have hsum_eq : n = d * s + ∑ i ∈ Finset.range d, i := by
      rw [← h, hsum]
    have hT : (∑ i ∈ Finset.range d, i) * 2 = d * (d - 1) :=
      Finset.sum_range_id_mul_two d
    have h2T : 2 * (∑ i ∈ Finset.range d, i) = d * (d - 1) := by
      rw [mul_comm, hT]
    have h2n : 2 * n = 2 * d * s + d * (d - 1) := by
      rw [hsum_eq, Nat.mul_add, h2T]
      ring
    have hposd : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    obtain ⟨q, hq⟩ := hd
    have h2 : 2 * n = d * (2 * q) := by rw [hq]; ring
    have h2n' : 2 * n = d * (2 * s + (d - 1)) := by
      rw [h2n]; ring
    have heq : 2 * q = 2 * s + (d - 1) := by
      apply Nat.mul_left_cancel hposd
      exact h2.symm.trans h2n'
    have hlt : d < 2 * q := by omega
    have hdOdd : Odd d := by
      have h : d = 2 * (q - s) + 1 := by omega
      exact ⟨q - s, h⟩
    have hbelow : d * d < 2 * n := by
      rw [hq]
      nlinarith
    exact ⟨hdOdd, hbelow⟩
  · rintro ⟨hdOdd, hbelow⟩
    obtain ⟨k, hk⟩ := hdOdd
    obtain ⟨q, hq⟩ := hd
    have hlt : d < 2 * q := by nlinarith
    have hpos : 0 < q - k := by omega
    have hdm1 : d - 1 = 2 * k := by omega
    have hhalf : d * (d - 1) / 2 = d * k := by
      rw [hdm1, hk]
      have h2 : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by ring
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
    refine ⟨q - k, hpos, ?_⟩
    have hsum : ∑ i ∈ Finset.range d, ((q - k) + i) =
        d * (q - k) + d * (d - 1) / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        Finset.sum_range_id]
      simp
    rw [hsum, hhalf]
    have hqk : (q - k) + k = q := by omega
    rw [← mul_add, hqk, hq]

private lemma even_form (n k s : ℕ) (hposk : 0 < k) (hs : 0 < s)
    (hsum : ∑ i ∈ Finset.range (2 * k), (s + i) = n) :
    ∃ m : ℕ, n = k * m ∧ Odd m ∧ 2 * k < m := by
  set m := 2 * s + 2 * k - 1 with hmdef
  have hhalf : (2 * k) * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    have h2 : (2 * k) * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  have hsum2 : n = 2 * k * s + k * (2 * k - 1) := by
    rw [sum_consec (2 * k) s, hhalf] at hsum
    exact hsum.symm
  have hmeq : m = 2 * s + (2 * k - 1) := by omega
  have hform : n = k * m := by
    have hk : k * m = 2 * k * s + k * (2 * k - 1) := by
      rw [hmeq]; ring
    exact hsum2.trans hk.symm
  set w := s + k - 1 with hwdef
  have hsw : 1 ≤ s + k := by omega
  have hmw : m = 2 * w + 1 := by
    simp only [hwdef, hmdef]
    omega
  have hmOdd : Odd m := ⟨w, hmw⟩
  have hmgt : 2 * k < m := by omega
  exact ⟨m, hform, hmOdd, hmgt⟩

private lemma even_consec (n k d : ℕ) (hposk : 0 < k) (hnd : n = k * d)
    (hdOdd : Odd d) (hlt : 2 * k < d) : IsConsecSum n (2 * k) := by
  obtain ⟨r, hr : d = 2 * r + 1⟩ := hdOdd
  have hkr : k ≤ r := by linarith
  set s := r - k + 1 with hsdef
  have hs : 0 < s := by omega
  have h2s : 2 * s + (2 * k - 1) = d := by
    rw [hsdef, hr]
    have hkr' : (r - k) + k = r := Nat.sub_add_cancel hkr
    have h : 2 * (r - k + 1) + (2 * k - 1) = 2 * r + 1 := by
      have h2 : 2 * (r - k + 1) = 2 * (r - k) + 2 := by ring
      rw [h2]
      omega
    exact h
  have hhalf : (2 * k) * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    have h2 : (2 * k) * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  have hL : 2 * k * s + k * (2 * k - 1) = k * d := by
    rw [← h2s, mul_add]; ring
  refine ⟨s, hs, ?_⟩
  rw [sum_consec (2 * k) s, hhalf, hL, hnd]

open Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a082647.main := by
  intro n hn
  let D := n.divisors
  let below (d : ℕ) := d * d < 2 * n
  let above (d : ℕ) := 2 * n < d * d
  let B := D.filter below
  let A := D.filter above
  let S := D.filter fun d => Odd d ∧ below d
  let L := D.filter fun d => Odd d ∧ above d
  let M := D.filter fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
  let E_B := D.filter fun d => Even d ∧ below d
  let E_A := D.filter fun d => Even d ∧ above d

  have hL1 : ∀ d ∈ D, IsConsecSum n d ↔ Odd d ∧ below d := by
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    exact consec_iff n d hn hdvd

  have ha : (a n : ℤ) = (S.card : ℤ) := by
    have hfil : D.filter (fun d => IsConsecSum n d) = S := by
      ext d
      simp only [S, Finset.mem_filter]
      constructor
      · rintro ⟨hd, hc⟩
        exact ⟨hd, (hL1 d hd).mp hc⟩
      · rintro ⟨hd, ho, hb⟩
        exact ⟨hd, (hL1 d hd).mpr ⟨ho, hb⟩⟩
    have h : a n = S.card := by
      rw [a, hfil]
    rw [h]

  let K := (Finset.Icc 1 n).filter fun k => IsConsecSum n (2 * k)
  have hA131576 : (A131576 n : ℤ) = (L.card : ℤ) := by
    have hbij : K.card = L.card := by
      refine Finset.card_bij' (fun k _ => n / k) (fun d _ => n / d) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkI, hconv⟩ := Finset.mem_filter.mp hk
        obtain ⟨s, hs, hsum⟩ := hconv
        have hposk : 0 < k := (Finset.mem_Icc.mp hkI).1
        obtain ⟨m, hform, hmOdd, hmgt⟩ := even_form n k s hposk hs hsum
        have hposm : 0 < m := by nlinarith
        have hmdvd : m ∣ n := ⟨k, by rw [hform]; ring⟩
        have hmD : m ∈ D := Nat.mem_divisors.mpr ⟨hmdvd, by linarith⟩
        have hmAbove : above m := by nlinarith
        have hmk : n / k = m := by
          have hdiv : k * (n / k) = n := Nat.mul_div_cancel' ⟨m, hform⟩
          apply Nat.mul_left_cancel hposk
          rw [hdiv, hform]
        simp only [L, Finset.mem_filter]
        exact ⟨by rw [hmk]; exact hmD, by rw [hmk]; exact ⟨hmOdd, hmAbove⟩⟩
      · intro d hd
        obtain ⟨hdD, hdOdd, hdAbove⟩ := Finset.mem_filter.mp hd
        have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
        set k := n / d with hkdef
        have hnd : n = k * d := by
          have h := Nat.mul_div_cancel' hdvd
          rw [mul_comm] at h
          exact h.symm
        have hposd : 0 < d := Nat.pos_of_mem_divisors hdD
        have hkpos : 0 < k := by nlinarith
        have hkle : k ≤ n := by nlinarith
        have h2k_lt_d : 2 * k < d := by nlinarith
        have hconv : IsConsecSum n (2 * k) :=
          even_consec n k d hkpos hnd hdOdd h2k_lt_d
        simp only [K, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hkpos, hkle⟩, hconv⟩
      · intro k hk
        obtain ⟨hkI, hconv⟩ := Finset.mem_filter.mp hk
        obtain ⟨s, hs, hsum⟩ := hconv
        have hposk : 0 < k := (Finset.mem_Icc.mp hkI).1
        obtain ⟨m, hform, _, _⟩ := even_form n k s hposk hs hsum
        have hposm : 0 < m := by nlinarith
        have hmk : n / k = m := by
          have hdiv : k * (n / k) = n := Nat.mul_div_cancel' ⟨m, hform⟩
          apply Nat.mul_left_cancel hposk
          rw [hdiv, hform]
        rw [hmk]
        have hdivm : m * (n / m) = n := Nat.mul_div_cancel' ⟨k, by rw [hform, mul_comm]⟩
        apply Nat.mul_left_cancel hposm
        rw [hdivm, hform, mul_comm]
      · intro d hd
        obtain ⟨hdD, hdOdd, hdAbove⟩ := Finset.mem_filter.mp hd
        have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
        set k := n / d with hkdef
        have hnd : n = k * d := by
          have h := Nat.mul_div_cancel' hdvd
          rw [mul_comm] at h
          exact h.symm
        have hposd : 0 < d := Nat.pos_of_mem_divisors hdD
        have hkpos : 0 < k := by nlinarith
        have hdivk : k * (n / k) = n := Nat.mul_div_cancel' ⟨d, hnd⟩
        apply Nat.mul_left_cancel hkpos
        rw [hdivk, hnd]
    have hK : A131576 n = K.card := by rfl
    rw [hK, hbij]

  let O := D.filter Odd
  have hA001227 : (A001227 n : ℤ) = (S.card + L.card : ℤ) := by
    have hdis : Disjoint S L := by
      rw [Finset.disjoint_left]
      intro d hs hl
      obtain ⟨_, _, hb⟩ := Finset.mem_filter.mp hs
      obtain ⟨_, _, ha⟩ := Finset.mem_filter.mp hl
      linarith
    have h1 : S ∪ L ⊆ O := by
      intro d h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨hd, ho, _⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hd, ho⟩
      · obtain ⟨hd, ho, _⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hd, ho⟩
    have h2 : O ⊆ S ∪ L := by
      intro d h
      obtain ⟨hd, ho⟩ := Finset.mem_filter.mp h
      by_cases hb : d * d < 2 * n
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hd, ho, hb⟩))
      · by_cases ha : 2 * n < d * d
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hd, ho, ha⟩))
        · have heq : d * d = 2 * n := by linarith
          have hOdd2 : Odd (d * d) := Odd.mul ho ho
          have hdiv : ¬(2 ∣ d * d) := hOdd2.not_two_dvd_nat
          rw [heq] at hdiv
          exact False.elim (hdiv ⟨n, by ring⟩)
    have hun : S ∪ L = O := Finset.Subset.antisymm h1 h2
    have hinter : (S ∩ L).card = 0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_empty]
    have hcard : O.card = S.card + L.card := by
      have h := Finset.card_union_add_card_inter S L
      rw [hinter, add_zero] at h
      rw [hun] at h
      exact h
    have hO : A001227 n = O.card := by rfl
    rw [hO]
    exact_mod_cast hcard

  let A' := D.filter fun e => 2 * e * e < n
  have hφ : A.card = A'.card := by
    refine Finset.card_bij' (fun d _ => n / d) (fun e _ => n / e) ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdD, habove⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
      set e := n / d with hedef
      have hde : d * e = n := Nat.mul_div_cancel' hdvd
      have hposd : 0 < d := Nat.pos_of_mem_divisors hdD
      have hpose : 0 < e := by nlinarith
      have hedvd : e ∣ n := ⟨d, by rw [mul_comm e d, hde]⟩
      have heD : e ∈ D := Nat.mem_divisors.mpr ⟨hedvd, by linarith⟩
      have hkey : 2 * e * e < n := by nlinarith
      exact Finset.mem_filter.mpr ⟨heD, hkey⟩
    · intro e he
      obtain ⟨heD, hsmall⟩ := Finset.mem_filter.mp he
      have hevd : e ∣ n := Nat.dvd_of_mem_divisors heD
      set d := n / e with hddef
      have hde : e * d = n := Nat.mul_div_cancel' hevd
      have hpose : 0 < e := Nat.pos_of_mem_divisors heD
      have hposd : 0 < d := by nlinarith
      have hddvd : d ∣ n := ⟨e, by rw [mul_comm d e, hde]⟩
      have hdD : d ∈ D := Nat.mem_divisors.mpr ⟨hddvd, by linarith⟩
      have habove : 2 * n < d * d := by nlinarith
      exact Finset.mem_filter.mpr ⟨hdD, habove⟩
    · intro d hd
      obtain ⟨hdD, _⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
      set e := n / d with hedef
      have hde : d * e = n := Nat.mul_div_cancel' hdvd
      have hpose : 0 < e := by nlinarith
      have hedvd : e ∣ n := ⟨d, by rw [mul_comm e d, hde]⟩
      have hdiv : e * (n / e) = n := Nat.mul_div_cancel' hedvd
      apply Nat.mul_left_cancel hpose
      rw [hdiv]
      exact hde.symm.trans (mul_comm d e)
    · intro e he
      obtain ⟨heD, _⟩ := Finset.mem_filter.mp he
      have hevd : e ∣ n := Nat.dvd_of_mem_divisors heD
      set d := n / e with hddef
      have hde : e * d = n := Nat.mul_div_cancel' hevd
      have hposd : 0 < d := by nlinarith
      have hddvd : d ∣ n := ⟨e, by rw [mul_comm d e, hde]⟩
      have hdiv : d * (n / d) = n := Nat.mul_div_cancel' hddvd
      apply Nat.mul_left_cancel hposd
      rw [hdiv]
      exact hde.symm.trans (mul_comm e d)
  have hMsub : M ⊆ B := by
    intro d hd
    obtain ⟨hdD, _, hbelow⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hdD, by simpa [pow_two, below] using hbelow⟩
  have hA'sub : A' ⊆ B := by
    intro d hd
    obtain ⟨hdD, hsmall⟩ := Finset.mem_filter.mp hd
    have hbelow : d * d < 2 * n := by nlinarith
    exact Finset.mem_filter.mpr ⟨hdD, hbelow⟩
  have hdisMA : Disjoint M A' := by
    rw [Finset.disjoint_left]
    intro x hM hA'
    obtain ⟨_, hge, _⟩ := Finset.mem_filter.mp hM
    obtain ⟨_, hlt⟩ := Finset.mem_filter.mp hA'
    linarith
  have hunMA : M ∪ A' = B := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hMsub h
      · exact hA'sub h
    · intro d hb
      obtain ⟨hdD, hbelow⟩ := Finset.mem_filter.mp hb
      by_cases h : n ≤ 2 * d ^ 2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hdD, h, by simpa [pow_two] using hbelow⟩))
      · have hlt : 2 * d * d < n := by nlinarith
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hdD, hlt⟩))
  have hinterMA : (M ∩ A').card = 0 := by
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisMA, Finset.card_empty]
  have hBsplit : B.card = M.card + A'.card := by
    have h := Finset.card_union_add_card_inter M A'
    rw [hinterMA, add_zero] at h
    rw [hunMA] at h
    exact h

  have hψ : E_B.card = E_A.card := by
    refine Finset.card_bij' (fun d _ => 2 * (n / d)) (fun e _ => 2 * (n / e)) ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdD, hdEven, hbelow⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
      obtain ⟨r, hr : d = 2 * r⟩ := even_iff_exists_two_mul.mp hdEven
      set q := n / d with hqdef
      have hnd : n = d * q := by
        have h := Nat.mul_div_cancel' hdvd
        simpa [hqdef] using h.symm
      set e := 2 * q with hedef
      have hposr : 0 < r := by
        have hposd : 0 < d := Nat.pos_of_mem_divisors hdD
        omega
      have hposq : 0 < q := by nlinarith
      have heEven : Even e := even_two_mul q
      have hnd2 : n = 2 * r * q := by rw [hnd, hr]
      have hws : n = e * r := by
        have h : e * r = d * q := by rw [hedef, hr]; ring
        rw [h, hnd]
      have hedvd : e ∣ n := ⟨r, hws⟩
      have heD : e ∈ D := Nat.mem_divisors.mpr ⟨hedvd, by linarith⟩
      have habove : above e := by
        rw [hedef]
        nlinarith [hbelow, hr, hnd2]
      exact Finset.mem_filter.mpr ⟨heD, heEven, habove⟩
    · intro e he
      obtain ⟨heD, heEven, habove⟩ := Finset.mem_filter.mp he
      have hevd : e ∣ n := Nat.dvd_of_mem_divisors heD
      obtain ⟨q, heq : e = 2 * q⟩ := even_iff_exists_two_mul.mp heEven
      set r := n / e with hrdef
      have hne : n = e * r := by
        have h := Nat.mul_div_cancel' hevd
        simpa [hrdef] using h.symm
      set d := 2 * r with hddef
      have hposq : 0 < q := by
        have hpose : 0 < e := Nat.pos_of_mem_divisors heD
        omega
      have hdEven : Even d := even_two_mul r
      have hne2 : n = 2 * q * r := by rw [hne, heq]
      have hws : n = d * q := by
        have h : d * q = e * r := by rw [hddef, heq]; ring
        rw [h, hne]
      have hddvd : d ∣ n := ⟨q, hws⟩
      have hdD : d ∈ D := Nat.mem_divisors.mpr ⟨hddvd, by linarith⟩
      have hbelow : below d := by
        rw [hddef]
        nlinarith [habove, heq, hne2]
      exact Finset.mem_filter.mpr ⟨hdD, hdEven, hbelow⟩
    · intro d hd
      obtain ⟨hdD, hdEven, _⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdD
      obtain ⟨r, hr : d = 2 * r⟩ := even_iff_exists_two_mul.mp hdEven
      set q := n / d with hqdef
      have hnd : n = d * q := by
        have h := Nat.mul_div_cancel' hdvd
        simpa [hqdef] using h.symm
      set e := 2 * q with hedef
      have hpose : 0 < e := by nlinarith
      have hne : n = e * r := by rw [hedef, hnd, hr]; ring
      have hedvd : e ∣ n := ⟨r, hne⟩
      have hdiv : e * (n / e) = n := Nat.mul_div_cancel' hedvd
      have hne' : n / e = r := by
        apply Nat.mul_left_cancel hpose
        rw [hdiv, hne]
      have hgoal : 2 * (n / e) = d := by rw [hne', hr]
      exact hgoal
    · intro e he
      obtain ⟨heD, heEven, _⟩ := Finset.mem_filter.mp he
      have hevd : e ∣ n := Nat.dvd_of_mem_divisors heD
      obtain ⟨q, heq : e = 2 * q⟩ := even_iff_exists_two_mul.mp heEven
      set r := n / e with hrdef
      have hne : n = e * r := by
        have h := Nat.mul_div_cancel' hevd
        simpa [hrdef] using h.symm
      have hpose : 0 < e := Nat.pos_of_mem_divisors heD
      have hne' : n / e = r := by
        apply Nat.mul_left_cancel hpose
        have hdiv : e * (n / e) = n := Nat.mul_div_cancel' hevd
        rw [hdiv, hne]
      set d := 2 * r with hddef
      have hposr : 0 < r := by
        by_contra h
        have h0 : r = 0 := by omega
        have hz : n = 0 := by rw [hne, h0, mul_zero]
        linarith
      have hposd : 0 < d := by rw [hddef]; omega
      have hws : n = d * q := by
        have h : d * q = e * r := by rw [hddef, heq]; ring
        rw [h, hne]
      have hddvd : d ∣ n := ⟨q, hws⟩
      have hdiv : d * (n / d) = n := Nat.mul_div_cancel' hddvd
      have hnd' : n / d = q := by
        apply Nat.mul_left_cancel hposd
        rw [hdiv, hws]
      have hgoal : 2 * (n / d) = e := by rw [hnd', heq]
      exact hgoal

  have hBS : B.card = S.card + E_B.card := by
    have hdis : Disjoint S E_B := by
      rw [Finset.disjoint_left]
      intro x hs hb
      obtain ⟨_, ho, _⟩ := Finset.mem_filter.mp hs
      obtain ⟨_, he, _⟩ := Finset.mem_filter.mp hb
      exact Nat.not_even_iff_odd.mpr ho he
    have hun : S ∪ E_B = B := by
      apply Finset.Subset.antisymm
      · intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · obtain ⟨hd, _, hb⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨hd, hb⟩
        · obtain ⟨hd, _, hb⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨hd, hb⟩
      · intro d hb
        obtain ⟨hdD, hbelow⟩ := Finset.mem_filter.mp hb
        by_cases ho : Odd d
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hdD, ho, hbelow⟩))
        · have he : Even d := Nat.not_odd_iff_even.mp ho
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hdD, he, hbelow⟩))
    have hinter : (S ∩ E_B).card = 0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_empty]
    have h := Finset.card_union_add_card_inter S E_B
    rw [hinter, add_zero] at h
    rw [hun] at h
    exact h
  have hAL : A.card = L.card + E_A.card := by
    have hdis : Disjoint L E_A := by
      rw [Finset.disjoint_left]
      intro x hl ha
      obtain ⟨_, ho, _⟩ := Finset.mem_filter.mp hl
      obtain ⟨_, he, _⟩ := Finset.mem_filter.mp ha
      exact Nat.not_even_iff_odd.mpr ho he
    have hun : L ∪ E_A = A := by
      apply Finset.Subset.antisymm
      · intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · obtain ⟨hd, _, ha⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨hd, ha⟩
        · obtain ⟨hd, _, ha⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨hd, ha⟩
      · intro d ha
        obtain ⟨hdD, habove⟩ := Finset.mem_filter.mp ha
        by_cases ho : Odd d
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hdD, ho, habove⟩))
        · have he : Even d := Nat.not_odd_iff_even.mp ho
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hdD, he, habove⟩))
    have hinter : (L ∩ E_A).card = 0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_empty]
    have h := Finset.card_union_add_card_inter L E_A
    rw [hinter, add_zero] at h
    rw [hun] at h
    exact h

  have hBS' : (B.card : ℤ) = S.card + E_B.card := by rw [hBS]; norm_cast
  have hAL' : (A.card : ℤ) = L.card + E_A.card := by rw [hAL]; norm_cast
  have hL4' : (B.card : ℤ) = M.card + A'.card := by rw [hBsplit]; norm_cast
  have hφ' : (A'.card : ℤ) = A.card := by rw [hφ.symm]
  have hψ' : (E_B.card : ℤ) = E_A.card := by rw [hψ]
  have hMid : (S.card : ℤ) = (M.card + L.card : ℤ) := by omega

  have h1 : a n = A067742 n + A131576 n := by
    have hM : A067742 n = M.card := by rfl
    have hS : S.card = M.card + L.card := by omega
    have hha : a n = S.card := by omega
    have hhA : A131576 n = L.card := by omega
    rw [hha, hS, hM, hhA]
  have h2 : (a n : ℤ) = (A001227 n : ℤ) - (A131576 n : ℤ) := by
    rw [ha, hA001227, hA131576]
    ring
  exact ⟨h1, h2⟩
