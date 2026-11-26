import FormalConjectures.ErdosProblems.«939»

/-!
The binomial construction in the [Erdős Problem 939 discussion](https://www.erdosproblems.com/forum/thread/939)
gives an unbounded family at exponent six. For `x = u^6` and `y = 120^6`,
the odd terms in `(x + y)^6 - (x - y)^6` and the term `(x - y)^6`
give four distinct six-powerful summands.
-/

lemma OMA.full_mul_pow_of_dvd {k a b : ℕ} (hab : a ∣ b) : k.Full (a * b ^ k) := by
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have hb : p ∣ b := (hprime.dvd_mul.mp hdiv).elim
    (fun ha ↦ ha.trans hab) hprime.dvd_of_dvd_pow
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hb k) a

lemma OMA.full_pow (k n : ℕ) : k.Full (n ^ k) := by
  simpa only [one_mul] using OMA.full_mul_pow_of_dvd (k := k) (one_dvd n)

lemma OMA.six_powerful_family (u v : ℕ) (hv : 0 < v) (hu : 2 * v ≤ u) (hv120 : 120 ∣ v)
    (cop_u : u.Coprime v) : ∃ s ∈ Erdos939.Erdos939Sums 6, u ≤ s.sup id := by
  let x := u ^ 6
  let y := v ^ 6
  let z := x - y
  let a := z ^ 6
  let b := 12 * x ^ 5 * y
  let c := 40 * x ^ 3 * y ^ 3
  let d := 12 * x * y ^ 5
  let s : Finset ℕ := {a, b, c, d}
  have h2v : 2 ∣ v := (by decide : 2 ∣ (120 : ℕ)).trans hv120
  have h12v : 12 ∣ v := (by decide : 12 ∣ (120 : ℕ)).trans hv120
  have h40v : 40 ∣ v := (by decide : 40 ∣ (120 : ℕ)).trans hv120
  have hy : 0 < y := pow_pos hv _
  have hdouble : 2 * y ≤ x := calc
    2 * y ≤ 64 * y := by omega
    _ = (2 * v)^6 := by dsimp only [y]; ring
    _ ≤ _ := Nat.pow_le_pow_left hu 6
  have hyx : y < x := by omega
  have hx := hy.trans hyx
  have hz : 0 < z := Nat.sub_pos_of_lt hyx
  have heq : x = z + y := (Nat.sub_add_cancel hyx.le).symm
  have cop_xy : x.Coprime y := (cop_u.pow_left 6).pow_right 6
  have cop_zy : z.Coprime y := (Nat.coprime_sub_self_left hyx.le).mpr cop_xy
  have cop_zx : z.Coprime x := (Nat.coprime_self_sub_left hyx.le).mpr cop_xy.symm
  have cop_zv : z.Coprime v := Nat.Coprime.of_dvd_right (dvd_pow_self v (by decide)) cop_zy
  have cop_z12 : z.Coprime 12 := Nat.Coprime.of_dvd_right h12v cop_zv
  have cop_ad : a.Coprime d := ((cop_z12.mul_right cop_zx).mul_right (cop_zy.pow_right 5)).pow_left 6
  have ha_odd : ¬ 2 ∣ a := by
    intro h
    have hdvd : 2 ∣ Nat.gcd a y := Nat.dvd_gcd h (h2v.trans (dvd_pow_self v (by decide)))
    rw [(cop_zy.pow_left 6).gcd_eq_one] at hdvd
    exact (by decide : ¬ 2 ∣ (1 : ℕ)) hdvd
  have hb_even : 2 ∣ b := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 2 ∣ (12 : ℕ)) _) _
  have hc_even : 2 ∣ c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 2 ∣ (40 : ℕ)) _) _
  have hd_even : 2 ∣ d := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 2 ∣ (12 : ℕ)) _) _
  have hsq : 4 * y^2 ≤ x^2 := calc
    _ = (2 * y)^2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left hdouble 2
  have hy_sq := pow_pos hy 2
  have hcb_coeff : 40 * y^2 < 12 * x^2 := by omega
  have hdc_coeff : 12 * y^2 < 40 * x^2 := by omega
  have hcb : c < b := calc
    c = (40 * y^2) * (x^3 * y) := by dsimp [c]; ring
    _ < (12 * x^2) * (x^3 * y) := by
      exact mul_lt_mul_of_pos_right hcb_coeff (Nat.mul_pos (pow_pos hx 3) hy)
    _ = b := by dsimp [b]; ring
  have hdc : d < c := calc
    d = (12 * y^2) * (x * y^3) := by dsimp [d]; ring
    _ < (40 * x^2) * (x * y^3) := by
      exact mul_lt_mul_of_pos_right hdc_coeff (Nat.mul_pos hx (pow_pos hy 3))
    _ = c := by dsimp [c]; ring
  have ha : a ∉ ({b, c, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hab | hac | had)
    · exact ha_odd (hab.symm ▸ hb_even)
    · exact ha_odd (hac.symm ▸ hc_even)
    · exact ha_odd (had.symm ▸ hd_even)
  have hb : b ∉ ({c, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hcb.ne', (hdc.trans hcb).ne'⟩
  have hc : c ∉ ({d} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hdc.ne'
  have hma : a ∈ s := Finset.mem_insert_self _ _
  have hmd : d ∈ s := by simp only [s, Finset.mem_insert, Finset.mem_singleton, eq_self, or_true]
  have hdpos : 0 < d := Nat.mul_pos (Nat.mul_pos (by decide) hx) (pow_pos hy 5)
  have hs : s ∈ Erdos939.Erdos939Sums 6 := by
    change s.card = 6 - 2 ∧ s.Coprime ∧ (6 : ℕ).Full (∑ n ∈ s, n) ∧
      ∀ n ∈ s, 0 < n ∧ (6 : ℕ).Full n
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [s, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
        Finset.card_insert_of_notMem hc, Finset.card_singleton]
    · change s.gcd id = 1
      have hdiv := Nat.dvd_gcd (Finset.gcd_dvd (f := id) hma) (Finset.gcd_dvd (f := id) hmd)
      exact Nat.dvd_one.mp (cop_ad.gcd_eq_one ▸ hdiv)
    · have hsum : (∑ n ∈ s, n) = (x + y)^6 := by
        simp only [s, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
          Finset.sum_singleton, a, b, c, d]
        rw [heq]
        ring
      rw [hsum]
      exact OMA.full_pow _ _
    · intro n hn
      have hcases : n = a ∨ n = b ∨ n = c ∨ n = d := by
        simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hn
      rcases hcases with hna | hnb | hnc | hnd
      · rw [hna]
        exact ⟨pow_pos hz 6, OMA.full_pow 6 z⟩
      · rw [hnb]
        refine ⟨Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos hx 5)) hy, ?_⟩
        have hform : b = 12 * (u^5 * v)^6 := by dsimp [b, x, y]; ring
        rw [hform]
        exact OMA.full_mul_pow_of_dvd (dvd_mul_of_dvd_right h12v _)
      · rw [hnc]
        refine ⟨Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos hx 3)) (pow_pos hy 3), ?_⟩
        have hform : c = 40 * (u^3 * v^3)^6 := by dsimp [c, x, y]; ring
        rw [hform]
        exact OMA.full_mul_pow_of_dvd (dvd_mul_of_dvd_right (h40v.trans (dvd_pow_self v (by decide))) _)
      · rw [hnd]
        refine ⟨hdpos, ?_⟩
        have hform : d = 12 * (u * v^5)^6 := by dsimp [d, x, y]; ring
        rw [hform]
        exact OMA.full_mul_pow_of_dvd (dvd_mul_of_dvd_right (h12v.trans (dvd_pow_self v (by decide))) _)
  have hdsup : d ≤ s.sup id := Finset.le_sup (f := id) hmd
  have hud : u ∣ d :=
    (dvd_pow_self u (by decide : 6 ≠ 0)).trans
      (dvd_mul_of_dvd_left (dvd_mul_left x 12) (y ^ 5))
  exact ⟨s, hs, (Nat.le_of_dvd hdpos hud).trans hdsup⟩

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.finite := by
  intro hfinite
  have hbounded := ((hfinite 6 (by decide)).image (fun s : Finset ℕ ↦ s.sup id)).bddAbove
  obtain ⟨M, hM⟩ := hbounded
  let u := 1 + (M + 2) * 120
  have hu : 2 * 120 ≤ u := by dsimp [u]; omega
  have cop_u : u.Coprime 120 := by
    dsimp [u]
    rw [Nat.coprime_add_mul_right_left]
    simp
  obtain ⟨s, hs, hus⟩ := OMA.six_powerful_family u 120 (by decide) hu dvd_rfl cop_u
  have hMs : s.sup id ≤ M := hM (Set.mem_image_of_mem _ hs)
  have hMu : M < u := by dsimp [u]; omega
  exact (not_lt_of_ge (hus.trans hMs)) hMu
