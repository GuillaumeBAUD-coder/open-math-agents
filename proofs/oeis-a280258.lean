import OMAStatements.S_oeis_a280258
import Mathlib

namespace OMA.A280258Proof

open OMA.S_oeis_a280258

private lemma odd_pxi_of_even {m : ℕ} (hm : Even m) : Odd (pxi m) := by
  unfold pxi
  refine Finset.prod_induction (fun k => k) Odd (fun _ _ ha hb => ha.mul hb) odd_one ?_
  intro k hk
  have hcop : Nat.Coprime k m := (Finset.mem_filter.mp hk).2
  rcases Nat.even_or_odd k with ⟨c, hc⟩ | hodd
  · exfalso
    obtain ⟨r, hr⟩ := hm
    have h2 : 2 ∣ Nat.gcd k m := Nat.dvd_gcd ⟨c, by omega⟩ ⟨r, by omega⟩
    rw [hcop.gcd_eq_one] at h2
    exact absurd (Nat.le_of_dvd (by decide) h2) (by decide)
  · exact hodd

private lemma pxi_one : pxi 1 = 1 := by decide

private lemma even_pxi_of_odd_gt_one {m : ℕ} (hm : Odd m) (hm1 : 1 < m) : Even (pxi m) := by
  rw [even_iff_two_dvd]
  unfold pxi
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, Nat.coprime_two_left.mpr hm⟩

private lemma zmod2_eq_zero_iff_even (x : ℕ) : ((x : ZMod 2) = 0) ↔ Even x := by
  rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

private lemma zmod2_eq_one_iff_odd (x : ℕ) : ((x : ZMod 2) = 1) ↔ Odd x := by
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h0 : ((k + k : ℕ) : ZMod 2) = 0 := (zmod2_eq_zero_iff_even _).mpr ⟨k, rfl⟩
    rw [h0]
    simp [Nat.not_odd_iff_even.mpr ⟨k, rfl⟩]
  · have h1 : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
      have h2 : (2 : ZMod 2) = 0 := rfl
      push_cast; rw [h2]; ring
    rw [h1]
    simp

private lemma odd_card_divisors_iff_exists_sq {m : ℕ} (hm : 0 < m) :
    Odd m.divisors.card ↔ ∃ k : ℕ, m = k ^ 2 := by
  set S1 := m.divisors.filter (fun d => d < m / d)
  set S2 := m.divisors.filter (fun d => m / d < d)
  set S0 := m.divisors.filter (fun d => d = m / d)
  have h12 : S1.card = S2.card := by
    refine Finset.card_bij (fun d _ => m / d) ?_ ?_ ?_
    · intro d hd
      simp only [S1, S2, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      have hd_dvd : d ∣ m := hd.1.1
      have hdiv : m / (m / d) = d := Nat.div_div_self hd_dvd hm.ne'
      exact ⟨⟨Nat.div_dvd_of_dvd hd_dvd, hm.ne'⟩, by rw [hdiv]; exact hd.2⟩
    · intro d1 hd1 d2 hd2 h
      simp only [S1, Finset.mem_filter, Nat.mem_divisors] at hd1 hd2
      have h1 : m / (m / d1) = d1 := Nat.div_div_self hd1.1.1 hm.ne'
      have h2 : m / (m / d2) = d2 := Nat.div_div_self hd2.1.1 hm.ne'
      rw [← h1, ← h2, h]
    · intro e he
      simp only [S1, S2, Finset.mem_filter, Nat.mem_divisors] at he ⊢
      have he_dvd : e ∣ m := he.1.1
      have hdiv : m / (m / e) = e := Nat.div_div_self he_dvd hm.ne'
      exact ⟨m / e, ⟨⟨Nat.div_dvd_of_dvd he_dvd, hm.ne'⟩, by rw [hdiv]; exact he.2⟩, hdiv⟩
  have hpart : m.divisors.card = S1.card + S2.card + S0.card := by
    have hdisj12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_filter]
      intro d _ h1 h2; omega
    have hdisj120 : Disjoint (S1 ∪ S2) S0 := by
      rw [Finset.disjoint_left]
      intro d hd12 hd0
      simp only [S1, S2, S0, Finset.mem_union, Finset.mem_filter] at hd12 hd0
      rcases hd12 with h1 | h2 <;> omega
    have hunion : S1 ∪ S2 ∪ S0 = m.divisors := by
      ext d
      simp only [S1, S2, S0, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hd
        rcases lt_trichotomy d (m / d) with h | h | h
        · exact Or.inl (Or.inl ⟨hd, h⟩)
        · exact Or.inr ⟨hd, h⟩
        · exact Or.inl (Or.inr ⟨hd, h⟩)
    rw [← hunion, Finset.card_union_of_disjoint hdisj120, Finset.card_union_of_disjoint hdisj12]
  rw [hpart, h12, ← two_mul]
  constructor
  · intro hodd
    have hS0_ne : S0.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.card_empty, add_zero] at hodd
      exact Nat.not_odd_iff_even.mpr ⟨S2.card, by omega⟩ hodd
    obtain ⟨k, hk⟩ := hS0_ne
    simp only [S0, Finset.mem_filter, Nat.mem_divisors] at hk
    refine ⟨k, ?_⟩
    have hmul : k * (m / k) = m := Nat.mul_div_cancel' hk.1.1
    rw [← hk.2, ← sq] at hmul
    exact hmul.symm
  · rintro ⟨k, rfl⟩
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hm
      · exact hpos
    have hS0 : S0 = {k} := by
      ext d
      simp only [S0, Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd_dvd, _⟩, hdeq⟩
        have hmul : d * d = k * k := by
          have := Nat.mul_div_cancel' hd_dvd
          rw [← hdeq] at this
          simpa [sq] using this
        nlinarith
      · rintro rfl
        refine ⟨⟨⟨d, by rw [sq]⟩, hm.ne'⟩, ?_⟩
        rw [sq, Nat.mul_div_cancel _ hk_pos]
    rw [hS0, Finset.card_singleton]
    exact ⟨S2.card, rfl⟩

private lemma even_a_iff {n : ℕ} (hn : 1 ≤ n) :
    Even (a n) ↔ ∃ k : ℕ, n = 2 * k ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have ha_mod : (a n : ZMod 2) = 1 + ((n.divisors.filter Even).card : ZMod 2) := by
    unfold a
    push_cast
    have hterm : ∀ d ∈ n.divisors, (pxi d : ZMod 2) = if d = 1 ∨ Even d then 1 else 0 := by
      intro d hd
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
      by_cases h1 : d = 1
      · subst h1; simp [pxi_one]
      · rcases Nat.even_or_odd d with he | ho
        · simp [he, (zmod2_eq_one_iff_odd _).mpr (odd_pxi_of_even he)]
        · have hnot : ¬ Even d := Nat.not_even_iff_odd.mpr ho
          simp [h1, hnot, (zmod2_eq_zero_iff_even _).mpr (even_pxi_of_odd_gt_one ho (by omega))]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    have hfilt : n.divisors.filter (fun d => d = 1 ∨ Even d) =
        insert 1 (n.divisors.filter Even) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hd, rfl | he⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hd, he⟩
      · rintro (rfl | ⟨hd, he⟩)
        · exact ⟨Nat.one_mem_divisors.mpr hn0, Or.inl rfl⟩
        · exact ⟨hd, Or.inr he⟩
    have h1not : (1 : ℕ) ∉ n.divisors.filter Even := by
      simp
    rw [hfilt, Finset.card_insert_of_notMem h1not]
    push_cast
    ring
  rw [← zmod2_eq_zero_iff_even, ha_mod]
  have h1add : ∀ x : ZMod 2, (1 + x = 0) ↔ x = 1 := by decide
  rw [h1add, zmod2_eq_one_iff_odd]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hn2m : n = 2 * m := by omega
    have hm_pos : 0 < m := by omega
    have hcard : (n.divisors.filter Even).card = m.divisors.card := by
      have himg : n.divisors.filter Even = m.divisors.image (fun d => 2 * d) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨⟨q, hq⟩, _⟩, ⟨d, rfl⟩⟩
          refine ⟨d, ⟨⟨q, ?_⟩, hm_pos.ne'⟩, by omega⟩
          have : 2 * m = 2 * (d * q) := by
            rw [← hn2m, hq]; ring
          omega
        · rintro ⟨d, ⟨⟨q, hq⟩, _⟩, rfl⟩
          refine ⟨⟨⟨q, ?_⟩, hn0⟩, ⟨d, by omega⟩⟩
          rw [hn2m, hq]; ring
      rw [himg, Finset.card_image_of_injective _ (fun x y h => by omega)]
    rw [hcard, odd_card_divisors_iff_exists_sq hm_pos]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · have hempty : n.divisors.filter Even = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd he
      have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      obtain ⟨r, rfl⟩ := he
      obtain ⟨q, hq⟩ := hd_dvd
      obtain ⟨t, ht⟩ := hodd
      have h2 : 2 ∣ n := ⟨r * q, by rw [hq]; ring⟩
      obtain ⟨s, hs⟩ := h2
      omega
    rw [hempty, Finset.card_empty]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨k, hk⟩
      obtain ⟨t, ht⟩ := hodd
      omega

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    ((¬ ∃ k : ℕ, n = 2 * k ^ 2) → Odd (a n)) ∧ ((∃ k : ℕ, n = 2 * k ^ 2) → Even (a n)) := by
  intro n hn
  constructor
  · intro h
    rw [← Nat.not_even_iff_odd]
    exact mt (even_a_iff hn).mp h
  · exact (even_a_iff hn).mpr

end OMA.A280258Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a280258.main :=
  OMA.A280258Proof.main_proof
