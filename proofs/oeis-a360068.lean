import OMAStatements.S_oeis_a360068

namespace OMA.S_oeis_a360068.Pf
open OMA.S_oeis_a360068

lemma no_partition (n : ℕ) (hn : 2 ≤ n) (hsq : Squarefree n) (p : Nat.Partition n)
    (h : meanParts p = meanMult p) : False := by
  set k := Multiset.card p.parts with hk
  set d := p.parts.toFinset.card with hd
  have hsum : p.parts.sum = n := p.parts_sum
  have hne : p.parts ≠ 0 := by
    intro h0; rw [h0] at hsum; simp at hsum; omega
  have hk0 : 0 < k := Multiset.card_pos.2 hne
  have hd0 : 0 < d := Finset.card_pos.2 (Multiset.toFinset_nonempty.2 hne)
  have hcount : (∑ x ∈ p.parts.toFinset, p.parts.count x) = k := Multiset.toFinset_sum_count_eq _
  unfold meanParts meanMult at h
  rw [hsum, hcount] at h
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [div_eq_div_iff hkq hdq] at h
  have hnd : n * d = k * k := by exact_mod_cast h
  -- each part is at least 1, so k ≤ n
  have hle : k ≤ n := by
    have : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
    have := Multiset.card_nsmul_le_sum this
    simp only [smul_eq_mul, mul_one] at this
    rw [← hsum]; exact this
  have hdvd : n ∣ k := by
    have : n ∣ k ^ 2 := ⟨d, by rw [sq, ← hnd, mul_comm]⟩
    exact (hsq.dvd_pow_iff_dvd (by norm_num)).1 this
  have hkn : k = n := le_antisymm hle (Nat.le_of_dvd hk0 hdvd)
  -- all parts are 1
  have hall : ∀ x ∈ p.parts, x = 1 := by
    intro x hx
    by_contra hx1
    have hx2 : 2 ≤ x := by have := p.parts_pos hx; omega
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hx
    have h1 : ∀ y ∈ t, 1 ≤ y := fun y hy => p.parts_pos (by rw [ht]; exact Multiset.mem_cons_of_mem hy)
    have := Multiset.card_nsmul_le_sum h1
    simp only [smul_eq_mul, mul_one] at this
    have hs := hsum
    rw [ht, Multiset.sum_cons] at hs
    have hc : k = Multiset.card t + 1 := by rw [hk, ht, Multiset.card_cons]
    omega
  have hd1 : d ≤ 1 := by
    rw [hd]
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [Multiset.mem_toFinset] at ha hb
    rw [hall a ha, hall b hb]
  rw [hkn] at hnd
  have : n * d ≤ n * 1 := Nat.mul_le_mul_left n hd1
  nlinarith

end OMA.S_oeis_a360068.Pf

open OMA.S_oeis_a360068 OMA.S_oeis_a360068.Pf in
theorem OMA.solution : type_of% @OMA.S_oeis_a360068.main := by
  intro n hn hsq
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  exact no_partition n hn hsq p h
