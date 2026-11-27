import OMAStatements.S_oeis_a000188

-- Problem: OEIS A000188 (residues with square zero versus k with n*k a square)
-- Credit: @JamesSlash
-- Bijection: x maps to x*x/n (and 0 maps to n); inverse k maps to sqrt(n*k) (and n maps to 0).

namespace OMA.A000188Proof

lemma fwd_mem (n x : ℕ) (hn : 1 ≤ n) (hx : x ∈ (Finset.range n).filter (fun x => x * x % n = 0)) :
    (if x = 0 then n else x * x / n) ∈ (Finset.Icc 1 n).filter (fun k => IsSquare (n * k)) := by
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨hxn, hdvd⟩ := hx
  have hd : n ∣ x * x := Nat.dvd_of_mod_eq_zero hdvd
  by_cases h0 : x = 0
  · simp only [h0, if_true, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn, le_rfl⟩, ⟨n, rfl⟩⟩
  · simp only [h0, if_false, Finset.mem_filter, Finset.mem_Icc]
    have hpos : 0 < x := Nat.pos_of_ne_zero h0
    have hxx : n * (x * x / n) = x * x := Nat.mul_div_cancel' hd
    refine ⟨⟨?_, ?_⟩, ⟨x, hxx⟩⟩
    · by_contra hc
      have : x * x / n = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le hc)
      rw [this, mul_zero] at hxx
      have : 0 < x * x := Nat.mul_pos hpos hpos
      omega
    · have hlt : x * x < n * n := Nat.mul_lt_mul'' hxn hxn
      have : n * (x * x / n) < n * n := by rw [hxx]; exact hlt
      exact le_of_lt (Nat.lt_of_mul_lt_mul_left this)

lemma bwd_mem (n k : ℕ) (hn : 1 ≤ n) (hk : k ∈ (Finset.Icc 1 n).filter (fun k => IsSquare (n * k))) :
    (if k = n then 0 else Nat.sqrt (n * k)) ∈ (Finset.range n).filter (fun x => x * x % n = 0) := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hkn⟩, ⟨s, hs⟩⟩ := hk
  by_cases hkeq : k = n
  · simp only [hkeq, if_true, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simp⟩
  · simp only [hkeq, if_false, Finset.mem_filter, Finset.mem_range]
    have hsq : Nat.sqrt (n * k) = s := by rw [hs]; exact Nat.sqrt_eq s
    rw [hsq]
    have hklt : k < n := lt_of_le_of_ne hkn hkeq
    refine ⟨?_, ?_⟩
    · by_contra hc
      have hc' : n ≤ s := Nat.le_of_not_lt hc
      have h1 : n * n ≤ s * s := Nat.mul_le_mul hc' hc'
      have h2 : n * k < n * n := Nat.mul_lt_mul_of_pos_left hklt (by omega)
      omega
    · rw [← hs]
      simp

lemma left_inv' (n x : ℕ) (hx : x ∈ (Finset.range n).filter (fun x => x * x % n = 0)) :
    (if (if x = 0 then n else x * x / n) = n then 0
      else Nat.sqrt (n * (if x = 0 then n else x * x / n))) = x := by
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨hxn, hdvd⟩ := hx
  have hd : n ∣ x * x := Nat.dvd_of_mod_eq_zero hdvd
  by_cases h0 : x = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hxx : n * (x * x / n) = x * x := Nat.mul_div_cancel' hd
    have hne : x * x / n ≠ n := by
      intro he
      rw [he] at hxx
      have hlt : x * x < n * n := Nat.mul_lt_mul'' hxn hxn
      omega
    simp only [hne, if_false, hxx]
    exact Nat.sqrt_eq x

lemma right_inv' (n k : ℕ) (hn : 1 ≤ n) (hk : k ∈ (Finset.Icc 1 n).filter (fun k => IsSquare (n * k))) :
    (if (if k = n then 0 else Nat.sqrt (n * k)) = 0 then n
      else (if k = n then 0 else Nat.sqrt (n * k)) * (if k = n then 0 else Nat.sqrt (n * k)) / n) = k := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hkn⟩, ⟨s, hs⟩⟩ := hk
  by_cases hkeq : k = n
  · simp [hkeq]
  · simp only [hkeq, if_false]
    have hsq : Nat.sqrt (n * k) = s := by rw [hs]; exact Nat.sqrt_eq s
    rw [hsq]
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs
      have : 0 < n * k := Nat.mul_pos (by omega) (by omega)
      omega
    simp only [hs0, if_false]
    rw [← hs]
    exact Nat.mul_div_cancel_left k (by omega)

end OMA.A000188Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000188.main := by
  intro n hn
  exact Finset.card_nbij' (fun x => if x = 0 then n else x * x / n)
    (fun k => if k = n then 0 else Nat.sqrt (n * k))
    (fun x hx => OMA.A000188Proof.fwd_mem n x hn hx)
    (fun k hk => OMA.A000188Proof.bwd_mem n k hn hk)
    (fun x hx => OMA.A000188Proof.left_inv' n x hx)
    (fun k hk => OMA.A000188Proof.right_inv' n k hn hk)
