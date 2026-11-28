import OMAStatements.S_oeis_a195538
import Mathlib

namespace OMA.S_oeis_a195538

lemma cp_succ (n : ℕ) : convPair (n + 1) =
    ((4 * (convPair n).2.1 + (convPair n).1.1, 4 * (convPair n).2.2 + (convPair n).1.2),
     (5 * (convPair n).2.1 + (convPair n).1.1, 5 * (convPair n).2.2 + (convPair n).1.2)) := rfl

lemma inv (n : ℕ) :
    0 < (convPair n).1.1 ∧ 0 < (convPair n).1.2 ∧ 0 < (convPair n).2.1 ∧ 0 < (convPair n).2.2 ∧
    (convPair n).1.1 * (convPair n).2.2 - (convPair n).1.2 * (convPair n).2.1 = -1 ∧
    (convPair n).1.1 % 2 = 1 ∧ (convPair n).1.2 % 2 = 1 ∧
    ((convPair n).2.1 + (convPair n).2.2) % 2 = 1 := by
  induction n with
  | zero => simp [convPair]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, hc, h5, h6, h7⟩ := ih
    rw [cp_succ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only <;> try omega
    linear_combination hc

lemma cop_of (z1 z2 : ℤ) (hc : IsCoprime z1 z2) :
    IsCoprime (z1 ^ 2 - z2 ^ 2) z1 ∧ IsCoprime (z1 ^ 2 - z2 ^ 2) z2 := by
  constructor
  · have h : IsCoprime (-(z2 ^ 2)) z1 := (hc.symm.pow_left (m := 2)).neg_left
    have h' := h.add_mul_left_left z1
    have e : -(z2 ^ 2) + z1 * z1 = z1 ^ 2 - z2 ^ 2 := by ring
    rwa [e] at h'
  · have h : IsCoprime (z1 ^ 2) z2 := hc.pow_left (m := 2)
    have h' := h.add_mul_left_left (-z2)
    have e : z1 ^ 2 + z2 * -z2 = z1 ^ 2 - z2 ^ 2 := by ring
    rwa [e] at h'

lemma den_opp (z1 z2 : ℤ) (h1 : 0 < z1) (h2 : 0 < z2) (hc : IsCoprime z1 z2)
    (hp : (z1 + z2) % 2 = 1) :
    ((((z1 : ℚ) ^ 2 - (z2 : ℚ) ^ 2) / (2 * (z1 : ℚ) * (z2 : ℚ))).den : ℤ) = 2 * z1 * z2 := by
  obtain ⟨c1, c2⟩ := cop_of z1 z2 hc
  have hodd : Odd (z1 ^ 2 - z2 ^ 2) := by
    have : (z1 ^ 2 - z2 ^ 2) % 2 = 1 := by
      have e : z1 ^ 2 - z2 ^ 2 = (z1 + z2) * (z1 - z2) := by ring
      rw [e, Int.mul_emod]
      have : (z1 - z2) % 2 = 1 := by omega
      rw [hp, this]; norm_num
    exact Int.odd_iff.2 this
  obtain ⟨k, hk⟩ := hodd
  have c3 : IsCoprime (z1 ^ 2 - z2 ^ 2) 2 := ⟨1, -k, by rw [hk]; ring⟩
  have cop : IsCoprime (z1 ^ 2 - z2 ^ 2) (2 * z1 * z2) := (c3.mul_right c1).mul_right c2
  have hN : (((z1 ^ 2 - z2 ^ 2 : ℤ) : ℚ)) = (z1 : ℚ) ^ 2 - (z2 : ℚ) ^ 2 := by push_cast; ring
  have hD : (((2 * z1 * z2 : ℤ) : ℚ)) = 2 * (z1 : ℚ) * (z2 : ℚ) := by push_cast; ring
  rw [← hN, ← hD]
  exact Rat.den_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.1 cop)

lemma den_odd (z1 z2 : ℤ) (h1 : 0 < z1) (h2 : 0 < z2) (hc : IsCoprime z1 z2)
    (hp1 : z1 % 2 = 1) (hp2 : z2 % 2 = 1) :
    ((((z1 : ℚ) ^ 2 - (z2 : ℚ) ^ 2) / (2 * (z1 : ℚ) * (z2 : ℚ))).den : ℤ) = z1 * z2 := by
  obtain ⟨c1, c2⟩ := cop_of z1 z2 hc
  obtain ⟨s, hs⟩ : ∃ s, z1 ^ 2 - z2 ^ 2 = 2 * s := by
    have : (z1 ^ 2 - z2 ^ 2) % 2 = 0 := by
      have e : z1 ^ 2 - z2 ^ 2 = (z1 + z2) * (z1 - z2) := by ring
      rw [e, Int.mul_emod]
      have : (z1 + z2) % 2 = 0 := by omega
      rw [this]; norm_num
    exact ⟨(z1 ^ 2 - z2 ^ 2) / 2, by omega⟩
  have cs1 : IsCoprime s z1 := by
    rw [hs] at c1; exact c1.of_mul_left_right
  have cs2 : IsCoprime s z2 := by
    rw [hs] at c2; exact c2.of_mul_left_right
  have cop : IsCoprime s (z1 * z2) := cs1.mul_right cs2
  have hN : (z1 : ℚ) ^ 2 - (z2 : ℚ) ^ 2 = 2 * (s : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hs
    push_cast at this; exact this
  have hz1 : (z1 : ℚ) ≠ 0 := by positivity
  have hz2 : (z2 : ℚ) ≠ 0 := by positivity
  have e : ((z1 : ℚ) ^ 2 - (z2 : ℚ) ^ 2) / (2 * (z1 : ℚ) * (z2 : ℚ)) =
      (((s : ℤ) : ℚ)) / (((z1 * z2 : ℤ)) : ℚ) := by
    rw [hN]; push_cast; field_simp
  rw [e]
  exact Rat.den_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.1 cop)

lemma aE (m : ℕ) : a (2 * m) = (((convPair m).1.1 * (convPair m).1.2 : ℤ) : ℚ) := by
  obtain ⟨i1, i2, i3, i4, ic, i5, i6, i7⟩ := inv m
  have hc : IsCoprime (convPair m).1.1 (convPair m).1.2 :=
    ⟨-(convPair m).2.2, (convPair m).2.1, by linear_combination (-1 : ℤ) * ic⟩
  have := den_odd _ _ i1 i2 hc i5 i6
  unfold a sourceRatio
  have e1 : 2 * m % 2 = 0 := by omega
  have e2 : 2 * m / 2 = m := by omega
  simp only [e1, e2, if_true]
  have h3 : ((((convPair m).1.1 : ℚ) ^ 2 - ((convPair m).1.2 : ℚ) ^ 2) /
      (2 * ((convPair m).1.1 : ℚ) * ((convPair m).1.2 : ℚ))).den
      = ((convPair m).1.1 * (convPair m).1.2).toNat := by omega
  rw [h3]
  have hpos : 0 < (convPair m).1.1 * (convPair m).1.2 := Int.mul_pos i1 i2
  have : (((((convPair m).1.1 * (convPair m).1.2).toNat : ℕ) : ℤ)) =
      (convPair m).1.1 * (convPair m).1.2 := Int.toNat_of_nonneg hpos.le
  have h4 := congrArg (fun z : ℤ => (z : ℚ)) this
  simp only [Int.cast_natCast] at h4
  exact h4

lemma aO (m : ℕ) : a (2 * m + 1) = 2 * (((convPair m).2.1 * (convPair m).2.2 : ℤ) : ℚ) := by
  obtain ⟨i1, i2, i3, i4, ic, i5, i6, i7⟩ := inv m
  have hc : IsCoprime (convPair m).2.1 (convPair m).2.2 :=
    ⟨(convPair m).1.2, -(convPair m).1.1, by linear_combination (-1 : ℤ) * ic⟩
  have := den_opp _ _ i3 i4 hc i7
  unfold a sourceRatio
  have e1 : (2 * m + 1) % 2 = 1 := by omega
  have e2 : (2 * m + 1) / 2 = m := by omega
  simp only [e1, e2, one_ne_zero, if_false]
  have h3 : ((((convPair m).2.1 : ℚ) ^ 2 - ((convPair m).2.2 : ℚ) ^ 2) /
      (2 * ((convPair m).2.1 : ℚ) * ((convPair m).2.2 : ℚ))).den
      = (2 * (convPair m).2.1 * (convPair m).2.2).toNat := by omega
  rw [h3]
  have hpos : 0 < 2 * (convPair m).2.1 * (convPair m).2.2 := by positivity
  have : ((((2 * (convPair m).2.1 * (convPair m).2.2).toNat : ℕ) : ℤ)) =
      2 * (convPair m).2.1 * (convPair m).2.2 := Int.toNat_of_nonneg hpos.le
  have h4 := congrArg (fun z : ℤ => (z : ℚ)) this
  simp only [Int.cast_natCast] at h4
  push_cast at h4 ⊢
  linear_combination h4

lemma comp_rec (n : ℕ) :
    (convPair (n + 2)).1.1 = 6 * (convPair (n + 1)).1.1 - (convPair n).1.1 ∧
    (convPair (n + 2)).1.2 = 6 * (convPair (n + 1)).1.2 - (convPair n).1.2 ∧
    (convPair (n + 2)).2.1 = 6 * (convPair (n + 1)).2.1 - (convPair n).2.1 ∧
    (convPair (n + 2)).2.2 = 6 * (convPair (n + 1)).2.2 - (convPair n).2.2 := by
  rw [cp_succ (n + 1), cp_succ n]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> ring

lemma prod_rec (u v : ℕ → ℤ) (hu : ∀ n, u (n + 2) = 6 * u (n + 1) - u n)
    (hv : ∀ n, v (n + 2) = 6 * v (n + 1) - v n) (n : ℕ) :
    u (n + 3) * v (n + 3) = 35 * (u (n + 2) * v (n + 2)) - 35 * (u (n + 1) * v (n + 1)) + u n * v n := by
  have h3u : u (n + 3) = 6 * u (n + 2) - u (n + 1) := hu (n + 1)
  have h3v : v (n + 3) = 6 * v (n + 2) - v (n + 1) := hv (n + 1)
  have h2u := hu n
  have h2v := hv n
  rw [h3u, h3v, h2u, h2v]
  ring

lemma PA_rec (n : ℕ) :
    (convPair (n + 3)).1.1 * (convPair (n + 3)).1.2 =
      35 * ((convPair (n + 2)).1.1 * (convPair (n + 2)).1.2) -
      35 * ((convPair (n + 1)).1.1 * (convPair (n + 1)).1.2) + (convPair n).1.1 * (convPair n).1.2 :=
  prod_rec (fun k => (convPair k).1.1) (fun k => (convPair k).1.2)
    (fun k => (comp_rec k).1) (fun k => (comp_rec k).2.1) n

lemma PB_rec (n : ℕ) :
    (convPair (n + 3)).2.1 * (convPair (n + 3)).2.2 =
      35 * ((convPair (n + 2)).2.1 * (convPair (n + 2)).2.2) -
      35 * ((convPair (n + 1)).2.1 * (convPair (n + 1)).2.2) + (convPair n).2.1 * (convPair n).2.2 :=
  prod_rec (fun k => (convPair k).2.1) (fun k => (convPair k).2.2)
    (fun k => (comp_rec k).2.2.1) (fun k => (comp_rec k).2.2.2) n

lemma r3A (m : ℕ) :
    r3 1 5 145 (m + 1) = (((convPair m).1.1 * (convPair m).1.2 : ℤ) : ℚ) ∧
    r3 1 5 145 (m + 2) = (((convPair (m + 1)).1.1 * (convPair (m + 1)).1.2 : ℤ) : ℚ) ∧
    r3 1 5 145 (m + 3) = (((convPair (m + 2)).1.1 * (convPair (m + 2)).1.2 : ℤ) : ℚ) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> simp [r3, convPair] <;> norm_num
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have := PA_rec m
    have hc := congrArg (fun z : ℤ => (z : ℚ)) this
    push_cast at hc
    show 35 * r3 1 5 145 (m + 3) - 35 * r3 1 5 145 (m + 2) + r3 1 5 145 (m + 1) = _
    rw [h1, h2, h3]
    push_cast
    simp only [show m + 1 + 2 = m + 3 from rfl]
    linear_combination (-1 : ℚ) * hc

lemma r3B (m : ℕ) :
    r3 0 12 420 (m + 1) = 2 * (((convPair m).2.1 * (convPair m).2.2 : ℤ) : ℚ) ∧
    r3 0 12 420 (m + 2) = 2 * (((convPair (m + 1)).2.1 * (convPair (m + 1)).2.2 : ℤ) : ℚ) ∧
    r3 0 12 420 (m + 3) = 2 * (((convPair (m + 2)).2.1 * (convPair (m + 2)).2.2 : ℤ) : ℚ) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> simp [r3, convPair] <;> norm_num
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have := PB_rec m
    have hc := congrArg (fun z : ℤ => (z : ℚ)) this
    push_cast at hc
    show 35 * r3 0 12 420 (m + 3) - 35 * r3 0 12 420 (m + 2) + r3 0 12 420 (m + 1) = _
    rw [h1, h2, h3]
    push_cast
    simp only [show m + 1 + 2 = m + 3 from rfl]
    linear_combination (-2 : ℚ) * hc

end OMA.S_oeis_a195538

theorem OMA.solution : type_of% @OMA.S_oeis_a195538.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [show 2 * m + 6 = 2 * (m + 3) by ring, show 2 * m + 4 = 2 * (m + 2) by ring,
        show 2 * m + 2 = 2 * (m + 1) by ring]
      simp only [OMA.S_oeis_a195538.aE]
      have hc := congrArg (fun z : ℤ => (z : ℚ)) (OMA.S_oeis_a195538.PA_rec m)
      push_cast at hc ⊢
      linear_combination hc
    · rw [show 2 * m + 1 + 6 = 2 * (m + 3) + 1 by ring, show 2 * m + 1 + 4 = 2 * (m + 2) + 1 by ring,
        show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring]
      simp only [OMA.S_oeis_a195538.aO]
      have hc := congrArg (fun z : ℤ => (z : ℚ)) (OMA.S_oeis_a195538.PB_rec m)
      push_cast at hc ⊢
      linear_combination 2 * hc
  · intro n
    rw [OMA.S_oeis_a195538.aE, (OMA.S_oeis_a195538.r3A n).1]
  · intro n
    rw [OMA.S_oeis_a195538.aO, (OMA.S_oeis_a195538.r3B n).1]
