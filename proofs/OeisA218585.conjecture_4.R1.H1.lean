import OMAReductions.R_OeisA218585_conjecture_4_R1

/-! A small-vector argument gives a representation of each split prime by the Eisenstein
norm. Uniqueness in the ordered positive sector identifies both list searches. -/

namespace OMA.SplitPrime

lemma cubicRoot (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ r : ZMod p, r ^ 2 + r + 1 = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hd
  have hc : (u : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
    rfl
  have hne : (u : ZMod p) ≠ 1 := by
    intro h
    have h' : u = 1 := Units.ext h
    simp [h'] at hu
  refine ⟨u, (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)⟩
  linear_combination hc

/-- Pigeonholing a square modulo p gives a nonzero vector with small coordinates. -/
lemma smallVector (p : ℕ) (hp : p.Prime) (r : ZMod p) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ p.sqrt ∧ |b| ≤ p.sqrt ∧
      (a : ZMod p) = r * (b : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := Fin (p.sqrt + 1)
  let f (v : B × B) : ZMod p := (v.1.val : ZMod p) - r * v.2.val
  obtain ⟨v, w, hvw, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simpa [B, ZMod.card] using Nat.lt_succ_sqrt p)
  let a : ℤ := (v.1.val : ℤ) - w.1.val
  let b : ℤ := (v.2.val : ℤ) - w.2.val
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · by_contra! hz
    apply hvw
    apply Prod.ext <;> apply Fin.ext
    · dsimp [a] at hz
      omega
    · dsimp [b] at hz
      omega
  · have hv := v.1.isLt
    have hw := w.1.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [a]
    omega
  · have hv := v.2.isLt
    have hw := w.2.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [b]
    omega
  · dsimp [a, b]
    push_cast
    dsimp [f] at heq
    linear_combination heq

/-- The small norm is a positive multiple of p strictly below 3p.
The residue 2 modulo 3 is impossible for the norm form. -/
lemma integralRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : ℤ, a ^ 2 + a * b + b ^ 2 = p := by
  obtain ⟨r, hr⟩ := cubicRoot p hp hmod
  obtain ⟨a, b, hab, ha, hb, heq⟩ := smallVector p hp r
  let q := a ^ 2 + a * b + b ^ 2
  have hd : (p : ℤ) ∣ q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [q]
    push_cast
    rw [heq]
    linear_combination (b : ZMod p) ^ 2 * hr
  have hpos : 0 < q := by
    dsimp [q]
    rcases hab with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg b, sq_nonneg (a + b)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a, sq_nonneg (a + b)]
  have hs : p.sqrt * p.sqrt < p :=
    lt_of_le_of_ne (Nat.sqrt_le _) (fun h => hp.prime.not_isSquare ⟨_, h.symm⟩)
  have hbound : q < 3 * p := by
    have hs' : (p.sqrt : ℤ) * p.sqrt < p := by exact_mod_cast hs
    have ha' := mul_self_le_mul_self (abs_nonneg a) ha
    have hb' := mul_self_le_mul_self (abs_nonneg b) hb
    rw [abs_mul_abs_self] at ha' hb'
    dsimp [q]
    nlinarith [sq_nonneg (a - b)]
  obtain ⟨k, hk⟩ := hd
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hkpos : 0 < k := pos_of_mul_pos_right (hk ▸ hpos) hp'.le
  have hksmall : k < 3 := by
    rw [hk, mul_comm (3 : ℤ)] at hbound
    exact (mul_lt_mul_iff_right₀ hp').mp hbound
  have hk1 : k = 1 := by
    by_contra h
    have hk2 : k = 2 := by omega
    have hq : a ^ 2 + a * b + b ^ 2 = (p : ℤ) * 2 := by simpa [q, hk2] using hk
    have h3 : (p : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, hmod]
      rfl
    have hbad := congrArg (fun z : ℤ => (z : ZMod 3)) hq
    push_cast at hbad
    rw [h3, one_mul] at hbad
    exact (show ∀ x y : ZMod 3, x ^ 2 + x * y + y ^ 2 ≠ 2 by decide) _ _ hbad
  exact ⟨a, b, by simpa [q, hk1] using hk⟩

/-- Among a, b, and -a-b, two share a weak sign. Each pair has the same norm. -/
lemma nonnegativeRepresentation (p : ℕ) (a b : ℤ) (h : a ^ 2 + a * b + b ^ 2 = p) :
    ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
  have liftPair (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v)
      (hn : u ^ 2 + u * v + v ^ 2 = p) : ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
    refine ⟨u.toNat, v.toNat, ?_⟩
    have he : (u.toNat : ℤ) ^ 2 + (u.toNat : ℤ) * v.toNat + (v.toNat : ℤ) ^ 2 = p := by
      simpa [Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv] using hn
    exact_mod_cast he
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · exact liftPair a b ha hb h
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair a (-a-b) ha hs (by linear_combination h)
    · exact liftPair (-b) (a+b) (by omega) (by omega) (by linear_combination h)
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair b (-a-b) hb hs (by linear_combination h)
    · exact liftPair (-a) (a+b) (by omega) (by omega) (by linear_combination h)
  · exact liftPair (-a) (-b) (by omega) (by omega) (by linear_combination h)

lemma orderedRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ x y : ℕ, 0 < y ∧ y < x ∧ x < p ∧ x ^ 2 + x * y + y ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := integralRepresentation p hp hmod
  obtain ⟨u, v, huv⟩ := nonnegativeRepresentation p a b hab
  obtain ⟨x, y, hle, hn⟩ : ∃ x y : ℕ, y ≤ x ∧ x ^ 2 + x * y + y ^ 2 = p := by
    rcases le_total v u with h | h
    · exact ⟨u, v, h, huv⟩
    · exact ⟨v, u, h, by linarith⟩
  have hy : 0 < y := by
    by_contra! hz
    have he : y = 0 := by omega
    exact hp.prime.not_isSquare ⟨x, by simpa [he, pow_two] using hn.symm⟩
  have hne : y ≠ x := by
    rintro rfl
    have hd : 3 ∣ p := ⟨y ^ 2, by nlinarith⟩
    omega
  refine ⟨x, y, hy, lt_of_le_of_ne hle hne, ?_, hn⟩
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) x, Nat.pow_pos hy (n := 2)]

/-- Swapping the coordinates interchanges the two roots of the norm form modulo p.
In the ordered sector only one cross product can vanish. -/
lemma uniqueSecond (p : ℕ) (hp : p.Prime) (a b c d : ℕ)
    (hb : 0 < b) (hab : b < a) (hd : 0 < d) (hcd : d < c)
    (h₁ : a ^ 2 + a * b + b ^ 2 = p) (h₂ : c ^ 2 + c * d + d ^ 2 = p) : b = d := by
  let : Fact p.Prime := ⟨hp⟩
  have h₁' : (a : ZMod p) ^ 2 + a * b + b ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₁
  have h₂' : (c : ZMod p) ^ 2 + c * d + d ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₂
  have hf : ((a : ZMod p) * d - b * c) * (a * c - b * d) = 0 := by
    linear_combination (c : ZMod p) * d * h₁' - (a : ZMod p) * b * h₂'
  have hac : a * c < p := by
    rcases le_total a c with h | h
    · have hsq := Nat.mul_le_mul_right c h
      nlinarith [Nat.mul_pos (hd.trans hcd) hd]
    · have hsq := Nat.mul_le_mul_left a h
      nlinarith [Nat.mul_pos (hb.trans hab) hb]
  have hbc := Nat.mul_lt_mul_of_pos_right hab (by omega : 0 < c)
  have had := Nat.mul_lt_mul_of_pos_left hcd (by omega : 0 < a)
  have hbd := Nat.mul_lt_mul_of_pos_right hab hd
  have liftEq (u v : ℕ) (hu : u < p) (hv : v < p) (h : (u : ZMod p) = v) : u = v := by
    simpa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using
      (ZMod.natCast_eq_natCast_iff' u v p).mp h
  have hcross : a * d = b * c := by
    rcases mul_eq_zero.mp hf with h | h
    · exact liftEq _ _ (had.trans hac) (hbc.trans hac) (by simpa using sub_eq_zero.mp h)
    · have he := liftEq (a*c) (b*d) hac (hbd.trans (had.trans hac)) (by simpa using sub_eq_zero.mp h)
      omega
  have he : p * d ^ 2 = p * b ^ 2 := calc
    p * d ^ 2 = (a*d) ^ 2 + (a*d)*(b*d) + (b*d) ^ 2 := by rw [← h₁]; ring
    _ = p * b ^ 2 := by rw [hcross, ← h₂]; ring
  have := Nat.eq_of_mul_eq_mul_left hp.pos he
  nlinarith

lemma findWitness (l : List ℕ) (f : ℕ → Bool) (w : ℕ) (hw : w ∈ l) (hf : f w) :
    f ((l.find? f).getD 0) := by
  cases h : l.find? f with
  | none => exact False.elim ((List.find?_eq_none.mp h w hw) hf)
  | some z => exact List.find?_some h

end OMA.SplitPrime

open OeisA218585 OMA.SplitPrime

theorem OMA.solution : OMA.R_OeisA218585_conjecture_4_R1.H1 := by
  intro p hp hmod
  obtain ⟨x, y, hy, hyx, hxp, hn⟩ := orderedRepresentation p hp hmod
  let X (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let Y (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  have specX (u : ℕ) : X u ↔ ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [X]
  have specY (v : ℕ) : Y v ↔ 0 < v ∧ ∃ u, (v + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [Y]
  have hx' : X (xp p) := findWitness (List.range p) X x (List.mem_range.mpr hxp)
    ((specX x).mpr ⟨y, hyx, hy, hn⟩)
  have hy' : Y (yp p) := findWitness (List.range p) Y y (List.mem_range.mpr (hyx.trans hxp))
    ((specY y).mpr ⟨hy, x, ⟨hyx, hxp⟩, hn⟩)
  obtain ⟨v, hvx, hv, h₁⟩ := (specX _).mp hx'
  obtain ⟨hy₀, u, ⟨hyu, _⟩, h₂⟩ := (specY _).mp hy'
  rwa [← uniqueSecond p hp (xp p) v u (yp p) hv hvx hy₀ hyu h₁ h₂]
