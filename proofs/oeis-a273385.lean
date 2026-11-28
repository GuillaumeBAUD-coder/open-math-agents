import OMAStatements.S_oeis_a273385

/-!
# OEIS A273385

Source: OEIS Foundation, https://oeis.org/A273385 (CC BY-SA 4.0).
Entry by Robert Price. Conjectures by Lars Blomberg, Colin Barker, and R. J. Mathar.
Formal statement credited to @yooeonwoo. Proof submitted by @grp06.

The neighborhood geometry and the power-series coefficient comparison adapt the
private A273386 proof (library-scout/rule659-0758/proofs/oeis-a273386.lean).
The accompanying A273386 formalization was submitted by @jleguina.
-/

namespace OMA.A273385Proof

open OMA.S_oeis_a273385 PowerSeries

private def family : Finset ℕ :=
  {659, 667, 723, 731, 931, 939, 947, 955, 995, 1003, 1011, 1019}

private abbrev Profile := ℤ → ℤ → Bool

private def seed : Profile := fun x y => decide (x = 0 ∧ y = 0)
private def axial : Profile := fun x y =>
  !decide ((x = 0 ∧ (y = 1 ∨ y = -1)) ∨ (y = 0 ∧ (x = 1 ∨ x = -1)))
private def ringProfile : Profile := fun x y =>
  !decide (|x| ≤ 1 ∧ |y| ≤ 1 ∧ ¬ (x = 0 ∧ y = 0))
private def hole : Profile := fun x y => !seed x y
private def full : Profile := fun _ _ => true
private def empty : Profile := fun _ _ => false

-- Truth-table index for the center, west, east, south and north bits.
private def localCode (c w e s n : Bool) : ℕ :=
  c.toNat + 2 * (w.toNat + e.toNat + s.toNat + n.toNat)

private def codeAt (f : Profile) (x y : ℤ) : ℕ :=
  localCode (f x y) (f (x - 1) y) (f (x + 1) y) (f x (y - 1)) (f x (y + 1))

private def step (r : ℕ) (f : Profile) : Profile :=
  fun x y => Nat.testBit r (codeAt f x y)

private theorem far_coordinate {x : ℤ} (h : ¬ (-2 ≤ x ∧ x ≤ 2)) :
    ∀ z ∈ ({x - 1, x, x + 1} : Set ℤ), z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1 ∧ ¬ |z| ≤ 1 := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  simp only [abs_le]
  omega

-- Only the following rows of the local table occur in the transient profiles.
private theorem geometry (x y : ℤ) :
    (codeAt seed x y = if seed x y then 1 else if axial x y then 0 else 2) ∧
    (if ringProfile x y then
      codeAt axial x y = 1 ∨ codeAt axial x y = 7 ∨ codeAt axial x y = 9
    else codeAt axial x y = 5 ∨ codeAt axial x y = 8) ∧
    (codeAt ringProfile x y = 1 ∨ codeAt ringProfile x y = 4 ∨
      codeAt ringProfile x y = 7 ∨ codeAt ringProfile x y = 9) ∧
    (codeAt hole x y = 7 ∨ codeAt hole x y = 8 ∨ codeAt hole x y = 9) := by
  by_cases hx : -2 ≤ x ∧ x ≤ 2
  · by_cases hy : -2 ≤ y ∧ y ≤ 2
    · obtain ⟨hx₁, hx₂⟩ := hx
      obtain ⟨hy₁, hy₂⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · obtain ⟨h0,hp,hm,h1⟩ := far_coordinate hy y (by simp)
      obtain ⟨h0p,hpp,hmp,h1p⟩ := far_coordinate hy (y+1) (by simp)
      obtain ⟨h0m,hpm,hmm,h1m⟩ := far_coordinate hy (y-1) (by simp)
      simp [codeAt, localCode, seed, axial, ringProfile, hole,
        h0,hp,hm,h1,h0p,hpp,hmp,h1p,h0m,hpm,hmm,h1m] <;> decide
  · obtain ⟨h0,hp,hm,h1⟩ := far_coordinate hx x (by simp)
    obtain ⟨h0p,hpp,hmp,h1p⟩ := far_coordinate hx (x+1) (by simp)
    obtain ⟨h0m,hpm,hmm,h1m⟩ := far_coordinate hx (x-1) (by simp)
    simp [codeAt, localCode, seed, axial, ringProfile, hole,
      h0,hp,hm,h1,h0p,hpp,hmp,h1p,h0m,hpm,hmm,h1m] <;> decide

private structure FamilyBits (r : ℕ) : Prop where
  bit0 : r.testBit 0 = true
  bit1 : r.testBit 1 = true
  bit2 : r.testBit 2 = false
  bit4 : r.testBit 5 = false → r.testBit 4 = true
  bit7 : r.testBit 7 = true
  bit8 : r.testBit 8 = r.testBit 5
  bit9 : r.testBit 9 = true

private theorem familyBits (r : ℕ) (hr : r ∈ family) : FamilyBits r := by
  simp only [family, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst r <;> constructor <;> decide

private theorem state_step (r t : ℕ) : state r (t + 1) = step r (state r t) := rfl

private theorem seed_step (r : ℕ) (hr : FamilyBits r) : step r seed = axial := by
  funext x y
  change r.testBit (codeAt seed x y) = axial x y
  rw [(geometry x y).1]
  cases hs : seed x y
  · cases ha : axial x y <;> simp [hs, ha, hr.bit0, hr.bit2]
  · have ha : axial x y = true := by
      have hz : x = 0 ∧ y = 0 := by simpa [seed] using hs
      simp [axial, hz.1, hz.2]
    simp [hs, ha, hr.bit1]

private theorem axial_step (r : ℕ) (hr : FamilyBits r) :
    step r axial = if r.testBit 5 then full else ringProfile := by
  funext x y
  have hcode := (geometry x y).2.1
  cases h : ringProfile x y
  · have hc : codeAt axial x y = 5 ∨ codeAt axial x y = 8 := by
      simpa [h] using hcode
    have ht : r.testBit (codeAt axial x y) = r.testBit 5 := by
      rcases hc with hc | hc
      · rw [hc]
      · rw [hc, hr.bit8]
    unfold step
    rw [ht]
    cases hb : r.testBit 5 <;> simp [hb, h, full]
  · have hc : codeAt axial x y = 1 ∨ codeAt axial x y = 7 ∨
        codeAt axial x y = 9 := by simpa [h] using hcode
    have ht : r.testBit (codeAt axial x y) = true := by
      rcases hc with hc | hc | hc
      · rw [hc, hr.bit1]
      · rw [hc, hr.bit7]
      · rw [hc, hr.bit9]
    unfold step
    rw [ht]
    cases hb : r.testBit 5 <;> simp [hb, h, full]

private theorem ring_step (r : ℕ) (hr : FamilyBits r) (hb : r.testBit 5 = false) :
    step r ringProfile = full := by
  funext x y
  change r.testBit (codeAt ringProfile x y) = true
  rcases (geometry x y).2.2.1 with h | h | h | h
  · rw [h, hr.bit1]
  · rw [h, hr.bit4 hb]
  · rw [h, hr.bit7]
  · rw [h, hr.bit9]

private theorem full_step (r : ℕ) (hr : FamilyBits r) : step r full = full := by
  funext x y
  exact hr.bit9

private theorem family_one (r : ℕ) (hr : FamilyBits r) : state r 1 = axial := by
  exact seed_step r hr

private theorem family_three (r : ℕ) (hr : FamilyBits r) : state r 3 = full := by
  have htwo : state r 2 = if r.testBit 5 then full else ringProfile := by
    rw [state_step r 1, family_one r hr]
    exact axial_step r hr
  rw [state_step r 2, htwo]
  cases hb : r.testBit 5
  · simpa [hb] using ring_step r hr hb
  · simpa [hb] using full_step r hr

private theorem family_full (r : ℕ) (hr : FamilyBits r) (t : ℕ) (ht : 3 ≤ t) :
    state r t = full := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : t = 2
    · subst t
      exact family_three r hr
    · rw [state_step, ih (by omega)]
      exact full_step r hr

private theorem five_one : state 5 1 = hole := by
  change step 5 seed = hole
  funext x y
  change Nat.testBit 5 (codeAt seed x y) = !seed x y
  rw [(geometry x y).1]
  cases seed x y <;> cases axial x y <;> decide

private theorem five_two : state 5 2 = empty := by
  rw [state_step 5 1, five_one]
  funext x y
  change Nat.testBit 5 (codeAt hole x y) = false
  rcases (geometry x y).2.2.2 with h | h | h <;> rw [h] <;> decide

private theorem five_parity (t : ℕ) (ht : 2 ≤ t) :
    state 5 t = if t % 2 = 1 then full else empty := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : t = 1
    · subst t
      exact five_two
    · rw [state_step, ih (by omega)]
      by_cases hodd : t % 2 = 1
      · have hn : ¬ (t + 1) % 2 = 1 := by omega
        rw [if_pos hodd, if_neg hn]
        funext x y
        change Nat.testBit 5 9 = false
        decide
      · have hn : (t + 1) % 2 = 1 := by omega
        rw [if_neg hodd, if_pos hn]
        funext x y
        change Nat.testBit 5 0 = true
        decide

private theorem count_zero (r : ℕ) : count r 0 = 1 := by
  have box : Finset.Icc (0 : ℤ) 0 = {0} := by simp
  unfold count
  change (((Finset.Icc (0 : ℤ) 0) ×ˢ Finset.Icc (0 : ℤ) 0).filter
    (fun p => seed p.1 p.2 = true)).card = 1
  rw [box] <;> decide +kernel

private theorem count_one (r : ℕ) (hr : FamilyBits r) : count r 1 = 5 := by
  have box : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold count
  rw [family_one r hr]
  change (((Finset.Icc (-1 : ℤ) 1) ×ˢ Finset.Icc (-1 : ℤ) 1).filter
    (fun p => axial p.1 p.2 = true)).card = 5
  rw [box] <;> decide +kernel

private theorem count_full (r t : ℕ) (hs : state r t = full) :
    count r t = (2 * t + 1)^2 := by
  have hf : ∀ p ∈ (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t),
      full p.1 p.2 = true := by
    intros
    rfl
  have h : ((t : ℤ) + 1 - -(t : ℤ)).toNat = 2 * t + 1 := by omega
  unfold count
  rw [hs, Finset.filter_true_of_mem hf]
  simp only [Finset.card_product, Int.card_Icc, h, pow_two]

private theorem sample_ge (n : ℕ) (hn : 2 ≤ n) : 3 ≤ 2 ^ n - 1 := by
  have h : 2 ^ 2 ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

private theorem sample_odd (n : ℕ) (hn : 2 ≤ n) : (2 ^ n - 1) % 2 = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have hp := sample_ge (n + 1) hn
    rw [pow_succ] at hp ⊢
    omega

private theorem baseBits : FamilyBits 659 := familyBits 659 (by decide)

private theorem agree_family (r : ℕ)
    (hr : r ∈ ({667, 723, 731, 931, 939, 947, 955, 995, 1003, 1011, 1019} : Finset ℕ))
    (n : ℕ) : count r (2 ^ n - 1) = a n := by
  have hb : FamilyBits r := familyBits r (Finset.mem_insert_of_mem hr)
  unfold a
  by_cases hn : 2 ≤ n
  · have hs := sample_ge n hn
    rw [count_full r _ (family_full r hb _ hs),
      count_full 659 _ (family_full 659 baseBits _ hs)]
  · have hn' : n ≤ 1 := by omega
    interval_cases n
    · exact (count_zero r).trans (count_zero 659).symm
    · exact (count_one r hb).trans (count_one 659 baseBits).symm

private theorem a_square (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = (2 ^ (n + 1) - 1)^2 := by
  unfold a
  rw [count_full 659 _ (family_full 659 baseBits _ (sample_ge n hn))]
  push_cast [Nat.cast_sub (Nat.one_le_pow n 2 (by decide))]
  rw [pow_succ (2 : ℤ) n]
  ring

private theorem a_exp (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n + 1 := by
  rw [a_square n hn, pow_succ (2 : ℤ) n]
  have h : (4 : ℤ)^n = (2^n)^2 := by
    rw [show (4 : ℤ) = 2^2 by norm_num, ← pow_mul, Nat.mul_comm 2 n, pow_mul]
  rw [h]
  ring

private theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  rw [a_exp n (by omega), a_exp (n - 1) (by omega),
    a_exp (n - 2) (by omega), a_exp (n - 3) (by omega)]
  have e0 : n = (n - 3) + 3 := by omega
  have e1 : n - 1 = (n - 3) + 2 := by omega
  have e2 : n - 2 = (n - 3) + 1 := by omega
  rw [e1, e2]
  conv_lhs => rw [e0]
  simp only [pow_add]
  ring

private theorem a_zero : a 0 = 1 := count_zero 659
private theorem a_one : a 1 = 5 := count_one 659 baseBits

private theorem generating_of_coefficients (f : ℕ → ℤ)
    (h0 : f 0 = 1) (h1 : f 1 = 5) (h2 : f 2 = 49)
    (h3 : f 3 = 225) (h4 : f 4 = 961)
    (rec : ∀ n : ℕ, 4 < n → f n = 7*f (n-1)-14*f (n-2)+8*f (n-3)) :
    mk f * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 28 * X ^ 2 - 56 * X ^ 3 + 32 * X ^ 4 := by
  let d : ℤ⟦X⟧ := (1 - X) * (1 - 2 * X) * (1 - 4 * X)
  let b : ℤ⟦X⟧ := 1 - 2 * X + 28 * X ^ 2 - 56 * X ^ 3 + 32 * X ^ 4
  change mk f * d = b
  rw [mul_comm (mk f) d]
  have eqd : d = 1 - C 7 * X^1 + C 14 * X^2 - C 8 * X^3 := by
    simp only [d, map_ofNat, pow_one]
    ring
  have eqb : b = 1 - C 2 * X^1 + C 28 * X^2 - C 56 * X^3 + C 32 * X^4 := by
    simp only [b, map_ofNat, pow_one]
  rw [eqd, eqb]
  ext n
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, coeff_mk]
  by_cases hn : 4 < n
  · have n0 : n ≠ 0 := by omega
    have n1 : n ≠ 1 := by omega
    have n2 : n ≠ 2 := by omega
    have n3 : n ≠ 3 := by omega
    have n4 : n ≠ 4 := by omega
    simp [n0, n1, n2, n3, n4,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith [rec n hn]
  · have hle : n ≤ 4 := by omega
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4]

private theorem generating_function :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 28 * X ^ 2 - 56 * X ^ 3 + 32 * X ^ 4 := by
  apply generating_of_coefficients
  · norm_num [a_zero]
  · norm_num [a_one]
  · exact (a_square 2 (by decide)).trans (by norm_num)
  · exact (a_square 3 (by decide)).trans (by norm_num)
  · exact (a_square 4 (by decide)).trans (by norm_num)
  · exact recurrence

private theorem agree_five (n : ℕ) (hn : 2 ≤ n) : a n = count 5 (2 ^ n - 1) := by
  have hs := sample_ge n hn
  have hf : state 5 (2 ^ n - 1) = full := by
    rw [five_parity _ (by omega), if_pos (sample_odd n hn)]
  unfold a
  rw [count_full 659 _ (family_full 659 baseBits _ hs), count_full 5 _ hf]

theorem solution : type_of% @OMA.S_oeis_a273385.main :=
  ⟨agree_family, fun n hn => ⟨a_exp n (by omega), a_square n (by omega)⟩,
    recurrence, generating_function, agree_five⟩

end OMA.A273385Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a273385.main := OMA.A273385Proof.solution
