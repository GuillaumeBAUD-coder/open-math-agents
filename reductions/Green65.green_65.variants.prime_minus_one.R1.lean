import FormalConjectures.GreensOpenProblems.«65»
import Mathlib.Analysis.Fourier.ZMod

/-! A finite Fourier reduction for shifted-prime differences, following Section 2 of
Ben Green, On Sárközy’s theorem for shifted primes (arXiv:2206.08001). -/

namespace OMA.R_Green65_green_65_variants_prime_minus_one_R1

open Filter
open Finset
open scoped Pointwise ComplexConjugate

/-- Green's Theorem 1.2, expressed by a normalized cosine polynomial with a
power-saving constant coefficient and shifted-prime frequencies. -/
def H1 : Prop :=
  ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    ∃ (P : Finset ℕ) (c : ℝ) (b : ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ p ≤ N) ∧ (c + ∑ p ∈ P, b p = 1) ∧
      (∀ t : ℝ, 0 ≤ c + ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p-1 : ℕ) * t)) ∧
      c ≤ C * (N : ℝ) ^ (-η)

/-- The zero Fourier mode bounds the quadratic form of a finite set from below. -/
def H2 : Prop :=
  ∀ (M : ℕ) [NeZero M] (A : Finset (ZMod M)) (K : ZMod M → ℝ),
    (∑ x, K x) = 1 →
    (∀ r, ∃ t : ℝ, 0 ≤ t ∧ ZMod.dft (fun x => (K x : ℂ)) r = (t : ℂ)) →
    (A.card : ℝ) ^ 2 ≤ (M : ℝ) * ∑ x ∈ A, ∑ y ∈ A, K (x - y)



lemma green_char_conj {M : ℕ} [NeZero M] (x : ZMod M) :
    ZMod.stdAddChar (-x) = conj (ZMod.stdAddChar x) := by
  change (↑(ZMod.toCircle (-x)) : ℂ) = conj (↑(ZMod.toCircle x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma green_symmetrized_spectrum {M : ℕ} [NeZero M] (a : ZMod M → ℝ) (r : ZMod M) :
    ZMod.dft (fun u => (((a u + a (-u))/2 : ℝ) : ℂ)) r =
      ((∑ j : ZMod M, a j * (ZMod.stdAddChar (j*r)).re : ℝ) : ℂ) := by
  have hneg : (∑ j : ZMod M, ZMod.stdAddChar (-(j*r)) * (a (-j) : ℂ)) =
      ∑ j : ZMod M, ZMod.stdAddChar (j*r) * (a j : ℂ) := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by simp)
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
    mul_div_assoc', mul_add, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hneg, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [green_char_conj, ← add_mul, add_comm (conj _), Complex.add_conj]
  push_cast
  ring

lemma green_char_to_cos {M : ℕ} [NeZero M] (d : ℕ) (r : ZMod M) :
    (ZMod.stdAddChar ((d : ZMod M) * r)).re =
      Real.cos (2 * Real.pi * d * ((r.val : ℝ) / M)) := by
  have he : (d : ZMod M) * r = (((d : ℤ) * (r.val : ℤ) : ℤ) : ZMod M) := by simp
  rw [he, ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

lemma green_kernel_of_cosine (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ N)
    (c : ℝ) (b : ℕ → ℝ) (hmean : c + ∑ p ∈ P, b p = 1)
    (hpos : ∀ t : ℝ, 0 ≤ c + ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p-1:ℕ) * t)) :
    ∃ K : ZMod (2*N+1) → ℝ,
      (∑ x, K x) = 1 ∧
      (∀ r, ∃ t : ℝ, 0 ≤ t ∧ ZMod.dft (fun x => (K x : ℂ)) r = (t : ℂ)) ∧
      (∀ x, x ≠ 0 → K x ≠ 0 → ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
        (x = (p : ZMod (2*N+1)) - 1 ∨ x = -((p : ZMod (2*N+1)) - 1))) ∧
      K 0 = c := by
  classical
  let d (p : ℕ) : ZMod (2*N+1) := ↑(p-1)
  let a (x : ZMod (2*N+1)) := (if x = 0 then c else 0) + ∑ p ∈ P, if d p = x then b p else 0
  have hw (f : ZMod (2*N+1) → ℝ) : ∑ x, a x * f x = c * f 0 + ∑ p ∈ P, b p * f (d p) := by
    simp only [a, add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm (s:=univ) (t:=P)]
    simp
  have hd (p : ℕ) (hp : p ∈ P) : d p ≠ 0 := by
    have h2 := (hP p hp).1.two_le
    have hn := (hP p hp).2
    intro h
    have := congrArg ZMod.val h
    rw [show (d p).val = p-1 from ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at this
    omega
  have haz : a 0 = c := by simp [a, Finset.sum_eq_zero (fun p hp => if_neg (hd p hp))]
  have hs (x : ZMod (2*N+1)) (hx : x ≠ 0) (h : a x ≠ 0) : ∃ p ∈ P, d p = x := by
    by_contra! hn
    exact h (by simp [a, hx, Finset.sum_eq_zero (fun p hp => if_neg (hn p hp))])
  refine ⟨fun x => (a x + a (-x))/2, ?_, ?_, ?_, ?_⟩
  · have ha : ∑ x, a x = 1 := by simpa using (hw (fun _ => 1)).trans (by simpa using hmean)
    have hf : ∑ x, a (-x) = ∑ x, a x := Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
    rw [← Finset.sum_div, Finset.sum_add_distrib, hf, ha]
    norm_num
  · intro r
    have hc := hw (fun x => (ZMod.stdAddChar (x*r)).re)
    simp only [zero_mul, AddChar.map_zero_eq_one, Complex.one_re, mul_one, d, green_char_to_cos] at hc
    refine ⟨_, hpos ((r.val:ℝ)/(2*N+1:ℕ)), ?_⟩
    rw [green_symmetrized_spectrum, hc]
  · intro x hx hK
    have hn : a x ≠ 0 ∨ a (-x) ≠ 0 := by by_contra! h; simp [h.1,h.2] at hK
    rcases hn with h | h
    · obtain ⟨p, hp, hpx⟩ := hs x hx h
      refine ⟨p,(hP p hp).1,(hP p hp).2,Or.inl ?_⟩
      simpa [d, Nat.cast_sub (hP p hp).1.one_le] using hpx.symm
    · obtain ⟨p, hp, hpx⟩ := hs (-x) (neg_ne_zero.mpr hx) h
      refine ⟨p,(hP p hp).1,(hP p hp).2,Or.inr ?_⟩
      simpa [d, Nat.cast_sub (hP p hp).1.one_le] using congrArg Neg.neg hpx.symm
  · simp [haz]

lemma lift_bounded_residue {N : ℕ} {x y : ℤ} (hx : -(N : ℤ) ≤ x ∧ x ≤ N)
    (hy : -(N : ℤ) ≤ y ∧ y ≤ N)
    (h : (x : ZMod (2 * N + 1)) = (y : ZMod (2 * N + 1))) : x = y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y (2 * N + 1)).mp h
  have hlt : |y - x| < ((2 * N + 1 : ℕ) : ℤ) := by
    rw [abs_lt]
    push_cast
    omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

lemma interval_image_card {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ)) :
    (A.image (fun a : ℤ => (a : ZMod (2 * N + 1)))).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp (hA ha)
  obtain ⟨hb1,hbN⟩ := Finset.mem_Icc.mp (hA hb)
  exact lift_bounded_residue (by constructor <;> omega) (by constructor <;> omega) hab

lemma interval_prime_witness {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ))
    {a b : ZMod (2 * N + 1)}
    (ha : a ∈ A.image (fun z : ℤ => (z : ZMod (2 * N + 1))))
    (hb : b ∈ A.image (fun z : ℤ => (z : ZMod (2 * N + 1))))
    {p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hd : a-b = (p : ZMod (2 * N + 1)) - 1 ∨ a-b = -((p : ZMod (2 * N + 1)) - 1)) :
    ∃ d ∈ A - A, Green65.IsPrimeMinusOne d := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hx1,hxN⟩ := Finset.mem_Icc.mp (hA hx)
  obtain ⟨hy1,hyN⟩ := Finset.mem_Icc.mp (hA hy)
  have hp0 := hp.two_le
  have h₁ : -(N : ℤ) ≤ (p : ℤ) - 1 ∧ (p : ℤ) - 1 ≤ N := by omega
  rcases hd with hd | hd
  · refine ⟨x-y, Finset.sub_mem_sub hx hy, p, hp, ?_⟩
    exact lift_bounded_residue (by constructor <;> omega) h₁ (by push_cast; exact hd)
  · refine ⟨y-x, Finset.sub_mem_sub hy hx, p, hp, ?_⟩
    apply lift_bounded_residue (by constructor <;> omega) h₁
    push_cast
    linear_combination -hd

lemma interval_image_kernel_sum {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ))
    (havoid : ¬ ∃ d ∈ A - A, Green65.IsPrimeMinusOne d)
    (K : ZMod (2 * N + 1) → ℝ)
    (hK : ∀ t, t ≠ 0 → K t ≠ 0 → ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
      (t = (p : ZMod (2 * N + 1)) - 1 ∨ t = -((p : ZMod (2 * N + 1)) - 1))) :
    let S := A.image (fun z : ℤ => (z : ZMod (2 * N + 1)))
    ∑ a ∈ S, ∑ b ∈ S, K (a-b) = (A.card : ℝ) * K 0 := by
  classical
  dsimp only
  set S := A.image (fun z : ℤ => (z : ZMod (2 * N + 1)))
  have hinner (a) (ha : a ∈ S) : ∑ b ∈ S, K (a-b) = K 0 := by
    rw [Finset.sum_eq_single_of_mem a ha, sub_self]
    intro b hb hba
    by_contra hne
    obtain ⟨p, hp, hpN, hd⟩ := hK (a-b) (sub_ne_zero.mpr hba.symm) hne
    exact havoid (interval_prime_witness A hA ha hb hp hpN hd)
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  rw [show S.card = A.card from interval_image_card A hA]

theorem main : H1 → H2 → type_of% @Green65.green_65.variants.prime_minus_one := by
  classical
  rintro ⟨η, C, hη, hC, hcert⟩ henergy
  let c := min (η / 2) (1 / 2 : ℝ)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  have hcη : c < η := lt_of_le_of_lt (min_le_left ..) (by linarith)
  refine ⟨c, hc, lt_of_le_of_lt (min_le_right ..) (by norm_num), ?_⟩
  have hgrowth := (tendsto_rpow_atTop (sub_pos.mpr hcη)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hcert, hgrowth.eventually_gt_atTop (3 * C), eventually_ge_atTop (1 : ℕ)] with N hK hlarge hN
  obtain ⟨P, a, b, hP, hnorm, hpospoly, ha⟩ := hK
  obtain ⟨K, hmass, hspec, hsupp, hK0⟩ := green_kernel_of_cosine N P hP a b hnorm hpospoly
  have hzero := hK0.le.trans ha
  intro A hA hcard
  by_contra havoid
  let S := A.image (fun a : ℤ => (a : ZMod (2 * N + 1)))
  have hsize : S.card = A.card := interval_image_card A hA
  have hdiag : ∑ x ∈ S, ∑ y ∈ S, K (x-y) = (A.card : ℝ) * K 0 :=
    interval_image_kernel_sum A hA havoid K hsupp
  have hquad := henergy (2 * N + 1) S K hmass hspec
  rw [hdiag, hsize] at hquad
  push_cast at hquad
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos := (Real.rpow_pos_of_pos hn (1-c)).trans_le hcard
  have hlin : (A.card : ℝ) ≤ (2 * N + 1 : ℝ) * K 0 := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hquad]
  have hupper : (A.card : ℝ) ≤ (3*C) * (N : ℝ) ^ (1-η) := calc
    _ ≤ (2 * N + 1 : ℝ) * (C * (N : ℝ) ^ (-η)) := hlin.trans (by gcongr)
    _ ≤ (3 * N : ℝ) * (C * (N : ℝ) ^ (-η)) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = (3*C) * (N : ℝ) ^ (1-η) := by
      rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
      ring
  have hstrict := mul_lt_mul_of_pos_right (show 3*C < (N : ℝ) ^ (η-c) from hlarge)
    (Real.rpow_pos_of_pos hn (1-η))
  rw [← Real.rpow_add hn, show η-c+(1-η) = 1-c by ring] at hstrict
  exact (not_lt_of_ge (hcard.trans hupper)) hstrict

end OMA.R_Green65_green_65_variants_prime_minus_one_R1
