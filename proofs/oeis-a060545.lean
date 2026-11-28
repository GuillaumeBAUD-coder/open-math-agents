import OMAStatements.S_oeis_a060545

/-! Proof of Peter Bala's congruence for OEIS A060545. Credit: @cjchaffin.

Peeling off indices divisible by p compares successive binomial coefficients.
Pair the remaining indices j and 2p^k-j. All pairs cancel modulo the target
prime power when k ≥ 2. For k = 1 the quadratic correction vanishes and the
linear correction is a multiple of the sum of inverse squares in the prime field.
-/

namespace A060545Proof
open Finset OMA.S_oeis_a060545

theorem normA (n : ℕ) (hn : 0 < n) : a n = (n^2-1).choose (n-1) := by
  have hh := Nat.add_one_mul_choose_eq (n^2-1) (n-1)
  rw [Nat.sub_add_cancel (pow_pos hn 2 : 1 ≤ n^2), Nat.sub_add_cancel hn] at hh
  have h : Nat.choose (n^2) n = n * (n^2-1).choose (n-1) := by
    apply Nat.eq_of_mul_eq_mul_left hn
    calc
      _ = n^2 * (n^2 - 1).choose (n-1) := (Nat.mul_comm _ _).trans hh.symm
      _ = _ := by ring
  simp [a, h, hn.ne']

private theorem denFact (b : ℕ) : (∏ j ∈ Ico 1 b, j) = (b-1).factorial := by
  rw [prod_Ico_eq_prod_range, Nat.factorial_eq_prod_range_add_one]
  simp only [add_comm 1]

private theorem cross (a b : ℕ) :
    (∏ j ∈ Ico 1 b, j) * ((a-1).choose (b-1)) = ∏ j ∈ Ico 1 b, (a-j) := by
  rw [denFact, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    prod_Ico_eq_prod_range]
  apply prod_congr rfl
  intro j hj
  omega

private theorem divideSlice (p b : ℕ) (hp : 0 < p) (g : ℕ → ℕ) :
    (∏ j ∈ (Ico 1 (p*b)).filter (fun j => p ∣ j), g j) =
      ∏ j ∈ Ico 1 b, g (p*j) := by
  symm
  apply prod_bij (fun j _ => p*j)
  · intro j hj
    have hj' := mem_Ico.mp hj
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hp hj'.1,
      Nat.mul_lt_mul_of_pos_left hj'.2 hp⟩, dvd_mul_right _ _⟩
  · intro i hi j hj h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro j hj
    obtain ⟨hj, u, rfl⟩ := mem_filter.mp hj
    have hj' := mem_Ico.mp hj
    exact ⟨u, mem_Ico.mpr ⟨by by_contra! h; obtain rfl : u = 0 := (by omega); simp at hj',
      (Nat.mul_lt_mul_left hp).mp hj'.2⟩, rfl⟩
  · intros; rfl

theorem scale (p a b : ℕ) (hp : 0 < p) :
    let s := (Ico 1 (p*b)).filter (fun j => ¬ p ∣ j)
    ((p*a-1).choose (p*b-1)) * (∏ j ∈ s, j) =
      ((a-1).choose (b-1)) * (∏ j ∈ s, (p*a-j)) := by
  dsimp only
  have big := cross (p*a) (p*b)
  have small := cross a b
  have h1 := prod_filter_mul_prod_filter_not (Ico 1 (p*b)) (fun j => p ∣ j) (fun j => j)
  have h2 := prod_filter_mul_prod_filter_not (Ico 1 (p*b)) (fun j => p ∣ j) (fun j => p*a-j)
  rw [← h1, ← h2, divideSlice _ _ hp, divideSlice _ _ hp] at big
  simp only [← Nat.mul_sub_left_distrib, prod_mul_distrib, prod_const] at big
  have hd : (∏ j ∈ Ico 1 b, p*j) = p ^ (Ico 1 b).card * (∏ j ∈ Ico 1 b, j) := by
    rw [prod_mul_distrib]; simp
  rw [hd, ← small] at big
  have pos : 0 < p ^ (Ico 1 b).card * (∏ j ∈ Ico 1 b, j) := by rw [denFact]; positivity
  apply Nat.eq_of_mul_eq_mul_left pos
  calc
    _ = _ := by convert big using 1 <;> ac_rfl
end A060545Proof


namespace A060545Proof
open Finset OMA.S_oeis_a060545

def Layer : Prop := ∀ p r k : ℕ, p.Prime → 5 ≤ p → 0 < r → 0 < k →
    let s := (Ico 1 (2*p^k)).filter (fun j => ¬ p ∣ j)
    (∏ j ∈ s, (4*p^(r+k)-j)) ≡ (∏ j ∈ s, j) [MOD p^(3+r)]

theorem resultOfLayer (layer : Layer) : type_of% @OMA.S_oeis_a060545.main := by
  intro p r hp hp5 hr
  have loop (k : ℕ) :
      (4*p^(r+k)-1).choose (2*p^k-1) ≡ 4*p^r-1 [MOD p^(3+r)] := by
    induction k with
    | zero => simp; exact Nat.ModEq.refl _
    | succ k ih =>
      have h := scale p (4*p^(r+k)) (2*p^k) hp.pos
      have e1 : p*(4*p^(r+k)) = 4*p^(r+(k+1)) := by rw [← add_assoc, pow_succ]; ring
      have e2 : p*(2*p^k) = 2*p^(k+1) := by rw [pow_succ]; ring
      dsimp only at h
      rw [e1, e2] at h
      let s := (Ico 1 (2*p^(k+1))).filter (fun j => ¬ p ∣ j)
      have hc : (p^(3+r)).Coprime (∏ j ∈ s, j) := by
        apply Nat.Coprime.prod_right
        intro j hj
        exact (hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).pow_left _
      apply Nat.ModEq.trans _ ih
      apply Nat.ModEq.cancel_right_of_coprime hc
      rw [h]
      exact (layer p r (k+1) hp hp5 hr (by omega)).mul_left _
  rw [normA _ (by positivity : 0 < 2*p^r)]
  simpa only [show (2*p^r)^2 = 4*p^(r+r) by rw [pow_add]; ring] using loop r
end A060545Proof


open scoped BigOperators

namespace OeisA060545InverseSquares

theorem sum_inverse_squares (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (∑ x : ZMod p, (x⁻¹) ^ 2) = 0 := by
  trans ∑ x : ZMod p, x ^ 2
  · exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x : ZMod p => x ^ 2)
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)

theorem sum_inverse_squares_nonzero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ 2) = 0 := by
  have h := Finset.sum_erase_add (s := Finset.univ) (fun x : ZMod p => (x⁻¹) ^ 2)
    (Finset.mem_univ (0 : ZMod p))
  simp only [inv_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
  exact h.trans (sum_inverse_squares p hp)

theorem sum_inverse_squares_range (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  trans ∑ x : ZMod p, x⁻¹ ^ 2
  · convert (ZMod.finEquiv p).toEquiv.sum_comp (fun x : ZMod p => x⁻¹ ^ 2) using 2 with x
    apply congrArg (fun t : ZMod p => t⁻¹ ^ 2)
    cases p with
    | zero => omega
    | succ q =>
      exact ZMod.natCast_zmod_val (n := q + 1) x
  · exact sum_inverse_squares p hp

theorem sum_inverse_squares_Ico (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  rw [Finset.sum_Ico_eq_sub _ (by omega), sum_inverse_squares_range p hp]
  simp

end OeisA060545InverseSquares




open Finset

namespace OeisA060545LayerPairing

private abbrev layer (p m : ℕ) := (Ico 1 m).filter fun j => ¬p ∣ j

private theorem halves (p m : ℕ) (hpm : p ∣ m) :
    layer p (2*m) = layer p m ∪ (layer p m).image (fun j => 2*m-j) ∧
    Disjoint (layer p m) ((layer p m).image (fun j => 2*m-j)) ∧
    Set.InjOn (fun j => 2*m-j) (layer p m) := by
  have reflect (x : ℕ) (hx : x ≤ 2*m) (h : ¬p ∣ x) : ¬p ∣ 2*m-x := by
    intro h'
    have h'' := Nat.dvd_sub (dvd_mul_of_dvd_right hpm 2) h'
    exact h (by simpa only [Nat.sub_sub_self hx] using h'')
  constructor
  · ext x
    simp only [layer, mem_union, mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hx⟩
      by_cases hxm : x < m
      · exact Or.inl ⟨⟨hx1, hxm⟩, hx⟩
      · have hne : x ≠ m := fun he => hx (he ▸ hpm)
        exact Or.inr ⟨2*m-x, ⟨⟨by omega, by omega⟩, reflect x hx2.le hx⟩, by omega⟩
    · rintro (⟨⟨hx1, hxm⟩, hx⟩ | ⟨j, ⟨⟨hj1, hjm⟩, hj⟩, rfl⟩)
      · exact ⟨⟨hx1, by omega⟩, hx⟩
      · exact ⟨⟨by omega, by omega⟩, reflect j (by omega) hj⟩
  constructor
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
    have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
    omega
  · intro x hx y hy hxy
    change 2*m-x = 2*m-y at hxy
    have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
    have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2
    omega

theorem prod_pair {M : Type*} [CommMonoid M] (p k : ℕ) (hk : 0 < k) (g : ℕ → M) :
    (∏ j ∈ (Ico 1 (2*p^k)).filter (fun j : ℕ => ¬p ∣ j), g j) =
      ∏ j ∈ (Ico 1 (p^k)).filter (fun j : ℕ => ¬p ∣ j), (g j * g (2*p^k-j)) := by
  obtain ⟨heq, hd, hi⟩ := halves p (p^k) (dvd_pow_self _ hk.ne')
  change (∏ j ∈ layer p (2*p^k), g j) = _
  rw [heq, Finset.prod_union hd, Finset.prod_image hi, Finset.prod_mul_distrib]

theorem even_card (p k : ℕ) (hk : 0 < k) :
    Even (((Ico 1 (2*p^k)).filter (fun j : ℕ => ¬p ∣ j)).card) := by
  obtain ⟨heq, hd, hi⟩ := halves p (p^k) (dvd_pow_self _ hk.ne')
  change Even (layer p (2*p^k)).card
  rw [heq, Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hi]
  exact ⟨_, rfl⟩

end OeisA060545LayerPairing


namespace A060545Pair

section Ring

variable {R ι : Type*} [CommRing R]

theorem prod_one_add_of_sq_zero (s : Finset ι) (f : ι → R) (C : R) (hC : C * C = 0) :
    ∏ i ∈ s, (1 + C * f i) = 1 + C * ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
    calc
      _ = 1 + C * (f i + ∑ j ∈ s, f j) + (C*C) * f i * ∑ j ∈ s, f j := by ring
      _ = _ := by rw [hC]; ring

theorem pair_identity (u v : Rˣ) (m X : R) (huv : (u : R) + (v : R) = m) :
    (1 - X * (↑(u⁻¹) : R)) * (1 - X * (↑(v⁻¹) : R)) =
      1 + (X*(X-m)) * ((↑(u⁻¹) : R) * (↑(v⁻¹) : R)) := by
  subst m
  linear_combination
    X * (↑(v⁻¹) : R) * (u.val_inv) + X * (↑(u⁻¹) : R) * (v.val_inv)

/-- Compare unnormalized paired products after the inverse sum has been killed. -/
theorem paired_products_eq (s : Finset ι) (u v : ι → Rˣ) (m X : R)
    (hsum : ∀ i ∈ s, (u i : R) + (v i : R) = m)
    (hC : (X*(X-m))*(X*(X-m)) = 0)
    (hkill : (X*(X-m)) * ∑ i ∈ s, (↑((u i)⁻¹) : R) * (↑((v i)⁻¹) : R) = 0) :
    ∏ i ∈ s, ((X - (u i : R)) * (X - (v i : R))) =
      ∏ i ∈ s, ((u i : R) * (v i : R)) := by
  let f (i : ι) := (↑((u i)⁻¹) : R) * (↑((v i)⁻¹) : R)
  have leg (w : Rˣ) : X - (w : R) = -(w : R) * (1 - X * (↑(w⁻¹) : R)) := by
    linear_combination X * (-w.val_inv)
  calc
    _ = ∏ i ∈ s, (((u i : R)*(v i : R)) * (1 + X*(X-m)*f i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [leg (u i), leg (v i), mul_mul_mul_comm, neg_mul_neg,
        pair_identity (u i) (v i) m X (hsum i hi)]
    _ = _ := by
      rw [Finset.prod_mul_distrib, prod_one_add_of_sq_zero s f _ hC, show (X*(X-m)) * ∑ i ∈ s, f i = 0 from hkill, add_zero, mul_one]

theorem layer_coeff_factor (p : R) (r k : ℕ) :
    (4*p^(r+k))*(4*p^(r+k)-2*p^k) =
      p^(r+(k+k))*(4*(4*p^r-2)) := by
  simp only [pow_add]
  ring

end Ring

private theorem zmod_pow_zero (p a e : ℕ) (h : a ≤ e) :
    (p : ZMod (p^a))^e = 0 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem layer_coeff_zero (p r k : ℕ) (hk : 2 ≤ k) :
    let X : ZMod (p^(3+r)) := 4*(p : ZMod (p^(3+r)))^(r+k)
    let m : ZMod (p^(3+r)) := 2*(p : ZMod (p^(3+r)))^k
    X*(X-m) = 0 := by
  dsimp only
  rw [layer_coeff_factor, zmod_pow_zero p (3+r) (r+(k+k)) (by omega), zero_mul]

theorem layer_coeff_one (p r : ℕ) :
    let X : ZMod (p^(3+r)) := 4*(p : ZMod (p^(3+r)))^(r+1)
    let m : ZMod (p^(3+r)) := 2*(p : ZMod (p^(3+r)))
    X*(X-m) = (p : ZMod (p^(3+r)))^(r+2) * (4*(4*(p : ZMod (p^(3+r)))^r-2)) := by
  simpa only [pow_one] using layer_coeff_factor (p : ZMod (p^(3+r))) r 1

theorem layer_coeff_one_sq_zero (p r : ℕ) :
    let X : ZMod (p^(3+r)) := 4*(p : ZMod (p^(3+r)))^(r+1)
    let m : ZMod (p^(3+r)) := 2*(p : ZMod (p^(3+r)))
    let C := X*(X-m)
    C*C = 0 := by
  dsimp only
  rw [layer_coeff_one p r]
  set u : ZMod (p^(3+r)) := 4 * (4 * (p : ZMod (p^(3+r)))^r - 2)
  rw [show (p : ZMod (p^(3+r)))^(r+2)*u*((p : ZMod (p^(3+r)))^(r+2)*u) =
      (p : ZMod (p^(3+r)))^((r+2)+(r+2))*(u*u) by rw [pow_add (p : ZMod (p^(3+r))) (r+2) (r+2)]; ring,
    zmod_pow_zero p (3+r) _ (by omega), zero_mul]

end A060545Pair

namespace A060545Mod

def reduce (p r : ℕ) : ZMod (p^(3+r)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : 3+r ≠ 0)) (ZMod p)

theorem exists_mul_of_reduce_zero {p r : ℕ} [NeZero p] {z : ZMod (p^(3+r))}
    (hz : reduce p r z = 0) : ∃ w : ZMod (p^(3+r)), z = (p : ZMod (p^(3+r))) * w := by
  have hc : (z.val : ZMod p) = 0 := by
    rw [← map_natCast (reduce p r) z.val, ZMod.natCast_zmod_val]
    exact hz
  obtain ⟨w,hw⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hc
  refine ⟨w, ?_⟩
  calc
    z = (z.val : ZMod (p^(3+r))) := (ZMod.natCast_zmod_val z).symm
    _ = _ := by rw [hw, Nat.cast_mul]

theorem pow_mul_eq_zero_of_reduce_zero {p r : ℕ} [NeZero p] {z : ZMod (p^(3+r))}
    (hz : reduce p r z = 0) : (p : ZMod (p^(3+r)))^(r+2) * z = 0 := by
  obtain ⟨w,rfl⟩ := exists_mul_of_reduce_zero hz
  rw [← mul_assoc, ← pow_succ, show r+2+1 = 3+r by omega, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem reduce_inverse_pair {p r j : ℕ} [Fact p.Prime] (hj : j ≤ 2*p)
    (u v : (ZMod (p^(3+r)))ˣ)
    (hu : (u : ZMod (p^(3+r))) = j)
    (hv : (v : ZMod (p^(3+r))) = (↑(2*p-j) : ZMod (p^(3+r)))) :
    reduce p r ((↑(u⁻¹) : ZMod (p^(3+r))) * (↑(v⁻¹) : ZMod (p^(3+r)))) =
      -(((j : ZMod p)⁻¹)^2) := by
  rw [map_mul, map_units_inv, map_units_inv, hu, hv, map_natCast, map_natCast,
    Nat.cast_sub hj, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_sub, inv_neg, pow_two]
  ring

theorem kill_inverse_pair_sum (p r : ℕ) [Fact p.Prime]
    (u v : ℕ → (ZMod (p^(3+r)))ˣ)
    (hu : ∀ j ∈ (Finset.Ico 1 p).filter (fun j => ¬p ∣ j), (u j : ZMod (p^(3+r))) = j)
    (hv : ∀ j ∈ (Finset.Ico 1 p).filter (fun j => ¬p ∣ j),
      (v j : ZMod (p^(3+r))) = (↑(2*p-j) : ZMod (p^(3+r))))
    (hsq : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹)^2 = 0) :
    (p : ZMod (p^(3+r)))^(r+2) * ∑ j ∈ (Finset.Ico 1 p).filter (fun j => ¬p ∣ j),
      (↑((u j)⁻¹) : ZMod (p^(3+r))) * (↑((v j)⁻¹) : ZMod (p^(3+r))) = 0 := by
  apply pow_mul_eq_zero_of_reduce_zero
  rw [map_sum]
  have hf : (Finset.Ico 1 p).filter (fun j => ¬p ∣ j) = Finset.Ico 1 p := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
  calc
    _ = ∑ j ∈ (Finset.Ico 1 p).filter (fun j => ¬p ∣ j), -(((j : ZMod p)⁻¹)^2) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
      exact reduce_inverse_pair (by omega) (u j) (v j) (hu j hj) (hv j hj)
    _ = 0 := by rw [hf, Finset.sum_neg_distrib, hsq, neg_zero]

end A060545Mod

namespace A060545Proof
open Finset OMA.S_oeis_a060545

private noncomputable def liftUnit (p r j : ℕ) : (ZMod (p^(3+r)))ˣ :=
  if h : j.Coprime (p^(3+r)) then ZMod.unitOfCoprime j h else 1

private theorem liftUnit_eq {p r j : ℕ} (hp : p.Prime) (hj : ¬p ∣ j) :
    (liftUnit p r j : ZMod (p^(3+r))) = j := by
  have h := (hp.coprime_iff_not_dvd.mpr hj).symm.pow_right (3+r)
  simp only [liftUnit, dif_pos h, ZMod.coe_unitOfCoprime]

theorem layer : Layer := by
  intro p r k hp hp5 hr hk
  let : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p^(3+r))
  let b := 2*p^k
  let t := 4*p^(r+k)
  let s := (Ico 1 (p^k)).filter (fun j => ¬p ∣ j)
  let u := liftUnit p r
  let v := fun j => liftUnit p r (b-j)
  have hb : p ∣ b := dvd_mul_of_dvd_right (dvd_pow_self _ hk.ne') _
  have hjb (j : ℕ) (hj : j ∈ s) : j ≤ b := by
    have h := (mem_Ico.mp (mem_filter.mp hj).1).2
    dsimp [b]; omega
  have hu (j : ℕ) (hj : j ∈ s) : (u j : R) = (j : R) :=
    liftUnit_eq hp (mem_filter.mp hj).2
  have hv (j : ℕ) (hj : j ∈ s) : (v j : R) = ((b-j : ℕ) : R) := by
    apply liftUnit_eq hp
    intro h
    have h' := Nat.dvd_sub hb h
    exact (mem_filter.mp hj).2 (by simpa [Nat.sub_sub_self (hjb _ hj)] using h')
  have huv (j : ℕ) (hj : j ∈ s) : (u j : R) + (v j : R) = (b : R) := by
    rw [hu _ hj, hv _ hj, Nat.cast_sub (hjb _ hj)]; ring
  have ht : b ≤ t := by
    dsimp [b,t]
    rw [pow_add]
    have hp' : 1 ≤ p^r := pow_pos hp.pos _
    nlinarith [pow_pos hp.pos k]
  have hz : (((t : R)*((t : R)-(b : R))) * ((t : R)*((t : R)-(b : R))) = 0) ∧
      ((t : R)*((t : R)-(b : R))) *
        (∑ j ∈ s, (↑((u j)⁻¹) : R) * (↑((v j)⁻¹) : R)) = 0 := by
    dsimp only [R, t, b]
    push_cast
    by_cases hk1 : k = 1
    · subst k
      simp only [pow_one]
      refine ⟨A060545Pair.layer_coeff_one_sq_zero p r, ?_⟩
      rw [A060545Pair.layer_coeff_one p r]
      have ha := A060545Mod.kill_inverse_pair_sum p r u v (by simpa [s] using hu)
        (by simpa [s,b] using hv) (OeisA060545InverseSquares.sum_inverse_squares_Ico p hp5)
      simp only [s, pow_one] at *
      linear_combination (4*(4*(p : ZMod (p^(3+r)))^r-2)) * ha
    · rw [A060545Pair.layer_coeff_zero p r k (by omega)]
      simp
  have pair := A060545Pair.paired_products_eq s u v (b : R) (t : R) huv hz.1 hz.2
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [OeisA060545LayerPairing.prod_pair p k hk, OeisA060545LayerPairing.prod_pair p k hk]
  push_cast
  convert pair using 1
  · apply prod_congr rfl
    intro j hj
    rw [hu _ hj, hv _ hj, Nat.cast_sub (le_trans (hjb _ hj) ht),
      Nat.cast_sub (le_trans (Nat.sub_le b j) ht)]
  · apply prod_congr rfl
    intro j hj
    rw [hu _ hj, hv _ hj]
end A060545Proof


theorem OMA.solution : type_of% @OMA.S_oeis_a060545.main :=
  A060545Proof.resultOfLayer A060545Proof.layer
