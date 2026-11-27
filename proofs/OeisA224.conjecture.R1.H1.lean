import OMAReductions.R_OeisA224_conjecture_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic
-- The square-count recurrence and closed form are from the existing rough-squares reduction by HudZah.
open Finset OeisA224
namespace OMA.RoughSquares

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
  let residues (n : ℕ) : Finset ℕ :=
    (Finset.range n).image (fun k => k^2 % n)

  have mem_res {n r : ℕ} (hn : 0 < n) :
      r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
    constructor
    · intro hr
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
      exact ⟨k, h⟩
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

  let unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
    classical
    exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      (u.val.val).val)

  have mem_unitSq {n x : ℕ} [NeZero n] :
      x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
    classical
    constructor
    · intro hx
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := u.property
      exact ⟨v, by simpa [← hv] using hu⟩
    · rintro ⟨u, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

  have unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
      (unitSq n).card = n.totient / 2 := by
    classical
    unfold unitSq
    have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
        u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

  let N := p^(e+2)
  have hp0 := hp.pos
  have hn0 : 0 < N := pow_pos hp0 _
  have : NeZero N := ⟨hn0.ne'⟩
  have : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hne (e+2)
  have fact (u : ℕ) : (p*u)^2 % N = p^2 * (u^2 % p^e) := by
    rw [show N = p^2*p^e by dsimp [N]; ring, mul_pow, Nat.mul_mod_mul_left]
  let M := (residues (p^e)).image (fun t => p^2*t)
  have split : residues N = M ∪ unitSq N := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, rfl⟩ := (mem_res hn0).mp hr
      by_cases hpk : p ∣ k
      · obtain ⟨u, rfl⟩ := hpk
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨u^2 % p^e, (mem_res (pow_pos hp0 _)).mpr ⟨u, rfl⟩, (fact u).symm⟩)
      · have hu : IsUnit (k : ZMod N) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hpk
        apply Finset.mem_union_right
        apply mem_unitSq.mpr
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← Nat.cast_pow, ZMod.val_natCast]⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, rfl⟩ := (mem_res (pow_pos hp0 _)).mp ht
        exact (mem_res hn0).mpr ⟨p*u, fact u⟩
      · obtain ⟨u, rfl⟩ := mem_unitSq.mp hr
        exact (mem_res hn0).mpr ⟨u.val.val, by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
  have disj : Disjoint M (unitSq N) := by
    apply Finset.disjoint_left.mpr
    rintro r hr hunit
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu⟩ := mem_unitSq.mp hunit
    have hU : IsUnit (((p^2*t : ℕ) : ZMod N)) := by
      rw [← hu, ZMod.natCast_zmod_val]
      exact u.isUnit.pow 2
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < e+2 by omega)).mp hU
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have high : 2 < N := lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    (Nat.le_pow (by omega : 0 < e+2))
  have hcnt : (unitSq N).card = _ := unitSq_card N high
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

private theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd]
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  omega

theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
    2*(p+1)*(a (p^e)-1) + (if Even e then p else 1) = p^(e+1) := by
  have hne : p ≠ 2 := by rintro rfl; norm_num at po
  induction e using Nat.twoStepInduction with
  | zero => simp [a_1]
  | one =>
    simp only [pow_one, prime_count hp hne, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := po
    have hhalf : p/2 = k := by omega
    rw [hhalf, hk]
    simp
    ring
  | more e ih _ =>
    let x := p^(e+1)
    let q := x*(p-1)/2
    have hdouble : 2*q = x*(p-1) := by
      apply Nat.mul_div_cancel'
      apply dvd_mul_of_dvd_right
      have hh := Nat.odd_iff.mp po
      omega
    have ha : 1 ≤ a (p^e) := by
      rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
      exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
    have hadd : a (p^(e+2)) - 1 = (a (p^e) - 1) + q := by
      rw [count_step p e hp hne]
      change a (p^e) + q - 1 = _
      omega
    have ev : Even (e+2) ↔ Even e := by simp only [Nat.even_iff]; omega
    rw [hadd, if_congr ev rfl rfl]
    calc
      _ = (2*(p+1)*(a (p^e)-1) + (if Even e then p else 1)) + (p+1)*(2*q) := by ring
      _ = x + (p+1)*(x*(p-1)) := by rw [ih, hdouble]
      _ = p^((e+2)+1) := by
        rw [show e+2+1 = (e+1)+2 by omega, pow_add]
        change x + (p+1)*(x*(p-1)) = x*p^2
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        rw [hj]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring

end OMA.RoughSquares

open OeisA224 in
theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 := by
  intro p k hp hn hk hmod
  let n := p^k
  let A := a n - 1
  have hpp := hp.odd_of_ne_two hn
  have eqn := OMA.RoughSquares.count_formula p hp hpp k
  rw [pow_succ] at eqn
  change 2*(p+1)*A + (if Even k then p else 1) = n*p at eqn
  have hdiv : A ∣ n^2-1 := by
    have hsq : 1 ≤ (p^k)^2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
    exact dvd_trans (dvd_mul_left _ _) ((Nat.modEq_iff_dvd' hsq).mp hmod.symm)
  have pd : p ∣ n := dvd_pow_self _ (by omega)
  by_cases ev : Even k
  · simp only [ev, if_true] at eqn
    have hd : p ∣ 2*(p+1)*A := by
      have hh : p ∣ 2*(p+1)*A + p := eqn ▸ dvd_mul_left _ _
      exact (Nat.dvd_add_iff_left (dvd_refl p)).mpr hh
    have hpa : p ∣ A := (hp.dvd_mul.mp hd).resolve_left (by
      intro hw
      rcases hp.dvd_mul.mp hw with h | h
      · exact hn ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact hp.not_dvd_one ((Nat.dvd_add_iff_left (dvd_refl p)).mpr (by simpa [add_comm] using h)))
    have hsq : p ∣ n^2 := dvd_pow pd (by decide)
    have nz : 1 ≤ n^2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
    have hh := Nat.dvd_sub hsq (hpa.trans hdiv)
    rw [show n^2-(n^2-1) = 1 by omega] at hh
    exact hp.not_dvd_one hh
  · simp only [ev, if_false] at eqn
    have h3 : 3 ≤ k := by
      by_contra! h
      have he2 : k = 2 := by omega
      exact ev (he2 ▸ ⟨1,rfl⟩)
    have h3p : 3 ≤ p := by have := hp.two_le; omega
    have low : p^3 ≤ n := Nat.pow_le_pow_right hp.pos h3
    have upper : p^2-1 < A := by
      by_contra! hh
      have hh1 := Nat.mul_le_mul_left (2*(p+1)) (show A ≤ p^2 by omega)
      have hmul := Nat.mul_le_mul_right p low
      have hp1 : p^2-1+1 = p^2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
      nlinarith only [hh1,hmul,eqn,Nat.mul_le_mul_right (p^3) h3p,Nat.mul_le_mul_right (p^2) h3p,h3p,sq_nonneg (p:ℤ)]
    have hd : (A : ℤ) ∣ (n : ℤ)^2-1 := by
      have hnp : 1 ≤ n^2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
      exact_mod_cast hdiv
    have he : (2:ℤ)*(p+1)*A + 1 = (n:ℤ)*p := by exact_mod_cast eqn
    have hmul : (A:ℤ) ∣ ((n:ℤ)*p)^2-1 := by
      use 2*(p+1)*((n:ℤ)*p+1)
      linear_combination ((n:ℤ)*p+1) * (-he)
    have ht : (A:ℤ) ∣ (p:ℤ)^2-1 := by
      rw [show (p:ℤ)^2-1 = ((n:ℤ)*p)^2-1 - p^2*(n^2-1) by ring]
      exact dvd_sub hmul (dvd_mul_of_dvd_right hd _)
    have hp2 : 0 < (p:ℤ)^2-1 := by
      have hh : (3:ℤ) ≤ p := by exact_mod_cast h3p
      nlinarith
    have := Int.le_of_dvd hp2 ht
    have natle : A + 1 ≤ p^2 := by exact_mod_cast (show (A:ℤ)+1 ≤ (p:ℤ)^2 by omega)
    omega
