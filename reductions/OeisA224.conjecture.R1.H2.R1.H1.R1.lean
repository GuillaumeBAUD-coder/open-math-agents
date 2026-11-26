import OMAReductions.R_OeisA224_conjecture_R1_H2_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
The square residue test fails whenever both prime factors exceed 200, for every
pair of positive exponents. Split the remaining cases according to whether
both primes or just the smaller prime are bounded.
Credit: @HudZah
-/

open Finset OeisA224

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1

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

private theorem relative_count {p e : ℕ} (hp : p.Prime) (po : Odd p) (big : 201 ≤ p) (he : 0 < e) :
    99 * p^e ≤ 200 * a (p^e) ∧ 200 * a (p^e) ≤ 101 * p^e := by
  have form := count_formula p hp po e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  let N := p^e
  let A := a N
  change 99*N ≤ 200*A ∧ 200*A ≤ 101*N
  have small : p ≤ N := Nat.le_pow he
  have hf : 2*(p+1)*A + (if Even e then p else 1) = p*N + 2*(p+1) := by
    change 2*(p+1)*(A-1)+(if Even e then p else 1)=_ at form
    rw [pow_succ, mul_comm (p^e)] at form
    have hA : A-1+1=A := Nat.sub_add_cancel ha
    change 2*(p+1)*(A-1)+(if Even e then p else 1) = p*N at form
    nlinarith only [form, congrArg (fun t => 2*(p+1)*t) hA]
  constructor
  · by_contra! bad
    have hm := Nat.mul_le_mul_left (p+1) (show 200*A+1 ≤ 99*N by omega)
    by_cases ev : Even e <;> simp [ev] at hf <;>
      nlinarith [Nat.mul_le_mul_right N (show 99 ≤ p by omega)]
  · by_contra! bad
    have hm := Nat.mul_le_mul_left (p+1) (show 101*N+1 ≤ 200*A by omega)
    by_cases ev : Even e <;> simp [ev] at hf <;>
      nlinarith only [hm,hf,small,big,Nat.mul_le_mul_right N big]

private theorem no_square16 {n A : ℕ} (ha : 2 ≤ A) : n^2 ≠ 16*(A*(A-1))+1 := by
  intro eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp at eq
  rcases le_or_gt n (4*k+5) with h | h
  · nlinarith [Nat.pow_le_pow_left h 2]
  · nlinarith [Nat.pow_le_pow_left (show 4*k+6 ≤ n by omega) 2]

theorem large_pair_fails {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) (pb : 201 ≤ p) (qb : 201 ≤ q)
    (he : 0 < e) (hf : 0 < f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)] := by
  intro test
  obtain ⟨pl, pu⟩ := relative_count hp hpo pb he
  obtain ⟨ql, qu⟩ := relative_count hq hqo qb hf
  let N := p^e*q^f
  let A := a (p^e) * a (q^f)
  have hc := (Nat.coprime_primes hp hq).mpr hne
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _) ((hc.pow_left _).pow_right _)] at test
  change N^2 ≡ 1 [MOD A*(A-1)] at test
  have lower : 9801*N ≤ 40000*A := by
    dsimp [N,A]; nlinarith only [Nat.mul_le_mul pl ql]
  have upper : 40000*A ≤ 10201*N := by
    dsimp [N,A]; nlinarith only [Nat.mul_le_mul pu qu]
  have nb : 201*201 ≤ N := Nat.mul_le_mul (pb.trans (Nat.le_pow he)) (qb.trans (Nat.le_pow hf))
  have ab : 9000 ≤ A := by omega
  have ha : A-1+1 = A := by omega
  have hn : 1 ≤ N^2 := by nlinarith
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn).mp test.symm
  have heq : N^2 = (A*(A-1))*k+1 := by omega
  rcases lt_trichotomy k 16 with h | rfl | h
  · have b := Nat.mul_le_mul_left (A*(A-1)) (show k ≤ 15 by omega)
    nlinarith only [heq,b,Nat.pow_le_pow_left upper 2, congrArg (A * ·) ha, ab, Nat.zero_le (A^2)]
  · exact no_square16 (A:=A) (n:=N) (by omega) (by simpa [mul_comm] using heq)
  · have b := Nat.mul_le_mul_left (A*(A-1)) (show 17 ≤ k by omega)
    have aa := Nat.mul_le_mul_left A ab
    nlinarith only [heq,b,Nat.pow_le_pow_left lower 2, congrArg (A * ·) ha, ab, aa]


-- Both prime bases lie in the finite range from 3 to 199.
def H1 : Prop :=
  ∀ p q e f : ℕ, p.Prime → q.Prime → Odd p → Odd q → p < q → q < 201 →
    0 < e → 0 < f → 3 ≤ e+f →
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)]

-- Only the smaller prime base lies in that range.
def H2 : Prop :=
  ∀ p q e f : ℕ, p.Prime → q.Prime → Odd p → Odd q → p < q → p < 201 → 201 ≤ q →
    0 < e → 0 < f → 3 ≤ e+f →
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)]

theorem ordered (both : H1) (one : H2) {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hlt : p < q) (he : 0 < e) (hf : 0 < f) (hs : 3 ≤ e+f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)] := by
  by_cases qp : q < 201
  · exact both p q e f hp hq hpo hqo hlt qp he hf hs
  by_cases pp : p < 201
  · exact one p q e f hp hq hpo hqo hlt pp (by omega) he hf hs
  exact large_pair_fails hp hq hpo hqo hlt.ne (by omega) (by omega) he hf

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1.H1 := by
  intro both one p q e f hp hq hpq hpo hqo he hf hs
  rcases lt_or_gt_of_ne hpq with h | h
  · exact ordered both one hp hq hpo hqo h he hf hs
  · simpa only [mul_comm (q^f) (p^e)] using
      ordered both one hq hp hqo hpo h hf he (by omega : 3 ≤ f+e)

end OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1
