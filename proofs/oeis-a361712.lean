import OMAStatements.S_oeis_a361712

/-!
# Two supercongruences for A361712

Formalization of Roberto Blanco Gómez's October 2026 proof. The prime
argument uses reflection of reciprocal powers. The prime-power proof
separates unit indices from multiples of the prime and uses the lifted
inverse-square sum on the final valuation class. Attribution for the
reused rational divisibility lemmas appears below.
-/

section

/-! Local-rational divisibility algebra adapted from the checked arithmetic
in local Public34346.lean, namespace OeisA363986Part23. No original target
or conjecture placeholder is imported. -/
namespace A361712
open Finset
/-- `p^M` divides `q : ℚ` in `ℤ_{(p)}`, i.e., `q = p^M * a / b` with `0 < b` and `p ⊥ b`. -/
def pDvdRat (p M : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ Nat.Coprime p b ∧ q = (p : ℚ) ^ M * (a : ℚ) / (b : ℚ)

lemma pDvdRat_zero (p M : ℕ) : pDvdRat p M 0 :=
  ⟨0, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩

lemma pDvdRat_mono {p M1 M2 : ℕ} {q : ℚ} (h : M1 ≤ M2) (hq : pDvdRat p M2 q) :
    pDvdRat p M1 q := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  refine ⟨(p : ℤ) ^ (M2 - M1) * a, b, hb, hcop, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

lemma pDvdRat_neg {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) : pDvdRat p M (-q) := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  exact ⟨-a, b, hb, hcop, by push_cast; ring⟩

lemma pDvdRat_add {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 + q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  have hb1q : (b1 : ℚ) ≠ 0 := by positivity
  have hb2q : (b2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma pDvdRat_sub {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 - q2) := by
  rw [sub_eq_add_neg]; exact pDvdRat_add h1 (pDvdRat_neg h2)

lemma pDvdRat_mul {p M1 M2 : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M1 q1) (h2 : pDvdRat p M2 q2) :
    pDvdRat p (M1 + M2) (q1 * q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * a2, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma pDvdRat_pow {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) (k : ℕ) :
    pDvdRat p (k * M) (q ^ k) := by
  induction k with
  | zero => exact ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact pDvdRat_mul ih hq

lemma pDvdRat_sum {ι : Type*} {s : Finset ι} {p M : ℕ} {f : ι → ℚ}
    (hf : ∀ i ∈ s, pDvdRat p M (f i)) : pDvdRat p M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p M
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pDvdRat_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma pDvdRat_of_int {p M : ℕ} (z : ℤ) (hz : (p : ℤ) ^ M ∣ z) : pDvdRat p M (z : ℚ) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨a, 1, Nat.one_pos, Nat.coprime_one_right p, by push_cast; ring⟩

lemma pDvdRat_of_int_zero (p : ℕ) (z : ℤ) : pDvdRat p 0 (z : ℚ) :=
  pDvdRat_of_int z (by simp)

lemma pDvdRat_inv_nat {p d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime p d) :
    pDvdRat p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, hcop, by push_cast; rw [pow_zero, one_mul, one_div]⟩

lemma int_dvd_of_pDvdRat {p M : ℕ} {z : ℤ} (hz : pDvdRat p M (z : ℚ)) : (p : ℤ) ^ M ∣ z := by
  rcases hz with ⟨a, b, hb, hcop, heq⟩
  have hbq : (b : ℚ) ≠ 0 := by positivity
  have hmulq : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ M * (a : ℚ) := by
    rw [heq, div_mul_cancel₀ _ hbq]
  have hmul : z * (b : ℤ) = (p : ℤ) ^ M * a := by exact_mod_cast hmulq
  have hdvd : (p : ℤ) ^ M ∣ (b : ℤ) * z := ⟨a, by linarith⟩
  have hcopZ : IsCoprime ((p : ℤ) ^ M) (b : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma pDvdRat_div_nat {p M d E : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hvp : padicValNat p d ≤ E) (hEM : E ≤ M) {q : ℚ} (hq : pDvdRat p M q) :
    pDvdRat p (M - E) (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  set v := padicValNat p d
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := p) (n := d)
  have hd'_pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with rfl | hpos
    · simp at hd'; omega
    · exact hpos
  have hcop_d' : Nat.Coprime p d' := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd'
    rcases hpd' with ⟨t, rfl⟩
    have h1 : p ^ (v + 1) ∣ d := ⟨t, by rw [hd', pow_succ]; ring⟩
    have h2 : v + 1 ≤ padicValNat p d := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  refine ⟨(p : ℤ) ^ (E - v) * a, b * d', Nat.mul_pos hb hd'_pos, hcop.mul_right hcop_d', ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd_cast : (d : ℚ) = (p : ℚ) ^ v * (d' : ℚ) := by exact_mod_cast hd'
  rw [hd_cast]
  have hexp : M = (M - E) + (E - v) + v := by omega
  push_cast
  calc (p : ℚ) ^ M * (a : ℚ) / (b : ℚ) / ((p : ℚ) ^ v * (d' : ℚ))
      = (p : ℚ) ^ ((M - E) + (E - v) + v) * (a : ℚ) / ((b : ℚ) * (d' : ℚ) * (p : ℚ) ^ v) := by
          rw [← hexp]; ring
    _ = ((p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ))) *
        ((p : ℚ) ^ v / (p : ℚ) ^ v) := by rw [pow_add, pow_add]; ring
    _ = (p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ)) := by
        rw [div_self (pow_ne_zero v hpq), mul_one]


end A361712

end

section

namespace A361712
open Finset

/-- Clear one finite common denominator to transfer a modular inverse-power
sum back to exact rational p-integral divisibility. -/
theorem pDvdRat_sum_inv_pow {ι : Type*} [DecidableEq ι]
    (p M e : ℕ) (S : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ S, 0 < d i) (hc : ∀ i ∈ S, Nat.Coprime p (d i))
    (hz : (∑ i ∈ S, ((d i : ZMod (p^M))^e)⁻¹)=0) :
    pDvdRat p M (∑ i ∈ S, ((d i : ℚ)^e)⁻¹) := by
  classical
  let B : ℕ := ∏ i ∈ S, d i^e
  let A : ℕ := ∑ i ∈ S, ∏ j ∈ S.erase i, d j^e
  have hBpos : 0 < B := Finset.prod_pos (fun i hi => pow_pos (hd i hi) e)
  have hBcop : Nat.Coprime p B := Nat.Coprime.prod_right fun i hi => (hc i hi).pow_right e
  have hB (i : ι) (hi : i ∈ S) : B=(∏ j ∈ S.erase i, d j^e)*d i^e :=
    (Finset.prod_erase_mul S (fun j => d j^e) hi).symm
  have hQ : (B : ℚ)*(∑ i ∈ S, ((d i : ℚ)^e)⁻¹)=(A : ℚ) := by
    rw [Finset.mul_sum]
    change _=((∑ i ∈ S, ∏ j ∈ S.erase i, d j^e : ℕ) : ℚ)
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hB i hi,Nat.cast_mul,Nat.cast_pow,mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero e (by exact_mod_cast (hd i hi).ne')),mul_one]
  have hZ : (B : ZMod (p^M))*(∑ i ∈ S, ((d i : ZMod (p^M))^e)⁻¹)=(A : ZMod (p^M)) := by
    rw [Finset.mul_sum]
    change _=((∑ i ∈ S, ∏ j ∈ S.erase i, d j^e : ℕ) : ZMod (p^M))
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu : IsUnit ((d i : ZMod (p^M))^e) :=
      ((ZMod.isUnit_iff_coprime _ _).mpr ((hc i hi).symm.pow_right M)).pow e
    rw [hB i hi,Nat.cast_mul,Nat.cast_pow,mul_assoc,ZMod.mul_inv_of_unit _ hu,mul_one]
  have ha0 : (A : ZMod (p^M))=0 := by rw [← hZ,hz,mul_zero]
  obtain ⟨a,ha⟩ := (ZMod.natCast_eq_zero_iff A (p^M)).mp ha0
  refine ⟨(a : ℤ),B,hBpos,hBcop,?_⟩
  apply (eq_div_iff (by exact_mod_cast hBpos.ne' : (B : ℚ) ≠ 0)).mpr
  calc
    _ = (B : ℚ)*(∑ i ∈ S, ((d i : ℚ)^e)⁻¹) := mul_comm _ _
    _ = (A : ℚ) := hQ
    _ = (p : ℚ)^M*((a : ℤ) : ℚ) := by rw [ha,Nat.cast_mul,Nat.cast_pow,Int.cast_natCast]

end A361712

end

section

namespace A361712
open Finset

noncomputable def unitRange (p L : ℕ) : Finset ℕ := (Ico 1 L).filter (fun j => ¬p∣j)
noncomputable def harmonic (p L e : ℕ) : ℚ := ∑ j ∈ unitRange p L, ((j : ℚ)^e)⁻¹

/-- Permuting units by a single unit annihilates their power sum whenever
v^e-1 is itself a unit. -/
theorem sum_units_inv_pow_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (e : ℕ) (v : Rˣ) (hv : IsUnit ((v : R)^e-1)) :
    ∑ u : Rˣ, (((u⁻¹ : Rˣ) : R)^e)=0 := by
  classical
  have h := Equiv.sum_comp (Equiv.mulLeft v) (fun u : Rˣ => (u : R)^e)
  change (∑ u : Rˣ, ((v*u : Rˣ) : R)^e)=(∑ u : Rˣ, (u : R)^e) at h
  simp only [Units.val_mul,mul_pow,← Finset.mul_sum] at h
  have hz : (∑ u : Rˣ, (u : R)^e)=0 := by
    apply hv.mul_right_eq_zero.mp
    calc
      _ = (v : R)^e*(∑ u : Rˣ,(u : R)^e)-(∑ u : Rˣ,(u : R)^e) := by ring
      _ = 0 := sub_eq_zero.mpr h
  have hi := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (u : R)^e)
  change (∑ u : Rˣ, (((u⁻¹ : Rˣ) : R)^e))=(∑ u : Rˣ,(u : R)^e) at hi
  exact hi.trans hz

/-- Exact natural representatives for the units modulo a prime power. -/
theorem sum_unitRange_eq_units {p h : ℕ} [NeZero (p^h)] (hp : p.Prime) (hh : 1 ≤ h) (e : ℕ) :
    (∑ j ∈ unitRange p (p^h), ((j : ZMod (p^h))^e)⁻¹)=
      ∑ u : (ZMod (p^h))ˣ, (((u⁻¹ : (ZMod (p^h))ˣ) : ZMod (p^h))^e) := by
  classical
  let : NeZero (p^h) := ⟨pow_ne_zero h hp.ne_zero⟩
  have hbase : (∑ j ∈ unitRange p (p^h), ((j : ZMod (p^h))^e)⁻¹)=
      ∑ u : (ZMod (p^h))ˣ, ((u : ZMod (p^h))^e)⁻¹ := by
    apply Finset.sum_bij (fun j hj => ZMod.unitOfCoprime j
      (((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hj).2).symm.pow_right h))
    · intro _ _; exact mem_univ _
    · intro a ha b hb hab
      have hc : (a : ZMod (p^h))=(b : ZMod (p^h)) := by
        simpa only [ZMod.coe_unitOfCoprime] using congrArg Units.val hab
      have hal : a < p^h := (mem_Ico.mp (mem_filter.mp ha).1).2
      have hbl : b < p^h := (mem_Ico.mp (mem_filter.mp hb).1).2
      have hv := congrArg ZMod.val hc
      simpa only [ZMod.val_natCast_of_lt hal,ZMod.val_natCast_of_lt hbl] using hv
    · intro u _
      have hcop : Nat.Coprime (u : ZMod (p^h)).val (p^h) := by
        rw [← ZMod.isUnit_iff_coprime]
        simpa only [ZMod.natCast_zmod_val] using u.isUnit
      have hnd : ¬p ∣ (u : ZMod (p^h)).val := by
        intro hd
        have he := Nat.dvd_gcd hd (dvd_pow_self p (by omega : h ≠ 0))
        rw [hcop.gcd_eq_one] at he
        exact hp.not_dvd_one he
      have hvpos : 1 ≤ (u : ZMod (p^h)).val := by
        have : (u : ZMod (p^h)).val ≠ 0 := by intro he; exact hnd (he ▸ dvd_zero p)
        omega
      refine ⟨(u : ZMod (p^h)).val,mem_filter.mpr
        ⟨mem_Ico.mpr ⟨hvpos,ZMod.val_lt _⟩,hnd⟩,?_⟩
      ext
      simp only [ZMod.coe_unitOfCoprime,ZMod.natCast_zmod_val]
    · intro j hj
      simp only [ZMod.coe_unitOfCoprime]
  rw [hbase]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Units.val_pow_eq_pow_val,ZMod.inv_coe_unit,← inv_pow,Units.val_pow_eq_pow_val]

/-- The complete inverse-square harmonic sum has at least h powers of p. -/
theorem harmonic_two_dvd {p h : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hh : 1 ≤ h) :
    pDvdRat p h (harmonic p (p^h) 2) := by
  classical
  let : NeZero (p^h) := ⟨pow_ne_zero h hp.ne_zero⟩
  have hc2 : Nat.Coprime 2 (p^h) :=
    ((hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by decide : 0 < 2) hd; omega)).symm).pow_right h
  have hc3 : Nat.Coprime 3 (p^h) :=
    ((hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by decide : 0 < 3) hd; omega)).symm).pow_right h
  let v := ZMod.unitOfCoprime 2 hc2
  have hv : IsUnit ((v : ZMod (p^h))^2-1) := by
    have he : ((v : ZMod (p^h))^2-1)=(3 : ZMod (p^h)) := by
      simp only [v,ZMod.coe_unitOfCoprime]; ring
    rw [he]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hc3
  apply pDvdRat_sum_inv_pow p h 2 (unitRange p (p^h)) id
  · intro j hj
    exact (mem_Ico.mp (mem_filter.mp hj).1).1
  · intro j hj
    exact hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2
  · change (∑ j ∈ unitRange p (p^h), ((j : ZMod (p^h))^2)⁻¹)=0
    rw [sum_unitRange_eq_units hp hh]
    exact sum_units_inv_pow_zero 2 v hv

/-- The prime-level inverse fourth-power harmonic sum is divisible by p. -/
theorem harmonic_four_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDvdRat p 1 (harmonic p p 4) := by
  classical
  have hmain : pDvdRat p 1 (harmonic p (p^1) 4) := by
    let : NeZero (p^1) := ⟨pow_ne_zero 1 hp.ne_zero⟩
    have hc2 : Nat.Coprime 2 (p^1) :=
      ((hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by decide : 0 < 2) hd; omega)).symm).pow_right 1
    have hc15p : Nat.Coprime 15 p := by
      apply Nat.Coprime.symm
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      have hd' : p ∣ 3*5 := by simpa using hd
      rcases hp.dvd_mul.mp hd' with hd | hd
      · have := Nat.le_of_dvd (by decide : 0 < 3) hd; omega
      · have := Nat.le_of_dvd (by decide : 0 < 5) hd; omega
    let v := ZMod.unitOfCoprime 2 hc2
    have hv : IsUnit ((v : ZMod (p^1))^4-1) := by
      have he : ((v : ZMod (p^1))^4-1)=(15 : ZMod (p^1)) := by
        simp only [v,ZMod.coe_unitOfCoprime]; ring
      rw [he]
      exact (ZMod.isUnit_iff_coprime _ _).mpr (hc15p.pow_right 1)
    apply pDvdRat_sum_inv_pow p 1 4 (unitRange p (p^1)) id
    · intro j hj
      exact (mem_Ico.mp (mem_filter.mp hj).1).1
    · intro j hj
      exact hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2
    · change (∑ j ∈ unitRange p (p^1), ((j : ZMod (p^1))^4)⁻¹)=0
      rw [sum_unitRange_eq_units hp (by omega : 1 ≤ 1)]
      exact sum_units_inv_pow_zero 4 v hv
  simpa only [pow_one] using hmain

end A361712

end

section

namespace A361712
open Finset

lemma pDvdRat_cancel_nat {p M c : ℕ} {q : ℚ} (hc : 0 < c) (hcp : Nat.Coprime p c)
    (h : pDvdRat p M ((c : ℚ)*q)) : pDvdRat p M q := by
  have hm := pDvdRat_mul h (pDvdRat_inv_nat hc hcp)
  have hc0 : (c : ℚ) ≠ 0 := by positivity
  have he : ((c : ℚ)*q)*(c : ℚ)⁻¹=q := by field_simp
  simpa only [Nat.add_zero,he] using hm

theorem harmonic_reflection (p N e : ℕ) (hpN : p ∣ N) :
    (∑ j ∈ unitRange p N, (((N-j : ℕ) : ℚ)^e)⁻¹)=harmonic p N e := by
  classical
  unfold harmonic
  apply Finset.sum_bij (fun j _ => N-j)
  · intro j hj
    obtain ⟨hjI,hjp⟩ := mem_filter.mp hj
    obtain ⟨hj0,hjN⟩ := mem_Ico.mp hjI
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    intro hd
    have he : N-j+j=N := Nat.sub_add_cancel hjN.le
    exact hjp ((Nat.dvd_add_right hd).mp (he.symm ▸ hpN))
  · intro a ha b hb he
    have haN := (mem_Ico.mp (mem_filter.mp ha).1).2
    have hbN := (mem_Ico.mp (mem_filter.mp hb).1).2
    omega
  · intro j hj
    obtain ⟨hjI,hjp⟩ := mem_filter.mp hj
    obtain ⟨hj0,hjN⟩ := mem_Ico.mp hjI
    refine ⟨N-j,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro hd
    have he : N-j+j=N := Nat.sub_add_cancel hjN.le
    exact hjp ((Nat.dvd_add_right hd).mp (he.symm ▸ hpN))
  · intro j hj
    rfl

/-- Exact reflection remainder: all denominators remain prime-to-p. -/
theorem cube_reflection_remainder {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : 1 ≤ k) (hkN : k < p^r) (hkp : ¬p∣k) :
    pDvdRat p (2*r)
      ((((p^r-k : ℕ) : ℚ)^3)⁻¹+((k : ℚ)^3)⁻¹+3*(p^r : ℕ)*((k : ℚ)^4)⁻¹) := by
  have hpN : p ∣ p^r := dvd_pow_self p (by omega)
  have hkN0 : 0 < p^r-k := by omega
  have hkm : ¬p ∣ p^r-k := by
    intro hd
    have he : p^r-k+k=p^r := Nat.sub_add_cancel hkN.le
    exact hkp ((Nat.dvd_add_right hd).mp (he.symm ▸ hpN))
  let A : ℤ := 3*(p^r : ℕ)^2-8*(p^r : ℕ)*k+6*(k : ℤ)^2
  let B : ℕ := k^4*(p^r-k)^3
  refine ⟨A,B,Nat.mul_pos (pow_pos hk 4) (pow_pos hkN0 3),
    (hp.coprime_iff_not_dvd.mpr hkp).pow_right 4 |>.mul_right
      ((hp.coprime_iff_not_dvd.mpr hkm).pow_right 3),?_⟩
  have hkq : (k : ℚ) ≠ 0 := by positivity
  have hkmq : ((p^r-k : ℕ) : ℚ) ≠ 0 := by positivity
  have hpow : (p : ℚ)^(2*r)=((p^r : ℕ) : ℚ)^2 := by
    push_cast
    rw [← pow_mul,Nat.mul_comm]
  rw [hpow]
  dsimp [A,B]
  push_cast
  rw [Nat.cast_sub hkN.le]
  have hm0 : ((p^r : ℕ) : ℚ)-(k : ℚ) ≠ 0 := by
    rw [← Nat.cast_sub hkN.le]
    exact hkmq
  field_simp [hkq,hm0]
  push_cast
  ring

/-- Reflection yields two powers of the full prime-power length in the
complete cubic harmonic relation. -/
theorem harmonic_cube_relation {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    pDvdRat p (2*r) (2*harmonic p (p^r) 3+3*(p^r : ℕ)*harmonic p (p^r) 4) := by
  have hh := harmonic_reflection p (p^r) 3 (dvd_pow_self p (by omega))
  have hs := pDvdRat_sum (s := unitRange p (p^r)) (fun k hk =>
    cube_reflection_remainder hp hr (mem_Ico.mp (mem_filter.mp hk).1).1
      (mem_Ico.mp (mem_filter.mp hk).1).2 (mem_filter.mp hk).2)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  rw [hh] at hs
  convert hs using 1 <;> unfold harmonic <;> ring

/-- H3(p) is divisible by p², using the p-divisibility of H4(p). -/
theorem harmonic_three_prime_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    pDvdRat p 2 (harmonic p p 3) := by
  have hr := harmonic_cube_relation (r := 1) hp (by omega)
  simp only [pow_one,Nat.mul_one] at hr
  have hc : pDvdRat p 1 (3*(p : ℚ)) := by
    refine ⟨3,1,by omega,Nat.coprime_one_right p,?_⟩
    simp
    ring
  have hm := pDvdRat_mul hc (harmonic_four_dvd hp hp7)
  have h2 := pDvdRat_sub hr hm
  have h2' : pDvdRat p 2 (2*harmonic p p 3) := by convert h2 using 1 <;> ring
  exact pDvdRat_cancel_nat (by omega : 0 < 2)
    (hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by omega : 0 < 2) h; omega)) h2'

end A361712

end

section

namespace A361712
open Finset

noncomputable def paired (n k : ℕ) : ℚ := (n.choose k : ℚ)*((n+k-1).choose k : ℚ)
noncomputable def productKernel (n k : ℕ) : ℚ :=
  ∏ j ∈ Ico 1 k, (1-(n : ℚ)^2/(j : ℚ)^2)

/-- Cleared-denominator adjacent-index identity, valid through k=n. -/
theorem paired_step (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    paired n (k+1)*(k+1 : ℚ)^2=paired n k*((n : ℚ)^2-(k : ℚ)^2) := by
  have h1 := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_succ_right_eq n k)
  have h2 := congrArg (fun a : ℕ => (a : ℚ)) (Nat.add_one_mul_choose_eq (n+k-1) k)
  have hnk : n+k-1+1=n+k := by omega
  rw [hnk] at h2
  have hsub : ((n-k : ℕ) : ℚ)=(n : ℚ)-k := Nat.cast_sub hk
  push_cast at h1 h2
  rw [hsub] at h1
  unfold paired
  rw [show n+(k+1)-1=n+k by omega]
  push_cast
  calc
    _ = ((n.choose (k+1) : ℚ)*(k+1))*(((n+k).choose (k+1) : ℚ)*(k+1)) := by ring
    _ = ((n.choose k : ℚ)*((n : ℚ)-k))*(((n : ℚ)+k)*((n+k-1).choose k : ℚ)) := by rw [h1,← h2]
    _ = _ := by ring

/-- Exact factorial-product identity, retaining its sign and all unit
 denominators rather than assuming a p-adic expansion. -/
theorem paired_product (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    paired n k=(-1 : ℚ)^(k-1)*(n : ℚ)^2/(k : ℚ)^2*productKernel n k := by
  have hall : ∀ j : ℕ, j+1 ≤ n →
      paired n (j+1)=(-1 : ℚ)^j*(n : ℚ)^2/(j+1 : ℚ)^2*productKernel n (j+1) := by
    intro j
    induction j with
    | zero =>
      intro h
      simp only [paired,productKernel,show n+1-1=n by omega]
      norm_num
      ring
    | succ j ih =>
      intro h
      have hprev := ih (by omega : j+1 ≤ n)
      have hstep := paired_step n (j+1) hn (by omega)
      have hj : (j+1 : ℚ) ≠ 0 := by positivity
      have hj2 : (j+1+1 : ℚ) ≠ 0 := by positivity
      have hprod : productKernel n (j+1+1)=productKernel n (j+1)*
          (1-(n : ℚ)^2/(j+1 : ℚ)^2) := by
        unfold productKernel
        rw [prod_Ico_succ_top (by omega : 1 ≤ j+1)]
        push_cast
        rfl
      rw [hprev] at hstep
      rw [hprod,pow_succ]
      push_cast at hstep ⊢
      apply mul_right_cancel₀ (pow_ne_zero 2 hj2)
      field_simp [hj] at hstep ⊢
      linear_combination hstep
  have he : k=(k-1)+1 := by omega
  rw [he]
  simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hall (k-1) (by omega)

noncomputable def term (n k : ℕ) : ℚ :=
  (n.choose k : ℚ)^2*((n+k).choose k : ℚ)*((n+k-1).choose k : ℚ)

/-- The exact product formula underlying both target supercongruences. -/
theorem term_product (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkn : k < n) :
    term n k=(n : ℚ)^3*((n : ℚ)+k)/(k : ℚ)^4*(productKernel n k)^2 := by
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have hkq : (k : ℚ) ≠ 0 := by positivity
  have hchoose := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_mul_succ_eq (n+k-1) k)
  rw [show n+k-1+1=n+k by omega,show n+k-k=n by omega] at hchoose
  push_cast at hchoose
  have hrel : term n k=paired n k^2*((n : ℚ)+k)/n := by
    unfold term paired
    apply (eq_div_iff hnq).mpr
    linear_combination -(n.choose k : ℚ)^2*((n+k-1).choose k : ℚ)*hchoose
  rw [hrel,paired_product n k hn hk hkn.le]
  have hsign : ((-1 : ℚ)^(k-1))^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  field_simp [hnq,hkq]
  rw [hsign,one_mul]

end A361712

end

section

namespace A361712
open Finset

lemma pDvdRat_one (p : ℕ) : pDvdRat p 0 (1 : ℚ) := pDvdRat_of_int_zero p 1

lemma pDvdRat_prod {ι : Type*} (S : Finset ι) {p : ℕ} (f : ι → ℚ)
    (hf : ∀ i ∈ S, pDvdRat p 0 (f i)) : pDvdRat p 0 (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using pDvdRat_one p
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    exact pDvdRat_mul (hf a (mem_insert_self _ _)) (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma pDvdRat_prod_sub_one {ι : Type*} (S : Finset ι) {p M : ℕ} (x : ι → ℚ)
    (hx : ∀ i ∈ S, pDvdRat p M (x i)) :
    pDvdRat p M ((∏ i ∈ S, (1+x i))-1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p M
  | insert a S ha ih =>
    have hxa := hx a (mem_insert_self _ _)
    have hxt : ∀ i ∈ S, pDvdRat p M (x i) := fun i hi => hx i (mem_insert_of_mem hi)
    have hP : pDvdRat p 0 (∏ i ∈ S, (1+x i)) := by
      apply pDvdRat_prod
      intro i hi
      exact pDvdRat_add (pDvdRat_one p) (pDvdRat_mono (Nat.zero_le _) (hxt i hi))
    have hmul : pDvdRat p M (x a*(∏ i ∈ S,(1+x i))) := by
      simpa only [Nat.add_zero] using pDvdRat_mul hxa hP
    have hsum := pDvdRat_add hmul (ih hxt)
    rw [Finset.prod_insert ha]
    convert hsum using 1 <;> ring

/-- Exact finite-precision linearization of a product in the localization. -/
lemma pDvdRat_prod_linear {ι : Type*} (S : Finset ι) {p M : ℕ} (x : ι → ℚ)
    (hx : ∀ i ∈ S, pDvdRat p M (x i)) :
    pDvdRat p (2*M) ((∏ i ∈ S, (1+x i))-1-∑ i ∈ S,x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p (2*M)
  | insert a S ha ih =>
    have hxa := hx a (mem_insert_self _ _)
    have hxt : ∀ i ∈ S, pDvdRat p M (x i) := fun i hi => hx i (mem_insert_of_mem hi)
    have hmul : pDvdRat p (2*M) (x a*((∏ i ∈ S,(1+x i))-1)) := by
      simpa only [two_mul] using pDvdRat_mul hxa (pDvdRat_prod_sub_one S x hxt)
    have hsum := pDvdRat_add (ih hxt) hmul
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    convert hsum using 1 <;> ring

/-- The squared product used in A361712 has linear term -2 Σz, and a
remainder of at least twice the individual p-divisibility. -/
lemma pDvdRat_square_prod_linear {ι : Type*} (S : Finset ι) {p M : ℕ} (z : ι → ℚ)
    (hz : ∀ i ∈ S, pDvdRat p M (z i)) :
    pDvdRat p (2*M) ((∏ i ∈ S,(1-z i))^2-1+2*∑ i ∈ S,z i) := by
  have hneg : ∀ i ∈ S, pDvdRat p M (-z i) := fun i hi => pDvdRat_neg (hz i hi)
  have hE := pDvdRat_prod_linear S (fun i => -z i) hneg
  have hP := pDvdRat_prod_sub_one S (fun i => -z i) hneg
  have hP2 := pDvdRat_pow hP 2
  have htwo : pDvdRat p 0 (2 : ℚ) := pDvdRat_of_int_zero p 2
  have h2E := pDvdRat_mul htwo hE
  simp only [Nat.zero_add] at h2E
  have hsum := pDvdRat_add hP2 h2E
  simp only [← sub_eq_add_neg,Finset.sum_neg_distrib,Nat.zero_add] at hsum
  convert hsum using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset

lemma harmonic_integral {p L : ℕ} (hp : p.Prime) (e : ℕ) :
    pDvdRat p 0 (harmonic p L e) := by
  apply pDvdRat_sum
  intro j hj
  have hj0 : 0<j := (mem_Ico.mp (mem_filter.mp hj).1).1
  have hjc := hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2
  have he := pDvdRat_pow (pDvdRat_inv_nat hj0 hjc) e
  simpa only [Nat.mul_zero,inv_pow] using he

lemma harmonic_three_power_dvd {p r : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hr : 1≤r) :
    pDvdRat p r (harmonic p (p^r) 3) := by
  have hN : pDvdRat p r ((p^r:ℕ):ℚ) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have hN3 := pDvdRat_mul (pDvdRat_of_int_zero p 3) hN
  simp only [Nat.zero_add] at hN3
  have he := pDvdRat_mul hN3 (harmonic_integral (L:=p^r) hp 4)
  simp only [Nat.add_zero] at he
  have hc := pDvdRat_mono (by omega : r≤2*r) (harmonic_cube_relation hp hr)
  have hs := pDvdRat_sub hc he
  have hs' : pDvdRat p r (2*harmonic p (p^r) 3) := by
    convert hs using 1 <;> ring
  exact pDvdRat_cancel_nat (by omega : 0<2)
    (hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by omega : 0<2) hd; omega)) hs'

end A361712

end

section

namespace A361712

lemma square_inverse_linear {p h : ℕ} {x y : ℚ}
    (hx : x≠0) (hxy : x+y≠0)
    (hxi : pDvdRat p 0 x⁻¹) (hxyi : pDvdRat p 0 (x+y)⁻¹)
    (hxint : pDvdRat p 0 x) (hy : pDvdRat p h y) :
    pDvdRat p (2*h) ((x+y)⁻¹^2-x⁻¹^2+2*y*x⁻¹^3) := by
  have hy0 := pDvdRat_mono (Nat.zero_le _) hy
  have hnum := pDvdRat_add (pDvdRat_mul (pDvdRat_of_int_zero p 3) hxint)
    (pDvdRat_mul (pDvdRat_of_int_zero p 2) hy0)
  have hden := pDvdRat_mul (pDvdRat_pow hxi 3) (pDvdRat_pow hxyi 2)
  have he := pDvdRat_mul (pDvdRat_pow hy 2) (pDvdRat_mul hnum hden)
  simp only [Nat.mul_zero,Nat.add_zero] at he
  convert he using 1
  field_simp
  ring

lemma square_inverse_quadratic {p h : ℕ} {x y : ℚ}
    (hx : x≠0) (hxy : x+y≠0)
    (hxi : pDvdRat p 0 x⁻¹) (hxyi : pDvdRat p 0 (x+y)⁻¹)
    (hxint : pDvdRat p 0 x) (hy : pDvdRat p h y) :
    pDvdRat p (3*h) ((x+y)⁻¹^2-x⁻¹^2+2*y*x⁻¹^3-3*y^2*x⁻¹^4) := by
  have hy0 := pDvdRat_mono (Nat.zero_le _) hy
  have hnum := pDvdRat_neg (pDvdRat_add
    (pDvdRat_mul (pDvdRat_of_int_zero p 4) hxint)
    (pDvdRat_mul (pDvdRat_of_int_zero p 3) hy0))
  have hden := pDvdRat_mul (pDvdRat_pow hxi 4) (pDvdRat_pow hxyi 2)
  have he := pDvdRat_mul (pDvdRat_pow hy 3) (pDvdRat_mul hnum hden)
  simp only [Nat.mul_zero,Nat.add_zero] at he
  convert he using 1
  field_simp
  ring

end A361712

end

section

namespace A361712
open Finset

lemma harmonic_blocks (p L a e : ℕ) (hL : 0<L) (hpL : p∣L) :
    harmonic p (a*L) e =
      ∑b∈range a,∑j∈unitRange p L,(((b*L+j:ℕ):ℚ)^e)⁻¹ := by
  classical
  rw [←sum_product (range a) (unitRange p L)
    (fun z : ℕ×ℕ => (((z.1*L+z.2:ℕ):ℚ)^e)⁻¹)]
  unfold harmonic
  symm
  apply sum_bij (fun z _ => z.1*L+z.2)
  · intro z hz
    obtain ⟨hb,hj⟩ := mem_product.mp hz
    have hb' := mem_range.mp hb
    obtain ⟨hjI,hjp⟩ := mem_filter.mp hj
    obtain ⟨hj0,hjL⟩ := mem_Ico.mp hjI
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨by omega,?_⟩,?_⟩
    · calc
        z.1*L+z.2 < z.1*L+L := Nat.add_lt_add_left hjL _
        _ = (z.1+1)*L := by ring
        _ ≤ a*L := Nat.mul_le_mul_right L (by omega)
    · intro hd
      exact hjp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpL z.1)).mp hd)
  · intro x hx y hy he
    have hxL := (mem_Ico.mp (mem_filter.mp (mem_product.mp hx).2).1).2
    have hyL := (mem_Ico.mp (mem_filter.mp (mem_product.mp hy).2).1).2
    have hdiv := congrArg (fun n=>n/L) he
    have hmod := congrArg (fun n=>n%L) he
    rw [Nat.add_comm (x.1*L),Nat.add_comm (y.1*L),
      Nat.add_mul_div_right _ _ hL,Nat.add_mul_div_right _ _ hL,
      Nat.div_eq_of_lt hxL,Nat.div_eq_of_lt hyL,Nat.zero_add,Nat.zero_add] at hdiv
    simp [Nat.add_mod,Nat.mod_eq_of_lt hxL,Nat.mod_eq_of_lt hyL] at hmod
    exact Prod.ext hdiv hmod
  · intro k hk
    obtain ⟨hkI,hkp⟩ := mem_filter.mp hk
    obtain ⟨hk0,hka⟩ := mem_Ico.mp hkI
    have hmL := Nat.mod_lt k hL
    have hmodp : ¬p∣k%L := by
      intro hd
      have he := Nat.mod_add_div k L
      have ht : p∣L*(k/L) := dvd_mul_of_dvd_left hpL (k/L)
      exact hkp (he ▸ Nat.dvd_add hd ht)
    have hm0 : 1≤k%L := by
      by_contra hn
      have hz : k%L=0 := by omega
      exact hmodp (hz ▸ dvd_zero p)
    refine ⟨(k/L,k%L),mem_product.mpr ⟨mem_range.mpr ?_,
      mem_filter.mpr ⟨mem_Ico.mpr ⟨hm0,hmL⟩,hmodp⟩⟩,?_⟩
    · exact (Nat.div_lt_iff_lt_mul hL).mpr (by simpa [Nat.mul_comm] using hka)
    · simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div k L
  · intro z hz
    rfl

end A361712

end

section

namespace A361712
open Finset

lemma harmonic_block_square {p h b : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (h+1)
      ((∑j∈unitRange p (p^h),(((b*p^h+j:ℕ):ℚ)^2)⁻¹)-harmonic p (p^h) 2) := by
  have hL : p∣p^h := dvd_pow_self p (by omega)
  have hy : pDvdRat p h ((b*p^h:ℕ):ℚ) :=
    ⟨b,1,by omega,Nat.coprime_one_right p,by push_cast; ring⟩
  have he := pDvdRat_sum (s:=unitRange p (p^h)) (fun j hj => by
    have hj0 : 0<j := (mem_Ico.mp (mem_filter.mp hj).1).1
    have hjp : ¬p∣j := (mem_filter.mp hj).2
    have hsum : ¬p∣j+b*p^h := by
      intro hd
      exact hjp ((Nat.dvd_add_left (dvd_mul_of_dvd_right hL b)).mp hd)
    have hxi := pDvdRat_inv_nat hj0 (hp.coprime_iff_not_dvd.mpr hjp)
    have hxyi := pDvdRat_inv_nat (by omega : 0<j+b*p^h)
      (hp.coprime_iff_not_dvd.mpr hsum)
    have hxint := pDvdRat_of_int_zero p (j:ℤ)
    have ht := square_inverse_linear (by positivity : (j:ℚ)≠0)
      (by positivity : (j:ℚ)+(b*p^h:ℕ)≠0) hxi
      (by simpa only [Nat.cast_add] using hxyi) hxint hy
    exact pDvdRat_mono (by omega : h+1≤2*h) ht)
  have hlin := pDvdRat_mul
    (pDvdRat_mul (pDvdRat_of_int_zero p 2) hy)
    (harmonic_three_power_dvd hp hp5 hh)
  have hlin' : pDvdRat p (h+1) (2*((b*p^h:ℕ):ℚ)*harmonic p (p^h) 3) :=
    pDvdRat_mono (by omega) hlin
  have hs := pDvdRat_sub he hlin'
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum] at hs
  unfold harmonic at hs ⊢
  convert hs using 1 <;> simp only [Nat.cast_add,add_comm (b*p^h:ℚ),inv_pow] <;> ring

lemma harmonic_multiple_square {p h a : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (h+1) (harmonic p (a*p^h) 2-(a:ℚ)*harmonic p (p^h) 2) := by
  rw [harmonic_blocks p (p^h) a 2 (pow_pos hp.pos _) (dvd_pow_self p (by omega))]
  have he := pDvdRat_sum (s:=range a) (fun b _ => harmonic_block_square hp hp5 hh (b:=b))
  simpa only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] using he

lemma harmonic_multiple_square_dvd {p h a : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p h (harmonic p (a*p^h) 2) := by
  have he := pDvdRat_mono (by omega : h≤h+1)
    (harmonic_multiple_square (a:=a) hp hp5 hh)
  have hm := pDvdRat_mul (pDvdRat_of_int_zero p (a:ℤ)) (harmonic_two_dvd hp hp5 hh)
  simp only [Nat.zero_add,Int.cast_natCast] at hm
  convert pDvdRat_add he hm using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset
lemma range_first_moment (n:ℕ) : 2*(∑b∈range n,(b:ℚ))=(n:ℚ)*((n:ℚ)-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; push_cast; linear_combination ih
lemma range_second_moment (n:ℕ) : 6*(∑b∈range n,(b:ℚ)^2)=
    (n:ℚ)*((n:ℚ)-1)*(2*(n:ℚ)-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma range_first_moment_dvd {p:ℕ} (hp:p.Prime) (hp5:5≤p) :
    pDvdRat p 1 (∑b∈range p,(b:ℚ)) := by
  have he : pDvdRat p 1 (2*(∑b∈range p,(b:ℚ))) := by
    rw [range_first_moment]
    refine ⟨(p:ℤ)-1,1,by omega,Nat.coprime_one_right p,?_⟩
    push_cast; ring
  apply pDvdRat_cancel_nat (by omega : 0<2) _ he
  exact hp.coprime_iff_not_dvd.mpr (fun hd=>by
    have := Nat.le_of_dvd (by omega : 0<2) hd; omega)

lemma range_second_moment_dvd {p:ℕ} (hp:p.Prime) (hp5:5≤p) :
    pDvdRat p 1 (∑b∈range p,(b:ℚ)^2) := by
  have he : pDvdRat p 1 (6*(∑b∈range p,(b:ℚ)^2)) := by
    rw [range_second_moment]
    refine ⟨((p:ℤ)-1)*(2*(p:ℤ)-1),1,by omega,Nat.coprime_one_right p,?_⟩
    push_cast; ring
  apply pDvdRat_cancel_nat (by omega : 0<6) _ he
  have hc2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (fun hd=>by
    have := Nat.le_of_dvd (by omega : 0<2) hd; omega)
  have hc3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (fun hd=>by
    have := Nat.le_of_dvd (by omega : 0<3) hd; omega)
  simpa using hc2.mul_right hc3

end A361712

end

section

namespace A361712
open Finset

lemma harmonic_block_square_quadratic {p h b : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (3*h)
      ((∑j∈unitRange p (p^h),(((b*p^h+j:ℕ):ℚ)^2)⁻¹)-harmonic p (p^h) 2+
       (2*((p^h:ℕ):ℚ)*harmonic p (p^h) 3)*(b:ℚ)-
       (3*((p^h:ℕ):ℚ)^2*harmonic p (p^h) 4)*(b:ℚ)^2) := by
  have hL : p∣p^h := dvd_pow_self p (by omega)
  have hy : pDvdRat p h ((b*p^h:ℕ):ℚ) :=
    ⟨b,1,by omega,Nat.coprime_one_right p,by push_cast; ring⟩
  have he := pDvdRat_sum (s:=unitRange p (p^h)) (fun j hj => by
    have hj0 : 0<j := (mem_Ico.mp (mem_filter.mp hj).1).1
    have hjp : ¬p∣j := (mem_filter.mp hj).2
    have hsum : ¬p∣j+b*p^h := by
      intro hd
      exact hjp ((Nat.dvd_add_left (dvd_mul_of_dvd_right hL b)).mp hd)
    have hxi := pDvdRat_inv_nat hj0 (hp.coprime_iff_not_dvd.mpr hjp)
    have hxyi := pDvdRat_inv_nat (by omega : 0<j+b*p^h)
      (hp.coprime_iff_not_dvd.mpr hsum)
    have hxint := pDvdRat_of_int_zero p (j:ℤ)
    have ht := square_inverse_quadratic (by positivity : (j:ℚ)≠0)
      (by positivity : (j:ℚ)+(b*p^h:ℕ)≠0) hxi
      (by simpa only [Nat.cast_add] using hxyi) hxint hy
    exact ht)
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum] at he
  unfold harmonic
  convert he using 1 <;> simp only [Nat.cast_add,inv_pow] <;> push_cast <;> ring

lemma harmonic_square_step {p h : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (h+2) (harmonic p (p^(h+1)) 2-(p:ℚ)*harmonic p (p^h) 2) := by
  have he := pDvdRat_sum (s:=range p)
    (fun b _ => harmonic_block_square_quadratic hp hp5 hh (b:=b))
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_range,
    nsmul_eq_mul,←mul_sum] at he
  have hblocks := harmonic_blocks p (p^h) p 2 (pow_pos hp.pos _)
    (dvd_pow_self p (by omega))
  rw [←hblocks,←pow_succ'] at he
  have hN : pDvdRat p h ((p^h:ℕ):ℚ) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have hlin := pDvdRat_mul
    (pDvdRat_mul (pDvdRat_mul (pDvdRat_of_int_zero p 2) hN)
      (harmonic_three_power_dvd hp hp5 hh)) (range_first_moment_dvd hp hp5)
  have hquad := pDvdRat_mul
    (pDvdRat_mul (pDvdRat_mul (pDvdRat_of_int_zero p 3) (pDvdRat_pow hN 2))
      (harmonic_integral (L:=p^h) hp 4)) (range_second_moment_dvd hp hp5)
  have he' := pDvdRat_mono (by omega : h+2≤3*h) he
  have hl' := pDvdRat_mono (by omega : h+2≤0+h+h+1) hlin
  have hq' := pDvdRat_mono (by omega : h+2≤0+2*h+0+1) hquad
  convert pDvdRat_add (pDvdRat_sub he' hl') hq' using 1 <;> ring

lemma harmonic_square_lift {p h : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (h+1) (harmonic p (p^h) 2-(p:ℚ)^(h-1)*harmonic p p 2) := by
  induction h, hh using Nat.le_induction with
  | base => simpa using pDvdRat_zero p 2
  | succ h hh ih =>
    have hp1 : pDvdRat p 1 (p:ℚ) :=
      ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
    have hm := pDvdRat_mul hp1 ih
    have he := harmonic_square_step hp hp5 hh
    have hm' : pDvdRat p (h+2)
        ((p:ℚ)*(harmonic p (p^h) 2-(p:ℚ)^(h-1)*harmonic p p 2)) := by
      simpa only [Nat.add_comm 1] using hm
    have hs := pDvdRat_add he hm'
    have hpow : (p:ℚ)^(h-1)*(p:ℚ)=(p:ℚ)^h := by
      rw [←pow_succ,Nat.sub_add_cancel hh]
    simp only [Nat.add_sub_cancel] at *
    convert hs using 1 <;> linear_combination (harmonic p p 2)*hpow

lemma harmonic_square_lift_multiple {p h a : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) (hh : 1≤h) :
    pDvdRat p (h+1)
      (harmonic p (a*p^h) 2-(a:ℚ)*(p:ℚ)^(h-1)*harmonic p p 2) := by
  have he := harmonic_multiple_square (a:=a) hp hp5 hh
  have hm := pDvdRat_mul (pDvdRat_of_int_zero p (a:ℤ))
    (harmonic_square_lift hp hp5 hh)
  simp only [Nat.zero_add,Int.cast_natCast] at hm
  convert pDvdRat_add he hm using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset

lemma valuation_lt_power {p b j:ℕ} (hp:p.Prime) (hj:0<j) (hjb:j<p^b) :
    padicValNat p j<b := by
  by_contra hn
  have hd : p^b∣j := (pow_dvd_pow p (by omega : b≤padicValNat p j)).trans
    (pow_padicValNat_dvd (p:=p) (n:=j))
  have := Nat.le_of_dvd hj hd
  omega

lemma power_kernel_sub_one {p b k:ℕ} (hp:p.Prime) (hb:1≤b) (hk:k≤p^b) :
    pDvdRat p 2 (productKernel (p^b) k-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz : ∀j∈Ico 1 k,pDvdRat p 2 ((((p^b:ℕ):ℚ)^2)/(j:ℚ)^2) := by
    intro j hj
    have hj0 : 0<j := (mem_Ico.mp hj).1
    have hjb : j<p^b := lt_of_lt_of_le (mem_Ico.mp hj).2 hk
    have hv := valuation_lt_power hp hj0 hjb
    have hn : pDvdRat p (2*b) (((p^b:ℕ):ℚ)^2) :=
      ⟨1,1,by omega,Nat.coprime_one_right p,by push_cast; simp [pow_mul,Nat.mul_comm]⟩
    have he := pDvdRat_div_nat (d:=j^2) hp (pow_pos hj0 2)
      (by rw [padicValNat.pow]) (by omega : 2*padicValNat p j≤2*b) hn
    have he' := pDvdRat_mono (by omega : 2≤2*b-2*padicValNat p j) he
    simpa only [Nat.cast_pow] using he'
  have he := pDvdRat_prod_sub_one (Ico 1 k)
    (fun j=>-((((p^b:ℕ):ℚ)^2)/(j:ℚ)^2)) (fun j hj=>pDvdRat_neg (hz j hj))
  simpa only [productKernel,←sub_eq_add_neg] using he

lemma power_kernel_integral {p b k:ℕ} (hp:p.Prime) (hb:1≤b) (hk:k≤p^b) :
    pDvdRat p 0 (productKernel (p^b) k) := by
  have he := pDvdRat_mono (by omega : 0≤2) (power_kernel_sub_one hp hb hk)
  convert pDvdRat_add he (pDvdRat_one p) using 1 <;> ring

lemma power_term_valuation {p b k:ℕ} (hp:p.Prime) (hb:1≤b) (hk:1≤k) (hkb:k<p^b) :
    pDvdRat p (3*(b-padicValNat p k)) (term (p^b) k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := padicValNat p k
  have hs : s<b := valuation_lt_power hp hk hkb
  have hnk : p^s∣p^b+k := Nat.dvd_add
    (pow_dvd_pow p hs.le) (pow_padicValNat_dvd (p:=p) (n:=k))
  have hnkZ : (p:ℤ)^s∣((p^b+k:ℕ):ℤ) := by exact_mod_cast hnk
  have hn : pDvdRat p (3*b) (((p^b:ℕ):ℚ)^3) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by push_cast; simp [pow_mul,Nat.mul_comm]⟩
  have hnum := pDvdRat_mul hn (pDvdRat_of_int ((p^b+k:ℕ):ℤ) hnkZ)
  have hd := pDvdRat_div_nat (d:=k^4) hp (pow_pos hk 4)
    (by rw [padicValNat.pow]) (by dsimp [s] at hs ⊢; omega : 4*padicValNat p k≤3*b+s) hnum
  have he := pDvdRat_mul hd (pDvdRat_pow (power_kernel_integral hp hb hkb.le) 2)
  rw [term_product _ _ (pow_pos hp.pos _) hk hkb]
  have hexp : 3*b+s-4*padicValNat p k+2*0=3*(b-padicValNat p k) := by dsimp [s] at hs ⊢; omega
  rw [hexp] at he
  simpa only [Int.cast_natCast,Int.cast_add,Int.cast_pow,Nat.cast_add,Nat.cast_pow] using he

end A361712

end

section

namespace A361712
open Finset
noncomputable def unitKernel (p n k:ℕ) : ℚ :=
  ∏j∈unitRange p k, (1-(n:ℚ)^2/(j:ℚ)^2)

lemma unit_kernel_factor {p b k j:ℕ} (hp:p.Prime) (hj:j∈unitRange p k) :
    pDvdRat p (2*b) ((((p^b:ℕ):ℚ)^2)/(j:ℚ)^2) := by
  have hj0 : 0<j := (mem_Ico.mp (mem_filter.mp hj).1).1
  have hjc := hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2
  refine ⟨1,j^2,pow_pos hj0 2,hjc.pow_right 2,?_⟩
  push_cast
  simp [pow_mul,Nat.mul_comm]

lemma unit_kernel_sub_one {p b k:ℕ} (hp:p.Prime) :
    pDvdRat p (2*b) (unitKernel p (p^b) k-1) := by
  have he := pDvdRat_prod_sub_one (unitRange p k)
    (fun j=>-((((p^b:ℕ):ℚ)^2)/(j:ℚ)^2))
    (fun j hj=>pDvdRat_neg (unit_kernel_factor (b:=b) hp hj))
  simpa only [unitKernel,←sub_eq_add_neg] using he

lemma unit_kernel_square_linear {p b k:ℕ} (hp:p.Prime) :
    pDvdRat p (4*b) ((unitKernel p (p^b) k)^2-1+
      2*(((p^b:ℕ):ℚ)^2)*harmonic p k 2) := by
  have he := pDvdRat_square_prod_linear (unitRange p k)
    (fun j=>(((p^b:ℕ):ℚ)^2)/(j:ℚ)^2)
    (fun j hj=>unit_kernel_factor (b:=b) hp hj)
  have heq : 2*(2*b)=4*b := by omega
  rw [heq] at he
  unfold unitKernel harmonic
  simp_rw [div_eq_mul_inv] at he
  rw [←mul_sum] at he
  simpa only [div_eq_mul_inv,mul_assoc] using he

lemma unit_kernel_square_sub_one {p b k:ℕ} (hp:p.Prime) :
    pDvdRat p (2*b) ((unitKernel p (p^b) k)^2-1) := by
  have hK := unit_kernel_sub_one (b:=b) (k:=k) hp
  have hsq := pDvdRat_mono (by omega : 2*b≤2*(2*b)) (pDvdRat_pow hK 2)
  have htwo := pDvdRat_mul (pDvdRat_of_int_zero p 2) hK
  simp only [Nat.zero_add] at htwo
  convert pDvdRat_add hsq htwo using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset

lemma kernel_split {p n k l:ℕ} (hp:0<p) (hlo:p*l<k) (hhi:k≤p*(l+1)) :
    productKernel (p*n) k=productKernel n (l+1)*unitKernel p (p*n) k := by
  have hm : (∏j∈(Ico 1 k).filter (fun j=>p∣j),
      (1-((p*n:ℕ):ℚ)^2/(j:ℚ)^2))=productKernel n (l+1) := by
    unfold productKernel
    symm
    apply prod_bij (fun h _=>p*h)
    · intro h hh
      obtain ⟨hh0,hhl⟩ := mem_Ico.mp hh
      apply mem_filter.mpr
      refine ⟨mem_Ico.mpr ⟨Nat.mul_pos hp hh0,?_⟩,dvd_mul_right p h⟩
      exact lt_of_le_of_lt (Nat.mul_le_mul_left p (by omega : h≤l)) hlo
    · intro a ha b hb he
      exact Nat.eq_of_mul_eq_mul_left hp he
    · intro j hj
      obtain ⟨hjI,hjd⟩ := mem_filter.mp hj
      obtain ⟨h,rfl⟩ := hjd
      have hh0 : 1≤h := by
        by_contra hn
        have hz:h=0 := by omega
        have := (mem_Ico.mp hjI).1
        simp [hz] at this
      have hhl : h<l+1 := Nat.lt_of_mul_lt_mul_left
        (lt_of_lt_of_le (mem_Ico.mp hjI).2 hhi)
      exact ⟨h,mem_Ico.mpr ⟨hh0,hhl⟩,rfl⟩
    · intro h hh
      have hh0 : (h:ℚ)≠0 := by have := (mem_Ico.mp hh).1; positivity
      have hp0 : (p:ℚ)≠0 := by positivity
      push_cast
      field_simp
  unfold productKernel unitKernel unitRange
  rw [←prod_filter_mul_prod_filter_not (Ico 1 k) (fun j=>p∣j)]
  rw [hm]
  rfl

lemma kernel_split_multiple {p n l:ℕ} (hp:0<p) (hl:1≤l) :
    productKernel (p*n) (p*l)=productKernel n l*unitKernel p (p*n) (p*l) := by
  have hlo : p*(l-1)<p*l := Nat.mul_lt_mul_of_pos_left (by omega) hp
  have hhi : p*l≤p*((l-1)+1) := by rw [Nat.sub_add_cancel hl]
  have he := kernel_split (n:=n) hp hlo hhi
  simpa only [Nat.sub_add_cancel hl] using he

lemma term_split_multiple {p n l:ℕ} (hp:0<p) (hn:0<n) (hl:1≤l) (hln:l<n) :
    term (p*n) (p*l)=term n l*(unitKernel p (p*n) (p*l))^2 := by
  rw [term_product _ _ (Nat.mul_pos hp hn) (Nat.mul_pos hp hl)
    (Nat.mul_lt_mul_of_pos_left hln hp),term_product n l hn hl hln,
    kernel_split_multiple hp hl]
  have hp0 : (p:ℚ)≠0 := by positivity
  have hl0 : (l:ℚ)≠0 := by positivity
  push_cast
  field_simp

end A361712

end

section

namespace A361712
lemma pDvdRat_pow_sub {p M:ℕ} {x y:ℚ} (hx:pDvdRat p 0 x) (hy:pDvdRat p 0 y)
    (hxy:pDvdRat p M (x-y)) (e:ℕ) : pDvdRat p M (x^e-y^e) := by
  induction e with
  | zero => simpa using pDvdRat_zero p M
  | succ e ih =>
    have h1 := pDvdRat_mul ih hx
    have h2 := pDvdRat_mul (pDvdRat_pow hy e) hxy
    simp only [Nat.add_zero,Nat.mul_zero,Nat.zero_add] at h1 h2
    convert pDvdRat_add h1 h2 using 1 <;> rw [pow_succ,pow_succ] <;> ring

lemma pDvdRat_inverse_shift {p M:ℕ} {x y:ℚ} (hx:x≠0) (hxy:x+y≠0)
    (hxi:pDvdRat p 0 x⁻¹) (hxyi:pDvdRat p 0 (x+y)⁻¹)
    (hy:pDvdRat p M y) (e:ℕ) :
    pDvdRat p M ((x+y)⁻¹^e-x⁻¹^e) := by
  have he := pDvdRat_neg (pDvdRat_mul hy (pDvdRat_mul hxi hxyi))
  simp only [Nat.add_zero] at he
  have he' : pDvdRat p M ((x+y)⁻¹-x⁻¹) := by
    convert he using 1
    field_simp
    ring
  exact pDvdRat_pow_sub hxyi hxi he' e
end A361712

end

section

namespace A361712
open Finset

lemma harmonic_block_residue {p h b : ℕ} (e:ℕ) (hp : p.Prime) (hh : 1≤h) :
    pDvdRat p h
      ((∑j∈unitRange p (p^h),(((b*p^h+j:ℕ):ℚ)^e)⁻¹)-harmonic p (p^h) e) := by
  have hL : p∣p^h := dvd_pow_self p (by omega)
  have hy : pDvdRat p h ((b*p^h:ℕ):ℚ) :=
    ⟨b,1,by omega,Nat.coprime_one_right p,by push_cast; ring⟩
  have he := pDvdRat_sum (s:=unitRange p (p^h)) (fun j hj => by
    have hj0 : 0<j := (mem_Ico.mp (mem_filter.mp hj).1).1
    have hjp : ¬p∣j := (mem_filter.mp hj).2
    have hsum : ¬p∣j+b*p^h := by
      intro hd
      exact hjp ((Nat.dvd_add_left (dvd_mul_of_dvd_right hL b)).mp hd)
    have hxi := pDvdRat_inv_nat hj0 (hp.coprime_iff_not_dvd.mpr hjp)
    have hxyi := pDvdRat_inv_nat (by omega : 0<j+b*p^h)
      (hp.coprime_iff_not_dvd.mpr hsum)
    have ht := pDvdRat_inverse_shift (by positivity : (j:ℚ)≠0)
      (by positivity : (j:ℚ)+(b*p^h:ℕ)≠0) hxi
      (by simpa only [Nat.cast_add] using hxyi) hy e
    exact ht)
  simp only [sum_sub_distrib] at he
  unfold harmonic
  convert he using 1 <;> simp only [Nat.cast_add,inv_pow] <;> ring

lemma harmonic_multiple_residue {p h a:ℕ} (hp:p.Prime) (hh:1≤h) (e:ℕ) :
    pDvdRat p h (harmonic p (a*p^h) e-(a:ℚ)*harmonic p (p^h) e) := by
  rw [harmonic_blocks p (p^h) a e (pow_pos hp.pos _) (dvd_pow_self p (by omega))]
  have he := pDvdRat_sum (s:=range a) (fun b _=>harmonic_block_residue e hp hh (b:=b))
  simpa only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] using he

lemma harmonic_four_power_dvd {p r:ℕ} (hp:p.Prime) (hr:2≤r) :
    pDvdRat p 1 (harmonic p (p^r) 4) := by
  have he := harmonic_multiple_residue (a:=p^(r-1)) hp (by omega : 1≤1) 4
  simp only [pow_one,←pow_succ,Nat.sub_add_cancel (by omega : 1≤r)] at he
  have hcoeff : pDvdRat p (r-1) (((p^(r-1):ℕ):ℚ)) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have hm := pDvdRat_mul hcoeff (harmonic_integral (L:=p) hp 4)
  have hm' := pDvdRat_mono (by omega : 1≤r-1+0) hm
  convert pDvdRat_add he hm' using 1 <;> ring

lemma harmonic_three_power_strong {p r:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:2≤r) :
    pDvdRat p 3 (harmonic p (p^r) 3) := by
  have hN : pDvdRat p r (((p^r:ℕ):ℚ)) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have hm := pDvdRat_mul (pDvdRat_mul (pDvdRat_of_int_zero p 3) hN)
    (harmonic_four_power_dvd hp hr)
  have hm' := pDvdRat_mono (by omega : 3≤0+r+1) hm
  have he := pDvdRat_mono (by omega : 3≤2*r) (harmonic_cube_relation hp (by omega : 1≤r))
  have hs : pDvdRat p 3 (2*harmonic p (p^r) 3) := by
    convert pDvdRat_sub he hm' using 1 <;> ring
  exact pDvdRat_cancel_nat (by omega : 0<2)
    (hp.coprime_iff_not_dvd.mpr (fun hd=>by
      have := Nat.le_of_dvd (by omega : 0<2) hd; omega)) hs

end A361712

end

section

namespace A361712
open Finset
noncomputable def scaledTerm (n k:ℕ):ℚ := term n k/(n:ℚ)^3

lemma scaled_term_split {p n k l:ℕ} (hp:0<p) (hn:0<n)
    (hk:1≤k) (hkn:k<p*n) (hlo:p*l<k) (hhi:k≤p*(l+1)) :
    scaledTerm (p*n) k=
      (((k:ℚ)^3)⁻¹+(p*n:ℕ)*((k:ℚ)^4)⁻¹)*
       (productKernel n (l+1))^2*(unitKernel p (p*n) k)^2 := by
  unfold scaledTerm
  rw [term_product _ _ (Nat.mul_pos hp hn) hk hkn,kernel_split hp hlo hhi]
  have hp0 : (p:ℚ)≠0 := by positivity
  have hn0 : (n:ℚ)≠0 := by positivity
  have hk0 : (k:ℚ)≠0 := by positivity
  push_cast
  field_simp
  ring

lemma scaled_unit_approx {p r k l:ℕ} (hp:p.Prime) (hr:2≤r)
    (hk:1≤k) (hkn:k<p^r) (hkp:¬p∣k)
    (hlo:p*l<k) (hhi:k≤p*(l+1)) (hl:l<p^(r-1)) :
    pDvdRat p 3 (scaledTerm (p^r) k-
      (((k:ℚ)^3)⁻¹+(p^r:ℕ)*((k:ℚ)^4)⁻¹)*(productKernel (p^(r-1)) (l+1))^2) := by
  have heq : p*p^(r-1)=p^r := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1≤r)]
  have hid := scaled_term_split hp.pos (pow_pos hp.pos _) hk (heq ▸ hkn) hlo hhi
  rw [heq] at hid
  rw [hid]
  have hki := pDvdRat_inv_nat hk (hp.coprime_iff_not_dvd.mpr hkp)
  have hcoef := pDvdRat_add (pDvdRat_pow hki 3)
    (pDvdRat_mul (pDvdRat_of_int_zero p ((p^r:ℕ):ℤ)) (pDvdRat_pow hki 4))
  have hW := pDvdRat_pow (power_kernel_integral hp (by omega : 1≤r-1)
    (by omega : l+1≤p^(r-1))) 2
  have hE := pDvdRat_mono (by omega : 3≤2*r)
    (unit_kernel_square_sub_one (b:=r) (k:=k) hp)
  have hm := pDvdRat_mul (pDvdRat_mul hcoef hW) hE
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Int.cast_natCast,inv_pow] at hm
  convert hm using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset
lemma sum_unit_blocks (p L a : ℕ) (f : ℕ→ℚ) (hL : 0<L) (hpL : p∣L) :
    (∑k∈unitRange p (a*L),f k) =
      ∑b∈range a,∑j∈unitRange p L,f (b*L+j) := by
  classical
  rw [←sum_product (range a) (unitRange p L)
    (fun z : ℕ×ℕ => f (z.1*L+z.2))]
  symm
  apply sum_bij (fun z _ => z.1*L+z.2)
  · intro z hz
    obtain ⟨hb,hj⟩ := mem_product.mp hz
    have hb' := mem_range.mp hb
    obtain ⟨hjI,hjp⟩ := mem_filter.mp hj
    obtain ⟨hj0,hjL⟩ := mem_Ico.mp hjI
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨by omega,?_⟩,?_⟩
    · calc
        z.1*L+z.2 < z.1*L+L := Nat.add_lt_add_left hjL _
        _ = (z.1+1)*L := by ring
        _ ≤ a*L := Nat.mul_le_mul_right L (by omega)
    · intro hd
      exact hjp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpL z.1)).mp hd)
  · intro x hx y hy he
    have hxL := (mem_Ico.mp (mem_filter.mp (mem_product.mp hx).2).1).2
    have hyL := (mem_Ico.mp (mem_filter.mp (mem_product.mp hy).2).1).2
    have hdiv := congrArg (fun n=>n/L) he
    have hmod := congrArg (fun n=>n%L) he
    rw [Nat.add_comm (x.1*L),Nat.add_comm (y.1*L),
      Nat.add_mul_div_right _ _ hL,Nat.add_mul_div_right _ _ hL,
      Nat.div_eq_of_lt hxL,Nat.div_eq_of_lt hyL,Nat.zero_add,Nat.zero_add] at hdiv
    simp [Nat.add_mod,Nat.mod_eq_of_lt hxL,Nat.mod_eq_of_lt hyL] at hmod
    exact Prod.ext hdiv hmod
  · intro k hk
    obtain ⟨hkI,hkp⟩ := mem_filter.mp hk
    obtain ⟨hk0,hka⟩ := mem_Ico.mp hkI
    have hmL := Nat.mod_lt k hL
    have hmodp : ¬p∣k%L := by
      intro hd
      have he := Nat.mod_add_div k L
      have ht : p∣L*(k/L) := dvd_mul_of_dvd_left hpL (k/L)
      exact hkp (he ▸ Nat.dvd_add hd ht)
    have hm0 : 1≤k%L := by
      by_contra hn
      have hz : k%L=0 := by omega
      exact hmodp (hz ▸ dvd_zero p)
    refine ⟨(k/L,k%L),mem_product.mpr ⟨mem_range.mpr ?_,
      mem_filter.mpr ⟨mem_Ico.mpr ⟨hm0,hmL⟩,hmodp⟩⟩,?_⟩
    · exact (Nat.div_lt_iff_lt_mul hL).mpr (by simpa [Nat.mul_comm] using hka)
    · simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div k L
  · intro z hz
    rfl

end A361712

end

section

namespace A361712
open Finset
noncomputable def residueBlock (p b e:ℕ):ℚ :=
  ∑a∈unitRange p p,(((b*p+a:ℕ):ℚ)^e)⁻¹

lemma residue_block_integral {p b:ℕ} (hp:p.Prime) (e:ℕ) :
    pDvdRat p 0 (residueBlock p b e) := by
  apply pDvdRat_sum
  intro a ha
  have ha0 := (mem_Ico.mp (mem_filter.mp ha).1).1
  have hkp : ¬p∣b*p+a := by
    intro hd
    exact (mem_filter.mp ha).2 ((Nat.dvd_add_right (dvd_mul_left p b)).mp hd)
  have he := pDvdRat_pow (pDvdRat_inv_nat (by omega : 0<b*p+a)
    (hp.coprime_iff_not_dvd.mpr hkp)) e
  simpa only [Nat.mul_zero,inv_pow] using he

lemma residue_block_cubic {p b:ℕ} (hp:p.Prime) (hp5:5≤p) :
    pDvdRat p 1 (residueBlock p b 3) := by
  have he := harmonic_block_residue 3 hp (by omega : 1≤1) (b:=b)
  have hh := harmonic_three_power_dvd hp hp5 (by omega : 1≤1)
  simp only [pow_one] at he hh
  convert pDvdRat_add he hh using 1 <;> unfold residueBlock <;> ring

lemma power_kernel_square_sub_one {p b k:ℕ} (hp:p.Prime) (hb:1≤b) (hk:k≤p^b) :
    pDvdRat p 2 ((productKernel (p^b) k)^2-1) := by
  have he := pDvdRat_pow_sub (power_kernel_integral hp hb hk) (pDvdRat_one p)
    (power_kernel_sub_one hp hb hk) 2
  simpa only [one_pow] using he

lemma scaled_unit_block {p r b:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:2≤r)
    (hb:b<p^(r-1)) :
    pDvdRat p 3 ((∑a∈unitRange p p,scaledTerm (p^r) (b*p+a))-
      (residueBlock p b 3+(p^r:ℕ)*residueBlock p b 4)) := by
  have heq : p^(r-1)*p=p^r := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤r)]
  have haProps : ∀a∈unitRange p p,
      1≤b*p+a ∧ b*p+a<p^r ∧ ¬p∣b*p+a ∧ p*b<b*p+a ∧ b*p+a≤p*(b+1) := by
    intro a ha
    obtain ⟨haI,hap⟩ := mem_filter.mp ha
    obtain ⟨ha0,haplt⟩ := mem_Ico.mp haI
    have hkp : ¬p∣b*p+a := by
      intro hd
      exact hap ((Nat.dvd_add_right (dvd_mul_left p b)).mp hd)
    have hkN : b*p+a<p^r := by
      calc
        b*p+a < b*p+p := Nat.add_lt_add_left haplt _
        _ = (b+1)*p := by ring
        _ ≤ p^(r-1)*p := Nat.mul_le_mul_right p (by omega)
        _ = p^r := heq
    refine ⟨by omega,hkN,hkp,?_,?_⟩
    · simpa only [Nat.mul_comm p b] using Nat.lt_add_of_pos_right (by omega : 0<a)
    · calc
        b*p+a ≤ b*p+p := Nat.add_le_add_left haplt.le _
        _ = p*(b+1) := by ring
  have he := pDvdRat_sum (s:=unitRange p p) (fun a ha =>
    scaled_unit_approx hp hr (haProps a ha).1 (haProps a ha).2.1
      (haProps a ha).2.2.1 (haProps a ha).2.2.2.1 (haProps a ha).2.2.2.2 hb)
  have he' : pDvdRat p 3 ((∑a∈unitRange p p,scaledTerm (p^r) (b*p+a))-
      (residueBlock p b 3+(p^r:ℕ)*residueBlock p b 4)*
        (productKernel (p^(r-1)) (b+1))^2) := by
    simpa only [sum_sub_distrib,←sum_mul,sum_add_distrib,←mul_sum,residueBlock] using he
  have hW := power_kernel_square_sub_one hp (by omega : 1≤r-1)
    (by omega : b+1≤p^(r-1))
  have h3 := pDvdRat_mul (residue_block_cubic (b:=b) hp hp5) hW
  have hN : pDvdRat p r (((p^r:ℕ):ℚ)) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have h4 := pDvdRat_mul (pDvdRat_mul hN (residue_block_integral (b:=b) hp 4)) hW
  have h4' := pDvdRat_mono (by omega : 3≤r+0+2) h4
  convert pDvdRat_add he' (pDvdRat_add h3 h4') using 1 <;> ring

lemma unit_sum_divisible {p r:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:2≤r) :
    pDvdRat p (3*r+3) (∑k∈unitRange p (p^r),term (p^r) k) := by
  have heq : p^(r-1)*p=p^r := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤r)]
  have hbS := sum_unit_blocks p p (p^(r-1)) (scaledTerm (p^r)) hp.pos (dvd_refl p)
  rw [heq] at hbS
  have hb3 := harmonic_blocks p p (p^(r-1)) 3 hp.pos (dvd_refl p)
  have hb4 := harmonic_blocks p p (p^(r-1)) 4 hp.pos (dvd_refl p)
  rw [heq] at hb3 hb4
  have he := pDvdRat_sum (s:=range (p^(r-1))) (fun b hb=>
    scaled_unit_block hp hp5 hr (mem_range.mp hb))
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,residueBlock] at he
  rw [←hbS,←hb3,←hb4] at he
  have hN : pDvdRat p r (((p^r:ℕ):ℚ)) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have h4 := pDvdRat_mono (by omega : 3≤r+1)
    (pDvdRat_mul hN (harmonic_four_power_dvd hp hr))
  have hplain := pDvdRat_add (harmonic_three_power_strong hp hp5 hr) h4
  have hscaled : pDvdRat p 3 (∑k∈unitRange p (p^r),scaledTerm (p^r) k) := by
    convert pDvdRat_add he hplain using 1 <;> ring
  have hN3 : pDvdRat p (3*r) (((p^r:ℕ):ℚ)^3) :=
    ⟨1,1,by omega,Nat.coprime_one_right p,by push_cast; simp [pow_mul,Nat.mul_comm]⟩
  have hm := pDvdRat_mul hN3 hscaled
  have hp0 : (((p^r:ℕ):ℚ))≠0 := by positivity
  rw [mul_sum] at hm
  convert hm using 1
  apply sum_congr rfl
  intro k hk
  unfold scaledTerm
  field_simp

end A361712

end

section

namespace A361712
open Finset

lemma prime_kernel_square {p k : ℕ} (hp : p.Prime) (hk : k ≤ p) :
    pDvdRat p 2 ((productKernel p k)^2-1) := by
  have hz : ∀ j ∈ Ico 1 k, pDvdRat p 2 ((p:ℚ)^2/(j:ℚ)^2) := by
    intro j hj
    have hj0 := (mem_Ico.mp hj).1
    have hjp : ¬ p ∣ j := by
      intro hd
      have := Nat.le_of_dvd (by omega : 0<j) hd
      have := (mem_Ico.mp hj).2
      omega
    refine ⟨1,j^2,pow_pos hj0 2,(hp.coprime_iff_not_dvd.mpr hjp).pow_right 2,?_⟩
    simp
  have hK := pDvdRat_prod_sub_one (Ico 1 k) (fun j => -((p:ℚ)^2/(j:ℚ)^2))
    (fun j hj => pDvdRat_neg (hz j hj))
  have hK' : pDvdRat p 2 (productKernel p k-1) := by
    simpa only [productKernel,←sub_eq_add_neg] using hK
  have hsq := pDvdRat_mono (by omega : 2≤2*2) (pDvdRat_pow hK' 2)
  have htwo := pDvdRat_mul (pDvdRat_of_int_zero p 2) hK'
  simp only [Nat.zero_add] at htwo
  convert pDvdRat_add hsq htwo using 1 <;> ring

lemma prime_term_error {p k : ℕ} (hp : p.Prime) (hk : 1≤k) (hkp : k<p) :
    pDvdRat p 5 (term p k-(p:ℚ)^3*((k:ℚ)^3)⁻¹-(p:ℚ)^4*((k:ℚ)^4)⁻¹) := by
  have hkc : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.le_of_dvd (by omega : 0<k) hd
    omega)
  have hf : pDvdRat p 3 ((p:ℚ)^3*((p:ℚ)+k)/(k:ℚ)^4) := by
    refine ⟨(p+k:ℕ),k^4,pow_pos hk 4,hkc.pow_right 4,?_⟩
    push_cast
    ring
  have he := pDvdRat_mul hf (prime_kernel_square hp hkp.le)
  rw [term_product p k hp.pos hk hkp]
  convert he using 1
  have hk0 : (k:ℚ)≠0 := by positivity
  field_simp
  ring

noncomputable def sequence (n : ℕ) : ℤ :=
  ∑k∈range n, ((n.choose k)^2*(n+k).choose k*(n+k-1).choose k:ℕ)

lemma sequence_rat (n : ℕ) : (sequence n:ℚ)=∑k∈range n,term n k := by
  simp [sequence,term]

lemma prime_sequence_expansion {p : ℕ} (hp : p.Prime) :
    pDvdRat p 5 ((sequence p:ℚ)-1-(p:ℚ)^3*harmonic p p 3-(p:ℚ)^4*harmonic p p 4) := by
  have he := pDvdRat_sum (s:=Ico 1 p) (fun k hk =>
    prime_term_error hp (mem_Ico.mp hk).1 (mem_Ico.mp hk).2)
  have hu : unitRange p p=Ico 1 p := by
    apply filter_eq_self.mpr
    intro k hk hd
    have := Nat.le_of_dvd (by have := (mem_Ico.mp hk).1; omega : 0<k) hd
    have := (mem_Ico.mp hk).2
    omega
  have hsum : (∑k∈range p,term p k)=1+∑k∈Ico 1 p,term p k := by
    rw [←sum_range_add_sum_Ico (fun k=>term p k) hp.one_le]
    simp [term]
  rw [sequence_rat,hsum]
  simp only [sum_sub_distrib,←mul_sum] at he
  unfold harmonic
  rw [hu]
  convert he using 1 <;> ring

 theorem prime_congruence {p : ℕ} (hp : p.Prime) (hp7 : 7≤p) :
    (p:ℤ)^5 ∣ sequence p-sequence 1 := by
  have h3 : pDvdRat p 3 ((p:ℚ)^3) := ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have h4 : pDvdRat p 4 ((p:ℚ)^4) := ⟨1,1,by omega,Nat.coprime_one_right p,by simp⟩
  have hm3 := pDvdRat_mul h3 (harmonic_three_prime_dvd hp hp7)
  have hm4 := pDvdRat_mul h4 (harmonic_four_dvd hp hp7)
  have hs := pDvdRat_add (pDvdRat_add (prime_sequence_expansion hp) hm3) hm4
  have hs' : pDvdRat p 5 ((sequence p-sequence 1:ℤ):ℚ) := by
    have h1 : sequence 1=1 := by norm_num [sequence]
    rw [Int.cast_sub,h1,Int.cast_one]
    convert hs using 1 <;> ring
  exact int_dvd_of_pDvdRat hs'

end A361712

end

section

namespace A361712
open Finset

lemma last_term_identity {p h a:ℕ} (hp:0<p) (ha:1≤a) (hap:a<p) :
    term (p^(h+1)) (a*p^h)=
      ((p:ℚ)^3*((a:ℚ)^3)⁻¹+(p:ℚ)^4*((a:ℚ)^4)⁻¹)*
        (productKernel (p^(h+1)) (a*p^h))^2 := by
  have hk : 1≤a*p^h := Nat.mul_pos ha (pow_pos hp _)
  have hkn : a*p^h<p^(h+1) := by
    rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_right hap (pow_pos hp _)
  rw [term_product _ _ (pow_pos hp _) hk hkn,pow_succ']
  have hp0 : (p:ℚ)≠0 := by positivity
  have ha0 : (a:ℚ)≠0 := by positivity
  push_cast
  field_simp
  ring

lemma last_term_approx {p h a:ℕ} (hp:p.Prime) (ha:1≤a) (hap:a<p) :
    pDvdRat p 4 (term (p^(h+1)) (a*p^h)-(p:ℚ)^3*((a:ℚ)^3)⁻¹) := by
  have hac : Nat.Coprime p a := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.le_of_dvd (by omega : 0<a) hd
    omega)
  have h3 : pDvdRat p 3 ((p:ℚ)^3*((a:ℚ)^3)⁻¹) := by
    refine ⟨1,a^3,pow_pos ha _,hac.pow_right 3,?_⟩
    simp [div_eq_mul_inv]
  have h4 : pDvdRat p 4 ((p:ℚ)^4*((a:ℚ)^4)⁻¹) := by
    refine ⟨1,a^4,pow_pos ha _,hac.pow_right 4,?_⟩
    simp [div_eq_mul_inv]
  have hcoef := pDvdRat_add h3 (pDvdRat_mono (by omega : 3≤4) h4)
  have hk : a*p^h≤p^(h+1) := by
    rw [pow_succ']; exact Nat.mul_le_mul_right _ hap.le
  have hW := power_kernel_square_sub_one hp (by omega : 1≤h+1) hk
  have he := pDvdRat_mono (by omega : 4≤3+2) (pDvdRat_mul hcoef hW)
  rw [last_term_identity hp.pos ha hap]
  convert pDvdRat_add he h4 using 1 <;> ring

lemma divisible_term_linear {p r l:ℕ} (hp:p.Prime) (hr:2≤r)
    (hl:1≤l) (hlm:l<p^(r-1)) :
    pDvdRat p (3*r+3)
      (term (p^r) (p*l)-term (p^(r-1)) l+
        2*(((p^r:ℕ):ℚ)^2)*term (p^(r-1)) l*harmonic p (p*l) 2) := by
  have heq : p*p^(r-1)=p^r := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1≤r)]
  have hid := term_split_multiple hp.pos (pow_pos hp.pos _) hl hlm
  rw [heq] at hid
  have hv := power_term_valuation hp (by omega : 1≤r-1) hl hlm
  have hs := valuation_lt_power hp hl hlm
  have hv3 := pDvdRat_mono (by omega : 3≤3*(r-1-padicValNat p l)) hv
  have he := pDvdRat_mul hv3 (unit_kernel_square_linear (b:=r) (k:=p*l) hp)
  have he' := pDvdRat_mono (by omega : 3*r+3≤3+4*r) he
  rw [hid]
  convert he' using 1 <;> ring

end A361712

end

section

namespace A361712
open Finset
noncomputable def correction (p r l:ℕ):ℚ :=
  2*(((p^r:ℕ):ℚ)^2)*term (p^(r-1)) l*harmonic p (p*l) 2

lemma harmonic_index_dvd {p l:ℕ} (hp:p.Prime) (hp5:5≤p) :
    pDvdRat p (padicValNat p l+1) (harmonic p (p*l) 2) := by
  obtain ⟨a,ha⟩ := pow_padicValNat_dvd (p:=p) (n:=l)
  have he : p*l=a*p^(padicValNat p l+1) := by
    conv_lhs => rw [ha]
    rw [pow_succ]
    ring
  rw [he]
  exact harmonic_multiple_square_dvd hp hp5 (by omega)

lemma correction_nonlast {p r l:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:2≤r)
    (hl:1≤l) (hlm:l<p^(r-1)) (hnot:¬p^(r-2)∣l) :
    pDvdRat p (3*r+3) (correction p r l) := by
  have hs : padicValNat p l<r-2 := by
    by_contra hn
    exact hnot ((pow_dvd_pow p (by omega : r-2≤padicValNat p l)).trans
      (pow_padicValNat_dvd (p:=p) (n:=l)))
  have hN : pDvdRat p (2*r) (2*(((p^r:ℕ):ℚ)^2)) := by
    refine ⟨2,1,by omega,Nat.coprime_one_right p,?_⟩
    push_cast
    rw [←pow_mul]
    rw [Nat.mul_comm]
    ring
  have he := pDvdRat_mul (pDvdRat_mul hN
    (power_term_valuation hp (by omega : 1≤r-1) hl hlm))
    (harmonic_index_dvd (l:=l) hp hp5)
  exact pDvdRat_mono (by omega) he

lemma correction_last {p h a:ℕ} (hp:p.Prime) (hp5:5≤p) (ha:1≤a) (hap:a<p) :
    pDvdRat p (3*(h+2)+3) (correction p (h+2) (a*p^h)-
      2*(p:ℚ)^(3*(h+2)+1)*harmonic p p 2*((a:ℚ)^2)⁻¹) := by
  have hindex : p*(a*p^h)=a*p^(h+1) := by rw [pow_succ]; ring
  have hh := harmonic_multiple_square_dvd (a:=a) hp hp5 (by omega : 1≤h+1)
  have hlift := harmonic_square_lift_multiple (a:=a) hp hp5 (by omega : 1≤h+1)
  simp only [Nat.add_sub_cancel] at hlift
  have hN : pDvdRat p (2*(h+2)) (2*(((p^(h+2):ℕ):ℚ)^2)) := by
    refine ⟨2,1,by omega,Nat.coprime_one_right p,?_⟩
    push_cast
    rw [←pow_mul]
    rw [Nat.mul_comm]
    ring
  have hterm := last_term_approx (h:=h) hp ha hap
  have hac : Nat.Coprime p a := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.le_of_dvd (by omega : 0<a) hd
    omega)
  have h3 : pDvdRat p 3 ((p:ℚ)^3*((a:ℚ)^3)⁻¹) := by
    refine ⟨1,a^3,pow_pos ha _,hac.pow_right 3,?_⟩
    simp [div_eq_mul_inv]
  have he1 := pDvdRat_mul (pDvdRat_mul hN hterm) hh
  have he2 := pDvdRat_mul (pDvdRat_mul hN h3) hlift
  have he1' := pDvdRat_mono (by omega : 3*(h+2)+3≤2*(h+2)+4+(h+1)) he1
  have he2' := pDvdRat_mono (by omega : 3*(h+2)+3≤2*(h+2)+3+(h+1+1)) he2
  unfold correction
  rw [hindex]
  simp only [show h+2-1=h+1 by omega]
  convert pDvdRat_add he1' he2' using 1
  have ha0 : (a:ℚ)≠0 := by positivity
  push_cast
  field_simp
  ring

end A361712

end

section

namespace A361712
open Finset
lemma sum_multiples (d m:ℕ) (hd:0<d) (f:ℕ→ℚ) :
    (∑j∈(Ico 1 (d*m)).filter (fun j=>d∣j),f j)=∑a∈Ico 1 m,f (d*a) := by
  symm
  apply sum_bij (fun a _=>d*a)
  · intro a ha
    obtain ⟨ha0,ham⟩ := mem_Ico.mp ha
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hd ha0,
      Nat.mul_lt_mul_of_pos_left ham hd⟩,dvd_mul_right d a⟩
  · intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro j hj
    obtain ⟨hjI,hjd⟩ := mem_filter.mp hj
    obtain ⟨a,rfl⟩ := hjd
    have ha0 : 1≤a := by
      by_contra hn
      have hz:a=0 := by omega
      have := (mem_Ico.mp hjI).1
      simp [hz] at this
    exact ⟨a,mem_Ico.mpr ⟨ha0,Nat.lt_of_mul_lt_mul_left (mem_Ico.mp hjI).2⟩,rfl⟩
  · intro a ha
    rfl

lemma prime_unit_range {p:ℕ} : unitRange p p=Ico 1 p := by
  apply filter_eq_self.mpr
  intro k hk hd
  have := Nat.le_of_dvd (by have := (mem_Ico.mp hk).1; omega : 0<k) hd
  have := (mem_Ico.mp hk).2
  omega

end A361712

end

section

namespace A361712
open Finset

lemma correction_sum (p h:ℕ) (hp:p.Prime) (hp5:5≤p) :
    pDvdRat p (3*(h+2)+3) (∑l∈Ico 1 (p^(h+1)),correction p (h+2) l) := by
  have hnot := pDvdRat_sum (s:=(Ico 1 (p^(h+1))).filter (fun l=>¬p^h∣l))
    (fun l hl=>correction_nonlast hp hp5 (by omega : 2≤h+2)
      (mem_Ico.mp (mem_filter.mp hl).1).1
      (by simpa only [show h+2-1=h+1 by omega] using (mem_Ico.mp (mem_filter.mp hl).1).2)
      (by simpa only [Nat.add_sub_cancel] using (mem_filter.mp hl).2))
  have herr := pDvdRat_sum (s:=Ico 1 p) (fun a ha=>
    correction_last (h:=h) hp hp5 (mem_Ico.mp ha).1 (mem_Ico.mp ha).2)
  simp only [sum_sub_distrib,←mul_sum] at herr
  have hH : (∑a∈Ico 1 p,((a:ℚ)^2)⁻¹)=harmonic p p 2 := by
    unfold harmonic
    rw [prime_unit_range]
  rw [hH] at herr
  have hcoeff : pDvdRat p (3*(h+2)+1) (2*(p:ℚ)^(3*(h+2)+1)) :=
    ⟨2,1,by omega,Nat.coprime_one_right p,by push_cast; ring⟩
  have hH2 := pDvdRat_pow (harmonic_two_dvd hp hp5 (by omega : 1≤1)) 2
  simp only [pow_one] at hH2
  have hlead : pDvdRat p (3*(h+2)+3)
      (2*(p:ℚ)^(3*(h+2)+1)*harmonic p p 2*harmonic p p 2) := by
    convert pDvdRat_mul hcoeff hH2 using 1 <;> ring
  have htail : pDvdRat p (3*(h+2)+3)
      (∑a∈Ico 1 p,correction p (h+2) (p^h*a)) := by
    have he := pDvdRat_add herr hlead
    simp_rw [Nat.mul_comm (p^h)]
    convert he using 1 <;> ring
  have hmult := sum_multiples (p^h) p (pow_pos hp.pos _) (correction p (h+2))
  rw [←pow_succ] at hmult
  rw [←hmult] at htail
  have he := pDvdRat_add htail hnot
  rw [sum_filter_add_sum_filter_not] at he
  exact he

lemma divisible_sum (p r:ℕ) (hp:p.Prime) (hp5:5≤p) (hr:2≤r) :
    pDvdRat p (3*r+3) (∑l∈Ico 1 (p^(r-1)),
      (term (p^r) (p*l)-term (p^(r-1)) l)) := by
  have he := pDvdRat_sum (s:=Ico 1 (p^(r-1))) (fun l hl=>
    divisible_term_linear hp hr (mem_Ico.mp hl).1 (mem_Ico.mp hl).2)
  have hc := correction_sum p (r-2) hp hp5
  simp only [Nat.sub_add_cancel hr,show r-2+1=r-1 by omega] at hc
  simp only [sum_add_distrib] at he
  convert pDvdRat_sub he hc using 1 <;> unfold correction <;> ring

lemma sequence_positive (n:ℕ) (hn:1≤n) :
    (sequence n:ℚ)=1+∑k∈Ico 1 n,term n k := by
  rw [sequence_rat,←sum_range_add_sum_Ico (fun k=>term n k) hn]
  simp [term]

lemma sequence_power_split (p r:ℕ) (hp:p.Prime) (hr:1≤r) :
    ((sequence (p^r)-sequence (p^(r-1)):ℤ):ℚ)=
      (∑k∈unitRange p (p^r),term (p^r) k)+
      ∑l∈Ico 1 (p^(r-1)),(term (p^r) (p*l)-term (p^(r-1)) l) := by
  have heq : p*p^(r-1)=p^r := by rw [←pow_succ',Nat.sub_add_cancel hr]
  have hs := sum_filter_add_sum_filter_not (Ico 1 (p^r)) (fun j=>p∣j) (term (p^r))
  have hm := sum_multiples p (p^(r-1)) hp.pos (term (p^r))
  rw [heq] at hm
  rw [hm] at hs
  change (∑l∈Ico 1 (p^(r-1)),term (p^r) (p*l))+
    (∑k∈unitRange p (p^r),term (p^r) k)=∑k∈Ico 1 (p^r),term (p^r) k at hs
  rw [Int.cast_sub,sequence_positive _ (pow_pos hp.pos _),
    sequence_positive _ (pow_pos hp.pos _),←hs,sum_sub_distrib]
  ring

 theorem tower_congruence (p r:ℕ) (hp:p.Prime) (hp5:5≤p) (hr:2≤r) :
    (p:ℤ)^(3*r+3) ∣ sequence (p^r)-sequence (p^(r-1)) := by
  apply int_dvd_of_pDvdRat
  rw [sequence_power_split p r hp (by omega)]
  exact pDvdRat_add (unit_sum_divisible hp hp5 hr) (divisible_sum p r hp hp5 hr)

end A361712

end
theorem OMA.solution : type_of% @OMA.S_oeis_a361712.main := by
  exact ⟨fun p hp hp7 => A361712.prime_congruence hp hp7,
    fun p r hp hp5 hr => A361712.tower_congruence p r hp hp5 hr⟩
