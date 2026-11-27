import FormalConjectures.OEIS.«212844»
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.Multiplicity

/-! Remainders of two to the power n+2. Prime extensions, sparse
exceptions to the prime-part construction, and a conditional descent.
Credit: @marcusbuffett. -/

namespace OMA.R_OeisA212844_conjecture_R1

open OeisA212844

private theorem pow_period {d x y : ℕ} (hd : Odd d)
    (hxy : x ≡ y [MOD d.totient]) : 2^x ≡ 2^y [MOD d] := by
  by_cases h : 1 < d
  · change 2^x % d = 2^y % d
    rw [Nat.pow_totient_mod h hd.coprime_two_left, Nat.pow_totient_mod (k := y) h hd.coprime_two_left]
    exact congrArg (fun t : ℕ => 2^t % d) hxy
  · obtain rfl : d = 1 := by obtain ⟨k,hk⟩ := hd; omega
    exact Nat.modEq_one

private theorem pow_zero_mod {a x : ℕ} (h : a ≤ x) :
    2^x ≡ 0 [MOD 2^a] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 h)

private theorem fermat_exponent (C p : ℕ) (hp : p.Prime) :
    2^(C*p+2) ≡ 2^(C+2) [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  push_cast
  rw [pow_add, pow_add, Nat.mul_comm C p, pow_mul, ZMod.pow_card]

/-- Arbitrarily large prime extensions of any positive cofactor give its unreduced power. -/
theorem prime_extensions (C B : ℕ) (hC : 0 < C) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧ a (C*p) = 2^(C+2) := by
  obtain ⟨s,d,hd,hsd⟩ := Nat.exists_eq_two_pow_mul_odd hC.ne'
  have hdpos : 0 < d := by obtain ⟨k,hk⟩ := hd; omega
  obtain ⟨p,hp,hbig,hper⟩ := Nat.exists_prime_gt_modEq_one
    (B+C+2^(C+2)) (Nat.totient_pos.mpr hdpos).ne'
  have hsum : B+C ≤ B+C+2^(C+2) := Nat.le_add_right _ _
  have hCp : C < p := (le_trans (Nat.le_add_left ..) hsum).trans_lt hbig
  have hle : s ≤ C := by
    have := s.lt_two_pow_self
    have := Nat.le_mul_of_pos_right (2^s) hdpos
    omega
  have hle' : C ≤ C*p := Nat.le_mul_of_pos_right C hp.pos
  refine ⟨p,hp,((Nat.le_add_right ..).trans hsum).trans_lt hbig, Nat.mod_eq_of_modEq ?_ ?_⟩
  · apply (Nat.modEq_and_modEq_iff_modEq_mul
      (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hC hCp)).symm).mp
    refine ⟨?_,fermat_exponent C p hp⟩
    conv => arg 1; rw [hsd]
    apply (Nat.modEq_and_modEq_iff_modEq_mul (hd.coprime_two_left.pow_left s)).mp
    refine ⟨(pow_zero_mod (by omega)).trans (pow_zero_mod (by omega)).symm, ?_⟩
    apply pow_period hd
    simpa using (hper.mul_left C).add_right 2
  · have := Nat.le_mul_of_pos_left p hC
    omega

theorem powers_of_two (e : ℕ) : ∃ n : ℕ, 1 ≤ n ∧ a n = 2^e := by
  match e with
  | 0 => exact ⟨7,by decide,by decide⟩
  | 1 => exact ⟨3,by decide,by decide⟩
  | 2 => exact ⟨6,by decide,by decide⟩
  | e+3 =>
    obtain ⟨p,hp,_,he⟩ := prime_extensions (e+1) 0 (by omega)
    exact ⟨_,Nat.mul_pos (by omega) hp.pos,he⟩

/-- Exact sufficient residue condition for a witness with odd prime part. -/
theorem prime_part (v h p : ℕ) (hp : p.Prime) (ho : Odd p) (hh : h < p)
    (hres : 2^(2^v+2-v) ≡ h [MOD p]) : a (2^v*p) = 2^v*h := by
  have hv := v.lt_two_pow_self
  have hC : 0 < 2^v := by positivity
  apply Nat.mod_eq_of_modEq _ (Nat.mul_lt_mul_of_pos_left hh hC)
  apply (Nat.modEq_and_modEq_iff_modEq_mul (ho.coprime_two_left.pow_left v)).mp
  refine ⟨?_,(fermat_exponent (2^v) p hp).trans ?_⟩
  · have := Nat.le_mul_of_pos_right (2^v) hp.pos
    exact (pow_zero_mod (by omega)).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)).symm
  · have he : 2^v+2 = v+(2^v+2-v) := by omega
    rw [he,pow_add]
    exact hres.mul_left _

/-- Fixed points of the translated exponential modulo every positive modulus. -/
theorem exponential_fixed_point (c M : ℕ) (hM : 0 < M) (B : ℕ) :
    ∃ b ≥ B, ∃ D > 0, ∀ j : ℕ, b+D*j ≡ 2^(b+D*j)+c [MOD M] := by
  induction M using Nat.strong_induction_on generalizing B with
  | h M ih =>
    by_cases h : M = 1
    · subst M; exact ⟨B,le_rfl,1,by decide,fun _ => Nat.modEq_one⟩
    obtain ⟨s,d,hd,hsd⟩ := Nat.exists_eq_two_pow_mul_odd hM.ne'
    have hdpos : 0 < d := by obtain ⟨k,hk⟩ := hd; omega
    have hdle : d ≤ M := hsd ▸ Nat.le_mul_of_pos_left d (by positivity)
    have hphi : d.totient < M := by
      by_cases hd1 : d = 1
      · simp [hd1]; omega
      · exact (Nat.totient_lt d (by omega)).trans_le hdle
    have hpos := Nat.totient_pos.mpr hdpos
    obtain ⟨x,hx,_,_,hseq⟩ := ih d.totient hphi hpos s
    have hfix : x ≡ 2^x+c [MOD d.totient] := by simpa using hseq 0
    let v := 2^x+c+(B+s)*(M*d.totient)
    have hbase := Nat.le_mul_of_pos_right (B+s) (Nat.mul_pos hM hpos)
    have hlow : B+s ≤ v := hbase.trans (Nat.le_add_left ..)
    have hvB : B ≤ v := (Nat.le_add_right ..).trans hlow
    have hvs : s ≤ v := (Nat.le_add_left ..).trans hlow
    refine ⟨v,hvB,M*d.totient,Nat.mul_pos hM hpos,?_⟩
    intro j
    have hmult (k : ℕ) (hk : k ∣ M*d.totient) : v+(M*d.totient)*j ≡ 2^x+c [MOD k] := by
      apply Nat.ModEq.trans (b := v)
      · exact Nat.add_modEq_left_iff.mpr (hk.trans (dvd_mul_right _ _))
      apply Nat.add_modEq_left_iff.mpr
      exact hk.trans (dvd_mul_left _ _)
    have hvx : v+(M*d.totient)*j ≡ x [MOD d.totient] :=
      (hmult _ (dvd_mul_left _ _)).trans hfix.symm
    have hex : 2^(v+(M*d.totient)*j) ≡ 2^x [MOD M] := by
      conv => arg 1; rw [hsd]
      apply (Nat.modEq_and_modEq_iff_modEq_mul (hd.coprime_two_left.pow_left s)).mp
      exact ⟨(pow_zero_mod (hvs.trans (Nat.le_add_right ..))).trans (pow_zero_mod hx).symm, pow_period hd hvx⟩
    exact (hmult _ (dvd_mul_right _ _)).trans (hex.add_right c).symm

private theorem odd_multiple (H : ℕ) :
    ∃ L : ℕ, Odd L ∧ ∀ h ≤ 2*H+1, Odd h → h ∣ L := by
  induction H with
  | zero =>
    refine ⟨1,by decide,?_⟩
    rintro h hh ⟨k,hk⟩
    obtain rfl : h = 1 := by omega
    exact dvd_refl _
  | succ H ih =>
    obtain ⟨L,hL,hdiv⟩ := ih
    refine ⟨L*(2*(H+1)+1),hL.mul ⟨_,rfl⟩,?_⟩
    intro h hh ho
    by_cases he : h = 2*(H+1)+1
    · subst h; exact dvd_mul_left _ _
    · apply dvd_mul_of_dvd_left (hdiv h ?_ ho)
      obtain ⟨k,hk⟩ := ho
      omega

private theorem exp_growth (v : ℕ) : 2*v ≤ 2^v+2 := by
  induction v with
  | zero => decide
  | succ v ih =>
    rw [pow_succ]
    have := v.lt_two_pow_self
    cases v with
    | zero => decide
    | succ v => omega

/-- If an even number is 2 modulo the square of an odd common multiple, then
subtracting a small odd number forces a prime factor outside that multiple. -/
private theorem large_factor {H L Y h : ℕ} (hL : Odd L)
    (hdiv : ∀ k ≤ H, Odd k → k ∣ L)
    (hy : Y ≡ 2 [MOD L^2]) (hbig : 3*L^2+2 ≤ Y)
    (he : Even Y) (hh : h ≤ H) (ho : Odd h) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ H < p ∧ Y ≡ h [MOD p] := by
  have hLpos : 0 < L := by obtain ⟨k,hk⟩ := hL; omega
  have hY : 2 ≤ Y := (Nat.le_add_left ..).trans hbig
  obtain ⟨z,hz⟩ := (Nat.modEq_iff_dvd' hY).mp hy.symm
  have hYz : Y = L^2*z+2 := by omega
  have hz3 : 3 ≤ z := by
    by_contra! hl
    have := Nat.mul_le_mul_left (L^2) (show z ≤ 2 by omega)
    nlinarith [sq_pos_of_pos (a := L) hLpos]
  have hfin (u : ℕ) (hu : 1 < u) (huY : u ∣ Y-h) (hhy : h ≤ Y)
      (hcop : ∀ p : ℕ, p.Prime → p ∣ L → p ∣ u → False) :
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ H < p ∧ Y ≡ h [MOD p] := by
    obtain ⟨p,hp,hpu⟩ := Nat.exists_prime_and_dvd (n := u) (by omega)
    have hpd := hpu.trans huY
    have hoy : Odd (Y-h) := by obtain ⟨i,hi⟩ := he; obtain ⟨j,hj⟩ := ho; exact ⟨i-j-1,by omega⟩
    have hop := hoy.of_dvd_nat hpd
    refine ⟨p,hp,hop,?_,((Nat.modEq_iff_dvd' hhy).mpr hpd).symm⟩
    by_contra! hl
    exact hcop _ hp (hdiv _ hl hop) hpu
  by_cases h1 : h = 1
  · subst h
    apply hfin (Y-1) (by have : 0 < L^2 := pow_pos hLpos _; omega) (dvd_refl _) (by omega)
    intro p hp hpL hpY
    have hd : p ∣ L^2*z := hpL.trans (by exact ⟨L*z,by ring⟩)
    have hu : Y-1 = L^2*z+1 := by omega
    rw [hu] at hpY
    exact hp.not_dvd_one ((Nat.dvd_add_right hd).mp hpY)
  · have hh3 : 3 ≤ h := by obtain ⟨k,hk⟩ := ho; omega
    let g := h-2
    have hgpos : 0 < g := by dsimp [g]; omega
    have hg : g+2 = h := by dsimp [g]; omega
    have hgo : Odd g := by obtain ⟨k,hk⟩ := ho; exact ⟨k-1,by omega⟩
    obtain ⟨t,ht⟩ := hdiv g (by omega) hgo
    have htpos : 0 < t := by by_contra! heq; simp [show t=0 by omega] at ht; omega
    let u := L*t*z-1
    have hprod : 3 ≤ L*t*z :=
      hz3.trans (Nat.le_mul_of_pos_left z (Nat.mul_pos hLpos htpos))
    have hu : u+1 = L*t*z := by dsimp [u]; omega
    have hgu : g*(u+1) = L^2*z := by rw [hu]; rw [ht]; ring
    rw [mul_add,mul_one] at hgu
    have hdiff : Y-h = g*u := by omega
    apply hfin u (by omega) (hdiff ▸ dvd_mul_left _ _) (by omega)
    intro p hp hpL hpu
    have hd : p ∣ u+1 := hu ▸ (hpL.trans (by exact ⟨t*z,by ring⟩))
    exact hp.not_dvd_one ((Nat.dvd_add_right hpu).mp hd)

/-- Every finite family of odd parts occurs simultaneously along an arithmetic
progression of exponents, with witnesses whose odd part is a prime exceeding H. -/
theorem simultaneous_dilations (H B : ℕ) :
    ∃ b ≥ B, ∃ D > 0, ∀ j : ℕ, ∀ h ≤ H, Odd h →
      ∃ p : ℕ, p.Prime ∧ H < p ∧ a (2^(b+D*j)*p) = 2^(b+D*j)*h := by
  obtain ⟨L,hL,hdiv⟩ := odd_multiple H
  have hLpos : 0 < L := by obtain ⟨k,hk⟩ := hL; omega
  obtain ⟨b,hb,D,hD,hfixed⟩ := exponential_fixed_point 1 (L^2).totient
    (Nat.totient_pos.mpr (pow_pos hLpos _)) (B+3*L^2+2)
  refine ⟨b,by omega,D,hD,?_⟩
  intro j h hh ho
  let v := b+D*j
  let T := 2^v+2-v
  have hTv : T+v = 2^v+2 := Nat.sub_add_cancel (by have := v.lt_two_pow_self; omega)
  have hT : v ≤ T := by have := exp_growth v; dsimp [T]; omega
  have hcon : T ≡ 1 [MOD (L^2).totient] := by
    apply Nat.ModEq.add_right_cancel' v
    rw [hTv]
    have he := (hfixed j).symm.add_left 1
    convert he using 1
    dsimp [v]
    omega
  have hy : 2^T ≡ 2 [MOD L^2] := by simpa using pow_period (hL.pow (n := 2)) hcon
  have hbound : 3*L^2+2 ≤ 2^T := by
    have hx : b ≤ v := Nat.le_add_right .. 
    have := T.lt_two_pow_self
    omega
  have hTe : Even (2^T) := by
    have hx : b ≤ v := Nat.le_add_right ..
    exact (even_two.pow_of_ne_zero (by omega))
  obtain ⟨p,hp,hop,hlarge,hres⟩ := large_factor hL
    (fun k hk ho => hdiv k (by omega) ho) hy hbound hTe hh ho
  exact ⟨p,hp,hlarge,prime_part v h p hp hop (hh.trans_lt hlarge) hres⟩

private theorem val_bound (p m : ℕ) : padicValNat p m ≤ m :=
  (padicValNat_le_nat_log _).trans (Nat.log_le_self ..)

/-- Lifting the exponent makes two high prime-power collisions at nearby
indices impossible when the indices agree modulo p-1. -/
private theorem collision_bound (p E v w : ℕ) (hp : p.Prime) (ho : Odd p)
    (hv : 2 ≤ v) (hvw : v < w) (hr : v ≡ w [MOD p-1])
    (hY : 2^(2^v+2-v) ≡ 2^(2^w+2-w) [MOD p^E]) :
    E ≤ 2^p + (w-v) := by
  have : Fact p.Prime := ⟨hp⟩
  let d := w-v
  have hd : 0 < d := Nat.sub_pos_of_lt hvw
  have hwd : v+d = w := by dsimp [d]; omega
  let A := 2^(p-1)
  have hp1 : 0 < p-1 := by have := hp.one_lt; omega
  have hA : 1 < A := Nat.one_lt_pow hp1.ne' (by decide)
  have hcop : p.Coprime 2 := ho.coprime_two_right
  have hpA : ¬ p ∣ A := hp.coprime_iff_not_dvd.mp (hcop.pow_right _)
  have hFA : p ∣ A-1 := by
    apply Nat.ModEq.dvd'
    exact (by simpa [A,Nat.totient_prime hp] using
      (Nat.ModEq.pow_totient hcop.symm).symm : 1 ≡ A [MOD p])
  have hc : 1 ≤ padicValNat p (A-1) :=
    one_le_padicValNat_of_dvd (by omega) hFA
  obtain ⟨r,hrd⟩ := hr.dvd'
  have hdr : d = (p-1)*r := hrd
  have hr0 : r ≠ 0 := by intro he; simp [he] at hdr; omega
  have hno : ¬p ∣ p-1 := Nat.not_dvd_of_pos_of_lt hp1 (by omega)
  have hval : padicValNat p d = padicValNat p r := by
    rw [hdr,padicValNat.mul hp1.ne' hr0,padicValNat.eq_zero_of_not_dvd hno,zero_add]
  have hinner : p^(padicValNat p d+1) ∣ 2^d-1 := by
    have he : 2^d = A^r := by rw [hdr,pow_mul]
    have hg : 1 < 2^d := Nat.one_lt_pow hd.ne' (by decide)
    apply (padicValNat_dvd_iff_le (by omega : 2^d-1 ≠ 0)).mpr
    rw [he]
    have h := padicValNat.pow_sub_pow ho hA hFA hpA hr0
    simp only [one_pow] at h
    omega
  let x := 2^v+2-v
  let y := 2^w+2-w
  have hx : x+v = 2^v+2 := Nat.sub_add_cancel (by have := v.lt_two_pow_self; omega)
  have hy : y+w = 2^w+2 := Nat.sub_add_cancel (by have := w.lt_two_pow_self; omega)
  have hdiff : 2^w = 2^v*(2^d-1)+2^v := by
    rw [← hwd,pow_add,← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_two_pow)]
  have hdle : d ≤ 2^d-1 := by have := d.lt_two_pow_self; omega
  have hdouble := Nat.mul_le_mul_left (2^v) hdle
  have hvpow := v.lt_two_pow_self
  have hlt : x < y := by nlinarith [Nat.mul_le_mul_right d hvpow.le]
  let t := y-x
  have ht : 0 < t := Nat.sub_pos_of_lt hlt
  have htd : t+d = 2^v*(2^d-1) := by dsimp [t]; omega
  have houter : p^E ∣ A^t-1 := by
    have he : (2^t : ℕ) ≡ 1 [MOD p^E] := by
      apply Nat.ModEq.cancel_left_of_coprime ((hcop.pow_left E).pow_right x)
      rw [mul_one,← pow_add, Nat.add_sub_of_le hlt.le]
      exact hY.symm
    have hf := he.pow (p-1)
    have hf' : A^t ≡ 1 [MOD p^E] := by
      simpa only [A,← pow_mul, Nat.mul_comm t (p-1),one_pow] using hf
    exact hf'.symm.dvd'
  have hAt : 1 < A^t := Nat.one_lt_pow ht.ne' hA
  have hvE := (padicValNat_dvd_iff_le (by omega : A^t-1 ≠ 0)).mp houter
  have hLTE := padicValNat.pow_sub_pow ho hA hFA hpA ht.ne'
  simp only [one_pow] at hLTE
  have hsmall : padicValNat p t ≤ padicValNat p d := by
    by_contra! hl
    have htdvd := (padicValNat_dvd_iff_le ht.ne').mpr (show padicValNat p d+1 ≤ padicValNat p t by omega)
    have hsum : p^(padicValNat p d+1) ∣ t+d := htd ▸ dvd_mul_of_dvd_right hinner _
    exact pow_succ_padicValNat_not_dvd hd.ne' ((Nat.dvd_add_right htdvd).mp hsum)
  have hAp : A ≤ 2^p := Nat.pow_le_pow_right (by decide) (Nat.sub_le p 1)
  have hvalA := val_bound p (A-1)
  have hvald := val_bound p d
  change E ≤ 2^p+d
  omega

/-- For each fixed odd part h, every sufficiently late interval of any prescribed
length contains at most (h+1)^2 exponents omitted by the prime-part construction.
In particular the exceptional exponents have upper Banach density zero. -/
theorem sparse_exceptions (h W : ℕ) (ho : Odd h) :
    ∃ B, ∀ b ≥ B, ∀ S : Finset ℕ, (∀ v ∈ S, b ≤ v ∧ v < b+W ∧
      ¬ ∃ p : ℕ, p.Prime ∧ Odd p ∧ h < p ∧ a (2^v*p) = 2^v*h) →
      S.card ≤ (h+1)^2 := by
  classical
  let E := 2^h+W+1
  let B := h.factorial^E+h+2
  refine ⟨B,?_⟩
  intro b hb S hS
  have color (v : ℕ) (hv : v ∈ S) :
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≤ h ∧ 2^(2^v+2-v) ≡ h [MOD p^E] := by
    obtain ⟨hvlo,_,hmiss⟩ := hS v hv
    let T := 2^v+2-v
    let N := 2^T-h
    have hTv : v ≤ T := by have := exp_growth v; dsimp [T]; omega
    have hgrowth := T.lt_two_pow_self
    have hcut : h.factorial^E < N := by dsimp [N]; dsimp [B] at hb; omega
    have hhY : h ≤ 2^T := by dsimp [B] at hb; omega
    have hTpos : T ≠ 0 := by dsimp [B] at hb; omega
    have hYN : N+h = 2^T := Nat.sub_add_cancel hhY
    have hNo : Odd N := by
      obtain ⟨i,hi⟩ := (even_two.pow_of_ne_zero hTpos : Even (2^T : ℕ))
      obtain ⟨j,hj⟩ := ho
      exact ⟨i-j-1,by omega⟩
    have hfac (p : ℕ) (hp : p.Prime) (hpd : p ∣ N) : p ≤ h := by
      by_contra! hl
      have hop := hNo.of_dvd_nat hpd
      have hr := ((Nat.modEq_iff_dvd' hhY).mpr hpd).symm
      exact hmiss ⟨p,hp,hop,hl,prime_part v h p hp hop hl hr⟩
    by_contra! hn
    have hN : N ∣ h.factorial^E := by
      apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
      intro p k hp hpk
      by_cases hk : k = 0
      · simp [hk]
      have hpd := (dvd_pow_self p hk).trans hpk
      have hle := hfac p hp hpd
      have hnp : ¬p^E ∣ N := by
        intro hpow
        exact hn p hp (hNo.of_dvd_nat hpd) hle ((Nat.modEq_iff_dvd' hhY).mpr hpow).symm
      have hkE : k ≤ E := by
        by_contra! hl
        exact hnp ((pow_dvd_pow p hl.le).trans hpk)
      exact (pow_dvd_pow p hkE).trans (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hle) E)
    exact (Nat.le_of_dvd (pow_pos h.factorial_pos E) hN).not_gt hcut
  let prime (v : ℕ) := if hv : v ∈ S then (color v hv).choose else 0
  have spec (v : ℕ) (hv : v ∈ S) : (prime v).Prime ∧ Odd (prime v) ∧ prime v ≤ h ∧
      2^(2^v+2-v) ≡ h [MOD (prime v)^E] := by simpa [prime,hv] using (color v hv).choose_spec
  let label (v : ℕ) := (prime v, v % (prime v-1))
  let box := Finset.range (h+1) ×ˢ Finset.range (h+1)
  have hin (v : ℕ) (hv : v ∈ S) : label v ∈ box := by
    obtain ⟨hp,_,hle,_⟩ := spec v hv
    have := Nat.mod_lt v (show 0 < prime v-1 by have := hp.one_lt; omega)
    change (prime v,v % (prime v-1)) ∈ Finset.range (h+1) ×ˢ Finset.range (h+1)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
  have sep (v w : ℕ) (hv : v ∈ S) (hw : w ∈ S) (hlt : v < w) (heq : label v = label w) : False := by
    have hprime : prime v = prime w := congrArg Prod.fst heq
    have hrem : v % (prime v-1) = w % (prime w-1) := congrArg Prod.snd heq
    rw [← hprime] at hrem
    obtain ⟨hp,hop,hle,hvp⟩ := spec v hv
    have hwp := (spec w hw).2.2.2
    rw [← hprime] at hwp
    obtain ⟨hvlo,_,_⟩ := hS v hv
    obtain ⟨_,hwhi,_⟩ := hS w hw
    have hlower : 2 ≤ v := by dsimp [B] at hb; omega
    have hh := collision_bound (prime v) E v w hp hop hlower hlt hrem (hvp.trans hwp.symm)
    have hpow : 2^(prime v) ≤ 2^h := Nat.pow_le_pow_right (by decide) hle
    dsimp [E] at hh
    omega
  have hinj : (S : Set ℕ).InjOn label := by
    intro v hv w hw he
    rcases lt_trichotomy v w with hlt | he' | hgt
    · exact (sep _ _ hv hw hlt he).elim
    · exact he'
    · exact (sep _ _ hw hv hgt he.symm).elim
  simpa [box,pow_two] using Finset.card_le_card_of_injOn label (fun _ hv => hin _ hv) hinj

/-- Arbitrarily late consecutive blocks of any requested length consist entirely
of witnessed exponents, for each prescribed odd part. -/
theorem exponent_blocks (h L V : ℕ) (ho : Odd h) :
    ∃ b ≥ V, ∀ t ≤ L, ∃ n : ℕ, 1 ≤ n ∧ a n = 2^(b+t)*h := by
  classical
  let K := (h+1)^2
  let W := (K+1)*(L+1)
  obtain ⟨B,hbound⟩ := sparse_exceptions h W ho
  let b := max B V
  by_contra! hno
  have hbad (i : ℕ) : ∃ t ≤ L, ¬ ∃ n : ℕ, 1 ≤ n ∧ a n = 2^(b+i*(L+1)+t)*h := by
    have hb : V ≤ b+i*(L+1) := (le_max_right ..).trans (Nat.le_add_right ..)
    obtain ⟨t,ht,hmiss⟩ := hno _ hb
    exact ⟨t,ht,by simpa only [not_exists,not_and] using hmiss⟩
  choose t ht hmiss using hbad
  let idx (i : ℕ) := b+i*(L+1)+t i
  let S := (Finset.range (K+1)).image idx
  have mono (i j : ℕ) (hij : i < j) : idx i < idx j := by
    have hi := ht i
    have hij' := Nat.mul_le_mul_right (L+1) (show i+1 ≤ j from hij)
    rw [Nat.add_mul,one_mul] at hij'
    dsimp [idx]
    omega
  have hcard : S.card = K+1 := by
    rw [Finset.card_image_of_injective _ (show Function.Injective idx from (show StrictMono idx from fun _ _ hij => mono _ _ hij).injective),Finset.card_range]
  have hab := hbound b (le_max_left ..) S (by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hir := Finset.mem_range.mp hi
    have ht' := ht i
    have he := Nat.mul_le_mul_right (L+1) (show i+1 ≤ K+1 by omega)
    rw [Nat.add_mul,one_mul] at he
    refine ⟨by dsimp [idx]; omega,by dsimp [idx,W]; omega,?_⟩
    rintro ⟨p,hp,_,_,hw⟩
    exact hmiss i ⟨_,Nat.mul_pos (by positivity) hp.pos,hw⟩)
  omega
/- Finite witnesses, checked by binary modular exponentiation. A zero in the
table marks an index for which no witness from the search is used. -/
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem finite_witnesses (k : ℕ) (hk : k ≤ 300) (ha : k ∉ [69, 91, 114, 141, 157, 175, 195]) :
    ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  let f : ℕ → ℕ → ℕ → ℕ := Nat.rec (fun n _ => 1 % n) (fun _ prev n e =>
    if e = 0 then 1 % n else
      let t := prev n (e/2)
      t*t*(if e%2=1 then 2 else 1) % n)
  have sound (l n e : ℕ) (hl : e < 2^l) : f l n e ≡ 2^e [MOD n] := by
    induction l generalizing e with
    | zero =>
      obtain rfl : e = 0 := by simpa using hl
      change 1%n ≡ 2^0 [MOD n]
      simpa only [pow_zero] using (Nat.mod_modEq 1 n)
    | succ l ih =>
      by_cases he : e = 0
      · subst e; simp [f,Nat.mod_modEq]
      · have hh : e/2 < 2^l := by rw [pow_succ] at hl; omega
        have hr := ih (e/2) hh
        change (if e=0 then 1%n else _ % n) ≡ _ [MOD n]
        rw [if_neg he]
        apply (Nat.mod_modEq ..).trans
        change f l n (e/2) * f l n (e/2) * (if e%2=1 then 2 else 1) ≡ 2^e [MOD n]
        by_cases ho : e%2=1
        · have heq : e = (e/2+e/2)+1 := by omega
          conv_rhs => rw [heq,pow_succ,pow_add]
          rw [if_pos ho]
          exact (hr.mul hr).mul_right 2
        · have heq : e = e/2+e/2 := by omega
          conv_rhs => rw [heq,pow_add]
          rw [if_neg ho,mul_one]
          exact hr.mul hr
  let ws : List ℕ := [
    1, 7, 3, 5, 6, 9, 10, 55, 11, 3521, 246, 21,
    52, 89969, 286, 60827, 22, 57481, 1501, 31937, 44, 2977, 49, 27,
    40, 39806401, 110, 16777, 114, 214293, 24823, 247, 33, 259274569, 222, 2739,
    70, 5993, 253217, 1062899, 72, 2007, 215, 85, 140, 4187, 50, 75,
    488, 3649409, 297, 3227, 95, 105, 143, 10571927, 88, 91, 66, 117,
    481, 517, 3082, 65, 68, 473, 130, 188591, 99, 0, 186, 632453,
    77, 1265, 231, 495029, 90, 81, 217, 209, 176, 18039353, 115, 187,
    860, 121, 374, 2137495, 104, 1083, 7186661, 0, 555, 2933, 558, 279,
    232, 155, 667, 8927, 266, 319, 26906, 125, 184, 88957, 190, 151135,
    484, 141523, 1554891, 4981, 144, 133, 0, 303503, 777, 6715, 138, 40727,
    196, 161, 963, 88759, 3252, 162319, 589, 97479487407649637967823280359036415, 145, 312167, 954, 639,
    77996, 8106149, 742, 203, 296, 273, 44297, 741635117, 477, 0, 253, 285,
    697, 6809, 650, 575, 492, 1287, 26603, 169, 578, 16667233, 1007, 26593,
    623, 0, 189, 3901, 312, 9159, 1363, 10745, 2453, 20703461, 198, 171,
    856, 859999, 31262, 6787, 275, 741581, 559, 0, 424, 1417, 425, 357,
    345119, 3210906976896455088019588433, 2937, 385, 287, 207, 230, 295, 1054, 30899, 39467, 749,
    352, 2548285, 927, 0, 228, 611, 1586, 211721, 824, 427337, 1819, 225,
    700, 375143, 3890, 395, 272, 5089809, 5162, 301, 15255, 34765, 462, 957,
    808, 2755, 41566, 2051, 306, 261, 235, 299, 440, 2369, 430, 507,
    925, 448036109, 363, 75012187, 1704, 4169, 506, 13944829, 1930, 407, 605, 243,
    841, 5312543, 437, 110423, 260, 3809, 250, 371, 345, 7223, 338, 840396671,
    9607, 259, 418, 793, 258, 1791, 88931, 7303, 13246, 1757, 335, 1785,
    3007, 14213, 351, 343, 476, 5315881, 29591, 25686329, 375, 670576040567489620325449, 2086, 1773,
    1910, 19754447, 1166, 5371, 732, 847, 1106, 32485, 1034, 148327, 1270, 323,
    2485, 1136591, 244246, 8983, 666, 585, 16237, 144367, 350, 22217, 1037, 3931931,
    4029547]
  have checked : ∀ i : Fin 301, i.val ∉ [69, 91, 114, 141, 157, 175, 195] →
      let n := ws[i.val]!
      1 ≤ n ∧ i.val < n ∧ n+2 < 2^120 ∧ f 120 n (n+2) = i.val := by decide +kernel
  obtain ⟨hn,hkn,hbound,hr⟩ := checked ⟨k,by omega⟩ ha
  have hs := (sound 120 ws[k]! _ hbound).symm
  rw [hr] at hs
  exact ⟨_,hn,Nat.mod_eq_of_modEq hs hkn⟩

private theorem fold_exponent {a m L : ℕ} (hp : a^L ≡ 1 [MOD m]) (e : ℕ) :
    a^e ≡ a^(e%L) [MOD m] := by
  conv_lhs => rw [← Nat.mod_add_div e L,pow_add,pow_mul]
  simpa only [one_pow,mul_one] using (hp.pow (e/L)).mul_left (a^(e%L))

/-- A modular obstruction to a difference of powers supported on two primes.
The first modulus forces a restricted pair of exponents, and the odd modulus
tests membership in the powers of two. -/
private theorem two_prime_obstruction (H P Q A M L : ℕ) (hL : 0 < L)
    (hp2 : P^L ≡ 1 [MOD 2^A]) (hq2 : Q^L ≡ 1 [MOD 2^A])
    (hpM : P^L ≡ 1 [MOD M]) (hqM : Q^L ≡ 1 [MOD M]) (h2M : 2^L ≡ 1 [MOD M])
    (table : ∀ i j : Fin L, (P^i.val*Q^j.val+H) % 2^A = 0 →
      (P^i.val*Q^j.val+H) % M ∉ (List.range L).map (fun t => 2^t % M)) :
    ∀ e ≥ A, ∀ r s : ℕ, 2^e ≠ P^r*Q^s+H := by
  intro e he r s heq
  let i : Fin L := ⟨r%L,Nat.mod_lt _ hL⟩
  let j : Fin L := ⟨s%L,Nat.mod_lt _ hL⟩
  have hmod (m : ℕ) (hP : P^L ≡ 1 [MOD m]) (hQ : Q^L ≡ 1 [MOD m]) :
      2^e ≡ P^i.val*Q^j.val+H [MOD m] := heq ▸ ((fold_exponent hP r).mul (fold_exponent hQ s)).add_right H
  have hzero := (hmod _ hp2 hq2).symm.trans (pow_zero_mod he)
  have hlast := (hmod _ hpM hqM).symm.trans (fold_exponent h2M e)
  apply table i j (by simpa only [Nat.ModEq,Nat.zero_mod] using hzero)
  exact List.mem_map.mpr ⟨e%L,List.mem_range.mpr (Nat.mod_lt _ hL),hlast.symm⟩

private theorem smooth_pair_witness (v h P Q : ℕ) (ho : Odd h)
    (hsm : ∀ p ≤ h, p.Prime → Odd p → ¬p ∣ h → p=P ∨ p=Q)
    (hbound : h < 2^(2^v+2-v))
    (hobs : ∀ r s : ℕ, 2^(2^v+2-v) ≠ P^r*Q^s+h) :
    ∃ n : ℕ, 1 ≤ n ∧ a n = 2^v*h := by
  let T := 2^v+2-v
  let N := 2^T-h
  have hN : 0 < N := Nat.sub_pos_of_lt hbound
  have hsum : N+h = 2^T := Nat.sub_add_cancel hbound.le
  have hT : T ≠ 0 := by dsimp [T]; have := v.lt_two_pow_self; omega
  have hNo : Odd N := by
    obtain ⟨i,hi⟩ := (even_two.pow_of_ne_zero hT : Even (2^T : ℕ))
    obtain ⟨j,hj⟩ := ho
    exact ⟨i-j-1,by omega⟩
  by_contra! hn
  have small (p : ℕ) (hp : p.Prime) (hd : p ∣ N) : p=P ∨ p=Q := by
    have hop := hNo.of_dvd_nat hd
    apply hsm p _ hp hop
    · intro hdh
      have hpow : p ∣ 2^T := hsum ▸ Nat.dvd_add hd hdh
      exact hp.coprime_iff_not_dvd.mp (hop.coprime_two_right.pow_right T) hpow
    · by_contra! hlt
      exact hn _ (Nat.mul_pos (by positivity) hp.pos) (prime_part v h p hp hop hlt
        ((Nat.modEq_iff_dvd' hbound.le).mpr hd).symm)
  have factor (l : List ℕ) (hs : ∀ p ∈ l, p=P ∨ p=Q) : ∃ r s : ℕ, l.prod = P^r*Q^s := by
    induction l with
    | nil => exact ⟨0,0,by simp⟩
    | cons p l ih =>
      obtain ⟨r,s,hrs⟩ := ih fun q hq => hs q (by simp [hq])
      rcases hs p (by simp) with rfl | rfl
      · exact ⟨r+1,s,by rw [List.prod_cons,hrs,pow_succ]; ring⟩
      · exact ⟨r,s+1,by rw [List.prod_cons,hrs,pow_succ]; ring⟩
  obtain ⟨r,s,hrs⟩ := factor N.primeFactorsList fun p hp =>
    small p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  rw [Nat.prod_primeFactorsList hN.ne'] at hrs
  exact hobs r s (by rw [← hrs]; exact hsum.symm)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
/-- Every target with odd part 1, 3, 5, 7, or 9 occurs. -/
theorem small_odd_parts (v h : ℕ) (hh : h ∈ [1,3,5,7,9]) :
    ∃ n : ℕ, 1 ≤ n ∧ a n = 2^v*h := by
  by_cases hv : v < 6
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl <;>
      interval_cases v <;> exact finite_witnesses _ (by decide) (by decide)
  have hT : 6 ≤ 2^v+2-v := by have := exp_growth v; omega
  have hY := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) hT
  norm_num1 at hY
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl|rfl
  · simpa using powers_of_two v
  · apply smooth_pair_witness v 3 1 1 (by decide) (by decide) (by omega)
    exact two_prime_obstruction 3 1 1 6 17 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) _ hT
  · apply smooth_pair_witness v 5 3 1 (by decide) (by decide) (by omega)
    exact two_prime_obstruction 5 3 1 6 17 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) _ hT
  · apply smooth_pair_witness v 7 3 5 (by decide) (by decide) (by omega)
    exact two_prime_obstruction 7 3 5 6 (17*29*113) 112 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) _ hT
  · apply smooth_pair_witness v 9 5 7 (by decide) (by decide) (by omega)
    exact two_prime_obstruction 9 5 7 6 (3*17*29*113) 112 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) _ hT

/-- Novák's divisibility condition produces an odd target four below its index. -/
theorem novak_value (m : ℕ) (hm : 4 < m) (hn : m ∣ 2^m+1) : a m = m-4 := by
  apply Nat.mod_eq_of_modEq _ (by omega)
  apply Nat.ModEq.add_right_cancel' 4
  rw [Nat.sub_add_cancel hm.le,pow_add]
  have hdiv : m ∣ 2^m*2^2+4 := by
    rw [show 2^m*2^2+4 = (2^m+1)*4 by ring]
    exact dvd_mul_of_dvd_left hn _
  exact (Nat.modEq_zero_iff_dvd.mpr hdiv).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m)).symm

/-- The divisor-extension rule for Novák numbers, cf. Alexander Kalmynin,
On Novák numbers, arXiv:1611.00417, Lemma 5. -/
theorem novak_extension (m d : ℕ) (hm : 0 < m) (hn : m ∣ 2^m+1) (hd : d ∣ 2^m+1) :
    m*d ∣ 2^(m*d)+1 := by
  have he : Even (2^m : ℕ) := even_two.pow_of_ne_zero hm.ne'
  have ho := (he.add_one).of_dvd_nat hd
  have hn' : (m : ℤ) ∣ (2:ℤ)^m-(-1) := by
    rw [sub_neg_eq_add]; exact_mod_cast hn
  have hd' : (d : ℤ) ∣ (2:ℤ)^m-(-1) := by
    rw [sub_neg_eq_add]; exact_mod_cast hd
  have hprod := mul_dvd_mul (dvd_geom_sum₂_self hd') hn'
  rw [geom_sum₂_mul,ho.neg_one_pow,sub_neg_eq_add,← pow_mul,mul_comm (d : ℤ)] at hprod
  exact_mod_cast hprod

theorem novak_ray (m d : ℕ) (hm : 0 < m) (hn : m ∣ 2^m+1) (hd : d ∣ 2^m+1) (j : ℕ) :
    m*d^j ∣ 2^(m*d^j)+1 := by
  have ho : Odd d := ((even_two.pow_of_ne_zero hm.ne' : Even (2^m : ℕ)).add_one).of_dvd_nat hd
  have hdpos : 0 < d := by obtain ⟨k,hk⟩ := ho; omega
  induction j with
  | zero => simpa using hn
  | succ j ih =>
    rw [pow_succ,← mul_assoc]
    apply novak_extension _ _ (Nat.mul_pos hm (pow_pos hdpos _)) ih
    apply hd.trans
    rw [pow_mul]
    have he := (ho.pow (n := j)).add_dvd_pow_add_pow ((2:ℤ)^m) 1
    simp only [one_pow] at he
    exact_mod_cast he

/-- Recover the odd value once every positive dyadic multiple has a witness.
Only uncertified odd values enter this step. -/
def H1 : Prop := ∀ h : ℕ, Odd h → (300 < h ∨ h ∈ [69, 91, 114, 141, 157, 175, 195]) →
  (¬ h+4 ∣ 2^(h+4)+1) →
  (∀ v : ℕ, 0 < v → ∃ m : ℕ, 1 ≤ m ∧ OeisA212844.a m = 2^v*h) →
  ∃ n : ℕ, 1 ≤ n ∧ OeisA212844.a n = h

/-- For each remaining odd part, some finite lookahead suffices for descent.
The length may depend arbitrarily on that odd part. Only exponents without a
prime-part certificate or a verified finite witness need this implication. -/
def H2 : Prop := ∀ h : ℕ, Odd h → 9 < h → ∃ L : ℕ, ∀ v : ℕ, 0 < v →
  (300 < 2^v*h ∨ 2^v*h ∈ [69, 91, 114, 141, 157, 175, 195]) →
  (∀ p : ℕ, p.Prime → h < p → ¬ 2^(2^v+2-v) ≡ h [MOD p]) →
  (∀ j : ℕ, 0 < j → j ≤ L → ∃ m : ℕ, 1 ≤ m ∧ OeisA212844.a m = 2^(v+j)*h) →
  ∃ n : ℕ, 1 ≤ n ∧ OeisA212844.a n = 2^v*h

theorem main : H1 → H2 → type_of% @OeisA212844.conjecture := by
  intro hodd heven k
  by_cases hk : k = 0
  · subst k; exact ⟨1,by decide,a_1⟩
  obtain ⟨v,h,ho,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  by_cases hsmall : h ≤ 9
  · apply small_odd_parts
    obtain ⟨m,hm⟩ := ho
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨L,hL⟩ := heven h ho (by omega)
  let occurs (j : ℕ) := ∃ n : ℕ, 1 ≤ n ∧ a n = 2^j*h
  have unverified (j : ℕ) (hc : ¬(2^j*h ≤ 300 ∧ 2^j*h ∉ [69, 91, 114, 141, 157, 175, 195])) :
      300 < 2^j*h ∨ 2^j*h ∈ [69, 91, 114, 141, 157, 175, 195] := by
    by_cases ht : 2^j*h ≤ 300
    · exact Or.inr (Classical.byContradiction fun hnot => hc ⟨ht,hnot⟩)
    · exact Or.inl (by omega)
  have down (j : ℕ) (hj : 0 < j) (hnext : ∀ t : ℕ, 0 < t → t ≤ L → occurs (j+t)) :
      occurs j := by
    by_cases hc : 2^j*h ≤ 300 ∧ 2^j*h ∉ [69, 91, 114, 141, 157, 175, 195]
    · exact finite_witnesses _ hc.1 hc.2
    by_cases hprime : ∃ p : ℕ, p.Prime ∧ h < p ∧ 2^(2^j+2-j) ≡ h [MOD p]
    · obtain ⟨p,hp,hhp,hr⟩ := hprime
      exact ⟨_,Nat.mul_pos (by positivity) hp.pos,
        prime_part _ _ _ hp (hp.odd_of_ne_two (by omega)) hhp hr⟩
    exact hL j hj (unverified j hc) (fun p hp hlt hr => hprime ⟨p,hp,hlt,hr⟩) hnext
  have positive (j : ℕ) (hj : 0 < j) : occurs j := by
    obtain ⟨b,hb,htop⟩ := exponent_blocks h L j ho
    let block (a : ℕ) := 0 < a → ∀ t ≤ L, occurs (a+t)
    have step (a : ℕ) (hup : block (a+1)) : block a := by
      intro ha t ht
      cases t with
      | zero =>
        rw [Nat.add_zero]
        apply down a ha
        intro r hr hrl
        obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hup (by omega) s (by omega)
      | succ s =>
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hup (by omega) s (by omega)
    have bj : block j := Nat.decreasingInduction (motive := fun a _ => block a)
      (fun a _ => step a) (fun _ => htop) hb
    simpa using bj hj 0 (Nat.zero_le _)
  by_cases hv : v = 0
  · subst v
    by_cases hf : 2^0*h ≤ 300 ∧ 2^0*h ∉ [69, 91, 114, 141, 157, 175, 195]
    · exact finite_witnesses _ hf.1 hf.2
    by_cases hn : h+4 ∣ 2^(h+4)+1
    · have hh : 4 < h+4 := by omega
      exact ⟨h+4,by omega,by simpa using novak_value _ hh hn⟩
    simpa using hodd h ho (by simpa using unverified 0 hf) hn positive
  exact positive v (Nat.pos_of_ne_zero hv)

end OMA.R_OeisA212844_conjecture_R1

