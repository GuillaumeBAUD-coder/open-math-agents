import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1

/-! Lucas’ theorem bounds the units and middle digits of k/w when a prime w
misses the binomial coefficient. For each pair of missing primes these digit
bounds contradict the close, increasing gaps. Thus the gcd contains two primes. -/
namespace GapDigits
open Nat

lemma next_digits {w n k : ℕ} (hw : w.Prime) (h : ¬w ∣ n.choose k) :
    k%w ≤ n%w ∧ ¬w ∣ (n/w).choose (k/w) := by
  let : Fact w.Prime := ⟨hw⟩
  have he := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := w) (n := n) (k := k)
  constructor
  · by_contra! hh
    rw [Nat.choose_eq_zero_of_lt hh,zero_mul] at he
    exact h (Nat.modEq_zero_iff_dvd.mp he)
  · intro hd
    exact h (Nat.modEq_zero_iff_dvd.mp
      (he.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hd _))))

lemma low {w u v z : ℕ} (hw : w.Prime) (h : ¬w ∣ (w*u).choose (w*v))
    (hlo : u%w=z) : v%w ≤ z := by
  have hn := (next_digits hw h).2
  simp only [Nat.mul_div_cancel_left _ hw.pos] at hn
  simpa only [←hlo] using (next_digits hw hn).1

lemma upper {w u v a b : ℕ} (hw : w.Prime) (h : ¬w ∣ (w*u).choose (w*v))
    (hu : u=b+(a+w)*w) (ha : a<w) (hb : b<w) (hv : 2*v≤u) : v < (a+1)*w := by
  have hn := (next_digits hw h).2
  simp only [Nat.mul_div_cancel_left _ hw.pos] at hn
  have h1 := (next_digits hw (next_digits hw hn).2).1
  have hv' : v / w < w := (Nat.div_lt_iff_lt_mul hw.pos).mpr (by
    nlinarith [Nat.mul_le_mul_right w (show a+1 ≤ w by omega)])
  rw [Nat.mod_eq_of_lt hv',hu,Nat.add_mul_div_right _ _ hw.pos,Nat.div_eq_of_lt hb,
    zero_add,Nat.add_mod_right,Nat.mod_eq_of_lt ha] at h1
  exact (Nat.div_lt_iff_lt_mul hw.pos).mp (by omega)

lemma neg_residue {w a d t : ℕ} (he : a+d=w) (ht : 0<t) (hd : 0<d) (hlt : t*d<w) :
    (t*a)%w = w-t*d := by
  have h1 : w-t*d+t*d=w := Nat.sub_add_cancel hlt.le
  have h2 : t-1+1=t := by omega
  have heq : t*a=(w-t*d)+(t-1)*w := by
    nlinarith only [h1,congrArg (t*·) he,congrArg (·*w) h2]
  rw [heq,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (by have := Nat.mul_pos ht hd; omega)]

lemma small_from_multiple {w s u t a b : ℕ} (hw : w.Prime)
    (h : ¬w ∣ (w*u).choose (w*(t*s))) (hhalf : 2*(t*s) ≤ u)
    (hu : u=b+(a+w)*w) (ha : a<w) (hb : b<w) (hs : w ≤ s) : t ≤ a := by
  have hh := upper hw h hu ha hb hhalf
  have hmul := Nat.mul_le_mul_left t hs
  by_contra! ht
  exact (not_lt_of_ge (Nat.mul_le_mul_right w ht)).elim (hmul.trans_lt hh)

lemma p_digits {p q r d e : ℕ} (hq : q=p+d) (hr : r=p+e) (hd : 0<d) (hde : d<e)
    (hs : 2*e^2 < p) :
    q*r=d*e+(d+e+p)*p ∧ d+e<p ∧ d*e<p := by
  refine ⟨by rw [hq,hr]; ring,?_,?_⟩
  · nlinarith [Nat.le_self_pow (by decide : 2≠0) e]
  · nlinarith [Nat.mul_le_mul_right e hde.le]

lemma q_digits {p q r d b : ℕ} (hq : p+d=q) (hr : q+b=r)
    (hd : 0<d) (hdb : d<b) (hs : 2*(d+b)^2 < p) :
    p*r=(q-d*b)+((b-d-1)+q)*q ∧ b-d-1<q ∧ q-d*b<q := by
  have hdvd : d*b<q := by nlinarith
  have h1 := Nat.sub_add_cancel hdvd.le
  have h2 : b-d-1+1+d=b := by omega
  refine ⟨?_,by nlinarith [Nat.le_self_pow (by decide : 2≠0) b],?_⟩
  · nlinarith only [h1,congrArg (·*q) h2,congrArg (p*·) hr,congrArg (·*q) hq,congrArg (·*b) hq]
  · have := Nat.mul_pos hd (show 0<b by omega)
    omega

lemma r_low {p q r e b : ℕ} (hp : p+e=r) (hq : q+b=r) (he : b≤e)
    (hs : 2*e^2<p) : (p*q)%r=e*b := by
  have hle : e*b<r := by nlinarith [Nat.mul_le_mul_left e he]
  have hb : e+b≤r := by nlinarith [Nat.le_self_pow (by decide : 2≠0) e]
  have h := Nat.sub_add_cancel hb
  have H : p*q=e*b+(r-(e+b))*r := by
    nlinarith only [congrArg (·*q) hp,congrArg (·*e) hq,congrArg (·*r) hq,congrArg (·*r) h]
  rw [H,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hle]
lemma top_clash {p q r e b s d t : ℕ} (hr : r.Prime)
    (hp : p+e=r) (hq : q+b=r) (hbe : b≤e) (hs : 2*e^2<p) (hsd : s+d=r)
    (ht : 0<t) (hd : 0<d) (hm : t*d+e*b<r)
    (h : ¬r ∣ (r*(p*q)).choose (r*(t*s))) : False := by
  have hl := low hr h (r_low hp hq hbe hs)
  rw [neg_residue hsd ht hd (by omega)] at hl
  omega

lemma pq_clash {p q r d b t : ℕ} (hqprime : q.Prime)
    (hq : p+d=q) (hr : q+b=r) (hd : 0<d) (hdb : d<b) (hs : 2*(d+b)^2<p)
    (ht : 0<t) (half : 2*t ≤ r)
    (h : ¬q ∣ (q*(p*r)).choose (q*(t*p))) : False := by
  obtain ⟨hu,ha,hb⟩ := q_digits hq hr hd hdb hs
  have hv : 2*(t*p) ≤ p*r := by nlinarith [Nat.mul_le_mul_right p half]
  have hupp := upper hqprime h hu ha hb hv
  let A := b-d-1
  have hA : A+1+d=b := by dsimp [A]; omega
  change t*p < (A+1)*q at hupp
  have hdbp : d*b<p := by nlinarith
  have hAprod : (A+1)*d < p := by nlinarith [Nat.mul_le_mul_right d (show A+1 ≤ b by omega)]
  have htA : t ≤ A+1 := by
    by_contra! hgt
    have := Nat.mul_le_mul_right p hgt
    nlinarith only [this,hupp,hAprod,congrArg ((A+1)*·) hq]
  have htd : t*d<q := by nlinarith [Nat.mul_le_mul_right d htA]
  have hlow := low hqprime h (show (p*r)%q=q-d*b by rw [hu,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hb])
  rw [neg_residue hq ht hd htd] at hlow
  have hlt : t*d<b*d := Nat.mul_lt_mul_of_pos_right (by omega) hd
  rw [Nat.mul_comm b d] at hlt
  omega

lemma pr_clash {p q r d b t : ℕ} (hp : p.Prime) (hrprime : r.Prime)
    (hq : p+d=q) (hr : q+b=r) (hd : 0<d) (hdb : d<b) (hs : 2*(d+b)^2<p)
    (ht : 0<t) (half : 2*t ≤ q)
    (h : ¬p ∣ (p*(q*r)).choose (p*(t*r))) (h' : ¬r ∣ (r*(p*q)).choose (r*(t*p))) : False := by
  let e := d+b
  have he : p+e=r := by dsimp [e]; omega
  obtain ⟨hu,ha,hb⟩ := p_digits hq.symm he.symm hd (show d<e by dsimp [e]; omega) hs
  have htbd := small_from_multiple hp h (by nlinarith [Nat.mul_le_mul_right r half]) hu ha hb (by omega)
  apply top_clash hrprime he hr (by dsimp [e]; omega) hs he ht (by dsimp [e]; omega) _ h'
  have := Nat.mul_le_mul_right e htbd
  dsimp [e] at *
  nlinarith only [this,hs,he]

lemma qr_clash {p q r d b t : ℕ} (hqprime : q.Prime) (hrprime : r.Prime)
    (hq : p+d=q) (hr : q+b=r) (hd : 0<d) (hdb : d<b) (hs : 2*(d+b)^2<p)
    (ht : 0<t) (half : 2*t ≤ p)
    (h : ¬q ∣ (q*(p*r)).choose (q*(t*r))) (h' : ¬r ∣ (r*(p*q)).choose (r*(t*q))) : False := by
  obtain ⟨hu,ha,hb⟩ := q_digits hq hr hd hdb hs
  have htbd := small_from_multiple hqprime h (by nlinarith [Nat.mul_le_mul_right r half]) hu ha hb (by omega)
  apply top_clash hrprime (show p+(d+b)=r by omega) hr (by omega) hs hr ht (by omega) _ h'
  have := Nat.mul_le_mul_right b (show t ≤ b by omega)
  nlinarith
lemma two_missing {u v w k : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u ≠ v)
    (hk : 0<k) (hhalf : 2*k ≤ u*v*w)
    (hx : ¬u ∣ (u*v*w).choose k) (hy : ¬v ∣ (u*v*w).choose k) :
    ∃ t, 0<t ∧ 2*t ≤ w ∧ k=u*v*t := by
  have hu' : u ∣ u*v*w := dvd_mul_of_dvd_left (dvd_mul_right u v) _
  have hv' : v ∣ u*v*w := dvd_mul_of_dvd_left (dvd_mul_left v u) _
  have a := Erdos700.prime_dvd_of_not_dvd_choose _ _ _ hu hu' hx
  have b := Erdos700.prime_dvd_of_not_dvd_choose _ _ _ hv hv' hy
  obtain ⟨t,he⟩ := ((Nat.coprime_primes hu hv).mpr huv).mul_dvd_of_dvd_of_dvd a b
  refine ⟨t,?_,?_,he⟩
  · by_contra! h
    simp [show t=0 by omega] at he
    omega
  · exact Nat.le_of_mul_le_mul_left (show (u*v)*(2*t) ≤ (u*v)*w by nlinarith only [hhalf, congrArg (2*·) he]) (Nat.mul_pos hu.pos hv.pos)

lemma prime_pair {u v w k : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u ≠ v)
    (hw : 0<w) (hx : u ∣ (u*v*w).choose k) (hy : v ∣ (u*v*w).choose k) :
    u*v ≤ Nat.gcd (u*v*w) ((u*v*w).choose k) := by
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hu.pos hv.pos) hw))
  apply Nat.dvd_gcd (dvd_mul_right _ _)
  exact ((Nat.coprime_primes hu hv).mpr huv).mul_dvd_of_dvd_of_dvd hx hy

lemma lower {p q r k : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p<q) (hqr : q<r) (hgap : q-p<r-q) (hs : 2*(r-p)^2<p)
    (hk : 0<k) (hhalf : 2*k≤p*q*r) : p*q ≤ Nat.gcd (p*q*r) ((p*q*r).choose k) := by
  let d := q-p
  let b := r-q
  have hd : p+d=q := by dsimp [d]; omega
  have hb : q+b=r := by dsimp [b]; omega
  have hdp : 0<d := by dsimp [d]; omega
  have hs' : 2*(d+b)^2<p := by simpa only [show d+b=r-p by omega] using hs
  by_cases P : p ∣ (p*q*r).choose k
  · by_cases Q : q ∣ (p*q*r).choose k
    · exact prime_pair hp hq hpq.ne hr.pos P Q
    · by_cases R : r ∣ (p*q*r).choose k
      · refine (Nat.mul_le_mul_left p hqr.le).trans ?_
        simpa only [mul_assoc,mul_left_comm,mul_comm] using
          prime_pair (w := q) (k := k) hp hr (hpq.trans hqr).ne hq.pos
            (by simpa only [mul_assoc,mul_left_comm,mul_comm] using P)
            (by simpa only [mul_assoc,mul_left_comm,mul_comm] using R)
      · obtain ⟨t,ht,hb',he⟩ := two_missing (w := p) hq hr hqr.ne hk
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hhalf)
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using Q)
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using R)
        exact False.elim (qr_clash hq hr hd hb hdp hgap hs' ht hb'
          (by simpa only [he,mul_assoc,mul_left_comm,mul_comm] using Q)
          (by simpa only [he,mul_assoc,mul_left_comm,mul_comm] using R))
  · by_cases Q : q ∣ (p*q*r).choose k
    · by_cases R : r ∣ (p*q*r).choose k
      · refine (Nat.mul_le_mul hpq.le hqr.le).trans ?_
        simpa only [mul_assoc,mul_left_comm,mul_comm] using
          prime_pair (w := p) (k := k) hq hr hqr.ne hp.pos
            (by simpa only [mul_assoc,mul_left_comm,mul_comm] using Q)
            (by simpa only [mul_assoc,mul_left_comm,mul_comm] using R)
      · obtain ⟨t,ht,hb',he⟩ := two_missing (w := q) hp hr (hpq.trans hqr).ne hk
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hhalf)
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using P)
          (by simpa only [mul_assoc,mul_left_comm,mul_comm] using R)
        exact False.elim (pr_clash hp hr hd hb hdp hgap hs' ht hb'
          (by simpa only [he,mul_assoc,mul_left_comm,mul_comm] using P)
          (by simpa only [he,mul_assoc,mul_left_comm,mul_comm] using R))
    · obtain ⟨t,ht,hb',he⟩ := two_missing hp hq hpq.ne hk hhalf P Q
      exact False.elim (pq_clash hq hd hb hdp hgap hs' ht hb'
        (by simpa only [he,mul_assoc,mul_left_comm,mul_comm] using Q))

lemma result (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p<q) (hqr : q<r) (hgap : q-p<r-q) (hs : 2*(r-p)^2<p) :
    p*q*r < Erdos700.f (p*q*r)^2 := by
  have h2 := hp.two_le
  have h3 : 4 ≤ p*q*r := by nlinarith [Nat.mul_le_mul (show 2 ≤ p*q by nlinarith) (show 2 ≤ r by omega)]
  have hnonempty : (Erdos700.fSet (p*q*r)).Nonempty :=
    ⟨_,Erdos700.f_mem _ 2 (by decide) (by omega)⟩
  obtain ⟨k,hk,hhalf,he⟩ := Nat.sInf_mem hnonempty
  have hl := lower hp hq hr hpq hqr hgap hs (by omega : 0<k) (by omega)
  rw [Erdos700.f_eq,he]
  have he' : r-p < p := by nlinarith [Nat.le_self_pow (by decide : 2≠0) (r-p)]
  have hrlt : r < p*q := by nlinarith [Nat.mul_le_mul_left p (show 2≤q by omega),Nat.sub_add_cancel (hpq.trans hqr).le]
  have := Nat.mul_lt_mul_of_pos_left hrlt (Nat.mul_pos hp.pos hq.pos)
  nlinarith only [this,Nat.pow_le_pow_left hl 2]
end GapDigits

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 := GapDigits.result
