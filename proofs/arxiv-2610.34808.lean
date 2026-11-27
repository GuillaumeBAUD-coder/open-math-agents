import OMAStatements.S_arxiv_2610_34808
import Mathlib

/-!
# Classification of the inverse totients in He’s Open Problem 16

Credit: @rleshner

Euler's prime multiplication rules give a complete generator with an
exponent budget. Carmichael's classical replacement of a prime by its
predecessor forces 4, 9 and 49 to divide any unique positive preimage.
Since φ(49) = 42, uniqueness is impossible in the specified family.

For part (a), a covering of exponents modulo 36 gives an infinite reduced
progression whose fibers are all empty. Conversely, the first occurrence of
the odd factor q supplies a seed with only one prime divisor. Multiplying
by three suitable integers of totient 256 gives at least three preimages
for another exponent, ruling out any uniformly nonempty 0-or-2 scenario.
-/

open OMA.S_arxiv_2610_34808

private theorem splitFactors {q x y s t : ℕ} (hq : q.Prime)
    (h : x*y = 2^s*q^t) :
    ∃ a b c d : ℕ, a+c=s ∧ b+d=t ∧ x=2^a*q^b ∧ y=2^c*q^d := by
  have hq0 := hq.pos
  have hx : x ∣ 2^s*q^t := ⟨y,h.symm⟩
  obtain ⟨u,v,hu,hv,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hx
  obtain ⟨a,ha,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  obtain ⟨b,hb,rfl⟩ := (Nat.dvd_prime_pow hq).mp hv
  refine ⟨a,b,s-a,t-b,by omega,by omega,rfl,?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^a*q^b)
  rw [h]
  calc
    2^s*q^t = 2^(a+(s-a))*q^(b+(t-b)) := by congr 2 <;> omega
    _ = _ := by rw [pow_add, pow_add]; ring

private theorem generated_sound {q : ℕ} (hq : q.Prime) {s t n : ℕ}
    (h : Generated q s t n) : n.totient = 2^s*q^t := by
  induction h with
  | one => simp
  | newPrime p hp form fresh old ih =>
    rw [Nat.totient_mul_of_prime_of_not_dvd hp fresh, ih, form, Nat.add_sub_cancel, pow_add,
      pow_add]
    ring
  | moreTwo already old ih =>
    rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two already, ih, pow_succ]
    ring
  | moreQ already old ih =>
    rw [Nat.totient_mul_of_prime_of_dvd hq already, ih, pow_succ]
    ring

private theorem generated_complete {q : ℕ} (hq : q.Prime) (n : ℕ) :
    ∀ s t : ℕ, n.totient = 2^s*q^t → Generated q s t n := by
  induction n using induction_on_primes with
  | zero =>
    intro s t h
    have hq0 := hq.pos
    simp only [Nat.totient_zero] at h
    exact ((by positivity : 0 < 2^s*q^t).ne' h.symm).elim
  | one =>
    intro s t h
    obtain ⟨hh,hj⟩ := mul_eq_one.mp (by simpa using h.symm : 2^s*q^t=1)
    have hs : s=0 := (Nat.pow_eq_one.mp hh).resolve_left (by decide)
    have ht : t=0 := (Nat.pow_eq_one.mp hj).resolve_left hq.ne_one
    subst s; subst t; exact .one
  | prime_mul p m hp ih =>
    intro s t h
    by_cases hd : p ∣ m
    · rw [Nat.totient_mul_of_prime_of_dvd hp hd] at h
      have hpd : p ∣ 2^s*q^t := ⟨m.totient,h.symm⟩
      rcases hp.dvd_mul.mp hpd with h2 | hq'
      · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
        subst p
        cases s with
        | zero =>
          simp only [pow_zero] at h2
          exact (Nat.prime_two.not_dvd_one h2).elim
        | succ s =>
          rw [pow_succ',mul_assoc] at h
          exact .moreTwo hd (ih _ _ (Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h))
      · have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hq')
        subst p
        cases t with
        | zero =>
          simp only [pow_zero] at hq'
          exact (hq.not_dvd_one hq').elim
        | succ t =>
          rw [pow_succ',mul_left_comm] at h
          exact .moreQ hd (ih _ _ (Nat.eq_of_mul_eq_mul_left hq.pos h))
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd] at h
      obtain ⟨a,b,c,d,rfl,rfl,hab,hcd⟩ := splitFactors hq h
      have hform : p=2^a*q^b+1 := by have := hp.pos; omega
      exact .newPrime p hp hform hd (ih _ _ hcd)

/-- Multiplying by a divisor of n scales its totient by that divisor. -/
private theorem scaleTotient {d n : ℕ} (hd : 0 < d) (h : d ∣ n) :
    (d*n).totient = d*n.totient := by
  have e := Nat.totient_gcd_mul_totient_mul d n
  rw [Nat.gcd_eq_left h] at e
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hd) (by simpa [mul_comm, mul_assoc,
    mul_left_comm] using e)

/-- Carmichael's forcing step: a unique positive preimage divisible by
(p-1)^2 must also contain p². Exchange p with p-1 in a suitable multiple. -/
private theorem forcedSquare {n : ℕ} (hn : 0 < n)
    (hu : ∀ m : ℕ, m.totient = n.totient → m = n) {p : ℕ} (hp : p.Prime)
    (h : (p-1)^2 ∣ n) : p^2 ∣ n := by
  let d := p-1
  have hd : 0 < d := by dsimp [d]; have := hp.one_lt; omega
  have hdvd : d ∣ n := (dvd_pow_self d (by decide : 2 ≠ 0)).trans h
  have hcop : d.Coprime p :=
    (Nat.coprime_self_sub_left hp.one_lt.le).mpr (Nat.coprime_one_left _)
  by_cases hpn : p ∣ n
  · obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by by_contra! h0; simp [Nat.eq_zero_of_le_zero h0] at hm; omega
    by_cases hpm : p ∣ m
    · obtain ⟨k,rfl⟩ := hpm
      exact ⟨k,by rw [hm]; ring⟩
    exfalso
    have hdm := hcop.dvd_of_dvd_mul_left (hm ▸ hdvd)
    have eq := hu (d*m) (by rw [hm, scaleTotient hd hdm,
      Nat.totient_mul_of_prime_of_not_dvd hp hpm])
    rw [hm] at eq
    have := Nat.eq_of_mul_eq_mul_right hmpos eq
    dsimp [d] at this
    omega
  · exfalso
    obtain ⟨k,hk⟩ := h
    let m := d*k
    have hm : n = d*m := by simpa [m, d, pow_two, Nat.mul_assoc] using hk
    have hdvm : d ∣ m := dvd_mul_right d k
    have hpm : ¬ p ∣ m := fun e => hpn (hm ▸ e.trans (dvd_mul_left m d))
    have eq := hu (p*m) (by rw [hm, Nat.totient_mul_of_prime_of_not_dvd hp hpm,
      scaleTotient hd hdvm])
    exact hpn ⟨m,eq.symm⟩

private theorem secondPreimage {q s n : ℕ} (hq : q.Prime)
    (h : n.totient = 2^s*q) : ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  by_contra! unique
  have hu : ∀ m : ℕ, m.totient = n.totient → m=n := by
    intro m hm
    by_contra hmn
    exact unique m hmn hm
  have hn : 0 < n := by
    have hq0 := hq.pos
    apply Nat.totient_pos.mp
    rw [h]; positivity
  have h4 : 4 ∣ n := forcedSquare hn hu Nat.prime_two (by norm_num)
  have h9 : 9 ∣ n := forcedSquare hn hu (by decide : Nat.Prime 3) h4
  have h36 : 36 ∣ n := (show Nat.Coprime 4 9 by decide).mul_dvd_of_dvd_of_dvd h4 h9
  have h49 : 49 ∣ n := forcedSquare hn hu (by decide : Nat.Prime 7) h36
  have h42 : 42 ∣ 2^s*q := h ▸ (show 42 ∣ n.totient by
    simpa only [show (49:ℕ).totient=42 by decide] using Nat.totient_dvd_of_dvd h49)
  have force (l : ℕ) (hl : l.Prime) (hld : l ∣ 42) (hl2 : l ≠ 2) : l = q := by
    rcases hl.dvd_mul.mp (hld.trans h42) with htwo | hq'
    · exact (hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow htwo))).elim
    · exact (Nat.prime_dvd_prime_iff_eq hl hq).mp hq'
  have := force 3 (by decide) (by decide) (by decide)
  have := force 7 (by decide) (by decide) (by decide)
  omega

/-- With neither a pure prime equal to q nor a mixed new prime, a construction
with at most one q in its budget cannot spend that q. -/
private theorem noMixed {q : ℕ} (hq : q.Prime) (pure : ∀ a : ℕ, q ≠ 2^a+1)
    (mixed : ∀ a : ℕ, ¬(2^a*q+1).Prime) {s t n : ℕ} (h : Generated q s t n) :
    t ≤ 1 → t = 0 ∧ ¬q ∣ n := by
  induction h with
  | one => exact fun _ => ⟨rfl,hq.not_dvd_one⟩
  | @newPrime m u v a b p hp form fresh old ih =>
    intro ht
    obtain ⟨rfl,hm⟩ := ih (by omega)
    have hb : b=0 := by
      by_contra! hn
      have hb : b=1 := by omega
      subst b
      apply mixed a
      simpa [form] using hp
    subst b
    refine ⟨rfl,?_⟩
    intro hd
    rcases hq.dvd_mul.mp hd with he | he
    · have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp he
      exact pure a (by simpa [form] using heq)
    · exact hm he
  | moreTwo already old ih =>
    intro h1
    obtain ⟨ht,hn⟩ := ih h1
    refine ⟨ht,?_⟩
    intro hd
    rcases hq.dvd_mul.mp hd with h2 | h'
    · exact pure 0 (by simpa using (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
    · exact hn h'
  | moreQ already old ih =>
    intro h1
    exact ((ih (by omega)).2 already).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Four multipliers have totient 256. At most one contains a specified
odd prime, so three can be used alongside any power of that prime. -/
private theorem multipliers {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ x y z : ℕ, x<y ∧ y<z ∧ x.Coprime r ∧ y.Coprime r ∧ z.Coprime r ∧
      x.totient=256 ∧ y.totient=256 ∧ z.totient=256 := by
  by_cases h3 : r=3
  · subst r; exact ⟨512,544,640,by decide⟩
  by_cases h5 : r=5
  · subst r; exact ⟨512,544,768,by decide⟩
  have hcop : (512*640*768 : ℕ).Coprime r := by
    apply Nat.Coprime.symm
    apply hr.coprime_iff_not_dvd.mpr
    intro hd
    rw [show (512*640*768 : ℕ) = 2^24*3*5 by decide] at hd
    rcases hr.dvd_mul.mp hd with h23 | h
    · rcases hr.dvd_mul.mp h23 with h | h
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp h)
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 5)).mp h)
  obtain ⟨hxy,hz⟩ := Nat.coprime_mul_iff_left.mp hcop
  obtain ⟨hx,hy⟩ := Nat.coprime_mul_iff_left.mp hxy
  exact ⟨512,640,768,by decide,by decide,hx,hy,hz,by decide,by decide,by decide⟩

private theorem threeFromSeed {q r k a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hs : (r^k).totient=2^a*q) :
    ∃ t ≥ 3, ∃ x y z : ℕ, x<y ∧ y<z ∧ x.totient=2^t*q ∧
      y.totient=2^t*q ∧ z.totient=2^t*q := by
  obtain ⟨x,y,z,hxy,hyz,hx,hy,hz,hxt,hyt,hzt⟩ := multipliers hr hr2
  have hpos := pow_pos hr.pos k
  refine ⟨8+a,by omega,x*r^k,y*r^k,z*r^k,Nat.mul_lt_mul_of_pos_right hxy hpos,
    Nat.mul_lt_mul_of_pos_right hyz hpos,?_⟩
  rw [Nat.totient_mul (hx.pow_right k),Nat.totient_mul (hy.pow_right k),
    Nat.totient_mul (hz.pow_right k),hxt,hyt,hzt,hs,pow_add]
  norm_num [Nat.mul_assoc]

private theorem nonemptyGivesThree {q n s : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : n.totient=2^s*q) :
    ∃ t ≥ 3, ∃ x y z : ℕ, x<y ∧ y<z ∧ x.totient=2^t*q ∧
      y.totient=2^t*q ∧ z.totient=2^t*q := by
  by_cases hF : ∃ a : ℕ, q=2^a+1
  · obtain ⟨a,ha⟩ := hF
    apply threeFromSeed (r:=q) (k:=2) (a:=a) hq hq2
    rw [Nat.totient_prime_pow hq (by decide)]
    simp [ha, Nat.mul_comm]
  by_cases hM : ∃ a : ℕ, (2^a*q+1).Prime
  · obtain ⟨a,ha⟩ := hM
    have hr : 2^a*q+1 ≠ 2 := by
      have hbig := hq.one_lt
      have hge := Nat.le_mul_of_pos_left q (by positivity : 0<2^a)
      omega
    apply threeFromSeed (k:=1) (a:=a) ha hr
    rw [pow_one,Nat.totient_prime ha,Nat.add_sub_cancel]
  have gen := generated_complete hq n s 1 (by simpa using hn)
  have hx := noMixed hq (not_exists.mp hF) (not_exists.mp hM) gen (by decide)
  omega

/-- The classical seven-prime covering for 78557, with the extra congruence
q ≡ 7 mod 8 to exclude Fermat-type factors. -/
private theorem inverseTotientCover :
    ∀ q : ℕ, q.Prime → q % 560403480 = 420381167 →
      (∀ a : ℕ, q ≠ 2 ^ a + 1) ∧ (∀ a : ℕ, ¬ (2 ^ a * q + 1).Prime) := by
  intro q _ hq
  have hmod : q ≡ 420381167 [MOD 560403480] := hq
  have hbig : 420381167 ≤ q := hq ▸ Nat.mod_le q 560403480
  constructor
  · intro a ha
    rcases a with _ | a
    · simp at ha; omega
    rcases a with _ | a
    · simp at ha; omega
    rcases a with _ | a
    · simp at ha; omega
    have h8 := hmod.of_dvd (show 8 ∣ 560403480 by decide)
    have h0 : 8 ∣ 2 ^ (a + 3) := by
      rw [pow_add]; exact dvd_mul_left _ _
    have h1 := Nat.mod_eq_zero_of_dvd h0
    change q % 8 = 7 at h8
    change q = 2 ^ (a + 3) + 1 at ha
    omega
  · intro a hp
    have cert : ∀ i : Fin 36, ∃ d : Fin 74, 1 < d.val ∧
        d.val ∣ 560403480 ∧ (2:ℕ)^36 ≡ 1 [MOD d.val] ∧
        (2^i.val * 420381167 + 1 : ℕ) ≡ 0 [MOD d.val] := by decide +kernel
    obtain ⟨d, hd, hM, period, zero⟩ := cert ⟨a % 36, Nat.mod_lt _ (by decide)⟩
    have hpow : (2:ℕ)^a ≡ 2^(a%36) [MOD d.val] := by
      calc
        2^a = 2^(a%36) * (2^36)^(a/36) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
        _ ≡ 2^(a%36) * 1^(a/36) [MOD d.val] := (period.pow _).mul_left _
        _ = _ := by simp
    have hend : (2^a*q+1 : ℕ) ≡ 0 [MOD d.val] :=
      ((hpow.mul (hmod.of_dvd hM)).add_right 1).trans zero
    have hf : d.val ∣ 2^a*q+1 := Nat.dvd_of_mod_eq_zero hend
    have hge : q ≤ 2^a*q := by simpa using Nat.mul_le_mul_right q (show 1 ≤ 2^a by exact Nat.one_le_pow _ _ (by decide))
    have hlt := d.isLt
    rcases (Nat.dvd_prime hp).mp hf with h | h <;> omega

theorem OMA.solution : type_of% @OMA.S_arxiv_2610_34808.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hodd s _
    refine ⟨?_, fun _ h => secondPreimage hq h, fun _ h => nonemptyGivesThree hq hodd h⟩
    intro n
    constructor
    · intro h; exact generated_complete hq n s 1 (by simpa using h)
    · intro h; simpa using generated_sound hq h
  · have h := Nat.infinite_setOfPred_prime_and_modEq (by decide : 560403480 ≠ 0)
      (by decide : Nat.Coprime 420381167 560403480)
    exact h
  · intro q hq hr s _ n h
    obtain ⟨pure, mixed⟩ := inverseTotientCover q hq hr
    have hg := generated_complete hq n s 1 (by simpa using h)
    have := (noMixed hq pure mixed hg (by decide)).1
    omega
