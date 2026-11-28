import OMAReductions.R_OeisA217703_conjecture_1_R1

/-! A finite-field criterion for polynomial irreducibility. -/

namespace OMA.SmallFactors
open Polynomial Finset

theorem irreducible_of_product_inverse {K : Type*} [Field K] [Finite K]
    {f : K[X]} (hpos : 0 < f.natDegree) (inv : K[X])
    (h : f ∣ inv * (∏ d ∈ Icc 1 (f.natDegree/2), (X ^ (Nat.card K)^d - X)) - 1) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by
    intro hf
    simp [hf] at hpos
  apply (irreducible_iff_lt_natDegree_lt hf0 (not_isUnit_of_natDegree_pos f hpos)).mpr
  intro g hg hsmall hgf
  have hneq : ¬ IsUnit g := not_isUnit_of_natDegree_pos g (mem_Ioc.mp hsmall).1
  obtain ⟨a, ha, hag⟩ := WfDvdMonoid.exists_irreducible_factor hneq hg.ne_zero
  have hmem : a.natDegree ∈ Icc 1 (f.natDegree/2) :=
    mem_Icc.mpr ⟨ha.natDegree_pos, (natDegree_le_of_dvd hag hg.ne_zero).trans (mem_Ioc.mp hsmall).2⟩
  have habase : a ∣ (X ^ (Nat.card K)^a.natDegree - X) :=
    ha.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp (dvd_refl _)
  have haprod : a ∣ (∏ d ∈ Icc 1 (f.natDegree/2), (X ^ (Nat.card K)^d - X)) :=
    habase.trans (dvd_prod_of_mem _ hmem)
  have hmul := dvd_mul_of_dvd_right haprod inv
  have hdiff := hag.trans (hgf.trans h)
  have hone : a ∣ (1 : K[X]) := by
    simpa only [sub_sub_cancel] using dvd_sub hmul hdiff
  exact ha.not_isUnit (isUnit_iff_dvd_one.mpr hone)

private noncomputable def polyAdd (k : ℕ) : Polynomial ℤ :=
  X + C (2*(k+1:ℤ)*(k+2))

private noncomputable def polyScale (k : ℕ) : Polynomial ℤ := C ((k+1:ℤ)^4)

theorem polyS_monic_degree (n : ℕ) :
    (OeisA217703.polyS n).Monic ∧ (OeisA217703.polyS n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [OeisA217703.polyS]
  | one => simp [OeisA217703.polyS]
  | more n h0 h1 =>
    let f := polyAdd n * OeisA217703.polyS (n+1)
    let g := polyScale n * OeisA217703.polyS n
    have hcast : ((n : ℤ) + 1) + 1 = n+2 := by omega
    have heq : OeisA217703.polyS (n+2) = f-g := by
      unfold OeisA217703.polyS f g polyAdd polyScale
      dsimp only
      rw [hcast]
    have ha : (polyAdd n).Monic := monic_X_add_C _
    have hma : (polyAdd n).natDegree = 1 := natDegree_X_add_C _
    have hfm : f.Monic := ha.mul h1.1
    have hfdeg : f.natDegree = n+2 := by
      rw [show f = polyAdd n * OeisA217703.polyS (n+1) from rfl,
        natDegree_mul ha.ne_zero h1.1.ne_zero, hma, h1.2]
      omega
    have hgdeg : g.natDegree ≤ n := by
      unfold g polyScale
      exact (natDegree_C_mul_le _ _).trans (le_of_eq h0.2)
    have hlt : g.natDegree < f.natDegree := by omega
    rw [heq]
    exact ⟨hfm.sub_of_left (degree_lt_degree hlt), (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hfdeg⟩

theorem transferMod {p n : ℕ} (hp : p.Prime)
    (h : Irreducible ((OeisA217703.polyS n).map (Int.castRingHom (ZMod p)))) :
    Irreducible ((OeisA217703.polyS n).map (Int.castRingHom ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hm := (polyS_monic_degree n).1
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp
    (Monic.irreducible_of_irreducible_map _ _ hm h)

end OMA.SmallFactors

namespace OMA.RadixPolynomial
open Polynomial Finset

private noncomputable def decode (b : ℕ) : ℕ → ℕ → ℕ[X]
  | 0, _ => 0
  | n+1, v => C (v%b) + X*decode b n (v/b)

private def digitCheck (b c : ℕ) : ℕ → ℕ → Bool
  | 0, v => decide (v=0)
  | n+1, v => decide (v%b<c) && digitCheck b c n (v/b)

private theorem evalDecode (b n v : ℕ) (hb : 0<b) (hv : v<b^n) :
    (decode b n v).eval b = v := by
  induction n generalizing v with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hv
    simp [decode, hv]
  | succ n ih =>
    simp only [decode, eval_add, eval_C, eval_mul, eval_X]
    have hdiv : v/b<b^n := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa only [pow_succ] using hv)
    rw [ih _ hdiv]
    exact Nat.mod_add_div _ _

private theorem decode_zero (b n v j : ℕ) (h : n≤j) :
    (decode b n v).coeff j = 0 := by
  induction n generalizing v j with
  | zero => simp [decode]
  | succ n ih =>
    cases j with
    | zero => omega
    | succ j =>
      simp [decode, coeff_add, coeff_X_mul, ih (v/b) j (by omega)]

private theorem digitCheck_sound (b c n v : ℕ) (hb : 0<b) (hc : 0<c)
    (h : digitCheck b c n v=true) :
    v < b^n ∧ ∀ j, (decode b n v).coeff j < c := by
  induction n generalizing v with
  | zero =>
    simp only [digitCheck, decide_eq_true_eq] at h
    simp [h, decode, hc]
  | succ n ih =>
    simp only [digitCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    have hq := ih (v/b) h.2
    refine ⟨by
      rw [pow_succ]
      exact (Nat.div_lt_iff_lt_mul hb).mp hq.1, ?_⟩
    intro j
    cases j with
    | zero => simpa [decode, coeff_add, coeff_X_mul] using h.1
    | succ j => simpa [decode, coeff_add, coeff_X_mul] using hq.2 j

private theorem headEval (b : ℕ) (f : ℕ[X]) :
    f.eval b = b*(f.divX.eval b)+f.coeff 0 := by
  simpa only [eval_add, eval_mul, eval_X, eval_C] using
    congrArg (eval b) (X_mul_divX_add f).symm

private theorem eqOfEval {b : ℕ} (hb : 0<b) (f g : ℕ[X])
    (hf : ∀ i, f.coeff i < b) (hg : ∀ i, g.coeff i < b) (he : f.eval b = g.eval b) : f=g := by
  ext i
  induction i generalizing f g with
  | zero =>
    have h := congrArg (fun n : ℕ => n%b) he
    change f.eval b % b = g.eval b % b at h
    rw [headEval b f, headEval b g, Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt (hf 0), Nat.mod_eq_of_lt (hg 0)] at h
    exact h
  | succ i ih =>
    have h := congrArg (fun n : ℕ => n/b) he
    have htail : f.divX.eval b=g.divX.eval b := by
      change f.eval b / b = g.eval b / b at h
      rw [headEval b f, headEval b g, Nat.mul_add_div hb, Nat.mul_add_div hb, Nat.div_eq_of_lt (hf 0),
        Nat.div_eq_of_lt (hg 0), add_zero, add_zero] at h
      exact h
    rw [← coeff_divX, ← coeff_divX]
    exact ih f.divX g.divX (fun i => by simpa [coeff_divX] using hf (i+1))
      (fun i => by simpa [coeff_divX] using hg (i+1)) htail

private theorem coeffMulBound (n m c d : ℕ) (f g : ℕ[X])
    (hf : ∀ i, f.coeff i ≤ c) (hg : ∀ i, g.coeff i ≤ d)
    (hf0 : ∀ i : ℕ, n ≤ i → f.coeff i = 0) (hg0 : ∀ i : ℕ, m ≤ i → g.coeff i = 0) (k : ℕ) :
    (f*g).coeff k ≤ (n+m)*(c*d) := by
  rw [coeff_mul]
  by_cases hk : k<n+m
  · calc
      _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal k, c*d :=
        sum_le_sum fun ij _ => Nat.mul_le_mul (hf ij.1) (hg ij.2)
      _ ≤ (n+m)*(c*d) := by
        rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        change (k+1)*(c*d) ≤ (n+m)*(c*d)
        exact Nat.mul_le_mul_right _ (by omega)
  · have hsum : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f.coeff ij.1*g.coeff ij.2) = 0 := by
      apply sum_eq_zero
      intro ij hij
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hi : n ≤ ij.1
      · rw [hf0 _ hi, zero_mul]
      · rw [hg0 _ (by omega), mul_zero]
    rw [hsum]
    exact Nat.zero_le _

private theorem packedIdentity {b n p a c f q r pad t : ℕ}
    (hb : 0 < b) (hn : 0 < n) (hp : 0 < p)
    (hfit : 2*n*p^2+p+p*16777216 < b)
    (ha : digitCheck b p n a = true)
    (hc : digitCheck b p n c = true)
    (hf : digitCheck b p n f = true)
    (hq : digitCheck b p (n-1) q = true)
    (hr : digitCheck b p n r = true)
    (hpad : digitCheck b (16777216) (2*n-1) pad = true)
    (ht : digitCheck b (16777216) (2*n-1) t = true)
    (heq : a*c+p*pad = (b^n+f)*q+r+p*t) :
    decode b n a * decode b n c + C p * decode b (2*n-1) pad =
      (X^n + decode b n f) * decode b (n-1) q + decode b n r + C p * decode b (2*n-1) t := by
  have hz : 0 < 16777216 := by positivity
  have ea := digitCheck_sound b p n a hb hp ha
  have ec := digitCheck_sound b p n c hb hp hc
  have ef := digitCheck_sound b p n f hb hp hf
  have eq := digitCheck_sound b p (n-1) q hb hp hq
  have er := digitCheck_sound b p n r hb hp hr
  have ep := digitCheck_sound b (16777216) (2*n-1) pad hb hz hpad
  have et := digitCheck_sound b (16777216) (2*n-1) t hb hz ht
  have hfBound (j : ℕ) : (X^n + decode b n f).coeff j ≤ p := by
    rw [coeff_add, coeff_X_pow]
    by_cases hj : j = n
    · subst j
      simpa [decode_zero b n f n le_rfl] using Nat.succ_le_of_lt hp
    · simp [hj, (ef.2 j).le]
  have hfZero (j : ℕ) (hj : n+1 ≤ j) : (X^n + decode b n f).coeff j = 0 := by
    rw [coeff_add, coeff_X_pow, decode_zero b n f j (by omega)]
    simp [show j ≠ n by omega]
  apply eqOfEval hb
  · intro j
    rw [coeff_add, coeff_C_mul]
    have hprod := coeffMulBound n n p p (decode b n a) (decode b n c)
      (fun i => (ea.2 i).le) (fun i => (ec.2 i).le)
      (decode_zero b n a) (decode_zero b n c) j
    calc
      _ ≤ (n+n)*(p*p)+p*(16777216) := Nat.add_le_add hprod (Nat.mul_le_mul_left _ (ep.2 j).le)
      _ ≤ 2*n*p^2+p+p*16777216 := by
        rw [show (n+n)*(p*p)=2*n*p^2 by ring]
        omega
      _ < b := hfit
  · intro j
    rw [coeff_add, coeff_add, coeff_C_mul]
    have hprod := coeffMulBound (n+1) (n-1) p p (X^n + decode b n f) (decode b (n-1) q)
      hfBound (fun i => (eq.2 i).le) hfZero (decode_zero b (n-1) q) j
    calc
      _ ≤ (n+1+(n-1))*(p*p)+p+p*(16777216) :=
        Nat.add_le_add (Nat.add_le_add hprod (er.2 j).le) (Nat.mul_le_mul_left _ (et.2 j).le)
      _ = 2*n*p^2+p+p*16777216 := by rw [show n+1+(n-1) = n+n by omega]; ring
      _ < b := hfit
  · simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X,
      evalDecode b n a hb ea.1, evalDecode b n c hb ec.1, evalDecode b n f hb ef.1,
      evalDecode b (n-1) q hb eq.1, evalDecode b n r hb er.1,
      evalDecode b (2*n-1) pad hb ep.1, evalDecode b (2*n-1) t hb et.1]
    exact heq

private theorem packedMulEval {K : Type*} [CommRing K]
    {b n p a c f q r pad t : ℕ} (g : ℕ[X] →+* K)
    (hb : 0 < b) (hn : 0 < n) (hp : 0 < p) (hfit : 2*n*p^2+p+p*16777216 < b)
    (ha : digitCheck b p n a = true) (hc : digitCheck b p n c = true)
    (hf : digitCheck b p n f = true) (hq : digitCheck b p (n-1) q = true)
    (hr : digitCheck b p n r = true)
    (hpad : digitCheck b (16777216) (2*n-1) pad = true)
    (ht : digitCheck b (16777216) (2*n-1) t = true)
    (heq : a*c+p*pad = (b^n+f)*q+r+p*t)
    (hchar : g (C p) = 0) (hmod : g (X^n + decode b n f) = 0) :
    g (decode b n a) * g (decode b n c) = g (decode b n r) := by
  have h := congrArg g (packedIdentity hb hn hp hfit ha hc hf hq hr hpad ht heq)
  rw [map_add, map_mul, map_mul, hchar, zero_mul, add_zero] at h
  rw [map_add, map_mul, hchar, zero_mul, add_zero, map_add, map_mul, hmod, zero_mul, zero_add] at h
  exact h

end OMA.RadixPolynomial

namespace OMA.CheckedPackedArithmetic

private def radix : ℕ := 18446744073709551616
private def power (n : ℕ) : ℕ := 1 <<< (64*n)

private def fill (n c : ℕ) : ℕ := c*((power n-1)/(radix-1))

private def lowWord (v : ℕ) : ℕ := v &&& (radix-1)

private def normalize (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, v => (lowWord v)%p + radix*normalize p n (v>>>64)

private def quotient (p n f : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, a =>
    let top := n+k
    let d := (a >>> (64*top))%p
    let low := (a &&& (power top-1)) - ((d*f)<<<(64*k))
    (d<<<(64*k)) + quotient p n f k low

private def mulChecked (p n f pad a b : ℕ) : Option ℕ :=
  let z := a*b+p*pad
  let c := quotient p n f (n-1) z
  let qf := c*(power n+f)
  let residual := z-qf
  let r := normalize p n residual
  let count := 2*n-1
  let t := (residual-r)/p
  let mask := fill count (radix-16777216)
  if t < power count ∧ t &&& mask = 0 ∧ z=qf+r+p*t then some r else none

private def subPacked (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => (lowWord a+p-lowWord b)%p + radix*subPacked p n (a>>>64) (b>>>64)

private def xPacked (p n f : ℕ) : ℕ := if n=1 then subPacked p n 0 f else radix

private def powChecked (p n f pad a : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => some 1
  | fuel+1, e =>
    if e=0 then some 1 else
    if e=1 then some a else do
      let r ← powChecked p n f pad a fuel (e/2)
      let s ← mulChecked p n f pad r r
      if e%2=0 then pure s else mulChecked p n f pad a s

private def productChecked (p n f pad fuel : ℕ) : ℕ → Option (ℕ × ℕ)
  | 0 => some (xPacked p n f, 1)
  | k+1 => do
    let state ← productChecked p n f pad fuel k
    let power ← powChecked p n f pad state.1 fuel p
    let diff := subPacked p n power (xPacked p n f)
    let product ← mulChecked p n f pad diff state.2
    pure (power, product)

private def checkInv (p n f inv : ℕ) : Bool :=
  let pad := fill (2*n-1) (n*p)
  let result := do
    let v ← productChecked p n f pad (p.log2+1) (n/2)
    mulChecked p n f pad v.2 inv
  decide (result = some 1)

open Polynomial OMA.RadixPolynomial

private theorem radix_pos : 0 < radix := by decide

private theorem power_eq (n : ℕ) : power n = radix^n := by
  unfold power
  rw [Nat.shiftLeft_eq, one_mul]
  change 2^(64*n) = (2^64)^n
  rw [pow_mul]

private theorem fill_succ (d n : ℕ) : fill (n+1) d = d + radix*fill n d := by
  have hradix : 2 ≤ radix := by decide
  unfold fill
  rw [power_eq, power_eq, ← Nat.geomSum_eq hradix, ← Nat.geomSum_eq hradix, geom_sum_succ]
  ring

private theorem lowWord_eq (v : ℕ) : lowWord v = v%radix := by
  exact Nat.and_two_pow_sub_one_eq_mod v 64

private theorem andPower_eq (v n : ℕ) : v &&& (power n-1) = v%power n := by
  unfold power
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

private theorem shiftWord_eq (v : ℕ) : v >>> 64 = v/radix := by
  exact Nat.shiftRight_eq_div_pow v 64

private theorem and_radix_mod (a b : ℕ) :
    (a &&& b)%radix = (a%radix &&& b%radix) := by
  exact Nat.and_mod_two_pow (a := a) (b := b) (n := 64)

private theorem and_radix_div (a b : ℕ) :
    (a &&& b)/radix = (a/radix &&& b/radix) := by
  exact Nat.and_div_two_pow (a := a) (b := b) (n := 64)

private theorem singleLane_bound {x : ℕ} (h : x<radix) (hz : x &&& (radix-16777216)=0) :
    x<16777216 := by
  by_contra! hlarge
  obtain ⟨j,hj,hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 24) hlarge
  have hj64 : j<64 := by
    by_contra! ha
    have lt : x<2^j := h.trans_le (Nat.pow_le_pow_right (by decide : 0<2) ha)
    have hb := Nat.testBit_lt_two_pow lt
    simp_all
  have hmask : (radix-16777216).testBit j=true := by
    rw [show radix-16777216 = (2^40-1) <<< 24 by decide,
      Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    have small : j-24<40 := by omega
    simp [hj,small]
  have hx : x.testBit j=true := hbit
  have bad := congrArg (fun w : ℕ => w.testBit j) hz
  simp [Nat.testBit_and,hx,hmask] at bad

private theorem guardedDigits {n t : ℕ} (fit : t<power n)
    (zero : t &&& fill n (radix-16777216)=0) :
    digitCheck radix 16777216 n t=true := by
  induction n generalizing t with
  | zero =>
    have ht : t=0 := by
      have hfit : t<1 := fit
      omega
    subst t
    simp [digitCheck]
  | succ n ih =>
    let m := radix-16777216
    have hm : m<radix := by decide
    have decomposition : fill (n+1) m = m+radix*fill n m := fill_succ _ _
    change t &&& fill (n+1) m=0 at zero
    have hmod : (fill (n+1) m)%radix = m := by
      rw [decomposition, Nat.add_comm, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hm]
    have hdiv : (fill (n+1) m)/radix = fill n m := by
      rw [decomposition, Nat.add_comm, Nat.mul_add_div radix_pos, Nat.div_eq_of_lt hm, add_zero]
    have hlow := congrArg (fun word => word%radix) zero
    rw [and_radix_mod, hmod, Nat.zero_mod] at hlow
    have hhead := singleLane_bound (Nat.mod_lt _ radix_pos) hlow
    have hwrapped := congrArg (fun word => word/radix) zero
    rw [and_radix_div, hdiv, Nat.zero_div] at hwrapped
    have hfit : t/radix < power n := by
      apply (Nat.div_lt_iff_lt_mul radix_pos).mpr
      rw [power_eq, ← pow_succ, ← power_eq]
      exact fit
    simp only [digitCheck, Bool.and_eq_true_iff, decide_eq_true_eq]
    exact ⟨hhead, ih hfit hwrapped⟩

private theorem consDigit {b bound n d v : ℕ} (hb : 0 < b)
    (hd : d<b) (hcap : d<bound) (hv : digitCheck b bound n v=true) :
    digitCheck b bound (n+1) (d+b*v)=true := by
  simp only [digitCheck, Bool.and_eq_true_iff, decide_eq_true_eq]
  rw [Nat.add_comm d, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hd,
    Nat.mul_add_div hb, Nat.div_eq_of_lt hd, add_zero]
  exact ⟨hcap,hv⟩

private theorem highDigit {b bound n v d : ℕ} (hb : 0<b)
    (hdb : d<b) (hdc : d<bound) (hv : digitCheck b bound n v=true) :
    digitCheck b bound (n+1) (v+b^n*d)=true := by
  induction n generalizing v with
  | zero =>
    simp only [digitCheck, decide_eq_true_eq] at hv
    subst v
    simpa using consDigit (n := 0) (v := 0) hb hdb hdc (by simp [digitCheck])
  | succ n ih =>
    simp only [digitCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at hv
    have heq : v+b^(n+1)*d = v%b+b*(v/b+b^n*d) := by
      calc
        _ = (v%b+b*(v/b))+b^(n+1)*d := by rw [Nat.mod_add_div]
        _ = _ := by rw [pow_succ]; ring
    rw [heq]
    exact consDigit hb (Nat.mod_lt _ hb) hv.1 (ih hv.2)

private theorem normalize_good {p : ℕ} (hp : 0<p) (hb : p≤radix) (n v : ℕ) :
    digitCheck radix p n (normalize p n v)=true := by
  induction n generalizing v with
  | zero => simp [normalize,digitCheck]
  | succ n ih =>
    unfold normalize
    simp only [lowWord_eq]
    apply consDigit radix_pos ((Nat.mod_lt _ hp).trans_le hb) (Nat.mod_lt _ hp)
    exact ih _

private theorem quotient_good {p : ℕ} (hp : 0<p) (hb : p≤radix) (n f k v : ℕ) :
    digitCheck radix p k (quotient p n f k v)=true := by
  induction k generalizing v with
  | zero => simp [quotient,digitCheck]
  | succ k ih =>
    unfold quotient
    simp only [andPower_eq]
    let d := (v >>> (64*(n+k)))%p
    let low := v%power (n+k) - ((d*f)<<<(64*k))
    change digitCheck radix p (k+1) ((d<<<(64*k))+quotient p n f k low)=true
    have heq : d<<<(64*k) = radix^k*d := by
      rw [Nat.shiftLeft_eq, mul_comm]
      change 2^(64*k)*d=(2^64)^k*d
      rw [pow_mul]
    rw [heq, add_comm (radix^k*d) (quotient p n f k low)]
    exact highDigit radix_pos ((Nat.mod_lt _ hp).trans_le hb) (Nat.mod_lt _ hp) (ih _)

private theorem mulSpec {K : Type*} [CommRing K]
    (g : ℕ[X] →+* K) {p n f pad a b r : ℕ}
    (hn : 0<n) (hp : 0<p) (hfit : 2*n*p^2+p+p*16777216 < radix)
    (hf : digitCheck radix p n f=true) (hpad : digitCheck radix (16777216) (2*n-1) pad=true)
    (ha : digitCheck radix p n a=true) (hb : digitCheck radix p n b=true)
    (hchar : g (C p)=0) (hpoly : g (X^n+decode radix n f)=0)
    (h : mulChecked p n f pad a b = some r) :
    digitCheck radix p n r=true ∧ g (decode radix n a)*g (decode radix n b)=g (decode radix n r) := by
  let z := a*b+p*pad
  let q := quotient p n f (n-1) z
  let qf := q*(power n+f)
  let rem := z-qf
  let rr := normalize p n rem
  let tt := (rem-rr)/p
  change (if tt < power (2*n-1) ∧ tt &&& fill (2*n-1) (radix-16777216)=0 ∧
    z=qf+rr+p*tt then some rr else none)=some r at h
  have hbnd : p≤radix := by omega
  split at h
  · rename_i hok
    have hr := Option.some.inj h
    subst r
    have hrr : digitCheck radix p n rr=true := normalize_good hp hbnd _ _
    have hqq : digitCheck radix p (n-1) q=true := quotient_good hp hbnd _ _ _ _
    have htt : digitCheck radix 16777216 (2*n-1) tt=true := guardedDigits hok.1 hok.2.1
    have he : a*b+p*pad = (radix^n+f)*q+rr+p*tt := by
      simpa only [qf, power_eq, mul_comm q (radix^n+f)] using hok.2.2
    exact ⟨hrr, packedMulEval g radix_pos hn hp hfit ha hb hf hqq hrr hpad htt he hchar hpoly⟩
  · contradiction

private theorem decodeHead {b n d v : ℕ} (hb : 0<b) (hd : d<b) :
    decode b (n+1) (d+b*v) = C d + X*decode b n v := by
  rw [Nat.add_comm d, decode, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hd,
    Nat.mul_add_div hb, Nat.div_eq_of_lt hd, add_zero]

private theorem decodeZero (n : ℕ) : decode radix n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [decode, ih]

private theorem decodeOne (n : ℕ) :
    decode radix (n+1) 1 = 1 := by
  have hh : 1 < radix := by decide
  simpa [decodeZero] using decodeHead (n := n) (v := 0) radix_pos hh

private theorem decodeX (n : ℕ) : decode radix (n+2) radix = X := by
  have hh : (0 : ℕ) < radix := radix_pos
  simpa [decodeOne] using decodeHead (n := n+1) (v := 1) radix_pos hh

private theorem zeroGood {p : ℕ} (hp : 0<p) (n : ℕ) :
    digitCheck radix p n 0=true := by
  induction n with
  | zero => simp [digitCheck]
  | succ n ih => simp [digitCheck, hp, ih]

private theorem oneGood {p n : ℕ} (hp : 1<p) (hn : 0<n) :
    digitCheck radix p n 1=true := by
  rcases n with _ | n
  · omega
  · have h : 1 < radix := by decide
    simpa using consDigit (n := n) (v := 0) radix_pos h hp (zeroGood (by omega) n)

private theorem xGood {p : ℕ} (hp : 1<p) (n : ℕ) :
    digitCheck radix p (n+2) radix=true := by
  simpa using consDigit (v := 1) (d := 0) radix_pos radix_pos
    (show 0<p by omega) (oneGood hp (show 0<n+1 by omega))

private theorem natVal {K : Type*} [CommRing K] (g : ℕ[X] →+* K) (a : ℕ) :
    g (C a) = (a:K) := by
  have h : (C a : ℕ[X]) = (a : ℕ[X]) := C_eq_natCast (R := ℕ) a
  rw [h, map_natCast]

private theorem natMod {K : Type*} [CommRing K] (g : ℕ[X] →+* K) {p : ℕ}
    (hp : g (C p)=0) (a : ℕ) : ((a%p:ℕ):K)=(a:K) := by
  have hp' := hp
  rw [natVal] at hp'
  have h := congrArg (fun n : ℕ => (n:K)) (Nat.mod_add_div a p)
  push_cast at h
  simpa [hp'] using h

private theorem subSpec {K : Type*} [CommRing K] (g : ℕ[X] →+* K) {p n a b : ℕ}
    (hp : 0<p) (hpb : p≤radix) (hchar : g (C p)=0)
    (ha : digitCheck radix p n a=true) (hb : digitCheck radix p n b=true) :
    digitCheck radix p n (subPacked p n a b)=true ∧
      g (decode radix n (subPacked p n a b)) = g (decode radix n a) - g (decode radix n b) := by
  induction n generalizing a b with
  | zero => simp [decode,subPacked,digitCheck]
  | succ n ih =>
    simp only [digitCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at ha hb
    let d := (a%radix+p-b%radix)%p
    have hsub : b%radix≤a%radix+p := by omega
    have hd : d<radix := (Nat.mod_lt _ hp).trans_le hpb
    have hdC : g (C d) = g (C (a%radix))-g (C (b%radix)) := by
      simp only [natVal, d, natMod g hchar, Nat.cast_sub hsub, Nat.cast_add]
      have hc := hchar
      rw [natVal] at hc
      rw [hc, add_zero]
    obtain ⟨ht,hs⟩ := ih ha.2 hb.2
    simp only [subPacked, lowWord_eq, shiftWord_eq]
    change digitCheck radix p (n+1) (d+radix*subPacked p n (a/radix) (b/radix))=true ∧ _
    refine ⟨consDigit radix_pos hd (Nat.mod_lt _ hp) ht, ?_⟩
    change g (decode radix (n+1) (d+radix*subPacked p n (a/radix) (b/radix))) =
      g (decode radix (n+1) a)-g (decode radix (n+1) b)
    rw [decodeHead radix_pos hd, map_add, map_mul, hs, hdC]
    simp only [decode, map_add, map_mul]
    ring

private theorem xSpec {K : Type*} [CommRing K] (g : ℕ[X] →+* K) {p n f : ℕ}
    (hp : 1<p) (hpb : p≤radix) (hn : 0<n) (hchar : g (C p)=0)
    (hmod : g (X^n+decode radix n f)=0)
    (hf : digitCheck radix p n f=true) :
    digitCheck radix p n (xPacked p n f)=true ∧ g (decode radix n (xPacked p n f)) = g X := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · change digitCheck radix p 1 (subPacked p 1 0 f)=true ∧ _
    obtain ⟨hv,he⟩ := subSpec g (by omega) hpb hchar (zeroGood (by omega) 1) hf
    refine ⟨hv, ?_⟩
    change g (decode radix 1 (subPacked p 1 0 f)) = g X
    rw [he, decodeZero, map_zero, zero_sub]
    change g (X^1+decode radix 1 f)=0 at hmod
    simp only [pow_one, map_add] at hmod
    linear_combination -hmod
  · have hn1 : n+2 ≠ 1 := by omega
    simpa [xPacked, hn1, decodeX] using xGood hp n

private theorem bindSome {A B : Type*} {o : Option A} {f : A → Option B} {r : B}
    (h : o.bind f=some r) : ∃ a, o=some a ∧ f a=some r := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a,rfl,h⟩

private theorem powSpec {K : Type*} [CommRing K]
    (g : ℕ[X] →+* K) {p n f pad : ℕ}
    (hn : 0<n) (hp : 1<p) (hfit : 2*n*p^2+p+p*16777216<radix)
    (hf : digitCheck radix p n f=true)
    (hpad : digitCheck radix (16777216) (2*n-1) pad=true)
    (hchar : g (C p)=0) (hpoly : g (X^n+decode radix n f)=0)
    (fuel e a r : ℕ) (he : e<2^fuel)
    (ha : digitCheck radix p n a=true) (h : powChecked p n f pad a fuel e=some r) :
    digitCheck radix p n r=true ∧ g (decode radix n r) = g (decode radix n a)^e := by
  have hone : g (decode radix n 1)=1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [decodeOne, map_one]
  induction fuel generalizing e a r with
  | zero =>
    have he0 : e=0 := by simpa using he
    have hr : r=1 := by simpa [powChecked, eq_comm] using h
    simp [hr, he0, hone, oneGood hp hn]
  | succ k ih =>
    by_cases he0 : e=0
    · have hr : r=1 := by simpa [powChecked, he0, eq_comm] using h
      simp [hr, he0, hone, oneGood hp hn]
    by_cases he1 : e=1
    · have hr : r=a := by simpa [powChecked, he0, he1, eq_comm] using h
      simp [hr, he1, ha]
    simp only [powChecked, if_neg he0, if_neg he1] at h
    obtain ⟨v,hv,hm⟩ := bindSome h
    obtain ⟨q,hq,hr⟩ := bindSome hm
    have hdiv : e/2<2^k := by rw [pow_succ] at he; omega
    obtain ⟨hvg,hve⟩ := ih _ _ _ hdiv ha hv
    obtain ⟨hqg,hqe⟩ := mulSpec g hn (by omega) hfit hf hpad hvg hvg hchar hpoly hq
    have hbase : g (decode radix n q) = g (decode radix n a)^(2*(e/2)) := by
      rw [← hqe, hve, mul_comm 2, pow_mul, pow_two]
    by_cases hmod : e%2=0
    · rw [if_pos hmod] at hr
      have hqr := Option.some.inj hr
      subst r
      exact ⟨hqg, by rw [hbase, show 2*(e/2)=e by omega]⟩
    · rw [if_neg hmod] at hr
      obtain ⟨hgood,hvalue⟩ := mulSpec g hn (by omega) hfit hf hpad ha hqg hchar hpoly hr
      refine ⟨hgood, ?_⟩
      rw [← hvalue, hbase, ← pow_succ', show 2*(e/2)+1=e by omega]

private theorem productSpec {K : Type*} [CommRing K]
    (g : ℕ[X] →+* K) {p n f pad fuel : ℕ}
    (hn : 0<n) (hp : 1<p) (hfit : 2*n*p^2+p+p*16777216 < radix)
    (hf : digitCheck radix p n f=true) (hpad : digitCheck radix (16777216) (2*n-1) pad=true)
    (hchar : g (C p)=0) (hpoly : g (X^n+decode radix n f)=0)
    (hpower : p<2^fuel) (steps a b : ℕ) (h : productChecked p n f pad fuel steps=some (a,b)) :
    digitCheck radix p n a=true ∧ digitCheck radix p n b=true ∧
      g (decode radix n a) = (g X)^(p^steps) ∧
      g (decode radix n b) = ∏ d ∈ Finset.Icc 1 steps, ((g X)^(p^d) - g X) := by
  have xok := xSpec g hp (by omega) hn hchar hpoly hf
  have hone : g (decode radix n 1)=1 := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [decodeOne, map_one]
  induction steps generalizing a b with
  | zero =>
    change some (xPacked p n f, 1)=some (a,b) at h
    have he := Option.some.inj h
    have ha : xPacked p n f=a := congrArg Prod.fst he
    have hb : (1:ℕ)=b := congrArg Prod.snd he
    subst a
    subst b
    simp [xok.1, xok.2, oneGood hp hn, hone]
  | succ steps ih =>
    simp only [productChecked] at h
    obtain ⟨state,hprev,hstep⟩ := bindSome h
    obtain ⟨x,hx,hacc⟩ := bindSome hstep
    obtain ⟨y,hy,hpair⟩ := bindSome hacc
    have he : (x,y)=(a,b) := Option.some.inj hpair
    have ha : x=a := congrArg Prod.fst he
    have hb : y=b := congrArg Prod.snd he
    subst a
    subst b
    obtain ⟨hprevX,hprevP,hevalX,hevalP⟩ := ih _ _ hprev
    obtain ⟨hnewX,heval⟩ := powSpec g hn hp hfit hf hpad hchar hpoly _ _ _ _ hpower hprevX hx
    have hpow : g (decode radix n x) = (g X)^(p^(steps+1)) := by
      rw [heval, hevalX, ← pow_mul, ← pow_succ]
    obtain ⟨hdiff,hde⟩ := subSpec g (by omega) (by omega) hchar hnewX xok.1
    obtain ⟨hfinal,hefinal⟩ := mulSpec g hn (by omega) hfit hf hpad hdiff hprevP hchar hpoly hy
    refine ⟨hnewX, hfinal, hpow, ?_⟩
    rw [← hefinal, hde, xok.2, hpow, hevalP, Finset.prod_Icc_succ_top (by omega)]
    exact mul_comm _ _

private theorem checkedInverse {K : Type*} [CommRing K]
    (g : ℕ[X] →+* K) {p n f inv : ℕ}
    (hn : 0<n) (hp : 1<p) (hfit : 2*n*p^2+p+p*16777216 < radix)
    (hf : digitCheck radix p n f=true)
    (hpad : digitCheck radix (16777216) (2*n-1) (fill (2*n-1) (n*p))=true)
    (hinv : digitCheck radix p n inv=true)
    (hchar : g (C p)=0) (hpoly : g (X^n+decode radix n f)=0)
    (h : checkInv p n f inv=true) :
    g (decode radix n inv) * (∏ d ∈ Finset.Icc 1 (n/2), ((g X)^(p^d) - g X)) = 1 := by
  simp only [checkInv, decide_eq_true_eq] at h
  obtain ⟨v,hchain,hend⟩ := bindSome h
  have hpower : p < 2^(p.log2+1) := (Nat.log2_lt (by omega : p≠0)).mp (Nat.lt_succ_self _)
  obtain ⟨_,hv,_,hvalue⟩ := productSpec g hn hp hfit hf hpad hchar hpoly hpower _ _ _ hchain
  obtain ⟨_,he⟩ := mulSpec g hn (by omega) hfit hf hpad hv hinv hchar hpoly hend
  have hone : g (decode radix n 1)=1 := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [decodeOne,map_one]
  rw [hvalue,hone] at he
  simpa only [mul_comm] using he

end OMA.CheckedPackedArithmetic

namespace OMA.CoefficientRows
open Polynomial

private def addVec (p : ℕ) (a b : List ℕ) : List ℕ :=
  List.zipWith (fun x y => (x+y)%p) a b

private def subVec (p : ℕ) (a b : List ℕ) : List ℕ :=
  List.zipWith (fun x y => (x+p-(y%p))%p) a b

private def scaleVec (p c : ℕ) (a : List ℕ) : List ℕ :=
  a.map (fun x => (x*c)%p)

section Soundness
variable {R : Type*} [CommRing R] {p : ℕ}

private def evalVec (x : R) : List ℕ → R
  | [] => 0
  | a::as => (a:R) + x*evalVec x as

private theorem castMod (hp : (p:R)=0) (a : ℕ) : ((a%p:ℕ):R) = a := by
  have h := congrArg (fun v : ℕ => (v:R)) (Nat.mod_add_div a p)
  push_cast at h
  simpa [hp] using h

private theorem castSubMod (hp : (p:R)=0) (hp' : 0<p) (a b : ℕ) :
    (((a+p-(b%p))%p:ℕ):R) = (a:R)-b := by
  have hmod := Nat.mod_lt b hp'
  rw [castMod hp, Nat.cast_sub (by omega : b%p ≤ a+p), Nat.cast_add, hp, add_zero, castMod hp]

private theorem evalZero (x : R) (n : ℕ) :
    evalVec x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, evalVec, ih]
    simp

private theorem evalAppend (x : R) (a b : List ℕ) :
    evalVec x (a++b) = evalVec x a + x^a.length * evalVec x b := by
  induction a with
  | nil => simp [evalVec]
  | cons h t ih =>
    simp only [List.cons_append, evalVec, List.length_cons, pow_succ, ih]
    ring

private theorem evalScale (hp : (p:R)=0) (x : R) (a : List ℕ) (c : ℕ) :
    evalVec x (scaleVec p c a) = (c:R)*evalVec x a := by
  induction a with
  | nil => simp [evalVec, scaleVec]
  | cons h t ih =>
    simp only [scaleVec, List.map_cons, evalVec, castMod hp, Nat.cast_mul] at ih ⊢
    rw [ih]
    ring

private theorem evalAdd (hp : (p:R)=0) (x : R) (a b : List ℕ) (h : a.length=b.length) :
    evalVec x (addVec p a b) = evalVec x a + evalVec x b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [addVec, evalVec]
  | cons hd tl ih =>
    cases b with
    | nil => simp at h
    | cons he tt =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [addVec, List.zipWith_cons_cons, evalVec, castMod hp, Nat.cast_add]
      have hi := ih tt h
      unfold addVec at hi
      rw [hi]
      ring

private theorem evalSub (hp : (p:R)=0) (hp' : 0<p) (x : R) (a b : List ℕ)
    (h : a.length=b.length) :
    evalVec x (subVec p a b) = evalVec x a - evalVec x b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [subVec, evalVec]
  | cons hd tl ih =>
    cases b with
    | nil => simp at h
    | cons he tt =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [subVec, List.zipWith_cons_cons, evalVec, castSubMod hp hp']
      have hi := ih tt h
      unfold subVec at hi
      rw [hi]
      ring

end Soundness

private def rowStep (p k : ℕ) (a b : List ℕ) : List ℕ :=
  let plus := addVec p (0::b) (scaleVec p (2*(k+1)*(k+2)) b ++ [0])
  let minus := scaleVec p ((k+1)^4) a ++ [0,0]
  subVec p plus minus

private def rowPair (p : ℕ) : ℕ → List ℕ × List ℕ
  | 0 => ([1], [0,1])
  | k+1 =>
    let prior := rowPair p k
    (prior.2, rowStep p k prior.1 prior.2)

private theorem subSmall {p : ℕ} (hp : 0<p) (a b : List ℕ) :
    ∀ t ∈ subVec p a b, t < p := by
  induction a generalizing b with
  | nil => simp [subVec]
  | cons h t ih =>
    cases b with
    | nil => simp [subVec]
    | cons e s =>
      intro z hz
      simp only [subVec, List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Nat.mod_lt _ hp
      · exact ih _ _ hz

private theorem polyChar (p : ℕ) : (p : (ZMod p)[X]) = 0 := by
  rw [← C_eq_natCast, ZMod.natCast_self, C_0]

private theorem stepLen (p k : ℕ) (a b : List ℕ) (ha : a.length=k+1) (hb : b.length=k+2) :
    (rowStep p k a b).length=k+3 := by
  simp [rowStep, subVec, addVec, scaleVec, List.length_zipWith, ha, hb]

private theorem stepEval {p : ℕ} (hp : 0<p) (k : ℕ) (a b : List ℕ)
    (ha : a.length=k+1) (hb : b.length=k+2) :
    evalVec (X : (ZMod p)[X]) (rowStep p k a b) =
      (X + ((2*(k+1)*(k+2) : ℕ) : (ZMod p)[X])) * evalVec X b -
        (((k+1)^4:ℕ) : (ZMod p)[X]) * evalVec X a := by
  let x : (ZMod p)[X] := X
  let c := 2*(k+1)*(k+2)
  let d := (k+1)^4
  have hplus : (0::b).length = (scaleVec p c b ++ [0]).length := by simp [scaleVec]
  have hsub : (addVec p (0::b) (scaleVec p c b ++ [0])).length =
      (scaleVec p d a ++ [0,0]).length := by
    simp [addVec, scaleVec, List.length_zipWith, ha, hb]
  change evalVec x (subVec p (addVec p (0::b) (scaleVec p c b ++[0])) (scaleVec p d a ++[0,0])) = _
  rw [evalSub (polyChar p) hp _ _ _ hsub, evalAdd (polyChar p) _ _ _ hplus,
    evalAppend, evalAppend, evalScale (polyChar p), evalScale (polyChar p)]
  simp only [evalVec, Nat.cast_zero, mul_zero, add_zero, zero_add]
  change x*evalVec x b + (c : (ZMod p)[X])*evalVec x b - (d : (ZMod p)[X])*evalVec x a =
    (x + (c : (ZMod p)[X]))*evalVec x b - (d : (ZMod p)[X])*evalVec x a
  rw [add_mul]

private theorem rowSpec {p : ℕ} (hp : 1<p) (k : ℕ) :
    (rowPair p k).1.length=k+1 ∧ (rowPair p k).2.length=k+2 ∧
      (∀ t ∈ (rowPair p k).1, t<p) ∧ (∀ t ∈ (rowPair p k).2, t<p) ∧
      evalVec (X : (ZMod p)[X]) (rowPair p k).1 = (OeisA217703.polyS k).map (Int.castRingHom (ZMod p)) ∧
      evalVec (X : (ZMod p)[X]) (rowPair p k).2 = (OeisA217703.polyS (k+1)).map (Int.castRingHom (ZMod p)) := by
  induction k with
  | zero =>
    simp [rowPair, evalVec, OeisA217703.polyS, hp, show 0<p by omega]
  | succ k ih =>
    obtain ⟨h₀,h₁,hsmall₀,hsmall₁,he₀,he₁⟩ := ih
    let a := (rowPair p k).1
    let b := (rowPair p k).2
    change b.length=k+1+1 ∧ (rowStep p k a b).length=k+1+2 ∧
      (∀ t ∈ b, t<p) ∧ (∀ t ∈ rowStep p k a b, t<p) ∧
      evalVec (X : (ZMod p)[X]) b = (OeisA217703.polyS (k+1)).map _ ∧ _
    refine ⟨h₁, stepLen p k a b h₀ h₁, hsmall₁, subSmall (by omega : 0<p) _ _, he₁, ?_⟩
    change evalVec (X : (ZMod p)[X]) (rowStep p k a b) = _
    rw [stepEval (by omega : 0<p) k a b h₀ h₁]
    change (X + ((2*(k+1)*(k+2) : ℕ) : (ZMod p)[X])) *
       evalVec (X : (ZMod p)[X]) (rowPair p k).2 -
      (((k+1)^4:ℕ):(ZMod p)[X]) * evalVec (X : (ZMod p)[X]) (rowPair p k).1 = _
    rw [he₀,he₁]
    rw [show (k+1)+1 = k+2 by omega, OeisA217703.polyS]
    have hc : ((2*(k+1)*(k+2):ℕ):ℤ) = 2*((k:ℤ)+1)*(((k:ℤ)+1)+1) := by
      push_cast <;> ring
    have hd : (((k+1)^4:ℕ):ℤ) = ((k:ℤ)+1)^4 := by push_cast <;> rfl
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
      ← hc, ← hd, C_eq_natCast, Polynomial.map_natCast]

end OMA.CoefficientRows

namespace OMA.PrimeCertificate

def primeTest (q : ℕ) : Bool :=
  if q ≤ 56 then decide q.Prime else decide (q < 3249 ∧ q.Coprime (Nat.factorial 56))

theorem primeTest_sound {q : ℕ} (h : primeTest q = true) : q.Prime := by
  unfold primeTest at h
  split at h
  · exact of_decide_eq_true h
  · rename_i hsmall
    obtain ⟨hu, hc⟩ := of_decide_eq_true h
    by_contra hprime
    let p := q.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hs : p^2 ≤ q := Nat.minFac_sq_le_self (by omega) hprime
    have hlim : p ≤ 56 := by
      by_contra! hgt
      have hn : (57 : ℕ)^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hcommon : p ∣ Nat.gcd q (Nat.factorial 56) :=
      Nat.dvd_gcd (Nat.minFac_dvd _) (Nat.dvd_factorial hp.pos hlim)
    have hg : Nat.gcd q (Nat.factorial 56) = 1 := hc
    rw [hg] at hcommon
    have := hp.two_le
    have := Nat.dvd_one.mp hcommon
    omega

end OMA.PrimeCertificate

namespace OMA.PolynomialCertificate
open Polynomial Finset
open OMA.SmallFactors OMA.RadixPolynomial OMA.CheckedPackedArithmetic OMA.CoefficientRows

private def packList : List ℕ → ℕ
  | [] => 0
  | a::as => a+radix*packList as

private abbrev checkCoefficients (p n f : ℕ) : Prop :=
  packList (rowPair p (n-1)).2 = power n + f

private theorem decodedSmall (b n v : ℕ) (hb : 0<b) (j : ℕ) :
    (decode b n v).coeff j < b := by
  induction n generalizing v j with
  | zero => simp [decode,hb]
  | succ n ih =>
    cases j with
    | zero => simpa [decode,coeff_add,coeff_X_mul] using Nat.mod_lt v hb
    | succ j => simpa [decode,coeff_add,coeff_X_mul] using ih (v/b) j

private theorem topDecode (n f : ℕ) (hf : f < radix^n) :
    decode radix (n+1) (power n+f) = X^n + decode radix n f := by
  have h2 : 2 ≤ radix := by decide
  have hsum : power n+f < radix^(n+1) := by
    rw [power_eq, pow_succ]
    have hle := Nat.mul_le_mul_left (radix^n) h2
    omega
  apply eqOfEval radix_pos
  · exact decodedSmall _ _ _ radix_pos
  · intro j
    by_cases hj : j=n
    · subst j
      simp [coeff_add, coeff_X_pow, decode_zero radix n f n le_rfl, show 1<radix by decide]
    · simpa [coeff_add, coeff_X_pow, hj] using decodedSmall radix n f radix_pos j
  · rw [evalDecode _ _ _ radix_pos hsum, eval_add, eval_pow, eval_X,
      evalDecode _ _ _ radix_pos hf, power_eq]

private theorem listDecode (p : ℕ) (as : List ℕ) (h : ∀ a ∈ as, a<radix) :
    (decode radix as.length (packList as)).map (Nat.castRingHom (ZMod p)) =
      evalVec (X : (ZMod p)[X]) as := by
  induction as with
  | nil => simp [decode, packList, evalVec]
  | cons a as ih =>
    have h1 := h a (by simp)
    have ht : ∀ b ∈ as, b < radix := fun b hb => h b (by simp [hb])
    simp only [List.length_cons, packList, decodeHead radix_pos h1, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, ih ht, evalVec,
      Nat.coe_castRingHom, C_eq_natCast]

private theorem coefficientSound {p n f : ℕ} (hp : 1<p) (hn : 0<n)
    (hfit : 2*n*p^2+p+p*16777216<radix)
    (hf : digitCheck radix p n f=true) (hc : checkCoefficients p n f) :
    (X^n+decode radix n f).map (Nat.castRingHom (ZMod p)) =
      (OeisA217703.polyS n).map (Int.castRingHom (ZMod p)) := by
  let a := (rowPair p (n-1)).2
  have hrows := rowSpec hp (n-1)
  have hal : a.length=n+1 := by
    change (rowPair p (n-1)).2.length=n+1
    rw [hrows.2.1]
    omega
  have hac : ∀ j ∈ a, j<radix := by
    intro j hj
    exact (hrows.2.2.2.1 j hj).trans_le (by omega)
  change packList a = power n+f at hc
  have hd := listDecode p a hac
  rw [hal,hc,topDecode n f (digitCheck_sound radix p n f radix_pos (by omega) hf).1] at hd
  rw [hd]
  have hh := hrows.2.2.2.2.2
  rw [show n-1+1=n by omega] at hh
  exact hh

private theorem certificate {p n f inv : ℕ}
    (h : p.Prime ∧ 0<n ∧ 2*n*p^2+p+p*16777216<radix ∧
      digitCheck radix p n f=true ∧
      digitCheck radix (16777216) (2*n-1) (fill (2*n-1) (n*p))=true ∧
      digitCheck radix p n inv=true ∧ checkCoefficients p n f ∧ checkInv p n f inv=true) :
    Irreducible ((OeisA217703.polyS n).map (Int.castRingHom ℚ)) := by
  obtain ⟨hp,hn,hfit,hf,hpad,hi,hc,hnum⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let F := (OeisA217703.polyS n).map (Int.castRingHom (ZMod p))
  let I : Ideal (ZMod p)[X] := Ideal.span {F}
  let q := Ideal.Quotient.mk I
  let m := Polynomial.mapRingHom (Nat.castRingHom (ZMod p))
  let g := q.comp m
  have hF0 : q F = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hgF : g (X^n+decode radix n f)=0 := by
    change q ((X^n+decode radix n f).map (Nat.castRingHom (ZMod p)))=0
    rw [coefficientSound hp.one_lt hn hfit hf hc]
    exact hF0
  have hchar : g (C p)=0 := by
    change q ((C p).map (Nat.castRingHom (ZMod p)))=0
    rw [Polynomial.map_C]
    change q (C (p:ZMod p))=0
    rw [ZMod.natCast_self, C_0, map_zero]
  have hnF : F.natDegree=n := ((polyS_monic_degree n).1.natDegree_map _).trans (polyS_monic_degree n).2
  have hprod := checkedInverse g hn hp.one_lt hfit hf hpad hi hchar hgF hnum
  let v := (decode radix n inv).map (Nat.castRingHom (ZMod p))
  have hx : g X = q X := by
    change q ((X : ℕ[X]).map (Nat.castRingHom (ZMod p))) = q X
    rw [Polynomial.map_X]
  have he : q (v * (∏ d ∈ Icc 1 (F.natDegree/2), ((X : (ZMod p)[X])^(Nat.card (ZMod p))^d-X)) -1)=0 := by
    simp only [hnF, Nat.card_zmod, map_sub, map_one, map_mul, map_prod, map_pow]
    rw [← hx]
    change g (decode radix n inv) * (∏ d ∈ Icc 1 (n/2), ((g X)^(p^d)-g X)) -1=0
    rw [hprod, sub_self]
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  exact transferMod hp (irreducible_of_product_inverse (by omega : 0<F.natDegree) v hd)

private theorem certificateWithPrimeTest {p n f inv : ℕ}
    (prime : OMA.PrimeCertificate.primeTest p=true)
    (h : 0<n ∧ 2*n*p^2+p+p*16777216<radix ∧
      digitCheck radix p n f=true ∧
      digitCheck radix (16777216) (2*n-1) (fill (2*n-1) (n*p))=true ∧
      digitCheck radix p n inv=true ∧ checkCoefficients p n f ∧ checkInv p n f inv=true) :
    Irreducible ((OeisA217703.polyS n).map (Int.castRingHom ℚ)) := by
  exact certificate ⟨OMA.PrimeCertificate.primeTest_sound prime,h⟩

end OMA.PolynomialCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree001 : PLift (Irreducible ((OeisA217703.polyS 1).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 2) (f := 0x0)
    (inv := 0x1) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree002 : PLift (Irreducible ((OeisA217703.polyS 2).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 3) (f := 0x10000000000000002)
    (inv := 0x20000000000000001) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree003 : PLift (Irreducible ((OeisA217703.polyS 3).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 5) (f := 0x100000000000000010000000000000003)
    (inv := 0x200000000000000000000000000000003) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree004 : PLift (Irreducible ((OeisA217703.polyS 4).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 7) (f := 0x5000000000000000500000000000000020000000000000003)
    (inv := 0x4000000000000000600000000000000010000000000000005) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree005 : PLift (Irreducible ((OeisA217703.polyS 5).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 37) (f := 0x6000000000000000d000000000000000f00000000000000000000000000000009)
    (inv := 0x100000000000000020000000000000019000000000000001c000000000000000c) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree006 : PLift (Irreducible ((OeisA217703.polyS 6).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 19) (f := 0x700000000000000010000000000000004000000000000000d00000000000000120000000000000011)
    (inv := 0x12000000000000000e0000000000000000000000000000000f000000000000000f0000000000000010) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree007 : PLift (Irreducible ((OeisA217703.polyS 7).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 19) (f := 0xf000000000000000f000000000000000f000000000000000200000000000000040000000000000000000000000000000b)
    (inv := 0x1000000000000000600000000000000010000000000000011000000000000000800000000000000110000000000000003) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree008 : PLift (Irreducible ((OeisA217703.polyS 8).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 61) (f := 0x1f0000000000000019000000000000000000000000000000260000000000000006000000000000001c000000000000002a000000000000000d)
    (inv := 0x310000000000000002000000000000002b000000000000001700000000000000140000000000000011000000000000003a000000000000000d) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree009 : PLift (Irreducible ((OeisA217703.polyS 9).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 13) (f := 0xc0000000000000001000000000000000c000000000000000a0000000000000004000000000000000c0000000000000009000000000000000b000000000000000a)
    (inv := 0x10000000000000006000000000000000a000000000000000a000000000000000c0000000000000003000000000000000c00000000000000010000000000000006) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree010 : PLift (Irreducible ((OeisA217703.polyS 10).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 13) (f := 0xa00000000000000070000000000000002000000000000000200000000000000020000000000000008000000000000000c000000000000000600000000000000030000000000000009)
    (inv := 0x2000000000000000c000000000000000c000000000000000c0000000000000002000000000000000a000000000000000900000000000000030000000000000009) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree011 : PLift (Irreducible ((OeisA217703.polyS 11).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 67) (f := 0x9000000000000002f0000000000000041000000000000001200000000000000050000000000000010000000000000001f0000000000000004000000000000002000000000000000020000000000000034)
    (inv := 0x420000000000000011000000000000001a00000000000000040000000000000038000000000000003d000000000000002a00000000000000400000000000000014000000000000002b0000000000000016) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree012 : PLift (Irreducible ((OeisA217703.polyS 12).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 19) (f := 0x40000000000000008000000000000000a000000000000000f00000000000000040000000000000004000000000000000b00000000000000090000000000000003000000000000000d0000000000000006000000000000000c)
    (inv := 0x40000000000000007000000000000000c000000000000000700000000000000120000000000000000000000000000000a000000000000000d0000000000000007000000000000000a00000000000000000000000000000001) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree013 : PLift (Irreducible ((OeisA217703.polyS 13).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 101) (f := 0x2a0000000000000041000000000000002b000000000000002f0000000000000024000000000000005d0000000000000027000000000000003f00000000000000200000000000000043000000000000002f000000000000005a000000000000004b)
    (inv := 0x36000000000000005d0000000000000001000000000000002900000000000000570000000000000005000000000000005a000000000000005100000000000000620000000000000029000000000000001c0000000000000043000000000000000e) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree014 : PLift (Irreducible ((OeisA217703.polyS 14).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 17) (f := 0x100000000000000000000000000000006000000000000000e00000000000000040000000000000010000000000000000c000000000000000a00000000000000050000000000000001000000000000000000000000000000010000000000000000000000000000000a)
    (inv := 0x100000000000000002000000000000000500000000000000030000000000000004000000000000000e0000000000000000000000000000000c000000000000000700000000000000060000000000000009000000000000000700000000000000050000000000000004) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree015 : PLift (Irreducible ((OeisA217703.polyS 15).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 163) (f := 0x790000000000000037000000000000000d000000000000005e00000000000000230000000000000055000000000000008c0000000000000029000000000000005900000000000000310000000000000011000000000000006200000000000000650000000000000088000000000000005b)
    (inv := 0x4c0000000000000006000000000000004a00000000000000310000000000000006000000000000009e000000000000000c000000000000001e000000000000004f000000000000000e0000000000000033000000000000004d000000000000000700000000000000360000000000000035) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree016 : PLift (Irreducible ((OeisA217703.polyS 16).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 181) (f := 0x50000000000000022000000000000007400000000000000750000000000000097000000000000004e0000000000000043000000000000005f0000000000000092000000000000003c000000000000008f000000000000006a000000000000004f000000000000003300000000000000270000000000000057)
    (inv := 0x3e00000000000000b1000000000000008100000000000000750000000000000025000000000000006e000000000000008b00000000000000310000000000000009000000000000004300000000000000420000000000000077000000000000000a0000000000000018000000000000002a000000000000001f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree017 : PLift (Irreducible ((OeisA217703.polyS 17).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 239) (f := 0x9d0000000000000021000000000000006f00000000000000580000000000000054000000000000000400000000000000ad0000000000000006000000000000005c00000000000000c5000000000000008d0000000000000084000000000000004400000000000000cd000000000000004a000000000000007900000000000000ac)
    (inv := 0xf000000000000002600000000000000a3000000000000000600000000000000240000000000000094000000000000006c000000000000009900000000000000d800000000000000ad00000000000000c80000000000000005000000000000000a000000000000004600000000000000e4000000000000009f0000000000000001) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree018 : PLift (Irreducible ((OeisA217703.polyS 18).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 89) (f := 0x31000000000000004e0000000000000045000000000000002700000000000000320000000000000050000000000000002300000000000000100000000000000055000000000000001100000000000000410000000000000023000000000000003200000000000000480000000000000033000000000000004700000000000000480000000000000035)
    (inv := 0x2a000000000000002b00000000000000060000000000000055000000000000001e000000000000003d00000000000000580000000000000020000000000000000800000000000000410000000000000024000000000000001f0000000000000049000000000000004a0000000000000054000000000000003d00000000000000350000000000000050) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree019 : PLift (Irreducible ((OeisA217703.polyS 19).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 43) (f := 0x2000000000000000b000000000000001400000000000000210000000000000026000000000000001f00000000000000240000000000000022000000000000002800000000000000280000000000000006000000000000000c000000000000001b000000000000000c0000000000000007000000000000000f000000000000001d000000000000000c0000000000000015)
    (inv := 0x280000000000000020000000000000000f000000000000001b00000000000000140000000000000027000000000000000000000000000000260000000000000010000000000000000e000000000000000f0000000000000016000000000000002a000000000000000f000000000000001400000000000000110000000000000009000000000000000f000000000000000a) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree020 : PLift (Irreducible ((OeisA217703.polyS 20).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 31) (f := 0x13000000000000000b000000000000001a0000000000000007000000000000000a0000000000000001000000000000000a00000000000000130000000000000003000000000000000600000000000000170000000000000007000000000000000c000000000000000a000000000000000b000000000000000a0000000000000018000000000000001400000000000000070000000000000013)
    (inv := 0xb000000000000000400000000000000150000000000000019000000000000001b0000000000000001000000000000000800000000000000030000000000000004000000000000000a00000000000000070000000000000011000000000000001700000000000000180000000000000005000000000000000200000000000000100000000000000010000000000000001a0000000000000015) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree021 : PLift (Irreducible ((OeisA217703.polyS 21).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 59) (f := 0x1800000000000000020000000000000015000000000000000700000000000000070000000000000004000000000000002300000000000000000000000000000027000000000000003100000000000000040000000000000036000000000000001a0000000000000001000000000000000700000000000000230000000000000036000000000000002d00000000000000280000000000000025000000000000001c)
    (inv := 0x1a00000000000000140000000000000003000000000000002c0000000000000039000000000000000c0000000000000008000000000000001e00000000000000170000000000000010000000000000000f000000000000001c00000000000000040000000000000007000000000000001e0000000000000037000000000000000a0000000000000036000000000000000a000000000000001d000000000000001d) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree022 : PLift (Irreducible ((OeisA217703.polyS 22).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 97) (f := 0x3000000000000002c000000000000000800000000000000200000000000000005000000000000000e0000000000000022000000000000002c000000000000003600000000000000360000000000000057000000000000004f0000000000000011000000000000004b0000000000000022000000000000000b000000000000002c000000000000004e0000000000000031000000000000003100000000000000290000000000000026)
    (inv := 0x2d0000000000000024000000000000003b0000000000000053000000000000000a0000000000000048000000000000004f0000000000000057000000000000005000000000000000160000000000000059000000000000001f0000000000000039000000000000001b000000000000001c0000000000000045000000000000005f000000000000000f0000000000000015000000000000005200000000000000220000000000000036) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree023 : PLift (Irreducible ((OeisA217703.polyS 23).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 41) (f := 0x1300000000000000000000000000000027000000000000000b00000000000000100000000000000016000000000000000e000000000000000d000000000000001f000000000000000c000000000000001e000000000000001d0000000000000021000000000000001500000000000000110000000000000013000000000000001d000000000000001a000000000000001c00000000000000120000000000000001000000000000000d0000000000000001)
    (inv := 0x16000000000000001f0000000000000000000000000000001d0000000000000003000000000000001f00000000000000100000000000000018000000000000001000000000000000260000000000000026000000000000000a000000000000002100000000000000240000000000000010000000000000000c0000000000000008000000000000001400000000000000060000000000000014000000000000001b0000000000000026000000000000001f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree024 : PLift (Irreducible ((OeisA217703.polyS 24).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 31) (f := 0x1800000000000000150000000000000016000000000000001d000000000000001d000000000000001700000000000000080000000000000016000000000000000f00000000000000000000000000000003000000000000001b00000000000000110000000000000005000000000000000f000000000000001e00000000000000040000000000000002000000000000000a0000000000000019000000000000000e000000000000000300000000000000030000000000000008)
    (inv := 0x1b000000000000000d000000000000001d0000000000000001000000000000000600000000000000100000000000000019000000000000000c00000000000000010000000000000013000000000000001d00000000000000070000000000000008000000000000000a0000000000000018000000000000001900000000000000110000000000000016000000000000001d000000000000001900000000000000050000000000000016000000000000000e0000000000000013) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree025 : PLift (Irreducible ((OeisA217703.polyS 25).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 29) (f := 0x12000000000000000e000000000000000a000000000000000900000000000000110000000000000002000000000000000a0000000000000011000000000000000d0000000000000016000000000000000000000000000000100000000000000019000000000000000400000000000000080000000000000000000000000000001b00000000000000050000000000000016000000000000000e00000000000000120000000000000017000000000000001700000000000000180000000000000002)
    (inv := 0x100000000000000008000000000000001200000000000000040000000000000008000000000000000a000000000000000b00000000000000030000000000000011000000000000001a000000000000000e000000000000001200000000000000000000000000000017000000000000001600000000000000100000000000000011000000000000000b000000000000001900000000000000080000000000000011000000000000000d000000000000001c0000000000000005) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree026 : PLift (Irreducible ((OeisA217703.polyS 26).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 127) (f := 0x10000000000000005c00000000000000160000000000000030000000000000007600000000000000670000000000000058000000000000004c0000000000000019000000000000004500000000000000040000000000000074000000000000004f000000000000001000000000000000700000000000000066000000000000003b0000000000000023000000000000001f0000000000000062000000000000003c000000000000003900000000000000040000000000000026000000000000000e000000000000007b)
    (inv := 0x49000000000000004200000000000000280000000000000072000000000000001a0000000000000070000000000000005b00000000000000420000000000000060000000000000001e000000000000001d00000000000000550000000000000061000000000000003d000000000000002a0000000000000036000000000000003200000000000000780000000000000079000000000000007c000000000000005c000000000000006000000000000000190000000000000055000000000000001f0000000000000060) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree027 : PLift (Irreducible ((OeisA217703.polyS 27).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 179) (f := 0x25000000000000005d0000000000000035000000000000001e000000000000009b000000000000003b000000000000008c00000000000000100000000000000072000000000000008200000000000000a300000000000000110000000000000003000000000000005800000000000000a2000000000000008a000000000000004f00000000000000a500000000000000500000000000000079000000000000002a000000000000000f00000000000000490000000000000093000000000000000f000000000000009e000000000000004e)
    (inv := 0x26000000000000009000000000000000a9000000000000001e0000000000000020000000000000001e0000000000000039000000000000003d00000000000000ae000000000000007300000000000000a30000000000000067000000000000001b000000000000001100000000000000a0000000000000001d000000000000008d0000000000000083000000000000006700000000000000510000000000000017000000000000009600000000000000a400000000000000aa00000000000000340000000000000090000000000000004f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree028 : PLift (Irreducible ((OeisA217703.polyS 28).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 59) (f := 0x2b0000000000000014000000000000002e00000000000000330000000000000028000000000000000e0000000000000034000000000000000400000000000000000000000000000021000000000000000f000000000000002c0000000000000030000000000000000a0000000000000002000000000000001e000000000000001a000000000000003400000000000000100000000000000027000000000000002e0000000000000022000000000000002c000000000000002a000000000000001600000000000000210000000000000024000000000000002e)
    (inv := 0x190000000000000017000000000000001d0000000000000000000000000000002f000000000000000d000000000000002c000000000000002b000000000000003a000000000000000f000000000000002b000000000000002b00000000000000250000000000000011000000000000000e000000000000001f000000000000000d0000000000000028000000000000002f000000000000003100000000000000220000000000000004000000000000000c0000000000000031000000000000001c00000000000000360000000000000004000000000000000b) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree029 : PLift (Irreducible ((OeisA217703.polyS 29).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 43) (f := 0x1d000000000000000d0000000000000010000000000000000800000000000000230000000000000018000000000000001e000000000000001400000000000000010000000000000008000000000000000200000000000000220000000000000012000000000000001400000000000000070000000000000021000000000000000000000000000000130000000000000013000000000000000c0000000000000023000000000000000d000000000000001100000000000000190000000000000029000000000000001e000000000000001e000000000000000b0000000000000019)
    (inv := 0x2000000000000000e0000000000000021000000000000000d000000000000001d0000000000000027000000000000001700000000000000160000000000000019000000000000001f000000000000001a0000000000000015000000000000001f000000000000002700000000000000270000000000000019000000000000000f00000000000000220000000000000017000000000000000a0000000000000029000000000000000b0000000000000015000000000000001b00000000000000280000000000000014000000000000000f0000000000000019000000000000000f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree030 : PLift (Irreducible ((OeisA217703.polyS 30).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 151) (f := 0xb000000000000002b00000000000000890000000000000053000000000000006b0000000000000094000000000000003f000000000000006f00000000000000920000000000000081000000000000003d0000000000000053000000000000001d00000000000000820000000000000096000000000000003d0000000000000012000000000000001c000000000000002e00000000000000380000000000000080000000000000001400000000000000410000000000000061000000000000000b0000000000000033000000000000006a0000000000000024000000000000002f000000000000003c)
    (inv := 0x6000000000000000460000000000000063000000000000000e000000000000000300000000000000300000000000000056000000000000003e000000000000004c000000000000007a0000000000000027000000000000001d0000000000000001000000000000000900000000000000860000000000000067000000000000005e00000000000000550000000000000017000000000000005300000000000000840000000000000078000000000000006e0000000000000009000000000000000c00000000000000810000000000000031000000000000005100000000000000260000000000000006) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree031 : PLift (Irreducible ((OeisA217703.polyS 31).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 97) (f := 0x34000000000000000c0000000000000005000000000000004e0000000000000012000000000000001e000000000000004d00000000000000180000000000000013000000000000001300000000000000030000000000000029000000000000002c000000000000004e000000000000003300000000000000460000000000000019000000000000005c000000000000000b000000000000001c0000000000000047000000000000002d000000000000002600000000000000360000000000000057000000000000003b00000000000000140000000000000036000000000000000a0000000000000058000000000000002e)
    (inv := 0x1d0000000000000041000000000000003300000000000000000000000000000051000000000000001a000000000000000b000000000000004c000000000000004c000000000000000f000000000000004a000000000000005a000000000000004a000000000000004f000000000000001100000000000000440000000000000012000000000000005e000000000000002f0000000000000055000000000000005800000000000000330000000000000013000000000000005a0000000000000047000000000000005800000000000000050000000000000018000000000000004b000000000000005d0000000000000025) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree032 : PLift (Irreducible ((OeisA217703.polyS 32).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 229) (f := 0x45000000000000006f0000000000000071000000000000007b000000000000003f00000000000000ab00000000000000af0000000000000048000000000000001f0000000000000048000000000000000b00000000000000720000000000000019000000000000009a000000000000000d000000000000003900000000000000b9000000000000000d00000000000000c600000000000000c000000000000000d6000000000000008300000000000000c6000000000000004200000000000000cc0000000000000078000000000000000f00000000000000050000000000000006000000000000007500000000000000c10000000000000001)
    (inv := 0x820000000000000099000000000000005f00000000000000e3000000000000003d00000000000000ad000000000000000100000000000000a10000000000000033000000000000008f00000000000000bb000000000000001f00000000000000540000000000000080000000000000009f00000000000000df000000000000003300000000000000e0000000000000001400000000000000d8000000000000007f00000000000000450000000000000039000000000000004b00000000000000d7000000000000005e00000000000000bf000000000000006500000000000000d8000000000000008c00000000000000d500000000000000a6) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree033 : PLift (Irreducible ((OeisA217703.polyS 33).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 239) (f := 0x2400000000000000e5000000000000000800000000000000c700000000000000b1000000000000005d00000000000000ae000000000000007800000000000000140000000000000028000000000000004d00000000000000c3000000000000006a00000000000000680000000000000003000000000000002500000000000000db0000000000000046000000000000009a00000000000000b100000000000000190000000000000045000000000000002f00000000000000d700000000000000c100000000000000130000000000000008000000000000006500000000000000c700000000000000700000000000000028000000000000003d0000000000000062)
    (inv := 0x51000000000000000f00000000000000e3000000000000000d000000000000002600000000000000cf0000000000000006000000000000001300000000000000cb00000000000000c7000000000000009400000000000000bb00000000000000440000000000000074000000000000006a0000000000000038000000000000009e0000000000000054000000000000006d000000000000000500000000000000e800000000000000c900000000000000c0000000000000001e000000000000009200000000000000ee000000000000009000000000000000bc000000000000004400000000000000a1000000000000004d000000000000001f00000000000000a3) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree034 : PLift (Irreducible ((OeisA217703.polyS 34).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 157) (f := 0x7600000000000000040000000000000056000000000000004d000000000000004500000000000000480000000000000000000000000000007d000000000000007d0000000000000037000000000000002c0000000000000068000000000000009c000000000000000d000000000000008c0000000000000045000000000000001d000000000000004c000000000000007c000000000000003f000000000000007b0000000000000088000000000000003200000000000000320000000000000018000000000000001700000000000000090000000000000030000000000000004a000000000000009c0000000000000089000000000000001c000000000000009a0000000000000001)
    (inv := 0x2d000000000000002b00000000000000940000000000000004000000000000007d00000000000000660000000000000036000000000000008a000000000000001e00000000000000100000000000000030000000000000007b00000000000000120000000000000091000000000000000c00000000000000980000000000000094000000000000004c000000000000009c00000000000000390000000000000012000000000000004600000000000000850000000000000051000000000000008b0000000000000029000000000000002b0000000000000025000000000000002800000000000000580000000000000023000000000000009600000000000000840000000000000098) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree035 : PLift (Irreducible ((OeisA217703.polyS 35).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 137) (f := 0x40000000000000001200000000000000800000000000000017000000000000001f0000000000000018000000000000003f000000000000001c00000000000000720000000000000078000000000000006900000000000000670000000000000055000000000000004c0000000000000084000000000000001d000000000000007300000000000000050000000000000016000000000000004300000000000000400000000000000054000000000000007d000000000000002500000000000000460000000000000053000000000000006b000000000000007a00000000000000390000000000000023000000000000000d000000000000004f000000000000006800000000000000030000000000000083)
    (inv := 0x86000000000000007f000000000000005a000000000000003f000000000000003b000000000000002400000000000000760000000000000021000000000000003f0000000000000015000000000000004a000000000000004d000000000000007900000000000000330000000000000051000000000000005c000000000000002a0000000000000045000000000000002d000000000000005f000000000000006f000000000000002e00000000000000560000000000000069000000000000005b000000000000006500000000000000030000000000000027000000000000007c0000000000000034000000000000006e0000000000000062000000000000005800000000000000680000000000000006) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree036 : PLift (Irreducible ((OeisA217703.polyS 36).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 311) (f := 0x123000000000000012d0000000000000058000000000000010900000000000000ba000000000000005c000000000000003f00000000000001300000000000000037000000000000003200000000000000a800000000000000bc000000000000003e000000000000006500000000000000bb000000000000009d00000000000000c700000000000000e500000000000000b000000000000000b400000000000000b10000000000000011000000000000002900000000000000bf000000000000000a00000000000000b4000000000000004f000000000000012c0000000000000072000000000000005400000000000000ad000000000000010800000000000000c2000000000000000500000000000000160000000000000046)
    (inv := 0x2e000000000000001900000000000000030000000000000032000000000000002c00000000000000fe0000000000000093000000000000007400000000000000bd00000000000000f30000000000000131000000000000004d000000000000007e000000000000012d000000000000007f00000000000000ec000000000000006100000000000001090000000000000012000000000000000d00000000000000c900000000000000dd0000000000000054000000000000012f0000000000000087000000000000009d0000000000000051000000000000008c000000000000010e000000000000003700000000000001310000000000000023000000000000006e00000000000000b3000000000000003900000000000000a2) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree037 : PLift (Irreducible ((OeisA217703.polyS 37).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 67) (f := 0x2b0000000000000035000000000000002f00000000000000260000000000000034000000000000001400000000000000390000000000000017000000000000002a0000000000000017000000000000000200000000000000350000000000000027000000000000001a000000000000000d0000000000000023000000000000001f000000000000001c000000000000000a000000000000002e0000000000000028000000000000002c000000000000003e000000000000000c000000000000004200000000000000310000000000000020000000000000003f000000000000000d000000000000001d000000000000001f0000000000000018000000000000002000000000000000020000000000000037000000000000000b000000000000003e)
    (inv := 0x29000000000000001e000000000000002e00000000000000170000000000000042000000000000001d000000000000003f0000000000000038000000000000002400000000000000300000000000000008000000000000002600000000000000380000000000000004000000000000000b00000000000000170000000000000032000000000000002a000000000000003c00000000000000130000000000000021000000000000000f000000000000002c000000000000003000000000000000240000000000000003000000000000000600000000000000090000000000000010000000000000000f00000000000000200000000000000013000000000000001c000000000000003900000000000000270000000000000002000000000000000f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree038 : PLift (Irreducible ((OeisA217703.polyS 38).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 43) (f := 0x6000000000000000f0000000000000017000000000000001d000000000000000300000000000000080000000000000001000000000000002500000000000000270000000000000001000000000000000a00000000000000030000000000000026000000000000000a000000000000000100000000000000050000000000000001000000000000000c0000000000000027000000000000001300000000000000270000000000000009000000000000000f000000000000000b000000000000000c000000000000002a00000000000000090000000000000009000000000000002300000000000000110000000000000021000000000000001b000000000000000200000000000000170000000000000006000000000000000d0000000000000009000000000000001c)
    (inv := 0x2100000000000000000000000000000005000000000000000400000000000000160000000000000010000000000000000e0000000000000027000000000000002400000000000000150000000000000001000000000000001a00000000000000200000000000000018000000000000001e00000000000000140000000000000006000000000000000e000000000000000e0000000000000015000000000000001d0000000000000017000000000000000300000000000000210000000000000029000000000000001d0000000000000002000000000000001b000000000000000e000000000000000000000000000000220000000000000017000000000000001400000000000000160000000000000002000000000000000e00000000000000020000000000000028) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree039 : PLift (Irreducible ((OeisA217703.polyS 39).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 53) (f := 0x23000000000000002d000000000000002b000000000000001900000000000000280000000000000027000000000000002f000000000000000500000000000000310000000000000025000000000000001200000000000000120000000000000027000000000000001500000000000000310000000000000005000000000000002a000000000000001c0000000000000024000000000000000c000000000000002d0000000000000017000000000000001a000000000000000c000000000000001e00000000000000270000000000000004000000000000001d000000000000001800000000000000330000000000000026000000000000002e000000000000000d000000000000001c000000000000002700000000000000260000000000000025000000000000000d0000000000000001)
    (inv := 0xf00000000000000040000000000000015000000000000001400000000000000030000000000000014000000000000002f00000000000000260000000000000012000000000000002d0000000000000034000000000000001e000000000000001d0000000000000034000000000000001200000000000000290000000000000004000000000000001b0000000000000015000000000000000e000000000000002b0000000000000016000000000000001b000000000000000a00000000000000310000000000000022000000000000001300000000000000270000000000000005000000000000002200000000000000080000000000000007000000000000002a0000000000000001000000000000002600000000000000320000000000000009000000000000000a000000000000002b) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree040 : PLift (Irreducible ((OeisA217703.polyS 40).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 389) (f := 0xef0000000000000130000000000000008f000000000000011e000000000000014400000000000000d900000000000000f8000000000000016c00000000000000fb00000000000000d70000000000000008000000000000014e000000000000003b000000000000017e0000000000000011000000000000001700000000000000400000000000000045000000000000017700000000000000fd0000000000000022000000000000002d000000000000011c000000000000000800000000000000d100000000000001580000000000000105000000000000001f00000000000000130000000000000114000000000000003000000000000000a4000000000000017800000000000001440000000000000172000000000000010900000000000000da000000000000000a0000000000000021000000000000010a)
    (inv := 0x119000000000000011a000000000000011a00000000000000f800000000000000c5000000000000014d0000000000000037000000000000016000000000000000a8000000000000006b0000000000000142000000000000009b000000000000015f00000000000000580000000000000175000000000000003b000000000000016900000000000000db00000000000000ff000000000000012d000000000000000d000000000000003d0000000000000117000000000000000f00000000000000840000000000000055000000000000006600000000000000ec00000000000001570000000000000059000000000000009f00000000000000ef0000000000000161000000000000006300000000000000e00000000000000170000000000000013a00000000000000cf00000000000000ff000000000000001c) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree041 : PLift (Irreducible ((OeisA217703.polyS 41).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 331) (f := 0xf2000000000000002900000000000000c3000000000000011e00000000000000eb00000000000000320000000000000131000000000000002400000000000000e5000000000000011600000000000000ca00000000000000a70000000000000099000000000000006e000000000000002e0000000000000078000000000000010d000000000000008b00000000000000b5000000000000003d00000000000000c4000000000000009e00000000000000d00000000000000146000000000000011a0000000000000082000000000000007f0000000000000026000000000000004500000000000000a80000000000000093000000000000010100000000000000270000000000000116000000000000004000000000000000aa00000000000000740000000000000004000000000000002f000000000000005d0000000000000136)
    (inv := 0xc3000000000000003f000000000000008900000000000000cf00000000000001150000000000000106000000000000002100000000000000bc00000000000000b4000000000000000c000000000000012b000000000000005d00000000000000f900000000000001380000000000000098000000000000013500000000000000c700000000000000be0000000000000094000000000000002300000000000000f400000000000000b700000000000000a60000000000000020000000000000010e00000000000000f6000000000000005c00000000000000bd00000000000000e1000000000000007f00000000000000c10000000000000149000000000000007000000000000000a4000000000000005700000000000000e70000000000000050000000000000013900000000000000d500000000000000f8000000000000011b) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree042 : PLift (Irreducible ((OeisA217703.polyS 42).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 127) (f := 0x58000000000000005f000000000000007400000000000000760000000000000016000000000000003c0000000000000012000000000000001b000000000000006c000000000000004c0000000000000044000000000000005a0000000000000046000000000000000b000000000000001f000000000000005e00000000000000410000000000000021000000000000004e000000000000002d000000000000002000000000000000710000000000000070000000000000000a0000000000000046000000000000004a000000000000006c0000000000000066000000000000001b0000000000000050000000000000000a000000000000005f00000000000000140000000000000022000000000000001d000000000000001400000000000000780000000000000061000000000000005100000000000000300000000000000062000000000000007a)
    (inv := 0x1900000000000000630000000000000049000000000000000f000000000000003f00000000000000060000000000000024000000000000006c000000000000000d0000000000000014000000000000002d00000000000000140000000000000030000000000000002d0000000000000061000000000000006f0000000000000041000000000000002300000000000000560000000000000046000000000000002b000000000000001a00000000000000360000000000000015000000000000003b000000000000002e0000000000000071000000000000006600000000000000710000000000000056000000000000004200000000000000200000000000000065000000000000005d000000000000000200000000000000780000000000000051000000000000006d000000000000003b0000000000000013000000000000001d0000000000000079) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree043 : PLift (Irreducible ((OeisA217703.polyS 43).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 71) (f := 0xa00000000000000020000000000000037000000000000003d000000000000003b00000000000000180000000000000041000000000000001c000000000000002a000000000000000900000000000000030000000000000010000000000000003a0000000000000040000000000000000b00000000000000210000000000000025000000000000000200000000000000330000000000000033000000000000002a0000000000000016000000000000003800000000000000170000000000000017000000000000002800000000000000220000000000000033000000000000001f000000000000001e00000000000000430000000000000031000000000000003a00000000000000380000000000000018000000000000003b00000000000000090000000000000007000000000000002300000000000000180000000000000012000000000000000f0000000000000037)
    (inv := 0xd000000000000000f0000000000000036000000000000001b000000000000002600000000000000440000000000000043000000000000001f000000000000002a0000000000000006000000000000003900000000000000450000000000000041000000000000000a00000000000000360000000000000029000000000000002a0000000000000022000000000000002600000000000000300000000000000001000000000000003200000000000000210000000000000040000000000000003a000000000000001d000000000000000900000000000000220000000000000016000000000000003d0000000000000029000000000000003a0000000000000023000000000000001c000000000000001c0000000000000038000000000000002b0000000000000023000000000000001f000000000000003d000000000000001d000000000000003b0000000000000019) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree044 : PLift (Irreducible ((OeisA217703.polyS 44).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 277) (f := 0xfc000000000000006300000000000000c20000000000000054000000000000006800000000000000520000000000000097000000000000009c00000000000000490000000000000100000000000000001300000000000000e600000000000000ee00000000000000850000000000000029000000000000005e000000000000002500000000000000dd000000000000001200000000000000670000000000000101000000000000004400000000000000a40000000000000066000000000000008d0000000000000042000000000000002a000000000000010300000000000000ad000000000000006400000000000000c40000000000000035000000000000002500000000000000e000000000000000d20000000000000020000000000000008e0000000000000067000000000000006c000000000000003d00000000000000ae00000000000000560000000000000044000000000000005f)
    (inv := 0x7a00000000000000e200000000000000de000000000000000e0000000000000039000000000000008400000000000000bd0000000000000107000000000000006e000000000000007400000000000000b300000000000000bb00000000000000a2000000000000004700000000000000c300000000000000bd00000000000000f4000000000000005e00000000000000450000000000000016000000000000003b000000000000009e0000000000000051000000000000009700000000000000080000000000000047000000000000004a00000000000000c4000000000000006800000000000000e9000000000000007700000000000000d1000000000000006e000000000000009c00000000000000f50000000000000060000000000000000600000000000000fd00000000000000a200000000000000f40000000000000007000000000000008d00000000000000c10000000000000099) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree045 : PLift (Irreducible ((OeisA217703.polyS 45).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 151) (f := 0x1200000000000000080000000000000084000000000000007c000000000000001b0000000000000054000000000000007900000000000000470000000000000051000000000000006b00000000000000630000000000000015000000000000002a000000000000003b0000000000000053000000000000000a000000000000000100000000000000750000000000000014000000000000001200000000000000810000000000000085000000000000004800000000000000450000000000000031000000000000001a000000000000003000000000000000530000000000000020000000000000006f000000000000007a00000000000000220000000000000074000000000000000c00000000000000310000000000000000000000000000008d000000000000007b000000000000004b00000000000000450000000000000075000000000000007f00000000000000800000000000000092000000000000002c)
    (inv := 0x17000000000000002a000000000000006f0000000000000055000000000000003700000000000000010000000000000056000000000000001000000000000000230000000000000080000000000000005400000000000000500000000000000031000000000000000e000000000000005a0000000000000053000000000000005f000000000000002f000000000000009500000000000000020000000000000024000000000000008a000000000000008000000000000000700000000000000002000000000000007a000000000000002a000000000000002c0000000000000081000000000000002300000000000000690000000000000022000000000000005f00000000000000700000000000000051000000000000003500000000000000530000000000000083000000000000006f0000000000000090000000000000001f0000000000000065000000000000000c0000000000000014000000000000003a) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree046 : PLift (Irreducible ((OeisA217703.polyS 46).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 79) (f := 0x100000000000000320000000000000022000000000000000a00000000000000300000000000000014000000000000004c0000000000000039000000000000000f000000000000002e000000000000004a0000000000000025000000000000002c00000000000000140000000000000002000000000000002f0000000000000035000000000000003e000000000000000e00000000000000060000000000000028000000000000004000000000000000370000000000000019000000000000003c0000000000000037000000000000004e000000000000001c000000000000004800000000000000160000000000000008000000000000000a000000000000003c000000000000000f0000000000000031000000000000003b000000000000002d000000000000001600000000000000450000000000000020000000000000001d000000000000000f0000000000000037000000000000000c00000000000000080000000000000038)
    (inv := 0x2000000000000000390000000000000000000000000000001d00000000000000460000000000000037000000000000004a0000000000000049000000000000000d0000000000000017000000000000004d0000000000000017000000000000003b0000000000000020000000000000001200000000000000490000000000000029000000000000003b0000000000000010000000000000004b000000000000003100000000000000010000000000000048000000000000001d0000000000000034000000000000002800000000000000220000000000000006000000000000003f00000000000000190000000000000049000000000000003a000000000000001f00000000000000260000000000000018000000000000003a0000000000000011000000000000002c000000000000002e0000000000000040000000000000004e000000000000002a000000000000002f0000000000000027000000000000002f0000000000000005) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree047 : PLift (Irreducible ((OeisA217703.polyS 47).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 601) (f := 0x45000000000000009c00000000000001ac0000000000000101000000000000009b000000000000016e00000000000001a700000000000001b900000000000001c00000000000000023000000000000017c00000000000000fe00000000000001c700000000000001fb000000000000008800000000000001c20000000000000086000000000000012a0000000000000063000000000000001000000000000001cf000000000000006f00000000000000e3000000000000021b000000000000012e000000000000018d0000000000000254000000000000006b00000000000001ad000000000000001e00000000000001f500000000000002530000000000000168000000000000018600000000000000f300000000000000100000000000000090000000000000019f000000000000016d000000000000025700000000000000ac00000000000001ce00000000000001db00000000000000e7000000000000016a0000000000000230000000000000007e)
    (inv := 0x1a60000000000000070000000000000010f000000000000006e000000000000015500000000000001800000000000000199000000000000011a00000000000001c600000000000000d0000000000000022100000000000000000000000000000044000000000000023d000000000000011300000000000001cd000000000000015b00000000000000e300000000000001ee0000000000000206000000000000024300000000000000e600000000000000120000000000000103000000000000014d00000000000000a0000000000000025100000000000001bf0000000000000117000000000000012f00000000000000fe00000000000000a500000000000000bb000000000000018b000000000000010d000000000000009a00000000000000b30000000000000075000000000000001300000000000002130000000000000013000000000000002100000000000001bf00000000000000d0000000000000025200000000000000bc0000000000000018) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree048 : PLift (Irreducible ((OeisA217703.polyS 48).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 373) (f := 0xd7000000000000011f00000000000000d700000000000000040000000000000162000000000000002a000000000000014700000000000000220000000000000092000000000000000b0000000000000121000000000000002b000000000000004600000000000000c1000000000000013300000000000001380000000000000049000000000000002600000000000000c90000000000000012000000000000013400000000000000a6000000000000000d000000000000015300000000000001290000000000000038000000000000005500000000000000220000000000000134000000000000009500000000000000ff0000000000000034000000000000009b0000000000000103000000000000009d000000000000013400000000000000730000000000000003000000000000004f00000000000000160000000000000147000000000000015a000000000000009e0000000000000168000000000000003c000000000000010800000000000001050000000000000049)
    (inv := 0x16b00000000000001270000000000000106000000000000011d00000000000000a600000000000000690000000000000080000000000000000600000000000000ad000000000000001c00000000000000f0000000000000010b000000000000000400000000000000f6000000000000017000000000000000ff000000000000000e00000000000001380000000000000109000000000000005f000000000000007000000000000001690000000000000006000000000000013a00000000000000dd000000000000012f000000000000012600000000000000fa00000000000000d100000000000000b1000000000000004f000000000000012a0000000000000003000000000000009c00000000000001490000000000000013000000000000016c0000000000000124000000000000001500000000000000d5000000000000006f000000000000005600000000000000df0000000000000020000000000000015a00000000000000bd000000000000007a000000000000010a) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree049 : PLift (Irreducible ((OeisA217703.polyS 49).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 89) (f := 0x500000000000000029000000000000004c0000000000000038000000000000003f00000000000000450000000000000029000000000000004700000000000000140000000000000008000000000000001d00000000000000140000000000000012000000000000003b000000000000002a000000000000001f0000000000000047000000000000003c000000000000003500000000000000070000000000000055000000000000004b00000000000000500000000000000031000000000000003d00000000000000230000000000000021000000000000000700000000000000460000000000000053000000000000004000000000000000050000000000000051000000000000004f00000000000000560000000000000013000000000000000600000000000000530000000000000023000000000000002a000000000000001b000000000000001e0000000000000011000000000000003f000000000000001d000000000000002b00000000000000210000000000000041000000000000000f)
    (inv := 0x51000000000000003f0000000000000019000000000000004c000000000000002d000000000000004800000000000000420000000000000030000000000000003f00000000000000410000000000000024000000000000002a000000000000002200000000000000460000000000000052000000000000001100000000000000540000000000000016000000000000003000000000000000170000000000000002000000000000001e00000000000000290000000000000035000000000000001700000000000000280000000000000019000000000000000b000000000000002100000000000000300000000000000038000000000000002f000000000000004c000000000000004a0000000000000041000000000000001d000000000000005300000000000000470000000000000019000000000000002c00000000000000250000000000000011000000000000002d000000000000003a000000000000001a0000000000000055000000000000004b00000000000000440000000000000009) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree050 : PLift (Irreducible ((OeisA217703.polyS 50).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 373) (f := 0x79000000000000013e0000000000000034000000000000008b0000000000000114000000000000010500000000000001680000000000000087000000000000005d000000000000011a0000000000000124000000000000002200000000000000d9000000000000006500000000000000420000000000000052000000000000002b000000000000003a0000000000000062000000000000005f000000000000002c0000000000000079000000000000013f00000000000000a70000000000000171000000000000012a00000000000000f10000000000000007000000000000016f000000000000002e000000000000001b000000000000011c000000000000002a0000000000000141000000000000006700000000000000f20000000000000169000000000000004f0000000000000004000000000000005500000000000000e10000000000000093000000000000005e00000000000000ed00000000000000a700000000000000b9000000000000004300000000000001170000000000000123000000000000005c)
    (inv := 0x1320000000000000031000000000000014f000000000000005e00000000000000230000000000000095000000000000003e00000000000000e60000000000000084000000000000014100000000000000de000000000000016800000000000000e50000000000000030000000000000014c00000000000000f60000000000000025000000000000002d000000000000014800000000000001630000000000000029000000000000008f000000000000003d000000000000006300000000000000fa0000000000000011000000000000004d000000000000008200000000000000ad00000000000000c400000000000000a800000000000000c3000000000000012a000000000000007a0000000000000075000000000000001e000000000000010d000000000000003e00000000000000be00000000000000560000000000000122000000000000006b0000000000000100000000000000009e000000000000007e00000000000000d200000000000000b000000000000000be00000000000000190000000000000146) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree051 : PLift (Irreducible ((OeisA217703.polyS 51).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 71) (f := 0x5000000000000000e0000000000000046000000000000001c000000000000001a000000000000001e000000000000000400000000000000400000000000000021000000000000000f00000000000000090000000000000040000000000000001600000000000000230000000000000038000000000000001d000000000000003c00000000000000190000000000000030000000000000003d000000000000001c000000000000001a00000000000000080000000000000044000000000000003d000000000000001d00000000000000040000000000000002000000000000002b0000000000000020000000000000001e0000000000000012000000000000002e0000000000000033000000000000001100000000000000020000000000000007000000000000000a000000000000003a0000000000000031000000000000000a0000000000000006000000000000002a0000000000000018000000000000001a000000000000002200000000000000300000000000000040000000000000001c0000000000000034000000000000000c)
    (inv := 0x46000000000000003e0000000000000012000000000000000400000000000000250000000000000025000000000000001c000000000000003200000000000000170000000000000031000000000000003900000000000000350000000000000033000000000000000900000000000000300000000000000004000000000000002c000000000000004300000000000000430000000000000035000000000000000a000000000000002800000000000000330000000000000003000000000000002800000000000000440000000000000018000000000000000100000000000000100000000000000032000000000000001d0000000000000025000000000000002a000000000000002e000000000000003e000000000000001c00000000000000350000000000000035000000000000002d0000000000000017000000000000004300000000000000170000000000000006000000000000000a0000000000000029000000000000002e000000000000001d000000000000000700000000000000150000000000000046000000000000003e) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree052 : PLift (Irreducible ((OeisA217703.polyS 52).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 107) (f := 0x4f000000000000005400000000000000580000000000000025000000000000001a000000000000003800000000000000350000000000000000000000000000002600000000000000220000000000000027000000000000001f000000000000006200000000000000380000000000000060000000000000002200000000000000390000000000000013000000000000005c000000000000004a0000000000000030000000000000006000000000000000230000000000000068000000000000003e00000000000000070000000000000013000000000000003300000000000000400000000000000004000000000000006a0000000000000060000000000000001b000000000000001a000000000000006800000000000000300000000000000010000000000000004c00000000000000460000000000000055000000000000001a000000000000005f000000000000005e000000000000006500000000000000600000000000000001000000000000005d0000000000000051000000000000000700000000000000160000000000000066000000000000002e)
    (inv := 0x680000000000000010000000000000002e000000000000002b00000000000000000000000000000052000000000000006a00000000000000380000000000000003000000000000002300000000000000620000000000000003000000000000004b000000000000000b000000000000002500000000000000520000000000000031000000000000005f0000000000000044000000000000004900000000000000060000000000000046000000000000002a000000000000002d000000000000002900000000000000150000000000000061000000000000006a00000000000000360000000000000064000000000000005c000000000000001d00000000000000480000000000000011000000000000005a000000000000001900000000000000020000000000000066000000000000001e000000000000004400000000000000390000000000000066000000000000005d000000000000003600000000000000490000000000000053000000000000003600000000000000010000000000000065000000000000003800000000000000020000000000000042) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree053 : PLift (Irreducible ((OeisA217703.polyS 53).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 739) (f := 0xbe00000000000002a9000000000000003e000000000000026d00000000000002410000000000000137000000000000012b0000000000000113000000000000018b000000000000010b000000000000007500000000000001a40000000000000099000000000000004b00000000000002930000000000000010000000000000011400000000000001a6000000000000023700000000000000c300000000000002c70000000000000246000000000000002400000000000000fb00000000000000a50000000000000224000000000000011f0000000000000103000000000000017b000000000000025e00000000000000e800000000000000ac0000000000000028000000000000024800000000000000b1000000000000025700000000000000ac00000000000000410000000000000093000000000000028500000000000002d60000000000000151000000000000004a0000000000000107000000000000009e000000000000029d000000000000028c000000000000009100000000000002d300000000000002d500000000000001b6000000000000023000000000000002af)
    (inv := 0x6900000000000001ad00000000000000c500000000000000e60000000000000295000000000000018a00000000000000c7000000000000016c000000000000008d000000000000005000000000000002d900000000000002c0000000000000026000000000000001de0000000000000030000000000000018c00000000000002c30000000000000206000000000000014c000000000000010c00000000000000020000000000000074000000000000001a000000000000006e00000000000000ca0000000000000080000000000000018800000000000002d00000000000000211000000000000011d000000000000024000000000000000630000000000000223000000000000007d00000000000001d300000000000002290000000000000140000000000000012200000000000002810000000000000053000000000000018400000000000001f7000000000000003d00000000000001b2000000000000017400000000000001e2000000000000024f00000000000000f9000000000000010d00000000000000d40000000000000116000000000000022700000000000002e0) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree054 : PLift (Irreducible ((OeisA217703.polyS 54).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 619) (f := 0x149000000000000026000000000000001a700000000000001d3000000000000018d00000000000000fe0000000000000217000000000000009400000000000000b200000000000002340000000000000043000000000000003d000000000000008c000000000000003500000000000000670000000000000116000000000000021f00000000000000d700000000000000e200000000000000d100000000000001d8000000000000007b000000000000005a00000000000000360000000000000014000000000000011f00000000000001b600000000000000a9000000000000020e0000000000000053000000000000005f000000000000008700000000000000f20000000000000166000000000000013d000000000000016400000000000001ef000000000000015000000000000001bf000000000000017e00000000000001b500000000000001810000000000000137000000000000025800000000000001a300000000000000b800000000000000bd0000000000000164000000000000003300000000000001410000000000000266000000000000014a000000000000018800000000000001d7)
    (inv := 0x120000000000000005000000000000005d00000000000002490000000000000047000000000000017c00000000000001cf000000000000013e000000000000000100000000000001300000000000000170000000000000018100000000000000bb0000000000000205000000000000002900000000000002170000000000000092000000000000000100000000000001e900000000000001210000000000000132000000000000014e00000000000002570000000000000196000000000000019600000000000000c80000000000000111000000000000022a00000000000001b0000000000000019700000000000000ce000000000000015100000000000001f50000000000000071000000000000002200000000000000d3000000000000000e0000000000000221000000000000005e000000000000011100000000000001f1000000000000004b000000000000001200000000000001c7000000000000000600000000000001f10000000000000263000000000000015b000000000000008400000000000001ea000000000000020400000000000000d500000000000000db0000000000000051) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree055 : PLift (Irreducible ((OeisA217703.polyS 55).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 641) (f := 0x274000000000000023700000000000000550000000000000019000000000000008d00000000000002060000000000000015000000000000025b00000000000000a7000000000000013d00000000000001760000000000000085000000000000010b0000000000000064000000000000024e00000000000001640000000000000196000000000000021c000000000000016f0000000000000269000000000000007b000000000000020700000000000000560000000000000225000000000000004b0000000000000118000000000000022200000000000001cd000000000000010e0000000000000161000000000000001700000000000000fb000000000000014e000000000000026600000000000000cc000000000000013a00000000000000d5000000000000014d00000000000000e60000000000000177000000000000000d000000000000026500000000000001810000000000000074000000000000005e000000000000023600000000000001bf000000000000021400000000000000e700000000000000cd000000000000025b000000000000000300000000000001270000000000000244000000000000017a)
    (inv := 0x1b300000000000000e200000000000001550000000000000144000000000000026d000000000000005f0000000000000134000000000000016100000000000001d100000000000000c7000000000000023200000000000000810000000000000272000000000000000c000000000000007200000000000000eb000000000000024400000000000001bf00000000000001640000000000000155000000000000027d000000000000025d0000000000000131000000000000006f000000000000016600000000000000f1000000000000017f00000000000000d4000000000000005e00000000000000c60000000000000228000000000000025e00000000000001ce00000000000000da00000000000002480000000000000253000000000000003700000000000000d70000000000000135000000000000004e000000000000004d000000000000000d000000000000016100000000000001f700000000000000c600000000000000cc0000000000000088000000000000027e00000000000001f1000000000000012500000000000000ca000000000000016000000000000001ba00000000000000d800000000000000e2) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree056 : PLift (Irreducible ((OeisA217703.polyS 56).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 179) (f := 0x990000000000000025000000000000008f000000000000000d000000000000008e000000000000000200000000000000a800000000000000990000000000000099000000000000005c000000000000008000000000000000a8000000000000007000000000000000a6000000000000007f000000000000009700000000000000430000000000000063000000000000004b000000000000000a000000000000000e0000000000000030000000000000001d000000000000002a0000000000000077000000000000002c000000000000004c000000000000005b000000000000007700000000000000ae00000000000000600000000000000071000000000000007d000000000000008f00000000000000af00000000000000a7000000000000004700000000000000a1000000000000002a000000000000002f00000000000000810000000000000018000000000000009f00000000000000770000000000000045000000000000002e0000000000000024000000000000009d000000000000008b0000000000000094000000000000000000000000000000090000000000000099000000000000002b0000000000000068000000000000009c)
    (inv := 0x12000000000000005c00000000000000a7000000000000008e00000000000000ad000000000000002d000000000000000a00000000000000a2000000000000005f0000000000000052000000000000009f00000000000000a7000000000000008f000000000000002a000000000000009d00000000000000a6000000000000002a0000000000000044000000000000003a000000000000002500000000000000190000000000000066000000000000009c000000000000009e00000000000000700000000000000080000000000000005f000000000000001100000000000000490000000000000003000000000000000700000000000000230000000000000076000000000000005a0000000000000051000000000000007e000000000000001b00000000000000460000000000000082000000000000000c0000000000000056000000000000009400000000000000470000000000000009000000000000007f000000000000009e00000000000000ae00000000000000550000000000000028000000000000005d0000000000000053000000000000009200000000000000650000000000000012000000000000000e0000000000000021) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree057 : PLift (Irreducible ((OeisA217703.polyS 57).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 577) (f := 0x20b000000000000011a0000000000000155000000000000001f000000000000008c000000000000006300000000000000ca000000000000019a00000000000000050000000000000162000000000000008d00000000000000ba000000000000022a0000000000000146000000000000012c000000000000005b000000000000005c000000000000000200000000000001af000000000000021b0000000000000152000000000000012e0000000000000235000000000000015c0000000000000104000000000000017e00000000000001c700000000000000b5000000000000021300000000000001ae000000000000021400000000000001dc0000000000000177000000000000006c000000000000020700000000000001f50000000000000004000000000000006100000000000000210000000000000054000000000000005100000000000001c2000000000000015b00000000000000b50000000000000158000000000000017c000000000000011800000000000000f6000000000000007000000000000000650000000000000163000000000000006d000000000000009400000000000001b200000000000000b40000000000000138000000000000021e)
    (inv := 0x9c0000000000000052000000000000010d00000000000001fe00000000000000c6000000000000022300000000000000110000000000000182000000000000020a0000000000000022000000000000006100000000000000ed000000000000019e000000000000001e000000000000016c000000000000022700000000000000a300000000000001c4000000000000013f000000000000021e000000000000000200000000000000f700000000000000c800000000000000ac00000000000000df00000000000001c400000000000000da00000000000001a800000000000001db00000000000000990000000000000169000000000000002b000000000000005300000000000000fc00000000000001a2000000000000002f000000000000022a00000000000001a500000000000000a2000000000000005200000000000001850000000000000239000000000000017000000000000000a500000000000001040000000000000140000000000000009f000000000000008500000000000000dc00000000000001660000000000000109000000000000022e000000000000004500000000000001310000000000000029000000000000006c000000000000007c) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree058 : PLift (Irreducible ((OeisA217703.polyS 58).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 71) (f := 0x230000000000000030000000000000000a00000000000000010000000000000013000000000000000c00000000000000340000000000000027000000000000000600000000000000130000000000000007000000000000003700000000000000400000000000000009000000000000000a0000000000000043000000000000001900000000000000040000000000000007000000000000001b00000000000000060000000000000042000000000000000000000000000000040000000000000023000000000000001e000000000000002c0000000000000004000000000000002900000000000000450000000000000037000000000000002c00000000000000220000000000000003000000000000000e000000000000000d000000000000000d000000000000000d000000000000002400000000000000440000000000000046000000000000000e000000000000003d0000000000000003000000000000001f0000000000000006000000000000004500000000000000080000000000000034000000000000004200000000000000050000000000000007000000000000000200000000000000330000000000000044000000000000000e000000000000003e0000000000000040)
    (inv := 0x300000000000000006000000000000002f0000000000000017000000000000000000000000000000440000000000000028000000000000000300000000000000080000000000000000000000000000001a000000000000004300000000000000230000000000000036000000000000002d000000000000002b00000000000000170000000000000003000000000000003d00000000000000190000000000000007000000000000000e000000000000001c000000000000001200000000000000140000000000000031000000000000002e000000000000001a0000000000000011000000000000002e000000000000001800000000000000150000000000000046000000000000000700000000000000440000000000000018000000000000003200000000000000050000000000000037000000000000003a00000000000000180000000000000011000000000000004300000000000000380000000000000033000000000000000c000000000000000a000000000000001e000000000000000e000000000000003c00000000000000140000000000000024000000000000003f000000000000001b000000000000002a000000000000003d00000000000000090000000000000042) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree059 : PLift (Irreducible ((OeisA217703.polyS 59).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 373) (f := 0x16a000000000000017400000000000001060000000000000084000000000000004f000000000000016100000000000001220000000000000021000000000000001c00000000000000c400000000000000b9000000000000001f00000000000000a70000000000000038000000000000007e00000000000000f700000000000000a300000000000000480000000000000136000000000000013e00000000000000590000000000000094000000000000013a00000000000000d700000000000000ce000000000000012000000000000000ff000000000000007100000000000000be00000000000000060000000000000108000000000000004d00000000000000fd0000000000000055000000000000001900000000000000ac00000000000000dd0000000000000139000000000000011700000000000000140000000000000036000000000000008b000000000000006600000000000000eb000000000000000b0000000000000122000000000000006c000000000000003b0000000000000045000000000000014200000000000000ba00000000000000d100000000000000b300000000000000b9000000000000002700000000000000700000000000000078000000000000016b000000000000012a)
    (inv := 0x4300000000000000b2000000000000011d00000000000001710000000000000008000000000000008a0000000000000024000000000000014c0000000000000066000000000000007f00000000000000810000000000000118000000000000004500000000000000ac00000000000001200000000000000043000000000000014400000000000000dd00000000000001560000000000000162000000000000003d00000000000000200000000000000148000000000000013d000000000000000f000000000000005a00000000000000dd00000000000000a1000000000000002300000000000000d6000000000000017200000000000000c30000000000000145000000000000005a000000000000007b00000000000000d70000000000000113000000000000005f000000000000000c00000000000001710000000000000129000000000000013500000000000000e20000000000000045000000000000011f000000000000010500000000000000fe000000000000005800000000000000d80000000000000157000000000000004700000000000000c200000000000000c4000000000000009100000000000000dc00000000000000430000000000000125000000000000000400000000000000c4) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree060 : PLift (Irreducible ((OeisA217703.polyS 60).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 1009) (f := 0x2aa000000000000026f000000000000035200000000000000bf000000000000017c000000000000026700000000000003cc000000000000034b0000000000000271000000000000034a00000000000000e3000000000000012b000000000000027a00000000000001b70000000000000029000000000000030b000000000000015200000000000001f70000000000000389000000000000024a000000000000020a000000000000014800000000000003bf00000000000002cc00000000000001ac00000000000001d900000000000003760000000000000109000000000000002700000000000000d500000000000003720000000000000239000000000000006300000000000002070000000000000251000000000000004d000000000000031500000000000000610000000000000299000000000000030200000000000001f200000000000003e9000000000000031d000000000000010500000000000000fc0000000000000320000000000000010d00000000000003890000000000000041000000000000017a000000000000016e0000000000000007000000000000029e00000000000003ed0000000000000310000000000000004900000000000003b90000000000000050000000000000023200000000000001da)
    (inv := 0x193000000000000035d00000000000001a300000000000003a3000000000000016f000000000000033900000000000000720000000000000263000000000000028f000000000000018e000000000000037e00000000000000ea000000000000018300000000000003be00000000000003a900000000000000140000000000000202000000000000025200000000000003120000000000000076000000000000002b00000000000001bd00000000000000b100000000000002f2000000000000029600000000000002d800000000000002b50000000000000219000000000000032d000000000000039d00000000000003d9000000000000030c00000000000000e4000000000000008900000000000000a8000000000000016b00000000000000cd00000000000000b800000000000003620000000000000038000000000000007000000000000003d0000000000000029400000000000000d500000000000003dc00000000000000c600000000000000d300000000000002e500000000000000a800000000000003c400000000000002e600000000000000e100000000000003ef00000000000003d900000000000002c4000000000000023800000000000000630000000000000258000000000000014200000000000000d3) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree061 : PLift (Irreducible ((OeisA217703.polyS 61).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 103) (f := 0x4c000000000000005600000000000000040000000000000046000000000000000a0000000000000053000000000000001f0000000000000009000000000000003a0000000000000002000000000000003700000000000000230000000000000046000000000000001000000000000000020000000000000033000000000000002b00000000000000560000000000000051000000000000005c0000000000000043000000000000003e000000000000000b000000000000001100000000000000290000000000000063000000000000004e00000000000000180000000000000038000000000000004f000000000000001f0000000000000048000000000000003b000000000000004c000000000000001b000000000000003c0000000000000066000000000000000c0000000000000034000000000000004d0000000000000058000000000000000100000000000000350000000000000054000000000000003c0000000000000012000000000000005f0000000000000015000000000000004d0000000000000056000000000000000a000000000000000a0000000000000011000000000000005d000000000000004200000000000000440000000000000000000000000000005c000000000000003d00000000000000330000000000000044)
    (inv := 0x140000000000000036000000000000005a0000000000000063000000000000003e0000000000000020000000000000000e000000000000000a0000000000000002000000000000003d000000000000003100000000000000010000000000000028000000000000002c000000000000001d0000000000000033000000000000004a000000000000003400000000000000380000000000000066000000000000003c00000000000000440000000000000059000000000000000d0000000000000008000000000000004f0000000000000040000000000000005e000000000000003c000000000000002b000000000000000f000000000000002f0000000000000063000000000000001e000000000000002700000000000000170000000000000029000000000000001a000000000000001e000000000000005b0000000000000002000000000000005f0000000000000035000000000000005b000000000000005200000000000000490000000000000031000000000000000b000000000000001900000000000000000000000000000022000000000000001a000000000000002900000000000000590000000000000048000000000000001500000000000000130000000000000007000000000000000c000000000000001d0000000000000027) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree062 : PLift (Irreducible ((OeisA217703.polyS 62).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 2677) (f := 0x38500000000000004ad00000000000000fc00000000000009e90000000000000076000000000000000f00000000000001d9000000000000092b00000000000009d4000000000000018d00000000000002f700000000000007dc000000000000092100000000000001d70000000000000382000000000000099200000000000006ff0000000000000a50000000000000053800000000000006ee0000000000000645000000000000069f00000000000000bb00000000000003610000000000000a6d000000000000089e00000000000009ae00000000000002f300000000000008dd000000000000040b000000000000044500000000000004ac000000000000046b00000000000003c000000000000008910000000000000076000000000000029a000000000000045f00000000000009c40000000000000a1c000000000000037400000000000003810000000000000985000000000000084f000000000000062700000000000003c30000000000000670000000000000016300000000000002c200000000000002330000000000000168000000000000089000000000000003cf0000000000000764000000000000060800000000000000f100000000000004de00000000000003db000000000000034700000000000009e0000000000000016c00000000000006b9)
    (inv := 0x6a3000000000000081100000000000004a4000000000000029f00000000000006a900000000000005730000000000000243000000000000033e000000000000061a00000000000008dc0000000000000454000000000000075000000000000007f900000000000008f4000000000000083100000000000005c7000000000000082d0000000000000807000000000000027f00000000000009fa000000000000068700000000000005700000000000000a23000000000000042e0000000000000844000000000000020f000000000000086a00000000000003b6000000000000065f00000000000003110000000000000685000000000000061100000000000005f50000000000000787000000000000041100000000000001d4000000000000024200000000000002a4000000000000066200000000000005be00000000000003a5000000000000083b000000000000068500000000000000ee0000000000000a0d00000000000000a800000000000002e200000000000008a100000000000006d100000000000006c900000000000002d00000000000000592000000000000094a00000000000004c200000000000006ac000000000000074f00000000000009bb0000000000000499000000000000079d00000000000005a400000000000004590000000000000355) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree063 : PLift (Irreducible ((OeisA217703.polyS 63).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 661) (f := 0x5400000000000000c800000000000000e5000000000000000c00000000000000610000000000000135000000000000001300000000000000a2000000000000024c000000000000002a000000000000007d0000000000000229000000000000020f00000000000002770000000000000025000000000000019300000000000000c8000000000000012f00000000000000fd000000000000003b0000000000000202000000000000008d000000000000010100000000000000eb0000000000000231000000000000000900000000000001c50000000000000271000000000000010b0000000000000040000000000000028b00000000000000930000000000000032000000000000012e000000000000005100000000000000eb000000000000025f00000000000000c3000000000000027c00000000000002910000000000000148000000000000021100000000000001b800000000000000e2000000000000016a00000000000000e100000000000000bb00000000000001d400000000000001b100000000000001a6000000000000007e00000000000000940000000000000118000000000000025b00000000000001e600000000000000af00000000000001b4000000000000015200000000000002800000000000000059000000000000025100000000000000f7000000000000009c)
    (inv := 0x1ed000000000000007900000000000001310000000000000227000000000000025b00000000000001b10000000000000226000000000000010c000000000000027400000000000000ff000000000000004b000000000000010b00000000000000f600000000000000e8000000000000013100000000000000ce000000000000024200000000000001f70000000000000021000000000000014b000000000000002300000000000000b1000000000000017a00000000000002630000000000000055000000000000023a0000000000000102000000000000025900000000000001800000000000000224000000000000004900000000000000d500000000000000c800000000000001bf000000000000005b00000000000000650000000000000274000000000000024500000000000000060000000000000175000000000000004300000000000001ee000000000000009c00000000000002120000000000000136000000000000018500000000000001e700000000000001890000000000000075000000000000012e00000000000000c5000000000000013d00000000000000cc00000000000000ad000000000000011c000000000000010e00000000000001350000000000000188000000000000017f0000000000000199000000000000025f000000000000014f000000000000022f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree064 : PLift (Irreducible ((OeisA217703.polyS 64).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 283) (f := 0x6d000000000000008d000000000000008e000000000000003c000000000000009d000000000000008500000000000000c4000000000000000d00000000000001170000000000000112000000000000004700000000000000d400000000000000e7000000000000010b000000000000010c000000000000004f000000000000002b0000000000000045000000000000007d00000000000000f600000000000000510000000000000109000000000000008e000000000000000000000000000000a200000000000000ca0000000000000054000000000000009f0000000000000039000000000000007e00000000000000e000000000000000aa00000000000000e100000000000000d200000000000000aa00000000000000b1000000000000003d000000000000009900000000000000e5000000000000010600000000000000d6000000000000010100000000000000bd0000000000000100000000000000001f000000000000001700000000000000e100000000000000f600000000000000230000000000000070000000000000010500000000000000b7000000000000010400000000000000330000000000000084000000000000008400000000000000d900000000000000500000000000000106000000000000000a00000000000000dd000000000000010c00000000000001120000000000000042)
    (inv := 0x380000000000000048000000000000009700000000000000db0000000000000064000000000000002e0000000000000003000000000000009700000000000000030000000000000076000000000000000700000000000000d800000000000000a3000000000000005b000000000000008c0000000000000003000000000000009d00000000000000f100000000000000d400000000000000cd000000000000002a000000000000011a000000000000009a00000000000000ad000000000000007400000000000000d2000000000000001e000000000000001b00000000000000f20000000000000059000000000000004c0000000000000087000000000000003f00000000000000af00000000000000140000000000000022000000000000011000000000000000d30000000000000021000000000000007500000000000000df00000000000000fd000000000000009c000000000000009200000000000000fc0000000000000002000000000000000d000000000000009600000000000001040000000000000118000000000000005a00000000000000bb00000000000000e800000000000000e100000000000000b0000000000000000c000000000000010a000000000000004e000000000000000f000000000000003a00000000000000fa000000000000000800000000000000cc00000000000000ee) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree065 : PLift (Irreducible ((OeisA217703.polyS 65).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 163) (f := 0x9a0000000000000038000000000000005c00000000000000790000000000000024000000000000000900000000000000180000000000000062000000000000006d000000000000005f00000000000000660000000000000004000000000000000b000000000000002f00000000000000150000000000000079000000000000006f000000000000001400000000000000550000000000000001000000000000003f000000000000002800000000000000580000000000000032000000000000003d000000000000009d000000000000009c000000000000002a00000000000000970000000000000027000000000000006c00000000000000840000000000000055000000000000008800000000000000360000000000000083000000000000001e000000000000005400000000000000450000000000000061000000000000003b000000000000001b0000000000000022000000000000004a000000000000006e00000000000000860000000000000092000000000000004a0000000000000041000000000000009c0000000000000018000000000000000a000000000000003a000000000000002000000000000000340000000000000074000000000000002b0000000000000007000000000000006d000000000000003c00000000000000540000000000000096000000000000007f00000000000000510000000000000006)
    (inv := 0x800000000000000300000000000000082000000000000007600000000000000030000000000000089000000000000005c000000000000002e000000000000006100000000000000470000000000000098000000000000003d000000000000000900000000000000210000000000000041000000000000006b000000000000002000000000000000460000000000000027000000000000008500000000000000120000000000000086000000000000000f000000000000005e0000000000000033000000000000007b00000000000000430000000000000027000000000000006a000000000000006b000000000000001d00000000000000860000000000000057000000000000001e000000000000001e0000000000000040000000000000008c0000000000000063000000000000006600000000000000900000000000000088000000000000007600000000000000400000000000000082000000000000003900000000000000660000000000000051000000000000006f00000000000000460000000000000042000000000000005d00000000000000260000000000000043000000000000002b00000000000000620000000000000048000000000000006300000000000000a00000000000000070000000000000006a0000000000000045000000000000001b00000000000000760000000000000026000000000000006a) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree066 : PLift (Irreducible ((OeisA217703.polyS 66).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 239) (f := 0xb500000000000000d500000000000000190000000000000074000000000000004c0000000000000069000000000000001c00000000000000a0000000000000007f00000000000000a50000000000000022000000000000000d00000000000000dc0000000000000015000000000000002600000000000000a100000000000000a000000000000000c100000000000000de000000000000009300000000000000de000000000000007a0000000000000003000000000000005f000000000000006e0000000000000067000000000000000800000000000000540000000000000008000000000000005500000000000000b500000000000000b1000000000000007b00000000000000b600000000000000ad0000000000000070000000000000007400000000000000420000000000000059000000000000001c000000000000006f00000000000000380000000000000020000000000000009c00000000000000010000000000000079000000000000003400000000000000a600000000000000c900000000000000e8000000000000006100000000000000930000000000000072000000000000004000000000000000d900000000000000ae000000000000009a0000000000000041000000000000005900000000000000c700000000000000740000000000000078000000000000005900000000000000e300000000000000d10000000000000038)
    (inv := 0xb00000000000000b10000000000000057000000000000006900000000000000a8000000000000004700000000000000900000000000000081000000000000001e00000000000000a90000000000000022000000000000000e000000000000001f00000000000000d3000000000000008800000000000000d600000000000000850000000000000047000000000000005200000000000000a30000000000000066000000000000007e000000000000005300000000000000d100000000000000ba0000000000000071000000000000004500000000000000a500000000000000bc0000000000000068000000000000008900000000000000c1000000000000007c000000000000006f000000000000006f000000000000004d000000000000000d00000000000000ec00000000000000460000000000000014000000000000004800000000000000a000000000000000b900000000000000290000000000000097000000000000004e00000000000000c3000000000000000a0000000000000082000000000000009e00000000000000ae00000000000000cf000000000000002b00000000000000ee00000000000000630000000000000079000000000000002100000000000000c6000000000000009300000000000000e2000000000000001c00000000000000cf00000000000000d8000000000000006700000000000000750000000000000079) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree067 : PLift (Irreducible ((OeisA217703.polyS 67).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 193) (f := 0x8200000000000000010000000000000038000000000000004c00000000000000b40000000000000046000000000000003c000000000000002e0000000000000096000000000000008600000000000000bf0000000000000071000000000000004d00000000000000350000000000000008000000000000006000000000000000a0000000000000007f000000000000001d00000000000000bd000000000000009b0000000000000002000000000000002f000000000000006900000000000000a2000000000000002e000000000000004100000000000000b90000000000000011000000000000004200000000000000ad000000000000002a00000000000000ae000000000000001700000000000000540000000000000010000000000000002c000000000000001a000000000000001e0000000000000071000000000000005c0000000000000052000000000000008b0000000000000082000000000000002900000000000000ad00000000000000a700000000000000b1000000000000001800000000000000a90000000000000070000000000000006400000000000000bc000000000000004b000000000000008b00000000000000380000000000000024000000000000003f0000000000000003000000000000008900000000000000b7000000000000004d0000000000000017000000000000005b00000000000000a8000000000000007a0000000000000008)
    (inv := 0x1700000000000000710000000000000098000000000000009600000000000000b500000000000000990000000000000083000000000000008b000000000000007b0000000000000046000000000000006a0000000000000011000000000000000e0000000000000005000000000000005e000000000000000b000000000000006f00000000000000b700000000000000bf000000000000001700000000000000060000000000000008000000000000005c0000000000000074000000000000005e0000000000000094000000000000007900000000000000690000000000000014000000000000007b00000000000000b7000000000000001a00000000000000a100000000000000a8000000000000002700000000000000970000000000000068000000000000001400000000000000b400000000000000610000000000000049000000000000001f000000000000009d00000000000000910000000000000013000000000000008c00000000000000140000000000000071000000000000002700000000000000a9000000000000000000000000000000690000000000000078000000000000005600000000000000a1000000000000001b00000000000000a70000000000000018000000000000002900000000000000b5000000000000001900000000000000a8000000000000003a0000000000000057000000000000007d00000000000000560000000000000014) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree068 : PLift (Irreducible ((OeisA217703.polyS 68).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 149) (f := 0x52000000000000003f0000000000000066000000000000000f000000000000000e000000000000008b0000000000000017000000000000000f0000000000000079000000000000002f000000000000007e000000000000007e0000000000000021000000000000001a00000000000000940000000000000003000000000000003f000000000000003f000000000000000d0000000000000080000000000000007f0000000000000011000000000000002a000000000000008a000000000000000200000000000000870000000000000005000000000000007600000000000000930000000000000012000000000000005200000000000000520000000000000074000000000000008500000000000000530000000000000052000000000000001b000000000000004c000000000000002a000000000000001c000000000000006f0000000000000051000000000000000f000000000000004a0000000000000031000000000000006a000000000000005600000000000000710000000000000036000000000000004600000000000000030000000000000007000000000000007f0000000000000005000000000000003f000000000000003c000000000000002100000000000000670000000000000052000000000000007a0000000000000074000000000000007e00000000000000460000000000000058000000000000000a000000000000001f00000000000000770000000000000036)
    (inv := 0x8d0000000000000032000000000000001d000000000000005b000000000000003a0000000000000080000000000000001600000000000000840000000000000031000000000000006f0000000000000079000000000000002d00000000000000630000000000000087000000000000008b0000000000000038000000000000006b00000000000000480000000000000006000000000000006c00000000000000000000000000000017000000000000005900000000000000630000000000000052000000000000002300000000000000170000000000000001000000000000007a0000000000000059000000000000003f000000000000003d000000000000005b0000000000000069000000000000006b0000000000000076000000000000005900000000000000420000000000000069000000000000003f0000000000000086000000000000008a000000000000000f000000000000003000000000000000570000000000000041000000000000003b0000000000000091000000000000001e0000000000000060000000000000008300000000000000310000000000000039000000000000004f0000000000000024000000000000008d0000000000000091000000000000007e0000000000000075000000000000002000000000000000510000000000000000000000000000006d000000000000003e0000000000000024000000000000002b000000000000002b0000000000000066) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree069 : PLift (Irreducible ((OeisA217703.polyS 69).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 311) (f := 0x1000000000000001280000000000000093000000000000012b000000000000003400000000000000bf00000000000000ae000000000000009c000000000000007000000000000000b600000000000000ec00000000000000e8000000000000001f00000000000000bb00000000000000de0000000000000026000000000000008f000000000000011400000000000000f100000000000000d6000000000000002c0000000000000027000000000000000100000000000000a300000000000000c3000000000000008600000000000000e80000000000000098000000000000009500000000000000d1000000000000001900000000000000680000000000000083000000000000006a000000000000013500000000000000860000000000000102000000000000006e000000000000004700000000000000d600000000000000c6000000000000009900000000000000240000000000000031000000000000008300000000000000cf00000000000000ea000000000000001e000000000000010a000000000000002d0000000000000084000000000000009800000000000000820000000000000095000000000000002300000000000000da00000000000000f10000000000000126000000000000012000000000000000ba00000000000000f6000000000000005e0000000000000047000000000000010b00000000000000c1000000000000006a0000000000000037000000000000007e0000000000000042)
    (inv := 0xd000000000000001600000000000000f8000000000000011c00000000000000a6000000000000011b000000000000006f000000000000002000000000000000d700000000000000c400000000000000bc000000000000006b00000000000000ba000000000000009a0000000000000125000000000000007100000000000000d100000000000000ab00000000000000f7000000000000008e00000000000000f80000000000000020000000000000000f0000000000000035000000000000011300000000000000c3000000000000006800000000000000cc00000000000000ea00000000000000340000000000000127000000000000012c00000000000000ad00000000000000c9000000000000001c0000000000000125000000000000009800000000000000aa00000000000000a500000000000000400000000000000134000000000000000a0000000000000126000000000000005200000000000000eb00000000000000d100000000000000cf000000000000005700000000000000b600000000000001080000000000000081000000000000001300000000000000a300000000000000a6000000000000007900000000000000d9000000000000004e00000000000001070000000000000069000000000000004a000000000000011300000000000000dd00000000000000bd00000000000000ab000000000000012f0000000000000072000000000000012000000000000000c800000000000000bf) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree070 : PLift (Irreducible ((OeisA217703.polyS 70).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 191) (f := 0xb8000000000000008300000000000000770000000000000085000000000000009300000000000000a20000000000000074000000000000006e0000000000000055000000000000008f000000000000002d000000000000004c000000000000004300000000000000b0000000000000009500000000000000b1000000000000003d00000000000000770000000000000048000000000000006d000000000000009e000000000000008000000000000000580000000000000060000000000000007b0000000000000022000000000000002c000000000000006e000000000000002f0000000000000075000000000000000100000000000000b80000000000000099000000000000009c000000000000002a00000000000000a80000000000000006000000000000002c000000000000004200000000000000170000000000000052000000000000006e0000000000000045000000000000009400000000000000ba0000000000000076000000000000004300000000000000bd00000000000000320000000000000034000000000000009c000000000000007f0000000000000034000000000000004e0000000000000055000000000000009e00000000000000150000000000000006000000000000000100000000000000820000000000000015000000000000008d000000000000007e000000000000000a000000000000005f000000000000004a000000000000008700000000000000b400000000000000bd0000000000000040)
    (inv := 0x2c0000000000000099000000000000000c0000000000000095000000000000001f0000000000000066000000000000004c000000000000008a0000000000000045000000000000003f00000000000000920000000000000027000000000000002a0000000000000019000000000000007c00000000000000a0000000000000005b0000000000000020000000000000005b000000000000006100000000000000780000000000000071000000000000000f000000000000001c000000000000007e000000000000001c000000000000008e000000000000004a00000000000000910000000000000060000000000000001400000000000000910000000000000012000000000000007100000000000000850000000000000079000000000000004300000000000000bd00000000000000820000000000000077000000000000002c00000000000000670000000000000001000000000000004300000000000000b500000000000000ad000000000000002500000000000000490000000000000064000000000000006e0000000000000090000000000000002400000000000000a70000000000000073000000000000002e000000000000006a000000000000005a000000000000000c0000000000000076000000000000004d000000000000004000000000000000a200000000000000a4000000000000009e000000000000006d000000000000003a0000000000000028000000000000009200000000000000220000000000000074) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree071 : PLift (Irreducible ((OeisA217703.polyS 71).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 241) (f := 0xd300000000000000cf00000000000000e0000000000000004e0000000000000093000000000000009100000000000000b9000000000000007500000000000000da00000000000000b2000000000000009c000000000000002b00000000000000de00000000000000810000000000000086000000000000002b00000000000000ea00000000000000e1000000000000001200000000000000c500000000000000b6000000000000009200000000000000e4000000000000008200000000000000cd00000000000000e7000000000000001b00000000000000ab000000000000000600000000000000ba000000000000007e00000000000000a5000000000000009000000000000000cc000000000000006100000000000000a2000000000000003c00000000000000ca000000000000002c000000000000007d00000000000000cb00000000000000c400000000000000eb0000000000000063000000000000005a000000000000009d000000000000006000000000000000e2000000000000005d00000000000000a100000000000000c700000000000000dc000000000000002f000000000000000c000000000000007d000000000000007400000000000000da00000000000000c10000000000000041000000000000005600000000000000a3000000000000001200000000000000de000000000000001f000000000000007600000000000000ee000000000000007600000000000000eb000000000000007500000000000000a80000000000000096)
    (inv := 0xe700000000000000ec000000000000005e00000000000000c2000000000000006200000000000000e1000000000000005d000000000000009300000000000000ae0000000000000094000000000000009e00000000000000cf00000000000000ba00000000000000cd0000000000000046000000000000006d00000000000000e600000000000000d10000000000000083000000000000001a000000000000005d00000000000000730000000000000044000000000000006600000000000000630000000000000024000000000000006700000000000000560000000000000081000000000000003d00000000000000e800000000000000da000000000000007f000000000000002a00000000000000840000000000000060000000000000008900000000000000af00000000000000670000000000000097000000000000004f0000000000000088000000000000007d0000000000000046000000000000008c00000000000000a000000000000000ec00000000000000ed00000000000000de00000000000000aa0000000000000035000000000000005f00000000000000c800000000000000b50000000000000035000000000000005a000000000000000b000000000000006a000000000000001b0000000000000049000000000000007a000000000000009300000000000000e200000000000000d3000000000000006e00000000000000be00000000000000210000000000000018000000000000001000000000000000dc0000000000000052) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree072 : PLift (Irreducible ((OeisA217703.polyS 72).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 239) (f := 0xe0000000000000001d0000000000000005000000000000005e000000000000004400000000000000580000000000000058000000000000006500000000000000dd0000000000000039000000000000003800000000000000da00000000000000090000000000000021000000000000005f0000000000000084000000000000007a000000000000004e000000000000007700000000000000ee00000000000000d200000000000000d70000000000000045000000000000009f000000000000009c00000000000000a5000000000000002e0000000000000047000000000000000f00000000000000e100000000000000140000000000000083000000000000005800000000000000e500000000000000e20000000000000014000000000000001f00000000000000aa00000000000000dc000000000000005800000000000000d7000000000000001d0000000000000059000000000000004d000000000000005300000000000000e700000000000000c600000000000000af00000000000000c100000000000000cf00000000000000bc000000000000007300000000000000890000000000000030000000000000006f00000000000000a200000000000000370000000000000041000000000000003b00000000000000bf000000000000006700000000000000dc0000000000000026000000000000007c000000000000007f00000000000000d300000000000000e200000000000000b800000000000000e200000000000000dd00000000000000a6000000000000007a)
    (inv := 0x140000000000000043000000000000001200000000000000b4000000000000004500000000000000d6000000000000006c000000000000005f0000000000000030000000000000006c000000000000009800000000000000eb0000000000000084000000000000000e000000000000003e000000000000009100000000000000e0000000000000008d000000000000000900000000000000db000000000000008400000000000000860000000000000092000000000000002400000000000000c100000000000000ac0000000000000037000000000000002000000000000000da00000000000000bd0000000000000009000000000000007d000000000000005f00000000000000c80000000000000010000000000000005f000000000000004e00000000000000970000000000000043000000000000000e0000000000000075000000000000003900000000000000e5000000000000003100000000000000bf00000000000000cb000000000000009e000000000000000e000000000000003400000000000000bd000000000000006f000000000000006c0000000000000074000000000000005a0000000000000083000000000000005f00000000000000dc00000000000000b500000000000000a2000000000000001700000000000000a000000000000000c4000000000000002300000000000000c6000000000000003400000000000000bc000000000000003c0000000000000088000000000000003b00000000000000b5000000000000009d00000000000000aa) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree073 : PLift (Irreducible ((OeisA217703.polyS 73).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 487) (f := 0xd400000000000000b400000000000001560000000000000105000000000000004b00000000000001c100000000000000ce000000000000000a00000000000001d7000000000000018a00000000000000e4000000000000003a000000000000017f000000000000014700000000000000b600000000000000e30000000000000008000000000000016b0000000000000165000000000000008f000000000000009a00000000000000ce00000000000001a50000000000000155000000000000002b00000000000000f600000000000000b9000000000000004000000000000000210000000000000010000000000000004a00000000000001be0000000000000117000000000000012600000000000000ce00000000000000940000000000000165000000000000008000000000000001a0000000000000005400000000000001e5000000000000005e000000000000010a000000000000009a00000000000001cc0000000000000059000000000000011a000000000000016000000000000001de000000000000013d000000000000013600000000000001d6000000000000011a000000000000016300000000000001390000000000000066000000000000009b000000000000014800000000000000fc0000000000000178000000000000015e000000000000008000000000000000e10000000000000002000000000000003a000000000000017f00000000000000f100000000000001b900000000000000a1000000000000018200000000000001e2000000000000006300000000000001d0)
    (inv := 0x18000000000000017d00000000000000d40000000000000197000000000000001a00000000000000fe000000000000010200000000000000dc00000000000000f300000000000000670000000000000192000000000000014100000000000000fe000000000000016300000000000000db000000000000013600000000000000cb000000000000016700000000000001610000000000000143000000000000004a00000000000001a100000000000001df000000000000002c00000000000000430000000000000108000000000000011d00000000000001800000000000000164000000000000012e000000000000009e00000000000001a40000000000000132000000000000010100000000000000b400000000000001d50000000000000043000000000000012f000000000000014400000000000001c80000000000000025000000000000009a00000000000001cc000000000000004200000000000000ac000000000000010100000000000001c200000000000000a9000000000000013400000000000001a3000000000000019400000000000000c600000000000001de000000000000005e000000000000007c00000000000000070000000000000048000000000000017e000000000000003e000000000000002100000000000001e0000000000000012e00000000000000230000000000000039000000000000013e00000000000000b0000000000000003a00000000000000a700000000000000e500000000000000cf00000000000001ce000000000000000e00000000000000af) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree074 : PLift (Irreducible ((OeisA217703.polyS 74).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 139) (f := 0x17000000000000004e000000000000002800000000000000110000000000000012000000000000001c000000000000001d000000000000007200000000000000820000000000000051000000000000005d000000000000002000000000000000620000000000000074000000000000006b00000000000000770000000000000046000000000000007d00000000000000210000000000000035000000000000004000000000000000150000000000000003000000000000001a000000000000006d000000000000004d0000000000000007000000000000000800000000000000440000000000000005000000000000008400000000000000620000000000000011000000000000005800000000000000590000000000000004000000000000004c000000000000003c000000000000005d0000000000000089000000000000003b0000000000000089000000000000002d000000000000003300000000000000470000000000000027000000000000007e00000000000000090000000000000049000000000000000e000000000000004800000000000000520000000000000031000000000000001d0000000000000081000000000000006d000000000000006d000000000000008a000000000000002400000000000000510000000000000056000000000000003400000000000000650000000000000074000000000000004a0000000000000057000000000000006d0000000000000063000000000000004e0000000000000085000000000000003e000000000000004500000000000000730000000000000055)
    (inv := 0x7c000000000000006e000000000000004700000000000000290000000000000007000000000000007e0000000000000000000000000000000d0000000000000057000000000000007000000000000000060000000000000023000000000000006800000000000000210000000000000001000000000000000b00000000000000480000000000000006000000000000007800000000000000050000000000000059000000000000000b000000000000006500000000000000840000000000000040000000000000007500000000000000090000000000000087000000000000006c000000000000007000000000000000250000000000000065000000000000005d000000000000007c000000000000002e000000000000000a000000000000007f00000000000000040000000000000016000000000000002900000000000000670000000000000072000000000000006a000000000000000200000000000000340000000000000083000000000000002500000000000000190000000000000028000000000000005600000000000000470000000000000057000000000000001c00000000000000380000000000000085000000000000000d00000000000000150000000000000047000000000000000a000000000000006a00000000000000800000000000000074000000000000001f00000000000000300000000000000049000000000000000d00000000000000280000000000000032000000000000006b000000000000000d000000000000006c000000000000003b0000000000000061000000000000000a) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree075 : PLift (Irreducible ((OeisA217703.polyS 75).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 821) (f := 0x1a2000000000000015f000000000000017c00000000000003260000000000000028000000000000019c0000000000000110000000000000028c000000000000029b00000000000001ef000000000000000500000000000001a80000000000000286000000000000021b000000000000006a000000000000008100000000000001a500000000000000cb0000000000000224000000000000026b000000000000013f00000000000002d00000000000000331000000000000003800000000000000c9000000000000003400000000000000b70000000000000084000000000000023a000000000000027900000000000002a200000000000001550000000000000110000000000000031b00000000000001af00000000000000de00000000000001330000000000000114000000000000016a00000000000000f4000000000000023a00000000000001550000000000000008000000000000025e000000000000029c000000000000010f00000000000002620000000000000300000000000000020c0000000000000215000000000000010600000000000000d70000000000000042000000000000025c000000000000022400000000000002480000000000000143000000000000026600000000000001de00000000000002c3000000000000026d00000000000001ae00000000000000a7000000000000029f0000000000000024000000000000027d00000000000000470000000000000154000000000000032b0000000000000185000000000000011100000000000001ad000000000000032700000000000001c1000000000000015b)
    (inv := 0x12700000000000001e300000000000001f20000000000000232000000000000032e00000000000002b2000000000000000c0000000000000044000000000000008b000000000000010a000000000000006b00000000000000600000000000000223000000000000023400000000000001810000000000000034000000000000019400000000000002c5000000000000012a00000000000000bc00000000000001ba000000000000023100000000000001d40000000000000257000000000000020300000000000002c700000000000000d700000000000000ee00000000000000bb000000000000016b00000000000002360000000000000166000000000000020a000000000000016200000000000002240000000000000172000000000000031600000000000000d700000000000001d70000000000000053000000000000001d00000000000001a30000000000000280000000000000023c0000000000000042000000000000018f00000000000001780000000000000107000000000000031600000000000000ed00000000000001fc000000000000025b000000000000004200000000000001fe0000000000000096000000000000022900000000000000ed00000000000001b500000000000000a400000000000000a600000000000001cd000000000000021a0000000000000071000000000000003300000000000001fe00000000000000a70000000000000201000000000000008d000000000000013f00000000000000d500000000000002f5000000000000030e00000000000001fd00000000000000990000000000000317) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree076 : PLift (Irreducible ((OeisA217703.polyS 76).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 103) (f := 0x50000000000000000b000000000000003d000000000000001400000000000000200000000000000057000000000000004e000000000000001e000000000000004900000000000000360000000000000012000000000000000e00000000000000170000000000000039000000000000004a00000000000000570000000000000013000000000000002300000000000000630000000000000002000000000000003600000000000000130000000000000062000000000000005a000000000000005a0000000000000042000000000000005600000000000000140000000000000058000000000000005200000000000000300000000000000036000000000000001b0000000000000022000000000000003c000000000000003a000000000000003100000000000000310000000000000023000000000000004f000000000000001a00000000000000560000000000000020000000000000004a000000000000002a0000000000000023000000000000002b0000000000000058000000000000005600000000000000360000000000000051000000000000001b000000000000000800000000000000510000000000000004000000000000003600000000000000410000000000000022000000000000001b000000000000006500000000000000040000000000000004000000000000001e0000000000000008000000000000000300000000000000440000000000000021000000000000001d0000000000000008000000000000000f0000000000000057000000000000005800000000000000390000000000000017000000000000002e0000000000000061)
    (inv := 0x11000000000000002d00000000000000440000000000000041000000000000003d0000000000000035000000000000004c000000000000003800000000000000130000000000000056000000000000005800000000000000160000000000000044000000000000004000000000000000240000000000000064000000000000003d000000000000002a0000000000000001000000000000002c000000000000002b00000000000000650000000000000005000000000000005d0000000000000014000000000000003e0000000000000056000000000000005e000000000000006600000000000000350000000000000031000000000000000a000000000000000f00000000000000070000000000000060000000000000004200000000000000220000000000000009000000000000004400000000000000090000000000000022000000000000005c000000000000002000000000000000590000000000000061000000000000003f0000000000000066000000000000002000000000000000300000000000000038000000000000000900000000000000590000000000000009000000000000003a000000000000003f000000000000000b000000000000005d000000000000002b00000000000000500000000000000063000000000000001c000000000000001c000000000000002d000000000000001b000000000000005b0000000000000031000000000000003000000000000000630000000000000007000000000000001f000000000000000a00000000000000210000000000000004000000000000002f000000000000005c0000000000000020) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree077 : PLift (Irreducible ((OeisA217703.polyS 77).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 619) (f := 0x177000000000000017e0000000000000154000000000000020d000000000000015200000000000001fb0000000000000060000000000000023b0000000000000030000000000000003a00000000000001bf000000000000011e0000000000000006000000000000004e00000000000000470000000000000188000000000000007d00000000000000e0000000000000003100000000000002270000000000000269000000000000024a000000000000021c00000000000000f7000000000000014400000000000001ac000000000000017b00000000000000e400000000000000ca000000000000019c000000000000008000000000000001db000000000000007100000000000000c700000000000000d600000000000000bb0000000000000221000000000000020a00000000000001fa000000000000001a0000000000000268000000000000025100000000000000c10000000000000260000000000000020b00000000000001150000000000000014000000000000018a0000000000000048000000000000012c00000000000000e9000000000000011800000000000001d50000000000000222000000000000000d000000000000010e0000000000000177000000000000020f000000000000019900000000000001da00000000000001f00000000000000073000000000000006100000000000001f9000000000000016e0000000000000038000000000000024500000000000000e800000000000000db00000000000000ac000000000000001c00000000000000a200000000000001d7000000000000006300000000000001ce00000000000000e80000000000000184)
    (inv := 0x54000000000000000f0000000000000089000000000000007900000000000000a600000000000001ff00000000000000cc000000000000003f000000000000008000000000000001260000000000000129000000000000009e000000000000006500000000000001a200000000000000d70000000000000167000000000000014a000000000000026700000000000001d300000000000000b80000000000000126000000000000007d000000000000002c0000000000000238000000000000000000000000000000a90000000000000178000000000000000700000000000000fc0000000000000075000000000000003a0000000000000250000000000000018d000000000000012e000000000000003c0000000000000120000000000000020c0000000000000186000000000000001a0000000000000175000000000000007a00000000000001a400000000000000d4000000000000021900000000000001510000000000000118000000000000015500000000000000fd00000000000001a100000000000000c500000000000001fd00000000000001a800000000000001ac000000000000008e000000000000026800000000000001fa00000000000000a00000000000000087000000000000004d0000000000000146000000000000007400000000000001f0000000000000007a000000000000017800000000000001b60000000000000223000000000000007c00000000000001e0000000000000025b00000000000001a500000000000000c3000000000000006400000000000001d1000000000000010c000000000000001a00000000000001080000000000000249) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree078 : PLift (Irreducible ((OeisA217703.polyS 78).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 2099) (f := 0x5ba000000000000054b000000000000044c0000000000000196000000000000080d00000000000001a800000000000002090000000000000225000000000000000b00000000000001cb000000000000009300000000000004f5000000000000027500000000000007a400000000000003ca00000000000005410000000000000000000000000000003600000000000007c200000000000001fd000000000000077f000000000000009f0000000000000477000000000000045f00000000000006af00000000000002dd0000000000000724000000000000025d00000000000001b5000000000000050c00000000000005040000000000000588000000000000014500000000000003bc000000000000076b00000000000002c7000000000000015f000000000000046200000000000005ea00000000000002a900000000000003b800000000000007db0000000000000411000000000000072d000000000000072e000000000000037a00000000000003cf00000000000006b400000000000003d500000000000007e100000000000002e30000000000000626000000000000054e000000000000047a00000000000008000000000000000372000000000000078200000000000007ca000000000000065400000000000006e4000000000000019b000000000000070500000000000003fd00000000000000cf000000000000022f000000000000068600000000000005c2000000000000064b000000000000004c00000000000003a4000000000000011b0000000000000134000000000000002b000000000000023600000000000005b2000000000000028f00000000000001220000000000000669)
    (inv := 0x30600000000000001d500000000000003ba00000000000005ec0000000000000331000000000000004500000000000002c300000000000000c6000000000000072d000000000000000400000000000007f100000000000001e1000000000000004000000000000001900000000000000276000000000000066e00000000000000a600000000000005d500000000000006cd00000000000007b700000000000001dc0000000000000543000000000000081900000000000007e800000000000005c2000000000000020c00000000000007e900000000000002f0000000000000079700000000000001a600000000000003530000000000000289000000000000022a000000000000050800000000000003c600000000000003150000000000000435000000000000070700000000000000810000000000000376000000000000008900000000000006f200000000000003ab000000000000069e000000000000059800000000000005a200000000000006ff000000000000057a000000000000081700000000000006f900000000000002e900000000000002fa000000000000031d0000000000000322000000000000018100000000000006f50000000000000628000000000000065e000000000000025700000000000005f20000000000000018000000000000076c000000000000036b000000000000044700000000000005b20000000000000527000000000000082b000000000000067700000000000003d70000000000000548000000000000053000000000000003bb00000000000007de000000000000028c000000000000045b000000000000053400000000000006220000000000000397) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree079 : PLift (Irreducible ((OeisA217703.polyS 79).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 173) (f := 0x71000000000000009500000000000000650000000000000089000000000000007700000000000000320000000000000071000000000000004800000000000000860000000000000037000000000000003c000000000000003e0000000000000024000000000000003f000000000000004f0000000000000071000000000000007a000000000000003e000000000000002f00000000000000a10000000000000038000000000000007f000000000000009f000000000000002c000000000000009f00000000000000490000000000000039000000000000004b0000000000000030000000000000007100000000000000910000000000000085000000000000005800000000000000510000000000000009000000000000008e00000000000000920000000000000062000000000000005c0000000000000089000000000000006100000000000000a4000000000000007d000000000000003a00000000000000770000000000000068000000000000002b000000000000003d000000000000008d0000000000000040000000000000000a00000000000000460000000000000052000000000000005200000000000000a9000000000000000c0000000000000060000000000000005d00000000000000000000000000000017000000000000004600000000000000190000000000000003000000000000001f00000000000000540000000000000077000000000000002f00000000000000020000000000000088000000000000007f000000000000000b00000000000000290000000000000039000000000000007b00000000000000a40000000000000035000000000000008a00000000000000670000000000000065)
    (inv := 0x2f00000000000000620000000000000064000000000000005a000000000000004a000000000000009900000000000000a7000000000000005d00000000000000a3000000000000008b00000000000000a9000000000000009a00000000000000a2000000000000001a00000000000000a60000000000000040000000000000000c000000000000006b0000000000000079000000000000001100000000000000210000000000000023000000000000008f00000000000000860000000000000014000000000000004d000000000000001c000000000000001b0000000000000016000000000000003800000000000000a3000000000000007100000000000000a6000000000000006b0000000000000044000000000000003f000000000000000b00000000000000a00000000000000066000000000000009e0000000000000085000000000000005400000000000000860000000000000034000000000000006b000000000000000900000000000000850000000000000049000000000000004d00000000000000ac00000000000000500000000000000089000000000000005d0000000000000060000000000000004500000000000000a20000000000000080000000000000006400000000000000ab000000000000004a000000000000000d0000000000000060000000000000001600000000000000a400000000000000630000000000000062000000000000004600000000000000a0000000000000008600000000000000810000000000000040000000000000009f000000000000003d000000000000002e00000000000000370000000000000017000000000000006c000000000000004a000000000000008f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree080 : PLift (Irreducible ((OeisA217703.polyS 80).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 379) (f := 0xb400000000000001230000000000000000000000000000009d000000000000008900000000000000e9000000000000005100000000000000a000000000000000ff000000000000009200000000000000a7000000000000009300000000000000a600000000000001760000000000000165000000000000000100000000000000d100000000000000a200000000000000b4000000000000014900000000000000f100000000000000f3000000000000009f00000000000000a2000000000000009500000000000000e1000000000000006b00000000000000ff00000000000001720000000000000058000000000000013200000000000000470000000000000113000000000000005600000000000000a4000000000000016900000000000001180000000000000088000000000000003a00000000000000da0000000000000018000000000000014500000000000000de000000000000007f000000000000010e000000000000012600000000000000ce000000000000000e000000000000010b0000000000000018000000000000000d0000000000000015000000000000002000000000000000cc0000000000000156000000000000014d000000000000004200000000000000cc00000000000000e7000000000000006e000000000000004700000000000001760000000000000032000000000000010b0000000000000002000000000000003600000000000000590000000000000063000000000000009f0000000000000110000000000000000500000000000000b9000000000000007000000000000001050000000000000072000000000000016400000000000000bc000000000000007900000000000001190000000000000008)
    (inv := 0x15f000000000000000e00000000000000f9000000000000003700000000000000d30000000000000122000000000000003700000000000000b9000000000000005700000000000000e700000000000000d2000000000000009800000000000000f000000000000000700000000000000144000000000000000a000000000000006d00000000000000d4000000000000003f000000000000002e00000000000000d6000000000000010100000000000000bd00000000000000c500000000000000cd000000000000014400000000000000a200000000000000cf000000000000014d0000000000000103000000000000007e0000000000000112000000000000016a000000000000010100000000000000d6000000000000004f0000000000000078000000000000004c00000000000000400000000000000171000000000000004400000000000001450000000000000126000000000000005f0000000000000115000000000000007d00000000000001610000000000000037000000000000007e00000000000000100000000000000021000000000000010d0000000000000130000000000000000400000000000000c40000000000000125000000000000008600000000000000f100000000000000f60000000000000000000000000000000100000000000000bb000000000000002a00000000000000760000000000000000000000000000001a00000000000000140000000000000000000000000000002d000000000000004700000000000000ee0000000000000034000000000000017600000000000000f7000000000000001c000000000000016e0000000000000159000000000000001400000000000000a20000000000000065) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree081 : PLift (Irreducible ((OeisA217703.polyS 81).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 193) (f := 0x55000000000000008d0000000000000027000000000000001f0000000000000076000000000000004a000000000000008f0000000000000026000000000000006c000000000000009b000000000000003900000000000000b600000000000000b000000000000000ac0000000000000075000000000000004d00000000000000ad000000000000008c00000000000000b6000000000000009500000000000000a600000000000000860000000000000015000000000000006c0000000000000007000000000000009f000000000000006d00000000000000580000000000000004000000000000004100000000000000bf00000000000000020000000000000075000000000000002d000000000000009b0000000000000063000000000000008f000000000000003f000000000000007c000000000000002700000000000000a500000000000000a4000000000000006a000000000000000a0000000000000041000000000000000300000000000000aa000000000000007e0000000000000025000000000000009b000000000000004b000000000000007200000000000000420000000000000031000000000000000700000000000000790000000000000009000000000000004b0000000000000061000000000000006100000000000000a4000000000000003600000000000000890000000000000041000000000000006200000000000000b000000000000000b0000000000000009f00000000000000b6000000000000007f00000000000000a7000000000000004c00000000000000870000000000000027000000000000007f000000000000008f00000000000000b100000000000000780000000000000025000000000000005700000000000000a9)
    (inv := 0x3000000000000001c0000000000000026000000000000007a000000000000001600000000000000b3000000000000008500000000000000bc000000000000003f000000000000009400000000000000ae0000000000000079000000000000007a00000000000000be00000000000000c0000000000000004100000000000000bf00000000000000070000000000000042000000000000001200000000000000b50000000000000004000000000000005d0000000000000078000000000000007200000000000000a8000000000000001e00000000000000500000000000000032000000000000008e0000000000000081000000000000003700000000000000320000000000000029000000000000009d000000000000001b000000000000009f000000000000009d0000000000000061000000000000008800000000000000690000000000000071000000000000004c00000000000000a4000000000000002b00000000000000a60000000000000083000000000000009d000000000000006e0000000000000055000000000000003f00000000000000880000000000000003000000000000006f000000000000002f000000000000008e00000000000000a6000000000000002500000000000000bd0000000000000032000000000000008b000000000000007300000000000000bf000000000000000e000000000000006300000000000000b000000000000000b90000000000000096000000000000001a00000000000000ad000000000000001400000000000000a2000000000000004800000000000000c0000000000000001c0000000000000034000000000000001000000000000000b5000000000000006100000000000000910000000000000063) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree082 : PLift (Irreducible ((OeisA217703.polyS 82).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 1163) (f := 0x10000000000000028100000000000001ec000000000000047e0000000000000247000000000000018a00000000000003f2000000000000027d000000000000017d000000000000008200000000000000bb00000000000000d1000000000000033e0000000000000054000000000000038600000000000002d900000000000002cc00000000000001fa0000000000000223000000000000023f000000000000047d00000000000003b7000000000000041d0000000000000283000000000000046600000000000000d8000000000000000400000000000003090000000000000132000000000000005800000000000002dc00000000000000490000000000000421000000000000043100000000000004510000000000000167000000000000045200000000000001d4000000000000014f000000000000027000000000000003bc000000000000025d000000000000026d000000000000030a0000000000000323000000000000025e0000000000000123000000000000029d0000000000000379000000000000015800000000000001110000000000000006000000000000009c0000000000000094000000000000039800000000000001f7000000000000034500000000000001bd00000000000002dd00000000000003a4000000000000033300000000000003d5000000000000005a000000000000019900000000000000db000000000000022000000000000001c100000000000000ae00000000000002fa000000000000016f0000000000000225000000000000031b000000000000033d00000000000003e9000000000000000100000000000001fb00000000000002820000000000000120000000000000022d0000000000000377000000000000045f000000000000016e)
    (inv := 0x170000000000000018c000000000000035c000000000000017d000000000000003400000000000000cb000000000000001b00000000000001370000000000000377000000000000039300000000000003720000000000000444000000000000031c0000000000000012000000000000026a00000000000002d200000000000002ca00000000000002a200000000000003970000000000000305000000000000045a00000000000003d100000000000001be00000000000000ff000000000000002b000000000000040500000000000000fc0000000000000295000000000000007a000000000000037300000000000001f9000000000000019a000000000000036d000000000000014c000000000000046500000000000000400000000000000354000000000000001500000000000001a7000000000000036300000000000003e4000000000000007200000000000001fc0000000000000013000000000000022200000000000002fa000000000000001a0000000000000268000000000000000a000000000000005d00000000000000e600000000000000e9000000000000000f00000000000002940000000000000350000000000000034200000000000001ec00000000000003750000000000000167000000000000012200000000000001aa00000000000003b500000000000002f400000000000004300000000000000368000000000000025a000000000000046000000000000003bc00000000000001dc000000000000021200000000000000a30000000000000097000000000000007700000000000002b000000000000003db000000000000045900000000000001cd00000000000001f500000000000000950000000000000196000000000000019d00000000000003b1) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree083 : PLift (Irreducible ((OeisA217703.polyS 83).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 523) (f := 0x1880000000000000159000000000000007e00000000000000f1000000000000013d0000000000000165000000000000005700000000000001a40000000000000000000000000000003c000000000000019000000000000001c800000000000001d5000000000000014800000000000001a800000000000001fb00000000000001ed00000000000001f8000000000000002e0000000000000009000000000000008500000000000000f8000000000000003700000000000000f9000000000000011d00000000000000bd00000000000000ea00000000000000d0000000000000013c00000000000000490000000000000208000000000000015100000000000000ed000000000000017c000000000000019e000000000000000a000000000000010d0000000000000160000000000000001a00000000000000ba000000000000010c000000000000009e0000000000000118000000000000019100000000000001e5000000000000018e00000000000001d200000000000001550000000000000048000000000000003500000000000000b50000000000000030000000000000013500000000000001fa00000000000001f900000000000001ae000000000000016300000000000001b900000000000001c900000000000001a800000000000000920000000000000033000000000000014d00000000000001560000000000000169000000000000014800000000000001e9000000000000008d0000000000000092000000000000017a000000000000009c00000000000000e7000000000000006300000000000001d900000000000000a9000000000000008d000000000000001400000000000001360000000000000205000000000000007000000000000001ba000000000000008d000000000000006c)
    (inv := 0xb700000000000001e300000000000001a80000000000000059000000000000010b0000000000000112000000000000016600000000000001b6000000000000000d0000000000000209000000000000001c000000000000001800000000000000c40000000000000079000000000000014b0000000000000064000000000000011b000000000000012300000000000001bf00000000000001290000000000000175000000000000013a000000000000015100000000000000cb0000000000000146000000000000006d000000000000006700000000000000e600000000000001a30000000000000087000000000000017900000000000000a800000000000001cd000000000000010d00000000000000bc000000000000012b00000000000001ae0000000000000068000000000000019f000000000000001e000000000000018f000000000000016500000000000001b1000000000000002800000000000000be000000000000005c0000000000000074000000000000005d000000000000011900000000000000a000000000000000dc000000000000014600000000000000f300000000000001560000000000000124000000000000002c000000000000005800000000000000ac000000000000002f000000000000008c000000000000019f000000000000013800000000000000e800000000000000a9000000000000010a00000000000001e600000000000001d300000000000001a9000000000000016e000000000000005c00000000000001540000000000000195000000000000014b0000000000000201000000000000009500000000000000ea000000000000002300000000000000570000000000000066000000000000013800000000000001810000000000000169000000000000019c) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree084 : PLift (Irreducible ((OeisA217703.polyS 84).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 229) (f := 0x37000000000000002400000000000000bd000000000000004e00000000000000c900000000000000da00000000000000250000000000000036000000000000002900000000000000b9000000000000009f00000000000000da000000000000003600000000000000b90000000000000033000000000000008d00000000000000130000000000000064000000000000003100000000000000c100000000000000cb00000000000000c900000000000000a3000000000000000000000000000000bc00000000000000d3000000000000002100000000000000db000000000000007100000000000000cb000000000000009500000000000000cb00000000000000b4000000000000004200000000000000b100000000000000af0000000000000038000000000000002200000000000000d5000000000000004400000000000000e10000000000000036000000000000000d000000000000001e00000000000000bd00000000000000610000000000000047000000000000007b000000000000002f000000000000009b000000000000009300000000000000df000000000000002000000000000000620000000000000050000000000000009600000000000000ae0000000000000023000000000000001d000000000000008f0000000000000012000000000000002b00000000000000970000000000000053000000000000005c00000000000000b200000000000000a600000000000000e2000000000000007400000000000000650000000000000019000000000000002600000000000000b000000000000000b400000000000000a800000000000000de000000000000002c00000000000000b900000000000000d8000000000000000000000000000000680000000000000064000000000000001e0000000000000076)
    (inv := 0x4200000000000000cb00000000000000cd00000000000000d900000000000000d3000000000000001700000000000000b0000000000000002d0000000000000074000000000000008500000000000000440000000000000028000000000000001e000000000000003000000000000000d60000000000000080000000000000007e0000000000000035000000000000001b000000000000006d000000000000006500000000000000d00000000000000062000000000000009d00000000000000e300000000000000b1000000000000005500000000000000450000000000000007000000000000004a00000000000000a400000000000000c700000000000000a6000000000000006e00000000000000e3000000000000008f000000000000000c00000000000000a6000000000000004e00000000000000bd0000000000000064000000000000003400000000000000c00000000000000033000000000000000a0000000000000075000000000000007a0000000000000031000000000000004e000000000000001c000000000000002300000000000000a90000000000000040000000000000003e00000000000000a900000000000000ac000000000000002f000000000000002400000000000000100000000000000032000000000000007200000000000000630000000000000017000000000000007400000000000000b70000000000000050000000000000008f000000000000000c000000000000003c00000000000000a300000000000000b00000000000000055000000000000008c000000000000003900000000000000be000000000000003600000000000000c90000000000000066000000000000005d00000000000000a500000000000000dc000000000000000000000000000000170000000000000059) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree085 : PLift (Irreducible ((OeisA217703.polyS 85).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 809) (f := 0x6000000000000027600000000000002c9000000000000020e00000000000000a8000000000000020000000000000002d8000000000000021000000000000001f800000000000000e60000000000000249000000000000031500000000000000140000000000000094000000000000002a00000000000002630000000000000166000000000000028a00000000000000a000000000000002e600000000000001500000000000000178000000000000018f000000000000011a000000000000015a000000000000023f000000000000025f000000000000008400000000000003210000000000000119000000000000018e00000000000002d600000000000002fa000000000000027600000000000000650000000000000052000000000000006a00000000000001ab000000000000009f000000000000013000000000000000a5000000000000005200000000000000d20000000000000276000000000000014600000000000002ab0000000000000084000000000000017b000000000000020800000000000000310000000000000061000000000000023b0000000000000202000000000000022a00000000000001bc0000000000000190000000000000031300000000000001290000000000000237000000000000030d00000000000000a2000000000000017900000000000001e20000000000000253000000000000000300000000000000ed0000000000000142000000000000013500000000000001070000000000000137000000000000030b00000000000002ed00000000000002e700000000000001f60000000000000208000000000000022c00000000000002ef0000000000000195000000000000007c000000000000021300000000000000b700000000000002e60000000000000119000000000000032400000000000000e7)
    (inv := 0xef00000000000000ab0000000000000248000000000000016100000000000001530000000000000224000000000000031300000000000002f400000000000001de000000000000016a000000000000020300000000000001fc00000000000002d6000000000000029a00000000000002890000000000000119000000000000007f0000000000000153000000000000005500000000000002ce00000000000002f50000000000000309000000000000007b000000000000000900000000000001280000000000000258000000000000023f00000000000001980000000000000173000000000000026c000000000000027e00000000000001b6000000000000015f000000000000002200000000000002aa000000000000029700000000000002a500000000000002f60000000000000217000000000000025c00000000000000e000000000000002af000000000000021e0000000000000214000000000000010800000000000002ac0000000000000189000000000000021100000000000000e1000000000000006c00000000000000cd000000000000028d0000000000000327000000000000011800000000000000d600000000000000e8000000000000006600000000000001e1000000000000032100000000000002c0000000000000025e00000000000002450000000000000056000000000000020a00000000000001c000000000000002b10000000000000201000000000000031e0000000000000013000000000000008300000000000002d000000000000002a60000000000000014000000000000020600000000000001db000000000000019b000000000000001a00000000000001c300000000000001eb00000000000000a20000000000000004000000000000025800000000000001770000000000000172000000000000001b) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree086 : PLift (Irreducible ((OeisA217703.polyS 86).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 379) (f := 0x10200000000000000a1000000000000003a00000000000000c6000000000000005c00000000000001230000000000000009000000000000008200000000000001410000000000000175000000000000015e0000000000000114000000000000002200000000000000d4000000000000010a0000000000000167000000000000007a000000000000013d000000000000016d00000000000001070000000000000145000000000000012e00000000000000c30000000000000145000000000000000600000000000001570000000000000010000000000000014100000000000000f5000000000000008900000000000000d2000000000000010c000000000000002900000000000000e900000000000000bf00000000000000d000000000000000d4000000000000003300000000000000d900000000000001260000000000000084000000000000014e0000000000000164000000000000000c00000000000000ed000000000000002000000000000000e200000000000000b600000000000000f9000000000000009000000000000000af000000000000014a000000000000001000000000000000bc000000000000009c0000000000000085000000000000004c000000000000001b00000000000000b200000000000000f800000000000000d200000000000001100000000000000087000000000000006e00000000000000f4000000000000016600000000000000cc00000000000000b80000000000000116000000000000016e0000000000000136000000000000016c0000000000000134000000000000012b000000000000008500000000000000d900000000000000c3000000000000003300000000000000ac00000000000000100000000000000175000000000000012e0000000000000136000000000000002a00000000000000af00000000000000a3)
    (inv := 0x150000000000000001f00000000000000340000000000000119000000000000011b0000000000000035000000000000017500000000000000e300000000000000380000000000000015000000000000016d000000000000003900000000000000520000000000000080000000000000001f0000000000000051000000000000016f0000000000000080000000000000001200000000000000340000000000000101000000000000003a000000000000008a0000000000000060000000000000010b00000000000000420000000000000030000000000000000500000000000000d800000000000000e9000000000000008400000000000000c20000000000000081000000000000012a00000000000000ea0000000000000037000000000000002000000000000000dd000000000000012200000000000000b500000000000000b700000000000001410000000000000053000000000000007900000000000000e3000000000000007c00000000000000e000000000000000e80000000000000023000000000000013b000000000000001900000000000000440000000000000008000000000000005200000000000000db000000000000006b00000000000001700000000000000005000000000000009b00000000000000aa000000000000016300000000000000ea000000000000011300000000000000ef000000000000009800000000000001610000000000000000000000000000013000000000000000b1000000000000014c000000000000013c00000000000000b7000000000000011d0000000000000066000000000000006b00000000000000c900000000000001060000000000000061000000000000009b0000000000000101000000000000016a00000000000000f50000000000000045000000000000003f00000000000000bb0000000000000043) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree087 : PLift (Irreducible ((OeisA217703.polyS 87).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 307) (f := 0xf1000000000000006500000000000000ec000000000000007300000000000000ea000000000000008f00000000000000dc0000000000000073000000000000007a00000000000000cf00000000000000bf00000000000000060000000000000026000000000000004300000000000000ee00000000000000da00000000000000c3000000000000003e0000000000000013000000000000008b000000000000009500000000000000c3000000000000006a0000000000000097000000000000009d00000000000000a4000000000000012800000000000000ca000000000000008400000000000000c700000000000001120000000000000038000000000000001a00000000000000cb0000000000000053000000000000006c000000000000007200000000000000fb00000000000000c9000000000000009e00000000000000f800000000000000be000000000000006b00000000000000bc000000000000005500000000000000980000000000000078000000000000003d00000000000000e1000000000000007a000000000000012d00000000000000080000000000000065000000000000002800000000000001010000000000000036000000000000001900000000000000d0000000000000002f00000000000000f30000000000000005000000000000009400000000000000f400000000000000df00000000000000f200000000000001300000000000000004000000000000009000000000000000c60000000000000036000000000000007200000000000000c8000000000000011b00000000000000b40000000000000130000000000000006100000000000000500000000000000077000000000000004b000000000000010c00000000000000980000000000000088000000000000003b000000000000005f00000000000000a000000000000000240000000000000035)
    (inv := 0xe7000000000000003f00000000000000e200000000000000e700000000000000bd00000000000000a50000000000000053000000000000007f00000000000000800000000000000074000000000000012d000000000000007200000000000000b800000000000000ae00000000000000ac00000000000000cc0000000000000062000000000000003100000000000000ab000000000000005d00000000000000690000000000000021000000000000009f000000000000010f00000000000000f5000000000000007b00000000000000ce00000000000001100000000000000111000000000000011b00000000000000a4000000000000000e00000000000000fa000000000000009e000000000000010100000000000000d60000000000000100000000000000010900000000000000df00000000000000fa00000000000000f600000000000000b900000000000000b8000000000000000f000000000000008f00000000000000210000000000000019000000000000006e000000000000008f00000000000000b2000000000000003e0000000000000022000000000000009700000000000000f30000000000000048000000000000004c000000000000010200000000000000d900000000000000970000000000000028000000000000003b000000000000000f0000000000000031000000000000008f00000000000000a30000000000000088000000000000002e0000000000000130000000000000011d00000000000000bd000000000000012b000000000000000f00000000000000f800000000000000910000000000000050000000000000002b000000000000006b00000000000000b40000000000000058000000000000008c0000000000000111000000000000000c0000000000000060000000000000005900000000000000d2000000000000009e00000000000000dc) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree088 : PLift (Irreducible ((OeisA217703.polyS 88).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 179) (f := 0x85000000000000005b00000000000000ad0000000000000021000000000000002e000000000000005600000000000000a0000000000000002500000000000000250000000000000061000000000000002400000000000000a7000000000000007b00000000000000750000000000000002000000000000000200000000000000aa000000000000006400000000000000b100000000000000a600000000000000ab000000000000007800000000000000aa00000000000000460000000000000081000000000000006300000000000000350000000000000089000000000000004c00000000000000390000000000000026000000000000003f000000000000009a000000000000005b000000000000009c00000000000000a000000000000000a10000000000000069000000000000004e000000000000000d00000000000000b2000000000000002a000000000000004c00000000000000230000000000000047000000000000002b0000000000000057000000000000009b0000000000000064000000000000004a000000000000003d000000000000006b0000000000000048000000000000008b0000000000000084000000000000006e000000000000009a000000000000009a000000000000005c0000000000000018000000000000002800000000000000730000000000000057000000000000003800000000000000760000000000000082000000000000005e00000000000000a0000000000000005f0000000000000053000000000000004f0000000000000010000000000000008e00000000000000540000000000000096000000000000008e000000000000001f000000000000002b0000000000000021000000000000009b0000000000000065000000000000004e000000000000009a000000000000004600000000000000a80000000000000053000000000000009b0000000000000098)
    (inv := 0xb000000000000004d0000000000000046000000000000008a000000000000001e00000000000000ab000000000000004e0000000000000098000000000000004d000000000000009b000000000000003d000000000000007500000000000000a400000000000000a4000000000000002000000000000000370000000000000024000000000000002e000000000000008d0000000000000012000000000000000e00000000000000090000000000000021000000000000003d000000000000008a00000000000000ae00000000000000900000000000000086000000000000004e000000000000000800000000000000950000000000000083000000000000000e000000000000009800000000000000ab0000000000000043000000000000007b000000000000006a0000000000000068000000000000003400000000000000b2000000000000003f000000000000009700000000000000930000000000000078000000000000001a00000000000000170000000000000086000000000000007a000000000000003b000000000000008f0000000000000019000000000000001e000000000000006e0000000000000041000000000000001400000000000000a3000000000000009c0000000000000009000000000000008b000000000000009900000000000000080000000000000002000000000000003b0000000000000046000000000000003300000000000000920000000000000035000000000000000f0000000000000076000000000000004b000000000000006e000000000000004b0000000000000001000000000000007f0000000000000084000000000000009a0000000000000011000000000000007e00000000000000250000000000000029000000000000007f00000000000000030000000000000086000000000000000e0000000000000082000000000000007f0000000000000034) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree089 : PLift (Irreducible ((OeisA217703.polyS 89).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 673) (f := 0xa600000000000000f60000000000000050000000000000025900000000000000ef00000000000000270000000000000234000000000000001d00000000000000e7000000000000028d00000000000000ca000000000000004b00000000000001bd0000000000000011000000000000022f00000000000001e2000000000000018e0000000000000129000000000000020500000000000000a50000000000000161000000000000025d00000000000000f9000000000000029f000000000000006e000000000000006500000000000000a0000000000000022400000000000001e9000000000000013c00000000000002850000000000000083000000000000020600000000000001c4000000000000015d000000000000023b000000000000012a0000000000000096000000000000019d00000000000001fe00000000000001e400000000000001b2000000000000028b000000000000012c00000000000000f500000000000001aa00000000000002180000000000000177000000000000003c000000000000020000000000000001ab00000000000000b00000000000000086000000000000011500000000000002300000000000000284000000000000001e000000000000020300000000000000f0000000000000010800000000000001e9000000000000001a000000000000016a000000000000006e000000000000027000000000000001a8000000000000021d0000000000000157000000000000027600000000000001d500000000000001ac000000000000003600000000000000bd000000000000007600000000000000290000000000000124000000000000029100000000000000af000000000000006e000000000000014c000000000000021000000000000001d60000000000000001000000000000010b0000000000000254000000000000013a00000000000001d3000000000000019300000000000001e5)
    (inv := 0x1e000000000000029d00000000000001cd00000000000000e6000000000000029f00000000000001ca000000000000022400000000000000fe000000000000026d000000000000022f00000000000001f500000000000000af00000000000000f900000000000001810000000000000151000000000000023100000000000001ae0000000000000059000000000000010900000000000001b60000000000000068000000000000005f0000000000000200000000000000011300000000000000f00000000000000075000000000000015a00000000000002a0000000000000014b000000000000001900000000000000a300000000000000a30000000000000262000000000000008500000000000001b000000000000002540000000000000163000000000000014f00000000000000850000000000000256000000000000003700000000000001be0000000000000035000000000000014200000000000000ea000000000000000e000000000000026f000000000000008a00000000000000aa0000000000000059000000000000009c00000000000001f200000000000000d2000000000000007600000000000000e1000000000000017800000000000002a00000000000000023000000000000024b000000000000013a0000000000000232000000000000010c000000000000000700000000000000f900000000000000ab00000000000001bf000000000000003e000000000000004000000000000000ab000000000000005000000000000001cf00000000000001ec00000000000000180000000000000296000000000000007e0000000000000030000000000000013600000000000001740000000000000280000000000000004600000000000001d2000000000000002d000000000000029900000000000000e3000000000000000c00000000000002430000000000000295000000000000029c000000000000029c) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree090 : PLift (Irreducible ((OeisA217703.polyS 90).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 821) (f := 0x2d900000000000001fd0000000000000014000000000000027f0000000000000047000000000000025000000000000002d6000000000000019700000000000002eb000000000000007700000000000001bf000000000000024e00000000000001da0000000000000252000000000000002400000000000000ce000000000000028900000000000000a100000000000001af000000000000004c000000000000015a0000000000000116000000000000003e0000000000000236000000000000000b000000000000009d00000000000001af00000000000000f9000000000000019500000000000001f800000000000000090000000000000180000000000000009c0000000000000200000000000000001f000000000000007100000000000000e000000000000001920000000000000122000000000000020700000000000002e400000000000000da00000000000001eb0000000000000038000000000000018600000000000002f1000000000000032100000000000000f3000000000000006500000000000002730000000000000020000000000000013b00000000000001d700000000000000a300000000000001820000000000000329000000000000012d00000000000000b0000000000000017b00000000000000cb000000000000019d000000000000032a00000000000001db00000000000001bf00000000000000e7000000000000003400000000000001cd000000000000001f00000000000000740000000000000233000000000000020f000000000000024200000000000000db0000000000000146000000000000024400000000000001ff000000000000000a0000000000000066000000000000033200000000000000a200000000000000980000000000000249000000000000026600000000000001a200000000000001b000000000000000bd00000000000000ae000000000000001700000000000001b2000000000000004d)
    (inv := 0x1510000000000000075000000000000004f00000000000001c900000000000002f300000000000000cb000000000000000800000000000002f100000000000000d8000000000000022f0000000000000315000000000000010800000000000001bf000000000000004c00000000000002360000000000000321000000000000020c000000000000006800000000000001860000000000000263000000000000007b000000000000001c00000000000001b800000000000001bd000000000000024e000000000000024f000000000000021d0000000000000236000000000000016800000000000001ad000000000000031c00000000000001910000000000000159000000000000014700000000000000a800000000000002af000000000000009e0000000000000049000000000000031900000000000001d3000000000000024f0000000000000218000000000000024300000000000001150000000000000151000000000000018d00000000000002f7000000000000009700000000000000c20000000000000000000000000000020e000000000000005f0000000000000332000000000000001c00000000000002fc00000000000000e000000000000000dd000000000000027f000000000000014900000000000000a40000000000000113000000000000006b0000000000000183000000000000021300000000000001c200000000000002950000000000000293000000000000029e00000000000001f4000000000000024a00000000000002c400000000000000fb000000000000007c0000000000000029000000000000006b000000000000023300000000000002ff0000000000000333000000000000024a000000000000018800000000000000b5000000000000024d00000000000002f0000000000000025500000000000000b7000000000000008e000000000000011500000000000001db000000000000031d000000000000004b) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree091 : PLift (Irreducible ((OeisA217703.polyS 91).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 103) (f := 0x5c00000000000000470000000000000050000000000000004a0000000000000060000000000000006600000000000000160000000000000023000000000000001900000000000000540000000000000001000000000000001e0000000000000018000000000000003b000000000000004a000000000000003400000000000000140000000000000062000000000000003400000000000000040000000000000034000000000000005c00000000000000030000000000000025000000000000004500000000000000000000000000000028000000000000003d000000000000002b0000000000000018000000000000003900000000000000530000000000000062000000000000004c00000000000000400000000000000005000000000000001c0000000000000063000000000000005f00000000000000380000000000000018000000000000003a000000000000004500000000000000030000000000000041000000000000002a00000000000000160000000000000019000000000000005900000000000000090000000000000047000000000000004e000000000000000e000000000000002800000000000000390000000000000031000000000000001000000000000000140000000000000018000000000000005e0000000000000035000000000000001f000000000000002700000000000000530000000000000000000000000000001d0000000000000048000000000000004d0000000000000051000000000000005400000000000000070000000000000041000000000000004e00000000000000180000000000000019000000000000004e000000000000005d0000000000000003000000000000000c000000000000002f00000000000000520000000000000027000000000000004f0000000000000049000000000000001a000000000000000d0000000000000042000000000000000800000000000000170000000000000040000000000000002f)
    (inv := 0x380000000000000037000000000000004d000000000000005c0000000000000043000000000000002c000000000000002a000000000000004400000000000000600000000000000058000000000000003e0000000000000007000000000000004e0000000000000060000000000000001f00000000000000130000000000000012000000000000002b0000000000000001000000000000003b000000000000003d000000000000001700000000000000650000000000000016000000000000000500000000000000000000000000000013000000000000001000000000000000570000000000000054000000000000003a0000000000000060000000000000003c000000000000002700000000000000350000000000000045000000000000002e0000000000000049000000000000004100000000000000640000000000000023000000000000004f000000000000000c000000000000005e0000000000000009000000000000002d00000000000000640000000000000028000000000000003d0000000000000060000000000000001c00000000000000070000000000000058000000000000000b000000000000001e000000000000005800000000000000520000000000000026000000000000002e000000000000002f0000000000000027000000000000004c000000000000006100000000000000560000000000000039000000000000000e000000000000002e000000000000004a000000000000001c0000000000000011000000000000000d000000000000000300000000000000140000000000000045000000000000002a000000000000006400000000000000160000000000000059000000000000002d0000000000000001000000000000000d0000000000000045000000000000000e00000000000000130000000000000019000000000000004f0000000000000057000000000000003d000000000000002e000000000000002a000000000000003f) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree092 : PLift (Irreducible ((OeisA217703.polyS 92).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 613) (f := 0x1d2000000000000009100000000000001310000000000000256000000000000023500000000000001da00000000000000d000000000000001db000000000000019100000000000001d80000000000000224000000000000024300000000000001ed0000000000000235000000000000021d00000000000002360000000000000237000000000000000800000000000001e6000000000000015a00000000000000e90000000000000126000000000000018200000000000001bf000000000000023c00000000000000a9000000000000024b000000000000014f00000000000001df00000000000000bc000000000000012900000000000001a700000000000001490000000000000058000000000000021a00000000000001eb00000000000000cd000000000000015d000000000000003d000000000000017e00000000000001ce00000000000001af0000000000000015000000000000020200000000000000ee00000000000000b800000000000001c400000000000001bc000000000000023300000000000000f8000000000000006900000000000001b40000000000000167000000000000014100000000000001bf00000000000001bf000000000000000700000000000000010000000000000121000000000000012f000000000000017e0000000000000171000000000000017500000000000001410000000000000157000000000000016b00000000000000b2000000000000017d00000000000000990000000000000078000000000000017700000000000001b6000000000000020a00000000000001c000000000000000b6000000000000001800000000000000a900000000000001ce000000000000001d00000000000001c400000000000001d8000000000000015800000000000000d40000000000000075000000000000020b000000000000000100000000000000180000000000000014000000000000019a0000000000000256000000000000009a00000000000000c7)
    (inv := 0x220000000000000005b00000000000001f2000000000000004f000000000000013600000000000001690000000000000237000000000000013200000000000000e2000000000000001e0000000000000188000000000000001f000000000000006d00000000000000750000000000000220000000000000008c0000000000000100000000000000024000000000000000e7000000000000004e0000000000000198000000000000025600000000000002200000000000000262000000000000014f000000000000005b0000000000000009000000000000002f00000000000000ac00000000000001b5000000000000001e00000000000001a2000000000000013600000000000000e800000000000000b60000000000000141000000000000016c000000000000013e000000000000001f00000000000001870000000000000114000000000000012600000000000001be0000000000000255000000000000006300000000000001a200000000000001aa00000000000001fb00000000000001b000000000000001d300000000000000aa00000000000000ba000000000000016800000000000000b00000000000000049000000000000015500000000000000da0000000000000071000000000000008b000000000000005a00000000000001cf000000000000002d000000000000023800000000000001b5000000000000013f000000000000023f00000000000002100000000000000132000000000000015c00000000000001710000000000000264000000000000020b00000000000001a400000000000001a6000000000000020b000000000000011400000000000000f7000000000000009f000000000000022c0000000000000242000000000000004700000000000000ed00000000000001fc00000000000000b700000000000001df00000000000001b2000000000000015000000000000001a70000000000000013000000000000005e00000000000000d500000000000001ea) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree093 : PLift (Irreducible ((OeisA217703.polyS 93).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 499) (f := 0xfa0000000000000128000000000000015800000000000000ec0000000000000149000000000000001900000000000000a50000000000000063000000000000011b000000000000018100000000000000e6000000000000003e000000000000017600000000000001d7000000000000017d0000000000000025000000000000007e0000000000000179000000000000015b000000000000009000000000000000db000000000000016c00000000000001b6000000000000002f000000000000001600000000000001e6000000000000005e00000000000001ab000000000000008c00000000000001830000000000000065000000000000013300000000000001a0000000000000005b00000000000001df000000000000003d000000000000005d000000000000013200000000000000ba00000000000001770000000000000171000000000000019a00000000000001cc00000000000000b5000000000000003c00000000000000c100000000000000e000000000000001b6000000000000003b0000000000000088000000000000006900000000000001cf000000000000017f000000000000019b00000000000000de0000000000000148000000000000012800000000000001b200000000000001230000000000000081000000000000015b00000000000000d800000000000000e700000000000000f500000000000000750000000000000102000000000000011000000000000001170000000000000181000000000000008600000000000000a200000000000000360000000000000028000000000000018b0000000000000125000000000000000f000000000000015f00000000000001a100000000000000230000000000000066000000000000015b0000000000000073000000000000019c00000000000000de00000000000000f200000000000000eb000000000000007d00000000000000d00000000000000147000000000000006800000000000000a600000000000000fc0000000000000166)
    (inv := 0x21000000000000016300000000000000db000000000000000600000000000000fa000000000000014900000000000001dc0000000000000063000000000000013c000000000000007c000000000000010500000000000000f30000000000000065000000000000017c00000000000000c500000000000000db000000000000015900000000000001d5000000000000010a00000000000001a8000000000000000700000000000001de00000000000000e4000000000000004c00000000000000bd000000000000009a000000000000017c0000000000000184000000000000002d0000000000000124000000000000007f00000000000001e500000000000001e30000000000000075000000000000014f00000000000001ea00000000000000030000000000000018000000000000003900000000000001ec000000000000016f0000000000000150000000000000004b000000000000012200000000000000cd0000000000000034000000000000002d00000000000001db000000000000015000000000000001e600000000000001aa000000000000018d0000000000000133000000000000002a0000000000000159000000000000009c000000000000007b00000000000001ca000000000000001300000000000001a40000000000000081000000000000010300000000000000ca00000000000001e00000000000000182000000000000001000000000000001a2000000000000009700000000000000cf000000000000017c00000000000001b100000000000000d100000000000000a60000000000000196000000000000009800000000000000a5000000000000001d000000000000001400000000000000ef00000000000001ef00000000000001bf00000000000001d9000000000000001a00000000000001c3000000000000012900000000000000de000000000000005c000000000000004c000000000000010d000000000000017400000000000000ca00000000000000c10000000000000086) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree094 : PLift (Irreducible ((OeisA217703.polyS 94).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 1063) (f := 0x38400000000000001fc00000000000001f6000000000000000000000000000000d20000000000000060000000000000032f000000000000028a000000000000008a000000000000019f000000000000041c00000000000002fd000000000000029900000000000002d500000000000001cf00000000000000b20000000000000203000000000000033c0000000000000179000000000000031f000000000000014100000000000001b3000000000000005700000000000000f6000000000000028c000000000000009d00000000000001a300000000000000ac00000000000000da000000000000029000000000000003890000000000000129000000000000039400000000000002530000000000000214000000000000010000000000000002c400000000000000e3000000000000003e000000000000014f000000000000007200000000000002e8000000000000011100000000000001f3000000000000041f0000000000000228000000000000036e000000000000034200000000000001d000000000000000ca000000000000023300000000000001c300000000000002a5000000000000010e00000000000003a200000000000003ac0000000000000024000000000000008c000000000000034600000000000000340000000000000383000000000000038d00000000000002ac00000000000002d30000000000000177000000000000011b00000000000000a6000000000000011500000000000001fe000000000000026d000000000000023c0000000000000143000000000000034e00000000000000ba00000000000001e800000000000003d400000000000000a40000000000000187000000000000017b000000000000017f00000000000002590000000000000272000000000000012e00000000000000240000000000000059000000000000012c000000000000011300000000000001630000000000000205000000000000038f0000000000000397000000000000016500000000000003db00000000000003b4)
    (inv := 0x9300000000000003df000000000000027900000000000000c20000000000000324000000000000016c00000000000002bf000000000000028e000000000000039100000000000000e1000000000000007300000000000000350000000000000054000000000000015f00000000000000bb00000000000001b00000000000000321000000000000022f0000000000000304000000000000013b00000000000002000000000000000204000000000000020d00000000000001c9000000000000001300000000000000c500000000000000e5000000000000010b0000000000000019000000000000041e000000000000027200000000000003c3000000000000020e000000000000020c000000000000003c000000000000018b000000000000040d000000000000025b0000000000000398000000000000028e00000000000004150000000000000259000000000000024600000000000001bc000000000000029c000000000000009f00000000000002c900000000000001ad000000000000031200000000000000f90000000000000152000000000000004f00000000000000d10000000000000158000000000000032d00000000000003eb000000000000019200000000000001e2000000000000000c00000000000003cf000000000000002f000000000000032300000000000000560000000000000095000000000000036a000000000000019c000000000000000100000000000001be000000000000028c0000000000000413000000000000008800000000000000e2000000000000032300000000000000c300000000000001650000000000000147000000000000025a00000000000003a100000000000003f90000000000000100000000000000040900000000000000c8000000000000014b0000000000000143000000000000013f00000000000000450000000000000103000000000000026a00000000000001d5000000000000037000000000000000020000000000000327000000000000035f0000000000000159) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree095 : PLift (Irreducible ((OeisA217703.polyS 95).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 857) (f := 0x2f6000000000000035800000000000002280000000000000124000000000000010700000000000000e900000000000000c700000000000000d000000000000002de000000000000022b0000000000000243000000000000004800000000000000d1000000000000027800000000000002f900000000000001f000000000000003010000000000000320000000000000007c000000000000027d000000000000008800000000000002c200000000000000e1000000000000029500000000000001f600000000000001e500000000000001c500000000000000b3000000000000025e000000000000005c000000000000021600000000000000b300000000000003300000000000000062000000000000009f0000000000000145000000000000006c000000000000016f00000000000001c8000000000000012e000000000000021000000000000002db0000000000000117000000000000027100000000000002c5000000000000032100000000000003580000000000000293000000000000010b000000000000018d00000000000003380000000000000335000000000000020f00000000000003360000000000000261000000000000013a00000000000003130000000000000264000000000000014500000000000002df00000000000001bf000000000000006d000000000000032c000000000000024100000000000002f60000000000000041000000000000013300000000000001f600000000000000d10000000000000208000000000000013500000000000001b900000000000003030000000000000177000000000000001b000000000000024100000000000002fe000000000000010d000000000000023b00000000000002f000000000000002940000000000000034000000000000016e000000000000034e000000000000031400000000000002b400000000000000640000000000000312000000000000015100000000000001ef000000000000029f00000000000002860000000000000005000000000000032e0000000000000086)
    (inv := 0xd900000000000001b000000000000001010000000000000032000000000000001a000000000000031a00000000000002fa000000000000034b000000000000001e000000000000011a000000000000033b00000000000002a500000000000001d2000000000000013000000000000002430000000000000251000000000000006a000000000000033f00000000000002c500000000000000e800000000000002c2000000000000022f00000000000001c4000000000000025e000000000000006d0000000000000085000000000000016b00000000000002bb000000000000009000000000000001e30000000000000138000000000000003200000000000002be00000000000000ec00000000000000980000000000000010000000000000001200000000000001b70000000000000123000000000000007e000000000000012c000000000000015b000000000000005e000000000000032f000000000000029200000000000001ec00000000000000fd0000000000000051000000000000031b000000000000010100000000000000b500000000000002ac00000000000001e8000000000000015d000000000000003600000000000002940000000000000107000000000000014b0000000000000061000000000000015000000000000001d90000000000000105000000000000002e00000000000000bf00000000000000a000000000000000c2000000000000022700000000000001d40000000000000006000000000000029b000000000000002500000000000002e100000000000001d300000000000000c4000000000000033e000000000000031e000000000000030900000000000002d90000000000000351000000000000012000000000000002a70000000000000161000000000000030d00000000000002f700000000000001c500000000000002be00000000000002dd000000000000016900000000000000280000000000000229000000000000002e00000000000000590000000000000342000000000000018d00000000000000e8) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree096 : PLift (Irreducible ((OeisA217703.polyS 96).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 347) (f := 0xcf00000000000001460000000000000037000000000000015900000000000000ac000000000000003000000000000000b000000000000000ce000000000000006a000000000000002f00000000000000ab00000000000000d900000000000000bc000000000000014a000000000000012e00000000000000c5000000000000007000000000000000ab00000000000000720000000000000092000000000000012b000000000000000800000000000000cc00000000000000950000000000000026000000000000005c00000000000000ee00000000000000d400000000000001140000000000000096000000000000001a0000000000000014000000000000012200000000000000d2000000000000000e00000000000000a6000000000000012c00000000000001140000000000000074000000000000005b00000000000000730000000000000149000000000000000c000000000000012f000000000000007100000000000000a4000000000000007b000000000000009d0000000000000153000000000000012e00000000000000f900000000000001190000000000000056000000000000002b000000000000013600000000000000600000000000000017000000000000004f000000000000003b000000000000005e00000000000000a100000000000000910000000000000137000000000000005b00000000000000d9000000000000008b00000000000000dd000000000000002900000000000000bd000000000000004300000000000000df000000000000014000000000000000c5000000000000000a00000000000000ad000000000000002a000000000000010b00000000000000600000000000000137000000000000001400000000000000970000000000000023000000000000001500000000000000f500000000000000e8000000000000012f00000000000000e9000000000000010e000000000000011700000000000000dd000000000000013d000000000000012b00000000000000a1000000000000007d000000000000013f00000000000000ea)
    (inv := 0x10d00000000000000360000000000000044000000000000008c00000000000001450000000000000008000000000000011b00000000000000c100000000000000c900000000000000a40000000000000141000000000000011600000000000000cd000000000000008d0000000000000046000000000000000d0000000000000061000000000000010b00000000000000d50000000000000010000000000000010800000000000000540000000000000043000000000000008300000000000000f400000000000000a40000000000000078000000000000007500000000000000f600000000000000bd000000000000006b00000000000000c500000000000000ca00000000000000d100000000000000d600000000000000220000000000000135000000000000014000000000000000a300000000000000bb000000000000009c00000000000000fa000000000000004f000000000000009400000000000001330000000000000068000000000000008b000000000000013400000000000000bd00000000000000220000000000000038000000000000011f0000000000000074000000000000005600000000000000750000000000000026000000000000008300000000000000f6000000000000002d000000000000007200000000000001000000000000000021000000000000005f0000000000000132000000000000002700000000000000f20000000000000047000000000000006700000000000000a70000000000000078000000000000015700000000000000e60000000000000029000000000000007700000000000000d900000000000000d900000000000000d50000000000000072000000000000007c000000000000006f00000000000000c3000000000000007e000000000000005600000000000000d80000000000000002000000000000002d0000000000000018000000000000000b000000000000007c0000000000000078000000000000004b0000000000000028000000000000003b000000000000000a00000000000001030000000000000100) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree097 : PLift (Irreducible ((OeisA217703.polyS 97).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 101) (f := 0x3d00000000000000070000000000000019000000000000003c000000000000000d000000000000003f0000000000000038000000000000005800000000000000620000000000000039000000000000002500000000000000000000000000000000000000000000004c000000000000004a000000000000001e0000000000000056000000000000005f0000000000000007000000000000001300000000000000330000000000000019000000000000005b000000000000001e000000000000000a0000000000000004000000000000000e000000000000001b00000000000000470000000000000026000000000000005b00000000000000060000000000000041000000000000005800000000000000250000000000000035000000000000002d00000000000000000000000000000039000000000000003600000000000000060000000000000021000000000000004d000000000000004900000000000000320000000000000002000000000000003c000000000000000d000000000000003a000000000000002000000000000000530000000000000040000000000000003c0000000000000001000000000000000a00000000000000160000000000000022000000000000004b0000000000000049000000000000003f0000000000000057000000000000002e0000000000000052000000000000000e00000000000000610000000000000044000000000000005c0000000000000055000000000000000d000000000000001a00000000000000380000000000000022000000000000004f0000000000000057000000000000003d0000000000000058000000000000000b00000000000000350000000000000005000000000000003e000000000000004b00000000000000230000000000000040000000000000002300000000000000150000000000000049000000000000004b00000000000000200000000000000031000000000000003900000000000000480000000000000048000000000000004a000000000000002e000000000000003600000000000000630000000000000038)
    (inv := 0x29000000000000004e00000000000000540000000000000058000000000000005a00000000000000610000000000000028000000000000001e00000000000000340000000000000061000000000000001f0000000000000028000000000000000300000000000000530000000000000011000000000000004f00000000000000560000000000000034000000000000000d0000000000000057000000000000000d000000000000003500000000000000140000000000000054000000000000002c000000000000003e00000000000000040000000000000031000000000000002d00000000000000190000000000000058000000000000005d000000000000000f000000000000004f000000000000005000000000000000610000000000000053000000000000004f0000000000000048000000000000002c000000000000005900000000000000630000000000000036000000000000000a00000000000000210000000000000015000000000000000a000000000000000d000000000000005c000000000000002f000000000000004500000000000000180000000000000020000000000000002e000000000000001f000000000000004e0000000000000063000000000000006300000000000000380000000000000029000000000000001b000000000000002000000000000000490000000000000013000000000000001d000000000000000f000000000000002e0000000000000000000000000000004d0000000000000033000000000000000b00000000000000440000000000000046000000000000001f0000000000000017000000000000004e00000000000000380000000000000035000000000000000a0000000000000062000000000000001f00000000000000500000000000000061000000000000004900000000000000040000000000000035000000000000004b00000000000000590000000000000011000000000000002800000000000000340000000000000009000000000000000c0000000000000010000000000000000000000000000000210000000000000052) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree098 : PLift (Irreducible ((OeisA217703.polyS 98).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 3041) (f := 0x3b6000000000000068c000000000000086500000000000000c50000000000000131000000000000079700000000000002da0000000000000bb5000000000000071900000000000009fa00000000000007dc000000000000064c00000000000004e9000000000000028b000000000000018c00000000000001f7000000000000060d000000000000000c0000000000000baa00000000000002ed0000000000000507000000000000003d00000000000005d80000000000000a36000000000000019c00000000000001e8000000000000071a00000000000001a400000000000008ff000000000000072a0000000000000a45000000000000017400000000000004dc00000000000004bd0000000000000955000000000000098a00000000000006d400000000000009ea00000000000009ea0000000000000b6600000000000005c200000000000003e20000000000000a6a00000000000000da00000000000007b300000000000004aa00000000000002c3000000000000056200000000000005b400000000000008db0000000000000302000000000000090d000000000000083700000000000000d80000000000000b6c00000000000004d400000000000006a900000000000004130000000000000b540000000000000784000000000000045e000000000000020c00000000000008430000000000000bc100000000000008c400000000000002f200000000000004c800000000000008b800000000000006a600000000000002c6000000000000035000000000000002d70000000000000b0b00000000000005e10000000000000ac300000000000003a600000000000008740000000000000b2500000000000003f800000000000006a00000000000000108000000000000092a0000000000000b6000000000000000e0000000000000099600000000000001b900000000000008b100000000000001d9000000000000043f000000000000058e00000000000003ea000000000000056f000000000000029a0000000000000668000000000000007e0000000000000b78000000000000030e00000000000008a3)
    (inv := 0x30100000000000000c0000000000000086300000000000004030000000000000b2300000000000005810000000000000427000000000000089d00000000000005ef0000000000000844000000000000048c000000000000050d00000000000002c70000000000000ac700000000000002a8000000000000094e00000000000000a000000000000008360000000000000186000000000000052500000000000005ac00000000000002d700000000000004d1000000000000015d00000000000001850000000000000078000000000000009e000000000000025b000000000000002400000000000008f40000000000000063000000000000022800000000000009c300000000000003f3000000000000037800000000000002b000000000000001f30000000000000aa800000000000004e5000000000000064c000000000000060400000000000009040000000000000172000000000000001e00000000000002c500000000000005f500000000000000e700000000000000a000000000000001fe00000000000001730000000000000589000000000000050c000000000000001100000000000007280000000000000b7f0000000000000965000000000000028300000000000001ff000000000000030d00000000000008ec000000000000094b00000000000007d20000000000000507000000000000025b00000000000001590000000000000848000000000000024300000000000009e4000000000000086300000000000003d9000000000000002b000000000000033100000000000005b80000000000000b41000000000000075f00000000000007ae00000000000001230000000000000b01000000000000055700000000000009fd000000000000078c00000000000004e5000000000000075100000000000005d1000000000000084800000000000004140000000000000862000000000000010d00000000000007c1000000000000092b0000000000000a4c0000000000000459000000000000088700000000000007d400000000000000340000000000000a0e00000000000002960000000000000b91) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree099 : PLift (Irreducible ((OeisA217703.polyS 99).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 1087) (f := 0x230000000000000090000000000000027c000000000000022200000000000002ea00000000000002d700000000000002f600000000000003a90000000000000071000000000000008000000000000002e100000000000001c200000000000002ca000000000000025f000000000000041900000000000003dc00000000000001d000000000000001390000000000000088000000000000024700000000000002e000000000000000170000000000000222000000000000009600000000000003bd00000000000003280000000000000053000000000000000f000000000000001100000000000000e9000000000000004d000000000000018a000000000000015f00000000000002ba00000000000003db0000000000000374000000000000035c00000000000003b600000000000000bf0000000000000299000000000000002000000000000000a4000000000000013d00000000000001e4000000000000019f0000000000000102000000000000030c00000000000002a2000000000000034c000000000000019d00000000000001510000000000000045000000000000002b00000000000001eb00000000000003f7000000000000003e00000000000001880000000000000345000000000000015400000000000001e400000000000000de000000000000007200000000000001fe00000000000001a2000000000000033400000000000001bb0000000000000297000000000000039400000000000001dc000000000000005500000000000002a600000000000003bb000000000000022600000000000003c200000000000000a5000000000000009900000000000002d800000000000001ee0000000000000334000000000000013a000000000000030a000000000000033d00000000000001d700000000000000d1000000000000036b00000000000000cc0000000000000077000000000000020b00000000000003de000000000000004c00000000000001aa00000000000001c7000000000000022e000000000000008d000000000000039e0000000000000230000000000000043c00000000000000e20000000000000353)
    (inv := 0xb5000000000000002e000000000000002b00000000000000e700000000000001d3000000000000002100000000000002d2000000000000018300000000000002f600000000000000ac000000000000017800000000000000d8000000000000016d00000000000002430000000000000405000000000000017f0000000000000151000000000000039400000000000003f3000000000000018e000000000000016b000000000000038100000000000001090000000000000040000000000000038b000000000000003600000000000003f800000000000001d4000000000000003b0000000000000407000000000000016d000000000000008b000000000000036000000000000001a6000000000000023b000000000000021c00000000000003ab00000000000000db00000000000002b2000000000000021000000000000003f000000000000001a5000000000000031f00000000000001690000000000000253000000000000019f00000000000003f400000000000003b9000000000000022f0000000000000271000000000000000a00000000000001fe00000000000000f300000000000003d100000000000003f00000000000000330000000000000037800000000000001f40000000000000245000000000000025f0000000000000395000000000000033a000000000000043200000000000001b3000000000000031b000000000000002600000000000000120000000000000336000000000000026000000000000002fa00000000000000ed000000000000026b000000000000005c000000000000010100000000000001fe00000000000002c1000000000000007600000000000001cf00000000000004250000000000000354000000000000028700000000000000fc000000000000010700000000000001540000000000000166000000000000023f00000000000001cb00000000000000c4000000000000008e000000000000023a000000000000018f00000000000001af0000000000000270000000000000040f00000000000000f100000000000000ae00000000000001f5000000000000009b0000000000000187) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private def verifiedDegree100 : PLift (Irreducible ((OeisA217703.polyS 100).map (Int.castRingHom ℚ))) :=
  ⟨OMA.PolynomialCertificate.certificateWithPrimeTest (p := 1153) (f := 0xa60000000000000026000000000000032f000000000000002200000000000003d300000000000002d000000000000002ed000000000000000800000000000003f5000000000000029a00000000000002bc000000000000023f000000000000004b0000000000000176000000000000035f0000000000000307000000000000025a00000000000000c1000000000000047800000000000001ef00000000000003510000000000000283000000000000026800000000000000880000000000000405000000000000008a000000000000037e000000000000008500000000000003e3000000000000025e0000000000000071000000000000025d0000000000000132000000000000044d0000000000000397000000000000018e000000000000032100000000000000220000000000000476000000000000026d000000000000021600000000000001d5000000000000014d0000000000000435000000000000038400000000000000100000000000000135000000000000037d00000000000000eb00000000000004370000000000000455000000000000021100000000000001ec00000000000001bc0000000000000373000000000000038200000000000001f200000000000003660000000000000116000000000000000400000000000000310000000000000440000000000000006300000000000002ce000000000000022b00000000000002f100000000000001bb000000000000012b0000000000000435000000000000022500000000000002c70000000000000056000000000000034b00000000000000b40000000000000412000000000000003300000000000000f50000000000000009000000000000046000000000000002ea00000000000002ef0000000000000382000000000000016b00000000000001e8000000000000033600000000000003e8000000000000022a000000000000019b000000000000010500000000000002e800000000000002f50000000000000262000000000000003600000000000001e7000000000000018c00000000000000ee000000000000039d0000000000000347000000000000001900000000000000c6)
    (inv := 0x35b000000000000044f000000000000013000000000000000d500000000000002b100000000000002390000000000000187000000000000018300000000000003440000000000000180000000000000007700000000000001bd0000000000000177000000000000039e00000000000003a100000000000002cd00000000000000d9000000000000047700000000000001a60000000000000149000000000000034d00000000000003b5000000000000029b000000000000023400000000000003a500000000000002bc00000000000001d500000000000002ea00000000000000ea0000000000000094000000000000010d0000000000000119000000000000025c000000000000021b000000000000047300000000000000390000000000000029000000000000012200000000000003ea000000000000022f00000000000003f000000000000002ad0000000000000102000000000000018f000000000000011c000000000000034a00000000000000af00000000000001f6000000000000029500000000000004400000000000000266000000000000042d000000000000038b00000000000000a50000000000000157000000000000042800000000000001ed000000000000011e00000000000001580000000000000158000000000000009f000000000000035000000000000001b900000000000001ed000000000000042a000000000000033d00000000000003a8000000000000030a00000000000003d000000000000002390000000000000084000000000000032d00000000000000310000000000000364000000000000028c000000000000025900000000000001a200000000000002ed00000000000002ad00000000000003f8000000000000036200000000000003cd000000000000036a0000000000000133000000000000029800000000000003d30000000000000221000000000000012a000000000000031a0000000000000463000000000000022a000000000000026500000000000003b4000000000000001a0000000000000378000000000000001200000000000000dc000000000000041e000000000000048000000000000003a5) (by decide +kernel) (by decide +kernel)⟩

theorem OMA.solution : OMA.R_OeisA217703_conjecture_1_R1.H1 := by
  intro n hlo hhi
  interval_cases n
  · exact verifiedDegree001.down
  · exact verifiedDegree002.down
  · exact verifiedDegree003.down
  · exact verifiedDegree004.down
  · exact verifiedDegree005.down
  · exact verifiedDegree006.down
  · exact verifiedDegree007.down
  · exact verifiedDegree008.down
  · exact verifiedDegree009.down
  · exact verifiedDegree010.down
  · exact verifiedDegree011.down
  · exact verifiedDegree012.down
  · exact verifiedDegree013.down
  · exact verifiedDegree014.down
  · exact verifiedDegree015.down
  · exact verifiedDegree016.down
  · exact verifiedDegree017.down
  · exact verifiedDegree018.down
  · exact verifiedDegree019.down
  · exact verifiedDegree020.down
  · exact verifiedDegree021.down
  · exact verifiedDegree022.down
  · exact verifiedDegree023.down
  · exact verifiedDegree024.down
  · exact verifiedDegree025.down
  · exact verifiedDegree026.down
  · exact verifiedDegree027.down
  · exact verifiedDegree028.down
  · exact verifiedDegree029.down
  · exact verifiedDegree030.down
  · exact verifiedDegree031.down
  · exact verifiedDegree032.down
  · exact verifiedDegree033.down
  · exact verifiedDegree034.down
  · exact verifiedDegree035.down
  · exact verifiedDegree036.down
  · exact verifiedDegree037.down
  · exact verifiedDegree038.down
  · exact verifiedDegree039.down
  · exact verifiedDegree040.down
  · exact verifiedDegree041.down
  · exact verifiedDegree042.down
  · exact verifiedDegree043.down
  · exact verifiedDegree044.down
  · exact verifiedDegree045.down
  · exact verifiedDegree046.down
  · exact verifiedDegree047.down
  · exact verifiedDegree048.down
  · exact verifiedDegree049.down
  · exact verifiedDegree050.down
  · exact verifiedDegree051.down
  · exact verifiedDegree052.down
  · exact verifiedDegree053.down
  · exact verifiedDegree054.down
  · exact verifiedDegree055.down
  · exact verifiedDegree056.down
  · exact verifiedDegree057.down
  · exact verifiedDegree058.down
  · exact verifiedDegree059.down
  · exact verifiedDegree060.down
  · exact verifiedDegree061.down
  · exact verifiedDegree062.down
  · exact verifiedDegree063.down
  · exact verifiedDegree064.down
  · exact verifiedDegree065.down
  · exact verifiedDegree066.down
  · exact verifiedDegree067.down
  · exact verifiedDegree068.down
  · exact verifiedDegree069.down
  · exact verifiedDegree070.down
  · exact verifiedDegree071.down
  · exact verifiedDegree072.down
  · exact verifiedDegree073.down
  · exact verifiedDegree074.down
  · exact verifiedDegree075.down
  · exact verifiedDegree076.down
  · exact verifiedDegree077.down
  · exact verifiedDegree078.down
  · exact verifiedDegree079.down
  · exact verifiedDegree080.down
  · exact verifiedDegree081.down
  · exact verifiedDegree082.down
  · exact verifiedDegree083.down
  · exact verifiedDegree084.down
  · exact verifiedDegree085.down
  · exact verifiedDegree086.down
  · exact verifiedDegree087.down
  · exact verifiedDegree088.down
  · exact verifiedDegree089.down
  · exact verifiedDegree090.down
  · exact verifiedDegree091.down
  · exact verifiedDegree092.down
  · exact verifiedDegree093.down
  · exact verifiedDegree094.down
  · exact verifiedDegree095.down
  · exact verifiedDegree096.down
  · exact verifiedDegree097.down
  · exact verifiedDegree098.down
  · exact verifiedDegree099.down
  · exact verifiedDegree100.down