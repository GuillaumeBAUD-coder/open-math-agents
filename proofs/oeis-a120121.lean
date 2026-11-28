import OMAStatements.S_oeis_a120121

/-!
# Decimal digit-product and digit-sum fixed points

The decimal length bound uses the leading digit and the fact that all other
digits are at most nine. The certified search examines sorted tails, pruning
whenever their largest possible completion cannot reach the required
magnitude. The totient lookup is checked against Mathlib, and the final
trials evaluate both digit statistics by transparent recursion.
-/


namespace DigitTotient


-- Ten bits per entry avoid repeated list traversals in the kernel certificate.
private def phiTable : ℕ :=
  0x906910c591086a0b0780d8570d07e8a0781063c104828a8820c0560d8730a866100511006c0807f0fc4e0dc640907d8fa530c87c8a4690f03c0d8700a07a8a8510f0798a2600dc420f06c080778ee4e0c05a09c690e84e0b863090748e83c0e073878730b0480e472090480e24b0e064078700c04a0de580906e8c03f0a06d890630d8380b46c0906b8a83c0d45a08c500d0450d269060688b4450c052084570cc440a0660805a0a8360c85a084640a0360c6630784e0c4410a858060610c03f0c03c0805f8be3f0905e86c540b8320a05d0784e0903c0b05b87848090370b455860598b2300b046074580a03607857070568ac2c0a84986c4b0803809c54060420a6360a452850450a0360a23c06c4808435080460684f09c2409c4e0604d878330784c8603c090320963f050420942d0903a0544909030070440603c0782408c4685c460602d08a45058320882408043848430842c06c34050418822a06036054400802007e370483e86429078360502a0782886e3c0403b860270742e0483a0701e05839048388701e06037848300502406c2d0482a06a23068348302d06021066280402a064210503183c3105418060300402f8481b05c2803c240581e0482d0302c8581d0501e0382b0541b04027030298521405028836210401a04e270301e03c180482582825048150481c0301e046170302282c22040120421b02820830150401f8241903c1403c1b8201803a12038160241c030120281b0241a8340c03019820190280f02a180201202e0f02c12018160280e02a10018148280d820138180f0240a02412018118180b020108140c0200901e0f0100e81c090180a0120d018080140a8100b816060140a80c0a010060120900c0601005010078080700c0480c050080580a0300804806040080200603004028040180401802010020080100400

private def phiFast (n : ℕ) : ℕ := (phiTable >>> (10*n)) % 1024

set_option maxHeartbeats 0 in
private theorem phiFast_eq (n : ℕ) (h : n ≤ 540) : phiFast n = Nat.totient n := by
  interval_cases n <;> decide +kernel




private def digitProduct : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, n =>
    if n = 0 then 1
    else if n % 10 = 0 then 0
    else (n % 10) * digitProduct f (n / 10)

private theorem digitProduct_correct (f n : ℕ) (h : n < 10^f) :
    digitProduct f n = (Nat.digits 10 n).prod := by
  induction f generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, digitProduct]
  | succ f ih =>
    by_cases h0 : n = 0
    · simp [h0, digitProduct]
    · have hn : 0 < n := Nat.pos_of_ne_zero h0
      rw [digitProduct, if_neg h0, Nat.digits_of_two_le_of_pos (by decide) hn, List.prod_cons]
      by_cases hm : n % 10 = 0
      · simp [hm]
      · rw [if_neg hm, ih]
        apply Nat.div_lt_of_lt_mul
        simpa [pow_succ, Nat.mul_comm] using h

private def digitSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f+1, n => if n = 0 then 0 else (n % 10) + digitSum f (n / 10)

private theorem digitSum_correct (f n : ℕ) (h : n < 10^f) :
    digitSum f n = (Nat.digits 10 n).sum := by
  induction f generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, digitSum]
  | succ f ih =>
    by_cases h0 : n = 0
    · simp [h0, digitSum]
    · have hn : 0 < n := Nat.pos_of_ne_zero h0
      rw [digitSum, if_neg h0, Nat.digits_of_two_le_of_pos (by decide) hn, List.sum_cons, ih]
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ, Nat.mul_comm] using h

private def trial (F : ℕ → ℕ → ℕ) (d p s lead : ℕ) : Bool :=
  let m := F (p*lead) (s+lead)
  (m ≤ 139968) || (m / 10^d != lead) || (m % 9 != (s+lead) % 9) ||
    (digitProduct (d+1) m != p*lead) || (digitSum (d+1) m != s+lead)

private theorem prod_sum_bound (digits : List ℕ) (hd : ∀ e ∈ digits, e ≤ 9) :
    digits.prod ≤ 9^digits.length ∧ digits.sum ≤ 9*digits.length := by
  induction digits with
  | nil => simp
  | cons e es ih =>
    have he := hd e List.mem_cons_self
    obtain ⟨hp, hs⟩ := ih (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    simp only [List.prod_cons, List.sum_cons, List.length_cons, pow_succ']
    exact ⟨Nat.mul_le_mul he hp, by omega⟩




private def finishCount (F : ℕ → ℕ → ℕ) (d p s : ℕ) : Bool :=
  if 27 ∣ p then trial F d p s (9-s%9)
  else (List.range 9).all fun j => trial F d p s (j+1)

private theorem finishCount_sound (F : ℕ → ℕ → ℕ) (d p s a : ℕ)
    (ha : 1 ≤ a) (ha' : a ≤ 9) (hmod : 27 ∣ p → (s+a)%9=0)
    (hf : finishCount F d p s = true) : trial F d p s a = true := by
  unfold finishCount at hf
  by_cases h : 27 ∣ p
  · rw [if_pos h] at hf
    have hm := hmod h
    have he : a = 9-s%9 := by omega
    simpa only [← he] using hf
  · rw [if_neg h,List.all_eq_true] at hf
    simpa only [Nat.sub_add_cancel ha] using hf (a-1) (List.mem_range.mpr (by omega))

/-- The search chooses the multiplicity of digit `lo`, then moves to the
next digit. All remaining digits equal 9 in the final branch. -/
private def scanCounts (F : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, k, p, s =>
    if p*9^k*(s+9*k+9) < 10^d then true
    else finishCount F d (p*9^k) (s+9*k)
  | f+1, lo, k, p, s =>
    if p*9^k*(s+9*k+9) < 10^d then true
    else (List.range (k+1)).all fun j =>
      scanCounts F d f (lo+1) (k-j) (p*lo^j) (s+lo*j)

private theorem scanCounts_sound (F : ℕ → ℕ → ℕ) (d f lo : ℕ)
    (hfuel : lo+f=9) (digits : List ℕ) (p s lead : ℕ)
    (hd : ∀ e ∈ digits, lo ≤ e ∧ e ≤ 9) (hL : 1 ≤ lead) (hU : lead ≤ 9)
    (hbound : 10^d ≤ (p*digits.prod)*(s+digits.sum+lead))
    (hmod : 27 ∣ p*digits.prod → (s+digits.sum+lead)%9=0)
    (hcert : scanCounts F d f lo digits.length p s = true) :
    trial F d (p*digits.prod) (s+digits.sum) lead = true := by
  induction f generalizing lo digits p s with
  | zero =>
    have hlo : lo=9 := by omega
    have hall (e : ℕ) (he : e ∈ digits) : e=9 := by have := hd e he; omega
    have heq : digits = List.replicate digits.length 9 := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hp : digits.prod = 9^digits.length := by rw [← List.prod_replicate, ← heq]
    have hs : digits.sum = 9*digits.length := by rw [mul_comm, ← List.sum_const_nat, ← heq]
    have hprune : ¬ p*9^digits.length*(s+9*digits.length+9) < 10^d := by
      apply not_lt_of_ge (hbound.trans ?_)
      rw [hp,hs]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [scanCounts, if_neg hprune, ← hp, ← hs] at hcert
    exact finishCount_sound F d _ _ _ hL hU hmod hcert
  | succ f ih =>
    obtain ⟨hprod,hsum⟩ := prod_sum_bound digits (fun e he => (hd e he).2)
    have hprune : ¬ p*9^digits.length*(s+9*digits.length+9) < 10^d := by
      apply not_lt_of_ge (hbound.trans ?_)
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hprod) (by omega)
    rw [scanCounts, if_neg hprune, List.all_eq_true] at hcert
    let j := digits.count lo
    let tail := digits.filter (fun e => !(decide (e=lo)))
    have hperm : (List.replicate j lo ++ tail).Perm digits := by
      simpa only [j,tail,List.filter_eq] using List.filter_append_perm (fun e => decide (e=lo)) digits
    have hlen : j+tail.length=digits.length := by simpa using hperm.length_eq
    have hp : lo^j*tail.prod=digits.prod := by simpa using hperm.prod_eq
    have hs : lo*j+tail.sum=digits.sum := by
      simpa [List.sum_const_nat, mul_comm] using hperm.sum_eq
    have htail (e : ℕ) (he : e ∈ tail) : lo+1 ≤ e ∧ e ≤ 9 := by
      have ⟨hm, hne⟩ := List.mem_filter.mp he
      have hne' : e≠lo := by simpa using hne
      have hh := hd e hm
      omega
    have hc := hcert j (List.mem_range.mpr (by omega))
    rw [show digits.length-j=tail.length by omega] at hc
    have hb : 10^d ≤ (p*lo^j*tail.prod)*(s+lo*j+tail.sum+lead) := by
      simpa only [mul_assoc, add_assoc, hp, hs] using hbound
    have hm : 27 ∣ p*lo^j*tail.prod → (s+lo*j+tail.sum+lead)%9 = 0 := by
      simpa only [mul_assoc, add_assoc, hp, hs] using hmod
    simpa only [mul_assoc, add_assoc, hp, hs] using
      ih (lo+1) (by omega) tail (p*lo^j) (s+lo*j) htail hb hm hc




/-- Keep the leading digit on both sides of the digit-product estimate. -/
private theorem leading_digit_bound (digits : List ℕ)
    (hn : digits ≠ []) (hd : ∀ x ∈ digits, x < 10) :
    10 ^ (digits.length - 1) * digits.prod ≤
      9 ^ (digits.length - 1) * Nat.ofDigits 10 digits := by
  induction digits with
  | nil => contradiction
  | cons e digits ih =>
    cases digits with
    | nil => simp
    | cons x xs =>
      let tail := x :: xs
      have hb := ih (by simp) (fun y hy => hd y (List.mem_cons_of_mem _ hy))
      change 10 ^ (tail.length - 1) * tail.prod ≤
        9 ^ (tail.length - 1) * Nat.ofDigits 10 tail at hb
      have he : e ≤ 9 := by
        have := hd e List.mem_cons_self
        omega
      have hlen : tail.length = tail.length - 1 + 1 := by simp [tail]
      change 10 ^ tail.length * (e * tail.prod) ≤
        9 ^ tail.length * Nat.ofDigits 10 (e :: tail)
      calc
        _ = (10 * e) * (10 ^ (tail.length - 1) * tail.prod) := by
          rw [show 10 ^ tail.length = 10 ^ (tail.length - 1) * 10 by rw [← pow_succ, ← hlen]]
          ring
        _ ≤ (10 * 9) * (9 ^ (tail.length - 1) * Nat.ofDigits 10 tail) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 10 he) hb
        _ = 9 ^ tail.length * (10 * Nat.ofDigits 10 tail) := by
          rw [show 9 ^ tail.length = 9 ^ (tail.length - 1) * 9 by rw [← pow_succ, ← hlen]]
          ring
        _ ≤ _ := by
          rw [Nat.ofDigits_cons]
          exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

private theorem lengthDecay (j : ℕ) : 9^(61+j)*(61+j) < 10^(60+j) := by
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    have h : 9*(61+j+1) ≤ 10*(61+j) := by omega
    change (9 : ℕ)^(61+j+1)*(61+j+1) < 10^(60+j+1)
    calc
      _ = 9^(61+j) * (9*(61+j+1)) := by rw [pow_succ, mul_assoc]
      _ ≤ 9^(61+j) * (10*(61+j)) := Nat.mul_le_mul_left _ h
      _ = 10*(9^(61+j)*(61+j)) := by ring
      _ < 10*(10^(60+j)) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = _ := by rw [pow_succ, mul_comm]


/-- Products grow by at most nine for every decimal place beyond the leading digit. -/
private theorem fixedLength (m : ℕ) (hm : 0 < m)
    (h : m ≤ (Nat.digits 10 m).prod * (Nat.digits 10 m).sum) :
    (Nat.digits 10 m).length ≤ 60 := by
  let digits := Nat.digits 10 m
  have hne : digits ≠ [] := by
    intro e
    have hv := Nat.ofDigits_digits 10 m
    rw [show Nat.digits 10 m = [] from e] at hv
    simp at hv
    omega
  have hd : ∀ e ∈ digits, e < 10 := fun _ he => Nat.digits_lt_base (by decide) he
  have hlead := leading_digit_bound digits hne hd
  have hv : Nat.ofDigits 10 digits = m := Nat.ofDigits_digits 10 m
  rw [hv] at hlead
  have hsum := (prod_sum_bound digits (fun e he => Nat.le_of_lt_succ (hd e he))).2
  let l := digits.length
  have hpos : 0 < l := List.length_pos_iff.mpr hne
  have hcalc : (10^(l-1))*m ≤ (9^(l-1)*(9*l))*m := by
    calc
      _ ≤ 10^(l-1) * (digits.prod * digits.sum) := Nat.mul_le_mul_left _ h
      _ = (10^(l-1)*digits.prod)*digits.sum := by ring
      _ ≤ (9^(l-1)*m)*(9*l) := Nat.mul_le_mul hlead hsum
      _ = _ := by ring
  have hpow := Nat.le_of_mul_le_mul_right hcalc hm
  by_contra! hh
  change 60 < l at hh
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 61 ≤ l by omega)
  rw [hj, show 61 + j - 1 = 60 + j by omega] at hpow
  have hd := lengthDecay j
  rw [show 61 + j = 60 + j + 1 by omega, pow_succ, mul_assoc] at hd
  rw [show 60+j+1 = 61+j by omega] at hd
  exact (not_lt_of_ge hpow) hd




private theorem fixedFromCertificate (F T : ℕ → ℕ → ℕ)
    (hF_le : ∀ p s, F p s ≤ p*s)
    (hFrom27 : ∀ p s, 27 ∣ p → 9 ∣ F p s)
    (hEval : ∀ digits : List ℕ, (∀ e ∈ digits, 1 ≤ e ∧ e ≤ 9) →
      digits.length ≤ 60 → F digits.prod digits.sum = T digits.prod digits.sum)
    (hCert : ∀ d ≤ 59, scanCounts T d 8 1 d 1 0 = true)
    (m : ℕ) (hm : 0 < m)
    (hfix : m = F (Nat.digits 10 m).prod (Nat.digits 10 m).sum) :
    m ≤ 139968 := by
  let digits := Nat.digits 10 m
  have hex : Nat.ofDigits 10 digits = m := Nat.ofDigits_digits 10 m
  have hsize : m ≤ digits.prod * digits.sum := hfix.le.trans (hF_le _ _)
  have hlen : digits.length ≤ 60 := fixedLength m hm hsize
  have hp : 0 < digits.prod := Nat.pos_of_mul_pos_right (hm.trans_le hsize)
  have hd (e : ℕ) (he : e ∈ digits) : 1 ≤ e ∧ e ≤ 9 := by
    exact ⟨(CanonicallyOrderedAdd.list_prod_pos.mp hp) e he,
      Nat.le_of_lt_succ (Nat.digits_lt_base (by decide) he)⟩
  have hcalc : T digits.prod digits.sum = m := (hEval digits hd hlen).symm.trans hfix.symm
  rcases List.eq_nil_or_concat' digits with hn | ⟨tail, lead, hsplit⟩
  · simp [hn] at hex
    omega
  have hpl : digits.prod = tail.prod * lead := by rw [hsplit]; simp
  have hsl : digits.sum = tail.sum + lead := by rw [hsplit]; simp
  have hlen' : digits.length = tail.length + 1 := by simp [hsplit]
  obtain ⟨hL, hU⟩ := hd lead (by rw [hsplit]; simp)
  let d := tail.length
  have hdmax : d ≤ 59 := by omega
  have htm : Nat.ofDigits 10 tail < 10 ^ d :=
    Nat.ofDigits_lt_base_pow_length (by decide) (fun i hi =>
      Nat.lt_succ_of_le (hd i (by rw [hsplit]; exact List.mem_append_left _ hi)).2)
  have hv : Nat.ofDigits 10 tail + 10^d * lead = m := by
    simpa only [hsplit, Nat.ofDigits_append, Nat.ofDigits_singleton, d] using hex
  have hlow : lead * 10^d ≤ m := by rw [← hv, mul_comm lead]; exact Nat.le_add_left _ _
  have hhigh : m < (lead+1)*10^d := by
    rw [← hv, Nat.succ_mul, mul_comm lead]
    omega
  have hdiv := Nat.div_eq_of_lt_le hlow hhigh
  have hcut : m < 10^(d+1) := by
    have hlo : lead+1 ≤ 10 := by omega
    rw [pow_succ']
    exact hhigh.trans_le (Nat.mul_le_mul_right _ hlo)
  have hbound : 10^d ≤ tail.prod * (tail.sum+lead) := by
    have hb : lead*10^d ≤ lead*(tail.prod*(tail.sum+lead)) := by
      calc
        _ ≤ m := hlow
        _ ≤ digits.prod * digits.sum := hsize
        _ = _ := by rw [hpl,hsl]; ring
    exact Nat.le_of_mul_le_mul_left hb hL
  have hel (e : ℕ) (he : e ∈ tail) : 1 ≤ e ∧ e ≤ 9 := by
    apply hd
    rw [hsplit]
    exact List.mem_append_left _ he
  have hb : 10^d ≤ (1*tail.prod)*(0+tail.sum+lead) := by simpa using hbound
  have hc : scanCounts T d 8 1 tail.length 1 0 = true := hCert d hdmax
  have hmod := Nat.modEq_digits_sum 9 10 (by decide) m
  change m % 9 = digits.sum % 9 at hmod
  have hmodLeaf (hp : 27 ∣ 1*tail.prod) : (0+tail.sum+lead)%9 = 0 := by
    rw [one_mul] at hp
    have hD : 27 ∣ digits.prod := hpl ▸ dvd_mul_of_dvd_left hp _
    have h := hFrom27 digits.prod digits.sum hD
    rw [← hfix] at h
    simpa only [zero_add, ← hsl, ← hmod] using Nat.mod_eq_zero_of_dvd h
  have ht := scanCounts_sound T d 8 1 (by decide) tail 1 0 lead hel hL hU hb hmodLeaf hc
  have ht' : trial T d tail.prod tail.sum lead = true := by simpa using ht
  have hdp : digitProduct (d+1) m = digits.prod := digitProduct_correct _ _ hcut
  have hds : digitSum (d+1) m = digits.sum := digitSum_correct _ _ hcut
  unfold trial at ht'
  simp only [← hpl, ← hsl, hcalc, hdiv, hmod, hdp, hds, bne_self_eq_false,
    Bool.or_false, decide_eq_true_eq] at ht'
  exact ht'




private def candidatePrimes : Finset ℕ := {2,3,5,7}

private theorem digitSmooth (ds : List ℕ) (hd : ∀ e ∈ ds, 1 ≤ e ∧ e ≤ 9) :
    ds.prod.primeFactors ⊆ candidatePrimes := by
  induction ds with
  | nil => simp
  | cons e es ih =>
    obtain ⟨he1, he9⟩ := hd e List.mem_cons_self
    have hrest (x : ℕ) (hx : x ∈ es) := hd x (List.mem_cons_of_mem _ hx)
    have hes : 0 < es.prod := CanonicallyOrderedAdd.list_prod_pos.mpr fun x hx => (hrest x hx).1
    have he' : e.primeFactors ⊆ candidatePrimes := by interval_cases e <;> decide +kernel
    rw [List.prod_cons, Nat.primeFactors_mul (by omega : e ≠ 0) hes.ne']
    exact Finset.union_subset he' (ih hrest)

private def phiSmooth (n : ℕ) : ℕ :=
  n / ((if 2 ∣ n then 2 else 1)*(if 3 ∣ n then 3 else 1)*
    (if 5 ∣ n then 5 else 1)*(if 7 ∣ n then 7 else 1)) *
  ((if 3 ∣ n then 2 else 1)*(if 5 ∣ n then 4 else 1)*(if 7 ∣ n then 6 else 1))

private theorem phiSmooth_eq {n : ℕ} (hn : 0 < n) (hs : n.primeFactors ⊆ candidatePrimes) :
    phiSmooth n = Nat.totient n := by
  have hp : n.primeFactors = candidatePrimes.filter fun p => p ∣ n := by
    ext p
    constructor
    · intro hm
      exact Finset.mem_filter.mpr ⟨hs hm, (Nat.mem_primeFactors.mp hm).2.1⟩
    · intro hm
      obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hm
      have hPr : p.Prime := by
        simp only [candidatePrimes, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> decide
      exact Nat.mem_primeFactors.mpr ⟨hPr, hd, hn.ne'⟩
  rw [Nat.totient_eq_div_primeFactors_mul, hp, Finset.prod_filter, Finset.prod_filter]
  simp [candidatePrimes, phiSmooth]

private def cand122 (p s : ℕ) : ℕ := phiSmooth p * s

private def cand121 (p s : ℕ) : ℕ :=
  let g := p.gcd s
  phiSmooth p * phiFast s * g / phiFast g

private theorem cand122_eq (digits : List ℕ) (hd : ∀ e ∈ digits, 1 ≤ e ∧ e ≤ 9) :
    Nat.totient digits.prod * digits.sum = cand122 digits.prod digits.sum := by
  have hp : 0 < digits.prod := CanonicallyOrderedAdd.list_prod_pos.mpr fun e he => (hd e he).1
  rw [cand122, phiSmooth_eq hp (digitSmooth digits hd)]

private theorem cand121_eq (digits : List ℕ) (hd : ∀ e ∈ digits, 1 ≤ e ∧ e ≤ 9)
    (hl : digits.length ≤ 60) :
    Nat.totient (digits.prod * digits.sum) = cand121 digits.prod digits.sum := by
  let p := digits.prod
  let s := digits.sum
  let g := p.gcd s
  have hp : 0 < p := CanonicallyOrderedAdd.list_prod_pos.mpr fun e he => (hd e he).1
  have hps : p.primeFactors ⊆ candidatePrimes := digitSmooth digits hd
  have hsl : s ≤ 540 := by
    have hh := (prod_sum_bound digits fun e he => (hd e he).2).2
    dsimp [s]
    omega
  change Nat.totient (p*s) = cand121 p s
  by_cases hs : s = 0
  · simp [cand121, hs, phiFast_eq 0 (by decide)]
  have hS : 0 < s := Nat.pos_of_ne_zero hs
  have hgl : g ≤ 540 := (Nat.gcd_le_right p hS).trans hsl
  have hgp : 0 < g := Nat.gcd_pos_of_pos_right p hS
  have h := Nat.totient_gcd_mul_totient_mul p s
  change Nat.totient g * Nat.totient (p*s) = Nat.totient p * Nat.totient s * g at h
  change Nat.totient (p*s) = phiSmooth p * phiFast s * g / phiFast g
  rw [phiSmooth_eq hp hps, phiFast_eq s hsl, phiFast_eq g hgl, ← h,
    Nat.mul_div_cancel_left _ (Nat.totient_pos.mpr hgp)]




set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_0 : scanCounts cand121 0 8 1 0 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_1 : scanCounts cand121 1 8 1 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_2 : scanCounts cand121 2 8 1 2 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_3 : scanCounts cand121 3 8 1 3 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_4 : scanCounts cand121 4 8 1 4 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_5 : scanCounts cand121 5 8 1 5 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_6 : scanCounts cand121 6 8 1 6 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_7 : scanCounts cand121 7 8 1 7 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_8 : scanCounts cand121 8 8 1 8 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_9 : scanCounts cand121 9 8 1 9 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_10 : scanCounts cand121 10 8 1 10 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_11 : scanCounts cand121 11 8 1 11 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_12 : scanCounts cand121 12 8 1 12 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_13 : scanCounts cand121 13 8 1 13 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_14 : scanCounts cand121 14 8 1 14 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_15 : scanCounts cand121 15 8 1 15 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_16 : scanCounts cand121 16 8 1 16 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_17 : scanCounts cand121 17 8 1 17 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_18 : scanCounts cand121 18 8 1 18 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_19 : scanCounts cand121 19 8 1 19 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_20 : scanCounts cand121 20 8 1 20 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_21 : scanCounts cand121 21 8 1 21 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_22 : scanCounts cand121 22 8 1 22 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_23 : scanCounts cand121 23 8 1 23 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_24 : scanCounts cand121 24 8 1 24 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_25 : scanCounts cand121 25 8 1 25 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_26 : scanCounts cand121 26 8 1 26 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_27 : scanCounts cand121 27 8 1 27 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_28 : scanCounts cand121 28 8 1 28 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_29 : scanCounts cand121 29 8 1 29 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_30 : scanCounts cand121 30 8 1 30 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_31 : scanCounts cand121 31 8 1 31 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_32 : scanCounts cand121 32 8 1 32 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_33 : scanCounts cand121 33 8 1 33 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_34 : scanCounts cand121 34 8 1 34 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_35 : scanCounts cand121 35 8 1 35 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_36 : scanCounts cand121 36 8 1 36 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_37 : scanCounts cand121 37 8 1 37 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_38 : scanCounts cand121 38 8 1 38 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_39 : scanCounts cand121 39 8 1 39 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_40 : scanCounts cand121 40 8 1 40 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_41 : scanCounts cand121 41 8 1 41 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_42 : scanCounts cand121 42 8 1 42 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_43 : scanCounts cand121 43 8 1 43 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_44 : scanCounts cand121 44 8 1 44 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_45 : scanCounts cand121 45 8 1 45 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_46 : scanCounts cand121 46 8 1 46 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_47 : scanCounts cand121 47 8 1 47 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_48 : scanCounts cand121 48 8 1 48 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_49 : scanCounts cand121 49 8 1 49 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_50 : scanCounts cand121 50 8 1 50 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_51 : scanCounts cand121 51 8 1 51 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_52 : scanCounts cand121 52 8 1 52 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_53 : scanCounts cand121 53 8 1 53 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_54 : scanCounts cand121 54 8 1 54 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_55 : scanCounts cand121 55 8 1 55 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_56 : scanCounts cand121 56 8 1 56 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_57 : scanCounts cand121 57 8 1 57 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_58 : scanCounts cand121 58 8 1 58 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search121_59 : scanCounts cand121 59 8 1 59 1 0 = true := by
  decide +kernel

private theorem search121 (d : ℕ) (hd : d ≤ 59) : scanCounts cand121 d 8 1 d 1 0 = true := by
  interval_cases d
  · exact search121_0
  · exact search121_1
  · exact search121_2
  · exact search121_3
  · exact search121_4
  · exact search121_5
  · exact search121_6
  · exact search121_7
  · exact search121_8
  · exact search121_9
  · exact search121_10
  · exact search121_11
  · exact search121_12
  · exact search121_13
  · exact search121_14
  · exact search121_15
  · exact search121_16
  · exact search121_17
  · exact search121_18
  · exact search121_19
  · exact search121_20
  · exact search121_21
  · exact search121_22
  · exact search121_23
  · exact search121_24
  · exact search121_25
  · exact search121_26
  · exact search121_27
  · exact search121_28
  · exact search121_29
  · exact search121_30
  · exact search121_31
  · exact search121_32
  · exact search121_33
  · exact search121_34
  · exact search121_35
  · exact search121_36
  · exact search121_37
  · exact search121_38
  · exact search121_39
  · exact search121_40
  · exact search121_41
  · exact search121_42
  · exact search121_43
  · exact search121_44
  · exact search121_45
  · exact search121_46
  · exact search121_47
  · exact search121_48
  · exact search121_49
  · exact search121_50
  · exact search121_51
  · exact search121_52
  · exact search121_53
  · exact search121_54
  · exact search121_55
  · exact search121_56
  · exact search121_57
  · exact search121_58
  · exact search121_59




private theorem largest121 :
    IsGreatest {m : ℕ | 0 < m ∧ OMA.S_oeis_a120121.IsDigitTotientFixedPoint m} 139968 := by
  constructor
  · refine ⟨by decide, ?_⟩
    change (139968 : ℕ) = Nat.totient ((Nat.digits 10 139968).prod * (Nat.digits 10 139968).sum)
    rw [← digitProduct_correct 6 _ (by decide), ← digitSum_correct 6 _ (by decide)]
    rw [show digitProduct 6 139968 = 11664 by decide, show digitSum 6 139968 = 36 by decide]
    have h := cand121_eq [8,6,9,9,3,1] (by decide) (by decide)
    change Nat.totient (11664*36) = cand121 11664 36 at h
    rw [h]
    decide +kernel
  · intro m hm
    apply fixedFromCertificate (fun p s => Nat.totient (p*s)) cand121 ?_ ?_ ?_ search121 m hm.1 hm.2
    · intro p s
      exact Nat.totient_le (p*s)
    · intro p s hp
      have hφ := Nat.totient_dvd_of_dvd (dvd_mul_of_dvd_left hp s)
      rw [show Nat.totient 27 = 18 by decide +kernel] at hφ
      exact (by decide : 9 ∣ 18).trans hφ
    · intro ds hds hlen
      exact cand121_eq ds hds hlen



end DigitTotient



theorem OMA.solution : type_of% @OMA.S_oeis_a120121.main := DigitTotient.largest121

