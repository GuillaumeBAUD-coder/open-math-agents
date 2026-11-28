import OMAStatements.S_oeis_a120123

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

/-- Search over nondecreasing non-leading digits. The variables `p` and `s`
are the product and sum of digits selected so far. -/
private def searchTail (F : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, p, s => (List.range 9).all fun j => trial F d p s (j+1)
  | k+1, lo, p, s =>
    if p * 9^(k+1) * (s + 9*(k+1) + 9) < 10^d then true
    else (List.range (10-lo)).all fun j =>
      let digit := lo+j
      searchTail F d k digit (p*digit) (s+digit)

private theorem prod_sum_bound (digits : List ℕ) (hd : ∀ e ∈ digits, e ≤ 9) :
    digits.prod ≤ 9^digits.length ∧ digits.sum ≤ 9*digits.length := by
  induction digits with
  | nil => simp
  | cons e es ih =>
    have he := hd e List.mem_cons_self
    obtain ⟨hp, hs⟩ := ih (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    simp only [List.prod_cons, List.sum_cons, List.length_cons, pow_succ']
    exact ⟨Nat.mul_le_mul he hp, by omega⟩

private theorem searchTail_sound (F : ℕ → ℕ → ℕ) (d : ℕ) (digits : List ℕ)
    (hsorted : digits.Pairwise (· ≤ ·)) (lo p s lead : ℕ)
    (hd : ∀ e ∈ digits, lo ≤ e ∧ e ≤ 9) (hlead1 : 1 ≤ lead) (hlead9 : lead ≤ 9)
    (hbound : 10^d ≤ (p*digits.prod)*(s+digits.sum+lead))
    (hcert : searchTail F d digits.length lo p s = true) :
    trial F d (p*digits.prod) (s+digits.sum) lead = true := by
  induction digits generalizing lo p s with
  | nil =>
    simp only [List.length_nil, searchTail, List.all_eq_true] at hcert
    have h := hcert (lead-1) (List.mem_range.mpr (by omega))
    simpa only [Nat.sub_add_cancel hlead1, List.prod_nil, List.sum_nil, mul_one, add_zero] using h
  | cons digit tail ih =>
    have hx := hd digit List.mem_cons_self
    obtain ⟨hfirst, hsortedTail⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨hp, hs⟩ := prod_sum_bound (digit :: tail) (fun e he => (hd e he).2)
    have hprune : ¬ p*9^((digit :: tail).length)*
        (s+9*((digit :: tail).length)+9) < 10^d := by
      apply not_lt_of_ge (hbound.trans ?_)
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (by omega)
    have hskip : ¬ p * 9^(tail.length+1) * (s+9*(tail.length+1)+9) < 10^d := by
      simpa only [List.length_cons] using hprune
    rw [List.length_cons, searchTail, if_neg hskip, List.all_eq_true] at hcert
    have hc := hcert (digit-lo) (List.mem_range.mpr (by omega))
    rw [Nat.add_sub_of_le hx.1] at hc
    have hbound' : 10^d ≤ (p*digit*tail.prod)*(s+digit+tail.sum+lead) := by
      simpa only [List.prod_cons, List.sum_cons, mul_assoc, add_assoc] using hbound
    have h := ih hsortedTail digit (p*digit) (s+digit)
      (fun e he => ⟨hfirst e he, (hd e (List.mem_cons_of_mem _ he)).2⟩) hbound' hc
    simpa only [List.prod_cons, List.sum_cons, mul_assoc, add_assoc] using h




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
    (hEval : ∀ digits : List ℕ, (∀ e ∈ digits, 1 ≤ e ∧ e ≤ 9) →
      digits.length ≤ 60 → F digits.prod digits.sum = T digits.prod digits.sum)
    (hCert : ∀ d ≤ 59, searchTail T d d 1 1 0 = true)
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
  let sorted := tail.mergeSort (· ≤ ·)
  have hperm : sorted.Perm tail := List.mergeSort_perm _ _
  have hslen : sorted.length = d := hperm.length_eq
  have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_mergeSort' _ _
  have hel (e : ℕ) (he : e ∈ sorted) : 1 ≤ e ∧ e ≤ 9 := by
    apply hd
    rw [hsplit]
    exact List.mem_append_left _ (hperm.mem_iff.mp he)
  have hb : 10^d ≤ (1*sorted.prod)*(0+sorted.sum+lead) := by
    simpa [hperm.prod_eq, hperm.sum_eq] using hbound
  have hc : searchTail T d sorted.length 1 1 0 = true := by
    rw [hslen]
    exact hCert d hdmax
  have ht := searchTail_sound T d sorted hsorted 1 1 0 lead hel hL hU hb hc
  have ht' : trial T d tail.prod tail.sum lead = true := by
    simpa [hperm.prod_eq, hperm.sum_eq] using ht
  have hmod := Nat.modEq_digits_sum 9 10 (by decide) m
  change m % 9 = digits.sum % 9 at hmod
  have hdp : digitProduct (d+1) m = digits.prod := digitProduct_correct _ _ hcut
  have hds : digitSum (d+1) m = digits.sum := digitSum_correct _ _ hcut
  unfold trial at ht'
  simp only [← hpl, ← hsl, hcalc, hdiv, hmod, hdp, hds, bne_self_eq_false,
    Bool.or_false, decide_eq_true_eq] at ht'
  exact ht'




private def cand123 (p s : ℕ) : ℕ := p * phiFast s

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_0 : searchTail cand123 0 0 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_1 : searchTail cand123 1 1 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_2 : searchTail cand123 2 2 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_3 : searchTail cand123 3 3 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_4 : searchTail cand123 4 4 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_5 : searchTail cand123 5 5 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_6 : searchTail cand123 6 6 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_7 : searchTail cand123 7 7 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_8 : searchTail cand123 8 8 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_9 : searchTail cand123 9 9 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_10 : searchTail cand123 10 10 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_11 : searchTail cand123 11 11 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_12 : searchTail cand123 12 12 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_13 : searchTail cand123 13 13 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_14 : searchTail cand123 14 14 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_15 : searchTail cand123 15 15 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_16 : searchTail cand123 16 16 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_17 : searchTail cand123 17 17 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_18 : searchTail cand123 18 18 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_19 : searchTail cand123 19 19 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_20 : searchTail cand123 20 20 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_21 : searchTail cand123 21 21 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_22 : searchTail cand123 22 22 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_23 : searchTail cand123 23 23 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_24 : searchTail cand123 24 24 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_25 : searchTail cand123 25 25 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_26 : searchTail cand123 26 26 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_27 : searchTail cand123 27 27 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_28 : searchTail cand123 28 28 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_29 : searchTail cand123 29 29 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_30 : searchTail cand123 30 30 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_31 : searchTail cand123 31 31 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_32 : searchTail cand123 32 32 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_33 : searchTail cand123 33 33 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_34 : searchTail cand123 34 34 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_35 : searchTail cand123 35 35 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_36 : searchTail cand123 36 36 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_37 : searchTail cand123 37 37 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_38 : searchTail cand123 38 38 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_39 : searchTail cand123 39 39 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_40 : searchTail cand123 40 40 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_41 : searchTail cand123 41 41 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_42 : searchTail cand123 42 42 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_43 : searchTail cand123 43 43 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_44 : searchTail cand123 44 44 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_45 : searchTail cand123 45 45 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_46 : searchTail cand123 46 46 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_47 : searchTail cand123 47 47 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_48 : searchTail cand123 48 48 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_49 : searchTail cand123 49 49 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_50 : searchTail cand123 50 50 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_51 : searchTail cand123 51 51 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_52 : searchTail cand123 52 52 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_53 : searchTail cand123 53 53 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_54 : searchTail cand123 54 54 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_55 : searchTail cand123 55 55 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_56 : searchTail cand123 56 56 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_57 : searchTail cand123 57 57 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_58 : searchTail cand123 58 58 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search123_59 : searchTail cand123 59 59 1 1 0 = true := by
  decide +kernel

private theorem search123 (d : ℕ) (hd : d ≤ 59) : searchTail cand123 d d 1 1 0 = true := by
  interval_cases d
  · exact search123_0
  · exact search123_1
  · exact search123_2
  · exact search123_3
  · exact search123_4
  · exact search123_5
  · exact search123_6
  · exact search123_7
  · exact search123_8
  · exact search123_9
  · exact search123_10
  · exact search123_11
  · exact search123_12
  · exact search123_13
  · exact search123_14
  · exact search123_15
  · exact search123_16
  · exact search123_17
  · exact search123_18
  · exact search123_19
  · exact search123_20
  · exact search123_21
  · exact search123_22
  · exact search123_23
  · exact search123_24
  · exact search123_25
  · exact search123_26
  · exact search123_27
  · exact search123_28
  · exact search123_29
  · exact search123_30
  · exact search123_31
  · exact search123_32
  · exact search123_33
  · exact search123_34
  · exact search123_35
  · exact search123_36
  · exact search123_37
  · exact search123_38
  · exact search123_39
  · exact search123_40
  · exact search123_41
  · exact search123_42
  · exact search123_43
  · exact search123_44
  · exact search123_45
  · exact search123_46
  · exact search123_47
  · exact search123_48
  · exact search123_49
  · exact search123_50
  · exact search123_51
  · exact search123_52
  · exact search123_53
  · exact search123_54
  · exact search123_55
  · exact search123_56
  · exact search123_57
  · exact search123_58
  · exact search123_59




private theorem largest123 :
    IsGreatest {m : ℕ | 0 < m ∧ OMA.S_oeis_a120123.IsDigitProductTotientSumFixedPoint m}
      139968 := by
  constructor
  · refine ⟨by decide, ?_⟩
    change (139968 : ℕ) = (Nat.digits 10 139968).prod * Nat.totient (Nat.digits 10 139968).sum
    rw [← digitProduct_correct 6 _ (by decide), ← digitSum_correct 6 _ (by decide)]
    rw [show digitProduct 6 139968 = 11664 by decide, show digitSum 6 139968 = 36 by decide]
    rw [← phiFast_eq 36 (by decide)]
    decide +kernel
  · intro m hm
    apply fixedFromCertificate (fun p s => p * Nat.totient s) cand123 ?_ ?_ search123 m hm.1 hm.2
    · intro p s
      exact Nat.mul_le_mul_left p (Nat.totient_le s)
    · intro ds hds hlen
      change _ = ds.prod * phiFast ds.sum
      rw [phiFast_eq]
      have hs := (prod_sum_bound ds (fun d hd => (hds d hd).2)).2
      omega



end DigitTotient



theorem OMA.solution : type_of% @OMA.S_oeis_a120123.main := DigitTotient.largest123

