import OMAStatements.S_oeis_a120122

/-!
# Decimal digit-product and digit-sum fixed points

The decimal length bound uses the leading digit and the fact that all other
digits are at most nine. The certified search examines sorted tails, pruning
whenever their largest possible completion cannot reach the required
magnitude. The totient lookup is checked against Mathlib, and the final
trials evaluate both digit statistics by transparent recursion.
-/


namespace DigitTotient


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

/-- Check consecutive multiplicities, stopping once the upper bound fails.
Increasing the count replaces a possible nine by a smaller digit. -/
private def countChoices (next : ℕ → ℕ → ℕ → Bool) (T lo : ℕ) :
    ℕ → ℕ → ℕ → Bool
  | 0, p, s => if T ≤ p*(s+9) then next 0 p s else true
  | k+1, p, s =>
    if T ≤ p*9^(k+1)*(s+9*(k+1)+9) then
      next (k+1) p s && countChoices next T lo k (p*lo) (s+lo)
    else true

private theorem countChoices_cover (next : ℕ → ℕ → ℕ → Bool)
    (T lo k p s j : ℕ) (hlo : lo ≤ 9) (hj : j ≤ k)
    (h : T ≤ (p*lo^j)*9^(k-j)*(s+lo*j+9*(k-j)+9))
    (hc : countChoices next T lo k p s = true) :
    next (k-j) (p*lo^j) (s+lo*j) = true := by
  induction k generalizing p s j with
  | zero =>
    have hj0 : j=0 := by omega
    simp only [hj0, Nat.sub_zero, pow_zero, mul_one, mul_zero, add_zero] at h ⊢
    rw [countChoices, if_pos h] at hc
    exact hc
  | succ k ih =>
    have hpow : lo^j*9^(k+1-j) ≤ 9^(k+1) := by
      calc
        _ ≤ 9^j*9^(k+1-j) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlo _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj]
    have hsum : s+lo*j+9*(k+1-j)+9 ≤ s+9*(k+1)+9 := by
      calc
        _ ≤ s+9*j+9*(k+1-j)+9 := by
          have hmul := Nat.mul_le_mul_right j hlo
          omega
        _ = _ := by rw [add_assoc s, ← Nat.mul_add, Nat.add_sub_of_le hj]
    have hcur : T ≤ p*9^(k+1)*(s+9*(k+1)+9) := by
      rw [mul_assoc p] at h
      exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hpow) hsum)
    rw [countChoices, if_pos hcur, Bool.and_eq_true] at hc
    cases j with
    | zero => simpa using hc.1
    | succ j =>
      have hj' : j ≤ k := by omega
      have hk : k+1-(j+1)=k-j := by omega
      have hp : p*lo^(j+1)=(p*lo)*lo^j := by rw [pow_succ', ← mul_assoc]
      have hs : s+lo*(j+1)=(s+lo)+lo*j := by rw [Nat.mul_succ lo j, ← add_assoc, add_right_comm s]
      rw [hk,hp,hs] at h ⊢
      exact ih (p*lo) (s+lo) j hj' h hc.2

private def scanCounts (F : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, k, p, s => finishCount F d (p*9^k) (s+9*k)
  | f+1, lo, k, p, s =>
    countChoices (scanCounts F d f (lo+1)) (10^d) lo k p s

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
    rw [scanCounts, ← hp, ← hs] at hcert
    exact finishCount_sound F d _ _ _ hL hU hmod hcert
  | succ f ih =>
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
    have hb : 10^d ≤ (p*lo^j*tail.prod)*(s+lo*j+tail.sum+lead) := by
      simpa only [mul_assoc, add_assoc, hp, hs] using hbound
    obtain ⟨hprod,hsum⟩ := prod_sum_bound tail (fun e he => (htail e he).2)
    have hcount : 10^d ≤ (p*lo^j)*9^tail.length*(s+lo*j+9*tail.length+9) :=
      hb.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hprod) (by omega))
    have hj : j ≤ digits.length := by omega
    have hlo : lo ≤ 9 := by omega
    rw [scanCounts] at hcert
    have hc := countChoices_cover _ _ _ _ _ _ _ hlo hj
      (by rwa [show digits.length-j=tail.length by omega]) hcert
    rw [show digits.length-j=tail.length by omega] at hc
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

private theorem cand122_eq (digits : List ℕ) (hd : ∀ e ∈ digits, 1 ≤ e ∧ e ≤ 9) :
    Nat.totient digits.prod * digits.sum = cand122 digits.prod digits.sum := by
  have hp : 0 < digits.prod := CanonicallyOrderedAdd.list_prod_pos.mpr fun e he => (hd e he).1
  rw [cand122, phiSmooth_eq hp (digitSmooth digits hd)]




set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_0 : scanCounts cand122 0 8 1 0 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_1 : scanCounts cand122 1 8 1 1 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_2 : scanCounts cand122 2 8 1 2 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_3 : scanCounts cand122 3 8 1 3 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_4 : scanCounts cand122 4 8 1 4 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_5 : scanCounts cand122 5 8 1 5 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_6 : scanCounts cand122 6 8 1 6 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_7 : scanCounts cand122 7 8 1 7 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_8 : scanCounts cand122 8 8 1 8 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_9 : scanCounts cand122 9 8 1 9 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_10 : scanCounts cand122 10 8 1 10 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_11 : scanCounts cand122 11 8 1 11 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_12 : scanCounts cand122 12 8 1 12 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_13 : scanCounts cand122 13 8 1 13 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_14 : scanCounts cand122 14 8 1 14 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_15 : scanCounts cand122 15 8 1 15 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_16 : scanCounts cand122 16 8 1 16 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_17 : scanCounts cand122 17 8 1 17 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_18 : scanCounts cand122 18 8 1 18 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_19 : scanCounts cand122 19 8 1 19 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_20 : scanCounts cand122 20 8 1 20 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_21 : scanCounts cand122 21 8 1 21 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_22 : scanCounts cand122 22 8 1 22 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_23 : scanCounts cand122 23 8 1 23 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_24 : scanCounts cand122 24 8 1 24 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_25 : scanCounts cand122 25 8 1 25 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_26 : scanCounts cand122 26 8 1 26 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_27 : scanCounts cand122 27 8 1 27 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_28 : scanCounts cand122 28 8 1 28 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_29 : scanCounts cand122 29 8 1 29 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_30 : scanCounts cand122 30 8 1 30 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_31 : scanCounts cand122 31 8 1 31 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_32 : scanCounts cand122 32 8 1 32 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_33 : scanCounts cand122 33 8 1 33 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_34 : scanCounts cand122 34 8 1 34 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_35 : scanCounts cand122 35 8 1 35 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_36 : scanCounts cand122 36 8 1 36 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_37 : scanCounts cand122 37 8 1 37 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_38 : scanCounts cand122 38 8 1 38 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_39 : scanCounts cand122 39 8 1 39 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_40 : scanCounts cand122 40 8 1 40 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_41 : scanCounts cand122 41 8 1 41 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_42 : scanCounts cand122 42 8 1 42 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_43 : scanCounts cand122 43 8 1 43 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_44 : scanCounts cand122 44 8 1 44 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_45 : scanCounts cand122 45 8 1 45 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_46 : scanCounts cand122 46 8 1 46 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_47 : scanCounts cand122 47 8 1 47 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_48 : scanCounts cand122 48 8 1 48 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_49 : scanCounts cand122 49 8 1 49 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_50 : scanCounts cand122 50 8 1 50 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_51 : scanCounts cand122 51 8 1 51 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_52 : scanCounts cand122 52 8 1 52 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_53 : scanCounts cand122 53 8 1 53 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_54 : scanCounts cand122 54 8 1 54 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_55 : scanCounts cand122 55 8 1 55 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_56 : scanCounts cand122 56 8 1 56 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_57 : scanCounts cand122 57 8 1 57 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_58 : scanCounts cand122 58 8 1 58 1 0 = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem search122_59 : scanCounts cand122 59 8 1 59 1 0 = true := by
  decide +kernel

private theorem search122 (d : ℕ) (hd : d ≤ 59) : scanCounts cand122 d 8 1 d 1 0 = true := by
  interval_cases d
  · exact search122_0
  · exact search122_1
  · exact search122_2
  · exact search122_3
  · exact search122_4
  · exact search122_5
  · exact search122_6
  · exact search122_7
  · exact search122_8
  · exact search122_9
  · exact search122_10
  · exact search122_11
  · exact search122_12
  · exact search122_13
  · exact search122_14
  · exact search122_15
  · exact search122_16
  · exact search122_17
  · exact search122_18
  · exact search122_19
  · exact search122_20
  · exact search122_21
  · exact search122_22
  · exact search122_23
  · exact search122_24
  · exact search122_25
  · exact search122_26
  · exact search122_27
  · exact search122_28
  · exact search122_29
  · exact search122_30
  · exact search122_31
  · exact search122_32
  · exact search122_33
  · exact search122_34
  · exact search122_35
  · exact search122_36
  · exact search122_37
  · exact search122_38
  · exact search122_39
  · exact search122_40
  · exact search122_41
  · exact search122_42
  · exact search122_43
  · exact search122_44
  · exact search122_45
  · exact search122_46
  · exact search122_47
  · exact search122_48
  · exact search122_49
  · exact search122_50
  · exact search122_51
  · exact search122_52
  · exact search122_53
  · exact search122_54
  · exact search122_55
  · exact search122_56
  · exact search122_57
  · exact search122_58
  · exact search122_59




private theorem largest122 :
    IsGreatest {m : ℕ | 0 < m ∧ OMA.S_oeis_a120122.IsDigitTotientProductFixedPoint m} 139968 := by
  constructor
  · refine ⟨by decide, ?_⟩
    change (139968 : ℕ) = Nat.totient (Nat.digits 10 139968).prod * (Nat.digits 10 139968).sum
    rw [← digitProduct_correct 6 _ (by decide), ← digitSum_correct 6 _ (by decide)]
    rw [show digitProduct 6 139968 = 11664 by decide, show digitSum 6 139968 = 36 by decide]
    have h := cand122_eq [8,6,9,9,3,1] (by decide)
    rw [show ([8,6,9,9,3,1] : List ℕ).prod = 11664 by decide,
      show ([8,6,9,9,3,1] : List ℕ).sum = 36 by decide] at h
    rw [h]
    decide +kernel
  · intro m hm
    apply fixedFromCertificate (fun p s => Nat.totient p*s) cand122 ?_ ?_ ?_ search122 m hm.1 hm.2
    · intro p s
      exact Nat.mul_le_mul_right s (Nat.totient_le p)
    · intro p s hp
      have hφ := Nat.totient_dvd_of_dvd hp
      rw [show Nat.totient 27 = 18 by decide +kernel] at hφ
      exact dvd_mul_of_dvd_left ((by decide : 9 ∣ 18).trans hφ) _
    · intro ds hds hlen
      exact cand122_eq ds hds



end DigitTotient



theorem OMA.solution : type_of% @OMA.S_oeis_a120122.main := DigitTotient.largest122

