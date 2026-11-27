import OMAReductions.R_Erdos985_erdos_985_R2
import Mathlib.Data.Nat.Factors

/-! Finite modular-order certificates for the small-prime range. -/

namespace OMA.PrimePrimitiveRootsSmall

private def modPower (p q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, e =>
    let r := modPower p q fuel (e / 2)
    let sq := (r * r) % p
    if e % 2 = 0 then sq else (sq * q) % p

private theorem modPower_cast (p q fuel e : ℕ) (he : e < 2 ^ fuel) :
    (modPower p q fuel e : ZMod p) = (q : ZMod p) ^ e := by
  induction fuel generalizing e with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at he
    simp [he, modPower]
  | succ fuel ih =>
    have he' : e / 2 < 2 ^ fuel := by rw [pow_succ] at he; omega
    simp only [modPower]
    split
    · rw [ZMod.natCast_mod, Nat.cast_mul, ih _ he', ← pow_add]
      congr 1
      omega
    · rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ih _ he',
        ← pow_add, ← pow_succ]
      congr 1
      omega

private theorem modPower_lt (p q e : ℕ) (fuel : ℕ) (hp : 1 < p) :
    modPower p q fuel e < p := by
  cases fuel with
  | zero => exact hp
  | succ fuel =>
    simp only [modPower]
    split <;> exact Nat.mod_lt _ (by omega)

private def candidates : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private def properDivisor (n d : ℕ) : Bool := decide (d < n ∧ d ∣ n)

private def trialPrime (n : ℕ) : Bool := decide (1 < n) && !candidates.any (properDivisor n)

private theorem small_primes :
    (List.range 54).all (fun d => decide (d.Prime → d ∈ candidates)) = true := by
  decide +kernel

private theorem trialPrime_spec {n : ℕ} (hn : n ≤ 2791) : trialPrime n = true ↔ n.Prime := by
  constructor
  · intro h
    have ht := h
    simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq] at ht
    have h₁ := ht.1
    by_contra hnp
    have hs := Nat.minFac_sq_le_self (by omega) hnp
    have hd₅₃ : n.minFac < 54 := by
      by_contra! hlo
      have h54 : 54 ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left hlo 2
      omega
    have hdprime := Nat.minFac_prime (show n ≠ 1 by omega)
    have hm := of_decide_eq_true (List.all_eq_true.1 small_primes n.minFac (List.mem_range.2 hd₅₃))
    have hdiv : properDivisor n n.minFac = true :=
      decide_eq_true ⟨(Nat.not_prime_iff_minFac_lt (by omega)).1 hnp, Nat.minFac_dvd n⟩
    have hsome := List.any_eq_true.2 ⟨n.minFac, hm hdprime, hdiv⟩
    simp only [trialPrime, hsome, Bool.not_true, Bool.and_false, Bool.false_eq_true] at h
  · intro hp
    have hnone : candidates.any (properDivisor n) = false := by
      by_contra! ht
      obtain ⟨d, hd, hgood⟩ := List.any_eq_true.1 (Bool.eq_true_of_not_eq_false ht)
      obtain ⟨hdn, hdvd⟩ := of_decide_eq_true hgood
      have hd₂ : 1 < d := by
        simpa using of_decide_eq_true
          (List.all_eq_true.1 (show candidates.all (fun a => decide (1 < a)) = true by decide +kernel) d hd)
      rcases hp.eq_one_or_self_of_dvd d hdvd with hh | hh <;> omega
    simp only [trialPrime, hp.one_lt, decide_true, hnone, Bool.not_false, Bool.and_self]

private def trialFactors : ℕ → ℕ → List ℕ
  | 0, m => [m]
  | fuel + 1, m =>
    match candidates.find? (properDivisor m) with
    | none => [m]
    | some d => d :: trialFactors fuel (m / d)

private def certificate (p q : ℕ) : Bool :=
  let fs := trialFactors 12 (p - 1)
  trialPrime q && decide (q < p) &&
  decide (modPower p q 12 (p - 1) = 1) &&
  decide (fs.prod = p - 1) &&
  fs.all (fun d => decide (d ≤ 2791) && trialPrime d &&
    decide (modPower p q 12 ((p - 1) / d) ≠ 1))

private def checked (p : ℕ) : Bool :=
  !(trialPrime p && decide (p ≠ 2)) || candidates.any (certificate p)

private theorem of_checked (p : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hpmax : p ≤ 2791)
    (hpchecked : checked p = true) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hp' := (trialPrime_spec hpmax).2 hp
  have hp₂' := decide_eq_true hp₂
  simp only [checked, hp', hp₂', Bool.and_self, Bool.not_true, Bool.false_or] at hpchecked
  obtain ⟨q, _, hq⟩ := List.any_eq_true.1 hpchecked
  simp only [certificate, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨⟨hqprime, hqlt⟩, hqpow⟩, hprod⟩, hdiv⟩ := hq
  let fs := trialFactors 12 (p - 1)
  have hfs (d : ℕ) (hd : d ∈ fs) :
      d.Prime ∧ modPower p q 12 ((p - 1) / d) ≠ 1 := by
    have h := List.all_eq_true.1 hdiv d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨(trialPrime_spec h.1.1).1 h.1.2, h.2⟩
  have hperm : List.Perm fs (p - 1).primeFactorsList :=
    Nat.primeFactorsList_unique hprod (fun d hd => (hfs d hd).1)
  have hval (e : ℕ) (he : e < 2 ^ 12) :
      ((q : ZMod p) ^ e).val = modPower p q 12 e := by
    rw [← modPower_cast p q 12 e he, ZMod.val_natCast_of_lt (modPower_lt p q e 12 hp.one_lt)]
  have hp₁ := hp.one_lt
  refine ⟨q, (trialPrime_spec (by omega)).1 hqprime, hqlt,
    orderOf_eq_of_pow_and_pow_div_prime (by omega) ?_ ?_⟩
  · rw [← modPower_cast p q 12 (p - 1) (by omega), hqpow, Nat.cast_one]
  · intro d hd hdp he
    have hmem : d ∈ (p - 1).primeFactorsList :=
      (Nat.mem_primeFactorsList_iff_dvd (by omega) hd).2 hdp
    have hexp : (p - 1) / d < 2 ^ 12 := (Nat.div_le_self _ _).trans_lt (by omega)
    apply (hfs d (hperm.mem_iff.2 hmem)).2
    simpa only [hval _ hexp, ZMod.val_one'' hp.ne_one] using congrArg ZMod.val he

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_0 : (List.range' 0 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_250 : (List.range' 250 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_500 : (List.range' 500 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_750 : (List.range' 750 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_1000 : (List.range' 1000 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_1250 : (List.range' 1250 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_1500 : (List.range' 1500 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_1750 : (List.range' 1750 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_2000 : (List.range' 2000 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_2250 : (List.range' 2250 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_2500 : (List.range' 2500 250).all checked = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked_2750 : (List.range' 2750 42).all checked = true := by
  decide +kernel

theorem small (p : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hpmax : p ≤ 2791) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  apply of_checked p hp hp₂ hpmax
  have hchunk : p / 250 < 12 := by omega
  interval_cases h : p / 250
  · exact List.all_eq_true.1 checked_0 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_250 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_500 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_750 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_1000 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_1250 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_1500 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_1750 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_2000 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_2250 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_2500 p (List.mem_range'_1.2 (by omega))
  · exact List.all_eq_true.1 checked_2750 p (List.mem_range'_1.2 (by omega))

end OMA.PrimePrimitiveRootsSmall


theorem OMA.solution : OMA.R_Erdos985_erdos_985_R2.H1 :=
  OMA.PrimePrimitiveRootsSmall.small
