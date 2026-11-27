import OMAReductions.R_Erdos985_erdos_985_R2

-- The order test follows @MrSeizy's proof in the merged Erdős 985 R1.H2.R1 reduction.
namespace OMA.Erdos985Small

private def candidates : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53]

private def certifies (p q : ℕ) : Bool :=
  decide (q.Prime ∧ q < p) &&
    (p - 1).primeFactorsList.all (fun r ↦ decide (q ^ ((p - 1) / r) % p ≠ 1))

-- Within the verified range, a composite has a divisor between 2 and 53.
private def canSkip (p : ℕ) : Bool :=
  decide (p < 3) || (List.range' 2 52).any (fun r ↦ decide (r < p ∧ r ∣ p))

private def covered (p : ℕ) : Bool :=
  canSkip p || candidates.any (certifies p)

private theorem cannotSkip {p : ℕ} (hp : p.Prime) (h₂ : p ≠ 2) : canSkip p = false := by
  cases h : canSkip p with
  | false => rfl
  | true =>
    exfalso
    rcases Bool.or_eq_true_iff.mp h with hlt | hdvd
    · have := hp.two_le
      have : p < 3 := of_decide_eq_true hlt
      omega
    · obtain ⟨r, hr, hdiv⟩ := List.any_eq_true.mp hdvd
      obtain ⟨hrp, hrdiv⟩ : r < p ∧ r ∣ p := of_decide_eq_true hdiv
      exact (Nat.prime_def_lt'.mp hp).2 r (List.mem_range'_1.mp hr).1 hrp hrdiv

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem checkedTable : (List.range 2792).all covered = true := by
  decide +kernel

private theorem certified_order {p q : ℕ} (hp : p.Prime) (h : certifies p q = true) :
    q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hcert := Bool.and_eq_true_iff.mp h
  obtain ⟨hq, hqp⟩ : q.Prime ∧ q < p := of_decide_eq_true hcert.1
  letI : Fact p.Prime := ⟨hp⟩
  have hnz : (q : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp hz)).not_gt hqp
  have hp₁ := hp.one_lt
  refine ⟨hq, hqp, orderOf_eq_of_pow_and_pow_div_prime (by omega)
    (ZMod.pow_card_sub_one_eq_one hnz) ?_⟩
  intro r hr hd hpow
  have hmem := (Nat.mem_primeFactorsList_iff_dvd (by omega) hr).2 hd
  have hres : q ^ ((p - 1) / r) % p ≠ 1 :=
    of_decide_eq_true (List.all_eq_true.mp hcert.2 r hmem)
  apply hres
  have hval := congrArg ZMod.val hpow
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one'' hp.ne_one] at hval
  exact hval

end OMA.Erdos985Small

open OMA.Erdos985Small in
theorem OMA.solution : OMA.R_Erdos985_erdos_985_R2.H1 := by
  intro p hp h₂ hbound
  have hmem : p ∈ List.range 2792 := List.mem_range.mpr (by omega)
  have hc := List.all_eq_true.mp checkedTable p hmem
  have hq : candidates.any (certifies p) = true := by
    simpa [covered, cannotSkip hp h₂] using hc
  obtain ⟨q, _, hcert⟩ := List.any_eq_true.mp hq
  exact ⟨q, certified_order hp hcert⟩
