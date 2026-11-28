import FormalConjectures.ErdosProblems.«396»
import Mathlib

/-! A square sieve for radical-compatible central binomial windows. Small
prime powers can be handled by a progression; above its prime cutoff it is
enough to hit each prime once, provided enough endpoints pass that weaker test.
Repeated large factors remove at most (k+1)(T/B + sqrt(M*T)+1) indices. -/
namespace OMA.R_Erdos396_erdos_396_R2

open Finset

/-- Small prime powers can be made harmless throughout a smooth progression. -/
def H1 : Prop := ∀ k B : ℕ, 2 ≤ B → k < B → ∃ M : ℕ, k + 1 < M ∧
    (∀ p : ℕ, p.Prime → p ∣ M → p ≤ B) ∧
    ∀ t p : ℕ, p.Prime → p ≤ B →
      let n := M * (t + 1) - 1
      (n.descFactorial (k+1)).factorization p ≤ n.centralBinom.factorization p

/-- Find sufficiently many endpoints where each large prime occurs at
least once in the coefficient; multiplicities need not be checked. -/
def H2 : Prop := ∀ k : ℕ, ∃ B : ℕ, 2 ≤ B ∧ k < B ∧ ∀ M : ℕ, k + 1 < M →
    (∀ p : ℕ, p.Prime → p ∣ M → p ≤ B) →
    ∃ T : ℕ, ∃ G : Finset ℕ, G ⊆ range T ∧
      (k+1) * (T / B + Nat.sqrt (M*T) + 1) < G.card ∧
      ∀ t ∈ G, ∀ p : ℕ, p.Prime → B < p →
        let n := M * (t+1) - 1
        p ∣ n.descFactorial (k+1) → p ∣ n.centralBinom

/-- One congruence can hit at most once in each full block of length q. -/
theorem congruence_count (M T q i : ℕ) (hq : q.Coprime M) :
    ((range T).filter (fun t => M*(t+1) ≡ i [MOD q])).card ≤ T/q + 1 := by
  classical
  rw [← card_range (T/q + 1)]
  apply card_le_card_of_injOn (fun t => t/q)
  · intro t ht
    have ht' := mem_range.mp (mem_filter.mp ht).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  · intro t ht u hu heq
    have he := ((mem_filter.mp ht).2.trans (mem_filter.mp hu).2.symm).cancel_left_of_coprime hq
    have hmod : t % q = u % q := Nat.ModEq.add_right_cancel' 1 he
    have ht' := Nat.mod_add_div t q
    have hu' := Nat.mod_add_div u q
    change t/q = u/q at heq
    rw [heq, hmod] at ht'
    omega

theorem telescoping_count (T B L : ℕ) (hB : 0 < B) :
    (∑ j ∈ range L, (T / (B+j+1)^2 + 1)) + T/(B+L) ≤ T/B + L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ]
    let d := B+L+1
    have hd : 0 < d := by dsimp [d]; omega
    have hc : T/d^2*d ≤ T/d := (Nat.le_div_iff_mul_le hd).2 (by
      rw [Nat.mul_assoc, ← sq]; exact Nat.div_mul_le_self _ _)
    have hp : 0 < B+L := by omega
    have ht : T/d^2 + T/d ≤ T/(B+L) := (Nat.le_div_iff_mul_le hp).2 (by
      have hdiv := Nat.div_mul_le_self T d
      change T / d * d ≤ T at hdiv
      calc
        _ = T/d^2*(B+L) + T/d*(B+L) := Nat.add_mul _ _ _
        _ ≤ T/d + T/d*(B+L) := Nat.add_le_add_right
          ((Nat.mul_le_mul_left _ (by dsimp [d]; omega : B+L ≤ d)).trans hc) _
        _ = T/d*d := by change _ = T/d*(B+L+1); ring
        _ ≤ T := hdiv)
    change (∑ j ∈ range L, (T / (B+j+1)^2 + 1)) + (T/d^2 + 1) + T/d ≤ T/B + (L+1)
    omega

/-- Finite union bound over the large prime square divisors of the window. -/
theorem square_sieve {M T B k : ℕ} (hk : k < B) (hM : k + 1 < M)
    (hsm : ∀ p : ℕ, p.Prime → p ∣ M → p ≤ B) :
    ∃ bad : Finset ℕ, bad.card ≤ (k+1)*(T/B + Nat.sqrt (M*T) + 1) ∧
      ∀ t < T, ∀ i ≤ k, ∀ p : ℕ, p.Prime → B < p →
        p^2 ∣ M*(t+1)-1-i → t ∈ bad := by
  classical
  let L := Nat.sqrt (M*T) + 1
  let hit (i j : ℕ) : Finset ℕ :=
    if (B+j+1).Prime then
      (range T).filter (fun t => M*(t+1) ≡ i+1 [MOD (B+j+1)^2])
    else ∅
  let bad := (range (k+1)).biUnion (fun i => (range L).biUnion (hit i))
  refine ⟨bad, ?_, ?_⟩
  · have bound (i j : ℕ) : (hit i j).card ≤ T/(B+j+1)^2 + 1 := by
      dsimp [hit]; split
      · rename_i hp
        apply congruence_count
        apply Nat.Coprime.pow_left
        apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
        intro hd
        have := hsm _ hp hd
        omega
      · simp
    have bnd (i : ℕ) : ((range L).biUnion (hit i)).card ≤ T/B + L := by
      apply card_biUnion_le.trans
      apply (sum_le_sum (fun j _ => bound i j)).trans
      exact (Nat.le_add_right _ _).trans (telescoping_count T B L (by omega))
    apply card_biUnion_le.trans
    exact (sum_le_sum (fun i _ => bnd i)).trans (by simp [L, Nat.add_assoc])
  · intro t ht i hi p hp hpB hsq
    have hm : M ≤ M*(t+1) := Nat.le_mul_of_pos_right M (by omega)
    have htM : M*(t+1) ≤ M*T := Nat.mul_le_mul_left M ht
    have hterm : 0 < M*(t+1)-1-i := by omega
    have hcut : p ≤ Nat.sqrt (M*T) := Nat.le_sqrt'.mpr ((Nat.le_of_dvd hterm hsq).trans (by omega))
    let j := p-(B+1)
    have hj : B+j+1 = p := by dsimp [j]; omega
    have hjL : j < L := by dsimp [j,L]; omega
    apply mem_biUnion.mpr ⟨i, mem_range.mpr (by omega), ?_⟩
    apply mem_biUnion.mpr ⟨j, mem_range.mpr hjL, ?_⟩
    dsimp [hit]; rw [hj, if_pos hp]
    apply mem_filter.mpr ⟨mem_range.mpr ht, ?_⟩
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (by omega)).mpr
    convert hsq using 1; omega

private lemma prime_sq_not_dvd_descFactorial {n k p : ℕ}
    (hp : p.Prime) (hkn : k < n) (hkp : k < p)
    (hsq : ∀ i ≤ k, ¬ p ^ 2 ∣ n - i) :
    ¬ p ^ 2 ∣ n.descFactorial (k + 1) := by
  have factor : ∀ m : ℕ, p ∣ n.descFactorial m → ∃ i < m, p ∣ n - i := by
    intro m
    induction m with
    | zero =>
      intro hd
      exact (hp.not_dvd_one (by simpa [Nat.descFactorial] using hd)).elim
    | succ m ih =>
      intro hd
      rw [Nat.descFactorial_succ] at hd
      rcases hp.dvd_mul.mp hd with hlast | hprev
      · exact ⟨m, Nat.lt_succ_self m, hlast⟩
      · obtain ⟨i, hi, hdvd⟩ := ih hprev
        exact ⟨i, by omega, hdvd⟩
  induction k with
  | zero =>
    simpa [Nat.descFactorial] using hsq 0 (by omega)
  | succ k ih =>
    intro hd
    rw [Nat.descFactorial_succ] at hd
    by_cases hlast : p ∣ n - (k + 1)
    · have hprev : ¬ p ∣ n.descFactorial (k + 1) := by
        intro h
        obtain ⟨i, hi, hdiv⟩ := factor (k + 1) h
        have heq : (n - i) - (n - (k + 1)) = k + 1 - i := by omega
        have hgap : p ∣ k + 1 - i := heq ▸ Nat.dvd_sub hdiv hlast
        have hle := Nat.le_of_dvd (show 0 < k + 1 - i by omega) hgap
        omega
      have hc := (hp.coprime_iff_not_dvd.mpr hprev).pow_left 2
      exact hsq (k + 1) (by omega) (hc.dvd_of_dvd_mul_right hd)
    · have hc := (hp.coprime_iff_not_dvd.mpr hlast).pow_left 2
      exact ih (by omega) (by omega) (fun i hi => hsq i (by omega))
        (hc.dvd_of_dvd_mul_left hd)

theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  classical
  intro hsmall hrad k
  obtain ⟨B, hB2, hkB, hG⟩ := hrad k
  obtain ⟨M, hM, hsm, hs⟩ := hsmall k B hB2 hkB
  obtain ⟨T, G, hGT, hsize, hgood⟩ := hG M hM hsm
  obtain ⟨bad, hcard, hbad⟩ := square_sieve (T := T) hkB hM hsm
  have hnsub : ¬ G ⊆ bad := fun h => (hcard.trans_lt hsize).not_ge (card_le_card h)
  obtain ⟨t, ht, hnot⟩ := Finset.not_subset.mp hnsub
  let n := M*(t+1)-1
  have hkn : k < n := by
    have := Nat.le_mul_of_pos_right M (by omega : 0 < t+1)
    dsimp [n]; omega
  have hn0 : n.descFactorial (k+1) ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
  refine ⟨n, (Nat.factorization_le_iff_dvd hn0 (Nat.centralBinom_pos n).ne').mp ?_⟩
  intro p
  by_cases hp : p.Prime
  · by_cases hpB : p ≤ B
    · exact hs t p hp hpB
    · by_cases hpd : p ∣ n.descFactorial (k+1)
      · have hp2 := prime_sq_not_dvd_descFactorial hp hkn (by omega : k < p)
          (fun i hi hd => hnot (hbad t (mem_range.mp (hGT ht)) i hi p hp (by omega) hd))
        have hv : (n.descFactorial (k+1)).factorization p < 2 :=
          Nat.lt_of_not_ge (fun hh => hp2 ((hp.pow_dvd_iff_le_factorization hn0).mpr hh))
        have hc := hp.factorization_pos_of_dvd (Nat.centralBinom_pos n).ne'
          (hgood t ht p hp (by omega) hpd)
        omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
        exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end OMA.R_Erdos396_erdos_396_R2
