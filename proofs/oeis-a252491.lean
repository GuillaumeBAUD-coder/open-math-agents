import OMAStatements.S_oeis_a252491

-- Credit: @anmolspace. M. F. Hasler recorded the A086766 implication in A252491.

open OMA.S_oeis_a252491
open Finset

private def rep (b k : ℕ) : ℕ := ∑ i ∈ range k, b ^ i

private lemma times_pred (b k : ℕ) (hb : 1 ≤ b) : rep b k * (b - 1) = b ^ k - 1 :=
  geom_sum_mul_of_one_le hb k

private lemma compose (b m n : ℕ) (hb : 1 < b) :
    rep b m * rep (b ^ m) n = rep b (m * n) := by
  apply Nat.eq_of_mul_eq_mul_right (show 0 < b - 1 by omega)
  calc
    _ = rep (b ^ m) n * (rep b m * (b - 1)) := by ring
    _ = rep (b ^ m) n * (b ^ m - 1) := by rw [times_pred _ _ hb.le]
    _ = (b ^ m) ^ n - 1 := times_pred _ _ (Nat.one_le_pow _ _ (by omega))
    _ = rep b (m * n) * (b - 1) := by rw [times_pred _ _ hb.le, pow_mul]

private lemma rep_gt_one {b k : ℕ} (hb : 0 < b) (hk : 2 ≤ k) : 1 < rep b k := by
  calc
    1 < b + 1 := by omega
    _ = rep b 2 := by simp [rep]
    _ ≤ rep b k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun _ _ _ => Nat.zero_le _)

private lemma rep_strict {b c k : ℕ} (hbc : b < c) (hk : 2 ≤ k) : rep b k < rep c k := by
  apply Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left hbc.le i)
  exact ⟨1, mem_range.mpr (by omega), by simpa using hbc⟩

private lemma coprime_repunits {m n : ℕ} (hc : m.Coprime n) :
    (rep 10 m).Coprime (rep 10 n) := by
  have h : (rep 10 m * (10 - 1)).gcd (rep 10 n * (10 - 1)) = 9 := by
    rw [times_pred _ _ (by decide), times_pred _ _ (by decide),
      Nat.pow_sub_one_gcd_pow_sub_one, hc.gcd_eq_one]
    decide
  rw [Nat.gcd_mul_right] at h
  change (rep 10 m).gcd (rep 10 n) = 1
  omega

private lemma rep_dvd_base_pow {m n : ℕ} (hc : m.Coprime n) :
    rep 10 m ∣ rep (10 ^ n) m := by
  apply (coprime_repunits hc).dvd_of_dvd_mul_left
  rw [compose _ _ _ (by decide), Nat.mul_comm n m, ← compose 10 m n (by decide)]
  exact dvd_mul_right _ _

private lemma a_eq (p : ℕ) (hp : 0 < p) : a p = rep (10 ^ p) p := by
  unfold a rep
  rw [Nat.geomSum_eq (by exact Nat.one_lt_pow (by omega) (by decide) : 2 ≤ 10 ^ p),
    ← pow_mul, sq]

private lemma no_prime_candidate {p : ℕ} (hp : p.Prime) (ha : ¬ (a p).Prime)
    (m : ℕ) (hm : 2 ≤ m) : ¬ (rep (10 ^ p) m).Prime := by
  intro hprime
  have hp2 := hp.two_le
  have hb : 1 < 10 ^ p := Nat.one_lt_pow (by omega) (by decide)
  by_cases hd : p ∣ m
  · obtain ⟨k, hk⟩ := hd
    have hadvd : a p ∣ rep (10 ^ p) m := by
      rw [a_eq p hp.pos, hk, ← compose _ _ _ hb]
      exact dvd_mul_right _ _
    have hn : 1 < a p := (a_eq p hp.pos).symm ▸ rep_gt_one (by positivity) hp2
    rcases (Nat.dvd_prime hprime).mp hadvd with h | h
    · omega
    · exact ha (h ▸ hprime)
  · have hc : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hd).symm
    have hdiv := rep_dvd_base_pow hc
    have hlt : rep 10 m < rep (10 ^ p) m := rep_strict (by
      calc
        10 = 10 ^ 1 := by norm_num
        _ < 10 ^ p := Nat.pow_lt_pow_right (by decide) (by omega)) hm
    have hbig : 1 < rep 10 m := rep_gt_one (by decide) hm
    rcases (Nat.dvd_prime hprime).mp hdiv with h | h <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a252491.main := by
  intro p hp ha
  have hp0 := hp.pos
  have hnum : (10 : ℕ) ^ (p - 1) ≠ 0 := by positivity
  have hlen : (Nat.digits 10 (10 ^ (p - 1))).length = p := by
    rw [Nat.length_digits _ _ (by decide) hnum, Nat.log_pow (by decide)]
    omega
  have ht : 10 ^ (p - 1) * 10 = 10 ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp0]
  unfold repetitionCount
  rw [if_neg hnum, hlen]
  suffices empty : {r : ℕ | 0 < r ∧
      (10 ^ (p - 1) * (∑ i ∈ range r, (10 ^ p) ^ i) * 10 + 1).Prime} = ∅ by
    simp [empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr, hprime⟩ := hr
  apply no_prime_candidate hp ha (r + 1) (by omega)
  unfold rep
  rw [geom_sum_succ]
  have hcandidate : 10 ^ (p - 1) * (∑ i ∈ range r, (10 ^ p) ^ i) * 10 + 1 =
      10 ^ p * (∑ i ∈ range r, (10 ^ p) ^ i) + 1 := by
    rw [mul_right_comm _ _ 10, ht]
  exact hcandidate ▸ hprime
