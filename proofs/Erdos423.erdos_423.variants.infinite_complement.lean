import FormalConjectures.ErdosProblems.«423»

/-!
If the excess over the index were bounded, the sequence would become consecutive.
Tang reduces a representation to the case of an initial block followed by a consecutive tail.
For this qualitative claim, choosing odd exponents rules out the remaining case by a gap between squares.
See Quanyu Tang, The Hofstadter Consecutive-Sum Sequence Omits Infinitely Many Positive Integers, arXiv:2603.09939.
-/

open Erdos423 Finset Filter

private lemma twice_sum_Ico_add (i j c : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    2 * (∑ l ∈ Ico i j, (l + c)) + (i + c - 1) * (i + c) =
      (j + c - 1) * (j + c) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
      rw [Finset.sum_Ico_succ_top hij]
      have hu : j + 1 + c - 1 = j + c := by omega
      have hv : j + c - 1 + 1 = j + c := by omega
      rw [hu]
      nlinarith [congrArg (fun x : ℕ => x * (j + c)) hv]

private lemma even_of_one_lt_of_dvd_two_pow {d m : ℕ} (hd : 1 < d) (hm : d ∣ 2 ^ m) :
    Even d := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
  cases k with
  | zero => simp at hd
  | succ k =>
      refine ⟨2 ^ k, ?_⟩
      rw [pow_succ]
      omega

private lemma no_large_even_square_gap {x y A B : ℕ}
    (hxy : x ≠ y) (hA : A < x) (hB : B < x) (h : x ^ 2 + A = y ^ 2 + B) :
    False := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hs : (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  · have hs : y ^ 2 ≤ (x - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have heq : x - 1 + 1 = x := by omega
    nlinarith [congrArg (fun z : ℕ => z * (x - 1)) heq]

theorem OMA.solution : type_of% @Erdos423.erdos_423.variants.infinite_complement := by
  intro a ha
  classical
  by_contra hfinite
  obtain ⟨M, hM⟩ := not_forall.mp (mt ha.infinite_compl_of_unbounded hfinite)
  have hbdd (n : ℕ) : a (n + 1) - (n + 1) ≤ M := by
    by_contra! h
    apply hM
    rw [eventually_atTop]
    refine ⟨n + 1, fun k hk => ?_⟩
    have hmono := erdos_423.variants.nondecreasing a ha (n + 1) k (by omega) hk
    omega
  obtain ⟨c, N₀, hlin₀⟩ := converges_of_monotone_of_bounded
    (f := fun n => a (n + 1) - (n + 1))
    (fun _ _ h => erdos_423.variants.nondecreasing a ha _ _ (by omega) (by omega)) hbdd
  let N := N₀ + 3
  have hN : 3 ≤ N := by omega
  have hlin (n : ℕ) (hn : N ≤ n) : a n = n + c := by
    have he := hlin₀ (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at he
    have hl := ha.le_apply n (by omega)
    omega

  let S := ∑ l ∈ Ico 1 N, a l
  let z := N + c - 1
  let m := 8 * S + (2 * z + 1) ^ 2 + (N + c) + 10
  let t := 2 ^ m
  let P := 2 ^ (2 * m + 1)
  have hmt : m < t := Nat.lt_two_pow_self
  have hP : P = 2 * t ^ 2 := by
    dsimp [P, t]
    rw [pow_succ, two_mul, pow_add, pow_two, mul_comm]
  have hPt : t ≤ P := by nlinarith [Nat.one_le_two_pow (n := m)]
  have hNP : N + c ≤ P := by dsimp [m] at hmt; omega
  have hSP : S < P := by dsimp [m] at hmt; omega
  have hrepresent := (ha.2.2 (P - c) (by omega)).1
  rw [hlin _ (by omega), Nat.sub_add_cancel (by omega : c ≤ P)] at hrepresent
  obtain ⟨i, j, hi, hij, -, heq⟩ := hrepresent
  rw [← Finset.Ico_succ_right_eq_Icc] at heq
  change P = ∑ l ∈ Ico i (j + 1), a l at heq

  have hj : N ≤ j := by
    by_contra! h
    have hsub : Ico i (j + 1) ⊆ Ico 1 N := by
      intro l hl
      simp only [mem_Ico] at hl ⊢
      omega
    have hle : (∑ l ∈ Ico i (j + 1), a l) ≤ S := Finset.sum_le_sum_of_subset hsub
    omega

  have hsum (k : ℕ) (hk : N ≤ k) (hkj : k ≤ j + 1) :
      2 * (∑ l ∈ Ico k (j + 1), a l) + (k + c - 1) * (k + c) =
        (j + c) * (j + c + 1) := by
    have hrewrite : (∑ l ∈ Ico k (j + 1), a l) = ∑ l ∈ Ico k (j + 1), (l + c) := by
      refine sum_congr rfl fun l hl => hlin l ?_
      exact hk.trans (mem_Ico.mp hl).1
    rw [hrewrite]
    have h1 : j + 1 + c - 1 = j + c := by omega
    have h2 : j + 1 + c = j + c + 1 := by omega
    simpa only [h2, Nat.add_sub_cancel] using twice_sum_Ico_add k (j + 1) c (by omega) hkj

  by_cases hNi : N ≤ i
  · have hformula := hsum i hNi (by omega)
    rw [← heq] at hformula
    have hlen : j + 1 - i + i = j + 1 := by omega
    have hstart : i + c - 1 + 1 = i + c := by omega
    have hfactor : (j + 1 - i) * (i + j + 2 * c) = 2 * P := by
      nlinarith [congrArg (fun x : ℕ => x * (i + j + 2 * c)) hlen,
        congrArg (fun x : ℕ => x * (i + c)) hstart]
    have hpow : 2 * P = 2 ^ (2 * m + 1 + 1) := by simp [P, pow_succ, mul_comm]
    rw [hpow] at hfactor
    obtain ⟨p, hp⟩ := even_of_one_lt_of_dvd_two_pow
      (d := j + 1 - i) (by omega) ⟨_, hfactor.symm⟩
    obtain ⟨q, hq⟩ := even_of_one_lt_of_dvd_two_pow
      (d := i + j + 2 * c) (by omega) ⟨_, hfactor.symm.trans (mul_comm _ _)⟩
    omega
  · let A := ∑ l ∈ Ico i N, a l
    have hsub : Ico i N ⊆ Ico 1 N := by
      intro l hl
      simp only [mem_Ico] at hl ⊢
      omega
    have hA : A ≤ S := Finset.sum_le_sum_of_subset hsub
    have hsplit : A + ∑ l ∈ Ico N (j + 1), a l = P := by
      dsimp [A]
      rw [Finset.sum_Ico_consecutive _ (by omega : i ≤ N) (by omega : N ≤ j + 1)]
      exact heq.symm
    have hz : N + c = z + 1 := by dsimp [z]; omega
    have hformula := hsum N (le_refl _) (by omega)
    change 2 * (∑ l ∈ Ico N (j + 1), a l) + z * (N + c) =
      (j + c) * (j + c + 1) at hformula
    rw [hz] at hformula
    have hsquare : (4 * t) ^ 2 + (2 * z + 1) ^ 2 =
        (2 * (j + c) + 1) ^ 2 + 8 * A := by nlinarith
    apply no_large_even_square_gap (x := 4 * t) (y := 2 * (j + c) + 1)
      (A := (2 * z + 1) ^ 2) (B := 8 * A)
    · omega
    · dsimp [m] at hmt
      omega
    · dsimp [m] at hmt
      omega
    · exact hsquare