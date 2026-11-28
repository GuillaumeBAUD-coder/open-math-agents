import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1.H2

Proves that no unitary perfect number has `5` as its unique repeated odd prime with exponent `2`,
`a = padicValNat 2 n ≥ 43`, `a ≡ 2 (mod 4)`, and `3 ∣ n` (so `padicValNat 2 n ≤ 0` holds vacuously).

Proof: An exact branch-and-bound search tree over the set `P` of simple odd primes, tracking a
known subset `X ⊆ P` and threshold `N` such that every prime in `P` below `N` belongs to `X`.
Starting from `X = [3, 7, 13]` and `N = 11`:
- `up_kill` rules out `X` when its weight alone reaches `2`;
- `up_jump` advances `N` directly to `N'` whenever any single prime below `N'` would push the weight
  of `X` to at least `2`;
- `extend` advances `N` to `N' < 2 * N` by ruling out all candidate primes `2 ^ i * 5 ^ j * d - 1`
  in `[N, N')` (with `d` a product of distinct open primes in `X`) via explicit composite factors;
- `low_kill` rules out states where the weight of `X` times the path bound over open primes
  (with per-open lower bound `max N (2 * c - 1)`), remaining ledger of `5` (at most `1` since
  `5 ∣ 2 ^ a + 1` already supplies one factor of `5`), and Mersenne tail bound (using the next
  Mersenne prime `≥ N`) falls strictly below `2 * 2 ^ 43 / (2 ^ 43 + 1)`.
-/

namespace OMA.P_Erdos1052_z5_e2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts path_bound tail_bound exists_child two_mul_le
  B_step B_anti B_nonneg one_add_le_B kernel_balance_one two_pow_of_no_odd_prime
  five_dvd_two_pow_add_one prime_dvd_prime_pow)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- Section 1. Computable checks and certificate tree.

def subProds : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProds t ++ (subProds t).map (fun d => c * d)

def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 13 && X.all (fun x => (x + 1) % c != 0))

def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

def ledgerLeft (X : List ℕ) : ℕ :=
  if (5 * succProd X) % 25 == 0 then 0 else 1

def nextMersenne (N : ℕ) : ℕ :=
  if N ≤ 3 then 3
  else if N ≤ 7 then 7
  else if N ≤ 31 then 31
  else if N ≤ 127 then 127
  else if N ≤ 8191 then 8191
  else if N ≤ 131071 then 131071
  else if N ≤ 524287 then 524287
  else if N ≤ 2147483647 then 2147483647
  else N

def openNum (X : List ℕ) (N : ℕ) : ℕ :=
  ((opens X).map (fun c => max N (2 * c - 1) + 1)).prod

def openDen (X : List ℕ) (N : ℕ) : ℕ :=
  ((opens X).map (fun c => max N (2 * c - 1) - 1)).prod

def candOk (X F : List ℕ) (N N' v : ℕ) : Bool :=
  decide (v < N) || decide (N' ≤ v) || decide (v ∈ X) ||
    F.any (fun f => decide (1 < f) && decide (f < v) && v % f == 0)

def checkDoubles (X F : List ℕ) (N N' : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, cur =>
    if N' < cur then true
    else candOk X F N N' (cur - 1) && checkDoubles X F N N' fuel (2 * cur)

def winOk (X F : List ℕ) (N N' : ℕ) : Bool :=
  decide (N' < 2 * N) && decide (N' < 2 ^ 40) &&
    (subProds (opens X)).all (fun d => [0, 1].all (fun j =>
      (5 ^ j * succProd X) % 25 == 0 ||
        checkDoubles X F N N' 40 (2 * (5 ^ j * d))))

def upOk (X : List ℕ) : Bool := decide (2 * 25 * X.prod ≤ 26 * succProd X)

def upJumpOk (X : List ℕ) (N N' : ℕ) : Bool :=
  decide (N ≤ N') && decide (1 ≤ N') &&
    decide (2 * 25 * X.prod * (N' - 1) ≤ 26 * succProd X * N')

def lowOk (X : List ℕ) (N : ℕ) : Bool :=
  let M := nextMersenne N
  let L := ledgerLeft X
  decide (5 ≤ N) &&
    decide ((2 ^ 43 + 1) * 26 * succProd X * openNum X N * (N + 1) ^ L * (M + 1) <
      2 * 2 ^ 43 * 25 * X.prod * openDen X N * (N - 1) ^ L * (M - 3))

inductive ProofTree where
  | up
  | low
  | led
  | jump (N' : ℕ) (t : ProofTree)
  | ext (N' : ℕ) (F : List ℕ) (t : ProofTree)
  | br (p : ℕ) (F : List ℕ) (t1 t2 : ProofTree)

def checkTree (X : List ℕ) (N : ℕ) : ProofTree → Bool
  | .up => upOk X
  | .low => lowOk X N
  | .led => decide (succProd X % 25 = 0)
  | .jump N' t => upJumpOk X N N' && checkTree X N' t
  | .ext N' F t => winOk X F N N' && checkTree X N' t
  | .br p F t1 t2 =>
    decide (N ≤ p) && decide (p ∉ X) && winOk X F N p &&
      checkTree (p :: X) (p + 1) t1 && checkTree X (p + 1) t2

-- Section 2. Context and state.

structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 26 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  h13 : ∀ p ∈ P, ¬ 13 ∣ p + 1
  led : ¬ 5 ^ 2 ∣ ∏ p ∈ P, (p + 1)
  hm : 43 ≤ m

def St (P : Finset ℕ) (X : List ℕ) (N : ℕ) : Prop :=
  (∀ x ∈ X, x ∈ P) ∧ X.Nodup ∧ ∀ p ∈ P, p < N → p ∈ X

theorem incl_step {P : Finset ℕ} {X : List ℕ} {p : ℕ} (h : St P X p) (hp : p ∈ P) (hpX : p ∉ X) :
    St P (p :: X) (p + 1) := by
  obtain ⟨hXP, hXn, hcl⟩ := h
  refine ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨hpX, hXn⟩, fun q hq hqp => ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact hXP x hx
  · by_cases hlt : q < p
    · exact List.mem_cons_of_mem _ (hcl q hq hlt)
    · have : q = p := by omega
      subst this
      exact List.mem_cons_self

theorem excl_step {P : Finset ℕ} {X : List ℕ} {p : ℕ} (h : St P X p) (hp : p ∉ P) :
    St P X (p + 1) := by
  obtain ⟨hXP, hXn, hcl⟩ := h
  refine ⟨hXP, hXn, fun q hq hqp => ?_⟩
  have hne : q ≠ p := fun e => hp (e ▸ hq)
  exact hcl q hq (by omega)

-- Section 3. Elementary lemmas.

theorem mem_subProds : ∀ (l : List ℕ), (∀ c ∈ l, c.Prime) → ∀ d : ℕ, d ∣ l.prod → d ∈ subProds l
  | [], _, d, hd => by
    rw [List.prod_nil, Nat.dvd_one] at hd
    rw [hd]
    exact List.mem_singleton.mpr rfl
  | c :: t, hl, d, hd => by
    have hc : c.Prime := hl c List.mem_cons_self
    have ht : ∀ x ∈ t, x.Prime := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.prod_cons] at hd
    unfold subProds
    rw [List.mem_append, List.mem_map]
    by_cases hcd : c ∣ d
    · obtain ⟨d', rfl⟩ := hcd
      exact Or.inr ⟨d', mem_subProds t ht d' (Nat.dvd_of_mul_dvd_mul_left hc.pos hd), rfl⟩
    · have hcop : Nat.Coprime d c := ((Nat.Prime.coprime_iff_not_dvd hc).mpr hcd).symm
      rw [mul_comm] at hd
      exact Or.inl (mem_subProds t ht d (Nat.Coprime.dvd_of_dvd_mul_right hcop hd))

theorem dvd_of_primes {d D : ℕ} (hsq : ∀ c : ℕ, c.Prime → ¬ c * c ∣ d)
    (h : ∀ c : ℕ, c.Prime → c ∣ d → c ∣ D) : d ∣ D := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd D d).mpr fun c k hc hck => ?_
  rcases k with _ | _ | k
  · rw [pow_zero]
    exact one_dvd _
  · rw [zero_add, pow_one] at hck ⊢
    exact h c hc hck
  · exact absurd ((Dvd.intro (c ^ k) (by ring) : c * c ∣ c ^ (k + 1 + 1)).trans hck) (hsq c hc)

theorem mem_opens {X : List ℕ} {c : ℕ} (hc : c ∈ X) (h13 : c ≠ 13)
    (h : ∀ x ∈ X, ¬ c ∣ x + 1) : c ∈ opens X := by
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨h13, fun x hx hmod => h x hx (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem succProd_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, (x + 1) = succProd X :=
  List.prod_toFinset _ hn

theorem prod_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, x = X.prod := by
  rw [List.prod_toFinset _ hn, List.map_id']

theorem prod_mul_dvd {P : Finset ℕ} {X : List ℕ} (hXP : ∀ x ∈ X, x ∈ P) (hn : X.Nodup)
    {T : Finset ℕ} (hT : T ⊆ P) (hTX : ∀ q ∈ T, q ∉ X) :
    (∏ q ∈ T, (q + 1)) * succProd X ∣ ∏ p ∈ P, (p + 1) := by
  have hdisj : Disjoint T X.toFinset :=
    Finset.disjoint_left.mpr fun q hq hqX => hTX q hq (List.mem_toFinset.mp hqX)
  rw [← succProd_eq hn, ← Finset.prod_union hdisj]
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.union_subset hT fun x hx => hXP x (List.mem_toFinset.mp hx))

theorem checkDoubles_spec (X F : List ℕ) (N N' : ℕ) :
    ∀ fuel cur, checkDoubles X F N N' fuel cur = true →
      ∀ k < fuel, 2 ^ k * cur ≤ N' → candOk X F N N' (2 ^ k * cur - 1) = true
  | 0, _, _, _, hk, _ => by omega
  | fuel + 1, cur, hchk, k, hk, hle => by
    unfold checkDoubles at hchk
    split_ifs at hchk with hgt
    · have h1 : cur ≤ 2 ^ k * cur := Nat.le_mul_of_pos_left cur (by positivity)
      omega
    · rw [Bool.and_eq_true] at hchk
      rcases k with _ | k
      · simpa using hchk.1
      · have hle' : 2 ^ k * (2 * cur) ≤ N' := by
          have : 2 ^ (k + 1) * cur = 2 ^ k * (2 * cur) := by rw [pow_succ]; ring
          omega
        have := checkDoubles_spec X F N N' fuel (2 * cur) hchk.2 k (by omega) hle'
        rwa [show 2 ^ (k + 1) * cur = 2 ^ k * (2 * cur) by rw [pow_succ]; ring]

private lemma not_prime_of_dvd_between {n d : ℕ} (hd1 : 1 < d) (hdn : d < n) (hdvd : d ∣ n) :
    ¬ n.Prime := by
  intro hp
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2 <;> omega

theorem mersenne_ge {q N : ℕ} (hq : q.Prime) (hpow : ∃ k, q + 1 = 2 ^ k) (hN : N ≤ q) :
    nextMersenne N ≤ q := by
  by_cases hbig : 2147483647 ≤ q
  · unfold nextMersenne
    split_ifs <;> omega
  · obtain ⟨k, hk⟩ := hpow
    have hk31 : k < 31 := by
      by_contra hge
      have h1 : 2 ^ 31 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h1
      omega
    have hq_eq : q = 2 ^ k - 1 := by omega
    have hcases : q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 ∨ q = 8191 ∨ q = 131071 ∨ q = 524287 := by
      interval_cases k
      · norm_num at hq_eq; subst hq_eq; norm_num at hq
      · norm_num at hq_eq; subst hq_eq; norm_num at hq
      · omega
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 7) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 23) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 7) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · omega
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 7) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 47) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 31) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 7) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 233) (by norm_num) (by norm_num) (by norm_num))
      · exact absurd hq (hq_eq ▸ not_prime_of_dvd_between (d := 3) (by norm_num) (by norm_num) (by norm_num))
    unfold nextMersenne
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> omega

theorem nextMersenne_ge_five {N : ℕ} (hN : 5 ≤ N) : 5 ≤ nextMersenne N := by
  unfold nextMersenne
  split_ifs <;> omega

-- Section 4. Window extension and kills.

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X F : List ℕ} {N N' : ℕ}
    (h : St P X N) (hchk : winOk X F N N' = true) : St P X N' := by
  obtain ⟨hXP, hXn, hcl⟩ := h
  refine ⟨hXP, hXn, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact hcl p hp hpN
  by_contra hpX
  simp only [winOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨hN2, hN40⟩, hall⟩ := hchk
  have hpp := (C.hP p hp).1
  have hp2 := (C.hP p hp).2
  have hpodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  obtain ⟨i, u, hu, hiu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := p + 1) (by omega) 2 (by norm_num)
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hiu
    omega
  obtain ⟨j, d, hd, hjd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := u) hu0 5 (by norm_num)
  have hdvd : d ∣ p + 1 := ⟨2 ^ i * 5 ^ j, by rw [hiu, hjd]; ring⟩
  have hprime : ∀ c : ℕ, c.Prime → c ∣ d → c ≠ 2 ∧ c ≠ 5 := fun c _ hcd =>
    ⟨fun h2 => hu (by rw [hjd]; exact (h2 ▸ hcd).mul_left _), fun h5 => hd (h5 ▸ hcd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ opens X := fun c hc hcd => by
    obtain ⟨hc2, hc5⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hc5 p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    refine mem_opens hcX (fun h13 => C.h13 p hp (h13 ▸ hcp)) fun x hx hcx => ?_
    exact hpX ((C.s3 c hc hc2 hc5 p hp x (hXP x hx) hcp hcx) ▸ hx)
  have hdD : d ∣ (opens X).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hc5⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hc5 p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hmem : d ∈ subProds (opens X) := mem_subProds _
    (fun c hc => (C.hP c (hXP c (List.mem_filter.mp hc).1)).1) d hdD
  have hjdvd : 5 ^ j ∣ p + 1 := ⟨2 ^ i * d, by rw [hiu, hjd]; ring⟩
  have hj2 : j < 2 := by
    by_contra hj
    exact C.led (((pow_dvd_pow 5 (by omega : 2 ≤ j)).trans hjdvd).trans
      (Finset.dvd_prod_of_mem (fun q => q + 1) hp))
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hu ⟨(p + 1) / 2, by omega⟩
  have hi40 : i ≤ 40 := by
    by_contra hi
    have h1 : 2 ^ 41 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ i ≤ p + 1 := by
      rw [hiu]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    norm_num at h1 hN40
    omega
  have h1 := hall d hmem j (by interval_cases j <;> decide)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · have h2 : 5 ^ 2 ∣ 5 ^ j * succProd X := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1)
    have h3 : 5 ^ j * succProd X ∣ (p + 1) * succProd X := Nat.mul_dvd_mul_right hjdvd _
    have h4 := prod_mul_dvd hXP hXn (T := {p}) (Finset.singleton_subset_iff.mpr hp)
      (fun q hq => (Finset.mem_singleton.mp hq) ▸ hpX)
    rw [Finset.prod_singleton] at h4
    exact C.led (h2.trans (h3.trans h4))
  · have hcur : 2 ^ (i - 1) * (2 * (5 ^ j * d)) = p + 1 := by
      have : 2 ^ (i - 1) * 2 = 2 ^ i := by
        rw [← pow_succ, Nat.sub_add_cancel hi1]
      calc 2 ^ (i - 1) * (2 * (5 ^ j * d)) = (2 ^ (i - 1) * 2) * (5 ^ j * d) := by ring
        _ = 2 ^ i * (5 ^ j * d) := by rw [this]
        _ = p + 1 := by rw [← hjd, ← hiu]
    have h2 := checkDoubles_spec X F N N' 40 (2 * (5 ^ j * d)) h1 (i - 1) (by omega) (by omega)
    rw [hcur, show p + 1 - 1 = p by omega] at h2
    simp only [candOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h2
    rcases h2 with ((h2 | h2) | h2) | ⟨f, -, ⟨hf1, hfp⟩, hmod⟩
    · exact hpN h2
    · omega
    · exact hpX h2
    · rcases (Nat.dvd_prime hpp).mp (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

theorem up_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N : ℕ}
    (h : St P X N) (hchk : upOk X = true) : False := by
  obtain ⟨hXP, hXn, -⟩ := h
  simp only [upOk, decide_eq_true_eq] at hchk
  have hF : X.toFinset ⊆ P := fun x hx => hXP x (List.mem_toFinset.mp hx)
  have h1 := Finset.prod_sdiff hF (f := fun p => p + 1)
  have h2 := Finset.prod_sdiff hF (f := fun p => p)
  rw [succProd_eq hXn] at h1
  rw [prod_eq hXn] at h2
  have hQ : ∏ p ∈ P \ X.toFinset, p ≤ ∏ p ∈ P \ X.toFinset, (p + 1) :=
    Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.le_succ i)
  have hpos : 0 < ∏ p ∈ P \ X.toFinset, (p + 1) := Finset.prod_pos fun p _ => Nat.succ_pos p
  have hSpos : 0 < succProd X := by
    unfold succProd
    exact List.prod_pos (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
      exact Nat.succ_pos x)
  have E := C.E
  rw [← h1, ← h2] at E
  have key : 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod) <
      (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) :=
    calc 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod)
        = 2 ^ m * ((∏ p ∈ P \ X.toFinset, p) * (2 * 25 * X.prod)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hchk)
      _ < (2 ^ m + 1) * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _)
            (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem up_jump {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N N' : ℕ}
    (h : St P X N) (hchk : upJumpOk X N N' = true) : St P X N' := by
  simp only [upJumpOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hNN', hN'1⟩, hnum⟩ := hchk
  obtain ⟨hXP, hXn, hcl⟩ := h
  refine ⟨hXP, hXn, fun p hp hpN' => ?_⟩
  by_contra hpX
  obtain ⟨k, rfl⟩ : ∃ k, N' = k + 1 := ⟨N' - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hnum
  have hp_le : p * (k + 1) ≤ (p + 1) * k := by nlinarith
  have hmul : 2 * 25 * (p * X.prod) * (k + 1) ≤ 26 * ((p + 1) * succProd X) * (k + 1) :=
    calc 2 * 25 * (p * X.prod) * (k + 1)
        = 2 * 25 * X.prod * (p * (k + 1)) := by ring
      _ ≤ 2 * 25 * X.prod * ((p + 1) * k) := Nat.mul_le_mul_left _ hp_le
      _ = (2 * 25 * X.prod * k) * (p + 1) := by ring
      _ ≤ (26 * succProd X * (k + 1)) * (p + 1) := Nat.mul_le_mul_right _ hnum
      _ = 26 * ((p + 1) * succProd X) * (k + 1) := by ring
  have hup : 2 * 25 * (p :: X).prod ≤ 26 * succProd (p :: X) := by
    simp only [List.prod_cons, succProd, List.map_cons]
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hst : St P (p :: X) N :=
    ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact hXP x hx,
      List.nodup_cons.mpr ⟨hpX, hXn⟩,
      fun q hq hqN => List.mem_cons_of_mem _ (hcl q hq hqN)⟩
  exact up_kill C hst (decide_eq_true hup)

theorem led_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N : ℕ}
    (h : St P X N) (hchk : decide (succProd X % 25 = 0) = true) : False := by
  obtain ⟨hXP, hXn, -⟩ := h
  have h25 : 5 ^ 2 ∣ succProd X := Nat.dvd_of_mod_eq_zero (decide_eq_true_eq.mp hchk)
  have h1 := prod_mul_dvd hXP hXn (T := ∅) (Finset.empty_subset _) (fun _ hq => absurd hq (Finset.notMem_empty _))
  rw [Finset.prod_empty, one_mul] at h1
  exact C.led (h25.trans h1)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 26 * ∏ p ∈ P, ((p : ℚ) + 1) =
      2 ^ (m + 1) * 25 * ∏ p ∈ P, (p : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) C.E
    push_cast at h
    exact h
  have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
    field_simp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [e]
  field_simp
  rw [pow_succ] at hcast
  linarith

theorem weight_list : ∀ X : List ℕ, (∀ x ∈ X, 0 < x) →
    (X.map (fun x : ℕ => 1 + 1 / (x : ℚ))).prod = (succProd X : ℚ) / (X.prod : ℚ)
  | [], _ => by simp [succProd]
  | x :: t, h => by
    have hx : (0 : ℚ) < x := by exact_mod_cast h x List.mem_cons_self
    have ht : (0 : ℚ) < (t.prod : ℚ) := by
      exact_mod_cast List.prod_pos (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ih := weight_list t (fun a ha => h a (List.mem_cons_of_mem _ ha))
    unfold succProd at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.prod_cons]
    push_cast
    field_simp

theorem open_prod_eq {N : ℕ} (hN : 5 ≤ N) : ∀ l : List ℕ,
    (l.map (fun c => (((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1))).prod =
      (((l.map (fun c => max N (2 * c - 1) + 1)).prod : ℕ) : ℚ) /
        (((l.map (fun c => max N (2 * c - 1) - 1)).prod : ℕ) : ℚ)
  | [] => by simp
  | c :: t => by
    have ih := open_prod_eq hN t
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    set m := max N (2 * c - 1)
    have hm : 5 ≤ m := le_trans hN (le_max_left _ _)
    have hsub : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hm1 : (0 : ℚ) < (m : ℚ) - 1 := by
      have : (5 : ℚ) ≤ m := by exact_mod_cast hm
      linarith
    have hdt : (0 : ℚ) < (((t.map (fun c => max N (2 * c - 1) - 1)).prod : ℕ) : ℚ) := by
      exact_mod_cast List.prod_pos (fun a ha => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
        have : 5 ≤ max N (2 * x - 1) := le_trans hN (le_max_left _ _)
        omega)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hsub]
    field_simp

theorem final_ineq {S Pi ON OD N M L : ℕ} (hN : 5 ≤ N) (hM : 5 ≤ M) (hPi : 0 < Pi) (hOD : 0 < OD)
    (h : (2 ^ 43 + 1) * 26 * S * ON * (N + 1) ^ L * (M + 1) <
      2 * 2 ^ 43 * 25 * Pi * OD * (N - 1) ^ L * (M - 3)) :
    (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) * ((S : ℚ) / Pi) *
      (((ON : ℚ) / OD) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ L * (((M : ℚ) + 1) / ((M : ℚ) - 3))) < 2 := by
  have hq := (Nat.cast_lt (α := ℚ)).mpr h
  push_cast at hq
  have hN1 : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hM3 : ((M - 3 : ℕ) : ℚ) = (M : ℚ) - 3 := by rw [Nat.cast_sub (by omega : 3 ≤ M)]; norm_num
  rw [hN1, hM3] at hq
  have hNq : (5 : ℚ) ≤ N := by exact_mod_cast hN
  have hMq : (5 : ℚ) ≤ M := by exact_mod_cast hM
  have hPiq : (0 : ℚ) < Pi := by exact_mod_cast hPi
  have hODq : (0 : ℚ) < OD := by exact_mod_cast hOD
  have hNm1 : (0 : ℚ) < (N : ℚ) - 1 := by linarith
  have hMm3 : (0 : ℚ) < (M : ℚ) - 3 := by linarith
  have e : (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) * ((S : ℚ) / Pi) *
      (((ON : ℚ) / OD) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ L * (((M : ℚ) + 1) / ((M : ℚ) - 3))) =
      (((2 : ℚ) ^ 43 + 1) * 26 * S * ON * ((N : ℚ) + 1) ^ L * ((M : ℚ) + 1)) /
        (2 ^ 43 * 25 * Pi * OD * ((N : ℚ) - 1) ^ L * ((M : ℚ) - 3)) := by
    rw [div_pow]
    field_simp
  rw [e, div_lt_iff₀ (by positivity)]
  linarith

theorem low_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N : ℕ}
    (h : St P X N) (hchk : lowOk X N = true) : False := by
  obtain ⟨hXP, hXn, hcl⟩ := h
  simp only [lowOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hN5, hnum⟩ := hchk
  classical
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hn5 : ∀ {c : ℕ}, c ∉ ({5} : Finset ℕ) → c ≠ 5 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 5 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hn5 hcN, C.s1 _ hc hc2 (hn5 hcN) p hp (hg p).1,
        two_mul_le hc hc2 (C.hP p hp).1 (C.hP p hp).2 (hg p).1⟩
  have hg1 : ∀ q ∈ P.filter (fun p => p ∉ X), g q ∈ P.filter (fun p => p ∉ X) → g q ≠ 1 :=
    fun q _ hgq h1 => by
      have := (C.hP _ (hQP _ hgq)).1
      rw [h1] at this
      exact Nat.not_prime_one this
  have hpath := path_bound g (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1)) (P.filter (fun p => p ∉ X)).card
    (P.filter (fun p => p ∉ X)) rfl
    (fun q hq => (C.hP q (hQP q hq)).1.pos)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      have := hc.two_le
      omega)
    (fun q hq q' hq' hgq he => by
      obtain ⟨hc, hc2, hc5, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact C.s3 _ hc hc2 hc5 q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
    (fun q hq => one_add_le_B (C.hP q (hQP q hq)).1.two_le)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact B_step hc.two_le h2)
  generalize hRdef : (P.filter (fun p => p ∉ X)).filter (fun q => g q ∉ P.filter (fun p => p ∉ X)) = R at hpath
  have hRQ : ∀ q ∈ R, q ∈ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).1
  have hRg : ∀ q ∈ R, g q ∉ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).2
  have hRP : ∀ q ∈ R, q ∈ P := fun q hq => hQP q (hRQ q hq)
  have hA : ∀ q ∈ R, g q ≠ 1 → g q ∈ opens X := fun q hq h1 => by
    have hqP := hRP q hq
    obtain ⟨hc, hc2, hc5, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hq (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    refine mem_opens hcX (fun h13 => C.h13 q hqP (h13 ▸ (hg q).1)) fun x hx hcx => ?_
    exact hQX q (hRQ q hq) ((C.s3 _ hc hc2 hc5 q hqP x (hXP x hx) (hg q).1 hcx) ▸ hx)
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (C.hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  -- class A: per-open lower bound max N (2 * c - 1)
  have hAinj : Set.InjOn g (R.filter (fun q => g q ≠ 1) : Set ℕ) := by
    intro q hq q' hq' he
    obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
    obtain ⟨hc, hc2, hc5, -, -⟩ := hgp q (hRP q hqR) h1
    exact C.s3 _ hc hc2 hc5 q (hRP q hqR) q' (hRP q' hqR') (hg q).1 (he ▸ (hg q').1)
  have hAimg : (R.filter (fun q => g q ≠ 1)).image g ⊆ (opens X).toFinset := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp hq
    exact List.mem_toFinset.mpr (hA q hqR h1)
  have hprodA : ∏ q ∈ R.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (openNum X N : ℚ) / (openDen X N : ℚ) := by
    have hstep1 : ∏ q ∈ R.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
        ∏ q ∈ R.filter (fun q => g q ≠ 1),
          ((((max N (2 * g q - 1) : ℕ) : ℚ) + 1) / (((max N (2 * g q - 1) : ℕ) : ℚ) - 1)) := by
      refine Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp hq).1) fun q hq => ?_
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, -, -, -, h2⟩ := hgp q (hRP q hqR) h1
      have hqN := hQN q (hRQ q hqR)
      exact B_anti (by omega) (max_le hqN (by omega))
    have hstep2 : ∏ q ∈ R.filter (fun q => g q ≠ 1),
          ((((max N (2 * g q - 1) : ℕ) : ℚ) + 1) / (((max N (2 * g q - 1) : ℕ) : ℚ) - 1)) =
        ∏ c ∈ (R.filter (fun q => g q ≠ 1)).image g,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) :=
      (Finset.prod_image (f := fun c => ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)))
        (fun x hx y hy he => hAinj hx hy he)).symm
    have hge1 : ∀ c ∈ (opens X).toFinset,
        (1 : ℚ) ≤ (((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1) := by
      intro c _
      have hm : (5 : ℚ) ≤ (max N (2 * c - 1) : ℕ) := by exact_mod_cast (le_trans hN5 (le_max_left _ _))
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hstep3 : ∏ c ∈ (R.filter (fun q => g q ≠ 1)).image g,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) ≤
        ∏ c ∈ (opens X).toFinset,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) := by
      rw [← Finset.prod_sdiff hAimg]
      have h1 : (1 : ℚ) ≤ ∏ c ∈ (opens X).toFinset \ (R.filter (fun q => g q ≠ 1)).image g,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) :=
        Finset.one_le_prod fun c hc => hge1 c (Finset.mem_sdiff.mp hc).1
      have h0 : (0 : ℚ) ≤ ∏ c ∈ (R.filter (fun q => g q ≠ 1)).image g,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) :=
        Finset.prod_nonneg fun c hc => le_trans zero_le_one (hge1 c (hAimg hc))
      nlinarith
    have hstep4 : ∏ c ∈ (opens X).toFinset,
          ((((max N (2 * c - 1) : ℕ) : ℚ) + 1) / (((max N (2 * c - 1) : ℕ) : ℚ) - 1)) =
        (openNum X N : ℚ) / (openDen X N : ℚ) := by
      have hop_nd : (opens X).Nodup := hXn.filter _
      rw [List.prod_toFinset _ hop_nd]
      exact open_prod_eq hN5 (opens X)
    exact (hstep1.trans (hstep2.le.trans hstep3)).trans hstep4.le
  -- class B: leaves with 5 | q + 1, counted by the ledger
  have hledB : ¬ 5 ^ 2 ∣ 5 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card * succProd X :=
    fun hd => by
      have hsub : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1), q ∈ R := fun q hq =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      have h1 := prod_mul_dvd hXP hXn (T := (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1))
        (fun q hq => hRP q (hsub q hq)) (fun q hq => hQX q (hRQ q (hsub q hq)))
      have h2 : 5 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ∣
          ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1), (q + 1) := by
        rw [← Finset.prod_const]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
      exact C.led (hd.trans ((Nat.mul_dvd_mul_right h2 _).trans h1))
  have hcardB : ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤ ledgerLeft X := by
    unfold ledgerLeft
    by_contra hlt
    apply hledB
    split_ifs at hlt with h1
    · have hd1 : 5 ^ 2 ∣ 5 ^ 1 * succProd X := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1)
      exact hd1.trans (Nat.mul_dvd_mul_right (pow_dvd_pow 5 (by omega)) _)
    · exact (pow_dvd_pow 5 (by omega : 2 ≤ _)).mul_right _
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ledgerLeft X := by
    have h1 : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1),
        (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^
          ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
        (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
    exact h1.trans (pow_le_pow_right₀ hBN1 hcardB)
  -- class C: Mersenne leaves, bounded using nextMersenne N
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, h5⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact h5 (this ▸ hcd)
  have hM5 : 5 ≤ nextMersenne N := nextMersenne_ge_five hN5
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((nextMersenne N : ℚ) + 1) / ((nextMersenne N : ℚ) - 3) := by
    refine tail_bound _ _ (nextMersenne N) rfl (by omega)
      (fun q hq => by
        have hqR := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
        exact mersenne_ge (C.hP q (hRP q hqR)).1 (hpow q hq) (hQN q (hRQ q hqR)))
      (fun q hq q' hq' hlt => ?_)
    obtain ⟨k, hk⟩ := hpow q hq
    obtain ⟨k', hk'⟩ := hpow q' hq'
    have hkk : k < k' := by
      by_contra hge
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge)
      omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt hkk)
    rw [pow_succ] at this
    omega
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 5 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hODpos : 0 < openDen X N := by
    unfold openDen
    exact List.prod_pos fun a ha => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
      have : 5 ≤ max N (2 * c - 1) := le_trans hN5 (le_max_left _ _)
      omega
  have hB0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := le_trans zero_le_one hBN1
  have hRbound : ∏ q ∈ R, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ((openNum X N : ℚ) / (openDen X N : ℚ)) *
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ledgerLeft X *
        (((nextMersenne N : ℚ) + 1) / ((nextMersenne N : ℚ) - 3)) := by
    rw [← hsplit1, ← hsplit2, ← mul_assoc]
    have hAB := mul_le_mul hprodA hprodB
      (Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (by positivity)
    exact mul_le_mul hAB hprodC
      (Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (by positivity)
  have hXpos : ∀ x ∈ X, 0 < x := fun x hx => (C.hP x (hXP x hx)).1.pos
  have hfil : P.filter (fun p => p ∈ X) = X.toFinset := by
    ext x
    rw [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hXP x h, h⟩⟩
  have hsplitP := Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ X) (fun p => 1 + 1 / (p : ℚ))
  rw [hfil, List.prod_toFinset _ hXn, weight_list X hXpos] at hsplitP
  have hbal := balance_q C
  rw [← hsplitP] at hbal
  have hPipos : 0 < X.prod := List.prod_pos hXpos
  have hfin := final_ineq hN5 hM5 hPipos hODpos hnum
  have hm43 : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 43 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) C.hm)
  have hSq : (0 : ℚ) ≤ (succProd X : ℚ) / (X.prod : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hQle := hpath.trans hRbound
  have hQ0 : (0 : ℚ) ≤ ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hchain : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
      ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) ≤
      (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ)) *
        (((openNum X N : ℚ) / (openDen X N : ℚ)) *
          (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ledgerLeft X *
          (((nextMersenne N : ℚ) + 1) / ((nextMersenne N : ℚ) - 3))) := by
    have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) ≤ (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h2 : (succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) ≤
        (succProd X : ℚ) / (X.prod : ℚ) *
          (((openNum X N : ℚ) / (openDen X N : ℚ)) *
            (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ledgerLeft X *
            (((nextMersenne N : ℚ) + 1) / ((nextMersenne N : ℚ) - 3))) :=
      mul_le_mul_of_nonneg_left hQle hSq
    calc (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
        ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)))
        ≤ (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ) *
          (((openNum X N : ℚ) / (openDen X N : ℚ)) *
            (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ledgerLeft X *
            (((nextMersenne N : ℚ) + 1) / ((nextMersenne N : ℚ) - 3)))) :=
          mul_le_mul h1 h2 (mul_nonneg hSq hQ0) (by positivity)
      _ = _ := by ring
  linarith

theorem checkTree_sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    ∀ (t : ProofTree) (X : List ℕ) (N : ℕ), St P X N → checkTree X N t = true → False
  | .up, X, N, h, hchk => up_kill C h hchk
  | .low, X, N, h, hchk => low_kill C h hchk
  | .led, X, N, h, hchk => led_kill C h hchk
  | .jump N' t, X, N, h, hchk => by
    simp only [checkTree, Bool.and_eq_true] at hchk
    exact checkTree_sound C t X N' (up_jump C h hchk.1) hchk.2
  | .ext N' F t, X, N, h, hchk => by
    simp only [checkTree, Bool.and_eq_true] at hchk
    exact checkTree_sound C t X N' (extend C h hchk.1) hchk.2
  | .br p F t1 t2, X, N, h, hchk => by
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨-, hpX⟩, hwin⟩, ht1⟩, ht2⟩ := hchk
    have hp := extend C h hwin
    by_cases hmem : p ∈ P
    · exact checkTree_sound C t1 (p :: X) (p + 1) (incl_step hp hmem hpX) ht1
    · exact checkTree_sound C t2 X (p + 1) (excl_step hp hmem) ht2

-- Section 5. Certificate data.

def certIn11 : ProofTree :=
  (.jump 14 (.br 19 [3] (.jump 49 (.ext 97 [3] (.br 127 [] (.br 151 [] (.jump 171 (.ext 341 [3,5,7,11] (.ext 681 [3,7] (.ext 1118 [3,5,19] .low)))) (.ext 303 [3,5,11] (.ext 502 [3] .low))) (.br 151 [] (.ext 303 [3,5,7] .low) (.ext 202 [5] .low))))) (.br 31 [3] (.br 43 [3] (.jump 59 (.br 61 [] (.jump 1681 (.br 1951 [3] (.jump 12123 (.br 13759 [] (.jump 101912 (.br 131071 [3,13] (.jump 458097 (.br 524287 [3] (.jump 3628547 (.br 3995647 [] (.jump 39494330 (.br 67108351 [3] (.jump 95980204 (.ext 191960407 [3,7,23,31] (.ext 383920813 [3,7] (.br 536866807 [5,13] (.ext 1073733615 [3,29,233] (.ext 1195207774 [3,5] .low)) (.ext 935010213 [3,233] .low))))) (.ext 134216703 [3,5,7,23] (.ext 268433405 [3,7] (.ext 341044764 [3,7,11] .low))))) (.br 4194271 [] (.jump 26901976 (.br 33554167 [3,79] (.jump 135695634 (.br 255721471 [3,13] (.jump 289106813 (.br 511442941 [13] (.jump 665036489 (.br 1073733343 [3,19] (.jump 1747191950 (.br 2147483647 [3,5,311] (.jump 9373329901 (.ext 18746659801 [3,5,7] (.ext 37493319601 [3,5,31,43] (.ext 74986639201 [3,17,797,20897,23039] (.ext 131366606056 [3,19] .low))))) (.ext 4294967295 [3,17,59] (.ext 8589934589 [3,7,17] (.ext 17179869177 [3,5,7] (.ext 20970468818 [3] .low)))))) (.ext 2147466687 [3,5,311] (.br 2147483647 [3] (.ext 4294967295 [3,5,17,59,9241] (.ext 8589934589 [3,7] (.ext 13488750518 [7] .low))) (.ext 4294967295 [3,5,17,59] (.ext 7981041287 [3,7] .low)))))) (.ext 1022885883 [3,233] (.br 1073733343 [3] (.ext 2147466687 [3,5,13,311] (.br 2147483647 [3] (.ext 4294967295 [3,59,9241] (.ext 6790103278 [3] .low)) (.ext 4294967295 [3,59] (.ext 4747801537 [3] .low)))) (.ext 2147466687 [3,5,13,311] (.br 2147483647 [3] (.ext 4294967295 [3,5,59,9241] (.ext 4677339984 [3] .low)) (.ext 3469395783 [] .low))))))) (.ext 511442943 [3,5,7,13] (.ext 1022885885 [3,233,659] (.br 1073733343 [7417] (.ext 1646535416 [3,5] .low) (.ext 1452782302 [3,5] .low)))))) (.ext 67108335 [3,31,103,3109] (.ext 134216669 [3,5,7] (.ext 226569639 [3,7,13,229] .low))))) (.ext 8388543 [3,5,929] (.ext 16777085 [3,19,47] (.br 16777183 [71] (.ext 33554367 [3,5,79] (.ext 37361373 [31] .low)) (.ext 29225916 [3,79] .low))))))) (.ext 1048575 [3,13,967] (.ext 2097149 [3,7] (.ext 2750931 [7] .low))))) (.br 249727 [3] (.ext 499455 [3,19] (.br 524287 [] (.br 1048573 [3] (.ext 2008603 [3,5,7] .low) (.ext 1538940 [3] .low)) (.ext 688926 [] .low))) (.ext 499455 [3,19] (.br 524287 [3] (.ext 667134 [] .low) .low))))) (.br 15607 [] (.jump 54296 (.br 81919 [3,23] (.jump 161016 (.ext 322031 [3,19] (.br 499423 [3,5] (.br 524287 [] (.br 655351 [] (.jump 1290319 (.ext 2580637 [3,7] (.ext 5161273 [3,5,7] (.br 5242807 [] (.br 10485613 [3,5,47] (.ext 15319243 [3] .low) (.ext 13736222 [3] .low)) (.ext 10347424 [3,5,47] .low))))) (.br 1048573 [3,5] (.ext 2097147 [3,5,7] (.ext 4194293 [3,7,127] (.ext 5946358 [3,5] .low))) (.ext 2097147 [3,7] (.ext 3479717 [3,7,127] .low)))) (.br 655351 [] (.ext 1310703 [3,5,7] (.ext 2238397 [3,7] .low)) (.ext 1310703 [3,5] (.ext 1426402 [3,7] .low)))) (.br 524287 [] (.br 655351 [] (.br 1048573 [3] (.ext 2097147 [3,5,7] (.ext 4194293 [3,7] (.ext 4391331 [3] .low))) (.ext 2097147 [3,5,7] (.ext 2882418 [3,7] .low))) (.br 1048573 [3] (.ext 2097147 [3,5,7] (.ext 2389722 [7] .low)) (.ext 1859883 [3,7] .low))) (.br 655351 [] (.ext 1267067 [3] .low) (.ext 966387 [3] .low)))))) (.br 131071 [3,5,83] (.ext 262143 [3,11,137] (.br 499423 [3,5,11,31] (.br 524287 [3] (.br 1048573 [3,5,13,41] (.br 1310719 [3] (.ext 1742421 [7] .low) (.ext 1609864 [7] .low)) (.br 1310719 [3] (.ext 1495093 [7] .low) (.ext 1454182 [7] .low))) (.ext 884727 [3,41] .low)) (.br 524287 [3] (.br 1048573 [3,13,41] (.ext 1147501 [3] .low) (.ext 1126250 [3] .low)) (.ext 741677 [3] .low)))) (.ext 262143 [3,137] (.br 499423 [3,5,11,31] (.br 524287 [] .low .low) (.br 524287 [] .low .low)))))) (.br 20479 [3] (.jump 29709 (.ext 59417 [3,7] (.ext 118833 [3,83,149] (.br 131071 [3] (.br 249727 [3,5,173] (.ext 499455 [3,5,11,19] (.br 524287 [3] .low .low)) (.ext 434753 [3,5,11] .low)) (.ext 230498 [3,5,173] .low))))) (.br 39019 [3,5,7] (.ext 78039 [3,73] (.br 131071 [83] .low .low)) (.ext 78039 [3,23,149] (.br 81919 [3] (.br 131071 [3,83] .low .low) (.ext 115449 [3,83] .low)))))))) (.ext 3903 [3,19,23] (.br 5119 [3,7] (.br 5503 [5] (.br 8191 [37] (.jump 10438 (.br 16381 [3,5] (.jump 28769 (.br 31231 [] (.jump 364903 (.br 524287 [3,19] (.jump 1200327 (.ext 2400653 [3,7,233] (.br 2620927 [] (.ext 5241855 [3,5,7,19] (.ext 10483709 [3,7,47] (.br 16777183 [3,11,31] (.ext 24206505 [3,5] .low) (.ext 22237087 [3,5] .low)))) (.ext 5241855 [3,5,7] (.ext 10483709 [3,7,47] (.ext 12030169 [7,31] .low)))))) (.ext 1048575 [3,17,43,97] (.ext 2097149 [3,233] (.br 2620927 [7] (.ext 3037198 [5] .low) (.ext 2921208 [5] .low)))))) (.ext 62463 [7,31,181] (.ext 124925 [3] (.br 131071 [7,11] (.ext 262143 [3,5,7,11] (.br 499711 [3] (.ext 516188 [] .low) (.ext 512806 [] .low))) (.ext 262143 [3,5,7] (.ext 294877 [3] .low))))))) (.br 31231 [3] (.ext 62463 [3,7,31] (.ext 124925 [3,7] (.br 131071 [3] (.ext 195616 [5,7] .low) (.ext 142462 [] .low)))) (.ext 62463 [3,7,31] (.ext 122539 [3,7] .low))))) (.ext 16383 [3,5,29] (.br 31231 [3] (.ext 32435 [] .low) (.ext 32024 [] .low)))) (.br 8191 [37] (.br 16381 [3,29] (.br 20983 [3] (.ext 41967 [5,7,31,181] (.ext 43388 [] .low)) (.br 31231 [5] (.ext 49219 [3,7,31,181] .low) (.ext 43024 [3,7,31,181] .low))) (.br 20983 [3] (.ext 26373 [] .low) (.br 31231 [5] (.ext 32796 [3,7] .low) (.ext 32391 [] .low)))) (.ext 16258 [3,29] .low))) (.br 5503 [5] (.br 8191 [37] (.br 16381 [3,5] (.br 20479 [3,131] (.br 31231 [3] (.ext 62463 [7,181] (.ext 67383 [3] .low)) (.ext 53071 [7,181] .low)) (.br 31231 [3] (.ext 44270 [3,7,181] .low) (.ext 40086 [3,7,181] .low))) (.br 20479 [3,131] (.br 31231 [3] (.ext 40438 [3,7] .low) (.ext 36820 [3,7] .low)) (.ext 30697 [3] .low))) (.ext 15679 [3,5] .low)) (.br 8191 [3,37] (.br 13759 [3] .low (.br 16381 [3] (.ext 18737 [3] .low) (.ext 18087 [3] .low))) (.ext 10631 [3] .low))))))) (.br 79 [3] (.jump 234 (.ext 467 [3,7,13] (.br 631 [3,7] (.br 991 [3] (.ext 1983 [3,5,7,13] (.ext 3965 [3,23] (.ext 5017 [3] .low))) (.ext 1983 [3,5,13] (.ext 2722 [3,5,23] .low))) (.br 991 [3] (.ext 1983 [3,5,7] (.ext 2159 [23] .low)) (.ext 1584 [3,5] .low))))) (.br 127 [3,5] (.ext 255 [3,11,13] (.ext 509 [3,7,11] (.br 619 [7] (.ext 756 [3] .low) (.br 859 [3] .low (.ext 939 [] .low))))) (.ext 255 [3,13] (.ext 367 [3,7,11] .low)))))) (.br 61 [] (.br 79 [3] (.jump 91 (.br 127 [11] (.jump 316 (.br 487 [3] (.jump 900 (.ext 1799 [3,5,7] (.ext 3597 [3,5,7,23] (.ext 7193 [3,5,17,37] (.br 8191 [3] (.ext 9564 [] .low) .low))))) (.br 631 [3,7] (.jump 633 (.ext 1265 [3,5,13,19] (.br 1951 [3] (.ext 3903 [3,5,23,47] (.ext 7805 [3,7,17,37] (.br 8191 [3] (.ext 10104 [3] .low) .low))) (.br 2683 [3,23] (.ext 5367 [3,5,7,17] (.br 8191 [3] .low .low)) (.ext 5367 [3,5,7,17] (.ext 7336 [3,37] .low)))))) (.ext 1263 [3,5,19] (.br 1951 [3] (.ext 3639 [3,5,7,23] .low) (.br 2683 [3,7,23] .low (.ext 2992 [3,5] .low))))))) (.br 157 [] (.jump 215 (.br 313 [3] (.jump 682 (.ext 1363 [3,19] (.br 1951 [3] (.br 2503 [23] (.ext 5007 [3,5,47] (.br 8191 [3] (.br 15607 [3,7] (.br 16381 [] (.br 20023 [3] (.ext 33867 [3,7,181] .low) (.ext 26329 [3] .low)) (.br 20023 [3] (.ext 22971 [3] .low) (.ext 21897 [] .low))) (.br 16381 [] (.br 20023 [3] (.ext 22200 [] .low) (.ext 21423 [] .low)) (.ext 19893 [3] .low))) (.ext 11446 [3,7] .low))) (.ext 5007 [3,5,47] (.br 8191 [3] (.ext 8830 [] .low) .low))) (.br 2503 [23] (.br 2683 [] (.ext 5367 [3,5] (.br 8191 [] (.ext 9528 [] .low) .low)) (.ext 5367 [3,5] (.br 8191 [3,37] .low .low))) (.br 2683 [] (.ext 5367 [3,5] (.ext 6606 [] .low)) (.ext 5367 [3,5] (.ext 6134 [3] .low))))))) (.br 487 [3] (.ext 975 [3,7,19] (.ext 1949 [3,5] (.ext 2835 [3,5,23] .low))) (.ext 975 [3,7,19] (.ext 1440 [3,5] .low))))) (.ext 315 [3,5] (.br 487 [3] (.ext 624 [7] .low) (.ext 571 [7] .low)))))) (.br 109 [3] (.br 127 [11] (.jump 151 (.ext 301 [3,7,11] (.br 487 [3] (.ext 975 [3,7,13] (.ext 1475 [3,5] .low)) (.ext 975 [3,7,13] (.ext 981 [3] .low))))) (.ext 255 [3,7] (.ext 287 [3] .low))) (.br 127 [11] (.ext 255 [3,5,11] (.br 439 [3,11] .low (.br 487 [] (.ext 539 [3,7] .low) (.ext 525 [3,7] .low)))) (.ext 255 [3,5] (.ext 260 [3] .low))))) (.br 79 [3] (.br 127 [3] (.br 157 [] (.br 313 [3,5,11,13] (.ext 627 [3,5,7] (.ext 852 [3,19] .low)) (.ext 627 [3,7] (.ext 636 [3] .low))) (.ext 315 [3,5,11,13] (.ext 423 [3] .low))) (.br 157 [] (.ext 285 [3,5,13] .low) (.ext 225 [5] .low))) (.br 109 [3] (.br 127 [3] (.ext 255 [7,11,13] (.ext 269 [3] .low)) .low) (.br 127 [3] (.ext 254 [3,5,11,13] .low) (.ext 153 [] .low)))))) (.br 43 [3] (.br 79 [3] (.br 127 [5] (.br 157 [] (.ext 268 [3,11] .low) (.ext 203 [3] .low)) .low) (.br 127 [5] .low .low)) (.br 79 [3] (.br 127 [3] .low .low) (.ext 101 [3] .low))))))

def certOut11 : ProofTree :=
  (.br 19 [3] (.br 23 [] (.br 31 [] (.br 37 [] (.jump 158 (.ext 315 [3,5,13] (.br 367 [] (.br 733 [3,7] (.br 991 [] (.ext 1983 [3,5,7] (.ext 3965 [3,23] (.br 7927 [3,5,11] (.ext 7977 [] .low) (.ext 7960 [] .low)))) (.ext 1983 [3,5,7] (.br 2293 [3,23] .low (.ext 3405 [3] .low)))) (.br 991 [] (.ext 1983 [3,7] (.ext 2835 [3,23] .low)) (.ext 1920 [3,7] .low))) (.ext 735 [3,7] (.br 991 [3] (.ext 1045 [3] .low) (.ext 1027 [3] .low)))))) (.br 61 [3] (.ext 123 [3,7,11] (.br 127 [] (.br 151 [] (.jump 435 (.br 487 [] (.jump 4036 (.br 4831 [3,17] (.jump 24520 (.ext 49039 [3,5,7,11] (.br 94207 [3,5,7] (.br 131071 [3,7] (.br 154591 [] (.ext 309183 [3,5,11,23,29,41] (.br 524287 [3,11] (.ext 816104 [3,5] .low) (.ext 622354 [3] .low))) (.ext 309183 [3,5,11,23,29] (.br 524287 [3,11] (.ext 534131 [] .low) .low))) (.br 154591 [] (.ext 309183 [3,5,23,29,41] (.ext 497825 [3,11] .low)) (.ext 309183 [3,5,23,29] (.ext 354948 [3] .low)))) (.br 131071 [3,7] (.br 154591 [] (.ext 309183 [3,5,11,23,41,71] (.br 524287 [3,7,11] .low .low)) (.ext 309183 [3,5,11,23,71] (.ext 391788 [3,7] .low))) (.br 154591 [] (.ext 296794 [3,5,23,71] .low) (.ext 241303 [3,5,71] .low)))))) (.br 8191 [3,7] (.br 15583 [3,7,29] (.jump 16258 (.br 16381 [] (.jump 2149383 (.br 2991103 [3,5] (.jump 7637965 (.ext 15275929 [3,5,7,47] (.br 18824263 [3] (.br 23928823 [] (.jump 27768996 (.br 33548287 [] (.jump 161196614 (.ext 322393227 [3,5,401] (.ext 644786453 [3,5,233] (.ext 1289572905 [3,5,1483] (.ext 1382219224 [] .low))))) (.ext 67096575 [5,31] (.ext 134193149 [3] (.ext 175702530 [7,11,1381] .low))))) (.br 33548287 [] (.ext 67096575 [3,5,31,397] (.ext 130063114 [3,5] .low)) (.ext 67096575 [3,5,31] (.ext 79010545 [3] .low)))) (.br 19788247 [] (.br 23928823 [] (.jump 25907228 (.ext 51814455 [5,11,31,139] (.ext 103628909 [3] (.ext 163325266 [5,7] .low)))) (.ext 47857647 [11,31,139] (.ext 76406732 [3] .low))) (.br 23928823 [11] (.br 33548287 [139] (.ext 67096575 [3,5,31,397] (.ext 134193149 [3,5,7] (.ext 139218146 [7] .low))) (.ext 67096575 [3,5,31] (.br 79152991 [3,5] .low (.ext 91667899 [7] .low)))) (.br 33548287 [139] (.ext 67096575 [3,31,397] (.ext 80600979 [3,5,7] .low)) (.ext 61985636 [3,31] .low))))))) (.ext 5982207 [3,5,7,23,31,97,113,1249] (.ext 11964413 [3,5,7,47,59,103,157] (.br 18824263 [3,5,7,113] .low (.br 19788247 [3] .low (.ext 21580238 [11] .low))))))) (.ext 32763 [3,5,7,11] (.ext 65525 [3,5,7,181] (.br 94207 [3,7,13] (.br 131071 [3,7] (.br 262111 [3,5,29] (.ext 357071 [3,11,17] .low) (.ext 336739 [3,11,17] .low)) (.ext 231132 [3,5,29] .low)) (.br 131071 [3,7] (.ext 258924 [3,5,7,71] .low) (.ext 185597 [3,5] .low))))))) (.br 16381 [5] (.ext 32763 [3,7,11,181] (.ext 65525 [3,5,7,11,181] (.br 94207 [3,13] (.br 131071 [3,7] (.br 147073 [] (.ext 294147 [3,5,11,29] (.ext 312866 [] .low)) (.ext 294147 [3,5,11,23,29] (.ext 309582 [3,17] .low))) (.br 147073 [] (.ext 180362 [] .low) (.ext 215558 [3,5,29] .low))) (.br 131071 [3,7] (.br 147073 [] (.ext 213154 [3,71] .low) (.ext 239537 [3,5,7,71] .low)) (.br 147073 [] .low (.ext 175420 [3,5] .low)))))) (.ext 32763 [3,7,11] (.ext 65525 [3,5,7,11,181] (.br 94207 [3,7,13] (.ext 108208 [] .low) (.ext 105084 [] .low)))))) (.br 15583 [3,7,29] (.ext 31167 [3,5,7,11] (.ext 52264 [3,5,7] .low)) (.ext 31167 [3,5,7,11] (.ext 36826 [3,7] .low)))))) (.ext 975 [3,7] (.br 1471 [3,5,17] (.br 1951 [] (.ext 3903 [3,17,23,47] (.br 4831 [3,17] (.br 8191 [3] (.br 9661 [] (.ext 14342 [7] .low) (.ext 12793 [7] .low)) (.ext 9057 [] .low)) (.br 8191 [3] (.ext 9612 [] .low) .low))) (.ext 3903 [3,17,23] (.br 4831 [3,17] (.br 8191 [3,37] .low .low) (.ext 7074 [3] .low)))) (.br 1951 [] (.ext 3903 [3,23,47] (.br 4831 [3,17] (.ext 6786 [3,7] .low) (.ext 6163 [3,7] .low))) (.ext 3903 [3,23] (.ext 4419 [3,17] .low))))))) (.ext 303 [3,11] (.br 367 [3] (.br 487 [] (.br 607 [3,7] (.br 733 [] (.jump 895 (.br 1213 [3,5,7] (.jump 3403 (.ext 6805 [3,5,11,17] (.br 8191 [3] (.br 15583 [3,31] (.br 16381 [5] (.jump 21469 (.ext 42937 [3,5,7,181] (.ext 85873 [3,7] (.br 131071 [3,7,17] (.ext 262143 [3,5,11,19,139] (.br 308101 [3] (.ext 322209 [] .low) (.ext 383142 [3,5] .low))) (.ext 256744 [3,19,139] .low))))) (.ext 32763 [3,5] (.ext 65525 [3,5,7] (.ext 129693 [3,7,17] .low)))) (.br 16381 [5] (.ext 32763 [3,5,181] (.ext 65525 [3,5,7] (.ext 124640 [3,7,17] .low))) (.ext 32763 [3,5] (.ext 65525 [3,5,7] (.ext 70784 [3,7] .low))))) (.br 15583 [3,31] (.ext 31167 [3,5] (.ext 40165 [3,5,7] .low)) (.ext 30378 [3,5] .low))))) (.ext 2427 [3,5,23] (.ext 4853 [3,5,17] (.br 8191 [3,5,11] (.ext 9488 [] .low) .low))))) (.br 1213 [3,5,7] (.ext 2427 [3,5,23] (.ext 4853 [3,5,17] (.ext 6845 [3] .low))) (.ext 2427 [3,23] (.ext 4015 [3,5] .low)))) (.br 733 [] (.ext 1467 [3,5,7] (.ext 2933 [3,11,23] (.ext 3516 [] .low))) (.ext 1467 [3,5,7] (.ext 2199 [3,23] .low)))) (.br 607 [3,7] (.br 733 [] (.br 1213 [3,5] (.br 1951 [5] (.ext 3903 [3,5,23,47] (.ext 5951 [3,11,17] .low)) (.ext 3903 [3,5,23] (.ext 4309 [3,17] .low))) (.br 1951 [5] (.ext 3624 [3,23] .low) (.ext 2985 [3,23] .low))) (.br 1213 [3,5] (.br 1951 [3] (.ext 2734 [3,5,23] .low) (.ext 2485 [3,5,23] .low)) (.br 1951 [3] (.ext 1988 [] .low) (.ext 1979 [] .low)))) (.br 733 [] (.ext 1467 [3,5] (.ext 1849 [] .low)) (.ext 1406 [3,5] .low)))) (.br 487 [] (.br 607 [3,7] (.br 1213 [3,5,7] (.br 1471 [] (.ext 2346 [3,23] .low) (.ext 1958 [3] .low)) (.br 1471 [] (.ext 1789 [] .low) (.ext 1698 [] .low))) (.ext 1215 [3,5,7] (.ext 1258 [3] .low))) (.br 607 [3,7] (.ext 1173 [3,5] .low) (.ext 952 [3] .low)))))) (.br 151 [] (.ext 303 [3,7] (.br 367 [] (.br 487 [] (.br 733 [3,7] (.ext 1467 [3,5,7,17] (.ext 1706 [] .low)) (.ext 1230 [3,7,17] .low)) (.br 733 [3,7] (.ext 952 [] .low) (.ext 866 [] .low))) (.br 487 [] (.ext 722 [3,7] .low) (.ext 622 [3,7] .low)))) (.ext 303 [3] (.br 367 [3] (.ext 371 [] .low) (.ext 370 [] .low)))))) (.ext 123 [3,7] (.br 127 [3] (.br 151 [] (.ext 303 [3,7,11,13] (.br 367 [] (.ext 476 [] .low) (.ext 443 [] .low))) (.ext 303 [3,11,13] (.ext 325 [3] .low))) (.br 151 [] (.ext 208 [3] .low) (.ext 185 [3] .low)))))) (.br 37 [] (.br 73 [3] (.br 127 [7] (.ext 255 [3,5,11] (.br 367 [3] (.ext 374 [] .low) (.ext 372 [] .low))) (.ext 167 [5] .low)) (.br 127 [7] (.ext 184 [3] .low) .low)) (.ext 75 [3] (.ext 122 [3,7] .low)))) (.br 31 [] (.br 37 [] (.br 47 [] (.br 61 [] (.jump 86 (.br 127 [3,11] (.jump 268 (.br 487 [3,5] (.jump 593 (.br 751 [] (.jump 2811 (.ext 5621 [3,5,17] (.br 6007 [] (.br 8191 [3] (.jump 14883 (.br 15583 [] (.jump 331004 (.br 444517 [3] (.jump 1296208 (.br 1994623 [3] (.jump 3701876 (.ext 7403751 [3,5,7] (.ext 14807501 [3,5,47,241] (.ext 29615001 [3,7,113,1531] (.ext 29820645 [] .low))))) (.ext 3989247 [3,5,7,71,1249] (.ext 7978493 [3,5,7] (.ext 10394764 [3,5,47] .low))))) (.br 524287 [3,5] (.jump 897859 (.br 1048447 [3,17] (.jump 6251188 (.ext 12502375 [3,5,7,47] (.br 16777183 [3,7,113] (.br 24412447 [3,5,7] (.ext 48824895 [3,5,13,29,31,139] (.br 77585077 [3,317] (.ext 155170155 [3,5,7,19,61] (.ext 179170172 [] .low)) (.ext 155170155 [3,5,7,19,61] (.ext 173794060 [3] .low)))) (.ext 48824895 [3,5,29,31,59,139,211] (.br 49209343 [3] (.br 77585077 [3,5,31,317] (.ext 152664244 [3,5,7,19] .low) (.ext 153490506 [3,5,7,17,19,61] .low)) (.br 77585077 [3,5,31,317] (.br 97649791 [] .low (.ext 110005068 [3] .low)) (.br 97649791 [61] (.ext 102536864 [] .low) (.ext 121824844 [3,41] .low)))))) (.br 24412447 [3,5,7] (.ext 48824895 [3,13,29,31,73,139] (.br 77585077 [3,5,317] .low (.ext 85364929 [3,61] .low))) (.ext 48824895 [3,29,31,59,73,139,211] (.br 49209343 [3] (.br 77585077 [3,5,31,317] .low (.ext 85132360 [3,61] .low)) (.ext 75898047 [3,5,31,317] .low))))))) (.br 1048573 [] (.jump 6246712 (.ext 12493423 [3,5,7,47] (.br 24412447 [3,5,7,113,1531] (.ext 48824895 [3,5,13,31,139] (.ext 85281492 [3,11,29,61,317] .low)) (.ext 48824895 [3,5,31,59,139,211,887] (.br 49209343 [3] (.ext 85049376 [3,5,11,29,31,41,61,317] .low) (.ext 75843069 [3,5,11,31,317] .low)))))) (.br 1778071 [3,5,11] (.jump 1813718 (.br 1994623 [] (.jump 19997613 (.ext 39995225 [3,31,887] (.br 56898271 [] (.ext 113796543 [3,5,11,47] (.ext 227593085 [3,5,7,109] (.br 255311743 [] (.ext 351889309 [3,7] .low) (.ext 327139680 [3,7] .low)))) (.ext 113796543 [3,5,11] (.ext 207713617 [3,5,7,109] .low))))) (.ext 3989247 [3,7,53,71,1249] (.ext 7978493 [3,5,7] (.ext 15956985 [3,5,7,47] (.br 16777183 [3,113,1531] (.ext 18592483 [3] .low) (.ext 18198662 [3] .low))))))) (.br 1994623 [] (.ext 3989247 [3,5,7,11,71] (.ext 7978493 [3,5,7] (.ext 15956985 [3,5,7,47] (.br 16777183 [3,113,1531] (.ext 20352474 [3,5] .low) (.ext 19654401 [3,5] .low))))) (.ext 3989247 [3,5,7,11,71,1249] (.ext 7978493 [3,5,7,43] (.ext 10792357 [3,5,7,47] .low)))))))) (.br 1048447 [3,5,11,13,17] (.br 1778071 [3,5,11] (.br 1994623 [] (.br 2096893 [3] (.ext 4193787 [5,7,53] (.ext 8387573 [3] (.ext 15243714 [7,47] .low))) (.ext 4193787 [5,7,53] (.ext 7986404 [3] .low))) (.br 2096893 [3] (.ext 4193787 [3,5,7,53,1249] (.ext 7796099 [3] .low)) (.ext 4193787 [3,5,7,53,1249] (.ext 5322511 [3] .low)))) (.br 1994623 [] (.br 2096893 [3] (.ext 4193787 [3,5,7,11] (.ext 8387573 [3,7] (.ext 9197825 [47] .low))) (.ext 4193787 [3,5,7,11] (.ext 6393415 [3,7] .low))) (.br 2096893 [3] (.ext 4193787 [3,5,7,11,1249] (.ext 6295004 [3,7,43] .low)) (.ext 4193787 [3,5,7,11,1249] (.ext 4841543 [3,43] .low))))) (.br 1778071 [3,5,11] (.br 1994623 [] (.ext 3989247 [3,5,7,53,71] (.ext 4091039 [] .low)) (.ext 3167173 [3,7,71] .low)) (.br 1994623 [] (.ext 3967167 [3,5,7,11,71] .low) (.ext 3312083 [3,5,7,11,71] .low))))))) (.br 16381 [5] (.jump 162679 (.ext 325357 [3,5,19,23,47] (.br 444517 [3] (.br 524287 [3,11,19] (.br 1048573 [3,5,17,673] (.ext 2097147 [3,5,37,233] (.ext 4194293 [3,5,7,113] (.ext 8388585 [3,7] (.ext 9665973 [47] .low)))) (.ext 2097147 [3,37,233] (.ext 4194293 [3,5,7,113] (.ext 5029591 [3,5] .low)))) (.ext 1048575 [3,5,17,673] (.ext 2053608 [3,37] .low))) (.br 524287 [3,11,19] (.br 1048573 [3,5,13,17,29] (.br 1778071 [3,5,11,31] (.ext 3556143 [3,5,7,37,53,233] (.ext 3674067 [] .low)) (.ext 3556143 [3,5,7,11,31,37,233] (.ext 3653873 [3] .low))) (.br 1778071 [3,5,11,31] (.ext 2569828 [3,7,37,233] .low) (.ext 2831616 [3,7,11,31,37,233] .low))) (.ext 1048575 [3,5,13,17,29] (.ext 1627283 [3,5,11,31] .low)))))) (.ext 32763 [3,19] (.br 36037 [3,7] (.br 72073 [3,5,7] (.br 131071 [3] (.br 262111 [5,19] (.br 524221 [3,11] (.br 524287 [3] (.br 1048573 [5,7,13,17] (.ext 1190590 [3] .low) (.ext 1164308 [3] .low)) (.ext 776224 [5,7] .low)) (.br 524287 [3] (.ext 970235 [5,7] .low) (.ext 708141 [7] .low))) (.ext 524223 [3,11] (.br 524287 [3] (.ext 708118 [7] .low) (.ext 557518 [] .low)))) (.br 262111 [5,19] (.br 524221 [3] (.br 524287 [] .low .low) (.br 524287 [] .low .low)) (.ext 445968 [3] .low))) (.br 131071 [3] (.br 262111 [3,5,19] (.ext 483283 [3,5,11] .low) (.ext 413500 [3,5,11] .low)) (.ext 251468 [3,19] .low))) (.br 37591 [] (.br 75181 [3,5,7] (.br 131071 [3] (.br 262111 [19,23,53] (.br 524221 [3,11] (.br 524287 [3] (.ext 974149 [5,7] .low) (.ext 665170 [7] .low)) (.br 524287 [3] (.ext 831430 [5,7] .low) (.ext 631226 [7] .low))) (.ext 524223 [3,11] (.br 524287 [3] (.ext 631208 [7] .low) .low))) (.br 262111 [19,23,53] (.ext 498801 [3] .low) (.ext 406934 [3] .low))) (.br 131071 [3] (.br 262111 [3,19,23] (.ext 451963 [3,7,11] .low) (.ext 394775 [3,7,11] .low)) (.ext 242716 [3,19] .low))) (.ext 75183 [3,5,7] (.br 131071 [3,5,7] (.ext 225718 [3,7,19] .low) (.ext 167892 [3,7] .low))))))))) (.br 9397 [] (.jump 12069 (.br 15583 [] (.jump 53511 (.ext 107021 [3,5] (.br 131071 [7] (.ext 262143 [3,11,19] (.ext 524285 [3,5,13] (.br 524287 [] (.br 1048573 [3,5,13] (.ext 1104728 [3] .low) (.ext 1093021 [3] .low)) (.ext 723569 [3] .low)))) (.ext 262143 [3,19] (.ext 524285 [3,5,13] (.br 524287 [] .low .low)))))) (.br 18793 [3] (.jump 33729 (.ext 67457 [3,5] (.br 131071 [3] (.br 150343 [] (.ext 300687 [3,5,11,19,23] (.br 524287 [3] (.ext 692598 [3] .low) .low)) (.ext 300687 [3,11,19,23] (.br 524287 [3] .low .low))) (.br 150343 [] (.ext 300687 [3,5,19,23] (.ext 390440 [3] .low)) (.ext 272496 [3,19,23] .low))))) (.ext 37587 [3,7] (.ext 75173 [3,5] (.ext 114636 [3,5] .low)))))) (.br 15583 [3,41] (.ext 31167 [3,5,19] (.br 37591 [3,7] (.br 75181 [3,5] (.ext 96673 [3] .low) (.ext 88263 [] .low)) (.ext 75183 [3,5,7] (.ext 84584 [3,5] .low)))) (.ext 31167 [3,5,19] (.br 36037 [3,7] (.ext 38740 [] .low) (.br 37591 [] (.ext 37898 [] .low) (.ext 50394 [3,5] .low))))))) (.br 8191 [3] (.br 9397 [] (.br 15583 [3] (.jump 15856 (.br 16381 [] (.jump 494082 (.br 524287 [5,19] (.jump 8576036 (.br 16777183 [3,1307] (.jump 17544096 (.br 33548287 [3,5,11,89,139] (.jump 36776264 (.ext 73552527 [3,5,397] (.ext 147105053 [3,5,7,19,31,79] (.ext 294210105 [3,5,313,569] (.ext 394809162 [5,19] .low))))) (.ext 67096575 [3,5,31] (.ext 134193149 [3,5,7,31,79,2731] (.ext 181368146 [3,7,19,1381] .low))))) (.br 33548287 [3,5,11,89,139] (.ext 67096575 [3,5,31,397] (.ext 117739238 [3,5,7,31,79] .low)) (.ext 67096575 [3,5,31] (.ext 87152628 [3,5,31] .low))))) (.ext 1048575 [3] (.br 1994623 [3,5,7] (.ext 3989247 [3,5,7,233] (.br 4811263 [3] (.ext 5429606 [] .low) (.ext 5260584 [] .low))) (.ext 3956300 [3,7,233] .low))))) (.br 18793 [3] (.jump 101435 (.br 131071 [3,7] (.jump 448608 (.br 524287 [3,5] (.jump 3107860 (.br 4194271 [3,7] (.jump 11998401 (.br 16777183 [3,541,1531] (.jump 42123572 (.br 49211527 [3] (.jump 292463072 (.ext 584926143 [3,5,7,233] (.ext 1169852285 [3,13,16699] (.br 2147483647 [3,5,17,31,61] (.ext 4294967295 [3,5,47,9241] (.ext 5417374644 [3] .low)) (.ext 4094619145 [3,5,47] .low))))) (.ext 98423055 [3,11,79] (.ext 196846109 [3,5,7,19,181,229] (.ext 393692217 [3,5,7] (.ext 548523323 [3,5,7,19,233] .low)))))) (.br 33554167 [3,5,89,139] (.br 49211527 [3,31,257] (.ext 98423055 [3,5,17,73] (.ext 196846109 [3,5,7] (.ext 318890982 [3,5,7] .low))) (.ext 98423055 [3,5,11,17,79] (.ext 196846109 [3,5,7,181] (.ext 232202091 [3,7] .low)))) (.br 49211527 [3,31,257] (.ext 98423055 [3,5,73] (.ext 163502254 [3,5,7,229] .low)) (.ext 98423055 [3,5,11,79] (.ext 147272371 [3,5,7,181,229] .low)))))) (.br 6152191 [3,5] (.jump 6280572 (.ext 12561143 [3,5,19,47] (.br 16777183 [3,71,1531] (.ext 33554367 [3,5,139] (.br 49217527 [31,257] (.br 67108351 [3,11] (.br 98435053 [3] (.ext 196870107 [3,5,7,19,31] (.ext 229115120 [] .low)) (.ext 191894382 [3,5,7,19,31] .low)) (.br 98435053 [3] (.ext 175077049 [3,5,7,19] .low) (.ext 154967333 [3,5,7,19] .low))) (.br 67108351 [3,11] (.ext 134216703 [3,5,31] (.ext 144835938 [7,19] .low)) (.ext 122757578 [3] .low)))) (.ext 33554367 [3,139] (.br 49217527 [3,31,257] (.br 67108351 [3,11] (.ext 92038742 [3,5] .low) (.ext 85673308 [3,5] .low)) (.br 67108351 [3,11] (.ext 78397032 [3,5] .low) (.ext 76259037 [3,5] .low))))))) (.ext 12304383 [3,5,47,541] (.br 16777183 [3,71,1531] (.ext 33554367 [3,5,89,139] (.ext 46101124 [31,257] .low)) (.ext 33554367 [3,5,89,139] (.ext 37511476 [3,31] .low))))))) (.br 1048447 [3,5] (.br 1994623 [3,7,13] (.br 2096893 [] (.jump 3366092 (.br 4194271 [5] (.jump 17047392 (.br 33554167 [3,5,89] (.jump 34653107 (.ext 69306213 [3,5,17,257] (.ext 138612425 [3,7,181] (.br 255311743 [3,5] (.ext 417512081 [3,5,13,19] .low) (.ext 370443324 [3,5,13] .low))))) (.ext 67108335 [3,5,31,257] (.ext 134216669 [3,7,181] (.ext 176064894 [5,7,229] .low))))) (.br 6152191 [3] (.jump 7432915 (.ext 14865829 [3,5,19,47] (.ext 29731657 [3,7,71] (.br 49217527 [3,31,257] (.br 67108351 [5] (.ext 96408028 [3] .low) (.ext 86920591 [3] .low)) (.br 67108351 [5] (.ext 77766990 [3] .low) (.ext 75372740 [3] .low)))))) (.ext 12304383 [3,5,47] (.ext 24608765 [3,7,71] (.ext 33873312 [3,5,31,89] .low)))))) (.ext 4193787 [3,5,7,97] (.br 4194271 [3] (.br 6152191 [3] (.ext 12304383 [3,5,7,19,47] (.ext 24608765 [3,7] (.ext 26943323 [] .low))) (.ext 12304383 [3,5,7,47] (.ext 18737358 [3,7] .low))) (.br 6152191 [3] (.ext 12304383 [3,5,19,47] (.ext 16405010 [7] .low)) (.ext 12304383 [3,5,47] (.ext 12951462 [3] .low)))))) (.br 2096893 [] (.ext 4193787 [3,5,7,97] (.br 4194271 [] (.br 6152191 [3] (.ext 12304383 [3,5,7,19,47] (.ext 24608765 [3,7] (.ext 25277977 [] .low))) (.ext 12304383 [3,5,7,47] (.ext 17916492 [3,7] .low))) (.br 6152191 [3] (.ext 12304383 [3,5,19,47] (.ext 15772331 [] .low)) (.ext 12304383 [3,5,47] (.ext 12553897 [3] .low))))) (.ext 4193787 [3,7,97] (.br 4194271 [3] (.br 6152191 [3] (.ext 11268344 [5,7,47] .low) (.ext 9661454 [5,7,47] .low)) (.br 6152191 [3] (.ext 8435492 [3,5,47] .low) (.ext 7852614 [] .low)))))) (.br 1994623 [3,7,13] (.ext 3989247 [3,5,7,97] (.br 4194271 [7] (.br 6152191 [3] (.ext 6493672 [] .low) (.ext 6404797 [] .low)) (.ext 5794063 [3] .low))) (.ext 3989247 [3,7,97] (.br 4194271 [3,7] (.ext 4570354 [3] .low) (.ext 4489837 [3] .low))))))) (.br 150343 [] (.jump 311808 (.br 524287 [3,5,29] (.jump 769377 (.br 1048447 [3] (.jump 2890487 (.ext 5780973 [3,5] (.br 6152191 [] (.ext 12304383 [3,5,19,47] (.br 16777183 [3] (.ext 33554367 [3,5,7,29,139] (.br 49217527 [3,31] (.ext 98382514 [3,5] .low) (.ext 82000018 [3,5] .low))) (.ext 33554367 [3,7,29,139] (.br 49217527 [3,31] (.ext 56769789 [] .low) (.ext 55079439 [] .low))))) (.ext 12304383 [3,5,47] (.br 16777183 [3] (.ext 33554367 [3,5,7,29,89,139] (.ext 35150016 [31] .low)) (.ext 29061349 [3,5,7,89] .low)))))) (.br 1048573 [] (.jump 2889530 (.ext 5779059 [3,5,7] (.br 6152191 [] (.ext 12304383 [3,5,7,19,47] (.ext 24608765 [3,7,1531] (.br 49217527 [3,5,31,139] (.ext 56723656 [] .low) (.ext 55044691 [] .low)))) (.ext 12304383 [3,5,7,47,541] (.ext 24608765 [3,5,7,1531] (.ext 29051672 [89] .low)))))) (.br 1202743 [3] (.jump 2135287 (.ext 4270573 [3,5,7] (.br 6152191 [3] (.br 9621943 [3,5,47] (.br 16777183 [3,19,1531] (.ext 33554367 [3,5,139] (.br 49217527 [3,31] (.ext 80204614 [3,11,211] .low) (.ext 71234805 [3,11] .low))) (.ext 33554367 [3,5,139] (.br 49217527 [3,31] (.ext 50204066 [] .low) (.ext 50003607 [] .low)))) (.br 16777183 [3,19,1531] (.ext 33554367 [3,5,139] (.ext 40931617 [5,31] .low)) (.ext 32903972 [3,139] .low))) (.br 9621943 [3,5,47] (.br 16777183 [3,541,1531] (.ext 32878547 [3,5,89,139] .low) (.ext 27583979 [3,5,89] .low)) (.br 16777183 [3,541,1531] (.ext 23038233 [3] .low) (.ext 21438140 [3] .low)))))) (.br 1994623 [7] (.ext 3989247 [3,5,7] (.br 6152191 [3,5,7] (.ext 12304383 [3,19,47] (.ext 15772886 [] .low)) (.ext 12304383 [3,47,541] (.ext 12554249 [3] .low)))) (.ext 3989247 [3,7] (.br 6152191 [3,5,7] (.ext 8223656 [5] .low) (.ext 7704809 [] .low)))))))) (.br 1048447 [3] (.br 1202743 [3] (.br 1994623 [7] (.br 2096893 [] (.jump 2254097 (.ext 4508193 [3,5] (.br 6152191 [3] (.br 9621943 [3,47] (.ext 19243887 [3,5,7,19] (.ext 38487773 [3,31] (.ext 45635757 [] .low))) (.ext 19243887 [3,7,19] (.ext 28650192 [3] .low))) (.br 9621943 [3,47] (.ext 19243887 [3,5,7] (.ext 23679510 [] .low)) (.ext 18108809 [3,7] .low))))) (.ext 4193787 [3,5,7] (.br 6152191 [3] (.br 9621943 [3,5,47] (.ext 10370104 [] .low) (.ext 10108116 [] .low)) (.ext 8708243 [3,5,47] .low)))) (.br 2096893 [] (.ext 4193787 [3,5,7] (.br 6152191 [3] (.br 9621943 [3,5,47] (.ext 9751911 [] .low) (.ext 9708200 [] .low)) (.ext 8482469 [3,5,47] .low))) (.ext 4193787 [3,5,7] (.ext 5633733 [3] .low)))) (.br 1994623 [7] (.br 2096893 [] (.ext 4193787 [3,5,7] (.br 6152191 [3,5] (.ext 6328320 [] .low) (.ext 6283349 [] .low))) (.ext 4193787 [3,5,7] (.ext 4571162 [3] .low))) (.br 2096893 [] (.ext 4193787 [3,5,7] (.ext 4508175 [3] .low)) (.ext 3553266 [3,7] .low)))) (.br 1202743 [3] (.br 1994623 [7] (.ext 3989247 [3,5,7] (.ext 4272452 [3,7] .low)) (.ext 3370112 [3,5,7] .low)) (.br 1994623 [7] (.ext 2724121 [3,7] .low) (.ext 2495912 [3,7] .low)))))) (.br 262111 [3] (.br 524221 [3,5,29] (.br 524287 [] (.br 1048573 [3,5,17] (.br 1994623 [3,7] (.ext 3989247 [3,5,7,97] (.br 6152191 [3,41] (.ext 12304383 [3,5,7,19,47] (.ext 16420447 [7] .low)) (.ext 12304383 [3,5,7,47] (.ext 12961082 [3] .low)))) (.ext 3989247 [3,5,7,97] (.br 6152191 [3,41] (.ext 8440592 [3,5,7,47] .low) (.ext 7856149 [] .low)))) (.br 1994623 [3,7] (.ext 3989247 [3,5,7,97] (.ext 5796372 [3,5,41] .low)) (.ext 3989247 [3,7,97] (.ext 4491224 [3,5,41] .low)))) (.ext 1048575 [3,5,17] (.ext 1935212 [3,7] .low))) (.br 524287 [] (.br 1048573 [3,5] (.br 1994623 [3,7] (.ext 3673461 [3,5,7,13,97] .low) (.ext 3144181 [3,5,7,13,97] .low)) (.br 1994623 [3,7] (.ext 2554720 [3,7,13,97] .low) (.ext 2418874 [3,7,13,97] .low))) (.ext 1048575 [3,5] (.ext 1324174 [3] .low)))) (.ext 524223 [3,5,29] (.br 524287 [3] (.br 1048447 [3,5] (.br 1048573 [] (.ext 1451243 [3] .low) (.ext 1324122 [3] .low)) (.br 1048573 [] (.ext 1324072 [3] .low) (.ext 1257969 [3] .low))) (.ext 811633 [3,5] .low))))))) (.ext 37587 [3,5,7] (.ext 75173 [3,7] (.br 131071 [3,5,7,97] (.ext 199104 [3] .low) (.ext 144303 [] .low))))))) (.br 16381 [] (.br 18793 [3] (.jump 77015 (.br 131071 [3,7,97] (.jump 186739 (.ext 373477 [3,11,23] (.br 524287 [3,19,29] (.br 1048573 [3,5,13,43] (.ext 2097147 [3,5,7,233] (.br 4194271 [3,5,7,97] (.ext 4961917 [3] .low) (.ext 4815040 [3] .low))) (.ext 2097147 [3,7,233] (.ext 3482432 [3,5,7,97] .low))) (.ext 1048575 [3,5,13,43] (.ext 1868036 [3,7] .low))))) (.br 150343 [] (.jump 157901 (.ext 315801 [3,5,23] (.br 524287 [3,19,29] (.br 1048573 [3,5,43] (.br 1202743 [3] (.ext 2405487 [3,5,7,233] (.ext 3789677 [3,5] .low)) (.ext 2405487 [3,5,7,233] (.ext 2881695 [3] .low))) (.br 1202743 [3] (.ext 2405487 [3,5,7,233] (.ext 2783636 [] .low)) (.ext 2260472 [3,7,233] .low))) (.ext 1048575 [3,5,43] (.br 1202743 [3] (.ext 1285254 [] .low) (.ext 1263583 [] .low)))))) (.ext 300687 [3,23] (.br 524287 [3,19,29] (.ext 872607 [3,5,43] .low) (.ext 616208 [5] .low)))))) (.ext 37587 [3,7,181] (.ext 75173 [3,5] (.br 131071 [3,5,7,97] (.ext 184732 [3] .low) (.ext 136601 [] .low))))) (.br 18793 [3] (.ext 37587 [3,5,7] (.ext 75173 [3,5,7] (.br 131071 [3,97] (.br 150343 [] (.ext 158572 [] .low) (.ext 156432 [] .low)) .low))) (.ext 37587 [3,7] (.ext 75173 [3,5,7] (.ext 82713 [5] .low)))))) (.br 15583 [3] (.br 16381 [5] (.ext 32763 [3,5,7,19,181] (.br 37591 [7] (.br 75181 [3] (.br 131071 [7,97] (.ext 175270 [53] .low) .low) (.br 131071 [7,97] (.ext 135720 [] .low) .low)) (.ext 75183 [3,7] (.ext 128342 [3,5,7,97] .low)))) (.ext 32763 [3,5,7,19] (.br 37591 [3,7] (.ext 69965 [3,7] .low) (.ext 71963 [3,7] .low)))) (.br 16381 [5] (.ext 32763 [3,7,19,181] (.br 36037 [7] (.ext 69293 [3,7] .low) (.br 37591 [] (.ext 67505 [3,5] .low) (.ext 70380 [3,5,7] .low)))) (.ext 32763 [3,7,19] (.br 36037 [3,7] (.ext 40642 [] .low) (.br 37591 [] (.ext 40020 [] .low) (.ext 49230 [3] .low))))))) (.br 9397 [] (.br 15583 [3] (.br 18793 [3] (.ext 37587 [5,7] (.ext 59161 [3] .low)) (.ext 37587 [5,7] (.ext 38803 [3] .low))) (.br 18793 [3] (.ext 35595 [3,7] .low) (.ext 27423 [7] .low))) (.br 15583 [3] (.ext 30478 [3,5,7,19] .low) (.ext 24600 [3,5,7,19] .low))))))) (.ext 1503 [3,5,7] (.ext 3005 [3,23] (.ext 6009 [3,5,17,31] (.ext 6678 [3] .low)))))) (.br 751 [3,7] (.ext 1503 [3,5,7,19] (.br 1951 [] (.ext 3903 [3,23,47] (.ext 5690 [3,5,17] .low)) (.ext 3903 [3,23] (.ext 4170 [3,17] .low)))) (.ext 1503 [3,5,7] (.br 1951 [3] (.ext 2698 [3,23] .low) (.ext 2463 [3,23] .low)))))) (.ext 255 [3,11] (.br 487 [3,5] (.ext 573 [7] .low) (.ext 541 [7] .low))))) (.br 73 [3] (.br 127 [3] (.jump 156 (.ext 311 [3,11,13] (.ext 621 [3,7,11] (.br 751 [] (.br 991 [] (.ext 1983 [3,5,7,19] (.ext 2245 [3,23] .low)) (.ext 1750 [3,5,19] .low)) (.br 991 [] (.ext 1545 [3,5] .low) (.ext 1355 [3,5] .low)))))) (.ext 255 [5,11,13] (.ext 437 [3] .low))) (.br 127 [3] (.ext 255 [3,11,13] (.ext 411 [3,5] .low)) (.ext 220 [3,11] .low)))) (.br 61 [] (.br 73 [3] (.br 127 [5,11] (.br 191 [5] (.ext 383 [3,11] (.br 487 [] (.ext 975 [3,7,11] (.ext 1949 [3,5] (.ext 2337 [3,5,23] .low))) (.ext 975 [3,7,11] (.ext 1462 [3,5] .low)))) (.ext 383 [3,5,11] (.br 383 [] (.br 487 [] (.ext 975 [3,7,11] (.ext 1325 [3,5] .low)) (.ext 975 [3,7,11] (.ext 989 [3] .low))) (.br 487 [19] (.br 761 [3,7,11] .low (.ext 911 [5,13] .low)) (.ext 748 [3,7,11,17] .low))))) (.br 191 [5] (.ext 383 [3] (.ext 451 [] .low)) (.ext 324 [3] .low))) (.br 127 [5,11] (.br 191 [3] (.ext 383 [3,5,11] (.ext 420 [] .low)) (.ext 330 [3,5,11,13] .low)) (.ext 187 [3] .low))) (.br 73 [3] (.br 127 [3,5] (.br 191 [5] (.ext 364 [3,11,13] .low) (.ext 297 [3,11,13] .low)) (.ext 173 [5] .low)) (.br 127 [3,5] (.ext 184 [3] .low) .low)))) (.br 47 [] (.br 61 [] (.ext 123 [3,11] (.br 127 [] (.br 151 [] (.ext 303 [3,7,11] (.ext 344 [] .low)) (.ext 268 [3,11] .low)) (.br 151 [] (.ext 164 [] .low) (.ext 159 [] .low)))) (.ext 123 [3] (.br 127 [3] (.br 151 [] (.ext 160 [] .low) (.ext 157 [] .low)) .low))) (.br 61 [] (.br 113 [3,5] (.br 127 [11] .low .low) (.br 127 [11] (.ext 140 [] .low) .low)) (.br 113 [3,5] .low (.br 127 [3] .low .low))))) (.br 37 [] (.br 47 [] (.br 73 [3] (.br 127 [3] .low .low) (.br 127 [3] .low .low)) (.br 73 [3] (.ext 94 [] .low) (.ext 82 [] .low))) (.br 47 [] (.ext 61 [] .low) (.ext 53 [] .low))))) (.br 23 [] (.br 31 [] (.br 61 [3] (.br 79 [3] (.br 127 [7,11] (.ext 152 [] .low) .low) (.br 127 [7,11] .low .low)) (.br 79 [3] (.br 127 [3,7] .low .low) (.ext 115 [7] .low))) (.ext 48 [3] .low)) (.br 29 [] (.br 31 [] (.br 61 [3] (.ext 71 [3] .low) (.ext 66 [3] .low)) .low) (.br 31 [] (.br 47 [3] (.br 61 [] (.br 79 [3] (.ext 124 [3,11] .low) (.ext 97 [3] .low)) (.ext 77 [3] .low)) (.br 59 [] .low (.br 61 [] (.ext 65 [3] .low) (.ext 64 [3] .low)))) .low))))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem okIn11 : checkTree [11, 3, 7, 13] 12 certIn11 = true := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem okOut11 : checkTree [3, 7, 13] 12 certOut11 = true := by decide +kernel

-- Section 6. Entry point.

theorem kill_z5_e2 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5)
    (he : n.factorization 5 = 2) (h43 : 43 ≤ padicValNat 2 n)
    (hm : padicValNat 2 n % 4 = 2) (h3 : 3 ∣ n) : False := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  set m := padicValNat 2 n
  set P := (n.primeFactors.erase 2).filter (fun r => r ∉ ({5} : Finset ℕ))
  have h5notP : 5 ∉ P := fun hx => (Finset.mem_filter.mp hx).2 (Finset.mem_singleton_self 5)
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ 2 → c ∈ ({5} : Finset ℕ) := prime_dvd_prime_pow (by norm_num)
  obtain ⟨S1, -, S3, -, -, S6, S7, S8⟩ := facts hP hK E
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h13P : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
  have h3P : 3 ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by norm_num, ?_⟩, hnz (by norm_num)⟩
    exact Nat.mem_primeFactors.mpr ⟨by norm_num, h3, h.2.ne'⟩
  have hled : ¬ 5 ^ 2 ∣ ∏ p ∈ P, (p + 1) := by
    intro h25
    have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm
    have h125 : 5 ^ 3 ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) := by
      have h1 : 5 * 5 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ P, (p + 1) := mul_dvd_mul h5m h25
      have h2 : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) := by
        exact ⟨1 + 5 ^ 2, by ring⟩
      exact (show 5 ^ 3 = 5 * 5 ^ 2 by norm_num).symm ▸ (h1.trans h2)
    rw [E] at h125
    have h5rhs : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := by
      have : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
        convert h125 using 1 <;> ring
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5 ^ 2)).mp this
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5rhs with h52 | h5prod
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h52)
      omega
    · obtain ⟨q, hqP, h5q⟩ := (Prime.dvd_finsetProd_iff (by norm_num : Nat.Prime 5).prime _).mp h5prod
      have hqeq : 5 = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP q hqP).1).mp h5q
      exact h5notP (hqeq ▸ hqP)
  have C : Ctx P m :=
    ⟨hP, by simpa using E,
      fun c hc hc2 hc5 => S1 c hc hc2 (hnz hc5),
      fun c hc hc2 hc5 => S3 c hc hc2 (hnz hc5),
      fun c hc hc2 hc5 => S6 c hc hc2 (hnz hc5),
      fun p hp => S8 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) p hp,
      hled, h43⟩
  have h0 : St P [3, 7, 13] 11 := by
    refine ⟨fun x hx => ?_, by decide, fun p hp hlt => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact h3P
      · exact h7P
      · exact h13P
    · have hpp := (hP p hp).1
      have hp2 := (hP p hp).2
      have hp5 : p ≠ 5 := fun e => h5notP (e ▸ hp)
      have hp_lo := hpp.two_le
      interval_cases p <;> first | (norm_num at hpp; done) | contradiction | decide
  by_cases h11 : 11 ∈ P
  · exact checkTree_sound C certIn11 [11, 3, 7, 13] 12 (incl_step h0 h11 (by decide)) okIn11
  · exact checkTree_sound C certOut11 [3, 7, 13] 12 (excl_step h0 h11) okOut11

end OMA.P_Erdos1052_z5_e2

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1.H2 := by
  refine ⟨0, fun n h hS he h43 hm h3 _ _ => ?_⟩
  exact (OMA.P_Erdos1052_z5_e2.kill_z5_e2 h hS he h43 hm h3).elim
