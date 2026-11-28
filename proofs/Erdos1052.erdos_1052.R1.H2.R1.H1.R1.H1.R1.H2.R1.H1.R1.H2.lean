import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1.H2

Hypothesis H2 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1`: unitary perfect numbers
`n = 2 ^ a * 3 ^ 11 * (simple odd primes)` with `a = 2 mod 4` and `a ≥ 262`. The step is vacuous: there is no
such `n`, so `A = 0` works. Of the hypotheses only `a = 2 mod 4` and `a ≥ 64` are used.

Credit: @marian2js (agent: Claude Code, model claude-opus-5-5). The method and most of the code are those of
@aroth01's proof of step `...R1.H2.R1.H1.R1.H2.R1.H1.R1.H2` (the case `5 ^ 2`), adapted to `3 ^ 11`; the base
lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...) are those of reduction
`...R1.H2.R1.H1.R1` (@adammcarter).

Setting. `P` is the set of simple odd primes (3 is not one of them). Balance:
  `(2 ^ a + 1) * (1 + 3 ^ 11) * prod (p + 1) = 2 ^ (a + 1) * 3 ^ 11 * prod p`, with `1 + 3 ^ 11 = 4 * 67 * 661`.
Every odd prime other than 3 occurs exactly once on the left. Forced: `67`, `661` (source `1 + 3 ^ 11`), `5`
(source `2 ^ a + 1`, as `a = 2 mod 4`), `17` (68), `331` (662), `83` (332), `7` (84). Closed: `5`, `67`, `661`
divide no `p + 1`. Ledger: neither `2 ^ a + 1` nor `1 + 3 ^ 11` is divisible by 3, so `3 ^ 12` does not divide
the product of the `p + 1`.

Proof. The search tree of @aroth01 over states `St P X Y N` (members of `X` are simple primes, those of `Y` are
not, every simple prime below `N` is in `X`), with windows `N → N' < 2 N` (`extend`) and the contradiction
`low_kill`: the unknown simple primes are at least `N` and lie on disjoint paths ending at an open member of
`X`, at a prime `q` with `3 ∣ q + 1` (at most `ledgerLeft X` of them) or at a Mersenne prime, so the weight is at
most `((N + 1) / (N - 1)) ^ (opens + ledger) * (N + 1) / (N - 3)`, too small. Starting from the seven forced
primes and `N = 5`, every branch dies by `N = 1025` (3105 splits, 3106 lower contradictions).
-/

namespace OMA.P_Erdos1052_z3_e11_c2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts path_bound tail_bound exists_child two_mul_le B_step B_anti
  B_nonneg one_add_le_B kernel_balance_one two_pow_of_no_odd_prime five_dvd_two_pow_add_one prime_dvd_prime_pow)

-- Section 1. The checks, as computable functions on lists of numbers.

/-- The products of the sublists of a list. -/
def subProds : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProds t ++ (subProds t).map (fun d => c * d)

/-- The open members of `X`: not closed (5, 67, 661), and dividing no `x + 1` with `x` in `X`. -/
def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 5 && c != 67 && c != 661 && X.all (fun x => (x + 1) % c != 0))

/-- The product of the `x + 1`. -/
def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

/-- How many more factors 3 the product of the `p + 1` can take. -/
def ledgerLeft (X : List ℕ) : ℕ :=
  Nat.findGreatest (fun c => (3 ^ c * succProd X) % 3 ^ 12 ≠ 0) 11

/-- A candidate `v` is harmless: above the window, known, excluded, or with a proper factor in `F`. -/
def candOk (X Y F : List ℕ) (N' v : ℕ) : Bool :=
  decide (N' ≤ v) || decide (v ∈ X) || decide (v ∈ Y) ||
    F.any (fun f => decide (1 < f) && decide (f < v) && v % f == 0)

/-- The window check: for `d` a product of distinct open members of `X` and `3 ^ j` allowed by the ledger, the
only number `2 ^ i * 3 ^ j * d - 1` in `[N, 2 * N)` is harmless. -/
def winOk (X Y F : List ℕ) (N N' : ℕ) : Bool :=
  decide (N' < 2 * N) &&
    (subProds (opens X)).all (fun d => (List.range (ledgerLeft X + 1)).all (fun j =>
      decide (N < 3 ^ j * d) ||
        candOk X Y F N' (2 ^ (Nat.log2 (N / (3 ^ j * d)) + 1) * (3 ^ j * d) - 1)))

/-- The weight of `X` alone is already too large. -/
def upOk (X : List ℕ) : Bool := decide (2 * 177147 * X.prod ≤ 177148 * succProd X)

/-- The weight of `X` together with everything that can still come above `N` is too small. -/
def lowOk (X : List ℕ) (N : ℕ) : Bool :=
  decide (5 ≤ N) &&
    decide ((2 ^ 64 + 1) * 177148 * succProd X * (N + 1) ^ ((opens X).length + ledgerLeft X + 1) <
      2 * 2 ^ 64 * 177147 * X.prod * (N - 1) ^ ((opens X).length + ledgerLeft X) * (N - 3))

-- Section 2. The setting and the state of the search.

/-- What is known about the set `P` of simple odd primes. -/
structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 177148 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 177147 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  hcl : ∀ p ∈ P, ¬ 5 ∣ p + 1 ∧ ¬ 67 ∣ p + 1 ∧ ¬ 661 ∣ p + 1
  led : ¬ 3 ^ 12 ∣ ∏ p ∈ P, (p + 1)
  hm : 64 ≤ m

/-- The state: the members of `X` are simple primes, those of `Y` are not, and every simple prime below `N` is
in `X`. -/
def St (P : Finset ℕ) (X Y : List ℕ) (N : ℕ) : Prop :=
  (∀ x ∈ X, x ∈ P) ∧ X.Nodup ∧ (∀ y ∈ Y, y ∉ P) ∧ ∀ p ∈ P, p < N → p ∈ X

theorem incl {P : Finset ℕ} {X Y : List ℕ} {N y : ℕ} (h : St P X Y N) (hy : y ∈ P) (hyX : y ∉ X) :
    St P (y :: X) Y N := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨hyX, hXn⟩, hY, fun p hp hpN => List.mem_cons_of_mem _ (hcl p hp hpN)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hy
  · exact hXP x hx

theorem excl {P : Finset ℕ} {X Y : List ℕ} {N y : ℕ} (h : St P X Y N) (hy : y ∉ P) : St P X (y :: Y) N := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨hXP, hXn, fun x hx => ?_, hcl⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hy
  · exact hY x hx

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

theorem mem_opens {X : List ℕ} {c : ℕ} (hc : c ∈ X) (h5 : c ≠ 5) (h67 : c ≠ 67) (h661 : c ≠ 661)
    (h : ∀ x ∈ X, ¬ c ∣ x + 1) : c ∈ opens X := by
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨⟨⟨h5, h67⟩, h661⟩, fun x hx hmod => h x hx (Nat.dvd_of_mod_eq_zero hmod)⟩

/-- A closed prime is not the open child of a simple prime. -/
theorem ne_closed {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {p c : ℕ} (hp : p ∈ P) (hc : c ∣ p + 1) :
    c ≠ 5 ∧ c ≠ 67 ∧ c ≠ 661 := by
  obtain ⟨h5, h67, h661⟩ := C.hcl p hp
  exact ⟨fun e => h5 (e ▸ hc), fun e => h67 (e ▸ hc), fun e => h661 (e ▸ hc)⟩

theorem succProd_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, (x + 1) = succProd X :=
  List.prod_toFinset _ hn

theorem prod_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, x = X.prod := by
  rw [List.prod_toFinset _ hn, List.map_id']

/-- The ledger: a set `T` of simple primes outside `X` contributes its `q + 1` next to those of `X`. -/
theorem prod_mul_dvd {P : Finset ℕ} {X : List ℕ} (hXP : ∀ x ∈ X, x ∈ P) (hn : X.Nodup)
    {T : Finset ℕ} (hT : T ⊆ P) (hTX : ∀ q ∈ T, q ∉ X) :
    (∏ q ∈ T, (q + 1)) * succProd X ∣ ∏ p ∈ P, (p + 1) := by
  have hdisj : Disjoint T X.toFinset :=
    Finset.disjoint_left.mpr fun q hq hqX => hTX q hq (List.mem_toFinset.mp hqX)
  rw [← succProd_eq hn, ← Finset.prod_union hdisj]
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.union_subset hT fun x hx => hXP x (List.mem_toFinset.mp hx))

/-- What the ledger allows is at most `ledgerLeft X`. -/
theorem ledger_le {X : List ℕ} {c : ℕ} (h : ¬ 3 ^ 12 ∣ 3 ^ c * succProd X) : c ≤ ledgerLeft X := by
  have hc : c ≤ 11 := by
    by_contra hlt
    exact h ((pow_dvd_pow 3 (by omega : 12 ≤ c)).trans (Dvd.intro _ rfl))
  exact Nat.le_findGreatest hc fun h0 => h (Nat.dvd_of_mod_eq_zero h0)

/-- The only `2 ^ i * w` in `(N, 2 * N)` is the one given by the binary logarithm of `N / w`. -/
theorem pow_window {N w i t : ℕ} (hw : 0 < w) (hwN : w ≤ N) (ht : t = 2 ^ i * w) (h1 : N < t) (h2 : t < 2 * N) :
    2 ^ (Nat.log2 (N / w) + 1) * w = t := by
  have hq0 : N / w ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos hwN hw)
  have hk1 : 2 ^ Nat.log2 (N / w) * w ≤ N :=
    (Nat.mul_le_mul_right _ (Nat.log2_self_le hq0)).trans (Nat.div_mul_le_self _ _)
  have hk2 : N < 2 ^ (Nat.log2 (N / w) + 1) * w := (Nat.div_lt_iff_lt_mul hw).mp Nat.lt_log2_self
  have hgt : Nat.log2 (N / w) < i := by
    by_contra hle
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hle))
    omega
  have hlt : i < Nat.log2 (N / w) + 2 := by
    by_contra hge
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge))
    have e : 2 ^ (Nat.log2 (N / w) + 2) * w = 2 * (2 ^ (Nat.log2 (N / w) + 1) * w) := by ring
    omega
  have hi : i = Nat.log2 (N / w) + 1 := by omega
  rw [ht, hi]

-- Section 4. The window lemma: the closure of the known set moves from `N` to `N'`.

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y F : List ℕ} {N N' : ℕ}
    (h : St P X Y N) (hchk : winOk X Y F N N' = true) : St P X Y N' := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨hXP, hXn, hY, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact hcl p hp hpN
  by_contra hpX
  simp only [winOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨hN2, hall⟩ := hchk
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
  obtain ⟨j, d, hd, hjd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := u) hu0 3 (by norm_num)
  have hdvd : d ∣ p + 1 := ⟨2 ^ i * 3 ^ j, by rw [hiu, hjd]; ring⟩
  have hprime : ∀ c : ℕ, c.Prime → c ∣ d → c ≠ 2 ∧ c ≠ 3 := fun c _ hcd =>
    ⟨fun h2 => hu (by rw [hjd]; exact (h2 ▸ hcd).mul_left _), fun hz => hd (hz ▸ hcd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ opens X := fun c hc hcd => by
    obtain ⟨hc2, hcz⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hcz p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    obtain ⟨h5, h67, h661⟩ := ne_closed C hp hcp
    refine mem_opens hcX h5 h67 h661 fun x hx hcx => ?_
    exact hpX ((C.s3 c hc hc2 hcz p hp x (hXP x hx) hcp hcx) ▸ hx)
  have hdD : d ∣ (opens X).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hcz⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hcz p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hmem : d ∈ subProds (opens X) := mem_subProds _
    (fun c hc => (C.hP c (hXP c (List.mem_filter.mp hc).1)).1) d hdD
  have hjdvd : 3 ^ j ∣ p + 1 := ⟨2 ^ i * d, by rw [hiu, hjd]; ring⟩
  have hjL : j ≤ ledgerLeft X := by
    refine ledger_le fun h2 => ?_
    have h3 : 3 ^ j * succProd X ∣ (p + 1) * succProd X := Nat.mul_dvd_mul_right hjdvd _
    have h4 := prod_mul_dvd hXP hXn (T := {p}) (Finset.singleton_subset_iff.mpr hp)
      (fun q hq => (Finset.mem_singleton.mp hq) ▸ hpX)
    rw [Finset.prod_singleton] at h4
    exact C.led (h2.trans (h3.trans h4))
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hu ⟨(p + 1) / 2, by omega⟩
  have hw0 : 0 < 3 ^ j * d := Nat.pos_of_ne_zero (by rw [← hjd]; exact hu0)
  have hpw : p + 1 = 2 ^ i * (3 ^ j * d) := by rw [hiu, hjd]
  have hwN : 3 ^ j * d ≤ N := by
    by_contra hNw
    have h2 : 2 ^ 1 * (3 ^ j * d) ≤ 2 ^ i * (3 ^ j * d) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi1)
    omega
  have h1 := hall d hmem j (List.mem_range.mpr (by omega))
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (of_decide_eq_true h1) (not_lt.mpr hwN)
  · have hv : 2 ^ (Nat.log2 (N / (3 ^ j * d)) + 1) * (3 ^ j * d) - 1 = p := by
      rw [pow_window hw0 hwN hpw (by omega) (by omega), Nat.add_sub_cancel]
    rw [hv] at h1
    simp only [candOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with ((h1 | h1) | h1) | ⟨f, -, ⟨hf1, hfp⟩, hmod⟩
    · omega
    · exact hpX h1
    · exact hY p h1 hp
    · rcases (Nat.dvd_prime hpp).mp (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

-- Section 5. The two contradictions.

theorem up_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ}
    (h : St P X Y N) (hchk : upOk X = true) : False := by
  obtain ⟨hXP, hXn, -, -⟩ := h
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
  have key : 2 ^ (m + 1) * 177147 * ((∏ p ∈ P \ X.toFinset, p) * X.prod) <
      (2 ^ m + 1) * 177148 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) :=
    calc 2 ^ (m + 1) * 177147 * ((∏ p ∈ P \ X.toFinset, p) * X.prod)
        = 2 ^ m * ((∏ p ∈ P \ X.toFinset, p) * (2 * 177147 * X.prod)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (177148 * succProd X)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hchk)
      _ < (2 ^ m + 1) * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (177148 * succProd X)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 177148 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (177148 / 177147) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 177148 * ∏ p ∈ P, ((p : ℚ) + 1) =
      2 ^ (m + 1) * 177147 * ∏ p ∈ P, (p : ℚ) := by
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

theorem final_ineq {S Pi N E : ℕ} (hN : 5 ≤ N) (hPi : 0 < Pi)
    (h : (2 ^ 64 + 1) * 177148 * S * (N + 1) ^ (E + 1) < 2 * 2 ^ 64 * 177147 * Pi * (N - 1) ^ E * (N - 3)) :
    (1 + 1 / (2 : ℚ) ^ 64) * (177148 / 177147) * ((S : ℚ) / Pi) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ E *
      (((N : ℚ) + 1) / ((N : ℚ) - 3)) < 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e3 : k + 3 - 3 = k := by omega
  rw [e1, e3] at h
  have hq := (Nat.cast_lt (α := ℚ)).mpr h
  push_cast at hq
  have hk : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  have hPiq : (0 : ℚ) < Pi := by exact_mod_cast hPi
  have hk2 : (0 : ℚ) < (k : ℚ) + 2 := by linarith
  have e : (1 + 1 / (2 : ℚ) ^ 64) * (177148 / 177147) * ((S : ℚ) / Pi) *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 1)) ^ E *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 3)) =
      (((2 : ℚ) ^ 64 + 1) * 177148 * S * ((k : ℚ) + 3 + 1) ^ (E + 1)) /
        (2 ^ 64 * 177147 * Pi * ((k : ℚ) + 2) ^ E * k) := by
    push_cast
    have e4 : (k : ℚ) + 3 - 1 = k + 2 := by ring
    have e5 : (k : ℚ) + 3 - 3 = k := by ring
    rw [e4, e5, div_pow]
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  linarith

theorem low_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ}
    (h : St P X Y N) (hchk : lowOk X N = true) : False := by
  obtain ⟨hXP, hXn, -, hcl⟩ := h
  simp only [lowOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hN5, hnum⟩ := hchk
  classical
  obtain ⟨g, hg⟩ := exists_child ({3} : Finset ℕ)
  have hnz : ∀ {c : ℕ}, c ∉ ({3} : Finset ℕ) → c ≠ 3 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 3 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hnz hcN, C.s1 _ hc hc2 (hnz hcN) p hp (hg p).1,
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
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact C.s3 _ hc hc2 hcz q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
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
    obtain ⟨hc, hc2, hcz, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hq (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    obtain ⟨h5, h67, h661⟩ := ne_closed C hqP (hg q).1
    refine mem_opens hcX h5 h67 h661 fun x hx hcx => ?_
    exact hQX q (hRQ q hq) ((C.s3 _ hc hc2 hcz q hqP x (hXP x hx) (hg q).1 hcx) ▸ hx)
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (C.hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcardA : (R.filter (fun q => g q ≠ 1)).card ≤ (opens X).length := by
    refine (Finset.card_le_card_of_injOn g (t := (opens X).toFinset) ?_ ?_).trans (List.toFinset_card_le _)
    · intro q hq
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (hA q hqR h1))
    · intro q hq q' hq' he
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hRP q hqR) h1
      exact C.s3 _ hc hc2 hcz q (hRP q hqR) q' (hRP q' hqR') (hg q).1 (he ▸ (hg q').1)
  have hledB : ¬ 3 ^ 12 ∣ 3 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1)).card * succProd X :=
    fun hd => by
      have hsub : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1), q ∈ R := fun q hq =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      have h1 := prod_mul_dvd hXP hXn (T := (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1))
        (fun q hq => hRP q (hsub q hq)) (fun q hq => hQX q (hRQ q (hsub q hq)))
      have h2 : 3 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1)).card ∣
          ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1), (q + 1) := by
        rw [← Finset.prod_const]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
      exact C.led (hd.trans ((Nat.mul_dvd_mul_right h2 _).trans h1))
  have hcardB : ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1)).card ≤ ledgerLeft X :=
    ledger_le hledB
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 3 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, hzq⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact hzq (this ▸ hcd)
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 3 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    refine tail_bound _ _ N rfl (by omega)
      (fun q hq => hQN q (hRQ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1))
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
  have hprodA : ∏ q ∈ R.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp hq).1)
      (fun q hq => hβN q (Finset.mem_filter.mp hq).1)
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 3 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hpowle : (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 3 ∣ q + 1)).card ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hBN1 (Nat.add_le_add hcardA hcardB)
  have hT0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    have : (5 : ℚ) ≤ N := by exact_mod_cast hN5
    exact div_nonneg (by linarith) (by linarith)
  have hB0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := le_trans zero_le_one hBN1
  have hRbound : ∏ q ∈ R, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    rw [← hsplit1, ← hsplit2, ← mul_assoc]
    refine mul_le_mul (le_trans (mul_le_mul hprodA hprodB ?_ (pow_nonneg hB0 _)) hpowle) hprodC ?_
      (pow_nonneg hB0 _)
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
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
  have hfin := final_ineq hN5 hPipos hnum
  have hm64 : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 64 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) C.hm)
  have hSq : (0 : ℚ) ≤ (succProd X : ℚ) / (X.prod : ℚ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hQle := hpath.trans hRbound
  have hQ0 : (0 : ℚ) ≤ ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hchain : (1 + 1 / (2 : ℚ) ^ m) * (177148 / 177147) *
      ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) ≤
      (1 + 1 / (2 : ℚ) ^ 64) * (177148 / 177147) * ((succProd X : ℚ) / (X.prod : ℚ)) *
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    have h1 : (1 + 1 / (2 : ℚ) ^ m) * (177148 / 177147) ≤ (1 + 1 / (2 : ℚ) ^ 64) * (177148 / 177147) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h2 : (succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) ≤
        (succProd X : ℚ) / (X.prod : ℚ) * ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
          (((N : ℚ) + 1) / ((N : ℚ) - 3))) := mul_le_mul_of_nonneg_left hQle hSq
    calc (1 + 1 / (2 : ℚ) ^ m) * (177148 / 177147) *
        ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)))
        ≤ (1 + 1 / (2 : ℚ) ^ 64) * (177148 / 177147) * ((succProd X : ℚ) / (X.prod : ℚ) *
          ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
            (((N : ℚ) + 1) / ((N : ℚ) - 3)))) :=
          mul_le_mul h1 h2 (mul_nonneg hSq hQ0) (by positivity)
      _ = _ := by ring
  linarith

-- Section 6. Search trees as data, and their checker.

/-- A search tree: `U` and `L` are the two contradictions, `W N' F t` moves the closure to `N'` (with the factors
`F`) and goes on with `t`, `B y t1 t2` splits on whether `y` is a simple prime. -/
inductive T where
  | U : T
  | L : T
  | W : ℕ → List ℕ → T → T
  | B : ℕ → T → T → T

/-- The checker of a tree at the state `X`, `Y`, `N`. -/
def chk : T → List ℕ → List ℕ → ℕ → Bool
  | T.U, X, _, _ => upOk X
  | T.L, X, _, N => lowOk X N
  | T.W N' F t, X, Y, N => winOk X Y F N N' && chk t X Y N'
  | T.B y t1 t2, X, Y, N => decide (y ∉ X) && chk t1 (y :: X) Y N && chk t2 X (y :: Y) N

theorem sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    ∀ (t : T) (X Y : List ℕ) (N : ℕ), chk t X Y N = true → St P X Y N → False
  | T.U, _, _, _, h, hs => up_kill C hs h
  | T.L, _, _, _, h, hs => low_kill C hs h
  | T.W N' F t, X, Y, N, h, hs => by
    rw [chk, Bool.and_eq_true] at h
    exact sound C t X Y N' h.2 (extend C hs h.1)
  | T.B y t1 t2, X, Y, N, h, hs => by
    rw [chk, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hy : y ∈ P
    · exact sound C t1 (y :: X) Y N h.1.2 (incl hs hy h.1.1)
    · exact sound C t2 X (y :: Y) N h.2 (excl hs hy)

-- Section 7. The search tree (found by an exact search; the kernel runs the checker on it).

set_option maxRecDepth 1000000 in
/-- The search tree: 3105 splits, 3106 lower contradictions, 3583 windows. -/
def tree : T :=
  (.W 9 [] (.B 11 (.W 17 [3] (.B 23 (.B 31 (.W 33 [3] (.B 43 (.B 47 (.B 53 (.B 61 (.W 65 [3] (.B 127 (.W 129 [3,
  5, 7, 11] (.B 137 (.B 211 (.W 257 [3, 11] (.B 421 (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7,
  29] .L) (.W 1025 [3, 5, 7, 29] .L)) (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)))) (.W 513
  [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)) (.B 751 (.W 1025 [3, 5, 29] .L) (.W
  1025 [3, 5, 29] .L))))) (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))
  (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5] .L)
  (.W 1025 [3, 5] .L)) (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L))))))) (.W 257 [3, 11] (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)))) (.B 191 (.B 211 (.W 257 [3, 11] (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] (.B 733
  (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)) (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3,
  5, 7, 29] .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)) (.B 751
  (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L))))) (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3,
  5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B
  733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L)))))) (.B 421 (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L))) (.W
  513 [3, 7] (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)))) (.B 487 (.W 513 [3, 7] (.B 751 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L))))))) (.W 257 [3, 11] (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3,
  5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025
  [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))))) (.B 487 (.W
  513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L))))) (.B 211 (.W 257 [3,
  11] (.B 257 (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5,
  7, 29] .L)) (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)))) (.W 513 [3, 7] (.B 733 (.B 751
  (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)) (.B 751 (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)))))
  (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)) (.B
  751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)))))) (.B 421 (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7, 29]
  .L) (.W 1025 [3, 5, 7, 29] .L))) (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)))) (.B
  487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L)))) (.B 281 (.B
  367 (.B 421 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L))) (.W 513 [3,
  7] (.B 733 (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)))) (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L))))) (.B 421 (.B
  487 (.W 513 [3, 7] (.W 1025 [3, 5, 7, 29] .L)) (.W 513 [3, 7] (.W 1025 [3, 5, 29] .L))) (.B 487 (.W 513 [3, 7]
  (.W 1025 [3, 5, 7] .L)) (.W 513 [3, 7] .L)))) (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751
  (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)) (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7,
  29] .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L)) (.B 751 (.W 1025
  [3, 5, 29] .L) (.W 1025 [3, 5, 29] .L))))) (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W
  1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 733 (.B 751
  (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)) (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)))))) (.B 421 (.B 487
  (.W 513 [3, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L)) (.B 733 (.B 751 (.B 761
  (.W 1025 [3, 7, 29] .L) (.W 1025 [3, 5, 7, 13, 29] .L)) (.B 761 (.W 1025 [3, 7, 29] .L) (.W 1025 [3, 5, 7, 13,
  29] .L))) (.B 751 (.B 761 (.W 1025 [3, 7, 29] .L) (.W 1025 [3, 5, 7, 13, 29] .L)) (.B 761 (.W 1025 [3, 7, 29]
  .L) (.W 1025 [3, 5, 7, 13, 29] .L)))))) (.W 513 [3, 5, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 29] .L) (.W 1025 [3,
  5, 29] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 29] .L) (.W 1025 [3, 5, 13, 17, 29] .L)) (.B 761 (.W 1025 [3,
  29] .L) (.W 1025 [3, 5, 13, 17, 29] .L))) (.B 751 (.B 761 (.W 1025 [3, 29] .L) (.W 1025 [3, 5, 13, 17, 29]
  .L)) (.B 761 (.W 1025 [3, 29] .L) (.W 1025 [3, 5, 13, 17, 29] .L))))))) (.B 487 (.W 513 [3, 7] (.B 563 (.B 733
  (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7,
  13] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W 1025
  [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13] .L)))))) (.W 513 [3, 5, 7] (.B 563 (.B
  733 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3] .L) (.W 1025 [3, 5, 13, 17]
  .L)) (.B 761 (.W 1025 [3] .L) (.W 1025 [3, 5, 13, 17] .L))) (.B 751 (.B 761 (.W 1025 [3] .L) (.W 1025 [3, 5,
  13, 17] .L)) (.B 761 (.W 1025 [3] .L) (.W 1025 [3, 5, 13, 17] .L))))))))) (.B 383 (.B 421 (.B 487 (.W 513 [3,
  7] (.B 751 (.W 1025 [3, 5, 7, 29] .L) (.W 1025 [3, 5, 7, 29] .L))) (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 29]
  .L) (.W 1025 [3, 5, 29] .L)))) (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))
  (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L))))) (.B 421 (.B 487 (.W 513 [3, 5, 7] (.B 563
  (.W 1025 [3, 5, 7, 29] .L) (.B 751 (.B 761 (.W 1025 [3, 7, 29] .L) (.W 1025 [3, 5, 7, 13, 19, 29] .L)) (.B 761
  (.W 1025 [3, 7, 29] .L) (.W 1025 [3, 5, 7, 13, 19, 29] .L))))) (.W 513 [3, 5, 7] (.B 563 (.W 1025 [3, 5, 29]
  .L) (.B 751 (.B 761 (.W 1025 [3, 29] .L) (.W 1025 [3, 5, 13, 17, 19, 29] .L)) (.B 761 (.W 1025 [3, 29] .L) (.W
  1025 [3, 5, 13, 17, 19, 29] .L)))))) (.B 487 (.W 513 [3, 5, 7] (.B 563 (.W 1025 [3, 5, 7] .L) (.B 751 (.B 761
  (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 19] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 19]
  .L))))) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 11] (.B 257 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 317 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751
  (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))))))) (.W 129 [3, 5, 7, 11] (.B 137 (.B
  211 (.W 257 [3, 11] (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)))) (.W 257 [3, 11] (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 191 (.B 211 (.W 257 [3, 11]
  (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))
  (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))))) (.W
  257 [3, 11] (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))))) (.B 211 (.W 257 [3, 11] (.B 257 (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 281 (.B 367 (.B 421 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W
  513 [7] .L) (.W 513 [7] .L))) (.B 421 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513
  [7] .L)))) (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 11] (.B 257 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 317 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))))))))) (.W 65 [3] (.B 127 (.W 129 [3, 5, 7] (.B 137
  (.B 211 (.W 257 [3, 11, 13] (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.W 257 [3, 11, 13] (.W 513 [3, 7]
  .L))) (.B 191 (.B 211 (.W 257 [3, 11, 13] (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3, 11, 13] (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B
  211 (.W 257 [3, 5, 11, 13] (.B 257 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 5, 11, 13] (.B 257 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 281 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 317 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))))))))))) (.W 129 [3, 5, 7] (.B 137 (.B 211 (.W 257 [3, 11, 13] (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.W 257 [3, 11, 13] .L)) (.B 191 (.B 211 (.W 257 [3, 11, 13] (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3, 11, 13] (.B 367 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)))) (.B 211 (.W 257 [3, 5, 11, 13] (.B 257 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 421 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 5, 11, 13] .L)))))))) (.B 61 (.W 65 [3,
  5] (.B 71 (.B 127 (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.W 257 [3, 11] (.B 283 (.B 487 (.W 513 [3, 7] (.B 547
  (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L)))) (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L))))) (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3,
  5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025
  [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))))))) (.W 257 [3,
  11] (.B 257 (.B 283 (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B
  751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5] .L) (.W
  1025 [3, 5] .L)) (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L))))) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 281 (.B 283 (.B 487 (.W 513 [3, 7] (.B 547 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513
  [3, 7] (.B 547 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)))) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B
  283 (.B 383 (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3,
  5] .L)) (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L))))) (.B 487 (.W 513 [3, 7] (.B 547 (.B 563 (.W 1025
  [3, 5, 7] .L) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7]
  .L) (.W 1025 [3, 5, 7, 13] .L)))) (.B 563 (.W 1025 [3, 5, 7] .L) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.B
  821 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B 761 (.W 1025 [3, 5, 7] .L) (.B 821 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7, 13] .L))))))) (.W 513 [3, 5, 7] (.B 547 (.B 563 (.W 1025 [3, 5] .L) (.B 751 (.B 761
  (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L)) (.B 761 (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L))))
  (.B 563 (.W 1025 [3, 5] .L) (.B 751 (.B 761 (.W 1025 [3, 5] .L) (.B 821 (.W 1025 [3, 5] .L) (.W 1025 [3, 5,
  13, 17] .L))) (.B 761 (.W 1025 [3, 5] .L) (.B 821 (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L))))))))) (.B
  383 (.B 487 (.W 513 [3, 7] (.B 547 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3,
  5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)))))))) (.B 191 (.W 257 [3, 11] (.B 257 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3,
  5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B
  733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L))))) (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] (.B 751
  (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))))) (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3,
  5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B
  733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L))))) (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L))))
  (.B 281 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513
  [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.B 487 (.W 513 [3, 7] (.W 1025 [3, 5, 7] .L))
  (.W 513 [3, 7] (.W 1025 [3, 5, 7] .L)))) (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W
  1025 [3, 5, 7] .L))) (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.B 487 (.W 513
  [3, 7] (.W 1025 [3, 5, 7] .L)) (.W 513 [3, 7] .L)))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733
  (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L))))) (.B 487 (.W 513 [3, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3,
  5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761
  (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)))))) (.W 513 [3, 5, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 7]
  .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 17] .L)) (.B
  761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 17] .L))) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025
  [3, 5, 7, 13, 17] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 17] .L)))))))) (.B 383 (.B 487
  (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L)))) (.B 487 (.W 513 [3, 5, 7] (.B 563 (.W 1025 [3, 5, 7] .L) (.B 751 (.B 761 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 19] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 19]
  .L))))) (.W 513 [3, 5, 7] (.B 563 (.W 1025 [3, 5, 7] .L) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3,
  5, 7, 13, 17, 19] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 17, 19] .L)))))))) (.B 367 (.B
  383 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3,
  5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7]
  .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))))) (.B 487 (.W 513 [3, 5, 7] (.B 563 (.B 733 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13,
  23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 23] .L))) (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W
  1025 [3, 5, 7, 13, 23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 23] .L)))))) (.W 513 [3, 5, 7]
  (.B 563 (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W
  1025 [3, 5, 7, 13, 17, 23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 17, 23] .L))) (.B 751 (.B
  761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 17, 23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13,
  17, 23] .L)))))))) (.B 383 (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W
  513 [3, 7] (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.B 487 (.W 513 [3, 5, 7] (.B 563 (.W 1025
  [3, 5, 7] .L) (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 19, 23] .L)) (.B 761 (.W 1025 [3, 7]
  .L) (.W 1025 [3, 5, 7, 13, 19, 23] .L))))) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 11] (.B 257 (.B 281 (.B
  283 (.B 367 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513
  [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)) (.B 751 (.W 1025 [3, 5] .L) (.W 1025 [3, 5]
  .L))))) (.B 487 (.W 513 [3, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751
  (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7,
  13] .L))) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7] .L)
  (.W 1025 [3, 5, 7, 13] .L)))))) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] (.B 751 (.W 1025 [3, 5,
  7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733 (.B 751 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 751 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)))) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)))))) (.B 281 (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3,
  5, 7] .L))) (.W 513 [3, 7] (.B 733 (.W 1025 [3, 5] .L) (.W 1025 [3, 5] .L)))) (.B 487 (.W 513 [3, 7] (.B 733
  (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7,
  13] .L)))) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] (.W 1025 [3, 5, 7] .L)) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 733 (.W 1025
  [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L))) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] (.B 563 (.B 733 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5,
  7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7]
  .L) (.W 1025 [3, 5, 7, 13] .L))) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761
  (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)))))) (.W 513 [3, 5, 7] (.B 563 (.B 733 (.W 1025 [3, 5] .L)
  (.W 1025 [3, 5] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L)) (.B 761 (.W 1025
  [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L))) (.B 751 (.B 761 (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L)) (.B
  761 (.W 1025 [3, 5] .L) (.W 1025 [3, 5, 13, 17] .L))))))) (.B 487 (.W 513 [3, 7] (.B 563 (.B 733 (.B 761 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B
  733 (.B 751 (.B 761 (.W 1025 [3, 5, 7, 13] .L) (.B 773 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B
  761 (.W 1025 [3, 5, 7, 13] .L) (.B 773 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L)))) (.B 751 (.B 761
  (.W 1025 [3, 5, 7, 13] .L) (.B 773 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L))) (.B 761 (.W 1025 [3, 5,
  7, 13] .L) (.B 773 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13] .L))))))) (.W 513 [3, 5, 7] .L))) (.B 383 (.B
  487 (.W 513 [3, 5, 7] (.B 563 (.W 1025 [3, 5, 7] .L) (.B 751 (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7,
  13, 19] .L)) (.B 761 (.W 1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7, 13, 19] .L))))) (.W 513 [3, 5, 7] .L)) (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] (.B 563 (.B 733 (.W
  1025 [3, 5, 7] .L) (.W 1025 [3, 5, 7] .L)) (.B 733 (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13,
  23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 23] .L))) (.B 751 (.B 761 (.W 1025 [3, 7] .L) (.W
  1025 [3, 5, 7, 13, 23] .L)) (.B 761 (.W 1025 [3, 7] .L) (.W 1025 [3, 5, 7, 13, 23] .L)))))) (.W 513 [3, 5, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))))) (.W 129 [3, 5, 7, 11] (.B 137 (.B 191
  (.W 257 [3, 11] (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L)))) (.W 257 [3, 11] (.B 257 (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 283 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5,
  7] .L) (.W 513 [3, 5, 7] .L)))))))) (.B 191 (.W 257 [3, 11] (.B 257 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 281 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 11] (.B
  257 (.B 281 (.B 283 (.B 367 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)))
  (.B 367 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)))) (.B 283 (.B 367
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)))))) (.B 281 (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W
  513 [5, 7] .L))) (.B 383 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7]
  .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7] .L))))) (.B
  283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5,
  7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))))))) (.B 107 (.B 127 (.W 129 [3, 5, 7, 11] (.B 137 (.W 257 [3, 11]
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 191 (.W 257 [3, 11] (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3, 11] (.B 257 (.B 367 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))))) (.W 129 [3, 5, 7,
  11] (.B 137 (.W 257 [3, 11] (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 191 (.W 257 [3, 11] (.B 367
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3,
  11] (.B 257 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 281 (.B 367 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L))) (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))))))))))) (.B 127 (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.W 257 [3, 11] (.B 257 (.B 281 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W 257 [3, 5, 11] (.B 257 (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)))))))) (.B 191 (.W 257 [3, 5, 11] (.B 257 (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3,
  5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 281 (.B 367 (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B
  383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 5, 7, 11] (.B 257 (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.B 281
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))))) (.B 367 (.B 383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3,
  7, 17] .L) (.W 513 [3, 5, 7, 17] .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  487 (.W 513 [3, 5, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L))))))))))) (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.W
  257 [3, 11] (.B 257 (.B 281 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W 257 [3, 5, 11] (.B 257 (.B
  281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.B 191 (.W 257 [3, 5, 11] (.B 257 (.B 281 (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L))))) (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3,
  5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B
  487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B
  487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 5, 7, 11] (.B 257 (.B 281 (.B 367 (.B 383
  (.B 487 (.W 513 [7] .L) (.W 513 [5, 7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [5, 7] .L))) (.B 383 (.B 487 (.W
  513 [5, 7] .L) (.W 513 [5, 7] .L)) (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7] .L)))) (.B 367 (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.B
  281 (.B 367 (.B 383 (.B 487 (.W 513 [7] .L) (.W 513 [5, 7] .L)) (.B 431 (.B 487 (.W 513 [7] .L) (.W 513 [7]
  .L)) (.B 487 (.W 513 [7] .L) (.W 513 [5, 7] .L)))) (.B 383 (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7] .L)) (.B
  431 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [5, 7] .L) (.W 513 [5, 7] .L))))) (.B 367 (.B 383
  (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B
  431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7, 17] .L) (.W 513 [3, 5, 7, 17]
  .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7, 17] .L)
  (.W 513 [3, 5, 7, 17] .L))))))))))))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257
  [3, 11, 13] (.B 283 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.W 257 [3, 5, 11, 13] (.B 257 (.B 283 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 281 (.B 283 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 283 (.B 383 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.B 191 (.W 257 [3, 5, 11,
  13] (.B 257 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 281 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L))))))) (.W 257 [3, 5, 11, 13] (.B 257 (.B 281 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B
  367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B
  383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 281 (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3,
  5, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))))) (.W 129 [3, 5, 7] (.B 137
  (.B 191 (.W 257 [3, 11, 13] (.B 283 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.W 257 [3, 5, 11, 13] (.B 257 (.B
  283 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 281 (.B 283 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 283 (.B
  383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.B 191 (.W
  257 [3, 5, 11, 13] (.B 257 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 367 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 281 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 367 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 5, 11, 13] (.B 257 (.B 281 (.B 283 (.B 367 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3,
  5, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 281 (.B 283 (.B 367 (.B 383 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 283 (.B 367 (.B 383 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3,
  5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))))) (.B 107 (.B 127
  (.W 129 [3, 5, 7] (.B 137 (.W 257 [3, 11, 13] (.W 513 [3, 7] .L)) (.B 191 (.W 257 [3, 11, 13] (.B 367 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L))) (.W 257 [3, 5, 11, 13] (.B 257 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 281 (.B 367 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))))))) (.W 129 [3, 5, 7] (.B 137 (.W 257 [3, 11, 13] .L) (.B
  191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))) (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257
  [3, 5, 11, 13] (.B 257 (.B 281 (.W 513 [3, 7] .L) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B
  383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))))) (.W 257 [3, 5,
  11, 13] (.B 257 (.B 281 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L))) (.B 281 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.B 431 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))))))) (.B 191 (.W 257 [3, 5, 11, 13] (.B 257 (.B 281 (.B 367 (.B 383 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 367 (.B 383 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3,
  7] .L) (.B 431 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 383 (.W 513 [3, 5, 7] .L) (.B 431 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 5, 7, 11, 13] (.B 257 (.B 281 (.B 367 (.B 383 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L)
  (.B 431 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 383 (.W 513 [3, 5, 7] .L) (.B 431 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L))))) (.B 281 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.B 431 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 383 (.W 513 [3, 5, 7] .L) (.B 431 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B
  431 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 431 (.W 513 [3, 7] .L) (.W 513 [3, 7, 17] .L))) (.B 383 (.B 431
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7, 17] .L)))))))))) (.W
  129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5,
  11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)))))))))) (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5,
  7, 11] (.B 211 (.W 257 [3, 11] (.B 283 (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)))))) (.W 257 [3, 11] (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))))))) (.W 129 [3, 5, 7, 11] (.B 211 (.W 257 [3] (.B 283 (.B 367 (.B 421
  (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L))) (.B 421 (.B 487 (.W 513 [7]
  .L) (.W 513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)))) (.B 367 (.B 421 (.B 487 (.W 513 [7] .L) (.W
  513 [7] .L)) (.B 487 (.W 513 [7] .L) (.W 513 [7] .L))) (.B 421 (.B 487 (.W 513 [7] .L) (.W 513 [7] .L)) (.B
  487 (.W 513 [7] .L) (.W 513 [7] .L)))))) (.W 257 [3] .L)))) (.B 127 (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.B
  211 (.W 257 [3, 11] (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)))) (.W 257 [3, 11] (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 211 (.W 257 [3, 11] (.B 257
  (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 383
  (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W
  257 [3, 11] (.B 257 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 317 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L)))))))) (.B 191 (.B 211 (.W 257 [3, 11] (.B 257 (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 11] (.B 257 (.B 367 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 317 (.B 367 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.B 211 (.W 257
  [3, 11] (.B 257 (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5,
  7] .L) (.W 513 [3, 5, 7] .L))))) (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 11] (.B 257 (.B 317 (.B
  367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 317
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W
  513 [3, 5, 7] .L))))))))))) (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.B 211 (.W 257 [3] (.B 421 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3] .L)) (.B 211 (.W
  257 [3] .L) (.W 257 [3] .L))) (.B 191 (.B 211 (.W 257 [3] (.B 257 (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3] .L)) (.B 211 (.W
  257 [3, 11] .L) (.W 257 [3, 11] .L)))))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7] (.B 211 (.W 257 [3,
  11, 13] (.B 283 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L))) (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))))) (.W 257 [3, 11, 13] .L))) (.W 129 [3, 5, 7] (.B 211 (.W 257 [3, 13] .L) (.W 257 [3, 13] .L)))) (.B 127
  (.W 129 [3, 5, 7] (.B 137 (.B 191 (.B 211 (.W 257 [3, 11, 13] (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))
  (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B 191 (.B 211 (.W
  257 [3, 5, 11, 13] (.B 257 (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 367 (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L))) (.B 383 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 5, 7] .L) (.W
  513 [3, 5, 7] .L)))))) (.W 257 [3, 5, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))))) (.W 129 [3, 5, 7] (.B 137 (.B 191 (.B 211 (.W 257 [3, 13] .L) (.W 257 [3, 13] .L)) (.B 211 (.W 257 [3,
  5, 13] .L) (.W 257 [3, 5, 13] .L))) (.B 191 (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 211 (.W
  257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129
  [5, 7, 11] (.W 257 [3, 11] (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)))))) (.W 129 [5, 7, 11] (.W 257 [3] .L))) (.B 127 (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W
  257 [3, 11] (.B 257 (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L))) (.B 283 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L)))))) (.W 257 [3, 11] (.B 257 (.B 283 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 283 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.B 191 (.W 257 [3, 11] (.B 257 (.B 283 (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W
  513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.W 257 [3, 5, 11] (.B 257 (.B 283 (.B 367 (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367
  (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L))))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))
  (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))))) (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W 257
  [3] (.B 257 (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))) (.B 283 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)))))) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] (.B 257 (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 283 (.B 367 (.B 383
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))))))) (.W 257 [3, 5, 11] .L)))))) (.B 107 (.B 127 (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W 257 [3,
  11] (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] (.B 257 (.B
  367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W
  257 [3, 11] .L)))) (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W 257 [3] .L) (.W 257 [3] .L)) (.B 191 (.W 257 [3] .L)
  (.W 257 [3, 11] .L))))) (.B 127 (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W 257 [3, 5, 11] (.B 257 (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W 257 [3, 5, 7, 11] (.B 257 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7, 17] .L)
  (.W 513 [3, 5, 7, 17] .L))))))) (.B 191 (.W 257 [3, 5, 7, 11] (.B 257 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 367 (.B 383 (.B 431
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 431 (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L)))) (.B
  383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7, 17] .L) (.W 513
  [3, 5, 7, 17] .L))))))) (.W 257 [3, 5, 7, 11] (.B 257 (.B 367 (.B 383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3,
  5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L))))) (.B 367 (.B
  383 (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7, 17] .L) (.W 513 [3, 5, 7,
  17] .L))) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7, 17] .L) (.W 513
  [3, 5, 7, 17] .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3,
  5, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L))) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487
  (.W 513 [3, 5, 7, 17] .L) (.W 513 [3, 5, 7, 17] .L)))))))))) (.W 129 [5, 7, 11] (.B 137 (.B 191 (.W 257 [3, 5,
  11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))))) (.W 65
  [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5, 7] (.W 257 [3, 11, 13] .L)) (.W 129 [3, 5, 7] (.W 257 [3, 13]
  .L))) (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191
  (.W 257 [3, 5, 11, 13] (.B 257 (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W 513
  [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 383 (.W 513
  [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 283 (.B 367 (.B 383 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.W
  513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 383
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.W 257 [3, 5, 11, 13] .L)))) (.W 129 [3, 5, 7] (.B 137 (.B
  191 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11,
  13] .L)))))) (.B 107 (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))) (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W
  257 [3, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 191 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 11, 13] .L))))) (.B 127
  (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B 191 (.W 257
  [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)))) (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 5, 11,
  13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13]
  .L))))))))))) (.B 47 (.B 53 (.B 61 (.W 65 [3] (.B 127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 211 (.W 257 [3, 11]
  (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))
  (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))))) (.W
  257 [3, 11] (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L))))) (.B 137 (.B 211 (.W 257 [3, 5, 11] (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3, 5, 11] (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B
  191 (.B 211 (.W 257 [3, 5, 11] (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.W 257 [3, 5, 11] (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 211 (.W 257 [3, 5, 11] (.B 263 (.B 367 (.B
  421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 281 (.B 367
  (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))
  (.B 367 (.B 383 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L))) (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5,
  7] .L)))) (.B 383 (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L)))))))) (.W 257 [3, 5, 11] (.B 263 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 317 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))))))) (.W 129 [3, 5, 7, 11]
  (.B 131 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 137 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5,
  11] .L)) (.B 191 (.B 211 (.W 257 [3, 5, 11] (.B 367 (.B 421 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 421 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.W 257 [3, 5, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W
  257 [3, 5, 11] .L)))))))) (.W 65 [3] (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257
  [3, 11, 13] .L)) (.B 137 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.B 211 (.W
  257 [3, 5, 11, 13] (.B 367 (.B 421 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 421 (.W 513 [3, 5, 7] .L) (.W
  513 [3, 5, 7] .L)))) (.W 257 [3, 5, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L)))))) (.W 129 [3, 5, 7] (.B 131 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 137 (.B 211
  (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3,
  5, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))))))) (.B 61 (.W 65 [3, 5] (.B
  71 (.B 127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.W 257 [3, 11] (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 191 (.W 257 [3, 11] (.B 283 (.B 367 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 367 (.B 487 (.W 513
  [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))))) (.W 257 [3, 11] (.B 281 (.B
  283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B
  367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.B 283
  (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))))))))) (.B 137 (.B 191 (.W 257 [3, 5, 11] (.B 283 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)))) (.W 257 [3, 5, 11] (.B 263 (.B 283 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 281 (.B 283 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))) (.B 283 (.B 383 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7]
  .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.B 191 (.W 257 [3, 5, 11]
  (.B 263 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)))) (.B 281 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W
  513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487
  (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))))) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11]
  (.B 263 (.B 281 (.B 283 (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L))) (.B 367 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  7] .L)))) (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5,
  7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5,
  7] .L) (.W 513 [3, 5, 7] .L)))))) (.B 281 (.B 283 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 283 (.B 367 (.B 383 (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B
  487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B
  367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513
  [3, 5, 7] .L))))))))))))) (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.W 257 [3, 11] .L) (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3,
  5, 11] .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))))) (.B 107 (.B 127 (.W 129 [3, 5, 7, 11] (.B
  131 (.W 257 [3, 11] .L) (.B 137 (.W 257 [3, 5, 11] .L) (.B 191 (.W 257 [3, 5, 11] (.B 367 (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.W 257 [3, 5, 11] .L)))))
  (.W 129 [3, 5, 7, 11] (.B 131 (.W 257 [3, 11] .L) (.B 137 (.W 257 [3, 5, 11] .L) (.B 191 (.W 257 [3, 5, 11]
  .L) (.W 257 [3, 5, 11] .L)))))) (.B 127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] (.B 281
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487
  (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))))) (.W 257 [3, 11] (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W
  513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.B 191 (.W 257 [3, 11] (.B 281 (.B 367
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B
  367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3,
  5, 7] .L)))))) (.W 257 [3, 5, 11] (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3,
  5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L)
  (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))) (.B 137 (.B 191 (.B 197 (.W
  257 [3, 11] .L) (.W 257 [3, 5, 11] (.B 263 (.B 281 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 383 (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 383
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B
  487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))) (.B
  197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] (.B 263 (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7]
  .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 281 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513
  [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W
  513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W
  513 [3, 5, 7] .L))))))))) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] (.B 263 (.B 281 (.B 367 (.B
  383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L))) (.B 383
  (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367
  (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7]
  .L))))) (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7]
  .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3,
  5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B
  383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5,
  7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))))))) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5,
  7, 11] (.B 263 (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3,
  7] .L) (.W 513 [3, 5, 7] .L))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 367 (.B 383 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B
  431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)))) (.B 383
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L))
  (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))))) (.B 281 (.B 367 (.B 383 (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L)))) (.B 383 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 431 (.B 487 (.W 513
  [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L))))) (.B 367 (.B 383
  (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)))
  (.B 431 (.B 487 (.W 513 [3, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7, 17] .L) (.W 513 [3, 5, 7,
  17] .L)))) (.B 383 (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7] .L)
  (.W 513 [3, 5, 7] .L))) (.B 431 (.B 487 (.W 513 [3, 5, 7] .L) (.W 513 [3, 5, 7] .L)) (.B 487 (.W 513 [3, 5, 7,
  17] .L) (.W 513 [3, 5, 7, 17] .L))))))))))))) (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 137 (.B 191 (.B 197 (.W 257
  [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 191 (.B 197 (.W
  257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))))))) (.W 65
  [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.W 257 [3, 11, 13] .L) (.B 191 (.W 257 [3, 11, 13]
  .L) (.W 257 [3, 5, 11, 13] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B
  191 (.W 257 [3, 5, 11, 13] .L) (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))))) (.W 129 [3, 5,
  7] (.B 131 (.B 137 (.W 257 [3, 11, 13] .L) (.B 191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B
  137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.B 197
  (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))))) (.B 107 (.B 127 (.W 129 [3, 5, 7] (.B 131 (.W 257 [3,
  11, 13] .L) (.B 137 (.W 257 [3, 5, 11, 13] .L) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))))) (.W 129 [3, 5, 7] (.B 131 (.W 257 [3, 11, 13] .L) (.B 137 (.W 257 [3, 5, 11, 13] .L) (.B 191 (.W 257
  [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))))) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257
  [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))
  (.B 137 (.B 191 (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L)
  (.W 257 [3, 5, 11, 13] .L))) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197
  (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)))))) (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W
  257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11,
  13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))
  (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)))))))))))) (.B 53 (.B 61 (.W 65 [3, 5] (.B 71
  (.B 127 (.W 129 [3, 7, 11] (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))) (.W 129 [3, 7, 11] (.B 211
  (.W 257 [3, 5] .L) (.W 257 [3, 5] .L)))) (.B 127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 211 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L)) (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L)
  (.W 257 [3, 11] .L)))) (.B 137 (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 211 (.W 257
  [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197
  (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))))))
  (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 211 (.W 257 [3] .L) (.W 257 [3] .L)) (.B 191 (.B 211 (.W 257 [3] .L)
  (.W 257 [3] .L)) (.B 211 (.W 257 [3] .L) (.W 257 [3] .L)))) (.B 137 (.B 191 (.B 211 (.W 257 [3, 5] .L) (.W 257
  [3, 5] .L)) (.B 211 (.W 257 [3, 5] .L) (.W 257 [3, 5] .L))) (.B 191 (.B 211 (.W 257 [3, 5] .L) (.W 257 [3, 5]
  .L)) (.B 197 (.B 211 (.W 257 [3] .L) (.W 257 [3] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11]
  .L)))))))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 7] (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11,
  13] .L))) (.W 129 [3, 7] (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)))) (.B 127 (.W 129 [3, 5, 7]
  (.B 131 (.B 137 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 191 (.B 211 (.W 257 [3, 11, 13]
  .L) (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))) (.B 137 (.B 191
  (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3,
  5, 11, 13] .L))) (.B 191 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.B 211 (.W
  257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))))))) (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 211 (.W 257 [3, 13] .L) (.W 257 [3, 13] .L)) (.B 191 (.B 211
  (.W 257 [3, 13] .L) (.W 257 [3, 13] .L)) (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)))) (.B 137 (.B
  191 (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13]
  .L))) (.B 191 (.B 211 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 197 (.B 211 (.W 257 [3, 13] .L) (.W
  257 [3, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))))))))) (.B 61 (.W 65 [3, 5]
  (.B 71 (.B 107 (.B 127 (.W 129 [3, 7, 11] (.W 257 [3, 5, 11] .L)) (.W 129 [3, 7, 11] (.W 257 [3, 5] .L))) (.B
  127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3,
  11] .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3,
  5, 11] .L))) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257
  [3, 5, 11] .L)))))) (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 191 (.W 257 [3] .L) (.W 257 [3] .L)) (.B 191 (.W
  257 [3] .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5] .L) (.B 197 (.W 257 [3] .L) (.W 257 [3, 5,
  11] .L))) (.B 191 (.B 197 (.W 257 [3] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3] .L) (.W 257 [3, 5, 11]
  .L)))))))) (.B 107 (.B 127 (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.W 257 [3, 11] .L) (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3,
  5, 11] .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.W
  257 [3] .L) (.B 191 (.W 257 [3] .L) (.W 257 [3] .L))) (.B 137 (.B 191 (.W 257 [3, 5] .L) (.W 257 [3, 5] .L))
  (.B 191 (.W 257 [3, 5] .L) (.B 197 (.W 257 [3] .L) (.W 257 [3, 5, 11] .L))))))) (.B 127 (.W 129 [3, 5, 7, 11]
  (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3,
  5, 7, 11] .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11]
  .L) (.W 257 [3, 5, 7, 11] .L))) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197 (.W 257
  [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))) (.W 129 [3, 5, 7, 11] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.B 137 (.B 191 (.B 197
  (.W 257 [3] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.B 191 (.B
  197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11]
  .L)))))))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 7] (.W 257 [3, 5, 11, 13] .L)) (.W 129 [3, 7]
  (.W 257 [3, 5, 13] .L))) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11, 13] .L) (.W 257 [3,
  5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B 137 (.B 191 (.W 257 [3, 5,
  11, 13] .L) (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B 191 (.B 197 (.W 257 [3, 11, 13]
  .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))))) (.W 129 [3,
  5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 191 (.W 257 [3, 5, 13] .L) (.W
  257 [3, 5, 11, 13] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 13] .L) (.B 197 (.W 257 [3, 13] .L) (.W 257 [3, 5, 11,
  13] .L))) (.B 191 (.B 197 (.W 257 [3, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 13] .L) (.W
  257 [3, 5, 11, 13] .L)))))))) (.B 107 (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.W 257 [3, 11, 13] .L) (.B
  191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257
  [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L)))))) (.W 129 [3, 5, 7] (.B 131 (.B 137 (.W 257 [3, 13] .L) (.B 191 (.W 257 [3, 13] .L) (.W 257 [3, 5, 13]
  .L))) (.B 137 (.B 191 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 13] .L)) (.B 191 (.W 257 [3, 5, 13] .L) (.B 197
  (.W 257 [3, 13] .L) (.W 257 [3, 5, 11, 13] .L))))))) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257
  [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13]
  .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5,
  11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11,
  13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)))))) (.W 129 [3, 5, 7] (.B 131 (.B
  137 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257
  [3, 5, 7, 11, 13] .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 5, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W
  257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3,
  5, 7, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))))))))))))))) (.W 33 [3]
  (.B 43 (.B 47 (.B 53 (.W 65 [3] (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11]
  .L)) (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11]
  .L))))) (.W 129 [3, 5, 7] (.B 137 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.B 211 (.W 257 [3,
  11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))))))) (.W 65 [3, 5] (.B 71 (.B
  127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W
  257 [3, 11] .L)))) (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257
  [3, 11] .L) (.W 257 [3, 11] .L))))) (.B 107 (.B 127 (.W 129 [3, 5, 7] (.B 137 (.W 257 [3, 11] .L) (.B 191 (.W
  257 [3, 11] .L) (.W 257 [3, 11] .L)))) (.W 129 [3, 5, 7] (.B 137 (.W 257 [3, 11] .L) (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L))))) (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11]
  .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)))) (.W 129 [3, 5, 7] (.B 137 (.B 191 (.W 257 [3,
  11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))))))))) (.B 53 (.W 65
  [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7] (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.W 129 [3, 5, 7]
  .L)) (.B 127 (.W 129 [3, 5, 7] (.B 137 (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W
  257 [3, 11] .L) (.W 257 [3, 11] .L))) (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257
  [3, 11] .L) (.W 257 [3, 11] .L))))) (.W 129 [3, 5, 7] .L)))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [5,
  7] (.W 257 [3, 11] .L)) (.W 129 [5, 7] .L)) (.B 127 (.W 129 [5, 7] (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257
  [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)))) (.W 129 [5, 7] (.B 137 (.B 191 (.W 257 [3]
  .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.B 107 (.B 127 (.W 129 [5,
  7] (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))))
  (.W 129 [5, 7] .L)) (.B 127 (.W 129 [5, 7] (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))
  (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L)))) (.W 129 [5, 7] (.B 137 (.B 191 (.W 257 [3, 5,
  11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))))))) (.B 47
  (.B 53 (.W 65 [3] (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 137
  (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5,
  11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 7] .L))) (.W 65 [3, 5] (.B
  71 (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.W 257 [3, 11] .L) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11]
  .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.B 197
  (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 7] (.B 131 (.B 137 (.W 257 [3, 11] .L) (.B 191
  (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B
  191 (.W 257 [3, 5, 11] .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))))) (.B 107 (.B 127 (.W 129
  [3, 5, 7] (.B 131 (.W 257 [3, 11] .L) (.B 137 (.W 257 [3, 5, 11] .L) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257
  [3, 5, 11] .L))))) (.W 129 [3, 5, 7] .L)) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 137 (.B 191 (.B 197 (.W 257
  [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 191 (.B 197 (.W
  257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))) (.W 129 [3,
  5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3,
  5, 11] .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L)
  (.W 257 [3, 5, 11] .L))) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11]
  .L) (.W 257 [3, 5, 7, 11] .L))))))))))) (.B 53 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7]
  .L)) (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L)))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3,
  7] .L) (.W 129 [3, 7] .L)) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3,
  11] .L)) (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.B 137 (.B 191 (.W 257 [3, 5, 11] .L) (.B 197 (.W
  257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197
  (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 7] .L))) (.B 107 (.B 127 (.W 129 [3, 5, 7] .L)
  (.W 129 [3, 5, 7] .L)) (.B 127 (.W 129 [3, 5, 7] (.B 131 (.B 137 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5,
  11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.B 137 (.B 191 (.B 197 (.W 257 [3, 11]
  .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.B 191 (.B 197 (.W 257
  [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)))))) (.W 129
  [3, 5, 7] .L)))))))))) (.B 31 (.W 33 [3] (.B 43 (.B 47 (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3,
  5, 11] (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.W 129 [3, 5, 11] (.B 211 (.W 257 [3, 11] .L) (.W
  257 [3, 11] .L)))) (.B 127 (.W 129 [3, 5, 11] (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211
  (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)))) (.W 129 [3, 5, 11] (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3,
  11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5] (.B
  211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L))) (.W 129 [3, 5] (.B 211 (.W 257 [3, 11, 13] .L) (.W 257
  [3, 11, 13] .L)))) (.B 127 (.W 129 [3, 5] (.B 191 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))) (.W 129 [3, 5] (.B 191 (.B 211 (.W 257
  [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L)))))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5, 11] (.W 257 [3, 11] .L)) (.W 129 [3, 5,
  11] (.W 257 [3, 11] .L))) (.B 127 (.W 129 [3, 5, 11] (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.W
  129 [3, 5, 11] (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))) (.B 107 (.B 127 (.W 129 [3, 5, 11] (.B
  191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.W 129 [3, 5, 11] (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11]
  .L)))) (.B 127 (.W 129 [3, 5, 11] (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.W 129 [3, 5,
  11] (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W
  129 [3, 5] (.W 257 [3, 11, 13] .L)) (.W 129 [3, 5] (.W 257 [3, 11, 13] .L))) (.B 127 (.W 129 [3, 5] (.B 191
  (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W
  257 [3, 5, 11, 13] .L))))) (.B 107 (.B 127 (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5,
  11, 13] .L))) (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))) (.B 127 (.W 129
  [3, 5] (.B 191 (.W 257 [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))) (.W 129 [3, 5] (.B 191 (.W 257
  [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))))))))) (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129
  [3, 5, 11] (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3,
  11] .L)))) (.W 129 [3, 5, 11] (.B 191 (.B 211 (.W 257 [3] .L) (.W 257 [3] .L)) (.B 211 (.W 257 [3] .L) (.W 257
  [3] .L))))) (.B 107 (.B 127 (.W 129 [3, 5, 11] (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.W 129 [3,
  5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W
  257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))) (.W 129 [3, 5, 11] (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257
  [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129
  [3, 5] (.B 191 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W
  257 [3, 5, 11, 13] .L)))) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127
  (.W 129 [3, 5] (.B 191 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 211 (.W 257 [3, 5,
  11, 13] .L) (.W 257 [3, 5, 11, 13] .L)))) (.W 129 [3, 5] .L)))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127
  (.W 129 [5, 11] (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.W 129 [5, 11] (.B 191 (.W 257 [3] .L) (.W
  257 [3] .L)))) (.B 127 (.W 129 [5, 11] (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.W 129 [5,
  11] (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L))))) (.B 107 (.B 127 (.W 129 [5, 11] (.B 191 (.W
  257 [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.W 129 [5, 11] (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))
  (.B 127 (.W 129 [5, 11] (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.W 129 [5, 11] (.B 191
  (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5]
  (.B 191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] (.B
  191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))) (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 11, 13]
  .L) (.W 257 [3, 5, 7, 11, 13] .L))))) (.B 107 (.B 127 (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W
  257 [3, 5, 11, 13] .L))) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 7, 11, 13] .L) (.W
  257 [3, 5, 7, 11, 13] .L))) (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13]
  .L)))))))))) (.B 47 (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 11] (.B 211 (.W 257 [3, 5, 11] .L)
  (.W 257 [3, 5, 11] .L))) (.W 129 [3, 11] (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))) (.B 127 (.W
  129 [3, 5, 11] (.B 131 (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L)
  (.W 257 [3, 11] .L))) (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.B 211 (.W 257
  [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 11]
  (.B 131 (.B 191 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11]
  .L))) (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.B 211 (.W 257 [3, 11] .L) (.W
  257 [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))))))))) (.W 65 [3, 5] (.B 71 (.B 127
  (.W 129 [3] (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))) (.W 129 [3] .L)) (.B 127 (.W 129
  [3, 5] (.B 131 (.B 191 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13]
  .L) (.W 257 [3, 5, 11, 13] .L))) (.B 191 (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B
  197 (.B 211 (.W 257 [3, 11, 13] .L) (.W 257 [3, 11, 13] .L)) (.B 211 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5,
  11, 13] .L)))))) (.W 129 [3, 5] .L))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 11] (.W 257
  [3, 5, 11] .L)) (.W 129 [3, 11] .L)) (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11] .L) (.W 257
  [3, 11] .L)) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257
  [3, 5, 11] .L))))) (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.B 197
  (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))))) (.B 107
  (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 5, 11]
  .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))))) (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L)) (.B 191 (.W 257 [3, 5, 11] .L) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11]
  .L)))))) (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191
  (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11]
  .L))))) (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.B 197
  (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11]
  .L))))))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3] (.W 257 [3, 5, 11, 13] .L)) (.W 129 [3] .L)) (.B
  127 (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.B 197 (.W
  257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))))) (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 191 (.B 197
  (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13]
  .L))))))) (.B 107 (.B 127 (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))
  (.B 191 (.W 257 [3, 5, 11, 13] .L) (.B 197 (.W 257 [3, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L))))) (.W 129 [3,
  5] .L)) (.B 127 (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B
  191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W
  257 [3, 5, 7, 11, 13] .L))))) (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11,
  13] .L)) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11,
  13] .L) (.W 257 [3, 5, 7, 11, 13] .L))))))))))) (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 11]
  (.B 131 (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L)) (.B 191 (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5,
  11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))))) (.W 129 [3, 5, 11] .L)) (.B 107 (.B 127 (.W
  129 [3, 11] .L) (.W 129 [3, 11] .L)) (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.B 211 (.W 257 [3, 11] .L)
  (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 11] .L) (.W 257 [3, 11] .L))) (.B 191 (.B 197 (.B 211 (.W 257 [3, 11]
  .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))) (.B 197 (.B 211 (.W 257 [3,
  11] .L) (.W 257 [3, 11] .L)) (.B 211 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L)))))) (.W 129 [3, 5, 11]
  .L))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129 [3] .L)
  (.W 129 [3] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B
  127 (.W 129 [3, 5, 11] (.B 131 (.W 257 [3, 11] .L) (.B 191 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 11] .L))))
  (.W 129 [3, 5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L))
  (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 7, 11]
  .L))))) (.W 129 [3, 5, 11] .L))) (.B 107 (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 11] .L) (.W
  257 [3, 11] .L)) (.B 191 (.B 197 (.W 257 [3, 11] .L) (.W 257 [3, 5, 11] .L)) (.B 197 (.W 257 [3, 11] .L) (.W
  257 [3, 5, 11] .L))))) (.W 129 [3, 5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 5, 7,
  11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197
  (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))))) (.W 129 [3, 5, 11] (.B 131 (.B 191 (.W 257 [3, 5, 7,
  11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.B 197 (.W 257 [3, 5, 11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 197
  (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))))))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3,
  5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5,
  11, 13] .L)) (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 11,
  13] .L) (.W 257 [3, 5, 7, 11, 13] .L))))) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3,
  5] .L)) (.B 127 (.W 129 [3, 5] (.B 131 (.B 191 (.W 257 [3, 5, 7, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L))
  (.B 191 (.B 197 (.W 257 [3, 5, 11, 13] .L) (.W 257 [3, 5, 7, 11, 13] .L)) (.B 197 (.W 257 [3, 5, 7, 11, 13]
  .L) (.W 257 [3, 5, 7, 11, 13] .L))))) (.W 129 [3, 5] .L)))))))))) (.W 33 [3] (.B 43 (.B 47 (.B 53 (.W 65 [3,
  5] (.B 71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))) (.W
  65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] (.B 191 (.W 257
  [3, 11] .L) (.W 257 [3, 5, 11] .L))) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5]
  .L)) (.B 127 (.W 129 [3, 5] (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L))) (.W 129 [3, 5]
  .L)))))) (.B 53 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129
  [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))))) (.W 65 [3, 5] (.B 71 (.B 107
  (.B 127 (.W 129 [5] .L) (.W 129 [5] .L)) (.B 127 (.W 129 [5] .L) (.W 129 [5] .L))) (.B 107 (.B 127 (.W 129 [5]
  .L) (.W 129 [5] .L)) (.B 127 (.W 129 [5] .L) (.W 129 [5] .L))))))) (.B 47 (.B 53 (.W 65 [3, 5] (.B 71 (.B 127
  (.W 129 [3] .L) (.W 129 [3] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))) (.W 65 [3, 5] (.B 71 (.B 107
  (.B 127 (.W 129 [3] .L) (.W 129 [3] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W
  129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))))) (.B 53 (.W 65 [3, 5] (.B
  71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129 [3] .L) (.W 129 [3] .L)) (.B 127 (.W
  129 [3, 5] .L) (.W 129 [3, 5] .L))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5]
  .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))
  (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))))))))))) (.W 17 [3] (.B 23 (.B 31 (.W 33 [] (.B 47 (.B 53 (.B
  61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 7, 11] .L) (.W 129 [3, 7, 11] .L)) (.B 127 (.W 129 [3, 5, 7, 11]
  .L) (.W 129 [3, 5, 7, 11] .L)))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7] .L)) (.B 127
  (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 7, 11]
  .L) (.W 129 [3, 7, 11] .L)) (.B 127 (.W 129 [3, 5, 7, 11] .L) (.W 129 [3, 5, 7, 11] .L))) (.B 107 (.B 127 (.W
  129 [3, 5, 7, 11] .L) (.W 129 [3, 5, 7, 11] .L)) (.B 127 (.W 129 [3, 5, 7, 11] (.B 137 (.B 191 (.W 257 [3, 5,
  11] .L) (.W 257 [3, 5, 7, 11] .L)) (.B 191 (.W 257 [3, 5, 7, 11] .L) (.W 257 [3, 5, 7, 11] .L)))) (.W 129 [3,
  5, 7, 11] .L))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7] .L)) (.B 127 (.W 129
  [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))) (.B 107 (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L)) (.B 127 (.W
  129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))))))) (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7, 11]
  .L) (.W 129 [3, 5, 7, 11] .L)) (.B 107 (.B 127 (.W 129 [3, 7, 11] .L) (.W 129 [3, 7, 11] .L)) (.B 127 (.W 129
  [3, 5, 7, 11] .L) (.W 129 [3, 5, 7, 11] .L))))) (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3,
  5, 7] .L)) (.B 107 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7] .L)) (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5,
  7] .L)))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [5, 7, 11] .L) (.W 129 [5, 7, 11] .L)) (.B 127
  (.W 129 [5, 7, 11] .L) (.W 129 [5, 7, 11] .L))) (.B 107 (.B 127 (.W 129 [5, 7, 11] .L) (.W 129 [5, 7, 11] .L))
  (.B 127 (.W 129 [5, 7, 11] .L) (.W 129 [5, 7, 11] .L))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5,
  7] .L) (.W 129 [3, 5, 7] .L)) (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))) (.B 107 (.B 127 (.W 129
  [3, 5, 7] .L) (.W 129 [3, 5, 7] .L)) (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))))))))) (.W 33 [] (.B
  47 (.B 53 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7] .L)) (.B 127 (.W 129 [3, 5, 7] .L)
  (.W 129 [3, 5, 7] .L)))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 7] .L) (.W 129 [3, 7] .L)) (.B 127
  (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L))) (.B 107 (.B 127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L)) (.B
  127 (.W 129 [3, 5, 7] .L) (.W 129 [3, 5, 7] .L)))))) (.B 53 (.W 65 [3, 5] .L) (.W 65 [3, 5] (.B 71 (.B 107 (.B
  127 (.W 129 [5, 7] .L) (.W 129 [5, 7] .L)) (.B 127 (.W 129 [5, 7] .L) (.W 129 [5, 7] .L))) (.B 107 (.B 127 (.W
  129 [5, 7] .L) (.W 129 [5, 7] .L)) (.B 127 (.W 129 [5, 7] .L) (.W 129 [5, 7] .L))))))))) (.B 31 (.W 33 [] (.B
  47 (.B 53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L)) (.B 107 (.B 127
  (.W 129 [3, 11] .L) (.W 129 [3, 11] .L)) (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L))))) (.W 65 [3,
  5] (.B 71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129 [3] .L) (.W 129 [3] .L)) (.B
  127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5, 11]
  .L) (.W 129 [3, 5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L))) (.B 107 (.B 127 (.W 129
  [3, 5, 11] .L) (.W 129 [3, 5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L))))) (.W 65 [3, 5]
  (.B 71 (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))
  (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))))))) (.B
  53 (.B 61 (.W 65 [3, 5] (.B 71 (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L)) (.B 107 (.B 127 (.W 129
  [3, 5, 11] .L) (.W 129 [3, 5, 11] .L)) (.B 127 (.W 129 [3, 5, 11] .L) (.W 129 [3, 5, 11] .L))))) (.W 65 [3, 5]
  (.B 71 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))
  (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)))))) (.B 61 (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [5, 11]
  .L) (.W 129 [5, 11] .L)) (.B 127 (.W 129 [5, 11] .L) (.W 129 [5, 11] .L))) (.B 107 (.B 127 (.W 129 [5, 11] .L)
  (.W 129 [5, 11] .L)) (.B 127 (.W 129 [5, 11] .L) (.W 129 [5, 11] .L))))) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127
  (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W 129
  [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L))))))))) (.W 33 [] (.B 47 (.B 53
  (.W 65 [3, 5] .L) (.W 65 [3, 5] (.B 71 (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129
  [3, 5] .L) (.W 129 [3, 5] .L))) (.B 107 (.B 127 (.W 129 [3, 5] .L) (.W 129 [3, 5] .L)) (.B 127 (.W 129 [3, 5]
  .L) (.W 129 [3, 5] .L)))))) (.B 53 (.W 65 [3, 5] .L) (.W 65 [3, 5] .L)))))))))

-- Section 8. The step.

set_option maxHeartbeats 20000000 in
theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  refine ⟨0, fun n h hiff he ha4 hlo _ => ?_⟩
  exfalso
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he, ha] at E
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) = P at hP E h3P
  generalize padicValNat 2 n = m at E ha4 hlo
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 3) (e := 11) (by norm_num)) E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one ha4
  have h67d : 67 ∣ 1 + 3 ^ 11 := by norm_num
  have h661d : 661 ∣ 1 + 3 ^ 11 := by norm_num
  have g5 := S2 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) h5m
  have g67 := S7 67 (by norm_num) (by norm_num) (hn3 (by norm_num)) h67d
  have g661 := S7 661 (by norm_num) (by norm_num) (hn3 (by norm_num)) h661d
  have g17 := S1 17 (by norm_num) (by norm_num) (hn3 (by norm_num)) 67 g67 (by norm_num)
  have g331 := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 661 g661 (by norm_num)
  have g83 := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have g7 := S1 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) 83 g83 (by norm_num)
  have hled : ¬ 3 ^ 12 ∣ ∏ p ∈ P, (p + 1) := fun hd => by
    have h1 : 3 ^ 11 * 3 ∣ (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) :=
      (show 3 ^ 11 * 3 = 3 ^ 12 by norm_num) ▸ hd.mul_left _
    rw [E] at h1
    have h2 : 3 ^ 11 * 3 ∣ 3 ^ 11 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
      have e : 3 ^ 11 * (2 ^ (m + 1) * ∏ p ∈ P, p) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p := by ring
      rw [e]
      exact h1
    have h3 : 3 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h4 | h4
    · have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4)
      omega
    · obtain ⟨p, hp, hpd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h4
      have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp hpd
      exact h3P (h5 ▸ hp)
  have e1 : (1 + 3 ^ 11 : ℕ) = 177148 := by norm_num
  have e2 : (3 ^ 11 : ℕ) = 177147 := by norm_num
  have C : Ctx P m :=
    { hP := hP
      E := by
        rw [e1, e2] at E
        exact E
      s1 := fun c hc hc2 hc3 p hp hd => S1 c hc hc2 (hn3 hc3) p hp hd
      s3 := fun c hc hc2 hc3 p hp p' hp' hd hd' => S3 c hc hc2 (hn3 hc3) p hp p' hp' hd hd'
      s6 := fun c hc hc2 hc3 p hp => S6 c hc hc2 (hn3 hc3) p hp
      hcl := fun p hp => ⟨S4 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) h5m p hp,
        S8 67 (by norm_num) (by norm_num) (hn3 (by norm_num)) h67d p hp,
        S8 661 (by norm_num) (by norm_num) (hn3 (by norm_num)) h661d p hp⟩
      led := hled
      hm := by omega }
  refine sound C tree [5, 7, 17, 67, 83, 331, 661] [] 5 (by decide +kernel)
    ⟨fun x hx => ?_, by decide, fun y hy => by simp at hy, fun p hp hp5 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · have hpp := (hP p hp).1
    have hp2 := (hP p hp).2
    interval_cases p <;> first | exact absurd rfl hp2 | exact absurd hp h3P | exact absurd hpp (by norm_num)

end OMA.P_Erdos1052_z3_e11_c2

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 :=
  OMA.P_Erdos1052_z3_e11_c2.step_proof
