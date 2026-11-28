import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1.H2

Hypothesis H2 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1`: unitary perfect numbers
`n = 2 ^ a * 5 ^ 2 * (simple odd primes)` such that `23 ∣ n` have `a ≤ 63`.

Credit: @aroth01. The base lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...)
are those of reductions `...R1.H2.R1.H1.R1` and `...R1.H2.R1.H1.R1.H2.R1`.

Setting. `P` is the set of simple odd primes (5 is not one of them). `13 ∣ 1 + 5 ^ 2` is a simple prime that
divides no `p + 1`, and `7` divides only `13 + 1`. Then `23` and `3` (which divides `23 + 1`) are simple primes. Every simple prime `p` has
`p + 1 = 2 ^ i * 5 ^ j * d` with `d` a product of distinct simple primes, each dividing only this `p + 1`. Ledger:
`5 ^ 3` does not divide the product of the `p + 1`. Balance: the product of the `1 + 1 / p` times
`(1 + 1 / 2 ^ a) * (26 / 25)` is `2`.

Proof. A search over statements `St P X Y N`: the members of the list `X` are simple primes, those of `Y` are
not, and every simple prime below `N` is in `X`.
* `cand_mem` / `extend`: a simple prime `p` of the window `[N, 2 * N - 1)` outside `X` has all the odd prime factors
  of `p + 1` below `N`, hence in `X` and open (dividing no `x + 1` with `x` in `X`), so `p` is one of the finitely
  many candidates `2 ^ i * 5 ^ j * d - 1`; and it is not `dead` (a candidate is dead when it is in `X` or `Y` or
  fails a small-factor or Fermat test, which a prime passes).
* `up_kill`: the weight of `X` alone is at least `2`.
* `low_kill`: the unknown simple primes are at least `N` and lie on disjoint paths (`path_bound`) that start at a
  parent of an open member of `X`, at a prime `q` with `5 ∣ q + 1` (the ledger bounds their number) or at a
  Mersenne prime (`tail_bound`); so their weight is at most
  `((N + 1) / (N - 1)) ^ (opens + ledger) * (N + 1) / (N - 3)`, which is too small.
* `search` runs this as a program: it splits on the least live candidate `y` (with `y` the closure moves to `y`,
  without it the search stays in the window), and `sound` proves that `search ... = true` refutes the state.
The kernel evaluates the search (`decide +kernel`). To keep each evaluation small the search is cut into 75
pieces (Section 7): a piece stops at the states (`holes`) where other pieces start. The cut was computed by a
script; nothing about it is trusted.
-/

namespace OMA.P_Erdos1052_z5_e2_part2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts path_bound tail_bound exists_child two_mul_le B_step B_anti
  B_nonneg one_add_le_B kernel_balance_one two_pow_of_no_odd_prime five_dvd_two_pow_add_one prime_dvd_prime_pow)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- Section 1. The checks, as computable functions on lists of numbers.

/-- The products of the sublists of a list that are at most `N`. -/
def subProdsLe (N : ℕ) : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProdsLe N t ++ ((subProdsLe N t).map (fun d => c * d)).filter (fun d => decide (d ≤ N))

/-- `powMod v f b e` is `b ^ e % v` when `e < 256 ^ f` (eight bits of the exponent at a time, so that the kernel
does the arithmetic on numerals). -/
def powMod (v : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % v
  | f + 1, b, e => (powMod v f b (e / 256)) ^ 256 * b ^ (e % 256) % v

/-- A certificate that the number `v` is not prime: a small proper factor, or the failure of Fermat's test to the
base 2 or 3. -/
def comp (v : ℕ) : Bool :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47].any (fun q => v % q == 0 && Nat.blt q v) ||
    (Nat.blt v (2 ^ 64) &&
      (powMod v 8 2 (v - 1) != 1 % v || (Nat.blt 3 v && powMod v 8 3 (v - 1) != 1 % v)))

/-- The open members of `X`: not closed, and dividing no `x + 1` with `x` in `X`. -/
def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 13 && X.all (fun x => (x + 1) % c != 0))

/-- The open members of `y :: X` from those of `X`. -/
def opensCons (y : ℕ) (X O : List ℕ) : List ℕ :=
  (if y != 13 && (y :: X).all (fun x => (x + 1) % y != 0) then [y] else []) ++
    O.filter (fun c => (y + 1) % c != 0)

/-- The product of the `x + 1`. -/
def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

/-- The candidates of the window `[N, 2 * N - 1)`: for `5 ^ j` allowed by the ledger and `d` a product of
distinct open members of `X` with `5 ^ j * d ≤ N`, the only number `2 ^ i * 5 ^ j * d - 1` in `[N, 2 * N)`. -/
def candsA (O : List ℕ) (S N : ℕ) : List ℕ :=
  (((List.range 3).filter (fun j => (5 ^ j * S) % 5 ^ 3 != 0)).flatMap (fun j =>
    (subProdsLe (N / 5 ^ j) O).map (fun d =>
      2 ^ (Nat.log2 (N / (5 ^ j * d)) + 1) * (5 ^ j * d) - 1))).filter (fun v => Nat.blt (v + 1) (2 * N))

/-- The candidates of the state `X`. -/
def cands (X : List ℕ) (N : ℕ) : List ℕ := candsA (opens X) (succProd X) N

/-- Membership in a list, as a computation on numerals. -/
def memB (v : ℕ) : List ℕ → Bool
  | [] => false
  | x :: t => Nat.beq v x || memB v t

/-- A candidate that needs no attention: zero, certainly not prime, known, or excluded. -/
def dead (X Y : List ℕ) (v : ℕ) : Bool :=
  v == 0 || comp v || memB v X || memB v Y

/-- The least member of a list, if any. -/
def minOpt : List ℕ → Option ℕ
  | [] => none
  | v :: t => match minOpt t with
    | none => some v
    | some u => some (min v u)

/-- The least member of `l` that is not dead, with the members of `l` above it (the candidates are looked at in
increasing order, so that the expensive test `comp` is run on few of them). -/
def firstLive (X Y : List ℕ) : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | f + 1, l => match minOpt l with
    | none => none
    | some v => if dead X Y v then firstLive X Y f (l.filter (fun u => u != v))
      else some (v, l.filter (fun u => u != v))

/-- The weight of `X` alone is already too large. -/
def upOkA (Pi S : ℕ) : Bool := Nat.ble (2 * 25 * Pi) (26 * S)

/-- The weight of `X` alone is already too large. -/
def upOk (X : List ℕ) : Bool := upOkA X.prod (succProd X)

/-- How many more simple primes `q` can have `5 ∣ q + 1`. -/
def ledgerLeftA (S : ℕ) : ℕ :=
  if (5 ^ 1 * S) % 5 ^ 3 == 0 then 0 else if (5 ^ 2 * S) % 5 ^ 3 == 0 then 1 else 2

/-- How many more simple primes `q` can have `5 ∣ q + 1`. -/
def ledgerLeft (X : List ℕ) : ℕ := ledgerLeftA (succProd X)

/-- The weight of `X` together with everything that can still come above `N` is too small. -/
def lowOkA (O : List ℕ) (S Pi N : ℕ) : Bool :=
  Nat.ble 5 N &&
    Nat.blt ((2 ^ 64 + 1) * 26 * S * (N + 1) ^ (O.length + ledgerLeftA S + 1))
      (2 * 2 ^ 64 * 25 * Pi * (N - 1) ^ (O.length + ledgerLeftA S) * (N - 3))

/-- The weight of `X` together with everything that can still come above `N` is too small. -/
def lowOk (X : List ℕ) (N : ℕ) : Bool := lowOkA (opens X) (succProd X) X.prod N

-- Section 2. The setting and the state of the search.

/-- What is known about the set `P` of simple odd primes. -/
structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 26 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  hc13 : ∀ p ∈ P, ¬ 13 ∣ p + 1
  led : ¬ 5 ^ 3 ∣ ∏ p ∈ P, (p + 1)
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

theorem mem_subProdsLe (N : ℕ) : ∀ (l : List ℕ), (∀ c ∈ l, c.Prime) → ∀ d : ℕ, d ∣ l.prod → d ≤ N →
    d ∈ subProdsLe N l
  | [], _, d, hd, _ => by
    rw [List.prod_nil, Nat.dvd_one] at hd
    rw [hd]
    exact List.mem_singleton.mpr rfl
  | c :: t, hl, d, hd, hdN => by
    have hc : c.Prime := hl c List.mem_cons_self
    have ht : ∀ x ∈ t, x.Prime := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.prod_cons] at hd
    unfold subProdsLe
    rw [List.mem_append, List.mem_filter, List.mem_map]
    by_cases hcd : c ∣ d
    · obtain ⟨d', rfl⟩ := hcd
      have hd'N : d' ≤ N := (Nat.le_mul_of_pos_left d' hc.pos).trans hdN
      exact Or.inr ⟨⟨d', mem_subProdsLe N t ht d' (Nat.dvd_of_mul_dvd_mul_left hc.pos hd) hd'N, rfl⟩,
        decide_eq_true hdN⟩
    · have hcop : Nat.Coprime d c := ((Nat.Prime.coprime_iff_not_dvd hc).mpr hcd).symm
      rw [mul_comm] at hd
      exact Or.inl (mem_subProdsLe N t ht d (Nat.Coprime.dvd_of_dvd_mul_right hcop hd) hdN)

theorem powMod_eq (v : ℕ) : ∀ (f b e : ℕ), e < 256 ^ f → powMod v f b e = b ^ e % v
  | 0, b, e, h => by
    have he : e = 0 := by
      rw [pow_zero] at h
      omega
    rw [he, pow_zero]
    rfl
  | f + 1, b, e, h => by
    have hlt : e / 256 < 256 ^ f := by
      rw [pow_succ] at h
      omega
    unfold powMod
    rw [powMod_eq v f b (e / 256) hlt]
    conv_rhs => rw [← Nat.div_add_mod e 256, pow_add, pow_mul']
    rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem not_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : comp p = false := by
  have hfermat : ∀ b : ℕ, b.Prime → b ≠ p → b ^ (p - 1) % p = 1 % p := fun b hb hbp => by
    have hcop : Nat.Coprime b p := (Nat.coprime_primes hb hp).mpr hbp
    have h := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime hp] at h
    exact h
  have hsm : ∀ q ∈ [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47], 1 < q := by decide
  unfold comp
  rw [Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false]
    intro q hq hc
    rw [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hc
    have hq1 : 1 < q := hsm q hq
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hc.1) with h | h <;> omega
  · rw [Bool.and_eq_false_iff]
    by_cases hlt : p < 2 ^ 64
    · right
      have hfuel : p - 1 < 256 ^ 8 := by
        norm_num at hlt ⊢
        omega
      rw [Bool.or_eq_false_iff, powMod_eq p 8 2 (p - 1) hfuel, hfermat 2 Nat.prime_two (Ne.symm hp2)]
      refine ⟨bne_self_eq_false' .., ?_⟩
      rw [Bool.and_eq_false_iff]
      by_cases h3 : 3 < p
      · right
        rw [powMod_eq p 8 3 (p - 1) hfuel, hfermat 3 Nat.prime_three (by omega)]
        exact bne_self_eq_false' ..
      · left
        by_contra hb
        rw [Bool.not_eq_false, Nat.blt_eq] at hb
        exact h3 hb
    · left
      by_contra hb
      rw [Bool.not_eq_false, Nat.blt_eq] at hb
      exact hlt hb

theorem minOpt_none : ∀ l : List ℕ, minOpt l = none → l = []
  | [], _ => rfl
  | v :: t, h => by
    unfold minOpt at h
    split at h <;> exact absurd h (by simp)

theorem minOpt_some : ∀ (l : List ℕ) (y : ℕ), minOpt l = some y → y ∈ l ∧ ∀ v ∈ l, y ≤ v
  | [], y, h => by simp [minOpt] at h
  | v :: t, y, h => by
    unfold minOpt at h
    split at h
    · rename_i hn
      have ht := minOpt_none t hn
      rw [Option.some.injEq] at h
      subst h
      subst ht
      exact ⟨List.mem_cons_self, fun w hw => by rw [List.mem_singleton.mp hw]⟩
    · rename_i u hu
      obtain ⟨hut, hmin⟩ := minOpt_some t u hu
      rw [Option.some.injEq] at h
      subst h
      refine ⟨?_, fun w hw => ?_⟩
      · rcases Nat.le_total v u with hvu | huv
        · rw [Nat.min_eq_left hvu]
          exact List.mem_cons_self
        · rw [Nat.min_eq_right huv]
          exact List.mem_cons_of_mem _ hut
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact Nat.min_le_left _ _
        · exact (Nat.min_le_right _ _).trans (hmin w hw)

theorem memB_iff (v : ℕ) : ∀ l : List ℕ, memB v l = true ↔ v ∈ l
  | [] => by simp [memB]
  | x :: t => by
    unfold memB
    rw [Bool.or_eq_true, memB_iff v t, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (h ▸ Nat.beq_refl v)
      · exact Or.inr h

theorem dead_cons {X Y : List ℕ} {y v : ℕ} (h : dead X (y :: Y) v = false) : dead X Y v = false ∧ v ≠ y := by
  unfold dead at h ⊢
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h ⊢
  have h2 : ¬ v ∈ y :: Y := fun hm => by
    rw [(memB_iff v (y :: Y)).mpr hm] at h
    exact absurd h.2 (by simp)
  refine ⟨⟨h.1, ?_⟩, fun hvy => h2 (hvy ▸ List.mem_cons_self)⟩
  by_contra hc
  rw [Bool.not_eq_false, memB_iff] at hc
  exact h2 (List.mem_cons_of_mem _ hc)

theorem firstLive_some (X Y : List ℕ) : ∀ (f : ℕ) (l : List ℕ) (y : ℕ) (r : List ℕ),
    firstLive X Y f l = some (y, r) →
    y ∈ l ∧ dead X Y y = false ∧ (∀ v ∈ l, dead X Y v = false → y ≤ v) ∧
      (∀ v ∈ l, dead X Y v = false → v ≠ y → v ∈ r) ∧ ∀ v ∈ r, v ∈ l
  | 0, _, _, _, h => by simp [firstLive] at h
  | f + 1, l, y, r, h => by
    unfold firstLive at h
    split at h
    · exact absurd h (by simp)
    · rename_i v hv
      obtain ⟨hvl, hvmin⟩ := minOpt_some l v hv
      split_ifs at h with hd
      · obtain ⟨hy, hyd, hymin, hrest, hsub⟩ := firstLive_some X Y f _ y r h
        have hne : ∀ w ∈ l, dead X Y w = false → (w != v) = true := fun w _ hwd => by
          rw [bne_iff_ne]
          rintro rfl
          rw [hd] at hwd
          exact absurd hwd (by simp)
        exact ⟨(List.mem_filter.mp hy).1, hyd,
          fun w hw hwd => hymin w (List.mem_filter.mpr ⟨hw, hne w hw hwd⟩) hwd,
          fun w hw hwd hwy => hrest w (List.mem_filter.mpr ⟨hw, hne w hw hwd⟩) hwd hwy,
          fun w hw => (List.mem_filter.mp (hsub w hw)).1⟩
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hvl, by simpa using hd, fun w hw _ => hvmin w hw,
          fun w hw _ hwy => List.mem_filter.mpr ⟨hw, by rw [bne_iff_ne]; exact hwy⟩,
          fun w hw => (List.mem_filter.mp hw).1⟩

theorem firstLive_none (X Y : List ℕ) : ∀ (f : ℕ) (l : List ℕ), l.length < f → firstLive X Y f l = none →
    ∀ v ∈ l, dead X Y v = true
  | 0, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, l, hf, h => by
    unfold firstLive at h
    split at h
    · rename_i hn
      rw [minOpt_none l hn]
      intro v hv
      exact absurd hv List.not_mem_nil
    · rename_i v hv
      obtain ⟨hvl, -⟩ := minOpt_some l v hv
      split_ifs at h with hd
      · have hlen : (l.filter (fun u => u != v)).length < l.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨v, hvl, by simp⟩
        have ih := firstLive_none X Y f _ (by omega) h
        intro w hw
        by_cases hwv : w = v
        · rw [hwv]
          exact hd
        · exact ih w (List.mem_filter.mpr ⟨hw, by rw [bne_iff_ne]; exact hwv⟩)

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

theorem opens_cons (y : ℕ) (X : List ℕ) : opens (y :: X) = opensCons y X (opens X) := by
  unfold opens opensCons
  rw [List.filter_cons, List.filter_filter]
  have hrest : List.filter (fun c => c != 13 && (y :: X).all (fun x => (x + 1) % c != 0)) X =
      List.filter (fun c => ((y + 1) % c != 0) && (c != 13 && X.all (fun x => (x + 1) % c != 0))) X := by
    refine List.filter_congr fun c _ => ?_
    rw [List.all_cons]
    cases ((y + 1) % c != 0) <;> simp
  rw [hrest]
  split_ifs <;> rfl

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

theorem pow_mul_dvd {a b s : ℕ} (hab : a ≤ b) (h : 5 ^ 3 ∣ 5 ^ a * s) : 5 ^ 3 ∣ 5 ^ b * s :=
  h.trans (Nat.mul_dvd_mul_right (pow_dvd_pow 5 hab) s)

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

-- Section 4. The window lemma: a simple prime of the window `[N, 2 * N - 1)` outside `X` is a candidate.

theorem cand_mem {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ} (h : St P X Y N)
    {p : ℕ} (hp : p ∈ P) (hpN : ¬ p < N) (hpN' : p + 1 < 2 * N) (hpX : p ∉ X) : p ∈ cands X N ∧ dead X Y p = false := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
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
    ⟨fun h2 => hu (by rw [hjd]; exact (h2 ▸ hcd).mul_left _), fun hz => hd (hz ▸ hcd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ opens X := fun c hc hcd => by
    obtain ⟨hc2, hcz⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hcz p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    refine mem_opens hcX (fun e => C.hc13 p hp (e ▸ hcp)) fun x hx hcx => ?_
    exact hpX ((C.s3 c hc hc2 hcz p hp x (hXP x hx) hcp hcx) ▸ hx)
  have hdD : d ∣ (opens X).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hcz⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hcz p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hjdvd : 5 ^ j ∣ p + 1 := ⟨2 ^ i * d, by rw [hiu, hjd]; ring⟩
  have hjL : j < 3 := by
    by_contra hj
    exact C.led (((pow_dvd_pow 5 (by omega : 3 ≤ j)).trans hjdvd).trans
      (Finset.dvd_prod_of_mem (fun q => q + 1) hp))
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hu ⟨(p + 1) / 2, by omega⟩
  have hw0 : 0 < 5 ^ j * d := Nat.pos_of_ne_zero (by rw [← hjd]; exact hu0)
  have hpw : p + 1 = 2 ^ i * (5 ^ j * d) := by rw [hiu, hjd]
  have hwN : 5 ^ j * d ≤ N := by
    by_contra hNw
    have h2 : 2 ^ 1 * (5 ^ j * d) ≤ 2 ^ i * (5 ^ j * d) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi1)
    omega
  have hzj : 0 < 5 ^ j := Nat.pos_of_ne_zero (by positivity)
  have hmem : d ∈ subProdsLe (N / 5 ^ j) (opens X) := mem_subProdsLe _ _
    (fun c hc => (C.hP c (hXP c (List.mem_filter.mp hc).1)).1) d hdD
    ((Nat.le_div_iff_mul_le hzj).mpr (by rw [mul_comm]; exact hwN))
  have hled : ¬ 5 ^ 3 ∣ 5 ^ j * succProd X := fun h2 => by
    have h3 : 5 ^ j * succProd X ∣ (p + 1) * succProd X := Nat.mul_dvd_mul_right hjdvd _
    have h4 := prod_mul_dvd hXP hXn (T := {p}) (Finset.singleton_subset_iff.mpr hp)
      (fun q hq => (Finset.mem_singleton.mp hq) ▸ hpX)
    rw [Finset.prod_singleton] at h4
    exact C.led (h2.trans (h3.trans h4))
  have hv : 2 ^ (Nat.log2 (N / (5 ^ j * d)) + 1) * (5 ^ j * d) - 1 = p := by
    rw [pow_window hw0 hwN hpw (by omega) (by omega), Nat.add_sub_cancel]
  refine ⟨?_, ?_⟩
  · unfold cands candsA
    rw [List.mem_filter, List.mem_flatMap, Nat.blt_eq]
    refine ⟨⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hjL, ?_⟩, List.mem_map.mpr ⟨d, hmem, hv⟩⟩, hpN'⟩
    rw [bne_iff_ne]
    exact fun h0 => hled (Nat.dvd_of_mod_eq_zero h0)
  · unfold dead
    rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨⟨hpp.ne_zero, not_comp hpp hp2⟩, ?_⟩, ?_⟩
    · by_contra hc
      rw [Bool.not_eq_false, memB_iff] at hc
      exact hpX hc
    · by_contra hc
      rw [Bool.not_eq_false, memB_iff] at hc
      exact hY p hc hp

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N N' : ℕ}
    (h : St P X Y N) (hN' : N' < 2 * N) (hchk : ∀ v ∈ cands X N, dead X Y v = false → N' ≤ v) :
    St P X Y N' := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact h.2.2.2 p hp hpN
  by_contra hpX
  obtain ⟨hc, hd⟩ := cand_mem C h hp hpN (by omega) hpX
  have := hchk p hc hd
  omega

-- Section 5. The two contradictions.

theorem up_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ}
    (h : St P X Y N) (hchk : upOk X = true) : False := by
  obtain ⟨hXP, hXn, -, -⟩ := h
  simp only [upOk, upOkA, Nat.ble_eq] at hchk
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
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 26 * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, (p : ℚ) := by
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
    (h : (2 ^ 64 + 1) * 26 * S * (N + 1) ^ (E + 1) < 2 * 2 ^ 64 * 25 * Pi * (N - 1) ^ E * (N - 3)) :
    (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ E *
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
  have e : (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 1)) ^ E *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 3)) =
      (((2 : ℚ) ^ 64 + 1) * 26 * S * ((k : ℚ) + 3 + 1) ^ (E + 1)) /
        (2 ^ 64 * 25 * Pi * ((k : ℚ) + 2) ^ E * k) := by
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
  simp only [lowOk, lowOkA, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hchk
  obtain ⟨hN5, hnum⟩ := hchk
  change (2 ^ 64 + 1) * 26 * succProd X * (N + 1) ^ ((opens X).length + ledgerLeft X + 1) <
    2 * 2 ^ 64 * 25 * X.prod * (N - 1) ^ ((opens X).length + ledgerLeft X) * (N - 3) at hnum
  classical
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hnz : ∀ {c : ℕ}, c ∉ ({5} : Finset ℕ) → c ≠ 5 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 5 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
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
    refine mem_opens hcX (fun e => C.hc13 q hqP (e ▸ (hg q).1))
      fun x hx hcx => ?_
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
  have hledB : ¬ 5 ^ 3 ∣ 5 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card * succProd X :=
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
    unfold ledgerLeft ledgerLeftA
    by_contra hlt
    apply hledB
    split_ifs at hlt with h1 h2
    · exact pow_mul_dvd (by omega) (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1))
    · exact pow_mul_dvd (by omega) (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h2))
    · exact pow_mul_dvd (by omega : 3 ≤ _) (Dvd.intro _ rfl)
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, hzq⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact hzq (this ▸ hcd)
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1),
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
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 5 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hpowle : (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤
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
  have hchain : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
      ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) ≤
      (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ)) *
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h2 : (succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) ≤
        (succProd X : ℚ) / (X.prod : ℚ) * ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
          (((N : ℚ) + 1) / ((N : ℚ) - 3))) := mul_le_mul_of_nonneg_left hQle hSq
    calc (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
        ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)))
        ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ) *
          ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
            (((N : ℚ) + 1) / ((N : ℚ) - 3)))) :=
          mul_le_mul h1 h2 (mul_nonneg hSq hQ0) (by positivity)
      _ = _ := by ring
  linarith

-- Section 6. The search, run by the kernel.

/-- The search with fuel `f` from the state `X`, `Y`, `N`. `O`, `S`, `Pi` are the open members of `X`, the product of
the `x + 1` and the product of `X`, kept up to date; `l` holds the candidates of the window `[N, 2 * N - 1)` that
are still to be looked at. A step is a contradiction of one of the two kinds, a hole (a state proved in another
evaluation), the next window when `l` has no live member, or a split on the least live member `y` of `l`: with `y` the
closure moves to `y`, without `y` the search goes on in the same window. -/
def search (holes : List (List ℕ × List ℕ × ℕ)) :
    ℕ → List ℕ → List ℕ → ℕ → List ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _, _, _, _, _ => false
  | f + 1, X, Y, N, O, S, Pi, l =>
    upOkA Pi S || lowOkA O S Pi N || holes.any (fun h => h.1 == X && h.2.1 == Y && h.2.2 == N) ||
      match firstLive X Y (l.length + 1) l with
      | none => search holes f X Y (2 * N - 1) O S Pi (candsA O S (2 * N - 1))
      | some (y, r) =>
        search holes f (y :: X) Y y (opensCons y X O) ((y + 1) * S) (y * Pi)
            (candsA (opensCons y X O) ((y + 1) * S) y) &&
          search holes f X (y :: Y) N O S Pi r

theorem sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) (holes : List (List ℕ × List ℕ × ℕ))
    (hh : ∀ X Y N, (X, Y, N) ∈ holes → St P X Y N → False) :
    ∀ (f : ℕ) (X Y : List ℕ) (N : ℕ) (O : List ℕ) (S Pi : ℕ) (l : List ℕ),
      O = opens X → S = succProd X → Pi = X.prod → 1 ≤ N →
      (∀ v ∈ cands X N, dead X Y v = false → v ∈ l) → (∀ v ∈ l, v ∈ cands X N) →
      search holes f X Y N O S Pi l = true → St P X Y N → False
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by simp [search] at h
  | f + 1, X, Y, N, O, S, Pi, l, hO, hS, hPi, hN1, hI, hII, h, hs => by
    subst hO hS hPi
    unfold search at h
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact up_kill C hs h
    · exact low_kill C hs h
    · rw [List.any_eq_true] at h
      obtain ⟨⟨hx, hy, hn⟩, hmem, heq⟩ := h
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      exact hh _ _ _ hmem hs
    · split at h
      · rename_i hnone
        have hall := firstLive_none X Y _ _ (Nat.lt_succ_self _) hnone
        refine sound C holes hh f X Y (2 * N - 1) _ _ _ _ rfl rfl rfl (by omega) (fun v hv _ => hv)
          (fun v hv => hv) h (extend C hs (by omega) fun v hv hd => ?_)
        rw [hall v (hI v hv hd)] at hd
        exact absurd hd (by simp)
      · rename_i y r hsome
        obtain ⟨hymem, hyd, hymin, hrest, hsub⟩ := firstLive_some X Y _ _ y r hsome
        have hylt : y + 1 < 2 * N := by
          have hyc := hII y hymem
          unfold cands candsA at hyc
          have := (List.mem_filter.mp hyc).2
          rwa [Nat.blt_eq] at this
        have hyd' := hyd
        unfold dead at hyd'
        rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hyd'
        have hyX : y ∉ X := fun hm => by
          rw [(memB_iff y X).mpr hm] at hyd'
          exact absurd hyd'.1.2 (by simp)
        rw [Bool.and_eq_true] at h
        have hs' : St P X Y y := extend C hs (by omega) fun v hv hd => hymin v (hI v hv hd) hd
        have hy1 : 1 ≤ y := Nat.pos_of_ne_zero hyd'.1.1.1
        by_cases hy : y ∈ P
        · have hl : candsA (opensCons y X (opens X)) ((y + 1) * succProd X) y = cands (y :: X) y := by
            unfold cands
            rw [opens_cons]
            rfl
          exact sound C holes hh f (y :: X) Y y _ _ _ _ (opens_cons y X).symm rfl rfl hy1
            (fun v hv _ => hl ▸ hv) (fun v hv => hl ▸ hv) h.1 (incl hs' hy hyX)
        · exact sound C holes hh f X (y :: Y) N _ _ _ _ rfl rfl rfl hN1
            (fun v hv hd => hrest v (hI v hv (dead_cons hd).1) (dead_cons hd).1 (dead_cons hd).2)
            (fun v hv => hII v (hsub v hv)) h.2 (excl hs hy)

/-- One evaluation of the search, started at a state with the candidates of its window. -/
theorem chunk_sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) (holes : List (List ℕ × List ℕ × ℕ))
    (hh : ∀ X Y N, (X, Y, N) ∈ holes → St P X Y N → False) (f : ℕ) (X Y : List ℕ) (N : ℕ) (hN : 1 ≤ N)
    (h : search holes f X Y N (opens X) (succProd X) X.prod (cands X N) = true) : St P X Y N → False :=
  sound C holes hh f X Y N _ _ _ _ rfl rfl rfl hN (fun v hv _ => hv) (fun v hv => hv) h

-- Section 7. The pieces of the search (written by a script; each `c` theorem is one kernel evaluation).

def x70306 : List ℕ := [11743, 8191, 7927, 4831, 991, 367, 313, 157, 151, 79, 31, 19, 3, 23, 7, 13]
def y70306 : List ℕ := [40063, 16381, 9661, 2503, 733, 127, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c70306 : search []
    100000 x70306 y70306 93937 (opens x70306) (succProd x70306) x70306.prod (cands x70306 93937) = true := by
  decide +kernel

theorem d70306 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x70306 y70306 93937 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c70306

def x70294 : List ℕ := [4831, 991, 367, 313, 157, 151, 79, 31, 19, 3, 23, 7, 13]
def y70294 : List ℕ := [2503, 733, 127, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c70294 : search [(x70306, y70306, 93937)]
    100000 x70294 y70294 4831 (opens x70294) (succProd x70294) x70294.prod (cands x70294 4831) = true := by
  decide +kernel

theorem d70294 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x70294 y70294 4831 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d70306 C) _ _ _ _ (by norm_num) c70294

def x69945 : List ℕ := [367, 313, 157, 151, 79, 31, 19, 3, 23, 7, 13]
def y69945 : List ℕ := [733, 127, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c69945 : search [(x70294, y70294, 4831)]
    100000 x69945 y69945 733 (opens x69945) (succProd x69945) x69945.prod (cands x69945 733) = true := by
  decide +kernel

theorem d69945 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x69945 y69945 733 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d70294 C) _ _ _ _ (by norm_num) c69945

def x69472 : List ℕ := [79, 31, 19, 3, 23, 7, 13]
def y69472 : List ℕ := [127, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c69472 : search [(x69945, y69945, 733)]
    100000 x69472 y69472 79 (opens x69472) (succProd x69472) x69472.prod (cands x69472 79) = true := by
  decide +kernel

theorem d69472 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x69472 y69472 79 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d69945 C) _ _ _ _ (by norm_num) c69472

def x66596 : List ℕ := [3967, 733, 607, 367, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y66596 : List ℕ := [5023, 1213, 991, 313, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c66596 : search []
    100000 x66596 y66596 7933 (opens x66596) (succProd x66596) x66596.prod (cands x66596 7933) = true := by
  decide +kernel

theorem d66596 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x66596 y66596 7933 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c66596

def x66561 : List ℕ := [607, 367, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y66561 : List ℕ := [313, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c66561 : search [(x66596, y66596, 7933)]
    100000 x66561 y66561 607 (opens x66561) (succProd x66561) x66561.prod (cands x66561 607) = true := by
  decide +kernel

theorem d66561 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x66561 y66561 607 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d66596 C) _ _ _ _ (by norm_num) c66561

def x63709 : List ℕ := [4194271, 1281463, 524287, 160183, 131071, 63487, 20023, 19423, 16381, 8191, 2503,
    1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y63709 : List ℕ := [1048573, 155383, 7873, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c63709 : search []
    100000 x63709 y63709 4194271 (opens x63709) (succProd x63709) x63709.prod (cands x63709 4194271) = true := by
  decide +kernel

theorem d63709 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x63709 y63709 4194271 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c63709

def x62522 : List ℕ := [524287, 155383, 131071, 63487, 20023, 19423, 16381, 8191, 2503, 1471, 607, 313, 157,
    127, 79, 31, 19, 3, 23, 7, 13]
def y62522 : List ℕ := [160183, 7873, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c62522 : search []
    100000 x62522 y62522 1048573 (opens x62522) (succProd x62522) x62522.prod (cands x62522 1048573) = true := by
  decide +kernel

theorem d62522 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x62522 y62522 1048573 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c62522

def x62513 : List ℕ := [20023, 19423, 16381, 8191, 2503, 1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y62513 : List ℕ := [7873, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c62513 : search [(x62522, y62522, 1048573), (x63709, y63709, 4194271)]
    100000 x62513 y62513 40045 (opens x62513) (succProd x62513) x62513.prod (cands x62513 40045) = true := by
  decide +kernel

theorem d62513 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x62513 y62513 40045 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d62522 C
    · exact d63709 C) _ _ _ _ (by norm_num) c62513

def x60556 : List ℕ := [1048447, 524287, 160183, 131071, 20023, 8191, 7873, 2503, 1471, 607, 313, 157, 127,
    79, 31, 19, 3, 23, 7, 13]
def y60556 : List ℕ := [262111, 62983, 19423, 16381, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c60556 : search []
    100000 x60556 y60556 1048447 (opens x60556) (succProd x60556) x60556.prod (cands x60556 1048447) = true := by
  decide +kernel

theorem d60556 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x60556 y60556 1048447 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c60556

def x60430 : List ℕ := [131071, 20023, 8191, 7873, 2503, 1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y60430 : List ℕ := [62983, 19423, 16381, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c60430 : search [(x60556, y60556, 1048447)]
    100000 x60430 y60430 131071 (opens x60430) (succProd x60430) x60430.prod (cands x60430 131071) = true := by
  decide +kernel

theorem d60430 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x60430 y60430 131071 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d60556 C) _ _ _ _ (by norm_num) c60430

def x59427 : List ℕ := [8191, 7873, 2503, 1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y59427 : List ℕ := [16381, 3967, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c59427 : search [(x60430, y60430, 131071)]
    100000 x59427 y59427 16381 (opens x59427) (succProd x59427) x59427.prod (cands x59427 16381) = true := by
  decide +kernel

theorem d59427 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x59427 y59427 16381 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d60430 C) _ _ _ _ (by norm_num) c59427

def x58361 : List ℕ := [131071, 20023, 3967, 2503, 1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y58361 : List ℕ := [126943, 19423, 8191, 7933, 1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c58361 : search []
    100000 x58361 y58361 131071 (opens x58361) (succProd x58361) x58361.prod (cands x58361 131071) = true := by
  decide +kernel

theorem d58361 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x58361 y58361 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c58361

def x58110 : List ℕ := [1471, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y58110 : List ℕ := [1213, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c58110 : search [(x58361, y58361, 131071), (x59427, y59427, 16381), (x62513, y62513, 40045)]
    100000 x58110 y58110 1471 (opens x58110) (succProd x58110) x58110.prod (cands x58110 1471) = true := by
  decide +kernel

theorem d58110 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x58110 y58110 1471 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d58361 C
    · exact d59427 C
    · exact d62513 C) _ _ _ _ (by norm_num) c58110

def x55231 : List ℕ := [1015423, 524287, 131071, 16381, 8191, 7933, 3967, 1213, 607, 313, 157, 127, 79, 31,
    19, 3, 23, 7, 13]
def y55231 : List ℕ := [1048573, 318007, 308101, 115183, 94207, 63463, 40063, 2851, 2503, 1471, 991, 367,
    151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c55231 : search []
    100000 x55231 y55231 2030845 (opens x55231) (succProd x55231) x55231.prod (cands x55231 2030845) = true := by
  decide +kernel

theorem d55231 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x55231 y55231 2030845 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c55231

def x54921 : List ℕ := [131071, 16381, 8191, 7933, 3967, 1213, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y54921 : List ℕ := [115183, 94207, 63463, 40063, 2851, 2503, 1471, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c54921 : search [(x55231, y55231, 2030845)]
    100000 x54921 y54921 262141 (opens x54921) (succProd x54921) x54921.prod (cands x54921 262141) = true := by
  decide +kernel

theorem d54921 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x54921 y54921 262141 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d55231 C) _ _ _ _ (by norm_num) c54921

def x54780 : List ℕ := [8191, 7933, 3967, 1213, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y54780 : List ℕ := [2851, 2503, 1471, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c54780 : search [(x54921, y54921, 262141)]
    100000 x54780 y54780 16381 (opens x54780) (succProd x54780) x54780.prod (cands x54780 16381) = true := by
  decide +kernel

theorem d54780 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x54780 y54780 16381 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d54921 C) _ _ _ _ (by norm_num) c54780

def x53646 : List ℕ := [8191, 2851, 1213, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y53646 : List ℕ := [5701, 2503, 1471, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c53646 : search []
    100000 x53646 y53646 16381 (opens x53646) (succProd x53646) x53646.prod (cands x53646 16381) = true := by
  decide +kernel

theorem d53646 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x53646 y53646 16381 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c53646

def x52415 : List ℕ := [8191, 2503, 1213, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y52415 : List ℕ := [16381, 7873, 3967, 2851, 1471, 991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c52415 : search []
    100000 x52415 y52415 16381 (opens x52415) (succProd x52415) x52415.prod (cands x52415 16381) = true := by
  decide +kernel

theorem d52415 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x52415 y52415 16381 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c52415

def x52343 : List ℕ := [607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y52343 : List ℕ := [991, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c52343 : search [(x52415, y52415, 16381), (x53646, y53646, 16381), (x54780, y54780, 16381), (x58110,
    y58110, 1471)]
    100000 x52343 y52343 1213 (opens x52343) (succProd x52343) x52343.prod (cands x52343 1213) = true := by
  decide +kernel

theorem d52343 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x52343 y52343 1213 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d52415 C
    · exact d53646 C
    · exact d54780 C
    · exact d58110 C) _ _ _ _ (by norm_num) c52343

def x50595 : List ℕ := [524287, 155383, 131071, 94207, 19423, 16381, 8191, 7927, 991, 607, 313, 157, 127, 79,
    31, 19, 3, 23, 7, 13]
def y50595 : List ℕ := [2013457, 1048573, 318007, 40063, 2503, 1471, 1213, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c50595 : search []
    100000 x50595 y50595 2097145 (opens x50595) (succProd x50595) x50595.prod (cands x50595 2097145) = true := by
  decide +kernel

theorem d50595 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x50595 y50595 2097145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c50595

def x50257 : List ℕ := [19423, 16381, 8191, 7927, 991, 607, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y50257 : List ℕ := [2503, 1471, 1213, 367, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c50257 : search [(x50595, y50595, 2097145)]
    100000 x50257 y50257 38845 (opens x50257) (succProd x50257) x50257.prod (cands x50257 38845) = true := by
  decide +kernel

theorem d50257 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x50257 y50257 38845 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d50595 C) _ _ _ _ (by norm_num) c50257

def x49380 : List ℕ := [8191, 367, 313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y49380 : List ℕ := [7873, 3967, 2503, 991, 733, 607, 151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c49380 : search []
    100000 x49380 y49380 8191 (opens x49380) (succProd x49380) x49380.prod (cands x49380 8191) = true := by
  decide +kernel

theorem d49380 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x49380 y49380 8191 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c49380

def x48691 : List ℕ := [313, 157, 127, 79, 31, 19, 3, 23, 7, 13]
def y48691 : List ℕ := [151, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c48691 : search [(x49380, y49380, 8191), (x50257, y50257, 38845), (x52343, y52343, 1213)]
    100000 x48691 y48691 313 (opens x48691) (succProd x48691) x48691.prod (cands x48691 313) = true := by
  decide +kernel

theorem d48691 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x48691 y48691 313 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d49380 C
    · exact d50257 C
    · exact d52343 C) _ _ _ _ (by norm_num) c48691

def x47391 : List ℕ := [631, 367, 151, 127, 79, 31, 19, 3, 23, 7, 13]
def y47391 : List ℕ := [157, 61, 37, 5]

set_option maxHeartbeats 0 in
theorem c47391 : search []
    100000 x47391 y47391 631 (opens x47391) (succProd x47391) x47391.prod (cands x47391 631) = true := by
  decide +kernel

theorem d47391 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x47391 y47391 631 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c47391

def x47383 : List ℕ := [31, 19, 3, 23, 7, 13]
def y47383 : List ℕ := [61, 37, 5]

set_option maxHeartbeats 0 in
theorem c47383 : search [(x47391, y47391, 631), (x48691, y48691, 313), (x66561, y66561, 607), (x69472,
    y69472, 79)]
    100000 x47383 y47383 61 (opens x47383) (succProd x47383) x47383.prod (cands x47383 61) = true := by
  decide +kernel

theorem d47383 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x47383 y47383 61 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d47391 C
    · exact d48691 C
    · exact d66561 C
    · exact d69472 C) _ _ _ _ (by norm_num) c47383

def x44497 : List ℕ := [262111, 131071, 15583, 11743, 8191, 5113, 2557, 1279, 1213, 607, 487, 367, 127, 61,
    31, 19, 3, 23, 7, 13]
def y44497 : List ℕ := [40903, 16381, 733, 379, 229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c44497 : search []
    100000 x44497 y44497 262111 (opens x44497) (succProd x44497) x44497.prod (cands x44497 262111) = true := by
  decide +kernel

theorem d44497 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x44497 y44497 262111 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c44497

def x44484 : List ℕ := [2557, 1279, 1213, 607, 487, 367, 127, 61, 31, 19, 3, 23, 7, 13]
def y44484 : List ℕ := [733, 379, 229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c44484 : search [(x44497, y44497, 262111)]
    100000 x44484 y44484 5113 (opens x44484) (succProd x44484) x44484.prod (cands x44484 5113) = true := by
  decide +kernel

theorem d44484 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x44484 y44484 5113 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d44497 C) _ _ _ _ (by norm_num) c44484

def x42863 : List ℕ := [8191, 1213, 733, 607, 487, 367, 127, 61, 31, 19, 3, 23, 7, 13]
def y42863 : List ℕ := [9739, 5119, 2539, 1279, 379, 229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c42863 : search []
    100000 x42863 y42863 8191 (opens x42863) (succProd x42863) x42863.prod (cands x42863 8191) = true := by
  decide +kernel

theorem d42863 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x42863 y42863 8191 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c42863

def x41785 : List ℕ := [131071, 19477, 9739, 8191, 1213, 733, 607, 487, 367, 127, 61, 31, 19, 3, 23, 7, 13]
def y41785 : List ℕ := [38953, 16381, 5119, 2539, 1279, 379, 229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c41785 : search []
    100000 x41785 y41785 131071 (opens x41785) (succProd x41785) x41785.prod (cands x41785 131071) = true := by
  decide +kernel

theorem d41785 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x41785 y41785 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c41785

def x41371 : List ℕ := [733, 607, 487, 367, 127, 61, 31, 19, 3, 23, 7, 13]
def y41371 : List ℕ := [379, 229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c41371 : search [(x41785, y41785, 131071), (x42863, y42863, 8191)]
    100000 x41371 y41371 733 (opens x41371) (succProd x41371) x41371.prod (cands x41371 733) = true := by
  decide +kernel

theorem d41371 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x41371 y41371 733 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d41785 C
    · exact d42863 C) _ _ _ _ (by norm_num) c41371

def x40473 : List ℕ := [379, 367, 127, 61, 31, 19, 3, 23, 7, 13]
def y40473 : List ℕ := [229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c40473 : search []
    100000 x40473 y40473 379 (opens x40473) (succProd x40473) x40473.prod (cands x40473 379) = true := by
  decide +kernel

theorem d40473 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x40473 y40473 379 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c40473

def x40471 : List ℕ := [127, 61, 31, 19, 3, 23, 7, 13]
def y40471 : List ℕ := [229, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c40471 : search [(x40473, y40473, 379), (x41371, y41371, 733), (x44484, y44484, 5113)]
    100000 x40471 y40471 253 (opens x40471) (succProd x40471) x40471.prod (cands x40471 253) = true := by
  decide +kernel

theorem d40471 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x40471 y40471 253 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d40473 C
    · exact d41371 C
    · exact d44484 C) _ _ _ _ (by norm_num) c40471

def x37855 : List ℕ := [155383, 131071, 19423, 8191, 1951, 607, 457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y37855 : List ℕ := [233983, 16381, 15607, 1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c37855 : search []
    100000 x37855 y37855 155383 (opens x37855) (succProd x37855) x37855.prod (cands x37855 155383) = true := by
  decide +kernel

theorem d37855 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37855 y37855 155383 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c37855

def x37428 : List ℕ := [131071, 19423, 8191, 1951, 607, 457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y37428 : List ℕ := [16381, 15607, 1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c37428 : search [(x37855, y37855, 155383)]
    100000 x37428 y37428 131071 (opens x37428) (succProd x37428) x37428.prod (cands x37428 131071) = true := by
  decide +kernel

theorem d37428 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37428 y37428 131071 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d37855 C) _ _ _ _ (by norm_num) c37428

def x36650 : List ℕ := [8191, 1951, 607, 457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y36650 : List ℕ := [15607, 1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c36650 : search [(x37428, y37428, 131071)]
    100000 x36650 y36650 16381 (opens x36650) (succProd x36650) x36650.prod (cands x36650 16381) = true := by
  decide +kernel

theorem d36650 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x36650 y36650 16381 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d37428 C) _ _ _ _ (by norm_num) c36650

def x35787 : List ℕ := [15607, 8191, 1951, 607, 457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y35787 : List ℕ := [131071, 19423, 16381, 1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c35787 : search []
    100000 x35787 y35787 124849 (opens x35787) (succProd x35787) x35787.prod (cands x35787 124849) = true := by
  decide +kernel

theorem d35787 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x35787 y35787 124849 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c35787

def x34234 : List ℕ := [63926143, 33554167, 7486573, 4194271, 524287, 499423, 131071, 15607, 8191, 1951, 607,
    457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y34234 : List ℕ := [157878271, 16777183, 1048573, 1048447, 554797, 464311, 262111, 233983, 19423, 16381,
    1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c34234 : search []
    100000 x34234 y34234 511409137 (opens x34234) (succProd x34234) x34234.prod (cands x34234 511409137) = true := by
  decide +kernel

theorem d34234 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x34234 y34234 511409137 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c34234

def x33935 : List ℕ := [131071, 15607, 8191, 1951, 607, 457, 229, 127, 61, 31, 19, 3, 23, 7, 13]
def y33935 : List ℕ := [262111, 233983, 19423, 16381, 1213, 487, 151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c33935 : search [(x34234, y34234, 511409137)]
    100000 x33935 y33935 262141 (opens x33935) (succProd x33935) x33935.prod (cands x33935 262141) = true := by
  decide +kernel

theorem d33935 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x33935 y33935 262141 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d34234 C) _ _ _ _ (by norm_num) c33935

def x33555 : List ℕ := [229, 127, 61, 31, 19, 3, 23, 7, 13]
def y33555 : List ℕ := [151, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c33555 : search [(x33935, y33935, 262141), (x35787, y35787, 124849), (x36650, y36650, 16381)]
    100000 x33555 y33555 457 (opens x33555) (succProd x33555) x33555.prod (cands x33555 457) = true := by
  decide +kernel

theorem d33555 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x33555 y33555 457 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d33935 C
    · exact d35787 C
    · exact d36650 C) _ _ _ _ (by norm_num) c33555

def x32407 : List ℕ := [1471, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y32407 : List ℕ := [1279, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c32407 : search []
    100000 x32407 y32407 1471 (opens x32407) (succProd x32407) x32407.prod (cands x32407 1471) = true := by
  decide +kernel

theorem d32407 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x32407 y32407 1471 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c32407

def x29488 : List ℕ := [2473453, 1236727, 524287, 154591, 131071, 94207, 16381, 8191, 5113, 4831, 2557, 1951,
    1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y29488 : List ℕ := [3995647, 1048573, 249727, 40903, 15607, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c29488 : search []
    100000 x29488 y29488 2473453 (opens x29488) (succProd x29488) x29488.prod (cands x29488 2473453) = true := by
  decide +kernel

theorem d29488 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x29488 y29488 2473453 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c29488

def x28871 : List ℕ := [1236727, 524287, 154591, 131071, 94207, 16381, 8191, 5113, 4831, 2557, 1951, 1279,
    151, 127, 61, 31, 19, 3, 23, 7, 13]
def y28871 : List ℕ := [1048573, 249727, 40903, 15607, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c28871 : search [(x29488, y29488, 2473453)]
    100000 x28871 y28871 2473453 (opens x28871) (succProd x28871) x28871.prod (cands x28871 2473453) = true := by
  decide +kernel

theorem d28871 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x28871 y28871 2473453 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d29488 C) _ _ _ _ (by norm_num) c28871

def x27958 : List ℕ := [1048573, 524287, 154591, 131071, 94207, 16381, 8191, 5113, 4831, 2557, 1951, 1279,
    151, 127, 61, 31, 19, 3, 23, 7, 13]
def y27958 : List ℕ := [249727, 40903, 15607, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c27958 : search []
    100000 x27958 y27958 1048573 (opens x27958) (succProd x27958) x27958.prod (cands x27958 1048573) = true := by
  decide +kernel

theorem d27958 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27958 y27958 1048573 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c27958

def x27613 : List ℕ := [16381, 8191, 5113, 4831, 2557, 1951, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y27613 : List ℕ := [15607, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c27613 : search [(x27958, y27958, 1048573), (x28871, y28871, 2473453)]
    100000 x27613 y27613 32761 (opens x27613) (succProd x27613) x27613.prod (cands x27613 32761) = true := by
  decide +kernel

theorem d27613 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27613 y27613 32761 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d27958 C
    · exact d28871 C) _ _ _ _ (by norm_num) c27613

def x24996 : List ℕ := [1236727, 524287, 524221, 499423, 262111, 154591, 131071, 15607, 8191, 5113, 4831,
    2557, 1951, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y24996 : List ℕ := [1048573, 94207, 40903, 16381, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c24996 : search []
    100000 x24996 y24996 2473453 (opens x24996) (succProd x24996) x24996.prod (cands x24996 2473453) = true := by
  decide +kernel

theorem d24996 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24996 y24996 2473453 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c24996

def x24720 : List ℕ := [262111, 154591, 131071, 15607, 8191, 5113, 4831, 2557, 1951, 1279, 151, 127, 61, 31,
    19, 3, 23, 7, 13]
def y24720 : List ℕ := [94207, 40903, 16381, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c24720 : search [(x24996, y24996, 2473453)]
    100000 x24720 y24720 262111 (opens x24720) (succProd x24720) x24720.prod (cands x24720 262111) = true := by
  decide +kernel

theorem d24720 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24720 y24720 262111 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d24996 C) _ _ _ _ (by norm_num) c24720

def x23164 : List ℕ := [131071, 94207, 15607, 8191, 5113, 4831, 2557, 1951, 1279, 151, 127, 61, 31, 19, 3,
    23, 7, 13]
def y23164 : List ℕ := [40903, 16381, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c23164 : search []
    100000 x23164 y23164 131071 (opens x23164) (succProd x23164) x23164.prod (cands x23164 131071) = true := by
  decide +kernel

theorem d23164 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x23164 y23164 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c23164

def x23162 : List ℕ := [15607, 8191, 5113, 4831, 2557, 1951, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y23162 : List ℕ := [40903, 16381, 9661, 1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c23162 : search [(x23164, y23164, 131071), (x24720, y24720, 262111)]
    100000 x23162 y23162 62425 (opens x23162) (succProd x23162) x23162.prod (cands x23162 62425) = true := by
  decide +kernel

theorem d23162 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x23162 y23162 62425 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d23164 C
    · exact d24720 C) _ _ _ _ (by norm_num) c23162

def x23085 : List ℕ := [1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y23085 : List ℕ := [1471, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c23085 : search [(x23162, y23162, 62425), (x27613, y27613, 32761)]
    100000 x23085 y23085 1279 (opens x23085) (succProd x23085) x23085.prod (cands x23085 1279) = true := by
  decide +kernel

theorem d23085 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x23085 y23085 1279 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d23162 C
    · exact d27613 C) _ _ _ _ (by norm_num) c23085

def x22050 : List ℕ := [8191, 5113, 2557, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y22050 : List ℕ := [4831, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c22050 : search []
    100000 x22050 y22050 8191 (opens x22050) (succProd x22050) x22050.prod (cands x22050 8191) = true := by
  decide +kernel

theorem d22050 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x22050 y22050 8191 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c22050

def x19479 : List ℕ := [2096893, 1048573, 1048447, 524287, 499711, 131071, 9661, 8191, 4831, 2557, 1471,
    1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y19479 : List ℕ := [262111, 179461, 31231, 16381, 15493, 5113, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c19479 : search []
    100000 x19479 y19479 2096893 (opens x19479) (succProd x19479) x19479.prod (cands x19479 2096893) = true := by
  decide +kernel

theorem d19479 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x19479 y19479 2096893 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c19479

def x19474 : List ℕ := [131071, 9661, 8191, 4831, 2557, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y19474 : List ℕ := [262111, 179461, 31231, 16381, 15493, 5113, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c19474 : search [(x19479, y19479, 2096893)]
    100000 x19474 y19474 262141 (opens x19474) (succProd x19474) x19474.prod (cands x19474 262141) = true := by
  decide +kernel

theorem d19474 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x19474 y19474 262141 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d19479 C) _ _ _ _ (by norm_num) c19474

def x18112 : List ℕ := [524287, 262111, 131071, 9661, 8191, 4831, 2557, 1471, 1279, 151, 127, 61, 31, 19, 3,
    23, 7, 13]
def y18112 : List ℕ := [1178641, 1048573, 524221, 499711, 179461, 31231, 16381, 15493, 5113, 1951, 919, 487,
    367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c18112 : search []
    100000 x18112 y18112 2097145 (opens x18112) (succProd x18112) x18112.prod (cands x18112 2097145) = true := by
  decide +kernel

theorem d18112 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x18112 y18112 2097145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c18112

def x16603 : List ℕ := [1048573, 524287, 262111, 131071, 9661, 8191, 4831, 2557, 1471, 1279, 151, 127, 61,
    31, 19, 3, 23, 7, 13]
def y16603 : List ℕ := [22791673, 20946943, 12050431, 7995391, 5978143, 4194271, 2871391, 2597911, 1178641,
    524221, 499711, 179461, 31231, 16381, 15493, 5113, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c16603 : search []
    100000 x16603 y16603 16777153 (opens x16603) (succProd x16603) x16603.prod (cands x16603 16777153) = true := by
  decide +kernel

theorem d16603 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x16603 y16603 16777153 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c16603

def x15794 : List ℕ := [262111, 131071, 9661, 8191, 4831, 2557, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7,
    13]
def y15794 : List ℕ := [499711, 179461, 31231, 16381, 15493, 5113, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c15794 : search [(x16603, y16603, 16777153), (x18112, y18112, 2097145)]
    100000 x15794 y15794 524221 (opens x15794) (succProd x15794) x15794.prod (cands x15794 524221) = true := by
  decide +kernel

theorem d15794 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x15794 y15794 524221 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d16603 C
    · exact d18112 C) _ _ _ _ (by norm_num) c15794

def x15535 : List ℕ := [4831, 2557, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y15535 : List ℕ := [5113, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c15535 : search [(x15794, y15794, 524221), (x19474, y19474, 262141)]
    100000 x15535 y15535 4831 (opens x15535) (succProd x15535) x15535.prod (cands x15535 4831) = true := by
  decide +kernel

theorem d15535 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x15535 y15535 4831 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d15794 C
    · exact d19474 C) _ _ _ _ (by norm_num) c15535

def x13899 : List ℕ := [524287, 499711, 154591, 131071, 40903, 5113, 4831, 2557, 1471, 1279, 151, 127, 61,
    31, 19, 3, 23, 7, 13]
def y13899 : List ℕ := [179461, 31231, 15493, 9661, 8191, 1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c13899 : search []
    100000 x13899 y13899 1048573 (opens x13899) (succProd x13899) x13899.prod (cands x13899 1048573) = true := by
  decide +kernel

theorem d13899 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x13899 y13899 1048573 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c13899

def x13661 : List ℕ := [2557, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y13661 : List ℕ := [1951, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c13661 : search [(x13899, y13899, 1048573), (x15535, y15535, 4831), (x22050, y22050, 8191)]
    100000 x13661 y13661 2557 (opens x13661) (succProd x13661) x13661.prod (cands x13661 2557) = true := by
  decide +kernel

theorem d13661 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x13661 y13661 2557 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d13899 C
    · exact d15535 C
    · exact d22050 C) _ _ _ _ (by norm_num) c13661

def x12484 : List ℕ := [154591, 131071, 81853, 40927, 15607, 4831, 1951, 1471, 1279, 151, 127, 61, 31, 19, 3,
    23, 7, 13]
def y12484 : List ℕ := [499423, 9661, 8191, 2557, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c12484 : search []
    100000 x12484 y12484 309181 (opens x12484) (succProd x12484) x12484.prod (cands x12484 309181) = true := by
  decide +kernel

theorem d12484 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x12484 y12484 309181 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c12484

def x10711 : List ℕ := [1048573, 524287, 249727, 131071, 9661, 4831, 1951, 1471, 1279, 151, 127, 61, 31, 19,
    3, 23, 7, 13]
def y10711 : List ℕ := [40927, 15607, 8191, 2557, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c10711 : search []
    100000 x10711 y10711 2097145 (opens x10711) (succProd x10711) x10711.prod (cands x10711 2097145) = true := by
  decide +kernel

theorem d10711 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x10711 y10711 2097145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c10711

def x10696 : List ℕ := [4831, 1951, 1471, 1279, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y10696 : List ℕ := [8191, 2557, 919, 487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c10696 : search [(x10711, y10711, 2097145), (x12484, y12484, 309181)]
    100000 x10696 y10696 9661 (opens x10696) (succProd x10696) x10696.prod (cands x10696 9661) = true := by
  decide +kernel

theorem d10696 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x10696 y10696 9661 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d10711 C
    · exact d12484 C) _ _ _ _ (by norm_num) c10696

def x10334 : List ℕ := [151, 127, 61, 31, 19, 3, 23, 7, 13]
def y10334 : List ℕ := [487, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c10334 : search [(x10696, y10696, 9661), (x13661, y13661, 2557), (x23085, y23085, 1279), (x32407,
    y32407, 1471)]
    100000 x10334 y10334 601 (opens x10334) (succProd x10334) x10334.prod (cands x10334 601) = true := by
  decide +kernel

theorem d10334 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x10334 y10334 601 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d10696 C
    · exact d13661 C
    · exact d23085 C
    · exact d32407 C) _ _ _ _ (by norm_num) c10334

def x9358 : List ℕ := [8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y9358 : List ℕ := [15583, 10159, 9739, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c9358 : search []
    100000 x9358 y9358 16381 (opens x9358) (succProd x9358) x9358.prod (cands x9358 16381) = true := by
  decide +kernel

theorem d9358 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x9358 y9358 16381 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c9358

def x8483 : List ℕ := [15583, 8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y8483 : List ℕ := [20479, 16381, 10159, 9739, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229, 79, 37,
    5]

set_option maxHeartbeats 0 in
theorem c8483 : search []
    100000 x8483 y8483 15583 (opens x8483) (succProd x8483) x8483.prod (cands x8483 15583) = true := by
  decide +kernel

theorem d8483 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x8483 y8483 15583 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c8483

def x7130 : List ℕ := [1048447, 524287, 131071, 20479, 15583, 8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y7130 : List ℕ := [889087, 262111, 94207, 16381, 10159, 9739, 5119, 4831, 3019, 2539, 1471, 1279, 919,
    367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c7130 : search []
    100000 x7130 y7130 1048447 (opens x7130) (succProd x7130) x7130.prod (cands x7130 1048447) = true := by
  decide +kernel

theorem d7130 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x7130 y7130 1048447 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c7130

def x6445 : List ℕ := [524287, 131071, 20479, 15583, 8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y6445 : List ℕ := [262111, 94207, 16381, 10159, 9739, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229,
    79, 37, 5]

set_option maxHeartbeats 0 in
theorem c6445 : search [(x7130, y7130, 1048447)]
    100000 x6445 y6445 524287 (opens x6445) (succProd x6445) x6445.prod (cands x6445 524287) = true := by
  decide +kernel

theorem d6445 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x6445 y6445 524287 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d7130 C) _ _ _ _ (by norm_num) c6445

def x5882 : List ℕ := [20479, 15583, 8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y5882 : List ℕ := [16381, 10159, 9739, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c5882 : search [(x6445, y6445, 524287)]
    100000 x5882 y5882 81913 (opens x5882) (succProd x5882) x5882.prod (cands x5882 81913) = true := by
  decide +kernel

theorem d5882 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5882 y5882 81913 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d6445 C) _ _ _ _ (by norm_num) c5882

def x4816 : List ℕ := [8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y4816 : List ℕ := [9739, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c4816 : search [(x5882, y5882, 81913), (x8483, y8483, 15583), (x9358, y9358, 16381)]
    100000 x4816 y4816 8191 (opens x4816) (succProd x4816) x4816.prod (cands x4816 8191) = true := by
  decide +kernel

theorem d4816 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x4816 y4816 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d5882 C
    · exact d8483 C
    · exact d9358 C) _ _ _ _ (by norm_num) c4816

def x3587 : List ℕ := [131071, 94207, 9739, 8191, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y3587 : List ℕ := [19477, 16381, 5119, 4831, 3019, 2539, 1471, 1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c3587 : search []
    100000 x3587 y3587 131071 (opens x3587) (succProd x3587) x3587.prod (cands x3587 131071) = true := by
  decide +kernel

theorem d3587 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x3587 y3587 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c3587

def x2642 : List ℕ := [4831, 487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y2642 : List ℕ := [40639, 38959, 29209, 20479, 15583, 10159, 9739, 9661, 8191, 5119, 3019, 2539, 1471,
    1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c2642 : search []
    100000 x2642 y2642 77281 (opens x2642) (succProd x2642) x2642.prod (cands x2642 77281) = true := by
  decide +kernel

theorem d2642 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x2642 y2642 77281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c2642

def x2194 : List ℕ := [487, 151, 127, 61, 31, 19, 3, 23, 7, 13]
def y2194 : List ℕ := [3019, 2539, 1471, 1279, 919, 367, 229, 79, 37, 5]

set_option maxHeartbeats 0 in
theorem c2194 : search [(x2642, y2642, 77281), (x3587, y3587, 131071), (x4816, y4816, 8191)]
    100000 x2194 y2194 3889 (opens x2194) (succProd x2194) x2194.prod (cands x2194 3889) = true := by
  decide +kernel

theorem d2194 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x2194 y2194 3889 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d2642 C
    · exact d3587 C
    · exact d4816 C) _ _ _ _ (by norm_num) c2194

def x1070 : List ℕ := [79, 61, 31, 19, 3, 23, 7, 13]
def y1070 : List ℕ := [367, 157, 151, 127, 37, 5]

set_option maxHeartbeats 0 in
theorem c1070 : search []
    100000 x1070 y1070 313 (opens x1070) (succProd x1070) x1070.prod (cands x1070 313) = true := by
  decide +kernel

theorem d1070 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1070 y1070 313 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c1070

def x5 : List ℕ := [31, 19, 3, 23, 7, 13]
def y5 : List ℕ := [5]

set_option maxHeartbeats 0 in
theorem c5 : search [(x1070, y1070, 313), (x2194, y2194, 3889), (x10334, y10334, 601), (x33555, y33555, 457),
    (x40471, y40471, 253), (x47383, y47383, 61)]
    100000 x5 y5 31 (opens x5) (succProd x5) x5.prod (cands x5 31) = true := by
  decide +kernel

theorem d5 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5 y5 31 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d1070 C
    · exact d2194 C
    · exact d10334 C
    · exact d33555 C
    · exact d40471 C
    · exact d47383 C) _ _ _ _ (by norm_num) c5

def x0 : List ℕ := [3, 23, 7, 13]
def y0 : List ℕ := [5]

set_option maxHeartbeats 0 in
theorem c0 : search [(x5, y5, 31)]
    100000 x0 y0 3 (opens x0) (succProd x0) x0.prod (cands x0 3) = true := by
  decide +kernel

theorem d0 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x0 y0 3 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d5 C) _ _ _ _ (by norm_num) c0

-- Section 8. The step.

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H2 := by
  refine ⟨63, fun n h hS he c23 => ?_⟩
  by_contra hlt
  have hm : 64 ≤ padicValNat 2 n := by omega
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h5P : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self 5)
  have h23P : 23 ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by norm_num,
      Nat.mem_primeFactors.mpr ⟨by norm_num, c23, h.2.ne'⟩⟩, by decide⟩
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) = P at hP E h5P h23P
  generalize padicValNat 2 n = m at E hm
  have hn5 : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, S3, -, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 5) (e := 2) (by norm_num)) E
  have h13d : 13 ∣ 1 + 5 ^ 2 := by norm_num
  have h13P := S7 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
  have h7P := S1 7 (by norm_num) (by norm_num) (hn5 (by norm_num)) 13 h13P (by norm_num)
  have h3P := S1 3 (by norm_num) (by norm_num) (hn5 (by norm_num)) 23 h23P (by norm_num)
  have hled : ¬ 5 ^ 3 ∣ ∏ p ∈ P, (p + 1) := fun hd => by
    have h1 : 5 ^ 3 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := E ▸ (hd.mul_left _)
    have h2 : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
      have e : 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by ring
      rw [e]
      exact h1
    have h3 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h3 with h4 | h4
    · have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4)
      omega
    · obtain ⟨p, hp, hpd⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime (by norm_num)) _).mp h4
      have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP p hp).1).mp hpd
      exact h5P (h5 ▸ hp)
  have e1 : (1 + 5 ^ 2 : ℕ) = 26 := by norm_num
  have e2 : (5 ^ 2 : ℕ) = 25 := by norm_num
  have C : Ctx P m :=
    { hP := hP
      E := by
        rw [e1, e2] at E
        exact E
      s1 := fun c hc hc2 hc5 p hp hd => S1 c hc hc2 (hn5 hc5) p hp hd
      s3 := fun c hc hc2 hc5 p hp p' hp' hd hd' => S3 c hc hc2 (hn5 hc5) p hp p' hp' hd hd'
      s6 := fun c hc hc2 hc5 p hp => S6 c hc hc2 (hn5 hc5) p hp
      hc13 := S8 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
      led := hled
      hm := hm }
  refine d0 C ⟨fun x hx => ?_, by decide, fun y hy => ?_, fun p hp hp3 => ?_⟩
  · simp only [x0, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · rw [y0, List.mem_singleton] at hy
    rw [hy]
    exact h5P
  · have hpp := (hP p hp).1
    have hp2 := (hP p hp).2
    interval_cases p <;> first | exact absurd rfl hp2 | exact absurd hpp (by norm_num)

end OMA.P_Erdos1052_z5_e2_part2

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H2 :=
  OMA.P_Erdos1052_z5_e2_part2.step_proof
