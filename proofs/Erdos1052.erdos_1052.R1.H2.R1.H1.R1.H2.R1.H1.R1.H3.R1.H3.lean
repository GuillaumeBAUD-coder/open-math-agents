import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1.H3

Hypothesis H3 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1`: unitary perfect numbers
`n = 2 ^ a * 5 ^ 2 * (simple odd primes)` such that `47 ∣ n` have `a ≤ 63`.

Credit: @aroth01. The base lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...)
are those of reductions `...R1.H2.R1.H1.R1` and `...R1.H2.R1.H1.R1.H2.R1`.

Setting. `P` is the set of simple odd primes (5 is not one of them). `13 ∣ 1 + 5 ^ 2` is a simple prime that
divides no `p + 1`, and `7` divides only `13 + 1`. Then `47` and `3` (which divides `47 + 1`) are simple primes. Every simple prime `p` has
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
The kernel evaluates the search (`decide +kernel`). To keep each evaluation small the search is cut into 49
pieces (Section 7): a piece stops at the states (`holes`) where other pieces start. The cut was computed by a
script; nothing about it is trusted.
-/

namespace OMA.P_Erdos1052_z5_e2_part3

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

def x43461 : List ℕ := [2096893, 1048447, 524287, 131071, 40063, 31231, 8191, 6007, 751, 313, 157, 151, 127,
    79, 61, 31, 19, 3, 47, 7, 13]
def y43461 : List ℕ := [4194271, 1048573, 262111, 16381, 15493, 4831, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c43461 : search []
    100000 x43461 y43461 4193785 (opens x43461) (succProd x43461) x43461.prod (cands x43461 4193785) = true := by
  decide +kernel

theorem d43461 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x43461 y43461 4193785 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c43461

def x43251 : List ℕ := [1048447, 524287, 131071, 40063, 31231, 8191, 6007, 751, 313, 157, 151, 127, 79, 61,
    31, 19, 3, 47, 7, 13]
def y43251 : List ℕ := [1048573, 262111, 16381, 15493, 4831, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c43251 : search [(x43461, y43461, 4193785)]
    100000 x43251 y43251 2096893 (opens x43251) (succProd x43251) x43251.prod (cands x43251 2096893) = true := by
  decide +kernel

theorem d43251 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x43251 y43251 2096893 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d43461 C) _ _ _ _ (by norm_num) c43251

def x42190 : List ℕ := [16381, 8191, 6007, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y42190 : List ℕ := [131071, 40063, 31231, 15493, 4831, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c42190 : search []
    100000 x42190 y42190 262081 (opens x42190) (succProd x42190) x42190.prod (cands x42190 262081) = true := by
  decide +kernel

theorem d42190 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x42190 y42190 262081 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c42190

def x41966 : List ℕ := [8191, 6007, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y41966 : List ℕ := [4831, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c41966 : search [(x42190, y42190, 262081), (x43251, y43251, 2096893)]
    100000 x41966 y41966 8191 (opens x41966) (succProd x41966) x41966.prod (cands x41966 8191) = true := by
  decide +kernel

theorem d41966 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x41966 y41966 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d42190 C
    · exact d43251 C) _ _ _ _ (by norm_num) c41966

def x38718 : List ℕ := [318007, 262111, 154591, 131071, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19,
    3, 47, 7, 13]
def y38718 : List ℕ := [190753, 91621, 40063, 31231, 16381, 15493, 9661, 6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c38718 : search []
    100000 x38718 y38718 318007 (opens x38718) (succProd x38718) x38718.prod (cands x38718 318007) = true := by
  decide +kernel

theorem d38718 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x38718 y38718 318007 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c38718

def x37912 : List ℕ := [190753, 154591, 131071, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47,
    7, 13]
def y37912 : List ℕ := [91621, 40063, 31231, 16381, 15493, 9661, 6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c37912 : search []
    100000 x37912 y37912 190753 (opens x37912) (succProd x37912) x37912.prod (cands x37912 190753) = true := by
  decide +kernel

theorem d37912 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37912 y37912 190753 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c37912

def x37910 : List ℕ := [131071, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y37910 : List ℕ := [91621, 40063, 31231, 16381, 15493, 9661, 6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c37910 : search [(x37912, y37912, 190753), (x38718, y38718, 318007)]
    100000 x37910 y37910 131071 (opens x37910) (succProd x37910) x37910.prod (cands x37910 131071) = true := by
  decide +kernel

theorem d37910 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37910 y37910 131071 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d37912 C
    · exact d38718 C) _ _ _ _ (by norm_num) c37910

def x37067 : List ℕ := [91621, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y37067 : List ℕ := [131071, 40063, 31231, 16381, 15493, 9661, 6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c37067 : search []
    100000 x37067 y37067 91621 (opens x37067) (succProd x37067) x37067.prod (cands x37067 91621) = true := by
  decide +kernel

theorem d37067 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37067 y37067 91621 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c37067

def x36062 : List ℕ := [131071, 91621, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y36062 : List ℕ := [40063, 31231, 16381, 15493, 9661, 6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c36062 : search []
    100000 x36062 y36062 131071 (opens x36062) (succProd x36062) x36062.prod (cands x36062 131071) = true := by
  decide +kernel

theorem d36062 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x36062 y36062 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c36062

def x35250 : List ℕ := [40063, 8191, 4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y35250 : List ℕ := [262111, 190753, 154591, 131071, 91621, 31231, 16381, 15493, 9661, 6007, 2503, 1951,
    487, 37, 5]

set_option maxHeartbeats 0 in
theorem c35250 : search []
    100000 x35250 y35250 320497 (opens x35250) (succProd x35250) x35250.prod (cands x35250 320497) = true := by
  decide +kernel

theorem d35250 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x35250 y35250 320497 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c35250

def x35225 : List ℕ := [4831, 751, 313, 157, 151, 127, 79, 61, 31, 19, 3, 47, 7, 13]
def y35225 : List ℕ := [6007, 2503, 1951, 487, 37, 5]

set_option maxHeartbeats 0 in
theorem c35225 : search [(x35250, y35250, 320497), (x36062, y36062, 131071), (x37067, y37067, 91621),
    (x37910, y37910, 131071)]
    100000 x35225 y35225 4831 (opens x35225) (succProd x35225) x35225.prod (cands x35225 4831) = true := by
  decide +kernel

theorem d35225 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x35225 y35225 4831 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d35250 C
    · exact d36062 C
    · exact d37067 C
    · exact d37910 C) _ _ _ _ (by norm_num) c35225

def x35208 : List ℕ := [127, 79, 61, 31, 19, 3, 47, 7, 13]
def y35208 : List ℕ := [37, 5]

set_option maxHeartbeats 0 in
theorem c35208 : search [(x35225, y35225, 4831), (x41966, y41966, 8191)]
    100000 x35208 y35208 127 (opens x35208) (succProd x35208) x35208.prod (cands x35208 127) = true := by
  decide +kernel

theorem d35208 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x35208 y35208 127 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d35225 C
    · exact d41966 C) _ _ _ _ (by norm_num) c35208

def x34316 : List ℕ := [79, 37, 31, 19, 3, 47, 7, 13]
def y34316 : List ℕ := [73, 61, 5]

set_option maxHeartbeats 0 in
theorem c34316 : search []
    100000 x34316 y34316 79 (opens x34316) (succProd x34316) x34316.prod (cands x34316 79) = true := by
  decide +kernel

theorem d34316 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x34316 y34316 79 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c34316

def x32061 : List ℕ := [8191, 6007, 751, 79, 73, 37, 31, 19, 3, 47, 7, 13]
def y32061 : List ℕ := [16381, 10111, 9343, 3967, 991, 631, 157, 127, 61, 5]

set_option maxHeartbeats 0 in
theorem c32061 : search []
    100000 x32061 y32061 32761 (opens x32061) (succProd x32061) x32061.prod (cands x32061 32761) = true := by
  decide +kernel

theorem d32061 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x32061 y32061 32761 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c32061

def x32006 : List ℕ := [79, 73, 37, 31, 19, 3, 47, 7, 13]
def y32006 : List ℕ := [631, 157, 127, 61, 5]

set_option maxHeartbeats 0 in
theorem c32006 : search [(x32061, y32061, 32761)]
    100000 x32006 y32006 625 (opens x32006) (succProd x32006) x32006.prod (cands x32006 625) = true := by
  decide +kernel

theorem d32006 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x32006 y32006 625 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d32061 C) _ _ _ _ (by norm_num) c32006

def x29257 : List ℕ := [1202743, 524287, 150343, 131071, 18793, 16381, 9397, 8191, 6007, 5113, 2557, 1951,
    1279, 751, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y29257 : List ℕ := [4194271, 3995647, 1048573, 249727, 40903, 15607, 739, 487, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c29257 : search []
    100000 x29257 y29257 9621937 (opens x29257) (succProd x29257) x29257.prod (cands x29257 9621937) = true := by
  decide +kernel

theorem d29257 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x29257 y29257 9621937 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c29257

def x28417 : List ℕ := [524287, 150343, 131071, 18793, 16381, 9397, 8191, 6007, 5113, 2557, 1951, 1279, 751,
    127, 61, 37, 31, 19, 3, 47, 7, 13]
def y28417 : List ℕ := [249727, 40903, 15607, 739, 487, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c28417 : search [(x29257, y29257, 9621937)]
    100000 x28417 y28417 1048573 (opens x28417) (succProd x28417) x28417.prod (cands x28417 1048573) = true := by
  decide +kernel

theorem d28417 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x28417 y28417 1048573 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d29257 C) _ _ _ _ (by norm_num) c28417

def x27425 : List ℕ := [18793, 15607, 9397, 8191, 6007, 5113, 2557, 1951, 1279, 751, 127, 61, 37, 31, 19, 3,
    47, 7, 13]
def y27425 : List ℕ := [40903, 16381, 739, 487, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c27425 : search []
    100000 x27425 y27425 75169 (opens x27425) (succProd x27425) x27425.prod (cands x27425 75169) = true := by
  decide +kernel

theorem d27425 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27425 y27425 75169 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c27425

def x27358 : List ℕ := [5113, 2557, 1951, 1279, 751, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y27358 : List ℕ := [739, 487, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c27358 : search [(x27425, y27425, 75169), (x28417, y28417, 1048573)]
    100000 x27358 y27358 5113 (opens x27358) (succProd x27358) x27358.prod (cands x27358 5113) = true := by
  decide +kernel

theorem d27358 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27358 y27358 5113 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d27425 C
    · exact d28417 C) _ _ _ _ (by norm_num) c27358

def x27254 : List ℕ := [127, 61, 37, 31, 19, 3, 47, 7, 13]
def y27254 : List ℕ := [487, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c27254 : search [(x27358, y27358, 5113)]
    100000 x27254 y27254 505 (opens x27254) (succProd x27254) x27254.prod (cands x27254 505) = true := by
  decide +kernel

theorem d27254 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27254 y27254 505 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d27358 C) _ _ _ _ (by norm_num) c27254

def x25896 : List ℕ := [15583, 8191, 5113, 2557, 1279, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y25896 : List ℕ := [9397, 751, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c25896 : search []
    100000 x25896 y25896 15583 (opens x25896) (succProd x25896) x25896.prod (cands x25896 15583) = true := by
  decide +kernel

theorem d25896 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x25896 y25896 15583 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c25896

def x24896 : List ℕ := [18793, 9397, 8191, 5113, 2557, 1279, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y24896 : List ℕ := [16381, 15583, 751, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c24896 : search []
    100000 x24896 y24896 37585 (opens x24896) (succProd x24896) x24896.prod (cands x24896 37585) = true := by
  decide +kernel

theorem d24896 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24896 y24896 37585 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c24896

def x24412 : List ℕ := [2557, 1279, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y24412 : List ℕ := [751, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c24412 : search [(x24896, y24896, 37585), (x25896, y25896, 15583)]
    100000 x24412 y24412 5113 (opens x24412) (succProd x24412) x24412.prod (cands x24412 5113) = true := by
  decide +kernel

theorem d24412 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24412 y24412 5113 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d24896 C
    · exact d25896 C) _ _ _ _ (by norm_num) c24412

def x22495 : List ℕ := [47353, 23677, 15583, 11839, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y22495 : List ℕ := [16381, 10159, 9739, 9397, 6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c22495 : search []
    100000 x22495 y22495 94705 (opens x22495) (succProd x22495) x22495.prod (cands x22495 94705) = true := by
  decide +kernel

theorem d22495 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x22495 y22495 94705 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c22495

def x21816 : List ℕ := [8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y21816 : List ℕ := [9739, 9397, 6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c21816 : search [(x22495, y22495, 94705)]
    100000 x21816 y21816 8191 (opens x21816) (succProd x21816) x21816.prod (cands x21816 8191) = true := by
  decide +kernel

theorem d21816 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x21816 y21816 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d22495 C) _ _ _ _ (by norm_num) c21816

def x20778 : List ℕ := [131071, 75181, 38953, 37591, 19477, 9739, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47,
    7, 13]
def y20778 : List ℕ := [16381, 9397, 6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c20778 : search []
    100000 x20778 y20778 131071 (opens x20778) (succProd x20778) x20778.prod (cands x20778 131071) = true := by
  decide +kernel

theorem d20778 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x20778 y20778 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c20778

def x18618 : List ℕ := [524287, 327619, 131071, 18793, 16381, 9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3,
    47, 7, 13]
def y18618 : List ℕ := [1048573, 240319, 150343, 81919, 38959, 20479, 15583, 9739, 6007, 5119, 2539, 1279,
    739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c18618 : search []
    100000 x18618 y18618 2097145 (opens x18618) (succProd x18618) x18618.prod (cands x18618 2097145) = true := by
  decide +kernel

theorem d18618 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x18618 y18618 2097145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c18618

def x18547 : List ℕ := [9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y18547 : List ℕ := [15583, 9739, 6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c18547 : search [(x18618, y18618, 2097145)]
    100000 x18547 y18547 9397 (opens x18547) (succProd x18547) x18547.prod (cands x18547 9397) = true := by
  decide +kernel

theorem d18547 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x18547 y18547 9397 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d18618 C) _ _ _ _ (by norm_num) c18547

def x17562 : List ℕ := [131071, 20479, 15583, 9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y17562 : List ℕ := [18793, 16381, 9739, 6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c17562 : search []
    100000 x17562 y17562 131071 (opens x17562) (succProd x17562) x17562.prod (cands x17562 131071) = true := by
  decide +kernel

theorem d17562 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x17562 y17562 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c17562

def x16754 : List ℕ := [18793, 15583, 9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y16754 : List ℕ := [163819, 150343, 131071, 81919, 20479, 16381, 9739, 6007, 5119, 2539, 1279, 739, 79,
    73, 5]

set_option maxHeartbeats 0 in
theorem c16754 : search []
    100000 x16754 y16754 150337 (opens x16754) (succProd x16754) x16754.prod (cands x16754 150337) = true := by
  decide +kernel

theorem d16754 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x16754 y16754 150337 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c16754

def x15609 : List ℕ := [150343, 18793, 15583, 9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y15609 : List ℕ := [311659, 262111, 240319, 163819, 131071, 81919, 20479, 16381, 9739, 6007, 5119, 2539,
    1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c15609 : search []
    100000 x15609 y15609 300685 (opens x15609) (succProd x15609) x15609.prod (cands x15609 300685) = true := by
  decide +kernel

theorem d15609 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x15609 y15609 300685 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c15609

def x14468 : List ℕ := [131071, 18793, 15583, 9397, 8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y14468 : List ℕ := [311659, 262111, 240319, 163819, 150343, 81919, 20479, 16381, 9739, 6007, 5119, 2539,
    1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c14468 : search []
    100000 x14468 y14468 524281 (opens x14468) (succProd x14468) x14468.prod (cands x14468 524281) = true := by
  decide +kernel

theorem d14468 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x14468 y14468 524281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c14468

def x13949 : List ℕ := [8191, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y13949 : List ℕ := [6007, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c13949 : search [(x14468, y14468, 524281), (x15609, y15609, 300685), (x16754, y16754, 150337),
    (x17562, y17562, 131071), (x18547, y18547, 9397), (x20778, y20778, 131071), (x21816, y21816, 8191)]
    100000 x13949 y13949 8191 (opens x13949) (succProd x13949) x13949.prod (cands x13949 8191) = true := by
  decide +kernel

theorem d13949 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x13949 y13949 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d14468 C
    · exact d15609 C
    · exact d16754 C
    · exact d17562 C
    · exact d18547 C
    · exact d20778 C
    · exact d21816 C) _ _ _ _ (by norm_num) c13949

def x12585 : List ℕ := [9397, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y12585 : List ℕ := [9739, 8191, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c12585 : search []
    100000 x12585 y12585 9397 (opens x12585) (succProd x12585) x12585.prod (cands x12585 9397) = true := by
  decide +kernel

theorem d12585 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x12585 y12585 9397 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c12585

def x10655 : List ℕ := [131071, 81919, 75181, 37591, 8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7,
    13]
def y10655 : List ℕ := [38959, 36037, 20479, 16381, 15583, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739,
    79, 73, 5]

set_option maxHeartbeats 0 in
theorem c10655 : search []
    100000 x10655 y10655 131071 (opens x10655) (succProd x10655) x10655.prod (cands x10655 131071) = true := by
  decide +kernel

theorem d10655 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x10655 y10655 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c10655

def x10348 : List ℕ := [8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y10348 : List ℕ := [36037, 20479, 16381, 15583, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739, 79, 73,
    5]

set_option maxHeartbeats 0 in
theorem c10348 : search [(x10655, y10655, 131071)]
    100000 x10348 y10348 32761 (opens x10348) (succProd x10348) x10348.prod (cands x10348 32761) = true := by
  decide +kernel

theorem d10348 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x10348 y10348 32761 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d10655 C) _ _ _ _ (by norm_num) c10348

def x8442 : List ℕ := [1048447, 655351, 524287, 131071, 81919, 72073, 36037, 8191, 6007, 751, 487, 127, 61,
    37, 31, 19, 3, 47, 7, 13]
def y8442 : List ℕ := [262111, 40639, 20479, 16381, 15583, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739,
    79, 73, 5]

set_option maxHeartbeats 0 in
theorem c8442 : search []
    100000 x8442 y8442 1048447 (opens x8442) (succProd x8442) x8442.prod (cands x8442 1048447) = true := by
  decide +kernel

theorem d8442 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x8442 y8442 1048447 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c8442

def x7782 : List ℕ := [131071, 81919, 72073, 36037, 8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y7782 : List ℕ := [40639, 20479, 16381, 15583, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739, 79, 73,
    5]

set_option maxHeartbeats 0 in
theorem c7782 : search [(x8442, y8442, 1048447)]
    100000 x7782 y7782 131071 (opens x7782) (succProd x7782) x7782.prod (cands x7782 131071) = true := by
  decide +kernel

theorem d7782 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x7782 y7782 131071 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d8442 C) _ _ _ _ (by norm_num) c7782

def x7434 : List ℕ := [36037, 8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y7434 : List ℕ := [20479, 16381, 15583, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c7434 : search [(x7782, y7782, 131071)]
    100000 x7434 y7434 36037 (opens x7434) (succProd x7434) x7434.prod (cands x7434 36037) = true := by
  decide +kernel

theorem d7434 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x7434 y7434 36037 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d7782 C) _ _ _ _ (by norm_num) c7434

def x5353 : List ℕ := [524287, 15583, 8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y5353 : List ℕ := [444517, 311659, 262111, 189439, 163819, 131071, 93979, 81919, 40639, 37591, 20479,
    16381, 11839, 10159, 9739, 9397, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c5353 : search []
    100000 x5353 y5353 524287 (opens x5353) (succProd x5353) x5353.prod (cands x5353 524287) = true := by
  decide +kernel

theorem d5353 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5353 y5353 524287 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c5353

def x5265 : List ℕ := [8191, 6007, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y5265 : List ℕ := [11839, 10159, 9739, 9397, 5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c5265 : search [(x5353, y5353, 524287), (x7434, y7434, 36037), (x10348, y10348, 32761)]
    100000 x5265 y5265 8191 (opens x5265) (succProd x5265) x5265.prod (cands x5265 8191) = true := by
  decide +kernel

theorem d5265 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5265 y5265 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d5353 C
    · exact d7434 C
    · exact d10348 C) _ _ _ _ (by norm_num) c5265

def x5255 : List ℕ := [751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y5255 : List ℕ := [5119, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c5255 : search [(x5265, y5265, 8191), (x12585, y12585, 9397), (x13949, y13949, 8191)]
    100000 x5255 y5255 6001 (opens x5255) (succProd x5255) x5255.prod (cands x5255 6001) = true := by
  decide +kernel

theorem d5255 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5255 y5255 6001 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d5265 C
    · exact d12585 C
    · exact d13949 C) _ _ _ _ (by norm_num) c5255

def x2386 : List ℕ := [307945471, 33554167, 4194271, 1048573, 1048447, 524287, 131071, 37591, 8191, 5119,
    751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y2386 : List ℕ := [123019807, 6152191, 4811647, 2620927, 2096893, 262111, 75181, 36037, 16381, 15583,
    9397, 6007, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c2386 : search []
    100000 x2386 y2386 615890941 (opens x2386) (succProd x2386) x2386.prod (cands x2386 615890941) = true := by
  decide +kernel

theorem d2386 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x2386 y2386 615890941 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c2386

def x2364 : List ℕ := [1048447, 524287, 131071, 37591, 8191, 5119, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7,
    13]
def y2364 : List ℕ := [262111, 75181, 36037, 16381, 15583, 9397, 6007, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c2364 : search [(x2386, y2386, 615890941)]
    100000 x2364 y2364 1048447 (opens x2364) (succProd x2364) x2364.prod (cands x2364 1048447) = true := by
  decide +kernel

theorem d2364 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x2364 y2364 1048447 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d2386 C) _ _ _ _ (by norm_num) c2364

def x1917 : List ℕ := [37591, 8191, 5119, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y1917 : List ℕ := [75181, 36037, 16381, 15583, 9397, 6007, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c1917 : search [(x2364, y2364, 1048447)]
    100000 x1917 y1917 75181 (opens x1917) (succProd x1917) x1917.prod (cands x1917 75181) = true := by
  decide +kernel

theorem d1917 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1917 y1917 75181 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d2364 C) _ _ _ _ (by norm_num) c1917

def x85 : List ℕ := [524287, 131071, 36037, 8191, 5119, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y85 : List ℕ := [262111, 190753, 72073, 16381, 15583, 9397, 6007, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c85 : search []
    100000 x85 y85 524287 (opens x85) (succProd x85) x85.prod (cands x85 524287) = true := by
  decide +kernel

theorem d85 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x85 y85 524287 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c85

def x77 : List ℕ := [36037, 8191, 5119, 751, 487, 127, 61, 37, 31, 19, 3, 47, 7, 13]
def y77 : List ℕ := [72073, 16381, 15583, 9397, 6007, 2539, 1279, 739, 79, 73, 5]

set_option maxHeartbeats 0 in
theorem c77 : search [(x85, y85, 524287)]
    100000 x77 y77 72073 (opens x77) (succProd x77) x77.prod (cands x77 72073) = true := by
  decide +kernel

theorem d77 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x77 y77 72073 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d85 C) _ _ _ _ (by norm_num) c77

def x5 : List ℕ := [31, 19, 3, 47, 7, 13]
def y5 : List ℕ := [5]

set_option maxHeartbeats 0 in
theorem c5 : search [(x77, y77, 72073), (x1917, y1917, 75181), (x5255, y5255, 6001), (x24412, y24412, 5113),
    (x27254, y27254, 505), (x32006, y32006, 625), (x34316, y34316, 79), (x35208, y35208, 127)]
    100000 x5 y5 31 (opens x5) (succProd x5) x5.prod (cands x5 31) = true := by
  decide +kernel

theorem d5 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5 y5 31 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d77 C
    · exact d1917 C
    · exact d5255 C
    · exact d24412 C
    · exact d27254 C
    · exact d32006 C
    · exact d34316 C
    · exact d35208 C) _ _ _ _ (by norm_num) c5

def x0 : List ℕ := [3, 47, 7, 13]
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

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H3 := by
  refine ⟨63, fun n h hS he c47 => ?_⟩
  by_contra hlt
  have hm : 64 ≤ padicValNat 2 n := by omega
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h5P : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self 5)
  have h47P : 47 ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by norm_num,
      Nat.mem_primeFactors.mpr ⟨by norm_num, c47, h.2.ne'⟩⟩, by decide⟩
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) = P at hP E h5P h47P
  generalize padicValNat 2 n = m at E hm
  have hn5 : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, S3, -, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 5) (e := 2) (by norm_num)) E
  have h13d : 13 ∣ 1 + 5 ^ 2 := by norm_num
  have h13P := S7 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
  have h7P := S1 7 (by norm_num) (by norm_num) (hn5 (by norm_num)) 13 h13P (by norm_num)
  have h3P := S1 3 (by norm_num) (by norm_num) (hn5 (by norm_num)) 47 h47P (by norm_num)
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

end OMA.P_Erdos1052_z5_e2_part3

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H3 :=
  OMA.P_Erdos1052_z5_e2_part3.step_proof
