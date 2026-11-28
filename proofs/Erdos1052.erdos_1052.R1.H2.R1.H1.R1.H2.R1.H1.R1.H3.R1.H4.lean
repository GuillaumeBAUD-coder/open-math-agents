import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1.H4

Hypothesis H4 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1`: unitary perfect numbers
`n = 2 ^ a * 5 ^ 2 * (simple odd primes)` such that none of `11`, `23`, `47` divides `n` have `a ≤ 63`.

Credit: @aroth01. The base lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...)
are those of reductions `...R1.H2.R1.H1.R1` and `...R1.H2.R1.H1.R1.H2.R1`.

Setting. `P` is the set of simple odd primes (5 is not one of them). `13 ∣ 1 + 5 ^ 2` is a simple prime that
divides no `p + 1`, and `7` divides only `13 + 1`. Then `11`, `23` and `47` are not simple primes. Every simple prime `p` has
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
The kernel evaluates the search (`decide +kernel`). To keep each evaluation small the search is cut into 68
pieces (Section 7): a piece stops at the states (`holes`) where other pieces start. The cut was computed by a
script; nothing about it is trusted.
-/

namespace OMA.P_Erdos1052_z5_e2_part4

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

def x60486 : List ℕ := [3061, 1531, 991, 383, 313, 157, 127, 79, 73, 37, 31, 19, 3, 7, 13]
def y60486 : List ℕ := [2503, 191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c60486 : search []
    100000 x60486 y60486 6121 (opens x60486) (succProd x60486) x60486.prod (cands x60486 6121) = true := by
  decide +kernel

theorem d60486 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x60486 y60486 6121 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c60486

def x59037 : List ℕ := [20023, 8191, 7927, 3061, 2503, 1531, 991, 383, 313, 157, 127, 79, 73, 37, 31, 19, 3,
    7, 13]
def y59037 : List ℕ := [18541, 16381, 9343, 6121, 191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c59037 : search []
    100000 x59037 y59037 40045 (opens x59037) (succProd x59037) x59037.prod (cands x59037 40045) = true := by
  decide +kernel

theorem d59037 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x59037 y59037 40045 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c59037

def x57864 : List ℕ := [20023, 12241, 6121, 3061, 2503, 1531, 991, 383, 313, 157, 127, 79, 73, 37, 31, 19, 3,
    7, 13]
def y57864 : List ℕ := [24481, 18541, 9343, 8191, 7927, 191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c57864 : search []
    100000 x57864 y57864 40045 (opens x57864) (succProd x57864) x57864.prod (cands x57864 40045) = true := by
  decide +kernel

theorem d57864 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x57864 y57864 40045 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c57864

def x57064 : List ℕ := [6121, 3061, 2503, 1531, 991, 383, 313, 157, 127, 79, 73, 37, 31, 19, 3, 7, 13]
def y57064 : List ℕ := [8191, 7927, 191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c57064 : search [(x57864, y57864, 40045)]
    100000 x57064 y57064 6121 (opens x57064) (succProd x57064) x57064.prod (cands x57064 6121) = true := by
  decide +kernel

theorem d57064 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x57064 y57064 6121 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d57864 C) _ _ _ _ (by norm_num) c57064

def x56873 : List ℕ := [2503, 1531, 991, 383, 313, 157, 127, 79, 73, 37, 31, 19, 3, 7, 13]
def y56873 : List ℕ := [191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c56873 : search [(x57064, y57064, 6121), (x59037, y59037, 40045)]
    100000 x56873 y56873 2503 (opens x56873) (succProd x56873) x56873.prod (cands x56873 2503) = true := by
  decide +kernel

theorem d56873 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x56873 y56873 2503 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d57064 C
    · exact d59037 C) _ _ _ _ (by norm_num) c56873

def x56870 : List ℕ := [383, 313, 157, 127, 79, 73, 37, 31, 19, 3, 7, 13]
def y56870 : List ℕ := [191, 61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c56870 : search [(x56873, y56873, 2503), (x60486, y60486, 6121)]
    100000 x56870 y56870 765 (opens x56870) (succProd x56870) x56870.prod (cands x56870 765) = true := by
  decide +kernel

theorem d56870 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x56870 y56870 765 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d56873 C
    · exact d60486 C) _ _ _ _ (by norm_num) c56870

def x56355 : List ℕ := [73, 37, 31, 19, 3, 7, 13]
def y56355 : List ℕ := [61, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c56355 : search [(x56870, y56870, 765)]
    100000 x56355 y56355 73 (opens x56355) (succProd x56355) x56355.prod (cands x56355 73) = true := by
  decide +kernel

theorem d56355 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x56355 y56355 73 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d56870 C) _ _ _ _ (by norm_num) c56355

def x54277 : List ℕ := [9397, 8191, 5023, 1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y54277 : List ℕ := [3061, 313, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c54277 : search []
    100000 x54277 y54277 9397 (opens x54277) (succProd x54277) x54277.prod (cands x54277 9397) = true := by
  decide +kernel

theorem d54277 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x54277 y54277 9397 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c54277

def x52416 : List ℕ := [131071, 46471, 15583, 8191, 3061, 1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7,
    13]
def y52416 : List ℕ := [92941, 39877, 37591, 16381, 11617, 9397, 6121, 5023, 313, 191, 73, 59, 29, 11, 23,
    47, 5]

set_option maxHeartbeats 0 in
theorem c52416 : search []
    100000 x52416 y52416 131071 (opens x52416) (succProd x52416) x52416.prod (cands x52416 131071) = true := by
  decide +kernel

theorem d52416 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x52416 y52416 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c52416

def x51741 : List ℕ := [15583, 8191, 3061, 1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y51741 : List ℕ := [37591, 16381, 11617, 9397, 6121, 5023, 313, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c51741 : search [(x52416, y52416, 131071)]
    100000 x51741 y51741 31165 (opens x51741) (succProd x51741) x51741.prod (cands x51741 31165) = true := by
  decide +kernel

theorem d51741 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x51741 y51741 31165 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d52416 C) _ _ _ _ (by norm_num) c51741

def x50808 : List ℕ := [131071, 37591, 15583, 8191, 3061, 1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7,
    13]
def y50808 : List ℕ := [262111, 75181, 16381, 11617, 9397, 6121, 5023, 313, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c50808 : search []
    100000 x50808 y50808 524281 (opens x50808) (succProd x50808) x50808.prod (cands x50808 524281) = true := by
  decide +kernel

theorem d50808 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x50808 y50808 524281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c50808

def x50193 : List ℕ := [8191, 3061, 1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y50193 : List ℕ := [9397, 6121, 5023, 313, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c50193 : search [(x50808, y50808, 524281), (x51741, y51741, 31165)]
    100000 x50193 y50193 8191 (opens x50193) (succProd x50193) x50193.prod (cands x50193 8191) = true := by
  decide +kernel

theorem d50193 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x50193 y50193 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d50808 C
    · exact d51741 C) _ _ _ _ (by norm_num) c50193

def x49824 : List ℕ := [1531, 487, 383, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y49824 : List ℕ := [313, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c49824 : search [(x50193, y50193, 8191), (x54277, y54277, 9397)]
    100000 x49824 y49824 3061 (opens x49824) (succProd x49824) x49824.prod (cands x49824 3061) = true := by
  decide +kernel

theorem d49824 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x49824 y49824 3061 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d50193 C
    · exact d54277 C) _ _ _ _ (by norm_num) c49824

def x47308 : List ℕ := [18793, 15583, 9397, 8191, 6143, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y47308 : List ℕ := [16381, 5843, 2503, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c47308 : search []
    100000 x47308 y47308 18793 (opens x47308) (succProd x47308) x47308.prod (cands x47308 18793) = true := by
  decide +kernel

theorem d47308 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x47308 y47308 18793 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c47308

def x45777 : List ℕ := [4194271, 1994623, 786271, 524287, 131071, 24571, 18793, 16381, 15583, 9397, 8191,
    6143, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y45777 : List ℕ := [1048573, 150343, 49141, 40063, 5843, 2503, 1877, 1523, 887, 761, 443, 383, 191, 73,
    59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c45777 : search []
    100000 x45777 y45777 16777081 (opens x45777) (succProd x45777) x45777.prod (cands x45777 16777081) = true := by
  decide +kernel

theorem d45777 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x45777 y45777 16777081 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c45777

def x45752 : List ℕ := [9397, 8191, 6143, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y45752 : List ℕ := [5843, 2503, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c45752 : search [(x45777, y45777, 16777081), (x47308, y47308, 18793)]
    100000 x45752 y45752 9397 (opens x45752) (succProd x45752) x45752.prod (cands x45752 9397) = true := by
  decide +kernel

theorem d45752 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x45752 y45752 9397 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d45777 C
    · exact d47308 C) _ _ _ _ (by norm_num) c45752

def x45480 : List ℕ := [487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y45480 : List ℕ := [2503, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c45480 : search [(x45752, y45752, 9397)]
    100000 x45480 y45480 3889 (opens x45480) (succProd x45480) x45480.prod (cands x45480 3889) = true := by
  decide +kernel

theorem d45480 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x45480 y45480 3889 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d45752 C) _ _ _ _ (by norm_num) c45480

def x44086 : List ℕ := [9397, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y44086 : List ℕ := [15017, 8191, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11,
    23, 47, 5]

set_option maxHeartbeats 0 in
theorem c44086 : search []
    100000 x44086 y44086 9397 (opens x44086) (succProd x44086) x44086.prod (cands x44086 9397) = true := by
  decide +kernel

theorem d44086 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x44086 y44086 9397 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c44086

def x42833 : List ℕ := [20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y42833 : List ℕ := [37591, 36037, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887,
    761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c42833 : search []
    100000 x42833 y42833 40045 (opens x42833) (succProd x42833) x42833.prod (cands x42833 40045) = true := by
  decide +kernel

theorem d42833 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x42833 y42833 40045 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c42833

def x41408 : List ℕ := [262111, 160183, 131071, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31,
    19, 3, 7, 13]
def y41408 : List ℕ := [196583, 93503, 75181, 46751, 36037, 16381, 15583, 15017, 14207, 9397, 7103, 6143,
    5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c41408 : search []
    100000 x41408 y41408 524221 (opens x41408) (succProd x41408) x41408.prod (cands x41408 524221) = true := by
  decide +kernel

theorem d41408 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x41408 y41408 524221 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c41408

def x40756 : List ℕ := [37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y40756 : List ℕ := [75181, 46751, 36037, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523,
    887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c40756 : search [(x41408, y41408, 524221)]
    100000 x40756 y40756 75181 (opens x40756) (succProd x40756) x40756.prod (cands x40756 75181) = true := by
  decide +kernel

theorem d40756 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x40756 y40756 75181 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d41408 C) _ _ _ _ (by norm_num) c40756

def x38231 : List ℕ := [1048447, 524287, 160183, 75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61,
    37, 31, 19, 3, 7, 13]
def y38231 : List ℕ := [961097, 786431, 262111, 196583, 131071, 93503, 46751, 36037, 16381, 15583, 15017,
    14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c38231 : search []
    100000 x38231 y38231 1048447 (opens x38231) (succProd x38231) x38231.prod (cands x38231 1048447) = true := by
  decide +kernel

theorem d38231 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x38231 y38231 1048447 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c38231

def x37985 : List ℕ := [160183, 75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y37985 : List ℕ := [262111, 196583, 131071, 93503, 46751, 36037, 16381, 15583, 15017, 14207, 9397, 7103,
    6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c37985 : search [(x38231, y38231, 1048447)]
    100000 x37985 y37985 320365 (opens x37985) (succProd x37985) x37985.prod (cands x37985 320365) = true := by
  decide +kernel

theorem d37985 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x37985 y37985 320365 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d38231 C) _ _ _ _ (by norm_num) c37985

def x36925 : List ℕ := [131071, 75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y36925 : List ℕ := [524287, 262111, 196583, 160183, 93503, 46751, 36037, 16381, 15583, 15017, 14207,
    9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c36925 : search []
    100000 x36925 y36925 524281 (opens x36925) (succProd x36925) x36925.prod (cands x36925 524281) = true := by
  decide +kernel

theorem d36925 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x36925 y36925 524281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c36925

def x35623 : List ℕ := [4811581, 4194271, 2405791, 524287, 131071, 75181, 37591, 20023, 8191, 2503, 487, 313,
    157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y35623 : List ℕ := [3145721, 2562943, 1048573, 1048447, 786431, 262111, 196583, 160183, 93503, 46751,
    36037, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59,
    29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c35623 : search []
    100000 x35623 y35623 9623161 (opens x35623) (succProd x35623) x35623.prod (cands x35623 9623161) = true := by
  decide +kernel

theorem d35623 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x35623 y35623 9623161 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c35623

def x34126 : List ℕ := [2562943, 2405791, 524287, 131071, 75181, 37591, 20023, 8191, 2503, 487, 313, 157,
    127, 79, 61, 37, 31, 19, 3, 7, 13]
def y34126 : List ℕ := [3145721, 1048573, 1048447, 786431, 262111, 196583, 160183, 93503, 46751, 36037,
    16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11,
    23, 47, 5]

set_option maxHeartbeats 0 in
theorem c34126 : search []
    100000 x34126 y34126 2562943 (opens x34126) (succProd x34126) x34126.prod (cands x34126 2562943) = true := by
  decide +kernel

theorem d34126 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x34126 y34126 2562943 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c34126

def x34122 : List ℕ := [524287, 131071, 75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31,
    19, 3, 7, 13]
def y34122 : List ℕ := [1048573, 1048447, 786431, 262111, 196583, 160183, 93503, 46751, 36037, 16381, 15583,
    15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c34122 : search [(x34126, y34126, 2562943), (x35623, y35623, 9623161)]
    100000 x34122 y34122 2097145 (opens x34122) (succProd x34122) x34122.prod (cands x34122 2097145) = true := by
  decide +kernel

theorem d34122 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x34122 y34122 2097145 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d34126 C
    · exact d35623 C) _ _ _ _ (by norm_num) c34122

def x33028 : List ℕ := [524287, 131071, 75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31,
    19, 3, 7, 13]
def y33028 : List ℕ := [786431, 262111, 196583, 160183, 93503, 46751, 36037, 16381, 15583, 15017, 14207,
    9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c33028 : search [(x34122, y34122, 2097145)]
    100000 x33028 y33028 524287 (opens x33028) (succProd x33028) x33028.prod (cands x33028 524287) = true := by
  decide +kernel

theorem d33028 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x33028 y33028 524287 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d34122 C) _ _ _ _ (by norm_num) c33028

def x33016 : List ℕ := [75181, 37591, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y33016 : List ℕ := [93503, 46751, 36037, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523,
    887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c33016 : search [(x33028, y33028, 524287), (x36925, y36925, 524281), (x37985, y37985, 320365)]
    100000 x33016 y33016 75181 (opens x33016) (succProd x33016) x33016.prod (cands x33016 75181) = true := by
  decide +kernel

theorem d33016 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x33016 y33016 75181 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d33028 C
    · exact d36925 C
    · exact d37985 C) _ _ _ _ (by norm_num) c33016

def x31945 : List ℕ := [36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y31945 : List ℕ := [131071, 72073, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523,
    887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c31945 : search []
    100000 x31945 y31945 144145 (opens x31945) (succProd x31945) x31945.prod (cands x31945 144145) = true := by
  decide +kernel

theorem d31945 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x31945 y31945 144145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c31945

def x31060 : List ℕ := [131071, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y31060 : List ℕ := [160183, 72073, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523,
    887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c31060 : search []
    100000 x31060 y31060 131071 (opens x31060) (succProd x31060) x31060.prod (cands x31060 131071) = true := by
  decide +kernel

theorem d31060 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x31060 y31060 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c31060

def x30183 : List ℕ := [160183, 131071, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y30183 : List ℕ := [262111, 196583, 195071, 72073, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143,
    5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c30183 : search []
    100000 x30183 y30183 320365 (opens x30183) (succProd x30183) x30183.prod (cands x30183 320365) = true := by
  decide +kernel

theorem d30183 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x30183 y30183 320365 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c30183

def x29363 : List ℕ := [262111, 160183, 131071, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31,
    19, 3, 7, 13]
def y29363 : List ℕ := [524221, 196583, 195071, 72073, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143,
    5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c29363 : search []
    100000 x29363 y29363 524221 (opens x29363) (succProd x29363) x29363.prod (cands x29363 524221) = true := by
  decide +kernel

theorem d29363 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x29363 y29363 524221 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c29363

def x28274 : List ℕ := [524287, 524221, 262111, 160183, 131071, 36037, 20023, 8191, 2503, 487, 313, 157, 127,
    79, 61, 37, 31, 19, 3, 7, 13]
def y28274 : List ℕ := [864887, 786431, 780287, 196583, 195071, 72073, 48767, 16381, 15583, 15017, 14207,
    9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c28274 : search []
    100000 x28274 y28274 524287 (opens x28274) (succProd x28274) x28274.prod (cands x28274 524287) = true := by
  decide +kernel

theorem d28274 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x28274 y28274 524287 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c28274

def x27166 : List ℕ := [160183, 131071, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y27166 : List ℕ := [72073, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887,
    761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c27166 : search [(x28274, y28274, 524287), (x29363, y29363, 524221), (x30183, y30183, 320365)]
    100000 x27166 y27166 160183 (opens x27166) (succProd x27166) x27166.prod (cands x27166 160183) = true := by
  decide +kernel

theorem d27166 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x27166 y27166 160183 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d28274 C
    · exact d29363 C
    · exact d30183 C) _ _ _ _ (by norm_num) c27166

def x26162 : List ℕ := [72073, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y26162 : List ℕ := [196583, 195071, 160183, 131071, 48767, 16381, 15583, 15017, 14207, 9397, 7103, 6143,
    5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c26162 : search []
    100000 x26162 y26162 144145 (opens x26162) (succProd x26162) x26162.prod (cands x26162 144145) = true := by
  decide +kernel

theorem d26162 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x26162 y26162 144145 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c26162

def x24688 : List ℕ := [131071, 72073, 36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y24688 : List ℕ := [780287, 524287, 432437, 262111, 196583, 195071, 160183, 48767, 16381, 15583, 15017,
    14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c24688 : search []
    100000 x24688 y24688 524281 (opens x24688) (succProd x24688) x24688.prod (cands x24688 524281) = true := by
  decide +kernel

theorem d24688 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24688 y24688 524281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c24688

def x24453 : List ℕ := [36037, 20023, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y24453 : List ℕ := [16381, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383,
    191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c24453 : search [(x24688, y24688, 524281), (x26162, y26162, 144145), (x27166, y27166, 160183),
    (x31060, y31060, 131071), (x31945, y31945, 144145)]
    100000 x24453 y24453 36037 (opens x24453) (succProd x24453) x24453.prod (cands x24453 36037) = true := by
  decide +kernel

theorem d24453 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x24453 y24453 36037 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d24688 C
    · exact d26162 C
    · exact d27166 C
    · exact d31060 C
    · exact d31945 C) _ _ _ _ (by norm_num) c24453

def x23258 : List ℕ := [16381, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y23258 : List ℕ := [36037, 20023, 15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443,
    383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c23258 : search []
    100000 x23258 y23258 32761 (opens x23258) (succProd x23258) x23258.prod (cands x23258 32761) = true := by
  decide +kernel

theorem d23258 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x23258 y23258 32761 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c23258

def x22107 : List ℕ := [524287, 131071, 36037, 16381, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y22107 : List ℕ := [961151, 864887, 786431, 780287, 393143, 240287, 195071, 72073, 48767, 20023, 15583,
    15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c22107 : search []
    100000 x22107 y22107 1048573 (opens x22107) (succProd x22107) x22107.prod (cands x22107 1048573) = true := by
  decide +kernel

theorem d22107 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x22107 y22107 1048573 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c22107

def x21259 : List ℕ := [524287, 131071, 36037, 16381, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3,
    7, 13]
def y21259 : List ℕ := [780287, 393143, 240287, 195071, 72073, 48767, 20023, 15583, 15017, 14207, 9397, 7103,
    6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c21259 : search [(x22107, y22107, 1048573)]
    100000 x21259 y21259 524287 (opens x21259) (succProd x21259) x21259.prod (cands x21259 524287) = true := by
  decide +kernel

theorem d21259 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x21259 y21259 524287 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d22107 C) _ _ _ _ (by norm_num) c21259

def x21114 : List ℕ := [8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y21114 : List ℕ := [15583, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73,
    59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c21114 : search [(x21259, y21259, 524287), (x23258, y23258, 32761), (x24453, y24453, 36037), (x33016,
    y33016, 75181), (x40756, y40756, 75181), (x42833, y42833, 40045)]
    100000 x21114 y21114 16381 (opens x21114) (succProd x21114) x21114.prod (cands x21114 16381) = true := by
  decide +kernel

theorem d21114 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x21114 y21114 16381 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d21259 C
    · exact d23258 C
    · exact d24453 C
    · exact d33016 C
    · exact d40756 C
    · exact d42833 C) _ _ _ _ (by norm_num) c21114

def x19836 : List ℕ := [15583, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y19836 : List ℕ := [48767, 37591, 20023, 16381, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887,
    761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c19836 : search []
    100000 x19836 y19836 62329 (opens x19836) (succProd x19836) x19836.prod (cands x19836 62329) = true := by
  decide +kernel

theorem d19836 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x19836 y19836 62329 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c19836

def x18545 : List ℕ := [131071, 48767, 15583, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y18545 : List ℕ := [185221, 37591, 20023, 16381, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887,
    761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c18545 : search []
    100000 x18545 y18545 131071 (opens x18545) (succProd x18545) x18545.prod (cands x18545 131071) = true := by
  decide +kernel

theorem d18545 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x18545 y18545 131071 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c18545

def x17454 : List ℕ := [37591, 15583, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y17454 : List ℕ := [196583, 131071, 93497, 75181, 20023, 16381, 15017, 14207, 9397, 7103, 6143, 5843,
    1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c17454 : search []
    100000 x17454 y17454 150361 (opens x17454) (succProd x17454) x17454.prod (cands x17454 150361) = true := by
  decide +kernel

theorem d17454 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x17454 y17454 150361 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c17454

def x16536 : List ℕ := [131071, 37591, 15583, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y16536 : List ℕ := [524287, 262111, 240287, 196583, 93497, 75181, 20023, 16381, 15017, 14207, 9397, 7103,
    6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c16536 : search []
    100000 x16536 y16536 524281 (opens x16536) (succProd x16536) x16536.prod (cands x16536 524281) = true := by
  decide +kernel

theorem d16536 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x16536 y16536 524281 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c16536

def x15798 : List ℕ := [37591, 15583, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y15798 : List ℕ := [93497, 75181, 20023, 16381, 15017, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887,
    761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c15798 : search [(x16536, y16536, 524281), (x17454, y17454, 150361)]
    100000 x15798 y15798 75181 (opens x15798) (succProd x15798) x15798.prod (cands x15798 75181) = true := by
  decide +kernel

theorem d15798 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x15798 y15798 75181 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d16536 C
    · exact d17454 C) _ _ _ _ (by norm_num) c15798

def x14929 : List ℕ := [15017, 8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y14929 : List ℕ := [16381, 15583, 14207, 9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73,
    59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c14929 : search []
    100000 x14929 y14929 30033 (opens x14929) (succProd x14929) x14929.prod (cands x14929 30033) = true := by
  decide +kernel

theorem d14929 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x14929 y14929 30033 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c14929

def x14619 : List ℕ := [8191, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y14619 : List ℕ := [9397, 7103, 6143, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47,
    5]

set_option maxHeartbeats 0 in
theorem c14619 : search [(x14929, y14929, 30033), (x15798, y15798, 75181), (x18545, y18545, 131071), (x19836,
    y19836, 62329), (x21114, y21114, 16381)]
    100000 x14619 y14619 8191 (opens x14619) (succProd x14619) x14619.prod (cands x14619 8191) = true := by
  decide +kernel

theorem d14619 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x14619 y14619 8191 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d14929 C
    · exact d15798 C
    · exact d18545 C
    · exact d19836 C
    · exact d21114 C) _ _ _ _ (by norm_num) c14619

def x12473 : List ℕ := [4194271, 524287, 131071, 20023, 6143, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19,
    3, 7, 13]
def y12473 : List ℕ := [5085841, 3120643, 2562943, 1572607, 1048573, 160183, 37591, 36037, 24571, 15583,
    9397, 8191, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c12473 : search []
    100000 x12473 y12473 16777081 (opens x12473) (succProd x12473) x12473.prod (cands x12473 16777081) = true := by
  decide +kernel

theorem d12473 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x12473 y12473 16777081 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c12473

def x12443 : List ℕ := [6143, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y12443 : List ℕ := [15583, 9397, 8191, 5843, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47,
    5]

set_option maxHeartbeats 0 in
theorem c12443 : search [(x12473, y12473, 16777081)]
    100000 x12443 y12443 12285 (opens x12443) (succProd x12443) x12443.prod (cands x12443 12285) = true := by
  decide +kernel

theorem d12443 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x12443 y12443 12285 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d12473 C) _ _ _ _ (by norm_num) c12443

def x11503 : List ℕ := [5843, 2503, 487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y11503 : List ℕ := [20023, 9397, 8191, 1877, 1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c11503 : search []
    100000 x11503 y11503 23369 (opens x11503) (succProd x11503) x11503.prod (cands x11503 23369) = true := by
  decide +kernel

theorem d11503 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x11503 y11503 23369 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c11503

def x11372 : List ℕ := [487, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y11372 : List ℕ := [1523, 887, 761, 443, 383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c11372 : search [(x11503, y11503, 23369), (x12443, y12443, 12285), (x14619, y14619, 8191), (x44086,
    y44086, 9397), (x45480, y45480, 3889)]
    100000 x11372 y11372 973 (opens x11372) (succProd x11372) x11372.prod (cands x11372 973) = true := by
  decide +kernel

theorem d11372 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x11372 y11372 973 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d11503 C
    · exact d12443 C
    · exact d14619 C
    · exact d44086 C
    · exact d45480 C) _ _ _ _ (by norm_num) c11372

def x11068 : List ℕ := [313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y11068 : List ℕ := [383, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c11068 : search [(x11372, y11372, 973)]
    100000 x11068 y11068 313 (opens x11068) (succProd x11068) x11068.prod (cands x11068 313) = true := by
  decide +kernel

theorem d11068 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x11068 y11068 313 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d11372 C) _ _ _ _ (by norm_num) c11068

def x9561 : List ℕ := [40063, 37591, 383, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y9561 : List ℕ := [31231, 15493, 9397, 8191, 4513, 2503, 1951, 1531, 487, 191, 73, 59, 29, 11, 23, 47,
    5]

set_option maxHeartbeats 0 in
theorem c9561 : search []
    100000 x9561 y9561 40063 (opens x9561) (succProd x9561) x9561.prod (cands x9561 40063) = true := by
  decide +kernel

theorem d9561 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x9561 y9561 40063 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c9561

def x8981 : List ℕ := [383, 313, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y8981 : List ℕ := [9397, 8191, 4513, 2503, 1951, 1531, 487, 191, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c8981 : search [(x9561, y9561, 40063)]
    100000 x8981 y8981 12225 (opens x8981) (succProd x8981) x8981.prod (cands x8981 12225) = true := by
  decide +kernel

theorem d8981 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x8981 y8981 12225 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d9561 C) _ _ _ _ (by norm_num) c8981

def x7190 : List ℕ := [8191, 1951, 191, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y7190 : List ℕ := [262111, 249727, 131071, 46471, 39877, 37591, 16381, 15607, 11617, 9397, 5023, 487,
    313, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c7190 : search []
    100000 x7190 y7190 262081 (opens x7190) (succProd x7190) x7190.prod (cands x7190 262081) = true := by
  decide +kernel

theorem d7190 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x7190 y7190 262081 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c7190

def x6552 : List ℕ := [1951, 191, 157, 127, 79, 61, 37, 31, 19, 3, 7, 13]
def y6552 : List ℕ := [5023, 487, 313, 73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c6552 : search [(x7190, y7190, 262081)]
    100000 x6552 y6552 7801 (opens x6552) (succProd x6552) x6552.prod (cands x6552 7801) = true := by
  decide +kernel

theorem d6552 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x6552 y6552 7801 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d7190 C) _ _ _ _ (by norm_num) c6552

def x6538 : List ℕ := [127, 79, 61, 37, 31, 19, 3, 7, 13]
def y6538 : List ℕ := [73, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c6538 : search [(x6552, y6552, 7801), (x8981, y8981, 12225), (x11068, y11068, 313), (x49824, y49824,
    3061)]
    100000 x6538 y6538 127 (opens x6538) (succProd x6538) x6538.prod (cands x6538 127) = true := by
  decide +kernel

theorem d6538 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x6538 y6538 127 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d6552 C
    · exact d8981 C
    · exact d11068 C
    · exact d49824 C) _ _ _ _ (by norm_num) c6538

def x3619 : List ℕ := [262111, 149503, 131071, 15583, 8191, 631, 487, 383, 79, 73, 61, 37, 31, 19, 3, 7, 13]
def y3619 : List ℕ := [98047, 16381, 9343, 1531, 191, 157, 127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c3619 : search []
    100000 x3619 y3619 524221 (opens x3619) (succProd x3619) x3619.prod (cands x3619 524221) = true := by
  decide +kernel

theorem d3619 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x3619 y3619 524221 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c3619

def x1431 : List ℕ := [1048447, 524287, 131071, 98047, 15583, 8191, 631, 487, 383, 79, 73, 61, 37, 31, 19, 3,
    7, 13]
def y1431 : List ℕ := [1048573, 262111, 149503, 16381, 9343, 1531, 191, 157, 127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c1431 : search []
    100000 x1431 y1431 1048447 (opens x1431) (succProd x1431) x1431.prod (cands x1431 1048447) = true := by
  decide +kernel

theorem d1431 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1431 y1431 1048447 → False :=
  chunk_sound C _ (fun _ _ _ hmem => absurd hmem List.not_mem_nil) _ _ _ _ (by norm_num) c1431

def x1427 : List ℕ := [131071, 98047, 15583, 8191, 631, 487, 383, 79, 73, 61, 37, 31, 19, 3, 7, 13]
def y1427 : List ℕ := [262111, 149503, 16381, 9343, 1531, 191, 157, 127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c1427 : search [(x1431, y1431, 1048447)]
    100000 x1427 y1427 524281 (opens x1427) (succProd x1427) x1427.prod (cands x1427 524281) = true := by
  decide +kernel

theorem d1427 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1427 y1427 524281 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d1431 C) _ _ _ _ (by norm_num) c1427

def x1419 : List ℕ := [15583, 8191, 631, 487, 383, 79, 73, 61, 37, 31, 19, 3, 7, 13]
def y1419 : List ℕ := [16381, 9343, 1531, 191, 157, 127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c1419 : search [(x1427, y1427, 524281), (x3619, y3619, 524221)]
    100000 x1419 y1419 62329 (opens x1419) (succProd x1419) x1419.prod (cands x1419 62329) = true := by
  decide +kernel

theorem d1419 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1419 y1419 62329 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d1427 C
    · exact d3619 C) _ _ _ _ (by norm_num) c1419

def x1405 : List ℕ := [487, 383, 79, 73, 61, 37, 31, 19, 3, 7, 13]
def y1405 : List ℕ := [191, 157, 127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c1405 : search [(x1419, y1419, 62329)]
    100000 x1405 y1405 487 (opens x1405) (succProd x1405) x1405.prod (cands x1405 487) = true := by
  decide +kernel

theorem d1405 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x1405 y1405 487 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d1419 C) _ _ _ _ (by norm_num) c1405

def x918 : List ℕ := [79, 73, 61, 37, 31, 19, 3, 7, 13]
def y918 : List ℕ := [127, 59, 29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c918 : search [(x1405, y1405, 487)]
    100000 x918 y918 157 (opens x918) (succProd x918) x918.prod (cands x918 157) = true := by
  decide +kernel

theorem d918 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x918 y918 157 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d1405 C) _ _ _ _ (by norm_num) c918

def x726 : List ℕ := [37, 31, 19, 3, 7, 13]
def y726 : List ℕ := [29, 11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c726 : search [(x918, y918, 157), (x6538, y6538, 127), (x56355, y56355, 73)]
    100000 x726 y726 37 (opens x726) (succProd x726) x726.prod (cands x726 37) = true := by
  decide +kernel

theorem d726 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x726 y726 37 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact d918 C
    · exact d6538 C
    · exact d56355 C) _ _ _ _ (by norm_num) c726

def x5 : List ℕ := [19, 3, 7, 13]
def y5 : List ℕ := [11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c5 : search [(x726, y726, 37)]
    100000 x5 y5 19 (opens x5) (succProd x5) x5.prod (cands x5 19) = true := by
  decide +kernel

theorem d5 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x5 y5 19 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d726 C) _ _ _ _ (by norm_num) c5

def x0 : List ℕ := [7, 13]
def y0 : List ℕ := [11, 23, 47, 5]

set_option maxHeartbeats 0 in
theorem c0 : search [(x5, y5, 19)]
    100000 x0 y0 3 (opens x0) (succProd x0) x0.prod (cands x0 3) = true := by
  decide +kernel

theorem d0 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) : St P x0 y0 3 → False :=
  chunk_sound C _ (fun X Y N hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact d5 C) _ _ _ _ (by norm_num) c0

-- Section 8. The step.

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H4 := by
  refine ⟨63, fun n h hS he c11 c23 c47 => ?_⟩
  by_contra hlt
  have hm : 64 ≤ padicValNat 2 n := by omega
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h5P : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self 5)
  have h11P : 11 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun hq => c11 (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hq).1))
  have h23P : 23 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun hq => c23 (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hq).1))
  have h47P : 47 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun hq => c47 (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hq).1))
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) = P at hP E h5P h11P h23P h47P
  generalize padicValNat 2 n = m at E hm
  have hn5 : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, S3, -, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 5) (e := 2) (by norm_num)) E
  have h13d : 13 ∣ 1 + 5 ^ 2 := by norm_num
  have h13P := S7 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
  have h7P := S1 7 (by norm_num) (by norm_num) (hn5 (by norm_num)) 13 h13P (by norm_num)
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
    rcases hx with rfl | rfl <;> assumption
  · simp only [y0, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  · have hpp := (hP p hp).1
    have hp2 := (hP p hp).2
    interval_cases p <;> first | exact absurd rfl hp2 | exact absurd hpp (by norm_num)

end OMA.P_Erdos1052_z5_e2_part4

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1.H4 :=
  OMA.P_Erdos1052_z5_e2_part4.step_proof
