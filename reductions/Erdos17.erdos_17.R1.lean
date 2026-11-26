import FormalConjectures.ErdosProblems.«17»

-- Reduction Erdos17.erdos_17.R1
-- Credit: @desenyon

/-!
# A sparse obstruction to the infinitude of cluster primes

A single permanently missing difference is one obstruction. Once every even
difference has a witness, a last cluster prime would force an increasing chain
of even differences. Each term's first witness lies at least nine beyond the
next term. Taking the longest possible jump along the chain puts the first
upper prime for each retained term into the following shifted interval.
-/

namespace OMA.R_Erdos17_erdos_17_R1

/-- Each even difference has a prime-pair witness with unrestricted endpoint. -/
def H1 : Prop :=
  ∀ i : ℕ, ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime

/-- Suppose each even difference `a k` has a witness whose upper prime lies in
`[a (k+1) + 9, a (k+2) + 9)`. At least one term also has a witness below
the left endpoint of that interval. -/
def H2 : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → (∀ k, Even (a k)) →
    (∀ k, ∃ r : ℕ, r.Prime ∧ (a k + r).Prime ∧
      a (k + 1) + 9 ≤ a k + r ∧ a k + r < a (k + 2) + 9) →
    ∃ k r : ℕ, r.Prime ∧ (a k + r).Prime ∧ a k + r < a (k + 1) + 9

/-- A missing difference at a prime endpoint has an odd composite deficit.
The three smaller possible odd deficits, 3, 5, and 7, give witnesses directly. -/
theorem composite_deficit {p n : ℕ} (hp : p.Prime) (hn : Even n) (hle : n + 3 ≤ p)
    (hmiss : ¬ ∃ r : ℕ, r.Prime ∧ (n + r).Prime ∧ n + r ≤ p) :
    9 ≤ p - n ∧ Odd (p - n) ∧ ¬ (p - n).Prime := by
  have hnp : ¬ (p - n).Prime := by
    intro h
    have heq : n + (p - n) = p := by omega
    exact hmiss ⟨p - n, h, heq.symm ▸ hp, heq.le⟩
  have hodd : Odd (p - n) := by
    obtain ⟨j, hj⟩ := hn
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨(p - n) / 2, by omega⟩
  refine ⟨?_, hodd, hnp⟩
  obtain ⟨k, hk⟩ := hodd
  by_contra! hsmall
  have hcases : p - n = 3 ∨ p - n = 5 ∨ p - n = 7 := by omega
  rcases hcases with h | h | h <;> rw [h] at hnp <;> norm_num at hnp

private theorem exists_missing {p : ℕ} (hp : p.Prime) (hbad : ¬ Erdos17.IsClusterPrime p) :
    ∃ i : ℕ, 2 * i + 3 ≤ p ∧ ¬ ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime ∧ 2 * i + r ≤ p := by
  by_contra! hall
  apply hbad
  refine ⟨hp, ?_⟩
  rintro n ⟨i, hi⟩ hle
  have heq : n = 2 * i := by omega
  obtain ⟨r, hr, hpr, hbound⟩ := hall i (by omega)
  exact ⟨2 * i + r, r, hpr, hr, hbound, by omega, by omega⟩

/-- If cluster primes stop, follow the least missing difference to its first
upper prime. Every smaller difference survives that move. The next missing
difference is at least nine below the new endpoint. -/
private theorem obstruction_chain (hpairs : H1) (N : ℕ)
    (hstop : ∀ p : ℕ, N < p → ¬ Erdos17.IsClusterPrime p) :
    ∃ a u : ℕ → ℕ, StrictMono a ∧ (∀ k, Even (a k)) ∧
      (∀ k, ∃ r : ℕ, r.Prime ∧ (u k).Prime ∧ a k + r = u k) ∧
      (∀ k, a (k + 1) + 9 ≤ u k) ∧
      ∀ k r : ℕ, r.Prime → (a k + r).Prime → u k ≤ a k + r := by
  classical
  let first (i : ℕ) := Nat.find (hpairs i)
  let upper (i : ℕ) := 2 * i + first i
  have hfirst (i : ℕ) : (first i).Prime ∧ (upper i).Prime := Nat.find_spec (hpairs i)
  have hmin (i r : ℕ) (hr : r.Prime) (hpr : (2 * i + r).Prime) : upper i ≤ 2 * i + r :=
    Nat.add_le_add_left (Nat.find_min' (hpairs i) ⟨hr, hpr⟩) _
  have hex (p : ℕ) : ∃ i, p < upper i := ⟨p + 1, by dsimp [upper]; omega⟩
  let hole (p : ℕ) := Nat.find (hex p)
  have hhole (p : ℕ) : p < upper (hole p) := Nat.find_spec (hex p)
  have hprefix {p i : ℕ} (hi : i < hole p) : upper i ≤ p :=
    le_of_not_gt (Nat.find_min (hex p) hi)
  have hstep (p : ℕ) : hole p < hole (upper (hole p)) := by
    have hnew := hhole (upper (hole p))
    rcases lt_trichotomy (hole (upper (hole p))) (hole p) with h | h | h
    · have := hprefix h
      have := hhole p
      omega
    · rw [h] at hnew
      omega
    · exact h
  have hmargin {p : ℕ} (hp : p.Prime) (hpN : N < p) : 2 * hole p + 9 ≤ p := by
    obtain ⟨i, hle, hmiss⟩ := exists_missing hp (hstop p hpN)
    have hibad : p < upper i := by
      by_contra! hu
      exact hmiss ⟨first i, (hfirst i).1, (hfirst i).2, hu⟩
    have hidx : hole p ≤ i := Nat.find_min' (hex p) hibad
    have hno : ¬ ∃ r : ℕ, r.Prime ∧ (2 * hole p + r).Prime ∧ 2 * hole p + r ≤ p := by
      rintro ⟨r, hr, hpr, hrle⟩
      exact (hhole p).not_ge ((hmin _ _ hr hpr).trans hrle)
    have := (composite_deficit hp (even_two_mul _) (by omega) hno).1
    omega
  let c : ℕ → ℕ := fun k => (fun p => upper (hole p))^[k] (N + 1)
  have hc (k : ℕ) : c (k + 1) = upper (hole (c k)) := Function.iterate_succ_apply' _ _ _
  have hcN (k : ℕ) : N < c k := by
    induction k with
    | zero => exact Nat.lt_succ_self _
    | succ k ih => rw [hc]; exact ih.trans (hhole _)
  have hp (k : ℕ) : (c (k + 1)).Prime := (hc k) ▸ (hfirst (hole (c k))).2
  refine ⟨fun k => 2 * hole (c k), fun k => c (k + 1),
    strictMono_nat_of_lt_succ (fun k => ?_), fun k => even_two_mul _,
    (fun k => ⟨first (hole (c k)), (hfirst _).1, hp k, (hc k).symm⟩),
    fun k => hmargin (hp k) (hcN (k + 1)), ?_⟩
  · change 2 * hole (c k) < 2 * hole (c (k + 1))
    rw [hc]
    have := hstep (c k)
    omega
  · intro k r hr hpr
    exact (hc k).trans_le (hmin _ _ hr hpr)

/-- Skip to the last term still lying nine below the current witness. After
this jump, the witness lies below the next retained term plus nine. -/
private theorem pack_chain (a u : ℕ → ℕ) (ha : StrictMono a)
    (hgap : ∀ k, a (k + 1) + 9 ≤ u k) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∀ k,
      a (j (k + 1)) + 9 ≤ u (j k) ∧ u (j k) < a (j (k + 2)) + 9 := by
  classical
  have hex (i : ℕ) : ∃ m, u i < a m + 9 := by
    refine ⟨u i, ?_⟩
    have h : u i ≤ a (u i) := ha.id_le _
    omega
  let jump (i : ℕ) := Nat.find (hex i) - 1
  have hindex (i : ℕ) : i + 1 < Nat.find (hex i) := by
    by_contra! hle
    have hu := Nat.find_spec (hex i)
    have hmono := ha.monotone hle
    have hbound := hgap i
    omega
  have hlt (i : ℕ) : i < jump i := by
    dsimp [jump]
    have := hindex i
    omega
  have hleft (i : ℕ) : a (jump i) + 9 ≤ u i := by
    apply le_of_not_gt (Nat.find_min (hex i) ?_)
    dsimp [jump]
    have := hindex i
    omega
  have hright (i : ℕ) : u i < a (jump i + 1) + 9 := by
    have heq : jump i + 1 = Nat.find (hex i) := by
      dsimp [jump]
      have := hindex i
      omega
    rw [heq]
    exact Nat.find_spec (hex i)
  let j : ℕ → ℕ := fun k => jump^[k] 0
  have hj (k : ℕ) : j (k + 1) = jump (j k) := Function.iterate_succ_apply' _ _ _
  have hinc (k : ℕ) : j k < j (k + 1) := by rw [hj]; exact hlt _
  refine ⟨j, strictMono_nat_of_lt_succ hinc, fun k => ⟨hj k ▸ hleft _, ?_⟩⟩
  have h := hright (j k)
  rw [← hj] at h
  exact lt_of_lt_of_le h (Nat.add_le_add_right (ha.monotone (hinc (k + 1))) 9)

theorem main : H1 → H2 → type_of% @Erdos17.erdos_17 := by
  intro hpairs hinterval
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  by_contra hnone
  have hstop (p : ℕ) (hp : N < p) (hc : Erdos17.IsClusterPrime p) : False :=
    hnone ⟨p, hc, hp⟩
  obtain ⟨a, u, ha, he, hu, hgap, hmin⟩ := obstruction_chain hpairs N hstop
  obtain ⟨j, hj, hpack⟩ := pack_chain a u ha hgap
  obtain ⟨k, r, hr, hpr, hle⟩ := hinterval (a ∘ j) (ha.comp hj) (fun k => he _) (fun k => by
    obtain ⟨r, hr, hpr, heq⟩ := hu (j k)
    exact ⟨r, hr, heq.symm ▸ hpr, (hpack k).1.trans_eq heq.symm,
      heq.trans_lt (hpack k).2⟩)
  exact hle.not_ge ((hpack k).1.trans (hmin _ r hr hpr))

/-- Both hypotheses are necessary. At a cluster prime above the start of the
sequence, take the last term at most the prime minus three. -/
theorem necessary (h : {p : ℕ | Erdos17.IsClusterPrime p}.Infinite) : H1 ∧ H2 := by
  classical
  have witness {n p : ℕ} (hc : Erdos17.IsClusterPrime p) (he : Even n) (hle : n + 3 ≤ p) :
      ∃ r : ℕ, r.Prime ∧ (n + r).Prime ∧ n + r ≤ p := by
    obtain ⟨q, r, hq, hr, hqp, _, heq⟩ := hc.2 he (by omega)
    have hnr : n + r = q := by omega
    exact ⟨r, hr, hnr.symm ▸ hq, hnr.trans_le hqp⟩
  constructor
  · intro i
    obtain ⟨p, hp, hbig⟩ := h.exists_gt (2 * i + 3)
    obtain ⟨r, hr, hpr, _⟩ := witness hp (even_two_mul i) hbig.le
    exact ⟨r, hr, hpr⟩
  · intro a ha he _
    obtain ⟨p, hp, hbig⟩ := h.exists_gt (a 0 + 3)
    have hex : ∃ m, p < a m + 3 := by
      refine ⟨p, ?_⟩
      have hle : p ≤ a p := ha.id_le _
      omega
    have hcross := Nat.find_spec hex
    have hpos : Nat.find hex ≠ 0 := by intro hz; rw [hz] at hcross; omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hklt : k < Nat.find hex := by omega
    have hleft : a k + 3 ≤ p := le_of_not_gt (Nat.find_min hex hklt)
    have hright : p < a (k + 1) + 3 := by simpa only [hk] using hcross
    obtain ⟨r, hr, hpr, hle⟩ := witness hp (he k) hleft
    exact ⟨k, r, hr, hpr, by omega⟩

end OMA.R_Erdos17_erdos_17_R1
