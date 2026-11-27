import FormalConjectures.ErdosProblems.«467»

/-!
# A one-colour sieve reduction for Erdős 467

The residues p / 3 at primes p = 2 mod 3 detect the factors of 3n+2.
With the prime cutoff x/d, each exceptional value 3n+2 is a prime
times a cofactor bounded by 3d. A fixed set of small trial divisors
thins these finitely many families. Unassigned large primes can then repair either colour.
-/

namespace OMA.R_Erdos467_erdos_467_R1

open Erdos467 Filter

/-- A prime-counting estimate in fixed arithmetic progressions. For every
desired saving, a fixed finite set of small trial divisors suffices.
For each cofactor k, write 3n+2 = kℓ with ℓ prime. Each trial prime
q = 1 mod 3 above 3d excludes one reduced class of ℓ modulo q. The
product of the surviving proportions tends to zero as K grows. -/
def H1 : Prop :=
  ∀ d t : ℕ, 2 ≤ d → 0 < t → ∃ K : ℕ, ∀ᶠ x : ℕ in atTop,
    let tail := (primesUpTo x).filter fun p => p % 3 = 2 ∧ x / d < p
    let trial := (primesUpTo K).filter fun p => p % 3 ≠ 2
    ((Finset.range x).filter fun n =>
      (∃ k ∈ Finset.Icc 1 (3 * d), k ∣ 3 * n + 2 ∧ ((3 * n + 2) / k).Prime) ∧
      ∀ q ∈ trial, ¬ q ∣ n).card ≤ tail.card / t

/-- One colour only. It may use primes 1 mod 3 above any fixed cutoff,
as well as any of the large tail primes. After paying one unused tail
prime per uncovered row there is still a positive fraction in reserve. -/
def H2 : Prop :=
  ∃ d t : ℕ, 2 ≤ d ∧ 0 < t ∧ ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
    let tail := (primesUpTo x).filter fun p => p % 3 = 2 ∧ x / d < p
    ∃ (S : Finset ℕ) (b : ℕ → ℕ),
      S ⊆ ((primesUpTo x).filter fun p => K < p ∧ p % 3 = 1) ∪ tail ∧
      tail.card / t +
        ((Finset.range x).filter fun n => ∀ p ∈ S, n % p ≠ b p % p).card ≤
        (tail \ S).card

lemma inert_factor (m : ℕ) (hm : m % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ p % 3 = 2 ∧ p ∣ m := by
  induction m using Nat.recOnMul with
  | zero => omega
  | one => omega
  | prime p hp => exact ⟨p, hp, hm, dvd_refl _⟩
  | mul a b ha hb =>
    rw [Nat.mul_mod] at hm
    have hor : a % 3 = 2 ∨ b % 3 = 2 := by
      by_contra! h
      have hA : a % 3 = 0 ∨ a % 3 = 1 := by omega
      have hB : b % 3 = 0 ∨ b % 3 = 1 := by omega
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp_all
    rcases hor with h | h
    · obtain ⟨p, hp, h3, hd⟩ := ha h
      exact ⟨p, hp, h3, dvd_mul_of_dvd_left hd _⟩
    · obtain ⟨p, hp, h3, hd⟩ := hb h
      exact ⟨p, hp, h3, dvd_mul_of_dvd_right hd _⟩

lemma affine_residue {p n : ℕ} (hp : p % 3 = 2) (hd : p ∣ 3 * n + 2) :
    n % p = (p / 3) % p := by
  have hc : Nat.Coprime 3 p := Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  apply Nat.ModEq.cancel_left_of_coprime hc.symm
  apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2)
  have h : 3 * (p / 3) + 2 = p := by omega
  rw [h]
  exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)).symm

lemma small_factor_or_bounded_cofactor {d x n : ℕ} (hd : 0 < d) (hn : n < x) :
    (∃ p : ℕ, p.Prime ∧ p % 3 = 2 ∧ p ≤ x / d ∧ p ∣ 3 * n + 2) ∨
      (∃ k ∈ Finset.Icc 1 (3 * d), k ∣ 3 * n + 2 ∧ ((3 * n + 2) / k).Prime) := by
  obtain ⟨p, hp, h3, hdiv⟩ := inert_factor (3 * n + 2) (by omega)
  by_cases h : p ≤ x / d
  · exact Or.inl ⟨p, hp, h3, h, hdiv⟩
  obtain ⟨k, hk⟩ := hdiv
  have hxp : x < p * d := (Nat.div_lt_iff_lt_mul hd).mp (by omega)
  have hk0 : 0 < k := by
    by_contra! hz
    simp [show k = 0 by omega] at hk
  have hks : k ≤ 3 * d := by
    by_contra! hlarge
    have hm := Nat.mul_le_mul_left p hlarge.le
    nlinarith only [hm, hxp, hk, hn]
  exact Or.inr ⟨k, Finset.mem_Icc.mpr ⟨hk0, hks⟩, ⟨p, by rw [hk, Nat.mul_comm]⟩,
    by simpa [hk, Nat.mul_div_cancel _ hk0] using hp⟩

lemma patch {x : ℕ} {base reserve holes : Finset ℕ} (r : ℕ → ℕ)
    (hd : Disjoint base reserve) (hc : holes.card ≤ reserve.card)
    (hcover : ∀ n < x, n ∉ holes → ∃ p ∈ base, n % p = r p % p) :
    ∃ a : ℕ → ℕ, ∀ n < x, ∃ p ∈ base ∪ reserve, n % p = a p % p := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card holes ≤ Fintype.card reserve by simpa using hc)
  let pick (i : holes) : ℕ := (f i).val
  have hi : Function.Injective pick := fun _ _ h => f.injective (Subtype.ext h)
  let fill := Function.extend pick (fun i : holes => i.val) (fun _ => 0)
  refine ⟨fun p => if p ∈ base then r p else fill p, ?_⟩
  intro n hn
  by_cases hh : n ∈ holes
  · let i : holes := ⟨n, hh⟩
    have hr : pick i ∈ reserve := (f i).property
    have hb : pick i ∉ base := fun h => Finset.disjoint_left.mp hd h hr
    refine ⟨pick i, Finset.mem_union_right _ hr, ?_⟩
    simp only [if_neg hb]
    rw [show fill (pick i) = n from hi.extend_apply _ _ i]
  · obtain ⟨p, hp, he⟩ := hcover n hn hh
    exact ⟨p, Finset.mem_union_left _ hp, by simpa [hp] using he⟩

lemma combine {x : ℕ} (hx : 0 < x) {R B : Finset ℕ}
    (hr : R ⊆ primesUpTo x) (hb : B ⊆ primesUpTo x) (hd : Disjoint R B)
    (r b : ℕ → ℕ) (cr : ∀ n < x, ∃ p ∈ R, n % p = r p % p)
    (cb : ∀ n < x, ∃ p ∈ B, n % p = b p % p) :
    ∃ a A B, PrimePartitionUpTo x A B ∧ CongruenceCover x a A B := by
  classical
  let A := primesUpTo x \ B
  have hA : R ⊆ A := fun _ h =>
    Finset.mem_sdiff.mpr ⟨hr h, Finset.disjoint_left.mp hd h⟩
  obtain ⟨p, hp, _⟩ := cr 0 hx
  obtain ⟨q, hq, _⟩ := cb 0 hx
  refine ⟨fun p => if p ∈ B then b p else r p, A, B,
    ⟨⟨p, hA hp⟩, ⟨q, hq⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.union_comm B A ▸ Finset.union_sdiff_of_subset hb
  · exact Finset.disjoint_iff_inter_eq_empty.mp Finset.sdiff_disjoint
  · intro n hn
    obtain ⟨p, hp, he⟩ := cr n hn
    obtain ⟨q, hq, hf⟩ := cb n hn
    exact ⟨⟨p, hA hp, by simpa [Finset.disjoint_left.mp hd hp] using he⟩,
      ⟨q, hq, by simpa [hq] using hf⟩⟩

theorem main : H1 → H2 → type_of% @Erdos467.erdos_467 := by
  classical
  intro estimate sieve
  obtain ⟨d, t, hd, ht, sparse⟩ := sieve
  obtain ⟨K, hexc⟩ := estimate d t hd ht
  filter_upwards [hexc, sparse K, eventually_ge_atTop K, eventually_ge_atTop 1]
    with x hred hblue hK hx
  let P := primesUpTo x
  let tail := P.filter fun p => p % 3 = 2 ∧ x / d < p
  let core := P.filter fun p => p % 3 = 2 ∧ p ≤ x / d
  let trial := (primesUpTo K).filter fun p => p % 3 ≠ 2
  let E := (Finset.range x).filter fun n =>
    (∃ k ∈ Finset.Icc 1 (3 * d), k ∣ 3 * n + 2 ∧ ((3 * n + 2) / k).Prime) ∧
      ∀ q ∈ trial, ¬ q ∣ n
  change E.card ≤ tail.card / t at hred
  obtain ⟨S, b, hs, budget⟩ := hblue
  let F := (Finset.range x).filter fun n => ∀ p ∈ S, n % p ≠ b p % p
  change tail.card / t + F.card ≤ (tail \ S).card at budget
  let R := core ∪ trial
  have hrow : ∀ n < x, n ∉ E →
      ∃ p ∈ R, n % p = (if p % 3 = 2 then p / 3 else 0) % p := by
    intro n hn hgood
    rcases small_factor_or_bounded_cofactor (by omega : 0 < d) hn with ⟨p, hprime, hp, hsize, hd⟩ | hbig
    · have hP : p ∈ P := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hsize.trans (Nat.div_le_self _ _)⟩, hprime⟩
      have hcore : p ∈ core := Finset.mem_filter.mpr ⟨hP, hp, hsize⟩
      exact ⟨p, Finset.mem_union_left _ hcore, by simpa [hp] using affine_residue hp hd⟩
    · have hex : ∃ q ∈ trial, q ∣ n := by
        by_contra! hnq
        exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hbig, hnq⟩)
      obtain ⟨q, hq, hd⟩ := hex
      have hq3 := (Finset.mem_filter.mp hq).2
      exact ⟨q, Finset.mem_union_right _ hq, by simp [hq3, Nat.mod_eq_zero_of_dvd hd]⟩
  have htP : tail ⊆ P := Finset.filter_subset _ _
  have hrP : R ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).1
    · have hpk := Finset.mem_filter.mp (Finset.mem_filter.mp h).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hpk.1).1, le_trans (Finset.mem_Icc.mp hpk.1).2 hK⟩, hpk.2⟩
  have hrt : Disjoint R tail := by
    apply Finset.disjoint_left.mpr
    intro p hR hp
    have htt := (Finset.mem_filter.mp hp).2
    rcases Finset.mem_union.mp hR with hc | htr
    · exact (not_le.mpr htt.2) (Finset.mem_filter.mp hc).2.2
    · exact (Finset.mem_filter.mp htr).2 htt.1
  have hsP : S ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp (hs hp) with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact htP h
  have hrs : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro p hr hS
    rcases Finset.mem_union.mp (hs hS) with h | h
    · have h1 := (Finset.mem_filter.mp h).2
      rcases Finset.mem_union.mp hr with h | h
      · have := (Finset.mem_filter.mp h).2.1
        omega
      · have hpk := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
        exact (not_le.mpr h1.1) (Finset.mem_Icc.mp hpk).2
    · exact Finset.disjoint_left.mp hrt hr h
  let U := tail \ S
  obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq
    (show E.card ≤ U.card by change E.card ≤ (tail \ S).card; omega)
  have hVcard : F.card ≤ (U \ T).card := by
    rw [Finset.card_sdiff_of_subset hTU, hTcard]
    change F.card ≤ (tail \ S).card - E.card
    omega
  have hTtail : T ⊆ tail := hTU.trans Finset.sdiff_subset
  have hVtail : U \ T ⊆ tail := Finset.sdiff_subset.trans Finset.sdiff_subset
  have hSU : Disjoint S U := Finset.disjoint_sdiff
  obtain ⟨r', cr⟩ := patch (fun p => if p % 3 = 2 then p / 3 else 0)
    (hrt.mono_right hTtail) hTcard.ge hrow
  obtain ⟨b', cb⟩ := patch b (hSU.mono_right Finset.sdiff_subset) hVcard (by
    intro n hn hnF
    by_contra! h
    exact hnF (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, h⟩))
  apply combine (by omega : 0 < x)
    (Finset.union_subset hrP (hTtail.trans htP))
    (Finset.union_subset hsP (hVtail.trans htP)) _ r' b' cr cb
  exact Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨hrs, hrt.mono_right hVtail⟩,
     Finset.disjoint_union_right.mpr ⟨(hSU.mono_right hTU).symm, Finset.disjoint_sdiff⟩⟩

end OMA.R_Erdos467_erdos_467_R1
