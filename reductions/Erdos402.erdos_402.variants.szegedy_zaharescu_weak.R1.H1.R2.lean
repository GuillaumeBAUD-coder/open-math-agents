import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1
import Mathlib

-- Reduction Erdos402.erdos_402.variants.szegedy_zaharescu_weak.R1.H1.R2 of step Erdos402.erdos_402.variants.szegedy_zaharescu_weak.R1.H1
-- Credit: @rickmanelius

/-! Graham's inequality for primitive families of size `n`, for large `n`.

Suppose every directed quotient `a / gcd a b` is below `n`. A multiple of a prime `q` with
`n < 2q` is ruled out by a two-layer count of `q`-adic valuations (`graham_of_multiple`).
A prime `n` is then ruled out by residues modulo `n`. For composite `n`, residues modulo a
prime `p` just below `2n` are distinct and nonzero, so many values `k` occur together with
`p - k`; each such key comes from a pair `m * d, (p - m) * d` of elements with `p/2 < m ≤ n`.
A prime `m` cannot occur, and a composite `m` contributes at most one more dilation than it
has normalized divisor pairs. The prime-location input H1 and the divisor-pair estimate H2
then leave too few keys.

H1 and H2 are, word for word, the two hypotheses of the merged equality-case reduction of
this problem (PR 4628); the same H2 is proved upstream (PR 4898). The finite arguments here are
written independently, following the ideas of PR 4628 and of Balasubramanian and
Soundararajan, On a conjecture of R. L. Graham, Acta Arith. 75 (1996). -/

namespace OMA.E402H1
open Finset

/-- `p ∣ a / gcd a b` exactly when the `p`-adic valuation of `a` exceeds that of `b`. -/
lemma dvd_div_gcd_iff {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    p ∣ a / a.gcd b ↔ b.factorization p < a.factorization p := by
  have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hq : a / a.gcd b ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg).ne'
  rw [hp.dvd_iff_one_le_factorization hq, Nat.factorization_div (Nat.gcd_dvd_left a b),
    Nat.factorization_gcd ha.ne' hb.ne']
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply]
  rcases le_total (a.factorization p) (b.factorization p) with h | h
  · rw [inf_of_le_left h]; omega
  · rw [inf_of_le_right h]; omega

/-- Ratios are positive. -/
lemma div_gcd_pos {a b : ℕ} (ha : 0 < a) : 0 < a / a.gcd b :=
  Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) (Nat.gcd_pos_of_pos_left b ha)

/-- Two-layer case of Graham's inequality for any `n`: if a prime `q` with `n/2 < q ≤ n` has
non-constant valuation on `A` (`|A| = n`, `0 ∉ A`), then some ratio `a / gcd a b` is at least `n`. -/
lemma two_layer_ineq {q n : ℕ} (hq : q.Prime) (hn2q : n < 2 * q) (A : Finset ℕ)
    (h0 : 0 ∉ A) (hcard : A.card = n) (hlt : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b < n)
    (hflat : ∃ a ∈ A, ∃ b ∈ A, a.factorization q ≠ b.factorization q) : False := by
  have hq2 := hq.two_le
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hflat
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image A (fun a => a.factorization q) ⟨a₁, ha₁⟩
  let A0 := A.filter (fun a => a.factorization q = m.factorization q)
  let A1 := A.filter (fun a => ¬ a.factorization q = m.factorization q)
  have hcard01 : A0.card + A1.card = n := by
    rw [Finset.card_filter_add_card_filter_not]; exact hcard
  have hmA0 : m ∈ A0 := Finset.mem_filter.2 ⟨hm, rfl⟩
  have hA0mem : ∀ b ∈ A0, b ∈ A ∧ b.factorization q = m.factorization q := fun b hb =>
    Finset.mem_filter.1 hb
  have hA1mem : ∀ a ∈ A1, a ∈ A ∧ m.factorization q < a.factorization q := by
    intro a ha
    obtain ⟨haA, hne'⟩ := Finset.mem_filter.1 ha
    exact ⟨haA, lt_of_le_of_ne (hmin a haA) (Ne.symm hne')⟩
  have hA1ne : A1.Nonempty := by
    by_cases h1 : a₁.factorization q = m.factorization q
    · exact ⟨b₁, Finset.mem_filter.2 ⟨hb₁, fun h2 => hab₁ (h1.trans h2.symm)⟩⟩
    · exact ⟨a₁, Finset.mem_filter.2 ⟨ha₁, h1⟩⟩
  have K1 : ∀ a ∈ A1, ∀ b ∈ A0, a / a.gcd b = q := by
    intro a ha b hb
    obtain ⟨haA, hva⟩ := hA1mem a ha
    obtain ⟨hbA, hvb⟩ := hA0mem b hb
    have hd : q ∣ a / a.gcd b := (dvd_div_gcd_iff hq (hpos a haA) (hpos b hbA)).2 (by omega)
    obtain ⟨t, ht⟩ := hd
    have hr := hlt a haA b hbA
    have hrpos := div_gcd_pos (b := b) (hpos a haA)
    rw [ht] at hr hrpos ⊢
    have h2 : q * t < q * 2 := by rw [mul_comm q 2]; exact lt_trans hr hn2q
    have ht2 : t < 2 := Nat.lt_of_mul_lt_mul_left h2
    have ht1 : 0 < t := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hrpos; exact lt_irrefl 0 hrpos)
    have : t = 1 := by omega
    rw [this, mul_one]
  have hqn : q < n := by
    obtain ⟨a, ha⟩ := hA1ne
    have := hlt a (hA1mem a ha).1 m hm
    rwa [K1 a ha m hmA0] at this
  have K1' : ∀ a ∈ A1, ∀ b ∈ A0, a = a.gcd b * q := by
    intro a ha b hb
    have h := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    rwa [K1 a ha b hb] at h
  have K2 : ∀ a ∈ A1, ∀ b ∈ A0, a / q = a.gcd b := fun a ha b hb =>
    Nat.div_eq_of_eq_mul_left hq.pos (K1' a ha b hb)
  have K2' : ∀ a ∈ A1, ∀ b ∈ A0, a / q ∣ b := fun a ha b hb =>
    (K2 a ha b hb) ▸ Nat.gcd_dvd_right a b
  have hap : ∀ a ∈ A1, a / q * q = a := by
    intro a ha
    rw [K2 a ha m hmA0]; exact (K1' a ha m hmA0).symm
  have K3 : ∀ a ∈ A1, ∀ b ∈ A0, b / (a / q) < n ∧ ¬ q ∣ b / (a / q) := by
    intro a ha b hb
    obtain ⟨haA, hva⟩ := hA1mem a ha
    obtain ⟨hbA, hvb⟩ := hA0mem b hb
    have hg : b.gcd a = a / q := by rw [Nat.gcd_comm, K2 a ha b hb]
    have h1 := hlt b hbA a haA
    have hnd : ¬ q ∣ b / b.gcd a := by
      rw [dvd_div_gcd_iff hq (hpos b hbA) (hpos a haA)]; omega
    rw [hg] at h1 hnd
    exact ⟨h1, hnd⟩
  let G := A0.gcd id
  have hGpos : 0 < G := by
    rw [Nat.pos_iff_ne_zero]
    intro hz
    rw [Finset.gcd_eq_zero_iff] at hz
    have := hz m hmA0
    simp only [id] at this
    exact absurd this (hpos m hm).ne'
  have hGdvd : ∀ b ∈ A0, G ∣ b := fun b hb => Finset.gcd_dvd (f := id) hb
  have hcG : ∀ a ∈ A1, a / q ∣ G := fun a ha => Finset.dvd_gcd (fun b hb => K2' a ha b hb)
  have hcpos : ∀ a ∈ A1, 0 < a / q := fun a ha => by
    rw [K2 a ha m hmA0]; exact Nat.gcd_pos_of_pos_left m (hpos a (hA1mem a ha).1)
  obtain ⟨bs, hbs, hbmax⟩ := Finset.exists_max_image A0 (fun b => b / G) ⟨m, hmA0⟩
  obtain ⟨as, has, hamax⟩ := Finset.exists_max_image A1 (fun a => G / (a / q)) hA1ne
  obtain ⟨u, hu⟩ := hGdvd bs hbs
  obtain ⟨w, hw⟩ := hcG as has
  have e1 : bs / G = u := by rw [hu, Nat.mul_div_cancel_left u hGpos]
  have e2 : G / (as / q) = w := by rw [hw, Nat.mul_div_cancel_left w (hcpos as has)]
  have e3 : bs / (as / q) = w * u := by
    rw [hu, hw, mul_assoc, Nat.mul_div_cancel_left _ (hcpos as has)]
  have hxy : u * w < n := by
    have := (K3 as has bs hbs).1
    rw [e3] at this
    rw [mul_comm]; exact this
  have hb_lb : ∀ b ∈ A0, 1 ≤ b / G := fun b hb =>
    Nat.div_pos (Nat.le_of_dvd (hpos b (hA0mem b hb).1) (hGdvd b hb)) hGpos
  have hb_ub : ∀ b ∈ A0, b / G ≤ u := fun b hb => e1 ▸ hbmax b hb
  have ha_lb : ∀ a ∈ A1, 1 ≤ G / (a / q) := fun a ha =>
    Nat.div_pos (Nat.le_of_dvd hGpos (hcG a ha)) (hcpos a ha)
  have ha_ub : ∀ a ∈ A1, G / (a / q) ≤ w := fun a ha => e2 ▸ hamax a ha
  have hu1 : 1 ≤ u := e1 ▸ hb_lb bs hbs
  have hw1 : 1 ≤ w := e2 ▸ ha_lb as has
  have hc0 : A0.card ≤ u := by
    have h := Finset.card_le_card_of_injOn (fun b => b / G) (t := Finset.Icc 1 u)
      (fun b hb => Finset.mem_Icc.2 ⟨hb_lb b hb, hb_ub b hb⟩)
      (fun b hb b' hb' hbb => (Nat.div_left_inj (hGdvd b hb) (hGdvd b' hb')).1 hbb)
    simpa using h
  have hinj1 : Set.InjOn (fun a => G / (a / q)) A1 := by
    intro a ha a' ha' haa
    simp only at haa
    have h1 : a / q = a' / q := by
      rw [← Nat.div_div_self (hcG a ha) hGpos.ne', ← Nat.div_div_self (hcG a' ha') hGpos.ne',
        haa]
    rw [← hap a ha, ← hap a' ha', h1]
  have hc1 : A1.card ≤ w := by
    have h := Finset.card_le_card_of_injOn (fun a => G / (a / q)) (t := Finset.Icc 1 w)
      (fun a ha => Finset.mem_Icc.2 ⟨ha_lb a ha, ha_ub a ha⟩) hinj1
    simpa using h
  have hcases : u = 1 ∨ w = 1 := by
    by_contra h
    rw [not_or] at h
    have hx2 : 2 ≤ u := by omega
    have hy2 : 2 ≤ w := by omega
    have : u + w ≤ u * w := by nlinarith
    omega
  -- the target set of values [1, n-1] minus q has n - 2 elements
  have hT : ((Finset.Icc 1 (n - 1)).erase q).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]
    simp
    omega
  rcases hcases with hu1' | hw1'
  · -- bottom layer is {G}; the top layer injects into [1, n-1] minus q
    have hbsG : G = bs := Nat.eq_of_dvd_of_div_eq_one (hGdvd bs hbs) (e1.trans hu1')
    have hw' : w ≤ n - 1 := by rw [hu1', one_mul] at hxy; omega
    have h := Finset.card_le_card_of_injOn (fun a => G / (a / q))
      (t := (Finset.Icc 1 (n - 1)).erase q)
      (fun a ha => by
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_Icc.2 ⟨ha_lb a ha, (ha_ub a ha).trans hw'⟩⟩
        intro hEq
        have hnd := (K3 a ha bs hbs).2
        rw [← hbsG] at hnd
        exact hnd ⟨1, by simp only at hEq; rw [hEq, mul_one]⟩) hinj1
    rw [hT] at h
    omega
  · -- top layer is {qG}; the bottom layer injects into [1, n-1] minus q
    have hasG : as / q = G := Nat.eq_of_dvd_of_div_eq_one (hcG as has) (e2.trans hw1')
    have hu' : u ≤ n - 1 := by rw [hw1', mul_one] at hxy; omega
    have h := Finset.card_le_card_of_injOn (fun b => b / G)
      (t := (Finset.Icc 1 (n - 1)).erase q)
      (fun b hb => by
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_Icc.2 ⟨hb_lb b hb, (hb_ub b hb).trans hu'⟩⟩
        intro hEq
        have hnd := (K3 as has b hb).2
        rw [hasG] at hnd
        exact hnd ⟨1, by simp only at hEq; rw [hEq, mul_one]⟩)
      (fun b hb b' hb' hbb => (Nat.div_left_inj (hGdvd b hb) (hGdvd b' hb')).1 hbb)
    rw [hT] at h
    omega

/-- Graham's inequality holds for every `n` and every primitive `A` of size `n` that contains a
multiple of some prime `q` with `n < 2q`: a primitive family has two `q`-layers, and
`two_layer_ineq` applies. -/
theorem graham_of_multiple {q n : ℕ} (hq : q.Prime) (hn2q : n < 2 * q)
    (A : Finset ℕ) (hcard : A.card = n) (h0 : 0 ∉ A) (hg : A.gcd id = 1)
    (hdiv : ∃ a ∈ A, q ∣ a) :
    ∃ a ∈ A, ∃ b ∈ A, n ≤ a / a.gcd b := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨a, ha, hqa⟩ := hdiv
  have hb : ∃ b ∈ A, ¬ q ∣ b := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have h1 : q ∣ A.gcd id := Finset.dvd_gcd (fun b hb => hall b hb)
    rw [hg] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨b, hb, hqb⟩ := hb
  apply two_layer_ineq hq hn2q A h0 hcard hcon
  refine ⟨a, ha, b, hb, ?_⟩
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hva : 1 ≤ a.factorization q := (hq.dvd_iff_one_le_factorization ha0).1 hqa
  have hvb : b.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqb
  omega

/-- A prime above the ratio bound divides no element of a primitive family: it would
have to divide the gcd of every pair, hence the gcd of the whole family. -/
lemma prime_free {A : Finset ℕ} {p N : ℕ} (hp : p.Prime) (hN : N < p)
    (pos : ∀ a ∈ A, 0 < a) (prim : A.gcd id = 1)
    (bd : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ N) : ∀ a ∈ A, ¬ p ∣ a := by
  intro a ha hpa
  have hall : ∀ b ∈ A, p ∣ b := by
    intro b hb
    have h2 : p ∣ a / a.gcd b * a.gcd b := by
      rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left a b)]
    rcases hp.dvd_mul.mp h2 with h | h
    · have h3 := Nat.le_of_dvd (div_gcd_pos (b := b) (pos a ha)) h
      have h4 := bd a ha b hb
      omega
    · exact h.trans (Nat.gcd_dvd_right a b)
  have h5 : p ∣ A.gcd id := Finset.dvd_gcd (fun b hb => hall b hb)
  rw [prim] at h5
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

/-- Residues modulo a prime above the ratio bound separate the elements: equal residues
force equal reduced parts. -/
lemma residue_inj {A : Finset ℕ} {p N : ℕ} (hp : p.Prime) (hN : N < p)
    (unit : ∀ a ∈ A, ¬ p ∣ a) (bd : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ N) :
    Set.InjOn (· % p) (A : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ∈ A := ha
  have hb' : b ∈ A := hb
  have hab' : a % p = b % p := hab
  have hu : a / a.gcd b * a.gcd b = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hv : b / a.gcd b * a.gcd b = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have cop : Nat.Coprime p (a.gcd b) :=
    hp.coprime_iff_not_dvd.mpr (fun h => unit a ha' (h.trans (Nat.gcd_dvd_left a b)))
  have hmod : a / a.gcd b * a.gcd b ≡ b / a.gcd b * a.gcd b [MOD p] := by
    rw [hu, hv]; exact hab'
  have h1 := bd a ha' b hb'
  have h2 : b / a.gcd b ≤ N := by rw [Nat.gcd_comm]; exact bd b hb' a ha'
  have heq := (Nat.ModEq.cancel_right_of_coprime cop hmod).eq_of_lt_of_lt
    (by omega) (by omega)
  calc a = a / a.gcd b * a.gcd b := hu.symm
    _ = b / a.gcd b * a.gcd b := by rw [heq]
    _ = b := hv

/-- Two elements with opposite nonzero residues modulo `p` have reduced parts summing to `p`. -/
lemma reduced_sum {a b p N : ℕ} (hp : p.Prime) (hN : N < p) (ha : 0 < a)
    (pa : ¬ p ∣ a) (hab : a / a.gcd b ≤ N) (hba : b / b.gcd a ≤ N)
    (hsum : a % p + b % p = p) : a / a.gcd b + b / a.gcd b = p := by
  have hu : a / a.gcd b * a.gcd b = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hv : b / a.gcd b * a.gcd b = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have hdiv : p ∣ (a / a.gcd b + b / a.gcd b) * a.gcd b := by
    rw [Nat.add_mul, hu, hv, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hsum, Nat.mod_self]
  have hg : ¬ p ∣ a.gcd b := fun h => pa (h.trans (Nat.gcd_dvd_left a b))
  obtain ⟨w, hw⟩ := (hp.dvd_mul.mp hdiv).resolve_right hg
  have upos : 0 < a / a.gcd b := div_gcd_pos ha
  have hv' : b / a.gcd b ≤ N := by rw [Nat.gcd_comm]; exact hba
  have h2 : p * w < p * 2 := by rw [← hw]; omega
  have h0 : 0 < p * w := by rw [← hw]; exact lt_of_lt_of_le upos (Nat.le_add_right _ _)
  have w2 := Nat.lt_of_mul_lt_mul_left h2
  have w1 : w = 1 := by
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h, mul_zero] at h0; omega
    · omega
  rw [hw, w1, mul_one]

/-- Among `n` nonzero residues modulo `p`, at least `n - p/2` values `k ≤ p/2` occur
together with `p - k`. -/
lemma keys_count {E : Finset ℕ} {p n : ℕ} (hE : E ⊆ Ico 1 p) (hc : E.card = n) :
    n - p / 2 ≤ ((Icc 1 (p / 2)).filter (fun k => k ∈ E ∧ p - k ∈ E)).card := by
  classical
  have mem : ∀ x ∈ E, 1 ≤ x ∧ x < p := fun x hx => mem_Ico.mp (hE hx)
  have hLR : (E.filter (· ≤ p / 2)).card + (E.filter (fun x => ¬ x ≤ p / 2)).card = n := by
    rw [card_filter_add_card_filter_not, hc]
  have hRi : ((E.filter (fun x => ¬ x ≤ p / 2)).image (p - ·)).card =
      (E.filter (fun x => ¬ x ≤ p / 2)).card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    have h1 := mem x (mem_filter.mp hx).1
    have h2 := mem y (mem_filter.mp hy).1
    have h3 : p - x = p - y := hxy
    omega
  have hU : E.filter (· ≤ p / 2) ∪ (E.filter (fun x => ¬ x ≤ p / 2)).image (p - ·) ⊆
      Icc 1 (p / 2) := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · obtain ⟨h1, h2⟩ := mem_filter.mp h
      exact mem_Icc.mpr ⟨(mem x h1).1, h2⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      obtain ⟨h1, h2⟩ := mem_filter.mp hy
      have h3 := mem y h1
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hI : E.filter (· ≤ p / 2) ∩ (E.filter (fun x => ¬ x ≤ p / 2)).image (p - ·) ⊆
      (Icc 1 (p / 2)).filter (fun k => k ∈ E ∧ p - k ∈ E) := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_inter.mp hx
    obtain ⟨y, hy, hyx⟩ := mem_image.mp h2
    obtain ⟨hyE, hyl⟩ := mem_filter.mp hy
    obtain ⟨hxE, hxl⟩ := mem_filter.mp h1
    have h3 := mem y hyE
    have h4 := mem x hxE
    have hpx : p - x = y := by omega
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h4.1, hxl⟩, hxE, hpx ▸ hyE⟩
  have c1 := card_le_card hU
  have c2 := card_le_card hI
  have c3 := card_union_add_card_inter (E.filter (· ≤ p / 2))
    ((E.filter (fun x => ¬ x ≤ p / 2)).image (p - ·))
  have c4 : (Icc 1 (p / 2)).card = p / 2 := by simp
  omega

/-- Every key `k` (both `k` and `p - k` are residues of the family) comes from a pair
`m * d, (p - m) * d` of elements with `p/2 < m ≤ n`; the key is the smaller residue. -/
lemma keys_cover {A : Finset ℕ} {p n : ℕ} (hp : p.Prime) (np : n < p) (p2 : 2 < p)
    (pos : ∀ a ∈ A, 0 < a) (unit : ∀ a ∈ A, ¬ p ∣ a)
    (bd : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ n) :
    (Icc 1 (p / 2)).filter (fun k => k ∈ A.image (· % p) ∧ p - k ∈ A.image (· % p)) ⊆
      (Ioc (p / 2) n).biUnion (fun m =>
        ((A.image (· / m)).filter (fun d => m * d ∈ A ∧ (p - m) * d ∈ A)).image
          (fun d => min ((m * d) % p) (p - (m * d) % p))) := by
  intro k hk
  obtain ⟨hk1, hkE, hpkE⟩ := mem_filter.mp hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk1
  obtain ⟨a, ha, hak⟩ := mem_image.mp hkE
  obtain ⟨b, hb, hbk⟩ := mem_image.mp hpkE
  have hak' : a % p = k := hak
  have hbk' : b % p = p - k := hbk
  have hsum : a % p + b % p = p := by omega
  have rs := reduced_sum hp np (pos a ha) (unit a ha) (bd a ha b hb) (bd b hb a ha) hsum
  have hu : a / a.gcd b * a.gcd b = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hv : b / a.gcd b * a.gcd b = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have hvb : b / a.gcd b ≤ n := by rw [Nat.gcd_comm]; exact bd b hb a ha
  have hua : a / a.gcd b ≤ n := bd a ha b hb
  have hne : a / a.gcd b ≠ b / a.gcd b := by
    intro h
    have h2 : 2 ∣ p := ⟨a / a.gcd b, by omega⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h3 | h3 <;> omega
  rw [mem_biUnion]
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨b / a.gcd b, mem_Ioc.mpr ⟨by omega, hvb⟩, mem_image.mpr ⟨a.gcd b, ?_, ?_⟩⟩
    · have e1 : p - b / a.gcd b = a / a.gcd b := by omega
      refine mem_filter.mpr ⟨mem_image.mpr ⟨b, hb, ?_⟩, ?_, ?_⟩
      · exact Nat.div_div_self (Nat.gcd_dvd_right a b) (pos b hb).ne'
      · rw [hv]; exact hb
      · rw [e1, hu]; exact ha
    · show min ((b / a.gcd b * a.gcd b) % p) (p - (b / a.gcd b * a.gcd b) % p) = k
      rw [hv, hbk']
      omega
  · refine ⟨a / a.gcd b, mem_Ioc.mpr ⟨by omega, hua⟩, mem_image.mpr ⟨a.gcd b, ?_, ?_⟩⟩
    · have e1 : p - a / a.gcd b = b / a.gcd b := by omega
      refine mem_filter.mpr ⟨mem_image.mpr ⟨a, ha, ?_⟩, ?_, ?_⟩
      · exact Nat.div_div_self (Nat.gcd_dvd_left a b) (pos a ha).ne'
      · rw [hu]; exact ha
      · rw [e1, hv]; exact hb
    · show min ((a / a.gcd b * a.gcd b) % p) (p - (a / a.gcd b * a.gcd b) % p) = k
      rw [hu, hak']
      omega

/-- A common factor of the two arguments cancels from a directed quotient bound. -/
lemma reduce_quot {c e g s t n : ℕ} (hg : 0 < g)
    (h : (c * (g * s)) / (c * (g * s)).gcd (e * (g * t)) ≤ n) :
    (c * s) / (c * s).gcd (e * t) ≤ n := by
  have h1 : c * (g * s) = g * (c * s) := by ring
  have h2 : e * (g * t) = g * (e * t) := by ring
  rwa [h1, h2, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hg] at h

/-- A coprime pair `(d, e)` whose two cross quotients against coprime `m, l` are at most `n`,
with `n^2 < 2 m^2`, has `d * e ∣ m * l`. Each gcd in a quotient divides the product of the
cross gcds, so `m^2 d e ≤ n^2` times the four cross gcds, and the cofactors of `d` and `e`
outside `m * l` must both be `1` (the idea of Balasubramanian and Soundararajan, Lemma 2.3). -/
lemma pair_support {m l d e n : ℕ} (dp : 0 < d) (ep : 0 < e) (ml : m.Coprime l)
    (de : d.Coprime e) (close : n ^ 2 < 2 * m ^ 2)
    (h1 : m * d / (m * d).gcd (l * e) ≤ n) (h2 : m * e / (m * e).gcd (l * d) ≤ n) :
    d * e ∣ m * l := by
  have g1 : (m * d).gcd (l * e) ∣ d.gcd l * e.gcd m := by
    have h : (m * d).gcd (l * e) ∣ (m * d).gcd l * (m * d).gcd e :=
      gcd_mul_dvd_mul_gcd (m * d) l e
    rwa [Nat.Coprime.gcd_mul_left_cancel d ml, Nat.Coprime.gcd_mul_right_cancel m de,
      Nat.gcd_comm m e] at h
  have g2 : (m * e).gcd (l * d) ∣ e.gcd l * d.gcd m := by
    have h : (m * e).gcd (l * d) ∣ (m * e).gcd l * (m * e).gcd d :=
      gcd_mul_dvd_mul_gcd (m * e) l d
    rwa [Nat.Coprime.gcd_mul_left_cancel e ml, Nat.Coprime.gcd_mul_right_cancel m de.symm,
      Nat.gcd_comm m d] at h
  have pa : 0 < d.gcd m := Nat.gcd_pos_of_pos_left _ dp
  have pb : 0 < d.gcd l := Nat.gcd_pos_of_pos_left _ dp
  have pc : 0 < e.gcd m := Nat.gcd_pos_of_pos_left _ ep
  have pd : 0 < e.gcd l := Nat.gcd_pos_of_pos_left _ ep
  have q1 : m * d ≤ n * (d.gcd l * e.gcd m) :=
    calc m * d = m * d / (m * d).gcd (l * e) * (m * d).gcd (l * e) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ ≤ n * (d.gcd l * e.gcd m) := Nat.mul_le_mul h1 (Nat.le_of_dvd (Nat.mul_pos pb pc) g1)
  have q2 : m * e ≤ n * (e.gcd l * d.gcd m) :=
    calc m * e = m * e / (m * e).gcd (l * d) * (m * e).gcd (l * d) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ ≤ n * (e.gcd l * d.gcd m) := Nat.mul_le_mul h2 (Nat.le_of_dvd (Nat.mul_pos pd pa) g2)
  have fd : d.gcd m * d.gcd l ∣ d :=
    (ml.gcd_both d d).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left d m) (Nat.gcd_dvd_left d l)
  have fe : e.gcd m * e.gcd l ∣ e :=
    (ml.gcd_both e e).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left e m) (Nat.gcd_dvd_left e l)
  have am := Nat.gcd_dvd_right d m
  have bl := Nat.gcd_dvd_right d l
  have cm := Nat.gcd_dvd_right e m
  have dl := Nat.gcd_dvd_right e l
  generalize d.gcd m = α at q2 fd am pa
  generalize d.gcd l = β at q1 fd bl pb
  generalize e.gcd m = γ at q1 fe cm pc
  generalize e.gcd l = δ at q2 fe dl pd
  obtain ⟨z, hz⟩ := fd
  obtain ⟨t, ht⟩ := fe
  have zpos : 0 < z := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hz; omega
  have tpos : 0 < t := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at ht; omega
  have prod := Nat.mul_le_mul q1 q2
  rw [hz, ht] at prod
  have key : (α * β * γ * δ) * (m ^ 2 * (z * t)) ≤ (α * β * γ * δ) * n ^ 2 :=
    calc (α * β * γ * δ) * (m ^ 2 * (z * t)) = m * (α * β * z) * (m * (γ * δ * t)) := by ring
      _ ≤ n * (β * γ) * (n * (δ * α)) := prod
      _ = (α * β * γ * δ) * n ^ 2 := by ring
  have pP : 0 < α * β * γ * δ := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pa pb) pc) pd
  have small := Nat.le_of_mul_le_mul_left key pP
  have zt2 : z * t < 2 := by
    by_contra hc
    have hc' : 2 ≤ z * t := by omega
    have h3 := Nat.mul_le_mul_left (m ^ 2) hc'
    omega
  have zt1 : z * t = 1 := by
    have h4 := Nat.mul_pos zpos tpos
    omega
  have z1 : z = 1 := Nat.dvd_one.mp (by rw [← zt1]; exact dvd_mul_right z t)
  have t1 : t = 1 := Nat.dvd_one.mp (by rw [← zt1]; exact dvd_mul_left t z)
  have hd : d ∣ m * l := by rw [hz, z1, mul_one]; exact Nat.mul_dvd_mul am bl
  have he : e ∣ m * l := by rw [ht, t1, mul_one]; exact Nat.mul_dvd_mul cm dl
  exact de.mul_dvd_of_dvd_of_dvd hd he

/-- Fix the least dilation `x` of a fiber; each other dilation `y` gives the reduced pair
`(x, y) / gcd x y`, these pairs are distinct, they inherit the four cross bounds, and by
`pair_support` they divide `m * l`. -/
lemma fiber_pairs {A S : Finset ℕ} {m l n : ℕ} (pos : ∀ a ∈ A, 0 < a)
    (bd : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ n) (hS : ∀ d ∈ S, m * d ∈ A ∧ l * d ∈ A)
    (ml : m.Coprime l) (close : n ^ 2 < 2 * m ^ 2) :
    ∃ F : Finset (ℕ × ℕ), S.card ≤ F.card + 1 ∧ ∀ z ∈ F, 0 < z.1 ∧ z.1 < z.2 ∧
      z.1.Coprime z.2 ∧ z.1 * z.2 ∣ m * l ∧
      m * z.1 / (m * z.1).gcd (l * z.2) ≤ n ∧ m * z.2 / (m * z.2).gcd (l * z.1) ≤ n ∧
      l * z.1 / (l * z.1).gcd (m * z.2) ≤ n ∧ l * z.2 / (l * z.2).gcd (m * z.1) ≤ n := by
  classical
  rcases S.eq_empty_or_nonempty with h | hne
  · exact ⟨∅, by simp [h], by simp⟩
  have dpos : ∀ d ∈ S, 0 < d := fun d hd =>
    Nat.pos_of_ne_zero fun h0 => (pos _ (hS d hd).1).ne' (by rw [h0, mul_zero])
  obtain ⟨x, hxS, hxmin⟩ : ∃ x ∈ S, ∀ y ∈ S, x ≤ y :=
    ⟨S.min' hne, min'_mem S hne, fun y hy => min'_le S y hy⟩
  have xpos := dpos x hxS
  have finj : Set.InjOn (fun y => (x / x.gcd y, y / x.gcd y)) ((S.erase x : Finset ℕ) : Set ℕ) := by
    intro y _ y' _ hyy
    have h1 : x / x.gcd y = x / x.gcd y' := congrArg Prod.fst hyy
    have h2 : y / x.gcd y = y' / x.gcd y' := congrArg Prod.snd hyy
    have hg : x.gcd y = x.gcd y' := by
      rw [← Nat.div_div_self (Nat.gcd_dvd_left x y) xpos.ne', h1,
        Nat.div_div_self (Nat.gcd_dvd_left x y') xpos.ne']
    rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right x y), ← Nat.div_mul_cancel (Nat.gcd_dvd_right x y'),
      h2, hg]
  refine ⟨(S.erase x).image (fun y => (x / x.gcd y, y / x.gcd y)), ?_, ?_⟩
  · rw [card_image_of_injOn finj, card_erase_of_mem hxS]
    omega
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
    obtain ⟨hyx, hyS⟩ := mem_erase.mp hy
    have xy : x < y := lt_of_le_of_ne (hxmin y hyS) (Ne.symm hyx)
    have cop0 := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left y xpos)
    obtain ⟨g, hg⟩ : ∃ g, x.gcd y = g := ⟨_, rfl⟩
    have gpos : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left y xpos
    obtain ⟨i, hi⟩ : g ∣ x := hg ▸ Nat.gcd_dvd_left x y
    obtain ⟨j, hj⟩ : g ∣ y := hg ▸ Nat.gcd_dvd_right x y
    have e1 : x / x.gcd y = i := by rw [hg]; exact Nat.div_eq_of_eq_mul_right gpos hi
    have e2 : y / x.gcd y = j := by rw [hg]; exact Nat.div_eq_of_eq_mul_right gpos hj
    rw [e1, e2] at cop0
    show 0 < (x / x.gcd y, y / x.gcd y).1 ∧ _
    simp only [e1, e2]
    have b1 := bd (m * x) (hS x hxS).1 (l * y) (hS y hyS).2
    have b2 := bd (m * y) (hS y hyS).1 (l * x) (hS x hxS).2
    have b3 := bd (l * x) (hS x hxS).2 (m * y) (hS y hyS).1
    have b4 := bd (l * y) (hS y hyS).2 (m * x) (hS x hxS).1
    rw [hi, hj] at b1 b2 b3 b4
    have ipos : 0 < i := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hi; omega
    have ij : i < j := by
      apply Nat.lt_of_mul_lt_mul_left (a := g)
      rw [← hi, ← hj]; exact xy
    exact ⟨ipos, ij, cop0, pair_support ipos (ipos.trans ij) ml cop0 close
      (reduce_quot gpos b1) (reduce_quot gpos b2), reduce_quot gpos b1, reduce_quot gpos b2,
      reduce_quot gpos b3, reduce_quot gpos b4⟩

end OMA.E402H1

namespace OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H1_R2
open Finset Filter

/-- Prime distribution at power-scale intervals (the same statement as the prime-location input of
the merged equality-case reduction): for composite `n`, a prime `p` just below `2n`, at distance between
`g` and `2g` from `2n` where `g` is about `n^(3/4)`, and at least about `n^(5/8)` primes in `(p/2, n]`. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, ¬n.Prime →
  let g := n.sqrt * n.sqrt.sqrt
  ∃ p : ℕ, p.Prime ∧ n<p ∧ 2*n≤p+2*g ∧ p+g≤2*n ∧ 2*n^2<p^2 ∧
    n.sqrt*n.sqrt.sqrt.sqrt ≤ ((Ioc (p/2) n).filter Nat.Prime).card

/-- A divisor-pair estimate, independent of any family of integers (the same statement as the
divisor-pair input of the merged equality-case reduction): normalized pairs `u < v` supported on
`m * (p - m)` whose four directed cross quotients against `m` and `p - m` are at most `n`, summed
over `m` in `(p/2, n]`, number fewer than about `n^(5/8)`. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, ¬n.Prime → ∀ p : ℕ, p.Prime → n<p →
  2*n≤p+2*(n.sqrt*n.sqrt.sqrt) → p+n.sqrt*n.sqrt.sqrt≤2*n →
  ∀ F : ℕ → Finset (ℕ×ℕ),
    (∀ m∈Ioc (p/2) n, ∀ z∈F m, 0<z.1 ∧ z.1<z.2 ∧ z.1.Coprime z.2 ∧
      z.1*z.2∣m*(p-m) ∧
      m*z.1/(m*z.1).gcd ((p-m)*z.2)≤n ∧ m*z.2/(m*z.2).gcd ((p-m)*z.1)≤n ∧
      (p-m)*z.1/((p-m)*z.1).gcd (m*z.2)≤n ∧ (p-m)*z.2/((p-m)*z.2).gcd (m*z.1)≤n) →
    (∑ m∈Ioc (p/2) n, (F m).card) < n.sqrt*n.sqrt.sqrt.sqrt

theorem main : H1 → H2 → OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1.H1 := by
  classical
  intro primes pairs
  filter_upwards [primes, pairs, eventually_ge_atTop 5] with n hP hD hn
  intro A card nz prim
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have pos : ∀ a ∈ A, 0 < a := fun a ha => Nat.pos_of_ne_zero (fun h => nz (h ▸ ha))
  have bd : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ n := fun a ha b hb => (hcon a ha b hb).le
  have avoid : ∀ q, q.Prime → n < 2 * q → ∀ a ∈ A, ¬ q ∣ a := by
    intro q hq hq2 a ha hqa
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      OMA.E402H1.graham_of_multiple hq hq2 A card nz prim ⟨a, ha, hqa⟩
    exact absurd (hcon x hx y hy) (not_lt.mpr hxy)
  by_cases hnp : n.Prime
  · -- prime size: the residues modulo `n` would inject `A` into the `n - 1` units
    have bd' : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ≤ n - 1 := fun a ha b hb => by
      have := hcon a ha b hb
      omega
    have unit := avoid n hnp (by omega)
    have inj := OMA.E402H1.residue_inj hnp (by omega : n - 1 < n) unit bd'
    have sub : A.image (· % n) ⊆ Ico 1 n := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
      exact mem_Ico.mpr ⟨Nat.pos_of_ne_zero (fun h => unit a ha (Nat.dvd_of_mod_eq_zero h)),
        Nat.mod_lt a hnp.pos⟩
    have h1 := card_le_card sub
    rw [card_image_of_injOn inj, card, Nat.card_Ico] at h1
    omega
  · -- composite size: signed residues modulo a prime `p` just below `2n`
    obtain ⟨p, hp, np, pl, pu, close, many⟩ := hP hnp
    have unit := OMA.E402H1.prime_free hp np pos prim bd
    have inj := OMA.E402H1.residue_inj hp np unit bd
    have cE : (A.image (· % p)).card = n := by rw [card_image_of_injOn inj, card]
    have sE : A.image (· % p) ⊆ Ico 1 p := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
      exact mem_Ico.mpr ⟨Nat.pos_of_ne_zero (fun h => unit a ha (Nat.dvd_of_mod_eq_zero h)),
        Nat.mod_lt a hp.pos⟩
    have keys := OMA.E402H1.keys_count sE cE
    have cover := OMA.E402H1.keys_cover hp np (by omega) pos unit bd
    have lower : n - p / 2 ≤ ∑ m ∈ Ioc (p / 2) n,
        ((A.image (· / m)).filter (fun d => m * d ∈ A ∧ (p - m) * d ∈ A)).card :=
      keys.trans ((card_le_card cover).trans (card_biUnion_le.trans
        (sum_le_sum fun m _ => card_image_le)))
    have fib : ∀ m, ∃ F : Finset (ℕ × ℕ),
        (m ∈ Ioc (p / 2) n → ((A.image (· / m)).filter
          (fun d => m * d ∈ A ∧ (p - m) * d ∈ A)).card ≤ F.card + (if ¬ m.Prime then 1 else 0)) ∧
        (m ∈ Ioc (p / 2) n → ∀ z ∈ F, 0 < z.1 ∧ z.1 < z.2 ∧ z.1.Coprime z.2 ∧
          z.1 * z.2 ∣ m * (p - m) ∧
          m * z.1 / (m * z.1).gcd ((p - m) * z.2) ≤ n ∧
          m * z.2 / (m * z.2).gcd ((p - m) * z.1) ≤ n ∧
          (p - m) * z.1 / ((p - m) * z.1).gcd (m * z.2) ≤ n ∧
          (p - m) * z.2 / ((p - m) * z.2).gcd (m * z.1) ≤ n) := by
      intro m
      by_cases hmJ : m ∈ Ioc (p / 2) n
      · have hJ := mem_Ioc.mp hmJ
        have hp2 : p < 2 * m := by omega
        by_cases hm : m.Prime
        · refine ⟨∅, fun _ => ?_, fun _ => by simp⟩
          have empty : (A.image (· / m)).filter (fun d => m * d ∈ A ∧ (p - m) * d ∈ A) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro d hd
            exact avoid m hm (by omega) _ (mem_filter.mp hd).2.1 (dvd_mul_right m d)
          rw [empty]
          simp
        · have cop : m.Coprime (p - m) := by
            rw [Nat.coprime_sub_self_right (by omega)]
            exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr
              (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)))
          have sq : p ^ 2 < (2 * m) ^ 2 := Nat.pow_lt_pow_left hp2 (by norm_num)
          have near : n ^ 2 < 2 * m ^ 2 := by nlinarith
          obtain ⟨F, hc, hF⟩ := OMA.E402H1.fiber_pairs (S := (A.image (· / m)).filter
            (fun d => m * d ∈ A ∧ (p - m) * d ∈ A)) (m := m) (l := p - m) pos bd
            (fun d hd => (mem_filter.mp hd).2) cop near
          refine ⟨F, fun _ => ?_, fun _ => hF⟩
          simp only [hm, not_false_eq_true, if_true]
          exact hc
      · exact ⟨∅, fun h => absurd h hmJ, fun h => absurd h hmJ⟩
    choose F hF1 hF2 using fib
    have upper := hD hnp p hp np pl pu F (fun m hm z hz => hF2 m hm z hz)
    have split : (∑ m ∈ Ioc (p / 2) n,
        ((A.image (· / m)).filter (fun d => m * d ∈ A ∧ (p - m) * d ∈ A)).card) ≤
        (∑ m ∈ Ioc (p / 2) n, (F m).card) + ((Ioc (p / 2) n).filter (fun m => ¬ m.Prime)).card := by
      rw [card_filter, ← sum_add_distrib]
      exact sum_le_sum fun m hm => hF1 m hm
    have parts := card_filter_add_card_filter_not (s := Ioc (p / 2) n) Nat.Prime
    rw [Nat.card_Ioc] at parts
    omega

end OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H1_R2
