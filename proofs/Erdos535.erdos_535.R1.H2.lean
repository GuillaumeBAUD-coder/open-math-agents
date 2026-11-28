import OMAReductions.R_Erdos535_erdos_535_R1

/-!
Extract a large constant-Omega layer from a set of integers up to N.
Delete the prime factors below y. There are at most (L + 1) ^ y such kernels
when every integer is below 2 ^ L, and the cofactor then has Omega at most K.
-/

open Erdos535 ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace OMA535Extract

def primesBelow (y : ℕ) : List ℕ :=
  ((Finset.range y).filter Nat.Prime).sort (· ≤ ·)

def sOf (y a : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range y).filter Nat.Prime, p ^ a.factorization p

def code (L y a : ℕ) : ℕ :=
  (primesBelow y).foldr (fun p acc => acc * (L + 1) + a.factorization p) 0

lemma foldr_succ_le {base : ℕ} (hb : 0 < base) (l : List ℕ) (d : ℕ → ℕ)
    (hd : ∀ p ∈ l, d p < base) :
    l.foldr (fun p acc => acc * base + d p) 0 + 1 ≤ base ^ l.length := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have hp : d p + 1 ≤ base := hd p (List.Mem.head ps)
    have hps := ih (fun q hq => hd q (List.Mem.tail p hq))
    have hfold : ps.foldr (fun q acc => acc * base + d q) 0 ≤ base ^ ps.length - 1 := by
      have := Nat.lt_of_succ_le hps
      omega
    calc
      ps.foldr (fun q acc => acc * base + d q) 0 * base + d p + 1
          = ps.foldr (fun q acc => acc * base + d q) 0 * base + (d p + 1) := by omega
      _ ≤ (base ^ ps.length - 1) * base + base :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hfold) hp
      _ = (base ^ ps.length - 1) * base + 1 * base := by rw [Nat.one_mul]
      _ = (base ^ ps.length - 1 + 1) * base := by rw [← Nat.add_mul]
      _ = base ^ ps.length * base := by
          rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hb)]

lemma foldr_eq_of_eq {base : ℕ} (hb : 0 < base) (l : List ℕ) {d e : ℕ → ℕ}
    (hd : ∀ p ∈ l, d p < base) (he : ∀ p ∈ l, e p < base)
    (h : l.foldr (fun p acc => acc * base + d p) 0 =
        l.foldr (fun p acc => acc * base + e p) 0) :
    ∀ p ∈ l, d p = e p := by
  induction l with
  | nil => intro p hp; cases hp
  | cons p ps ih =>
    simp only [List.foldr_cons] at h
    have hpd : d p < base := hd p (List.Mem.head ps)
    have hpe : e p < base := he p (List.Mem.head ps)
    have hhead : d p = e p := by
      have hdmod :
          (ps.foldr (fun q acc => acc * base + d q) 0 * base + d p) % base = d p := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hpd]
      have hemod :
          (ps.foldr (fun q acc => acc * base + e q) 0 * base + e p) % base = e p := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hpe]
      rw [← hdmod, ← hemod, h]
    have htail :
        ps.foldr (fun q acc => acc * base + d q) 0 =
          ps.foldr (fun q acc => acc * base + e q) 0 := by
      have hd0 :
          (ps.foldr (fun q acc => acc * base + d q) 0 * base + d p) / base =
            ps.foldr (fun q acc => acc * base + d q) 0 := by
        rw [Nat.mul_comm (ps.foldr (fun q acc => acc * base + d q) 0) base,
          Nat.mul_add_div hb, Nat.div_eq_of_lt hpd, Nat.add_zero]
      have he0 :
          (ps.foldr (fun q acc => acc * base + e q) 0 * base + e p) / base =
            ps.foldr (fun q acc => acc * base + e q) 0 := by
        rw [Nat.mul_comm (ps.foldr (fun q acc => acc * base + e q) 0) base,
          Nat.mul_add_div hb, Nat.div_eq_of_lt hpe, Nat.add_zero]
      rw [← hd0, ← he0, h]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hhead
    · exact ih (fun r hr => hd r (List.Mem.tail p hr))
        (fun r hr => he r (List.Mem.tail p hr)) htail q hq

lemma factorization_le_two_pow {a L p : ℕ} (ha : a ≠ 0) (hlt : a < 2 ^ L) (hp : p.Prime) :
    a.factorization p ≤ L := by
  by_contra hgt
  have hge : L + 1 ≤ a.factorization p := by omega
  have hdvd : p ^ (L + 1) ∣ a := (hp.pow_dvd_iff_le_factorization ha).2 hge
  have hle : p ^ (L + 1) ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hdvd
  have hbase : 2 ^ (L + 1) ≤ p ^ (L + 1) := Nat.pow_le_pow_left hp.two_le _
  have hcontra : 2 ^ (L + 1) < 2 ^ L := lt_of_le_of_lt (hbase.trans hle) hlt
  rw [Nat.pow_succ] at hcontra
  exact Nat.lt_irrefl _ (lt_of_le_of_lt (Nat.le_mul_of_pos_right (2 ^ L) (by decide : 0 < 2)) hcontra)

lemma sOf_ne_zero (y a : ℕ) : sOf y a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2)

lemma prodPowDvd {a : ℕ} (ha : a ≠ 0) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ^ a.factorization p ∣ a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hp' : p.Prime := hs p (Finset.mem_insert_self p s)
    have hpow : p ^ a.factorization p ∣ a :=
      (hp'.pow_dvd_iff_le_factorization ha).2 le_rfl
    have hrest : ∏ q ∈ s, q ^ a.factorization q ∣ a :=
      ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime (p ^ a.factorization p) (∏ q ∈ s, q ^ a.factorization q) := by
      refine Nat.Coprime.pow_left _ ?_
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      have hq' : q.Prime := hs q (Finset.mem_insert_of_mem hq)
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp' hq').2 hne)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpow hrest

lemma sOf_dvd {y a : ℕ} (ha : a ≠ 0) : sOf y a ∣ a := by
  simpa [sOf] using prodPowDvd ha ((Finset.range y).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.mp hp).2)

lemma code_lt {L y a : ℕ} (hexp : ∀ p, p.Prime → p < y → a.factorization p ≤ L) :
    code L y a < (L + 1) ^ (primesBelow y).length := by
  have hd : ∀ p ∈ primesBelow y, a.factorization p < L + 1 := by
    intro p hp
    rw [primesBelow, Finset.mem_sort] at hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.lt_succ_of_le (hexp p hp'.2 (Finset.mem_range.mp hp'.1))
  exact Nat.lt_of_succ_le (foldr_succ_le (by omega) (primesBelow y) (fun p => a.factorization p) hd)

lemma code_eq_sOf {L y a b : ℕ}
    (ha : ∀ p, p.Prime → p < y → a.factorization p ≤ L)
    (hb : ∀ p, p.Prime → p < y → b.factorization p ≤ L)
    (hcode : code L y a = code L y b) : sOf y a = sOf y b := by
  have hd : ∀ p ∈ primesBelow y, a.factorization p < L + 1 := by
    intro p hp
    rw [primesBelow, Finset.mem_sort] at hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.lt_succ_of_le (ha p hp'.2 (Finset.mem_range.mp hp'.1))
  have he : ∀ p ∈ primesBelow y, b.factorization p < L + 1 := by
    intro p hp
    rw [primesBelow, Finset.mem_sort] at hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.lt_succ_of_le (hb p hp'.2 (Finset.mem_range.mp hp'.1))
  have hfac : ∀ p ∈ (Finset.range y).filter Nat.Prime, a.factorization p = b.factorization p := by
    intro p hp
    have hmem : p ∈ primesBelow y := by
      rw [primesBelow, Finset.mem_sort]
      exact hp
    exact foldr_eq_of_eq (by omega) (primesBelow y) hd he hcode p hmem
  unfold sOf
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [hfac p hp]

lemma sOf_factor {y a q : ℕ} (hq : q.Prime) (hqy : q < y) :
    (sOf y a).factorization q = a.factorization q := by
  classical
  let P := (Finset.range y).filter Nat.Prime
  have hqP : q ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqy, hq⟩
  have hsplit : sOf y a =
      q ^ a.factorization q * ∏ p ∈ P.erase q, p ^ a.factorization p := by
    simpa [sOf, P] using (Finset.mul_prod_erase P (fun p => p ^ a.factorization p) hqP).symm
  have hrest : Nat.Coprime q (∏ p ∈ P.erase q, p ^ a.factorization p) := by
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
    have hne : q ≠ p := by
      intro h
      exact Finset.notMem_erase q P (h ▸ hp)
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hp').2 hne)
  have hrest0 : (∏ p ∈ P.erase q, p ^ a.factorization p).factorization q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have hgcd : q.gcd (∏ p ∈ P.erase q, p ^ a.factorization p) = q := Nat.gcd_eq_left hdvd
    rw [hrest] at hgcd
    exact hq.ne_one hgcd.symm
  have hpow0 : q ^ a.factorization q ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hprod0 : ∏ p ∈ P.erase q, p ^ a.factorization p ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2)
  rw [hsplit, Nat.factorization_mul hpow0 hprod0, Finsupp.add_apply,
    Nat.factorization_pow_self hq, hrest0, add_zero]

lemma rough {y a q : ℕ} (ha : a ≠ 0) (hq : q.Prime) (hdvd : q ∣ a / sOf y a) : y ≤ q := by
  by_contra hlt
  have hqy : q < y := Nat.lt_of_not_ge hlt
  have hsdiv : sOf y a ∣ a := sOf_dvd ha
  have hmul : sOf y a * (a / sOf y a) = a := Nat.mul_div_cancel' hsdiv
  have hb0 : a / sOf y a ≠ 0 := by
    intro hb
    rw [hb, Nat.mul_zero] at hmul
    exact ha hmul.symm
  have houter : (sOf y a * (a / sOf y a)).factorization q = a.factorization q :=
    congrArg (fun n => n.factorization q) hmul
  have hsplit : (sOf y a * (a / sOf y a)).factorization q =
      (sOf y a).factorization q + (a / sOf y a).factorization q := by
    rw [Nat.factorization_mul (sOf_ne_zero y a) hb0, Finsupp.add_apply]
  have hone : 1 ≤ (a / sOf y a).factorization q :=
    (hq.pow_dvd_iff_le_factorization hb0).1 (by simpa using hdvd)
  have hsum : a.factorization q =
      (sOf y a).factorization q + (a / sOf y a).factorization q :=
    houter.symm.trans hsplit
  rw [sOf_factor hq hqy] at hsum
  omega

lemma listPowLeProd {y : ℕ} (l : List ℕ) (hl : ∀ q ∈ l, y ≤ q) : y ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons q qs ih =>
    rw [List.length_cons, List.prod_cons, Nat.pow_succ]
    have hq : y ≤ q := hl q (List.Mem.head qs)
    have hqs : y ^ qs.length ≤ qs.prod :=
      ih (fun r hr => hl r (List.Mem.tail q hr))
    calc
      y ^ qs.length * y ≤ qs.prod * q := Nat.mul_le_mul hqs hq
      _ = q * qs.prod := Nat.mul_comm _ _

lemma yPowOmegaLe {y b : ℕ} (hb : b ≠ 0) (hfac : ∀ q : ℕ, q.Prime → q ∣ b → y ≤ q) :
    y ^ Ω b ≤ b := by
  have hlen : Ω b = b.primeFactorsList.length := cardFactors_apply
  have hprod : b.primeFactorsList.prod = b := Nat.prod_primeFactorsList hb
  have hlist : y ^ b.primeFactorsList.length ≤ b.primeFactorsList.prod := by
    refine listPowLeProd b.primeFactorsList ?_
    intro q hq
    have hmem := (Nat.mem_primeFactorsList hb).1 hq
    exact hfac q hmem.1 hmem.2
  calc
    y ^ Ω b = y ^ b.primeFactorsList.length := by rw [hlen]
    _ ≤ b.primeFactorsList.prod := hlist
    _ = b := hprod

lemma omegaLe {y K a : ℕ} (hy : 2 ≤ y) (ha : a ≠ 0) (hK : a < y ^ (K + 1)) :
    Ω (a / sOf y a) ≤ K := by
  set b := a / sOf y a with hbEq
  by_contra hgt
  have hge : K + 1 ≤ Ω b := by omega
  have hb0 : b ≠ 0 := by
    intro hb
    have hmul := Nat.mul_div_cancel' (sOf_dvd (y := y) ha)
    rw [← hbEq, hb, Nat.mul_zero] at hmul
    exact ha hmul.symm
  have hpow : y ^ Ω b ≤ b :=
    yPowOmegaLe hb0 (fun q hq hdvd => rough ha hq hdvd)
  have hmono : y ^ (K + 1) ≤ y ^ Ω b := Nat.pow_le_pow_right (by omega : 1 ≤ y) hge
  have hb_le : b ≤ a := Nat.div_le_self _ _
  exact (lt_irrefl a) (lt_of_lt_of_le hK (hmono.trans (hpow.trans hb_le)))

end OMA535Extract

open OMA535Extract

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  intro N y L K hy hTwo hPow A hA
  classical
  by_cases hne : A.Nonempty
  · let Pcard := (primesBelow y).length
    let M := (L + 1) ^ Pcard
    let t := A.image (code L y)
    have hexp : ∀ a ∈ A, ∀ p, p.Prime → p < y → a.factorization p ≤ L := by
      intro a ha p hp hpy
      have haI := Finset.mem_Icc.mp (hA ha)
      exact factorization_le_two_pow (by omega) (lt_of_le_of_lt haI.2 hTwo) hp
    have ht_lt : ∀ c ∈ t, c < M := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [M, Pcard] using code_lt (hexp a ha)
    have hcardt : t.card ≤ M := by
      have hsub : t ⊆ Finset.range M := fun c hc => Finset.mem_range.mpr (ht_lt c hc)
      simpa [Finset.card_range] using Finset.card_le_card hsub
    have hMle : M ≤ (L + 1) ^ y := by
      have hlen : Pcard ≤ y := by
        simpa [Pcard, primesBelow, Finset.length_sort] using
          Finset.card_filter_le (Finset.range y) Nat.Prime
      exact Nat.pow_le_pow_right (by omega : 1 ≤ L + 1) hlen
    have htne : t.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨code L y a, Finset.mem_image_of_mem _ ha⟩
    obtain ⟨c0, hc0, hcmax⟩ := Finset.exists_max_image t
      (fun c => (A.filter (fun a => code L y a = c)).card) htne
    let F := A.filter (fun a => code L y a = c0)
    have hAcard : A.card ≤ t.card * F.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := A) (t := t) (f := code L y) (fun a ha => Finset.mem_image_of_mem _ ha)
      calc
        A.card = ∑ c ∈ t, (A.filter (fun a => code L y a = c)).card := hfib
        _ ≤ ∑ _c ∈ t, F.card := Finset.sum_le_sum (fun c hc => hcmax c hc)
        _ = t.card * F.card := by rw [Finset.sum_const, smul_eq_mul]
    have hFne : F.Nonempty := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc0
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
    obtain ⟨a0, ha0F⟩ := hFne
    let s := sOf y a0
    have hs_eq : ∀ a ∈ F, sOf y a = s := by
      intro a haF
      have hcode : code L y a = code L y a0 := by
        have ha := Finset.mem_filter.mp haF
        have ha0 := Finset.mem_filter.mp ha0F
        rw [ha.2, ha0.2]
      exact code_eq_sOf (hexp a (Finset.mem_filter.mp haF).1)
        (hexp a0 (Finset.mem_filter.mp ha0F).1) hcode
    have hsdiv : ∀ a ∈ F, s ∣ a := by
      intro a haF
      have haA := (Finset.mem_filter.mp haF).1
      have ha0 : a ≠ 0 := by
        have := (Finset.mem_Icc.mp (hA haA)).1
        omega
      rw [← hs_eq a haF]
      exact sOf_dvd ha0
    let Bs := F.image (fun a => a / s)
    have hcardF : F.card = Bs.card := by
      symm
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb hab
      have ha' : a ∈ F := by simpa using ha
      have hb' : b ∈ F := by simpa using hb
      have hma := Nat.mul_div_cancel' (hsdiv a ha')
      have hmb := Nat.mul_div_cancel' (hsdiv b hb')
      have hab' : a / s = b / s := by simpa using hab
      rw [← hma, ← hmb, hab']
    have hOmegaMap : ∀ b ∈ Bs, Ω b ∈ Finset.range (K + 1) := by
      intro b hb
      obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp hb
      have haA := (Finset.mem_filter.mp haF).1
      have haI := Finset.mem_Icc.mp (hA haA)
      have ha0 : a ≠ 0 := by omega
      have hle := omegaLe hy ha0 (lt_of_le_of_lt haI.2 hPow)
      rw [hs_eq a haF] at hle
      rw [Finset.mem_range]
      omega
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (Finset.range (K + 1))
      (fun j => (Bs.filter (fun b => Ω b = j)).card)
      ⟨0, Finset.mem_range.mpr (by omega)⟩
    let B := Bs.filter (fun b => Ω b = k)
    have hBcard : Bs.card ≤ (K + 1) * B.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := Bs) (t := Finset.range (K + 1)) (f := fun b => Ω b) hOmegaMap
      calc
        Bs.card = ∑ j ∈ Finset.range (K + 1), (Bs.filter (fun b => Ω b = j)).card := hfib
        _ ≤ ∑ _j ∈ Finset.range (K + 1), B.card :=
            Finset.sum_le_sum (fun j hj => hkmax j hj)
        _ = (K + 1) * B.card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hAle : A.card ≤ (L + 1) ^ y * (K + 1) * B.card := by
      calc
        A.card ≤ t.card * F.card := hAcard
        _ ≤ M * F.card := Nat.mul_le_mul_right _ hcardt
        _ = M * Bs.card := by rw [hcardF]
        _ ≤ M * ((K + 1) * B.card) := Nat.mul_le_mul_left _ hBcard
        _ = M * (K + 1) * B.card := by rw [Nat.mul_assoc]
        _ ≤ (L + 1) ^ y * (K + 1) * B.card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hMle)
    have hspos : 0 < s := Nat.pos_of_ne_zero (by
      have ha0 : a0 ≠ 0 := by
        have := (Finset.mem_Icc.mp (hA (Finset.mem_filter.mp ha0F).1)).1
        omega
      simpa [s] using sOf_ne_zero y a0)
    have hkLe : k ≤ K := by
      have := Finset.mem_range.mp hk
      omega
    refine ⟨s, k, B, hspos, hkLe, ?_, hAle, ?_⟩
    · intro b hb
      obtain ⟨hbB, hbΩ⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp hbB
      have haA := (Finset.mem_filter.mp haF).1
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hA haA)).1
      have ha0 : a ≠ 0 := by omega
      have hmul := Nat.mul_div_cancel' (hsdiv a haF)
      have hb0 : a / s ≠ 0 := by
        intro hb0
        rw [hb0, Nat.mul_zero] at hmul
        exact ha0 hmul.symm
      exact ⟨Nat.one_le_iff_ne_zero.mpr hb0, hbΩ⟩
    · intro b hb
      obtain ⟨hbB, _⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp hbB
      rw [Nat.mul_div_cancel' (hsdiv a haF)]
      exact (Finset.mem_filter.mp haF).1
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, 0, ∅, Nat.one_pos, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro a ha
      exact (Finset.notMem_empty a ha).elim
    · simp [hempty]
    · intro b hb
      exact (Finset.notMem_empty b hb).elim
