import OMAReductions.R_oeis_a247602_R1
import Mathlib

/-! Sun's equation for the first eleven indices. The two larger counts use
Legendre's partial sieve. The cardinality argument follows eitan654's
oeis-a366274.R1, with a stopping rule for complete descending prime lists.
Once the current cutoff prime is at least n, only 1 survives. -/

open Finset

private def sift : List ℕ → ℕ → ℕ
  | [], n => n
  | p :: ps, n => if n = 0 then 0 else if n ≤ p then 1 else sift ps n - sift ps (n / p)

private def smallPrimes : List ℕ :=
  [409, 401, 397, 389, 383, 379, 373, 367, 359, 353, 349, 347, 337, 331, 317,
   313, 311, 307, 293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233,
   229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151,
   149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73,
   71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13,
   11, 7, 5, 3, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem piLegendre (x : ℕ) (lo : 409 ≤ x) (hi : x ≤ 174570) :
    Nat.primeCounting x + 1 = 80 + sift smallPrimes x := by
  have card_sieve : ∀ (ps : List ℕ), (∀ p ∈ ps, Nat.Prime p) → ps.Pairwise Nat.Coprime →
      ps.Pairwise (· > ·) → (∀ r ∈ ps, ∀ q ≤ r, Nat.Prime q → q ∈ ps) →
      ∀ n : ℕ, ((Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)).card = sift ps n := by
    intro ps
    induction ps with
    | nil =>
      intro _ _ _ _ n
      simp [sift]
    | cons p ps ih =>
      intro hprime hpw hsort hfill n
      obtain ⟨hcop_p, hpw_ps⟩ := List.pairwise_cons.mp hpw
      obtain ⟨hmax, hsort_ps⟩ := List.pairwise_cons.mp hsort
      have hp : 0 < p := (hprime p (List.mem_cons_self ..)).pos
      have hprime_ps : ∀ q ∈ ps, Nat.Prime q := fun q hq =>
        hprime q (List.mem_cons_of_mem p hq)
      have hfill_ps : ∀ r ∈ ps, ∀ q ≤ r, Nat.Prime q → q ∈ ps := by
        intro r hr q hqr hq
        have hm := hfill r (List.mem_cons_of_mem p hr) q hqr hq
        exact (List.mem_cons.mp hm).resolve_left (ne_of_lt (lt_of_le_of_lt hqr (hmax r hr)))
      by_cases hn : n = 0
      · subst n
        simp [sift]
      by_cases hsmall : n ≤ p
      · have E : ((Icc 1 n).filter (fun m => ∀ q ∈ p :: ps, ¬ q ∣ m)) = {1} := by
          ext m
          simp only [mem_filter, mem_Icc, mem_singleton]
          constructor
          · rintro ⟨⟨hm, hmn⟩, hd⟩
            by_contra hne
            have prime := Nat.minFac_prime hne
            have dv := Nat.minFac_dvd m
            have bound := Nat.le_of_dvd (by omega : 0 < m) dv
            exact hd m.minFac (hfill p (List.mem_cons_self ..) m.minFac (by omega) prime) dv
          · rintro rfl
            exact ⟨⟨by decide, by omega⟩, fun q hq => (hprime q hq).not_dvd_one⟩
        rw [E]
        simp [sift, hn, hsmall]
      · have hphi_eq : sift (p :: ps) n = sift ps n - sift ps (n / p) := by
          change (if n = 0 then 0 else if n ≤ p then 1 else _) = _
          rw [if_neg hn, if_neg hsmall]
        rw [hphi_eq]
        set S := (Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)
        have hS : S.card = sift ps n := ih hprime_ps hpw_ps hsort_ps hfill_ps n
        have hA_eq :
            (Icc 1 n).filter (fun m => ∀ q ∈ p :: ps, ¬ q ∣ m) =
              S.filter (fun m => ¬ p ∣ m) := by
          ext m
          simp only [S, mem_filter, List.mem_cons, forall_eq_or_imp]
          tauto
        have hsplit : (S.filter (fun m => ¬ p ∣ m)).card + (S.filter (fun m => p ∣ m)).card = S.card := by
          simpa [add_comm] using Finset.card_filter_add_card_filter_not (s := S) (p := fun m => p ∣ m)
        have hB :
            (S.filter (fun m => p ∣ m)).card =
              ((Icc 1 (n / p)).filter (fun k => ∀ q ∈ ps, ¬ q ∣ k)).card := by
          symm
          refine Finset.card_bij (fun k _ => p * k) ?_ ?_ ?_
          · intro k hk
            simp only [mem_filter, mem_Icc, S] at hk ⊢
            obtain ⟨⟨hk1, hkle⟩, hnd⟩ := hk
            refine ⟨⟨⟨by nlinarith,
              (Nat.mul_comm p k).trans_le ((Nat.le_div_iff_mul_le hp).mp hkle)⟩,
              fun q hq hdiv => ?_⟩, dvd_mul_right p k⟩
            have hcop : q.Coprime p := (hcop_p q hq).symm
            exact hnd q hq (hcop.dvd_of_dvd_mul_left hdiv)
          · intro k₁ _ k₂ _ heq
            exact Nat.eq_of_mul_eq_mul_left hp heq
          · intro m hm
            simp only [mem_filter, mem_Icc, S] at hm
            obtain ⟨⟨⟨hm1, hmn⟩, hnd⟩, ⟨k, rfl⟩⟩ := hm
            refine ⟨k, ?_, rfl⟩
            simp only [mem_filter, mem_Icc]
            refine ⟨⟨?_, (Nat.le_div_iff_mul_le hp).mpr (by rw [Nat.mul_comm]; exact hmn)⟩,
              fun q hq hdiv => hnd q hq (dvd_mul_of_dvd_right hdiv p)⟩
            by_contra hk0
            have : k = 0 := by omega
            subst this
            omega
        have hB_phi : (S.filter (fun m => p ∣ m)).card = sift ps (n / p) := by
          rw [hB]
          exact ih hprime_ps hpw_ps hsort_ps hfill_ps (n / p)
        rw [hA_eq]
        omega
  have primeCounting_eq_phi :
      ∀ (ps : List ℕ) (n : ℕ),
        (∀ p ∈ ps, p.Prime) → ps.Nodup → (∀ p ∈ ps, p ≤ n) →
        ps.Pairwise (· > ·) → (∀ r ∈ ps, ∀ q ≤ r, Nat.Prime q → q ∈ ps) →
        (∀ q : ℕ, q.Prime → q * q ≤ n → q ∈ ps) → 1 ≤ n →
        Nat.primeCounting n + 1 = ps.length + sift ps n := by
    intro ps n hprime hnodup hle hsort hfill hsq hn1
    have hpos : ∀ p ∈ ps, 0 < p := fun p hp => (hprime p hp).pos
    have hpw : ps.Pairwise Nat.Coprime := by
      refine hnodup.imp_of_mem ?_
      intro a b ha hb hne
      exact (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hne
    have hcard := card_sieve ps hprime hpw hsort hfill n
    set S := (Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)
    have hSeq : S = insert 1 (Nat.primesLE n \ ps.toFinset) := by
      ext m
      simp only [S, mem_filter, mem_Icc, mem_insert, mem_sdiff, Nat.mem_primesLE, List.mem_toFinset]
      constructor
      · rintro ⟨⟨hm1, hmn⟩, hnd⟩
        by_cases h1 : m = 1
        · exact Or.inl h1
        · right
          have hmpr : m.Prime := by
            by_contra hnot
            have hqpr : m.minFac.Prime := Nat.minFac_prime h1
            have hqsq : m.minFac * m.minFac ≤ m := by
              simpa [sq] using Nat.minFac_sq_le_self (by omega) hnot
            have hqmem : m.minFac ∈ ps := hsq m.minFac hqpr (hqsq.trans hmn)
            exact hnd m.minFac hqmem (Nat.minFac_dvd m)
          refine ⟨⟨hmn, hmpr⟩, fun hmem => hnd m hmem dvd_rfl⟩
      · rintro (rfl | ⟨⟨hmn, hmpr⟩, hnotmem⟩)
        · exact ⟨⟨le_rfl, hn1⟩, fun q hq => (hprime q hq).not_dvd_one⟩
        · refine ⟨⟨hmpr.one_le, hmn⟩, fun q hq hdvd => ?_⟩
          have heq : q = m := (Nat.prime_dvd_prime_iff_eq (hprime q hq) hmpr).mp hdvd
          exact hnotmem (heq ▸ hq)
    have hsub : ps.toFinset ⊆ Nat.primesLE n := by
      intro p hp
      rw [List.mem_toFinset] at hp
      exact Nat.mem_primesLE.mpr ⟨hle p hp, hprime p hp⟩
    have h1not : (1 : ℕ) ∉ Nat.primesLE n \ ps.toFinset := by
      intro h1
      exact Nat.not_prime_one (Nat.mem_primesLE.mp (mem_sdiff.mp h1).1).2
    have hScard : S.card = 1 + ((Nat.primesLE n).card - ps.toFinset.card) := by
      rw [hSeq, card_insert_of_notMem h1not, card_sdiff_of_subset hsub]
      omega
    have hlen : ps.toFinset.card = ps.length := List.toFinset_card_of_nodup hnodup
    have hpi : (Nat.primesLE n).card = Nat.primeCounting n := Nat.primesLE_card_eq_primeCounting n
    have hle_card : ps.toFinset.card ≤ (Nat.primesLE n).card := card_le_card hsub
    rw [hlen, hpi] at hScard hle_card
    omega
  have maxPrime : ∀ r ∈ smallPrimes, r ≤ 409 := by decide +kernel
  have covers : ∀ q : Fin 418, q.val.Prime → q.val ∈ smallPrimes := by decide +kernel
  have hfill : ∀ r ∈ smallPrimes, ∀ q ≤ r, Nat.Prime q → q ∈ smallPrimes := by
    intro r hr q hq hpr
    have : r ≤ 409 := maxPrime r hr
    exact covers ⟨q, by omega⟩ hpr
  have hsq : ∀ q : ℕ, q.Prime → q*q ≤ x → q ∈ smallPrimes := by
    intro q hp hb
    apply covers ⟨q, ?_⟩ hp
    by_contra! h
    have hh := Nat.mul_le_mul h h
    omega
  exact primeCounting_eq_phi smallPrimes x (by decide +kernel) (by decide +kernel)
    (fun p hp => (maxPrime p hp).trans lo) (by decide +kernel) hfill hsq (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pi10 : Nat.primeCounting 80410 = 7872 := by
  have h := piLegendre 80410 (by decide) (by decide)
  have e : sift smallPrimes 80410 = 7793 := by decide +kernel
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pi11 : Nat.primeCounting 174570 = 15880 := by
  have h := piLegendre 174570 (by decide) (by decide)
  have e : sift smallPrimes 174570 = 15801 := by decide +kernel
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_oeis_a247602_R1.H1 := by
  intro n hn hN
  interval_cases n
  · exact ⟨3, by decide, by decide +kernel⟩
  · exact ⟨2, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨91, by decide, by decide +kernel⟩
  · exact ⟨6, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · refine ⟨8041, by decide, ?_⟩
    change Nat.primeCounting 80410 = Nat.totient (83 * 97)
    rw [pi10, Nat.totient_mul (by decide : Nat.Coprime 83 97),
      Nat.totient_prime (by norm_num : Nat.Prime 83), Nat.totient_prime (by norm_num : Nat.Prime 97)]
  · refine ⟨15870, by decide, ?_⟩
    change Nat.primeCounting 174570 = Nat.totient 15881
    rw [pi11, Nat.totient_prime (by norm_num : Nat.Prime 15881)]


