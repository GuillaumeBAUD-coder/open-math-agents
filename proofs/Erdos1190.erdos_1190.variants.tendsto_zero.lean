import FormalConjectures.ErdosProblems.«1190»

/-!
# The limiting reciprocal mass of disjoint residue classes

Apply the prime-dividing descent for Erdős 202 to the moduli in a dyadic interval.
The divisor-counting estimate and an estimate for multiples of large prime powers
give a summable bound for the mass of each interval.

The CRT, finite-fiber, harmonic-sum and multiple-counting lemmas below are adapted from
Pawan Sasanka Ammanamanchi and collaborators' Apache-2.0 formalization:
https://github.com/Shashi456/erdos-formalizations and
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos202.lean .
-/
namespace OMA.E202
open Filter Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}
lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  constructor
  · rintro ⟨n, hnq, hnr⟩
    rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd] at hnq hnr
    rw [Int.modEq_iff_dvd]
    have hdq : (Nat.gcd q r : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left q r
    have hdr : (Nat.gcd q r : ℤ) ∣ (r : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right q r
    have hqa : (Nat.gcd q r : ℤ) ∣ a - n := dvd_trans hdq hnq
    have hrb : (Nat.gcd q r : ℤ) ∣ b - n := dvd_trans hdr hnr
    have hsub : (Nat.gcd q r : ℤ) ∣ (b - n) - (a - n) := dvd_sub hrb hqa
    convert hsub using 1
    ring
  · intro hab
    rw [Int.modEq_iff_dvd] at hab
    rcases hab with ⟨k, hk⟩
    let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
    refine ⟨n, ?_, ?_⟩
    · rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd]
      refine ⟨-(Nat.gcdA q r * k), ?_⟩
      simp [n]
      ring
    · rw [residueClass, Set.mem_ofPred_eq, Int.modEq_iff_dvd]
      refine ⟨Nat.gcdB q r * k, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab q r
      calc
        b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
          simp [n]
          ring
        _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hk]
        _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
              - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hbez]
        _ = (r : ℤ) * (Nat.gcdB q r * k) := by
          ring
lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

private structure Packing {ι : Type} (s : Finset ι) (q : ι → ℕ) (a : ι → ℤ) (N : ℕ) : Prop where
  bounds : ∀ i ∈ s, 0 < q i ∧ q i ≤ N
  inj : Set.InjOn q (s : Set ι)
  sep : ∀ i ∈ s, ∀ j ∈ s, ∀ x : ℤ, x ≡ a i [ZMOD (q i : ℤ)] →
      x ≡ a j [ZMOD (q j : ℤ)] → i = j

private theorem Packing.restrict {ι : Type} {s t : Finset ι} {q a N}
    (h : Packing s q a N) (ht : t ⊆ s) : Packing t q a N :=
  ⟨fun i hi => h.bounds i (ht hi), h.inj.mono ht,
    fun i hi j hj => h.sep i (ht hi) j (ht hj)⟩

private theorem Packing.share {ι : Type} {s : Finset ι} {q a N} (h : Packing s q a N)
    (hs : 1 < s.card) {i j} (hi : i ∈ s) (hj : j ∈ s) :
    ∃ p ∈ (q i).primeFactors, p ∣ q j := by
  have aux : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ (q x).Coprime (q y) := by
    intro x hx y hy hxy hc
    have hm : a x ≡ a y [ZMOD (Nat.gcd (q x) (q y) : ℤ)] := by simp [hc.gcd_eq_one, Int.ModEq]
    obtain ⟨z, hz, hz'⟩ := (residueClass_inter_nonempty_iff
      (h.bounds x hx).1 (h.bounds y hy).1 (a x) (a y)).2 hm
    exact hxy (h.sep x hx y hy z hz hz')
  have hnc : ¬ (q i).Coprime (q j) := by
    by_cases he : i = j
    · subst j
      obtain ⟨b, hb, hbi⟩ := s.exists_mem_ne hs i
      intro hc
      have hone : q i = 1 := by simpa [Nat.Coprime] using hc
      exact aux i hi b hb hbi.symm (by simp [hone])
    · exact aux i hi j hj he
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpi, (h.bounds i hi).1.ne'⟩, hpj⟩

private theorem Packing.step {ι : Type} {s : Finset ι} {q a N K k D : _}
    (h : Packing s q a N) (hs : 1 < s.card) (hd : N ≤ D * s.card)
    (hk : k + 1 ≤ K) (hΩ : ∀ i ∈ s, Ω (q i) ≤ k + 1) :
    ∃ (p : ℕ) (t : Finset ι), 0 < p ∧ p ≤ D*K ∧ p ≤ N ∧
      Packing t (fun i => q i / p) (fun i => a i / (p : ℤ)) (N / p) ∧
      N / p ≤ (D*K) * t.card ∧ ∀ i ∈ t, Ω (q i / p) ≤ k := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let g := fun j => if hj : j ∈ s then (h.share hs hi hj).choose else 0
  have hg (j) (hj : j ∈ s) : g j ∈ (q i).primeFactors ∧ g j ∣ q j := by
    simpa [g, hj] using (h.share hs hi hj).choose_spec
  obtain ⟨p, hp, hpop⟩ := exists_fiber_card_mul_range_card_ge s (q i).primeFactors g
    ⟨g i, (hg i hi).1⟩ (fun j hj => (hg j hj).1)
  let u := s.filter fun j => g j = p
  have hK : (q i).primeFactors.card ≤ K :=
    (List.toFinset_card_le _).trans ((hΩ i hi).trans hk)
  have hpop' : s.card ≤ K * u.card := hpop.trans (Nat.mul_le_mul_right _ hK)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpN := (Nat.le_of_dvd (h.bounds i hi).1 (Nat.dvd_of_mem_primeFactors hp)).trans (h.bounds i hi).2
  have hu (j) (hj : j ∈ u) : j ∈ s ∧ p ∣ q j := by
    obtain ⟨hsj, hh⟩ := mem_filter.mp hj
    exact ⟨hsj, hh ▸ (hg j hsj).2⟩
  have hu_pos (j) (hj : j ∈ u) : 0 < q j / p :=
    Nat.div_pos (Nat.le_of_dvd (h.bounds j (hu j hj).1).1 (hu j hj).2) hprime.pos
  have inj' : Set.InjOn (fun j => q j / p) (u : Set ι) := by
    intro x hx y hy he
    apply h.inj (hu x hx).1 (hu y hy).1
    simpa only [Nat.div_mul_cancel (hu x hx).2, Nat.div_mul_cancel (hu y hy).2] using
      congrArg (fun v : ℕ => v * p) he
  have hcount : u.card ≤ N / p := by
    have := Finset.card_le_card_of_injOn (s := u) (t := Icc 1 (N / p))
      (fun j => q j / p) (fun j hj => mem_Icc.mpr ⟨hu_pos j hj,
        Nat.div_le_div_right (h.bounds j (hu j hj).1).2⟩) inj'
    simpa using this
  have hud : N ≤ (D*K) * u.card := by
    simpa only [Nat.mul_assoc] using hd.trans (Nat.mul_le_mul_left D hpop')
  have hu0 : 0 < u.card := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh, Nat.mul_zero] at hpop'
    omega
  have hpDK : p ≤ D*K := by
    apply Nat.le_of_mul_le_mul_right (c := u.card) _ hu0
    exact (Nat.mul_le_mul_left p hcount).trans ((Nat.mul_div_le N p).trans hud)
  let b := fun j => (a j % (p : ℤ)).toNat
  have hpi : (0 : ℤ) < p := by exact_mod_cast hprime.pos
  have hb (j) : (b j : ℤ) = a j % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hpi.ne')
  obtain ⟨r, hr, hres⟩ := exists_fiber_card_mul_range_card_ge u (range p) b
    ⟨0, by simpa using hprime.pos⟩ (fun j _ => by
      apply mem_range.mpr
      have := Int.emod_lt_of_pos (a j) hpi
      rw [← hb] at this
      exact_mod_cast this)
  let t := u.filter fun j => b j = r
  have hres' : u.card ≤ p * t.card := by simpa [t] using hres
  have ht (j) (hj : j ∈ t) : j ∈ u := (mem_filter.mp hj).1
  have heq (j) (hj : j ∈ t) : (r : ℤ) + p * (a j / (p : ℤ)) = a j := by
    rw [← (mem_filter.mp hj).2, hb]
    exact Int.emod_add_mul_ediv _ _
  refine ⟨p, t, hprime.pos, hpDK, hpN, ⟨?_, inj'.mono (filter_subset _ _), ?_⟩, ?_, ?_⟩
  · intro j hj
    exact ⟨hu_pos j (ht j hj), Nat.div_le_div_right (h.bounds j (hu j (ht j hj)).1).2⟩
  · intro j hj l hl x hx hy
    have lift (v) (hv : v ∈ t) (hxv : x ≡ a v / (p : ℤ) [ZMOD (q v / p : ℕ)]) :
        (r : ℤ) + p*x ≡ a v [ZMOD (q v : ℤ)] := by
      have hz := (Int.ModEq.mul_left' (c := (p : ℤ)) hxv).add_left (r : ℤ)
      have hprod : (p : ℤ) * (q v / p : ℕ) = q v := by
        exact_mod_cast Nat.mul_div_cancel' (hu v (ht v hv)).2
      rwa [hprod, heq v hv] at hz
    exact h.sep j (hu j (ht j hj)).1 l (hu l (ht l hl)).1 _ (lift j hj hx) (lift l hl hy)
  · have hz := hud.trans (Nat.mul_le_mul_left (D*K) hres')
    calc
      N / p ≤ ((D*K*t.card)*p)/p := Nat.div_le_div_right (by simpa only [Nat.mul_assoc, Nat.mul_comm p t.card] using hz)
      _ = _ := Nat.mul_div_cancel _ hprime.pos
  · intro j hj
    have hv := hu j (ht j hj)
    have hbound := hΩ j hv.1
    have hh := ArithmeticFunction.cardFactors_mul hprime.ne_zero (hu_pos j (ht j hj)).ne'
    rw [Nat.mul_div_cancel' hv.2, ArithmeticFunction.cardFactors_apply_prime hprime] at hh
    omega

private theorem Packing.small {ι : Type} {s : Finset ι} {q a N} (h : Packing s q a N)
    (h0 : ∀ i ∈ s, Ω (q i) ≤ 0) : s.card ≤ 1 := by
  by_contra! hs
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨p, hp, -⟩ := h.share hs hx hx
  have he := cardFactors_eq_zero_iff_eq_zero_or_one.mp (Nat.eq_zero_of_le_zero (h0 x hx))
  have hxpos := (h.bounds x hx).1
  rcases he with he | he
  · omega
  · simp [he] at hp

private theorem chain {ι : Type} (K B k : ℕ) (hK : 1 ≤ K) (hk : k ≤ K)
    {s : Finset ι} {q a N D} (h : Packing s q a N) (hd : N ≤ D * s.card)
    (hΩ : ∀ i ∈ s, Ω (q i) ≤ k) (hB : D*K^k ≤ B) :
    N + 1 ≤ (B+1)^(k+1) := by
  have hDB : D ≤ B := (Nat.le_mul_of_pos_right _ (pow_pos hK _)).trans hB
  by_cases hs : s.card ≤ 1
  · have hn : N ≤ D := hd.trans (by simpa using Nat.mul_le_mul_left D hs)
    exact (Nat.succ_le_succ (hn.trans hDB)).trans (Nat.le_self_pow (by omega) _)
  · cases k with
    | zero => exact False.elim (hs (h.small hΩ))
    | succ k =>
      obtain ⟨p, t, hp, hpD, hpN, ht, hdt, hΩt⟩ := h.step (by omega) hd hk hΩ
      have hB' : (D*K)*K^k ≤ B := by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm K] using hB
      have hpb : p ≤ B := hpD.trans ((Nat.le_mul_of_pos_right _ (pow_pos hK _)).trans hB')
      have hrec := chain K B k hK (by omega) ht hdt hΩt hB'
      have hrem := Nat.mod_lt N hp
      have hdiv := Nat.mod_add_div N p
      calc
        N+1 ≤ p * (N/p+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ (B+1) * (B+1)^(k+1) := Nat.mul_le_mul (by omega) hrec
        _ = _ := by rw [pow_succ (B+1) (k+1), Nat.mul_comm]
termination_by k

lemma card_Icc_filter_dvd_le_div (y d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
  classical
  calc
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card
        ≤ (Finset.Icc 1 (y / d)).card := by
          refine Finset.card_le_card_of_injOn
            (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
            (t := Finset.Icc 1 (y / d))
            (fun n : ℕ => n / d) ?_ ?_
          · intro n hn
            have hn' : n ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hn
            rw [Finset.mem_filter] at hn'
            have hnIcc := Finset.mem_Icc.mp hn'.1
            have hdn : d ∣ n := hn'.2
            have htarget : n / d ∈ Finset.Icc 1 (y / d) := by
              rw [Finset.mem_Icc]
              refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
              exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hnIcc.1 hdn) hd)
            simpa using htarget
          · intro a ha b hb hab
            have ha' : a ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using ha
            have hb' : b ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hb
            rw [Finset.mem_filter] at ha'
            rw [Finset.mem_filter] at hb'
            have hda : d ∣ a := ha'.2
            have hdb : d ∣ b := hb'.2
            have hab' : a / d = b / d := by simpa using hab
            calc
              a = a / d * d := (Nat.div_mul_cancel hda).symm
              _ = b / d * d := by rw [hab']
              _ = b := Nat.div_mul_cancel hdb
    _ = y / d := by simp
lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h :=
    Real.one_sub_inv_le_log_of_pos
      (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

lemma harmonic_Icc_one_le_one_add_log (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (m : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        have htop_not : m + 1 ∉ Finset.Icc 1 m := by
          simp
        have hIcc :
            Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k
          simp
          omega
        have hterm := one_div_nat_succ_le_log_succ_sub_log (m := m) hm
        calc
          (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
              = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
                  (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                    rw [hIcc, Finset.sum_insert htop_not]
                    ring
          _ ≤ (1 + Real.log (m : ℝ)) +
                (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
          _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
                  linarith
          _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
                  rfl

lemma sum_inv_sq_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)
lemma sum_Icc_inv_sq_le_two_bfv (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  classical
  have hIcc :
      Finset.Icc 1 N = (Finset.range N).image (fun ν : ℕ => ν + 1) := by
    ext d
    constructor
    · intro hd
      have hdIcc := Finset.mem_Icc.mp hd
      exact Finset.mem_image.2
        ⟨d - 1, Finset.mem_range.2 (Nat.sub_one_lt_of_le hdIcc.1 hdIcc.2),
          by omega⟩
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨ν, hν, rfl⟩
      exact Finset.mem_Icc.2
        ⟨by omega, Nat.succ_le_iff.2 (Finset.mem_range.1 hν)⟩
  rw [hIcc]
  rw [Finset.sum_image]
  · simpa using sum_inv_sq_le_two N
  · intro a _ha b _hb h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)

private theorem total_divisors (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) ≤ N*(1+Real.log N) := by
  classical
  let I := Icc 1 N
  have eqd (n) (hn : n ∈ I) : n.divisors = I.filter (· ∣ n) := by
    ext d
    obtain ⟨h1,hN⟩ := mem_Icc.mp hn
    simp only [Nat.mem_divisors, mem_filter, I, mem_Icc]
    constructor
    · rintro ⟨hd,hn0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd h1, (Nat.le_of_dvd h1 hd).trans hN⟩,hd⟩
    · exact fun ha => ⟨ha.2, by omega⟩
  calc
    _ = ∑ n ∈ I, ∑ d ∈ I, (if d ∣ n then (1:ℝ) else 0) := by
      apply sum_congr rfl
      intro n hn
      simp [eqd n hn]
    _ = ∑ d ∈ I, ((I.filter (fun n => d ∣ n)).card:ℝ) := by
      rw [sum_comm]; simp
    _ ≤ ∑ d ∈ I, (N:ℝ)*(1/d) := by
      apply sum_le_sum
      intro d hd
      rw [mul_one_div]
      exact (Nat.cast_le.mpr (card_Icc_filter_dvd_le_div N d (mem_Icc.mp hd).1)).trans Nat.cast_div_le
    _ ≤ _ := by
      rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (harmonic_Icc_one_le_one_add_log N) (by positivity)

private theorem many_factors {s : Finset ℕ} {N T : ℕ} (hs : s ⊆ Icc 1 N)
    (h : ∀ n ∈ s, T ≤ n.primeFactors.card) :
    (s.card : ℝ)*2^T ≤ N*(1+Real.log N) := by
  calc
    _ = ∑ _n ∈ s, (2:ℝ)^T := by simp
    _ ≤ ∑ n ∈ s, (n.divisors.card:ℝ) := by
      apply sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp (hs hn)).1
      suffices hh : 2^T ≤ n.divisors.card by exact_mod_cast hh
      rw [Nat.card_divisors hn0]
      calc
        _ ≤ 2^n.primeFactors.card := Nat.pow_le_pow_right (by norm_num) (h n hn)
        _ = ∏ _p ∈ n.primeFactors, 2 := by simp
        _ ≤ _ := Finset.prod_le_prod' fun p hp => by
          have he := Finsupp.mem_support_iff.mp (show p ∈ n.factorization.support from hp)
          omega
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans (total_divisors N)

private theorem large_power {s : Finset ℕ} {N T : ℕ} (hs : s ⊆ Icc 1 N)
    (h : ∀ n ∈ s, ∃ p ∈ n.primeFactors, T+2 ≤ n.factorization p) :
    (s.card : ℝ)*2^T ≤ N*2 := by
  classical
  let P := Icc 2 N
  let E := fun p => (Icc 1 N).filter fun n => p^(T+2) ∣ n
  have sub : s ⊆ P.biUnion E := by
    intro n hn
    obtain ⟨p,hp,he⟩ := h n hn
    have hprime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hpos,hN⟩ := mem_Icc.mp (hs hn)
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨hprime.two_le,
      (Nat.le_of_dvd hpos (Nat.dvd_of_mem_primeFactors hp)).trans hN⟩,
      mem_filter.mpr ⟨hs hn,(hprime.pow_dvd_iff_le_factorization (Nat.ne_of_gt hpos)).mpr he⟩⟩
  have hc : s.card ≤ ∑ p ∈ P, (E p).card := (card_le_card sub).trans card_biUnion_le
  calc
    _ ≤ (∑ p ∈ P, ((E p).card:ℝ)) * (2:ℝ)^T := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = ∑ p ∈ P, ((E p).card:ℝ)*(2:ℝ)^T := sum_mul ..
    _ ≤ ∑ p ∈ P, (N:ℝ)*(1/(p:ℝ)^2) := by
      apply sum_le_sum
      intro p hp
      have hp2 := (mem_Icc.mp hp).1
      have hp0 : 0 < p := by omega
      have hh : ((E p).card:ℝ) ≤ (N:ℝ)/(p:ℝ)^(T+2) := by
        have hz := Nat.cast_le (α := ℝ) |>.mpr (card_Icc_filter_dvd_le_div N (p^(T+2)) (pow_pos hp0 _))
        exact hz.trans (by simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := p^(T+2))))
      have hR : (0:ℝ) < p := by exact_mod_cast hp0
      have h1 : (2:ℝ)^T ≤ (p:ℝ)^T := by gcongr; exact_mod_cast hp2
      calc
        _ ≤ ((N:ℝ)/(p:ℝ)^(T+2))*(p:ℝ)^T := mul_le_mul hh h1 (by positivity) (by positivity)
        _ = _ := by rw [pow_add]; field_simp
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg (fun x hx => mem_Icc.mpr
        ⟨by have := (mem_Icc.mp hx).1; omega, (mem_Icc.mp hx).2⟩)
        (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_le_two_bfv N)

private theorem omega_le {n T : ℕ} (hw : n.primeFactors.card ≤ T)
    (he : ∀ p ∈ n.primeFactors, n.factorization p ≤ T+2) : Ω n ≤ T*(T+2) := by
  rw [cardFactors_eq_sum_factorization, Finsupp.sum]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, (T+2) := sum_le_sum he
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (T+2) hw

private theorem log2_top : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro t
  filter_upwards [eventually_ge_atTop (2^t : ℕ)] with n hn
  exact Nat.le_log_of_pow_le (by decide) hn

private def depth (b : ℕ) := (4*b)*(4*b+2)

private theorem growth : ∀ᶠ t : ℕ in atTop,
    (2*(t+1)+(depth (t+1))^2+1)*(depth (t+1)+1) ≤ 2^t := by
  have hh := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 6 (r := 2) (by norm_num)).bound
    (show 0 < (1:ℝ)/10000000 by norm_num)
  filter_upwards [hh,eventually_ge_atTop (1:ℕ)] with t ht h1
  have hnat : 10000000*t^6 ≤ 2^t := by
    simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (t:ℝ)^6),
      Real.norm_of_nonneg (by positivity : 0 ≤ (2:ℝ)^t)] at ht
    exact_mod_cast (show (10000000:ℝ)*(t:ℝ)^6 ≤ (2:ℝ)^t by linarith)
  apply le_trans _ hnat
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le h1
  unfold depth
  ring_nf
  omega

private theorem interval_bound : ∀ᶠ j : ℕ in atTop,
    ∀ (s : Finset ℕ) (a : ℕ → ℤ), Packing s id a (2^(j+1)) →
      (s.card:ℝ)*(j+1:ℝ)^2 ≤ 4*(2:ℝ)^(j+1) := by
  classical
  have htop : Tendsto (fun j : ℕ => Nat.log 2 (j+1)) atTop atTop :=
    log2_top.comp (tendsto_add_atTop_nat 1)
  filter_upwards [htop.eventually growth] with j hj
  intro s a h
  let t := Nat.log 2 (j+1)
  let b := t+1
  let T := 4*b
  let K := depth b
  let D := 2^(2*b)
  let N := 2^(j+1)
  let v := s.filter fun n => T ≤ n.primeFactors.card
  let w := s.filter fun n => ∃ p ∈ n.primeFactors, T+2 ≤ n.factorization p
  let u := s.filter fun n => Ω n ≤ K
  have hs : s ⊆ Icc 1 N := fun n hn => mem_Icc.mpr (h.bounds n hn)
  have hv := many_factors (s := v) (N := N) ((filter_subset _ _).trans hs)
    (fun n hn => (mem_filter.mp hn).2)
  have hw := large_power (s := w) (N := N) ((filter_subset _ _).trans hs)
    (fun n hn => (mem_filter.mp hn).2)
  have hhi : j+1 < 2^b := Nat.lt_pow_succ_log_self (by decide) _
  have hlo : 2^t ≤ j+1 := Nat.pow_log_le_self 2 (by omega)
  have hD : (j+1)^2 ≤ D := by
    calc
      _ ≤ (2^b)^2 := Nat.pow_le_pow_left hhi.le _
      _ = _ := by simp [D, ← pow_mul, Nat.mul_comm]
  have hhN : N > D*u.card := by
    by_contra! hd
    have hc := chain K (D*K^K) K (by change 0 < (4*(t+1))*(4*(t+1)+2); positivity) le_rfl
      (h.restrict (show u ⊆ s from filter_subset _ _)) hd
      (fun i hi => (mem_filter.mp hi).2) le_rfl
    have hbase : D*K^K ≤ 2^(2*b+K^2) := by
      rw [pow_add, pow_two K, pow_mul 2 K K]
      exact Nat.mul_le_mul_left D (Nat.pow_le_pow_left K.lt_two_pow_self.le _)
    have hbase' : D*K^K+1 ≤ 2^(2*b+K^2+1) := by
      rw [pow_succ]
      have := Nat.two_pow_pos (2*b+K^2)
      omega
    have hbound : (D*K^K+1)^(K+1) ≤ N := by
      calc
        _ ≤ (2^(2*b+K^2+1))^(K+1) := Nat.pow_le_pow_left hbase' _
        _ = 2^((2*b+K^2+1)*(K+1)) := (pow_mul ..).symm
        _ ≤ N := Nat.pow_le_pow_right (by decide) (hj.trans hlo)
    exact (Nat.not_succ_le_self N) (hc.trans hbound)
  have hcard : s.card ≤ u.card + v.card + w.card := by
    have hsub : s ⊆ (u ∪ v) ∪ w := by
      intro n hn
      by_cases hvn : T ≤ n.primeFactors.card
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hvn⟩))
      by_cases hwn : ∃ p ∈ n.primeFactors, T+2 ≤ n.factorization p
      · exact mem_union_right _ (mem_filter.mpr ⟨hn,hwn⟩)
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,
        omega_le (Nat.le_of_lt (Nat.lt_of_not_ge hvn)) (fun p hp => by
          have hnot : ¬ T+2 ≤ n.factorization p := fun hle => hwn ⟨p,hp,hle⟩
          omega)⟩))
    exact (card_le_card hsub).trans ((card_union_le ..).trans
      (Nat.add_le_add_right (card_union_le ..) _))
  have hD0 : 0 < (D:ℝ) := by dsimp [D]; positivity
  have hDT : (2:ℝ)^T = (D:ℝ)^2 := by
    dsimp [T,D]; push_cast; rw [← pow_mul]; ring_nf
  have hlog : 1+Real.log (N:ℝ) ≤ D := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    have hpow : j+2 ≤ D := hhi.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [b]; omega))
    have hr : (j:ℝ)+2 ≤ D := by exact_mod_cast hpow
    dsimp [N]; push_cast; rw [Real.log_pow]; push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ (j:ℝ)+1 by positivity)]
  have hv' : (v.card:ℝ)*D ≤ N := by
    rw [hDT] at hv
    apply le_of_mul_le_mul_right (a := (D:ℝ)) _ hD0
    calc
      _ = (v.card:ℝ)*D^2 := by ring
      _ ≤ _ := hv
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
  have hw' : (w.card:ℝ)*D ≤ 2*N := by
    have h1 : (1:ℝ) ≤ D := by exact_mod_cast Nat.one_le_two_pow (n := 2*b)
    calc
      _ ≤ (w.card:ℝ)*2^T := by rw [hDT]; gcongr; nlinarith
      _ ≤ _ := by simpa [mul_comm] using hw
  have hcd : (s.card:ℝ) ≤ (u.card:ℝ)+v.card+w.card := by exact_mod_cast hcard
  have hu' : (D:ℝ)*u.card < N := by exact_mod_cast hhN
  have hind : ((j:ℝ)+1)^2 ≤ D := by exact_mod_cast hD
  suffices z : (s.card:ℝ)*((j:ℝ)+1)^2 ≤ 4*(N:ℝ) by simpa [N] using z
  exact (mul_le_mul_of_nonneg_left hind (Nat.cast_nonneg _)).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hcd hD0.le])

private noncomputable def massBound (j : ℕ) : ℝ := 8/((j:ℝ)+1)^2

private theorem mass_summable : Summable massBound := by
  have hs := ((summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))).mul_left (8 : ℝ)
  change Summable (fun j : ℕ => (8:ℝ)/((j:ℝ)+1)^2)
  simpa [div_eq_mul_inv] using hs

private theorem tail_bound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop, Erdos1190.eps m ≤ ε := by
  classical
  obtain ⟨J,hJ⟩ := eventually_atTop.mp interval_bound
  obtain ⟨k,hk⟩ := mass_summable.nat_tsum_vanishing (Iio_mem_nhds hε)
  filter_upwards [eventually_ge_atTop (2^(max k J) : ℕ)] with m hm
  unfold Erdos1190.eps
  apply csSup_le
  · refine ⟨0, ∅, fun _ => 0, ?_, ?_, ?_⟩ <;> simp
  rintro z ⟨s,a,hs,ha,rfl⟩
  let L := s.image (Nat.log 2)
  have hindex {j} (hj : j ∈ L) : max k J ≤ j := by
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
    exact Nat.le_log_of_pow_le (by decide) (hm.trans (hs n hn).le)
  have htail := hk (L : Set ℕ) (fun x hx => (le_max_left _ _).trans (hindex hx))
  rw [Finset.tsum_subtype', Set.mem_Iio] at htail
  apply le_trans _ htail.le
  calc
    _ = ∑ j ∈ L, ∑ n ∈ s.filter (fun n => Nat.log 2 n = j), (n:ℝ)⁻¹ :=
      (sum_fiberwise_of_maps_to (fun n => mem_image_of_mem (Nat.log 2)) _).symm
    _ ≤ ∑ j ∈ L, massBound j := by
      apply sum_le_sum
      intro j hj
      let U := s.filter fun n => Nat.log 2 n = j
      have hU {n} (hn : n ∈ U) : n ∈ s ∧ 2^j ≤ n ∧ n < 2^(j+1) := by
        obtain ⟨hnS, he⟩ := mem_filter.mp hn
        have hpos := hs n hnS
        exact ⟨hnS, he ▸ Nat.pow_log_le_self 2 (by omega),
          he ▸ Nat.lt_pow_succ_log_self (by decide) n⟩
      have hu : Packing U id a (2^(j+1)) := by
        refine ⟨fun n hn => ⟨?_,(hU hn).2.2.le⟩, Function.injective_id.injOn, ?_⟩
        · exact (Nat.zero_le m).trans_lt (hs n (hU hn).1)
        · intro n hn n' hn' x hx hx'
          by_contra hne
          exact ha n (hU hn).1 n' (hU hn').1 hne ⟨x,hx,hx'⟩
      have hcount := hJ j ((le_max_right _ _).trans (hindex hj)) U a hu
      calc
        _ ≤ ∑ _n ∈ U, ((2:ℝ)^j)⁻¹ := by
          apply sum_le_sum
          intro n hn
          exact inv_anti₀ (by positivity) (by exact_mod_cast (hU hn).2.1)
        _ = (U.card:ℝ) / (2:ℝ)^j := by simp [div_eq_mul_inv]
        _ ≤ massBound j := by
          rw [massBound, div_le_div_iff₀ (by positivity) (by positivity)]
          rw [pow_succ (2 : ℝ) j] at hcount
          linarith

end OMA.E202

open OMA.E202 Filter in
theorem OMA.solution : type_of% @Erdos1190.erdos_1190.variants.tendsto_zero := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [tail_bound (ε/2) (half_pos hε)] with m hm
  have hpos : 0 ≤ Erdos1190.eps m := by
    apply Real.sSup_nonneg
    rintro _ ⟨S,a,_,_,rfl⟩
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  linarith
