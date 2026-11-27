import FormalConjectures.ErdosProblems.«971»

/-!
Following Erdős, On some applications of Brun's method (1949), we count
ordered pairs of primes in the same reduced residue class. H1 locates
many pairs for infinitely many moduli. H2 bounds the third moment so
their contribution cannot be concentrated in a few highly occupied
classes. H3 bounds the total population after slightly enlarging the
cutoff. Clipping the occupancy at 2V/δ produces a positive density of
classes with no prime below the enlarged cutoff.
-/

namespace OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1

open Finset Filter Real Erdos971
open scoped Topology Classical

/-- A positive density of ordered prime pairs in the same coprime class,
for infinitely many moduli with bounded ratio d / phi(d). -/
def H1 : Prop :=
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  ∃ M > (0:ℝ), ∃ δ > (0:ℝ), ∃ᶠ d : ℕ in atTop,
    (d:ℝ)  ≤  M*d.totient ∧ δ*d.totient  ≤ 
      ((∑ a ∈ residues d, hits d (scale d) a * (hits d (scale d) a-1) : ℕ):ℝ)

/-- The third moment of the counts in coprime classes at phi(d) log d. -/
def H2 : Prop :=
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  ∀ M > (0:ℝ), ∃ V > (0:ℝ), ∀ᶠ d : ℕ in atTop,
    (d:ℝ)  ≤  M*d.totient →
      ((∑ a ∈ residues d, hits d (scale d) a ^ 3 : ℕ):ℝ)  ≤  V*d.totient

/-- Upper half of the prime number theorem at real cutoffs. -/
def H3 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1+ε)*(x/log x)

private lemma clip (K n : ℕ) : n*(n-1)*K  ≤  K^2*(n-1)+n^3 := by
  by_cases h : n ≤ K
  · have hh := Nat.mul_le_mul_right ((n-1)*K) h
    nlinarith only [hh, Nat.zero_le (n^3)]
  · have hh := Nat.mul_le_mul (Nat.sub_le n 1) (by omega : K ≤ n)
    nlinarith only [Nat.mul_le_mul_left n hh, Nat.zero_le (K^2*(n-1))]

theorem main : H1 → H2 → H3 → type_of% @Erdos971.erdos_971.variants.infinite_sequence := by
  rintro ⟨M,hM,δ,hδ,hpair⟩ hthird hprimeNumber
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  let extra := fun (d : ℕ) (y : ℝ) => ∑ a ∈ residues d, (hits d y a-1)
  have clip_sum (d K : ℕ) (y : ℝ) :
      (∑ a ∈ residues d, hits d y a * (hits d y a-1))*K  ≤ 
      K^2*extra d y + ∑ a ∈ residues d, hits d y a^3 := by
    simpa only [extra, sum_mul, mul_sum, sum_add_distrib] using
      sum_le_sum (s:=residues d) (fun a _ => clip K (hits d y a))

  have total (d : ℕ) (y : ℝ) :
      ∑ a ∈ residues d, hits d y a  ≤  Nat.primeCounting ⌊y⌋₊ := by
    dsimp only [hits]
    rw [sum_card_fiberwise_eq_card_filter, ← Nat.primesLE_card_eq_primeCounting]
    exact card_filter_le ..

  have missing (d : ℕ) (hd : 0<d) (y : ℝ) :
      d.totient + extra d y  ≤ 
        ((range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y).card +
        Nat.primeCounting ⌊y⌋₊ := by
    let miss := (residues d).filter fun a => hits d y a = 0
    have hs : miss ⊆ (range d).filter (fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y) := by
      intro a ha
      obtain ⟨ha,hz⟩ := mem_filter.mp ha
      obtain ⟨ha,hc⟩ := mem_filter.mp ha
      refine mem_filter.mpr ⟨ha,hc,?_⟩
      by_contra! h
      obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hd.ne' hc
      have hmem := Nat.sInf_mem (show Set.Nonempty {p : ℕ | p.Prime ∧ p ≡ a [MOD d]} from ⟨p,hp,he⟩)
      change (leastCongruentPrime a d).Prime ∧ leastCongruentPrime a d ≡ a [MOD d] at hmem
      have hmod := hmem.2
      change leastCongruentPrime a d % d = a%d at hmod
      rw [Nat.mod_eq_of_lt (mem_range.mp ha)] at hmod
      have hpos : 0<hits d y a := card_pos.mpr ⟨_,mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor h,hmem.1⟩,hmod⟩⟩
      omega
    have he : d.totient = (residues d).card := by simp [Nat.totient_eq_card_coprime,residues,Nat.coprime_comm]
    have hsum : (residues d).card + extra d y = miss.card + ∑ a ∈ residues d, hits d y a := by
      dsimp only [extra]
      rw [card_eq_sum_ones (residues d), ←sum_add_distrib]
      change _ = ((residues d).filter _).card + _
      rw [card_filter, ←sum_add_distrib]
      apply sum_congr rfl
      intro a _
      split_ifs <;> omega
    rw [he,hsum]
    exact Nat.add_le_add (card_le_card hs) (total ..)

  have extra_mono (d : ℕ) {x y : ℝ} (h : x ≤ y) : extra d x  ≤  extra d y := by
    apply sum_le_sum
    intro a _
    apply Nat.sub_le_sub_right
    apply card_le_card
    intro p hp
    obtain ⟨hm,he⟩ := mem_filter.mp hp
    obtain ⟨hl,hp'⟩ := Nat.mem_primesLE.mp hm
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hl.trans (Nat.floor_mono h),hp'⟩,he⟩


  obtain ⟨V,hV,h3⟩ := hthird M hM
  let K := ⌈2*V/δ⌉₊ + 1
  have hK : (0:ℝ)<K := by dsimp [K]; positivity
  have hKV : 2*V  ≤  δ*K := by
    have h := Nat.le_ceil (2*V/δ)
    have hh := (div_le_iff₀ hδ).mp h
    dsimp [K]; push_cast; nlinarith
  let c := min (1/2:ℝ) (δ/(8*K))
  have hc : 0<c := lt_min (by norm_num) (by positivity)
  have hcK : 8*c*K ≤ δ := by
    have h := (le_div_iff₀ (by positivity : 0<(8:ℝ)*K)).mp (min_le_right _ _ : c  ≤  δ/(8*K))
    linarith
  refine ⟨c,hc,c,hc,Nat.frequently_atTop_iff_infinite.mp ?_⟩
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (hprimeNumber c hc)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M)
  apply (hpair.and_eventually (h3.and (hlog.and ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Y)).and (eventually_ge_atTop 2))))).mono
  rintro d ⟨⟨hMd,hP⟩,hVd,hl,hYd,hd⟩
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr (show 0<d by omega)
  change M ≤ log (d:ℝ) at hl
  change Y ≤ (d:ℝ) at hYd
  let y := (1+c)*scale d
  have hlogpos : 0<log (d:ℝ) := by linarith
  have hs : (d:ℝ) ≤ scale d := hMd.trans (by dsimp [scale]; nlinarith [mul_le_mul_of_nonneg_left hl hφ.le])
  have hy : scale d ≤ y := by dsimp [y]; nlinarith [mul_nonneg hc.le (hd'.le.trans hs)]
  have hqy := hY y (hYd.trans (hs.trans hy))
  have hlogy : log (d:ℝ)  ≤  log y := log_le_log hd' (hs.trans hy)
  have hyφ : y/log y  ≤  (1+c)*d.totient := by
    apply (div_le_iff₀ (hlogpos.trans_le hlogy)).mpr
    calc y = ((1+c)*d.totient)*log d := by dsimp [y,scale]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlogy (by positivity)
  have hprime : (Nat.primeCounting ⌊y⌋₊ : ℝ)  ≤  (1+3*c)*d.totient := by
    have hc1 : c ≤ 1 := (min_le_left ..).trans (by norm_num : (1/2:ℝ) ≤ 1)
    refine hqy.trans ((mul_le_mul_of_nonneg_left hyφ (by positivity)).trans ?_)
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hc.le) hφ.le]
  let A := extra d (scale d)
  have ht := hVd hMd
  have hu := clip_sum d K (scale d)
  have hr : ((∑ a ∈ residues d, hits d (scale d) a * (hits d (scale d) a-1) : ℕ):ℝ)*K  ≤ 
      (K:ℝ)^2*(A:ℝ) + ((∑ a ∈ residues d, hits d (scale d) a^3 : ℕ):ℝ) := by exact_mod_cast hu
  have hA : 4*c*d.totient  ≤  (A:ℝ) := by
    apply le_of_mul_le_mul_left (a:=(K:ℝ)^2) _ (by positivity)
    nlinarith only [hr,ht,mul_le_mul_of_nonneg_right hP hK.le,
      mul_le_mul_of_nonneg_right hKV hφ.le,
      mul_le_mul_of_nonneg_right hcK (mul_nonneg hK.le hφ.le)]
  let S := (range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y
  have hmis : (d.totient:ℝ)+(extra d y:ℕ)  ≤  (S.card:ℝ)+Nat.primeCounting ⌊y⌋₊ := by
    exact_mod_cast missing d (by omega) y
  have hmono : (A:ℝ)  ≤  extra d y := by exact_mod_cast extra_mono d hy
  rw [Nat.Iio_eq_range]
  change c*d.totient  ≤  ((range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ) > (1+c)*d.totient*log d).card
  have he : (1+c)*d.totient*log d=y := by dsimp [y,scale]; ring
  rw [he]
  change c*d.totient  ≤  (S.card:ℝ)
  linarith

end OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1

