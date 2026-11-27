import OMAReductions.R_Erdos318_erdos_318_parts_ii_R1

-- Step Erdos318.erdos_318.parts.ii.R1.H1: hypothesis H1 of reduction Erdos318.erdos_318.parts.ii.R1
-- Credit: @iLc0

/-!
# Erdős 318 (ii), étape R1.H1 : le théorème « circle » de Larsen pour `D = Z \ E`

Pour `q = w(T) − w(S)` et `α = w(D)/q ∈ [1,01 ; 100]`, on compte les parties `D' ⊆ D` de somme
`≡ q (mod 1)`, pondérées par `(α − 1)^|D \ D'|`, par orthogonalité sur `ℤ/m` (`m = ppcm Z`) :
`F_α = (1/m) ∑_{h<m} e(−hq) ∏_{d ∈ D} (α − 1 + e(h/d))`, où `e(x) = exp(2πix)`. Le terme `h = 0`
vaut `α^|D|`. Tout est prouvé dans ce fichier :
* l'identité d'orthogonalité (`OMA.E318H1F.fourier_holds`) ;
* la taille `2·ppcm(Z) < 1,01^|D|` (`OMA.E318H1T.taille_holds`) ;
* les arcs majeurs : pour `0 < h`, `h⁵ ≤ N⁸`, le terme de `h` a une partie réelle `≥ 0`
  (`OMA.E318H1A.arcs_majeurs_holds`) ;
* les arcs mineurs, en trois plages de `h* = min(h, m − h)`, chacune bornant la somme des modules
  des produits :
  - (a) `2h* ≤ N²`, borne `α^|D|/8` (`OMA.E318H1Ma.plage_a_holds` ; facteurs `d = p²`, `p` premier
    de `]N, 8N]`, borne de Tchebychev de Mathlib) ;
  - (b) `N² < 2h*` et `h* ≤ N³⁶`, borne `α^|D|/8` (`OMA.E318H1Mb.plage_b_holds`, énoncé `H1` ;
    `p` premier de `]y, 8y]` avec `y = ⌊√(2h*)⌋`) ;
  - (c) `h* > N³⁶`, borne `α^|D|/4` (`OMA.E318H1Mc.plage_c_holds`, énoncé `H2` ; structure des `Q_i`
    de Larsen, échelles `2^j·N`) ;
* l'assemblage (`OMA.E318H1R.circle_core`, `minor_split`, `main`) : par la symétrie `h ↦ m − h`,
  `Re ∑ ≥ α^|D|/2` dès que les arcs mineurs pèsent au plus `α^|D|/2`, donc au moins deux parties `D'`.
-/

namespace OMA.E318H1R

open Finset

def H1 : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀,
  let B : Finset ℕ := ((range (N * 2 ^ N)).filter
    (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
  let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
  let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
  let E : Finset ℕ := B.filter (· < N ^ 4)
  let m : ℕ := Z.lcm id
  ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
    ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
        (N ^ 2 : ℕ) < (2 * h : ℕ) ∧ (N ^ 2 : ℕ) < (2 * (m - h) : ℕ) ∧
        ((h : ℕ) ≤ (N ^ 36 : ℕ) ∨ (m - h : ℕ) ≤ (N ^ 36 : ℕ))),
      ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
      α ^ (Z \ E).card / 8

def H2 : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀,
  let B : Finset ℕ := ((range (N * 2 ^ N)).filter
    (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
  let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
  let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
  let E : Finset ℕ := B.filter (· < N ^ 4)
  let m : ℕ := Z.lcm id
  ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
    ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
        (N ^ 2 : ℕ) < (2 * h : ℕ) ∧ (N ^ 2 : ℕ) < (2 * (m - h) : ℕ) ∧
        (N ^ 36 : ℕ) < (h : ℕ) ∧ (N ^ 36 : ℕ) < (m - h : ℕ)),
      ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
      α ^ (Z \ E).card / 4

end OMA.E318H1R

namespace OMA.E318H1F

open Finset

lemma f_integral (t : Finset ℕ) (m : ℕ) (q : ℝ) (hm : 0 < m)
    (ht : ∀ d ∈ t, d ∣ m) (hq : ∃ j : ℤ, (m : ℝ) * q = j) :
    ∃ j : ℤ, (m : ℝ) * ((∑ d ∈ t, (1 : ℝ) / d) - q) = j := by
  obtain ⟨j, hj⟩ := hq
  refine ⟨(∑ d ∈ t, ((m / d : ℕ) : ℤ)) - j, ?_⟩
  simp only [Int.cast_sub, Int.cast_sum, Int.cast_natCast]
  rw [mul_sub, Finset.mul_sum, hj]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : 0 < d := Nat.pos_of_dvd_of_pos (ht d hd) hm
  rw [Nat.cast_div (ht d hd) (by positivity : (d : ℝ) ≠ 0)]
  ring

open Classical in
lemma f_kernel (m : ℕ) (w q : ℝ) (hm : 0 < m)
    (hj : ∃ j : ℤ, (m : ℝ) * (w - q) = j) :
    (1 / (m : ℂ)) * ∑ h ∈ range m,
        Complex.exp ((h : ℂ) * (((w : ℂ) - q) * (2 * Real.pi * Complex.I))) =
      if ∃ k : ℤ, w = q + k then 1 else 0 := by
  classical
  let c : ℂ := 2 * Real.pi * Complex.I
  let z := Complex.exp (((w : ℂ) - q) * c)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hz : z = 1 ↔ ∃ k : ℤ, w = q + k := by
    rw [show z = _ from rfl, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have he : (w : ℂ) - q = (k : ℂ) := mul_right_cancel₀ hc hk
      have he' : w - q = (k : ℝ) := by exact_mod_cast he
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      simp [c]
  obtain ⟨j, hj⟩ := hj
  have hzpow : z ^ m = 1 := by
    rw [show z = _ from rfl, ← Complex.exp_nat_mul, ← mul_assoc]
    have he : (m : ℂ) * ((w : ℂ) - q) = j := by exact_mod_cast hj
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I j
  change (1 / (m : ℂ)) * (∑ h ∈ range m, Complex.exp ((h : ℂ) * (((w : ℂ) - q) * c))) = _
  simp_rw [Complex.exp_nat_mul]
  change (1 / (m : ℂ)) * (∑ h ∈ range m, z ^ h) = _
  split_ifs with h
  · rw [hz.mpr h]
    simp [show (m : ℂ) ≠ 0 by exact_mod_cast hm.ne']
  · rw [geom_sum_eq (mt hz.mp h), hzpow]
    simp

lemma f_expand (D : Finset ℕ) (h : ℕ) (a q c : ℂ) :
    Complex.exp (-(c * (h * q))) * ∏ d ∈ D, (a + Complex.exp (c * (h / (d : ℂ)))) =
      ∑ t ∈ D.powerset, a ^ (D.card - t.card) *
        Complex.exp ((h : ℂ) * (((((∑ d ∈ t, (1 : ℝ) / d) : ℝ) : ℂ) - q) * c)) := by
  classical
  have hp := Finset.prod_add (fun d : ℕ => Complex.exp (c * (h / (d : ℂ)))) (fun _ => a) D
  simp only [add_comm a _, hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht),
    ← Complex.exp_sum, ← mul_assoc, ← Complex.exp_add, mul_comm (a ^ _)]
  congr 2
  have hs : ∑ d ∈ t, c * (h / (d : ℂ)) = c * (h * (((∑ d ∈ t, (1 : ℝ) / d) : ℝ) : ℂ)) := by
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hs]
  ring

open Classical in
theorem fourier_holds :
    ∀ (D : Finset ℕ) (m : ℕ) (q a : ℝ), 0 < m → (∀ d ∈ D, d ∣ m) →
        (∃ j : ℤ, (m : ℝ) * q = j) →
        ((∑ D' ∈ D.powerset.filter (fun D' : Finset ℕ => ∃ k : ℤ, ∑ d ∈ D', (1 : ℝ) / (d : ℝ) = q + k),
            a ^ (D.card - D'.card) : ℝ) : ℂ) =
          (1 / (m : ℂ)) * ∑ h ∈ range m, Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) *
            ∏ d ∈ D, ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ)))) := by
  classical
  intro D m q a hm hD hq
  symm
  conv_rhs => rw [Complex.ofReal_sum, Finset.sum_filter]
  simp_rw [f_expand]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hj := f_integral t m q hm (fun d hd => hD d (Finset.mem_powerset.mp ht hd)) hq
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (m : ℂ)), mul_assoc, f_kernel m _ q hm hj]
  split_ifs <;> simp

end OMA.E318H1F

namespace OMA.E318H1T

open Finset

lemma t_count (N : ℕ) (hN : 0 < N) : N - 1 ≤
    ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).card := by
  have ex (k : ℕ) : ∃ p : ℕ, p.Prime ∧ N * 2 ^ k < p ∧ p ≤ N * 2 ^ (k + 1) := by
    obtain ⟨p, hp, hl, hr⟩ := Nat.exists_prime_lt_and_le_two_mul (N * 2 ^ k) (by positivity)
    exact ⟨p, hp, hl, by simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hr⟩
  choose f hf hl hr using ex
  have inc : StrictMono f := strictMono_nat_of_lt_succ fun k => (hr k).trans_lt (hl (k + 1))
  have inc' : StrictMono (fun k : ℕ => N * 2 ^ k) := fun a b h =>
    Nat.mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) h) hN
  rw [← card_range (N - 1)]
  apply card_le_card_of_injOn f _ inc.injective.injOn
  intro k hk
  have hk' := mem_range.mp hk
  exact mem_filter.mpr ⟨mem_range.mpr ((hr k).trans_lt (inc' (by omega))), hf k,
    (show N ≤ N * 2 ^ k by simpa using inc'.monotone (Nat.zero_le k)).trans_lt (hl k)⟩

lemma t_sq_inj : Function.Injective (fun k : ℕ => k ^ 2) :=
  fun _ _ h => (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp h

lemma t_prod_sq (S : Finset ℕ) : (∏ q ∈ S.image (· ^ 2), q) = (∏ p ∈ S, p) ^ 2 := by
  rw [prod_image t_sq_inj.injOn, prod_pow]

lemma t_many (B P : Finset ℕ) (hB : 1 ∈ B) (hp : ∀ p ∈ P, Nat.Prime p) :
    2 ^ P.card ≤ ((B ×ˢ (P.image (· ^ 2)).powerset).image
      (fun x => x.1 * ∏ q ∈ x.2, q)).card := by
  rw [← card_powerset]
  apply card_le_card_of_injOn (fun s : Finset ℕ => (∏ p ∈ s, p) ^ 2)
  · intro s hs
    refine mem_image.mpr ⟨(1, s.image (· ^ 2)), mem_product.mpr ⟨hB, mem_powerset.mpr ?_⟩, ?_⟩
    · exact image_subset_image (mem_powerset.mp hs)
    · simp only [one_mul, t_prod_sq]
  · intro s hs t ht h
    have hs' := Nat.primeFactors_prod (fun p h => hp p (mem_powerset.mp hs h))
    have ht' := Nat.primeFactors_prod (fun p h => hp p (mem_powerset.mp ht h))
    exact hs'.symm.trans ((congrArg Nat.primeFactors (t_sq_inj h)).trans ht')

lemma t_smooth_dvd {n N M : ℕ} (hn : 0 < n) (hnM : n < M)
    (hs : ∀ p ∈ n.primeFactors, p ≤ N) :
    n ∣ ∏ p ∈ (range (N + 1)).filter Nat.Prime, p ^ Nat.log p M := by
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn.ne'
    _ ∣ ∏ p ∈ n.primeFactors, p ^ Nat.log p M := prod_dvd_prod_of_dvd _ _ fun p hp =>
      pow_dvd_pow p (Nat.le_log_of_pow_le (Nat.prime_of_mem_primeFactors hp).one_lt
        ((Nat.ordProj_le p hn.ne').trans hnM.le))
    _ ∣ _ := prod_dvd_prod_of_subset _ _ _ fun p hp => mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (hs p hp)), Nat.prime_of_mem_primeFactors hp⟩

lemma t_upper (M N : ℕ) (hM : 0 < M) (P B : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p ∧ p < M)
    (hb : ∀ b ∈ B, ∃ n : ℕ, 0 < n ∧ n < M ∧ (∀ p ∈ n.primeFactors, p ≤ N) ∧ n ^ 2 = b) :
    ((B ×ˢ (P.image (· ^ 2)).powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)).lcm id ≤
      M ^ (2 * (N + 1 + P.card)) := by
  let F := (range (N + 1)).filter Nat.Prime
  let K := ∏ p ∈ F, p ^ Nat.log p M
  have Kpos : 0 < K := prod_pos fun p h => pow_pos (mem_filter.mp h).2.pos _
  have hdiv : ((B ×ˢ (P.image (· ^ 2)).powerset).image
      (fun x => x.1 * ∏ q ∈ x.2, q)).lcm id ∣ K ^ 2 * (∏ q ∈ P.image (· ^ 2), q) := by
    apply Finset.lcm_dvd
    intro z hz
    obtain ⟨⟨b, s⟩, hbs, rfl⟩ := mem_image.mp hz
    obtain ⟨hb', hs⟩ := mem_product.mp hbs
    obtain ⟨n, hn, hnM, hns, rfl⟩ := hb b hb'
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (t_smooth_dvd hn hnM hns) 2)
      (prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hs))
  rw [t_prod_sq] at hdiv
  have ppos : 0 < ∏ p ∈ P, p := prod_pos fun p h => (hp p h).1
  have hK : K ≤ M ^ (N + 1) := by
    apply (prod_le_pow_card F _ M fun p _ => Nat.pow_log_le_self p hM.ne').trans
    apply Nat.pow_le_pow_right hM
    simpa using (card_le_card (filter_subset Nat.Prime (range (N + 1))))
  have hP := prod_le_pow_card P (fun p => p) M fun p h => (hp p h).2.le
  calc
    _ ≤ K ^ 2 * (∏ p ∈ P, p) ^ 2 := Nat.le_of_dvd (by positivity) hdiv
    _ ≤ (M ^ (N + 1)) ^ 2 * (M ^ P.card) ^ 2 := by gcongr
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

lemma t_growth (k : ℕ) (hk : 64 ≤ k) : 10000 * (k + 2) ^ 4 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_succ]
    apply lt_of_le_of_lt _ (Nat.mul_lt_mul_of_pos_right ih (by decide : 0 < 2))
    nlinarith only [Nat.zero_le j, Nat.zero_le (j ^ 2), Nat.zero_le (j ^ 3), Nat.zero_le (j ^ 4)]

theorem taille_holds :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let B : Finset ℕ := ((range (N * 2 ^ N)).filter
        (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
      let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
      let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
      let E : Finset ℕ := B.filter (· < N ^ 4)
      2 * ((Z.lcm id : ℕ) : ℝ) < (101 / 100 : ℝ) ^ (Z \ E).card := by
  refine ⟨65, fun N hN => ?_⟩
  let M := N * 2 ^ N
  let P := (range M).filter (fun p => p.Prime ∧ N < p)
  let B := ((range M).filter (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
  let Z := (B ×ˢ (P.image (· ^ 2)).powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
  let E := B.filter (· < N ^ 4)
  change 2 * ((Z.lcm id : ℕ) : ℝ) < (101 / 100 : ℝ) ^ (Z \ E).card
  have hN' : 1 < N := by omega
  have hM : 1 < M := lt_of_lt_of_le hN' (Nat.le_mul_of_pos_right _ (by positivity))
  have hP (p : ℕ) (h : p ∈ P) : p.Prime ∧ p < M :=
    ⟨(mem_filter.mp h).2.1, mem_range.mp (mem_filter.mp h).1⟩
  have h1 : 1 ∈ B := mem_image.mpr ⟨1, mem_filter.mpr ⟨mem_range.mpr hM, by simp⟩, by simp⟩
  have hZ : 2 ^ P.card ≤ Z.card := t_many B P h1 fun p h => (hP p h).1
  have hE : E.card ≤ N ^ 4 := by
    rw [← card_range (N ^ 4)]
    exact card_le_card fun n hn => mem_range.mpr (mem_filter.mp hn).2
  have hD : 2 ^ P.card ≤ (Z \ E).card + N ^ 4 :=
    hZ.trans (card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hE _))
  have hk : N - 1 ≤ P.card := t_count N (by omega)
  have hA : Z.lcm id ≤ M ^ (2 * (N + 1 + P.card)) := by
    apply t_upper M N (by omega) P B (fun p h => ⟨(hP p h).1.pos, (hP p h).2⟩)
    intro b hb
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
    exact ⟨n, (mem_filter.mp hn).2.1, mem_range.mp (mem_filter.mp hn).1, (mem_filter.mp hn).2.2, rfl⟩
  have hM' : M ≤ 2 ^ (2 * N) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul_right _ N.lt_two_pow_self.le
  let A := (2 * N) * (2 * (N + 1 + P.card))
  have hL : Z.lcm id ≤ 2 ^ A :=
    (hA.trans (Nat.pow_le_pow_left hM' _)).trans_eq (pow_mul _ _ _).symm
  have hG := t_growth P.card (by omega)
  have hA' : 100 * (A + 1) + N ^ 4 < 2 ^ P.card := by
    apply lt_of_le_of_lt _ hG
    have hNP : N ≤ P.card + 1 := by omega
    dsimp only [A]
    calc
      _ ≤ 100 * ((2 * (P.card + 1)) * (2 * (P.card + 1 + 1 + P.card)) + 1) + (P.card + 1) ^ 4 := by gcongr
      _ ≤ _ := by nlinarith only [Nat.zero_le P.card, Nat.zero_le (P.card ^ 2),
        Nat.zero_le (P.card ^ 3), Nat.zero_le (P.card ^ 4)]
  have hBern : (2 : ℝ) ≤ (101 / 100 : ℝ) ^ 100 := by norm_num
  calc
    2 * ((Z.lcm id : ℕ) : ℝ) ≤ 2 ^ (A + 1) := by
      rw [pow_succ, mul_comm]; gcongr; exact_mod_cast hL
    _ ≤ ((101 / 100 : ℝ) ^ 100) ^ (A + 1) := by gcongr
    _ = (101 / 100 : ℝ) ^ (100 * (A + 1)) := (pow_mul _ _ _).symm
    _ < _ := pow_lt_pow_right₀ (by norm_num) (by omega)

end OMA.E318H1T

namespace OMA.E318H1A

open Finset

/-- Structure de `Z` et de `E`. -/
theorem a_Zstruct (N : ℕ) (hN : 2 ≤ N) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) :
    (∀ z ∈ Z, IsSquare z ∧ 0 < z) ∧ E ⊆ Z ∧ 1 ∈ E ∧
      (∀ e ∈ E, e = 1 ∨ ∃ d : ℕ, 2 ≤ d ∧ d + 1 ≤ N ^ 2 ∧ e = d ^ 2) ∧
      (∀ d ∈ Z \ E, N ^ 2 < d) ∧ (Z \ E).Nonempty ∧
      (∀ a : ℕ, 2 ≤ a → a ≤ N → a ^ 2 ∈ Z) := by
  classical
  have hpos : 0 < N := by omega
  have hbound : N ^ 2 < N * 2 ^ N := by
    simpa only [sq] using Nat.mul_lt_mul_of_pos_left
      (show N < 2 ^ N from Nat.lt_two_pow_self) hpos
  have hNsq : N < N ^ 2 := by nlinarith only [hN]
  have hNfour : N ^ 2 < N ^ 4 := by
    calc
      N ^ 2 < (N ^ 2) ^ 2 := Nat.pow_lt_pow_left hNsq (by decide)
      _ = N ^ 4 := by ring
  have hBin {b : ℕ} : b ∈ B ↔ ∃ n : ℕ, n < N * 2 ^ N ∧ 0 < n ∧
      (∀ p ∈ n.primeFactors, p ≤ N) ∧ n ^ 2 = b := by
    rw [hB]
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨n, ⟨hr, hn, hp⟩, heq⟩
      exact ⟨n, hr, hn, hp, heq⟩
    · rintro ⟨n, hr, hn, hp, heq⟩
      exact ⟨n, ⟨hr, hn, hp⟩, heq⟩
  have hQinfo {q : ℕ} (hq : q ∈ Q) : IsSquare q ∧ N ^ 2 < q := by
    rw [hQ, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨⟨p, sq p⟩, Nat.pow_lt_pow_left (mem_filter.mp hp).2.2 (by decide)⟩
  have hZin {z : ℕ} : z ∈ Z ↔ ∃ b ∈ B, ∃ s ⊆ Q, b * ∏ q ∈ s, q = z := by
    rw [hZ, mem_image]
    constructor
    · rintro ⟨⟨b, s⟩, hbs, rfl⟩
      exact ⟨b, (mem_product.mp hbs).1, s, mem_powerset.mp (mem_product.mp hbs).2, rfl⟩
    · rintro ⟨b, hb, s, hs, rfl⟩
      exact ⟨(b, s), mem_product.mpr ⟨hb, mem_powerset.mpr hs⟩, rfl⟩
  have hBZ : B ⊆ Z := by
    intro b hb
    exact hZin.mpr ⟨b, hb, ∅, empty_subset _, by simp⟩
  have hEin {e : ℕ} : e ∈ E ↔ e ∈ B ∧ e < N ^ 4 := by
    rw [hE, mem_filter]
  have hsmall {a : ℕ} (ha : 0 < a) (haN : a ≤ N) : a ^ 2 ∈ B :=
    hBin.mpr ⟨a, haN.trans_lt (hNsq.trans hbound), ha,
      fun _ hp => (Nat.le_of_mem_primeFactors hp).trans haN, rfl⟩
  have hprod {s : Finset ℕ} (hs : s ⊆ Q) : 0 < ∏ q ∈ s, q :=
    Finset.prod_pos fun q hq => (Nat.zero_le _).trans_lt (hQinfo (hs hq)).2
  refine ⟨?_, fun e he => hBZ (hEin.mp he).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    exact ⟨(show IsSquare (n ^ 2) from ⟨n, sq n⟩).mul
      (Finset.isSquare_prod (fun q => q) fun q hq => (hQinfo (hs hq)).1),
      Nat.mul_pos (pow_pos hn _) (hprod hs)⟩
  · apply hEin.mpr
    exact ⟨by simpa using hsmall (a := 1) (by decide) (by omega), by omega⟩
  · intro e he
    obtain ⟨hb, hlt⟩ := hEin.mp he
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    by_cases h : n = 1
    · left
      simp [h]
    · right
      refine ⟨n, by omega, ?_, rfl⟩
      by_contra! hle
      have hge : N ^ 2 ≤ n := by omega
      have hsq : (N ^ 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
      nlinarith only [hsq, hlt]
  · intro d hd
    obtain ⟨hz, hne⟩ := mem_sdiff.mp hd
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · simp only [prod_empty, mul_one] at hne ⊢
      exact hNfour.trans_le (le_of_not_gt fun h => hne (hEin.mpr ⟨hb, h⟩))
    · obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
      have hdvd := Finset.dvd_prod_of_mem (fun t : ℕ => t) hq
      have hle := Nat.le_of_dvd (hprod hs) hdvd
      calc
        N ^ 2 < q := (hQinfo (hs hq)).2
        _ ≤ ∏ t ∈ s, t := hle
        _ ≤ n ^ 2 * ∏ t ∈ s, t := Nat.le_mul_of_pos_left _ (pow_pos hn _)
  · have hfour : N ^ 4 ∈ B := by
      refine hBin.mpr ⟨N ^ 2, hbound, pow_pos hpos _, ?_, by ring⟩
      intro p hp
      rw [Nat.primeFactors_pow N (by decide : 2 ≠ 0)] at hp
      exact Nat.le_of_mem_primeFactors hp
    exact ⟨N ^ 4, mem_sdiff.mpr ⟨hBZ hfour, fun he => (lt_irrefl _) (hEin.mp he).2⟩⟩
  · intro a ha haN
    exact hBZ (hsmall (by omega) haN)

theorem a_sum_squares_le (N : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, IsSquare d ∧ N ^ 2 < d) :
    ∑ d ∈ D, (1 : ℝ) / d ≤ 2 / (N + 1) := by
  classical
  set M := D.sup id + 1 with hM
  set R := (Ioo N M).filter (fun n => n ^ 2 ∈ D) with hR
  have hDR : D = R.image (· ^ 2) := by
    ext d
    constructor
    · intro hd
      obtain ⟨⟨r, hr⟩, hlt⟩ := hD d hd
      subst hr
      have hdle : r * r ≤ D.sup id := Finset.le_sup (f := id) hd
      have hNr : N < r := by
        by_contra h
        push Not at h
        have : r * r ≤ N * N := Nat.mul_le_mul h h
        nlinarith
      refine Finset.mem_image.2 ⟨r, Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hNr, ?_⟩, by rw [sq]; exact hd⟩, by rw [sq]⟩
      have : r ≤ r * r := Nat.le_mul_of_pos_left r (by omega)
      omega
    · intro hd
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hd
      exact (Finset.mem_filter.1 hr).2
  rw [hDR, Finset.sum_image (fun x _ y _ h => Nat.pow_left_injective (by norm_num) h)]
  have h1 : ∑ n ∈ R, (1 : ℝ) / ((n ^ 2 : ℕ) : ℝ) = ∑ n ∈ R, ((n : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    rw [one_div]
  have h2 : ∑ n ∈ R, ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ Ioo N M, ((n : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
  have h3 := sum_Ioo_inv_sq_le (α := ℝ) N M
  rw [h1]
  linarith

lemma a_abs_arg (z : ℂ) (hz : 0 < z.re) : |z.arg| ≤ |z.im / z.re| := by
  have hb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have ht := Real.le_tan (abs_nonneg z.arg) hb
  rw [← Complex.tan_arg]
  rcases le_or_gt 0 z.arg with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact ht.trans (le_abs_self _)
  · rw [abs_of_neg h, Real.tan_neg] at ht
    rw [abs_of_neg h]
    exact ht.trans (neg_le_abs _)

/-- Après rotation individuelle, les termes linéaires des deux sinus s'annulent. -/
lemma a_argument (a t : ℝ) (ha : 1 ≤ a) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    |(Complex.exp (((-(t / a) : ℝ) : ℂ) * Complex.I) *
      (((a - 1 : ℝ) : ℂ) + Complex.exp ((t : ℂ) * Complex.I))).arg| ≤ t ^ 3 := by
  have ha0 : 0 < a := by linarith
  let x := t / a
  let y := t - x
  have hx : 0 ≤ x := div_nonneg ht ha0.le
  have hxt : x ≤ t := div_le_self ht ha
  have hy : 0 ≤ y := sub_nonneg.mpr hxt
  have hyt : y ≤ t := sub_le_self _ hx
  have hcancel : (a - 1) * x = y := by dsimp [x,y]; field_simp [ha0.ne']
  let z : ℂ := ((a - 1 : ℝ) : ℂ) * Complex.exp (((-x : ℝ) : ℂ) * Complex.I) +
                Complex.exp ((y : ℂ) * Complex.I)
  have hrot : Complex.exp (((-x : ℝ) : ℂ) * Complex.I) *
      (((a - 1 : ℝ) : ℂ) + Complex.exp ((t : ℂ) * Complex.I)) = z := by
    dsimp only [z,y]
    rw [mul_add, ← Complex.exp_add, mul_comm _ ((↑(a - 1) : ℂ))]
    push_cast
    ring_nf
  change |(Complex.exp (((-x : ℝ) : ℂ) * Complex.I) * _).arg| ≤ _
  rw [hrot]
  have hcos (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ t) : 1 / 2 ≤ Real.cos s := by
    have hsq := pow_le_pow_left₀ hs (hs'.trans ht') 2
    linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hre : a / 2 ≤ z.re := by
    simp only [z, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    linarith [mul_le_mul_of_nonneg_left (hcos x hx hxt) (sub_nonneg.mpr ha), hcos y hy hyt]
  have hsin (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ t) : |s - Real.sin s| ≤ t ^ 3 / 6 := by
    have h := Real.abs_sub_sin_le s
    rw [abs_of_nonneg hs] at h
    exact h.trans (by gcongr)
  have him : |z.im| ≤ a * (t ^ 3 / 6) := by
    have heq : z.im = (a - 1) * (x - Real.sin x) - (y - Real.sin y) := by
      simp only [z, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      linarith only [hcancel]
    rw [heq]
    calc
      _ ≤ |(a - 1) * (x - Real.sin x)| + |y - Real.sin y| := abs_sub _ _
      _ ≤ (a - 1) * (t ^ 3 / 6) + t ^ 3 / 6 := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ha)]
        gcongr
        · exact hsin x hx hxt
        · exact hsin y hy hyt
      _ = _ := by ring
  have hz : 0 < z.re := by linarith
  apply (a_abs_arg z hz).trans
  rw [abs_div, abs_of_pos hz, div_le_iff₀ hz]
  have hm := mul_le_mul_of_nonneg_left hre (pow_nonneg ht 3)
  nlinarith only [him, hm, mul_nonneg ha0.le (pow_nonneg ht 3)]

lemma a_threshold (n h : ℝ) (hn : 1024 ^ 5 ≤ n) (hh : 0 ≤ h) (hp : h ^ 5 ≤ n ^ 8) :
    16 * h ≤ n ^ 2 ∧ 1024 * h ^ 3 ≤ n ^ 5 := by
  have hn0 : 0 ≤ n := by linarith
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 5) (by decide) (sq_nonneg _)
    calc
      _ = (16 : ℝ) ^ 5 * h ^ 5 := by ring
      _ ≤ 16 ^ 5 * n ^ 8 := by gcongr
      _ ≤ n ^ 2 * n ^ 8 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hn0 _)
        nlinarith only [hn, sq_nonneg (n - 1)]
      _ = _ := by ring
  · apply le_of_pow_le_pow_left₀ (n := 5) (by decide) (pow_nonneg hn0 _)
    calc
      _ = (1024 : ℝ) ^ 5 * (h ^ 5) ^ 3 := by ring
      _ ≤ n * (n ^ 8) ^ 3 := by gcongr
      _ = _ := by ring

/-- Petitesse uniforme des phases et borne sur la somme de leurs cubes. -/
lemma a_phases (N h : ℕ) (hn : (1024 : ℝ) ^ 5 ≤ N) (hp : h ^ 5 ≤ N ^ 8)
    (D : Finset ℕ) (hD : ∀ d ∈ D, IsSquare d ∧ N ^ 2 < d) :
    (∀ d ∈ D, 2 * Real.pi * h / d ≤ (1 / 2 : ℝ)) ∧
    (∑ d ∈ D, (2 * Real.pi * h / d) ^ 3) ≤ 1 := by
  have hn0 : (0 : ℝ) < N := by linarith
  have hh : (0 : ℝ) ≤ h := by positivity
  obtain ⟨hs, hb⟩ := a_threshold N h hn hh (by exact_mod_cast hp)
  have hnum : 2 * Real.pi * h ≤ 8 * (h : ℝ) := by
    gcongr
    linarith [Real.pi_lt_four]
  have hd2 (d : ℕ) (hd : d ∈ D) : (N : ℝ) ^ 2 ≤ d := by exact_mod_cast (hD d hd).2.le
  have hd0 (d : ℕ) (hd : d ∈ D) : (0 : ℝ) < d := (pow_pos hn0 2).trans_le (hd2 d hd)
  constructor
  · intro d hd
    rw [div_le_iff₀ (hd0 d hd)]
    linarith [hd2 d hd]
  · have hpoint (d : ℕ) (hd : d ∈ D) : (2 * Real.pi * h / d) ^ 3 ≤
        ((8 * (h : ℝ)) ^ 3 / (N : ℝ) ^ 4) * (1 / d) := by
      have hsquare : (N : ℝ) ^ 4 ≤ (d : ℝ) ^ 2 := by
        simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) (hd2 d hd) 2
      calc
        _ ≤ (8 * (h : ℝ) / d) ^ 3 := by gcongr
        _ = ((8 * (h : ℝ)) ^ 3 / (d : ℝ) ^ 2) * (1 / d) := by ring
        _ ≤ _ := by gcongr
    calc
      _ ≤ ∑ d ∈ D, ((8 * (h : ℝ)) ^ 3 / (N : ℝ) ^ 4) * (1 / d) := sum_le_sum hpoint
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ ((8 * (h : ℝ)) ^ 3 / (N : ℝ) ^ 4) * (2 / (N + 1)) := by
        gcongr
        exact a_sum_squares_le N D hD
      _ ≤ ((8 * (h : ℝ)) ^ 3 / (N : ℝ) ^ 4) * (2 / N) := by gcongr; linarith
      _ = 1024 * (h : ℝ) ^ 3 / (N : ℝ) ^ 5 := by ring
      _ ≤ 1 := (div_le_one (pow_pos hn0 _)).2 hb

lemma a_prod_re (D : Finset ℕ) (z : ℕ → ℂ) (hb : ∑ d ∈ D, |(z d).arg| ≤ 1) :
    0 ≤ (∏ d ∈ D, z d).re := by
  let s := ∑ d ∈ D, (z d).arg
  have hs : |s| ≤ 1 := (Finset.abs_sum_le_sum_abs ..).trans hb
  have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [(abs_le.mp hs).1, Real.pi_gt_three])
    (by linarith [(abs_le.mp hs).2, Real.pi_gt_three])
  have he : ∏ d ∈ D, z d = ((∏ d ∈ D, ‖z d‖ : ℝ) : ℂ) *
        Complex.exp ((s : ℂ) * Complex.I) := by
    simp only [s, Complex.ofReal_prod, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      ← Finset.prod_mul_distrib, Complex.norm_mul_exp_arg_mul_I]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) hcos

lemma a_major (D : Finset ℕ) (a : ℝ) (ha : 1 ≤ a) (h : ℕ)
    (hs : ∀ d ∈ D, 2 * Real.pi * h / d ≤ (1 / 2 : ℝ))
    (hc : (∑ d ∈ D, (2 * Real.pi * h / d) ^ 3) ≤ 1) :
    0 ≤ (Complex.exp (-(2 * Real.pi * Complex.I *
        ((h : ℂ) * (((∑ d ∈ D, (1 : ℝ) / d) / a : ℝ) : ℂ)))) *
      ∏ d ∈ D, (((a - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))).re := by
  let t (d : ℕ) : ℝ := 2 * Real.pi * h / d
  let z (d : ℕ) := Complex.exp (((-(t d / a) : ℝ) : ℂ) * Complex.I) *
      (((a - 1 : ℝ) : ℂ) + Complex.exp (((t d : ℝ) : ℂ) * Complex.I))
  have hb : ∑ d ∈ D, |(z d).arg| ≤ 1 := by
    apply le_trans _ hc
    apply sum_le_sum
    intro d hd
    exact a_argument a (t d) ha (by dsimp [t]; positivity) (hs d hd)
  have hphase : -(2 * Real.pi * Complex.I *
        ((h : ℂ) * (((∑ d ∈ D, (1 : ℝ) / d) / a : ℝ) : ℂ))) =
      ∑ d ∈ D, (((-(t d / a) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    simp only [t, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro d _
    ring
  have he (d : ℕ) : 2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ)) = (t d : ℂ) * Complex.I := by
    dsimp [t]; push_cast; ring
  rw [hphase, Complex.exp_sum, ← Finset.prod_mul_distrib]
  simpa only [he] using a_prod_re D z hb

theorem arcs_majeurs_holds :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let B : Finset ℕ := ((range (N * 2 ^ N)).filter
        (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
      let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
      let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
      let E : Finset ℕ := B.filter (· < N ^ 4)
      ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 → ∀ h : ℕ, 0 < h → h ^ 5 ≤ N ^ 8 →
        0 ≤ (Complex.exp (-(2 * Real.pi * Complex.I *
            ((h : ℂ) * (((∑ d ∈ Z \ E, (1 : ℝ) / d) / α : ℝ) : ℂ)))) *
          ∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))).re := by
  refine ⟨1024 ^ 5, ?_⟩
  intro N hN B Q Z E a ha _ h _ hp
  have hh := a_Zstruct N (by omega) B Q Z E rfl rfl rfl rfl
  have hD : ∀ d ∈ Z \ E, IsSquare d ∧ N ^ 2 < d := fun d hd =>
    ⟨(hh.1 d (mem_sdiff.mp hd).1).1, hh.2.2.2.2.1 d hd⟩
  obtain ⟨hs, hc⟩ := a_phases N h (by exact_mod_cast hN) hp _ hD
  exact a_major _ a (by linarith) h hs hc

end OMA.E318H1A

namespace OMA.E318H1Ma

open Finset

lemma ma_phase (h d : ℕ) : 2 * Real.pi * Complex.I * ((h : ℂ) / d) =
    ((2 * (Real.pi * ((h : ℝ) / d)) : ℝ) : ℂ) * Complex.I := by push_cast; ring

lemma ma_sq (a x : ℝ) :
    ‖(a : ℂ) + Complex.exp (((2 * (Real.pi * x) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (a+1)^2 - 4*a*(Real.sin (Real.pi*x))^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, Complex.re_ofReal_mul,
    Complex.conj_re, Complex.exp_ofReal_mul_I_re, Real.cos_two_mul_eq_one_sub]
  ring

lemma ma_factor (α : ℝ) (h d : ℕ) (hα : 1 ≤ α) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / d))‖ ≤ α := by
  rw [ma_phase]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα),
    Complex.norm_exp_ofReal_mul_I]
  linarith
  
lemma ma_good (α c : ℝ) (h d : ℕ) (hα : 101/100 ≤ α) (hα' : α ≤ 100)
    (hc : 0 ≤ c) (hx : c ≤ (h : ℝ)/d) (hx' : (h : ℝ)/d ≤ 1/2) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ ≤
      α * Real.exp (-(c^2/25)) := by
  let x := (h : ℝ)/d
  change c ≤ x at hx
  change x ≤ 1/2 at hx'
  rw [ma_phase]
  have hs := Real.mul_le_sin (x := Real.pi*x) (mul_nonneg Real.pi_pos.le (hc.trans hx))
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hx') Real.pi_pos.le])
  rw [show 2 / Real.pi * (Real.pi * x) = 2*x by field_simp] at hs
  have hsq : (2*c)^2 ≤ Real.sin (Real.pi*x)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have ha : α^2 ≤ 200*(α-1) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hα') (sub_nonneg.mpr hα), hα]
  have hc2 : c^2 ≤ (1/2 : ℝ)^2 := pow_le_pow_left₀ hc (hx.trans hx') _
  have hα0 : 0 ≤ α := by linarith
  apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(c^2/25))) hα0)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hα0 (by linarith))).mp
  rw [ma_sq]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ α-1 by linarith),
    mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg c), sq_nonneg (α*c^2)]

lemma ma_symm (a : ℝ) (m h d : ℕ) (hh : h ≤ m) (hd : d ∣ m) :
    ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (((m-h : ℕ) : ℂ)/d))‖ =
      ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ := by
  by_cases hz : d = 0
  · simp [hz]
  rw [← Complex.norm_conj ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d)))]
  congr 1
  simp only [Nat.cast_sub hh, map_add, ← Complex.exp_conj, map_mul, map_div₀, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, map_natCast]
  congr 1
  have he : 2 * Real.pi * Complex.I * (((m : ℂ) - h)/d) =
      2 * Real.pi * (-Complex.I) * ((h : ℂ)/d) + (m / d : ℕ) * (2 * Real.pi * Complex.I) := by
    rw [Nat.cast_div hd (by exact_mod_cast hz : (d : ℂ) ≠ 0)]; ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma ma_prod (D G : Finset ℕ) (f : ℕ → ℂ) (α t : ℝ) (hα : 0 ≤ α) (hg : G ⊆ D)
    (hall : ∀ d ∈ D, ‖f d‖ ≤ α) (hgood : ∀ d ∈ G, ‖f d‖ ≤ α * Real.exp (-t)) :
    ‖∏ d ∈ D, f d‖ ≤ α ^ D.card * Real.exp (-(G.card*t)) := by
  rw [norm_prod, ← Finset.prod_sdiff (f := fun d => ‖f d‖) hg]
  calc
    _ ≤ (∏ _d ∈ D \ G, α) * (∏ _d ∈ G, (α * Real.exp (-t))) := by
      apply mul_le_mul
      · exact prod_le_prod (fun _ _ => norm_nonneg _) fun d hd => hall d (mem_sdiff.mp hd).1
      · exact prod_le_prod (fun _ _ => norm_nonneg _) hgood
      · exact prod_nonneg fun _ _ => norm_nonneg _
      · exact prod_nonneg fun _ _ => hα
    _ = _ := by
      rw [prod_const, prod_const, mul_pow, ← mul_assoc, ← pow_add,
        card_sdiff_of_subset hg, Nat.sub_add_cancel (card_le_card hg), ← Real.exp_nat_mul]
      congr 2; ring

lemma ma_count (S : Finset ℕ) (m K : ℕ)
    (hs : ∀ h ∈ S, h ≤ m ∧ (h ≤ K ∨ m-h ≤ K)) : S.card ≤ 2*K+2 := by
  let A := range (K+1)
  have hsub : S ⊆ A ∪ A.image (fun j => m-j) := by
    intro h hh
    obtain ⟨hm, hl | hr⟩ := hs h hh
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_image.mpr ⟨m-h, mem_range.mpr (by omega), by omega⟩)
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 : (A.image (fun j => m-j)).card ≤ A.card := card_image_le
  have h3 : A.card = K+1 := card_range _
  omega

lemma ma_decay (n j k : ℝ) (hn : (10^10 : ℝ)^20 ≤ n) (hj : 0 ≤ j)
    (hp : n^8 < j^5) (hk : n / (2*Real.log n) ≤ k) :
    Real.log (8*(2*n^2+2)) ≤ k * ((j/(64*n^2))^2/25) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : 0 < n := by linarith
  let r := n ^ (1/20 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hn0 _
  have he : r^20 = n := by
    rw [show r^20 = n^((1/20 : ℝ)*(20 : ℕ)) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hr0 : (10^10 : ℝ) ≤ r := by
    apply le_of_not_gt; intro h
    have ht := pow_lt_pow_left₀ h hr.le (by decide : 20 ≠ 0)
    linarith only [ht, he, hn]
  have hlog : Real.log n ≤ 20*r := by
    have hl := Real.log_le_rpow_div hn0.le (by norm_num : (0:ℝ) < 1/20)
    dsimp [r]; linarith
  have hj' : r^32 ≤ j := by
    apply le_of_not_gt; intro h
    have ht := pow_lt_pow_left₀ h hj (by decide : 5 ≠ 0)
    rw [← he] at hp
    nlinarith only [hp, ht]
  have hk0 := (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos hn1))).mp hk
  have hkpos : 0 ≤ k := (div_nonneg hn0.le (mul_nonneg (by norm_num) (Real.log_pos hn1).le)).trans hk
  have hk' : r^19 / 40 ≤ k := by
    have hu := mul_le_mul_of_nonneg_left hlog hkpos
    apply le_of_mul_le_mul_right (a := r) _ hr
    nlinarith only [hk0, hu, he]
  have hL : Real.log (8*(2*n^2+2)) ≤ 72*r := by
    calc
      _ ≤ Real.log (32*n^2) := Real.log_le_log (by positivity) (by nlinarith only [hn1, sq_nonneg (n-1)])
      _ = Real.log 32 + 2*Real.log n := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ _ := by linarith only [Real.log_le_self (by norm_num : (0:ℝ) ≤ 32), hlog, hr0]
  apply hL.trans
  calc
    72*r ≤ r^3/4096000 := by
      have hrr : (10^10 : ℝ)^2 ≤ r^2 := pow_le_pow_left₀ (by positivity) hr0 _
      nlinarith only [mul_nonneg (sub_nonneg.mpr hrr) hr.le, hr.le]
    _ = r^19 / 40 * ((r^32/(64*n^2))^2/25) := by rw [← he]; field_simp; ring
    _ ≤ _ := by gcongr

open Filter

lemma ma_primes : ∀ᶠ y : ℕ in atTop,
    (y : ℝ) / (2 * Real.log y) ≤ ((Nat.primesLE (8 * y) \ Nat.primesLE y).card : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1/10) (by norm_num))
  filter_upwards [he, eventually_ge_atTop 32] with y hπ hy
  rw [Nat.floor_natCast] at hπ
  have hy' : 32 ≤ (y : ℝ) := by exact_mod_cast hy
  have hpos : 0 < (y : ℝ) := by linarith
  have hlog := Real.log_pos (by linarith : 1 < (y : ℝ))
  have h8 := Real.log_pos (by linarith : 1 < 8 * (y : ℝ))
  have h8le : Real.log (8 * (y : ℝ)) ≤ 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 8) (by linarith : 8 ≤ (y:ℝ))]
  have hsmall : Real.log (8 * (y : ℝ) + 1) ≤ y := by
    calc
      _ ≤ Real.log (18 * ((y : ℝ) / 2)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 18 + Real.log ((y : ℝ) / 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ y := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (y:ℝ)/2),
                              Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18)]
  have hlow := Chebyshev.pi_ge (8*y)
  push_cast at hlow
  have hkey := (div_le_iff₀ h8).mp hlow
  have hprod := mul_le_mul_of_nonneg_left h8le
    (by positivity : 0 ≤ (Nat.primeCounting (8*y) : ℝ))
  have hlog2 : (5:ℝ)/8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 2*(y:ℝ) ≤ Nat.primeCounting (8*y) * Real.log y := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 hpos.le]
  have hU := (le_div_iff₀ hlog).mp hπ
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have huc : Real.log 4 + 1/10 ≤ 3/2 := by rw [hlog4]; linarith [Real.log_two_lt_d9]
  have hs : Nat.primesLE y ⊆ Nat.primesLE (8*y) := Nat.primesLE_mono (by omega)
  have hc := Finset.card_le_card hs
  simp only [Nat.primesLE_card_eq_primeCounting] at hc
  rw [Finset.card_sdiff_of_subset hs]
  simp only [Nat.primesLE_card_eq_primeCounting, Nat.cast_sub hc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right huc hpos.le]

lemma ma_square (N : ℕ) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) {p : ℕ} (hp : p.Prime)
    (hl : N < p) (hu : p < N * 2^N) : p^2 ∈ Z \ E := by
  classical
  have h1 : 1 ∈ B := by
    rw [hB]
    exact mem_image.mpr ⟨1, mem_filter.mpr ⟨mem_range.mpr (lt_trans hp.one_lt hu), by simp⟩, by simp⟩
  have hq : p^2 ∈ Q := by
    rw [hQ]
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr hu, hp, hl⟩, rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [hZ]
    exact mem_image.mpr ⟨(1,{p^2}), mem_product.mpr ⟨h1, mem_powerset.mpr (by simpa using hq)⟩, by simp⟩
  · rw [hE]
    intro he
    have hb := (mem_filter.mp he).1
    rw [hB] at hb
    obtain ⟨n,hn,hnp⟩ := mem_image.mp hb
    have heq : n = p := by simpa using hnp
    subst n
    exact hl.not_ge ((mem_filter.mp hn).2.2 p (by simp [hp.primeFactors]))

theorem plage_a_holds :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let B : Finset ℕ := ((range (N * 2 ^ N)).filter
        (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
      let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
      let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
      let E : Finset ℕ := B.filter (· < N ^ 4)
      let m : ℕ := Z.lcm id
      ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
        ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
            ((2 * h : ℕ) ≤ (N ^ 2 : ℕ) ∨ (2 * (m - h) : ℕ) ≤ (N ^ 2 : ℕ))),
          ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
          α ^ (Z \ E).card / 8 := by
  classical
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp ma_primes
  refine ⟨max Y ((10^10)^20), ?_⟩
  intro N hN B Q Z E m α hα hα'
  have hNbig := (max_le_iff.mp hN).2
  have hN9 : 9 ≤ N := le_trans (by norm_num) hNbig
  have hNpos : 0 < N := by omega
  have hα0 : 0 ≤ α := by linarith
  let P := Nat.primesLE (8*N) \ Nat.primesLE N
  let G := P.image (fun p => p^2)
  let D := Z \ E
  let S := (range m).filter (fun h => N^8 < h^5 ∧ N^8 < (m-h)^5 ∧ (2*h ≤ N^2 ∨ 2*(m-h) ≤ N^2))
  let F := fun (h d : ℕ) => ((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))
  change ∑ h ∈ S, ‖∏ d ∈ D, F h d‖ ≤ α^D.card/8
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ N < p ∧ p ≤ 8*N := by
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesLE h1
    exact ⟨hprime, lt_of_not_ge fun hn => h2 (Nat.mem_primesLE.mpr ⟨hn,hprime⟩), Nat.le_of_mem_primesLE h1⟩
  have hG : G ⊆ D := by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨h1,h2,h3⟩ := hP p hp
    apply ma_square N B Q Z E rfl rfl rfl rfl h1 h2
    calc
      p ≤ 8*N := h3
      _ = N*8 := Nat.mul_comm _ _
      _ < _ := Nat.mul_lt_mul_of_pos_left ((by omega : 8 < N).trans Nat.lt_two_pow_self) hNpos
  have hcard : G.card = P.card := Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)
  let b := 2*(N:ℝ)^2+2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbcard : (S.card : ℝ) ≤ b := by
    have hn := ma_count S m (N^2) (by
      intro h hh
      obtain ⟨hm, _, _, h1 | h2⟩ := Finset.mem_filter.mp hh
      · exact ⟨(mem_range.mp hm).le, Or.inl (by omega)⟩
      · exact ⟨(mem_range.mp hm).le, Or.inr (by omega)⟩)
    dsimp [b]; exact_mod_cast hn
  have hterm (h : ℕ) (hh : h ∈ S) : ‖∏ d ∈ D, F h d‖ ≤ α^D.card / (8*b) := by
    obtain ⟨hhm, h1, h2, h3⟩ := Finset.mem_filter.mp hh
    have hm := (mem_range.mp hhm).le
    let j := min h (m-h)
    have hj1 : N^8 < j^5 := by
      rcases le_total h (m-h) with u|u
      · simpa only [j, min_eq_left u] using h1
      · simpa only [j, min_eq_right u] using h2
    have hj2 : 2*j ≤ N^2 := by dsimp [j]; omega
    have hs (d : ℕ) (hd : d ∈ D) : ‖F h d‖ = ‖F j d‖ := by
      rcases le_total h (m-h) with u|u
      · simp [j, min_eq_left u]
      · rw [show j = m-h from min_eq_right u]
        exact (ma_symm _ _ _ _ hm (Finset.dvd_lcm (f := id) (Finset.mem_sdiff.mp hd).1)).symm
    let c := (j:ℝ)/(64*(N:ℝ)^2)
    have hj' : (2:ℝ)*j ≤ (N:ℝ)^2 := by exact_mod_cast hj2
    have hdamp := ma_prod D G (F h) α (c^2/25) hα0 hG (fun d _ => ma_factor α _ _ (by linarith)) (by
      intro d hd
      rw [hs d (hG hd)]
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hpp, hpN, hp8⟩ := hP p hp
      have hp' : 0 < (p:ℝ) := by exact_mod_cast hpp.pos
      have hpu : (p:ℝ)^2 ≤ (8*(N:ℝ))^2 := pow_le_pow_left₀ hp'.le (by exact_mod_cast hp8) _
      have hpl : (N:ℝ)^2 ≤ (p:ℝ)^2 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpN.le) _
      apply ma_good _ _ _ _ hα hα' (by dsimp [c]; positivity)
      · dsimp [c]; push_cast
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith only [hpu])
      · push_cast
        apply (div_le_iff₀ (by positivity)).mpr
        linarith only [hj', hpl])
    have hlog := ma_decay (N:ℝ) j P.card (by exact_mod_cast hNbig) (by positivity)
      (by exact_mod_cast hj1) (hY N (max_le_iff.mp hN).1)
    rw [hcard] at hdamp
    apply hdamp.trans
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα0 _)
    rw [← Real.exp_log (mul_pos (by norm_num : (0:ℝ) < 8) hb), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hlog)
  calc
    _ ≤ ∑ _h ∈ S, α^D.card / (8*b) := sum_le_sum hterm
    _ = (S.card : ℝ) * (α^D.card / (8*b)) := by simp
    _ ≤ b * (α^D.card / (8*b)) := mul_le_mul_of_nonneg_right hbcard (by positivity)
    _ = _ := by field_simp

end OMA.E318H1Ma

namespace OMA.E318H1R

open Finset

/-- Structure de `Z` et de `E`. -/
theorem Zstruct (N : ℕ) (hN : 2 ≤ N) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) :
    (∀ z ∈ Z, IsSquare z ∧ 0 < z) ∧ E ⊆ Z ∧ 1 ∈ E ∧
      (∀ e ∈ E, e = 1 ∨ ∃ d : ℕ, 2 ≤ d ∧ d + 1 ≤ N ^ 2 ∧ e = d ^ 2) ∧
      (∀ d ∈ Z \ E, N ^ 2 < d) ∧ (Z \ E).Nonempty ∧
      (∀ a : ℕ, 2 ≤ a → a ≤ N → a ^ 2 ∈ Z) := by
  classical
  have hpos : 0 < N := by omega
  have hbound : N ^ 2 < N * 2 ^ N := by
    simpa only [sq] using Nat.mul_lt_mul_of_pos_left
      (show N < 2 ^ N from Nat.lt_two_pow_self) hpos
  have hNsq : N < N ^ 2 := by nlinarith only [hN]
  have hNfour : N ^ 2 < N ^ 4 := by
    calc
      N ^ 2 < (N ^ 2) ^ 2 := Nat.pow_lt_pow_left hNsq (by decide)
      _ = N ^ 4 := by ring
  have hBin {b : ℕ} : b ∈ B ↔ ∃ n : ℕ, n < N * 2 ^ N ∧ 0 < n ∧
      (∀ p ∈ n.primeFactors, p ≤ N) ∧ n ^ 2 = b := by
    rw [hB]
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨n, ⟨hr, hn, hp⟩, heq⟩
      exact ⟨n, hr, hn, hp, heq⟩
    · rintro ⟨n, hr, hn, hp, heq⟩
      exact ⟨n, ⟨hr, hn, hp⟩, heq⟩
  have hQinfo {q : ℕ} (hq : q ∈ Q) : IsSquare q ∧ N ^ 2 < q := by
    rw [hQ, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨⟨p, sq p⟩, Nat.pow_lt_pow_left (mem_filter.mp hp).2.2 (by decide)⟩
  have hZin {z : ℕ} : z ∈ Z ↔ ∃ b ∈ B, ∃ s ⊆ Q, b * ∏ q ∈ s, q = z := by
    rw [hZ, mem_image]
    constructor
    · rintro ⟨⟨b, s⟩, hbs, rfl⟩
      exact ⟨b, (mem_product.mp hbs).1, s, mem_powerset.mp (mem_product.mp hbs).2, rfl⟩
    · rintro ⟨b, hb, s, hs, rfl⟩
      exact ⟨(b, s), mem_product.mpr ⟨hb, mem_powerset.mpr hs⟩, rfl⟩
  have hBZ : B ⊆ Z := by
    intro b hb
    exact hZin.mpr ⟨b, hb, ∅, empty_subset _, by simp⟩
  have hEin {e : ℕ} : e ∈ E ↔ e ∈ B ∧ e < N ^ 4 := by
    rw [hE, mem_filter]
  have hsmall {a : ℕ} (ha : 0 < a) (haN : a ≤ N) : a ^ 2 ∈ B :=
    hBin.mpr ⟨a, haN.trans_lt (hNsq.trans hbound), ha,
      fun _ hp => (Nat.le_of_mem_primeFactors hp).trans haN, rfl⟩
  have hprod {s : Finset ℕ} (hs : s ⊆ Q) : 0 < ∏ q ∈ s, q :=
    Finset.prod_pos fun q hq => (Nat.zero_le _).trans_lt (hQinfo (hs hq)).2
  refine ⟨?_, fun e he => hBZ (hEin.mp he).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    exact ⟨(show IsSquare (n ^ 2) from ⟨n, sq n⟩).mul
      (Finset.isSquare_prod (fun q => q) fun q hq => (hQinfo (hs hq)).1),
      Nat.mul_pos (pow_pos hn _) (hprod hs)⟩
  · apply hEin.mpr
    exact ⟨by simpa using hsmall (a := 1) (by decide) (by omega), by omega⟩
  · intro e he
    obtain ⟨hb, hlt⟩ := hEin.mp he
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    by_cases h : n = 1
    · left
      simp [h]
    · right
      refine ⟨n, by omega, ?_, rfl⟩
      by_contra! hle
      have hge : N ^ 2 ≤ n := by omega
      have hsq : (N ^ 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
      nlinarith only [hsq, hlt]
  · intro d hd
    obtain ⟨hz, hne⟩ := mem_sdiff.mp hd
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · simp only [prod_empty, mul_one] at hne ⊢
      exact hNfour.trans_le (le_of_not_gt fun h => hne (hEin.mpr ⟨hb, h⟩))
    · obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
      have hdvd := Finset.dvd_prod_of_mem (fun t : ℕ => t) hq
      have hle := Nat.le_of_dvd (hprod hs) hdvd
      calc
        N ^ 2 < q := (hQinfo (hs hq)).2
        _ ≤ ∏ t ∈ s, t := hle
        _ ≤ n ^ 2 * ∏ t ∈ s, t := Nat.le_mul_of_pos_left _ (pow_pos hn _)
  · have hfour : N ^ 4 ∈ B := by
      refine hBin.mpr ⟨N ^ 2, hbound, pow_pos hpos _, ?_, by ring⟩
      intro p hp
      rw [Nat.primeFactors_pow N (by decide : 2 ≠ 0)] at hp
      exact Nat.le_of_mem_primeFactors hp
    exact ⟨N ^ 4, mem_sdiff.mpr ⟨hBZ hfour, fun he => (lt_irrefl _) (hEin.mp he).2⟩⟩
  · intro a ha haN
    exact hBZ (hsmall (by omega) haN)

/-- `m · w(T)` est entier quand `T ⊆ Z`, `m = ppcm Z`. -/
theorem lcm_mul_sum_nat (Z T : Finset ℕ) (hT : T ⊆ Z) (hZ : ∀ z ∈ Z, 0 < z) :
    ∃ j : ℕ, ((Z.lcm id : ℕ) : ℝ) * ∑ t ∈ T, (1 : ℝ) / t = j := by
  refine ⟨∑ t ∈ T, Z.lcm id / t, ?_⟩
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hd : t ∣ Z.lcm id := Finset.dvd_lcm (f := id) (hT ht)
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (hZ t (hT ht)).ne'
  rw [Nat.cast_div hd ht', mul_one_div]

lemma m_exp_shift (x y : ℂ) (j : ℤ) (h : x = y + j * (2 * Real.pi * Complex.I)) :
    Complex.exp x = Complex.exp y := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Symétrie `h ↦ m − h` : le terme de `m − h` est le conjugué de celui de `h`. -/
theorem term_conj (D : Finset ℕ) (m : ℕ) (q a : ℝ) (hD : ∀ d ∈ D, d ∣ m) (hD0 : ∀ d ∈ D, 0 < d)
    (hq : ∃ j : ℤ, (m : ℝ) * q = j) (h : ℕ) (hh : h ≤ m) :
    Complex.exp (-(2 * Real.pi * Complex.I * (((m - h : ℕ) : ℂ) * (q : ℂ)))) *
        ∏ d ∈ D, ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (((m - h : ℕ) : ℂ) / (d : ℂ)))) =
      (starRingEnd ℂ) (Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) *
        ∏ d ∈ D, ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))) := by
  obtain ⟨j, hj⟩ := hq
  have hj' : (m : ℂ) * (q : ℂ) = j := by exact_mod_cast hj
  simp only [Nat.cast_sub hh, map_mul, map_prod, map_add, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat, map_div₀]
  congr 1
  · apply m_exp_shift _ _ (-j)
    push_cast
    rw [← hj']
    ring
  · apply Finset.prod_congr rfl
    intro d hd
    congr 1
    apply m_exp_shift _ _ (m / d : ℕ)
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (hD0 d hd).ne'
    rw [Int.cast_natCast, Nat.cast_div (hD d hd) hd']
    ring

/-- Comptage : la somme pondérée est au plus le nombre de parties fois `max(1, a)^|D|`. -/
theorem weighted_le_card (D : Finset ℕ) (P : Finset ℕ → Prop) [DecidablePred P] (a : ℝ)
    (ha : 0 ≤ a) :
    ∑ D' ∈ D.powerset.filter P, a ^ (D.card - D'.card) ≤
      ((D.powerset.filter P).card : ℝ) * (max 1 a) ^ D.card := by
  calc
    _ ≤ ∑ _ ∈ D.powerset.filter P, (max 1 a) ^ D.card := by
      apply Finset.sum_le_sum
      intro s _
      exact (pow_le_pow_left₀ ha (le_max_right 1 a) _).trans
        (pow_le_pow_right₀ (le_max_left 1 a) (Nat.sub_le _ _))
    _ = _ := by simp

/-- À `N` fixé : la partie réelle de la somme de Fourier vaut au moins `α^|D|/2`. -/
theorem re_sum_ge (N : ℕ) (D : Finset ℕ) (m : ℕ) (q α : ℝ) (hm : 0 < m)
    (hD : ∀ d ∈ D, d ∣ m) (hD0 : ∀ d ∈ D, 0 < d) (hq : ∃ j : ℤ, (m : ℝ) * q = j)
    (hmaj : ∀ h : ℕ, 0 < h → h ^ 5 ≤ N ^ 8 →
      0 ≤ (Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) *
        ∏ d ∈ D, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))).re)
    (hmin : ∑ h ∈ (range m).filter (fun h => N ^ 8 < h ^ 5 ∧ N ^ 8 < (m - h) ^ 5),
      ‖∏ d ∈ D, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
      α ^ D.card / 2) :
    α ^ D.card / 2 ≤ (∑ h ∈ range m, Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) *
      ∏ d ∈ D, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))).re := by
  classical
  let p := fun h : ℕ => N ^ 8 < h ^ 5 ∧ N ^ 8 < (m - h) ^ 5
  let g := fun h : ℕ => ∏ d ∈ D, (((α - 1 : ℝ) : ℂ) +
    Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))
  let t := fun h : ℕ => Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) * g h
  change α ^ D.card / 2 ≤ (∑ h ∈ range m, t h).re
  change ∑ h ∈ (range m).filter p, ‖g h‖ ≤ _ at hmin
  have ht0 : (t 0).re = α ^ D.card := by
    simp [t, g, ← Complex.ofReal_pow]
  have hmaj' (h : ℕ) (hh : h ∈ (range m).filter (fun j => ¬p j)) : 0 ≤ (t h).re := by
    obtain ⟨hhm, hp⟩ := mem_filter.mp hh
    have hlt := mem_range.mp hhm
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · rw [ht0]
      have hn := Finset.sum_nonneg (s := (range m).filter p) (fun h _ => norm_nonneg (g h))
      linarith
    by_cases hsmall : h ^ 5 ≤ N ^ 8
    · exact hmaj h hpos hsmall
    have hsmall' : (m - h) ^ 5 ≤ N ^ 8 := le_of_not_gt (fun hn => hp ⟨lt_of_not_ge hsmall, hn⟩)
    have heq : t (m - h) = (starRingEnd ℂ) (t h) := term_conj D m q (α - 1) hD hD0 hq h hlt.le
    have hh' : 0 ≤ (t (m - h)).re := hmaj _ (Nat.sub_pos_of_lt hlt) hsmall'
    simpa only [heq, Complex.conj_re] using hh'
  have h0 : 0 ∈ (range m).filter (fun j => ¬p j) := by simp [p, hm]
  have hbig := Finset.single_le_sum hmaj' h0
  rw [ht0] at hbig
  have hn (h : ℕ) : ‖t h‖ = ‖g h‖ := by
    simp [t, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hlow : ∑ h ∈ (range m).filter p, -‖g h‖ ≤ ∑ h ∈ (range m).filter p, (t h).re := by
    apply Finset.sum_le_sum
    intro h _
    rw [← hn]
    exact (abs_le.mp (Complex.abs_re_le_norm _)).1
  rw [Finset.sum_neg_distrib] at hlow
  rw [Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not (range m) p]
  linarith

open Classical in
/-- L'assemblage : orthogonalité, taille, arcs majeurs et arcs mineurs donnent deux parties
`D'` distinctes. -/
theorem circle_core :
    (∀ (D : Finset ℕ) (m : ℕ) (q a : ℝ), 0 < m → (∀ d ∈ D, d ∣ m) →
          (∃ j : ℤ, (m : ℝ) * q = j) →
          ((∑ D' ∈ D.powerset.filter (fun D' : Finset ℕ => ∃ k : ℤ, ∑ d ∈ D', (1 : ℝ) / (d : ℝ) = q + k),
              a ^ (D.card - D'.card) : ℝ) : ℂ) =
            (1 / (m : ℂ)) * ∑ h ∈ range m, Complex.exp (-(2 * Real.pi * Complex.I * ((h : ℂ) * (q : ℂ)))) *
              ∏ d ∈ D, ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))) →
    (∃ N₀ : ℕ, ∀ N ≥ N₀,
        let B : Finset ℕ := ((range (N * 2 ^ N)).filter
          (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
        let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
        let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
        let E : Finset ℕ := B.filter (· < N ^ 4)
        2 * ((Z.lcm id : ℕ) : ℝ) < (101 / 100 : ℝ) ^ (Z \ E).card) →
    (∃ N₀ : ℕ, ∀ N ≥ N₀,
        let B : Finset ℕ := ((range (N * 2 ^ N)).filter
          (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
        let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
        let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
        let E : Finset ℕ := B.filter (· < N ^ 4)
        ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 → ∀ h : ℕ, 0 < h → h ^ 5 ≤ N ^ 8 →
          0 ≤ (Complex.exp (-(2 * Real.pi * Complex.I *
              ((h : ℂ) * (((∑ d ∈ Z \ E, (1 : ℝ) / d) / α : ℝ) : ℂ)))) *
            ∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))).re) →
    (∃ N₀ : ℕ, ∀ N ≥ N₀,
        let B : Finset ℕ := ((range (N * 2 ^ N)).filter
          (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
        let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
        let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
        let E : Finset ℕ := B.filter (· < N ^ 4)
        let m : ℕ := Z.lcm id
        ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
          ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ)),
            ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
            α ^ (Z \ E).card / 2) →
    OMA.R_Erdos318_erdos_318_parts_ii_R1.H1 := by
  classical
  rintro hF ⟨N₂, hsize⟩ ⟨N₃, hmaj⟩ ⟨N₄, hmin⟩
  refine ⟨max (max N₂ N₃) (max N₄ 2), ?_⟩
  intro N hN B Q Z E T hT S hS h₁ h₂
  have hNs := max_le_iff.mp hN
  have hN₂ := (max_le_iff.mp hNs.1).1
  have hN₃ := (max_le_iff.mp hNs.1).2
  have hN₄ := (max_le_iff.mp hNs.2).1
  have hN' := (max_le_iff.mp hNs.2).2
  obtain ⟨hz, hEZ, _, _, _, hne, _⟩ := Zstruct N hN' B Q Z E rfl rfl rfl rfl
  let D := Z \ E
  let m := Z.lcm id
  let q := ∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s
  let w := ∑ d ∈ D, (1 : ℝ) / d
  have hZpos : ∀ z ∈ Z, 0 < z := fun z h => (hz z h).2
  have hDpos : ∀ d ∈ D, 0 < d := fun d h => hZpos d (mem_sdiff.mp h).1
  have hw : 0 < w := Finset.sum_pos (fun d hd => by
    have : 0 < (d : ℝ) := by exact_mod_cast hDpos d hd
    positivity) hne
  change 101 / 100 * q ≤ w at h₁
  change w ≤ 100 * q at h₂
  have hqpos : 0 < q := by linarith only [hw, h₂]
  let α := w / q
  have hlo : 101 / 100 ≤ α := (le_div_iff₀ hqpos).mpr h₁
  have hhi : α ≤ 100 := (div_le_iff₀ hqpos).mpr h₂
  have hq' : w / α = q := by dsimp only [α]; field_simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun he => by
    obtain ⟨z, hz', he'⟩ := Finset.lcm_eq_zero_iff.mp he
    exact (hZpos z hz').ne' he')
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hdvd : ∀ d ∈ D, d ∣ m := fun d h => Finset.dvd_lcm (f := id) (mem_sdiff.mp h).1
  obtain ⟨t, ht⟩ := lcm_mul_sum_nat Z T hT hZpos
  obtain ⟨s, hs⟩ := lcm_mul_sum_nat Z S (hS.trans hEZ) hZpos
  have hmq : ∃ j : ℤ, (m : ℝ) * q = j := by
    refine ⟨(t : ℤ) - s, ?_⟩
    dsimp only [m, q]
    rw [mul_sub, ht, hs]
    norm_cast
  have hbound := re_sum_ge N D m q α hmpos hdvd hDpos hmq (by
    rw [← hq']
    exact hmaj N hN₃ α hlo hhi) (hmin N hN₄ α hlo hhi)
  let P := fun A : Finset ℕ => ∃ k : ℤ, ∑ d ∈ A, (1 : ℝ) / d = q + k
  let F := ∑ A ∈ D.powerset.filter P, (α - 1) ^ (D.card - A.card)
  let b := max 1 (α - 1)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcount : F ≤ ((D.powerset.filter P).card : ℝ) * b ^ D.card :=
    weighted_le_card D P (α - 1) (by linarith only [hlo])
  have hFR := congrArg Complex.re (hF D m q (α - 1) hmpos hdvd hmq)
  rw [show 1 / (m : ℂ) = ((1 / (m : ℝ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.ofReal_re] at hFR
  have hmass : α ^ D.card / 2 ≤ (m : ℝ) * F := by
    calc
      _ ≤ _ := hbound
      _ = _ := by rw [show F = _ from hFR, ← mul_assoc, mul_one_div, div_self hm'.ne', one_mul]
  have hr : 101 / 100 * b ≤ α := by
    dsimp only [b]
    rcases le_total (α - 1) 1 with h | h
    · rw [max_eq_left h, mul_one]; exact hlo
    · rw [max_eq_right h]; linarith only [hhi]
  have hrpow := pow_le_pow_left₀ (by positivity : 0 ≤ 101 / 100 * b) hr D.card
  rw [mul_pow] at hrpow
  have hsiz : 2 * (m : ℝ) < (101 / 100 : ℝ) ^ D.card := hsize N hN₂
  have hstrict := mul_lt_mul_of_pos_right hsiz (pow_pos hb D.card)
  have hc : 1 < (D.powerset.filter P).card := by
    by_contra! h
    have h' : ((D.powerset.filter P).card : ℝ) ≤ 1 := by exact_mod_cast h
    have hle := hcount.trans (mul_le_mul_of_nonneg_right h' (pow_pos hb D.card).le)
    rw [one_mul] at hle
    have hle' := mul_le_mul_of_nonneg_left hle hm'.le
    linarith only [hmass, hrpow, hstrict, hle']
  obtain ⟨A, hA, C, hC, hAC⟩ := Finset.one_lt_card.mp hc
  exact ⟨A, C, mem_powerset.mp (mem_filter.mp hA).1, mem_powerset.mp (mem_filter.mp hC).1,
    hAC, (mem_filter.mp hA).2, (mem_filter.mp hC).2⟩

/-- Les trois plages partagent les arcs mineurs. -/
theorem minor_split_sum (m N : ℕ) (f : ℕ → ℝ) :
    ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ)), f h =
      ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
          ((2 * h : ℕ) ≤ (N ^ 2 : ℕ) ∨ (2 * (m - h) : ℕ) ≤ (N ^ 2 : ℕ))), f h +
      ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
          (N ^ 2 : ℕ) < (2 * h : ℕ) ∧ (N ^ 2 : ℕ) < (2 * (m - h) : ℕ) ∧
          ((h : ℕ) ≤ (N ^ 36 : ℕ) ∨ (m - h : ℕ) ≤ (N ^ 36 : ℕ))), f h +
      ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
          (N ^ 2 : ℕ) < (2 * h : ℕ) ∧ (N ^ 2 : ℕ) < (2 * (m - h) : ℕ) ∧
          (N ^ 36 : ℕ) < (h : ℕ) ∧ (N ^ 36 : ℕ) < (m - h : ℕ)), f h := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> first | (exfalso; omega) | simp

/-- Les trois plages donnent la borne `α^|D|/2` des arcs mineurs. -/
theorem minor_split : (∃ N₀ : ℕ, ∀ N ≥ N₀,
        let B : Finset ℕ := ((range (N * 2 ^ N)).filter
          (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
        let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
        let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
        let E : Finset ℕ := B.filter (· < N ^ 4)
        let m : ℕ := Z.lcm id
        ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
          ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ) ∧
              ((2 * h : ℕ) ≤ (N ^ 2 : ℕ) ∨ (2 * (m - h) : ℕ) ≤ (N ^ 2 : ℕ))),
            ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
            α ^ (Z \ E).card / 8) → H1 → H2 →
    (∃ N₀ : ℕ, ∀ N ≥ N₀,
        let B : Finset ℕ := ((range (N * 2 ^ N)).filter
          (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
        let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
        let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
        let E : Finset ℕ := B.filter (· < N ^ 4)
        let m : ℕ := Z.lcm id
        ∀ α : ℝ, 101 / 100 ≤ α → α ≤ 100 →
          ∑ h ∈ (range m).filter (fun h : ℕ => (N ^ 8 : ℕ) < (h ^ 5 : ℕ) ∧ (N ^ 8 : ℕ) < ((m - h) ^ 5 : ℕ)),
            ‖∏ d ∈ Z \ E, (((α - 1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / (d : ℂ))))‖ ≤
            α ^ (Z \ E).card / 2) := by
  rintro ⟨N₁, h1⟩ ⟨N₂, h2⟩ ⟨N₃, h3⟩
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have k1 := h1 N (le_trans (le_max_left _ _) hN)
  have k2 := h2 N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have k3 := h3 N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  dsimp only at k1 k2 k3 ⊢
  intro α hα1 hα2
  rw [minor_split_sum]
  linarith [k1 α hα1 hα2, k2 α hα1 hα2, k3 α hα1 hα2]

theorem main : H1 → H2 → OMA.R_Erdos318_erdos_318_parts_ii_R1.H1 :=
  fun h1 h2 => circle_core OMA.E318H1F.fourier_holds OMA.E318H1T.taille_holds
    OMA.E318H1A.arcs_majeurs_holds (minor_split OMA.E318H1Ma.plage_a_holds h1 h2)

end OMA.E318H1R

/-! Plage (b) des arcs mineurs : la plage `N² < 2h*`, `h* ≤ N³⁶` des arcs mineurs
(`h* = min(h, m − h)`), où la somme des modules des produits vaut au plus `α^|D|/8`.
Pour `y = ⌊√(2h*)⌋`, chaque premier `p` de `]y, 8y]` donne `d = p² ∈ D` avec `h*/p² ∈ [1/128, 1/2[`, donc un
facteur `‖α − 1 + e(h/p²)‖ ≤ α(1 − 1/409600)` ; Tchebychev (Mathlib) donne au moins `y/(2 log y)` tels
premiers, ce qui écrase le nombre `2N³⁶ + 2` de termes. -/

namespace OMA.E318H1Mb

open Finset

lemma mb_phase (h d : ℕ) : 2 * Real.pi * Complex.I * ((h : ℂ) / d) =
    ((2 * (Real.pi * ((h : ℝ) / d)) : ℝ) : ℂ) * Complex.I := by push_cast; ring

lemma mb_sq (a x : ℝ) :
    ‖(a : ℂ) + Complex.exp (((2 * (Real.pi * x) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (a+1)^2 - 4*a*(Real.sin (Real.pi*x))^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, Complex.re_ofReal_mul,
    Complex.conj_re, Complex.exp_ofReal_mul_I_re, Real.cos_two_mul_eq_one_sub]
  ring

lemma mb_factor (α : ℝ) (h d : ℕ) (hα : 1 ≤ α) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / d))‖ ≤ α := by
  rw [mb_phase]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα),
    Complex.norm_exp_ofReal_mul_I]
  linarith
  
lemma mb_good (α c : ℝ) (h d : ℕ) (hα : 101/100 ≤ α) (hα' : α ≤ 100)
    (hc : 0 ≤ c) (hx : c ≤ (h : ℝ)/d) (hx' : (h : ℝ)/d ≤ 1/2) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ ≤
      α * Real.exp (-(c^2/25)) := by
  let x := (h : ℝ)/d
  change c ≤ x at hx
  change x ≤ 1/2 at hx'
  rw [mb_phase]
  have hs := Real.mul_le_sin (x := Real.pi*x) (mul_nonneg Real.pi_pos.le (hc.trans hx))
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hx') Real.pi_pos.le])
  rw [show 2 / Real.pi * (Real.pi * x) = 2*x by field_simp] at hs
  have hsq : (2*c)^2 ≤ Real.sin (Real.pi*x)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have ha : α^2 ≤ 200*(α-1) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hα') (sub_nonneg.mpr hα), hα]
  have hc2 : c^2 ≤ (1/2 : ℝ)^2 := pow_le_pow_left₀ hc (hx.trans hx') _
  have hα0 : 0 ≤ α := by linarith
  apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(c^2/25))) hα0)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hα0 (by linarith))).mp
  rw [mb_sq]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ α-1 by linarith),
    mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg c), sq_nonneg (α*c^2)]

lemma mb_symm (a : ℝ) (m h d : ℕ) (hh : h ≤ m) (hd : d ∣ m) :
    ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (((m-h : ℕ) : ℂ)/d))‖ =
      ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ := by
  by_cases hz : d = 0
  · simp [hz]
  rw [← Complex.norm_conj ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d)))]
  congr 1
  simp only [Nat.cast_sub hh, map_add, ← Complex.exp_conj, map_mul, map_div₀, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, map_natCast]
  congr 1
  have he : 2 * Real.pi * Complex.I * (((m : ℂ) - h)/d) =
      2 * Real.pi * (-Complex.I) * ((h : ℂ)/d) + (m / d : ℕ) * (2 * Real.pi * Complex.I) := by
    rw [Nat.cast_div hd (by exact_mod_cast hz : (d : ℂ) ≠ 0)]; ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma mb_prod (D G : Finset ℕ) (f : ℕ → ℂ) (α t : ℝ) (hα : 0 ≤ α) (hg : G ⊆ D)
    (hall : ∀ d ∈ D, ‖f d‖ ≤ α) (hgood : ∀ d ∈ G, ‖f d‖ ≤ α * Real.exp (-t)) :
    ‖∏ d ∈ D, f d‖ ≤ α ^ D.card * Real.exp (-(G.card*t)) := by
  rw [norm_prod, ← Finset.prod_sdiff (f := fun d => ‖f d‖) hg]
  calc
    _ ≤ (∏ _d ∈ D \ G, α) * (∏ _d ∈ G, (α * Real.exp (-t))) := by
      apply mul_le_mul
      · exact prod_le_prod (fun _ _ => norm_nonneg _) fun d hd => hall d (mem_sdiff.mp hd).1
      · exact prod_le_prod (fun _ _ => norm_nonneg _) hgood
      · exact prod_nonneg fun _ _ => norm_nonneg _
      · exact prod_nonneg fun _ _ => hα
    _ = _ := by
      rw [prod_const, prod_const, mul_pow, ← mul_assoc, ← pow_add,
        card_sdiff_of_subset hg, Nat.sub_add_cancel (card_le_card hg), ← Real.exp_nat_mul]
      congr 2; ring

open Filter

lemma mb_primes : ∀ᶠ y : ℕ in atTop,
    (y : ℝ) / (2 * Real.log y) ≤ ((Nat.primesLE (8 * y) \ Nat.primesLE y).card : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1/10) (by norm_num))
  filter_upwards [he, eventually_ge_atTop 32] with y hπ hy
  rw [Nat.floor_natCast] at hπ
  have hy' : 32 ≤ (y : ℝ) := by exact_mod_cast hy
  have hpos : 0 < (y : ℝ) := by linarith
  have hlog := Real.log_pos (by linarith : 1 < (y : ℝ))
  have h8 := Real.log_pos (by linarith : 1 < 8 * (y : ℝ))
  have h8le : Real.log (8 * (y : ℝ)) ≤ 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 8) (by linarith : 8 ≤ (y:ℝ))]
  have hsmall : Real.log (8 * (y : ℝ) + 1) ≤ y := by
    calc
      _ ≤ Real.log (18 * ((y : ℝ) / 2)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 18 + Real.log ((y : ℝ) / 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ y := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (y:ℝ)/2),
                              Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18)]
  have hlow := Chebyshev.pi_ge (8*y)
  push_cast at hlow
  have hkey := (div_le_iff₀ h8).mp hlow
  have hprod := mul_le_mul_of_nonneg_left h8le
    (by positivity : 0 ≤ (Nat.primeCounting (8*y) : ℝ))
  have hlog2 : (5:ℝ)/8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 2*(y:ℝ) ≤ Nat.primeCounting (8*y) * Real.log y := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 hpos.le]
  have hU := (le_div_iff₀ hlog).mp hπ
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have huc : Real.log 4 + 1/10 ≤ 3/2 := by rw [hlog4]; linarith [Real.log_two_lt_d9]
  have hs : Nat.primesLE y ⊆ Nat.primesLE (8*y) := Nat.primesLE_mono (by omega)
  have hc := Finset.card_le_card hs
  simp only [Nat.primesLE_card_eq_primeCounting] at hc
  rw [Finset.card_sdiff_of_subset hs]
  simp only [Nat.primesLE_card_eq_primeCounting, Nat.cast_sub hc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right huc hpos.le]

lemma mb_square (N : ℕ) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) {p : ℕ} (hp : p.Prime)
    (hl : N < p) (hu : p < N * 2^N) : p^2 ∈ Z \ E := by
  classical
  have h1 : 1 ∈ B := by
    rw [hB]
    exact mem_image.mpr ⟨1, mem_filter.mpr ⟨mem_range.mpr (lt_trans hp.one_lt hu), by simp⟩, by simp⟩
  have hq : p^2 ∈ Q := by
    rw [hQ]
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr hu, hp, hl⟩, rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [hZ]
    exact mem_image.mpr ⟨(1,{p^2}), mem_product.mpr ⟨h1, mem_powerset.mpr (by simpa using hq)⟩, by simp⟩
  · rw [hE]
    intro he
    have hb := (mem_filter.mp he).1
    rw [hB] at hb
    obtain ⟨n,hn,hnp⟩ := mem_image.mp hb
    have heq : n = p := by simpa using hnp
    subst n
    exact hl.not_ge ((mem_filter.mp hn).2.2 p (by simp [hp.primeFactors]))

lemma mb_growth : ∀ᶠ y : ℕ in atTop, ∀ N : ℕ, N ≤ y →
    409600 * Real.log (8 * (2 * (N:ℝ)^36 + 2)) ≤ (y:ℝ) / (2 * Real.log y) := by
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1)).bound
      (by norm_num : (0:ℝ) < 1/40000000))
  filter_upwards [he, eventually_ge_atTop 32] with y hy hy32
  intro N hN
  have hy' : 32 ≤ (y:ℝ) := by exact_mod_cast hy32
  have hy0 : 0 < (y:ℝ) := by linarith
  have hy1 : 1 ≤ (y:ℝ) := by linarith
  have hlog := Real.log_pos (by linarith : 1 < (y:ℝ))
  simp only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (y:ℝ))),
    abs_of_nonneg hy0.le] at hy
  have hp : (N:ℝ)^36 ≤ (y:ℝ)^36 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN) _
  have hlog' : Real.log (8 * (2 * (N:ℝ)^36 + 2)) ≤ 37 * Real.log y := by
    calc
      _ ≤ Real.log ((y:ℝ)^37) := by
        apply Real.log_le_log (by positivity)
        rw [pow_succ]
        nlinarith [one_le_pow₀ hy1 (n := 36),
          mul_le_mul_of_nonneg_left hy' (by positivity : 0 ≤ (y:ℝ)^36)]
      _ = 37 * Real.log y := by rw [Real.log_pow]; norm_num
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlog' hlog.le]

lemma mb_power_growth : ∀ᶠ N : ℕ in atTop, 16*N^18 < N*2^N := by
  have he := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 18 (by norm_num : (1:ℝ)<2)).bound
    (by norm_num : (0:ℝ) < 1/32)
  filter_upwards [he, eventually_ge_atTop 1] with N h hN
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (N:ℝ)^18),
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)] at h
  have hn : 16*(N:ℝ)^18 < 2^N := by linarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
  exact lt_of_lt_of_le (by exact_mod_cast hn : 16*N^18 < 2^N) (Nat.le_mul_of_pos_left _ hN)

lemma mb_count {m k : ℕ} (S : Finset ℕ)
    (hs : ∀ h ∈ S, h ≤ m ∧ (h ≤ k ∨ m-h ≤ k)) : S.card ≤ 2*k+2 := by
  classical
  have hh : S ⊆ range (k+1) ∪ (range (k+1)).image (m-·) := by
    intro h hx
    obtain ⟨hm, h1 | h2⟩ := hs h hx
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_image.mpr ⟨m-h, mem_range.mpr (by omega), by omega⟩)
  calc
    _ ≤ _ := card_le_card hh
    _ ≤ _ := card_union_le _ _
    _ ≤ (range (k+1)).card + (range (k+1)).card := Nat.add_le_add_left card_image_le _
    _ = _ := by simp; omega

lemma mb_geometry {N j : ℕ} (hl : N^2 < 2*j) (hu : j ≤ N^36)
    (hg : 16*N^18 < N*2^N) :
    let y := Nat.sqrt (2*j)
    N ≤ y ∧ ∀ p ∈ Nat.primesLE (8*y) \ Nat.primesLE y,
      p.Prime ∧ N < p ∧ p < N*2^N ∧
      (1/128 : ℝ) ≤ (j:ℝ)/(p^2:ℕ) ∧ (j:ℝ)/(p^2:ℕ) ≤ 1/2 := by
  intro y
  have hy : N ≤ y := Nat.le_sqrt'.mpr hl.le
  refine ⟨hy, ?_⟩
  intro p hp
  obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpu,hpr⟩ := Nat.mem_primesLE.mp hm
  have hpl : y < p := lt_of_not_ge (fun H => hn (Nat.mem_primesLE.mpr ⟨H,hpr⟩))
  have hs : y^2 ≤ 2*j := Nat.sqrt_le' _
  have hsu : 2*j < p^2 := Nat.sqrt_lt'.mp hpl
  have hsy : y ≤ 2*N^18 := by
    apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp
    calc y^2 ≤ 2*N^36 := hs.trans (by omega)
         _ ≤ (2*N^18)^2 := by ring_nf; omega
  have hpp : p^2 ≤ 128*j := calc
    p^2 ≤ (8*y)^2 := Nat.pow_le_pow_left hpu _
    _ = 64*y^2 := by ring
    _ ≤ _ := by omega
  refine ⟨hpr, hy.trans_lt hpl, lt_of_le_of_lt (by omega : p ≤ 16*N^18) hg, ?_, ?_⟩
  · apply (le_div_iff₀ (by exact_mod_cast pow_pos hpr.pos 2 : (0:ℝ) < (p^2:ℕ))).mpr
    linarith [show ((p^2 : ℕ):ℝ) ≤ 128*(j:ℝ) by exact_mod_cast hpp]
  · apply (div_le_iff₀ (by exact_mod_cast pow_pos hpr.pos 2 : (0:ℝ) < (p^2:ℕ))).mpr
    linarith [show 2*(j:ℝ) < ((p^2:ℕ):ℝ) by exact_mod_cast hsu]

theorem plage_b_holds : OMA.E318H1R.H1 := by
  classical
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (mb_primes.and mb_growth)
  obtain ⟨K, hK⟩ := eventually_atTop.mp mb_power_growth
  refine ⟨max K Y, ?_⟩
  intro N hN B Q Z E m α hα hα'
  let D := Z \ E
  let f (h d : ℕ) := ((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h:ℂ) / d))
  let S := (range m).filter (fun h : ℕ => N^8 < h^5 ∧ N^8 < (m-h)^5 ∧
    N^2 < 2*h ∧ N^2 < 2*(m-h) ∧ (h ≤ N^36 ∨ m-h ≤ N^36))
  change ∑ h ∈ S, ‖∏ d ∈ D, f h d‖ ≤ α^D.card / 8
  let L : ℝ := 2*(N:ℝ)^36+2
  have hL : 0 < L := by dsimp [L]; positivity
  have ha : 0 ≤ α := by linarith
  have hcard : (S.card : ℝ) ≤ L := by
    have hc := mb_count (m := m) (k := N^36) S (by
      intro h hh
      obtain ⟨hm, _, _, _, _, hz⟩ := mem_filter.mp hh
      exact ⟨(mem_range.mp hm).le, hz⟩)
    dsimp [L]; exact_mod_cast hc
  have hbound (h : ℕ) (hh : h ∈ S) : ‖∏ d ∈ D, f h d‖ ≤ α^D.card / (8*L) := by
    obtain ⟨hhm, _, _, h1, h2, h3⟩ := mem_filter.mp hh
    have hm : h ≤ m := (mem_range.mp hhm).le
    obtain ⟨j, hj, hj', hje⟩ : ∃ j : ℕ, N^2 < 2*j ∧ j ≤ N^36 ∧
        ∀ d ∈ D, ‖f h d‖ = ‖f j d‖ := by
      rcases h3 with hl | hr
      · exact ⟨h,h1,hl,fun _ _ => rfl⟩
      · refine ⟨m-h,h2,hr,fun d hd => (mb_symm _ _ _ _ hm ?_).symm⟩
        exact dvd_lcm (f := id) (Finset.mem_sdiff.mp hd).1
    let y := Nat.sqrt (2*j)
    let P := Nat.primesLE (8*y) \ Nat.primesLE y
    let G := P.image (·^2)
    obtain ⟨hNy, hgeo⟩ := mb_geometry hj hj' (hK N ((le_max_left _ _).trans hN))
    have hy := hY y ((le_max_right _ _).trans (hN.trans hNy))
    have hPG : G.card = P.card := card_image_of_injective _ (fun a b hab => by simpa using hab)
    have hGD : G ⊆ D := by
      intro d hd
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hd
      obtain ⟨hp',hpN,hpu,_⟩ := hgeo p hp
      exact mb_square N B Q Z E rfl rfl rfl rfl hp' hpN hpu
    apply (mb_prod D G (f h) α ((1/128)^2/25) ha hGD
      (fun d _ => mb_factor _ _ _ (by linarith)) ?_).trans
    · have hk : 409600 * Real.log (8*L) ≤ (P.card:ℝ) := (hy.2 N hNy).trans hy.1
      have ht : -((G.card:ℝ) * ((1/128)^2/25)) ≤ -Real.log (8*L) := by
        rw [hPG]; linarith
      rw [div_eq_mul_inv (α^D.card) (8*L)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha _)
      simpa [Real.exp_neg, Real.exp_log (by positivity : 0 < 8*L)] using Real.exp_le_exp.mpr ht
    · intro d hd
      rw [hje d (hGD hd)]
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hd
      obtain ⟨_,_,_,hl,hu⟩ := hgeo p hp
      exact mb_good _ _ _ _ hα hα' (by norm_num) hl hu
  calc
    _ ≤ ∑ _h ∈ S, α^D.card / (8*L) := sum_le_sum hbound
    _ = (S.card:ℝ) * (α^D.card / (8*L)) := by simp
    _ ≤ L * (α^D.card / (8*L)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

end OMA.E318H1Mb

/-! Plage (c) des arcs mineurs : `min(h, m − h) > N³⁶`, borne `α^|D|/4` (cœur du th. 2 de Larsen),
par échelles `s_j = 2^j·N` et les diviseurs `Q_i` de `m`. -/

namespace OMA.E318H1Mc

open Finset

lemma mc_phase (h d : ℕ) : 2 * Real.pi * Complex.I * ((h : ℂ) / d) =
    ((2 * (Real.pi * ((h : ℝ) / d)) : ℝ) : ℂ) * Complex.I := by push_cast; ring

lemma mc_sq (a x : ℝ) :
    ‖(a : ℂ) + Complex.exp (((2 * (Real.pi * x) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (a+1)^2 - 4*a*(Real.sin (Real.pi*x))^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, Complex.re_ofReal_mul,
    Complex.conj_re, Complex.exp_ofReal_mul_I_re, Real.cos_two_mul_eq_one_sub]
  ring

lemma mc_factor (α : ℝ) (h d : ℕ) (hα : 1 ≤ α) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / d))‖ ≤ α := by
  rw [mc_phase]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα),
    Complex.norm_exp_ofReal_mul_I]
  linarith
  
lemma mc_good (α c : ℝ) (h d : ℕ) (hα : 101/100 ≤ α) (hα' : α ≤ 100)
    (hc : 0 ≤ c) (hx : c ≤ (h : ℝ)/d) (hx' : (h : ℝ)/d ≤ 1/2) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ ≤
      α * Real.exp (-(c^2/25)) := by
  let x := (h : ℝ)/d
  change c ≤ x at hx
  change x ≤ 1/2 at hx'
  rw [mc_phase]
  have hs := Real.mul_le_sin (x := Real.pi*x) (mul_nonneg Real.pi_pos.le (hc.trans hx))
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hx') Real.pi_pos.le])
  rw [show 2 / Real.pi * (Real.pi * x) = 2*x by field_simp] at hs
  have hsq : (2*c)^2 ≤ Real.sin (Real.pi*x)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have ha : α^2 ≤ 200*(α-1) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hα') (sub_nonneg.mpr hα), hα]
  have hc2 : c^2 ≤ (1/2 : ℝ)^2 := pow_le_pow_left₀ hc (hx.trans hx') _
  have hα0 : 0 ≤ α := by linarith
  apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(c^2/25))) hα0)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hα0 (by linarith))).mp
  rw [mc_sq]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ α-1 by linarith),
    mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg c), sq_nonneg (α*c^2)]

lemma mc_symm (a : ℝ) (m h d : ℕ) (hh : h ≤ m) (hd : d ∣ m) :
    ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (((m-h : ℕ) : ℂ)/d))‖ =
      ‖(a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ := by
  by_cases hz : d = 0
  · simp [hz]
  rw [← Complex.norm_conj ((a : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d)))]
  congr 1
  simp only [Nat.cast_sub hh, map_add, ← Complex.exp_conj, map_mul, map_div₀, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, map_natCast]
  congr 1
  have he : 2 * Real.pi * Complex.I * (((m : ℂ) - h)/d) =
      2 * Real.pi * (-Complex.I) * ((h : ℂ)/d) + (m / d : ℕ) * (2 * Real.pi * Complex.I) := by
    rw [Nat.cast_div hd (by exact_mod_cast hz : (d : ℂ) ≠ 0)]; ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma mc_prod (D G : Finset ℕ) (f : ℕ → ℂ) (α t : ℝ) (hα : 0 ≤ α) (hg : G ⊆ D)
    (hall : ∀ d ∈ D, ‖f d‖ ≤ α) (hgood : ∀ d ∈ G, ‖f d‖ ≤ α * Real.exp (-t)) :
    ‖∏ d ∈ D, f d‖ ≤ α ^ D.card * Real.exp (-(G.card*t)) := by
  rw [norm_prod, ← Finset.prod_sdiff (f := fun d => ‖f d‖) hg]
  calc
    _ ≤ (∏ _d ∈ D \ G, α) * (∏ _d ∈ G, (α * Real.exp (-t))) := by
      apply mul_le_mul
      · exact prod_le_prod (fun _ _ => norm_nonneg _) fun d hd => hall d (mem_sdiff.mp hd).1
      · exact prod_le_prod (fun _ _ => norm_nonneg _) hgood
      · exact prod_nonneg fun _ _ => norm_nonneg _
      · exact prod_nonneg fun _ _ => hα
    _ = _ := by
      rw [prod_const, prod_const, mul_pow, ← mul_assoc, ← pow_add,
        card_sdiff_of_subset hg, Nat.sub_add_cancel (card_le_card hg), ← Real.exp_nat_mul]
      congr 2; ring

open Filter

lemma mc_primes : ∀ᶠ y : ℕ in atTop,
    (y : ℝ) / (2 * Real.log y) ≤ ((Nat.primesLE (8 * y) \ Nat.primesLE y).card : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1/10) (by norm_num))
  filter_upwards [he, eventually_ge_atTop 32] with y hπ hy
  rw [Nat.floor_natCast] at hπ
  have hy' : 32 ≤ (y : ℝ) := by exact_mod_cast hy
  have hpos : 0 < (y : ℝ) := by linarith
  have hlog := Real.log_pos (by linarith : 1 < (y : ℝ))
  have h8 := Real.log_pos (by linarith : 1 < 8 * (y : ℝ))
  have h8le : Real.log (8 * (y : ℝ)) ≤ 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 8) (by linarith : 8 ≤ (y:ℝ))]
  have hsmall : Real.log (8 * (y : ℝ) + 1) ≤ y := by
    calc
      _ ≤ Real.log (18 * ((y : ℝ) / 2)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 18 + Real.log ((y : ℝ) / 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ y := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (y:ℝ)/2),
                              Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18)]
  have hlow := Chebyshev.pi_ge (8*y)
  push_cast at hlow
  have hkey := (div_le_iff₀ h8).mp hlow
  have hprod := mul_le_mul_of_nonneg_left h8le
    (by positivity : 0 ≤ (Nat.primeCounting (8*y) : ℝ))
  have hlog2 : (5:ℝ)/8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 2*(y:ℝ) ≤ Nat.primeCounting (8*y) * Real.log y := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 hpos.le]
  have hU := (le_div_iff₀ hlog).mp hπ
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have huc : Real.log 4 + 1/10 ≤ 3/2 := by rw [hlog4]; linarith [Real.log_two_lt_d9]
  have hs : Nat.primesLE y ⊆ Nat.primesLE (8*y) := Nat.primesLE_mono (by omega)
  have hc := Finset.card_le_card hs
  simp only [Nat.primesLE_card_eq_primeCounting] at hc
  rw [Finset.card_sdiff_of_subset hs]
  simp only [Nat.primesLE_card_eq_primeCounting, Nat.cast_sub hc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right huc hpos.le]

lemma mc_square (N : ℕ) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) {p : ℕ} (hp : p.Prime)
    (hl : N < p) (hu : p < N * 2^N) : p^2 ∈ Z \ E := by
  classical
  have h1 : 1 ∈ B := by
    rw [hB]
    exact mem_image.mpr ⟨1, mem_filter.mpr ⟨mem_range.mpr (lt_trans hp.one_lt hu), by simp⟩, by simp⟩
  have hq : p^2 ∈ Q := by
    rw [hQ]
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr hu, hp, hl⟩, rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [hZ]
    exact mem_image.mpr ⟨(1,{p^2}), mem_product.mpr ⟨h1, mem_powerset.mpr (by simpa using hq)⟩, by simp⟩
  · rw [hE]
    intro he
    have hb := (mem_filter.mp he).1
    rw [hB] at hb
    obtain ⟨n,hn,hnp⟩ := mem_image.mp hb
    have heq : n = p := by simpa using hnp
    subst n
    exact hl.not_ge ((mem_filter.mp hn).2.2 p (by simp [hp.primeFactors]))

lemma mc_count {m k : ℕ} (S : Finset ℕ)
    (hs : ∀ h ∈ S, h ≤ m ∧ (h ≤ k ∨ m-h ≤ k)) : S.card ≤ 2*k+2 := by
  classical
  have hh : S ⊆ range (k+1) ∪ (range (k+1)).image (m-·) := by
    intro h hx
    obtain ⟨hm, h1 | h2⟩ := hs h hx
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_image.mpr ⟨m-h, mem_range.mpr (by omega), by omega⟩)
  calc
    _ ≤ _ := card_le_card hh
    _ ≤ _ := card_union_le _ _
    _ ≤ (range (k+1)).card + (range (k+1)).card := Nat.add_le_add_left card_image_le _
    _ = _ := by simp; omega

/- ## Plage (c) : lemmes propres (plan : `h1/plan-plage-c.md`)

Échelle `s` : `P_s` = premiers de `]s, 8s]` (`Nat.primesLE (8 * s) \ Nat.primesLE s`), `n_s = |P_s|`,
`Q_s = P_s.image (· ^ 2) ⊆ Q`, `Y = s²⁰`, `c = 1/(64¹² s⁴)`. -/

/-- Facteur amorti : si `h` est loin (au moins `c·d`) de tout multiple de `d`, le facteur de `d`
vaut au plus `α·exp(−c²/25)`. On se ramène à `r = h % d` ou `d − r` (`mc_symm`, `mc_good`). -/
lemma mc_far (α c : ℝ) (h d : ℕ) (hα : 101/100 ≤ α) (hα' : α ≤ 100) (hd : 0 < d) (hc : 0 ≤ c)
    (hfar : ∀ k : ℕ, c * d ≤ |(h : ℝ) - k * d|) :
    ‖((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ)/d))‖ ≤
      α * Real.exp (-(c^2/25)) := by
  have hdiv : h = d * (h / d) + h % d := (Nat.div_add_mod h d).symm
  have hrd : h % d < d := Nat.mod_lt h hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) / d)) =
      Complex.exp (2 * Real.pi * Complex.I * (((h % d : ℕ) : ℂ) / d)) := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hhC : (h : ℂ) = d * ((h / d : ℕ) : ℂ) + ((h % d : ℕ) : ℂ) := by exact_mod_cast hdiv
    have : 2 * Real.pi * Complex.I * ((h : ℂ) / d) =
        2 * Real.pi * Complex.I * (((h % d : ℕ) : ℂ) / d) +
          ((h / d : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hhC]; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]
  have hhR : (h : ℝ) = d * ((h / d : ℕ) : ℝ) + ((h % d : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hk1 := hfar (h / d)
  have hk2 := hfar (h / d + 1)
  have hr1 : (h : ℝ) - ((h / d : ℕ) : ℝ) * d = ((h % d : ℕ) : ℝ) := by rw [hhR]; ring
  have hr2 : (h : ℝ) - ((h / d + 1 : ℕ) : ℝ) * d = ((h % d : ℕ) : ℝ) - d := by
    push_cast; rw [hhR]; ring
  have hrdR : ((h % d : ℕ) : ℝ) < d := by exact_mod_cast hrd
  rw [hr1, abs_of_nonneg (Nat.cast_nonneg _)] at hk1
  rw [hr2, abs_of_nonpos (by linarith)] at hk2
  rcases le_or_gt (2 * (h % d)) d with h2r | h2r
  · have h2rR : 2 * ((h % d : ℕ) : ℝ) ≤ d := by exact_mod_cast h2r
    apply mc_good α c (h % d) d hα hα' hc
    · rw [le_div_iff₀ hdR]; linarith
    · rw [div_le_iff₀ hdR]; linarith
  · have h2rR : (d : ℝ) < 2 * ((h % d : ℕ) : ℝ) := by exact_mod_cast h2r
    have hsym := mc_symm (α - 1) d (d - h % d) d (Nat.sub_le d _) (dvd_refl d)
    rw [Nat.sub_sub_self hrd.le] at hsym
    rw [hsym]
    apply mc_good α c (d - h % d) d hα hα' hc
    · rw [le_div_iff₀ hdR, Nat.cast_sub hrd.le]; linarith
    · rw [div_le_iff₀ hdR, Nat.cast_sub hrd.le]; linarith

/-- Deux parties de `Q` (carrés de premiers) de même produit sont égales. -/
lemma mc_inj (Q : Finset ℕ) (hQ : ∀ q ∈ Q, ∃ p, p.Prime ∧ q = p ^ 2) {T₁ T₂ : Finset ℕ}
    (h₁ : T₁ ⊆ Q) (h₂ : T₂ ⊆ Q) (he : ∏ q ∈ T₁, q = ∏ q ∈ T₂, q) : T₁ = T₂ := by
  classical
  have sub {U V : Finset ℕ} (hU : U ⊆ Q) (hV : V ⊆ Q)
      (heq : ∏ q ∈ U, q = ∏ q ∈ V, q) : U ⊆ V := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := hQ q (hU hq)
    have hd : p ∣ ∏ q ∈ V, q := heq ▸
      dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) (dvd_prod_of_mem id hq)
    obtain ⟨a, ha, hpa⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    obtain ⟨b, hb, rfl⟩ := hQ a (hV ha)
    have := (Nat.prime_dvd_prime_iff_eq hp hb).mp (hp.dvd_of_dvd_pow hpa)
    simpa [this] using ha
  exact Subset.antisymm (sub h₁ h₂ he) (sub h₂ h₁ he.symm)

lemma mcc_coprime {Q : Finset ℕ} (hQ : ∀ q ∈ Q, ∃ p, p.Prime ∧ q = p ^ 2)
    {a b : ℕ} (ha : a ∈ Q) (hb : b ∈ Q) (hne : a ≠ b) : Nat.Coprime a b := by
  obtain ⟨p, hp, rfl⟩ := hQ a ha
  obtain ⟨q, hq, rfl⟩ := hQ b hb
  exact Nat.coprime_pow_primes 2 2 hp hq (fun he => hne (he ▸ rfl))

lemma mcc_prod_dvd (T : Finset ℕ) (M : ℕ)
    (hc : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime a b)
    (hd : ∀ q ∈ T, q ∣ M) : ∏ q ∈ T, q ∣ M := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hsub : T ⊆ insert a T := subset_insert _ _
    rw [prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (hd a (mem_insert_self _ _))
      (ih (fun b hb c hc' => hc b (hsub hb) c (hsub hc')) (fun q hq => hd q (hsub hq)))
    exact Nat.Coprime.prod_right fun b hb => hc a (mem_insert_self _ _) b (hsub hb)
      (fun he => ha (he ▸ hb))

/-- Des carrés de premiers distincts qui divisent tous `M` : leur produit divise `M`. -/
lemma mc_Rdvd (Q V : Finset ℕ) (hQ : ∀ q ∈ Q, ∃ p, p.Prime ∧ q = p ^ 2) (hV : V ⊆ Q)
    (M : ℕ) (hM : ∀ q ∈ V, q ∣ M) : ∏ q ∈ V, q ∣ M := by
  exact mcc_prod_dvd V M (fun _ ha _ hb => mcc_coprime hQ (hV ha) (hV hb)) hM

/-- Dichotomie (Larsen, th. 2) : ou bien au moins la moitié des parties `T ⊆ Q_s` à 12 éléments
sont « mauvaises » (`h` à distance `> Y` de tout multiple de `∏ T`), ou bien un même `M` proche
de `h` (`|h − M| ≤ Y`) est multiple d'au moins la moitié des éléments de `Q_s`.
Preuve : double comptage des paires (`U` à 11 éléments, `q ∉ U`) ; un `U` a plus de `(n − 11)/2`
extensions bonnes ; leurs multiples proches de `h` sont des multiples de `∏ U > 2Y` distants
de `≤ 2Y`, donc égaux. -/
lemma mc_core (Qs : Finset ℕ) (y Y h : ℕ)
    (hlow : ∀ q ∈ Qs, y < q) (hY : 2 * Y < y ^ 11) :
    (∃ W ⊆ Qs.powersetCard 12, Qs.card.choose 12 ≤ 2 * W.card ∧
        ∀ T ∈ W, ∀ k : ℕ, (Y : ℤ) < |(h : ℤ) - k * ∏ q ∈ T, (q : ℤ)|) ∨
    ∃ M : ℕ, |(h : ℤ) - M| ≤ Y ∧ ∃ S ⊆ Qs, Qs.card ≤ 2 * S.card ∧ ∀ q ∈ S, q ∣ M := by
  classical
  let A := Qs.powersetCard 12
  let L := Qs.powersetCard 11
  let bad := fun T : Finset ℕ => ∀ k : ℕ, (Y : ℤ) < |(h : ℤ) - k * ∏ q ∈ T, (q : ℤ)|
  let W := A.filter bad
  by_cases hcount : Qs.card.choose 12 ≤ 2 * W.card
  · exact Or.inl ⟨W, filter_subset _ _, hcount, fun _ ht => (mem_filter.mp ht).2⟩
  right
  let G := A \ W
  have hW : W ⊆ A := filter_subset _ _
  have hcardG : Qs.card.choose 12 < 2 * G.card := by
    have h := card_sdiff_of_subset hW
    have hh := card_le_card hW
    change G.card = A.card - W.card at h
    have hA : A.card = Qs.card.choose 12 := card_powersetCard _ _
    omega
  let rel := fun (T U : Finset ℕ) => U ⊆ T
  have upper : ∃ U ∈ L, (Qs.card - 11) / 2 < (G.bipartiteBelow rel U).card := by
    by_contra! hall
    have hbound := Finset.card_mul_le_card_mul (r := rel) (s := G) (t := L) (m := 12)
      (n := (Qs.card - 11) / 2) (fun T ht => by
        have hT := mem_powersetCard.mp (mem_sdiff.mp ht).1
        have heq : L.bipartiteAbove rel T = T.powersetCard 11 := by
          ext U
          simp only [mem_bipartiteAbove, L, rel, mem_powersetCard]
          exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hT.1, h.2⟩, h.1⟩⟩
        rw [heq, card_powersetCard, hT.2]
        decide) hall
    have hrec := Nat.choose_succ_right_eq Qs.card 11
    change Qs.card.choose 12 * 12 = _ at hrec
    have hmul := Nat.mul_le_mul_left (Qs.card.choose 11) (Nat.div_mul_le_self (Qs.card - 11) 2)
    change G.card * 12 ≤ L.card * _ at hbound
    have hL : L.card = Qs.card.choose 11 := card_powersetCard _ _
    rw [hL] at hbound
    rw [← Nat.mul_assoc] at hmul
    omega
  obtain ⟨U, hU, hmany⟩ := upper
  obtain ⟨hUQ, hUc⟩ := mem_powersetCard.mp hU
  let I := (Qs \ U).filter fun q => insert q U ∈ G
  have covers : G.bipartiteBelow rel U ⊆ I.image (fun q => insert q U) := by
    intro T hT
    obtain ⟨ht, hUT⟩ := mem_filter.mp hT
    change U ⊆ T at hUT
    obtain ⟨hTQ, hc⟩ := mem_powersetCard.mp (mem_sdiff.mp ht).1
    obtain ⟨q, hq, rfl⟩ := exists_eq_insert_iff.mpr ⟨hUT, by omega⟩
    exact mem_image.mpr ⟨q, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hTQ (mem_insert_self _ _), hq⟩, ht⟩, rfl⟩
  have hcnt := (card_le_card covers).trans card_image_le
  have hI {q} (hq : q ∈ I) : q ∈ Qs ∧ q ∉ U ∧ insert q U ∈ G :=
    ⟨(mem_sdiff.mp (mem_filter.mp hq).1).1, (mem_sdiff.mp (mem_filter.mp hq).1).2, (mem_filter.mp hq).2⟩
  let v := ∏ q ∈ U, q
  have hv : 2 * Y < v := by
    have hle := pow_card_le_prod U id y fun q hq => (hlow _ (hUQ hq)).le
    rw [hUc] at hle
    exact hY.trans_le hle
  have close {q} (hq : q ∈ I) : ∃ a : ℕ, |(h : ℤ) - ((v * a : ℕ) : ℤ)| ≤ Y ∧ q ∣ a := by
    obtain ⟨_, hn, ht⟩ := hI hq
    have hb : ¬ bad (insert q U) := fun hb =>
      (mem_sdiff.mp ht).2 (mem_filter.mpr ⟨(mem_sdiff.mp ht).1, hb⟩)
    change ¬ ∀ k : ℕ, _ at hb
    push Not at hb
    obtain ⟨k, hk⟩ := hb
    refine ⟨k * q, ?_, dvd_mul_left _ _⟩
    rw [prod_insert hn] at hk
    simpa [v, Nat.cast_prod, mul_comm, mul_left_comm, mul_assoc] using hk
  obtain ⟨q₀, hq₀⟩ := card_pos.mp (show 0 < I.card by omega)
  obtain ⟨a, ha, _⟩ := close hq₀
  have unique {b : ℕ} (hb : |(h : ℤ) - ((v * b : ℕ) : ℤ)| ≤ Y) : a = b := by
    have sep {u w : ℕ} (he : u < w) : v * u + v ≤ v * w := by
      simpa [Nat.mul_succ] using Nat.mul_le_mul_left v (show u + 1 ≤ w from he)
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    rcases lt_trichotomy a b with hab | hab | hab
    · have := sep hab
      omega
    · exact hab
    · have := sep hab
      omega
  have hdj : Disjoint U I := disjoint_left.mpr fun _ hu hi => (hI hi).2.1 hu
  refine ⟨v * a, ha, U ∪ I, union_subset hUQ (fun q hq => (hI hq).1), ?_, ?_⟩
  · rw [card_union_of_disjoint hdj, hUc]
    omega
  · intro q hq
    rcases mem_union.mp hq with hu | hi
    · exact dvd_mul_of_dvd_left (dvd_prod_of_mem id hu) _
    · obtain ⟨b, hb, hd⟩ := close hi
      rw [unique hb]
      exact dvd_mul_of_dvd_right hd _

/-- Rigidité : si `∏ T` divise `M` (proche de `h`), `∏ T ≥ 2Y` et `r ∤ M`, alors `h` est à
distance `≥ ∏ T / 2` de tout multiple de `r·∏ T`. -/
lemma mc_rigid (T : Finset ℕ) (Y h M r : ℕ) (hM : |(h : ℤ) - M| ≤ Y)
    (hcop : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime a b) (hdiv : ∀ q ∈ T, q ∣ M)
    (hr : ¬ r ∣ M) (hbig : 2 * Y ≤ ∏ q ∈ T, q) (k : ℕ) :
    (((∏ q ∈ T, q) : ℕ) : ℤ) ≤ 2 * |(h : ℤ) - k * (((r * ∏ q ∈ T, q) : ℕ) : ℤ)| := by
  let P := ∏ q ∈ T, q
  obtain ⟨u, hu⟩ : P ∣ M := mcc_prod_dvd T M hcop hdiv
  have hne : u ≠ k * r := by
    rintro rfl
    exact hr ⟨P * k, by rw [hu]; ring⟩
  have hsep : (P : ℤ) ≤ |(M : ℤ) - k * ((r * P : ℕ) : ℤ)| := by
    rw [hu]
    push_cast
    rw [show (P : ℤ) * u - k * (r * P) = (P : ℤ) * (u - k * r) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (P : ℤ))]
    have hn : (u : ℤ) ≠ k * r := by exact_mod_cast hne
    have hpos : 0 < |(u : ℤ) - k * r| := abs_pos.mpr (sub_ne_zero.mpr hn)
    nlinarith only [mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ |(u : ℤ) - k * r| by omega)
      (by positivity : 0 ≤ (P : ℤ))]
  have htri := abs_sub_le (M : ℤ) (h : ℤ) ((k : ℤ) * ((r * P : ℕ) : ℤ))
  rw [abs_sub_comm (M : ℤ) (h : ℤ)] at htri
  have hcast : 2 * (Y : ℤ) ≤ P := by exact_mod_cast hbig
  change (P : ℤ) ≤ 2 * |(h : ℤ) - k * ((r * P : ℕ) : ℤ)|
  omega

/-- Clé : si tout `M` proche de `h` (`|h − M| ≤ s²⁰`) a un diviseur manquant `r ∈ V`
(`V ⊆ Q ∪ B`, `r ≤ 256 s²`), alors au moins `C(n_s/2, 11)` éléments `d` de `Z \ E` sont tels que
`h` est à distance `≥ d/(64¹² s⁴)` de tout multiple de `d`.
Cas (A), `mc_core` gauche : `G = {∏ T : T mauvais}`. Cas (B) : `r ∤ M`, `G = {r·∏ T' : T' ⊆ S, |T'| = 11}`
(`mc_rigid`). Injectivité : `mc_inj`. -/
lemma mc_key (N : ℕ) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4))
    (s : ℕ) (hs : N ≤ s) (hs2 : 2 ≤ s) (hs8 : 8 * s < N * 2 ^ N)
    (hn : 35 ≤ (Nat.primesLE (8 * s) \ Nat.primesLE s).card)
    (V : Finset ℕ) (hV : V ⊆ Q ∪ B) (hVs : ∀ r ∈ V, r ≤ 256 * s ^ 2)
    (h : ℕ) (hfar : ∀ M : ℕ, |(h : ℤ) - M| ≤ ((s ^ 20 : ℕ) : ℤ) → ∃ r ∈ V, ¬ r ∣ M) :
    ∃ G ⊆ Z \ E, ((Nat.primesLE (8 * s) \ Nat.primesLE s).card / 2).choose 11 ≤ G.card ∧
      ∀ d ∈ G, ∀ k : ℕ, (1 / (64 ^ 12 * (s : ℝ) ^ 4)) * d ≤ |(h : ℝ) - k * d| := by
  classical
  let P := Nat.primesLE (8 * s) \ Nat.primesLE s
  let A := P.image (· ^ 2)
  have hAcard : A.card = P.card := card_image_of_injective _ (fun a b he => by simpa using he)
  have hn' : 35 ≤ P.card := hn
  have hA (q : ℕ) (hq : q ∈ A) : q ∈ Q ∧ s ^ 2 < q ∧ q ≤ 64 * s ^ 2 := by
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hu, hl⟩ := mem_sdiff.mp hp
    obtain ⟨hpu, hpr⟩ := Nat.mem_primesLE.mp hu
    have hpl : s < p := lt_of_not_ge fun le => hl (Nat.mem_primesLE.mpr ⟨le, hpr⟩)
    refine ⟨?_, by nlinarith, ?_⟩
    · rw [hQ]
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr (hpu.trans_lt hs8), hpr, hs.trans_lt hpl⟩, rfl⟩
    · nlinarith only [Nat.pow_le_pow_left hpu 2]
  have hprime (q : ℕ) (hq : q ∈ Q) : ∃ p, p.Prime ∧ q = p ^ 2 := by
    rw [hQ] at hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact ⟨p, (mem_filter.mp hp).2.1, rfl⟩
  have h1 : 1 ∈ B := by
    rw [hB]
    exact mem_image.mpr ⟨1, mem_filter.mpr ⟨mem_range.mpr (by omega), by simp⟩, by simp⟩
  have memZ (b : ℕ) (hb : b ∈ B) (T : Finset ℕ) (hT : T ⊆ Q) : b * ∏ q ∈ T, q ∈ Z := by
    rw [hZ]
    exact mem_image.mpr ⟨(b, T), mem_product.mpr ⟨hb, mem_powerset.mpr hT⟩, rfl⟩
  have notE {d : ℕ} (hd : N ^ 4 ≤ d) : d ∉ E := by
    rw [hE]
    exact fun he => hd.not_gt (mem_filter.mp he).2
  have hy : 2 * s ^ 20 < (s ^ 2) ^ 11 := by
    rw [← pow_mul, show 2 * 11 = 20 + 2 by decide, pow_add, mul_comm 2]
    exact Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
  have hNs : N ^ 4 ≤ (s ^ 2) ^ 11 := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_left hs _).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have large (T : Finset ℕ) (hT : T ⊆ A) (hcard : 11 ≤ T.card) :
      (s ^ 2) ^ 11 ≤ ∏ q ∈ T, q :=
    (Nat.pow_le_pow_right (by positivity) hcard).trans
      (pow_card_le_prod T id _ fun q hq => (hA q (hT hq)).2.1.le)
  have hAQ : A ⊆ Q := fun q hq => (hA q hq).1
  have den : (0 : ℝ) < 64 ^ 12 * (s : ℝ) ^ 4 := by positivity
  rcases mc_core A (s ^ 2) (s ^ 20) h (fun q hq => (hA q hq).2.1) hy with
    ⟨W, hW, hcount, hbad⟩ | ⟨M, hM, S, hS, hcount, hdvd⟩
  · let f := fun T : Finset ℕ => ∏ q ∈ T, q
    have hT {T} (ht : T ∈ W) := mem_powersetCard.mp (hW ht)
    refine ⟨W.image f, ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨T, ht, rfl⟩ := mem_image.mp hd
      have ht' := hT ht
      exact mem_sdiff.mpr ⟨by simpa [f] using memZ 1 h1 T (ht'.1.trans hAQ),
        notE (hNs.trans (large T ht'.1 (by omega)))⟩
    · rw [card_image_of_injOn (fun T ht U hu he =>
          mc_inj Q hprime ((hT ht).1.trans hAQ) ((hT hu).1.trans hAQ) he)]
      rw [hAcard] at hcount
      have hrec := Nat.choose_succ_right_eq P.card 11
      change P.card.choose 12 * 12 = _ at hrec
      have h24 := Nat.mul_le_mul_left (P.card.choose 11) (show 24 ≤ P.card - 11 by omega)
      apply (Nat.choose_le_choose 11 (Nat.div_le_self P.card 2)).trans
      omega
    · intro d hd k
      obtain ⟨T, ht, rfl⟩ := mem_image.mp hd
      have ht' := hT ht
      have hu := prod_le_pow_card T id (64 * s ^ 2) (fun q hq => (hA q (ht'.1 hq)).2.2)
      rw [ht'.2] at hu
      have hu' : (f T : ℝ) ≤ (64 * (s : ℝ) ^ 2) ^ 12 := by exact_mod_cast hu
      have hdist : (s : ℝ) ^ 20 < |(h : ℝ) - k * (f T : ℝ)| := by
        have hh := hbad T ht k
        rw [← Nat.cast_prod] at hh
        change ((s ^ 20 : ℕ) : ℤ) < |(h : ℤ) - k * (f T : ℤ)| at hh
        exact_mod_cast hh
      apply le_trans _ hdist.le
      rw [one_div_mul_eq_div, div_le_iff₀ den]
      exact hu'.trans (le_of_eq (by ring))
  · obtain ⟨r, hr, hrM⟩ := hfar M hM
    have hrpos : 0 < r := by
      rcases mem_union.mp (hV hr) with hq | hb
      · obtain ⟨p, hp, rfl⟩ := hprime _ hq
        exact pow_pos hp.pos _
      · rw [hB] at hb
        obtain ⟨n, hn0, rfl⟩ := mem_image.mp hb
        exact pow_pos (mem_filter.mp hn0).2.1 _
    let f := fun T : Finset ℕ => r * ∏ q ∈ T, q
    have hT {T} (ht : T ∈ S.powersetCard 11) := mem_powersetCard.mp ht
    refine ⟨(S.powersetCard 11).image f, ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨T, ht, rfl⟩ := mem_image.mp hd
      obtain ⟨hTS, hc⟩ := hT ht
      have hTA := hTS.trans hS
      have hTQ := hTA.trans hAQ
      refine mem_sdiff.mpr ⟨?_, notE ((hNs.trans (large T hTA hc.ge)).trans
        (Nat.le_mul_of_pos_left _ hrpos))⟩
      rcases mem_union.mp (hV hr) with hq | hb
      · have hrT : r ∉ T := fun hh => hrM (hdvd _ (hTS hh))
        simpa [f, prod_insert hrT] using memZ 1 h1 (insert r T) (insert_subset hq hTQ)
      · exact memZ r hb T hTQ
    · rw [card_image_of_injOn (fun T ht U hu he =>
          mc_inj Q hprime ((hT ht).1.trans (hS.trans hAQ)) ((hT hu).1.trans (hS.trans hAQ))
            (Nat.eq_of_mul_eq_mul_left hrpos he)), card_powersetCard]
      rw [hAcard] at hcount
      exact Nat.choose_le_choose 11 (by change P.card / 2 ≤ S.card; omega)
    · intro d hd k
      obtain ⟨T, ht, rfl⟩ := mem_image.mp hd
      obtain ⟨hTS, hc⟩ := hT ht
      have hTA := hTS.trans hS
      have hTQ := hTA.trans hAQ
      have hrig := mc_rigid T (s ^ 20) h M r hM
        (fun _ ha _ hb => mcc_coprime hprime (hTQ ha) (hTQ hb))
        (fun _ hq => hdvd _ (hTS hq)) hrM (hy.le.trans (large T hTA hc.ge)) k
      let v := ∏ q ∈ T, q
      have hrig' : (v : ℝ) ≤ 2 * |(h : ℝ) - k * (f T : ℝ)| := by exact_mod_cast hrig
      have hru : (r : ℝ) ≤ 256 * (s : ℝ) ^ 2 := by exact_mod_cast hVs r hr
      have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      have hsc : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 4 := by
        apply pow_le_pow_right₀ (by linarith) (by decide)
      have hrden : 2 * (r : ℝ) ≤ 64 ^ 12 * (s : ℝ) ^ 4 := by
        nlinarith only [hru, hsc, sq_nonneg (s : ℝ)]
      rw [one_div_mul_eq_div, div_le_iff₀ den]
      change (↑(r * v) : ℝ) ≤ |(h : ℝ) - k * ↑(r * v)| * _
      change (v : ℝ) ≤ 2 * |(h : ℝ) - k * ↑(r * v)| at hrig'
      rw [Nat.cast_mul] at hrig' ⊢
      nlinarith only [mul_le_mul_of_nonneg_right hrden (show 0 ≤ (v : ℝ) by positivity),
        mul_le_mul_of_nonneg_right hrig' den.le]

open Filter in
/-- Croissance : pour `s` grand, `n_s ≥ 35` et `C(n_s/2, 11)·c²/25 ≥ 64 s log(16 s) + s + 3`
(`n_s ≥ s/(2 log s)` par `mc_primes` ; `Nat.pow_le_choose`). -/
lemma mc_growth : ∀ᶠ s : ℕ in atTop, 35 ≤ (Nat.primesLE (8 * s) \ Nat.primesLE s).card ∧
    64 * (s : ℝ) * Real.log (16 * s) + s + 3 ≤
      ((((Nat.primesLE (8 * s) \ Nat.primesLE s).card / 2).choose 11 : ℕ) : ℝ) *
        ((1 / (64 ^ 12 * (s : ℝ) ^ 4)) ^ 2 / 25) := by
  let K : ℕ := 132 * 25 * 64^24 * 8^11 * Nat.factorial 11
  have he₁ := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0:ℝ) < 1)).bound (by norm_num : (0:ℝ) < 1/200))
  have he₂ := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop 12 (by norm_num : (0:ℝ) < 1)).bound (by norm_num : (0:ℝ) < 1))
  filter_upwards [he₁,he₂,mc_primes,eventually_ge_atTop K,eventually_ge_atTop 16] with s h₁ h₂ hp hK hs
  let n := (Nat.primesLE (8*s) \ Nat.primesLE s).card
  change (s:ℝ) / (2 * Real.log s) ≤ n at hp
  change 35 ≤ n ∧ _ ≤ ((n/2).choose 11 : ℝ) * _
  have hs16 : 16 ≤ (s:ℝ) := by exact_mod_cast hs
  have hs0 : 0 < (s:ℝ) := by linarith
  have hl : 0 < Real.log (s:ℝ) := Real.log_pos (by linarith)
  simp only [Real.rpow_one, Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg hl.le,
    abs_of_nonneg (pow_nonneg hl.le _),abs_of_nonneg hs0.le,one_mul] at h₁ h₂
  have hn : 100 ≤ n := by
    have h : (100:ℝ) ≤ (s:ℝ)/(2*Real.log s) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    exact_mod_cast h.trans hp
  refine ⟨by omega, ?_⟩
  have hquarter : n ≤ 4*(n/2 + 1 - 11) := by omega
  have hsfrac : (s:ℝ)/(8*Real.log s) ≤ ((n/2+1-11:ℕ):ℝ) := by
    have hh : (n:ℝ) ≤ 4*((n/2+1-11:ℕ):ℝ) := by exact_mod_cast hquarter
    calc _ = ((s:ℝ)/(2*Real.log s))/4 := by ring
         _ ≤ (n:ℝ)/4 := by linarith only [hp]
         _ ≤ _ := by linarith only [hh]
  have hc : ((s:ℝ)/(8*Real.log s))^11 / (Nat.factorial 11 : ℝ) ≤ (n/2).choose 11 := by
    apply le_trans _ (Nat.pow_le_choose (α := ℝ) 11 (n/2))
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsfrac _) (by positivity)
  have hlog : Real.log (16*(s:ℝ)) ≤ 2*Real.log s := by
    rw [Real.log_mul (by norm_num) hs0.ne']; linarith only [Real.log_le_log (by norm_num) hs16]
  have hl1 : 1 ≤ Real.log (s:ℝ) := by
    have hh := Real.log_le_log (by norm_num : 0 < (2:ℝ)^4) (by norm_num; exact hs : (2:ℝ)^4 ≤ s)
    rw [Real.log_pow] at hh; norm_num only [Nat.cast_ofNat] at hh; linarith only [hh,Real.log_two_gt_d9]
  have hk : (K:ℝ) * (Real.log (s:ℝ))^12 ≤ (s:ℝ)^2 := by
    rw [pow_two]; exact mul_le_mul (by exact_mod_cast hK) h₂ (by positivity) hs0.le
  calc _ ≤ 132*(s:ℝ)*Real.log s := by
         nlinarith only [mul_le_mul_of_nonneg_left hlog hs0.le,
           mul_le_mul_of_nonneg_left hl1 hs0.le,hs16]
       _ ≤ ((s:ℝ)/(8*Real.log s))^11 / (Nat.factorial 11:ℝ) * ((1/(64^12*(s:ℝ)^4))^2/25) := by
         dsimp [K] at hk
         push_cast at hk
         field_simp [hl.ne', hs0.ne']
         linarith only [hk]
       _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- Taille de `m` : tout `z ∈ Z` divise `((M₀ − 1)!)⁴`, donc `ppcm Z ≤ M₀^(4 M₀)`, `M₀ = N·2^N`. -/
lemma mc_mbound (N : ℕ) (B Q Z : Finset ℕ) (hN : 1 ≤ N)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)) :
    Z.lcm id ≤ (N * 2 ^ N) ^ (4 * (N * 2 ^ N)) := by
  classical
  let L := N*2^N
  let P := (range L).filter (fun p => p.Prime ∧ N < p)
  have hp : (∏ p ∈ P, p) ∣ L.factorial := by
    rw [← prod_Ico_id_eq_factorial]
    apply prod_dvd_prod_of_subset
    intro p hp; obtain ⟨h,_,hh⟩ := mem_filter.mp hp
    exact mem_Ico.mpr ⟨hN.trans hh.le,Nat.lt_succ_of_lt (mem_range.mp h)⟩
  have hQprod : (∏ q ∈ Q, q) ∣ L.factorial ^ 2 := by
    change Q = P.image (·^2) at hQ
    rw [hQ,prod_image (by intro a _ b _ hab; simpa using hab),prod_pow]
    exact pow_dvd_pow_of_dvd hp _
  have hdiv : Z.lcm id ∣ L.factorial^4 := by
    apply Finset.lcm_dvd; intro z hz
    rw [hZ] at hz
    obtain ⟨⟨b,T⟩,hbT,rfl⟩ := mem_image.mp hz
    obtain ⟨hb,hT⟩ := mem_product.mp hbT
    rw [hB] at hb
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
    have hnf := Nat.dvd_factorial (mem_filter.mp hn).2.1 (mem_range.mp (mem_filter.mp hn).1).le
    have hd := (prod_dvd_prod_of_subset T Q id (mem_powerset.mp hT)).trans hQprod
    rw [show L.factorial^4 = L.factorial^2 * L.factorial^2 by ring]
    exact Nat.mul_dvd_mul (pow_dvd_pow_of_dvd hnf 2) hd
  calc _ ≤ L.factorial^4 := Nat.le_of_dvd (pow_pos (Nat.factorial_pos L) _) hdiv
       _ ≤ (L^L)^4 := Nat.pow_le_pow_left (Nat.factorial_le_pow _) _
       _ = L^(4*L) := by rw [← pow_mul,Nat.mul_comm]

/-- Le produit `R_s` des `q ∈ Q`, `q ≤ 64 s²`, dépasse `2·(2s)²⁰` (il contient les `p²`, `p ∈ P_s`). -/
lemma mc_Rge (N : ℕ) (Q : Finset ℕ)
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (s : ℕ) (hs : N ≤ s) (hs8 : 8 * s < N * 2 ^ N) (h2 : 2 ≤ s)
    (hn : 35 ≤ (Nat.primesLE (8 * s) \ Nat.primesLE s).card) :
    2 * (2 * s) ^ 20 ≤ ∏ q ∈ Q.filter (· ≤ 64 * s ^ 2), q := by
  classical
  let P := Nat.primesLE (8*s) \ Nat.primesLE s
  let G := P.image (·^2)
  have hb (p : ℕ) (hp : p ∈ P) : p.Prime ∧ s < p ∧ p ≤ 8*s := by
    obtain ⟨hp8,hps⟩ := mem_sdiff.mp hp
    obtain ⟨hu,hpr⟩ := Nat.mem_primesLE.mp hp8
    exact ⟨hpr,lt_of_not_ge (fun h => hps (Nat.mem_primesLE.mpr ⟨h,hpr⟩)),hu⟩
  have hG : G ⊆ Q.filter (· ≤ 64*s^2) := by
    intro q hq; obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨hpr,hl,hu⟩ := hb p hp
    apply mem_filter.mpr; constructor
    · rw [hQ]; exact mem_image.mpr ⟨p,mem_filter.mpr ⟨mem_range.mpr (hu.trans_lt hs8),hpr,hs.trans_lt hl⟩,rfl⟩
    · calc p^2 ≤ (8*s)^2 := Nat.pow_le_pow_left hu _
           _ = _ := by ring
  have hc : G.card = P.card := card_image_of_injective _ (fun a b hab => by simpa using hab)
  calc 2*(2*s)^20 = 2^21*s^20 := by ring
       _ ≤ s^50*s^20 := by
         apply Nat.mul_le_mul_right
         exact (Nat.pow_le_pow_left h2 21).trans (Nat.pow_le_pow_right (by omega) (by decide))
       _ = (s^2)^35 := by ring
       _ ≤ (s^2)^G.card := Nat.pow_le_pow_right (by positivity) (hc ▸ hn)
       _ ≤ ∏ q ∈ G, q := pow_card_le_prod G id (s^2) (by
         intro q hq; obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
         exact Nat.pow_le_pow_left (hb p hp).2.1.le _)
       _ ≤ _ := prod_le_prod_of_subset_of_one_le' hG (by
         intro q hq _; obtain ⟨p,hp,rfl⟩ := mem_image.mp (hQ ▸ (mem_filter.mp hq).1)
         exact one_le_pow₀ (mem_filter.mp hp).2.1.one_le)

/-- Un multiple `M` de `R` proche de `h` (`|h − M| ≤ Y < h*`) est impossible quand `R ∣ m` et
`2h* ≤ R`, où `h* = min(h, m − h)`. -/
lemma mc_near (m R h M Y : ℕ) (hh : h < m) (hR : R ∣ m) (hRM : R ∣ M)
    (hY : Y < min h (m - h)) (hRh : 2 * min h (m - h) ≤ R) (hM : |(h : ℤ) - M| ≤ Y) : False := by
  obtain ⟨a, rfl⟩ := hRM
  obtain ⟨b, rfl⟩ := hR
  have h2 := min_le_right h (R * b - h)
  have h3 : min h (R * b - h) = h ∨ min h (R * b - h) = R * b - h := min_choice _ _
  rw [abs_le] at hM
  obtain ⟨hM1, hM2⟩ := hM
  push_cast at hM1 hM2
  have hsub : ((R * b - h : ℕ) : ℤ) = (R : ℤ) * b - h := by
    rw [Nat.cast_sub hh.le]; push_cast; ring
  have hYμ : (Y : ℤ) < (min h (R * b - h) : ℕ) := by exact_mod_cast hY
  have h2μ : 2 * ((min h (R * b - h) : ℕ) : ℤ) ≤ R := by exact_mod_cast hRh
  have hμ2 : ((min h (R * b - h) : ℕ) : ℤ) ≤ (R : ℤ) * b - h := by
    rw [← hsub]; exact_mod_cast h2
  have hμ1 : ((min h (R * b - h) : ℕ) : ℤ) ≤ h := by exact_mod_cast min_le_left h (R * b - h)
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp at hM2
    linarith
  rcases le_or_gt b a with hab | hab
  · have : (R : ℤ) * b ≤ R * a := by exact_mod_cast Nat.mul_le_mul_left R hab
    linarith
  · have hRa : (R : ℤ) ≤ R * a := by
      have : R * 1 ≤ R * a := Nat.mul_le_mul_left R ha
      simpa using (by exact_mod_cast this : ((R * 1 : ℕ) : ℤ) ≤ ((R * a : ℕ) : ℤ))
    have hRba : (R : ℤ) * a + R ≤ R * b := by
      have : R * (a + 1) ≤ R * b := Nat.mul_le_mul_left R hab
      have : ((R * (a + 1) : ℕ) : ℤ) ≤ ((R * b : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at this; linarith
    rcases h3 with h3 | h3
    · have : ((min h (R * b - h) : ℕ) : ℤ) = h := by exact_mod_cast h3
      linarith
    · have : ((min h (R * b - h) : ℕ) : ℤ) = (R : ℤ) * b - h := by rw [← hsub]; exact_mod_cast h3
      linarith

/-- Si tout `r ∈ Q ∪ B` divise `M`, alors `ppcm Z` divise `M` (`b` et `∏ T` premiers entre eux). -/
lemma mc_top_dvd (N : ℕ) (B Q Z : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (M : ℕ) (hM : ∀ r ∈ Q ∪ B, r ∣ M) : Z.lcm id ∣ M := by
  classical
  have hprime : ∀ q ∈ Q, ∃ p, p.Prime ∧ q = p ^ 2 := by
    intro q hq
    rw [hQ] at hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact ⟨p, (mem_filter.mp hp).2.1, rfl⟩
  apply Finset.lcm_dvd
  intro z hz
  rw [hZ] at hz
  obtain ⟨⟨b, T⟩, hpair, rfl⟩ := mem_image.mp hz
  obtain ⟨hb, hT⟩ := mem_product.mp hpair
  have hTQ := mem_powerset.mp hT
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (hM b (mem_union_right _ hb))
    (mc_Rdvd Q T hprime hTQ M fun q hq => hM q (mem_union_left _ (hTQ hq)))
  apply Nat.Coprime.prod_right
  intro q hq
  have hq' := hTQ hq
  rw [hQ] at hq'
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq'
  rw [hB] at hb
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
  have hn' := (mem_filter.mp hn).2
  have hp' := (mem_filter.mp hp).2
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  exact hp'.1.coprime_iff_not_dvd.mpr fun hd =>
    hp'.2.not_ge (hn'.2 p (Nat.mem_primeFactors.mpr ⟨hp'.1, hd, hn'.1.ne'⟩))

/-- Somme des fibres : `∑_{j ≤ J} exp(−2^j·N − 3) ≤ 1/4` dès `N ≥ 1`. -/
lemma mc_series (N J : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ range (J + 1), Real.exp (-((2 ^ j * N : ℕ) : ℝ) - 3) ≤ 1 / 4 := by
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp (1 : ℝ)
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have he3 : Real.exp (-3) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp (3 : ℝ)
    rw [inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
    linarith
  have hterm : ∀ j ∈ range (J + 1),
      Real.exp (-((2 ^ j * N : ℕ) : ℝ) - 3) ≤ (1 / 4) * (1 / 2) ^ (j + 1) := by
    intro j _
    have hj : (j : ℝ) + 1 ≤ ((2 ^ j * N : ℕ) : ℝ) := by
      have h1 : j < 2 ^ j := Nat.lt_two_pow_self
      have : j + 1 ≤ 2 ^ j * N := by nlinarith
      exact_mod_cast this
    calc Real.exp (-((2 ^ j * N : ℕ) : ℝ) - 3)
        = Real.exp (-3) * Real.exp (-((2 ^ j * N : ℕ) : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ (1 / 4) * Real.exp (-1) ^ (j + 1) := by
          apply mul_le_mul he3 _ (Real.exp_pos _).le (by norm_num)
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          push_cast at hj ⊢; linarith
      _ ≤ (1 / 4) * (1 / 2) ^ (j + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ (Real.exp_pos _).le he1 _
  have hgeo : ∀ n : ℕ, ∑ j ∈ range n, (1 / 2 : ℝ) ^ (j + 1) = 1 - (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  calc _ ≤ ∑ j ∈ range (J + 1), (1 / 4 : ℝ) * (1 / 2) ^ (j + 1) := sum_le_sum hterm
    _ = (1 / 4) * ∑ j ∈ range (J + 1), (1 / 2 : ℝ) ^ (j + 1) := by rw [mul_sum]
    _ ≤ (1 / 4) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [hgeo]
        have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (J + 1)
        linarith
    _ = 1 / 4 := by ring

set_option maxHeartbeats 2000000 in
/-- Assemblage. Échelles `s_j = 2^j·N`, `j ≤ J = N − 4` (`16 s_J = M₀`) ; `j(h)` = plus grand `j ≤ J`
avec `s_j²⁰ < h*` (`Nat.findGreatest`). Si `j < J` : `V = Q.filter (· ≤ 64 s_j²)` (`mc_Rdvd`,
`mc_Rge`, `mc_near`) ; si `j = J` : `V = Q ∪ B` (`mc_top_dvd`, `mc_near` avec `R = m`). Puis
`mc_key`, `mc_far`, `mc_prod`, `mc_growth` : `‖∏‖ ≤ α^|D|·exp(−64 s log(16 s) − s − 3)`. Fibre de `j` :
au plus `2(2s_j)²⁰ + 2` éléments si `j < J` (`mc_count`), au plus `m ≤ M₀^(4M₀)` si `j = J`
(`mc_mbound`), donc au plus `exp(64 s log(16 s))` ; `mc_series` conclut. -/
theorem plage_c_holds : OMA.E318H1R.H2 := by
  classical
  obtain ⟨S₀,hS₀⟩ := eventually_atTop.mp mc_growth
  refine ⟨max S₀ 64, ?_⟩
  intro N hN B Q Z E m α hα hα'
  let D := Z \ E
  let f (h d : ℕ) := ((α-1 : ℝ) : ℂ) + Complex.exp (2 * Real.pi * Complex.I * ((h:ℂ) / d))
  let S := (range m).filter (fun h : ℕ => N^8 < h^5 ∧ N^8 < (m-h)^5 ∧
    N^2 < 2*h ∧ N^2 < 2*(m-h) ∧ N^36 < h ∧ N^36 < m-h)
  change ∑ h ∈ S, ‖∏ d ∈ D, f h d‖ ≤ α^D.card / 4
  let J := N - 4
  let s (j : ℕ) := 2^j * N
  let u (h : ℕ) := min h (m-h)
  let jf (h : ℕ) := Nat.findGreatest (fun j => s j ^ 20 < u h) J
  have h64 : 64 ≤ N := (le_max_right _ _).trans hN
  have hNs (j : ℕ) : N ≤ s j := Nat.le_mul_of_pos_left _ (by positivity : 0 < 2^j)
  have htop : 16 * s J = N * 2^N := by
    conv_rhs => rw [show (2:ℕ)^N = 2^(J+4) by congr 1; dsimp [J]; omega, pow_add]
    dsimp [s]; ring
  have h8 (j : ℕ) (hj : j ≤ J) : 8 * s j < N * 2^N := by
    have hx : s j ≤ s J := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hj)
    rw [← htop]; have := hNs j; omega
  have hle (h : ℕ) : jf h ≤ J := Nat.findGreatest_le _
  have hub (h : ℕ) (hj : jf h < J) : u h ≤ (2 * s (jf h))^20 := by
    have he : s (jf h + 1) = 2 * s (jf h) := by dsimp [s]; rw [pow_succ]; ring
    rw [← he]; apply le_of_not_gt
    exact Nat.findGreatest_is_greatest (P := fun j => s j ^ 20 < u h)
      (Nat.lt_succ_self (jf h)) (by omega)
  have hQp (q : ℕ) (hq : q ∈ Q) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p < N * 2^N ∧ q = p^2 := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    exact ⟨p,(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2,mem_range.mp (mem_filter.mp hp).1,rfl⟩
  have hQ' (q : ℕ) (hq : q ∈ Q) : ∃ p : ℕ, p.Prime ∧ q = p^2 := by
    obtain ⟨p,hp,_,_,he⟩ := hQp q hq; exact ⟨p,hp,he⟩
  have hpos (d : ℕ) (hd : d ∈ D) : 0 < d := by
    obtain ⟨⟨b,T⟩,hbT,rfl⟩ := mem_image.mp (mem_sdiff.mp hd).1
    obtain ⟨hb,hT⟩ := mem_product.mp hbT
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
    apply Nat.mul_pos (pow_pos (mem_filter.mp hn).2.1 _)
    apply prod_pos; intro q hq
    obtain ⟨p,hp,rfl⟩ := hQ' q ((mem_powerset.mp hT) hq)
    exact pow_pos hp.pos _
  have ha : 0 ≤ α := by linarith
  have hbound (h : ℕ) (hh : h ∈ S) :
      ‖∏ d ∈ D, f h d‖ ≤ α^D.card * Real.exp (-(64*(s (jf h):ℝ)*Real.log (16*s (jf h)) + s (jf h) + 3)) := by
    let j := jf h
    have hj : j ≤ J := hle h
    let x := s j
    have hx : N ≤ x := hNs j
    have hx2 : 2 ≤ x := by omega
    have hx8 : 8*x < N*2^N := h8 j hj
    obtain ⟨hn,hgrow⟩ := hS₀ x (((le_max_left _ _).trans hN).trans hx)
    obtain ⟨hr,_,_,_,_,hu,hv⟩ := mem_filter.mp hh
    have hm : h < m := mem_range.mp hr
    have hlo : x ^ 20 < u h := by
      apply Nat.findGreatest_spec (P := fun i => s i ^ 20 < u h) (Nat.zero_le J)
      have hpow := Nat.pow_le_pow_right (by omega : 0 < N) (by decide : 20 ≤ 36)
      simpa [s,u] using (lt_min (hpow.trans_lt hu) (hpow.trans_lt hv))
    obtain ⟨V,hV,hrange,hfar⟩ : ∃ V : Finset ℕ, V ⊆ Q ∪ B ∧ (∀ r ∈ V, r ≤ 256*x^2) ∧
        ∀ M : ℕ, |(h:ℤ)-M| ≤ ((x^20:ℕ):ℤ) → ∃ r ∈ V, ¬ r ∣ M := by
      by_cases hj' : j < J
      · let V := Q.filter (· ≤ 64*x^2)
        have hvq : V ⊆ Q := filter_subset _ _
        refine ⟨V, fun r hr => mem_union_left _ (hvq hr), fun r hr => ?_, ?_⟩
        · have := (mem_filter.mp hr).2; omega
        · intro M hM; by_contra! hall
          apply mc_near m (∏ q ∈ V, q) h M (x^20) hm _ (mc_Rdvd Q V hQ' hvq M hall) hlo _ hM
          · apply mc_Rdvd Q V hQ' hvq; intro q hq
            obtain ⟨p,hp,hpn,hpu,rfl⟩ := hQp q (hvq hq)
            exact dvd_lcm (f := id) (mem_sdiff.mp (mc_square N B Q Z E rfl rfl rfl rfl hp hpn hpu)).1
          · exact (Nat.mul_le_mul_left 2 (hub h hj')).trans (mc_Rge N Q rfl x hx hx8 hx2 hn)
      · have he : j = J := by omega
        have hX : N * 2^N = 16*x := by simpa only [x,he] using htop.symm
        refine ⟨Q ∪ B,Subset.rfl, ?_, ?_⟩
        · intro r hr
          have hex : ∃ a : ℕ, a < N*2^N ∧ r = a^2 := by
            rcases mem_union.mp hr with hq|hb
            · obtain ⟨p,_,_,hp,he⟩ := hQp r hq; exact ⟨p,hp,he⟩
            · obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
              exact ⟨n,mem_range.mp (mem_filter.mp hn).1,rfl⟩
          obtain ⟨a,ha,rfl⟩ := hex
          calc a^2 ≤ (16*x)^2 := Nat.pow_le_pow_left (hX ▸ ha.le) _
               _ = _ := by ring
        · intro M hM; by_contra! hall
          apply mc_near m m h M (x^20) hm dvd_rfl (mc_top_dvd N B Q Z rfl rfl rfl M hall) hlo _ hM
          omega
    obtain ⟨G,hGD,hcard,hG⟩ := mc_key N B Q Z E rfl rfl rfl rfl x hx hx2 hx8 hn V hV hrange h hfar
    let c : ℝ := 1/(64^12 * (x:ℝ)^4)
    apply (mc_prod D G (f h) α (c^2/25) ha hGD (fun d _ => mc_factor _ _ _ (by linarith))
      (fun d hd => mc_far _ _ _ _ hα hα' (hpos d (hGD hd)) (by dsimp [c]; positivity) (hG d hd))).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hgrow.trans ?_))) (pow_nonneg ha _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hcard (j : ℕ) (hj : j ≤ J) : (S.filter (fun h => jf h = j)).card ≤ (16*s j)^(64*s j) := by
    by_cases hlt : j < J
    · apply (mc_count (m := m) (k := (2*s j)^20) _ ?_).trans
      · have h1 : 1 ≤ (2*s j)^20 := one_le_pow₀ (by have := hNs j; omega) (n := 20)
        calc 2*(2*s j)^20+2 ≤ 4*(2*s j)^20 := by omega
             _ ≤ (16*s j)^21 := by
               rw [pow_succ (16*s j)]; apply le_trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : 2*s j ≤ 16*s j) 20))
               rw [mul_comm]; exact Nat.mul_le_mul_left _ (by have := hNs j; omega)
             _ ≤ _ := Nat.pow_le_pow_right (by have := hNs j; omega) (by have := hNs j; omega)
      · intro h hh
        obtain ⟨hs,he⟩ := mem_filter.mp hh
        have hu := hub h (by omega : jf h < J)
        rw [he] at hu
        exact ⟨(mem_range.mp (mem_filter.mp hs).1).le, min_le_iff.mp hu⟩
    · obtain rfl : j = J := by omega
      calc _ ≤ (range m).card := card_le_card fun h hh => (mem_filter.mp (mem_filter.mp hh).1).1
           _ = m := card_range _
           _ ≤ _ := mc_mbound N B Q Z (by omega) rfl rfl rfl
           _ = _ := by rw [← htop]; congr 1; ring
  have hmap (h : ℕ) (_ : h ∈ S) : jf h ∈ range (J+1) := mem_range.mpr (Nat.lt_succ_of_le (hle h))
  rw [← sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ j ∈ range (J+1), α^D.card * Real.exp (-(s j:ℝ)-3) := by
         apply sum_le_sum; intro j hj
         let A : ℝ := 64 * (s j:ℝ) * Real.log (16*s j)
         let F := S.filter (fun h => jf h = j)
         have hc : (F.card:ℝ) ≤ Real.exp A := by
           have h := hcard j (by simpa using hj)
           have he : Real.exp A = (16*(s j:ℝ))^(64*s j) := by
             have := hNs j; have : 0 < s j := by omega
             have hpos : 0 < 16*(s j:ℝ) := by positivity
             simpa only [A,Nat.cast_mul,Nat.cast_ofNat,Real.exp_log hpos] using
               (Real.exp_nat_mul (Real.log (16*(s j:ℝ))) (64*s j))
           rw [he]; exact_mod_cast h
         calc _ ≤ ∑ _h ∈ F, α^D.card * Real.exp (-(A + s j + 3)) := by
                apply sum_le_sum; intro h hh; simpa only [(mem_filter.mp hh).2,A] using hbound h (mem_filter.mp hh).1
              _ = (F.card:ℝ) * (α^D.card * Real.exp (-(A + s j + 3))) := by simp
              _ ≤ Real.exp A * (α^D.card * Real.exp (-(A + s j + 3))) := mul_le_mul_of_nonneg_right hc (by positivity)
              _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring
       _ = α^D.card * ∑ j ∈ range (J+1), Real.exp (-(s j:ℝ)-3) := (mul_sum ..).symm
       _ ≤ α^D.card * (1/4) := mul_le_mul_of_nonneg_left (mc_series N J (by omega)) (pow_nonneg ha _)
       _ = _ := by ring

end OMA.E318H1Mc

theorem OMA.solution : OMA.R_Erdos318_erdos_318_parts_ii_R1.H1 :=
  OMA.E318H1R.main OMA.E318H1Mb.plage_b_holds OMA.E318H1Mc.plage_c_holds
