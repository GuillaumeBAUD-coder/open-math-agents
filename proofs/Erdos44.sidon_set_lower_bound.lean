import FormalConjectures.ErdosProblems.«44»

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand

open Finset Real

/- A Sidon set of size `√N / 2` inside `{1, …, N}`.

For `N < 16` the sets `{1}` and `{1, 2}` are large enough. For `N ≥ 16`, Bertrand's postulate
supplies an odd prime `p` with `⌊√N⌋ / 2 < p ≤ √N`. The prefix
`a ↦ 2 p a + (a² mod p) + 1` for `a = 0, …, ⌊√N⌋ / 2` lands in `{1, …, N}` and is Sidon,
because equal sums determine the sum and the product of the indices in `ZMod p`. -/

lemma sidon_singleton_one : IsSidon (({1} : Finset ℕ) : Set ℕ) := by decide

lemma sidon_pair_one_two : IsSidon (({1, 2} : Finset ℕ) : Set ℕ) := by decide

lemma bosePrefix_sidon {p k : ℕ} (hp : Nat.Prime p) (hk : k < p) (hp2 : p ≠ 2) :
    IsSidon
      (((Finset.range (k + 1)).image (fun a => 2 * p * a + (a * a) % p + 1) : Finset ℕ) :
        Set ℕ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rw [Finset.mem_coe, Finset.mem_image] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have ha_lt : a < p := by rw [Finset.mem_range] at ha; omega
  have hb_lt : b < p := by rw [Finset.mem_range] at hb; omega
  have hc_lt : c < p := by rw [Finset.mem_range] at hc; omega
  have hd_lt : d < p := by rw [Finset.mem_range] at hd; omega
  have hpos : 0 < p := hp.pos
  have hsum' :
      2 * p * (a + b) + ((a * a) % p + (b * b) % p) =
        2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by
    have hcancel :
        2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) =
          2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := by
      omega
    calc
      2 * p * (a + b) + ((a * a) % p + (b * b) % p)
          = 2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) := by ring
      _ = 2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := hcancel
      _ = 2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by ring
  have hσ : (a * a) % p + (b * b) % p < 2 * p := by
    have haσ : (a * a) % p < p := Nat.mod_lt _ hpos
    have hbσ : (b * b) % p < p := Nat.mod_lt _ hpos
    omega
  have hτ : (c * c) % p + (d * d) % p < 2 * p := by
    have hcτ : (c * c) % p < p := Nat.mod_lt _ hpos
    have hdτ : (d * d) % p < p := Nat.mod_lt _ hpos
    omega
  have htwo : 0 < 2 * p := by omega
  have hquot (q r : ℕ) (hr : r < 2 * p) :
      (r + (2 * p) * q) / (2 * p) = q := by
    rw [Nat.add_mul_div_left _ _ htwo, Nat.div_eq_of_lt hr, zero_add]
  have hidx : a + b = c + d := by
    have hleft := hquot (a + b) ((a * a) % p + (b * b) % p) hσ
    have hright := hquot (c + d) ((c * c) % p + (d * d) % p) hτ
    have hcomm :
        (a * a) % p + (b * b) % p + (2 * p) * (a + b) =
          (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by
      calc
        (a * a) % p + (b * b) % p + (2 * p) * (a + b)
            = (2 * p) * (a + b) + ((a * a) % p + (b * b) % p) := by ac_rfl
        _ = (2 * p) * (c + d) + ((c * c) % p + (d * d) % p) := hsum'
        _ = (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by ac_rfl
    rw [← hleft, ← hright, hcomm]
  have hres :
      (a * a) % p + (b * b) % p = (c * c) % p + (d * d) % p :=
    Nat.add_left_cancel (n := 2 * p * (a + b)) (by simpa [hidx] using hsum')
  have hsq :
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    calc
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2
          = (((a * a) % p : ℕ) : ZMod p) + (((b * b) % p : ℕ) : ZMod p) := by
            simp [pow_two, ZMod.natCast_mod]
      _ = ((((a * a) % p + (b * b) % p : ℕ) : ZMod p)) := by
            push_cast
            rfl
      _ = ((((c * c) % p + (d * d) % p : ℕ) : ZMod p)) := by
            exact congr_arg (Nat.cast : ℕ → ZMod p) hres
      _ = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
            simp [pow_two, ZMod.natCast_mod]
  have hsumZ : (a : ZMod p) + b = (c : ZMod p) + d := by
    have : ((a + b : ℕ) : ZMod p) = (c + d : ℕ) := congr_arg (Nat.cast : ℕ → ZMod p) hidx
    simpa [Nat.cast_add] using this
  have htwo_mul :
      (2 : ZMod p) * (a : ZMod p) * b = (2 : ZMod p) * (c : ZMod p) * d := by
    have hleft : (2 : ZMod p) * a * b = ((a : ZMod p) + b) ^ 2 - ((a : ZMod p) ^ 2 + b ^ 2) := by
      ring
    have hright : (2 : ZMod p) * c * d = ((c : ZMod p) + d) ^ 2 - ((c : ZMod p) ^ 2 + d ^ 2) := by
      ring
    rw [hleft, hright, hsumZ, hsq]
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_two, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have : 2 ≤ p := hp.two_le
    omega
  have hprod : (a : ZMod p) * b = (c : ZMod p) * d := by
    apply mul_left_cancel₀ htwo_ne
    simpa [mul_assoc, mul_left_comm, mul_comm] using htwo_mul
  have hfactor : ((c : ZMod p) - a) * ((c : ZMod p) - b) = 0 := by
    calc
      ((c : ZMod p) - a) * (c - b)
          = (c : ZMod p) ^ 2 - ((a : ZMod p) + b) * c + a * b := by ring
      _ = (c : ZMod p) ^ 2 - ((c : ZMod p) + d) * c + c * d := by rw [hsumZ, hprod]
      _ = 0 := by ring
  have hc_eq : (c : ZMod p) = a ∨ (c : ZMod p) = b := by
    rcases mul_eq_zero.mp hfactor with hca | hcb
    · left
      exact sub_eq_zero.mp hca
    · right
      exact sub_eq_zero.mp hcb
  have lift {x y : ℕ} (hx : x < p) (hy : y < p) (hxy : (x : ZMod p) = y) : x = y := by
    have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  rcases hc_eq with hca | hcb
  · have hac : a = c := lift ha_lt hc_lt hca.symm
    have hbd : b = d := by omega
    left
    subst hac
    subst hbd
    exact ⟨rfl, rfl⟩
  · have hab : b = c := lift hb_lt hc_lt hcb.symm
    have had : a = d := by omega
    right
    subst hab
    subst had
    exact ⟨rfl, rfl⟩

theorem OMA.solution : type_of% @Erdos44.sidon_set_lower_bound := by
  intro N hN
  by_cases h4 : N < 4
  · refine ⟨{1}, ?_, sidon_singleton_one, ?_⟩
    · simp [Finset.subset_iff, Finset.mem_Icc]
      omega
    · have hlt : Real.sqrt (N : ℝ) < 2 := by
        have hN4 : (N : ℝ) < 4 := by exact_mod_cast h4
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [← hsqrt4]
        exact Real.sqrt_lt_sqrt (by positivity) hN4
      have hcard : Real.sqrt (N : ℝ) / 2 < 1 := by linarith
      have : (({1} : Finset ℕ).card : ℝ) = 1 := by simp
      linarith
  · by_cases h16 : N < 16
    · refine ⟨{1, 2}, ?_, sidon_pair_one_two, ?_⟩
      · simp [Finset.subset_iff, Finset.mem_Icc]
        omega
      · have hlt : Real.sqrt (N : ℝ) < 4 := by
          have hN16 : (N : ℝ) < 16 := by exact_mod_cast h16
          have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
            rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          rw [← hsqrt16]
          exact Real.sqrt_lt_sqrt (by positivity) hN16
        have hhalf : Real.sqrt (N : ℝ) / 2 < 2 := by linarith
        have : (({1, 2} : Finset ℕ).card : ℝ) = 2 := by simp
        linarith
    · have hN16 : 16 ≤ N := Nat.le_of_not_lt h16
      let s := Nat.sqrt N
      have hs4 : 4 ≤ s := by
        have hsqrt16 : Nat.sqrt 16 = 4 := by simpa using (Nat.sqrt_eq 4)
        have : Nat.sqrt 16 ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN16
        simpa [s, hsqrt16] using this
      let k := s / 2
      have hk2 : 2 ≤ k := by omega
      obtain ⟨p, hp, hklt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega : k ≠ 0)
      have hp3 : 3 ≤ p := by omega
      have hp_le : p ≤ 2 * k - 1 := by
        have hpne : p ≠ 2 * k := by
          intro hpk
          have hdiv : 2 ∣ p := by
            rw [hpk]
            exact ⟨k, by ring⟩
          have hdisj := hp.eq_one_or_self_of_dvd 2 hdiv
          omega
        omega
      have hmul_le : p * (2 * k + 1) ≤ N := by
        have hstep : p * (2 * k + 1) ≤ (2 * k - 1) * (2 * k + 1) :=
          Nat.mul_le_mul_right _ hp_le
        have hident : (2 * k - 1) * (2 * k + 1) = 4 * k * k - 1 := by
          apply Nat.cast_injective (R := ℤ)
          rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ 2 * k by omega),
            Nat.cast_sub (show 1 ≤ 4 * k * k by nlinarith)]
          push_cast
          ring
        have hsq : 4 * k * k ≤ N := by
          have h2k : 2 * k ≤ s := by omega
          have hmul : 2 * k * (2 * k) ≤ s * s := Nat.mul_le_mul h2k h2k
          have heq : 4 * k * k = 2 * k * (2 * k) := by ring
          have hsN : s * s ≤ N := by simpa [Nat.pow_two] using (Nat.sqrt_le' N : s ^ 2 ≤ N)
          rw [heq]
          exact le_trans hmul hsN
        exact le_trans hstep (le_trans (by rw [hident]) (le_trans (Nat.sub_le _ _) hsq))
      let g : ℕ → ℕ := fun a => 2 * p * a + (a * a) % p + 1
      let A : Finset ℕ := (Finset.range (k + 1)).image g
      have hA_sub : A ⊆ Finset.Icc 1 N := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        have ha_le : a ≤ k := by
          rw [Finset.mem_range] at ha
          omega
        have hle : g a ≤ p * (2 * k + 1) := by
          have hmul : 2 * p * a ≤ 2 * p * k := Nat.mul_le_mul_left _ ha_le
          have hrest : (a * a) % p + 1 ≤ p := by
            have : (a * a) % p < p := Nat.mod_lt _ hp.pos
            omega
          have hsum : 2 * p * a + (a * a) % p + 1 ≤ 2 * p * k + p := by omega
          have heq : 2 * p * k + p = p * (2 * k + 1) := by ring
          simpa [g, heq] using hsum
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · change 1 ≤ 2 * p * a + (a * a) % p + 1
          omega
        · exact le_trans hle hmul_le
      have hsid : IsSidon (A : Set ℕ) := bosePrefix_sidon hp (by omega) (by omega)
      have hinj : Set.InjOn g (Finset.range (k + 1) : Set ℕ) := by
        intro a ha b hb hab
        have ha_lt : a < p := by
          have : a ∈ Finset.range (k + 1) := by simpa using ha
          rw [Finset.mem_range] at this
          omega
        have hb_lt : b < p := by
          have : b ∈ Finset.range (k + 1) := by simpa using hb
          rw [Finset.mem_range] at this
          omega
        by_contra hne
        have hstrict : a < b ∨ b < a := lt_or_gt_of_ne hne
        have hblow {x y : ℕ} (hx : x < y) (hxlt : x < p) (hylt : y < p)
            (heq : g x = g y) : False := by
          have hxy :
              2 * p * x + (x * x) % p = 2 * p * y + (y * y) % p := by
            simpa [g] using heq
          have hy : 2 * p * (x + 1) ≤ 2 * p * y := by
            exact Nat.mul_le_mul_left _ hx
          have hmodx : (x * x) % p < p := Nat.mod_lt _ hp.pos
          have hleft : 2 * p * x + (x * x) % p < 2 * p * x + p := by omega
          have hright : 2 * p * x + 2 * p ≤ 2 * p * y + (y * y) % p := by
            have : 2 * p * x + 2 * p = 2 * p * (x + 1) := by ring
            have : 2 * p * (x + 1) ≤ 2 * p * y := hy
            have : 2 * p * y ≤ 2 * p * y + (y * y) % p := Nat.le_add_right _ _
            omega
          omega
        rcases hstrict with hlt | hgt
        · exact hblow hlt ha_lt hb_lt hab
        · exact hblow hgt hb_lt ha_lt hab.symm
      have hcard : A.card = k + 1 := by
        rw [show A = (Finset.range (k + 1)).image g from rfl, Finset.card_image_of_injOn hinj]
        simp
      have hsqrt : Real.sqrt (N : ℝ) < (s : ℝ) + 1 := by
        simpa [s, Nat.cast_add, Nat.cast_one] using Real.real_sqrt_lt_nat_sqrt_succ (a := N)
      have hhalf : Real.sqrt (N : ℝ) / 2 < (k + 1 : ℝ) := by
        have hdiv : Real.sqrt (N : ℝ) / 2 < ((s : ℝ) + 1) / 2 :=
          div_lt_div_of_pos_right hsqrt (by norm_num)
        have hcmp : ((s : ℝ) + 1) / 2 ≤ (k + 1 : ℝ) := by
          rcases (show s = 2 * k ∨ s = 2 * k + 1 by omega) with hs | hs
          · have hsR : (s : ℝ) = 2 * (k : ℝ) := by simp [hs, Nat.cast_mul]
            rw [hsR]
            have hsplit : (2 * (k : ℝ) + 1) / 2 = (k : ℝ) + (1 : ℝ) / 2 := by ring
            have hle : (k : ℝ) + (1 : ℝ) / 2 ≤ (k : ℝ) + 1 := by linarith
            have hcast : (k : ℝ) + 1 = (k + 1 : ℝ) := by norm_cast
            linarith
          · have hsR : (s : ℝ) = 2 * (k : ℝ) + 1 := by norm_cast
            rw [hsR]
            have hsplit : (2 * (k : ℝ) + 1 + 1) / 2 = (k : ℝ) + 1 := by ring
            have hcast : (k : ℝ) + 1 = (k + 1 : ℝ) := by norm_cast
            linarith
        linarith
      have hreal : Real.sqrt (N : ℝ) / 2 ≤ (A.card : ℝ) := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        exact le_of_lt hhalf
      exact ⟨A, hA_sub, hsid, hreal⟩
