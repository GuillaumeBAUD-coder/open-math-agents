import FormalConjectures.ErdosProblems.«364»
import Mathlib

/-!
A short powerful triple gives an integral point on a split cubic. The
squarefree part of the product is the twist, and its cube divides the
square coordinate. An abc-type bound controls the twist and already
handles arithmetic progressions. The cubic height bound is needed for
unequal spacings.

The squarefree representation argument adapts Alewawa's reduction of
Erdos364.erdos_364.variants.strong.R1.H3. The pair estimate is related to
Alewawa's reduction of the R1.H1 step.
The arithmetic progression argument uses the same square-difference identity
as Broughan, ABC and k-th roots, Theorem 5.7, with a variable common difference.
https://www.kevinbroughan.nz/papers/abc01.pdf
-/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R2

/-- A gap form of abc for pairs whose prime support is covered by a
square divisor of their product. The factor R covers the prime support
of the endpoints, and the entire gap covers the remaining primes. -/
def H1 : Prop :=
  ∀ e : ℕ, 0 < e → ∃ A : ℕ, ∀ m n R : ℕ,
    0 < m → m < n → R ^ 2 ∣ m * n →
    (∀ p : ℕ, p.Prime → p ∣ m * n → p ∣ R) →
    n ^ e ≤ A * ((n - m) * R) ^ (e + 1)

/-- A polynomial height bound on a family of split cubics, restricted to
integral points with the indicated divisibility at the twist. -/
def H2 : Prop :=
  ∃ K B : ℕ, 0 < K ∧ ∀ d X Y h w : ℕ,
    0 < d → Squarefree d → 0 < X → 0 < h → h < w → w ≠ 2 * h →
    d ∣ X → d ^ 3 ∣ Y →
    ¬ (IsSquare X ∨ IsSquare (X + d * h) ∨ IsSquare (X + d * w)) →
    Y ^ 2 = X * (X + d * h) * (X + d * w) →
    X ≤ B * (d * w) ^ K

/-- Normalize by the gcd to obtain the gap estimate from the corresponding
coprime abc bound with any integer covering the prime support. -/
theorem gap_bound_of_coprime_abc
    (habc : ∀ e : ℕ, 0 < e → ∃ A : ℕ, ∀ x y S : ℕ,
      0 < x → 0 < y → x.Coprime y →
      (∀ p : ℕ, p.Prime → p ∣ x * y * (x + y) → p ∣ S) →
      (x + y) ^ e ≤ A * S ^ (e + 1)) : H1 := by
  intro e he
  obtain ⟨A, habc⟩ := habc e he
  refine ⟨A, ?_⟩
  intro m n R hm hmn _ hsupport
  let h := n - m
  let g := m.gcd h
  let x := m / g
  let y := h / g
  have hh : 0 < h := Nat.sub_pos_of_lt hmn
  have hg : 0 < g := Nat.gcd_pos_of_pos_left h hm
  have hx : g * x = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m h)
  have hy : g * y = h := Nat.mul_div_cancel' (Nat.gcd_dvd_right m h)
  have hx0 : 0 < x := Nat.div_pos (Nat.gcd_le_left h hm) hg
  have hy0 : 0 < y := Nat.div_pos (Nat.gcd_le_right m hh) hg
  have hn : g * (x + y) = n := by
    rw [Nat.mul_add, hx, hy]
    exact Nat.add_sub_of_le hmn.le
  have hxDvd : x ∣ m := ⟨g, by rw [← hx, mul_comm]⟩
  have hnDvd : x + y ∣ n := ⟨g, by rw [← hn, mul_comm]⟩
  have hs (p : ℕ) (hp : p.Prime) (hpd : p ∣ x * y * (x + y)) : p ∣ y * R := by
    rcases hp.dvd_mul.mp hpd with hxy | hsum
    · rcases hp.dvd_mul.mp hxy with hpx | hpy
      · exact (hsupport p hp ((hpx.trans hxDvd).mul_right n)).mul_left y
      · exact hpy.mul_right R
    · exact (hsupport p hp ((hsum.trans hnDvd).mul_left m)).mul_left y
  have hest := habc x y (y * R) hx0 hy0 (Nat.coprime_div_gcd_div_gcd hg) hs
  change n ^ e ≤ A * (h * R) ^ (e + 1)
  calc
    n ^ e = g ^ e * (x + y) ^ e := by rw [← hn, mul_pow]
    _ ≤ g ^ e * (A * (y * R) ^ (e + 1)) := Nat.mul_le_mul_left _ hest
    _ ≤ g ^ (e + 1) * (A * (y * R) ^ (e + 1)) := by
      exact Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by omega) (by omega))
    _ = A * (h * R) ^ (e + 1) := by
      rw [← hy, mul_assoc, mul_pow]
      ring

theorem squarefree_weight {n : ℕ} (hn : 0 < n) (hp : n.Powerful) :
    ∃ r u : ℕ, 0 < r ∧ 0 < u ∧ Squarefree r ∧ r ∣ u ∧ n = r * u ^ 2 := by
  obtain ⟨r, u, hr, hu, hprod, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hfact : n.factorization = 2 • u.factorization + r.factorization := by
    rw [← hprod, Nat.factorization_mul (pow_ne_zero 2 hu.ne') hr.ne',
      Nat.factorization_pow]
  have hdiv : r ∣ u := by
    rw [← Nat.factorization_le_iff_dvd hr.ne' hu.ne', Finsupp.le_iff]
    intro p hpSupport
    have hpr : p ∈ r.primeFactors := Nat.support_factorization r ▸ hpSupport
    obtain ⟨hprime, hpd, _⟩ := Nat.mem_primeFactors.mp hpr
    have hpn : p ∣ n := hprod ▸ (hpd.mul_left (u ^ 2))
    have htwo := (Nat.Prime.pow_dvd_iff_le_factorization hprime hn.ne').mp
      (hp p (Nat.mem_primeFactors.mpr ⟨hprime, hpn, hn.ne'⟩))
    have hone := (Nat.squarefree_iff_factorization_le_one hr.ne').mp hsf p
    have he : n.factorization p = 2 * u.factorization p + r.factorization p := by
      simp [hfact, Finsupp.add_apply, two_smul, two_mul]
    omega
  exact ⟨r, u, hr, hu, hsf, hdiv, by rw [← hprod, mul_comm]⟩

private theorem prime_dvd_root {p r u : ℕ} (hp : p.Prime) (hr : r ∣ u)
    (hd : p ∣ r * u ^ 2) : p ∣ u := by
  rcases hp.dvd_mul.mp hd with h | h
  · exact h.trans hr
  · exact hp.dvd_of_dvd_pow h

/-- The radical estimate controls the product of the two squarefree weights. -/
theorem pair_weight_bound (hABC : H1) (e : ℕ) (he : 0 < e) :
    ∃ A : ℕ, ∀ r s u v h : ℕ,
      0 < r → 0 < s → r ∣ u → s ∣ v → 0 < u → 0 < h →
      r * u ^ 2 + h = s * v ^ 2 →
      (r * s) ^ e ≤ A * (s * v ^ 2) * h ^ (2 * e + 1) := by
  obtain ⟨A, hABC⟩ := hABC (2 * e) (by omega)
  refine ⟨A, ?_⟩
  intro r s u v h hr hs hru hsv hu hh heq
  let m := r * u ^ 2
  let n := s * v ^ 2
  let R := u * v
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : m < n := by dsimp [m, n]; omega
  have hv : 0 < v := by
    by_contra! he
    have : v = 0 := by omega
    simp [n, this] at hn
  have hR : 0 < R := by dsimp [R]; positivity
  have hprod : m * n = (r * s) * R ^ 2 := by dsimp [m, n, R]; ring
  have hsupp (p : ℕ) (hp : p.Prime) (hd : p ∣ m * n) : p ∣ R := by
    rcases hp.dvd_mul.mp hd with hm' | hn'
    · exact (prime_dvd_root hp hru hm').mul_right v
    · exact (prime_dvd_root hp hsv hn').mul_left u
  have hgap : n - m = h := by dsimp [m, n]; omega
  have hRd : R ^ 2 ∣ m * n := by
    rw [hprod]
    exact dvd_mul_left _ _
  have hmain := hABC m n R hm hn hRd hsupp
  rw [hgap] at hmain
  have hRle : R ≤ n := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      R ^ 2 ≤ (r * s) * R ^ 2 := by
        have hrs : 1 ≤ r * s := Nat.mul_pos hr hs
        simpa using Nat.mul_le_mul_right (R ^ 2) hrs
      _ = m * n := hprod.symm
      _ ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hn.le
  have hscaled : (r * s) ^ e * R ^ (2 * e) ≤
      (A * h ^ (2 * e + 1) * R) * R ^ (2 * e) := by
    calc
      (r * s) ^ e * R ^ (2 * e) = (m * n) ^ e := by
        rw [hprod, pow_mul R 2 e, ← mul_pow]
      _ ≤ (n ^ 2) ^ e := by rw [sq]; gcongr
      _ ≤ A * (h * R) ^ (2 * e + 1) := by rwa [← pow_mul n 2 e]
      _ = (A * h ^ (2 * e + 1) * R) * R ^ (2 * e) := by
        rw [mul_pow, pow_succ R]
        ring
  exact (Nat.le_of_mul_le_mul_right hscaled (by positivity)).trans (by
    change A * h ^ (2 * e + 1) * R ≤ A * n * h ^ (2 * e + 1)
    rw [mul_right_comm A]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRle))

/-- For equal spacings the radical estimate applies to the outer product and
the square of the middle term, whose difference is the square of the gap. -/
theorem arithmetic_progression_bound (hABC : H1) :
    ∃ A : ℕ, ∀ a h : ℕ, 0 < a → 0 < h →
      a.Powerful → (a + h).Powerful → (a + 2 * h).Powerful →
      a ≤ A * h ^ 5 := by
  obtain ⟨A, hABC⟩ := hABC 19 (by decide)
  let B := max 1 A
  refine ⟨B, ?_⟩
  intro a h ha0 hh haPower hbPower hcPower
  let b := a + h
  let c := a + 2 * h
  have hb0 : 0 < b := by dsimp [b]; omega
  have hc0 : 0 < c := by dsimp [c]; omega
  obtain ⟨r, u, _, _, _, hru, ha⟩ := squarefree_weight ha0 haPower
  obtain ⟨s, v, _, _, _, hsv, hb⟩ := squarefree_weight hb0 hbPower
  obtain ⟨t, z, _, _, _, htz, hc⟩ := squarefree_weight hc0 hcPower
  let R := u * v * z
  have hdiff : a * c + h ^ 2 = b ^ 2 := by dsimp [b, c]; ring
  have hh2 : 0 < h ^ 2 := pow_pos hh _
  have hmn : a * c < b ^ 2 := by omega
  have hRdvd : R ^ 2 ∣ (a * c) * b ^ 2 := by
    refine ⟨r * s * t * b, ?_⟩
    calc
      (a * c) * b ^ 2 = (a * b * c) * b := by ring
      _ = R ^ 2 * (r * s * t * b) := by rw [ha, hb, hc]; dsimp [R]; ring
  have hsupp (p : ℕ) (hp : p.Prime) (hd : p ∣ (a * c) * b ^ 2) : p ∣ R := by
    rcases hp.dvd_mul.mp hd with hac | hb'
    · rcases hp.dvd_mul.mp hac with ha' | hc'
      · exact ((prime_dvd_root hp hru (ha ▸ ha')).mul_right v).mul_right z
      · exact (prime_dvd_root hp htz (hc ▸ hc')).mul_left (u * v)
    · exact ((prime_dvd_root hp hsv (hb ▸ hp.dvd_of_dvd_pow hb')).mul_left u).mul_right z
  have hgap : b ^ 2 - a * c = h ^ 2 := by omega
  have hmain := hABC (a * c) (b ^ 2) R (by positivity) hmn hRdvd hsupp
  rw [hgap] at hmain
  have hR : R ^ 2 ≤ b ^ 3 := by
    calc
      R ^ 2 ≤ a * b * c := by
        apply Nat.le_of_dvd (by positivity)
        exact ⟨r * s * t, by rw [ha, hb, hc]; dsimp [R]; ring⟩
      _ = (a * c) * b := by ring
      _ ≤ b ^ 2 * b := Nat.mul_le_mul_right _ hmn.le
      _ = b ^ 3 := by ring
  have hbig : b ^ 60 * b ^ 16 ≤ b ^ 60 * (A ^ 2 * h ^ 80) := by
    calc
      b ^ 60 * b ^ 16 = ((b ^ 2) ^ 19) ^ 2 := by ring
      _ ≤ (A * (h ^ 2 * R) ^ (19 + 1)) ^ 2 := Nat.pow_le_pow_left hmain _
      _ = A ^ 2 * h ^ 80 * (R ^ 2) ^ 20 := by ring
      _ ≤ A ^ 2 * h ^ 80 * (b ^ 3) ^ 20 := by gcongr
      _ = b ^ 60 * (A ^ 2 * h ^ 80) := by ring
  have hA : A ^ 2 ≤ B ^ 16 :=
    (Nat.pow_le_pow_left (le_max_right 1 A) 2).trans
      (pow_le_pow_right₀ (le_max_left 1 A) (by decide))
  have hlast : b ^ 16 ≤ (B * h ^ 5) ^ 16 := by
    calc
      b ^ 16 ≤ A ^ 2 * h ^ 80 := Nat.le_of_mul_le_mul_left hbig (by positivity)
      _ ≤ B ^ 16 * h ^ 80 := Nat.mul_le_mul_right _ hA
      _ = (B * h ^ 5) ^ 16 := by ring
  exact (show a ≤ b by dsimp [b]; omega).trans
    ((Nat.pow_le_pow_iff_left (by decide : 16 ≠ 0)).mp hlast)

/-- A pair with distinct squarefree weights can be searched by the
generalized Pell equation of discriminant r times s. -/
theorem weighted_pair_pell {r s u v h : ℕ} (hru : r ∣ u) (hsv : s ∣ v)
    (he : r * u ^ 2 + h = s * v ^ 2) :
    (r * u) ^ 2 + r * h = (r * s) * v ^ 2 ∧ r ^ 2 ∣ r * u ∧ s ∣ v := by
  refine ⟨?_, ?_, hsv⟩
  · calc
      (r * u) ^ 2 + r * h = r * (r * u ^ 2 + h) := by ring
      _ = (r * s) * v ^ 2 := by rw [he, mul_assoc]
  · simpa only [pow_two] using mul_dvd_mul (dvd_refl r) hru

/-- Multiplication by a Pell unit preserves the norm equation. -/
theorem pell_step {D N x y p q : ℤ} (hu : p ^ 2 - D * q ^ 2 = 1)
    (hn : x ^ 2 - D * y ^ 2 = N) :
    (p * x + D * q * y) ^ 2 - D * (q * x + p * y) ^ 2 = N := by
  calc
    _ = (p ^ 2 - D * q ^ 2) * (x ^ 2 - D * y ^ 2) := by ring
    _ = N := by rw [hu, hn, one_mul]

/-- The same gap controls the error in approximating a square root.
For fixed distinct weights this yields the two simultaneous
approximations to which Schmidt's theorem applies. -/
theorem weighted_pair_approximation {r s u v h α : ℝ} (hs : 0 < s) (hu : 0 < u)
    (hα : s * α ^ 2 = r) (he : r * u ^ 2 + h = s * v ^ 2) :
    (v / u - α) * (v / u + α) = h / (s * u ^ 2) := by
  have hd : s * (v ^ 2 - α ^ 2 * u ^ 2) = h := by
    calc
      s * (v ^ 2 - α ^ 2 * u ^ 2) = s * v ^ 2 - (s * α ^ 2) * u ^ 2 := by ring
      _ = h := by rw [hα, ← he]; ring
  calc
    (v / u - α) * (v / u + α) = (v ^ 2 - α ^ 2 * u ^ 2) / u ^ 2 := by
      field_simp [hu.ne']
      ring
    _ = (s * (v ^ 2 - α ^ 2 * u ^ 2)) / (s * u ^ 2) := by
      field_simp [hs.ne', hu.ne']
    _ = h / (s * u ^ 2) := by rw [hd]

/-- A shared part of two weights contributes its cube to their gap. -/
theorem shared_weight_cube_dvd_gap {r s u v h : ℕ} (hru : r ∣ u) (hsv : s ∣ v)
    (he : r * u ^ 2 + h = s * v ^ 2) : (r.gcd s) ^ 3 ∣ h := by
  have hr := Nat.gcd_dvd_left r s
  have hs := Nat.gcd_dvd_right r s
  have ha : (r.gcd s) ^ 3 ∣ r * u ^ 2 := by
    simpa only [pow_succ', pow_one] using mul_dvd_mul hr (pow_dvd_pow_of_dvd (hr.trans hru) 2)
  have hb : (r.gcd s) ^ 3 ∣ s * v ^ 2 := by
    simpa only [pow_succ', pow_one] using mul_dvd_mul hs (pow_dvd_pow_of_dvd (hs.trans hsv) 2)
  have hdiff := Nat.dvd_sub hb ha
  rwa [← he, Nat.add_sub_cancel_left] at hdiff

private theorem weight_dvd_twist_gcds {r s t d g : ℕ}
    (hr : Squarefree r) (hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hg : 0 < g)
    (he : g ^ 2 * d = r * s * t) :
    r ∣ d * r.gcd s * r.gcd t := by
  have hr0 := hr.ne_zero
  have hgs : 0 < r.gcd s := Nat.gcd_pos_of_pos_right r hs
  have hgt : 0 < r.gcd t := Nat.gcd_pos_of_pos_right r ht
  have htarget : 0 < d * r.gcd s * r.gcd t := by positivity
  rw [← Nat.factorization_le_iff_dvd hr0 htarget.ne', Finsupp.le_iff]
  intro p hpSupport
  have hpr : p ∈ r.primeFactors := Nat.support_factorization r ▸ hpSupport
  obtain ⟨hp, hpDvd, _⟩ := Nat.mem_primeFactors.mp hpr
  have hOne := Nat.factorization_eq_one_of_squarefree hr hp hpDvd
  rw [hOne]
  apply (hp.dvd_iff_one_le_factorization htarget.ne').mp
  by_cases hpd : p ∣ d
  · exact (hpd.mul_right (r.gcd s)).mul_right (r.gcd t)
  by_cases hps : p ∣ s
  · exact ((Nat.dvd_gcd hpDvd hps).mul_left d).mul_right (r.gcd t)
  by_cases hpt : p ∣ t
  · exact (Nat.dvd_gcd hpDvd hpt).mul_left (d * r.gcd s)
  exfalso
  have hVal := congrArg (fun n : ℕ => n.factorization p) he
  simp only [Nat.factorization_mul (pow_ne_zero 2 hg.ne') hd.ne',
    Nat.factorization_mul (mul_ne_zero hr0 hs.ne') ht.ne',
    Nat.factorization_mul hr0 hs.ne', Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, nsmul_eq_mul, hOne, Nat.factorization_eq_zero_of_not_dvd hpd,
    Nat.factorization_eq_zero_of_not_dvd hps, Nat.factorization_eq_zero_of_not_dvd hpt] at hVal
  omega

/-- Factoring the twist and the two gaps bounds the possible weight of the
entry shared by the two pairs. Use the pairs incident to each entry to
obtain the corresponding bound for all three weights. -/
theorem weight_cube_dvd_twist_gaps {r s t d g u v z h w : ℕ}
    (hr : Squarefree r) (hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hg : 0 < g)
    (he : g ^ 2 * d = r * s * t) (hru : r ∣ u) (hsv : s ∣ v) (htz : t ∣ z)
    (hpair : r * u ^ 2 + h = s * v ^ 2) (houter : r * u ^ 2 + w = t * z ^ 2) :
    r ^ 3 ∣ d ^ 3 * h * w := by
  calc
    r ^ 3 ∣ (d * r.gcd s * r.gcd t) ^ 3 :=
      pow_dvd_pow_of_dvd (weight_dvd_twist_gcds hr hs ht hd hg he) _
    _ = d ^ 3 * (r.gcd s) ^ 3 * (r.gcd t) ^ 3 := by simp [mul_pow]
    _ ∣ d ^ 3 * h * w :=
      mul_dvd_mul (mul_dvd_mul dvd_rfl (shared_weight_cube_dvd_gap hru hsv hpair))
        (shared_weight_cube_dvd_gap hru htz houter)

private theorem same_weight_gap {a b r u v : ℕ} (hr : 0 < r)
    (ha : a = r * u ^ 2) (hb : b = r * v ^ 2) (hab : a < b) :
    a < (b - a) ^ 2 := by
  have huv : u < v := by
    by_contra! h
    exact hab.not_ge (by rw [ha, hb]; gcongr)
  have hg : r * (u + 1) ^ 2 ≤ b := by
    rw [hb]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have he : b - a + a = b := Nat.sub_add_cancel hab.le
  have hu : r * u < b - a := by
    nlinarith [Nat.zero_le (r * u)]
  have hr2 : r ≤ r ^ 2 := by nlinarith
  calc
    a = r * u ^ 2 := ha
    _ ≤ r ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hr2
    _ = (r * u) ^ 2 := by ring
    _ < (b - a) ^ 2 := by gcongr

private theorem cancel_square_factor {x y Y : ℕ} (hx : 0 < x)
    (hs : IsSquare x) (he : Y ^ 2 = x * y) : IsSquare y := by
  obtain ⟨v, hv⟩ := hs
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [hv] at hx
  have hvY : v ∣ Y := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    ⟨y, by rw [he, hv, pow_two]⟩
  obtain ⟨u, hu⟩ := hvY
  have hprod : v ^ 2 * y = v ^ 2 * u ^ 2 := by rw [← mul_pow, ← hu, he, hv, pow_two]
  exact ⟨u, by simpa only [pow_two] using mul_left_cancel₀ (pow_ne_zero _ hv0) hprod⟩

private theorem square_product_gap {a b : ℕ} (hab : a < b)
    (hs : IsSquare (a * b)) : a < (b - a) ^ 2 := by
  obtain ⟨v, hv⟩ := hs
  have hidentity : (a + b) ^ 2 = (2 * v) ^ 2 + (b - a) ^ 2 := by
    zify [hab.le] at hv ⊢
    nlinarith
  have hpos : 0 < (b - a) ^ 2 := pow_pos (Nat.sub_pos_of_lt hab) _
  have hvab : 2 * v < a + b := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
    rw [hidentity]
    omega
  have hfactor : (a + b) ^ 2 =
      (a + b - 2 * v) * (a + b + 2 * v) + (2 * v) ^ 2 := by
    zify [hvab.le]
    ring
  have hle : a + b ≤ (a + b - 2 * v) * (a + b + 2 * v) := by
    simpa using Nat.mul_le_mul (show 1 ≤ a + b - 2 * v by omega)
      (show a + b ≤ a + b + 2 * v by omega)
  omega

private theorem other_factors_square {d a b c Y : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hs : IsSquare (d * a))
    (he : Y ^ 2 = (d * a) * (d * b) * (d * c)) : IsSquare (b * c) := by
  have hrest : IsSquare ((d * b) * (d * c)) :=
    cancel_square_factor (Nat.mul_pos hd ha) hs (by simpa [mul_assoc] using he)
  obtain ⟨v, hv⟩ := hrest
  apply cancel_square_factor (Y := v) (pow_pos hd 2) (IsSquare.sq d)
  rw [pow_two, ← hv]
  ring

/-- A square factor in the cubic forces two of the original entries to
have a square product. Their difference already bounds the smallest entry. -/
theorem split_cubic_square_factor_gap {d a b c Y : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hab : a < b) (hbc : b < c)
    (he : Y ^ 2 = (d * a) * (d * b) * (d * c))
    (hs : IsSquare (d * a) ∨ IsSquare (d * b) ∨ IsSquare (d * c)) :
    a < (c - a) ^ 2 := by
  rcases hs with hs | hs | hs
  · have hgap := square_product_gap hbc (other_factors_square hd ha hs he)
    exact (hab.trans hgap).trans_le (Nat.pow_le_pow_left (by omega) _)
  · have hrest : IsSquare (a * c) := other_factors_square hd (ha.trans hab) hs (by
      simpa only [mul_left_comm, mul_comm, mul_assoc] using he)
    exact square_product_gap (hab.trans hbc) hrest
  · have hrest : IsSquare (a * b) := other_factors_square hd (ha.trans (hab.trans hbc)) hs (by
      simpa only [mul_left_comm, mul_comm, mul_assoc] using he)
    exact (square_product_gap hab hrest).trans_le (Nat.pow_le_pow_left (by omega) _)

/-- The squarefree part of the product is a twist with a divisible
integral point. It is at most the product of the three weights. -/
theorem split_cubic_point {a b c r s t u v z : ℕ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hru : r ∣ u) (hsv : s ∣ v) (htz : t ∣ z)
    (ha : a = r * u ^ 2) (hb : b = s * v ^ 2) (hc : c = t * z ^ 2)
    (hab : a ≤ b) (hac : a ≤ c) :
    ∃ d Y : ℕ, 0 < d ∧ Squarefree d ∧ d ∣ r * s * t ∧ d ^ 3 ∣ Y ∧
      Y ^ 2 = (d * a) * (d * a + d * (b - a)) * (d * a + d * (c - a)) := by
  obtain ⟨d, g, hd, _, hprod, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (show 0 < r * s * t by positivity)
  have hdWeight : d ∣ r * s * t := ⟨g ^ 2, by rw [← hprod, mul_comm]⟩
  have hdu : d ∣ u * v * z := hdWeight.trans (mul_dvd_mul (mul_dvd_mul hru hsv) htz)
  obtain ⟨q, hq⟩ := hdu
  refine ⟨d, d ^ 3 * (g * q), hd, hsf, hdWeight, dvd_mul_right _ _, ?_⟩
  have hleft : d * a + d * (b - a) = d * b := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hab]
  have hright : d * a + d * (c - a) = d * c := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hac]
  have hscaled : d ^ 3 * (g * q) = d ^ 2 * (g * (u * v * z)) := by
    rw [hq]
    ring
  rw [hleft, hright, hscaled, ha, hb, hc]
  calc
    (d ^ 2 * (g * (u * v * z))) ^ 2 =
        d ^ 3 * (g ^ 2 * d) * (u * v * z) ^ 2 := by ring
    _ = (d * (r * u ^ 2)) * (d * (s * v ^ 2)) * (d * (t * z ^ 2)) := by
      rw [hprod]
      ring

/-- Translation removes the quadratic term from the cubic. Any common
divisor of the new first coordinate and the scaled square divides the
constant determined by the two spacings. -/
theorem translated_cubic_common_divisor {X Y a b g : ℤ}
    (he : Y ^ 2 = X * (X + a) * (X + b))
    (hX : g ∣ 3 * X + a + b) (hY : g ∣ 27 * Y ^ 2) :
    g ∣ (a + b) * (2 * a - b) * (2 * b - a) := by
  have hconstant :
      (3 * X + a + b) * ((3 * X + a + b) ^ 2 - 3 * (a ^ 2 - a * b + b ^ 2)) -
        27 * Y ^ 2 = (a + b) * (2 * a - b) * (2 * b - a) := by
    linear_combination -27 * he
  rw [← hconstant]
  exact dvd_sub (dvd_mul_of_dvd_left hX _) hY

/-- For each odd prime divisor of the translated first coordinate, the
negative of three times the spacing constant is a square modulo that prime. -/
theorem translated_cubic_square_residue {X Y a b : ℤ}
    (he : Y ^ 2 = X * (X + a) * (X + b)) :
    (9 * Y) ^ 2 ≡ -3 * ((a + b) * (2 * a - b) * (2 * b - a))
      [ZMOD 3 * X + a + b] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨9 * (a ^ 2 - a * b + b ^ 2) - 3 * (3 * X + a + b) ^ 2, ?_⟩
  linear_combination -81 * he

/-- Clearing denominators gives the short Weierstrass equation and an
explicit discriminant factorization for comparison with height bounds. -/
theorem split_cubic_short_weierstrass {X Y a b : ℤ}
    (he : Y ^ 2 = X * (X + a) * (X + b)) :
    let U := 3 * (3 * X + a + b)
    let A := -27 * (a ^ 2 - a * b + b ^ 2)
    let B := -27 * ((a + b) * (2 * a - b) * (2 * b - a))
    (27 * Y) ^ 2 = U ^ 3 + A * U + B ∧
      4 * A ^ 3 + 27 * B ^ 2 = -(3 ^ 12) * a ^ 2 * b ^ 2 * (a - b) ^ 2 := by
  dsimp only
  constructor
  · linear_combination 729 * he
  · ring

private theorem algebraic_bound (hABC : H1) (hcurve : H2) :
    ∃ C q : ℕ, 2 ≤ q ∧ ∀ a b c : ℕ, a < b → b < c →
      a.Powerful → b.Powerful → c.Powerful → a ≤ C * (c - a) ^ q := by
  obtain ⟨K, B, hK, hcurve⟩ := hcurve
  let e := 2 * K
  let p := 2 * e + 1
  obtain ⟨A, hpair⟩ := pair_weight_bound hABC e (by dsimp [e]; omega)
  obtain ⟨Aap, hprogression⟩ := arithmetic_progression_bound hABC
  let curveConstant := B ^ 4 * (2 * A) ^ 3
  let C := max 1 (max curveConstant Aap)
  let q := 3 * p + 2 * e
  have hq : 5 ≤ q := by dsimp [q, p, e]; omega
  have hCcurve : curveConstant ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCap : Aap ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, q, by omega, ?_⟩
  intro a b c hab hbc hpa hpb hpc
  let w := c - a
  have hw : 2 ≤ w := by dsimp [w]; omega
  have hmul : w ^ q ≤ C * w ^ q := by
    simpa using Nat.mul_le_mul_right (w ^ q) (le_max_left 1 (max curveConstant Aap))
  have hsmall {i : ℕ} (hi : i ≤ q) (h : a ≤ w ^ i) : a ≤ C * w ^ q :=
    h.trans ((pow_le_pow_right₀ (by omega : 1 ≤ w) hi).trans hmul)
  by_cases haz : a = 0
  · simp [haz]
  have ha0 : 0 < a := Nat.pos_of_ne_zero haz
  by_cases hwide : 2 * a < c
  · exact hsmall (i := 1) (by omega) (by simp [w]; omega)
  have hcmax : c ≤ 2 * a := by omega
  let h := b - a
  have hh : 0 < h := by dsimp [h]; omega
  have hhw : h < w := by dsimp [h, w]; omega
  by_cases hAP : w = 2 * h
  · have hb : a + h = b := by dsimp [h]; omega
    have hc : a + 2 * h = c := by dsimp [h, w] at *; omega
    have habound := hprogression a h ha0 hh hpa (hb.symm ▸ hpb) (hc.symm ▸ hpc)
    refine habound.trans ?_
    exact Nat.mul_le_mul hCap
      ((Nat.pow_le_pow_left hhw.le 5).trans (pow_le_pow_right₀ (by omega) hq))
  obtain ⟨r, u, hr, hu, _, hru, ha⟩ := squarefree_weight ha0 hpa
  obtain ⟨s, v, hs, hv, _, hsv, hb⟩ := squarefree_weight (ha0.trans hab) hpb
  obtain ⟨t, z, ht, _, _, htz, hc⟩ := squarefree_weight (ha0.trans (hab.trans hbc)) hpc
  by_cases hrs : r = s
  · subst s
    apply hsmall (show 2 ≤ q by omega)
    exact (same_weight_gap hr ha hb hab).le.trans
      (Nat.pow_le_pow_left (by dsimp [w]; omega) 2)
  by_cases hrt : r = t
  · subst t
    exact hsmall (show 2 ≤ q by omega) (same_weight_gap hr ha hc (hab.trans hbc)).le
  by_cases hst : s = t
  · subst t
    apply hsmall (show 2 ≤ q by omega)
    exact hab.le.trans ((same_weight_gap hs hb hc hbc).le.trans
      (Nat.pow_le_pow_left (by dsimp [w]; omega) 2))
  obtain ⟨d, Y, hd, hdf, hdWeight, hdY, hY⟩ :=
    split_cubic_point hr hs ht hru hsv htz ha hb hc hab.le (hab.trans hbc).le
  by_cases hsquare :
      IsSquare (d * a) ∨ IsSquare (d * a + d * h) ∨ IsSquare (d * a + d * w)
  · have hleft : d * a + d * h = d * b := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hab.le]
    have hright : d * a + d * w = d * c := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (hab.trans hbc).le]
    rw [hleft, hright] at hsquare hY
    exact hsmall (show 2 ≤ q by omega)
      (split_cubic_square_factor_gap hd ha0 hab hbc hY hsquare).le
  have hdX : d ∣ d * a := dvd_mul_right d a
  have hX := hcurve d (d * a) Y h w hd hdf (by positivity) hh hhw hAP hdX hdY hsquare hY
  have haCurve : a ≤ B * (d * w) ^ K := by
    have had : a ≤ d * a := by
      simpa using Nat.mul_le_mul_right a (show 1 ≤ d by omega)
    exact had.trans hX
  have habEq : r * u ^ 2 + h = s * v ^ 2 := by rw [← ha, ← hb]; dsimp [h]; omega
  have hacEq : r * u ^ 2 + w = t * z ^ 2 := by rw [← ha, ← hc]; dsimp [w]; omega
  have hbcEq : s * v ^ 2 + (c - b) = t * z ^ 2 := by rw [← hb, ← hc]; omega
  let M := 2 * A * a
  have habWeight : (r * s) ^ e ≤ M * h ^ p := by
    calc
      (r * s) ^ e ≤ A * (s * v ^ 2) * h ^ (2 * e + 1) :=
        hpair r s u v h hr hs hru hsv hu hh habEq
      _ = A * b * h ^ p := by rw [hb]
      _ ≤ A * (2 * a) * h ^ p := by gcongr; omega
      _ = M * h ^ p := by dsimp [M]; ring
  have hacWeight : (r * t) ^ e ≤ M * w ^ p := by
    calc
      (r * t) ^ e ≤ A * (t * z ^ 2) * w ^ (2 * e + 1) :=
        hpair r t u z w hr ht hru htz hu (by omega) hacEq
      _ = A * c * w ^ p := by rw [hc]
      _ ≤ A * (2 * a) * w ^ p := by gcongr
      _ = M * w ^ p := by dsimp [M]; ring
  have hbcWeight : (s * t) ^ e ≤ M * (c - b) ^ p := by
    calc
      (s * t) ^ e ≤ A * (t * z ^ 2) * (c - b) ^ (2 * e + 1) :=
        hpair s t v z (c - b) hs ht hsv htz hv (Nat.sub_pos_of_lt hbc) hbcEq
      _ = A * c * (c - b) ^ p := by rw [hc]
      _ ≤ A * (2 * a) * (c - b) ^ p := by gcongr
      _ = M * (c - b) ^ p := by dsimp [M]; ring
  have hdProduct : d ≤ r * s * t := Nat.le_of_dvd (by positivity) hdWeight
  have hdBound : d ^ (2 * e) ≤ M ^ 3 * (h * w * (c - b)) ^ p := by
    calc
      d ^ (2 * e) ≤ (r * s * t) ^ (2 * e) := Nat.pow_le_pow_left hdProduct _
      _ = (r * s) ^ e * (r * t) ^ e * (s * t) ^ e := by
        rw [pow_mul, show (r * s * t) ^ 2 = (r * s) * (r * t) * (s * t) by ring]
        simp only [mul_pow]
      _ ≤ (M * h ^ p) * (M * w ^ p) * (M * (c - b) ^ p) :=
        Nat.mul_le_mul (Nat.mul_le_mul habWeight hacWeight) hbcWeight
      _ = M ^ 3 * (h * w * (c - b)) ^ p := by simp only [mul_pow]; ring
  have hgapProduct : h * w * (c - b) ≤ w ^ 3 := by
    rw [pow_succ w 2, sq]
    exact Nat.mul_le_mul (Nat.mul_le_mul_right w hhw.le) (by dsimp [w]; omega)
  have hdSpan : d ^ (2 * e) ≤ M ^ 3 * w ^ (3 * p) := by
    apply hdBound.trans
    rw [pow_mul w 3 p]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgapProduct _)
  have haFourth : a ^ 4 ≤ a ^ 3 * (curveConstant * w ^ q) := by
    calc
      a ^ 4 ≤ (B * (d * w) ^ K) ^ 4 := Nat.pow_le_pow_left haCurve _
      _ = B ^ 4 * d ^ (2 * e) * w ^ (2 * e) := by
        rw [mul_pow, ← pow_mul, show K * 4 = 2 * e by dsimp [e]; omega, mul_pow, mul_assoc]
      _ ≤ B ^ 4 * (M ^ 3 * w ^ (3 * p)) * w ^ (2 * e) := by gcongr
      _ = a ^ 3 * (curveConstant * w ^ q) := by
        rw [show q = 3 * p + 2 * e from rfl, pow_add]
        dsimp [M, curveConstant]
        ring
  have haSmall : a ≤ curveConstant * w ^ q := by
    apply Nat.le_of_mul_le_mul_left (c := a ^ 3) ?_ (by positivity)
    calc
      a ^ 3 * a = a ^ 4 := by ring
      _ ≤ a ^ 3 * (curveConstant * w ^ q) := haFourth
  exact haSmall.trans (Nat.mul_le_mul_right _ hCcurve)

private theorem infinitely_many_powerful : (Set.ofPred Nat.Powerful).Infinite := by
  have hsquare (n : ℕ) : (n ^ 2).Powerful := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hd : p ∣ n := (hpp.dvd_mul.mp (by simpa [pow_two] using hpd)).elim id id
    simpa only [pow_two] using mul_dvd_mul hd hd
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => n ^ 2) ?_).mono
  · rintro _ ⟨n, rfl⟩
    exact hsquare n
  · intro x y h
    exact (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp h

theorem main : H1 → H2 → type_of% @Erdos364.erdos_364.variants.strong := by
  intro hpair hcurve
  obtain ⟨C, q, hq, hpoly⟩ := algebraic_bound hpair hcurve
  let j := C + q + 1
  have hj : 0 < j := by dsimp [j]; omega
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  refine ⟨1 / (j : ℝ), by positivity, ?_⟩
  intro k
  let a := Nat.nth Nat.Powerful k
  let b := Nat.nth Nat.Powerful (k + 1)
  let c := Nat.nth Nat.Powerful (k + 2)
  let w := c - a
  have hab : a < b := (Nat.nth_lt_nth infinitely_many_powerful).mpr (by omega)
  have hbc : b < c := (Nat.nth_lt_nth infinitely_many_powerful).mpr (by omega)
  have hw : 2 ≤ w := by dsimp [w]; omega
  have ha : a ≤ C * w ^ q := hpoly a b c hab hbc
    (Nat.nth_mem_of_infinite infinitely_many_powerful _)
    (Nat.nth_mem_of_infinite infinitely_many_powerful _)
    (Nat.nth_mem_of_infinite infinitely_many_powerful _)
  have hC : C ≤ (2 : ℕ) ^ C := Nat.lt_two_pow_self.le
  have hpow : a < w ^ j := by
    calc
      a ≤ C * w ^ q := ha
      _ ≤ w ^ C * w ^ q :=
        Nat.mul_le_mul_right _ (hC.trans (Nat.pow_le_pow_left hw _))
      _ = w ^ (C + q) := (pow_add _ _ _).symm
      _ < w ^ j := pow_lt_pow_right₀ (by omega) (by dsimp [j]; omega)
  have hpow' : (a : ℝ) < (w : ℝ) ^ j := by exact_mod_cast hpow
  have hreal : (a : ℝ) ^ (1 / (j : ℝ)) < (w : ℝ) := by
    calc
      (a : ℝ) ^ (1 / (j : ℝ)) < ((w : ℝ) ^ j) ^ (1 / (j : ℝ)) :=
        Real.rpow_lt_rpow (by positivity) hpow' (one_div_pos.mpr hj')
      _ = (w : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div,
          div_self hj'.ne', Real.rpow_one]
  change (a : ℝ) ^ (1 / (j : ℝ)) < (c : ℝ) - (a : ℝ)
  change (a : ℝ) ^ (1 / (j : ℝ)) < ((c - a : ℕ) : ℝ) at hreal
  rwa [Nat.cast_sub (hab.trans hbc).le] at hreal

end OMA.R_Erdos364_erdos_364_variants_strong_R2
