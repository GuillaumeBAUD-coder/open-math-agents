import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Proof of `OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H2`

For every `n ≥ 4`, `OeisA105751.a n ≠ 0`.

Proof outline:
1. Represent `∏_{k=0}^n (1 + k * i)` as an exact integer pair `seqPair n : ℤ × ℤ` so that
   `OeisA105751.a n = (seqPair n).2`.
2. Group consecutive factors into 8-factor blocks normalized by `4`, starting from `n = 0` (`B0`)
   and `n = 3` (`B3`, where `seqPair 3 = (-10, 0)`). Both `B0 m` and `B3 m` satisfy
   `Re ≡ 1 (mod 4)`, `Im ≡ 12 (mod 16)`, and `16 * d ∣ B (m + d) - B m`.
3. By dyadic doubling, any product of `L = 2^t * (2q + 1)` consecutive `B`-blocks satisfies
   `Re ≡ 1 (mod 4)`, `2^(t+2) ∣ Im`, and `¬ 2^(t+3) ∣ Im` (hence `Im ≠ 0`).
4. This directly gives `a n ≠ 0` for `n ≡ 0, 1, 2, 3 (mod 8)` (`n ≥ 8`). For `n ≡ 4, 5, 6, 7 (mod 8)`
   (`n ≥ 4`), factor out `2^(2x - 1)` from `2x - 1` 4-factor blocks and multiply by the exact
   trailing 4-factor block `T4` or `T7` whose normalized imaginary part is divisible by `8 * x`;
   vanishing of `a n` would force `2^(t+3) ∣ Im` of the `x`-block product, contradiction.
-/

namespace OMA105751R1H2

open Finset

def gmul (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

def gscale (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (c * p.1, c * p.2)

lemma gmul_assoc (p q r : ℤ × ℤ) : gmul (gmul p q) r = gmul p (gmul q r) := by
  ext <;> dsimp [gmul] <;> ring

lemma gmul_one (p : ℤ × ℤ) : gmul p (1, 0) = p := by
  ext <;> dsimp [gmul] <;> ring

lemma one_gmul (p : ℤ × ℤ) : gmul (1, 0) p = p := by
  ext <;> dsimp [gmul] <;> ring

lemma gscale_gmul (c d : ℤ) (p q : ℤ × ℤ) :
    gmul (gscale c p) (gscale d q) = gscale (c * d) (gmul p q) := by
  ext <;> dsimp [gmul, gscale] <;> ring

lemma gscale_mul_left (c : ℤ) (p q : ℤ × ℤ) :
    gmul (gscale c p) q = gscale c (gmul p q) := by
  ext <;> dsimp [gmul, gscale] <;> ring

lemma gscale_mul_right (c : ℤ) (p q : ℤ × ℤ) :
    gmul p (gscale c q) = gscale c (gmul p q) := by
  ext <;> dsimp [gmul, gscale] <;> ring

lemma gscale_gscale (c d : ℤ) (p : ℤ × ℤ) :
    gscale c (gscale d p) = gscale (c * d) p := by
  ext <;> dsimp [gscale] <;> ring

lemma gscale_inj {c : ℤ} (hc : c ≠ 0) {p q : ℤ × ℤ} (h : gscale c p = gscale c q) : p = q := by
  have h1 : c * p.1 = c * q.1 := congrArg Prod.fst h
  have h2 : c * p.2 = c * q.2 := congrArg Prod.snd h
  ext
  · exact mul_left_cancel₀ hc h1
  · exact mul_left_cancel₀ hc h2

def seqPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => gmul (seqPair n) (1, ((n + 1 : ℕ) : ℤ))

lemma prod_complex_eq_seqPair (n : ℕ) :
    ∏ k ∈ range (n + 1), ((1 : ℂ) + (k : ℂ) * Complex.I) =
      ((seqPair n).1 : ℂ) + ((seqPair n).2 : ℂ) * Complex.I := by
  induction n with
  | zero =>
    simp [seqPair]
  | succ n ih =>
    rw [prod_range_succ, ih]
    simp only [seqPair, gmul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, mul_one]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((seqPair n).2 : ℂ) * ((n + 1 : ℕ) : ℂ) * hI2

lemma a_eq_seqPair_snd (n : ℕ) : OeisA105751.a n = (seqPair n).2 := by
  unfold OeisA105751.a
  dsimp only
  rw [prod_complex_eq_seqPair]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

lemma seqPair_three : seqPair 3 = gscale (-10) (1, 0) := by
  rfl

def block4 (a : ℤ) : ℤ × ℤ :=
  gmul (gmul (gmul (1, a + 1) (1, a + 2)) (1, a + 3)) (1, a + 4)

def block8 (a : ℤ) : ℤ × ℤ :=
  gmul (block4 a) (block4 (a + 4))

lemma seqPair_add_four (n : ℕ) :
    seqPair (n + 4) = gmul (seqPair n) (block4 (n : ℤ)) := by
  simp only [seqPair, block4, gmul_assoc]
  have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have h2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have h3 : ((n + 3 : ℕ) : ℤ) = (n : ℤ) + 3 := by push_cast; ring
  have h4 : ((n + 4 : ℕ) : ℤ) = (n : ℤ) + 4 := by push_cast; ring
  rw [h1, h2, h3, h4]

lemma seqPair_add_eight (n : ℕ) :
    seqPair (n + 8) = gmul (seqPair n) (block8 (n : ℤ)) := by
  have h1 : n + 8 = (n + 4) + 4 := by omega
  rw [h1, seqPair_add_four, seqPair_add_four, gmul_assoc]
  have hcast : ((n + 4 : ℕ) : ℤ) = (n : ℤ) + 4 := by push_cast; ring
  rw [hcast]
  rfl

lemma block4_even (a : ℤ) : ∃ p : ℤ × ℤ, block4 a = gscale 2 p := by
  have hre : (block4 a).1 = -10 + 20 * a + 29 * a ^ 2 + 10 * a ^ 3 + a ^ 4 := by
    dsimp [block4, gmul]; ring
  have him : (block4 a).2 = 2 * (-20 - 33 * a - 15 * a ^ 2 - 2 * a ^ 3) := by
    dsimp [block4, gmul]; ring
  have hre2 : 2 ∣ (block4 a).1 := by
    rw [hre]
    rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine ⟨-5 + 20 * k + 58 * k ^ 2 + 40 * k ^ 3 + 8 * k ^ 4, ?_⟩; ring
    · refine ⟨25 + 112 * k + 130 * k ^ 2 + 56 * k ^ 3 + 8 * k ^ 4, ?_⟩; ring
  rcases hre2 with ⟨u, hu⟩
  refine ⟨(u, -20 - 33 * a - 15 * a ^ 2 - 2 * a ^ 3), ?_⟩
  ext
  · exact hu
  · exact him

lemma seqPair_add_four_mul (s : ℕ) (base : ℤ × ℤ) (hbase : seqPair s = base) :
    ∀ k : ℕ, ∃ p : ℤ × ℤ, seqPair (s + 4 * k) = gscale ((2 : ℤ) ^ k) (gmul base p) := by
  intro k
  induction k with
  | zero =>
    refine ⟨(1, 0), ?_⟩
    simp [hbase, gmul_one, gscale]
  | succ k ih =>
    rcases ih with ⟨p, hp⟩
    have hidx : s + 4 * (k + 1) = (s + 4 * k) + 4 := by omega
    rw [hidx, seqPair_add_four, hp]
    rcases block4_even ((s + 4 * k : ℕ) : ℤ) with ⟨q, hq⟩
    rw [hq, gscale_gmul, gmul_assoc]
    refine ⟨gmul p q, ?_⟩
    rw [pow_succ]

def gprod (F : ℕ → ℤ × ℤ) (m : ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | L + 1 => gmul (gprod F m L) (F (m + L))

lemma gprod_one (F : ℕ → ℤ × ℤ) (m : ℕ) : gprod F m 1 = F m := by
  simp [gprod, one_gmul]

lemma gprod_add (F : ℕ → ℤ × ℤ) (m a b : ℕ) :
    gprod F m (a + b) = gmul (gprod F m a) (gprod F (m + a) b) := by
  induction b with
  | zero =>
    simp [gprod, gmul_one]
  | succ b ih =>
    have h1 : a + (b + 1) = (a + b) + 1 := by omega
    have h2 : m + (a + b) = m + a + b := by omega
    rw [h1, gprod, ih, gprod, gmul_assoc, h2]

lemma gmul_sub_dvd {M : ℤ} {a b c d : ℤ × ℤ}
    (ha : M ∣ a.1 - c.1 ∧ M ∣ a.2 - c.2)
    (hb : M ∣ b.1 - d.1 ∧ M ∣ b.2 - d.2) :
    M ∣ (gmul a b).1 - (gmul c d).1 ∧ M ∣ (gmul a b).2 - (gmul c d).2 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  constructor
  · have h : (gmul a b).1 - (gmul c d).1 =
        (a.1 - c.1) * b.1 + c.1 * (b.1 - d.1) - ((a.2 - c.2) * b.2 + c.2 * (b.2 - d.2)) := by
      dsimp [gmul]; ring
    rw [h]
    exact dvd_sub
      (dvd_add (dvd_mul_of_dvd_left ha1 _) (dvd_mul_of_dvd_right hb1 _))
      (dvd_add (dvd_mul_of_dvd_left ha2 _) (dvd_mul_of_dvd_right hb2 _))
  · have h : (gmul a b).2 - (gmul c d).2 =
        (a.1 - c.1) * b.2 + c.1 * (b.2 - d.2) + ((a.2 - c.2) * b.1 + c.2 * (b.1 - d.1)) := by
      dsimp [gmul]; ring
    rw [h]
    exact dvd_add
      (dvd_add (dvd_mul_of_dvd_left ha1 _) (dvd_mul_of_dvd_right hb2 _))
      (dvd_add (dvd_mul_of_dvd_left ha2 _) (dvd_mul_of_dvd_right hb1 _))

lemma gprod_diff (F : ℕ → ℤ × ℤ) (M : ℤ) (m d : ℕ)
    (hF : ∀ j : ℕ, M ∣ (F (m + d + j)).1 - (F (m + j)).1 ∧
      M ∣ (F (m + d + j)).2 - (F (m + j)).2) :
    ∀ L : ℕ, M ∣ (gprod F (m + d) L).1 - (gprod F m L).1 ∧
      M ∣ (gprod F (m + d) L).2 - (gprod F m L).2 := by
  intro L
  induction L with
  | zero =>
    simp [gprod]
  | succ L ih =>
    simp only [gprod]
    exact gmul_sub_dvd ih (hF L)

lemma dyadic_doubling (F : ℕ → ℤ × ℤ)
    (hre : ∀ m, (F m).1 % 4 = 1)
    (him : ∀ m, (F m).2 % 16 = 12)
    (hdiff : ∀ m d : ℕ, 16 * (d : ℤ) ∣ (F (m + d)).1 - (F m).1 ∧
      16 * (d : ℤ) ∣ (F (m + d)).2 - (F m).2) :
    ∀ t m : ℕ,
      (gprod F m (2 ^ t)).1 % 4 = 1 ∧
      ((2 : ℤ) ^ (t + 2) ∣ (gprod F m (2 ^ t)).2) ∧
      ¬ ((2 : ℤ) ^ (t + 3) ∣ (gprod F m (2 ^ t)).2) := by
  intro t
  induction t with
  | zero =>
    intro m
    rw [pow_zero, gprod_one]
    have h12 := him m
    refine ⟨hre m, ?_, ?_⟩
    · refine ⟨(F m).2 / 4, ?_⟩; omega
    · intro h8
      rcases h8 with ⟨k, hk⟩
      omega
  | succ t ih =>
    intro m
    have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
    rw [hpow, gprod_add]
    set P1 := gprod F m (2 ^ t)
    set P2 := gprod F (m + 2 ^ t) (2 ^ t)
    rcases ih m with ⟨hre1, hdvd1, hndvd1⟩
    rcases ih (m + 2 ^ t) with ⟨hre2, hdvd2, hndvd2⟩
    rcases hdvd1 with ⟨y1, hy1⟩
    rcases hdvd2 with ⟨y2, hy2⟩
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (t + 2) := by positivity
    have hy1_odd : y1 % 2 = 1 := by
      rcases Int.even_or_odd y1 with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exfalso
        apply hndvd1
        refine ⟨k, ?_⟩
        rw [hy1]; ring
      · omega
    have hdiff_P := gprod_diff F (16 * ((2 ^ t : ℕ) : ℤ)) m (2 ^ t)
      (fun j => by
        have heq : m + 2 ^ t + j = m + j + 2 ^ t := by omega
        rw [heq]
        exact hdiff (m + j) (2 ^ t))
      (2 ^ t)
    have hdiff_im : (2 : ℤ) ^ (t + 4) ∣ P2.2 - P1.2 := by
      have h16 : (16 : ℤ) * ((2 ^ t : ℕ) : ℤ) = (2 : ℤ) ^ (t + 4) := by
        push_cast; ring
      rw [← h16]
      exact hdiff_P.2
    have hy_mod4 : 4 ∣ y2 - y1 := by
      rcases hdiff_im with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hmul : (2 : ℤ) ^ (t + 2) * (y2 - y1) = (2 : ℤ) ^ (t + 2) * (4 * k) := by
        have hpow4 : (2 : ℤ) ^ (t + 4) = (2 : ℤ) ^ (t + 2) * 4 := by ring
        calc (2 : ℤ) ^ (t + 2) * (y2 - y1) = P2.2 - P1.2 := by rw [hy1, hy2]; ring
          _ = (2 : ℤ) ^ (t + 4) * k := hk
          _ = (2 : ℤ) ^ (t + 2) * (4 * k) := by rw [hpow4]; ring
      exact mul_left_cancel₀ hpos.ne' hmul
    have hP1 : P1.1 = 4 * (P1.1 / 4) + 1 := by have : P1.1 % 4 = 1 := hre1; omega
    have hP2 : P2.1 = 4 * (P2.1 / 4) + 1 := by have : P2.1 % 4 = 1 := hre2; omega
    have him_eq : (gmul P1 P2).2 = (2 : ℤ) ^ (t + 2) * (P1.1 * y2 + P2.1 * y1) := by
      dsimp [gmul]; rw [hy1, hy2]; ring
    have hsum_form : ∃ m' : ℤ, P1.1 * y2 + P2.1 * y1 = 4 * m' + 2 := by
      rcases hy_mod4 with ⟨k, hk⟩
      have hy2_eq : y2 = y1 + 4 * k := by omega
      have hy1_eq : y1 = 2 * (y1 / 2) + 1 := by omega
      refine ⟨(P1.1 / 4) * (2 * (y1 / 2) + 1 + 4 * k) + k + (P2.1 / 4) * (2 * (y1 / 2) + 1) +
        (y1 / 2), ?_⟩
      calc P1.1 * y2 + P2.1 * y1
          = (4 * (P1.1 / 4) + 1) * ((2 * (y1 / 2) + 1) + 4 * k) +
            (4 * (P2.1 / 4) + 1) * (2 * (y1 / 2) + 1) := by rw [hy2_eq, ← hP1, ← hP2, ← hy1_eq]
        _ = 4 * ((P1.1 / 4) * (2 * (y1 / 2) + 1 + 4 * k) + k +
              (P2.1 / 4) * (2 * (y1 / 2) + 1) + (y1 / 2)) + 2 := by ring
    refine ⟨?_, ?_, ?_⟩
    · dsimp [gmul]
      have h4_1 : 4 ∣ P1.2 := by
        rw [hy1]
        have h4 : (2 : ℤ) ^ (t + 2) = 4 * (2 : ℤ) ^ t := by ring
        rw [h4]; exact ⟨(2 : ℤ) ^ t * y1, by ring⟩
      rcases h4_1 with ⟨c1, hc1⟩
      have hre_form : P1.1 * P2.1 - P1.2 * P2.2 =
          4 * ((P1.1 / 4) * (4 * (P2.1 / 4) + 1) + (P2.1 / 4) - c1 * P2.2) + 1 := by
        calc P1.1 * P2.1 - P1.2 * P2.2
            = (4 * (P1.1 / 4) + 1) * (4 * (P2.1 / 4) + 1) - (4 * c1) * P2.2 := by
              rw [← hP1, ← hP2, ← hc1]
          _ = 4 * ((P1.1 / 4) * (4 * (P2.1 / 4) + 1) + (P2.1 / 4) - c1 * P2.2) + 1 := by ring
      rw [hre_form]; omega
    · rcases hsum_form with ⟨m', hm'⟩
      refine ⟨2 * m' + 1, ?_⟩
      rw [him_eq, hm']; ring
    · intro hbad
      rcases hsum_form with ⟨m', hm'⟩
      rcases hbad with ⟨k, hk⟩
      have hpow4 : (2 : ℤ) ^ (t + 1 + 3) = (2 : ℤ) ^ (t + 2) * 4 := by ring
      have hmul : (2 : ℤ) ^ (t + 2) * (P1.1 * y2 + P2.1 * y1) = (2 : ℤ) ^ (t + 2) * (4 * k) := by
        rw [← him_eq, hk, hpow4]; ring
      have h4 : P1.1 * y2 + P2.1 * y1 = 4 * k := mul_left_cancel₀ hpos.ne' hmul
      omega

lemma general_blocks (F : ℕ → ℤ × ℤ)
    (hre : ∀ m, (F m).1 % 4 = 1)
    (him : ∀ m, (F m).2 % 16 = 12)
    (hdiff : ∀ m d : ℕ, 16 * (d : ℤ) ∣ (F (m + d)).1 - (F m).1 ∧
      16 * (d : ℤ) ∣ (F (m + d)).2 - (F m).2) :
    ∀ t q m : ℕ,
      (gprod F m (2 ^ t * (2 * q + 1))).1 % 4 = 1 ∧
      ((2 : ℤ) ^ (t + 2) ∣ (gprod F m (2 ^ t * (2 * q + 1))).2) ∧
      ¬ ((2 : ℤ) ^ (t + 3) ∣ (gprod F m (2 ^ t * (2 * q + 1))).2) := by
  intro t q
  induction q with
  | zero =>
    intro m
    simpa using dyadic_doubling F hre him hdiff t m
  | succ q ih =>
    intro m
    have hsplit : 2 ^ t * (2 * (q + 1) + 1) = 2 ^ (t + 1) + 2 ^ t * (2 * q + 1) := by ring
    rw [hsplit, gprod_add]
    set A := gprod F m (2 ^ (t + 1))
    set B := gprod F (m + 2 ^ (t + 1)) (2 ^ t * (2 * q + 1))
    rcases dyadic_doubling F hre him hdiff (t + 1) m with ⟨hreA, hdvdA, _⟩
    rcases ih (m + 2 ^ (t + 1)) with ⟨hreB, hdvdB, hndvdB⟩
    have hpowA : (2 : ℤ) ^ (t + 1 + 2) = (2 : ℤ) ^ (t + 3) := by ring
    rw [hpowA] at hdvdA
    have hdvdA' : (2 : ℤ) ^ (t + 3) ∣ A.2 := hdvdA
    have hdvdA2 : (2 : ℤ) ^ (t + 2) ∣ A.2 := by
      have h2 : (2 : ℤ) ^ (t + 3) = (2 : ℤ) ^ (t + 2) * 2 := by ring
      exact dvd_trans ⟨2, h2⟩ hdvdA'
    have hA1 : A.1 = 4 * (A.1 / 4) + 1 := by have : A.1 % 4 = 1 := hreA; omega
    have hB1 : B.1 = 4 * (B.1 / 4) + 1 := by have : B.1 % 4 = 1 := hreB; omega
    refine ⟨?_, ?_, ?_⟩
    · dsimp [gmul]
      have h4A : 4 ∣ A.2 := by
        have h4 : (2 : ℤ) ^ (t + 2) = 4 * (2 : ℤ) ^ t := by ring
        exact dvd_trans ⟨(2 : ℤ) ^ t, h4⟩ hdvdA2
      rcases h4A with ⟨c, hc⟩
      have hre_form : A.1 * B.1 - A.2 * B.2 =
          4 * ((A.1 / 4) * (4 * (B.1 / 4) + 1) + (B.1 / 4) - c * B.2) + 1 := by
        calc A.1 * B.1 - A.2 * B.2
            = (4 * (A.1 / 4) + 1) * (4 * (B.1 / 4) + 1) - (4 * c) * B.2 := by
              rw [← hA1, ← hB1, ← hc]
          _ = 4 * ((A.1 / 4) * (4 * (B.1 / 4) + 1) + (B.1 / 4) - c * B.2) + 1 := by ring
      rw [hre_form]; omega
    · dsimp [gmul]
      exact dvd_add (dvd_mul_of_dvd_right hdvdB _) (dvd_mul_of_dvd_left hdvdA2 _)
    · intro hbad
      dsimp [gmul] at hbad
      have hAB : (2 : ℤ) ^ (t + 3) ∣ A.1 * B.2 := by
        have hsub := dvd_sub hbad (dvd_mul_of_dvd_left hdvdA' B.1)
        simpa using hsub
      rcases hdvdB with ⟨y, hy⟩
      rcases hAB with ⟨k, hk⟩
      have hpos : (0 : ℤ) < (2 : ℤ) ^ (t + 2) := by positivity
      have hpow3 : (2 : ℤ) ^ (t + 3) = (2 : ℤ) ^ (t + 2) * 2 := by ring
      have hmul : (2 : ℤ) ^ (t + 2) * (A.1 * y) = (2 : ℤ) ^ (t + 2) * (2 * k) := by
        calc (2 : ℤ) ^ (t + 2) * (A.1 * y) = A.1 * ((2 : ℤ) ^ (t + 2) * y) := by ring
          _ = A.1 * B.2 := by rw [← hy]
          _ = (2 : ℤ) ^ (t + 3) * k := hk
          _ = (2 : ℤ) ^ (t + 2) * (2 * k) := by rw [hpow3]; ring
      have h2Ay : A.1 * y = 2 * k := mul_left_cancel₀ hpos.ne' hmul
      rcases Int.even_or_odd y with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · apply hndvdB
        refine ⟨j, ?_⟩
        rw [hy]; ring
      · have hodd : A.1 * (2 * j + 1) = 2 * (2 * (A.1 / 4) * (2 * j + 1) + j) + 1 := by
          calc A.1 * (2 * j + 1) = (4 * (A.1 / 4) + 1) * (2 * j + 1) := by rw [← hA1]
            _ = 2 * (2 * (A.1 / 4) * (2 * j + 1) + j) + 1 := by ring
        omega

lemma exists_two_pow_mul_odd (n : ℕ) (hn : 0 < n) :
    ∃ t q : ℕ, n = 2 ^ t * (2 * q + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hodd : n % 2 = 1
    · exact ⟨0, n / 2, by omega⟩
    · have hhalf_pos : 0 < n / 2 := by omega
      have hhalf_lt : n / 2 < n := by omega
      rcases ih (n / 2) hhalf_lt hhalf_pos with ⟨t, q, hq⟩
      refine ⟨t + 1, q, ?_⟩
      have hn2 : n = 2 * (n / 2) := by omega
      rw [hn2, hq]
      ring

def B0 (m : ℕ) : ℤ × ℤ :=
  let z : ℤ := (m : ℤ)
  (-13975 - 139680 * z - 134528 * z ^ 2 + 2967552 * z ^ 3 + 14672896 * z ^ 4 +
     30965760 * z ^ 5 + 33947648 * z ^ 6 + 18874368 * z ^ 7 + 4194304 * z ^ 8,
   -11700 - 299440 * z - 2515968 * z ^ 2 - 10103296 * z ^ 3 - 21934080 * z ^ 4 -
     26378240 * z ^ 5 - 16515072 * z ^ 6 - 4194304 * z ^ 7)

def B3 (m : ℕ) : ℤ × ℤ :=
  let z : ℤ := (m : ℤ)
  (706745 + 9081120 * z + 45249664 * z ^ 2 + 119132160 * z ^ 3 + 184984576 * z ^ 4 +
     175472640 * z ^ 5 + 100007936 * z ^ 6 + 31457280 * z ^ 7 + 4194304 * z ^ 8,
   -1690260 - 14500144 * z - 51851520 * z ^ 2 - 100420096 * z ^ 3 - 113971200 * z ^ 4 -
     75923456 * z ^ 5 - 27525120 * z ^ 6 - 4194304 * z ^ 7)

lemma block8_B0 (m : ℕ) : block8 ((8 * m : ℕ) : ℤ) = gscale 4 (B0 m) := by
  ext <;> dsimp [block8, block4, gmul, gscale, B0] <;> ring

lemma block8_B3 (m : ℕ) : block8 ((8 * m + 3 : ℕ) : ℤ) = gscale 4 (B3 m) := by
  ext <;> dsimp [block8, block4, gmul, gscale, B3] <;> ring

lemma poly_diff_dvd_16 {a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℤ} (z d : ℤ) :
    16 * d ∣
      ((a0 + 16 * a1 * (z + d) + 16 * a2 * (z + d) ^ 2 + 16 * a3 * (z + d) ^ 3 +
        16 * a4 * (z + d) ^ 4 + 16 * a5 * (z + d) ^ 5 + 16 * a6 * (z + d) ^ 6 +
        16 * a7 * (z + d) ^ 7 + 16 * a8 * (z + d) ^ 8) -
       (a0 + 16 * a1 * z + 16 * a2 * z ^ 2 + 16 * a3 * z ^ 3 +
        16 * a4 * z ^ 4 + 16 * a5 * z ^ 5 + 16 * a6 * z ^ 6 +
        16 * a7 * z ^ 7 + 16 * a8 * z ^ 8)) := by
  refine ⟨a1 + a2 * (2 * z + d) + a3 * (3 * z ^ 2 + 3 * z * d + d ^ 2) +
      a4 * (4 * z ^ 3 + 6 * z ^ 2 * d + 4 * z * d ^ 2 + d ^ 3) +
      a5 * (5 * z ^ 4 + 10 * z ^ 3 * d + 10 * z ^ 2 * d ^ 2 + 5 * z * d ^ 3 + d ^ 4) +
      a6 * (6 * z ^ 5 + 15 * z ^ 4 * d + 20 * z ^ 3 * d ^ 2 + 15 * z ^ 2 * d ^ 3 +
        6 * z * d ^ 4 + d ^ 5) +
      a7 * (7 * z ^ 6 + 21 * z ^ 5 * d + 35 * z ^ 4 * d ^ 2 + 35 * z ^ 3 * d ^ 3 +
        21 * z ^ 2 * d ^ 4 + 7 * z * d ^ 5 + d ^ 6) +
      a8 * (8 * z ^ 7 + 28 * z ^ 6 * d + 56 * z ^ 5 * d ^ 2 + 70 * z ^ 4 * d ^ 3 +
        56 * z ^ 3 * d ^ 4 + 28 * z ^ 2 * d ^ 5 + 8 * z * d ^ 6 + d ^ 7), ?_⟩
  ring

lemma B0_re_mod4 (m : ℕ) : (B0 m).1 % 4 = 1 := by
  dsimp [B0]
  set z : ℤ := (m : ℤ)
  have h : -13975 - 139680 * z - 134528 * z ^ 2 + 2967552 * z ^ 3 + 14672896 * z ^ 4 +
      30965760 * z ^ 5 + 33947648 * z ^ 6 + 18874368 * z ^ 7 + 4194304 * z ^ 8 =
      1 + 4 * (-3494 - 34920 * z - 33632 * z ^ 2 + 741888 * z ^ 3 + 3668224 * z ^ 4 +
        7741440 * z ^ 5 + 8486912 * z ^ 6 + 4718592 * z ^ 7 + 1048576 * z ^ 8) := by ring
  rw [h]; omega

lemma B0_im_mod16 (m : ℕ) : (B0 m).2 % 16 = 12 := by
  dsimp [B0]
  set z : ℤ := (m : ℤ)
  have h : -11700 - 299440 * z - 2515968 * z ^ 2 - 10103296 * z ^ 3 - 21934080 * z ^ 4 -
      26378240 * z ^ 5 - 16515072 * z ^ 6 - 4194304 * z ^ 7 =
      12 + 16 * (-732 - 18715 * z - 157248 * z ^ 2 - 631456 * z ^ 3 - 1370880 * z ^ 4 -
        1648640 * z ^ 5 - 1032192 * z ^ 6 - 262144 * z ^ 7) := by ring
  rw [h]; omega

lemma B0_diff (m d : ℕ) :
    16 * (d : ℤ) ∣ (B0 (m + d)).1 - (B0 m).1 ∧
    16 * (d : ℤ) ∣ (B0 (m + d)).2 - (B0 m).2 := by
  constructor
  · have h := poly_diff_dvd_16 (a0 := -13975) (a1 := -8730) (a2 := -8408) (a3 := 185472)
      (a4 := 917056) (a5 := 1935360) (a6 := 2121728) (a7 := 1179648) (a8 := 262144)
      (m : ℤ) (d : ℤ)
    have heq : (B0 (m + d)).1 - (B0 m).1 =
        (-13975 + 16 * -8730 * ((m : ℤ) + (d : ℤ)) + 16 * -8408 * ((m : ℤ) + (d : ℤ)) ^ 2 +
          16 * 185472 * ((m : ℤ) + (d : ℤ)) ^ 3 + 16 * 917056 * ((m : ℤ) + (d : ℤ)) ^ 4 +
          16 * 1935360 * ((m : ℤ) + (d : ℤ)) ^ 5 + 16 * 2121728 * ((m : ℤ) + (d : ℤ)) ^ 6 +
          16 * 1179648 * ((m : ℤ) + (d : ℤ)) ^ 7 + 16 * 262144 * ((m : ℤ) + (d : ℤ)) ^ 8) -
        (-13975 + 16 * -8730 * (m : ℤ) + 16 * -8408 * (m : ℤ) ^ 2 +
          16 * 185472 * (m : ℤ) ^ 3 + 16 * 917056 * (m : ℤ) ^ 4 +
          16 * 1935360 * (m : ℤ) ^ 5 + 16 * 2121728 * (m : ℤ) ^ 6 +
          16 * 1179648 * (m : ℤ) ^ 7 + 16 * 262144 * (m : ℤ) ^ 8) := by
      dsimp [B0]; ring
    rwa [heq]
  · have h := poly_diff_dvd_16 (a0 := -11700) (a1 := -18715) (a2 := -157248) (a3 := -631456)
      (a4 := -1370880) (a5 := -1648640) (a6 := -1032192) (a7 := -262144) (a8 := 0)
      (m : ℤ) (d : ℤ)
    have heq : (B0 (m + d)).2 - (B0 m).2 =
        (-11700 + 16 * -18715 * ((m : ℤ) + (d : ℤ)) + 16 * -157248 * ((m : ℤ) + (d : ℤ)) ^ 2 +
          16 * -631456 * ((m : ℤ) + (d : ℤ)) ^ 3 + 16 * -1370880 * ((m : ℤ) + (d : ℤ)) ^ 4 +
          16 * -1648640 * ((m : ℤ) + (d : ℤ)) ^ 5 + 16 * -1032192 * ((m : ℤ) + (d : ℤ)) ^ 6 +
          16 * -262144 * ((m : ℤ) + (d : ℤ)) ^ 7 + 16 * 0 * ((m : ℤ) + (d : ℤ)) ^ 8) -
        (-11700 + 16 * -18715 * (m : ℤ) + 16 * -157248 * (m : ℤ) ^ 2 +
          16 * -631456 * (m : ℤ) ^ 3 + 16 * -1370880 * (m : ℤ) ^ 4 +
          16 * -1648640 * (m : ℤ) ^ 5 + 16 * -1032192 * (m : ℤ) ^ 6 +
          16 * -262144 * (m : ℤ) ^ 7 + 16 * 0 * (m : ℤ) ^ 8) := by
      dsimp [B0]; ring
    rwa [heq]

lemma B3_re_mod4 (m : ℕ) : (B3 m).1 % 4 = 1 := by
  dsimp [B3]
  set z : ℤ := (m : ℤ)
  have h : 706745 + 9081120 * z + 45249664 * z ^ 2 + 119132160 * z ^ 3 + 184984576 * z ^ 4 +
      175472640 * z ^ 5 + 100007936 * z ^ 6 + 31457280 * z ^ 7 + 4194304 * z ^ 8 =
      1 + 4 * (176686 + 2270280 * z + 11312416 * z ^ 2 + 29783040 * z ^ 3 + 46246144 * z ^ 4 +
        43868160 * z ^ 5 + 25001984 * z ^ 6 + 7864320 * z ^ 7 + 1048576 * z ^ 8) := by ring
  rw [h]; omega

lemma B3_im_mod16 (m : ℕ) : (B3 m).2 % 16 = 12 := by
  dsimp [B3]
  set z : ℤ := (m : ℤ)
  have h : -1690260 - 14500144 * z - 51851520 * z ^ 2 - 100420096 * z ^ 3 - 113971200 * z ^ 4 -
      75923456 * z ^ 5 - 27525120 * z ^ 6 - 4194304 * z ^ 7 =
      12 + 16 * (-105642 - 906259 * z - 3240720 * z ^ 2 - 6276256 * z ^ 3 - 7123200 * z ^ 4 -
        4745216 * z ^ 5 - 1720320 * z ^ 6 - 262144 * z ^ 7) := by ring
  rw [h]; omega

lemma B3_diff (m d : ℕ) :
    16 * (d : ℤ) ∣ (B3 (m + d)).1 - (B3 m).1 ∧
    16 * (d : ℤ) ∣ (B3 (m + d)).2 - (B3 m).2 := by
  constructor
  · have h := poly_diff_dvd_16 (a0 := 706745) (a1 := 567570) (a2 := 2828104) (a3 := 7445760)
      (a4 := 11561536) (a5 := 10967040) (a6 := 6250496) (a7 := 1966080) (a8 := 262144)
      (m : ℤ) (d : ℤ)
    have heq : (B3 (m + d)).1 - (B3 m).1 =
        (706745 + 16 * 567570 * ((m : ℤ) + (d : ℤ)) + 16 * 2828104 * ((m : ℤ) + (d : ℤ)) ^ 2 +
          16 * 7445760 * ((m : ℤ) + (d : ℤ)) ^ 3 + 16 * 11561536 * ((m : ℤ) + (d : ℤ)) ^ 4 +
          16 * 10967040 * ((m : ℤ) + (d : ℤ)) ^ 5 + 16 * 6250496 * ((m : ℤ) + (d : ℤ)) ^ 6 +
          16 * 1966080 * ((m : ℤ) + (d : ℤ)) ^ 7 + 16 * 262144 * ((m : ℤ) + (d : ℤ)) ^ 8) -
        (706745 + 16 * 567570 * (m : ℤ) + 16 * 2828104 * (m : ℤ) ^ 2 +
          16 * 7445760 * (m : ℤ) ^ 3 + 16 * 11561536 * (m : ℤ) ^ 4 +
          16 * 10967040 * (m : ℤ) ^ 5 + 16 * 6250496 * (m : ℤ) ^ 6 +
          16 * 1966080 * (m : ℤ) ^ 7 + 16 * 262144 * (m : ℤ) ^ 8) := by
      dsimp [B3]
    rwa [heq]
  · have h := poly_diff_dvd_16 (a0 := -1690260) (a1 := -906259) (a2 := -3240720) (a3 := -6276256)
      (a4 := -7123200) (a5 := -4745216) (a6 := -1720320) (a7 := -262144) (a8 := 0)
      (m : ℤ) (d : ℤ)
    have heq : (B3 (m + d)).2 - (B3 m).2 =
        (-1690260 + 16 * -906259 * ((m : ℤ) + (d : ℤ)) + 16 * -3240720 * ((m : ℤ) + (d : ℤ)) ^ 2 +
          16 * -6276256 * ((m : ℤ) + (d : ℤ)) ^ 3 + 16 * -7123200 * ((m : ℤ) + (d : ℤ)) ^ 4 +
          16 * -4745216 * ((m : ℤ) + (d : ℤ)) ^ 5 + 16 * -1720320 * ((m : ℤ) + (d : ℤ)) ^ 6 +
          16 * -262144 * ((m : ℤ) + (d : ℤ)) ^ 7 + 16 * 0 * ((m : ℤ) + (d : ℤ)) ^ 8) -
        (-1690260 + 16 * -906259 * (m : ℤ) + 16 * -3240720 * (m : ℤ) ^ 2 +
          16 * -6276256 * (m : ℤ) ^ 3 + 16 * -7123200 * (m : ℤ) ^ 4 +
          16 * -4745216 * (m : ℤ) ^ 5 + 16 * -1720320 * (m : ℤ) ^ 6 +
          16 * -262144 * (m : ℤ) ^ 7 + 16 * 0 * (m : ℤ) ^ 8) := by
      dsimp [B3]; ring
    rwa [heq]

lemma seqPair_eight_mul (q : ℕ) :
    seqPair (8 * q) = gscale ((4 : ℤ) ^ q) (gprod B0 0 q) := by
  induction q with
  | zero =>
    simp [seqPair, gprod, gscale]
  | succ q ih =>
    have h1 : 8 * (q + 1) = 8 * q + 8 := by omega
    rw [h1, seqPair_add_eight, ih, block8_B0, gscale_gmul, pow_succ]
    simp [gprod]

lemma seqPair_eight_mul_add_three (q : ℕ) :
    seqPair (8 * q + 3) = gscale (-10 * (4 : ℤ) ^ q) (gprod B3 0 q) := by
  induction q with
  | zero =>
    simp [seqPair_three, gprod]
  | succ q ih =>
    have h1 : 8 * (q + 1) + 3 = (8 * q + 3) + 8 := by omega
    rw [h1, seqPair_add_eight, ih, block8_B3, gscale_gmul]
    have hpow : -10 * (4 : ℤ) ^ q * 4 = -10 * (4 : ℤ) ^ (q + 1) := by rw [pow_succ]; ring
    rw [hpow]
    simp [gprod]

def T4 (x : ℤ) : ℤ × ℤ :=
  (-5 + 48 * x + 160 * x ^ 2 - 1536 * x ^ 3 + 2048 * x ^ 4,
   8 * x * (-9 + 72 * x - 128 * x ^ 2))

def T7 (x : ℤ) : ℤ × ℤ :=
  (-5 - 48 * x + 160 * x ^ 2 + 1536 * x ^ 3 + 2048 * x ^ 4,
   8 * x * (-9 - 72 * x - 128 * x ^ 2))

lemma block4_T4 (x : ℕ) (hx : 1 ≤ x) :
    block4 ((8 * x - 4 : ℕ) : ℤ) = gscale 2 (T4 (x : ℤ)) := by
  have hcast : ((8 * x - 4 : ℕ) : ℤ) = 8 * (x : ℤ) - 4 := by omega
  rw [hcast]
  ext <;> dsimp [block4, gmul, gscale, T4] <;> ring

lemma block4_T7 (x : ℕ) (hx : 1 ≤ x) :
    block4 ((8 * x - 1 : ℕ) : ℤ) = gscale 2 (T7 (x : ℤ)) := by
  have hcast : ((8 * x - 1 : ℕ) : ℤ) = 8 * (x : ℤ) - 1 := by omega
  rw [hcast]
  ext <;> dsimp [block4, gmul, gscale, T7] <;> ring

lemma gprod_B0_props (x : ℕ) (hx : 0 < x) :
    ∃ t : ℕ, ((2 : ℤ) ^ t ∣ (x : ℤ)) ∧
      (gprod B0 0 x).1 % 4 = 1 ∧
      ((2 : ℤ) ^ (t + 2) ∣ (gprod B0 0 x).2) ∧
      ¬ ((2 : ℤ) ^ (t + 3) ∣ (gprod B0 0 x).2) := by
  rcases exists_two_pow_mul_odd x hx with ⟨t, q, hq⟩
  refine ⟨t, ⟨2 * (q : ℤ) + 1, by exact_mod_cast hq⟩, ?_⟩
  rw [hq]
  exact general_blocks B0 B0_re_mod4 B0_im_mod16 B0_diff t q 0

lemma gprod_B3_props (x : ℕ) (hx : 0 < x) :
    ∃ t : ℕ, ((2 : ℤ) ^ t ∣ (x : ℤ)) ∧
      (gprod B3 0 x).1 % 4 = 1 ∧
      ((2 : ℤ) ^ (t + 2) ∣ (gprod B3 0 x).2) ∧
      ¬ ((2 : ℤ) ^ (t + 3) ∣ (gprod B3 0 x).2) := by
  rcases exists_two_pow_mul_odd x hx with ⟨t, q, hq⟩
  refine ⟨t, ⟨2 * (q : ℤ) + 1, by exact_mod_cast hq⟩, ?_⟩
  rw [hq]
  exact general_blocks B3 B3_re_mod4 B3_im_mod16 B3_diff t q 0

lemma seqPair_four_mod_eight (q : ℕ) :
    ∃ U V : ℤ, seqPair (8 * q + 4) = gscale ((2 : ℤ) ^ (2 * q + 1)) (U, V) ∧
      U % 2 = 1 ∧ V % 2 = 0 ∧ V ≠ 0 := by
  set x := q + 1
  have hx : 1 ≤ x := by omega
  have hidx : 8 * q + 4 = 0 + 4 * (2 * q + 1) := by omega
  rcases seqPair_add_four_mul 0 (1, 0) rfl (2 * q + 1) with ⟨⟨U, V⟩, hUV⟩
  rw [← hidx, one_gmul] at hUV
  have h8x : seqPair (8 * x) = gscale ((4 : ℤ) ^ x) (gmul (U, V) (T4 (x : ℤ))) := by
    have hstep : 8 * x = (8 * q + 4) + 4 := by omega
    rw [hstep, seqPair_add_four, hUV]
    have h4 : 8 * q + 4 = 8 * x - 4 := by omega
    rw [h4, block4_T4 x hx, gscale_gmul]
    have hpow : (2 : ℤ) ^ (2 * q + 1) * 2 = (4 : ℤ) ^ x := by
      have : (4 : ℤ) ^ x = ((2 : ℤ) ^ 2) ^ (q + 1) := by rfl
      rw [this, ← pow_mul]; ring
    rw [hpow]
  have hGeq : gprod B0 0 x = gmul (U, V) (T4 (x : ℤ)) := by
    apply gscale_inj (c := (4 : ℤ) ^ x) (by positivity)
    rw [← seqPair_eight_mul x, h8x]
  rcases gprod_B0_props x (by omega) with ⟨t, h2tx, hreG, hdvdG, hndvdG⟩
  rw [hGeq] at hreG hdvdG hndvdG
  have hT4_re_odd : (T4 (x : ℤ)).1 % 2 = 1 := by
    dsimp [T4]
    have h : -5 + 48 * (x : ℤ) + 160 * (x : ℤ) ^ 2 - 1536 * (x : ℤ) ^ 3 + 2048 * (x : ℤ) ^ 4 =
        2 * (-3 + 24 * (x : ℤ) + 80 * (x : ℤ) ^ 2 - 768 * (x : ℤ) ^ 3 + 1024 * (x : ℤ) ^ 4) + 1 := by ring
    rw [h]; omega
  have hT4_im_even : (T4 (x : ℤ)).2 % 2 = 0 := by
    dsimp [T4]
    have h : 8 * (x : ℤ) * (-9 + 72 * (x : ℤ) - 128 * (x : ℤ) ^ 2) =
        2 * (4 * (x : ℤ) * (-9 + 72 * (x : ℤ) - 128 * (x : ℤ) ^ 2)) := by ring
    rw [h]; omega
  have hU_odd : U % 2 = 1 := by
    have h1 : (gmul (U, V) (T4 (x : ℤ))).1 % 2 = 1 := by omega
    dsimp [gmul] at h1
    rw [Int.sub_emod, Int.mul_emod U, Int.mul_emod V, hT4_re_odd, hT4_im_even] at h1
    omega
  have hV_even : V % 2 = 0 := by
    have h4G : 2 ∣ (gmul (U, V) (T4 (x : ℤ))).2 := by
      have h2 : (2 : ℤ) ^ (t + 2) = 2 * (2 : ℤ) ^ (t + 1) := by ring
      exact dvd_trans ⟨(2 : ℤ) ^ (t + 1), h2⟩ hdvdG
    rcases h4G with ⟨c, hc⟩
    have h1 : (gmul (U, V) (T4 (x : ℤ))).2 % 2 = 0 := by omega
    dsimp [gmul] at h1
    rw [Int.add_emod, Int.mul_emod U, Int.mul_emod V, hT4_re_odd, hT4_im_even] at h1
    omega
  have hV_ne : V ≠ 0 := by
    intro hV0
    apply hndvdG
    dsimp [gmul, T4]
    rw [hV0, zero_mul, add_zero]
    rcases h2tx with ⟨m, hm⟩
    refine ⟨U * m * (-9 + 72 * (x : ℤ) - 128 * (x : ℤ) ^ 2), ?_⟩
    have hpow3 : (2 : ℤ) ^ (t + 3) = 8 * (2 : ℤ) ^ t := by ring
    rw [hpow3, hm]; ring
  exact ⟨U, V, hUV, hU_odd, hV_even, hV_ne⟩

lemma seqPair_seven_mod_eight (q : ℕ) : (seqPair (8 * q + 7)).2 ≠ 0 := by
  set x := q + 1
  have hx : 1 ≤ x := by omega
  have hidx : 8 * q + 7 = 3 + 4 * (2 * q + 1) := by omega
  rcases seqPair_add_four_mul 3 (gscale (-10) (1, 0)) seqPair_three (2 * q + 1) with ⟨⟨U, V⟩, hUV⟩
  rw [← hidx, gscale_mul_left, one_gmul, gscale_gscale] at hUV
  have h8x3 : seqPair (8 * x + 3) = gscale (-10 * (4 : ℤ) ^ x) (gmul (U, V) (T7 (x : ℤ))) := by
    have hstep : 8 * x + 3 = (8 * q + 7) + 4 := by omega
    rw [hstep, seqPair_add_four, hUV]
    have h7 : 8 * q + 7 = 8 * x - 1 := by omega
    rw [h7, block4_T7 x hx, gscale_gmul]
    have hpow : (2 : ℤ) ^ (2 * q + 1) * (-10) * 2 = -10 * (4 : ℤ) ^ x := by
      have : (4 : ℤ) ^ x = ((2 : ℤ) ^ 2) ^ (q + 1) := by rfl
      rw [this, ← pow_mul]; ring
    rw [hpow]
  have hGeq : gprod B3 0 x = gmul (U, V) (T7 (x : ℤ)) := by
    apply gscale_inj (c := -10 * (4 : ℤ) ^ x) (by
      have : (0 : ℤ) < (4 : ℤ) ^ x := by positivity
      omega)
    rw [← seqPair_eight_mul_add_three x, h8x3]
  rcases gprod_B3_props x (by omega) with ⟨t, h2tx, _, _, hndvdG⟩
  rw [hGeq] at hndvdG
  have hV_ne : V ≠ 0 := by
    intro hV0
    apply hndvdG
    dsimp [gmul, T7]
    rw [hV0, zero_mul, add_zero]
    rcases h2tx with ⟨m, hm⟩
    refine ⟨U * m * (-9 - 72 * (x : ℤ) - 128 * (x : ℤ) ^ 2), ?_⟩
    have hpow3 : (2 : ℤ) ^ (t + 3) = 8 * (2 : ℤ) ^ t := by ring
    rw [hpow3, hm]; ring
  rw [hUV]
  dsimp [gscale]
  have hc : (2 : ℤ) ^ (2 * q + 1) * (-10) ≠ 0 := by
    have : (0 : ℤ) < (2 : ℤ) ^ (2 * q + 1) := by positivity
    omega
  exact mul_ne_zero hc hV_ne

lemma step1_odd_im {U V k : ℤ} (hU : U % 2 = 1) (hV : V % 2 = 0) (hk : k % 2 = 1) :
    (gmul (U, V) (1, k)).2 ≠ 0 := by
  dsimp [gmul]
  intro h0
  have hmod : (U * k + V * 1) % 2 = 0 := by omega
  rw [Int.add_emod, Int.mul_emod U, Int.mul_emod V, hU, hV, hk] at hmod
  omega

lemma step2_odd_im {U V k : ℤ} (hU : U % 2 = 1) (hV : V % 2 = 0) :
    (gmul (gmul (U, V) (1, k)) (1, k + 1)).2 ≠ 0 := by
  dsimp [gmul]
  intro h0
  have h1 : (U * 1 - V * k) * (k + 1) + (U * k + V * 1) * 1 =
      U * (2 * k + 1) + V * (1 - k * (k + 1)) := by ring
  rw [h1] at h0
  have hmod : (U * (2 * k + 1) + V * (1 - k * (k + 1))) % 2 = 0 := by omega
  rw [Int.add_emod, Int.mul_emod U, Int.mul_emod V, hU, hV] at hmod
  have h2k : (2 * k + 1) % 2 = 1 := by omega
  rw [h2k] at hmod
  omega

end OMA105751R1H2

open OMA105751R1H2 in
theorem OMA.solution :
    OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H2 := by
  intro n hn
  rw [a_eq_seqPair_snd]
  set q := n / 8
  set r := n % 8
  have hn_eq : n = 8 * q + r := by omega
  have hr : r < 8 := Nat.mod_lt n (by decide)
  interval_cases r
  · -- n = 8 * q, q ≥ 1
    have hq : 0 < q := by omega
    rw [hn_eq, add_zero, seqPair_eight_mul]
    dsimp [gscale]
    rcases gprod_B0_props q hq with ⟨t, _, _, _, hndvd⟩
    have him : (gprod B0 0 q).2 ≠ 0 := fun h0 => hndvd (by rw [h0]; exact dvd_zero _)
    exact mul_ne_zero (by positivity) him
  · -- n = 8 * q + 1, q ≥ 1
    have hq : 0 < q := by omega
    have hstep : n = 8 * q + 1 := hn_eq
    rw [hstep, seqPair, seqPair_eight_mul, gscale_mul_left]
    dsimp [gscale]
    rcases gprod_B0_props q hq with ⟨t, _, hre, hdvd, _⟩
    have hU : (gprod B0 0 q).1 % 2 = 1 := by omega
    have hV : (gprod B0 0 q).2 % 2 = 0 := by
      have h2 : (2 : ℤ) ^ (t + 2) = 2 * (2 : ℤ) ^ (t + 1) := by ring
      rcases dvd_trans ⟨(2 : ℤ) ^ (t + 1), h2⟩ hdvd with ⟨c, hc⟩
      omega
    have hk : ((8 * q + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    exact mul_ne_zero (by positivity) (step1_odd_im hU hV hk)
  · -- n = 8 * q + 2, q ≥ 1
    have hq : 0 < q := by omega
    have hstep : n = (8 * q + 1) + 1 := by omega
    rw [hstep, seqPair, seqPair, seqPair_eight_mul, gscale_mul_left, gscale_mul_left]
    dsimp [gscale]
    rcases gprod_B0_props q hq with ⟨t, _, hre, hdvd, _⟩
    have hU : (gprod B0 0 q).1 % 2 = 1 := by omega
    have hV : (gprod B0 0 q).2 % 2 = 0 := by
      have h2 : (2 : ℤ) ^ (t + 2) = 2 * (2 : ℤ) ^ (t + 1) := by ring
      rcases dvd_trans ⟨(2 : ℤ) ^ (t + 1), h2⟩ hdvd with ⟨c, hc⟩
      omega
    exact mul_ne_zero (by positivity) (step2_odd_im (k := ((8 * q + 1 : ℕ) : ℤ)) hU hV)
  · -- n = 8 * q + 3, q ≥ 1
    have hq : 0 < q := by omega
    rw [hn_eq, seqPair_eight_mul_add_three]
    dsimp [gscale]
    rcases gprod_B3_props q hq with ⟨t, _, _, _, hndvd⟩
    have him : (gprod B3 0 q).2 ≠ 0 := fun h0 => hndvd (by rw [h0]; exact dvd_zero _)
    have hc : -10 * (4 : ℤ) ^ q ≠ 0 := by
      have : (0 : ℤ) < (4 : ℤ) ^ q := by positivity
      omega
    exact mul_ne_zero hc him
  · -- n = 8 * q + 4
    rw [hn_eq]
    rcases seqPair_four_mod_eight q with ⟨U, V, hUV, _, _, hV⟩
    rw [hUV]
    dsimp [gscale]
    exact mul_ne_zero (by positivity) hV
  · -- n = 8 * q + 5
    have hstep : n = (8 * q + 4) + 1 := by omega
    rw [hstep, seqPair]
    rcases seqPair_four_mod_eight q with ⟨U, V, hUV, hU, hV, _⟩
    rw [hUV, gscale_mul_left]
    dsimp [gscale]
    have hk : ((8 * q + 4 + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    exact mul_ne_zero (by positivity) (step1_odd_im hU hV hk)
  · -- n = 8 * q + 6
    have hstep : n = ((8 * q + 4) + 1) + 1 := by omega
    rw [hstep, seqPair, seqPair]
    rcases seqPair_four_mod_eight q with ⟨U, V, hUV, hU, hV, _⟩
    rw [hUV, gscale_mul_left, gscale_mul_left]
    dsimp [gscale]
    have hcast : ((8 * q + 4 + 1 + 1 : ℕ) : ℤ) = ((8 * q + 4 + 1 : ℕ) : ℤ) + 1 := by
      push_cast; ring
    have htarget :
        (gmul (gmul (U, V) (1, ((8 * q + 4 + 1 : ℕ) : ℤ))) (1, ((8 * q + 4 + 1 + 1 : ℕ) : ℤ))).2 ≠ 0 := by
      rw [hcast]
      exact step2_odd_im hU hV
    exact mul_ne_zero (by positivity) htarget
  · -- n = 8 * q + 7
    rw [hn_eq]
    exact seqPair_seven_mod_eight q
