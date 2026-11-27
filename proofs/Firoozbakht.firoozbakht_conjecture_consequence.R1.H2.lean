import OMAReductions.R_Firoozbakht_firoozbakht_conjecture_consequence_R1

/-!
# Explicit prime-gap certificates through 1772200

The lists contain half-gaps between consecutive certificate endpoints, which are
odd primes. For each block, an exact power-of-two comparison gives a common
lower bound for the logarithm. An endpoint prime and the integer bound for a
gap then verify the estimate throughout that interval. The merged proof by
@steveDOTdigital in PR #4301 uses a gcd against a factorial; here a common
multiple verified once against the small divisors serves the same purpose.
-/

namespace OMA.FiroozbakhtFiniteGaps

private def scaledLog (p : ℕ) : ℕ := 6931 * (p ^ 256).log2

private def OnInterval (l r : ℕ) : Prop :=
  ∀ p : ℕ, l ≤ p → p < r → ∃ q : ℕ, p < q ∧ q.Prime ∧
    2560000 ^ 2 * (q - p) + 2560000 * scaledLog p < scaledLog p ^ 2

/-- A common multiple of all positive integers through 1332. -/
private def commonMultiple : ℕ :=
  270042270089695499205872267054112802334002833670849203489259316419915581836927647172083176329358293387568951160156986896909627618221684241192974985595282904027039219640984539238853963471906018413505714800078311022687126546670094698506487299772714580887577574188667980472410691539839617301176931330486773217332873833833430128844423959373715380352118660505876401957416464604342513649112613764009318264585844477784594881394485713776635270625148068717925059737912387180388359683632032671907782836092626748841395860381323452146998829774644139187337751084542732432806868811964436705352320000

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem dividesCommon : ∀ i : Fin 1333, 0 < i.val → commonMultiple % i.val = 0 := by
  decide +kernel

private def certifiedPrime (q : ℕ) : Bool :=
  if q ≤ 1332 then decide q.Prime else decide (q ≤ 1332 ^ 2 ∧ q.gcd commonMultiple = 1)

/-- A composite number in this range has a divisor between 2 and 1332. -/
private theorem certifiedPrimeSound {q : ℕ} (cert : certifiedPrime q = true) : q.Prime := by
  by_cases small : q ≤ 1332
  · simp only [certifiedPrime, if_pos small] at cert
    exact of_decide_eq_true cert
  · simp only [certifiedPrime, if_neg small] at cert
    have ⟨hi, cop⟩ : q ≤ 1332 ^ 2 ∧ q.gcd commonMultiple = 1 := of_decide_eq_true cert
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
    intro m hm hs dvd
    have root : q.sqrt ≤ 1332 := (Nat.sqrt_le_sqrt hi).trans (by decide)
    have rem := dividesCommon (⟨m, by omega⟩ : Fin 1333) (by simpa using (by omega : 0 < m))
    have common : m ∣ commonMultiple := Nat.dvd_of_mod_eq_zero rem
    have one := Nat.dvd_gcd dvd common
    rw [cop] at one
    have bound := Nat.le_of_dvd (by decide : 0 < 1) one
    omega

private def gapOK (e start halfGap : ℕ) : Bool :=
  certifiedPrime (start + 2 * halfGap) && decide
    (2560000 ^ 2 * (2 * halfGap) + 2560000 * (6931 * e) < (6931 * e) ^ 2)

private theorem oneInterval {start e halfGap : ℕ} (floor : 2 ^ e ≤ start ^ 256)
    (large : 2560000 ≤ 6931 * e) (cert : gapOK e start halfGap = true) :
    OnInterval start (start + 2 * halfGap) := by
  obtain ⟨pr, inequality⟩ := Bool.and_eq_true_iff.mp cert
  have prime := certifiedPrimeSound pr
  have bound : 2560000 ^ 2 * (2 * halfGap) + 2560000 * (6931 * e) < (6931 * e) ^ 2 :=
    of_decide_eq_true inequality
  intro p lp pq
  refine ⟨start + 2 * halfGap, pq, prime, ?_⟩
  have mono : 6931 * e ≤ scaledLog p := by
    unfold scaledLog
    apply Nat.mul_le_mul_left
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by decide) (floor.trans (Nat.pow_le_pow_left lp 256))
  let d := scaledLog p - 6931 * e
  have add : scaledLog p = 6931 * e + d := by dsimp [d]; omega
  have gap := Nat.mul_le_mul_left (2560000 ^ 2) (by omega : start + 2 * halfGap - p ≤ 2 * halfGap)
  have cross := Nat.mul_le_mul_right d large
  rw [add]
  nlinarith only [bound, gap, cross, Nat.zero_le ((6931 * e) * d), Nat.zero_le (d ^ 2)]

private theorem joinIntervals {l m r : ℕ} (left : OnInterval l m)
    (right : OnInterval m r) : OnInterval l r := by
  intro p lp pr
  by_cases h : p < m
  · exact left p lp h
  · exact right p (by omega) pr

private def chainOK (e stop start : ℕ) : List ℕ → Bool
  | [] => decide (start = stop)
  | g :: gs => gapOK e start g && chainOK e stop (start + 2 * g) gs

private theorem chainSound (stop e : ℕ) (large : 2560000 ≤ 6931 * e) (gaps : List ℕ) :
    ∀ start : ℕ, 2 ^ e ≤ start ^ 256 → chainOK e stop start gaps = true → OnInterval start stop := by
  induction gaps with
  | nil =>
    intro start _ cert
    have eq : start = stop := of_decide_eq_true cert
    intro p hp hq
    omega
  | cons g gs ih =>
    intro start floor cert
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp cert
    exact joinIntervals (oneInterval floor large head)
      (ih (start + 2 * g) (floor.trans (Nat.pow_le_pow_left (by omega) 256)) tail)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block0 : OnInterval 11 13 := by
  apply chainSound 13 885 (by decide)
    [
      1
    ] 11 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block1 : OnInterval 13 23 := by
  apply chainSound 23 947 (by decide)
    [
      2, 1, 2
    ] 13 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block2 : OnInterval 23 89 := by
  apply chainSound 89 1158 (by decide)
    [
      3, 1, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3
    ] 23 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block3 : OnInterval 89 523 := by
  apply chainSound 523 1657 (by decide)
    [
      7, 5, 7, 6, 6, 6, 5, 4, 6, 3, 6, 6, 5, 4, 5, 6, 7, 3, 5, 7, 5, 7,
      3, 6, 5, 7, 5, 7, 6, 6, 6, 5, 7, 5, 6, 6, 6, 3, 7
    ] 89 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block4 : OnInterval 523 1327 := by
  apply chainSound 1327 2311 (by decide)
    [
      12, 15, 15, 12, 15, 15, 14, 16, 11, 12, 16, 15, 14, 16, 14, 15, 16, 15, 15, 14, 16, 12,
      14, 16, 12, 11, 16, 15, 3
    ] 523 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block5 : OnInterval 1327 5701 := by
  apply chainSound 5701 2655 (by decide)
    [
      20, 21, 22, 20, 19, 20, 21, 22, 21, 21, 21, 20, 22, 20, 22, 21, 18, 20, 22, 20, 13, 21,
      15, 21, 20, 22, 20, 21, 22, 20, 18, 21, 21, 22, 21, 21, 21, 14, 21, 18, 16, 20, 19, 20,
      16, 21, 20, 13, 21, 21, 17, 22, 21, 18, 21, 18, 18, 20, 18, 21, 19, 20, 22, 20, 22, 20,
      21, 19, 15, 21, 20, 19, 21, 21, 18, 21, 17, 18, 21, 21, 15, 22, 18, 20, 18, 22, 18, 21,
      15, 20, 19, 21, 21, 15, 18, 21, 9, 17, 22, 20, 22, 21, 14, 21, 22, 21, 21, 21, 14, 16,
      18, 21
    ] 1327 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block6 : OnInterval 5701 12479 := by
  apply chainSound 12479 3194 (by decide)
    [
      24, 32, 33, 30, 24, 33, 30, 30, 28, 29, 33, 22, 27, 20, 31, 33, 30, 29, 33, 33, 24, 33,
      30, 33, 25, 30, 32, 33, 31, 33, 32, 33, 33, 27, 33, 30, 33, 22, 27, 32, 33, 31, 32, 28,
      30, 29, 33, 30, 28, 32, 30, 33, 24, 33, 33, 30, 25, 32, 33, 27, 28, 32, 33, 30, 31, 30,
      30, 33, 32, 28, 33, 33, 32, 33, 27, 33, 27, 28, 32, 33, 30, 31, 30, 30, 33, 33, 27, 23,
      33, 31, 33, 32, 30, 31, 32, 28, 24, 33, 32, 31, 32, 30, 33, 27, 31, 32, 25, 32, 31, 29,
      33, 33
    ] 5701 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block7 : OnInterval 12479 20599 := by
  apply chainSound 20599 3483 (by decide)
    [
      37, 33, 39, 33, 39, 39, 32, 33, 39, 30, 36, 39, 37, 38, 33, 37, 35, 33, 39, 36, 27, 33,
      37, 35, 37, 38, 37, 39, 39, 38, 33, 36, 36, 27, 36, 31, 38, 33, 34, 39, 36, 38, 37, 39,
      32, 39, 31, 39, 36, 30, 39, 39, 39, 36, 39, 38, 37, 33, 35, 30, 34, 36, 39, 36, 35, 34,
      33, 38, 34, 38, 37, 38, 28, 39, 39, 36, 39, 36, 36, 39, 39, 39, 38, 39, 36, 39, 39, 27,
      33, 39, 33, 37, 38, 37, 36, 39, 38, 39, 34, 39, 38, 39, 39, 39, 37, 39, 35, 39, 36, 37,
      39, 39
    ] 12479 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block8 : OnInterval 20599 29641 := by
  apply chainSound 29641 3668 (by decide)
    [
      41, 39, 25, 44, 43, 42, 41, 39, 43, 44, 43, 41, 40, 44, 42, 36, 42, 43, 42, 41, 39, 42,
      39, 40, 44, 42, 43, 35, 43, 39, 38, 43, 44, 40, 44, 40, 44, 31, 42, 42, 36, 39, 42, 44,
      36, 43, 42, 44, 42, 42, 43, 44, 36, 33, 42, 40, 42, 42, 44, 31, 35, 40, 41, 34, 39, 42,
      44, 43, 41, 39, 40, 42, 41, 42, 43, 38, 40, 44, 42, 40, 44, 40, 39, 36, 39, 32, 40, 35,
      39, 36, 34, 41, 43, 38, 33, 40, 42, 42, 41, 42, 43, 44, 42, 39, 42, 42, 42, 40, 44, 42,
      43, 36
    ] 20599 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block9 : OnInterval 29641 39323 := by
  apply chainSound 39323 3802 (by decide)
    [
      41, 40, 39, 39, 44, 46, 42, 45, 45, 47, 40, 47, 46, 45, 44, 46, 45, 35, 42, 40, 20, 46,
      47, 42, 42, 33, 45, 42, 46, 45, 44, 46, 45, 47, 42, 46, 45, 42, 42, 41, 33, 46, 45, 45,
      44, 45, 39, 46, 45, 47, 37, 32, 43, 42, 44, 42, 42, 31, 41, 45, 43, 45, 42, 44, 45, 46,
      44, 42, 43, 47, 37, 47, 46, 44, 43, 47, 43, 45, 41, 45, 46, 41, 43, 47, 45, 45, 42, 46,
      44, 46, 47, 43, 47, 37, 47, 43, 47, 46, 47, 42, 45, 40, 35, 46, 42, 45, 47, 46, 47, 46,
      47, 45
    ] 29641 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block10 : OnInterval 39323 49639 := by
  apply chainSound 49639 3907 (by decide)
    [
      48, 46, 48, 48, 48, 44, 48, 40, 50, 45, 49, 41, 49, 48, 41, 46, 48, 48, 44, 49, 45, 44,
      48, 48, 49, 45, 38, 49, 44, 45, 49, 48, 48, 47, 49, 48, 50, 48, 49, 45, 50, 43, 47, 48,
      45, 48, 49, 45, 45, 50, 49, 50, 46, 50, 36, 48, 49, 47, 49, 50, 37, 35, 49, 50, 48, 31,
      47, 49, 38, 36, 45, 45, 46, 48, 45, 50, 37, 50, 45, 45, 40, 48, 45, 50, 46, 44, 40, 50,
      48, 48, 46, 48, 42, 50, 49, 50, 46, 50, 46, 50, 49, 50, 49, 47, 45, 48, 42, 42, 43, 44,
      39, 40
    ] 39323 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block11 : OnInterval 49639 60509 := by
  apply chainSound 60509 3993 (by decide)
    [
      51, 51, 50, 52, 53, 39, 51, 45, 52, 50, 48, 49, 51, 39, 35, 49, 47, 49, 50, 51, 48, 45,
      52, 48, 51, 51, 53, 52, 47, 52, 53, 51, 46, 53, 51, 52, 53, 51, 49, 45, 44, 51, 51, 49,
      50, 52, 53, 51, 49, 47, 52, 53, 52, 53, 48, 46, 44, 46, 53, 45, 46, 47, 52, 48, 53, 46,
      53, 48, 52, 53, 45, 52, 53, 49, 53, 51, 51, 49, 39, 51, 36, 48, 53, 49, 45, 41, 49, 50,
      49, 42, 48, 41, 51, 49, 53, 46, 47, 49, 30, 53, 43, 47, 52, 50, 46, 47, 42, 49, 42, 47,
      48, 48
    ] 49639 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block12 : OnInterval 60509 71993 := by
  apply chainSound 71993 4066 (by decide)
    [
      54, 55, 47, 51, 54, 55, 45, 54, 51, 53, 55, 50, 52, 53, 52, 50, 51, 55, 50, 54, 55, 50,
      51, 43, 54, 51, 50, 55, 45, 54, 51, 50, 52, 53, 52, 54, 51, 53, 37, 54, 48, 50, 55, 53,
      54, 49, 44, 55, 53, 54, 55, 53, 48, 54, 54, 46, 53, 45, 52, 41, 55, 50, 55, 53, 55, 50,
      55, 50, 54, 51, 55, 54, 48, 45, 53, 55, 54, 53, 48, 55, 36, 53, 52, 48, 53, 54, 49, 50,
      42, 43, 50, 51, 54, 52, 53, 49, 51, 54, 51, 45, 47, 49, 51, 53, 54, 55, 53, 55, 54, 53,
      55, 53
    ] 60509 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block13 : OnInterval 71993 83663 := by
  apply chainSound 83663 4130 (by decide)
    [
      55, 54, 51, 54, 56, 55, 48, 42, 54, 56, 49, 51, 54, 54, 56, 55, 51, 50, 45, 52, 56, 54,
      43, 53, 54, 55, 45, 53, 55, 48, 54, 56, 54, 52, 56, 45, 55, 44, 49, 54, 56, 55, 56, 49,
      50, 51, 51, 54, 55, 56, 55, 54, 56, 52, 50, 51, 51, 54, 54, 55, 45, 56, 52, 54, 56, 49,
      44, 49, 53, 54, 55, 41, 54, 49, 56, 48, 46, 56, 55, 54, 50, 54, 46, 54, 56, 52, 48, 54,
      41, 55, 54, 56, 54, 48, 55, 45, 50, 55, 48, 54, 56, 55, 56, 46, 50, 55, 47, 55, 56, 55,
      56, 51
    ] 71993 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block14 : OnInterval 83663 95713 := by
  apply chainSound 95713 4186 (by decide)
    [
      57, 57, 48, 51, 55, 57, 54, 56, 58, 56, 55, 54, 57, 54, 56, 58, 51, 56, 54, 51, 40, 48,
      57, 57, 57, 53, 55, 53, 45, 43, 56, 51, 52, 56, 54, 58, 54, 56, 55, 54, 54, 54, 56, 54,
      58, 48, 56, 49, 50, 51, 58, 50, 46, 57, 45, 50, 28, 54, 56, 57, 52, 56, 57, 58, 57, 57,
      53, 57, 58, 54, 56, 58, 47, 57, 57, 58, 57, 56, 55, 54, 56, 58, 57, 57, 57, 53, 37, 56,
      58, 54, 45, 51, 54, 51, 56, 58, 56, 45, 52, 53, 52, 57, 56, 57, 55, 47, 58, 57, 56, 57,
      57, 58
    ] 83663 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block15 : OnInterval 95713 108247 := by
  apply chainSound 108247 4235 (by decide)
    [
      53, 55, 57, 57, 56, 54, 60, 52, 51, 60, 54, 54, 60, 50, 60, 60, 57, 58, 60, 59, 57, 49,
      60, 60, 57, 54, 48, 56, 57, 60, 54, 49, 60, 60, 57, 59, 60, 55, 59, 52, 60, 57, 56, 57,
      57, 60, 60, 57, 40, 60, 54, 56, 60, 58, 60, 57, 59, 55, 54, 57, 56, 54, 55, 60, 59, 46,
      48, 60, 57, 60, 56, 55, 53, 57, 58, 47, 52, 56, 60, 57, 55, 57, 60, 53, 60, 58, 60, 60,
      57, 48, 57, 45, 48, 57, 60, 45, 45, 60, 60, 60, 59, 58, 57, 53, 58, 54, 59, 46, 56, 60,
      58, 54
    ] 95713 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block16 : OnInterval 108247 120899 := by
  apply chainSound 120899 4281 (by decide)
    [
      56, 52, 54, 53, 61, 59, 60, 61, 60, 59, 61, 60, 56, 61, 57, 48, 50, 54, 34, 60, 59, 57,
      55, 59, 57, 48, 61, 51, 60, 59, 61, 57, 56, 55, 56, 61, 50, 52, 57, 60, 59, 60, 57, 60,
      58, 54, 60, 50, 61, 60, 57, 50, 58, 57, 54, 60, 60, 59, 52, 54, 56, 58, 57, 54, 59, 52,
      59, 61, 57, 60, 56, 54, 60, 43, 57, 60, 53, 60, 57, 57, 54, 61, 54, 56, 60, 61, 60, 60,
      42, 57, 59, 52, 59, 61, 50, 58, 51, 60, 59, 61, 60, 56, 54, 60, 55, 56, 58, 41, 60, 60,
      54, 60
    ] 108247 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block17 : OnInterval 120899 133691 := by
  apply chainSound 133691 4322 (by decide)
    [
      61, 59, 60, 60, 61, 60, 53, 58, 62, 57, 61, 62, 61, 56, 51, 57, 57, 58, 60, 56, 51, 58,
      62, 60, 60, 60, 40, 59, 55, 59, 61, 56, 60, 51, 48, 55, 60, 60, 59, 61, 59, 58, 60, 50,
      58, 60, 62, 60, 54, 51, 54, 49, 54, 57, 54, 56, 61, 59, 61, 59, 48, 60, 61, 60, 56, 61,
      59, 51, 60, 55, 57, 45, 51, 59, 61, 62, 57, 48, 58, 62, 52, 60, 56, 55, 50, 55, 59, 55,
      57, 54, 59, 57, 60, 58, 57, 59, 60, 51, 51, 57, 61, 62, 57, 58, 62, 51, 60, 52, 62, 57,
      60, 60
    ] 120899 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block18 : OnInterval 133691 146953 := by
  apply chainSound 146953 4359 (by decide)
    [
      61, 53, 60, 61, 63, 57, 56, 63, 57, 60, 63, 60, 61, 63, 56, 61, 63, 62, 63, 61, 62, 60,
      60, 55, 60, 60, 42, 51, 60, 60, 62, 60, 57, 63, 63, 54, 61, 59, 63, 63, 61, 56, 58, 62,
      55, 50, 54, 63, 63, 63, 60, 61, 63, 62, 63, 63, 57, 63, 63, 55, 50, 61, 60, 63, 53, 63,
      57, 60, 49, 60, 60, 63, 60, 56, 61, 60, 63, 63, 50, 57, 57, 61, 62, 58, 63, 51, 59, 52,
      60, 63, 56, 61, 63, 60, 56, 61, 57, 63, 60, 63, 56, 58, 63, 60, 59, 54, 60, 54, 63, 58,
      62, 55
    ] 133691 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block19 : OnInterval 146953 160253 := by
  apply chainSound 160253 4394 (by decide)
    [
      60, 62, 61, 50, 64, 63, 63, 60, 51, 63, 51, 59, 58, 63, 59, 63, 54, 63, 63, 64, 59, 60,
      55, 57, 59, 60, 64, 59, 63, 60, 63, 60, 64, 60, 63, 63, 59, 63, 64, 60, 63, 60, 53, 63,
      64, 62, 64, 62, 63, 61, 56, 39, 64, 62, 60, 63, 64, 62, 63, 58, 60, 60, 60, 63, 60, 54,
      60, 60, 57, 63, 62, 63, 60, 58, 29, 60, 58, 56, 51, 61, 63, 57, 54, 63, 57, 63, 60, 53,
      64, 59, 60, 54, 61, 57, 63, 62, 63, 64, 62, 55, 56, 63, 57, 64, 56, 58, 59, 63, 52, 56,
      60, 42
    ] 146953 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block20 : OnInterval 160253 174061 := by
  apply chainSound 174061 4426 (by decide)
    [
      60, 63, 64, 65, 63, 63, 64, 65, 60, 60, 60, 63, 64, 65, 54, 55, 65, 57, 64, 65, 64, 65,
      64, 63, 62, 60, 63, 64, 65, 63, 60, 61, 62, 57, 61, 65, 55, 62, 63, 61, 60, 63, 65, 63,
      60, 64, 60, 63, 56, 55, 56, 64, 65, 60, 64, 65, 46, 62, 64, 60, 65, 64, 65, 61, 65, 64,
      62, 55, 63, 65, 60, 55, 65, 57, 64, 63, 63, 53, 64, 62, 64, 65, 64, 65, 61, 62, 49, 60,
      56, 63, 60, 61, 63, 65, 60, 61, 65, 61, 60, 60, 63, 60, 63, 63, 65, 60, 61, 65, 63, 60,
      63, 64
    ] 160253 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block21 : OnInterval 174061 187921 := by
  apply chainSound 187921 4456 (by decide)
    [
      54, 65, 66, 51, 63, 57, 64, 56, 64, 63, 63, 65, 63, 66, 64, 66, 60, 50, 64, 66, 65, 64,
      62, 58, 56, 63, 63, 64, 56, 60, 49, 63, 63, 65, 64, 65, 66, 42, 61, 66, 66, 65, 57, 63,
      64, 56, 64, 66, 62, 52, 65, 63, 66, 66, 55, 48, 66, 59, 63, 63, 64, 66, 60, 65, 64, 66,
      65, 61, 65, 63, 63, 60, 63, 66, 64, 66, 65, 66, 58, 65, 64, 62, 63, 63, 57, 63, 64, 63,
      66, 66, 53, 57, 64, 65, 66, 64, 56, 60, 63, 60, 66, 66, 49, 59, 66, 66, 61, 65, 63, 64,
      53, 64
    ] 174061 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block22 : OnInterval 187921 202021 := by
  apply chainSound 202021 4485 (by decide)
    [
      54, 65, 66, 63, 58, 60, 63, 66, 66, 63, 51, 65, 64, 66, 53, 67, 65, 64, 62, 63, 67, 63,
      62, 64, 63, 63, 63, 57, 62, 67, 66, 63, 62, 67, 66, 56, 63, 60, 67, 60, 63, 66, 56, 66,
      63, 60, 67, 65, 64, 66, 60, 60, 63, 59, 66, 57, 60, 55, 59, 66, 64, 59, 66, 64, 66, 65,
      63, 66, 61, 63, 65, 55, 66, 51, 66, 65, 64, 66, 62, 63, 57, 66, 67, 63, 66, 65, 66, 67,
      57, 65, 66, 57, 63, 57, 67, 65, 63, 57, 64, 66, 65, 66, 60, 64, 65, 66, 63, 67, 65, 67,
      66, 66
    ] 187921 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block23 : OnInterval 202021 216119 := by
  apply chainSound 216119 4511 (by decide)
    [
      54, 57, 59, 66, 67, 65, 66, 67, 59, 54, 67, 39, 65, 61, 65, 67, 65, 63, 67, 60, 68, 64,
      68, 66, 66, 58, 66, 65, 67, 60, 65, 67, 68, 60, 58, 66, 50, 66, 67, 62, 64, 66, 66, 68,
      55, 66, 68, 63, 67, 65, 66, 61, 65, 61, 60, 63, 66, 68, 60, 60, 61, 66, 68, 63, 67, 57,
      65, 64, 60, 65, 49, 65, 67, 59, 60, 64, 65, 66, 60, 60, 64, 63, 63, 57, 54, 68, 66, 64,
      66, 66, 65, 66, 64, 68, 67, 63, 68, 58, 66, 68, 61, 62, 40, 65, 63, 66, 63, 55, 68, 55,
      60, 68
    ] 202021 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block24 : OnInterval 216119 230611 := by
  apply chainSound 230611 4536 (by decide)
    [
      57, 69, 69, 69, 67, 69, 69, 56, 69, 66, 69, 60, 66, 54, 66, 61, 48, 68, 64, 65, 69, 64,
      68, 67, 68, 69, 69, 69, 61, 66, 65, 64, 66, 66, 69, 65, 64, 69, 66, 59, 67, 63, 68, 63,
      69, 63, 67, 66, 66, 68, 66, 67, 69, 50, 66, 60, 63, 69, 57, 69, 69, 60, 66, 67, 68, 69,
      57, 69, 60, 69, 63, 63, 67, 69, 69, 69, 57, 63, 65, 67, 69, 65, 69, 58, 69, 56, 64, 69,
      69, 60, 62, 63, 67, 65, 69, 69, 67, 68, 58, 68, 64, 68, 63, 55, 69, 63, 57, 66, 66, 56,
      57, 52
    ] 216119 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block25 : OnInterval 230611 245407 := by
  apply chainSound 245407 4560 (by decide)
    [
      66, 65, 64, 65, 70, 69, 69, 65, 66, 69, 67, 68, 70, 65, 67, 66, 69, 65, 70, 68, 70, 60,
      68, 42, 70, 63, 69, 69, 69, 66, 69, 68, 70, 57, 63, 63, 62, 64, 65, 70, 65, 66, 70, 68,
      67, 69, 56, 67, 63, 65, 70, 62, 70, 65, 70, 66, 66, 63, 65, 67, 63, 66, 66, 66, 63, 59,
      67, 68, 66, 66, 66, 69, 54, 70, 65, 64, 68, 70, 65, 64, 65, 61, 62, 67, 66, 69, 69, 69,
      66, 69, 68, 64, 68, 66, 69, 63, 70, 68, 67, 68, 61, 56, 67, 68, 69, 69, 66, 70, 68, 67,
      69, 69
    ] 230611 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block26 : OnInterval 245407 259967 := by
  apply chainSound 259967 4583 (by decide)
    [
      63, 69, 59, 61, 69, 69, 66, 60, 69, 68, 63, 70, 60, 65, 70, 66, 66, 69, 65, 70, 69, 69,
      65, 70, 68, 69, 63, 70, 65, 70, 68, 69, 70, 68, 63, 63, 54, 67, 51, 69, 66, 69, 68, 67,
      69, 66, 66, 69, 68, 70, 68, 70, 68, 70, 69, 51, 60, 66, 39, 57, 57, 60, 66, 69, 66, 69,
      66, 60, 69, 60, 53, 70, 69, 68, 70, 66, 69, 65, 70, 65, 67, 63, 66, 57, 62, 67, 60, 66,
      57, 62, 70, 63, 66, 66, 63, 62, 70, 68, 70, 66, 69, 68, 64, 69, 57, 53, 55, 60, 62, 70,
      59, 63
    ] 245407 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block27 : OnInterval 259967 274889 := by
  apply chainSound 274889 4604 (by decide)
    [
      61, 71, 66, 63, 70, 66, 66, 69, 69, 66, 69, 71, 70, 63, 68, 69, 70, 69, 71, 70, 69, 69,
      66, 69, 71, 67, 59, 70, 69, 66, 69, 66, 71, 69, 58, 71, 69, 70, 66, 66, 66, 54, 68, 67,
      69, 65, 69, 60, 66, 70, 66, 68, 70, 68, 70, 69, 69, 71, 69, 70, 71, 66, 58, 57, 60, 65,
      57, 66, 70, 71, 61, 62, 63, 64, 68, 67, 60, 69, 65, 61, 66, 68, 64, 71, 60, 70, 71, 66,
      69, 70, 56, 69, 69, 69, 57, 70, 71, 70, 69, 71, 67, 56, 70, 59, 70, 68, 70, 59, 64, 69,
      62, 69
    ] 259967 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block28 : OnInterval 274889 289771 := by
  apply chainSound 289771 4625 (by decide)
    [
      69, 70, 71, 72, 70, 68, 54, 72, 66, 72, 72, 63, 72, 55, 69, 72, 60, 63, 60, 69, 68, 72,
      57, 63, 70, 68, 70, 68, 64, 72, 68, 70, 71, 61, 71, 69, 66, 69, 69, 69, 67, 69, 66, 68,
      70, 62, 63, 66, 46, 66, 60, 62, 70, 72, 69, 60, 72, 62, 48, 69, 70, 71, 72, 67, 71, 72,
      70, 71, 69, 72, 63, 70, 66, 72, 62, 72, 64, 72, 65, 70, 72, 57, 69, 60, 60, 72, 63, 66,
      69, 69, 66, 66, 71, 58, 65, 61, 60, 59, 69, 66, 70, 72, 45, 57, 71, 70, 66, 71, 72, 57,
      66, 64
    ] 274889 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block29 : OnInterval 289771 304739 := by
  apply chainSound 304739 4645 (by decide)
    [
      63, 72, 71, 72, 72, 70, 63, 71, 67, 65, 72, 66, 72, 69, 66, 69, 61, 69, 68, 63, 69, 64,
      60, 71, 64, 60, 72, 65, 69, 61, 69, 63, 72, 71, 63, 42, 70, 63, 62, 64, 69, 72, 48, 71,
      63, 72, 70, 63, 71, 49, 71, 72, 69, 70, 71, 54, 63, 70, 72, 63, 63, 69, 54, 69, 68, 70,
      69, 63, 60, 66, 71, 70, 68, 61, 71, 66, 70, 68, 64, 60, 72, 69, 69, 72, 71, 69, 69, 72,
      67, 66, 71, 54, 67, 72, 71, 72, 69, 70, 69, 65, 69, 66, 70, 60, 66, 68, 66, 72, 69, 64,
      69, 71
    ] 289771 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block30 : OnInterval 304739 320119 := by
  apply chainSound 320119 4663 (by decide)
    [
      72, 73, 59, 67, 71, 70, 50, 70, 72, 72, 59, 70, 71, 49, 69, 72, 69, 69, 71, 67, 60, 72,
      72, 69, 69, 71, 67, 72, 68, 73, 71, 70, 66, 72, 68, 67, 72, 59, 72, 72, 73, 65, 64, 71,
      67, 71, 72, 73, 60, 71, 63, 70, 68, 72, 73, 72, 65, 73, 63, 72, 72, 66, 66, 63, 71, 72,
      73, 56, 70, 69, 71, 70, 71, 64, 69, 69, 71, 70, 71, 73, 66, 69, 71, 67, 65, 67, 71, 72,
      72, 70, 66, 72, 69, 65, 61, 72, 68, 69, 70, 71, 73, 62, 64, 69, 69, 71, 70, 71, 73, 72,
      71, 73
    ] 304739 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block31 : OnInterval 320119 335477 := by
  apply chainSound 335477 4681 (by decide)
    [
      60, 69, 72, 69, 66, 68, 73, 65, 69, 64, 71, 73, 72, 69, 66, 50, 73, 71, 55, 69, 72, 71,
      70, 72, 66, 71, 73, 68, 70, 72, 72, 71, 72, 72, 70, 66, 69, 71, 72, 72, 73, 72, 71, 70,
      60, 72, 72, 65, 70, 71, 70, 72, 68, 70, 69, 66, 65, 73, 71, 70, 66, 72, 71, 66, 70, 71,
      72, 73, 72, 63, 72, 60, 68, 72, 61, 71, 69, 69, 72, 70, 68, 72, 69, 61, 66, 65, 72, 73,
      68, 57, 64, 69, 71, 64, 69, 72, 63, 66, 66, 68, 70, 68, 64, 71, 73, 72, 50, 69, 73, 72,
      63, 65
    ] 320119 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block32 : OnInterval 335477 350947 := by
  apply chainSound 350947 4699 (by decide)
    [
      66, 69, 73, 74, 70, 68, 73, 68, 64, 72, 71, 70, 74, 63, 58, 74, 73, 68, 73, 74, 73, 65,
      72, 58, 62, 72, 70, 65, 63, 73, 74, 73, 71, 67, 69, 66, 74, 61, 68, 70, 71, 73, 68, 73,
      66, 69, 72, 74, 63, 66, 69, 73, 74, 64, 69, 66, 59, 72, 73, 72, 71, 70, 68, 69, 63, 73,
      60, 72, 74, 66, 64, 71, 69, 69, 67, 65, 72, 63, 73, 66, 74, 72, 73, 66, 69, 66, 74, 70,
      72, 63, 72, 74, 66, 70, 62, 72, 60, 70, 71, 54, 73, 71, 69, 73, 68, 72, 72, 72, 70, 71,
      73, 69
    ] 335477 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block33 : OnInterval 350947 366733 := by
  apply chainSound 366733 4715 (by decide)
    [
      75, 66, 66, 71, 75, 75, 64, 75, 74, 70, 71, 75, 55, 69, 74, 73, 69, 74, 70, 74, 72, 63,
      67, 74, 75, 70, 72, 74, 73, 68, 75, 70, 75, 75, 75, 72, 71, 66, 75, 73, 57, 66, 69, 74,
      70, 59, 75, 75, 73, 74, 75, 75, 70, 71, 70, 75, 69, 65, 70, 69, 75, 74, 75, 70, 75, 75,
      62, 75, 69, 60, 72, 73, 60, 71, 70, 63, 60, 68, 75, 72, 72, 70, 68, 72, 75, 58, 75, 75,
      65, 61, 74, 75, 57, 70, 75, 75, 75, 69, 75, 65, 70, 74, 73, 69, 74, 72, 75, 73, 74, 75,
      67, 51
    ] 350947 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block34 : OnInterval 366733 382391 := by
  apply chainSound 382391 4731 (by decide)
    [
      74, 73, 68, 75, 72, 73, 74, 69, 70, 71, 61, 75, 75, 75, 69, 74, 70, 75, 75, 56, 75, 73,
      72, 74, 46, 75, 75, 66, 72, 56, 75, 75, 70, 62, 75, 67, 72, 63, 56, 67, 74, 75, 70, 75,
      74, 75, 75, 70, 71, 73, 66, 69, 71, 72, 75, 60, 75, 75, 73, 60, 71, 73, 75, 75, 72, 74,
      75, 54, 55, 65, 70, 75, 66, 65, 66, 70, 75, 66, 74, 55, 65, 69, 69, 75, 67, 69, 72, 75,
      72, 71, 70, 74, 72, 69, 55, 74, 72, 75, 75, 69, 75, 70, 75, 75, 74, 70, 75, 51, 72, 57,
      75, 62
    ] 366733 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block35 : OnInterval 382391 398273 := by
  apply chainSound 398273 4747 (by decide)
    [
      75, 76, 75, 68, 67, 74, 69, 75, 72, 73, 74, 73, 72, 65, 70, 75, 75, 63, 68, 76, 71, 67,
      63, 74, 66, 75, 72, 73, 69, 65, 63, 75, 75, 75, 72, 69, 75, 70, 59, 75, 72, 76, 68, 76,
      71, 72, 76, 71, 75, 76, 65, 67, 75, 75, 63, 75, 65, 75, 69, 51, 69, 73, 62, 76, 63, 69,
      72, 75, 74, 70, 72, 75, 74, 76, 69, 75, 75, 74, 75, 75, 76, 71, 75, 73, 69, 68, 72, 72,
      69, 66, 61, 68, 76, 69, 74, 73, 69, 71, 63, 76, 66, 75, 72, 63, 75, 65, 67, 65, 76, 66,
      74, 72
    ] 382391 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block36 : OnInterval 398273 414209 := by
  apply chainSound 414209 4762 (by decide)
    [
      75, 73, 71, 76, 63, 74, 73, 75, 75, 74, 70, 69, 74, 75, 75, 75, 76, 72, 75, 74, 73, 65,
      76, 72, 72, 68, 72, 73, 72, 72, 69, 56, 61, 69, 74, 75, 76, 69, 74, 76, 74, 73, 69, 68,
      58, 69, 75, 71, 72, 76, 69, 71, 76, 71, 55, 74, 76, 75, 72, 71, 67, 72, 75, 75, 75, 68,
      69, 75, 63, 73, 75, 65, 75, 72, 75, 73, 69, 75, 74, 72, 73, 75, 72, 75, 69, 63, 72, 63,
      75, 75, 65, 67, 74, 76, 60, 75, 71, 72, 67, 75, 53, 70, 71, 72, 75, 55, 62, 76, 75, 72,
      69, 74
    ] 398273 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block37 : OnInterval 414209 430433 := by
  apply chainSound 430433 4776 (by decide)
    [
      76, 71, 75, 75, 73, 74, 67, 75, 71, 75, 75, 73, 69, 75, 75, 68, 75, 73, 75, 72, 75, 77,
      73, 77, 73, 74, 75, 75, 70, 66, 74, 69, 54, 75, 75, 76, 77, 75, 70, 77, 73, 74, 70, 66,
      72, 71, 75, 70, 75, 77, 75, 70, 65, 75, 73, 77, 58, 74, 67, 75, 75, 74, 69, 75, 76, 77,
      73, 77, 72, 75, 76, 72, 75, 77, 76, 74, 73, 74, 61, 74, 75, 76, 74, 58, 68, 73, 77, 75,
      69, 66, 75, 73, 77, 75, 75, 72, 63, 63, 75, 76, 71, 72, 72, 61, 74, 75, 76, 77, 66, 64,
      71, 72
    ] 414209 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block38 : OnInterval 430433 446503 := by
  apply chainSound 446503 4791 (by decide)
    [
      73, 72, 75, 74, 76, 69, 69, 77, 64, 75, 75, 68, 75, 70, 66, 77, 75, 70, 77, 75, 67, 68,
      76, 65, 75, 76, 66, 74, 70, 75, 74, 75, 66, 76, 69, 71, 73, 77, 69, 60, 66, 75, 72, 75,
      66, 72, 63, 67, 60, 72, 68, 72, 70, 77, 75, 69, 75, 76, 74, 70, 77, 70, 69, 71, 73, 77,
      70, 77, 76, 71, 55, 75, 66, 74, 73, 75, 77, 76, 69, 68, 73, 74, 76, 77, 73, 74, 69, 72,
      70, 75, 74, 64, 74, 70, 65, 70, 77, 73, 77, 76, 72, 77, 69, 67, 72, 75, 75, 68, 72, 72,
      66, 70
    ] 430433 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block39 : OnInterval 446503 462887 := by
  apply chainSound 462887 4804 (by decide)
    [
      77, 58, 74, 73, 77, 66, 78, 66, 76, 75, 75, 78, 74, 67, 78, 78, 78, 77, 75, 78, 75, 75,
      60, 75, 70, 71, 70, 75, 63, 78, 78, 72, 77, 72, 78, 78, 73, 74, 76, 77, 78, 76, 78, 66,
      77, 75, 64, 75, 69, 71, 70, 75, 78, 78, 78, 77, 78, 67, 74, 76, 69, 78, 71, 76, 75, 75,
      68, 76, 77, 69, 69, 70, 77, 75, 78, 76, 63, 75, 68, 58, 69, 78, 75, 68, 76, 78, 72, 78,
      48, 77, 76, 66, 75, 78, 75, 77, 75, 75, 73, 77, 78, 76, 74, 45, 72, 76, 68, 61, 75, 78,
      78, 77
    ] 446503 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block40 : OnInterval 462887 479387 := by
  apply chainSound 479387 4817 (by decide)
    [
      73, 78, 77, 70, 75, 77, 67, 74, 72, 69, 66, 69, 78, 75, 76, 66, 63, 66, 71, 75, 78, 78,
      64, 78, 63, 77, 75, 66, 72, 75, 70, 77, 75, 78, 75, 75, 70, 68, 69, 78, 69, 76, 77, 78,
      78, 75, 67, 78, 71, 73, 75, 78, 77, 78, 75, 78, 76, 75, 74, 72, 67, 71, 76, 75, 75, 75,
      75, 74, 75, 75, 76, 71, 72, 73, 78, 75, 74, 75, 78, 78, 76, 74, 75, 67, 69, 74, 76, 78,
      77, 76, 78, 65, 75, 70, 75, 75, 72, 77, 76, 77, 73, 72, 78, 72, 69, 71, 72, 75, 78, 69,
      75, 78
    ] 462887 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block41 : OnInterval 479387 496007 := by
  apply chainSound 496007 4830 (by decide)
    [
      78, 48, 72, 78, 76, 59, 70, 77, 72, 78, 78, 75, 70, 69, 72, 75, 78, 63, 77, 73, 75, 78,
      75, 77, 72, 75, 78, 72, 76, 77, 78, 75, 75, 72, 60, 75, 72, 70, 77, 64, 77, 78, 76, 78,
      75, 78, 74, 76, 78, 66, 74, 76, 78, 68, 78, 69, 75, 70, 77, 78, 73, 75, 74, 73, 75, 77,
      78, 76, 74, 67, 78, 78, 78, 77, 75, 78, 76, 78, 78, 68, 76, 78, 75, 78, 75, 65, 72, 78,
      75, 78, 76, 78, 75, 78, 74, 73, 75, 77, 76, 77, 75, 76, 77, 78, 69, 76, 75, 74, 76, 62,
      69, 78
    ] 479387 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block42 : OnInterval 496007 512663 := by
  apply chainSound 512663 4843 (by decide)
    [
      78, 75, 79, 69, 77, 78, 75, 64, 77, 79, 77, 75, 78, 75, 76, 69, 74, 67, 71, 78, 76, 71,
      78, 76, 78, 78, 77, 76, 77, 78, 79, 77, 73, 78, 77, 70, 75, 77, 79, 77, 69, 79, 74, 78,
      72, 75, 70, 78, 78, 77, 60, 79, 74, 76, 74, 67, 72, 68, 69, 73, 78, 78, 75, 72, 77, 75,
      51, 76, 75, 71, 75, 79, 78, 71, 67, 77, 72, 73, 75, 75, 65, 75, 72, 79, 77, 78, 79, 72,
      69, 77, 78, 75, 72, 73, 74, 75, 58, 75, 78, 69, 77, 76, 72, 78, 75, 77, 76, 75, 74, 73,
      77, 78
    ] 496007 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block43 : OnInterval 512663 529313 := by
  apply chainSound 529313 4855 (by decide)
    [
      79, 78, 77, 76, 78, 77, 78, 75, 79, 72, 78, 78, 78, 77, 72, 72, 63, 72, 79, 77, 75, 75,
      79, 71, 78, 75, 79, 77, 78, 75, 78, 70, 63, 54, 77, 79, 75, 66, 66, 74, 79, 77, 79, 78,
      72, 74, 76, 63, 77, 79, 75, 77, 78, 79, 71, 79, 77, 79, 72, 78, 77, 58, 77, 78, 76, 75,
      74, 75, 75, 70, 66, 78, 78, 78, 74, 60, 76, 69, 71, 46, 74, 79, 78, 77, 60, 76, 66, 78,
      71, 72, 78, 79, 78, 74, 79, 77, 79, 69, 72, 77, 63, 78, 76, 78, 75, 78, 78, 75, 77, 72,
      75, 78
    ] 512663 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block44 : OnInterval 529313 546071 := by
  apply chainSound 546071 4867 (by decide)
    [
      79, 74, 66, 60, 78, 78, 78, 54, 78, 75, 79, 80, 79, 77, 69, 76, 80, 78, 76, 71, 78, 61,
      74, 79, 72, 78, 80, 66, 67, 77, 73, 78, 77, 69, 75, 79, 75, 75, 77, 70, 78, 74, 75, 76,
      75, 75, 72, 80, 78, 70, 80, 79, 77, 79, 74, 76, 66, 65, 76, 78, 75, 77, 79, 80, 69, 79,
      78, 78, 80, 79, 75, 77, 75, 70, 75, 78, 77, 78, 73, 78, 80, 72, 79, 78, 78, 77, 67, 74,
      42, 79, 80, 70, 78, 71, 75, 76, 75, 80, 79, 75, 75, 60, 75, 69, 71, 76, 80, 79, 80, 75,
      79, 77
    ] 529313 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block45 : OnInterval 546071 562871 := by
  apply chainSound 562871 4879 (by decide)
    [
      70, 78, 78, 80, 79, 68, 78, 79, 75, 80, 76, 78, 80, 79, 72, 75, 78, 80, 63, 79, 80, 75,
      79, 80, 67, 72, 77, 78, 76, 74, 76, 75, 80, 67, 77, 78, 75, 78, 76, 68, 73, 60, 75, 78,
      75, 77, 79, 69, 77, 72, 76, 80, 79, 80, 73, 74, 73, 80, 70, 71, 79, 72, 68, 75, 75, 75,
      76, 77, 73, 77, 78, 61, 75, 80, 69, 75, 75, 75, 69, 78, 79, 80, 70, 71, 73, 75, 77, 72,
      72, 78, 66, 75, 79, 78, 72, 80, 72, 75, 79, 77, 73, 80, 70, 69, 71, 76, 71, 78, 79, 80,
      72, 75
    ] 546071 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block46 : OnInterval 562871 579893 := by
  apply chainSound 579893 4890 (by decide)
    [
      75, 81, 72, 81, 67, 77, 78, 78, 81, 79, 62, 73, 74, 81, 69, 81, 81, 81, 79, 75, 78, 78,
      80, 79, 78, 75, 78, 65, 67, 81, 81, 80, 69, 75, 79, 80, 78, 78, 76, 80, 75, 64, 81, 75,
      75, 81, 78, 71, 69, 81, 79, 66, 78, 81, 81, 74, 66, 79, 81, 81, 80, 75, 79, 81, 80, 78,
      75, 79, 80, 67, 74, 76, 81, 75, 63, 65, 79, 72, 59, 75, 72, 75, 69, 76, 80, 75, 73, 81,
      65, 76, 78, 71, 79, 81, 80, 78, 81, 81, 79, 77, 75, 79, 81, 80, 75, 78, 67, 77, 73, 77,
      75, 78
    ] 562871 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block47 : OnInterval 579893 597137 := by
  apply chainSound 597137 4901 (by decide)
    [
      70, 77, 78, 72, 76, 77, 73, 81, 81, 74, 81, 79, 80, 73, 72, 69, 75, 77, 79, 78, 75, 81,
      80, 67, 77, 81, 76, 78, 68, 72, 81, 79, 78, 77, 70, 75, 75, 80, 81, 79, 78, 78, 81, 81,
      80, 79, 78, 81, 80, 75, 79, 80, 73, 78, 81, 80, 81, 78, 69, 81, 79, 78, 78, 77, 79, 78,
      65, 78, 63, 79, 81, 77, 75, 79, 80, 75, 81, 79, 80, 81, 73, 81, 81, 80, 75, 73, 74, 76,
      77, 54, 79, 77, 78, 75, 70, 74, 78, 79, 81, 80, 79, 80, 81, 72, 75, 76, 81, 81, 80, 79,
      81, 77
    ] 579893 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block48 : OnInterval 597137 614063 := by
  apply chainSound 614063 4912 (by decide)
    [
      67, 81, 80, 52, 81, 74, 78, 72, 78, 75, 58, 81, 66, 65, 78, 60, 81, 75, 79, 77, 75, 79,
      78, 78, 80, 75, 72, 78, 78, 76, 80, 76, 77, 72, 75, 81, 67, 77, 75, 76, 77, 72, 81, 78,
      81, 75, 79, 80, 66, 69, 81, 79, 66, 81, 80, 79, 78, 80, 81, 76, 80, 81, 78, 76, 80, 79,
      66, 81, 80, 79, 74, 72, 79, 78, 75, 81, 80, 79, 68, 78, 76, 75, 69, 75, 69, 80, 72, 78,
      81, 81, 76, 74, 66, 60, 75, 79, 81, 77, 78, 75, 72, 73, 80, 78, 72, 78, 64, 77, 79, 77,
      70, 80
    ] 597137 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block49 : OnInterval 614063 631307 := by
  apply chainSound 631307 4922 (by decide)
    [
      78, 79, 77, 81, 79, 66, 77, 81, 75, 79, 80, 76, 80, 82, 75, 77, 78, 73, 81, 75, 75, 81,
      57, 72, 78, 81, 75, 81, 80, 79, 81, 78, 81, 77, 82, 72, 75, 75, 65, 75, 81, 78, 76, 80,
      75, 81, 79, 80, 79, 80, 81, 81, 73, 75, 81, 81, 78, 81, 65, 78, 75, 82, 81, 80, 78, 79,
      71, 79, 80, 61, 74, 82, 74, 82, 80, 73, 77, 60, 72, 78, 78, 82, 77, 75, 76, 81, 74, 81,
      81, 73, 72, 78, 80, 60, 76, 80, 81, 82, 72, 74, 82, 77, 78, 82, 81, 81, 69, 80, 76, 81,
      77, 75
    ] 614063 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block50 : OnInterval 631307 648449 := by
  apply chainSound 648449 4932 (by decide)
    [
      82, 74, 67, 80, 70, 78, 81, 75, 81, 80, 79, 80, 78, 78, 78, 82, 80, 75, 82, 77, 78, 82,
      81, 77, 75, 78, 82, 81, 80, 70, 80, 82, 80, 79, 75, 75, 74, 82, 68, 82, 78, 71, 49, 71,
      76, 69, 78, 81, 75, 80, 79, 77, 70, 75, 78, 77, 79, 81, 69, 81, 80, 81, 70, 75, 78, 77,
      64, 66, 80, 70, 75, 59, 73, 77, 79, 80, 81, 78, 78, 75, 79, 50, 73, 81, 75, 81, 81, 77,
      82, 80, 73, 80, 78, 79, 71, 69, 81, 82, 78, 77, 72, 81, 82, 81, 81, 80, 81, 79, 78, 63,
      80, 78
    ] 631307 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block51 : OnInterval 648449 665677 := by
  apply chainSound 665677 4942 (by decide)
    [
      79, 78, 77, 82, 68, 82, 80, 78, 76, 81, 48, 81, 72, 77, 67, 81, 78, 81, 75, 78, 81, 81,
      80, 75, 81, 82, 81, 75, 81, 81, 80, 60, 78, 70, 80, 79, 75, 65, 82, 75, 78, 81, 77, 69,
      78, 76, 81, 78, 77, 79, 77, 78, 79, 81, 71, 79, 74, 82, 81, 69, 74, 82, 77, 76, 77, 79,
      81, 80, 82, 80, 67, 80, 81, 78, 82, 77, 81, 82, 75, 78, 75, 80, 79, 77, 66, 72, 76, 77,
      73, 80, 70, 71, 76, 78, 77, 78, 81, 79, 77, 72, 82, 80, 69, 76, 81, 77, 67, 81, 80, 78,
      79, 75
    ] 648449 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block52 : OnInterval 665677 682967 := by
  apply chainSound 682967 4952 (by decide)
    [
      83, 75, 75, 79, 83, 70, 83, 82, 83, 70, 68, 76, 83, 82, 74, 75, 72, 57, 82, 83, 78, 73,
      66, 74, 76, 78, 77, 78, 76, 81, 74, 75, 76, 83, 81, 81, 78, 81, 81, 78, 81, 76, 83, 78,
      78, 79, 83, 82, 78, 78, 75, 45, 74, 81, 76, 71, 79, 66, 78, 80, 75, 79, 80, 82, 66, 77,
      81, 76, 74, 81, 76, 80, 79, 83, 78, 79, 81, 77, 70, 78, 75, 83, 82, 74, 81, 67, 80, 81,
      76, 78, 81, 80, 72, 79, 83, 81, 81, 79, 81, 83, 78, 79, 81, 80, 79, 74, 79, 68, 79, 83,
      61, 74
    ] 665677 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block53 : OnInterval 682967 700471 := by
  apply chainSound 700471 4961 (by decide)
    [
      81, 72, 82, 83, 78, 82, 65, 82, 81, 74, 78, 79, 80, 70, 80, 79, 81, 80, 79, 80, 55, 77,
      78, 76, 83, 78, 79, 83, 82, 83, 81, 76, 75, 83, 78, 79, 83, 75, 82, 83, 78, 79, 81, 83,
      79, 75, 77, 76, 68, 82, 80, 79, 78, 83, 79, 74, 82, 80, 79, 83, 78, 82, 78, 78, 80, 79,
      83, 79, 83, 81, 67, 77, 75, 82, 78, 77, 79, 74, 82, 69, 77, 73, 65, 72, 78, 82, 83, 76,
      83, 81, 81, 81, 75, 82, 72, 81, 59, 81, 82, 77, 69, 81, 81, 82, 83, 79, 78, 83, 82, 72,
      80, 70
    ] 682967 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block54 : OnInterval 700471 718051 := by
  apply chainSound 718051 4970 (by decide)
    [
      81, 78, 80, 70, 69, 78, 83, 81, 76, 77, 81, 81, 81, 60, 82, 75, 72, 81, 75, 83, 81, 81,
      73, 80, 66, 78, 70, 83, 82, 83, 82, 80, 61, 77, 79, 81, 80, 82, 83, 78, 81, 79, 80, 81,
      73, 83, 82, 80, 81, 82, 77, 82, 75, 81, 72, 80, 82, 83, 78, 79, 83, 81, 81, 81, 75, 75,
      82, 83, 82, 78, 83, 82, 83, 81, 79, 77, 70, 83, 76, 74, 76, 83, 76, 77, 82, 80, 82, 66,
      80, 79, 75, 80, 81, 82, 80, 76, 75, 80, 72, 79, 80, 81, 75, 78, 82, 80, 79, 78, 83, 79,
      83, 67
    ] 700471 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block55 : OnInterval 718051 735697 := by
  apply chainSound 735697 4980 (by decide)
    [
      68, 81, 82, 74, 76, 80, 73, 81, 83, 76, 77, 79, 74, 81, 76, 77, 78, 82, 83, 84, 78, 81,
      82, 65, 84, 81, 84, 84, 76, 69, 77, 84, 78, 82, 84, 84, 83, 64, 83, 72, 84, 76, 81, 77,
      76, 77, 82, 83, 73, 80, 81, 75, 79, 77, 84, 76, 84, 84, 81, 75, 83, 78, 79, 75, 81, 72,
      71, 84, 82, 81, 72, 78, 77, 81, 81, 76, 77, 82, 83, 75, 81, 72, 57, 81, 75, 81, 76, 84,
      74, 79, 83, 84, 81, 82, 77, 81, 84, 79, 80, 69, 82, 83, 73, 84, 83, 81, 84, 82, 75, 81,
      80, 82
    ] 718051 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block56 : OnInterval 735697 753257 := by
  apply chainSound 753257 4989 (by decide)
    [
      78, 80, 84, 49, 84, 80, 67, 81, 78, 74, 73, 78, 77, 78, 81, 70, 71, 79, 84, 84, 83, 82,
      83, 73, 77, 73, 81, 81, 84, 84, 84, 83, 78, 81, 76, 60, 74, 84, 61, 81, 77, 82, 84, 84,
      81, 59, 82, 81, 77, 75, 81, 84, 78, 75, 84, 79, 75, 84, 83, 79, 75, 84, 81, 84, 80, 82,
      84, 81, 78, 84, 83, 73, 84, 83, 70, 78, 81, 80, 76, 78, 69, 77, 81, 84, 78, 78, 84, 60,
      58, 80, 81, 84, 76, 77, 69, 79, 75, 77, 84, 84, 81, 81, 78, 79, 80, 82, 84, 77, 84, 81,
      79, 83
    ] 735697 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block57 : OnInterval 753257 771073 := by
  apply chainSound 771073 4997 (by decide)
    [
      82, 84, 81, 54, 84, 78, 80, 73, 81, 80, 84, 84, 82, 81, 77, 82, 84, 84, 83, 75, 82, 83,
      75, 72, 67, 81, 77, 72, 84, 84, 81, 82, 84, 71, 78, 84, 78, 75, 84, 84, 82, 83, 82, 84,
      81, 78, 75, 84, 77, 81, 84, 81, 84, 84, 79, 75, 71, 81, 84, 82, 83, 84, 75, 82, 78, 80,
      78, 84, 81, 79, 81, 65, 84, 84, 84, 81, 75, 84, 76, 81, 83, 73, 84, 75, 83, 75, 82, 81,
      75, 80, 79, 74, 82, 84, 84, 81, 78, 77, 79, 84, 75, 65, 70, 81, 77, 84, 75, 78, 81, 81,
      84, 82
    ] 753257 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block58 : OnInterval 771073 788789 := by
  apply chainSound 788789 5006 (by decide)
    [
      80, 85, 83, 85, 80, 81, 85, 81, 72, 83, 82, 81, 65, 79, 78, 69, 84, 80, 84, 66, 69, 82,
      81, 80, 72, 78, 73, 84, 81, 84, 78, 78, 84, 83, 73, 80, 81, 75, 85, 75, 80, 66, 78, 75,
      82, 83, 75, 82, 80, 85, 84, 68, 73, 83, 85, 75, 81, 81, 83, 82, 84, 84, 81, 83, 85, 72,
      75, 69, 84, 81, 81, 81, 84, 75, 75, 74, 85, 81, 75, 83, 70, 81, 72, 84, 81, 74, 85, 75,
      81, 84, 75, 83, 76, 84, 81, 81, 81, 78, 75, 81, 84, 74, 72, 84, 84, 70, 81, 84, 77, 79,
      71, 84
    ] 771073 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block59 : OnInterval 788789 806857 := by
  apply chainSound 806857 5014 (by decide)
    [
      85, 81, 65, 84, 85, 80, 67, 84, 84, 80, 84, 81, 85, 84, 81, 84, 83, 78, 76, 71, 85, 77,
      85, 80, 75, 81, 85, 84, 78, 84, 84, 84, 81, 65, 82, 83, 85, 69, 68, 82, 81, 84, 81, 75,
      84, 77, 78, 76, 80, 81, 85, 84, 84, 71, 82, 77, 85, 81, 74, 85, 68, 84, 85, 80, 70, 81,
      78, 84, 80, 81, 82, 84, 83, 85, 77, 85, 83, 82, 84, 81, 80, 84, 85, 84, 83, 73, 84, 78,
      80, 79, 83, 85, 81, 81, 83, 81, 85, 84, 83, 85, 84, 84, 77, 85, 84, 80, 79, 77, 85, 83,
      85, 69
    ] 788789 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block60 : OnInterval 806857 824671 := by
  apply chainSound 824671 5023 (by decide)
    [
      80, 85, 75, 78, 77, 85, 78, 69, 78, 77, 84, 81, 84, 84, 78, 82, 81, 84, 83, 84, 84, 85,
      81, 83, 85, 80, 82, 78, 83, 78, 85, 84, 83, 84, 73, 81, 84, 83, 72, 72, 66, 85, 77, 82,
      83, 73, 80, 78, 79, 83, 85, 78, 71, 84, 84, 82, 84, 75, 80, 85, 84, 77, 75, 78, 82, 83,
      73, 83, 82, 84, 74, 82, 84, 71, 82, 75, 75, 66, 84, 83, 85, 84, 71, 73, 81, 84, 77, 82,
      81, 60, 84, 71, 79, 78, 83, 85, 80, 52, 83, 82, 72, 72, 84, 77, 84, 84, 84, 81, 76, 74,
      81, 85
    ] 806857 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block61 : OnInterval 824671 842747 := by
  apply chainSound 842747 5031 (by decide)
    [
      81, 84, 80, 84, 81, 85, 84, 84, 78, 80, 82, 72, 81, 78, 74, 82, 83, 82, 80, 81, 84, 84,
      85, 84, 83, 79, 84, 84, 81, 81, 84, 77, 84, 70, 84, 77, 82, 81, 75, 75, 81, 80, 85, 84,
      84, 81, 84, 80, 85, 80, 85, 80, 82, 84, 84, 83, 82, 80, 85, 81, 84, 83, 84, 79, 77, 84,
      85, 84, 84, 72, 84, 74, 61, 84, 81, 66, 84, 84, 80, 82, 83, 73, 78, 75, 77, 84, 70, 71,
      78, 76, 83, 85, 78, 78, 77, 73, 84, 81, 81, 83, 81, 84, 81, 84, 85, 77, 85, 84, 80, 85,
      84, 80
    ] 824671 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block62 : OnInterval 842747 860647 := by
  apply chainSound 860647 5039 (by decide)
    [
      70, 78, 84, 86, 85, 74, 70, 86, 85, 84, 86, 64, 63, 75, 86, 81, 85, 84, 86, 85, 86, 79,
      83, 76, 84, 81, 80, 84, 73, 78, 77, 84, 73, 78, 74, 84, 81, 78, 76, 86, 85, 83, 67, 86,
      85, 75, 84, 86, 69, 78, 85, 80, 76, 86, 84, 70, 77, 85, 83, 84, 58, 80, 85, 83, 82, 84,
      74, 79, 83, 85, 83, 82, 84, 84, 86, 79, 80, 76, 80, 63, 85, 83, 79, 83, 82, 84, 65, 82,
      78, 84, 86, 81, 79, 60, 77, 85, 84, 78, 83, 75, 85, 84, 86, 85, 84, 74, 76, 84, 57, 84,
      84, 84
    ] 842747 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block63 : OnInterval 860647 878893 := by
  apply chainSound 878893 5047 (by decide)
    [
      86, 76, 84, 80, 70, 80, 81, 84, 84, 82, 81, 80, 78, 85, 86, 85, 71, 84, 84, 85, 77, 85,
      78, 86, 78, 55, 86, 85, 84, 86, 81, 84, 82, 84, 84, 74, 82, 71, 85, 84, 80, 81, 73, 77,
      85, 84, 84, 80, 84, 82, 84, 86, 85, 84, 84, 83, 78, 75, 85, 81, 78, 78, 84, 83, 72, 84,
      84, 85, 75, 78, 84, 81, 78, 84, 72, 84, 81, 86, 85, 78, 84, 86, 84, 75, 75, 85, 83, 78,
      85, 86, 84, 82, 84, 86, 85, 80, 85, 80, 84, 84, 81, 73, 83, 85, 83, 85, 84, 81, 86, 81,
      85, 75
    ] 860647 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block64 : OnInterval 878893 897163 := by
  apply chainSound 897163 5054 (by decide)
    [
      84, 83, 82, 81, 84, 80, 81, 84, 78, 82, 86, 84, 79, 84, 86, 85, 86, 69, 85, 84, 86, 85,
      86, 81, 75, 75, 84, 79, 86, 73, 86, 76, 81, 80, 82, 86, 85, 84, 81, 80, 81, 79, 81, 83,
      75, 70, 81, 59, 76, 84, 83, 85, 80, 84, 84, 85, 86, 81, 85, 84, 83, 85, 71, 85, 86, 79,
      72, 84, 84, 86, 84, 75, 76, 86, 85, 74, 85, 86, 85, 83, 84, 85, 86, 85, 86, 85, 84, 81,
      84, 80, 84, 81, 85, 86, 85, 81, 83, 84, 70, 83, 85, 84, 83, 85, 71, 66, 84, 84, 72, 78,
      85, 78
    ] 878893 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block65 : OnInterval 897163 915641 := by
  apply chainSound 915641 5062 (by decide)
    [
      83, 85, 86, 79, 77, 85, 87, 83, 85, 80, 82, 87, 80, 85, 84, 86, 85, 84, 81, 80, 84, 81,
      76, 84, 84, 81, 86, 84, 81, 84, 85, 86, 85, 87, 80, 82, 86, 85, 78, 77, 82, 77, 84, 85,
      87, 84, 66, 77, 81, 82, 87, 87, 81, 83, 87, 84, 85, 83, 82, 84, 84, 83, 78, 85, 84, 87,
      74, 85, 86, 84, 84, 82, 81, 78, 84, 83, 87, 76, 80, 70, 77, 84, 81, 85, 78, 81, 83, 87,
      85, 78, 83, 85, 84, 69, 87, 84, 80, 85, 83, 76, 86, 85, 75, 81, 87, 81, 86, 85, 86, 84,
      84, 81
    ] 897163 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block66 : OnInterval 915641 934319 := by
  apply chainSound 934319 5069 (by decide)
    [
      79, 87, 84, 75, 86, 85, 77, 87, 81, 84, 85, 86, 85, 84, 86, 79, 84, 86, 76, 83, 85, 86,
      73, 87, 80, 85, 86, 84, 76, 83, 87, 87, 82, 86, 87, 85, 75, 86, 82, 84, 86, 87, 85, 83,
      87, 82, 80, 85, 84, 87, 84, 86, 85, 84, 84, 84, 83, 72, 81, 84, 76, 86, 85, 81, 87, 83,
      85, 87, 86, 87, 87, 87, 85, 80, 81, 87, 67, 86, 87, 81, 87, 85, 87, 87, 86, 84, 84, 79,
      86, 79, 87, 86, 84, 85, 83, 87, 84, 81, 84, 84, 82, 81, 78, 81, 86, 78, 84, 87, 84, 85,
      75, 80
    ] 915641 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block67 : OnInterval 934319 952829 := by
  apply chainSound 952829 5077 (by decide)
    [
      85, 75, 86, 85, 84, 77, 79, 80, 85, 56, 75, 87, 87, 78, 87, 79, 80, 79, 86, 79, 86, 87,
      87, 81, 87, 85, 75, 84, 69, 87, 84, 75, 83, 85, 86, 85, 86, 85, 86, 84, 85, 84, 87, 87,
      83, 78, 85, 87, 74, 85, 84, 87, 87, 87, 86, 84, 85, 86, 82, 81, 80, 82, 84, 84, 80, 87,
      82, 75, 77, 75, 85, 86, 87, 73, 84, 86, 87, 85, 86, 85, 86, 81, 84, 73, 81, 84, 77, 84,
      81, 85, 68, 85, 87, 80, 84, 85, 66, 83, 85, 87, 84, 86, 84, 85, 86, 81, 82, 87, 86, 87,
      85, 86
    ] 934319 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block68 : OnInterval 952829 971111 := by
  apply chainSound 971111 5084 (by decide)
    [
      84, 87, 85, 83, 87, 85, 80, 85, 71, 87, 87, 79, 81, 81, 83, 82, 87, 81, 87, 77, 82, 83,
      78, 84, 76, 83, 85, 72, 84, 86, 82, 63, 75, 84, 86, 70, 78, 80, 87, 84, 69, 85, 86, 69,
      85, 80, 84, 85, 86, 87, 87, 81, 84, 87, 78, 87, 85, 74, 84, 75, 82, 86, 79, 81, 72, 87,
      81, 75, 84, 86, 85, 83, 84, 85, 87, 83, 81, 87, 87, 75, 57, 85, 84, 84, 65, 70, 87, 74,
      79, 81, 84, 80, 87, 78, 87, 84, 67, 84, 78, 83, 87, 87, 84, 84, 81, 81, 85, 86, 85, 87,
      83, 84
    ] 952829 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block69 : OnInterval 971111 989671 := by
  apply chainSound 989671 5091 (by decide)
    [
      85, 80, 75, 88, 86, 87, 82, 83, 85, 87, 78, 78, 77, 84, 88, 81, 80, 85, 86, 88, 81, 87,
      77, 81, 87, 88, 80, 72, 82, 66, 86, 79, 84, 86, 87, 87, 88, 87, 80, 78, 87, 88, 83, 87,
      78, 87, 87, 88, 84, 81, 72, 75, 86, 79, 86, 87, 82, 87, 84, 87, 84, 78, 86, 81, 79, 87,
      84, 86, 87, 82, 84, 87, 80, 82, 87, 78, 87, 86, 85, 87, 83, 84, 85, 83, 78, 82, 77, 85,
      81, 84, 84, 86, 85, 84, 77, 88, 86, 70, 84, 77, 78, 82, 83, 84, 87, 85, 83, 76, 72, 87,
      80, 82
    ] 971111 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block70 : OnInterval 989671 1008209 := by
  apply chainSound 1008209 5098 (by decide)
    [
      84, 87, 84, 84, 87, 75, 84, 84, 86, 88, 87, 86, 85, 75, 80, 88, 81, 84, 87, 87, 87, 78,
      87, 81, 83, 85, 80, 85, 66, 83, 85, 86, 82, 87, 83, 82, 78, 84, 86, 78, 79, 81, 81, 84,
      87, 87, 68, 87, 88, 80, 87, 82, 80, 81, 73, 86, 75, 84, 84, 88, 80, 79, 84, 87, 78, 80,
      87, 84, 88, 86, 84, 87, 88, 78, 84, 84, 84, 83, 87, 88, 84, 83, 81, 81, 78, 88, 87, 83,
      87, 87, 73, 83, 85, 80, 87, 88, 59, 88, 77, 88, 87, 86, 85, 83, 85, 65, 84, 70, 87, 80,
      76, 83
    ] 989671 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block71 : OnInterval 1008209 1026761 := by
  apply chainSound 1026761 5105 (by decide)
    [
      85, 84, 86, 76, 83, 85, 83, 82, 66, 87, 80, 88, 87, 83, 84, 87, 88, 77, 84, 75, 84, 75,
      76, 84, 87, 84, 87, 84, 86, 75, 88, 87, 84, 86, 82, 83, 84, 76, 78, 86, 84, 87, 73, 86,
      73, 71, 75, 85, 87, 80, 88, 87, 87, 86, 87, 78, 87, 88, 80, 82, 84, 78, 87, 84, 84, 86,
      84, 87, 88, 86, 76, 86, 79, 78, 87, 83, 88, 78, 87, 80, 82, 86, 87, 84, 81, 82, 86, 79,
      83, 85, 84, 83, 88, 63, 87, 80, 87, 78, 88, 87, 87, 81, 81, 81, 84, 78, 86, 81, 78, 85,
      83, 84
    ] 1008209 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block72 : OnInterval 1026761 1045277 := by
  apply chainSound 1045277 5112 (by decide)
    [
      78, 75, 87, 88, 87, 84, 86, 88, 83, 82, 80, 88, 84, 86, 88, 72, 84, 83, 88, 84, 68, 85,
      83, 88, 87, 74, 75, 84, 81, 85, 69, 69, 72, 84, 86, 79, 77, 79, 83, 88, 83, 81, 88, 72,
      86, 79, 81, 87, 87, 84, 86, 85, 86, 88, 71, 84, 85, 84, 87, 80, 84, 79, 86, 87, 88, 87,
      83, 82, 87, 86, 87, 84, 81, 87, 81, 87, 87, 82, 78, 81, 84, 86, 82, 84, 81, 78, 87, 83,
      84, 88, 84, 80, 70, 84, 80, 82, 83, 81, 85, 84, 84, 86, 67, 78, 84, 87, 86, 88, 81, 80,
      88, 80
    ] 1026761 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block73 : OnInterval 1045277 1063913 := by
  apply chainSound 1063913 5118 (by decide)
    [
      75, 73, 83, 84, 87, 88, 78, 87, 62, 78, 88, 78, 87, 89, 85, 83, 88, 78, 86, 84, 81, 88,
      83, 88, 87, 78, 89, 76, 77, 88, 81, 86, 88, 87, 84, 83, 88, 89, 81, 82, 86, 85, 84, 86,
      79, 86, 82, 84, 89, 84, 76, 47, 85, 84, 86, 88, 87, 65, 82, 87, 86, 84, 79, 89, 76, 80,
      87, 84, 73, 83, 85, 89, 63, 85, 83, 82, 87, 86, 88, 89, 88, 89, 84, 84, 76, 84, 83, 87,
      82, 83, 87, 84, 79, 87, 86, 78, 87, 82, 86, 85, 81, 86, 88, 89, 87, 88, 86, 82, 83, 76,
      89, 87
    ] 1045277 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block74 : OnInterval 1063913 1082533 := by
  apply chainSound 1082533 5125 (by decide)
    [
      87, 88, 84, 81, 89, 85, 84, 87, 75, 84, 86, 88, 81, 86, 82, 87, 84, 71, 76, 78, 86, 79,
      89, 87, 81, 88, 89, 87, 84, 81, 79, 87, 89, 79, 84, 87, 71, 82, 87, 74, 87, 84, 73, 87,
      89, 85, 86, 88, 83, 64, 83, 73, 84, 78, 66, 77, 84, 85, 80, 84, 82, 75, 83, 87, 88, 57,
      83, 87, 88, 87, 84, 83, 85, 86, 87, 87, 87, 88, 77, 81, 84, 79, 86, 79, 89, 88, 89, 88,
      87, 86, 84, 84, 85, 86, 75, 84, 79, 83, 87, 88, 80, 87, 85, 68, 87, 88, 87, 86, 84, 85,
      86, 82
    ] 1063913 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block75 : OnInterval 1082533 1101143 := by
  apply chainSound 1101143 5131 (by decide)
    [
      87, 87, 89, 76, 83, 82, 86, 84, 85, 84, 77, 87, 88, 84, 81, 84, 84, 81, 84, 86, 78, 78,
      85, 78, 87, 89, 73, 66, 75, 89, 88, 89, 73, 87, 74, 81, 85, 83, 85, 78, 83, 85, 80, 85,
      84, 81, 87, 84, 78, 86, 84, 85, 75, 86, 87, 88, 87, 84, 78, 86, 82, 89, 88, 83, 84, 81,
      87, 88, 84, 86, 78, 76, 89, 87, 78, 87, 88, 77, 84, 88, 71, 87, 82, 86, 87, 79, 89, 85,
      86, 81, 78, 75, 82, 84, 81, 84, 84, 86, 84, 75, 87, 88, 80, 87, 87, 87, 75, 81, 85, 89,
      73, 83
    ] 1082533 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block76 : OnInterval 1101143 1119649 := by
  apply chainSound 1119649 5138 (by decide)
    [
      88, 77, 88, 81, 78, 75, 81, 89, 63, 87, 82, 83, 85, 57, 89, 87, 88, 71, 88, 81, 89, 87,
      84, 84, 82, 83, 87, 70, 86, 73, 86, 81, 84, 79, 81, 84, 77, 87, 88, 78, 87, 84, 80, 88,
      75, 78, 80, 88, 84, 80, 82, 86, 88, 87, 84, 86, 85, 78, 80, 87, 88, 86, 85, 86, 82, 75,
      77, 85, 89, 85, 84, 86, 85, 87, 77, 88, 87, 86, 82, 84, 84, 87, 84, 83, 85, 86, 87, 85,
      84, 83, 76, 71, 88, 77, 79, 87, 83, 84, 73, 84, 69, 87, 78, 84, 83, 88, 89, 78, 88, 87,
      65, 88
    ] 1101143 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block77 : OnInterval 1119649 1138591 := by
  apply chainSound 1138591 5144 (by decide)
    [
      87, 89, 79, 89, 90, 85, 81, 89, 88, 90, 87, 90, 81, 86, 85, 89, 90, 81, 90, 76, 87, 86,
      81, 88, 87, 90, 86, 73, 77, 78, 55, 80, 90, 85, 90, 90, 87, 90, 83, 90, 79, 87, 63, 77,
      88, 90, 90, 90, 90, 81, 90, 81, 89, 76, 84, 89, 90, 90, 88, 89, 85, 90, 89, 79, 86, 82,
      80, 84, 81, 85, 89, 90, 64, 84, 78, 89, 84, 72, 87, 90, 90, 90, 76, 86, 88, 78, 60, 87,
      90, 87, 90, 90, 83, 82, 90, 90, 86, 87, 90, 88, 87, 86, 85, 90, 84, 86, 90, 84, 85, 63,
      89, 70
    ] 1119649 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block78 : OnInterval 1138591 1157449 := by
  apply chainSound 1157449 5150 (by decide)
    [
      90, 74, 84, 88, 80, 82, 77, 90, 90, 90, 84, 85, 84, 90, 86, 90, 79, 86, 82, 78, 81, 90,
      86, 84, 85, 75, 86, 78, 87, 87, 85, 80, 88, 90, 89, 90, 88, 77, 85, 90, 84, 87, 80, 88,
      86, 85, 89, 81, 90, 81, 90, 87, 82, 84, 86, 90, 90, 81, 88, 72, 84, 60, 86, 90, 90, 90,
      85, 87, 66, 87, 90, 90, 87, 78, 87, 78, 84, 84, 77, 90, 87, 67, 84, 87, 89, 84, 84, 90,
      78, 82, 72, 65, 88, 87, 90, 86, 87, 90, 78, 87, 90, 58, 87, 90, 87, 84, 81, 89, 90, 81,
      84, 85
    ] 1138591 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block79 : OnInterval 1157449 1176641 := by
  apply chainSound 1176641 5156 (by decide)
    [
      89, 82, 89, 85, 89, 87, 81, 87, 90, 90, 76, 89, 73, 90, 83, 85, 90, 80, 85, 89, 90, 90,
      88, 89, 90, 85, 84, 90, 87, 89, 88, 87, 89, 90, 84, 82, 89, 90, 87, 82, 83, 78, 90, 90,
      87, 88, 90, 86, 85, 90, 68, 88, 83, 81, 81, 90, 84, 85, 89, 87, 90, 90, 84, 88, 81, 90,
      89, 90, 88, 84, 83, 70, 90, 83, 88, 87, 80, 90, 88, 84, 68, 90, 88, 84, 90, 80, 85, 83,
      85, 90, 83, 90, 84, 90, 81, 84, 88, 90, 89, 88, 87, 86, 88, 74, 85, 80, 90, 87, 78, 78,
      85, 89
    ] 1157449 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block80 : OnInterval 1176641 1195919 := by
  apply chainSound 1195919 5162 (by decide)
    [
      85, 86, 88, 86, 88, 87, 89, 90, 87, 90, 82, 81, 89, 75, 88, 90, 90, 87, 86, 85, 90, 84,
      72, 90, 90, 74, 85, 87, 87, 80, 75, 73, 90, 89, 90, 90, 88, 87, 69, 86, 81, 84, 90, 84,
      87, 90, 90, 88, 89, 82, 90, 81, 90, 90, 90, 84, 90, 89, 90, 84, 90, 85, 83, 88, 87, 89,
      85, 78, 75, 90, 75, 80, 90, 87, 90, 85, 90, 90, 83, 85, 83, 79, 90, 90, 89, 82, 89, 90,
      84, 87, 90, 87, 88, 89, 85, 90, 86, 90, 90, 88, 90, 72, 90, 89, 79, 89, 90, 90, 85, 90,
      87, 89
    ] 1176641 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block81 : OnInterval 1195919 1215029 := by
  apply chainSound 1215029 5168 (by decide)
    [
      85, 90, 81, 89, 82, 83, 87, 88, 89, 82, 84, 86, 90, 85, 80, 90, 79, 90, 84, 81, 90, 90,
      84, 75, 90, 87, 83, 87, 84, 90, 90, 76, 89, 85, 90, 86, 90, 88, 86, 87, 90, 82, 80, 90,
      87, 88, 77, 85, 84, 84, 86, 87, 79, 89, 90, 87, 90, 75, 87, 85, 83, 88, 87, 83, 87, 90,
      90, 67, 81, 71, 90, 84, 76, 90, 84, 87, 83, 90, 85, 89, 76, 90, 89, 87, 85, 69, 84, 90,
      81, 84, 90, 78, 89, 90, 70, 90, 80, 84, 84, 90, 90, 87, 90, 90, 85, 90, 89, 87, 78, 90,
      90, 90
    ] 1195919 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block82 : OnInterval 1215029 1234271 := by
  apply chainSound 1234271 5174 (by decide)
    [
      90, 91, 89, 87, 90, 84, 91, 89, 84, 90, 87, 87, 91, 90, 89, 87, 91, 89, 90, 91, 89, 90,
      91, 90, 89, 91, 90, 74, 90, 91, 77, 91, 75, 90, 89, 91, 90, 74, 78, 87, 91, 87, 87, 81,
      90, 87, 90, 87, 83, 87, 88, 90, 83, 91, 78, 86, 91, 83, 87, 88, 90, 81, 81, 90, 81, 89,
      91, 89, 81, 64, 86, 72, 81, 91, 90, 86, 90, 87, 73, 84, 81, 90, 89, 91, 90, 84, 80, 85,
      80, 85, 90, 81, 90, 87, 78, 87, 87, 86, 73, 90, 84, 90, 90, 90, 83, 88, 89, 78, 64, 84,
      84, 77
    ] 1215029 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block83 : OnInterval 1234271 1253171 := by
  apply chainSound 1253171 5180 (by decide)
    [
      84, 87, 88, 90, 90, 89, 88, 83, 82, 83, 87, 82, 90, 75, 80, 87, 88, 86, 91, 65, 91, 90,
      89, 91, 84, 84, 87, 87, 90, 87, 89, 87, 85, 87, 78, 75, 68, 91, 60, 89, 82, 89, 88, 71,
      90, 91, 86, 90, 78, 85, 77, 60, 84, 84, 87, 84, 84, 91, 81, 89, 81, 85, 83, 79, 90, 90,
      80, 82, 81, 89, 91, 77, 91, 89, 81, 91, 84, 89, 90, 87, 84, 91, 89, 87, 85, 87, 86, 91,
      86, 79, 81, 90, 75, 90, 77, 85, 87, 83, 88, 68, 75, 67, 89, 78, 82, 84, 77, 87, 91, 90,
      89, 87
    ] 1234271 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block84 : OnInterval 1253171 1272461 := by
  apply chainSound 1272461 5185 (by decide)
    [
      88, 87, 90, 75, 90, 86, 87, 90, 91, 84, 87, 89, 84, 91, 75, 90, 84, 86, 85, 86, 88, 78,
      89, 91, 90, 80, 88, 86, 91, 83, 91, 90, 89, 84, 87, 91, 90, 87, 86, 91, 86, 90, 85, 78,
      90, 89, 88, 78, 80, 91, 90, 68, 87, 85, 90, 90, 78, 90, 80, 82, 83, 88, 90, 90, 87, 87,
      90, 84, 89, 81, 91, 90, 84, 90, 77, 84, 85, 90, 84, 77, 87, 90, 87, 91, 87, 90, 80, 91,
      89, 88, 84, 90, 90, 86, 88, 84, 90, 87, 84, 81, 84, 81, 86, 87, 91, 86, 69, 91, 90, 90,
      89, 66
    ] 1253171 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block85 : OnInterval 1272461 1291691 := by
  apply chainSound 1291691 5191 (by decide)
    [
      90, 85, 90, 84, 87, 87, 90, 78, 87, 83, 90, 73, 81, 90, 84, 90, 81, 90, 89, 90, 85, 87,
      83, 90, 91, 89, 82, 77, 91, 90, 87, 84, 84, 75, 89, 85, 90, 90, 90, 90, 81, 87, 89, 76,
      80, 75, 70, 89, 91, 78, 89, 91, 87, 90, 90, 84, 90, 84, 89, 87, 91, 89, 63, 90, 87, 90,
      85, 71, 90, 90, 90, 85, 89, 88, 77, 90, 84, 82, 90, 78, 87, 90, 90, 80, 82, 86, 91, 90,
      83, 90, 87, 76, 90, 89, 81, 79, 81, 89, 90, 91, 80, 90, 88, 89, 91, 90, 87, 89, 88, 90,
      83, 84
    ] 1272461 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block86 : OnInterval 1291691 1310809 := by
  apply chainSound 1310809 5197 (by decide)
    [
      85, 84, 74, 88, 78, 75, 86, 90, 84, 91, 90, 80, 84, 85, 81, 84, 57, 84, 86, 90, 90, 82,
      83, 84, 84, 87, 82, 78, 90, 90, 87, 90, 86, 91, 81, 83, 67, 90, 84, 83, 82, 86, 82, 87,
      83, 76, 87, 84, 89, 87, 90, 90, 90, 84, 91, 80, 87, 87, 75, 79, 90, 89, 88, 90, 90, 84,
      86, 88, 87, 89, 85, 84, 77, 88, 90, 81, 81, 90, 84, 86, 84, 90, 84, 85, 90, 87, 89, 91,
      72, 78, 87, 87, 90, 90, 90, 86, 90, 90, 88, 90, 89, 90, 91, 86, 90, 84, 90, 87, 85, 90,
      80, 88
    ] 1291691 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block87 : OnInterval 1310809 1330313 := by
  apply chainSound 1330313 5202 (by decide)
    [
      92, 90, 90, 85, 89, 78, 85, 92, 91, 87, 86, 91, 83, 76, 92, 87, 87, 91, 90, 92, 90, 88,
      90, 92, 88, 92, 78, 88, 89, 82, 90, 90, 86, 88, 92, 84, 88, 90, 92, 91, 90, 89, 84, 87,
      88, 92, 85, 89, 91, 90, 90, 80, 82, 90, 65, 90, 91, 92, 90, 78, 84, 91, 89, 87, 91, 83,
      87, 75, 90, 90, 90, 88, 92, 75, 90, 87, 82, 90, 90, 81, 87, 83, 85, 78, 92, 85, 87, 92,
      91, 84, 90, 89, 87, 87, 85, 87, 74, 90, 81, 90, 88, 83, 88, 89, 91, 89, 85, 90, 81, 86,
      79, 92
    ] 1310809 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block88 : OnInterval 1330313 1349897 := by
  apply chainSound 1349897 5207 (by decide)
    [
      90, 78, 91, 83, 78, 90, 90, 85, 87, 80, 88, 89, 91, 90, 92, 87, 91, 92, 82, 89, 84, 87,
      78, 90, 87, 91, 87, 80, 91, 92, 78, 90, 85, 86, 91, 87, 90, 90, 83, 88, 89, 91, 92, 88,
      89, 91, 86, 91, 89, 90, 84, 91, 83, 91, 86, 91, 89, 84, 90, 82, 89, 81, 90, 85, 92, 82,
      83, 87, 90, 85, 84, 92, 88, 87, 90, 92, 85, 87, 86, 85, 90, 92, 91, 92, 82, 92, 90, 85,
      89, 87, 90, 88, 92, 85, 92, 85, 83, 90, 82, 90, 92, 88, 90, 92, 66, 88, 84, 86, 91, 81,
      90, 92
    ] 1330313 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block89 : OnInterval 1349897 1369021 := by
  apply chainSound 1369021 5213 (by decide)
    [
      88, 92, 73, 80, 90, 84, 91, 87, 86, 91, 89, 91, 84, 84, 86, 90, 90, 90, 84, 90, 87, 91,
      92, 82, 83, 73, 89, 85, 80, 85, 86, 90, 84, 90, 88, 81, 80, 91, 89, 91, 81, 78, 36, 80,
      88, 90, 92, 91, 90, 87, 87, 86, 87, 70, 87, 78, 77, 79, 87, 92, 91, 86, 90, 90, 85, 86,
      82, 90, 90, 86, 85, 92, 84, 90, 90, 76, 84, 86, 90, 87, 88, 92, 82, 81, 84, 89, 91, 90,
      89, 82, 77, 58, 89, 79, 87, 74, 78, 90, 88, 90, 92, 91, 90, 84, 92, 91, 87, 81, 90, 77,
      82, 87
    ] 1349897 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block90 : OnInterval 1369021 1388483 := by
  apply chainSound 1388483 5218 (by decide)
    [
      90, 86, 84, 91, 87, 90, 75, 90, 90, 81, 92, 90, 75, 84, 88, 86, 85, 89, 90, 82, 81, 83,
      91, 90, 90, 90, 84, 92, 90, 79, 84, 90, 92, 72, 88, 90, 89, 90, 91, 84, 90, 63, 86, 87,
      87, 90, 90, 90, 91, 90, 87, 90, 92, 90, 91, 92, 90, 84, 90, 91, 92, 82, 86, 85, 89, 88,
      81, 87, 90, 92, 90, 81, 90, 91, 89, 90, 85, 90, 75, 90, 90, 92, 87, 85, 81, 92, 90, 79,
      78, 86, 91, 89, 87, 90, 88, 92, 88, 84, 87, 86, 87, 85, 83, 88, 92, 60, 84, 91, 89, 90,
      91, 80
    ] 1369021 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block91 : OnInterval 1388483 1407751 := by
  apply chainSound 1407751 5223 (by decide)
    [
      88, 89, 85, 92, 90, 90, 88, 92, 88, 83, 84, 90, 91, 92, 81, 79, 87, 90, 69, 81, 81, 87,
      87, 90, 86, 90, 88, 87, 80, 85, 87, 92, 78, 91, 90, 87, 90, 92, 73, 72, 92, 73, 87, 90,
      86, 85, 84, 81, 90, 92, 90, 90, 81, 87, 88, 90, 92, 87, 85, 90, 86, 91, 90, 86, 90, 90,
      90, 84, 81, 88, 77, 85, 80, 90, 90, 90, 85, 92, 90, 76, 92, 90, 87, 87, 84, 91, 81, 80,
      88, 56, 91, 80, 90, 84, 81, 88, 86, 91, 84, 89, 85, 86, 90, 79, 84, 75, 86, 91, 84, 90,
      89, 82
    ] 1388483 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block92 : OnInterval 1407751 1427567 := by
  apply chainSound 1427567 5228 (by decide)
    [
      93, 93, 89, 76, 90, 92, 91, 86, 93, 93, 87, 91, 89, 90, 82, 89, 91, 90, 90, 86, 93, 90,
      84, 85, 90, 92, 91, 75, 90, 93, 87, 93, 92, 85, 83, 85, 89, 87, 91, 93, 87, 92, 90, 91,
      92, 90, 90, 93, 90, 81, 84, 84, 91, 89, 93, 88, 92, 90, 90, 90, 79, 89, 79, 90, 86, 79,
      92, 90, 91, 89, 76, 90, 92, 90, 90, 93, 88, 90, 89, 93, 93, 87, 88, 89, 93, 85, 92, 91,
      92, 82, 92, 88, 93, 90, 80, 93, 87, 88, 86, 93, 85, 77, 91, 84, 86, 88, 92, 93, 79, 93,
      89, 78
    ] 1407751 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block93 : OnInterval 1427567 1447333 := by
  apply chainSound 1447333 5233 (by decide)
    [
      93, 87, 93, 84, 75, 91, 90, 93, 92, 93, 91, 83, 87, 85, 80, 90, 81, 93, 87, 84, 93, 91,
      87, 93, 89, 85, 83, 90, 93, 90, 91, 86, 79, 84, 92, 93, 90, 85, 90, 92, 90, 70, 93, 89,
      93, 88, 92, 87, 90, 90, 88, 93, 92, 84, 93, 90, 90, 93, 88, 86, 61, 90, 92, 91, 89, 91,
      92, 93, 90, 84, 90, 93, 93, 81, 91, 93, 90, 92, 90, 88, 77, 93, 91, 93, 92, 88, 93, 89,
      90, 91, 93, 75, 92, 87, 46, 92, 93, 72, 88, 90, 86, 91, 90, 87, 93, 92, 90, 91, 92, 84,
      91, 90
    ] 1427567 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block94 : OnInterval 1447333 1466957 := by
  apply chainSound 1466957 5239 (by decide)
    [
      87, 77, 91, 89, 93, 90, 91, 87, 93, 92, 90, 93, 91, 90, 90, 90, 83, 88, 92, 93, 85, 92,
      78, 93, 79, 81, 90, 86, 90, 88, 86, 91, 90, 86, 85, 84, 83, 91, 90, 86, 93, 88, 92, 81,
      87, 88, 87, 84, 89, 84, 93, 69, 91, 83, 82, 93, 92, 90, 85, 92, 93, 93, 85, 92, 82, 77,
      90, 93, 90, 87, 90, 91, 92, 82, 83, 90, 90, 67, 90, 93, 93, 89, 91, 93, 75, 89, 93, 75,
      88, 92, 90, 84, 88, 87, 89, 90, 82, 80, 93, 87, 93, 91, 81, 92, 76, 86, 78, 93, 87, 93,
      90, 87
    ] 1447333 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block95 : OnInterval 1466957 1486637 := by
  apply chainSound 1486637 5244 (by decide)
    [
      93, 93, 91, 90, 86, 63, 87, 57, 91, 90, 84, 81, 89, 88, 93, 92, 93, 90, 91, 89, 79, 90,
      92, 91, 92, 90, 91, 92, 90, 88, 90, 92, 85, 93, 87, 77, 93, 85, 90, 92, 91, 81, 84, 87,
      93, 86, 91, 92, 90, 88, 92, 91, 87, 93, 90, 87, 89, 93, 91, 89, 82, 93, 93, 90, 90, 92,
      91, 89, 93, 85, 77, 91, 90, 81, 90, 89, 91, 90, 84, 81, 93, 78, 80, 93, 84, 87, 81, 93,
      91, 89, 79, 92, 91, 93, 89, 93, 87, 93, 88, 86, 75, 93, 91, 84, 92, 79, 87, 77, 85, 92,
      75, 93
    ] 1466957 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block96 : OnInterval 1486637 1506287 := by
  apply chainSound 1506287 5248 (by decide)
    [
      88, 93, 90, 90, 92, 85, 87, 93, 84, 93, 90, 93, 87, 93, 84, 93, 83, 84, 85, 86, 93, 79,
      92, 91, 93, 84, 87, 90, 86, 90, 90, 90, 93, 81, 81, 85, 89, 84, 76, 93, 81, 90, 89, 90,
      90, 93, 82, 93, 93, 92, 85, 92, 91, 86, 91, 90, 92, 60, 91, 87, 83, 91, 90, 78, 75, 93,
      89, 93, 87, 88, 66, 92, 93, 91, 84, 92, 90, 75, 93, 85, 92, 88, 92, 88, 86, 91, 93, 92,
      88, 84, 92, 90, 85, 89, 90, 87, 90, 90, 87, 75, 76, 90, 89, 91, 77, 88, 86, 91, 92, 91,
      87, 92
    ] 1486637 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block97 : OnInterval 1506287 1526179 := by
  apply chainSound 1526179 5253 (by decide)
    [
      93, 90, 93, 90, 82, 93, 81, 84, 90, 92, 94, 83, 85, 83, 93, 94, 90, 92, 84, 91, 90, 93,
      93, 90, 93, 87, 93, 92, 78, 94, 87, 89, 85, 81, 93, 93, 87, 86, 90, 94, 92, 88, 90, 87,
      80, 84, 94, 92, 90, 93, 90, 82, 93, 77, 90, 91, 89, 94, 81, 90, 78, 86, 85, 89, 90, 93,
      78, 94, 92, 94, 92, 79, 93, 93, 92, 91, 89, 93, 94, 93, 92, 88, 90, 87, 78, 87, 93, 90,
      87, 71, 87, 90, 91, 92, 94, 89, 94, 90, 92, 94, 87, 90, 90, 93, 77, 90, 82, 90, 81, 90,
      90, 90
    ] 1506287 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block98 : OnInterval 1526179 1545751 := by
  apply chainSound 1545751 5258 (by decide)
    [
      92, 87, 75, 93, 94, 93, 71, 94, 92, 94, 89, 93, 78, 87, 94, 89, 91, 93, 80, 82, 83, 85,
      80, 76, 87, 93, 81, 90, 83, 81, 94, 81, 90, 92, 82, 78, 90, 93, 92, 88, 87, 87, 93, 84,
      90, 93, 83, 88, 89, 87, 88, 86, 72, 94, 93, 86, 91, 83, 90, 91, 87, 92, 88, 93, 74, 87,
      88, 86, 94, 93, 93, 89, 93, 93, 91, 74, 91, 93, 92, 90, 78, 88, 84, 84, 92, 94, 90, 83,
      93, 90, 87, 73, 84, 74, 64, 92, 94, 90, 92, 93, 87, 90, 87, 93, 87, 78, 88, 87, 87, 87,
      89, 91
    ] 1526179 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block99 : OnInterval 1545751 1565659 := by
  apply chainSound 1565659 5263 (by decide)
    [
      83, 88, 90, 90, 93, 92, 93, 94, 93, 90, 80, 85, 90, 89, 91, 93, 87, 84, 89, 91, 90, 78,
      93, 92, 91, 89, 90, 93, 72, 93, 93, 90, 87, 85, 87, 90, 93, 92, 88, 93, 92, 93, 94, 80,
      87, 88, 80, 88, 89, 76, 92, 90, 93, 93, 90, 94, 92, 91, 92, 93, 94, 75, 93, 87, 93, 86,
      79, 86, 85, 90, 84, 92, 94, 92, 90, 94, 84, 84, 90, 93, 83, 82, 80, 93, 94, 86, 87, 87,
      87, 93, 82, 86, 90, 90, 94, 71, 90, 93, 87, 94, 84, 90, 89, 88, 93, 92, 94, 90, 89, 94,
      92, 94
    ] 1545751 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block100 : OnInterval 1565659 1585201 := by
  apply chainSound 1585201 5268 (by decide)
    [
      87, 77, 88, 93, 90, 72, 92, 91, 90, 77, 88, 90, 87, 92, 88, 93, 90, 71, 90, 90, 94, 84,
      81, 92, 87, 93, 94, 75, 83, 93, 73, 90, 92, 93, 91, 84, 92, 87, 78, 93, 87, 63, 91, 86,
      58, 89, 88, 93, 92, 94, 90, 89, 94, 87, 89, 94, 93, 92, 76, 92, 90, 67, 83, 93, 94, 93,
      89, 94, 90, 77, 93, 94, 90, 92, 94, 81, 86, 64, 84, 92, 93, 91, 84, 80, 91, 93, 77, 93,
      91, 74, 91, 87, 93, 92, 67, 93, 93, 90, 86, 94, 92, 93, 85, 90, 60, 92, 85, 93, 87, 93,
      92, 94
    ] 1565659 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block101 : OnInterval 1585201 1604833 := by
  apply chainSound 1604833 5272 (by decide)
    [
      93, 86, 94, 77, 94, 84, 90, 93, 84, 90, 75, 90, 86, 90, 94, 89, 87, 70, 90, 87, 87, 78,
      83, 90, 87, 91, 90, 90, 92, 87, 61, 90, 89, 93, 87, 93, 87, 88, 84, 93, 87, 74, 91, 80,
      81, 94, 84, 87, 90, 92, 88, 93, 92, 82, 93, 89, 94, 89, 93, 94, 93, 92, 90, 91, 65, 90,
      64, 84, 74, 91, 92, 85, 77, 88, 93, 71, 91, 90, 90, 93, 92, 88, 74, 93, 87, 88, 92, 91,
      90, 89, 91, 90, 92, 93, 94, 86, 91, 86, 93, 94, 93, 92, 91, 86, 90, 84, 94, 93, 93, 92,
      69, 91
    ] 1585201 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block102 : OnInterval 1604833 1624573 := by
  apply chainSound 1624573 5277 (by decide)
    [
      92, 91, 75, 92, 93, 94, 87, 90, 89, 82, 90, 92, 91, 89, 93, 94, 86, 84, 93, 87, 91, 93,
      86, 84, 76, 81, 83, 91, 71, 94, 75, 90, 80, 94, 92, 94, 90, 93, 90, 92, 94, 90, 89, 91,
      86, 88, 92, 94, 90, 87, 92, 85, 77, 93, 91, 87, 92, 81, 87, 90, 90, 84, 91, 78, 89, 88,
      89, 91, 93, 65, 81, 91, 84, 83, 90, 91, 92, 93, 91, 84, 89, 85, 81, 92, 94, 83, 88, 93,
      89, 91, 81, 89, 79, 93, 89, 94, 90, 86, 91, 93, 84, 87, 93, 93, 78, 84, 90, 90, 86, 91,
      93, 93
    ] 1604833 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block103 : OnInterval 1624573 1644547 := by
  apply chainSound 1644547 5281 (by decide)
    [
      92, 93, 90, 94, 95, 88, 95, 90, 90, 76, 62, 85, 78, 92, 94, 80, 88, 95, 78, 94, 95, 90,
      90, 90, 94, 90, 95, 94, 92, 94, 87, 90, 95, 85, 90, 87, 95, 93, 90, 94, 95, 94, 75, 89,
      93, 93, 94, 95, 91, 95, 94, 83, 93, 90, 91, 74, 94, 95, 93, 90, 94, 93, 93, 89, 93, 93,
      94, 86, 87, 93, 94, 90, 93, 95, 90, 81, 81, 84, 72, 93, 84, 87, 94, 77, 90, 78, 91, 90,
      93, 90, 87, 78, 77, 84, 90, 75, 91, 95, 90, 93, 91, 95, 91, 95, 85, 95, 93, 91, 81, 95,
      76, 87
    ] 1624573 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block104 : OnInterval 1644547 1664633 := by
  apply chainSound 1664633 5286 (by decide)
    [
      86, 91, 93, 83, 93, 87, 94, 89, 87, 84, 94, 86, 90, 93, 90, 90, 78, 82, 95, 82, 90, 90,
      86, 90, 85, 93, 89, 90, 93, 85, 89, 90, 90, 94, 90, 95, 67, 95, 94, 75, 90, 90, 95, 94,
      92, 94, 95, 94, 92, 90, 85, 74, 91, 92, 93, 94, 95, 91, 93, 95, 91, 83, 91, 95, 85, 77,
      84, 94, 95, 90, 91, 95, 94, 92, 85, 92, 82, 93, 86, 94, 92, 91, 92, 90, 75, 91, 92, 93,
      91, 95, 91, 93, 72, 90, 83, 79, 92, 90, 94, 87, 95, 94, 90, 93, 90, 95, 93, 94, 90, 95,
      93, 93
    ] 1644547 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block105 : OnInterval 1664633 1684679 := by
  apply chainSound 1684679 5290 (by decide)
    [
      94, 93, 95, 73, 95, 88, 95, 91, 95, 88, 90, 92, 94, 95, 87, 94, 95, 88, 86, 82, 92, 91,
      92, 90, 90, 94, 95, 93, 85, 81, 77, 93, 90, 91, 81, 89, 94, 87, 90, 69, 90, 84, 86, 93,
      88, 93, 89, 91, 92, 88, 95, 91, 83, 91, 92, 88, 86, 93, 88, 93, 69, 95, 88, 90, 95, 94,
      95, 81, 94, 81, 95, 88, 87, 92, 90, 91, 95, 84, 91, 81, 90, 95, 94, 95, 94, 83, 84, 93,
      90, 93, 93, 87, 93, 90, 91, 93, 90, 95, 91, 92, 90, 93, 87, 93, 85, 84, 90, 80, 75, 90,
      91, 95
    ] 1664633 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block106 : OnInterval 1684679 1704763 := by
  apply chainSound 1704763 5295 (by decide)
    [
      94, 92, 90, 94, 90, 90, 92, 93, 90, 91, 95, 85, 95, 93, 87, 91, 90, 93, 92, 94, 84, 86,
      90, 94, 84, 90, 78, 93, 95, 87, 87, 82, 90, 95, 91, 84, 80, 93, 93, 88, 95, 94, 93, 78,
      87, 93, 90, 90, 92, 87, 87, 94, 92, 90, 90, 94, 90, 95, 94, 95, 94, 95, 91, 95, 90, 85,
      60, 77, 94, 95, 79, 84, 92, 94, 90, 87, 92, 91, 95, 87, 90, 85, 89, 85, 90, 93, 95, 90,
      91, 95, 87, 88, 95, 94, 95, 73, 90, 78, 90, 74, 87, 91, 95, 87, 91, 86, 91, 95, 94, 93,
      95, 88
    ] 1684679 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block107 : OnInterval 1704763 1724587 := by
  apply chainSound 1724587 5299 (by decide)
    [
      95, 94, 95, 81, 93, 91, 74, 91, 95, 94, 87, 92, 93, 94, 83, 91, 92, 88, 86, 91, 90, 87,
      77, 88, 93, 77, 70, 93, 75, 77, 91, 95, 75, 81, 90, 94, 69, 95, 88, 95, 93, 90, 91, 93,
      71, 87, 87, 90, 93, 94, 86, 85, 92, 93, 94, 95, 94, 72, 90, 83, 90, 69, 90, 88, 90, 90,
      93, 87, 95, 94, 80, 79, 84, 90, 83, 85, 92, 91, 75, 95, 91, 86, 87, 88, 87, 95, 91, 92,
      88, 75, 81, 93, 92, 90, 94, 95, 94, 93, 93, 89, 93, 94, 93, 86, 91, 95, 94, 92, 90, 94,
      93, 90
    ] 1704763 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block108 : OnInterval 1724587 1744657 := by
  apply chainSound 1744657 5303 (by decide)
    [
      87, 84, 81, 84, 80, 87, 94, 93, 90, 90, 93, 90, 95, 94, 95, 90, 91, 95, 88, 95, 91, 93,
      95, 87, 70, 93, 77, 76, 92, 91, 90, 87, 89, 91, 93, 95, 91, 90, 95, 91, 90, 72, 87, 95,
      94, 95, 94, 95, 93, 93, 90, 94, 92, 90, 91, 92, 90, 91, 95, 85, 92, 93, 90, 91, 90, 90,
      89, 94, 95, 91, 86, 94, 90, 80, 84, 72, 90, 90, 84, 91, 71, 94, 83, 93, 94, 95, 94, 95,
      84, 88, 89, 91, 93, 89, 93, 90, 93, 91, 89, 94, 92, 94, 84, 87, 89, 91, 80, 90, 85, 89,
      90, 94
    ] 1724587 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block109 : OnInterval 1744657 1765139 := by
  apply chainSound 1765139 5308 (by decide)
    [
      81, 96, 93, 96, 96, 96, 92, 91, 96, 93, 95, 93, 93, 96, 85, 96, 83, 94, 96, 90, 80, 96,
      94, 96, 95, 94, 89, 93, 90, 90, 94, 84, 92, 93, 87, 90, 85, 92, 87, 96, 94, 95, 96, 93,
      96, 84, 91, 95, 96, 90, 90, 88, 89, 96, 85, 95, 87, 87, 82, 96, 93, 96, 96, 92, 85, 90,
      96, 75, 89, 91, 84, 96, 95, 94, 92, 91, 93, 95, 87, 94, 95, 96, 87, 87, 91, 93, 90, 92,
      85, 92, 96, 84, 81, 96, 84, 94, 92, 85, 95, 94, 92, 90, 93, 96, 96, 93, 96, 93, 91, 95,
      85, 95
    ] 1744657 (by decide +kernel)
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem block110 : OnInterval 1765139 1772297 := by
  apply chainSound 1772297 5312 (by decide)
    [
      81, 84, 96, 91, 89, 94, 95, 94, 93, 83, 96, 93, 96, 94, 96, 90, 92, 94, 89, 91, 96, 89,
      93, 93, 79, 96, 92, 91, 95, 84, 91, 96, 96, 95, 93, 96, 93, 91, 89
    ] 1765139 (by decide +kernel)
  decide +kernel

private theorem allIntervals : OnInterval 11 1772297 :=
  (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals block0 (joinIntervals block1 block2)) (joinIntervals block3 (joinIntervals block4 block5))) (joinIntervals (joinIntervals block6 (joinIntervals block7 block8)) (joinIntervals (joinIntervals block9 block10) (joinIntervals block11 block12)))) (joinIntervals (joinIntervals (joinIntervals block13 (joinIntervals block14 block15)) (joinIntervals (joinIntervals block16 block17) (joinIntervals block18 block19))) (joinIntervals (joinIntervals block20 (joinIntervals block21 block22)) (joinIntervals (joinIntervals block23 block24) (joinIntervals block25 block26))))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals block27 (joinIntervals block28 block29)) (joinIntervals (joinIntervals block30 block31) (joinIntervals block32 block33))) (joinIntervals (joinIntervals block34 (joinIntervals block35 block36)) (joinIntervals (joinIntervals block37 block38) (joinIntervals block39 block40)))) (joinIntervals (joinIntervals (joinIntervals block41 (joinIntervals block42 block43)) (joinIntervals (joinIntervals block44 block45) (joinIntervals block46 block47))) (joinIntervals (joinIntervals block48 (joinIntervals block49 block50)) (joinIntervals (joinIntervals block51 block52) (joinIntervals block53 block54)))))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals block55 (joinIntervals block56 block57)) (joinIntervals (joinIntervals block58 block59) (joinIntervals block60 block61))) (joinIntervals (joinIntervals block62 (joinIntervals block63 block64)) (joinIntervals (joinIntervals block65 block66) (joinIntervals block67 block68)))) (joinIntervals (joinIntervals (joinIntervals block69 (joinIntervals block70 block71)) (joinIntervals (joinIntervals block72 block73) (joinIntervals block74 block75))) (joinIntervals (joinIntervals block76 (joinIntervals block77 block78)) (joinIntervals (joinIntervals block79 block80) (joinIntervals block81 block82))))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals block83 (joinIntervals block84 block85)) (joinIntervals (joinIntervals block86 block87) (joinIntervals block88 block89))) (joinIntervals (joinIntervals block90 (joinIntervals block91 block92)) (joinIntervals (joinIntervals block93 block94) (joinIntervals block95 block96)))) (joinIntervals (joinIntervals (joinIntervals block97 (joinIntervals block98 block99)) (joinIntervals (joinIntervals block100 block101) (joinIntervals block102 block103))) (joinIntervals (joinIntervals block104 (joinIntervals block105 block106)) (joinIntervals (joinIntervals block107 block108) (joinIntervals block109 block110)))))))

theorem finitePrimeGaps : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1.H2 := by
  intro p lo hi _
  exact allIntervals p lo (by omega)

end OMA.FiroozbakhtFiniteGaps

theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1.H2 :=
  OMA.FiroozbakhtFiniteGaps.finitePrimeGaps
