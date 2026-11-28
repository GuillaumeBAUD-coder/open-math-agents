import OMAReductions.R_oeis_a228431_R1
import Mathlib

namespace PolygonPrimeWitness

private def witnesses : ℕ → List ℕ
  | 0 => [1, 1, 3, 4, 2, 1, 7, 8, 7, 4, 11, 12, 10, 13, 7, 16, 11, 16, 19, 20, 18, 16, 23, 13, 22]
  | 1 => [25, 27, 25, 26, 28, 22, 29, 15, 16, 35, 25, 31, 37, 34, 40, 38, 37, 43, 44, 22, 40, 47, 45, 46, 49]
  | 2 => [51, 16, 50, 49, 31, 56, 43, 40, 47, 60, 22, 53, 63, 64, 59, 48, 58, 68, 67, 61, 71, 52, 58, 73, 75]
  | 3 => [76, 74, 73, 58, 76, 78, 61, 58, 84, 79, 80, 82, 88, 86, 88, 82, 77, 91, 88, 95, 96, 94, 97, 99, 100]
  | 4 => [95, 93, 82, 101, 102, 97, 107, 85, 91, 100, 111, 112, 110, 112, 106, 113, 103, 88, 118, 112, 115, 109, 115, 112, 107]
  | 5 => [120, 118, 101, 123, 124, 131, 132, 130, 121, 135, 121, 131, 121, 106, 140, 138, 112, 142, 141, 142, 137, 139, 148, 142, 145]
  | 6 => [142, 148, 151, 148, 154, 145, 139, 157, 159, 148, 158, 153, 163, 152, 163, 112, 167, 168, 163, 157, 142, 172, 170, 169, 175]
  | 7 => [172, 171, 172, 179, 172, 178, 181, 171, 184, 170, 180, 187, 176, 186, 181, 187, 181, 187, 172, 190, 193, 191, 193, 187, 200]
  | 8 => [187, 193, 203, 189, 199, 205, 207, 208, 167, 208, 211, 196, 211, 184, 214, 205, 187, 212, 219, 205, 218, 217, 223, 217, 222]
  | 9 => [172, 226, 228, 226, 205, 226, 208, 227, 232, 226, 236, 223, 220, 238, 240, 223, 241, 235, 193, 239, 237, 238, 208, 247, 229]
  | 10 => [251, 249, 235, 236, 247, 253, 254, 256, 238, 260, 247, 256, 247, 264, 223, 265, 262, 220, 263, 268, 271, 269, 271, 268, 275]
  | 11 => [265, 271, 268, 262, 280, 271, 277, 271, 284, 274, 277, 286, 288, 283, 289, 291, 256, 290, 292, 295, 280, 291, 256, 299, 297]
  | 12 => [298, 293, 298, 292, 295, 280, 307, 296, 307, 304, 302, 288, 250, 304, 310, 316, 299, 316, 298, 320, 310, 316, 322, 313, 319]
  | 13 => [325, 327, 325, 307, 321, 298, 328, 327, 316, 311, 333, 307, 325, 303, 301, 322, 324, 343, 344, 343, 340, 346, 348, 286, 337]
  | 14 => [343, 352, 338, 352, 334, 332, 342, 352, 359, 348, 355, 313, 363, 364, 362, 361, 358, 320, 366, 316, 347, 372, 367, 368, 375]
  | 15 => [376, 367, 376, 367, 376, 355, 373, 358, 328, 382, 385, 387, 340, 386, 373, 346, 392, 391, 388, 331, 396, 358, 365, 399, 397]
  | 16 => [395, 396, 391, 401, 403, 397, 394, 408, 394, 404, 403, 409, 403, 412, 406, 401, 414, 376, 419, 420, 406, 409, 411, 388, 418]
  | 17 => [421, 391, 428, 427, 424, 431, 432, 430, 433, 426, 436, 431, 420, 439, 440, 430, 433, 443, 436, 442, 445, 447, 421, 446, 448]
  | 18 => [418, 448, 450, 433, 454, 453, 439, 457, 451, 460, 422, 456, 451, 464, 454, 460, 467, 445, 463, 469, 466, 436, 463, 469, 475]
  | 19 => [473, 474, 445, 478, 477, 442, 473, 478, 484, 478, 481, 478, 485, 487, 472, 487, 457, 382, 476, 495, 436, 491, 492, 427, 464]
  | 20 => [463, 481, 503, 504, 475, 493, 487, 508, 499, 501, 511, 497, 486, 457, 514, 516, 514, 508, 514, 520, 515, 492, 463, 496, 522]
  | 21 => [517, 502, 520, 526, 529, 522, 517, 518, 532, 487, 517, 534, 520, 539, 537, 511, 541, 511, 541, 527, 541, 526, 548, 547, 544]
  | 22 => [551, 552, 550, 548, 555, 541, 554, 553, 559, 560, 546, 556, 562, 561, 562, 557, 562, 556, 542, 568, 571, 568, 571, 553, 575]
  | 23 => [556, 562, 536, 579, 580, 563, 564, 523, 557, 582, 565, 578, 580, 583, 572, 583, 589, 575, 592, 586, 596, 523, 568, 598, 597]
  | 24 => [562, 601, 603, 604, 583, 600, 562, 608, 606, 556, 602, 592, 586, 613, 615, 601, 614, 616, 559, 613, 618, 541, 623, 604, 583]
  | 25 => [620, 627, 628, 626, 628, 622, 632, 631, 628, 590, 636, 631, 637, 639, 628, 638, 616, 631, 637, 643, 640, 634, 648, 634, 641]
  | 26 => [651, 616, 647, 628, 643, 656, 654, 652, 647, 660, 646, 661, 658, 661, 659, 661, 667, 641, 667, 625, 671, 672, 670, 661, 667]
  | 27 => [640, 667, 676, 679, 665, 670, 673, 671, 684, 667, 685, 687, 628, 659, 684, 691, 692, 690, 676, 695, 685, 679, 697, 687, 673]
  | 28 => [695, 696, 667, 704, 702, 685, 707, 705, 703, 709, 703, 673, 643, 709, 715, 716, 702, 712, 718, 709, 682, 713, 703, 652, 722]
  | 29 => [705, 682, 712, 727, 724, 730, 709, 718, 724, 726, 736, 731, 736, 691, 740, 738, 733, 730, 712, 739, 745, 742, 697, 743, 744]
  | 30 => [751, 737, 751, 736, 743, 753, 718, 733, 754, 760, 758, 748, 742, 764, 763, 757, 767, 757, 751, 769, 771, 733, 751, 768, 763]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 2577426147548683169379880845613862450845254401055092509543183257270179188707233718999293223417932941038924189941484105421516996015467418326179536384362799440729804187886824533414953001905801090622787969540076319408964006230

private theorem product_eq : primorial 547 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 547 then n.Prime else n ≤ 300000 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 547
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 300000 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 547 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 548 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 2
  let x := witness i j
  let y := n - x
  0 < x ∧ 0 < y ∧ n = x + y ∧ Certified (x * (x + 1) / 2 + y * (2*y-1))

private instance (i : ℕ) (j : Fin 25) : Decidable (Valid i j) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked0 : ∀ j : Fin 25, Valid 0 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked1 : ∀ j : Fin 25, Valid 1 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked2 : ∀ j : Fin 25, Valid 2 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked3 : ∀ j : Fin 25, Valid 3 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked4 : ∀ j : Fin 25, Valid 4 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked5 : ∀ j : Fin 25, Valid 5 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked6 : ∀ j : Fin 25, Valid 6 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked7 : ∀ j : Fin 25, Valid 7 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked8 : ∀ j : Fin 25, Valid 8 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked9 : ∀ j : Fin 25, Valid 9 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked10 : ∀ j : Fin 25, Valid 10 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked11 : ∀ j : Fin 25, Valid 11 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked12 : ∀ j : Fin 25, Valid 12 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked13 : ∀ j : Fin 25, Valid 13 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked14 : ∀ j : Fin 25, Valid 14 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked15 : ∀ j : Fin 25, Valid 15 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked16 : ∀ j : Fin 25, Valid 16 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked17 : ∀ j : Fin 25, Valid 17 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked18 : ∀ j : Fin 25, Valid 18 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked19 : ∀ j : Fin 25, Valid 19 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked20 : ∀ j : Fin 25, Valid 20 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked21 : ∀ j : Fin 25, Valid 21 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked22 : ∀ j : Fin 25, Valid 22 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked23 : ∀ j : Fin 25, Valid 23 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked24 : ∀ j : Fin 25, Valid 24 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked25 : ∀ j : Fin 25, Valid 25 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked26 : ∀ j : Fin 25, Valid 26 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked27 : ∀ j : Fin 25, Valid 27 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked28 : ∀ j : Fin 25, Valid 28 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked29 : ∀ j : Fin 25, Valid 29 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked30 : ∀ j : Fin 25, Valid 30 j := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 31) (j : Fin 25) : Valid i j := by
  interval_cases i
  · exact checked0 j
  · exact checked1 j
  · exact checked2 j
  · exact checked3 j
  · exact checked4 j
  · exact checked5 j
  · exact checked6 j
  · exact checked7 j
  · exact checked8 j
  · exact checked9 j
  · exact checked10 j
  · exact checked11 j
  · exact checked12 j
  · exact checked13 j
  · exact checked14 j
  · exact checked15 j
  · exact checked16 j
  · exact checked17 j
  · exact checked18 j
  · exact checked19 j
  · exact checked20 j
  · exact checked21 j
  · exact checked22 j
  · exact checked23 j
  · exact checked24 j
  · exact checked25 j
  · exact checked26 j
  · exact checked27 j
  · exact checked28 j
  · exact checked29 j
  · exact checked30 j

end PolygonPrimeWitness

open PolygonPrimeWitness

theorem OMA.solution : OMA.R_oeis_a228431_R1.H1 := by
  intro n hlo hhi
  let i := (n - 2) / 25
  let j : Fin 25 := ⟨(n - 2) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 31 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 2 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hy, hsum, hp⟩ := h
  exact ⟨witness i j, n - witness i j, hx, hy, hsum, primeOfCertified hp⟩