import OMAReductions.R_OeisA237720_conjecture_3_R1
import Mathlib

namespace PrimeWitnesses

private def witnesses : ℕ → List ℕ
  | 0 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2]
  | 1 => [2, 2, 2, 2, 2, 2, 17, 17, 13, 13, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2]
  | 2 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 59, 59, 59, 59, 59, 59, 53, 53, 53, 53, 53, 53, 47, 47, 47, 47]
  | 3 => [43, 43, 41, 41, 41, 41, 37, 37, 37, 37, 37, 37, 31, 31, 29, 29, 29, 29, 29, 29, 23, 23, 23, 23, 19]
  | 4 => [19, 17, 17, 17, 17, 13, 13, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 5 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29, 29, 29, 29, 23, 23, 23, 23, 19, 19, 17]
  | 6 => [17, 17, 17, 13, 13, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 7 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 97, 97, 97, 97, 97, 97, 89, 89, 89]
  | 8 => [89, 89, 89, 83, 83, 83, 83, 79, 79, 79, 79, 79, 79, 73, 73, 71, 71, 71, 71, 67, 67, 67, 67, 67, 67]
  | 9 => [61, 61, 59, 59, 59, 59, 59, 59, 53, 53, 53, 53, 53, 53, 47, 47, 47, 47, 43, 43, 41, 41, 41, 41, 37]
  | 10 => [37, 37, 37, 37, 37, 31, 31, 29, 29, 29, 29, 29, 29, 23, 23, 23, 23, 19, 19, 17, 17, 17, 17, 13, 13]
  | 11 => [11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 12 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 41, 41, 37, 37, 37, 37]
  | 13 => [37, 37, 31, 31, 29, 29, 29, 29, 29, 29, 23, 23, 23, 23, 19, 19, 17, 17, 17, 17, 13, 13, 11, 11, 11]
  | 14 => [11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 15 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 131, 131, 131, 131, 127]
  | 16 => [127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 113, 113, 113, 113, 109, 109, 107, 107, 107, 107, 103, 103]
  | 17 => [101, 101, 101, 101, 97, 97, 97, 97, 97, 97, 97, 97, 89, 89, 89, 89, 89, 89, 83, 83, 83, 83, 79, 79, 79]
  | 18 => [79, 79, 79, 73, 73, 71, 71, 71, 71, 67, 67, 67, 67, 67, 67, 61, 61, 59, 59, 59, 59, 59, 59, 53, 53]
  | 19 => [53, 53, 53, 53, 47, 47, 47, 47, 43, 43, 41, 41, 41, 41, 37, 37, 37, 37, 37, 37, 31, 31, 29, 29, 29]
  | 20 => [29, 29, 29, 23, 23, 23, 23, 19, 19, 17, 17, 17, 17, 13, 13, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2]
  | 21 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 22 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 269, 269, 269, 269]
  | 23 => [263, 263, 263, 263, 263, 263, 257, 257, 257, 257, 257, 257, 251, 251, 251, 251, 251, 251, 251, 251, 251, 251, 241, 241, 239]
  | 24 => [239, 239, 239, 239, 239, 233, 233, 233, 233, 229, 229, 227, 227, 227, 227, 223, 223, 223, 223, 223, 223, 223, 223, 223, 223]
  | 25 => [223, 223, 211, 211, 211, 211, 211, 211, 211, 211, 211, 211, 211, 211, 199, 199, 197, 197, 197, 197, 193, 193, 191, 191, 191]
  | 26 => [191, 191, 191, 191, 191, 191, 191, 181, 181, 179, 179, 179, 179, 179, 179, 173, 173, 173, 173, 173, 173, 167, 167, 167, 167]
  | 27 => [163, 163, 163, 163, 163, 163, 157, 157, 157, 157, 157, 157, 151, 151, 149, 149, 149, 149, 149, 149, 149, 149, 149, 149, 139]
  | 28 => [139, 137, 137, 137, 137, 137, 137, 131, 131, 131, 131, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127]
  | 29 => [113, 113, 113, 113, 109, 109, 107, 107, 107, 107, 103, 103, 101, 101, 101, 101, 97, 97, 97, 97, 97, 97, 97, 97, 89]
  | 30 => [89, 89, 89, 89, 89, 83, 83, 83, 83, 79, 79, 79, 79, 79, 79, 73, 73, 71, 71, 71, 71, 67, 67, 67, 67]
  | 31 => [67, 67, 61, 61, 59, 59, 59, 59, 59, 59, 53, 53, 53, 53, 53, 53, 47, 47, 47, 47, 43, 43, 41, 41, 41]
  | 32 => [41, 37, 37, 37, 37, 37, 37, 31, 31, 29, 29, 29, 29, 29, 29, 23, 23, 23, 23, 19, 19, 17, 17, 17, 17]
  | 33 => [13, 13, 11, 11, 11, 11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 34 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 35 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 67, 67, 61, 61, 59]
  | 36 => [59, 59, 59, 59, 59, 53, 53, 53, 53, 53, 53, 47, 47, 47, 47, 43, 43, 41, 41, 41, 41, 37, 37, 37, 37]
  | 37 => [37, 37, 31, 31, 29, 29, 29, 29, 29, 29, 23, 23, 23, 23, 19, 19, 17, 17, 17, 17, 13, 13, 11, 11, 11]
  | 38 => [11, 7, 7, 5, 5, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | 39 => [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 3
  let p := witness i j
  p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime

private instance (i : ℕ) (j : Fin 25) : Decidable (Valid i j) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked0 : ∀ j : Fin 25, Valid 0 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked1 : ∀ j : Fin 25, Valid 1 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked2 : ∀ j : Fin 25, Valid 2 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked3 : ∀ j : Fin 25, Valid 3 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked4 : ∀ j : Fin 25, Valid 4 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked5 : ∀ j : Fin 25, Valid 5 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked6 : ∀ j : Fin 25, Valid 6 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked7 : ∀ j : Fin 25, Valid 7 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked8 : ∀ j : Fin 25, Valid 8 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked9 : ∀ j : Fin 25, Valid 9 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked10 : ∀ j : Fin 25, Valid 10 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked11 : ∀ j : Fin 25, Valid 11 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked12 : ∀ j : Fin 25, Valid 12 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked13 : ∀ j : Fin 25, Valid 13 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked14 : ∀ j : Fin 25, Valid 14 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked15 : ∀ j : Fin 25, Valid 15 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked16 : ∀ j : Fin 25, Valid 16 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked17 : ∀ j : Fin 25, Valid 17 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked18 : ∀ j : Fin 25, Valid 18 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked19 : ∀ j : Fin 25, Valid 19 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked20 : ∀ j : Fin 25, Valid 20 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked21 : ∀ j : Fin 25, Valid 21 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked22 : ∀ j : Fin 25, Valid 22 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked23 : ∀ j : Fin 25, Valid 23 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked24 : ∀ j : Fin 25, Valid 24 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked25 : ∀ j : Fin 25, Valid 25 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked26 : ∀ j : Fin 25, Valid 26 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked27 : ∀ j : Fin 25, Valid 27 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked28 : ∀ j : Fin 25, Valid 28 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked29 : ∀ j : Fin 25, Valid 29 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked30 : ∀ j : Fin 25, Valid 30 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked31 : ∀ j : Fin 25, Valid 31 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked32 : ∀ j : Fin 25, Valid 32 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked33 : ∀ j : Fin 25, Valid 33 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked34 : ∀ j : Fin 25, Valid 34 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked35 : ∀ j : Fin 25, Valid 35 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked36 : ∀ j : Fin 25, Valid 36 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked37 : ∀ j : Fin 25, Valid 37 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked38 : ∀ j : Fin 25, Valid 38 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked39 : ∀ j : Fin 25, Valid 39 j := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 40) (j : Fin 25) : Valid i j := by
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
  · exact checked31 j
  · exact checked32 j
  · exact checked33 j
  · exact checked34 j
  · exact checked35 j
  · exact checked36 j
  · exact checked37 j
  · exact checked38 j
  · exact checked39 j

theorem result : OMA.R_OeisA237720_conjecture_3_R1.H1 := by
  intro n hlo hhi
  let i := (n - 3) / 25
  let j : Fin 25 := ⟨(n - 3) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 3 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  exact ⟨witness i j, h⟩

end PrimeWitnesses

theorem OMA.solution : OMA.R_OeisA237720_conjecture_3_R1.H1 :=
  PrimeWitnesses.result