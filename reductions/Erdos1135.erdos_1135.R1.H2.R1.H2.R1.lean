import OMAReductions.R_Erdos1135_erdos_1135_R1_H2_R1

/-! A quantitative short-step certificate for recovery after a late
coefficient crossing. In each of the 237 ordinary residue classes, a
step within eight accelerated iterations has slope at most 243/256.
This controls descent below the initial seed even after a small overshoot. -/

namespace OMA.R_Erdos1135_erdos_1135_R1_H2_R1_H2_R1

open Function Finset

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
private theorem contraction_table (T : ℕ → ℕ)
    (hT : T = fun n ↦ if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 256, (r.val + 2) % 256 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) →
      ∃ j : Fin 9, T^[j.val] (r.val + 2) ≤ 209 ∧
        T^[j.val] (256 + (r.val + 2)) ≤ 243 + T^[j.val] (r.val + 2) := by
  subst T
  decide +kernel

private theorem nearby_descent (T : ℕ → ℕ)
    (hT : T = fun v ↦ if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)
    {n m : ℕ} (hn : 40000 < n) (hnm : n ≤ m) (hgap : 21 * (m - n) < n)
    (hres : m % 256 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ)) :
    ∃ j : ℕ, T^[j] m < n := by
  let r : Fin 256 := ⟨(m - 2) % 256, Nat.mod_lt _ (by decide)⟩
  let b := r.val + 2
  let q := (m - 2) / 256
  have hm : m = 256 * q + b := by dsimp [q, b, r]; omega
  have hb : b % 256 = m % 256 := by omega
  obtain ⟨j, hbase, hslope⟩ := contraction_table T hT r (by simpa only [← hb] using hres)
  change T^[j.val] b ≤ 209 at hbase
  change T^[j.val] (256 + b) ≤ 243 + T^[j.val] b at hslope
  let w := 2 ^ (8 - j.val)
  have hw : 2 ^ j.val * w = 256 := by
    dsimp [w]
    rw [← pow_add, show j.val + (8 - j.val) = 8 by omega]
    decide
  obtain ⟨a, ha⟩ := OMA.R_Erdos1135_erdos_1135_R1.residue_affine T
    (fun v ↦ congrFun hT v) j.val b
  have hs := ha w
  rw [hw] at hs
  have hcoeff : a * w ≤ 243 := by omega
  refine ⟨j.val, ?_⟩
  calc
    T^[j.val] m = T^[j.val] (2 ^ j.val * (w * q) + b) := by
      rw [← Nat.mul_assoc, hw, ← hm]
    _ = a * w * q + T^[j.val] b := by rw [ha, Nat.mul_assoc]
    _ ≤ 243 * q + 209 := Nat.add_le_add (Nat.mul_le_mul_right q hcoeff) hbase
    _ < n := by omega

/-- Late crossings with an odd-step count exceeding one seventh of the seed. -/
def H1 : Prop :=
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  ∀ n k : ℕ, 860179 < n → n % 9 = 5 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) →
    let s := fun j : ℕ => ((range j).filter fun i => T^[i] n % 2 = 1).card
    4096 < k → 3 ^ s k < 2 ^ k → (∀ i < k, 2 ^ i ≤ 3 ^ s i) →
    n ≤ T^[k] n → 3 * (2 ^ k - 3 ^ s k) * n ≤ s k * 3 ^ s k →
    3 * (T^[k] n - n) < s k →
    n < 7 * s k → ∃ j : ℕ, T^[j] (T^[k] n) < n

/-- Late crossings with a small odd-step count whose endpoints remain in a
residue not treated by the eight-step certificate. -/
def H2 : Prop :=
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  ∀ n k : ℕ, 860179 < n → n % 9 = 5 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) →
    let s := fun j : ℕ => ((range j).filter fun i => T^[i] n % 2 = 1).card
    4096 < k → 3 ^ s k < 2 ^ k → (∀ i < k, 2 ^ i ≤ 3 ^ s i) →
    n ≤ T^[k] n → 3 * (2 ^ k - 3 ^ s k) * n ≤ s k * 3 ^ s k →
    3 * (T^[k] n - n) < s k →
    7 * s k ≤ n →
    (T^[k] n) % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) →
    ∃ j : ℕ, T^[j] (T^[k] n) < n

theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R1_H2_R1.H2 := by
  intro hTall hHard
  unfold OMA.R_Erdos1135_erdos_1135_R1_H2_R1.H2
  dsimp only
  intro n k hn h9 h256 hk hcoeff hbefore hnm hnear hover
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let s := fun j : ℕ => ((range j).filter fun i => T^[i] n % 2 = 1).card
  change n ≤ T^[k] n at hnm
  change 3 * (T^[k] n - n) < s k at hover
  change ∃ j : ℕ, T^[j] (T^[k] n) < n
  by_cases hsize : 7 * s k ≤ n
  · by_cases hres : (T^[k] n) % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ)
    · exact hHard n k hn h9 h256 hk hcoeff hbefore hnm hnear hover hsize hres
    · exact nearby_descent T rfl (by omega) hnm (by omega) hres
  · exact hTall n k hn h9 h256 hk hcoeff hbefore hnm hnear hover (lt_of_not_ge hsize)

end OMA.R_Erdos1135_erdos_1135_R1_H2_R1_H2_R1
