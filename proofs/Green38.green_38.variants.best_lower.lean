import FormalConjectures.GreensOpenProblems.«38»
import Mathlib

/-! The 367 words are from the Appendix of Polak and Schrijver, New lower bound on the Shannon capacity of C₇ from circular graphs, Information Processing Letters 143 (2019). -/

namespace C7Seed
open scoped Pointwise

-- Polak and Schrijver, IPL 143 (2019), Appendix. Decimal digits give coordinates,
-- read from right to left, so a missing leading zero is retained by the decoder.
private def codes : List ℕ := [
    2020, 2112, 2204, 2306, 2461, 2553, 3645, 3040, 3032, 3124, 3226, 3311,
    3403, 14144, 14231, 14323, 14415, 14510, 15602, 15064, 15166, 15251, 15343, 15430,
    15522, 16614, 16016, 16101, 16263, 16355, 16450, 16542, 10636, 10021, 10113, 10205,
    10300, 10462, 10554, 11656, 11041, 11033, 11125, 11220, 11312, 11404, 11506, 12661,
    12053, 12145, 12240, 12232, 12324, 12426, 12511, 13603, 13065, 13160, 13252, 13344,
    13446, 13431, 24010, 24102, 24264, 24366, 24451, 24543, 25630, 25022, 25114, 25216,
    25301, 25463, 25555, 26650, 26042, 26034, 26136, 26221, 26313, 26405, 26500, 20662,
    20054, 20156, 20241, 20233, 20325, 20420, 20512, 21604, 21006, 21161, 21253, 21345,
    21440, 21432, 22626, 22011, 22103, 22265, 22360, 22452, 22544, 23631, 23023, 23115,
    23210, 23302, 23464, 23566, 34130, 34222, 34314, 34416, 34501, 35663, 35055, 35150,
    35242, 35234, 35336, 35421, 35513, 36605, 36000, 36162, 36254, 36356, 36441, 36433,
    30620, 30012, 30104, 30206, 30361, 30453, 30545, 31632, 31024, 31126, 31211, 31303,
    31465, 31560, 32652, 32044, 32131, 32223, 32315, 32410, 32502, 33664, 33066, 33151,
    33243, 33235, 33330, 33422, 44616, 44001, 44163, 44255, 44350, 44442, 44434, 44536,
    45621, 45013, 45105, 45200, 45362, 45454, 45556, 46633, 46025, 46120, 46212, 46304,
    46406, 46561, 40653, 40045, 40132, 40224, 40326, 40411, 40503, 41665, 41060, 41152,
    41244, 41331, 41423, 41515, 42610, 42002, 42164, 42266, 42351, 42443, 42435, 43622,
    43014, 43116, 43201, 43363, 43455, 43550, 54634, 54036, 54121, 54213, 54305, 54400,
    54562, 55654, 55056, 55141, 55133, 55225, 55320, 55412, 55504, 56606, 56061, 56153,
    56245, 56332, 56424, 56526, 50611, 50003, 50165, 50260, 50352, 50444, 51623, 51015,
    51110, 51202, 51364, 51551, 52643, 52635, 52030, 52122, 52214, 53655, 53134, 64332,
    64424, 64526, 65611, 65003, 65260, 65352, 65444, 65546, 66623, 66110, 66202, 66364,
    66466, 66551, 60643, 60645, 60030, 60122, 60214, 60316, 60401, 60563, 61050, 61142,
    61134, 61236, 61321, 61413, 62600, 62062, 62154, 62256, 62341, 62333, 62520, 63612,
    63004, 63106, 63261, 63353, 63445, 63540, 64532, 4026, 4111, 4203, 4460, 4552,
    5644, 5031, 5123, 5310, 5402, 5564, 6666, 6051, 6143, 6230, 6322, 6414,
    6516, 601, 63, 155, 250, 342, 334, 436, 1613, 1100, 1262, 1354,
    1456, 1541, 2625, 521, 1005, 2533, 3565, 4052, 4365, 4624, 4660, 5046,
    5225, 10534, 14246, 15435, 22524, 24615, 24651, 32046, 34035, 34043, 36525, 40040,
    41246, 42530, 43514, 45641, 50531, 51456, 52400, 52563, 53050, 53142, 53320, 53412,
    56340, 61505, 62425, 64154, 64340, 65105, 66025]

private def decode (n : ℕ) (i : Fin 5) : ZMod 7 := ((n / 10^i.val) % 10 : ℕ)

private def separated (x y : Fin 5 → ZMod 7) : Prop :=
  ∃ i : Fin 5, x i - y i ∉ ({-1,0,1} : Finset (ZMod 7))

private instance (x y : Fin 5 → ZMod 7) : Decidable (separated x y) := by
  unfold separated
  infer_instance

private instance : Std.Symm separated where
  symm x y h := by
    obtain ⟨i,hi⟩ := h
    refine ⟨i, fun hbad => hi ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbad ⊢
    rcases hbad with ha|ha|ha
    · exact Or.inr (Or.inr (by linear_combination -ha))
    · exact Or.inr (Or.inl (by linear_combination -ha))
    · exact Or.inl (by linear_combination -ha)

private def words := codes.map decode

-- Check decimal digits directly; the correctness bridge below has only 100
-- cases, independently of the length of the code.
private def digitFar (a b : ℕ) : Bool :=
  let d := (a + 7 - b) % 7
  2 ≤ d && d ≤ 5

private def farAt (x y power : ℕ) : Bool :=
  digitFar (x / power % 10) (y / power % 10)

private def far (x y : ℕ) : Bool :=
  farAt x y 1 || farAt x y 10 || farAt x y 100 ||
    farAt x y 1000 || farAt x y 10000

private theorem digit_sound : ∀ a b : Fin 10, digitFar a b = true →
    ((a.val : ZMod 7) - (b.val : ZMod 7)) ∉ ({-1,0,1} : Finset (ZMod 7)) := by
  decide +kernel

private lemma far_sound (x y : ℕ) (h : far x y = true) : separated (decode x) (decode y) := by
  have hi (i : Fin 5) (h : farAt x y (10^i.val) = true) :
      separated (decode x) (decode y) :=
    ⟨i, digit_sound ⟨_, Nat.mod_lt _ (by decide : 0 < 10)⟩
      ⟨_, Nat.mod_lt _ (by decide : 0 < 10)⟩ h⟩
  simp only [far, Bool.or_eq_true] at h
  rcases h with (((h|h)|h)|h)|h
  · exact hi 0 h
  · exact hi 1 h
  · exact hi 2 h
  · exact hi 3 h
  · exact hi 4 h

private def valid : List ℕ → Bool
  | [] => true
  | x :: xs => xs.all (far x) && valid xs

private lemma valid_sound (xs : List ℕ) (h : valid xs = true) :
    (xs.map decode).Pairwise separated := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : xs.all (far x) = true ∧ valid xs = true := by simpa [valid] using h
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hx.2⟩
    intro v hv
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hv
    exact far_sound x y (List.all_eq_true.mp hx.1 y hy)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem checked : words.Pairwise separated :=
  valid_sound codes (by decide +kernel)

private lemma certificate_of_list (xs : List (Fin 5 → ZMod 7))
    (hpair : xs.Pairwise separated) (hlen : xs.length = 367) :
    ∃ A : Finset (Fin 5 → ZMod 7), A.card = 367 ∧ Green38.IntersectsOnlyAtZero A := by
  have hn : xs.Nodup := hpair.imp (fun {x y} h he => by
    obtain ⟨i,hi⟩ := h
    exact hi (by simp [he]))
  refine ⟨xs.toFinset, (List.toFinset_card_of_nodup hn).trans hlen, ?_⟩
  intro d hd hclose
  obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_sub.mp hd
  by_cases h : x = y
  · simp [h]
  obtain ⟨i,hi⟩ := hpair.forall (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) h
  exact False.elim (hi (hclose i))

set_option maxRecDepth 8000 in
lemma certificate : ∃ A : Finset (Fin 5 → ZMod 7),
    A.card = 367 ∧ Green38.IntersectsOnlyAtZero A :=
  certificate_of_list words checked (by rw [words, List.length_map]; rfl)

end C7Seed

namespace C7Amplify

open Green38 Filter
open scoped Pointwise Topology

lemma separate {n : ℕ} {A : Finset (Fin n → ZMod 7)} (h : IntersectsOnlyAtZero A)
    {x y} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : ∀ i, x i - y i ∈ ({-1, 0, 1} : Finset (ZMod 7))) : x = y :=
  sub_eq_zero.mp (h (x-y) (Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩) hxy)

lemma valid_product {a b m n : ℕ} (ha : a ∈ ValidCardinalities m)
    (hb : b ∈ ValidCardinalities n) : a * b ∈ ValidCardinalities (m+n) := by
  classical
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  let pair : ((Fin m → ZMod 7) × (Fin n → ZMod 7)) ↪ (Fin (m+n) → ZMod 7) :=
    ⟨fun p => Fin.append p.1 p.2, by
      rintro ⟨x,y⟩ ⟨x',y'⟩ eq
      apply Prod.ext
      · funext i
        simpa using congrFun eq (Fin.castAdd n i)
      · funext i
        simpa using congrFun eq (Fin.natAdd m i)⟩
  refine ⟨(A ×ˢ B).map pair, ?_, by simp⟩
  rintro z hz close
  obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨⟨x',y'⟩, hxy', rfl⟩ := Finset.mem_map.mp hw
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  obtain ⟨hx',hy'⟩ := Finset.mem_product.mp hxy'
  change ∀ i, Fin.append x y i - Fin.append x' y' i ∈ ({-1, 0, 1} : Finset (ZMod 7)) at close
  have e₁ : x = x' := separate hA hx hx' fun i => by
    simpa only [Fin.append_left] using close (Fin.castAdd n i)
  have e₂ : y = y' := separate hB hy hy' fun i => by
    simpa only [Fin.append_right] using close (Fin.natAdd m i)
  subst x' y'
  exact sub_self _

lemma one_valid (n : ℕ) : 1 ∈ ValidCardinalities n := by
  refine ⟨{0}, ?_, by simp⟩
  rintro z hz _
  simpa using hz

lemma powers_valid {a d : ℕ} (ha : a ∈ ValidCardinalities d) (k : ℕ) :
    a^k ∈ ValidCardinalities (d*k) := by
  induction k with
  | zero => simpa using one_valid 0
  | succ k ih => simpa [Nat.mul_succ, pow_succ] using valid_product ih ha

lemma padded_cardinality {a d : ℕ} (ha : a ∈ ValidCardinalities d) (n : ℕ) :
    (a : ℝ)^(n/d) ≤ LargestAdmissibleCardinality n := by
  have h := valid_product (powers_valid ha (n/d)) (one_valid (n%d))
  rw [mul_one, Nat.div_add_mod] at h
  change _ ≤ ((sSup (ValidCardinalities n) : ℕ) : ℝ)
  exact_mod_cast le_csSup green_38.test_bound_above h

lemma capacity_growth {a d : ℕ} (ha : a ∈ ValidCardinalities d) (hd : 0 < d)
    (C : ℝ) (hC : 1 ≤ C) (hCa : C^d = a) (ε : ℝ) (he : ε ∈ Set.Ioo 0 C) :
    ∀ᶠ n : ℕ in atTop, (C-ε)^n ≤ LargestAdmissibleCardinality n := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hapos : 0 < (a : ℝ) := hCa ▸ pow_pos hCp d
  have hr : (C-ε)/C < 1 := (div_lt_one hCp).mpr (sub_lt_self _ he.1)
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (sub_nonneg.mpr he.2.le) hCp.le) hr
  filter_upwards [lim.eventually_lt_const (inv_pos.mpr hapos)] with n hn
  have hdim : n ≤ d * (n / d) + d := by
    have := Nat.mod_lt n hd
    have := Nat.div_add_mod n d
    omega
  have hp : C^n ≤ (a : ℝ)^(n/d) * a := by
    calc
      C^n ≤ C^(d*(n/d)+d) := pow_le_pow_right₀ hC hdim
      _ = _ := by rw [pow_add, pow_mul, hCa]
  have small := mul_le_mul_of_nonneg_right hn.le (pow_pos hCp n).le
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hCp.ne')] at small
  apply (small.trans ?_).trans (padded_cardinality ha n)
  calc
    (a : ℝ)⁻¹ * C^n ≤ (a : ℝ)⁻¹ * ((a : ℝ)^(n/d) * a) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hapos.le)
    _ = _ := by field_simp

lemma five_dimensional (h : ∃ A : Finset (Fin 5 → ZMod 7),
    A.card = 367 ∧ IntersectsOnlyAtZero A) : type_of% @Green38.green_38.variants.best_lower := by
  obtain ⟨A, hsize, hA⟩ := h
  intro ε hε
  apply capacity_growth (a := 367) (d := 5) ⟨A, hA, hsize⟩ (by decide) C₁ _ _ ε hε
  · exact Real.one_le_rpow (by norm_num) (by norm_num)
  · exact Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 367) (by decide : 5 ≠ 0)

end C7Amplify

theorem OMA.solution : type_of% @Green38.green_38.variants.best_lower := by
  exact C7Amplify.five_dimensional C7Seed.certificate
