import FormalConjectures.GreensOpenProblems.«14»

-- Problem: Ben Green's Open Problem 14 — W 3 38 lower
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/14.lean:360 (declaration Green14.W_3_38_lower)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Certificate: a good partition of {1..1378} for w(2;3,38) (Ahmed, Kullmann, Snevily 2014).
-- Bit x of CERT is 1 iff x is in the part avoiding 38-term progressions.
-- Nonemptiness via Hales-Jewett.

namespace OMA.O6

def CERT : ℕ := 13193621487557232788213796680705498233903954266815354327699405484755063606447301647880684740287754456572203004878577901005575738064732754741858317356968327951902098841640721698422742758765614675368806307974285182229510014016201174259816622383369533180616085026382682530704630499839043845916366601763952035616704256033187217421338622061518457150259453745064102282844593854586551547283555958651015753569216230116556798

def col (x : ℕ) : Bool := Nat.testBit CERT x

def good3 (a d : ℕ) : Bool :=
  col a || col (a + d) || col (a + 2 * d)

def chk3 : Bool :=
  (List.range 688).all fun d => (List.range (1378 - 2 * (d + 1))).all fun a => good3 (a + 1) (d + 1)

def good38 (a d : ℕ) : Bool :=
  (List.range 38).any fun i => !col (a + i * d)

def chk38 : Bool :=
  (List.range 37).all fun d => (List.range (1378 - 37 * (d + 1))).all fun a => good38 (a + 1) (d + 1)

set_option maxRecDepth 100000 in
theorem chk3_ok : chk3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chk38_ok : chk38 = true := by decide +kernel

theorem chk3_spec (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (had : a + 2 * d ≤ 1378) :
    col a = true ∨ col (a + d) = true ∨ col (a + 2 * d) = true := by
  have h := chk3_ok
  simp only [chk3, List.all_eq_true, List.mem_range] at h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have := h d' (by omega) a' (by omega)
  simp only [good3, Bool.or_eq_true] at this
  rcases this with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem chk38_spec (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (had : a + 37 * d ≤ 1378) :
    ∃ i < 38, col (a + i * d) = false := by
  have h := chk38_ok
  simp only [chk38, List.all_eq_true, List.mem_range] at h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have := h d' (by omega) a' (by omega)
  simp only [good38, List.any_eq_true, List.mem_range, Bool.not_eq_true'] at this
  obtain ⟨i, hi, h1⟩ := this
  exact ⟨i, hi, h1⟩

theorem ap_pts {N L : ℕ} (hL : 2 ≤ L) (s : Finset (Set.Icc 1 N)) (l : ℕ∞)
    (hs : ({(s' : ℕ) | s' ∈ s} : Set ℕ).IsAPOfLength l) (hl : (L : ℕ∞) = l) :
    ∃ a d : ℕ, 1 ≤ d ∧ ∀ n < L, ∃ y ∈ s, (y : ℕ) = a + n * d := by
  obtain ⟨a, d, hcard, heq⟩ := hs
  have mem : ∀ n < L, a + n * d ∈ ({(s' : ℕ) | s' ∈ s} : Set ℕ) := by
    intro n hn
    rw [heq]
    exact ⟨n, by rw [← hl]; exact_mod_cast hn, by rw [smul_eq_mul]⟩
  refine ⟨a, d, ?_, fun n hn => ?_⟩
  · by_contra hd
    have hd0 : d = 0 := by omega
    subst hd0
    have hsub : ({(s' : ℕ) | s' ∈ s} : Set ℕ) ⊆ {a} := by
      intro x hx
      rw [heq] at hx
      obtain ⟨n, _, rfl⟩ := hx
      simp
    have h1 := Set.encard_le_encard hsub
    rw [Set.encard_singleton] at h1
    have h2 : ({(s' : ℕ) | s' ∈ s} : Set ℕ).encard = (L : ℕ∞) := by
      rw [hl]; exact hcard
    rw [h2] at h1
    norm_cast at h1
    omega
  · exact mem n hn

theorem mk_ap {N b m L : ℕ} (hm : 1 ≤ m) (P : Set.Icc 1 N → Prop)
    (hP : ∀ j < L, ∃ h : b + m * j ∈ Set.Icc 1 N, P ⟨_, h⟩) (l : ℕ∞) (hl : (L : ℕ∞) = l) :
    ∃ s : Finset (Set.Icc 1 N), ({(s' : ℕ) | s' ∈ s} : Set ℕ).IsAPOfLength l ∧
      ∀ x ∈ s, P x := by
  classical
  let s : Finset (Set.Icc 1 N) :=
    Finset.univ.filter (fun y => ∃ j < L, (y : ℕ) = b + m * j)
  have hS : ({(s' : ℕ) | s' ∈ s} : Set ℕ) =
      (((Finset.range L).image (fun j => b + m * j) : Finset ℕ) : Set ℕ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, ⟨j, hj, hy⟩, rfl⟩
      exact ⟨j, hj, hy.symm⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨h, _⟩ := hP j hj
      exact ⟨⟨_, h⟩, ⟨j, hj, rfl⟩, rfl⟩
  have inj : Function.Injective (fun j : ℕ => b + m * j) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (Nat.add_left_cancel hxy)
  refine ⟨s, ⟨b, m, ?_, ?_⟩, ?_⟩
  · change Set.encard _ = l
    rw [hS, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ inj,
      Finset.card_range, hl]
  · rw [hS]
    ext x
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Set.mem_setOf_eq, smul_eq_mul, ← hl, Nat.cast_lt]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by ring⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by ring⟩
  · intro x hx
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    obtain ⟨h, hPj⟩ := hP j hj
    have : x = ⟨_, h⟩ := Subtype.ext hxj
    rw [this]
    exact hPj

theorem nonempty : (Green14.mixedMonoAPGuaranteeSet 3 38).Nonempty := by
  classical
  obtain ⟨ι, hι, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin 38) (Fin 2)
  refine ⟨Fintype.card ι * 37 + 1, ?_⟩
  intro coloring
  let f : ℕ → Fin 2 := fun x =>
    if h : x ∈ Set.Icc 1 (Fintype.card ι * 37 + 1) then coloring ⟨x, h⟩ else 0
  obtain ⟨l, c, hl⟩ := hHJ (fun v => f (1 + ∑ i, ((v i : Fin 38) : ℕ)))
  have hsum : ∀ x : Fin 38, 1 + ∑ i, ((l x i : Fin 38) : ℕ) =
      (1 + ∑ i, (((l.idxFun i).getD 0 : Fin 38) : ℕ)) +
        (Finset.univ.filter fun i => l.idxFun i = none).card * (x : ℕ) := by
    intro x
    have h1 : ∀ i, ((l x i : Fin 38) : ℕ) = (((l.idxFun i).getD 0 : Fin 38) : ℕ) +
        if l.idxFun i = none then (x : ℕ) else 0 := by
      intro i
      show (((l.idxFun i).getD x : Fin 38) : ℕ) = _
      cases l.idxFun i <;> simp
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const, smul_eq_mul, add_zero]
    ring
  have hbound : ∀ v : ι → Fin 38, ∑ i, ((v i : Fin 38) : ℕ) ≤ Fintype.card ι * 37 := by
    intro v
    calc ∑ i, ((v i : Fin 38) : ℕ) ≤ ∑ _i : ι, 37 :=
          Finset.sum_le_sum fun i _ => by have := (v i).isLt; omega
      _ = Fintype.card ι * 37 := by simp [Finset.sum_const, Finset.card_univ]
  have hm : 1 ≤ (Finset.univ.filter fun i => l.idxFun i = none).card := by
    obtain ⟨i0, hi0⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i0, by simp [hi0]⟩
  have hpt : ∀ j < 38, ∃ h : (1 + ∑ i, (((l.idxFun i).getD 0 : Fin 38) : ℕ)) +
      (Finset.univ.filter fun i => l.idxFun i = none).card * j ∈
        Set.Icc 1 (Fintype.card ι * 37 + 1), coloring ⟨_, h⟩ = c := by
    intro j hj
    have e := hsum ⟨j, hj⟩
    have hb := hbound (l ⟨j, hj⟩)
    have hc := hl ⟨j, hj⟩
    simp only at e hc
    rw [e] at hc
    have hmem : (1 + ∑ i, (((l.idxFun i).getD 0 : Fin 38) : ℕ)) +
        (Finset.univ.filter fun i => l.idxFun i = none).card * j ∈
          Set.Icc 1 (Fintype.card ι * 37 + 1) := by
      rw [← e]
      constructor <;> omega
    refine ⟨hmem, ?_⟩
    simp only [f, dif_pos hmem] at hc
    exact hc
  have hc2 : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  rcases hc2 with rfl | rfl
  · left
    exact mk_ap (L := 3) hm (fun x => coloring x = 0) (fun j hj => hpt j (by omega)) 3 (by norm_num)
  · right
    exact mk_ap (L := 38) hm (fun x => coloring x = 1) (fun j hj => hpt j hj) 38 (by norm_num)

theorem notMem (N : ℕ) (hN : N ≤ 1378) : N ∉ Green14.mixedMonoAPGuaranteeSet 3 38 := by
  intro h
  rcases h (fun x => if col x.1 then 1 else 0) with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
  · obtain ⟨a, d, hd, hpts⟩ := ap_pts (L := 3) (by norm_num) s 3 hs (by norm_num)
    have key : ∀ n < 3, col (a + n * d) = false ∧ 1 ≤ a + n * d ∧ a + n * d ≤ N := by
      intro n hn
      obtain ⟨y, hy, hyv⟩ := hpts n hn
      have h1 := hc y hy
      have h2 := y.2
      rw [hyv] at h1 h2
      refine ⟨?_, h2.1, h2.2⟩
      cases hcol : col (a + n * d) <;> simp_all
    obtain ⟨k0, ha, _⟩ := key 0 (by norm_num)
    obtain ⟨k1, _, _⟩ := key 1 (by norm_num)
    obtain ⟨k2, _, hle⟩ := key 2 (by norm_num)
    simp only [Nat.zero_mul, add_zero, one_mul] at k0 k1 k2 ha hle
    rcases chk3_spec a d ha hd (by omega) with e | e | e <;> simp_all
  · obtain ⟨a, d, hd, hpts⟩ := ap_pts (L := 38) (by norm_num) s 38 hs (by norm_num)
    have key : ∀ n < 38, col (a + n * d) = true ∧ 1 ≤ a + n * d ∧ a + n * d ≤ N := by
      intro n hn
      obtain ⟨y, hy, hyv⟩ := hpts n hn
      have h1 := hc y hy
      have h2 := y.2
      rw [hyv] at h1 h2
      refine ⟨?_, h2.1, h2.2⟩
      cases hcol : col (a + n * d) <;> simp_all
    obtain ⟨_, ha, _⟩ := key 0 (by norm_num)
    obtain ⟨_, _, hle⟩ := key 37 (by norm_num)
    simp only [Nat.zero_mul, add_zero] at ha
    obtain ⟨i, hi, hci⟩ := chk38_spec a d ha hd (by omega)
    have := (key i hi).1
    rw [hci] at this
    exact Bool.false_ne_true this

end OMA.O6

theorem OMA.solution : type_of% @Green14.W_3_38_lower := by
  show 1379 ≤ Green14.W 3 38
  unfold Green14.W
  apply le_csInf OMA.O6.nonempty
  intro N hN
  by_contra hlt
  exact OMA.O6.notMem N (by omega) hN
