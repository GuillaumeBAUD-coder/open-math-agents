import FormalConjectures.GreensOpenProblems.«24»

/-! Encode a progression by two points on the same side of the median.
Their order distinguishes the two possible signs of its common difference. -/

open Green24 Green24.variants Filter

namespace OMA.Median

def encode (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  let (x,y) := p
  let z := x + 3*(y-x)
  if y < c then (if x < y then (x,y) else (y,z))
  else (if x < y then (y,z) else (x,y))

lemma encode_inj (c : ℤ) {x y u v : ℤ} (hxy : x ≠ y) (huv : u ≠ v)
    (h : encode c (x,y) = encode c (u,v)) : (x,y) = (u,v) := by
  dsimp only [encode] at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at * <;> omega

def pairs (A : Finset ℤ) := (A ×ˢ A).filter (fun (x,y) => x ≠ y ∧ x+3*(y-x) ∈ A)

lemma count (A : Finset ℤ) {n : ℕ} (ha : A.card = n) (hn : 2 ≤ n) :
    4*(pairs A).card ≤ 3*n^2 := by
  let i : Fin n := ⟨n/2, by omega⟩
  let e := A.orderEmbOfFin ha
  let c := e i
  let L := (Finset.Iio i).map e.toEmbedding
  let U := (Finset.Ici i).map e.toEmbedding
  have sides {z : ℤ} (hz : z ∈ A) : (z < c → z ∈ L) ∧ (c ≤ z → z ∈ U) := by
    have hz' : z ∈ Set.range e := by rwa [A.range_orderEmbOfFin ha]
    obtain ⟨j,rfl⟩ := hz'
    exact ⟨fun h => Finset.mem_map.mpr ⟨j,Finset.mem_Iio.mpr (e.lt_iff_lt.mp h),rfl⟩,
      fun h => Finset.mem_map.mpr ⟨j,Finset.mem_Ici.mpr (e.le_iff_le.mp h),rfl⟩⟩
  have maps : Set.MapsTo (encode c) (pairs A) ((L ×ˢ L ∪ U ×ˢ U : Finset _) : Set _) := by
    rintro ⟨x,y⟩ hp
    obtain ⟨hp, hxy, hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    by_cases h : y < c <;> by_cases h' : x < y <;> simp only [encode, h, h', if_true, if_false]
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨(sides hx).1 (by omega),(sides hy).1 h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨(sides hy).1 h,(sides hz).1 (by omega)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨(sides hy).2 (by omega),(sides hz).2 (by omega)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨(sides hx).2 (by omega),(sides hy).2 (by omega)⟩)
  have hij : ((pairs A : Finset _) : Set _).InjOn (encode c) := by
    rintro ⟨x,y⟩ hx ⟨u,v⟩ hu he
    exact encode_inj c (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hu).2.1 he
  have bound := (Finset.card_le_card_of_injOn (encode c) maps hij).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product, L, U, Finset.card_map, Fin.card_Iio, Fin.card_Ici, i] at bound
  have parity : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
  rcases parity with h | h
  · have hh : n - n/2 = n/2 := by omega
    rw [hh] at bound
    nlinarith [congrArg (fun z : ℕ => z^2) h]
  · have hh : n - n/2 = n/2+1 := by omega
    rw [hh] at bound
    nlinarith [congrArg (fun z : ℕ => z^2) h, show 1 ≤ n/2 by omega]

end OMA.Median

theorem OMA.solution : type_of% @Green24.variants.upper_HL := by
  unfold gamma
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le _ (x := 0) fun n => by positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : max013AffineTranslates n ≤ 3*n^2/4 := by
      apply csSup_le
      · refine ⟨_, (Finset.range n).image Int.ofNat, ?_, rfl⟩
        simp [Finset.card_image_of_injective _ Int.ofNat_injective]
      · rintro k ⟨A,ha,rfl⟩
        apply Nat.le_div_iff_mul_le (by decide) |>.mpr
        simpa [OMA.Median.pairs, mul_comm 4] using OMA.Median.count A ha hn
    have hnat : 4 * max013AffineTranslates n ≤ 3*n^2 := by omega
    have hr : 4*(max013AffineTranslates n : ℝ) ≤ 3*(n : ℝ)^2 := by exact_mod_cast hnat
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
