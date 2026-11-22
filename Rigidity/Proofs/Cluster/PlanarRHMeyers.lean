import Rigidity.Proofs.Cluster.PlanarRHLocal

/-!
# The planar Meyers estimate above a partition of local reverse Hölder cubes

Step 1 of the proof of Proposition 3.8 of Armstrong and Dario uses the reverse Hölder inequality on
the predecessors of the cells of the partition `𝓡` for the gradients of a solution on a larger
cluster. With the local family `planarRHGood A₀` this is immediate: for a function `w` harmonic in
the cluster `𝒞(V)` of a resolved cube and a child `cube k z` of a predecessor, the set
`𝒞(V) ∩ 3 cube k z` is closed under the open edges inside the triple and `w` is harmonic on it; the
energy densities agree on the child and are smaller on the triple
(`avg_clusterEnergy_le_of_planarRHCube`). Averaging over the nine children gives the reverse Hölder
inequality on the predecessor with constant `27 max(1, A₀)` (`avg_clusterEnergy_le_of_planarRHGood`),
and `meyers_triadic_uniform` gives the Meyers estimate with `ε` and `t` depending only on `A₀`
(`planar_meyers_rh_uniform`), in the form of `planar_meyers_clusterHarmonic_uniform`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- A lattice neighbour of a point of a cube lies in its triple. -/
theorem mem_enl_of_near_cube {k : ℕ} {z a b : Vertex 2} (ha : a ∈ cube k z)
    (hb : ∀ i, |b i - a i| ≤ 1) : b ∈ enl 1 k z := by
  rw [cube, mem_box] at ha
  rw [enl, mem_box]
  intro i
  have h1 := ha i
  have h2 := hb i
  have h3 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h4 := halfSide_nonneg k
  calc |b i - center k z i| ≤ |b i - a i| + |a i - center k z i| := abs_sub_le _ _ _
    _ ≤ 1 + halfSide k := add_le_add h2 h1
    _ ≤ halfSide (k + 1) := by rw [h3]; linarith

/-- **The reverse Hölder inequality on a child for the cluster of a resolved cube.** -/
theorem avg_clusterEnergy_le_of_planarRHCube (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {w : ClusterFun ω V} (hw : w ∈ clusterHarmonic ω V) {A₀ : ℝ}
    (hA₀ : 0 ≤ A₀) {k : ℕ} {z : Vertex 2} (hint : ∀ x ∈ enl 1 k z, V.IsInterior x)
    (hRH : PlanarRHCube A₀ ω k z) :
    avg (cube k z) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ≤
      A₀ * avg (enl 1 k z) (fun x => clusterEnergy ω (clusterVertices ω V)
        (clusterExtend ω V w) x ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) ^
          ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) := by
  set U₀ := clusterVertices ω V with hU₀
  set f := clusterExtend ω V w with hf
  set C := U₀.filter (· ∈ enl 1 k z) with hC
  have hCsub : C ⊆ enl 1 k z := fun a ha => (Finset.mem_filter.1 ha).2
  have hCU : C ⊆ U₀ := Finset.filter_subset _ _
  have hVmem : ∀ x ∈ enl 1 k z, x ∈ V.vertices := fun x hx =>
    hint x hx x fun i => by simp
  have hcl : ∀ a ∈ C, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 k z → b ∈ C := by
    intro a ha b hadj hb
    exact Finset.mem_filter.2 ⟨mem_clusterVertices_of_adj_mem hP hV (hCU ha) hadj (hVmem b hb), hb⟩
  have hu : ∀ a ∈ C, (∀ b, (openGraph ω).Adj a b → b ∈ C) → openLaplacian ω f a = 0 :=
    fun a ha _ => openLaplacian_clusterExtend_eq_zero hP hV hw (hCU ha) (hint a (hCsub ha))
  have h1 := hRH C hCsub hcl f hu
  have heq : ∀ a ∈ cube k z, clusterEnergy ω U₀ f a = clusterEnergy ω C f a := by
    intro a ha
    have haE := cube_subset_enl 1 k z ha
    unfold clusterEnergy
    by_cases haU : a ∈ U₀
    · have haC : a ∈ C := Finset.mem_filter.2 ⟨haU, haE⟩
      rw [if_pos haU, if_pos haC]
      unfold clusterGradSq
      congr 2
      refine Finset.filter_congr fun b hb => ?_
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hb
      have hbE : b ∈ enl 1 k z := mem_enl_of_near_cube ha fun i => by
        rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj hadj i
      constructor
      · intro hbU; exact Finset.mem_filter.2 ⟨hbU, hbE⟩
      · intro hbC; exact hCU hbC
    · have haC : a ∉ C := fun h => haU (hCU h)
      rw [if_neg haU, if_neg haC]
  have hle : ∀ a, clusterEnergy ω C f a ≤ clusterEnergy ω U₀ f a := by
    intro a
    unfold clusterEnergy
    by_cases haC : a ∈ C
    · rw [if_pos haC, if_pos (hCU haC)]
      exact clusterGradSq_le_of_subset ω hCU f a
    · rw [if_neg haC]
      split_ifs
      · exact clusterGradSq_nonneg ω U₀ f a
      · exact le_rfl
  have e1 : avg (cube k z) (clusterEnergy ω U₀ f) = avg (cube k z) (clusterEnergy ω C f) := by
    unfold avg
    rw [Finset.sum_congr rfl heq]
  rw [e1]
  refine h1.trans ?_
  have hθ : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) / ((2 : ℕ) + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ (by positivity)) hA₀
  · exact div_nonneg (Finset.sum_nonneg fun a _ =>
      Real.rpow_nonneg (clusterEnergy_nonneg ω C f a) _) (Nat.cast_nonneg _)
  · unfold avg
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow (clusterEnergy_nonneg ω C f a) (hle a) hθ

theorem rpow_two_thirds_div_nine (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1)) / 9) ^ ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) = a / 27 := by
  have e1 : (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1)) = 2 / 3 := by norm_num
  have e2 : ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) = 3 / 2 := by norm_num
  rw [e1, e2, Real.div_rpow (Real.rpow_nonneg ha _) (by norm_num), ← Real.rpow_mul ha]
  have h9 : (9 : ℝ) ^ (3 / 2 : ℝ) = 27 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h9]
  norm_num

/-- **The reverse Hölder inequality on a predecessor** from the local family, with constant
`27 max(1, A₀)`. -/
theorem avg_clusterEnergy_le_of_planarRHGood (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {w : ClusterFun ω V} (hw : w ∈ clusterHarmonic ω V) {A₀ : ℝ}
    {k : ℕ} {y : Vertex 2} (hint : ∀ x ∈ enl 1 k y, V.IsInterior x)
    (hgood : (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω) :
    avg (cube k y) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ≤
      27 * max 1 A₀ * avg (enl 1 k y) (fun x => clusterEnergy ω (clusterVertices ω V)
        (clusterExtend ω V w) x ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) ^
          ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) := by
  set G := clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) with hGdef
  have hG0 : ∀ x, 0 ≤ G x := fun x => clusterEnergy_nonneg _ _ _ x
  set θ : ℝ := ((2 : ℕ) : ℝ) / ((2 : ℕ) + 1) with hθ
  set ι : ℝ := (((2 : ℕ) : ℝ) + 1) / (2 : ℕ) with hι
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hι0 : 0 ≤ ι := by rw [hι]; positivity
  have hM1 : (1 : ℝ) ≤ max 1 A₀ := le_max_left _ _
  have havg0 : 0 ≤ avg (enl 1 k y) (fun x => G x ^ θ) :=
    div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hG0 x) _) (Nat.cast_nonneg _)
  cases k with
  | zero =>
    rw [avg, cube_zero, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one]
    have hyE : y ∈ enl 1 0 y := cube_subset_enl 1 0 y (mem_cube_self 0 y)
    have hcard : ((enl 1 0 y).card : ℝ) = 9 := by rw [card_enl]; norm_num
    have hlow : G y ^ θ / 9 ≤ avg (enl 1 0 y) (fun x => G x ^ θ) := by
      rw [avg, hcard]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum
        (f := fun x => G x ^ θ) (fun x _ => Real.rpow_nonneg (hG0 x) _) hyE) (by norm_num)
    have h1 : G y / 27 ≤ avg (enl 1 0 y) (fun x => G x ^ θ) ^ ι := by
      rw [← rpow_two_thirds_div_nine (G y) (hG0 y)]
      exact Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg (hG0 y) _) (by norm_num)) hlow hι0
    have h2 : (0 : ℝ) ≤ avg (enl 1 0 y) (fun x => G x ^ θ) ^ ι := Real.rpow_nonneg havg0 _
    have h3 := mul_le_mul_of_nonneg_right hM1 h2
    rw [one_mul] at h3
    have h4 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 27 by norm_num)
    have h5 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 27 by norm_num)
    calc G y = 27 * (G y / 27) := by ring
      _ ≤ _ := h4
      _ ≤ _ := h5
      _ = _ := by ring
  | succ k' =>
    have hsub : ∀ z ∈ cube (k' + 1) y, cube k' z ⊆ cube (k' + 1) y := fun z hz =>
      (cube_subset_succ k' z).trans (cube_eq_of_mem hz).le
    have henl : ∀ z ∈ cube (k' + 1) y, enl 1 k' z ⊆ enl 1 (k' + 1) y := fun z hz =>
      (enl_subset_enl (Nat.le_succ k') 1 z).trans (enl_eq_of_mem hz).le
    have hchild : ∀ z ∈ cube (k' + 1) y, avg (cube k' z) G ≤
        27 * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
      intro z hz
      have hRH : PlanarRHCube (max 1 A₀) ω k' z := by
        have h := hgood k' rfl z (mem_triadicCube_idx_iff.2 hz)
        intro C hC hcl u hu
        refine (h C hC hcl u hu).trans ?_
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ?_ _)
        exact div_nonneg (Finset.sum_nonneg fun x _ =>
          Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ x) _) (Nat.cast_nonneg _)
      have h1 := avg_clusterEnergy_le_of_planarRHCube hP hV hw (by positivity)
        (fun x hx => hint x (henl z hz hx)) hRH
      refine h1.trans ?_
      have hcard : ((enl 1 (k' + 1) y).card : ℝ) = 9 * (enl 1 k' z).card := by
        rw [card_enl, card_enl]
        ring
      have hpos : (0 : ℝ) < (enl 1 k' z).card := by rw [card_enl]; positivity
      have hav : avg (enl 1 k' z) (fun x => G x ^ θ) ≤
          9 * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) := by
        rw [avg, avg, hcard, div_le_iff₀ hpos]
        have : ∑ x ∈ enl 1 k' z, G x ^ θ ≤ ∑ x ∈ enl 1 (k' + 1) y, G x ^ θ :=
          Finset.sum_le_sum_of_subset_of_nonneg (henl z hz)
            fun x _ _ => Real.rpow_nonneg (hG0 x) _
        have e : 9 * ((∑ x ∈ enl 1 (k' + 1) y, G x ^ θ) / (9 * (enl 1 k' z).card)) *
            (enl 1 k' z).card = ∑ x ∈ enl 1 (k' + 1) y, G x ^ θ := by
          field_simp
        rw [e]
        exact this
      have h9 : (9 * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ)) ^ ι =
          27 * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
        rw [Real.mul_rpow (by norm_num) havg0, hι]
        have : (9 : ℝ) ^ ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) = 27 := by
          rw [show ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) = (3 / 2 : ℝ) by norm_num,
            show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [this]
      calc max 1 A₀ * avg (enl 1 k' z) (fun x => G x ^ θ) ^ ι
          ≤ max 1 A₀ * (9 * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ)) ^ ι :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg
              fun x _ => Real.rpow_nonneg (hG0 x) _) (Nat.cast_nonneg _)) hav hι0) (by positivity)
        _ = 27 * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
            rw [h9]; ring
    have hpos : (0 : ℝ) < (cube (k' + 1) y).card := card_cube_pos _ _
    rw [avg, sum_eq_sum_cube_avg hsub G, div_le_iff₀ hpos]
    calc ∑ z ∈ cube (k' + 1) y, (∑ x ∈ cube k' z, G x) / (cube k' z).card
        ≤ ∑ _z ∈ cube (k' + 1) y,
            27 * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι :=
          Finset.sum_le_sum fun z hz => hchild z hz
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The planar Meyers estimate above a partition of local reverse Hölder cubes, with `ε` and `t`
chosen before the moment bound** (Armstrong and Dario, Proposition 3.8, deterministic part, in
dimension two, with the predecessors in the family of Definition 3.7). -/
theorem planar_meyers_rh_uniform (A₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2) := by
  have hA : (1 : ℝ) ≤ 27 * max 1 A₀ := by
    have := le_max_left (1 : ℝ) A₀
    linarith
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_triadic_uniform (d := 2) (by norm_num) hA
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω hP V hV w hw n x₀ s hint hcell hnb hΩ hcubes hmom
  refine hMK n x₀ _ s (fun x => clusterEnergy_nonneg _ _ _ x) hcell hnb hΩ
    (fun k y hk hsub => ?_) hmom
  exact avg_clusterEnergy_le_of_planarRHGood hP hV hw (fun x hx => hint x (hsub hx))
    (hcubes k y hk hsub)

end Rigidity.Proofs.Cluster
