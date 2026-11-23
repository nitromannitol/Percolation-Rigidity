import Rigidity.Proofs.Regularity.PlanarCoarseComparison

/-!
# The comparison (7.8) on planar squares, almost surely above a minimal scale

`planarCoarseComparisonTwo_of_minimalScales` proves the comparison (7.8) of the proof of
Armstrong–Dario, Lemma 7.1 (arXiv:1609.09431v2), in `L²` on the squares of the plane, almost surely
above a minimal scale `𝒳 ≤ O_s(θ)`, from the minimal scales of Proposition 2.4
(`PlanarMinimalScalesTwo p`), the density of the infinite cluster (proved) and the planar Meyers
estimate on the reverse Hölder cells (`planar_meyers_rh_uniform`, proved). The ingredients at one
scale are `coarseComparison_on_square`; here they are checked above the minimal scale:

* the cells of the reverse Hölder partition inside `□_{j+1}` have scale at most `j + 1`
  (the bound `3^{s(x)} ≤ 3^{m/2}` of Proposition 2.4) and satisfy the moment bound used by the
  Meyers estimate (`meyers_on_square`);
* the reach scales of the planar partition are bounded by its reach
  (`three_pow_reachScale_le_planarReach`), whose moments are bounded by Proposition 2.4
  (`sum_reachScale_rpow_le`);
* the squares are resolved and their clusters lie in the infinite cluster
  (`PlanarClusterInclusions`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal

variable {ω : Configuration 2}

/-- The reach scale of the planar coarse-graining data is bounded by the reach of the partition. -/
theorem three_pow_reachScale_le_planarReach (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (z : Vertex 2) :
    (3 : ℝ≥0∞) ^ (planarCoarseData hP U hU).reachScale z ≤ planarReach ω z := by
  have hown : (3 : ℝ≥0∞) ^ (planarPartCube ω z).scale ≤ planarReach ω z := by
    unfold planarReach
    refine le_iSup₂ (f := fun (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
      z ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) => (3 : ℝ≥0∞) ^ Q.scale) (planarPartCube ω z)
      ⟨(planarPartCube_spec hP z).2, ?_⟩
    rw [TriadicCube.mem_ninefold]
    intro i
    have h1 := (planarPartCube ω z).abs_sub_center_le (planarPartCube_spec hP z).1 i
    have h2 := (planarPartCube ω z).two_mul_ninefoldRadius
    have hpos : (1 : ℤ) ≤ 3 ^ (planarPartCube ω z).scale := one_le_pow₀ (by norm_num)
    omega
  unfold CoarseData.reachScale
  rcases Finset.eq_empty_or_nonempty ((planarCoarseData hP U hU).cluster.filter
      fun x => z ∈ (planarCoarseData hP U hU).region x) with h | h
  · rw [h, Finset.sup_empty]
    exact (one_le_pow₀ (by norm_num)).trans hown
  · obtain ⟨x, hx, hxsup⟩ := Finset.exists_mem_eq_sup _ h
      (fun x => ((planarCoarseData hP U hU).part x).scale)
    rw [hxsup]
    obtain ⟨hxc, hzx⟩ := Finset.mem_filter.1 hx
    have hxU : x ∈ U.vertices := (mem_clusterVertices.1 hxc).1
    have hzw : z ∈ ((planarPartCube ω x).thicken 4).vertices :=
      planarClusterWindow_subset_thicken hP hU hxU hzx
    rw [← TriadicCube.ninefold_vertices_eq_thicken] at hzw
    unfold planarReach
    exact le_iSup₂ (f := fun (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
      z ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) => (3 : ℝ≥0∞) ^ Q.scale) (planarPartCube ω x)
      ⟨(planarPartCube_spec hP x).2, Finset.mem_coe.2 hzw⟩

/-- **Moments of the reach scales** on the cluster of `□_j` from the moments of the reach on the
triadic cube of scale `j`. -/
theorem sum_reachScale_rpow_le (hP : PlanarPartitionEvent ω) {j : ℕ}
    (hres : PlanarResolved ω ⟨j, 0⟩) {τ K : ℝ} (hτ : 0 < τ)
    (hfin : ∀ x ∈ cube j (0 : Vertex 2), planarReach ω x ≠ ⊤)
    (hsum : ∑ x ∈ cube j (0 : Vertex 2), planarReach ω x ^ ⌈τ⌉₊ ≤
      ENNReal.ofReal (K * (cube j (0 : Vertex 2)).card)) (hK : 0 ≤ K) :
    ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤ K * 9 ^ j := by
  have hcube : ((cube j (0 : Vertex 2)).card : ℝ) = 9 ^ j := by
    rw [card_cube, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have hpt : ∀ z ∈ clusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤
        (planarReach ω z).toReal ^ ⌈τ⌉₊ := by
    intro z hz
    have hzc : z ∈ cube j (0 : Vertex 2) :=
      mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
    have hle := three_pow_reachScale_le_planarReach hP hres z
    have hle' : (3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z ≤
        (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (hfin z hzc) hle
      simpa using this
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z :=
      one_le_pow₀ (by norm_num)
    calc ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ
        ≤ (planarReach ω z).toReal ^ τ := Real.rpow_le_rpow (by positivity) hle' hτ.le
      _ ≤ (planarReach ω z).toReal ^ (⌈τ⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (h1.trans hle') (Nat.le_ceil τ)
      _ = (planarReach ω z).toReal ^ ⌈τ⌉₊ := Real.rpow_natCast _ _
  have hsub : clusterVertices ω ⟨j, 0⟩ ⊆ cube j (0 : Vertex 2) :=
    fun z hz => mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
  calc ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ hres).reachScale z) ^ τ
      ≤ ∑ z ∈ clusterVertices ω ⟨j, 0⟩, (planarReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ z ∈ cube j (0 : Vertex 2), (planarReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ z ∈ cube j (0 : Vertex 2), planarReach ω z ^ ⌈τ⌉₊).toReal := by
        rw [ENNReal.toReal_sum fun z hz => ENNReal.pow_ne_top (hfin z hz)]
        exact Finset.sum_congr rfl fun z _ => (ENNReal.toReal_pow _ _).symm
    _ ≤ (ENNReal.ofReal (K * (cube j (0 : Vertex 2)).card)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = K * 9 ^ j := by
        rw [ENNReal.toReal_ofReal (by positivity), hcube]

theorem enl_one_zero_eq_cube (j : ℕ) : enl 1 j (0 : Vertex 2) = cube (j + 1) (0 : Vertex 2) := by
  rw [enl, cube, center_zero, center_zero]

/-- **The Meyers estimate on `□_j`** for the restriction of `u` to the cluster of `□_{j+2}`, from the
cells of the reverse Hölder partition. -/
theorem meyers_on_square {A₀ ε t K CM : ℝ}
    (hMey : ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
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
          CM * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2))
    (hP : PlanarPartitionEvent ω) (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (hres2 : PlanarResolved ω ⟨j + 2, 0⟩)
    (h2C : ∀ x ∈ clusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    (s : Vertex 2 → ℕ) (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (hnb : ∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1)
    (hrh : ∀ (k : ℕ) (y : Vertex 2), s y ≤ k → (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω)
    (hsize : ∀ z ∈ cube (j + 1) (0 : Vertex 2), s z ≤ j + 1)
    (hmom : ∑ x ∈ cube j (0 : Vertex 2), ((3 : ℝ) ^ s x) ^ t ≤ K * (cube j (0 : Vertex 2)).card) :
    avg (cube j (0 : Vertex 2)) (fun x => clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 j (0 : Vertex 2)) (clusterEnergy ω (clusterVertices ω ⟨j + 2, 0⟩)
        (clusterExtend ω ⟨j + 2, 0⟩ (clusterRestrictTo C u ⟨j + 2, 0⟩))) ^ (1 + ε / 2) := by
  have hw := clusterRestrictTo_mem_clusterHarmonic hP hres2 C h2C fun x hx hxV _ => by
    refine hharm x hx ?_
    have h1 := mem_square_of_mem_clusterVertices hxV
    rw [mem_square_iff_int] at h1 ⊢
    intro i
    have := h1 i
    have h3 : (3 : ℤ) ^ (j + 2) ≤ 3 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine hMey ω hP ⟨j + 2, 0⟩ hres2 _ hw j 0 s ?_ hcell hnb ?_ (fun k y hk _ => hrh k y hk) hmom
  · intro x hx y hy
    have hx1 := mem_square_of_mem_enl hx
    rw [mem_triadicCube_zero_iff]
    intro i
    have h1 := (mem_square_iff_int.1 hx1) i
    have h2 := hy i
    have h3 : (3 : ℤ) ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
    have hpos : (1 : ℤ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have ha := abs_sub_abs_le_abs_sub (y i) (x i)
    rw [abs_sub_comm (y i) (x i)] at ha
    omega
  · intro z hz
    rw [enl_one_zero_eq_cube] at hz ⊢
    intro w hw'
    have hle := hsize z hz
    have h1 : w ∈ cube (j + 1) z := cube_mono hle z hw'
    rw [cube_eq_of_mem hz] at h1
    exact h1

theorem two_mul_le_of_three_pow_le_rpow_half {a m : ℕ}
    (h : (3 : ℝ) ^ a ≤ ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ)) : a * 2 ≤ m := by
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), ← pow_mul] at hsq
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hsq

/-- The comparison (7.8) of the proof of Armstrong–Dario, Lemma 7.1, in `L²` on the squares
`□_j` of the plane, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for
the functions harmonic on `𝒞_∞ ∩ B_R`, `2 · 3^{j+3} ≤ R`. -/
def PlanarCoarseComparisonTwo (p : unitInterval) : Prop :=
  ∃ s θ K₂ : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ K₂ ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → 2 * 3 ^ (j + 3) ≤ R →
            clusterSquareL2 ω j (fun x => Rigidity.Section3.extend (uniqueInfiniteComponent h) u x -
                planarCoarse (uniqueInfiniteComponent h) u x) ≤
              K₂ / 3 ^ j * clusterSquareOsc (uniqueInfiniteComponent h) u (j + 3)

/-- Harmonicity on `𝒞 ∩ □_{j+3}` from harmonicity on `𝒞 ∩ B_R`, `2 · 3^{j+3} ≤ R`. -/
theorem harm_on_square_of_isHarmonicInBall {C : OpenComponent ω} {R : ℝ} {u : C → ℝ}
    (hu : IsHarmonicInBall C R u) {j : ℕ} (hjR : 2 * 3 ^ (j + 3) ≤ R) :
    ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ triadicCubeFinset 2 (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0 := by
  intro x hx hxsq
  have hd := dist_lt_of_mem_square hxsq
  have h3 : (3 : ℝ) ≤ 3 ^ (j + 3) := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) * 1 ≤ 3 ^ (j + 3) := by
    have : Real.sqrt ((2 : ℕ) : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  refine hu ⟨x, hx⟩ ?_ fun y hy => ?_
  · rw [mem_componentEuclideanBall]; linarith
  · rw [mem_componentEuclideanBall]
    have hadj : (openGraph ω).Adj x y.val := hy
    have hy1 : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x) ≤
        Real.sqrt ((2 : ℕ) : ℝ) * 1 := by
      apply dist_latticeEuclideanEmbedding_le zero_le_one
      intro i
      have := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hadj) i
      have e : (latticeEuclideanEmbedding x) i = (x i : ℝ) := rfl
      rw [e]
      exact_mod_cast this
    have := dist_triangle (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding (0 : Vertex 2))
    linarith

/-- **The comparison (7.8) on planar squares almost surely**, from the minimal scales of
Proposition 2.4. -/
theorem planarCoarseComparisonTwo_of_minimalScales {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hM5 : PlanarMinimalScalesTwo p) :
    PlanarCoarseComparisonTwo p := by
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ :=
    planarPartitionSizeScale_of_minimalScales hM5
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := hM5
  obtain ⟨ε, hε, t, ht, hMK⟩ := planar_meyers_rh_uniform A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  have hpq := Real.HolderConjugate.conjExponent hq
  have hτ : 0 < 4 * Real.conjExponent (1 + ε / 2) := by have := hpq.symm.pos; positivity
  obtain ⟨Kr, r₂, θ₂, hKr, hr₂, hθ₂, M₂, hM₂m, hM₂0, hM₂os, hM₂ae⟩ :=
    hmoms (4 * Real.conjExponent (1 + ε / 2)) hτ (1 / 2) (by norm_num)
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 1
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  set r := min (min r₁ r₂) (min s₃ s₄) with hrdef
  have hr : 0 < r := lt_min (lt_min hr₁ hr₂) (lt_min hs₃ hs₄)
  have hr1 : r ≤ r₁ := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ r₂ := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ s₃ := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr4 : r ≤ s₄ := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have h1 := IsOsBond.mono_exponent hr hr1 hM₁m hM₁os
  have h2 := IsOsBond.mono_exponent hr hr2 hM₂m hM₂os
  have h3 := IsOsBond.mono_exponent hr hr3 hM₃m hM₃os
  have h4 := IsOsBond.mono_exponent hr hr4 hM₄m hM₄os
  have h12 := IsOsBond.max hr (by positivity) (by positivity) hM₁m hM₂m h1 h2
  have h34 := IsOsBond.max hr (by positivity) (by positivity) hM₃m hM₄m h3 h4
  have h1234 := IsOsBond.max hr (by positivity) (by positivity) (hM₁m.max hM₂m)
    (hM₃m.max hM₄m) h12 h34
  obtain ⟨θX, hθX, hXos⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond 2 p
      (fun ω => max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) r θ := ⟨_, by positivity, h1234⟩
  have hK₂0 : 0 ≤ 12 * planarCoarseConst *
      Real.sqrt (CM ^ (1 / (1 + ε / 2)) * Kr ^ (1 / Real.conjExponent (1 + ε / 2))) := by
    have := planarCoarseConst_nonneg; positivity
  refine ⟨r, θX, _, hr, hθX, hK₂0, _, (hM₁m.max hM₂m).max (hM₃m.max hM₄m),
    fun ω => (hM₁0 ω).trans ((le_max_left _ _).trans (le_max_left _ _)), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₂ae, hM₃ae, hM₄ae, ae_planarPartitionEvent hpc] with
    ω hcells hω₁ hω₂ hω₃ hω₄ hP h R u hu j hj hjR
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  have hinf := uniqueInfiniteComponent_infinite h
  have hle : ∀ m, j ≤ m → (3 : ℝ) ^ j ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hj1 : M₁ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
  have hj2 : M₂ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
  have hj3 : M₃ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_right _ _)).trans hj
  have hj4 : M₄ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_right _ _)).trans hj
  have hres : ∀ m, j ≤ m → PlanarResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset 2 m 0 := mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 hz)
    have := hω₃ m (hj3.trans (hle m hm)) z hz'
    show (planarPartCube ω z).scale ≤ m
    omega
  have hκ : 0 < theta 2 p / 2 := by positivity
  have hsub : ∀ m, j ≤ m → ∀ x ∈ clusterVertices ω ⟨m, 0⟩, x ∈ (uniqueInfiniteComponent h).supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_square_of_clusterCubeDensity (uniqueInfiniteComponent h) hκ
      (hω₄ h) (hj4.trans (hle m hm))
    exact mem_supp_of_mem_clusterVertices hP (hres m hm) _ hinf
      (mem_triadicCube_zero_iff.2 (mem_square_iff_int.1 hx₀)) x₀.2 hx
  have hsucc : ∀ m, j ≤ m → ∀ x ∈ triadicCubeFinset 2 m 0, x ∈ (uniqueInfiniteComponent h).supp →
      x ∈ clusterVertices ω ⟨m + 1, 0⟩ := fun m hm x hx hxC =>
    mem_clusterVertices_succ hP _ hinf (hω₃ m (hj3.trans (hle m hm))) hx hxC
  have h02 : clusterVertices ω ⟨j, 0⟩ ⊆ clusterVertices ω ⟨j + 2, 0⟩ := by
    intro x hx
    have hxC := hsub j le_rfl x hx
    have hx1 : x ∈ triadicCubeFinset 2 (j + 1) 0 := by
      have := mem_square_of_mem_clusterVertices hx
      rw [mem_square_iff_int] at this ⊢
      intro i
      have h := this i
      have h3 : (3 : ℤ) ^ j ≤ 3 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    exact hsucc (j + 1) (by omega) x hx1 hxC
  have hharm := harm_on_square_of_isHarmonicInBall hu hjR
  -- the Meyers estimate
  have hω₁' := hω₁ (j + 1) (hj1.trans (hle (j + 1) (by omega)))
  have hsize : ∀ z ∈ cube (j + 1) (0 : Vertex 2), sc ω z ≤ j + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half (hω₁'.2.1 z hz)
    omega
  have hMeyj := meyers_on_square hMey hP (uniqueInfiniteComponent h) u (hres (j + 2) (by omega))
    (hsub (j + 2) (by omega)) hharm (sc ω) hcell hnb hrh hsize (hω₁ j hj1).1
  -- the moments of the reach scales
  have hω₂j := hω₂ j hj2
  have hfin : ∀ x ∈ cube j (0 : Vertex 2), planarReach ω x ≠ ⊤ := fun x hx =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hω₂j.2.2.2.2.2 x hx)
  have hreach := sum_reachScale_rpow_le hP (hres j le_rfl) hτ hfin hω₂j.2.2.2.2.1 hKr
  have hreach' : ∑ z ∈ clusterVertices ω ⟨j, 0⟩,
      (((3 : ℝ) ^ (planarCoarseData hP ⟨j, 0⟩ (hres j le_rfl)).reachScale z) ^ (4 : ℕ)) ^
        Real.conjExponent (1 + ε / 2) ≤ Kr * 9 ^ j := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) hreach
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  exact coarseComparison_on_square hP (uniqueInfiniteComponent h) u (hres j le_rfl) h02
    (hsub (j + 2) (by omega)) (hsucc (j + 2) (by omega)) hharm hq hCM hKr hMeyj hreach'

end Rigidity.Proofs.Regularity
