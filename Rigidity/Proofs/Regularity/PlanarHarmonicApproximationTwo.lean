import Rigidity.Proofs.Regularity.PlanarClusterInclusions
import Rigidity.Proofs.Regularity.PlanarOrderZeroInput

/-!
# Armstrong–Dario, Lemma 7.1, in dimension two, from the estimates on squares, almost surely

`planarHarmonicApproximationTwo_of_squareEstimates` proves `PlanarHarmonicApproximationTwo` from
two statements on the planar partition, taken as hypotheses:

* `PlanarSquareEstimatesTwo p`: above a minimal scale `𝒳 ≤ O_s(θ)`, every `u` harmonic on
  `𝒞_∞ ∩ B_R` satisfies the estimates (7.3), (7.4) and the bound of Step 2 of the proof of Lemma 7.1
  on the squares `□_j`, `3^j ≥ 𝒳`, `L 3^{j + 3} ≤ R` (`PlanarSquareEstimates`);
* `PlanarPartitionSizeScale p`: above a minimal scale `𝓜 ≤ O_s(θ)`, the partition cubes of the
  vertices of `□_m` have scale at most `m - 2` (the second bound of (2.12) of the source,
  Proposition 2.4, which gives `size(□_𝒫(x)) ≤ 3^{2m/3}` for `t = 1`).

The density of the infinite cluster in triadic cubes (Dario–Gu, Proposition A.1, proved) gives a
vertex of `𝒞_∞` in every large square, so that the clusters of the squares lie in `𝒞_∞`
(`mem_supp_of_mem_clusterVertices`), and the bound on the partition cubes gives
`𝒞_∞ ∩ □_m ⊆ C_*(□_{m + 1})` (`mem_clusterVertices_succ`) and the resolution of the squares.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- The partition cubes of the vertices of `□_m` have scale at most `m - 2` above a minimal scale
`𝓜 ≤ O_s(θ)`. -/
def PlanarPartitionSizeScale (p : unitInterval) : Prop :=
  ∃ s θ : ℝ, 0 < s ∧ 0 < θ ∧
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, M ω ≤ 3 ^ m →
        ∀ x ∈ triadicCubeFinset 2 m 0, (planarPartCube ω x).scale + 2 ≤ m

/-- The estimates of the proof of Armstrong–Dario, Lemma 7.1, on the squares `□_j` above a
minimal scale `𝒳 ≤ O_s(θ)`, for the functions harmonic on the balls of the infinite cluster. -/
def PlanarSquareEstimatesTwo (p : unitInterval) : Prop :=
  ∃ s θ L C₁ K₂ K₃ α : ℝ, 0 < s ∧ 0 < θ ∧ 1 ≤ L ∧ 0 ≤ C₁ ∧ 0 ≤ K₂ ∧ 0 ≤ K₃ ∧ 0 < α ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
            PlanarSquareEstimates (uniqueInfiniteComponent h) C₁ K₂ K₃ α j u

/-- A vertex of a cluster in a large square, from the density in cubes. -/
theorem exists_mem_square_of_clusterCubeDensity {ω : Configuration 2} (C : OpenComponent ω)
    {ℓ κ : ℝ} (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 1 ℓ κ) {j : ℕ} (hj : ℓ ≤ 3 ^ j) :
    ∃ x : C, x.val ∈ triadicCubeFinset 2 j 0 := by
  have hin : ∀ y ∈ triadicCube 2 j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) <
        1 * 3 ^ j := by
    intro y hy
    rw [one_mul]
    rw [← coe_triadicCubeFinset] at hy
    exact dist_lt_of_mem_square hy
  have h := hcube j 0 hj hin
  have hpos : 0 < (clusterCubePoints C 0 (1 * 3 ^ j) j 0).card := by
    have : (0 : ℝ) < (clusterCubePoints C 0 (1 * 3 ^ j) j 0).card :=
      lt_of_lt_of_le (by positivity) h
    exact_mod_cast this
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  refine ⟨x, ?_⟩
  simp only [clusterCubePoints, mem_filter] at hx
  rw [mem_square_iff]
  intro i
  simpa using hx.2 i

/-- **Armstrong–Dario, Lemma 7.1, in dimension two** (`PlanarHarmonicApproximationTwo`), from
the estimates on squares and the bound on the scales of the partition cubes. -/
theorem planarHarmonicApproximationTwo_of_squareEstimates
    (hS : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarSquareEstimatesTwo p)
    (hM : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarPartitionSizeScale p) :
    PlanarHarmonicApproximationTwo := by
  intro p hpc hp1
  obtain ⟨s₁, θ₁, L, C₁, K₂, K₃, α, hs₁, hθ₁, hL, hC₁, hK₂, hK₃, hα, X, hXm, hX0, hXos, hSae⟩ :=
    hS p hpc hp1
  obtain ⟨s₂, θ₂, hs₂, hθ₂, M, hMm, hM0, hMos, hMae⟩ := hM p hpc hp1
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₃, θ₃, hs₃, hθ₃, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 1
  obtain ⟨Md, hMdm, hMd0, hMdos, hMdae⟩ := hcube 0
  set A := 4374 * L with hAdef
  set K := max 1 (max (K₂ * (4374 * L) / 162) (K₃ * (4374 * L) / 6)) with hKdef
  set c := squareScale (4374 * L) L C₁ K₂ α with hcdef
  have hc1 : 1 ≤ c := by
    rw [hcdef]; unfold squareScale; exact (le_max_left _ _).trans (le_max_right _ _)
  have hc0 : 0 < c := by linarith
  -- the minimal scale
  set s := min s₁ (min s₂ s₃) with hsdef
  have hs : 0 < s := lt_min hs₁ (lt_min hs₂ hs₃)
  have hss₁ : s ≤ s₁ := by rw [hsdef]; exact min_le_left _ _
  have hss₂ : s ≤ s₂ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hss₃ : s ≤ s₃ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have h1 := IsOsBond.mono_exponent hs hss₁ hXm hXos
  have h2 := IsOsBond.mono_exponent hs hss₂ hMm hMos
  have h3 := IsOsBond.mono_exponent hs hss₃ hMdm hMdos
  have h23 := IsOsBond.max hs (by positivity) (by positivity) hMm hMdm h2 h3
  have h123 := IsOsBond.max hs (by positivity) (by positivity) hXm (hMm.max hMdm) h1 h23
  have hone := isOsBond_const (p := p) (d := 2) one_pos hs
  have h1234 := IsOsBond.max hs (by positivity) (by positivity)
    (hXm.max (hMm.max hMdm)) measurable_const h123 hone
  have hcc := isOsBond_const (p := p) (d := 2) hc0 hs
  have h12345 := IsOsBond.max hs (by positivity) (by positivity)
    ((hXm.max (hMm.max hMdm)).max measurable_const) measurable_const h1234 hcc
  set Y : Configuration 2 → ℝ := fun ω => max (max (max (X ω) (max (M ω) (Md ω))) 1) c
    with hYdef
  have hYm : Measurable Y := ((hXm.max (hMm.max hMdm)).max measurable_const).max measurable_const
  have hY1 : ∀ ω, 1 ≤ Y ω := fun ω => (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨θY, hθY, hYos⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond 2 p Y s θ := ⟨_, by positivity, h12345⟩
  refine ⟨s, θY, A, α / 2, K, hs, hθY, by rw [hAdef]; linarith, by positivity,
    by rw [hKdef]; positivity, Y, hYm, hY1, hYos, ?_⟩
  filter_upwards [hSae, hMae, hMdae, ae_planarPartitionEvent hpc] with ω hω₁ hω₂ hω₃ hP h
  set C := uniqueInfiniteComponent h with hCdef
  have hinf : C.supp.Infinite := uniqueInfiniteComponent_infinite h
  set X₀ := max (X ω) (max (M ω) (Md ω)) with hX₀def
  have hXX₀ : X ω ≤ X₀ := le_max_left _ _
  have hMX₀ : M ω ≤ X₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hMdX₀ : Md ω ≤ X₀ := (le_max_right _ _).trans (le_max_right _ _)
  set X₁ := max X₀ 1 with hX₁def
  have hX₁1 : 1 ≤ X₁ := le_max_right _ _
  have hX₀X₁ : X₀ ≤ X₁ := le_max_left _ _
  have hκ : 0 < theta 2 p / 2 := by positivity
  have hsub : ∀ j : ℕ, X₁ ≤ 3 ^ j → ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp := by
    intro j hj x hx
    have hsize := hω₂ j (hMX₀.trans (hX₀X₁.trans hj))
    have hres : PlanarResolved ω ⟨j, 0⟩ := by
      intro z hz
      have hz' : z ∈ triadicCubeFinset 2 j 0 :=
        mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 hz)
      have := hsize z hz'
      show (planarPartCube ω z).scale ≤ j
      omega
    obtain ⟨x₀, hx₀⟩ := exists_mem_square_of_clusterCubeDensity C hκ (hω₃ h)
      (hMdX₀.trans (hX₀X₁.trans hj))
    exact mem_supp_of_mem_clusterVertices hP hres C hinf
      (mem_triadicCube_zero_iff.2 (mem_square_iff_int.1 hx₀)) x₀.2 hx
  have hgeo : ∀ (m : ℕ) (r : ℝ), X₁ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        x.val ∈ clusterVertices ω ⟨m + 1, 0⟩ := by
    intro m r hr hm x hx
    have hr0 : 0 ≤ r := by linarith
    have hsize := hω₂ m (by linarith)
    have hxm : x.val ∈ triadicCubeFinset 2 m 0 := mem_square_of_dist_lt (by linarith)
    exact mem_clusterVertices_succ hP C hinf hsize hxm x.2
  have hest : ∀ R : ℝ, ∀ u : C → ℝ, IsHarmonicInBall C R u → ∀ j : ℕ, X₁ ≤ 3 ^ j →
      L * 3 ^ (j + 3) ≤ R → PlanarSquareEstimates C C₁ K₂ K₃ α j u :=
    fun R u hu j hj hjR => hω₁ h R u hu j (hXX₀.trans (hX₀X₁.trans hj)) hjR
  have hfinal := planarHarmonicApproximationAt_of_squareEstimates hL hC₁ hK₂ hK₃ hα C hX₁1 hsub
    hgeo hest
  exact hfinal

end Rigidity.Proofs.Regularity
