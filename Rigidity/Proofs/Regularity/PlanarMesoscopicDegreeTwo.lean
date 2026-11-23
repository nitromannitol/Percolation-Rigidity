import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoMain
import Rigidity.Proofs.Regularity.OrderOneOriginTwo
import Rigidity.Proofs.Percolation.SupercriticalUniqueness
import Rigidity.Proofs.Cluster.GehringCubes

/-!
# Lemma 7.3 at `k = 2` in the plane, almost surely

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, (7.18) at `k = 2`, for planar supercritical
bond percolation (`ArmstrongDarioMesoscopicDegreeTwoPlanar`), from two named inputs:

* `PlanarCoarseHarmonicApproximationTwo`: Lemma 7.1 in dimension two, in the ball form of the proof
  of Lemma 7.3, almost surely above a minimal scale `𝒳 ≤ O_s(θ)`
  (`PlanarCoarseApproximationAt`; the coarsening is `coarseAtAnchor`, `[u]_𝒫(y) = u(anchor of the
  partition cube of y)`);
* `PlanarPartCubeMoments p`: the minimal scales of Proposition 2.4 for the sizes of the planar
  partition cubes: for all `t, α > 0`, above a minimal scale `M ≤ O_r(θ)` the `t`-th moment of
  the sizes on the triadic cube `□_m ∋ 0` is at most `K |□_m|` and each size is at most `3^{α m}`.

The density of `𝒞_∞` in cubes is `exists_clusterCubeDensity_of_concentration` with
`cluster_density_concentration`. On a ball `B_R` the cube bounds give sides at most `9 R^{α/2}`
and moments of orders one and two at most `81 K R²` (`planar_cube_bounds`), and
`mesoscopicDegreeTwo_core` gives (7.18) with `δ = α/2`, `α ≤ 1` the exponent of Lemma 7.1
(`mesoscopicDegreeTwoAt_of_inputs`). With the planar corrector inputs this gives Theorem 2 (iii) at
`k = 1` in the plane (`armstrongDarioOrderOneOriginTwo_of_inputs`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.S2

/-- **Lemma 7.1 in dimension two, in the ball form of the proof of Lemma 7.3**, for one cluster:
the coarsening `[u]_𝒫` of `u` harmonic on `C ∩ B_R`, `R ≥ A X`, satisfies the harmonic
approximation hypothesis of Lemma 7.2 on the balls of `ℤ²`, is close to `u` on the cluster balls,
and its distance to a constant on a ball of `ℤ²` is bounded by that of `u` on the cluster ball. -/
def PlanarCoarseApproximationAt {ω : Configuration 2} (C : OpenComponent ω) (A α K X : ℝ) :
    Prop :=
  ∀ R : ℝ, A * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
    HarmonicApproximation (componentBallSeminorm (latticeComponent 2) 0)
        (latticeHarmonicClass 0) (clusterConstants (latticeComponent 2)) A α X R
        (K / R * ⨅ a : ℝ, clusterBallVolumeL2 C R (u - fun _ => a))
        (fun x => coarseAtAnchor C u x.val) ∧
      (∀ r : ℝ, X ≤ r → r ≤ R / A →
        clusterBallVolumeL2 C r (u - fun x => coarseAtAnchor C u x.val) ≤
          K / r * ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a)) ∧
      ∀ r : ℝ, X ≤ r → r ≤ R / A → ∀ a : ℝ,
        componentBallL2 (latticeComponent 2) 0 r (fun x => coarseAtAnchor C u x.val - a) ≤
          K * clusterBallVolumeL2 C (A * r) (u - fun _ => a)

/-- **Armstrong–Dario, Lemma 7.1, in dimension two**, in the form used in the proof of Lemma 7.3,
almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`. -/
def PlanarCoarseHarmonicApproximationTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ A α K : ℝ), 0 < s ∧ 0 < θ ∧ 2 ≤ A ∧ 0 < α ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        PlanarCoarseApproximationAt (uniqueInfiniteComponent h) A α K (X ω)

/-- **The minimal scales of Proposition 2.4 for the sizes of the planar partition cubes**
(Armstrong and Dario, Propositions 2.1 and 2.4, dimension two, form `O_s`). -/
def PlanarPartCubeMoments (p : unitInterval) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M r θ ∧
      ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, M ω ≤ 3 ^ m →
        ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
            ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t ≤
          K * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card ∧
        ∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
          (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ α

/-- The harmonic approximation hypothesis for an exponent gives it for a smaller exponent. -/
theorem HarmonicApproximation.mono_exponent {F : Type*} [AddCommGroup F]
    {N : ℝ → AddGroupSeminorm F} {Abar : ℝ → Set F} {P₀ : AddSubgroup F} {A α α' X R E : ℝ}
    {u : F} (h : HarmonicApproximation N Abar P₀ A α X R E u) (hX : 1 ≤ X) (hA : 0 < A)
    (hE : 0 ≤ E) (hαα : α' ≤ α) : HarmonicApproximation N Abar P₀ A α' X R E u := by
  intro r hr hrR
  have hr1 : 1 ≤ r := hX.trans hr
  have hr0 : 0 < r := by linarith
  refine (h r hr hrR).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)) ?_)
  exact add_nonneg (Real.iSup_nonneg fun s => div_nonneg (ballExcess_nonneg _ _ _ _)
    ((mul_pos hA hr0).le.trans s.2.1)) (div_nonneg hE hr0.le)

/-- Lemma 7.1 in the ball form gives the hypothesis of `mesoscopicDegreeTwo_core`. -/
theorem coarseApproximationAt_of_planar {ω : Configuration 2}
    {h : HasUniqueInfiniteOpenComponent ω} {A α α' K X : ℝ}
    (H : PlanarCoarseApproximationAt (uniqueInfiniteComponent h) A α K X) (hA : 2 ≤ A)
    (hK : 0 ≤ K) (hX : 1 ≤ X) (hαα : α' ≤ α) : CoarseApproximationAt h A α' K X := by
  intro R hR u hu
  obtain ⟨h1, h2, -⟩ := H R hR u hu
  have hR0 : 0 ≤ R := le_trans (mul_nonneg (by linarith) (by linarith)) hR
  exact ⟨h1.mono_exponent hX (by linarith) (mul_nonneg (div_nonneg hK hR0)
    (iInf_nonneg_of_nonneg fun _ => clusterBallVolumeL2_nonneg' _ _ _)) hαα, h2⟩

/-- The ball `B_R` lies in the triadic cube `□_m ∋ 0` when `2R + 1 ≤ 3^m`. -/
theorem mem_cube_zero_of_dist_lt {R : ℝ} {m : ℕ} (hm : 2 * R + 1 ≤ (3 : ℝ) ^ m) {y : Vertex 2}
    (hy : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R) :
    y ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2) := by
  rw [Rigidity.Proofs.Cluster.cube, Rigidity.Proofs.Cluster.mem_box]
  intro i
  have h3 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one m
  have h0 := Rigidity.Proofs.Cluster.halfSide_nonneg m
  have hc : Rigidity.Proofs.Cluster.center m (0 : Vertex 2) i = 0 := by
    simp only [Rigidity.Proofs.Cluster.center, Rigidity.Proofs.Cluster.idx, Pi.zero_apply,
      zero_add]
    rw [Int.ediv_eq_zero_of_lt h0 (by omega), mul_zero]
  rw [hc, sub_zero]
  have hi := abs_sub_le_dist_latticeEuclideanEmbedding y 0 i
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hi
  have h3r : 2 * (Rigidity.Proofs.Cluster.halfSide m : ℝ) + 1 = (3 : ℝ) ^ m := by
    exact_mod_cast h3
  by_contra hcon
  push Not at hcon
  have h5 : ((Rigidity.Proofs.Cluster.halfSide m + 1 : ℤ) : ℝ) ≤ ((|y i| : ℤ) : ℝ) :=
    Int.cast_le.2 (by omega)
  push_cast at h5
  linarith

/-- **The partition cubes on `B_R`** from the minimal scales: sides at most `9 R^β`, and moments
of orders one and two at most `81 K R²`. -/
theorem planar_cube_bounds {ω : Configuration 2} {K₁ K₂ β R M₁ M₂ : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hR : 1 ≤ R) (hM₁ : M₁ ≤ R) (hM₂ : M₂ ≤ R)
    (h₁ : ∀ m : ℕ, M₁ ≤ 3 ^ m →
      ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
          ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (1 : ℝ) ≤
        K₁ * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card ∧
      ∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
        (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ β)
    (h₂ : ∀ m : ℕ, M₂ ≤ 3 ^ m →
      ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
          ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ (2 : ℝ) ≤
        K₂ * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card ∧
      ∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
        (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ β)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    (∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R →
        (3 : ℝ) ^ (planarPartCube ω y).scale ≤ 9 * R ^ β) ∧
    (∑ y ∈ latticeBallPoints 0 R, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ 81 * K₁ * R ^ 2) ∧
    ∑ y ∈ latticeBallPoints 0 R, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤
      81 * K₂ * R ^ 2 := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ 2 * R + 1)
    (by norm_num : (1 : ℝ) < 3)
  have hm : 2 * R + 1 ≤ (3 : ℝ) ^ (n + 1) := hn2.le
  have hm9 : (3 : ℝ) ^ (n + 1) ≤ 9 * R := by rw [pow_succ]; linarith
  obtain ⟨hs₁, hmax⟩ := h₁ (n + 1) (by linarith)
  obtain ⟨hs₂, -⟩ := h₂ (n + 1) (by linarith)
  have hcard' : ((Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2)).card : ℝ) ≤
      81 * R ^ 2 := by
    rw [Rigidity.Proofs.Cluster.card_cube]
    have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := by positivity
    calc ((3 : ℝ) ^ (n + 1)) ^ 2 ≤ (9 * R) ^ 2 := pow_le_pow_left₀ h0 hm9 2
      _ = 81 * R ^ 2 := by ring
  have hsub : latticeBallPoints 0 R ⊆ Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2) := by
    intro y hy
    exact mem_cube_zero_of_dist_lt hm (mem_latticeBallPoints.1 hy)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have h1 := hmax y (mem_cube_zero_of_dist_lt hm hy)
    have h2 : ((3 : ℝ) ^ (n + 1)) ^ β ≤ (9 * R) ^ β :=
      Real.rpow_le_rpow (by positivity) hm9 hβ0
    have h3 : (9 * R) ^ β = (9 : ℝ) ^ β * R ^ β := Real.mul_rpow (by norm_num) (by linarith)
    have h4 : (9 : ℝ) ^ β ≤ 9 := by
      calc (9 : ℝ) ^ β ≤ 9 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 9 := Real.rpow_one 9
    have h5 : 0 ≤ R ^ β := Real.rpow_nonneg (by linarith) _
    calc (3 : ℝ) ^ (planarPartCube ω y).scale ≤ ((3 : ℝ) ^ (n + 1)) ^ β := h1
      _ ≤ (9 * R) ^ β := h2
      _ = (9 : ℝ) ^ β * R ^ β := h3
      _ ≤ 9 * R ^ β := mul_le_mul_of_nonneg_right h4 h5
  · calc ∑ y ∈ latticeBallPoints 0 R, (3 : ℝ) ^ (planarPartCube ω y).scale
        ≤ ∑ y ∈ Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2),
            (3 : ℝ) ^ (planarPartCube ω y).scale :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ y ∈ Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2),
            ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ (1 : ℝ) := by simp only [Real.rpow_one]
      _ ≤ K₁ * (Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2)).card := hs₁
      _ ≤ K₁ * (81 * R ^ 2) := mul_le_mul_of_nonneg_left hcard' hK₁
      _ = 81 * K₁ * R ^ 2 := by ring
  · calc ∑ y ∈ latticeBallPoints 0 R, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2
        ≤ ∑ y ∈ Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2),
            ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ y ∈ Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2),
            ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ (2 : ℝ) := by simp only [Real.rpow_two]
      _ ≤ K₂ * (Rigidity.Proofs.Cluster.cube (n + 1) (0 : Vertex 2)).card := hs₂
      _ ≤ K₂ * (81 * R ^ 2) := mul_le_mul_of_nonneg_left hcard' hK₂
      _ = 81 * K₂ * R ^ 2 := by ring

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane, for one law**, from Lemma 7.1
in the ball form and the minimal scales of the partition cubes. -/
theorem mesoscopicDegreeTwoAt_of_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hHA : ∃ (s θ A α K : ℝ), 0 < s ∧ 0 < θ ∧ 2 ≤ A ∧ 0 < α ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        PlanarCoarseApproximationAt (uniqueInfiniteComponent h) A α K (X ω))
    (hmom : PlanarPartCubeMoments p) : MesoscopicDegreeTwoAt 2 p := by
  obtain ⟨s₁, θ₁, A, α, K, hs₁, hθ₁, hA, hα, hK, X₁, hX₁m, hX₁1, hX₁os, hae₁⟩ := hHA
  obtain ⟨α', hα'⟩ : ∃ x : ℝ, x = min α 1 := ⟨_, rfl⟩
  have hα'0 : 0 < α' := by rw [hα']; exact lt_min hα one_pos
  have hα'1 : α' ≤ 1 := by rw [hα']; exact min_le_right _ _
  have hα'α : α' ≤ α := by rw [hα']; exact min_le_left _ _
  have hβ0 : 0 ≤ α' / 2 := by positivity
  have hβ1 : α' / 2 ≤ 1 := by linarith
  obtain ⟨K₁, r₁, θ₂, hK₁, hr₁, hθ₂, M₁, hM₁m, hM₁0, hM₁os, hae₂⟩ :=
    hmom 1 one_pos (α' / 2) (by positivity)
  obtain ⟨K₂, r₂, θ₃, hK₂, hr₂, hθ₃, M₂, hM₂m, hM₂0, hM₂os, hae₃⟩ :=
    hmom 2 two_pos (α' / 2) (by positivity)
  have hθp : 0 < LatticeProb.Percolation.theta 2 p := theta_pos_of_criticalProbability_lt 2 p hpc
  have hκ : 0 < LatticeProb.Percolation.theta 2 p / 2 := by positivity
  have hΛ24 := le_quadLocality (d := 2) two_pos (capFraction_pos (d := 2) two_pos hκ)
  have hΛ0 : 0 < quadLocality 2 (capFraction 2 (LatticeProb.Percolation.theta 2 p / 2)) :=
    lt_of_lt_of_le (by positivity) hΛ24
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1)
    (quadLocality 2 (capFraction 2 (LatticeProb.Percolation.theta 2 p / 2)))
  obtain ⟨M₃, hM₃m, hM₃0, hM₃os, hae₄⟩ := hcube 0
  obtain ⟨C, r₀, hC, hr₀, hcore⟩ := mesoscopicDegreeTwo_core (K₁ := 81 * K₁) (K₂ := 81 * K₂)
    (κ := LatticeProb.Percolation.theta 2 p / 2) (cS := 9) hA hα'0 hα'1 hK (by positivity)
    (by positivity) hκ (by norm_num)
  obtain ⟨c₀, hc₀⟩ : ∃ x : ℝ,
      x = r₀ + quadLocality 2 (capFraction 2 (LatticeProb.Percolation.theta 2 p / 2)) + 1 :=
    ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; linarith
  have hc₀r : r₀ ≤ c₀ := by rw [hc₀]; linarith
  have hc₀Λ : quadLocality 2 (capFraction 2 (LatticeProb.Percolation.theta 2 p / 2)) ≤ c₀ := by
    rw [hc₀]; linarith
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; linarith
  -- the random scale
  obtain ⟨s, hsdef⟩ : ∃ x : ℝ, x = min s₁ (min r₁ (min r₂ s₄)) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact lt_min hs₁ (lt_min hr₁ (lt_min hr₂ hs₄))
  have hs1 : s ≤ s₁ := by rw [hsdef]; exact min_le_left _ _
  have hs2 : s ≤ r₁ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ r₂ := by
    rw [hsdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : s ≤ s₄ := by
    rw [hsdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1os := IsOsBond.mono_exponent hs hs1 hX₁m hX₁os
  have h2os := IsOsBond.mono_exponent hs hs2 hM₁m hM₁os
  have h3os := IsOsBond.mono_exponent hs hs3 hM₂m hM₂os
  have h4os := IsOsBond.mono_exponent hs hs4 hM₃m hM₃os
  have h34 := IsOsBond.max hs (by positivity) (by positivity) hM₂m hM₃m h3os h4os
  have h234 := IsOsBond.max hs (by positivity) (by positivity) hM₁m (hM₂m.max hM₃m) h2os h34
  have h1234 := IsOsBond.max hs (by positivity) (by positivity) hX₁m
    (hM₁m.max (hM₂m.max hM₃m)) h1os h234
  have hXos := IsOsBond.const_mul hc₀0 h1234
  refine ⟨s, _, α' / 2, hs, by positivity, by positivity,
    fun ω => c₀ * max (X₁ ω) (max (M₁ ω) (max (M₂ ω) (M₃ ω))),
    (hX₁m.max (hM₁m.max (hM₂m.max hM₃m))).const_mul c₀,
    fun ω => mul_nonneg hc₀0.le ((zero_le_one.trans (hX₁1 ω)).trans (le_max_left _ _)), hXos,
    C, ?_⟩
  filter_upwards [hae₁, hae₂, hae₃, hae₄, ae_planarPartitionEvent hpc] with ω h₁ h₂ h₃ h₄ hP
  intro h R hR u hu r hr hrR
  obtain ⟨mx, hmx⟩ : ∃ x : ℝ, x = max (X₁ ω) (max (M₁ ω) (max (M₂ ω) (M₃ ω))) := ⟨_, rfl⟩
  have hR' : 2 * (c₀ * mx) ≤ R := by rw [hmx]; exact hR
  have hr' : c₀ * mx ≤ r := by rw [hmx]; exact hr
  have hmX : X₁ ω ≤ mx := by rw [hmx]; exact le_max_left _ _
  have hm1 : M₁ ω ≤ mx := by rw [hmx]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hm2 : M₂ ω ≤ mx := by
    rw [hmx]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hm3 : M₃ ω ≤ mx := by
    rw [hmx]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hX1 := hX₁1 ω
  have hmx1 : 1 ≤ mx := hX1.trans hmX
  have hcm : mx ≤ c₀ * mx := le_mul_of_one_le_left (by linarith) hc₀1
  have hr₀X : r₀ * X₁ ω ≤ c₀ * mx := mul_le_mul hc₀r hmX (by linarith) hc₀0.le
  have hRX : r₀ * X₁ ω ≤ R := by linarith
  have hrX : r₀ * X₁ ω ≤ r := by linarith
  have hRq : quadLocality 2 (capFraction 2 (LatticeProb.Percolation.theta 2 p / 2)) *
      max (M₃ ω) 1 ≤ R := by
    have h1 : max (M₃ ω) 1 ≤ mx := max_le hm3 hmx1
    have h2 := mul_le_mul hc₀Λ h1 (zero_le_one.trans (le_max_right _ _)) hc₀0.le
    linarith
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨hsize, hmo₁, hmo₂⟩ := planar_cube_bounds hβ0 hβ1 hR1 (by linarith) (by linarith)
    h₂ h₃ hK₁ hK₂
  exact hcore ω hP h (X₁ ω) (M₃ ω) R u hX1 hRX hRq hu
    (coarseApproximationAt_of_planar (h₁ h) hA hK hX1 hα'α) hsize hmo₁ hmo₂ (h₄ h) r hrX hrR

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane**, from Lemma 7.1 in the ball
form and the minimal scales of the planar partition cubes. -/
theorem armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs
    (hHA : PlanarCoarseHarmonicApproximationTwo)
    (hmom : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarPartCubeMoments p) :
    ArmstrongDarioMesoscopicDegreeTwoPlanar := fun p hpc hp1 =>
  mesoscopicDegreeTwoAt_of_inputs hpc hp1 (hHA p hpc hp1) (hmom p hpc hp1)

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in the plane**, from Lemma 7.1
in the ball form, the minimal scales of the planar partition cubes and the planar corrector
inputs. -/
theorem armstrongDarioOrderOneOriginTwo_of_inputs
    (hHA : PlanarCoarseHarmonicApproximationTwo)
    (hmom : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarPartCubeMoments p)
    (hcorr : CorrectorQuantitativeInputTwo) (hqual : SupercriticalBondCorrectorInputTwo) :
    ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar
    (armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs hHA hmom) hcorr hqual

end Rigidity.Proofs.Regularity
