import Rigidity.Proofs.Regularity.LatticeHarmonicExcess
import Rigidity.Proofs.Regularity.OrderOneOrigin
import Rigidity.Proofs.Regularity.OrderZeroLiouville
import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Draft.Section3Statements

/-!
# Armstrong–Dario, Lemma 7.1, in dimension two: statement and squares of the lattice

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Lemma 7.1, approximate the coarsening `[u]_𝒫` of a function `u` harmonic on
the infinite cluster by `ā`-harmonic functions on the triadic cubes `□_m`, and the proof of
Lemma 7.3 turns this into the harmonic approximation hypothesis of Lemma 7.2 on balls. In
dimension two, with the homogenized problem discretized (the function `u_hom` of Theorem 1 being
harmonic for the lattice Laplacian), the approximating class on the balls of `ℤ²` is
`latticeHarmonicClass 0`.

This file states the outcome in the form used by the iteration
(`PlanarHarmonicApproximationTwo`): above a minimal scale `𝒳 ≤ O_s(θ)`, for `R ≥ A 𝒳` and `u`
harmonic on `𝒞_∞ ∩ B_R`, the coarsening `[u]_𝒫` (`planarCoarse`, the value of `u` at the anchor
of the partition cube) satisfies the hypothesis of Lemma 7.2 on the balls of the lattice with
`E = K R^{-1} inf_a R^{-1} ‖u - a‖_{L²(𝒞_∞ ∩ B_R)}`, `u` is close to `[u]_𝒫` on the cluster
balls (the `L²` form of (7.4)), and the normalized norms of `[u]_𝒫 - a` on the balls of the
lattice are bounded by those of `u - a` on larger cluster balls.

It also introduces the normalized `ℓ²` norms on the squares `□_m = ℤ² ∩ (-3^m/2, 3^m/2)²`
(`squareL2`), the oscillation `inf_a ‖f - a‖_{L̲²(□_m)}` (`squareOsc`) and the distance to the
lattice harmonic functions on `□_m` (`squareHarmonicDist`), and compares the normalized norms on
squares and on the balls of the lattice: a ball inside a square (`componentBallL2_le_squareL2`) and
a square inside a ball (`squareL2_le_componentBallL2`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- The coarsening `[u]_𝒫` of a function on an open component of a planar configuration: the
value of `u`, extended by `0` off the component, at the anchor of the partition cube. -/
noncomputable def planarCoarse {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ) :
    Vertex 2 → ℝ :=
  fun y => Rigidity.Section3.extend C u (planarCoarseAnchor ω y)

/-- The conclusion of Armstrong–Dario, Lemma 7.1, in dimension two, for one cluster `C` above the
scale `X`, in the form used in the proof of Lemma 7.3: for `R ≥ A X` and `u` harmonic on
`C ∩ B_R`, the coarsening `[u]_𝒫` satisfies on the balls of `ℤ²` the harmonic approximation
hypothesis of Lemma 7.2 with the lattice harmonic functions and
`E = K R^{-1} inf_a R^{-1} ‖u - a‖_{L²(C ∩ B_R)}`; for `r ∈ [X, R / A]`,
`r^{-1} ‖u - [u]_𝒫‖_{L²(C ∩ B_r)} ≤ K r^{-1} inf_a (A r)^{-1} ‖u - a‖_{L²(C ∩ B_{A r})}`
(the `L²` form of (7.4)); and, for every `a ∈ ℝ`,
`‖[u]_𝒫 - a‖_{L̲²(B_r)} ≤ K (A r)^{-1} ‖u - a‖_{L²(C ∩ B_{A r})}` on the balls of `ℤ²` (the bound
of Step 2 of the proof of Lemma 7.1 with `w` constant). -/
def PlanarHarmonicApproximationAt {ω : Configuration 2} (C : OpenComponent ω) (A α K X : ℝ) :
    Prop :=
  ∀ R : ℝ, A * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
    HarmonicApproximation (componentBallSeminorm (latticeComponent 2) 0)
        (latticeHarmonicClass 0) (clusterConstants (latticeComponent 2)) A α X R
        (K / R * ⨅ a : ℝ, clusterBallVolumeL2 C R (u - fun _ => a))
        (fun x => planarCoarse C u x.val) ∧
      (∀ r : ℝ, X ≤ r → r ≤ R / A →
        clusterBallVolumeL2 C r (u - fun x => planarCoarse C u x.val) ≤
          K / r * ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a)) ∧
      ∀ r : ℝ, X ≤ r → r ≤ R / A → ∀ a : ℝ,
        componentBallL2 (latticeComponent 2) 0 r (fun x => planarCoarse C u x.val - a) ≤
          K * clusterBallVolumeL2 C (A * r) (u - fun _ => a)

/-- **Armstrong–Dario, Lemma 7.1, in dimension two**, in the form used in the proof of Lemma 7.3
(`PlanarHarmonicApproximationAt`), almost surely on the infinite cluster above a minimal scale
`𝒳 ≤ O_s(θ)`. -/
def PlanarHarmonicApproximationTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ A α K : ℝ), 0 < s ∧ 0 < θ ∧ 2 ≤ A ∧ 0 < α ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        PlanarHarmonicApproximationAt (uniqueInfiniteComponent h) A α K (X ω)

/-! ### Squares of the lattice -/

/-- The normalized `ℓ²` norm `‖g‖_{L̲²(□_m)} = (3^{-2m} ∑_{□_m} g²)^{1/2}` on the square
`□_m = ℤ² ∩ (-3^m/2, 3^m/2)²`. -/
noncomputable def squareL2 (m : ℕ) (g : Vertex 2 → ℝ) : ℝ :=
  Real.sqrt ((∑ y ∈ triadicCubeFinset 2 m 0, g y ^ 2) / 3 ^ (2 * m))

/-- The oscillation `inf_{a ∈ ℝ} ‖f - a‖_{L̲²(□_m)}`. -/
noncomputable def squareOsc (m : ℕ) (f : Vertex 2 → ℝ) : ℝ :=
  ⨅ a : ℝ, squareL2 m (fun y => f y - a)

/-- The functions on `ℤ²` harmonic for the lattice Laplacian at every point of `□_m`. -/
def squareHarmonic (m : ℕ) : Set (Vertex 2 → ℝ) :=
  {F | ∀ y ∈ triadicCubeFinset 2 m 0, latticeLaplacian F y = 0}

/-- The distance `inf_{w ∈ Ā(□_m)} ‖f - w‖_{L̲²(□_m)}` to the lattice harmonic functions. -/
noncomputable def squareHarmonicDist (m : ℕ) (f : Vertex 2 → ℝ) : ℝ :=
  ⨅ F : squareHarmonic m, squareL2 m (f - F)

theorem squareL2_nonneg (m : ℕ) (g : Vertex 2 → ℝ) : 0 ≤ squareL2 m g :=
  Real.sqrt_nonneg _

theorem zero_mem_squareHarmonic (m : ℕ) : (0 : Vertex 2 → ℝ) ∈ squareHarmonic m :=
  fun _ _ => by simp [latticeLaplacian]

theorem squareOsc_le (m : ℕ) (f : Vertex 2 → ℝ) (a : ℝ) :
    squareOsc m f ≤ squareL2 m (fun y => f y - a) :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ squareL2_nonneg _ _⟩ a

theorem squareOsc_nonneg (m : ℕ) (f : Vertex 2 → ℝ) : 0 ≤ squareOsc m f :=
  le_ciInf fun _ => squareL2_nonneg _ _

theorem squareHarmonicDist_nonneg (m : ℕ) (f : Vertex 2 → ℝ) : 0 ≤ squareHarmonicDist m f := by
  haveI : Nonempty (squareHarmonic m) := ⟨⟨0, zero_mem_squareHarmonic m⟩⟩
  exact le_ciInf fun _ => squareL2_nonneg _ _

theorem sum_sq_square_eq (m : ℕ) (g : Vertex 2 → ℝ) :
    ∑ y ∈ triadicCubeFinset 2 m 0, g y ^ 2 = (3 : ℝ) ^ (2 * m) * squareL2 m g ^ 2 := by
  have h3 : (0 : ℝ) < 3 ^ (2 * m) := by positivity
  rw [squareL2, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) h3.le)]
  field_simp

theorem mem_square_iff (m : ℕ) (y : Vertex 2) :
    y ∈ triadicCubeFinset 2 m 0 ↔ ∀ i, |(y i : ℝ)| < 3 ^ m / 2 := by
  rw [← Finset.mem_coe, coe_triadicCubeFinset]
  simp [triadicCube]

/-- The points of `ℤ²` at distance less than `3^m / 2` from the origin lie in `□_m`. -/
theorem mem_square_of_dist_lt {m : ℕ} {y : Vertex 2}
    (hy : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) <
      3 ^ m / 2) : y ∈ triadicCubeFinset 2 m 0 := by
  rw [mem_square_iff]
  intro i
  have h := abs_sub_le_dist_latticeEuclideanEmbedding y 0 i
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h
  exact h.trans_lt hy

/-- The points of `□_m` lie at distance less than `3^m` from the origin. -/
theorem dist_lt_of_mem_square {m : ℕ} {y : Vertex 2} (hy : y ∈ triadicCubeFinset 2 m 0) :
    dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < 3 ^ m := by
  rw [mem_square_iff] at hy
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have hle := dist_latticeEuclideanEmbedding_le (y := y)
    (w := latticeEuclideanEmbedding (0 : Vertex 2)) (a := 3 ^ m / 2) (by positivity) fun i => by
      show |(y i : ℝ) - ((0 : Vertex 2) i : ℝ)| ≤ 3 ^ m / 2
      simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
      exact (hy i).le
  have e : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  rw [e] at hle
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  calc _ ≤ Real.sqrt 2 * (3 ^ m / 2) := hle
    _ < 2 * (3 ^ m / 2) := by gcongr
    _ = 3 ^ m := by ring

theorem mem_latticeComponent_supp (y : Vertex 2) : y ∈ (latticeComponent 2).supp := by
  rw [latticeComponent_supp]; trivial

/-- Square sums over a lattice ball are sums over its points in `ℤ²`. -/
theorem sum_latticeBall_eq (r : ℝ) (g : Vertex 2 → ℝ) :
    ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 r, g x.val ^ 2 =
      ∑ y ∈ (componentEuclideanBall (latticeComponent 2) 0 r).image Subtype.val, g y ^ 2 :=
  (sum_image (f := fun y => g y ^ 2) fun _ _ _ _ h => Subtype.val_injective h).symm

theorem mem_image_latticeBall {r : ℝ} {y : Vertex 2} :
    y ∈ (componentEuclideanBall (latticeComponent 2) 0 r).image Subtype.val ↔
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < r := by
  rw [mem_image_componentEuclideanBall]
  exact ⟨fun h => h.2, fun h => ⟨mem_latticeComponent_supp y, h⟩⟩

/-- A lattice ball containing `□_j` has at least `3^{2j}` points. -/
theorem le_card_latticeBall {r : ℝ} {j : ℕ} (hj : (3 : ℝ) ^ j ≤ r) :
    (3 : ℝ) ^ (2 * j) ≤ (componentEuclideanBall (latticeComponent 2) 0 r).card := by
  classical
  have hsub : triadicCubeFinset 2 j 0 ⊆
      (componentEuclideanBall (latticeComponent 2) 0 r).image Subtype.val := fun y hy =>
    mem_image_latticeBall.2 ((dist_lt_of_mem_square hy).trans_le hj)
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := componentEuclideanBall (latticeComponent 2) 0 r)
    (f := Subtype.val)
  rw [card_triadicCubeFinset] at h1
  exact_mod_cast h1.trans h2

/-- **A ball inside a square.** If `B_r ⊆ □_m` and `□_j ⊆ B_r`, the normalized norm on `B_r` is
at most `3^m / 3^j` times the one on `□_m`. -/
theorem componentBallL2_le_squareL2 {r : ℝ} {m j : ℕ}
    (hsub : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        y ∈ triadicCubeFinset 2 m 0)
    (hj : (3 : ℝ) ^ j ≤ r) (g : Vertex 2 → ℝ) :
    componentBallL2 (latticeComponent 2) 0 r (fun x => g x.val) ≤
      (3 : ℝ) ^ m / 3 ^ j * squareL2 m g := by
  have hc := le_card_latticeBall hj
  have h3 : (0 : ℝ) < 3 ^ (2 * j) := by positivity
  have hcpos : (0 : ℝ) < (componentEuclideanBall (latticeComponent 2) 0 r).card := h3.trans_le hc
  have hsum : ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 r, g x.val ^ 2 ≤
      ∑ y ∈ triadicCubeFinset 2 m 0, g y ^ 2 := by
    rw [sum_latticeBall_eq]
    exact sum_le_sum_of_subset_of_nonneg (fun y hy => hsub y (mem_image_latticeBall.1 hy))
      fun _ _ _ => sq_nonneg _
  rw [sum_sq_square_eq] at hsum
  have hK : 0 ≤ (3 : ℝ) ^ m / 3 ^ j * squareL2 m g :=
    mul_nonneg (by positivity) (squareL2_nonneg _ _)
  rw [componentBallL2, Real.sqrt_le_left hK, div_le_iff₀ hcpos]
  calc ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 r, g x.val ^ 2
      ≤ (3 : ℝ) ^ (2 * m) * squareL2 m g ^ 2 := hsum
    _ = ((3 : ℝ) ^ m / 3 ^ j * squareL2 m g) ^ 2 * 3 ^ (2 * j) := by
        rw [pow_mul', pow_mul']; field_simp
    _ ≤ ((3 : ℝ) ^ m / 3 ^ j * squareL2 m g) ^ 2 *
          (componentEuclideanBall (latticeComponent 2) 0 r).card :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)

/-- **A square inside a ball.** If `3^j ≤ s`, the normalized norm on `□_j` is at most
`(2 s + 3) / 3^j` times the one on the lattice ball `B_s`. -/
theorem squareL2_le_componentBallL2 {s : ℝ} {j : ℕ} (hj : (3 : ℝ) ^ j ≤ s) (g : Vertex 2 → ℝ) :
    squareL2 j g ≤ (2 * s + 3) / 3 ^ j *
      componentBallL2 (latticeComponent 2) 0 s (fun x => g x.val) := by
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hs : 0 ≤ s := h3.le.trans hj
  have hsum : ∑ y ∈ triadicCubeFinset 2 j 0, g y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 s, g x.val ^ 2 := by
    rw [sum_latticeBall_eq]
    exact sum_le_sum_of_subset_of_nonneg
      (fun y hy => mem_image_latticeBall.2 ((dist_lt_of_mem_square hy).trans_le hj))
      fun _ _ _ => sq_nonneg _
  rw [sum_sq_square_eq, sum_sq_eq_card_mul_componentBallL2_sq] at hsum
  have hcard := card_componentEuclideanBall_le (latticeComponent 2) 0 hs
  have hK : 0 ≤ (2 * s + 3) / 3 ^ j *
      componentBallL2 (latticeComponent 2) 0 s (fun x => g x.val) :=
    mul_nonneg (by positivity) (componentBallL2_nonneg _ _ _ _)
  rw [← Real.sqrt_sq hK, squareL2]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (by positivity)]
  set N := componentBallL2 (latticeComponent 2) 0 s (fun x => g x.val)
  calc ∑ y ∈ triadicCubeFinset 2 j 0, g y ^ 2 ≤ (3 : ℝ) ^ (2 * j) * squareL2 j g ^ 2 := by
        rw [sum_sq_square_eq]
    _ ≤ ((componentEuclideanBall (latticeComponent 2) 0 s).card : ℝ) * N ^ 2 := hsum
    _ ≤ (2 * s + 3) ^ 2 * N ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = ((2 * s + 3) / 3 ^ j * N) ^ 2 * 3 ^ (2 * j) := by
        rw [pow_mul']; field_simp

end Rigidity.Proofs.Regularity
