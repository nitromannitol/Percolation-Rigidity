import Rigidity.External.ClusterDensity
import Rigidity.Proofs.Regularity.ClusterBallExcess

/-!
# Volume comparison and cap density of cluster balls from the density in cubes

The cluster-ball properties `ClusterBallVolumeComparison` and `ClusterBallCapDensity` used by the
iteration of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), on cluster balls follow from a lower
bound on the density of the cluster in the triadic cubes `□_m(3^m k)` (`triadicCube`) of size at
least `ℓ` inside a ball `B_R(z)` (`ClusterCubeDensity`): every cluster ball `C ∩ B_s(z)`,
`s ∈ [6 √d max ℓ 1, R]`, contains a cube of size comparable to `s` near `z`, and every cap
`C ∩ B_ρ(z) ∩ {±⟪p, x - z⟫ ≥ ‖p‖ ρ / 2}`, `ρ ∈ [24 √d max ℓ 1, R]`, contains a cube of size
comparable to `ρ` near `z ± (3ρ / 4) p / ‖p‖`, while a ball of radius `r ≥ 1` has at most
`(2 r + 3) ^ d` lattice points (`card_componentEuclideanBall_le`).

For the infinite cluster of supercritical bond percolation, the cube density with `κ = θ(p) / 2`
above a minimal scale is the consequence of the concentration of the density in triadic cubes
(Dario–Gu, Proposition A.1, `Rigidity.External.ClusterDensityConcentrationInput`).
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

theorem abs_sub_le_dist_latticeEuclideanEmbedding (y z : Vertex d) (i : Fin d) :
    |(y i : ℝ) - (z i : ℝ)| ≤ dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) := by
  have hi := PiLp.norm_apply_le (latticeEuclideanEmbedding y - latticeEuclideanEmbedding z) i
  change |(y i : ℝ) - (z i : ℝ)| ≤
    ‖latticeEuclideanEmbedding y - latticeEuclideanEmbedding z‖ at hi
  rwa [dist_eq_norm]

theorem dist_latticeEuclideanEmbedding_le {y : Vertex d} {w : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i, |(y i : ℝ) - w i| ≤ a) :
    dist (latticeEuclideanEmbedding y) w ≤ Real.sqrt d * a := by
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (latticeEuclideanEmbedding y i) (w i) ^ 2)
      ≤ Real.sqrt (∑ _i : Fin d, a ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        have hy : latticeEuclideanEmbedding y i = (y i : ℝ) := rfl
        rw [Real.dist_eq, hy]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = Real.sqrt d * a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ha]

/-- A cluster ball of radius `r ≥ 0` has at most `(2 r + 3) ^ d` vertices. -/
theorem card_componentEuclideanBall_le (C : OpenComponent ω) (z : Vertex d) {r : ℝ}
    (hr : 0 ≤ r) : ((componentEuclideanBall C z r).card : ℝ) ≤ (2 * r + 3) ^ d := by
  classical
  set box := Fintype.piFinset fun i : Fin d => Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)
  have hsub : (componentEuclideanBall C z r).map (Function.Embedding.subtype _) ⊆ box := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_componentEuclideanBall] at hx
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val z i
    have h2 : |(x.val i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉ : ℝ) := (h1.trans hx.le).trans (Int.le_ceil r)
    obtain ⟨hl, hu⟩ := abs_le.1 h2
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : (z i : ℝ) - (⌈r⌉ : ℝ) ≤ (x.val i : ℝ))
    · exact_mod_cast (by linarith : (x.val i : ℝ) ≤ (z i : ℝ) + (⌈r⌉ : ℝ))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have hIcc : ∀ i, ((Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)).card : ℝ) ≤ 2 * r + 3 := by
    intro i
    rw [Int.card_Icc]
    have h0 : 0 ≤ z i + ⌈r⌉ + 1 - (z i - ⌈r⌉) := by
      have := Int.ceil_nonneg hr
      linarith
    have hcast : (((z i + ⌈r⌉ + 1 - (z i - ⌈r⌉)).toNat : ℕ) : ℝ) =
        ((z i + ⌈r⌉ + 1 - (z i - ⌈r⌉) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [hcast]
    push_cast
    linarith [Int.ceil_lt_add_one r]
  have hbox : (box.card : ℝ) ≤ (2 * r + 3) ^ d := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    calc ∏ i, ((Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)).card : ℝ) ≤ ∏ _i : Fin d, (2 * r + 3) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => hIcc i
      _ = (2 * r + 3) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_le.2 hcard).trans hbox

/-- The vertices of the cluster ball `C ∩ B_R(z)` in the triadic cube `□_m(3^m k)`. -/
noncomputable def clusterCubePoints (C : OpenComponent ω) (z : Vertex d) (R : ℝ) (m : ℕ)
    (k : Vertex d) : Finset C :=
  (componentEuclideanBall C z R).filter fun x =>
    ∀ i, |((x.val i : ℤ) : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2

/-- Every triadic cube of size `3^m ≥ ℓ` inside the ball `B_R(z)` carries at least `κ 3^{d m}`
vertices of the cluster `C`. -/
def ClusterCubeDensity (C : OpenComponent ω) (z : Vertex d) (ℓ R κ : ℝ) : Prop :=
  ∀ (m : ℕ) (k : Vertex d), ℓ ≤ 3 ^ m →
    (∀ y ∈ triadicCube d m k,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < R) →
    κ * 3 ^ (d * m) ≤ (clusterCubePoints C z R m k).card

/-- The triadic cube of size `3^m` nearest to a point `w` lies within `√d 3^m` of `w`. -/
theorem dist_le_of_mem_triadicCube_round (m : ℕ) (w : EuclideanSpace ℝ (Fin d)) {y : Vertex d}
    (hy : ∀ i, |(y i : ℝ) - 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ)| < 3 ^ m / 2) :
    dist (latticeEuclideanEmbedding y) w ≤ Real.sqrt d * 3 ^ m := by
  apply dist_latticeEuclideanEmbedding_le (by positivity)
  intro i
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have h1 := abs_sub_round (w i / 3 ^ m)
  have h2 : |3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i| ≤ 3 ^ m / 2 := by
    have e : 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i =
        -(3 ^ m * (w i / 3 ^ m - round (w i / 3 ^ m))) := by field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos h3]
    nlinarith
  calc |(y i : ℝ) - w i| ≤ |(y i : ℝ) - 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ)| +
        |3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i| := abs_sub_le _ _ _
    _ ≤ 3 ^ m := by linarith [hy i]

/-- **A cube near `w`.** If the ball of radius `√d 3^m` around `w` lies in `B_ρ(z)`, `ρ ≤ R`, and
`3^m ≥ ℓ`, then at least `κ 3^{d m}` vertices of `C ∩ B_ρ(z)` lie within `√d 3^m` of `w`. -/
theorem le_card_filter_of_clusterCubeDensity (C : OpenComponent ω) (z : Vertex d) {ℓ R κ ρ : ℝ}
    (hcube : ClusterCubeDensity C z ℓ R κ) {m : ℕ} (hℓ : ℓ ≤ 3 ^ m)
    {w : EuclideanSpace ℝ (Fin d)}
    (hw : dist w (latticeEuclideanEmbedding z) + Real.sqrt d * 3 ^ m < ρ) (hρR : ρ ≤ R)
    (P : C → Prop) [DecidablePred P]
    (hP : ∀ x : C, dist (latticeEuclideanEmbedding x.val) w ≤ Real.sqrt d * 3 ^ m → P x) :
    κ * 3 ^ (d * m) ≤ ((componentEuclideanBall C z ρ).filter P).card := by
  set k : Vertex d := fun i => round (w i / 3 ^ m) with hk
  have hin : ∀ y : Vertex d, (∀ i, |(y i : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2) →
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < ρ := by
    intro y hy
    have := dist_le_of_mem_triadicCube_round m w hy
    calc dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z)
        ≤ dist (latticeEuclideanEmbedding y) w + dist w (latticeEuclideanEmbedding z) :=
          dist_triangle _ _ _
      _ < ρ := by linarith
  have h1 := hcube m k hℓ fun y hy => (hin y hy).trans_le hρR
  refine h1.trans (Nat.cast_le.2 (Finset.card_le_card ?_))
  intro x hx
  simp only [clusterCubePoints, Finset.mem_filter] at hx
  rw [Finset.mem_filter, mem_componentEuclideanBall]
  exact ⟨hin x.val hx.2, hP x (dist_le_of_mem_triadicCube_round m w hx.2)⟩

end Rigidity.Proofs.Regularity
