import PercolationClusterHomogenization.Proofs.Density.InfluenceSpatialMoment
import PercolationClusterHomogenization.Proofs.Density.TriadicCubeGeometry
import PercolationClusterHomogenization.Proofs.Percolation.BondShellMomentRoots

/-!
# Summability of density influence moment roots

The moment roots required to estimate a sum of squared single-bond influences are summable over
all bonds, with a bound proportional to the volume of the counting cube.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The `Lʳ` norms of squared planar density-count influences sum at the cube-volume scale. -/
theorem planar_density_influence_moment_roots_summable (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∀ e : Bond 2, Integrable (fun q : Configuration 2 × Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ (2 * r))
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ∧
      Summable (fun e : Bond 2 => (∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ (2 * r)
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ^ (1 / (r : ℝ))) ∧
      (∑' e : Bond 2, (∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ (2 * r)
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ^ (1 / (r : ℝ))) ≤
        C * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 := by
  classical
  obtain ⟨a, A, ha, hA, hmoment⟩ := planar_density_influence_polynomial_moment p hp
  obtain ⟨a', A', b, B, ha', hA', hb, hB, hspatial⟩ :=
    planar_density_influence_spatial_moment p hp
  let s : ℕ := 2 * r
  let Q : ℝ := (4 : ℝ) ^ (s + 1) * (((2 * s).factorial : ℝ) / a ^ (2 * s)) * A
  let T : ℝ := (4 : ℝ) ^ (2 * s + 1) *
    (((2 * (2 * s)).factorial : ℝ) / a' ^ (2 * (2 * s))) * A'
  let K : ℝ := Q + Real.sqrt T * Real.sqrt B + 1
  let c : ℝ := b / 2
  let t : ℝ := 1 / (r : ℝ)
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 * Real.exp (-(c * t) * Real.sqrt n)
  let C : ℝ := 36 * K ^ t * (1 + ∑' n, q n)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hqsum : Summable q := Rigidity.Percolation.summable_shift_square_exp_sqrt _ (mul_pos hc ht)
  have hq0 : 0 ≤ ∑' n, q n := tsum_nonneg fun n => by dsimp [q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let z : Vertex 2 := fun i => (3 : ℤ) ^ m * k i
  let R : ℕ := 3 ^ m
  let f : Bond 2 → ℝ := fun e => ∫ q : Configuration 2 × Configuration 2,
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ s ∂μ
  have hf (e : Bond 2) : 0 ≤ f e := integral_nonneg fun q => pow_nonneg (abs_nonneg _) _
  have hglobal (e : Bond 2) : f e ≤ K := by
    have h := (hmoment m k e s hs).2
    have hQK : Q ≤ K := by dsimp [K]; nlinarith [mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg B)]
    exact h.trans hQK
  have hdecay (n : ℕ) (hn : 1 ≤ n) (e : Bond 2)
      (he : e ∈ Rigidity.Percolation.bondShell 2 z R n) :
      f e ≤ K * Real.exp (-c * Real.sqrt n) := by
    obtain ⟨i, hsep⟩ := Rigidity.Percolation.bondShell_separated z R n e he
    have hsep' : ∀ x ∈ triadicCube 2 m k, ∀ y ∈ e.val,
        (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| :=
      fun x hx => hsep x (triadicCube_subset_cubeAt m k hx)
    have h := (hspatial m k e s hs i n hn hsep').2
    have hsqrt : Real.sqrt (B * Real.exp (-(b * Real.sqrt n))) =
        Real.sqrt B * Real.exp (-c * Real.sqrt n) := by
      rw [Real.sqrt_mul hB.le, ← Real.exp_half]
      congr 1
      dsimp [c]
      ring
    rw [hsqrt] at h
    have hTK : Real.sqrt T * Real.sqrt B ≤ K := by dsimp [K]; linarith
    exact h.trans (by
      calc
        _ = (Real.sqrt T * Real.sqrt B) * Real.exp (-c * Real.sqrt n) := by ring
        _ ≤ K * Real.exp (-c * Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hTK (Real.exp_pos _).le)
  obtain ⟨_, hfs, hsum⟩ := Rigidity.Percolation.summable_planar_bond_shells_rpow z R f K c t
    hK.le hc ht hf hglobal hdecay
  refine ⟨fun e => (hmoment m k e s hs).1, hfs, hsum.trans ?_⟩
  change 36 * ((R : ℝ) + 1) ^ 2 * K ^ t * (1 + ∑' n, q n) ≤
    C * ((R : ℝ) + 1) ^ 2
  dsimp only [C]
  exact le_of_eq (by ring)

end Rigidity.Proofs.S2
