import Rigidity.Proofs.S2.InfluenceSpatialMoment
import Rigidity.Proofs.S2.TriadicCubeGeometry
import Rigidity.Proofs.Percolation.BondShellStretchedExponential

/-!
# Summability of density influence moments

The moments of single-bond influences are summable over bonds, with a bound proportional to the
volume of the triadic cube and explicit dependence on the moment order.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- Planar density influence moments sum over bonds at the volume scale. -/
theorem planar_density_influence_moments_summable (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ a A a' A' D : ℝ, 0 < a ∧ 0 < A ∧ 0 < a' ∧ 0 < A' ∧ 0 < D ∧
      ∀ (m : ℕ) (k : Vertex 2) (r : ℕ), 1 ≤ r →
      (∀ e : Bond 2, Integrable (fun q : Configuration 2 × Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ∧
      Summable (fun e : Bond 2 => ∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ∧
      (∑' e : Bond 2, ∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤
        D * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 *
          max ((4 : ℝ) ^ (r + 1) * (((2 * r).factorial : ℝ) / a ^ (2 * r)) * A)
            (Real.sqrt ((4 : ℝ) ^ (2 * r + 1) *
              (((2 * (2 * r)).factorial : ℝ) / a' ^ (2 * (2 * r))) * A')) := by
  classical
  obtain ⟨a, A, ha, hA, hmoment⟩ := planar_density_influence_polynomial_moment p hp
  obtain ⟨a', A', b, B, ha', hA', hb, hB, hspatial⟩ :=
    planar_density_influence_spatial_moment p hp
  let c : ℝ := b / 2
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)
  let D : ℝ := 36 * (1 + Real.sqrt B) * (1 + ∑' n, q n)
  have hc : 0 < c := by dsimp [c]; positivity
  have hqsum : Summable q := Rigidity.Percolation.summable_shift_square_exp_sqrt c hc
  have hq0 : 0 ≤ ∑' n, q n := tsum_nonneg fun n => by dsimp [q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨a, A, a', A', D, ha, hA, ha', hA', hD, fun m k r hr => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let z : Vertex 2 := fun i => (3 : ℤ) ^ m * k i
  let R : ℕ := 3 ^ m
  let Q : ℝ := (4 : ℝ) ^ (r + 1) * (((2 * r).factorial : ℝ) / a ^ (2 * r)) * A
  let T : ℝ := (4 : ℝ) ^ (2 * r + 1) *
    (((2 * (2 * r)).factorial : ℝ) / a' ^ (2 * (2 * r))) * A'
  let M : ℝ := max Q (Real.sqrt T)
  let K : ℝ := M * (1 + Real.sqrt B)
  let f : Bond 2 → ℝ := fun e => ∫ q : Configuration 2 × Configuration 2,
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r ∂μ
  have hM : 0 ≤ M := (Real.sqrt_nonneg T).trans (le_max_right _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hMle : M ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hM (Real.sqrt_nonneg B)]
  have hf (e : Bond 2) : 0 ≤ f e := integral_nonneg fun q => pow_nonneg (abs_nonneg _) _
  have hglobal (e : Bond 2) : f e ≤ K :=
    (hmoment m k e r hr).2.trans ((le_max_left _ _).trans hMle)
  have hdecay (n : ℕ) (hn : 1 ≤ n) (e : Bond 2)
      (he : e ∈ Rigidity.Percolation.bondShell 2 z R n) :
      f e ≤ K * Real.exp (-c * Real.sqrt n) := by
    obtain ⟨i, hsep⟩ := Rigidity.Percolation.bondShell_separated z R n e he
    have hsep' : ∀ x ∈ triadicCube 2 m k, ∀ y ∈ e.val,
        (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| :=
      fun x hx => hsep x (triadicCube_subset_cubeAt m k hx)
    have hm := (hspatial m k e r hr i n hn hsep').2
    have hsqrt : Real.sqrt (B * Real.exp (-(b * Real.sqrt n))) =
        Real.sqrt B * Real.exp (-c * Real.sqrt n) := by
      rw [Real.sqrt_mul hB.le, ← Real.exp_half]
      congr 1
      dsimp [c]
      ring
    rw [hsqrt] at hm
    have hfactor : Real.sqrt T * Real.sqrt B ≤ K := by
      have h1 : Real.sqrt T ≤ M := le_max_right _ _
      have h2 : Real.sqrt B ≤ 1 + Real.sqrt B := by linarith
      exact mul_le_mul h1 h2 (Real.sqrt_nonneg B) hM
    exact hm.trans (by
      calc
        _ = (Real.sqrt T * Real.sqrt B) * Real.exp (-c * Real.sqrt n) := by ring
        _ ≤ K * Real.exp (-c * Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le)
  obtain ⟨_, hfs, hsum⟩ := Rigidity.Percolation.summable_planar_bond_shells z R f K c hK hc hf
    hglobal hdecay
  refine ⟨fun e => (hmoment m k e r hr).1, hfs, hsum.trans ?_⟩
  change 36 * ((R : ℝ) + 1) ^ 2 * (M * (1 + Real.sqrt B)) *
    (1 + ∑' n, q n) ≤ D * ((R : ℝ) + 1) ^ 2 * M
  dsimp only [D]
  exact le_of_eq (by ring)

end Rigidity.Proofs.S2
