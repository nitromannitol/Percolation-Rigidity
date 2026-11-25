import Rigidity.Proofs.WeakPoincare.VeryGood
import Rigidity.Proofs.Green.DarioGuApproxInputs

/-!
# Very good balls of the planar infinite cluster with the planar objects

The case `d = 2` of `clusterVeryGoodBalls_holds` (Barlow 2004, Theorem 2.18 (c) with Lemma 2.19,
Euclidean balls), written with the planar distance, balls and averages of `Rigidity.Green`
(`Rigidity.Green.latticeDist`, `Rigidity.Green.clusterBall`, `Rigidity.Green.finAvg`), for
`θ ∈ (0, 1]` and centres `|z - y| ≤ R`, with the good ball written out: the volume bound
`CV r² ≤ |K ∩ B_r(z)|` and the weak Poincaré inequality with the Dirichlet energy
`Σ_{x ∈ U} Σ_{z ∈ U, z ∼ x} (u(z) - u(x))²` over the open edges inside `U = K ∩ B_{Lr}(z)`
(`planarVeryGoodBalls_holds`). This is the form of the very good balls used by the proof of the
Gaussian upper bound of Barlow in dimension two.
-/

open scoped Classical
open MeasureTheory Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.WeakPoincare

theorem green_clusterBall_eq {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2)
    (r : ℝ) : Rigidity.Green.clusterBall K y r = clusterBall K y r := by
  ext x
  rw [Rigidity.Green.mem_clusterBall, mem_clusterBall]
  rfl

theorem nbrEnergy_eq_sum (ω : Configuration 2) (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) :
    nbrEnergy ω U u =
      ∑ x ∈ U, ∑ z ∈ U.filter (fun z => (openGraph ω).Adj x z), (u z - u x) ^ 2 := by
  unfold nbrEnergy
  congr

/-- **Very good balls of the planar infinite cluster**, with the planar objects of
`Rigidity.Green`: for `θ ∈ (0, 1]` there are constants and, for every `y`, a scale
`S(y) ≤ O_s(C)` such that almost surely, for `R ≥ S(y)`, every ball `𝒞_∞ ∩ B_r(z)` with
`|z - y| ≤ R` and `r ≥ R^θ` satisfies `CV r² ≤ |𝒞_∞ ∩ B_r(z)|` and the weak Poincaré inequality
with constant `CP` and the gradient on `𝒞_∞ ∩ B_{Lr}(z)`. -/
theorem planarVeryGoodBalls_holds :
    ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∃ CV CP L s C : ℝ, 0 < CV ∧ 0 < CP ∧ 1 ≤ L ∧ 0 < s ∧ 0 < C ∧
        ∀ y : Vertex 2, ∃ S : Configuration 2 → ℝ, Measurable S ∧ (∀ ω, 0 ≤ S ω) ∧
          IsOsBond 2 p S s C ∧ ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
            ∀ R : ℝ, S ω ≤ R → ∀ z : Vertex 2, Rigidity.Green.latticeDist z y ≤ R →
              ∀ r : ℝ, R ^ θ ≤ r →
                CV * r ^ 2 ≤ (Rigidity.Green.clusterBall (uniqueInfiniteComponent h) z r).card ∧
                ∀ u : Vertex 2 → ℝ,
                  ∑ x ∈ Rigidity.Green.clusterBall (uniqueInfiniteComponent h) z r,
                      (u x - Rigidity.Green.finAvg
                        (Rigidity.Green.clusterBall (uniqueInfiniteComponent h) z r) u) ^ 2 ≤
                    CP * r ^ 2 *
                      ∑ x ∈ Rigidity.Green.clusterBall (uniqueInfiniteComponent h) z (L * r),
                        ∑ z' ∈ (Rigidity.Green.clusterBall (uniqueInfiniteComponent h) z
                          (L * r)).filter (fun z' => (openGraph ω).Adj x z'),
                          (u z' - u x) ^ 2 := by
  intro p hpc hp1 θ hθ _
  obtain ⟨C, L, hC, hL, hvg⟩ := clusterVeryGoodBalls_holds (d := 2) le_rfl p hpc hp1
  obtain ⟨s, C', hs, hC', hy⟩ := hvg θ 1 hθ le_rfl
  refine ⟨C⁻¹, C, L, s, C', inv_pos.2 hC, hC, hL, hs, hC', fun y => ?_⟩
  obtain ⟨S, hSm, hS0, hSos, hSae⟩ := hy y
  refine ⟨S, hSm, hS0, hSos, ?_⟩
  filter_upwards [hSae] with ω hω
  intro h R hR z hz r hr
  obtain ⟨⟨hvol, hpo⟩, -⟩ := hω h R hR z (by rw [one_mul]; exact hz) r hr
  refine ⟨by rw [green_clusterBall_eq]; exact hvol, fun u => ?_⟩
  rw [green_clusterBall_eq, green_clusterBall_eq, ← nbrEnergy_eq_sum]
  exact hpo u

end Rigidity.WeakPoincare
