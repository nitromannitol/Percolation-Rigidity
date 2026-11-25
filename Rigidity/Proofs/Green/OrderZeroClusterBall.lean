import Rigidity.Proofs.Green.EllipticSliceEstimate
import Rigidity.Proofs.Green.DarioGuApproxInputs
import LatticeProb.Prob.Percolation.LatticeOrderZeroTranslation
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds

/-!
# The order-zero estimate on the balls `𝒞_∞ ∩ B_r(z)` of the plane

The order-zero regularity of Armstrong and Dario (Theorem 2 (iii) at `k = 0`, proved in
Percolation-Cluster-Homogenization, `armstrongDarioOrderZero_holds`), transported to every centre by
stationarity (Lattice-Probability, `exists_all_centers_constant_approximation`), in the form used by
the elliptic oscillation estimate `exists_nL2_sub_le_of_laplacian`: for the open graph, the balls
`clusterBall K z r = 𝒞_∞ ∩ B_r(z)` and functions on the whole lattice
(`exists_orderZero_clusterBall`). The transfer from functions on the vertex type of the cluster is
`orderZero_nL2`: the normalized norms agree (`componentBallL2_eq_nL2`) and harmonicity at the
interior vertices of the ball in the cluster is harmonicity for the open graph at the vertices of
`interiorOf`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

variable {ω : Configuration 2}

theorem clusterBall_eq_map (K : OpenComponent ω) (z : Vertex 2) (r : ℝ) :
    clusterBall K z r = (componentEuclideanBall K z r).map (Function.Embedding.subtype _) := by
  ext v
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_clusterBall]
  constructor
  · rintro ⟨hv, hd⟩
    exact ⟨⟨v, hv⟩, (mem_componentEuclideanBall K z r _).2 (by rw [dist_eq_norm]; exact hd), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have := (mem_componentEuclideanBall K z r x).1 hx
    rw [dist_eq_norm] at this
    exact ⟨x.2, this⟩

theorem componentBallL2_eq_nL2 (K : OpenComponent ω) (z : Vertex 2) (r : ℝ) {g : K → ℝ}
    {f : Vertex 2 → ℝ} (hgf : ∀ x, g x = f x.val) :
    componentBallL2 K z r g = nL2 (clusterBall K z r) f := by
  simp only [componentBallL2, nL2, clusterBall_eq_map, Finset.sum_map, Finset.card_map,
    Function.Embedding.coe_subtype, hgf]

/-- The order-zero estimate for functions on the cluster gives the estimate for functions on the
lattice that are harmonic for the open graph at the vertices of `interiorOf`. -/
theorem orderZero_nL2 {h : HasUniqueInfiniteOpenComponent ω} {z : Vertex 2} {X C₀ : ℝ}
    (hOZ : ∀ R : ℝ, 2 * X ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R,
        (∀ y : uniqueInfiniteComponent h, (componentGraph (uniqueInfiniteComponent h)).Adj x y →
          y ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R) →
        componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 (uniqueInfiniteComponent h) z r (u - fun _ => c) ≤
          C₀ * (r / R) * componentBallL2 (uniqueInfiniteComponent h) z R u) :
    ∀ R', 2 * X ≤ R' → ∀ u : Vertex 2 → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall (uniqueInfiniteComponent h) z R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall (uniqueInfiniteComponent h) z r) (fun x => u x - c) ≤
          C₀ * (r / R') * nL2 (clusterBall (uniqueInfiniteComponent h) z R') u := by
  intro R' hR' u hu
  set K := uniqueInfiniteComponent h with hK
  obtain ⟨c, hc⟩ := hOZ R' hR' (fun x => u x.val) (fun x hx hin => by
    rw [componentLaplacian_restrict_eq]
    apply hu
    rw [mem_interiorOf, mem_clusterBall]
    have hd := (mem_componentEuclideanBall K z R' x).1 hx
    rw [dist_eq_norm] at hd
    refine ⟨⟨x.2, hd⟩, fun w hw => ?_⟩
    have hwK : w ∈ K.supp := K.mem_supp_of_adj_mem_supp x.2 hw
    have hd' := (mem_componentEuclideanBall K z R' _).1 (hin ⟨w, hwK⟩ hw)
    rw [dist_eq_norm] at hd'
    exact mem_clusterBall.2 ⟨hwK, hd'⟩)
  refine ⟨c, fun r hr hrR => ?_⟩
  have h1 := hc r hr hrR
  rw [componentBallL2_eq_nL2 K z r (g := (fun x : K => u x.val) - fun _ => c)
      (f := fun v => u v - c) (fun x => rfl),
    componentBallL2_eq_nL2 K z R' (g := fun x : K => u x.val) (f := u) (fun x => rfl)] at h1
  exact h1

/-- **The order-zero estimate of Armstrong and Dario at every centre of the plane**, on the balls
`𝒞_∞ ∩ B_r(z)`, with a minimal scale `X(z) ≤ O_s(θ)`. -/
theorem exists_orderZero_clusterBall {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ s θ C₀ : ℝ, 0 < s ∧ 0 < θ ∧ 0 < C₀ ∧ ∃ X : Vertex 2 → Configuration 2 → ℝ,
      (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧ (∀ z, IsOsBond 2 p (X z) s θ) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ z : Vertex 2,
        ∀ R', 2 * X z ω ≤ R' → ∀ u : Vertex 2 → ℝ,
          (∀ x ∈ interiorOf (openGraph ω) (clusterBall (uniqueInfiniteComponent h) z R'),
            LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
          ∃ c : ℝ, ∀ r, X z ω ≤ r → r ≤ R' / 2 →
            nL2 (clusterBall (uniqueInfiniteComponent h) z r) (fun x => u x - c) ≤
              C₀ * (r / R') * nL2 (clusterBall (uniqueInfiniteComponent h) z R') u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hX0, hXi, hXb, hae⟩ :=
    exists_all_centers_constant_approximation
      Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds 2 le_rfl p hpc hp1
  refine ⟨s, θ, C, hs, hθ, hC, X, hXm, hX0, fun z => ?_, ?_⟩
  · have e : (fun ω => Real.exp (Real.rpow (max (X z ω / θ) 0) s)) =
        fun ω => Real.exp (Real.rpow (X z ω / θ) s) :=
      funext fun ω => by rw [max_eq_left (div_nonneg (hX0 z ω) hθ.le)]
    exact ⟨by rw [e]; exact hXi z, by rw [e]; exact hXb z⟩
  · filter_upwards [hae] with ω hω
    obtain ⟨_, hω⟩ := hω
    intro h z
    exact orderZero_nL2 (hω h z)

end Rigidity.Green
