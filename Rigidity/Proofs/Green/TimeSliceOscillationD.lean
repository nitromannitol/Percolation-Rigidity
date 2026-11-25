import Rigidity.Proofs.Green.EllipticSliceEstimate
import Rigidity.Proofs.Green.HeatFlowGraph
import Rigidity.Proofs.WeakPoincare.Balls
import LatticeProb.Prob.Percolation.LatticeOrderZeroTranslation
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds

/-!
# The oscillation of the time slices of the heat semigroup on the cluster of `ℤ^d`

* `exists_orderZero_clusterBallD`: the order-zero regularity of Armstrong and Dario (Theorem 2 (iii)
  at `k = 0`, proved in Percolation-Cluster-Homogenization) at every centre of `ℤ^d`, on the balls
  `𝒞_∞ ∩ B_r(z)` (`Rigidity.WeakPoincare.clusterBall`) and for functions on the lattice that are
  harmonic for the open graph at the vertices of `interiorOf`;
* `exists_nL2_heatFlowG_sub_le`: for a square summable `φ` and `σ > 0`, the time slice
  `v = P_σ φ` of the heat semigroup of the open graph has
  `‖v - c‖_{L̲²(𝒞_∞ ∩ B_l(y))} ≤ K l (U/R + R F)` with `U² = A₁ ‖φ‖²`, `F² = 8 (2σ)^{-2} A₂ ‖φ‖²`, where
  `A₁` and `A₂` bound `p_{2σ}(z, z)` and `p_{σ/2}(z, z)` on `B_R(y)`: the elliptic oscillation
  estimate with the bounds of `HeatFlowGraph.lean`. With `σ ≈ t`, `R ≈ √t` and the diagonal bound
  `p_s(z, z) ≤ C s^{-d/2}` of Theorem 4 this is `‖P_σ φ - c‖_{L̲²(B_l)} ≤ C l t^{-d/4 - 1/2} ‖φ‖`.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ} {ω : Configuration d}

open Rigidity.WeakPoincare in
theorem clusterBallD_eq_map (K : OpenComponent ω) (z : Vertex d) (r : ℝ) :
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

theorem componentBallL2_eq_nL2D (K : OpenComponent ω) (z : Vertex d) (r : ℝ) {g : K → ℝ}
    {f : Vertex d → ℝ} (hgf : ∀ x, g x = f x.val) :
    componentBallL2 K z r g = nL2 (Rigidity.WeakPoincare.clusterBall K z r) f := by
  simp only [componentBallL2, nL2, clusterBallD_eq_map, Finset.sum_map, Finset.card_map,
    Function.Embedding.coe_subtype, hgf]

open Rigidity.WeakPoincare in
/-- The order-zero estimate for functions on the cluster gives the estimate for functions on the
lattice, on the balls `clusterBall K z r` of `ℤ^d`. -/
theorem orderZero_nL2D {h : HasUniqueInfiniteOpenComponent ω} {z : Vertex d} {X C₀ : ℝ}
    (hOZ : ∀ R : ℝ, 2 * X ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R,
        (∀ y : uniqueInfiniteComponent h, (componentGraph (uniqueInfiniteComponent h)).Adj x y →
          y ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R) →
        componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 (uniqueInfiniteComponent h) z r (u - fun _ => c) ≤
          C₀ * (r / R) * componentBallL2 (uniqueInfiniteComponent h) z R u) :
    ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
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
  rw [componentBallL2_eq_nL2D K z r (g := (fun x : K => u x.val) - fun _ => c)
      (f := fun v => u v - c) (fun x => rfl),
    componentBallL2_eq_nL2D K z R' (g := fun x : K => u x.val) (f := u) (fun x => rfl)] at h1
  exact h1

open Rigidity.WeakPoincare in
/-- **The order-zero estimate of Armstrong and Dario at every centre of `ℤ^d`**, on the balls
`𝒞_∞ ∩ B_r(z)`, with a minimal scale `X(z) ≤ O_s(θ)`. -/
theorem exists_orderZero_clusterBallD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s θ C₀ : ℝ, 0 < s ∧ 0 < θ ∧ 0 < C₀ ∧ ∃ X : Vertex d → Configuration d → ℝ,
      (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
      (∀ z, Rigidity.External.IsOsBond d p (X z) s θ) ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ z : Vertex d,
        ∀ R', 2 * X z ω ≤ R' → ∀ u : Vertex d → ℝ,
          (∀ x ∈ interiorOf (openGraph ω) (clusterBall (uniqueInfiniteComponent h) z R'),
            LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
          ∃ c : ℝ, ∀ r, X z ω ≤ r → r ≤ R' / 2 →
            nL2 (clusterBall (uniqueInfiniteComponent h) z r) (fun x => u x - c) ≤
              C₀ * (r / R') * nL2 (clusterBall (uniqueInfiniteComponent h) z R') u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hX0, hXi, hXb, hae⟩ :=
    exists_all_centers_constant_approximation
      Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds d hd p hpc hp1
  refine ⟨s, θ, C, hs, hθ, hC, X, hXm, hX0, fun z => ?_, ?_⟩
  · have e : (fun ω => Real.exp (Real.rpow (max (X z ω / θ) 0) s)) =
        fun ω => Real.exp (Real.rpow (X z ω / θ) s) :=
      funext fun ω => by rw [max_eq_left (div_nonneg (hX0 z ω) hθ.le)]
    exact ⟨by rw [e]; exact hXi z, by rw [e]; exact hXb z⟩
  · filter_upwards [hae] with ω hω
    obtain ⟨_, hω⟩ := hω
    intro h z
    exact orderZero_nL2D (hω h z)

open Rigidity.WeakPoincare in
/-- **The oscillation of a time slice of the heat semigroup** on the balls of the cluster of
`ℤ^d`. -/
theorem exists_nL2_heatFlowG_sub_le [NeZero d] {K : OpenComponent ω} {y : Vertex d}
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {σ : ℝ} (hσ : 0 < σ) {φ : Vertex d → ℝ} (hφ : Summable fun w => φ w ^ 2)
    {r R A₁ A₂ : ℝ} (hXr : X ≤ r) (hr : 0 < r) (hρ₀ : ρ₀ ≤ 2 * r) (hrR : 2 * r ≤ R)
    (hdiag1 : ∀ z ∈ clusterBall K y R, vsrwHeat (openGraph ω) (2 * d) (σ + σ) z z ≤ A₁)
    (hdiag2 : ∀ z ∈ clusterBall K y R, vsrwHeat (openGraph ω) (2 * d) ((σ + σ) / 4) z z ≤ A₂) :
    ∃ c : ℝ, nL2 (clusterBall K y r) (fun x => heatFlowG (openGraph ω) (2 * d) σ φ x - c) ≤
      (C₀ + (10 * C₀ + 32) * A) * r *
        (Real.sqrt (A₁ * ∑' w, φ w ^ 2) / R +
          R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂ * ∑' w, φ w ^ 2)) := by
  have hD : 0 < 2 * d := by have := NeZero.pos d; omega
  have hdeg : ∀ z, (openGraph ω).degree z ≤ 2 * d := openGraph_degree_le ω
  have hS : 0 ≤ ∑' w, φ w ^ 2 := tsum_nonneg fun w => sq_nonneg _
  refine exists_nL2_sub_le_of_laplacian (G := openGraph ω) (D := 2 * d) hD hdeg
    (B := clusterBall K y) (fun ρ ρ' h => clusterBall_mono h) hacc hC₀ hOZ hA hHK hXr hr hρ₀ hrR
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (fun z hz => ?_) (fun z hz => ?_)
  · rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact (sq_heatFlowG_le_diag hD hdeg hσ.le hφ z).trans
      (mul_le_mul_of_nonneg_right (hdiag1 z hz) hS)
  · rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    refine (sq_laplacian_heatFlowG_le hD hdeg hσ hφ z).trans ?_
    have hz' := interiorOf_subset _ hz
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdiag2 z hz') (by positivity)) hS

end Rigidity.Green
