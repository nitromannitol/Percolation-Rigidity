import PercolationClusterHomogenization.Percolation.SelectedPathSegment
import PercolationClusterHomogenization.Percolation.CrossingPathCoalescence

/-!
# Simple paths with large diameter

Large-diameter open walks contain connected endpoints joined by a simple open
path with the same coordinate displacement.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A crossing component that connects every simple path with well-separated
endpoints also connects every open walk of the same coordinate diameter. -/
theorem HasCrossingComponentConnectingPaths.of_simple_paths {d : ℕ}
    {ω : Configuration d} {B : Set (Vertex d)}
    {lower upper : Fin d → Set (Vertex d)} {root : Vertex d} (r : ℤ)
    (hroot : IsCrossingRoot ω B lower upper root)
    (hsimple : ∀ x y, ∀ walk : (openIn ω B).Walk x y, walk.IsPath →
      (∃ k : Fin d, r ≤ |x k - y k|) → (openIn ω B).Reachable root x) :
    HasCrossingComponentConnectingPaths ω B lower upper (pathDiameterAtLeast r) := by
  refine ⟨root, hroot, ?_⟩
  intro n γ hdiam hstart hadj
  let hγ : IsSelectedOpenPath ω B (pathDiameterAtLeast r) n γ :=
    ⟨hdiam, hstart, hadj⟩
  obtain ⟨i, j, k, hk⟩ := hdiam
  have hij := (hγ.reachable_start i).symm.trans (hγ.reachable_start j)
  obtain ⟨walk, hwalk⟩ := hij.exists_isPath
  have hrooti := hsimple (γ i) (γ j) walk hwalk ⟨k, hk⟩
  exact ⟨γ 0, hstart, SimpleGraph.Reachable.refl _,
    hrooti.trans (hγ.reachable_start i).symm⟩

end Rigidity.Percolation
