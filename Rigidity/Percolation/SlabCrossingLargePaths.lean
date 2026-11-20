import Rigidity.Percolation.SlabLongPathEscape
import Rigidity.Percolation.CrossingPathCoalescence

/-!
# Slab bounds for crossing components and large paths

Cube crossing and long-path attachment estimates combine to bound the failure
of a crossing component that connects every path of a prescribed diameter.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Failure of the crossing-and-connection event implies either that no
crossing component exists or that a selected path misses one. -/
theorem not_crossingComponentConnectingPaths_imp {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop} :
    ¬ HasCrossingComponentConnectingPaths ω B lower upper large →
      (¬ ∃ root, IsCrossingRoot ω B lower upper root) ∨
      ∃ root, IsCrossingRoot ω B lower upper root ∧
        ∃ n γ, IsSelectedOpenPath ω B large n γ ∧
          ¬ (openIn ω B).Reachable root (γ 0) := by
  classical
  intro hfail
  by_cases hroot : ∃ root, IsCrossingRoot ω B lower upper root
  · obtain ⟨root, hr⟩ := hroot
    right
    refine ⟨root, hr, ?_⟩
    by_contra hpaths
    apply hfail
    refine ⟨root, hr, ?_⟩
    intro n γ hlarge hstart hadj
    have hconn : (openIn ω B).Reachable root (γ 0) := by
      by_contra hnot
      exact hpaths ⟨n, γ, ⟨hlarge, hstart, hadj⟩, hnot⟩
    exact ⟨γ 0, hstart, SimpleGraph.Reachable.refl _, hconn⟩
  · exact Or.inl hroot

/-- Uniform two-point connectivity in full slabs bounds the failure of a
cube-crossing component that connects every path of the stated diameter. -/
theorem IntegerCube.measureReal_no_crossing_connecting_paths_le_of_twoPoint_slabs {d : ℕ}
    (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j) (width k₀ N : ℕ)
    (hwidth : 0 < width) (hstart : 0 < k₀ * width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hprob : ∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (pathDiameterAtLeast (((N + 1) * width : ℕ) : ℤ))} ≤
      ((1 - ρ) ^ (Q.size / width) +
        ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N) +
      ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) := by
  let F : Set (Configuration d) := {ω | ¬ ∃ z,
    IsCrossingRoot ω Q.vertices (fun t => ↑(Q.lowerFace t))
      (fun t => ↑(Q.upperFace t)) z}
  let G : Set (Configuration d) := {ω | ∃ root,
    IsCrossingRoot ω Q.vertices (fun t => ↑(Q.lowerFace t))
      (fun t => ↑(Q.upperFace t)) root ∧
    ∃ n γ, IsSelectedOpenPath ω Q.vertices
      (pathDiameterAtLeast (((N + 1) * width : ℕ) : ℤ)) n γ ∧
      ¬ (openIn ω Q.vertices).Reachable root (γ 0)}
  have hcover : {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (pathDiameterAtLeast (((N + 1) * width : ℕ) : ℤ))} ⊆ F ∪ G := by
    intro ω hω
    exact not_crossingComponentConnectingPaths_imp hω
  have hparallel : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y} := by
    intro n hn
    apply hprob j (k₀ + n)
    have hnle : k₀ + n + 1 ≤ k₀ + N := by omega
    exact (Nat.mul_le_mul_right width hnle).trans (Nat.le_of_lt (hsize N le_rfl))
  have hperp : ∀ k : Fin (Q.size / width), ∀ x ∈ Q.slab i width k,
      ∀ y ∈ Q.slab i width k, ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab i width k)).Reachable x y} := by
    intro k
    apply hprob i k
    apply (Nat.le_div_iff_mul_le hwidth).mp
    exact k.isLt
  calc
    _ ≤ (latticeBondLaw d p).real (F ∪ G) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ (latticeBondLaw d p).real F + (latticeBondLaw d p).real G := measureReal_union_le _ _
    _ ≤ _ := add_le_add
      (Q.measureReal_no_crossing_le_of_twoPoint_slabs j i hij width width k₀ N hwidth hwidth
        hstart hsize p ρ hρ hρ₁ hparallel hperp)
      (Q.measureReal_disconnected_large_path_le_of_twoPoint_slabs width N hwidth p ρ hρ₁ hprob)

end Rigidity.Percolation
