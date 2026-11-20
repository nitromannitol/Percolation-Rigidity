import Rigidity.Percolation.SlabTransverseCrossing
import Rigidity.Percolation.SelectedPathSegment

/-!
# Paths escaping past a crossing component

A path separated from a cube-crossing component, with one vertex in an early
prefix and one beyond a later prefix, gives two disconnected components that
escape through the same sequence of slabs.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A crossing component and a disconnected path spanning two prefixes yield
two disconnected roots that both escape the later prefix. -/
theorem IntegerCube.two_escapes_of_disconnected_path {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k₀ N : ℕ} (hstart : 0 < k₀ * width)
    (hend : (k₀ + N) * width < Q.size) {ω : Configuration d}
    {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
      (fun i => ↑(Q.upperFace i)) root)
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω Q.vertices large n γ)
    {a b : Fin (n + 1)} (ha : γ a ∈ Q.slabPrefix j width k₀)
    (hb : γ b ∉ Q.slabPrefix j width (k₀ + N))
    (hsep : ¬ (openIn ω Q.vertices).Reachable root (γ 0)) :
    ∃ z ∈ Q.slabPrefix j width k₀, ∃ z' ∈ Q.slabPrefix j width k₀,
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z' ω ∧
      ¬ (openIn ω Q.vertices).Reachable z z' := by
  obtain ⟨hL, hR⟩ := Q.faces_separated_by_prefixes j hstart hend
  obtain ⟨⟨u, huQ, huL, hru⟩, ⟨v, hvQ, hvR, hrv⟩⟩ := hroot.2 j
  refine ⟨u, hL huL, γ a, ha,
    ⟨v, hvQ, hR hvR, hru.symm.trans hrv⟩,
    ⟨γ b, hγ.mem_region b, ⟨hγ.mem_region b, hb⟩,
      (hγ.reachable_start a).symm.trans (hγ.reachable_start b)⟩, ?_⟩
  intro hconn
  exact hsep (hru.trans (hconn.trans (hγ.reachable_start a).symm))

open Classical in
/-- The probability of a path spanning two prefixes while disconnected from a
crossing component is bounded by the two-component slab survival estimate. -/
theorem IntegerCube.measureReal_disconnected_path_spanning_prefixes_le {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hstart : 0 < k₀ * width) (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (p : unitInterval) (ρ : ℝ) (hρ : ρ ≤ 1)
    (hprob : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        (∃ a, γ a ∈ Q.slabPrefix j width k₀) ∧
        (∃ b, γ b ∉ Q.slabPrefix j width (k₀ + N)) ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ≤
      ((Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k₀).card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N := by
  classical
  let A := Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k₀
  have hA : (↑A : Set (Vertex d)) ⊆ Q.slabPrefix j width k₀ := fun x hx =>
    (Finset.mem_filter.mp hx).2
  have hcover : {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        (∃ a, γ a ∈ Q.slabPrefix j width k₀) ∧
        (∃ b, γ b ∉ Q.slabPrefix j width (k₀ + N)) ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ⊆ {ω | ∃ z ∈ A, ∃ z' ∈ A,
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z' ω ∧
      ¬ (openIn ω Q.vertices).Reachable z z'} := by
    rintro ω ⟨root, hroot, n, γ, hγ, ⟨a, ha⟩, ⟨b, hb⟩, hsep⟩
    obtain ⟨z, hz, z', hz', h₁, h₂, h₃⟩ :=
      Q.two_escapes_of_disconnected_path j hstart (hsize N le_rfl) hroot hγ ha hb hsep
    exact ⟨z, Finset.mem_filter.mpr ⟨hz.1, hz⟩, z',
      Finset.mem_filter.mpr ⟨hz'.1, hz'⟩, h₁, h₂, h₃⟩
  apply (measureReal_mono hcover (measure_ne_top _ _)).trans
  exact Q.measureReal_exists_two_escapes_le j width k₀ N hwidth hsize A hA p ρ hρ hprob

end Rigidity.Percolation
