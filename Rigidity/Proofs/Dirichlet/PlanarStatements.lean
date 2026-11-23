import Rigidity.Proofs.Dirichlet.PropSixOne
import Rigidity.Proofs.Cluster.PlanarCoarseData
import Rigidity.Proofs.Percolation.PlanarNuQuadratic
import Rigidity.External.CorrectorQuantitative

/-!
# Theorem 1 of Armstrong and Dario in dimension two, and its two inputs on the cluster

This file states, as definitions of propositions, the quantitative homogenization of the Dirichlet
problem on the planar cluster (S. Armstrong and P. Dario, *Elliptic regularity and quantitative
homogenization on percolation clusters*, Comm. Pure Appl. Math. 71 (2018), Theorem 1) and the two
inputs on the cluster from which it is derived in Section 6 of the source.

* `PlanarMinimalScales p`: the minimal scales of the planar partition (Proposition 2.4 of the
  source, the two bounds of (2.12)): for every `t ≥ 1` a random scale `𝓜_t ≤ O_s(C)` such that
  `3^m ≥ 𝓜_t` implies `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
  `size(□_𝒫(x)) ≤ 3^{2m/(2+t)}` for every `x ∈ □_m`.
* `PlanarMesoscopicConvergence p`: the convergence of `μ` and `ν` on the mesoscopic cubes of the
  proofs of Lemmas 6.2 and 6.3 above a random scale `𝒩 ≤ O_s(C)` (Definition 5.12, Proposition 5.13
  and (6.10)–(6.11) of the source), on the cubes `z + □_k`, `z ∈ 3^k ℤ²`, `k = ⌈m/8⌉`, contained in
  `□_m`. These cubes are triadic.
* `PlanarHomogenizationError p p'`: Theorem 1 for the exponent `p' > 2`, with the discrete
  homogenized solution: `ā = σ I` and, for `3^m ≥ 𝒳` and every `u` harmonic on `C_*(□_m)` off the
  boundary of `□_m`, a discrete harmonic function `u_hom` on the lattice cube `□_m` equal to `u` on
  `C_*(□_m) ∩ ∂□_m` with `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²` and
  `3^{-m} (|□_m|⁻¹ Σ_{C_*(□_m)} |u − u_hom|²)^{1/2} ≤ C 3^{-mα} M`,
  `M = (|□_m|⁻¹ Σ_{C_*(□_m)} |∇u 1_{a≠0}|^{p'})^{1/p'}`.

The source states the bound on the gradient of `u_hom` as
`⨍ |∇u_hom|² ≤ |□_m|⁻¹ Σ |∇u 1_{a≠0}|^p`, which is not homogeneous in `u`; the statement here is
the homogeneous form `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²` that the proof gives (Lemma 6.4 (iii) and the
Dirichlet principle).
-/

open MeasureTheory LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Matrix

namespace Rigidity.Dirichlet

/-- The normalized `L^{p'}` norm `M = (|□_m|⁻¹ Σ_{x ∈ C_*(□_m)} |∇u 1_{a≠0}|^{p'}(x))^{1/p'}` of the
open gradient of `u` on the cluster of `□_m`. -/
noncomputable def planarGradNorm (ω : Configuration 2) (m : ℕ) (p' : ℝ) (u : Vertex 2 → ℝ) : ℝ :=
  ((∑ x ∈ clusterVertices ω ⟨m, 0⟩,
      gradNormIn (openGraph ω) (clusterVertices ω ⟨m, 0⟩) u x ^ p') / 9 ^ m) ^ (1 / p')

/-- **Minimal scales of the planar partition** (Armstrong and Dario, Proposition 2.4, both bounds
of (2.12), for the planar partition): for every `t ≥ 1` there is a random scale `𝓜_t ≤ O_s(C)`
such that `3^m ≥ 𝓜_t` implies `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
`size(□_𝒫(x)) ≤ 3^{2m/(2+t)}` for `x ∈ □_m`. -/
def PlanarMinimalScales (p : unitInterval) : Prop :=
  ∀ t : ℝ, 1 ≤ t → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, M ω ≤ 3 ^ m →
        (∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
            ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t) / 9 ^ m ≤ C ∧
          ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
            (3 : ℝ) ^ (planarPartCube ω x).scale ≤ (3 : ℝ) ^ (2 * (m : ℝ) / (2 + t))

/-- **Convergence of `μ` and `ν` on the mesoscopic cubes** (Armstrong and Dario, Definition 5.12,
Proposition 5.13 and (6.10)–(6.11), on the triadic cubes `z + □_k`, `z ∈ 3^k ℤ²`, `k = ⌈m/8⌉`,
contained in `□_m`): there is a random scale `𝒩 ≤ O_s(C)` such that for `3^m ≥ 𝒩`, every such
cube `T` and all `q, ξ`,
`|μ(T, q) + (1/2) q · ā⁻¹ q| ≤ C |q|² 3^{-mα}` and `|ν(T, ξ) − (1/2) ξ · ā ξ| ≤ C |ξ|² 3^{-mα}`. -/
def PlanarMesoscopicConvergence (p : unitInterval) : Prop :=
  ∃ s α C : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧
    ∃ N : Configuration 2 → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond 2 p N s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, N ω ≤ 3 ^ m →
        ∀ T : TriadicCube 2, T.scale = (m + 7) / 8 →
          T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices → ∀ q ξ : Fin 2 → ℝ,
            |planarMu ω T q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
                C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(α * m)) ∧
              |planarNu ω T ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
                C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(α * m))

/-- **Armstrong and Dario, Theorem 1, in dimension two, with the discrete homogenized solution**,
for the exponent `p' > 2`: `ā = σ I` with `σ > 0`, and there are `s, α, C > 0` and a random scale
`𝒳 ≤ O_s(C)` such that for `3^m ≥ 𝒳` the partition event holds, `□_m` is resolved and, for every
`u` harmonic on `C_*(□_m)` off `∂□_m`, there is a discrete harmonic `u_hom` on the lattice cube
`□_m` with `u_hom = u` on `C_*(□_m) ∩ ∂□_m`, `|□_m|⁻¹ Σ_{edges in □_m} |∇u_hom|² ≤ C M²` and
`3^{-m} (|□_m|⁻¹ Σ_{C_*(□_m)} (u − u_hom)²)^{1/2} ≤ C 3^{-mα} M`, where `M = planarGradNorm`. -/
def PlanarHomogenizationError (p : unitInterval) (p' : ℝ) : Prop :=
  ∃ s α C σ : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧ 0 < σ ∧
    planarAhom p = σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, X ω ≤ 3 ^ m →
        PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ ∧
          ∀ u : Vertex 2 → ℝ,
            (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩ →
            ∃ uHom : Vertex 2 → ℝ,
              (∀ x ∈ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube,
                condLaplacian (constCond fun _ => (1 : ℝ)) uHom x = 0) ∧
              (∀ x ∈ clusterVertices ω ⟨m, 0⟩,
                x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube → uHom x = u x) ∧
              innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
                  uHom / 9 ^ m ≤ C * planarGradNorm ω m p' u ^ 2 ∧
              (3 : ℝ) ^ (-(m : ℝ)) *
                  √((∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - uHom x) ^ 2) / 9 ^ m) ≤
                C * (3 : ℝ) ^ (-(α * m)) * planarGradNorm ω m p' u

end Rigidity.Dirichlet
