import Rigidity.Proofs.Cluster.ReverseHolder
import Rigidity.Proofs.Cluster.GehringCubes

/-!
# The reverse Hölder inequality on triadic cubes

Armstrong–Dario, Lemma 3.6, for the cubes `□_m = cube m x₀` and `□_{m+1} = 3□_m = enl 1 m x₀`. If
`U ⊆ 3□_m` contains every point of `3□_m` joined by an open edge to a point of `U` (as the cluster
`𝒞_*(□_{m+1})` does), then every point of `U` with an open edge leaving `U` lies at sup-norm distance
at least `3^m` from `□_m` (`le_supDist_of_exit`), so `reverse_holder_of_sobolev` applies with
`r = 3^m`, `N = |□_{m+1}| = 3^{(m+1)d}`, `N' = |□_m| = 3^{md}` and `K = 3^{d+2}`
(`reverse_holder_triadic`). For `s = d + 2` the exponents are those of the partition `𝓡` of
Definition 3.7: `s' 2_* = 2d/(d+1)` (`reverse_holder_exponents`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators

variable {d : ℕ}

/-- **Distance to the exit points.** If `U` contains every point of `3□_m` joined by an open edge to
a point of `U`, every point of `U` with an open edge leaving `U` is at sup-norm distance at least `3^m`
from every point of `□_m`. -/
theorem le_supDist_of_exit (ω : Configuration d) {m : ℕ} {x₀ : Vertex d} {U : Finset (Vertex d)}
    (hclosed : ∀ z ∈ U, ∀ y, (openGraph ω).Adj z y → y ∈ enl 1 m x₀ → y ∈ U)
    {x z : Vertex d} (hx : x ∈ cube m x₀) (hz : z ∈ U)
    (hexit : ∃ y, (openGraph ω).Adj z y ∧ y ∉ U) : (3 : ℝ) ^ m ≤ supDist x z := by
  obtain ⟨y, hadj, hyU⟩ := hexit
  have hyΩ : y ∉ enl 1 m x₀ := fun h => hyU (hclosed z hz y hadj h)
  rw [enl, mem_box] at hyΩ
  simp only [not_forall, not_le] at hyΩ
  obtain ⟨i, hi⟩ := hyΩ
  rw [cube, mem_box] at hx
  have h1 := abs_sub_le_one_of_openGraph_adj hadj i
  have h2 := hx i
  have h3 : halfSide (m + 1) = 3 * halfSide m + 1 := rfl
  have h4 := two_mul_halfSide_add_one m
  have h5 : (3 : ℤ) ^ m ≤ |x i - z i| := by
    have e1 := abs_sub_le (y i) (z i) (center m x₀ i)
    have e2 := abs_sub_le (z i) (x i) (center m x₀ i)
    rw [abs_sub_comm (y i) (z i)] at e1
    rw [abs_sub_comm (z i) (x i)] at e2
    linarith
  have h6 : (3 : ℤ) ^ m ≤ ((x i - z i).natAbs : ℤ) := by rwa [Int.natCast_natAbs]
  have h7 : 3 ^ m ≤ (x i - z i).natAbs := by exact_mod_cast h6
  have h8 : 3 ^ m ≤ supDist x z := h7.trans (natAbs_le_supDist x z i)
  exact_mod_cast h8

/-- **Reverse Hölder inequality on triadic cubes** (Armstrong–Dario, Lemma 3.6, deterministic part).
Let `U ⊆ 3□_m` contain every point of `3□_m` joined by an open edge to a point of `U`, `V ⊆ U ∩ □_m`,
assume the Sobolev inequality `ClusterSobolevTwo ω U size C_S`, the moment bound
`∑_{x ∈ U} size(x)^{2ds} ≤ C_G |□_{m+1}|` with `s`, `t` Hölder conjugate, and let `u` be harmonic for
the open edges at the points of `U` whose open edges stay in `U`. Then
`|□_m|⁻¹ ∑_V |∇u|² ≤ 8d C_S C_G^{2/(s 2_*)} 3^{d+2} (|□_{m+1}|⁻¹ ∑_U |∇u|^{t 2_*})^{2/(t 2_*)}`. -/
theorem reverse_holder_triadic (ω : Configuration d) (hd : 0 < d) (m : ℕ) (x₀ : Vertex d)
    (U V : Finset (Vertex d)) (hVU : V ⊆ U) (hV : V ⊆ cube m x₀)
    (hclosed : ∀ z ∈ U, ∀ y, (openGraph ω).Adj z y → y ∈ enl 1 m x₀ → y ∈ U)
    (size : Vertex d → ℝ) (hsize : ∀ x, 0 ≤ size x) {CS CG s t : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG)
    (hst : s.HolderConjugate t) (hSob : ClusterSobolevTwo ω U size CS)
    (hgood : ∑ x ∈ U, size x ^ (2 * (d : ℝ) * s) ≤ CG * (3 : ℝ) ^ ((m + 1) * d))
    (u : Vertex d → ℝ)
    (hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) → openLaplacian ω u x = 0) :
    (1 / (3 : ℝ) ^ (m * d)) * ∑ x ∈ V, clusterGradSq ω U u x ≤
      8 * d * CS * CG ^ (2 / (s * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
        ((1 / (3 : ℝ) ^ ((m + 1) * d)) *
          ∑ x ∈ U, clusterGradSq ω U u x ^ (t * lowerSobolevTwo d / 2)) ^
            (2 / (t * lowerSobolevTwo d)) := by
  refine reverse_holder_of_sobolev ω hd U V hVU (r := (3 : ℝ) ^ m) (by positivity)
    (fun x hx z hz hexit => le_supDist_of_exit ω hclosed (hV hx) hz hexit) size hsize hCS hCG hst
    (by positivity) (by positivity) hSob hgood ?_ u hu
  rw [triadic_volume_relation hd m]

/-- For `s = d + 2` and its conjugate `t = (d+2)/(d+1)`, `t 2_*/2 = d/(d+1)` and
`2/(t 2_*) = (d+1)/d`: the exponent `s' 2_* = 2d/(d+1)` of the partition `𝓡` of Armstrong–Dario,
Definition 3.7. -/
theorem reverse_holder_exponents (hd : 0 < d) :
    ((d : ℝ) + 2).HolderConjugate (((d : ℝ) + 2) / (d + 1)) ∧
      ((d : ℝ) + 2) / (d + 1) * lowerSobolevTwo d / 2 = (d : ℝ) / (d + 1) ∧
      2 / (((d : ℝ) + 2) / (d + 1) * lowerSobolevTwo d) = ((d : ℝ) + 1) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (d : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (d : ℝ) ≠ 0 := hd'.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    rw [inv_div]
    field_simp
    ring
  · unfold lowerSobolevTwo
    field_simp
  · unfold lowerSobolevTwo
    field_simp

end Rigidity.Proofs.Cluster
