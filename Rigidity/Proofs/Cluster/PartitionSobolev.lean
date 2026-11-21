import Rigidity.Proofs.Cluster.CoarseSobolev
import Rigidity.Proofs.Cluster.PartitionCoarseData

/-!
# The Sobolev inequality on the cluster of a resolved cube

Armstrong and Dario, Proposition 3.4 (case `∑_{C_*(U)} w = 0`), for the partition into good cubes,
given the lattice Sobolev–Poincaré inequality on the triadic cube `U`: for `1 ≤ t ≤ s` there is
`K(d, s, t, S)` with
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ K (∑_{z ∈ C_*(U)} (3^{ρ(z)})^{td} |∇w 1_{a≠0}|^t(z))^{s/t}`
for every cube `U` resolved by the partition and every `w` of mean zero on `C_*(U)`, where `ρ(z)`
is the reach scale of the coarse-graining data. Armstrong and Dario state the weight
`size(□_𝒫(z))^{sd}`; the reach scale replaces the scale of the partition cube as in Lemma 3.2, and
`td ≤ sd`.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 3.4, for the partition into good cubes**, given the lattice
Sobolev–Poincaré inequality on the resolved cube (case `∑_{C_*(U)} w = 0`). -/
theorem exists_partition_sum_rpow_le_of_latticeSobolevOn (hd : 0 < d) {s t S : ℝ} (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hts : t ≤ s) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U), LatticeSobolevOn U.toIntegerCube.vertices s t S →
      ∀ w : Vertex d → ℝ, ∑ x ∈ crossingClusterVertices ω U, w x = 0 →
        ∑ x ∈ crossingClusterVertices ω U, |w x| ^ s ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData hd hP U hU).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t) := by
  set C₂ : ℝ := 3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d *
    (2 * √(d : ℝ)) with hC₂
  set C₃ : ℝ := 2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) *
    (2 * √(d : ℝ)) with hC₃
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  have hst : 0 ≤ s / t := by positivity
  have hsne : s ≠ 0 := (show (0 : ℝ) < s by linarith).ne'
  refine ⟨2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
    (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) * 2 ^ (s / t), by positivity, ?_⟩
  intro ω hP U hU hLS w hw
  set P := partitionCoarseData hd hP U hU with hPdef
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  have h32 := partition_sum_abs_sub_coarseAnchor_rpow_le hd hP hU w hs
  have h33 := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hU w ht
  have hmain := P.sum_rpow_le_of_latticeSobolevOn hs ht hts (Real.rpow_nonneg hC₂0 s)
    (Real.rpow_nonneg hC₃0 t) hS (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * d))
    (b := fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    hLS w h32 h33 hw
  refine hmain.trans ?_
  have hweight : ∀ z ∈ crossingClusterVertices ω U,
      (((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) +
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1) ≤
      2 * ((3 : ℝ) ^ P.reachScale z) ^ (t * d) := by
    intro z hz
    have h1 : (((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) =
        ((3 : ℝ) ^ P.reachScale z) ^ (t * d) := by
      rw [← Real.rpow_mul (x := (3 : ℝ) ^ P.reachScale z) (by positivity)]
      congr 1
      field_simp
    have hn : (partitionCube ω z).scale ≤ P.reachScale z := P.scale_le_reachScale_self hz
    have h2 : ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1) ≤
        ((3 : ℝ) ^ P.reachScale z) ^ (t * d) := by
      have htd : 0 ≤ t * d := by positivity
      calc ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1)
          ≤ ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
        _ ≤ ((3 : ℝ) ^ P.reachScale z) ^ (t * d) :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) hn) htd
    rw [h1]
    linarith
  have hsum : ∑ z ∈ crossingClusterVertices ω U,
      ((((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) +
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1)) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t ≤
      2 * ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hweight z hz) (Real.rpow_nonneg (hg0 z) _)
  have hX0 : 0 ≤ ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
      gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t :=
    Finset.sum_nonneg fun z _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (hg0 z) _)
  have hW0 : 0 ≤ ∑ z ∈ crossingClusterVertices ω U,
      ((((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) +
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1)) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t :=
    Finset.sum_nonneg fun z _ => mul_nonneg (add_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (hg0 z) _)
  have hpow := Real.rpow_le_rpow hW0 hsum hst
  rw [Real.mul_rpow (x := (2 : ℝ)) (by norm_num) hX0] at hpow
  have hK0 : 0 ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
      (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) := by positivity
  calc _ ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
        (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) *
        (2 ^ (s / t) * (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t)) :=
        mul_le_mul_of_nonneg_left hpow hK0
    _ = _ := by ring

end Rigidity.Percolation
