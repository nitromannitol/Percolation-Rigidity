import Rigidity.Proofs.Cluster.SobolevCube
import Rigidity.Proofs.Cluster.PartitionSobolev

/-!
# The Sobolev inequality on the cluster of a resolved cube in every dimension

Armstrong and Dario, Proposition 3.4 (case `∑_{C_*(U)} w = 0`), for the partition into good cubes
in every dimension `d ≥ 2`, for `s > d/(d-1)` and `s_* = sd/(s+d)`: the lattice Sobolev–Poincaré
inequality on integer cubes discharges the lattice Sobolev input of the deduction from Lemmas 3.2
and 3.3. There is `K(d, s)` with
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ K (∑_{z ∈ C_*(U)} (3^{ρ(z)})^{s_* d} |∇w 1_{a≠0}|^{s_*}(z))^{s/s_*}`
for every cube `U` resolved by the partition and every `w` of mean zero on `C_*(U)`, with `ρ` the
reach scale of the coarse-graining data. The same bound holds with constant `K(d, s)` when instead
`∑_{x ∈ U} [w]_𝒫(x) = 0`.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 3.4, for the partition into good cubes in every
dimension** (case `∑_{C_*(U)} w = 0`). -/
theorem exists_partition_sum_rpow_le_of_sum_eq_zero (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) < s) (ht : t = s * d / (s + d)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U) (w : Vertex d → ℝ),
      ∑ x ∈ crossingClusterVertices ω U, w x = 0 →
        ∑ x ∈ crossingClusterVertices ω U, |w x| ^ s ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t) := by
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hsd : (d : ℝ) < s * (d - 1) := by rwa [div_lt_iff₀ hdm] at hs
  have hs1 : 1 ≤ s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hsd0]
    nlinarith
  have hts : t ≤ s := by
    rw [ht, div_le_iff₀ hsd0]
    nlinarith
  obtain ⟨S, hS, hLS⟩ := IntegerCube.exists_latticeSobolevOn hd hs ht
  obtain ⟨K, hK, h⟩ := exists_partition_sum_rpow_le_of_latticeSobolevOn hd0 hs1 ht1 hts hS
  refine ⟨K, hK, fun ω hP U hU w hw => h ω hP U hU (hLS _ ?_) w hw⟩
  show 0 < 3 ^ U.scale
  positivity

/-- **Armstrong and Dario, Proposition 3.4, for the partition into good cubes in every
dimension** (case `∑_{U} [w]_𝒫 = 0`). -/
theorem exists_partition_sum_rpow_le_of_sum_coarsen_eq_zero (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) < s) (ht : t = s * d / (s + d)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U) (w : Vertex d → ℝ),
      ∑ x ∈ U.toIntegerCube.vertices, w (partitionAnchor ω x) = 0 →
        ∑ x ∈ crossingClusterVertices ω U, |w x| ^ s ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t) := by
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hsd : (d : ℝ) < s * (d - 1) := by rwa [div_lt_iff₀ hdm] at hs
  have hs0 : 0 < s := by nlinarith
  have hs1 : 1 ≤ s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hsd0]
    nlinarith
  have hts : t ≤ s := by
    rw [ht, div_le_iff₀ hsd0]
    nlinarith
  obtain ⟨S, hS, hLS⟩ := IntegerCube.exists_latticeSobolevOn hd hs ht
  set C₂ : ℝ := 3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d *
    (2 * √(d : ℝ)) with hC₂
  set C₃ : ℝ := 2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) *
    (2 * √(d : ℝ)) with hC₃
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  have hst : 0 ≤ s / t := by positivity
  refine ⟨2 ^ (s - 1) * (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) * 2 ^ (s / t), by positivity, ?_⟩
  intro ω hP U hU w hw
  set P := partitionCoarseData hd0 hP U hU with hPdef
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  have h32 := partition_sum_abs_sub_coarseAnchor_rpow_le hd0 hP hU w hs1
  have h33 := partition_sum_gradNormIn_coarseAnchor_rpow_le hd0 hP hU w ht1
  have hsize : 0 < U.toIntegerCube.size := by
    show 0 < 3 ^ U.scale
    positivity
  have hmain := P.sum_rpow_le_of_latticeSobolevOn_of_sum_coarsen hs1 ht1 hts
    (Real.rpow_nonneg hC₂0 s) (Real.rpow_nonneg hC₃0 t) hS
    (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * d))
    (b := fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    (hLS _ hsize) w h32 h33 hw
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
  have hK0 : 0 ≤ 2 ^ (s - 1) * (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) := by positivity
  calc _ ≤ 2 ^ (s - 1) * (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) *
        (2 ^ (s / t) * (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t)) :=
        mul_le_mul_of_nonneg_left hpow hK0
    _ = _ := by ring

end Rigidity.Percolation
