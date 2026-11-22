import Rigidity.Proofs.Cluster.PartitionBoxCluster
import Rigidity.Proofs.Cluster.SobolevCube
import Rigidity.Proofs.Cluster.ReverseHolderSobolev
import Rigidity.Proofs.Cluster.PartitionReachMoments

/-!
# The Sobolev inequality on the cluster of a resolved integer cube in every dimension

Armstrong and Dario, Lemmas 3.2 and 3.3 and Proposition 3.4 (case `∑_{C(B)} w = 0`), for the
partition into good cubes in every dimension `d ≥ 2`, on the cluster `C(B)` of an integer cube `B`
resolved by the partition (for instance the triple `3□'` of a triadic cube, which is not triadic).
The regions of the local paths lie in the `3s`-neighbourhoods of the partition cubes, and the pair
regions in the unions of two neighbouring partition cubes, so Lemma 3.2 holds with the reach scale
`ρ` of the coarse-graining data of `B` and Lemma 3.3 in its stated form. With the lattice Sobolev
inequality on the integer cube `B`, the Sobolev hypothesis `ClusterSobolevTwo` of the reverse Hölder
inequality holds on `C(B)` with the weight `3^{ρ(z)}` (`exists_clusterSobolevTwo_box`), and
`3^{ρ(z)}` is at most the reach of the partition `partitionReach ω z`.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The region of a vertex lies in the `3s`-neighbourhood of its partition cube. -/
theorem partitionBoxRegion_subset_thicken (hP : PartitionEvent ω) (B : IntegerCube d)
    (x : Vertex d) : partitionBoxRegion ω B x ⊆ ((partitionCube ω x).thicken 3).vertices := by
  intro y hy
  have hy' := (Finset.mem_filter.1 hy).2
  have h1 : y ∈ cubeAt x (3 ^ ((partitionCube ω x).scale + 1)) := by
    rcases hy' with h | h
    · exact parent_union_cubeAt_subset hP x (Or.inl h)
    · have hle : 3 ^ (partitionCube ω x).scale - 1 ≤ 3 ^ ((partitionCube ω x).scale + 1) :=
        (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      simp only [cubeAt, Set.mem_setOf_eq] at h ⊢
      exact fun i => (h i).trans (by exact_mod_cast hle)
  exact Finset.mem_coe.1 ((partitionCube ω x).cubeAt_subset_thicken (mem_partitionCube hP x)
    (by rw [pow_succ]; omega) h1)

/-- The pair regions of a resolved integer cube have bounded overlap with constants `1 + 3^d`,
`21^d` and `1`. -/
theorem partitionBoxCoarseData_pairOverlap (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) :
    (partitionBoxCoarseData hd hP B hB).PairOverlap (1 + 3 ^ d) (21 ^ d) 1 :=
  (partitionBoxCoarseData hd hP B hB).pairOverlap_of_mem
    (fun _ _ _ hz => (Finset.mem_filter.1 (Finset.mem_inter.1 hz).1).2)
    (fun _ _ _ _ hn => by
      obtain ⟨a, ha, b, hb, hab⟩ := hn
      have h := partitionCube_scales_close hP hab
      rw [partitionCube_eq_of_mem hP ha, partitionCube_eq_of_mem hP hb] at h
      exact h.1)

/-- **Armstrong and Dario, Lemma 3.2, on a resolved integer cube, with the reach scale.** -/
theorem partitionBox_sum_abs_sub_coarseAnchor_rpow_le (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) (w : Vertex d → ℝ) {s : ℝ}
    (hs : 1 ≤ s) :
    ∑ x ∈ partitionBoxCluster ω B, |w x - w (partitionAnchor ω x)| ^ s ≤
      (3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ partitionBoxCluster ω B,
          ((3 : ℝ) ^ (partitionBoxCoarseData hd hP B hB).reachScale z) ^ (s * d) *
            gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ s :=
  (partitionBoxCoarseData hd hP B hB).sum_abs_sub_coarsen_rpow_le_reach (c := 3)
    (fun x _ => Finset.inter_subset_left.trans (partitionBoxRegion_subset_thicken hP B x))
    (by omega) w hs

/-- **Armstrong and Dario, Lemma 3.3, on a resolved integer cube.** -/
theorem partitionBox_sum_gradNormIn_coarseAnchor_rpow_le (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) (w : Vertex d → ℝ) {s : ℝ}
    (hs : 1 ≤ s) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices
        (fun x => w (partitionAnchor ω x)) x ^ s ≤
      (2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) *
        (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ partitionBoxCluster ω B, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1) *
          gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ s :=
  (partitionBoxCoarseData hd hP B hB).sum_gradNormIn_coarsen_rpow_le
    (partitionBoxCoarseData_pairOverlap hd hP hB) (Nat.le_add_right 1 _)
    (Nat.one_le_pow _ _ (by norm_num)) (by omega) w hs

/-- **Armstrong and Dario, Proposition 3.4, on a resolved integer cube**, given the lattice
Sobolev–Poincaré inequality on the cube (case `∑_{C(B)} w = 0`). -/
theorem exists_partitionBox_sum_rpow_le_of_latticeSobolevOn (hd : 0 < d) {s t S : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hts : t ≤ s) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (B : IntegerCube d)
      (hB : PartitionBoxResolved ω B), LatticeSobolevOn B.vertices s t S →
      ∀ w : Vertex d → ℝ, ∑ x ∈ partitionBoxCluster ω B, w x = 0 →
        ∑ x ∈ partitionBoxCluster ω B, |w x| ^ s ≤
          K * (∑ z ∈ partitionBoxCluster ω B,
            ((3 : ℝ) ^ (partitionBoxCoarseData hd hP B hB).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t) ^ (s / t) := by
  set C₂ : ℝ := 3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d *
    (2 * √(d : ℝ)) with hC₂
  set C₃ : ℝ := 2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) *
    (2 * √(d : ℝ)) with hC₃
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  have hst : 0 ≤ s / t := by positivity
  refine ⟨2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
    (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) * 2 ^ (s / t), by positivity, ?_⟩
  intro ω hP B hB hLS w hw
  set P := partitionBoxCoarseData hd hP B hB with hPdef
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  have h32 := partitionBox_sum_abs_sub_coarseAnchor_rpow_le hd hP hB w hs
  have h33 := partitionBox_sum_gradNormIn_coarseAnchor_rpow_le hd hP hB w ht
  have hmain := P.sum_rpow_le_of_latticeSobolevOn hs ht hts (Real.rpow_nonneg hC₂0 s)
    (Real.rpow_nonneg hC₃0 t) hS (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * d))
    (b := fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    hLS w h32 h33 hw
  refine hmain.trans ?_
  have hweight : ∀ z ∈ partitionBoxCluster ω B,
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
  have hsum : ∑ z ∈ partitionBoxCluster ω B,
      ((((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) +
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1)) *
        gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t ≤
      2 * ∑ z ∈ partitionBoxCluster ω B, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
        gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hweight z hz) (Real.rpow_nonneg (hg0 z) _)
  have hX0 : 0 ≤ ∑ z ∈ partitionBoxCluster ω B, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
      gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t :=
    Finset.sum_nonneg fun z _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (hg0 z) _)
  have hW0 : 0 ≤ ∑ z ∈ partitionBoxCluster ω B,
      ((((3 : ℝ) ^ P.reachScale z) ^ (s * d)) ^ (t / s) +
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1)) *
        gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t :=
    Finset.sum_nonneg fun z _ => mul_nonneg (add_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (hg0 z) _)
  have hpow := Real.rpow_le_rpow hW0 hsum hst
  rw [Real.mul_rpow (x := (2 : ℝ)) (by norm_num) hX0] at hpow
  have hK0 : 0 ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
      (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) := by positivity
  calc _ ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
        (C₂ ^ s + S * (C₃ ^ t) ^ (s / t)) *
        (2 ^ (s / t) * (∑ z ∈ partitionBoxCluster ω B, ((3 : ℝ) ^ P.reachScale z) ^ (t * d) *
          gradNormIn (openGraph ω) (partitionBoxCluster ω B) w z ^ t) ^ (s / t)) :=
        mul_le_mul_of_nonneg_left hpow hK0
    _ = _ := by ring

/-- **Proposition 3.4 with `s = 2` on a resolved integer cube, as the Sobolev hypothesis of the
reverse Hölder inequality**, in every dimension `d ≥ 2`, with the weight `3^{ρ(z)}`. -/
theorem exists_clusterSobolevTwo_box (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (B : IntegerCube d)
      (_ : 0 < B.size) (hB : PartitionBoxResolved ω B),
      Rigidity.Proofs.Cluster.ClusterSobolevTwo ω (partitionBoxCluster ω B)
        (fun z => (3 : ℝ) ^ (partitionBoxCoarseData (by omega) hP B hB).reachScale z) K := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hs : (d : ℝ) / (d - 1) ≤ 2 := by
    rw [div_le_iff₀ hdm]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : Rigidity.Proofs.Cluster.lowerSobolevTwo d = 2 * d / (2 + d) := by
    rw [Rigidity.Proofs.Cluster.lowerSobolevTwo, add_comm (d : ℝ) 2]
  obtain ⟨S, hS, hLS⟩ := IntegerCube.exists_latticeSobolevOn hd hs ht
  have h1 := Rigidity.Proofs.Cluster.one_le_lowerSobolevTwo hd
  have h2 := Rigidity.Proofs.Cluster.lowerSobolevTwo_le_two (d := d)
  obtain ⟨K, hK0, hK⟩ := exists_partitionBox_sum_rpow_le_of_latticeSobolevOn (d := d) (by omega)
    (s := 2) (t := Rigidity.Proofs.Cluster.lowerSobolevTwo d) (by norm_num) h1 h2 hS
  refine ⟨K, hK0, fun ω hP B hBs hB w hw => ?_⟩
  have h := hK ω hP B hB (hLS B hBs) w hw
  set C := partitionBoxCluster ω B with hC
  have hq0 : 0 ≤ Rigidity.Proofs.Cluster.lowerSobolevTwo d := by linarith
  calc ∑ x ∈ C, w x ^ 2 = ∑ x ∈ C, |w x| ^ (2 : ℝ) :=
        Finset.sum_congr rfl fun x _ => by rw [Real.rpow_two, sq_abs]
    _ ≤ K * (∑ z ∈ C, ((3 : ℝ) ^ (partitionBoxCoarseData (by omega) hP B hB).reachScale z) ^
          (Rigidity.Proofs.Cluster.lowerSobolevTwo d * d) *
          gradNormIn (openGraph ω) C w z ^ Rigidity.Proofs.Cluster.lowerSobolevTwo d) ^
            (2 / Rigidity.Proofs.Cluster.lowerSobolevTwo d) := h
    _ ≤ K * (∑ z ∈ C, ((3 : ℝ) ^ (partitionBoxCoarseData (by omega) hP B hB).reachScale z) ^
          (2 * (d : ℝ)) * Rigidity.Proofs.Cluster.clusterGradSq ω C w z ^
            (Rigidity.Proofs.Cluster.lowerSobolevTwo d / 2)) ^
            (2 / Rigidity.Proofs.Cluster.lowerSobolevTwo d) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Finset.sum_nonneg fun z _ =>
          mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _))
          (Finset.sum_le_sum fun z _ => ?_) (div_nonneg zero_le_two hq0)) hK0
        have hgrad : gradNormIn (openGraph ω) C w z ^ Rigidity.Proofs.Cluster.lowerSobolevTwo d =
            Rigidity.Proofs.Cluster.clusterGradSq ω C w z ^
              (Rigidity.Proofs.Cluster.lowerSobolevTwo d / 2) := by
          rw [Rigidity.Proofs.Cluster.gradNormIn_openGraph_eq, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (Rigidity.Proofs.Cluster.clusterGradSq_nonneg ω C w z)]
          congr 1
          ring
        rw [hgrad]
        refine mul_le_mul_of_nonneg_right ?_
          (Real.rpow_nonneg (Rigidity.Proofs.Cluster.clusterGradSq_nonneg ω C w z) _)
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by nlinarith)

/-- On a resolved integer cube, `3^{ρ(z)}` is at most the reach of the partition at `z`. -/
theorem three_pow_reachScale_le_partitionReach_box (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {z : Vertex d}
    (hz : z ∈ partitionBoxCluster ω B) :
    (3 : ℝ≥0∞) ^ (partitionBoxCoarseData hd hP B hB).reachScale z ≤ partitionReach ω z := by
  set P := partitionBoxCoarseData hd hP B hB
  have hne : (P.cluster.filter fun x => z ∈ P.region x).Nonempty :=
    ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
  obtain ⟨x, hx, hxs⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
  rw [Finset.mem_filter] at hx
  unfold CoarseData.reachScale
  rw [hxs]
  unfold partitionReach
  exact le_iSup₂_of_le (partitionCube ω x)
    ⟨(partitionCube_spec hP x).2, partitionBoxRegion_subset_thicken hP B x hx.2⟩ le_rfl

end Rigidity.Percolation
