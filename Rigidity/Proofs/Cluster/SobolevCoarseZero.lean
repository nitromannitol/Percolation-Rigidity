import Rigidity.Proofs.Cluster.SobolevZero
import Rigidity.Proofs.Cluster.PartitionSobolev

/-!
# The Sobolev inequality on a cluster for coarsenings vanishing on the boundary

Armstrong and Dario, Proposition 3.4, in the case where the coarsening `[w]_𝒫` vanishes on the
boundary of the cube: the usual Sobolev inequality on `ℤ^d` with zero boundary values applied to
`[w]_𝒫`, Lemma 3.3 for `∇[w]_𝒫` and Lemma 3.2 for `w - [w]_𝒫`. For coarse-graining data whose
domain satisfies the lattice Sobolev inequality with zero boundary values, with exponents
`1 ≤ t ≤ s`, Lemma 3.2 with constant `A` and weights `a`, and Lemma 3.3 with constant `B` and
weights `b`,
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ 2^{s-1} (A + S B^{s/t})
(∑_z (a(z)^{t/s} + b(z)) |∇w 1_{a≠0}|^t(z))^{s/t}`
whenever `[w]_𝒫` vanishes at the vertices of the domain having a lattice neighbour outside it.
For the partition into good cubes in dimension `d ≥ 2` with `s ≥ d/(d-1)` and `t = s_* = sd/(s+d)`
the hypothesis on the domain holds by the lattice Sobolev inequality with zero boundary values.
Armstrong and Dario state the condition as `[w]_𝒫 = 0` on the `𝐚`-boundary of the cube; the
lattice Sobolev inequality they apply needs it on the lattice boundary, which is used here.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The lattice Sobolev inequality with zero boundary values on a finite domain `D` with
exponents `s`, `t` and constant `S`: `∑_{x ∈ D} |f(x)|^s ≤ S (∑_{x ∈ D} |∇f|^t(x))^{s/t}` for
every `f` vanishing at the vertices of `D` having a lattice neighbour outside `D`. -/
def LatticeSobolevZeroOn (D : Finset (Vertex d)) (s t S : ℝ) : Prop :=
  ∀ f : Vertex d → ℝ, (∀ x ∈ D, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ D → f x = 0) →
    ∑ x ∈ D, |f x| ^ s ≤
      S * (∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ t) ^ (s / t)

/-- The lattice Sobolev inequality with zero boundary values holds on every finite domain of
`ℤ^d`, `d ≥ 2`, for `s ≥ d/(d-1)` and `t = sd/(s+d)`, with a constant depending on `d` and `s`. -/
theorem exists_latticeSobolevZeroOn (hd : 2 ≤ d) {s t : ℝ} (hs : (d : ℝ) / (d - 1) ≤ s)
    (ht : t = s * d / (s + d)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ D : Finset (Vertex d), LatticeSobolevZeroOn D s t S :=
  exists_sum_rpow_le_of_eq_zero_on_boundary hd hs ht

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- **Armstrong and Dario, Proposition 3.4, from the lattice Sobolev inequality with zero
boundary values** (case `[w]_𝒫 = 0` on the boundary of the domain). -/
theorem sum_rpow_le_of_latticeSobolevZeroOn {s t A B S : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hts : t ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) {a b : Vertex d → ℝ}
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hLS : LatticeSobolevZeroOn P.domain s t S)
    (w : Vertex d → ℝ)
    (h32 : ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      A * ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s)
    (h33 : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t ≤
      B * ∑ z ∈ P.cluster, b z * gradNormIn (openGraph ω) P.cluster w z ^ t)
    (hw : ∀ x ∈ P.domain, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ P.domain →
      P.coarsen w x = 0) :
    ∑ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (A + S * B ^ (s / t)) *
        (∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
          gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  have htne : t ≠ 0 := ht0.ne'
  have hst : 1 ≤ s / t := by rw [le_div_iff₀ ht0]; linarith
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) P.cluster w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
      gradNormIn (openGraph ω) P.cluster w z ^ t := ⟨_, rfl⟩
  rw [← hW]
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (add_nonneg (Real.rpow_nonneg (ha z) _) (hb z))
      (Real.rpow_nonneg (hg0 z) _)
  have hc0 : (0 : ℝ) ≤ 2 ^ (s - 1) := by positivity
  have hUW : ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤ A * W ^ (s / t) := by
    refine h32.trans (mul_le_mul_of_nonneg_left ?_ hA)
    calc ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s
        = ∑ z ∈ P.cluster, (a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          Finset.sum_congr rfl fun z _ => by
            have e1 : (a z ^ (t / s)) ^ (s / t) = a z := by
              rw [← Real.rpow_mul (ha z), show t / s * (s / t) = 1 by field_simp, Real.rpow_one]
            have e2 : (gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) =
                gradNormIn (openGraph ω) P.cluster w z ^ s := by
              rw [← Real.rpow_mul (hg0 z), show t * (s / t) = s by field_simp]
            rw [Real.mul_rpow (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _), e1, e2]
      _ ≤ (∑ z ∈ P.cluster, a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          sum_rpow_le_rpow_sum _ _ hst fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _)
      _ ≤ W ^ (s / t) := by
          rw [hW]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _))
            (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (hb z)) (Real.rpow_nonneg (hg0 z) _)) (by linarith)
  have hVW : ∑ x ∈ P.cluster, |P.coarsen w x| ^ s ≤ S * B ^ (s / t) * W ^ (s / t) := by
    have h1 : ∑ x ∈ P.cluster, |P.coarsen w x| ^ s ≤ ∑ x ∈ P.domain, |P.coarsen w x| ^ s :=
      Finset.sum_le_sum_of_subset_of_nonneg P.cluster_subset fun _ _ _ =>
        Real.rpow_nonneg (abs_nonneg _) _
    have h3 : (∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^
        (s / t) ≤ (B * W) ^ (s / t) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (h33.trans ?_) (by linarith)
      rw [hW]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Real.rpow_nonneg (ha z) _)) (Real.rpow_nonneg (hg0 z) _)) hB
    rw [Real.mul_rpow hB hW0] at h3
    calc ∑ x ∈ P.cluster, |P.coarsen w x| ^ s
        ≤ ∑ x ∈ P.domain, |P.coarsen w x| ^ s := h1
      _ ≤ S * (∑ x ∈ P.domain,
            gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^ (s / t) :=
          hLS (P.coarsen w) hw
      _ ≤ S * (B ^ (s / t) * W ^ (s / t)) := mul_le_mul_of_nonneg_left h3 hS
      _ = S * B ^ (s / t) * W ^ (s / t) := by ring
  have hpt : ∀ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s + |P.coarsen w x| ^ s) := by
    intro x _
    have e : w x = (w x - P.coarsen w x) + P.coarsen w x := by ring
    calc |w x| ^ s = |(w x - P.coarsen w x) + P.coarsen w x| ^ s := by rw [← e]
      _ ≤ (|w x - P.coarsen w x| + |P.coarsen w x|) ^ s :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by linarith)
      _ ≤ _ := add_rpow_le_two_rpow_mul (abs_nonneg _) (abs_nonneg _) hs
  calc ∑ x ∈ P.cluster, |w x| ^ s
      ≤ ∑ x ∈ P.cluster, 2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s + |P.coarsen w x| ^ s) :=
        Finset.sum_le_sum hpt
    _ = 2 ^ (s - 1) * (∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s +
          ∑ x ∈ P.cluster, |P.coarsen w x| ^ s) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ (s - 1) * (A * W ^ (s / t) + S * B ^ (s / t) * W ^ (s / t)) :=
        mul_le_mul_of_nonneg_left (add_le_add hUW hVW) hc0
    _ = 2 ^ (s - 1) * (A + S * B ^ (s / t)) * W ^ (s / t) := by ring

end CoarseData

/-- **Armstrong and Dario, Proposition 3.4, for the partition into good cubes** (case
`[w]_𝒫 = 0` on the boundary of the cube). For `d ≥ 2`, `s ≥ d/(d-1)` and `t = s_* = sd/(s+d)`
there is `K(d, s)` with
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ K (∑_{z ∈ C_*(U)} (3^{ρ(z)})^{td} |∇w 1_{a≠0}|^t(z))^{s/t}`
for every cube `U` resolved by the partition and every `w` whose coarsening vanishes at the
vertices of `U` having a lattice neighbour outside `U`, with `ρ` the reach scale. -/
theorem exists_partition_sum_rpow_le_of_coarsen_eq_zero (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) ≤ s) (ht : t = s * d / (s + d)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U) (w : Vertex d → ℝ),
      (∀ x ∈ U.toIntegerCube.vertices, ∀ y, (nearestNeighborGraph d).Adj x y →
        y ∉ U.toIntegerCube.vertices → w (partitionAnchor ω x) = 0) →
        ∑ x ∈ crossingClusterVertices ω U, |w x| ^ s ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t) := by
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hsd : (d : ℝ) ≤ s * (d - 1) := by rwa [div_le_iff₀ hdm] at hs
  have hs0 : 0 < s := by nlinarith
  have hs1 : 1 ≤ s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hsd0]
    nlinarith
  have hts : t ≤ s := by
    rw [ht, div_le_iff₀ hsd0]
    nlinarith
  obtain ⟨S, hS, hLS⟩ := exists_latticeSobolevZeroOn hd hs ht
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
  have hmain := P.sum_rpow_le_of_latticeSobolevZeroOn hs1 ht1 hts (Real.rpow_nonneg hC₂0 s)
    (Real.rpow_nonneg hC₃0 t) hS (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * d))
    (b := fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (t * d - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    (hLS _) w h32 h33 hw
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
