import Rigidity.Proofs.Cluster.SobolevCoarseZero

/-!
# The Sobolev inequality on a cluster from an approximation vanishing on the boundary

Armstrong and Dario, end of the proof of Proposition 3.4: for any function `v` vanishing on the
lattice boundary of the domain, for which `w - v` satisfies the bound of Lemma 3.2 and `∇v` the
bound of Lemma 3.3, the Sobolev inequality on the cluster holds for `w`, by the lattice Sobolev
inequality with zero boundary values applied to `v`. With `v = [w]_𝒫` this is the case
`[w]_𝒫 = 0` on the boundary; Armstrong and Dario use a modification of `[w]_𝒫` vanishing on the
partition cubes touching the boundary for the case `w = 0` on the `𝐚`-boundary.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- **Armstrong and Dario, Proposition 3.4, for an approximation vanishing on the boundary.** If
`v` vanishes at the vertices of the domain having a lattice neighbour outside it, `w - v` satisfies
the bound of Lemma 3.2 on the cluster and `∇v` the bound of Lemma 3.3 on the domain, then the
Sobolev inequality on the cluster holds for `w`. Armstrong and Dario apply this with `v` equal to
`[w]_𝒫` off the partition cubes touching the boundary and to `0` on them, in the case `w = 0` on
the `𝐚`-boundary. -/
theorem sum_rpow_le_of_latticeSobolevZeroOn_of_approx {s t A B S : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hts : t ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) {a b : Vertex d → ℝ}
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hLS : LatticeSobolevZeroOn P.domain s t S)
    (w v : Vertex d → ℝ)
    (h32 : ∑ x ∈ P.cluster, |w x - v x| ^ s ≤
      A * ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s)
    (h33 : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain v x ^ t ≤
      B * ∑ z ∈ P.cluster, b z * gradNormIn (openGraph ω) P.cluster w z ^ t)
    (hv : ∀ x ∈ P.domain, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ P.domain → v x = 0) :
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
  have hUW : ∑ x ∈ P.cluster, |w x - v x| ^ s ≤ A * W ^ (s / t) := by
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
  have hVW : ∑ x ∈ P.cluster, |v x| ^ s ≤ S * B ^ (s / t) * W ^ (s / t) := by
    have h1 : ∑ x ∈ P.cluster, |v x| ^ s ≤ ∑ x ∈ P.domain, |v x| ^ s :=
      Finset.sum_le_sum_of_subset_of_nonneg P.cluster_subset fun _ _ _ =>
        Real.rpow_nonneg (abs_nonneg _) _
    have h3 : (∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain v x ^ t) ^
        (s / t) ≤ (B * W) ^ (s / t) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (h33.trans ?_) (by linarith)
      rw [hW]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Real.rpow_nonneg (ha z) _)) (Real.rpow_nonneg (hg0 z) _)) hB
    rw [Real.mul_rpow hB hW0] at h3
    calc ∑ x ∈ P.cluster, |v x| ^ s
        ≤ ∑ x ∈ P.domain, |v x| ^ s := h1
      _ ≤ S * (∑ x ∈ P.domain,
            gradNormIn (nearestNeighborGraph d) P.domain v x ^ t) ^ (s / t) :=
          hLS v hv
      _ ≤ S * (B ^ (s / t) * W ^ (s / t)) := mul_le_mul_of_nonneg_left h3 hS
      _ = S * B ^ (s / t) * W ^ (s / t) := by ring
  have hpt : ∀ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (|w x - v x| ^ s + |v x| ^ s) := by
    intro x _
    have e : w x = (w x - v x) + v x := by ring
    calc |w x| ^ s = |(w x - v x) + v x| ^ s := by rw [← e]
      _ ≤ (|w x - v x| + |v x|) ^ s :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by linarith)
      _ ≤ _ := add_rpow_le_two_rpow_mul (abs_nonneg _) (abs_nonneg _) hs
  calc ∑ x ∈ P.cluster, |w x| ^ s
      ≤ ∑ x ∈ P.cluster, 2 ^ (s - 1) * (|w x - v x| ^ s + |v x| ^ s) :=
        Finset.sum_le_sum hpt
    _ = 2 ^ (s - 1) * (∑ x ∈ P.cluster, |w x - v x| ^ s +
          ∑ x ∈ P.cluster, |v x| ^ s) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ (s - 1) * (A * W ^ (s / t) + S * B ^ (s / t) * W ^ (s / t)) :=
        mul_le_mul_of_nonneg_left (add_le_add hUW hVW) hc0
    _ = 2 ^ (s - 1) * (A + S * B ^ (s / t)) * W ^ (s / t) := by ring

end CoarseData

end Rigidity.Percolation
