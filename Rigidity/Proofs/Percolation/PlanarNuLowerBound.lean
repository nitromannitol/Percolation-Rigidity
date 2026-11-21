import Rigidity.Proofs.Percolation.PlanarSubcubeCounts

/-!
# Lower bound for `ν`

For the maximizer `v` of `ν(U, p)` on a resolved cube `U` of side `L`, the boundary error of the
coarsened gradient satisfies `|p|₁ BE(p, v) / |U| ≤ 9 |p|₁² (162001 S / (L √L) + 1 / (2 √L))`,
with `S = ∑_{x ∈ ∂U} s_x⁴`. Testing the comparison of `μ` and `ν` with `q = λ p`, `λ ≥ 0`, gives

`λ |p|² ≤ ν(U, p) - μ(U, λ p) + λ (|p|² / L + 9 |p|₁² (162001 S / (L √L) + 1 / (2 √L)))`.

Since `E[-μ(U, λ p)] ≤ C λ² |p|₁²` and the boundary terms have expectation `O(|p|₁² / √L)`, choosing
`λ` small gives, uniformly in `U`,

`c |p|² ≤ E[ν(U, p); partition event, U resolved] + C |p|₁² / √L`

(Armstrong and Dario, Lemma 4.7, (4.14), in expectation; the deterministic `λ` replaces the random
choice of `q` made there, which is possible after taking expectations).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **Boundary error for the maximizer of `ν`.** -/
theorem mul_boundaryError_div_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) {v : ClusterFun ω U}
    (hv : v ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w) :
    (|p 0| + |p 1|) * boundaryError ω U p v / U.volume ≤
      9 * (|p 0| + |p 1|) ^ 2 * (162001 * (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) /
        ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ)) +
        1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ)) := by
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact_mod_cast (show 1 ≤ U.toIntegerCube.size from by
      change 1 ≤ 3 ^ U.scale
      exact Nat.one_le_pow _ _ (by norm_num))
  have hLvol : L * L = U.volume := by
    rw [hL]
    change ((3 ^ U.scale : ℕ) : ℝ) * ((3 ^ U.scale : ℕ) : ℝ) = (9 : ℝ) ^ U.scale
    push_cast
    rw [← mul_pow]
    norm_num
  set S4 := ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 with hS4def
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun k _ => by
    have := one_le_partSide (ω := ω) k.2.2
    positivity
  rcases (show (0 : ℝ) ≤ |p 0| + |p 1| by positivity).eq_or_lt with hP0 | hPpos
  · rw [← hP0]
    simp
  set Q := 9 * (|p 0| + |p 1|) with hQ
  have hQpos : 0 < Q := by positivity
  have hP₁ : |p 0| + |p 1| = Q / 9 := by
    rw [hQ]
    ring
  have hB : clusterForm ω U v v ≤ 9 / 2 * (Q / 9) ^ 2 * (L * L) := by
    have h1 := clusterForm_le_of_variation p hv hvar
    have h2 := planarNu_le (ω := ω) (U := U) p
    rw [hP₁] at h2
    rw [hLvol]
    have hvol := U.volume_pos
    calc clusterForm ω U v v ≤ 2 * U.volume * planarNu ω U p := h1
      _ ≤ 2 * U.volume * (9 / 4 * (Q / 9) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 9 / 2 * (Q / 9) ^ 2 * U.volume := by ring
  set t := 1 / (Q / 9 * Real.sqrt L) with ht
  have htpos : 0 < t := by positivity
  have hbe := boundaryError_le p v htpos
  rw [hP₁] at hbe
  have hW := sum_sq_boundaryWeight_le hP hU
  have hfaces : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, (3 : ℝ) ^ (planarPartCube ω x).scale +
      ∑ x ∈ U.toIntegerCube.lowerFace i, (3 : ℝ) ^ (planarPartCube ω x).scale) ≤ S4 := by
    have := sum_boundaryIndex U (fun x => (3 : ℝ) ^ (planarPartCube ω x).scale)
    rw [← this]
    exact sum_boundaryIndex_partSide_le U
  have hBE : boundaryError ω U p v ≤
      (9 * (324000 * S4) / t + t * (2 * (9 / 2 * (Q / 9) ^ 2 * (L * L)))) / 2 +
        Q / 9 * S4 := by
    have h1 : 9 * (∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2) / t ≤
        9 * (324000 * S4) / t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num)) htpos.le
    have h2 : t * (2 * clusterForm ω U v v) ≤ t * (2 * (9 / 2 * (Q / 9) ^ 2 * (L * L))) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    have h3 := mul_le_mul_of_nonneg_left hfaces (show (0 : ℝ) ≤ Q / 9 by positivity)
    linarith
  have halg := boundary_algebra hQpos hL1 hS4 hBE
  rw [← hLvol, hP₁]
  have e1 : Q / 9 * boundaryError ω U p v / (L * L) =
      Q * boundaryError ω U p v / (L * L) / 9 := by ring
  have e2 : 9 * (Q / 9) ^ 2 * (162001 * S4 / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) =
      Q ^ 2 * (162001 * S4 / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) / 9 := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right halg (by norm_num)

/-- **Lower bound for `ν` by testing `μ` with `q = λ p`.** -/
theorem planarNu_ge (hP : PlanarPartitionEvent ω) {U : TriadicCube 2} (hU : PlanarResolved ω U)
    (p : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * (p 0 ^ 2 + p 1 ^ 2) ≤ planarNu ω U p - planarMu ω U (fun i => lam * p i) +
      lam * ((p 0 ^ 2 + p 1 ^ 2) / (U.toIntegerCube.size : ℝ) +
        9 * (|p 0| + |p 1|) ^ 2 * (162001 * (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) /
          ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ)) +
          1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ))) := by
  set q : Fin 2 → ℝ := fun i => lam * p i with hq
  obtain ⟨v, hv, hvar, hle⟩ := planarMu_le_planarNu_sub hP hU p q
  have hs : ∑ i, q i * p i = lam * (p 0 ^ 2 + p 1 ^ 2) := by
    simp only [hq, Fin.sum_univ_two]
    ring
  have hq1 : |q 0| + |q 1| = lam * (|p 0| + |p 1|) := by
    simp only [hq, abs_mul, abs_of_nonneg hlam]
    ring
  rw [hs, hq1, abs_of_nonneg (show 0 ≤ lam * (p 0 ^ 2 + p 1 ^ 2) by positivity)] at hle
  have e3 : lam * (|p 0| + |p 1|) * boundaryError ω U p v / U.volume =
      lam * ((|p 0| + |p 1|) * boundaryError ω U p v / U.volume) := by ring
  have e4 : lam * (p 0 ^ 2 + p 1 ^ 2) / (U.toIntegerCube.size : ℝ) =
      lam * ((p 0 ^ 2 + p 1 ^ 2) / (U.toIntegerCube.size : ℝ)) := by ring
  rw [e3, e4] at hle
  have hbe := mul_le_mul_of_nonneg_left (mul_boundaryError_div_le hP hU p hv hvar) hlam
  linarith

/-- An unresolved cube contains a vertex with a large partition cube. -/
theorem one_le_sum_of_not_resolved {U : TriadicCube 2} (h : ¬ PlanarResolved ω U) :
    1 ≤ ∑ z ∈ U.toIntegerCube.vertices, (partSide ω z / 3 ^ (U.scale + 1)) ^ 6 := by
  have hnn : ∀ z, 0 ≤ (partSide ω z / 3 ^ (U.scale + 1)) ^ 6 := fun z => by positivity
  unfold PlanarResolved at h
  push Not at h
  obtain ⟨z, hz, hlt⟩ := h
  have hzU : z ∈ U.toIntegerCube.vertices := (U.mem_toIntegerCube_vertices z).2 hz
  have h1 : 1 ≤ (partSide ω z / 3 ^ (U.scale + 1)) ^ 6 := by
    have hside : (3 : ℝ) ^ (U.scale + 1) ≤ partSide ω z := by
      unfold partSide
      exact pow_le_pow_right₀ (by norm_num) hlt
    have : 1 ≤ partSide ω z / 3 ^ (U.scale + 1) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact one_le_pow₀ this
  exact h1.trans (Finset.single_le_sum (fun z _ => hnn z) hzU)

/-- Sums of sixth powers of scaled partition sides, by reach sums. -/
theorem ofReal_sum_partSide_div_pow_le (hP : PlanarPartitionEvent ω) (S : Finset (Vertex 2))
    (m : ℕ) :
    ENNReal.ofReal (∑ z ∈ S, (partSide ω z / 3 ^ (m + 1)) ^ 6) ≤
      ∑ z ∈ S, ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (m + 1))) * reachSum ω 6 z := by
  rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by positivity]
  refine Finset.sum_le_sum fun z _ => ?_
  have e : (partSide ω z / 3 ^ (m + 1)) ^ 6 =
      1 / (3 : ℝ) ^ (6 * (m + 1)) * partSide ω z ^ (5 + 1) := by
    rw [div_pow, ← pow_mul, mul_comm (m + 1) 6]
    ring
  rw [e, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_of_nonneg_left (ofReal_partSide_pow_le hP z 5) zero_le

/-- The reach-sum majorant of the errors in the lower bound for `ν`. -/
noncomputable def nuLowerErrorBound (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ)
    (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (9 * (lam * (|p 0| + |p 1|)) ^ 2 / U.volume) *
      ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a +
    ENNReal.ofReal (lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 /
      ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ))) *
      ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 +
    ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2)) *
      ∑ z ∈ U.toIntegerCube.vertices,
        ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z

theorem measurable_nuLowerErrorBound (U : TriadicCube 2) (p : Fin 2 → ℝ) (lam : ℝ) :
    Measurable fun ω : Configuration 2 => nuLowerErrorBound ω U p lam := by
  unfold nuLowerErrorBound
  exact (((Finset.measurable_sum _ fun a _ => (measurable_reachSum 4 a).const_mul _).const_mul
      _).add ((Finset.measurable_sum _ fun k _ => measurable_reachSum 4 k.2.2).const_mul _)).add
    ((Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _).const_mul _)

/-- **Pointwise lower bound for `ν` in reach sums.** -/
theorem ofReal_lam_le (U : TriadicCube 2) (p : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2)) ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (planarNu ω U p)
        else 0) +
      (nuLowerErrorBound ω U p lam +
        ENNReal.ofReal (lam * ((p 0 ^ 2 + p 1 ^ 2) / (U.toIntegerCube.size : ℝ) +
          9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ))))) +
      (if PlanarPartitionEvent ω then 0 else ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2))) := by
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL0 : 0 < L := by
    rw [hL]
    exact_mod_cast (show 0 < U.toIntegerCube.size from by
      change 0 < 3 ^ U.scale
      positivity)
  have hvol := U.volume_pos
  by_cases hP : PlanarPartitionEvent ω
  · rw [if_pos hP, add_zero]
    by_cases hU : PlanarResolved ω U
    · rw [if_pos ⟨hP, hU⟩]
      have hb := planarNu_ge hP hU p hlam
      rw [← hL] at hb
      set S4 := ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 with hS4def
      have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun k _ => by
        have := one_le_partSide (ω := ω) k.2.2
        positivity
      have hmu := planarMu_nonpos hP hU (fun i => lam * p i)
      have hν := planarNu_nonneg (ω := ω) (U := U) p
      have e : lam * ((p 0 ^ 2 + p 1 ^ 2) / L + 9 * (|p 0| + |p 1|) ^ 2 *
          (162001 * S4 / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L)) =
          lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L) * S4 +
          lam * ((p 0 ^ 2 + p 1 ^ 2) / L + 9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L)) := by
        ring
      rw [e] at hb
      have hb' : lam * (p 0 ^ 2 + p 1 ^ 2) ≤ planarNu ω U p +
          (-planarMu ω U (fun i => lam * p i) +
            lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L) * S4) +
          lam * ((p 0 ^ 2 + p 1 ^ 2) / L + 9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L)) := by
        linarith
      have hc0 : 0 ≤ lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L) := by positivity
      have hAS := mul_nonneg hc0 hS4
      have hB0 : 0 ≤ lam * ((p 0 ^ 2 + p 1 ^ 2) / L +
          9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L)) := by positivity
      refine (ENNReal.ofReal_le_ofReal hb').trans ?_
      rw [ENNReal.ofReal_add (by linarith) hB0, ENNReal.ofReal_add hν (by linarith),
        ENNReal.ofReal_add (by linarith) hAS, ENNReal.ofReal_mul hc0]
      have hmuB := ofReal_neg_planarMu_le hP hU (fun i => lam * p i)
      have hq1 : |lam * p 0| + |lam * p 1| = lam * (|p 0| + |p 1|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam]
        ring
      rw [hq1] at hmuB
      have hmuB' : ENNReal.ofReal (-planarMu ω U (fun i => lam * p i)) ≤
          ENNReal.ofReal (9 * (lam * (|p 0| + |p 1|)) ^ 2 / U.volume) *
            ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a := by
        refine hmuB.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) zero_le)
        exact mul_le_mul_of_nonneg_left (planarReach_pow_le ω a 3) zero_le
      have hS4B : ENNReal.ofReal S4 ≤ ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 := by
        rw [hS4def, ENNReal.ofReal_sum_of_nonneg fun k _ => by
          have := one_le_partSide (ω := ω) k.2.2
          positivity]
        exact Finset.sum_le_sum fun k _ => ofReal_partSide_pow_le hP k.2.2 3
      unfold nuLowerErrorBound
      rw [← hL]
      calc ENNReal.ofReal (planarNu ω U p) +
            (ENNReal.ofReal (-planarMu ω U (fun i => lam * p i)) +
              ENNReal.ofReal (lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L)) *
                ENNReal.ofReal S4) +
            ENNReal.ofReal (lam * ((p 0 ^ 2 + p 1 ^ 2) / L +
              9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L)))
          ≤ ENNReal.ofReal (planarNu ω U p) +
            (ENNReal.ofReal (9 * (lam * (|p 0| + |p 1|)) ^ 2 / U.volume) *
              ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a +
              ENNReal.ofReal (lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L)) *
                ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2) +
            ENNReal.ofReal (lam * ((p 0 ^ 2 + p 1 ^ 2) / L +
              9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L))) := by
            gcongr
        _ ≤ ENNReal.ofReal (planarNu ω U p) +
            (ENNReal.ofReal (9 * (lam * (|p 0| + |p 1|)) ^ 2 / U.volume) *
              ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a +
              ENNReal.ofReal (lam * 9 * (|p 0| + |p 1|) ^ 2 * 162001 / (L * Real.sqrt L)) *
                ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 +
              ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2)) *
                ∑ z ∈ U.toIntegerCube.vertices,
                  ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z) +
            ENNReal.ofReal (lam * ((p 0 ^ 2 + p 1 ^ 2) / L +
              9 * (|p 0| + |p 1|) ^ 2 * (1 / 2 / Real.sqrt L))) :=
            add_le_add (add_le_add le_rfl le_self_add) le_rfl
        _ = _ := by ring
    · rw [if_neg (fun h => hU h.2), zero_add]
      have h1 := one_le_sum_of_not_resolved (ω := ω) hU
      have h2 := ofReal_sum_partSide_div_pow_le hP U.toIntegerCube.vertices U.scale
      have h3 : (1 : ℝ≥0∞) ≤ ∑ z ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z := by
        refine le_trans ?_ h2
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal h1
      unfold nuLowerErrorBound
      calc ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2))
          = ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2)) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (lam * (p 0 ^ 2 + p 1 ^ 2)) *
              ∑ z ∈ U.toIntegerCube.vertices,
                ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z :=
            mul_le_mul_of_nonneg_left h3 zero_le
        _ ≤ _ := by
            refine le_trans ?_ le_self_add
            exact le_add_left le_rfl
  · rw [if_neg hP, if_neg (fun h => hP h.1), zero_add]
    exact le_add_left le_rfl

/-- The side of a triadic cube is at least one. -/
theorem one_le_cast_size (U : TriadicCube 2) : (1 : ℝ) ≤ (U.toIntegerCube.size : ℝ) := by
  exact_mod_cast (show 1 ≤ U.toIntegerCube.size from by
    change 1 ≤ 3 ^ U.scale
    exact Nat.one_le_pow _ _ (by norm_num))

theorem cast_size_mul_self (U : TriadicCube 2) :
    (U.toIntegerCube.size : ℝ) * (U.toIntegerCube.size : ℝ) = U.volume := by
  change ((3 ^ U.scale : ℕ) : ℝ) * ((3 ^ U.scale : ℕ) : ℝ) = (9 : ℝ) ^ U.scale
  push_cast
  rw [← mul_pow]
  norm_num

/-- **Integrated pointwise lower bound for `ν`.** -/
theorem ofReal_lam_le_lintegral {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (U : TriadicCube 2) (ξ : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ENNReal.ofReal (lam * (ξ 0 ^ 2 + ξ 1 ^ 2)) ≤
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) +
        (∫⁻ ω, nuLowerErrorBound ω U ξ lam ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (lam * ((ξ 0 ^ 2 + ξ 1 ^ 2) / (U.toIntegerCube.size : ℝ) +
            9 * (|ξ 0| + |ξ 1|) ^ 2 * (1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ))))) := by
  set B := ENNReal.ofReal (lam * ((ξ 0 ^ 2 + ξ 1 ^ 2) / (U.toIntegerCube.size : ℝ) +
    9 * (|ξ 0| + |ξ 1|) ^ 2 * (1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ)))) with hB
  have hae : (fun ω : Configuration 2 =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (planarNu ω U ξ)
        else 0) + (nuLowerErrorBound ω U ξ lam + B) +
      (if PlanarPartitionEvent ω then 0 else ENNReal.ofReal (lam * (ξ 0 ^ 2 + ξ 1 ^ 2))))
      =ᵐ[latticeBondLaw 2 p] (fun ω : Configuration 2 =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (planarNu ω U ξ)
        else 0) + (nuLowerErrorBound ω U ξ lam + B)) := by
    filter_upwards [ae_planarPartitionEvent hpc] with ω hω
    rw [if_pos hω, add_zero]
  have hmF : Measurable fun ω : Configuration 2 => nuLowerErrorBound ω U ξ lam + B :=
    (measurable_nuLowerErrorBound U ξ lam).add measurable_const
  calc ENNReal.ofReal (lam * (ξ 0 ^ 2 + ξ 1 ^ 2))
      = ∫⁻ _ω, ENNReal.ofReal (lam * (ξ 0 ^ 2 + ξ 1 ^ 2)) ∂(latticeBondLaw 2 p) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) + (nuLowerErrorBound ω U ξ lam + B) +
        (if PlanarPartitionEvent ω then 0 else ENNReal.ofReal (lam * (ξ 0 ^ 2 + ξ 1 ^ 2))))
          ∂(latticeBondLaw 2 p) := lintegral_mono fun ω => ofReal_lam_le (ω := ω) U ξ hlam
    _ = ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) + (nuLowerErrorBound ω U ξ lam + B))
          ∂(latticeBondLaw 2 p) := lintegral_congr_ae hae
    _ = _ := by
        rw [lintegral_add_right _ hmF, lintegral_add_right _ measurable_const, lintegral_const,
          measure_univ, mul_one]

/-- **Expected size of the error majorant.** -/
theorem lintegral_nuLowerErrorBound_le {p : unitInterval} {c₄ c₆ : ℝ}
    (hc₆ : 0 ≤ c₆) (h4 : ∀ a, ∫⁻ ω, reachSum ω 4 a ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal c₄)
    (h6 : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal c₆)
    (U : TriadicCube 2) (ξ : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫⁻ ω, nuLowerErrorBound ω U ξ lam ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (9 * 234256 * c₄ * lam ^ 2 * (|ξ 0| + |ξ 1|) ^ 2) +
        ENNReal.ofReal (lam * (9 * 162001 * 4 * c₄) *
          ((|ξ 0| + |ξ 1|) ^ 2 / Real.sqrt (U.toIntegerCube.size : ℝ))) +
        ENNReal.ofReal (lam * c₆ * ((|ξ 0| + |ξ 1|) ^ 2 /
          Real.sqrt (U.toIntegerCube.size : ℝ))) := by
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set X := ξ 0 ^ 2 + ξ 1 ^ 2 with hX
  have hL1 : 1 ≤ L := one_le_cast_size U
  have hL0 : 0 < L := by linarith
  have hLvol : L * L = U.volume := cast_size_mul_self U
  have hvol := U.volume_pos
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsqL : Real.sqrt L ≤ L := by
    have hsq := Real.sq_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg L]
  have hXP : X ≤ P₁ ^ 2 := by
    rw [hX, hP₁]
    nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), sq_abs (ξ 0), sq_abs (ξ 1)]
  have hX0 : 0 ≤ X := by positivity
  have hcardU : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal U.volume :=
    card_toIntegerCube_vertices U
  have hcardB : ((boundaryIndex U).card : ℝ≥0∞) ≤ ENNReal.ofReal (4 * L) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_boundaryIndex_le U)
  have hm1 : Measurable fun ω : Configuration 2 =>
      ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a :=
    Finset.measurable_sum _ fun a _ => (measurable_reachSum 4 a).const_mul _
  have hm2 : Measurable fun ω : Configuration 2 => ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 :=
    Finset.measurable_sum _ fun k _ => measurable_reachSum 4 k.2.2
  have hm3 : Measurable fun ω : Configuration 2 => ∑ z ∈ U.toIntegerCube.vertices,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z :=
    Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _
  have hm12 : Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal (9 * (lam * P₁) ^ 2 / U.volume) *
        ∑ a ∈ U.toIntegerCube.vertices, 234256 * reachSum ω 4 a +
      ENNReal.ofReal (lam * 9 * P₁ ^ 2 * 162001 / (L * Real.sqrt L)) *
        ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 :=
    (hm1.const_mul _).add (hm2.const_mul _)
  have e1 : ∑ a ∈ U.toIntegerCube.vertices, ∫⁻ ω, 234256 * reachSum ω 4 a ∂(latticeBondLaw 2 p)
      ≤ ENNReal.ofReal U.volume * (234256 * ENNReal.ofReal c₄) := by
    calc _ ≤ ∑ _a ∈ U.toIntegerCube.vertices, 234256 * ENNReal.ofReal c₄ :=
          Finset.sum_le_sum fun a _ => by
            rw [lintegral_const_mul _ (measurable_reachSum 4 a)]
            exact mul_le_mul_of_nonneg_left (h4 a) zero_le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardU]
  have e2 : ∑ k ∈ boundaryIndex U, ∫⁻ ω, reachSum ω 4 k.2.2 ∂(latticeBondLaw 2 p)
      ≤ ENNReal.ofReal (4 * L) * ENNReal.ofReal c₄ := by
    calc _ ≤ ∑ _k ∈ boundaryIndex U, ENNReal.ofReal c₄ := Finset.sum_le_sum fun k _ => h4 k.2.2
      _ = ((boundaryIndex U).card : ℝ≥0∞) * ENNReal.ofReal c₄ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardB zero_le
  have e3 : ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z ∂(latticeBondLaw 2 p)
      ≤ ENNReal.ofReal U.volume *
        (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * ENNReal.ofReal c₆) := by
    calc _ ≤ ∑ _z ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * ENNReal.ofReal c₆ :=
          Finset.sum_le_sum fun z _ => by
            rw [lintegral_const_mul _ (measurable_reachSum 6 z)]
            exact mul_le_mul_of_nonneg_left (h6 z) zero_le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardU]
  have k1 : ENNReal.ofReal (9 * (lam * P₁) ^ 2 / U.volume) * (ENNReal.ofReal U.volume *
      (234256 * ENNReal.ofReal c₄)) = ENNReal.ofReal (9 * 234256 * c₄ * lam ^ 2 * P₁ ^ 2) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul hvol.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hv : U.volume ≠ 0 := hvol.ne'
    calc 9 * (lam * P₁) ^ 2 / U.volume * (U.volume * (234256 * c₄))
        = 9 * (lam * P₁) ^ 2 * (234256 * c₄) * (U.volume / U.volume) := by ring
      _ = _ := by rw [div_self hv]; ring
  have k2 : ENNReal.ofReal (lam * 9 * P₁ ^ 2 * 162001 / (L * Real.sqrt L)) *
      (ENNReal.ofReal (4 * L) * ENNReal.ofReal c₄) =
      ENNReal.ofReal (lam * (9 * 162001 * 4 * c₄) * (P₁ ^ 2 / Real.sqrt L)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hL' : L ≠ 0 := hL0.ne'
    have hs' : Real.sqrt L ≠ 0 := hsqpos.ne'
    calc lam * 9 * P₁ ^ 2 * 162001 / (L * Real.sqrt L) * (4 * L * c₄)
        = lam * (9 * 162001 * 4 * c₄) * (P₁ ^ 2 / Real.sqrt L) * (L / L) := by
          field_simp
      _ = _ := by rw [div_self hL']; ring
  have k3 : ENNReal.ofReal (lam * X) * (ENNReal.ofReal U.volume *
      (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * ENNReal.ofReal c₆)) ≤
      ENNReal.ofReal (lam * c₆ * (P₁ ^ 2 / Real.sqrt L)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hvol.le,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hv1 : U.volume * (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) ≤ 1 / Real.sqrt L := by
      rw [← hLvol, mul_one_div, div_le_div_iff₀ (by positivity) hsqpos]
      have h3 : L * L * Real.sqrt L ≤ L * L * L :=
        mul_le_mul_of_nonneg_left hsqL (by positivity)
      have h4 : L * L * L ≤ (3 : ℝ) ^ (6 * (U.scale + 1)) := by
        rw [hL]
        have hc : ((U.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ U.scale := by
          change ((3 ^ U.scale : ℕ) : ℝ) = _
          push_cast
          rfl
        rw [hc, ← pow_two, ← pow_succ, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hX' : lam * X ≤ lam * P₁ ^ 2 := mul_le_mul_of_nonneg_left hXP hlam
    calc lam * X * (U.volume * (1 / (3 : ℝ) ^ (6 * (U.scale + 1)) * c₆))
        = lam * X * (U.volume * (1 / (3 : ℝ) ^ (6 * (U.scale + 1)))) * c₆ := by ring
      _ ≤ lam * P₁ ^ 2 * (1 / Real.sqrt L) * c₆ := by gcongr
      _ = lam * c₆ * (P₁ ^ 2 / Real.sqrt L) := by ring
  unfold nuLowerErrorBound
  rw [← hP₁, ← hX, ← hL]
  rw [lintegral_add_left hm12, lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
    lintegral_const_mul _ hm2, lintegral_const_mul _ hm3,
    lintegral_finsetSum _ fun a _ => (measurable_reachSum 4 a).const_mul _,
    lintegral_finsetSum _ fun k _ => measurable_reachSum 4 k.2.2,
    lintegral_finsetSum _ fun z _ => (measurable_reachSum 6 z).const_mul _]
  calc _ ≤ ENNReal.ofReal (9 * (lam * P₁) ^ 2 / U.volume) * (ENNReal.ofReal U.volume *
          (234256 * ENNReal.ofReal c₄)) +
        ENNReal.ofReal (lam * 9 * P₁ ^ 2 * 162001 / (L * Real.sqrt L)) *
          (ENNReal.ofReal (4 * L) * ENNReal.ofReal c₄) +
        ENNReal.ofReal (lam * X) * (ENNReal.ofReal U.volume *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * ENNReal.ofReal c₆)) := by
        gcongr
    _ ≤ _ := by
        rw [k1, k2]
        exact add_le_add le_rfl k3

/-- The real-number algebra of the lower bound for `ν`. -/
theorem nu_lower_algebra {c₄ c₆ X P₁ L : ℝ} (hc₄ : 0 ≤ c₄) (hX : 0 ≤ X)
    (hXP : X ≤ P₁ ^ 2) (hPX : P₁ ^ 2 ≤ 2 * X) (hL1 : 1 ≤ L) :
    9 * 234256 * c₄ * (1 / (2 * (18 * 234256 * c₄ + 1))) ^ 2 * P₁ ^ 2 +
        1 / (2 * (18 * 234256 * c₄ + 1)) * (9 * 162001 * 4 * c₄) * (P₁ ^ 2 / Real.sqrt L) +
        1 / (2 * (18 * 234256 * c₄ + 1)) * c₆ * (P₁ ^ 2 / Real.sqrt L) +
        1 / (2 * (18 * 234256 * c₄ + 1)) * (X / L + 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L)) ≤
      (18 * 234256 * c₄ + 1) * (1 / (2 * (18 * 234256 * c₄ + 1))) ^ 2 * X +
        1 / (2 * (18 * 234256 * c₄ + 1)) * (1 + 9 / 2 + 9 * 162001 * 4 * c₄ + c₆) *
          (P₁ ^ 2 / Real.sqrt L) := by
  set K := 18 * 234256 * c₄ + 1 with hK
  set lam := 1 / (2 * K) with hlam
  have hKpos : 0 < K := by positivity
  have hlam0 : 0 < lam := by positivity
  have hL0 : 0 < L := by linarith
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsqL : Real.sqrt L ≤ L := by
    have hsq := Real.sq_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg L]
  have h1 : X / L ≤ P₁ ^ 2 / Real.sqrt L := by
    rw [div_le_div_iff₀ hL0 hsqpos]
    have := mul_le_mul hXP hsqL hsqpos.le (sq_nonneg P₁)
    linarith
  have h2 : 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L) = 9 / 2 * (P₁ ^ 2 / Real.sqrt L) := by ring
  rw [h2]
  have h3 := mul_le_mul_of_nonneg_left h1 hlam0.le
  have h4 := mul_le_mul_of_nonneg_left hPX
    (show 0 ≤ 9 * 234256 * c₄ * lam ^ 2 by positivity)
  have h5 : 0 ≤ lam ^ 2 * X := by positivity
  nlinarith

/-- **Expected lower bound for `ν`** (Armstrong and Dario, Lemma 4.7, (4.14), in expectation). -/
theorem exists_lintegral_planarNu_ge {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (ξ : Fin 2 → ℝ),
      ENNReal.ofReal (c * (ξ 0 ^ 2 + ξ 1 ^ 2)) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
            ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) +
          C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 / Real.sqrt (U.toIntegerCube.size : ℝ)) := by
  obtain ⟨C₄, hC₄, h4⟩ := exists_lintegral_tsum_ninefold_le hpc 4
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  have h4' : ∀ a, ∫⁻ ω, reachSum ω 4 a ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal C₄.toReal := by
    rw [ENNReal.ofReal_toReal hC₄]
    exact h4
  have h6' : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal C₆.toReal := by
    rw [ENNReal.ofReal_toReal hC₆]
    exact h6
  have hc₄0 : 0 ≤ C₄.toReal := ENNReal.toReal_nonneg
  have hc₆0 : 0 ≤ C₆.toReal := ENNReal.toReal_nonneg
  have hKpos : 0 < 18 * 234256 * C₄.toReal + 1 := by positivity
  have hlam0 : 0 < 1 / (2 * (18 * 234256 * C₄.toReal + 1)) := by positivity
  have hD0 : 0 ≤ 1 / (2 * (18 * 234256 * C₄.toReal + 1)) *
      (1 + 9 / 2 + 9 * 162001 * 4 * C₄.toReal + C₆.toReal) := by positivity
  refine ⟨1 / (4 * (18 * 234256 * C₄.toReal + 1)), by positivity,
    ENNReal.ofReal (1 / (2 * (18 * 234256 * C₄.toReal + 1)) *
      (1 + 9 / 2 + 9 * 162001 * 4 * C₄.toReal + C₆.toReal)), ENNReal.ofReal_ne_top,
    fun U ξ => ?_⟩
  have hint := ofReal_lam_le_lintegral hpc U ξ hlam0.le
  have hE := lintegral_nuLowerErrorBound_le hc₆0 h4' h6' U ξ hlam0.le
  have hX0 : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  have hXP : ξ 0 ^ 2 + ξ 1 ^ 2 ≤ (|ξ 0| + |ξ 1|) ^ 2 := by
    nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), sq_abs (ξ 0), sq_abs (ξ 1)]
  have hPX : (|ξ 0| + |ξ 1|) ^ 2 ≤ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
    nlinarith [sq_abs (ξ 0), sq_abs (ξ 1), sq_nonneg (|ξ 0| - |ξ 1|)]
  have halg := nu_lower_algebra (c₆ := C₆.toReal) hc₄0 hX0 hXP hPX (one_le_cast_size U)
  set K := 18 * 234256 * C₄.toReal + 1 with hK
  set lam := 1 / (2 * K) with hlam
  set X := ξ 0 ^ 2 + ξ 1 ^ 2 with hX
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  set D := lam * (1 + 9 / 2 + 9 * 162001 * 4 * C₄.toReal + C₆.toReal) with hD
  set I := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) with hI
  have ha : 0 ≤ 9 * 234256 * C₄.toReal * lam ^ 2 * P₁ ^ 2 := by positivity
  have hb : 0 ≤ lam * (9 * 162001 * 4 * C₄.toReal) * (P₁ ^ 2 / Real.sqrt L) := by positivity
  have hc : 0 ≤ lam * C₆.toReal * (P₁ ^ 2 / Real.sqrt L) := by positivity
  have hd : 0 ≤ lam * (X / L + 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L)) := by positivity
  have hq1 : 0 ≤ 1 / (4 * K) * X := by positivity
  have hq2 : 0 ≤ K * lam ^ 2 * X := by positivity
  have hDP : 0 ≤ D * (P₁ ^ 2 / Real.sqrt L) := by positivity
  have hsum : ENNReal.ofReal (lam * X) ≤ I + (ENNReal.ofReal (K * lam ^ 2 * X) +
      ENNReal.ofReal (D * (P₁ ^ 2 / Real.sqrt L))) := by
    refine hint.trans (add_le_add le_rfl ?_)
    calc ∫⁻ ω, nuLowerErrorBound ω U ξ lam ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (lam * (X / L + 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L)))
        ≤ ENNReal.ofReal (9 * 234256 * C₄.toReal * lam ^ 2 * P₁ ^ 2) +
          ENNReal.ofReal (lam * (9 * 162001 * 4 * C₄.toReal) * (P₁ ^ 2 / Real.sqrt L)) +
          ENNReal.ofReal (lam * C₆.toReal * (P₁ ^ 2 / Real.sqrt L)) +
          ENNReal.ofReal (lam * (X / L + 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L))) :=
          add_le_add hE le_rfl
      _ = ENNReal.ofReal (9 * 234256 * C₄.toReal * lam ^ 2 * P₁ ^ 2 +
          lam * (9 * 162001 * 4 * C₄.toReal) * (P₁ ^ 2 / Real.sqrt L) +
          lam * C₆.toReal * (P₁ ^ 2 / Real.sqrt L) +
          lam * (X / L + 9 * P₁ ^ 2 * (1 / 2 / Real.sqrt L))) := by
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) hc) hd,
            ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb]
      _ ≤ ENNReal.ofReal (K * lam ^ 2 * X + D * (P₁ ^ 2 / Real.sqrt L)) :=
          ENNReal.ofReal_le_ofReal halg
      _ = _ := ENNReal.ofReal_add hq2 hDP
  have hsplit : ENNReal.ofReal (lam * X) =
      ENNReal.ofReal (1 / (4 * K) * X) + ENNReal.ofReal (K * lam ^ 2 * X) := by
    rw [(ENNReal.ofReal_add hq1 hq2).symm]
    congr 1
    rw [hlam]
    have hK0 : K ≠ 0 := hKpos.ne'
    calc 1 / (2 * K) * X = (1 / (4 * K) + K * (1 / (2 * K)) ^ 2) * X := by
          congr 1
          field_simp
          ring
      _ = _ := by ring
  rw [hsplit, add_comm (ENNReal.ofReal (K * lam ^ 2 * X)), ← add_assoc] at hsum
  have hfin := (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hsum
  refine hfin.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity)]

end Rigidity.Percolation
