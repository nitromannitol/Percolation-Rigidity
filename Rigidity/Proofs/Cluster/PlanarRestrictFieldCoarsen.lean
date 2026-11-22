import Rigidity.Proofs.Cluster.PlanarRestrictField
import Rigidity.Proofs.Cluster.PlanarRestrictQuadGehring

/-!
# Lemma 5.5 of Armstrong and Dario for the pairings with a bounded field

For a lattice field `g` with `|g| ≤ G`, the expectation of the quantity
`N⁻¹ ∑_V (⟨∇[u(·, U, q)]_𝒫, g⟩_V - ⟨∇[u(·, V, q)]_𝒫, g⟩_V)² / |V|²` is at most
`C G² |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})` for `n ∈ [9m/10, m)`, from the partition for the reverse
Hölder inequality (`exists_lintegral_planarMuRestrictFieldError_le`). The proof is that of
`planarRestrictQuadCoarsenMu_of_inputs`: off the bad event the bound
`planarMuRestrictFieldError_le_of_not_mem_restrictBad` and Lemma 5.4 on every cube; on the bad
event the Cauchy–Schwarz inequality with the majorant `2 G² M`, where `M` is the measurable majorant
of the energies (`|⟨∇f, g⟩_V|² ≤ 2 G² |V| ∑_{edges of V} |∇f|²`, `sq_edgePairing_le`). This is the
estimate of Lemma 5.5 used in Step 3 of the proof of Lemma 5.7.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- **Cauchy–Schwarz for the pairing with a bounded field.** -/
theorem sq_edgePairing_le (D : Finset (Vertex 2)) {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) (f : Vertex 2 → ℝ) :
    edgePairing D g f ^ 2 ≤ G ^ 2 * (2 * D.card) * edgeEnergy D f := by
  set c : Vertex 2 × Fin 2 → ℝ := fun e =>
    if e.1 + unitVertex e.2 ∈ D then g e.1 e.2 * (f (e.1 + unitVertex e.2) - f e.1) else 0 with hc
  have h1 : edgePairing D g f = ∑ e ∈ D ×ˢ (Finset.univ : Finset (Fin 2)), c e := by
    rw [Finset.sum_product]
    rfl
  have h2 : edgeEnergy D f = ∑ e ∈ D ×ˢ (Finset.univ : Finset (Fin 2)),
      (if e.1 + unitVertex e.2 ∈ D then (f (e.1 + unitVertex e.2) - f e.1) ^ 2 else 0) := by
    rw [Finset.sum_product]
    rfl
  have hcard : ((D ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) = 2 * D.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  have hCS := sq_sum_le_card_mul_sum_sq (s := D ×ˢ (Finset.univ : Finset (Fin 2))) (f := c)
  rw [h1, h2]
  refine hCS.trans ?_
  rw [hcard, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  simp only [hc]
  split_ifs
  · have hg2 : g e.1 e.2 ^ 2 ≤ G ^ 2 := by
      have := abs_le.1 (hg e.1 e.2)
      nlinarith [abs_nonneg (g e.1 e.2), sq_abs (g e.1 e.2)]
    have hD : (0 : ℝ) ≤ 2 * D.card := by positivity
    have hΔ := sq_nonneg (f (e.1 + unitVertex e.2) - f e.1)
    calc 2 * (D.card : ℝ) * (g e.1 e.2 * (f (e.1 + unitVertex e.2) - f e.1)) ^ 2
        = 2 * D.card * (g e.1 e.2 ^ 2 * (f (e.1 + unitVertex e.2) - f e.1) ^ 2) := by ring
      _ ≤ 2 * D.card * (G ^ 2 * (f (e.1 + unitVertex e.2) - f e.1) ^ 2) := by gcongr
      _ = G ^ 2 * (2 * D.card) * (f (e.1 + unitVertex e.2) - f e.1) ^ 2 := by ring
  · simp

/-- **The quantity with a field by the energies.** -/
theorem restrictFieldError_le_energy {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (fU : Vertex 2 → ℝ) (fV : TriadicCube 2 → Vertex 2 → ℝ) {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) :
    ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n,
        ((edgePairing V.toIntegerCube.vertices g fU -
          edgePairing V.toIntegerCube.vertices g (fV V)) / V.volume) ^ 2 ≤
      2 * G ^ 2 * (4 / U.volume * (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 +
        ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2)) := by
  have hN := card_subcubesAt_mul hn
  have hvolU := U.volume_pos
  have hNpos : (0 : ℝ) < (subcubesAt U n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (subcubesAt U n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
  have hterm : ∀ V ∈ subcubesAt U n,
      ((edgePairing V.toIntegerCube.vertices g fU -
        edgePairing V.toIntegerCube.vertices g (fV V)) / V.volume) ^ 2 ≤
      4 * G ^ 2 / 9 ^ n * (edgeEnergy V.toIntegerCube.vertices fU +
        edgeEnergy V.toIntegerCube.vertices (fV V)) := by
    intro V hV
    have hVs : V.scale = n := scale_of_mem_subcubesAt hV
    have hvol : V.volume = (9 : ℝ) ^ n := by rw [TriadicCube.volume, hVs]
    have hcard : (V.toIntegerCube.vertices.card : ℝ) = 9 ^ n := by
      rw [card_toIntegerCube_vertices_eq, hVs]
    have h1 := sq_edgePairing_le V.toIntegerCube.vertices hg fU
    have h2 := sq_edgePairing_le V.toIntegerCube.vertices hg (fV V)
    rw [hcard] at h1 h2
    set a := edgePairing V.toIntegerCube.vertices g fU
    set b := edgePairing V.toIntegerCube.vertices g (fV V)
    have h9 : (0 : ℝ) < 9 ^ n := by positivity
    rw [div_pow, hvol, div_le_iff₀ (by positivity)]
    have hab : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a + b)]
    have e : 4 * G ^ 2 / 9 ^ n * (edgeEnergy V.toIntegerCube.vertices fU +
        edgeEnergy V.toIntegerCube.vertices (fV V)) * ((9 : ℝ) ^ n) ^ 2 =
        2 * (G ^ 2 * (2 * 9 ^ n) * edgeEnergy V.toIntegerCube.vertices fU +
          G ^ 2 * (2 * 9 ^ n) * edgeEnergy V.toIntegerCube.vertices (fV V)) := by
      field_simp
      ring
    rw [e]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hU := sum_edgeEnergy_subcubes_le hn fU
  have hEU := edgeEnergy_le_two_mul_sum_gradNormIn_sq U.toIntegerCube.vertices fU
  have hEV : ∑ V ∈ subcubesAt U n, edgeEnergy V.toIntegerCube.vertices (fV V) ≤
      2 * ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun V _ => edgeEnergy_le_two_mul_sum_gradNormIn_sq _ _
  set A := ∑ x ∈ U.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 with hA
  set B := ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 with hB
  have hstep : ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n,
        ((edgePairing V.toIntegerCube.vertices g fU -
          edgePairing V.toIntegerCube.vertices g (fV V)) / V.volume) ^ 2 ≤
      ((subcubesAt U n).card : ℝ)⁻¹ * (4 * G ^ 2 / 9 ^ n * (2 * A + 2 * B)) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (inv_nonneg.2 hNpos.le)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  refine hstep.trans (le_of_eq ?_)
  rw [← hN]
  field_simp

/-- The energies of the coarsened functions by the majorant (the second step of
`ofReal_restrictError_le_majorant`). -/
theorem ofReal_energy_sum_le_majorant {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (fU : Vertex 2 → ℝ) (fV : TriadicCube 2 → Vertex 2 → ℝ) (c : ℝ≥0∞)
    (hU : ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2) ≤
      c * (U.toIntegerCube.vertices.card : ℝ≥0∞) *
        (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)))
    (hV : ∀ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤
      c * (V.toIntegerCube.vertices.card : ℝ≥0∞) *
        (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ))) :
    ENNReal.ofReal (4 / U.volume * (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 +
        ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2)) ≤
      8 * c * (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) := by
  set X := (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) with hX
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have hvol := U.volume_pos
  have hNvol : ((U.toIntegerCube.vertices.card : ℕ) : ℝ) = U.volume := (volume_eq_card U).symm
  have hA0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : ∀ V ∈ subcubesAt U n, 0 ≤ ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 :=
    fun V _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.ofReal_mul (div_nonneg (by norm_num) hvol.le),
    ENNReal.ofReal_add hA0 (Finset.sum_nonneg hB0),
    ENNReal.ofReal_sum_of_nonneg hB0]
  have hVX : ∀ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤
      c * (V.toIntegerCube.vertices.card : ℝ≥0∞) * X := fun V hV' =>
    (hV V hV').trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow
      (sum_reachSum_subcube_le hn hV' _) (by positivity)) zero_le)
  have hsumV : ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤ c * N * X := by
    calc ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2)
        ≤ ∑ V ∈ subcubesAt U n, c * (V.toIntegerCube.vertices.card : ℝ≥0∞) * X :=
          Finset.sum_le_sum hVX
      _ = c * N * X := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sum_card_subcubes hn]
  have h4 : ENNReal.ofReal (4 / U.volume) * N = 4 := by
    rw [hNdef, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg (by norm_num) hvol.le),
      hNvol,
      div_mul_cancel₀ _ hvol.ne']
    simp
  calc ENNReal.ofReal (4 / U.volume) * (ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2) +
        ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2))
      ≤ ENNReal.ofReal (4 / U.volume) * (c * N * X + c * N * X) := by gcongr
    _ = 2 * (ENNReal.ofReal (4 / U.volume) * N) * c * X := by ring
    _ = 8 * c * X := by
        rw [h4]
        ring


/-- **A measurable majorant of the quantity with a field.** -/
theorem exists_planarMuRestrictFieldError_majorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ (g : Vertex 2 → Fin 2 → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) → ∀ ω,
          ENNReal.ofReal (planarMuRestrictFieldError ω U n q g) ≤
            ENNReal.ofReal (2 * G ^ 2) * M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p) ≤
          C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ) := by
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * 3)
  refine ⟨(8 * energyConst * 18) ^ 2 * CT ^ (2 / 3 : ℝ), ?_, fun U n hn q => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (by norm_num) energyConst_ne_top) (by norm_num)))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCT)
  set c : ℝ≥0∞ := energyConst * ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) with hc
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) with hXdef
  have hXm : Measurable X :=
    (Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * 3) z).pow_const _
  refine ⟨fun ω => 8 * c * X ω, hXm.const_mul _, fun g G hg ω => ?_, ?_⟩
  · have h1 := restrictFieldError_le_energy hn (coarsen ω U (planarMuMinimizer ω U q))
      (fun V => coarsen ω V (planarMuMinimizer ω V q)) hg
    have h2 := ofReal_energy_sum_le_majorant (ω := ω) hn
      (coarsen ω U (planarMuMinimizer ω U q)) (fun V => coarsen ω V (planarMuMinimizer ω V q)) c
      (ofReal_energy_planarMuMinimizer_le U q)
      (fun V _ => ofReal_energy_planarMuMinimizer_le V q)
    have hG2 : 0 ≤ 2 * G ^ 2 := by positivity
    calc ENNReal.ofReal (planarMuRestrictFieldError ω U n q g)
        ≤ ENNReal.ofReal (2 * G ^ 2 * (4 / U.volume * (∑ x ∈ U.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
              (coarsen ω U (planarMuMinimizer ω U q)) x ^ 2 +
          ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (coarsen ω V (planarMuMinimizer ω V q)) x ^ 2))) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (2 * G ^ 2) * ENNReal.ofReal (4 / U.volume *
          (∑ x ∈ U.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
              (coarsen ω U (planarMuMinimizer ω U q)) x ^ 2 +
          ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (coarsen ω V (planarMuMinimizer ω V q)) x ^ 2)) := ENNReal.ofReal_mul hG2
      _ ≤ ENNReal.ofReal (2 * G ^ 2) * (8 * c * X ω) :=
          mul_le_mul_of_nonneg_left h2 zero_le
  · have hpt : ∀ ω, (8 * c * X ω) ^ 2 = (8 * c) ^ 2 * X ω ^ 2 := fun ω => by ring
    simp only [hpt]
    rw [lintegral_const_mul _ (hXm.pow_const 2)]
    have hJ := lintegral_reachSum_rpow_le (latticeBondLaw 2 p) U
    have hEX : ∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p) ≤
        (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
      rw [lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * 3) z]
      calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p)
          ≤ ∑ _z ∈ U.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
        _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (8 * c) ^ 2 * ∫⁻ ω, X ω ^ 2 ∂(latticeBondLaw 2 p)
        ≤ (8 * c) ^ 2 * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (2 / 3 : ℝ) := by
          gcongr
          exact hJ.trans (ENNReal.rpow_le_rpow hEX (by norm_num))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hc,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
          simp only [ENNReal.ofReal_ofNat]
          ring

end Rigidity.Proofs.Cluster
