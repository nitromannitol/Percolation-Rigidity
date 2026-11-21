import Rigidity.Proofs.Percolation.PlanarNuLocal
import Rigidity.Proofs.Percolation.PlanarMuStationarity

/-!
# The local version of `μ` in the plane

On the event that the partition exists and agrees with the capped partition on `V`, the local
data of the partition at `V` determine the cluster `C_*(V)`, its open edges and the coarse anchors
of the vertices of `V`, hence `1{V res} (-μ(V, q))`. The local version `μ_loc(V, q)` is its value
at any configuration of this event with the same local data; it is measurable for the σ-algebra of
the bonds near `V`, so that local versions on cubes with disjoint neighbourhoods are independent.

Since each coarse weight is at most the number `2 |V|` of lattice edges of `V`,
`-μ(V, q) ≤ 36 |q|₁² |V|²` on resolved cubes. Hence the local version agrees with
`1{P, V res} (-μ(V, q))` outside an event of probability at most `C exp (-c 3ⁿ)`, and the
expectations differ by at most `C |q|₁² exp (-c 3ⁿ / 2)`. This is the planar form of Armstrong and
Dario, (4.39) and Proposition 4.10, for `μ`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- A deterministic bound for `-μ` on resolved cubes: `-μ(U, q) ≤ 36 |q|₁² |U|²`. -/
theorem neg_planarMu_le_volume_sq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    -planarMu ω U q ≤ 36 * (|q 0| + |q 1|) ^ 2 * U.volume ^ 2 := by
  have h := neg_planarMu_le hP hU q
  have hvol := U.volume_pos
  have hcw : ∀ a, coarseWeight ω U a ≤ 2 * U.volume := by
    intro a
    refine (Finset.sum_le_card_nsmul _ _ 1 fun k _ => by split_ifs <;> norm_num).trans ?_
    rw [nsmul_eq_mul, mul_one]
    exact card_latticeEdgesIn_le U
  have hcard : (Fintype.card ↥(clusterVertices ω U) : ℝ) ≤ U.volume := by
    rw [Fintype.card_coe, show U.volume = ((U.toIntegerCube.vertices.card : ℕ) : ℝ) from
      (card_toIntegerCube_vertices_eq U).symm]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsum : ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2 ≤
      U.volume * (2 * U.volume) ^ 2 := by
    calc ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2
        ≤ ∑ _x : ↥(clusterVertices ω U), (2 * U.volume) ^ 2 :=
          Finset.sum_le_sum fun x _ =>
            pow_le_pow_left₀ (coarseWeight_nonneg U x.1) (hcw x.1) 2
      _ = (Fintype.card ↥(clusterVertices ω U) : ℝ) * (2 * U.volume) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ U.volume * (2 * U.volume) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  calc -planarMu ω U q ≤ _ := h
    _ ≤ 9 * (|q 0| + |q 1|) ^ 2 * (U.volume * (2 * U.volume) ^ 2) / U.volume := by
        gcongr
    _ = 36 * (|q 0| + |q 1|) ^ 2 * U.volume ^ 2 := by
        field_simp
        ring

/-- The value of `1{P, V res} (-μ(V, q))` at a configuration of the good event with given local
data. -/
noncomputable def planarMuLocOf (V : TriadicCube 2) (q : Fin 2 → ℝ) (t : PlanarLocalDatum V) :
    ℝ≥0∞ :=
  if h : ∃ ω, PlanarLocalGood ω V ∧ planarLocalData ω V = t then
    (if PlanarPartitionEvent h.choose ∧ PlanarResolved h.choose V then
      ENNReal.ofReal (-planarMu h.choose V q) else 0)
  else 0

/-- **The local version of `-μ`.** -/
noncomputable def planarMuLoc (V : TriadicCube 2) (q : Fin 2 → ℝ) (ω : Configuration 2) :
    ℝ≥0∞ :=
  planarMuLocOf V q (planarLocalData ω V)

/-- On the good event, the local data determine `1{P, V res} (-μ(V, q))`. -/
theorem planarMu_indicator_eq_of_planarLocalData_eq {V : TriadicCube 2}
    (hω : PlanarLocalGood ω V) (hω' : PlanarLocalGood ω' V)
    (h : planarLocalData ω V = planarLocalData ω' V) (q : Fin 2 → ℝ) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (-planarMu ω V q)
      else 0) =
      if PlanarPartitionEvent ω' ∧ PlanarResolved ω' V then
        ENNReal.ofReal (-planarMu ω' V q) else 0 := by
  obtain ⟨hres, hC, hadj, hanc⟩ := planarLocalData_eq_imp hω hω' h
  by_cases hr : PlanarResolved ω V
  · rw [if_pos ⟨hω.1, hr⟩, if_pos ⟨hω'.1, hres.1 hr⟩]
    congr 2
    exact (planarMu_eq_of_cluster_anchor_eq hC (fun x hx y hy =>
      hadj x (mem_clusterVertices.1 hx).1 y (mem_clusterVertices.1 hy).1) hanc q).symm
  · rw [if_neg fun h' => hr h'.2, if_neg fun h' => hr (hres.2 h'.2)]

/-- **Agreement with `μ`.** -/
theorem planarMuLoc_eq_of_good {V : TriadicCube 2} (hω : PlanarLocalGood ω V)
    (q : Fin 2 → ℝ) :
    planarMuLoc V q ω = if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (-planarMu ω V q) else 0 := by
  have hex : ∃ ω', PlanarLocalGood ω' V ∧ planarLocalData ω' V = planarLocalData ω V :=
    ⟨ω, hω, rfl⟩
  unfold planarMuLoc planarMuLocOf
  rw [dif_pos hex]
  exact planarMu_indicator_eq_of_planarLocalData_eq hex.choose_spec.1 hω hex.choose_spec.2 q

theorem planarMu_indicator_le (V : TriadicCube 2) (q : Fin 2 → ℝ) (ω : Configuration 2) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (-planarMu ω V q)
      else 0) ≤ ENNReal.ofReal (36 * (|q 0| + |q 1|) ^ 2 * V.volume ^ 2) := by
  split_ifs with h
  · exact ENNReal.ofReal_le_ofReal (neg_planarMu_le_volume_sq h.1 h.2 q)
  · exact zero_le

theorem planarMuLoc_le (V : TriadicCube 2) (q : Fin 2 → ℝ) (ω : Configuration 2) :
    planarMuLoc V q ω ≤ ENNReal.ofReal (36 * (|q 0| + |q 1|) ^ 2 * V.volume ^ 2) := by
  unfold planarMuLoc planarMuLocOf
  split
  · exact planarMu_indicator_le V q _
  · exact zero_le

/-- The local version of `-μ` is measurable. -/
theorem measurable_planarMuLoc (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable (planarMuLoc V q) :=
  measurable_of_fiber_const (fun ω => planarLocalData ω V)
    (fun t => measurableSet_planarLocalData_eq V t) fun _ _ h =>
      congrArg (planarMuLocOf V q) h

/-- **Locality of `μ_loc`** (planar form of Armstrong and Dario, (4.39), for `μ`). -/
theorem measurable_planarMuLoc_localBondSigma (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable[localBondSigma V.planarLocalRegion] (planarMuLoc V q) :=
  measurable_localBondSigma_of_eq _ (measurable_planarMuLoc V q) fun _ _ h =>
    congrArg (planarMuLocOf V q) (planarLocalData_eq_of_localBonds h).symm

/-- **Independence of local versions of `μ`.** -/
theorem indepFun_planarMuLoc (p : unitInterval) {V W : TriadicCube 2}
    (hVW : Disjoint V.planarLocalRegion W.planarLocalRegion) (q r : Fin 2 → ℝ) :
    IndepFun (planarMuLoc V q) (planarMuLoc W r) (latticeBondLaw 2 p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_planarMuLoc_localBondSigma V q).comap_le)
    (measurable_planarMuLoc_localBondSigma W r).comap_le)

/-- **Localization of `μ`** (planar form of Armstrong and Dario, Proposition 4.10, for `μ`). The
expectations of the local version and of `1{P, V res} (-μ(V, q))` differ by at most
`C |q|₁² exp (-c 3ⁿ)`. -/
theorem exists_planarMuLoc_localization {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube 2) (q : Fin 2 → ℝ),
      ∫⁻ ω, planarMuLoc V q ω ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) ∧
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, planarMuLoc V q ω ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hloc⟩ := exists_planarNuLoc_localization hpc
  set M : ℝ := (max 1 (2 * ((4 : ℕ) + 1) / c)) ^ 4 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨36 * ENNReal.ofReal M * C, by finiteness, c / 2, by positivity, fun V q => ?_⟩
  have hbad := (hloc V 0).1
  set B := {ω : Configuration 2 | ¬ PlanarLocalGood ω V}
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set K : ℝ≥0∞ := ENNReal.ofReal (36 * s * V.volume ^ 2) with hK
  have hpoly : (V.volume : ℝ) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
      M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale) := by
    have h3 : (0 : ℝ) ≤ 3 ^ V.scale := by positivity
    have h9 : (9 : ℝ) ^ V.scale = ((3 : ℝ) ^ V.scale) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hv : (V.volume : ℝ) ^ 2 = ((3 : ℝ) ^ V.scale) ^ 4 := by
      change ((9 : ℝ) ^ V.scale) ^ 2 = _
      rw [h9]
      ring
    have hle : ((3 : ℝ) ^ V.scale) ^ 4 ≤ ((3 : ℝ) ^ V.scale + 1) ^ 4 :=
      pow_le_pow_left₀ h3 (by linarith) 4
    have h := add_one_pow_mul_exp_neg_le 4 hc h3
    rw [hv]
    calc ((3 : ℝ) ^ V.scale) ^ 4 * Real.exp (-c * (3 : ℝ) ^ V.scale)
        ≤ ((3 : ℝ) ^ V.scale + 1) ^ 4 * Real.exp (-(c * (3 : ℝ) ^ V.scale)) := by
          rw [neg_mul]
          exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale) := by
          rw [show -(c / 2) * (3 : ℝ) ^ V.scale = -(c / 2 * 3 ^ V.scale) by ring]
          exact h
  have hKe : K * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) ≤
      36 * ENNReal.ofReal M * C *
        ENNReal.ofReal (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
    rw [hK, mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    have hAB : 36 * s * V.volume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
        36 * s * (M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
      calc 36 * s * V.volume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)
          = 36 * s * (V.volume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)
    calc C * ENNReal.ofReal (36 * s * V.volume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale))
        ≤ C * ENNReal.ofReal (36 * s * (M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hAB)
      _ = _ := by
          rw [show 36 * s * (M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) =
              36 * (M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale))) by ring,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hM0, ENNReal.ofReal_ofNat]
          ring
  have hf := measurable_planarMu_indicator V q
  have hl := measurable_planarMuLoc V q
  refine ⟨?_, ?_⟩
  · calc ∫⁻ ω, planarMuLoc V q ω ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) + B.indicator (fun _ => K) ω)
            ∂(latticeBondLaw 2 p) := lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (planarMuLoc_le V q ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (planarMuLoc_eq_of_good hω q).le
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw 2 p) :=
          lintegral_add_left hf _
      _ ≤ _ := add_le_add le_rfl (((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl hbad)).trans hKe)
  · calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ ω, (planarMuLoc V q ω + B.indicator (fun _ => K) ω) ∂(latticeBondLaw 2 p) :=
          lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (planarMu_indicator_le V q ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (planarMuLoc_eq_of_good hω q).ge
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw 2 p) :=
          lintegral_add_left hl _
      _ ≤ _ := add_le_add le_rfl (((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl hbad)).trans hKe)

end Rigidity.Percolation
