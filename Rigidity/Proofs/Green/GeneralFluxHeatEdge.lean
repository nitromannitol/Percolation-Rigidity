import Rigidity.Proofs.Green.GeneralFluxSpatialAverage
import Rigidity.Proofs.Green.GeneralFluxBox
import Rigidity.Proofs.Corrector.GeneralStepTwoDefs
import Rigidity.Proofs.Corrector.GeneralCaseHeatField
import Rigidity.Proofs.Corrector.GeneralFlipTerms
import Rigidity.Proofs.Corrector.GeneralLemmaThreeTwoProof
import Rigidity.Proofs.Corrector.GeneralCellEnergy

/-!
# The flux of the corrected planes of `ℤ^d` along the edges and the heat field of the edges

The parts of `DarioGuFluxFlip.lean`, `DarioGuFluxHeat.lean`, `DarioGuFluxObservable.lean`,
`DarioGuFluxPairing.lean` and `DarioGuFluxPartition.lean` that do not involve Step 2 of the proof
of Lemma 3.3 of Dario (*Optimal corrector estimates on percolation clusters*), extended from `ℤ²`
to `ℤ^d`. They serve the variance bound (3.4) of Gu's proof of his Proposition 1.1
(*An efficient algorithm for solving elliptic problems on percolation clusters*).

* `planeFluxD C ℓ b = (ℓ(z + e_i) - ℓ(z)) 1{b ∈ E(C)}`, the flux of `ℓ` along the oriented edge
  `b = (z, i)` (planar `planeFlux`); the measurable flux `fluxValD` is the flux of the corrected
  plane (`fluxValD_eq_planeFluxD`), and the flip difference of the heat average `fluxObsD` of the
  flux across a bond `e` is the difference of the heat averages of the fluxes of corrected planes of
  `ω^{e,1}` and `ω^{e,0}` (`bondFlipDiff_fluxObsD_eq`, planar `bondFlipDiff_fluxObs_eq`, stated
  there for the bond of an oriented edge). The heat average of the flux of a corrected plane
  converges (`summable_heat_planeFluxD`).
* The heat field `heatEdgeD ω r x i = Σ_z Φ_{r²}(x, z) 1_{(z, i)}` over the open edges whose tail
  lies in an infinite component (planar `heatEdge`), with `Φ` the heat kernel of `ℤ^d`; its pairing
  is the heat average along these edges (`inner_heatEdgeD`) and its value at an edge is
  `Φ_{r²}(x, z)` or `0` (`heatEdgeD_apply`).
* `fluxFlipSumD = Σ_e (D_e X)²` (planar `fluxFlipSum`).
* `tsum_weight_openEnergy_heatD_le` (planar `tsum_weight_openEnergy_heat_le`): for a partition into
  cells with comparable neighbours carrying the Meyers estimate on their children and a weight with
  `Σ_T W^q ≤ M |T|`, `Σ_u W(u) E_v(u) ≤ 3 K Σ_y Φ_{r²}(x, y)² ((3^d)^{n(y)})^{1 - 1/(1 + ε/2)}`;
  the constant is `K = M^{1/q'} + 3 · 4^d cellConst(ε, C_M, 3^d M)` and the cells have `3^d`
  children in place of the planar `48 cellConst(ε, C_M, 9M)` and `9^{n(y)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External Rigidity.Corrector.GeneralDim
open Rigidity.Corrector (correctorDiff correctorDiff_eq)
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)
open scoped Classical ENNReal InnerProductSpace

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

/-! ### The flux along the edges and the heat field -/

/-- The flux of `ℓ` along the oriented edge `b`: `(ℓ(edgeHead b) - ℓ(b.1)) 1{b open, b.1 ∈ C}`
(planar: `Rigidity.Green.planeFlux`). -/
noncomputable def planeFluxD {ω : Configuration d} (C : OpenComponent ω) (ℓ : C → ℝ)
    (b : LatticeEdge d) : ℝ :=
  if EdgeOpen ω b ∧ b.1 ∈ C.supp then extendComp C ℓ (edgeHead b) - extendComp C ℓ b.1 else 0

/-- The unit field of the edge `(z, i)` when it is open with its tail in an infinite component
(planar: `Rigidity.Green.heatEdgeTerm`). -/
noncomputable def heatEdgeTermD (ω : Configuration d) (i : Fin d) (z : Vertex d) : EdgeField d :=
  if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then lp.single 2 (z, i) (1 : ℝ) else 0

/-- **The heat field** `Σ_z Φ_{r²}(x, z) 1_{(z, i)}` over the open edges of the infinite components
(planar: `Rigidity.Green.heatEdge`). -/
noncomputable def heatEdgeD (ω : Configuration d) (r : ℝ) (x : Vertex d) (i : Fin d) :
    EdgeField d :=
  ∑' z, zdHeat d (r ^ 2) x z • heatEdgeTermD ω i z

/-- The sum over the bonds of the squared flip differences of the heat average of the flux
(planar: `Rigidity.Green.fluxFlipSum`). -/
noncomputable def fluxFlipSumD {G : Set (Configuration d)} (hG : MeasurableSet G)
    (hGv : G ⊆ correctorValidEvent d) (k i : Fin d) (r : ℝ) (x : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' e : Bond d, ENNReal.ofReal (bondFlipDiff (fluxObsD hG hGv k i r x) e ω ^ 2)

/-! ### The flip difference of the heat average of the flux -/

section Observable

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The measurable flux is the flux of the corrected plane** (planar: `fluxVal_eq_planeFlux`). -/
theorem fluxValD_eq_planeFluxD {k : Fin d} {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single k 1) ℓ) (z : Vertex d)
    (i : Fin d) :
    fluxValD hG hGv k ω z i = planeFluxD (uniqueInfiniteComponent h) ℓ (z, i) := by
  unfold fluxValD planeFluxD
  have e : ((openGraph ω).Adj z (z + unit i) ∧ ω ∈ infiniteComponentEvent z) ↔
      (EdgeOpen ω (z, i) ∧ z ∈ (uniqueInfiniteComponent h).supp) :=
    and_congr_right fun _ => (mem_uniqueInfiniteComponent_iff h z).symm
  by_cases hc : EdgeOpen ω (z, i) ∧ z ∈ (uniqueInfiniteComponent h).supp
  · rw [if_pos (e.2 hc), if_pos hc]
    have hy : z + unit i ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hc.2 hc.1
    rw [correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨z + unit i, hy⟩
      ⟨z, hc.2⟩]
    rw [show edgeHead ((z, i) : LatticeEdge d) = z + unit i from rfl,
      extendComp_of_mem _ _ hy, extendComp_of_mem _ _ hc.2]
    have hs := sum_single_mul_add_unit_sub k i z
    linarith
  · rw [if_neg (fun h' => hc (e.1 h')), if_neg hc]

/-- The heat average of the flux through a corrected plane (planar: `fluxObs_eq`). -/
theorem fluxObsD_eq_planeFluxD {k : Fin d} {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single k 1) ℓ) (i : Fin d) (r : ℝ)
    (x : Vertex d) :
    fluxObsD hG hGv k i r x ω =
      ∑' z, zdHeat d (r ^ 2) x z * planeFluxD (uniqueInfiniteComponent h) ℓ (z, i) := by
  unfold fluxObsD
  exact tsum_congr fun z => by rw [fluxValD_eq_planeFluxD hG hGv hω h hℓ]

end Observable

/-- **The flip difference of the heat average of the flux** (planar: `bondFlipDiff_fluxObs_eq`):
if `ω^{e,1}, ω^{e,0} ∈ G`, it is the difference of the heat averages of the fluxes of corrected
planes of slope `e_k` of `ω^{e,1}` and `ω^{e,0}`. The planar statement is for the bond of an
oriented edge. -/
theorem bondFlipDiff_fluxObsD_eq {G : Set (Configuration d)} (hG : MeasurableSet G)
    (hGv : G ⊆ correctorValidEvent d) {k : Fin d} {e : Bond d} {ω : Configuration d}
    (h1G : setBond e true ω ∈ G) (h0G : setBond e false ω ∈ G)
    (h₁ : HasUniqueInfiniteOpenComponent (setBond e true ω))
    (h₀ : HasUniqueInfiniteOpenComponent (setBond e false ω))
    {ℓ₁ : uniqueInfiniteComponent h₁ → ℝ} {ℓ₀ : uniqueInfiniteComponent h₀ → ℝ}
    (hℓ₁ : IsCorrectedPlane (uniqueInfiniteComponent h₁) (Pi.single k 1) ℓ₁)
    (hℓ₀ : IsCorrectedPlane (uniqueInfiniteComponent h₀) (Pi.single k 1) ℓ₀) (i : Fin d) (r : ℝ)
    (x : Vertex d) :
    bondFlipDiff (fluxObsD hG hGv k i r x) e ω =
      (∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₁ (z, i)) -
        ∑' z, zdHeat d (r ^ 2) x z * planeFluxD _ ℓ₀ (z, i) := by
  unfold bondFlipDiff
  rw [fluxObsD_eq_planeFluxD hG hGv h1G h₁ hℓ₁, fluxObsD_eq_planeFluxD hG hGv h0G h₀ hℓ₀]

/-! ### Heat averages of the flux of the corrected planes -/

/-- **The flux of a corrected plane grows at most linearly** (planar: `exists_abs_planeFlux_le`). -/
theorem exists_abs_planeFluxD_le {ω : Configuration d} {C : OpenComponent ω}
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (i : Fin d) :
    ∃ A : ℝ, ∀ z : Vertex d,
      |planeFluxD C ℓ (z, i)| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖) := by
  obtain ⟨B, hB, hBℓ⟩ := exists_abs_le_of_isCorrectedPlaneD hℓ
  refine ⟨3 * B, fun z => ?_⟩
  have hext : ∀ w : Vertex d, |extendComp C ℓ w| ≤ B * (1 + ‖latticeEuclideanEmbedding w‖) := by
    intro w
    by_cases hw : w ∈ C.supp
    · rw [extendComp_of_mem _ _ hw]
      exact hBℓ ⟨w, hw⟩
    · rw [extendComp_of_not_mem _ _ hw, abs_zero]
      positivity
  have hhead : ‖latticeEuclideanEmbedding (edgeHead ((z, i) : LatticeEdge d))‖ ≤
      ‖latticeEuclideanEmbedding z‖ + 1 :=
    norm_latticeEuclideanEmbedding_add_unit_le z i
  unfold planeFluxD
  split_ifs
  · calc |extendComp C ℓ (edgeHead (z, i)) - extendComp C ℓ (z, i).1|
        ≤ |extendComp C ℓ (edgeHead (z, i))| + |extendComp C ℓ z| := by
          have := abs_add_le (extendComp C ℓ (edgeHead (z, i))) (-extendComp C ℓ z)
          rwa [abs_neg, ← sub_eq_add_neg] at this
      _ ≤ B * (1 + ‖latticeEuclideanEmbedding (edgeHead ((z, i) : LatticeEdge d))‖) +
          B * (1 + ‖latticeEuclideanEmbedding z‖) := add_le_add (hext _) (hext _)
      _ ≤ 3 * B * (1 + ‖latticeEuclideanEmbedding z‖) := by
          nlinarith [norm_nonneg (latticeEuclideanEmbedding z)]
  · rw [abs_zero]
    positivity

/-! ### The heat field of the edges -/

variable [NeZero d]

/-- **The heat average of the flux of a corrected plane converges** (planar:
`summable_heat_planeFlux`). -/
theorem summable_heat_planeFluxD {ω : Configuration d} {C : OpenComponent ω}
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (i : Fin d) (r : ℝ)
    (x : Vertex d) :
    Summable fun z => zdHeat d (r ^ 2) x z * planeFluxD C ℓ (z, i) := by
  obtain ⟨A, hA⟩ := exists_abs_planeFluxD_le hℓ i
  exact summable_zdHeat_mul_of_abs_le (sq_nonneg r) x hA

section HeatEdge

variable (ω : Configuration d) (r : ℝ) (x : Vertex d) (i : Fin d)

omit [NeZero d] in
theorem norm_heatEdgeTermD_le (z : Vertex d) : ‖heatEdgeTermD ω i z‖ ≤ 1 := by
  unfold heatEdgeTermD
  split_ifs
  · rw [lp.norm_single (by norm_num)]
    simp
  · simp

theorem summable_heatEdgeD :
    Summable fun z => zdHeat d (r ^ 2) x z • heatEdgeTermD ω i z :=
  Summable.of_norm_bounded (summable_zdHeat (sq_nonneg r) x) fun z => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x z)]
    exact mul_le_of_le_one_right (zdHeat_nonneg (sq_nonneg r) x z) (norm_heatEdgeTermD_le ω i z)

/-- **The pairing with the heat field** is the heat average along the open edges of direction `i`
of the infinite components. -/
theorem inner_heatEdgeD (g : EdgeField d) :
    ⟪g, heatEdgeD ω r x i⟫_ℝ = ∑' z, zdHeat d (r ^ 2) x z *
      (if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then g (z, i) else 0) := by
  unfold heatEdgeD
  have hmap := (innerSL ℝ g).map_tsum (summable_heatEdgeD ω r x i)
  simp only [innerSL_apply_apply] at hmap
  rw [hmap]
  refine tsum_congr fun z => ?_
  rw [real_inner_smul_right]
  congr 1
  unfold heatEdgeTermD
  split_ifs <;> simp [lp.inner_single_right]

end HeatEdge

/-- **The heat field at an edge** (planar: `heatEdge_apply`). -/
theorem heatEdgeD_apply (ω : Configuration d) (r : ℝ) (x : Vertex d) (i : Fin d)
    (b : LatticeEdge d) :
    heatEdgeD ω r x i b =
      if b.2 = i ∧ EdgeOpen ω b ∧ ω ∈ infiniteComponentEvent b.1 then
        zdHeat d (r ^ 2) x b.1 else 0 := by
  obtain ⟨z₀, j⟩ := b
  have h := inner_heatEdgeD ω r x i (lp.single 2 (z₀, j) (1 : ℝ))
  rw [lp.inner_single_left, Real.inner_apply, one_mul] at h
  rw [h, tsum_eq_single z₀]
  · by_cases hji : j = i
    · subst hji
      by_cases hc : EdgeOpen ω (z₀, j) ∧ ω ∈ infiniteComponentEvent z₀
      · rw [if_pos hc, lp.single_apply_self, mul_one, if_pos ⟨rfl, hc⟩]
      · rw [if_neg hc, mul_zero, if_neg (fun h' => hc h'.2)]
    · have hne : ((z₀, i) : LatticeEdge d) ≠ (z₀, j) := fun e => hji (congrArg Prod.snd e).symm
      rw [if_neg (show ¬ (((z₀, j) : LatticeEdge d).2 = i ∧ EdgeOpen ω (z₀, j) ∧
        ω ∈ infiniteComponentEvent ((z₀, j) : LatticeEdge d).1) from fun h' => hji h'.1)]
      split_ifs
      · rw [lp.single_apply_ne _ _ _ hne, mul_zero]
      · rw [mul_zero]
  · intro z hz
    have hne : ((z, i) : LatticeEdge d) ≠ (z₀, j) := fun e => hz (congrArg Prod.fst e)
    split_ifs
    · rw [lp.single_apply_ne _ _ _ hne, mul_zero]
    · rw [mul_zero]


theorem summable_heat_ite_greenProjD (ω : Configuration d) (r : ℝ) (x : Vertex d) (i : Fin d)
    (ξ : EdgeField d) (B : ℝ) (hB : ∀ b, |greenProj ω ξ b| ≤ B) :
    Summable fun z => zdHeat d (r ^ 2) x z *
      (if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then greenProj ω ξ (z, i) else 0) := by
  refine Summable.of_norm_bounded ((summable_zdHeat (sq_nonneg r) x).mul_right B) fun z => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x z)]
  refine mul_le_mul_of_nonneg_left ?_ (zdHeat_nonneg (sq_nonneg r) x z)
  split_ifs
  · exact hB _
  · rw [abs_zero]; exact (abs_nonneg _).trans (hB (z, i))

omit [NeZero d] in
/-- The heat average of the indicator of one edge. -/
theorem tsum_heat_ite_eqD (r : ℝ) (x : Vertex d) (i : Fin d) (a : LatticeEdge d) :
    ∑' z, zdHeat d (r ^ 2) x z * (if ((z, i) : LatticeEdge d) = a then 1 else 0) =
      if a.2 = i then zdHeat d (r ^ 2) x a.1 else 0 := by
  rw [tsum_eq_single a.1]
  · by_cases h : a.2 = i
    · have : ((a.1, i) : LatticeEdge d) = a := Prod.ext rfl h.symm
      rw [if_pos this, if_pos h, mul_one]
    · have : ((a.1, i) : LatticeEdge d) ≠ a := fun e => h (congrArg Prod.snd e).symm
      rw [if_neg this, if_neg h, mul_zero]
  · intro z hz
    have : ((z, i) : LatticeEdge d) ≠ a := fun e => hz (congrArg Prod.fst e)
    rw [if_neg this, mul_zero]

omit [NeZero d] in
theorem summable_heat_ite_eqD (r : ℝ) (x : Vertex d) (i : Fin d) (a : LatticeEdge d) :
    Summable fun z => zdHeat d (r ^ 2) x z * (if ((z, i) : LatticeEdge d) = a then 1 else 0) := by
  refine summable_of_ne_finset_zero (s := {a.1}) fun z hz => ?_
  have : ((z, i) : LatticeEdge d) ≠ a := fun e =>
    hz (by rw [← e]; exact Finset.mem_singleton_self _)
  rw [if_neg this, mul_zero]

/-! ### The weighted energy of the heat field through the cells -/

theorem edgeSq_heatEdgeD_le (ω : Configuration d) (r : ℝ) (x : Vertex d) (i : Fin d)
    (z : Vertex d) : edgeSq (heatEdgeD ω r x i) z ≤ zdHeat d (r ^ 2) x z ^ 2 := by
  have hterm : ∀ j : Fin d, heatEdgeD ω r x i (z, j) ^ 2 ≤
      if j = i then zdHeat d (r ^ 2) x z ^ 2 else 0 := by
    intro j
    rw [heatEdgeD_apply]
    by_cases hj : j = i
    · rw [if_pos hj]
      split_ifs
      · exact le_rfl
      · rw [sq, mul_zero]; exact sq_nonneg _
    · rw [if_neg (fun h => hj h.1), if_neg hj, sq, mul_zero]
  unfold edgeSq
  calc ∑ j : Fin d, heatEdgeD ω r x i (z, j) ^ 2 ≤
        ∑ j : Fin d, (if j = i then zdHeat d (r ^ 2) x z ^ 2 else 0) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = zdHeat d (r ^ 2) x z ^ 2 := by
        rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

/-- **The weighted energy for the heat field** over a partition into cells carrying the Meyers
estimate and the weight bound (planar: `tsum_weight_openEnergy_heat_le`). -/
theorem tsum_weight_openEnergy_heatD_le {ω : Configuration d} {r : ℝ} {x : Vertex d} {i : Fin d}
    {n : Vertex d → ℕ} (hn : IsCellScale n) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M)
    (hMey : ∀ x' z, 1 ≤ n x' → z ∈ cube (n x') x' → GeneralDim.MeyersCube ε CM ω (n x' - 1) z)
    {We : Vertex d → ℝ≥0∞} (hfin : ∀ u, We u ≠ ∞)
    (hWM : ∀ x', ∑ u ∈ cube (n x') x', (We u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x') x').card) :
    ∑' u, We u * ENNReal.ofReal
        (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u) ≤
      3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
          ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n y) ^ (1 - 1 / (1 + ε / 2))) := by
  have hα0 : 0 ≤ 1 - 1 / (1 + ε / 2) := by
    have : 1 / (1 + ε / 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc1 : ∀ z, 1 ≤ (((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) := fun z =>
    Real.one_le_rpow (one_le_pow₀ (one_le_pow₀ (by norm_num))) hα0
  have hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω
      (clusterPot ω (heatEdgeD ω r x i)) z = edgeDiv ω (heatEdgeD ω r x i) z :=
    fun z hz => openLaplacian_clusterPot _ hz
  have hcell := tsum_weight_energy_le hn hv hε hCM hMey (W := fun u => (We u).toReal)
    (fun u => ENNReal.toReal_nonneg) hM hWM
  have henergy := tsum_clusterOpenEnergy_le (ω := ω) (heatEdgeD ω r x i)
  have hpath : ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
      edgeSq (heatEdgeD ω r x i) z) ≤
      ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
        ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n y) ^ (1 - 1 / (1 + ε / 2))) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    rw [mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (edgeSq_heatEdgeD_le ω r x i z)
      (zero_le_one.trans (hc1 z))
  have hΓ : ∑' z, ENNReal.ofReal (edgeSq (heatEdgeD ω r x i) z) ≤
      ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
        edgeSq (heatEdgeD ω r x i) z) :=
    ENNReal.tsum_le_tsum fun z => ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left (edgeSq_nonneg _ z) (hc1 z))
  have e1 : ∑' u, We u * ENNReal.ofReal
        (Rigidity.Corrector.GeneralDim.openEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u) =
      ∑' u, ENNReal.ofReal ((We u).toReal *
        clusterOpenEnergy ω (clusterPot ω (heatEdgeD ω r x i)) u) := by
    refine tsum_congr fun u => ?_
    rw [openEnergy_clusterPot_eq, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin u)]
  rw [e1]
  refine hcell.trans ?_
  calc _ ≤ ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        (2 * ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (heatEdgeD ω r x i) z) +
          ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (heatEdgeD ω r x i) z)) := by
        gcongr
        exact henergy.trans (by gcongr)
    _ = 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
          edgeSq (heatEdgeD ω r x i) z) := by ring
    _ ≤ _ := by gcongr

end Rigidity.Green.GeneralFlux
