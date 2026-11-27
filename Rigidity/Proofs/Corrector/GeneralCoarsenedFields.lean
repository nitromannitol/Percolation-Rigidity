import Rigidity.Proofs.Corrector.GeneralDarioOptimalCorrector
import Rigidity.Proofs.Corrector.GeneralShiftedAnchor
import Rigidity.Proofs.Corrector.PlanarMeasurableCorrector

/-!
# The coarsened correctors of Dario's §5 in every dimension

With the measurable corrector increments `correctorDiff` and the anchors `shiftedAnchor` of the
translated partitions `𝒫_y` into good cubes of `ℤᵈ`, the coarsened corrector of slope `e_i` for the
partition `𝒫_{y'}` is `coarseField i y' z = χ(a_{𝒫_{y'}}(z)) - χ(a_𝒫(0))`, and the fields re-centred
at `y` are `recentredField i y y' z = coarseField i (y + y') (y + z)`. The translation identity
`coarseField_translation` (from the stationarity (2.3) of the corrector and the translation of the
partitions) reduces the hypotheses of `DarioCoarsenedCorrectorThree` to statements about
`coarseField` at the base point: (5.5) at the origin with box oscillations bounded uniformly in the
scale (`BaseTheorem` with the growth exponent `0`), the moment form of (5.7) and the coarsening
error (5.10) (`darioCoarsenedCorrectorThree_of_base`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2
open scoped Classical ENNReal

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- An `O_s` bound is preserved by translating the configuration. -/
theorem IsOsBond.comp_translation {p : unitInterval} {X : Configuration d → ℝ} {s θ : ℝ}
    (z : Vertex d) (hX : Measurable X) (h : IsOsBond d p X s θ) :
    IsOsBond d p (fun ω => X (configurationTranslation z ω)) s θ := by
  have hT := measurePreserving_configurationTranslation p z
  obtain ⟨hi, hb⟩ := h
  have hm : Measurable fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s) :=
    Real.measurable_exp.comp (((hX.div_const θ).max measurable_const).pow_const s)
  refine ⟨(hT.integrable_comp hm.aestronglyMeasurable).2 hi, ?_⟩
  have e := hT.integral_comp (configurationTranslationMeasurableEquiv z).measurableEmbedding
    (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s))
  exact e.trans_le hb

section Fields

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

omit [NeZero d] in
theorem correctorDiff_sub_eq {q : Fin d → ℝ} {ω : Configuration d} (hω : ω ∈ G)
    {a b c : Vertex d} (ha : ω ∈ infiniteComponentEvent a) (hb : ω ∈ infiniteComponentEvent b)
    (hc : ω ∈ infiniteComponentEvent c) :
    correctorDiff hG hGv q ω a c - correctorDiff hG hGv q ω b c =
      correctorDiff hG hGv q ω a b := by
  obtain ⟨h, -⟩ := hGv hω
  have e : correctorDiff hG hGv q ω a c =
      correctorDiff hG hGv q ω a b + correctorDiff hG hGv q ω b c :=
    correctorDiff_add hG hGv hω (uniqueInfiniteComponent_infinite h)
      ⟨a, (mem_uniqueInfiniteComponent_iff h a).2 ha⟩
      ⟨b, (mem_uniqueInfiniteComponent_iff h b).2 hb⟩
      ⟨c, (mem_uniqueInfiniteComponent_iff h c).2 hc⟩
  linarith

omit [NeZero d] in
theorem correctorDiff_translate {q : Fin d → ℝ} {ω : Configuration d} (t : Vertex d)
    (hω : ω ∈ G) (hω' : configurationTranslation t ω ∈ G) {a b : Vertex d}
    (ha : ω ∈ infiniteComponentEvent a) (hb : ω ∈ infiniteComponentEvent b) :
    correctorDiff hG hGv q (configurationTranslation t ω) (a + t) (b + t) =
      correctorDiff hG hGv q ω a b := by
  obtain ⟨h, -⟩ := hGv hω
  exact correctorDiff_translation hG hGv t hω hω' (uniqueInfiniteComponent_infinite h)
    ⟨a, (mem_uniqueInfiniteComponent_iff h a).2 ha⟩ ⟨b, (mem_uniqueInfiniteComponent_iff h b).2 hb⟩

omit [NeZero d] in
theorem measurable_correctorDiff_comp (q : Fin d → ℝ) {a b : Configuration d → Vertex d}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => correctorDiff hG hGv q ω (a ω) (b ω) := by
  have h : Measurable fun x : Configuration d × (Vertex d × Vertex d) =>
      correctorDiff hG hGv q x.1 x.2.1 x.2.2 :=
    measurable_from_prod_countable_left fun ab => measurable_correctorDiff hG hGv q ab.1 ab.2
  exact h.comp (measurable_id.prodMk (ha.prodMk hb))

/-- The coarsened corrector `[χ_{e_i}]_{𝒫_{y'}}(z) - [χ_{e_i}]_𝒫(0)`. -/
noncomputable def coarseField (i : Fin d) (y' z : Vertex d) (ω : Configuration d) : ℝ :=
  correctorDiff hG hGv (Pi.single i 1) ω (shiftedAnchor y' ω z) (shiftedAnchor 0 ω 0)

/-- The coarsened correctors re-centred at `y`: `[χ_{e_i}]_{𝒫_{y + y'}}(y + z)`. -/
noncomputable def recentredField (i : Fin d) (y y' z : Vertex d) (ω : Configuration d) : ℝ :=
  coarseField hG hGv i (y + y') (y + z) ω

omit [NeZero d] in
theorem measurable_coarseField (i : Fin d) (y' z : Vertex d) :
    Measurable (coarseField hG hGv i y' z) :=
  measurable_correctorDiff_comp hG hGv _ (measurable_shiftedAnchor y' z)
    (measurable_shiftedAnchor 0 0)

/-- The anchors of `𝒫_y` are in the infinite cluster on the partition event of `τ_{-y} ω`. -/
theorem infinite_shiftedAnchor_zero {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) : ω ∈ infiniteComponentEvent (shiftedAnchor 0 ω z) :=
  infinite_shiftedAnchor (Nat.pos_of_neZero d)
    (by rw [neg_zero, configurationTranslation_zero]; exact hP) z

/-- **Translation identity of the coarsened correctors**: for a configuration `ω'` and a
translation `t`,
`coarseField (t + Y') (t + Z) (τ_t ω') - coarseField (t + Y'') (t + W) (τ_t ω')`
`= coarseField Y' Z ω' - coarseField Y'' W ω'`. -/
theorem coarseField_translation (i : Fin d) {ω' : Configuration d} (t Y' Y'' Z W : Vertex d)
    (hω' : ω' ∈ G) (htω' : configurationTranslation t ω' ∈ G)
    (hP : PartitionEvent ω') (htP : PartitionEvent (configurationTranslation t ω'))
    (hP' : PartitionEvent (configurationTranslation (-Y') ω'))
    (hP'' : PartitionEvent (configurationTranslation (-Y'') ω')) :
    coarseField hG hGv i (t + Y') (t + Z) (configurationTranslation t ω') -
        coarseField hG hGv i (t + Y'') (t + W) (configurationTranslation t ω') =
      coarseField hG hGv i Y' Z ω' - coarseField hG hGv i Y'' W ω' := by
  have hA1 : shiftedAnchor (t + Y') (configurationTranslation t ω') (t + Z) =
      shiftedAnchor Y' ω' Z + t := by
    rw [add_comm t Y', add_comm t Z]
    exact shiftedAnchor_translation Y' t ω' Z
  have hA2 : shiftedAnchor (t + Y'') (configurationTranslation t ω') (t + W) =
      shiftedAnchor Y'' ω' W + t := by
    rw [add_comm t Y'', add_comm t W]
    exact shiftedAnchor_translation Y'' t ω' W
  have h1 := infinite_shiftedAnchor (Nat.pos_of_neZero d) hP' Z
  have h2 := infinite_shiftedAnchor (Nat.pos_of_neZero d) hP'' W
  unfold coarseField
  rw [correctorDiff_sub_eq hG hGv htω'
      (by rw [hA1]; exact mem_infiniteComponentEvent_translation t h1)
      (by rw [hA2]; exact mem_infiniteComponentEvent_translation t h2)
      (infinite_shiftedAnchor_zero htP 0),
    correctorDiff_sub_eq hG hGv hω' h1 h2 (infinite_shiftedAnchor_zero hP 0), hA1, hA2]
  exact correctorDiff_translate hG hGv t hω' htω' h1 h2

omit [NeZero d] in
theorem correctorDiff_add' {q : Fin d → ℝ} {ω : Configuration d} (hω : ω ∈ G)
    {a b c : Vertex d} (ha : ω ∈ infiniteComponentEvent a) (hb : ω ∈ infiniteComponentEvent b)
    (hc : ω ∈ infiniteComponentEvent c) :
    correctorDiff hG hGv q ω a c = correctorDiff hG hGv q ω a b + correctorDiff hG hGv q ω b c := by
  have := correctorDiff_sub_eq hG hGv (q := q) hω ha hb hc
  linarith

omit [NeZero d] in
theorem correctorDiff_swap' {q : Fin d → ℝ} {ω : Configuration d} (hω : ω ∈ G)
    {a b : Vertex d} (ha : ω ∈ infiniteComponentEvent a) (hb : ω ∈ infiniteComponentEvent b) :
    correctorDiff hG hGv q ω b a = -correctorDiff hG hGv q ω a b := by
  have h1 := correctorDiff_sub_eq hG hGv (q := q) hω ha hb ha
  have h0 := correctorDiff_sub_eq hG hGv (q := q) hω ha ha ha
  linarith

/-- The `q`-th moment of the oscillation of a field over the box `[-3^m, 3^m]ᵈ` of `ℤᵈ`, normalized
by `(3^m)^d`. -/
noncomputable def boxOsc (u : Vertex d → Configuration d → ℝ) (m : ℕ) (q : ℝ)
    (ω : Configuration d) : ℝ :=
  (∑ z ∈ boxAt 0 m, |u z ω - boxAvg u 0 m ω| ^ q) / (3 ^ m) ^ d

omit [NeZero d] in
theorem measurable_boxOsc {u : Vertex d → Configuration d → ℝ} (hu : ∀ z, Measurable (u z))
    (m : ℕ) (q : ℝ) : Measurable (boxOsc u m q) :=
  (Finset.measurable_sum _ fun z _ =>
    ((hu z).sub (measurable_boxAvg hu 0 m)).abs.pow_const q).div_const _

omit [NeZero d] in
/-- The box oscillation depends only on the increments of the field. -/
theorem boxOsc_eq_of_sub_eq {u v : Vertex d → Configuration d → ℝ} {ω ω' : Configuration d}
    (h : ∀ z w, u z ω - u w ω = v z ω' - v w ω') (m : ℕ) (q : ℝ) :
    boxOsc u m q ω = boxOsc v m q ω' := by
  unfold boxOsc
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sub_boxAvg_eq u (u z ω) 0 m ω, sub_boxAvg_eq v (v z ω') 0 m ω']
  simp only [h z]

omit [NeZero d] in
theorem configurationTranslation_neg_cancel (y : Vertex d) (ω : Configuration d) :
    configurationTranslation y (configurationTranslation (-y) ω) = ω := by
  rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]

/-- **(5.5) at the origin for the coarsened correctors** (base hypothesis), with the growth
exponent `a` in the scale. -/
def BaseTheorem (p : unitInterval) (A k a : ℝ) : Prop :=
  ∀ i : Fin d, ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 1 ≤ q →
    ∫⁻ ω, ENNReal.ofReal (boxOsc (coarseField hG hGv i 0) m q ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A * q ^ k) ^ q * (m : ℝ) ^ (q * a))

/-- **The moment form of (5.7)** for the coarsened correctors (base hypothesis; proved:
`baseComparison`). -/
def BaseComparison (p : unitInterval) (B k : ℝ) : Prop :=
  ∀ (i : Fin d) (y' z : Vertex d) (q : ℝ), 1 ≤ q →
    mom p (fun ω => coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω) q ≤
      ENNReal.ofReal ((B * q ^ k) ^ q)

/-- **The coarsening error (5.10)** at a point of the infinite cluster (base hypothesis; proved:
`baseCoarseningError`). -/
def BaseCoarseningError (p : unitInterval) (s₆ C₆ : ℝ) : Prop :=
  ∀ (i : Fin d) (v : Vertex d), ∃ E : Configuration d → ℝ, Measurable E ∧ IsOsBond d p E s₆ C₆ ∧
    ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ infiniteComponentEvent v →
      |correctorDiff hG hGv (Pi.single i 1) ω v (guardAnchor ω v)| ≤ E ω

variable (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
  (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)

include hd hpc hGae in
/-- The re-centred fields satisfy the hypotheses of Steps 1–4, from the base hypotheses. -/
theorem linftyIterationData_recentred {A B k a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (h2 : BaseTheorem hG hGv p A k a) (hc : BaseComparison hG hGv p B k) (i : Fin d)
    (y : Vertex d) : LinftyIterationData p (recentredField hG hGv i y) A B k a where
  hA := hA
  hB := hB
  ha := ha
  meas := fun y' z => measurable_coarseField hG hGv i (y + y') (y + z)
  thm2 := by
    intro m hm q hq
    have hGt : ∀ t, ∀ᵐ ω ∂latticeBondLaw d p, configurationTranslation t ω ∈ G := fun t =>
      (measurePreserving_configurationTranslation p t).quasiMeasurePreserving.ae hGae
    have hae : ∀ᵐ ω ∂latticeBondLaw d p, boxOsc (recentredField hG hGv i y 0) m q ω =
        boxOsc (coarseField hG hGv i 0) m q (configurationTranslation (-y) ω) := by
      filter_upwards [hGae, hGt (-y), ae_partitionEvent hd hpc,
        ae_partitionEvent_translation hd hpc (-y)] with ω h1 h2 h3 h4
      refine boxOsc_eq_of_sub_eq (fun z w => ?_) m q
      have h4' :
          PartitionEvent (configurationTranslation (-0) (configurationTranslation (-y) ω)) := by
        rw [neg_zero, configurationTranslation_zero]; exact h4
      have e := coarseField_translation hG hGv i y 0 0 z w h2
        (by rw [configurationTranslation_neg_cancel]; exact h1) h4
        (by rw [configurationTranslation_neg_cancel]; exact h3) h4' h4'
      rw [configurationTranslation_neg_cancel] at e
      exact e
    change ∫⁻ ω, ENNReal.ofReal (boxOsc (recentredField hG hGv i y 0) m q ω) ∂latticeBondLaw d p ≤ _
    rw [lintegral_congr_ae (hae.mono fun ω h => by rw [h]),
      (measurePreserving_configurationTranslation p (-y)).lintegral_comp
        (measurable_boxOsc (measurable_coarseField hG hGv i 0) m q).ennreal_ofReal]
    exact h2 i m hm q hq
  stat := by
    intro y'
    have hGt : ∀ t, ∀ᵐ ω ∂latticeBondLaw d p, configurationTranslation t ω ∈ G := fun t =>
      (measurePreserving_configurationTranslation p t).quasiMeasurePreserving.ae hGae
    refine ⟨configurationTranslation y', measurePreserving_configurationTranslation p y', ?_⟩
    filter_upwards [hGae, hGt y', ae_partitionEvent hd hpc,
      ae_partitionEvent_translation hd hpc y', ae_partitionEvent_translation hd hpc (-y)]
      with ω h1 h2 h3 h4 h5
    intro z w
    have e := coarseField_translation hG hGv i y' y y (y + z) (y + w) h1 h2 h3 h4 h5 h5
    simp only [recentredField, add_zero]
    rw [show y' + y = y + y' by abel, show y' + (y + z) = y + (z + y') by abel,
      show y' + (y + w) = y + (w + y') by abel] at e
    exact e.symm
  comp := by
    intro y' z q hq
    have hGt : ∀ t, ∀ᵐ ω ∂latticeBondLaw d p, configurationTranslation t ω ∈ G := fun t =>
      (measurePreserving_configurationTranslation p t).quasiMeasurePreserving.ae hGae
    have hae : ∀ᵐ ω ∂latticeBondLaw d p,
        ENNReal.ofReal (|recentredField hG hGv i y y' z ω - recentredField hG hGv i y 0 z ω| ^ q) =
          ENNReal.ofReal (|coarseField hG hGv i y' z (configurationTranslation (-y) ω) -
            coarseField hG hGv i 0 z (configurationTranslation (-y) ω)| ^ q) := by
      filter_upwards [hGae, hGt (-y), ae_partitionEvent hd hpc,
        ae_partitionEvent_translation hd hpc (-y),
        ae_partitionEvent_translation hd hpc (-y' + -y)] with ω h1 h2 h3 h4 h5
      have h5' :
          PartitionEvent (configurationTranslation (-y') (configurationTranslation (-y) ω)) := by
        rw [configurationTranslation_add]; exact h5
      have h4' :
          PartitionEvent (configurationTranslation (-0) (configurationTranslation (-y) ω)) := by
        rw [neg_zero, configurationTranslation_zero]; exact h4
      have e := coarseField_translation hG hGv i y y' 0 z z h2
        (by rw [configurationTranslation_neg_cancel]; exact h1) h4
        (by rw [configurationTranslation_neg_cancel]; exact h3) h5' h4'
      rw [configurationTranslation_neg_cancel] at e
      simp only [add_zero] at e
      simp only [recentredField, add_zero]
      rw [e]
    have hcomp := (measurePreserving_configurationTranslation p (-y)).lintegral_comp
      (f := fun ω =>
        ENNReal.ofReal (|coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ^ q))
      (measurable_ofReal_abs_rpow ((measurable_coarseField hG hGv i y' z).sub
        (measurable_coarseField hG hGv i 0 z)) q)
    unfold mom
    rw [lintegral_congr_ae hae, hcomp]
    exact hc i y' z q hq

include hd hpc hGae in
/-- The coarsening error of Step 6 for the re-centred fields, from the base hypothesis. -/
theorem coarseningError_recentred {s₆ C₆ : ℝ} (hs₆ : 0 < s₆) (hC₆ : 0 < C₆)
    (h6 : BaseCoarseningError hG hGv p s₆ C₆) :
    CoarseningError p (recentredField hG hGv) s₆ (2 * (C₆ * 4 ^ (1 / s₆))) := by
  intro i x y
  obtain ⟨E₁, hE₁m, hE₁, hE₁ae⟩ := h6 i (x - y)
  obtain ⟨E₀, hE₀m, hE₀, hE₀ae⟩ := h6 i 0
  have hTm := (configurationTranslationMeasurableEquiv (-y)).measurable
  have hTq := (measurePreserving_configurationTranslation p (-y)).quasiMeasurePreserving
  have hGt : ∀ t, ∀ᵐ ω ∂latticeBondLaw d p, configurationTranslation t ω ∈ G := fun t =>
    (measurePreserving_configurationTranslation p t).quasiMeasurePreserving.ae hGae
  refine ⟨fun ω => 2 * max (E₁ (configurationTranslation (-y) ω))
    (E₀ (configurationTranslation (-y) ω)), ((hE₁m.comp hTm).max (hE₀m.comp hTm)).const_mul 2,
    ?_, ?_⟩
  · have h1 := IsOsBond.comp_translation (-y) hE₁m hE₁
    have h0 := IsOsBond.comp_translation (-y) hE₀m hE₀
    have hmax := IsOsBond.max hs₆ hC₆ hC₆ (hE₁m.comp hTm) (hE₀m.comp hTm) h1 h0
    rw [max_self] at hmax
    exact IsOsBond.const_mul two_pos hmax
  · filter_upwards [hGae, hGt (-y), ae_partitionEvent hd hpc,
      ae_partitionEvent_translation hd hpc (-y), hTq.ae hE₁ae, hTq.ae hE₀ae]
      with ω hω hω' hP hP' he1 he0
    intro h ℓ hℓ hx hy
    set ω' := configurationTranslation (-y) ω with hω'def
    have hωω' : configurationTranslation y ω' = ω := configurationTranslation_neg_cancel y ω
    have hxω : ω ∈ infiniteComponentEvent x := (mem_uniqueInfiniteComponent_iff h x).1 hx
    have hyω : ω ∈ infiniteComponentEvent y := (mem_uniqueInfiniteComponent_iff h y).1 hy
    have hx' : ω' ∈ infiniteComponentEvent (x - y) := by
      have := mem_infiniteComponentEvent_translation (-y) hxω
      rwa [← sub_eq_add_neg] at this
    have hy' : ω' ∈ infiniteComponentEvent 0 := by
      have := mem_infiniteComponentEvent_translation (-y) hyω
      rwa [add_neg_cancel] at this
    -- the anchors of `𝒫_y` at `x` and `y`
    have hAx : shiftedAnchor y ω x = shiftedAnchor 0 ω' (x - y) + y := by
      have := shiftedAnchor_translation 0 y ω' (x - y)
      rwa [zero_add, hωω', sub_add_cancel] at this
    have hAy : shiftedAnchor y ω y = shiftedAnchor 0 ω' 0 + y := by
      have := shiftedAnchor_translation 0 y ω' 0
      simp only [zero_add] at this
      rwa [hωω'] at this
    have hax := infinite_shiftedAnchor_zero hP' (x - y)
    have hay := infinite_shiftedAnchor_zero hP' 0
    have hAxω : ω ∈ infiniteComponentEvent (shiftedAnchor y ω x) :=
      infinite_shiftedAnchor (Nat.pos_of_neZero d) hP' x
    have hAyω : ω ∈ infiniteComponentEvent (shiftedAnchor y ω y) :=
      infinite_shiftedAnchor (Nat.pos_of_neZero d) hP' y
    have hbase := infinite_shiftedAnchor_zero hP 0
    -- the corrector increments at `x` and `y`
    have tx := correctorDiff_translate hG hGv (q := Pi.single i 1) y hω'
      (by rw [hωω']; exact hω) hx' hax
    rw [hωω', sub_add_cancel, ← hAx, shiftedAnchor_zero] at tx
    have ty := correctorDiff_translate hG hGv (q := Pi.single i 1) y hω'
      (by rw [hωω']; exact hω) hy' hay
    rw [hωω', zero_add, ← hAy, shiftedAnchor_zero] at ty
    have hD : ((ℓ ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * x j) -
        (ℓ ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * y j)) =
          correctorDiff hG hGv (Pi.single i 1) ω x y :=
      (correctorDiff_eq hG hGv hω (uniqueInfiniteComponent_infinite h) hℓ ⟨x, hx⟩ ⟨y, hy⟩).symm
    rw [hD]
    have hF : recentredField hG hGv i y 0 (x - y) ω - recentredField hG hGv i y 0 0 ω =
        correctorDiff hG hGv (Pi.single i 1) ω (shiftedAnchor y ω x) (shiftedAnchor y ω y) := by
      have e : y + (x - y) = x := by abel
      simp only [recentredField, coarseField, add_zero]
      rw [e]
      exact correctorDiff_sub_eq hG hGv hω hAxω hAyω hbase
    rw [hF]
    have c1 := correctorDiff_add' hG hGv (q := Pi.single i 1) hω hxω hAxω hyω
    have c2 := correctorDiff_add' hG hGv (q := Pi.single i 1) hω hAxω hAyω hyω
    have c3 := correctorDiff_swap' hG hGv (q := Pi.single i 1) hω hyω hAyω
    have b1 := he1 hx'
    have b0 := he0 hy'
    rw [← tx] at b1
    rw [← ty] at b0
    have hm1 := le_max_left (E₁ ω') (E₀ ω')
    have hm0 := le_max_right (E₁ ω') (E₀ ω')
    calc |correctorDiff hG hGv (Pi.single i 1) ω x y -
          correctorDiff hG hGv (Pi.single i 1) ω (shiftedAnchor y ω x) (shiftedAnchor y ω y)|
        = |correctorDiff hG hGv (Pi.single i 1) ω x (shiftedAnchor y ω x) -
            correctorDiff hG hGv (Pi.single i 1) ω y (shiftedAnchor y ω y)| := by
          congr 1
          linarith
      _ ≤ |correctorDiff hG hGv (Pi.single i 1) ω x (shiftedAnchor y ω x)| +
            |correctorDiff hG hGv (Pi.single i 1) ω y (shiftedAnchor y ω y)| := abs_sub _ _
      _ ≤ 2 * max (E₁ ω') (E₀ ω') := by linarith

include hd hpc hGae in
/-- **`DarioCoarsenedCorrectorThree` from the base hypotheses** on the coarsened correctors, with
box oscillations bounded uniformly in the scale. -/
theorem darioCoarsenedCorrectorThree_of_base {A B k s₆ C₆ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs₆ : 0 < s₆) (hC₆ : 0 < C₆) (h2 : BaseTheorem hG hGv p A k 0)
    (hc : BaseComparison hG hGv p B k) (h6 : BaseCoarseningError hG hGv p s₆ C₆) :
    DarioCoarsenedCorrectorThree d p :=
  ⟨A, B, k, s₆, 2 * (C₆ * 4 ^ (1 / s₆)), hs₆, by positivity, recentredField hG hGv,
    fun i y => linftyIterationData_recentred hG hGv hd hpc hGae hA hB le_rfl h2 hc i y,
    coarseningError_recentred hG hGv hd hpc hGae hs₆ hC₆ h6⟩

end Fields

/-- **The base hypotheses of Dario's §5 in dimension `d ≥ 3`**: a measurable almost sure event of
valid correctors on which the coarsened correctors satisfy (5.5) at the origin with box
oscillations bounded uniformly in the scale, the moment form of (5.7) and the coarsening error
(5.10). -/
def DarioBaseThree (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∃ (G : Set (Configuration d)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d),
    (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) ∧ ∃ A B k s₆ C₆ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < s₆ ∧ 0 < C₆ ∧
      BaseTheorem hG hGv p A k 0 ∧ BaseComparison hG hGv p B k ∧
        BaseCoarseningError hG hGv p s₆ C₆

/-- **Dario's Theorem 1 in dimension `d ≥ 3`** (`DarioOptimalCorrectorThree`) from the base
hypotheses of §5 on the coarsened correctors. -/
theorem darioOptimalCorrectorThree_of_base
    (hB : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → DarioBaseThree d p) : DarioOptimalCorrectorThree := by
  refine darioOptimalCorrectorThree_of_coarsened fun d _ hd3 p hpc hp1 => ?_
  obtain ⟨G, hG, hGv, hGae, A, B, k, s₆, C₆, hA, hB0, hs₆, hC₆, h2, hc, h6⟩ := hB d hd3 p hpc hp1
  exact darioCoarsenedCorrectorThree_of_base hG hGv (by omega) hpc hGae hA hB0 hs₆ hC₆ h2 hc h6

end Rigidity.Corrector.GeneralDim
