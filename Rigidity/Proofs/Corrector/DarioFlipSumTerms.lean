import Rigidity.Proofs.Corrector.DarioStepTwoCases

/-!
# The flip sum of Lemma 3.3 of Dario from the two terms of (3.15)

The flip form `DarioFlipSumBound` of (3.13) bounds `Σ_e (D_e X)²` for
`X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)`. With the correctors `χ_b` of the flips `ω^{e,b}`, rooted at the
anchor `z̄⁰(0)` of the origin for `ω^{e,0}` (`flipCorrector`; this point lies in the infinite
cluster of both flips), the split (3.15) of Dario reads

`D_e X = T₁(e) + T₂(e)`, `T₁(e) = Σ_y Φ_{r²}(x, y) (∇_j[χ₁]_{𝒫¹}(y) - ∇_j[χ₁]_{𝒫⁰}(y))`,
`T₂(e) = Φ_{r²} * ∇_j[χ₁ - χ₀]_{𝒫⁰}(x)`

(`bondFlipDiff_eq_flipTermOne_add_flipTermTwo`), on the configurations whose flips lie in `G` and
in the partition event, when the series converge (`FlipSummable`). The term `T₁` is the change of
partition of Step 1 (`flipTermOne_eq_tsum_partitionChange`, bounded by
`sq_tsum_partitionChange_le`), and `T₂` the change of corrector of Step 2. Hence
(`darioFlipSumBound_of_terms`) Dario's (3.13) in flip form follows from

* the almost sure convergence of the series,
* `Σ_e T₁(e)² ≤ O_s(C/r²)` (Step 1) and `Σ_e T₂(e)² ≤ O_s(C/r²)` (Step 2), both almost surely
  finite,

through `(a + b)² ≤ 2a² + 2b²` and the `O_s` bound of a maximum.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2
open scoped Classical ENNReal

theorem infiniteComponentEvent_setBond_true {e : Bond 2} {ω : Configuration 2} {v : Vertex 2}
    (h : setBond e false ω ∈ infiniteComponentEvent v) (b : Bool) :
    setBond e b ω ∈ infiniteComponentEvent v := by
  cases b
  · exact h
  · exact Set.Infinite.mono (supp_setBond_false_subset e ω v) h

section Terms

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem measurable_correctorDiff_comp_config (q : Fin 2 → ℝ)
    {f : Configuration 2 → Configuration 2} (hf : Measurable f)
    {a b : Configuration 2 → Vertex 2} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => correctorDiff hG hGv q (f ω) (a ω) (b ω) := by
  have h : Measurable fun x : Configuration 2 × (Vertex 2 × Vertex 2) =>
      correctorDiff hG hGv q x.1 x.2.1 x.2.2 :=
    measurable_from_prod_countable_left fun ab => measurable_correctorDiff hG hGv q ab.1 ab.2
  exact h.comp (hf.prodMk (ha.prodMk hb))

/-- The corrector `χ_b` of the flip `ω^{e,b}`, rooted at the anchor `z̄⁰(0)` of the origin for the
partition of `ω^{e,0}`. -/
noncomputable def flipCorrector (i : Fin 2) (b : Bool) (e : Bond 2) (ω : Configuration 2)
    (v : Vertex 2) : ℝ :=
  correctorDiff hG hGv (Pi.single i 1) (setBond e b ω) v (guardAnchor (setBond e false ω) 0)

theorem measurable_flipCorrector_comp (i : Fin 2) (b : Bool) (e : Bond 2)
    {a : Configuration 2 → Vertex 2} (ha : Measurable a) :
    Measurable fun ω => flipCorrector hG hGv i b e ω (a ω) :=
  measurable_correctorDiff_comp_config hG hGv _ (measurable_setBond e b) ha
    ((measurable_guardAnchor 0).comp (measurable_setBond e false))

theorem measurable_guardAnchor_setBond (e : Bond 2) (b : Bool) (z : Vertex 2) :
    Measurable fun ω => guardAnchor (setBond e b ω) z :=
  (measurable_guardAnchor z).comp (measurable_setBond e b)

/-- The term (3.15)-(i) in flip form: the heat average of the change of the coarse gradient of
`χ₁` from the partition of `ω^{e,1}` to that of `ω^{e,0}`. -/
noncomputable def flipTermOne (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2)
    (ω : Configuration 2) : ℝ :=
  ∑' y, latticeHeat (r ^ 2) x y *
    ((flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) y)) -
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y)))

/-- The term (3.15)-(ii) in flip form: `Φ_{r²} * ∇_j[χ₁ - χ₀]_{𝒫⁰}(x)`. -/
noncomputable def flipTermTwo (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2)
    (ω : Configuration 2) : ℝ :=
  heatComp (fun z => flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) z) -
    flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) z)) r x j

/-- The convergence of the three heat series of the split. -/
def FlipSummable (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2) (ω : Configuration 2) : Prop :=
  (Summable fun y => latticeHeat (r ^ 2) x y *
    (flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
      flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) y))) ∧
  (Summable fun y => latticeHeat (r ^ 2) x y *
    (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
      flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y))) ∧
  (Summable fun y => latticeHeat (r ^ 2) x y *
    (flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
      flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) y)))

/-- `Σ_e T₁(e)²`. -/
noncomputable def flipSumOne (i j : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2)

/-- `Σ_e T₂(e)²`. -/
noncomputable def flipSumTwo (i j : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2)

theorem measurable_flipTermOne (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2) :
    Measurable (flipTermOne hG hGv i j r x e) := by
  unfold flipTermOne
  refine Measurable.tsum fun y => Measurable.const_mul ?_ _
  have m := fun (b : Bool) (z : Vertex 2) =>
    measurable_flipCorrector_comp hG hGv i true e (measurable_guardAnchor_setBond e b z)
  exact ((m true _).sub (m true _)).sub ((m false _).sub (m false _))

theorem measurable_flipTermTwo (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2) :
    Measurable (flipTermTwo hG hGv i j r x e) := by
  unfold flipTermTwo
  exact measurable_heatComp (fun z =>
    (measurable_flipCorrector_comp hG hGv i true e (measurable_guardAnchor_setBond e false z)).sub
      (measurable_flipCorrector_comp hG hGv i false e (measurable_guardAnchor_setBond e false z)))
    r x j

theorem measurable_flipSumOne (i j : Fin 2) (r : ℝ) (x : Vertex 2) :
    Measurable (flipSumOne hG hGv i j r x) :=
  Measurable.tsum fun e =>
    ENNReal.measurable_ofReal.comp ((measurable_flipTermOne hG hGv i j r x e).pow_const 2)

theorem measurable_flipSumTwo (i j : Fin 2) (r : ℝ) (x : Vertex 2) :
    Measurable (flipSumTwo hG hGv i j r x) :=
  Measurable.tsum fun e =>
    ENNReal.measurable_ofReal.comp ((measurable_flipTermTwo hG hGv i j r x e).pow_const 2)

/-- On a flip in `G` and in the partition event, the variable of Lemma 3.3 is the heat average of
the coarse gradient of `χ_b`. -/
theorem heatCoarseComp_setBond_eq {e : Bond 2} {ω : Configuration 2} {b : Bool}
    (hω : setBond e b ω ∈ G) (hP : PlanarPartitionEvent (setBond e b ω))
    (hP₀ : PlanarPartitionEvent (setBond e false ω)) (i j : Fin 2) (r : ℝ) (x : Vertex 2) :
    heatCoarseComp hG hGv i j r x (setBond e b ω) =
      heatComp (fun z => flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) z)) r x j := by
  unfold heatCoarseComp
  have ho : setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e false ω) 0) := by
    refine infiniteComponentEvent_setBond_true ?_ b
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ 0
  have hA : ∀ z, setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e b ω) z) :=
    fun z => by
      rw [guardAnchor_of_event hP]
      exact infinite_planarCoarseAnchor hP z
  have e' : (fun z => coarseField hG hGv i 0 z (setBond e b ω)) = fun z =>
      flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) z) +
        -flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) 0) := by
    funext z
    unfold coarseField flipCorrector
    rw [shiftedAnchor_zero, shiftedAnchor_zero]
    have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA z) (hA 0) ho
    linarith
  rw [e', heatComp_add_const]

/-- **The split (3.15) in flip form**: `D_e X = T₁(e) + T₂(e)`. -/
theorem bondFlipDiff_eq_flipTermOne_add_flipTermTwo {e : Bond 2} {ω : Configuration 2}
    (hω₁ : setBond e true ω ∈ G) (hω₀ : setBond e false ω ∈ G)
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    (i j : Fin 2) (r : ℝ) (x : Vertex 2) (hS : FlipSummable hG hGv i j r x e ω) :
    bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω =
      flipTermOne hG hGv i j r x e ω + flipTermTwo hG hGv i j r x e ω := by
  unfold bondFlipDiff
  rw [heatCoarseComp_setBond_eq hG hGv hω₁ hP₁ hP₀ i j r x,
    heatCoarseComp_setBond_eq hG hGv hω₀ hP₀ hP₀ i j r x,
    heatComp_sub_eq_split _ _ _ _ r x j hS.1 hS.2.1 hS.2.2]
  rfl

/-- On the partition events, `T₁(e)` is the heat average of `partitionChange ω⁰ ω¹ χ₁`, the
quantity bounded in Step 1 (`sq_tsum_partitionChange_le`). -/
theorem flipTermOne_eq_tsum_partitionChange {e : Bond 2} {ω : Configuration 2}
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    (i j : Fin 2) (r : ℝ) (x : Vertex 2) :
    flipTermOne hG hGv i j r x e ω = ∑' y, latticeHeat (r ^ 2) x y *
      partitionChange (setBond e false ω) (setBond e true ω)
        (flipCorrector hG hGv i true e ω) j y := by
  unfold flipTermOne partitionChange
  simp only [guardAnchor_of_event hP₁, guardAnchor_of_event hP₀]

end Terms

theorem ofReal_sq_add_le (a b : ℝ) :
    ENNReal.ofReal ((a + b) ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  have h : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc ENNReal.ofReal ((a + b) ^ 2) ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **(3.13) in flip form from the two terms of (3.15)**: `DarioFlipSumBound` holds if, for the
conull sets `G` of the measurable corrector, there are `s, C > 0` such that for all `i, j`, `r ≥ 1`
and `x`, almost surely the series of the split converge for every bond, and the sums
`Σ_e T₁(e)²` (Step 1) and `Σ_e T₂(e)²` (Step 2) are almost surely finite and `≤ O_s(C/r²)`. -/
theorem darioFlipSumBound_of_terms
    (h : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, ∀ e, FlipSummable hG hGv i j r x e ω) ∧
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumOne hG hGv i j r x ω < ∞) ∧
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C / r ^ 2) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioFlipSumBound := by
  intro p hpc hp1 G hG hGv hGae
  obtain ⟨s, C, hs, hC, hb⟩ := h p hpc hp1 G hG hGv hGae
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  refine ⟨s, 4 * C * 4 ^ (1 / s), hs, by positivity, fun i j r hr x => ?_⟩
  obtain ⟨hsum, hf1, hf2, h1, h2⟩ := hb i j r hr x
  have hflipG := ae_setBond hp0 hp1 hGae
  have hflipP := ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc)
  have hle : ∀ᵐ ω ∂latticeBondLaw 2 p, heatFlipSum hG hGv i j r x ω ≤
      2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω := by
    filter_upwards [hflipG, hflipP, hsum] with ω hG' hP' hS
    unfold heatFlipSum flipSumOne flipSumTwo
    calc ∑' e, ENNReal.ofReal (bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω ^ 2)
        ≤ ∑' e, (2 * ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2) +
            2 * ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2)) :=
          ENNReal.tsum_le_tsum fun e => by
            rw [bondFlipDiff_eq_flipTermOne_add_flipTermTwo hG hGv (hG' e true) (hG' e false)
              (hP' e true) (hP' e false) i j r x (hS e)]
            exact ofReal_sq_add_le _ _
      _ = 2 * ∑' e, ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2) +
          2 * ∑' e, ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hfin : ∀ᵐ ω ∂latticeBondLaw 2 p, heatFlipSum hG hGv i j r x ω < ∞ := by
    filter_upwards [hle, hf1, hf2] with ω h0 h1' h2'
    exact h0.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) h1',
      ENNReal.mul_lt_top (by norm_num) h2'⟩)
  refine ⟨hfin, ?_⟩
  have hr0 : 0 < r := by linarith
  have hθ : 0 < C / r ^ 2 := by positivity
  have hm1 := (measurable_flipSumOne hG hGv i j r x).ennreal_toReal
  have hm2 := (measurable_flipSumTwo hG hGv i j r x).ennreal_toReal
  have hmax := IsOsBond.const_mul (c := 4) (by norm_num) (IsOsBond.max hs hθ hθ hm1 hm2 h1 h2)
  have e' : 4 * (max (C / r ^ 2) (C / r ^ 2) * 4 ^ (1 / s)) = 4 * C * 4 ^ (1 / s) / r ^ 2 := by
    rw [max_self]
    ring
  rw [e'] at hmax
  refine isOsBond_of_ae_le hs (by positivity)
    (Measurable.ennreal_toReal (Measurable.tsum fun e => ENNReal.measurable_ofReal.comp
      ((measurable_bondFlipDiff (measurable_heatCoarseComp hG hGv i j r x) e).pow_const 2)))
    ?_ hmax
  filter_upwards [hle, hf1, hf2] with ω h0 h1' h2'
  have hsum_lt : 2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω < ∞ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) h1', ENNReal.mul_lt_top (by norm_num) h2'⟩
  calc (heatFlipSum hG hGv i j r x ω).toReal
      ≤ (2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω).toReal :=
        ENNReal.toReal_mono hsum_lt.ne h0
    _ = 2 * (flipSumOne hG hGv i j r x ω).toReal + 2 * (flipSumTwo hG hGv i j r x ω).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_lt_top (by norm_num) h1').ne
          (ENNReal.mul_lt_top (by norm_num) h2').ne, ENNReal.toReal_mul, ENNReal.toReal_mul]
        norm_num
    _ ≤ 4 * max (flipSumOne hG hGv i j r x ω).toReal (flipSumTwo hG hGv i j r x ω).toReal := by
        have := le_max_left (flipSumOne hG hGv i j r x ω).toReal
          (flipSumTwo hG hGv i j r x ω).toReal
        have := le_max_right (flipSumOne hG hGv i j r x ω).toReal
          (flipSumTwo hG hGv i j r x ω).toReal
        linarith

end Rigidity.Corrector
