import Rigidity.Proofs.Corrector.GeneralFlipResampling

/-!
# The flip differences of Lemma 3.3 of Dario on `ℤᵈ` and the two terms of (3.15)

For the variable `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` of Dario's Lemma 3.3 on `ℤᵈ`
(`heatCoarseComp`, with the coarsened corrector `coarseField` of the partition into good cubes),
the flip form of (3.13) bounds `Σ_e (D_e X)²` (`heatFlipSum`). With the correctors `χ_b` of the
flips `ω^{e,b}`, rooted at the anchor `z̄⁰(0)` of the origin for `ω^{e,0}` (`flipCorrector`; this
point lies in the infinite cluster of both flips, since closing `e` only removes an edge), the
split (3.15) of Dario reads

`D_e X = T₁(e) + T₂(e)`, `T₁(e) = Σ_y Φ_{r²}(x, y) (∇_j[χ₁]_{𝒫¹}(y) - ∇_j[χ₁]_{𝒫⁰}(y))`,
`T₂(e) = Φ_{r²} * ∇_j[χ₁ - χ₀]_{𝒫⁰}(x)`

(`bondFlipDiff_eq_flipTermOne_add_flipTermTwo`), on the configurations whose flips lie in `G` and
in the partition event, when the heat series of `T₁` converges (`FlipTermOneSummable`; the heat
series of `∇[χ_b]_{𝒫^b}` converge almost surely for every flip, `ae_flipSeries_summable`). The term
`T₁` is the change of partition of Step 1 and `T₂` the change of corrector of Step 2;
`flipSumOne` and `flipSumTwo` are `Σ_e T₁(e)²` and `Σ_e T₂(e)²`. This is the planar construction of
`Rigidity.Corrector.flipTermOne` and `Rigidity.Corrector.flipTermTwo`, in every dimension.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Poincare.GeneralDim (zdHeat)
open scoped Classical ENNReal

variable {d : ℕ}

theorem openGraph_setBond_le (e : Bond d) (ω : Configuration d) :
    openGraph (setBond e false ω) ≤ openGraph (setBond e true ω) := by
  intro u v h
  obtain ⟨hl, hopen⟩ := (openGraph_adj_iff _ _ _).1 h
  refine (openGraph_adj_iff _ _ _).2 ⟨hl, ?_⟩
  by_cases he : bondOfAdjacent hl = e
  · rw [he, setBond, Function.update_self]
  · rw [setBond_apply_ne he] at hopen
    rw [setBond_apply_ne he]
    exact hopen

/-- Closing a bond shrinks the open components. -/
theorem supp_setBond_false_subset (e : Bond d) (ω : Configuration d) (u : Vertex d) :
    ((openGraph (setBond e false ω)).connectedComponentMk u).supp ⊆
      ((openGraph (setBond e true ω)).connectedComponentMk u).supp := by
  intro w hw
  refine (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
    (SimpleGraph.ConnectedComponent.sound ?_)
  exact SimpleGraph.Reachable.mono (openGraph_setBond_le e ω) (SimpleGraph.ConnectedComponent.exact
    ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw))

theorem infiniteComponentEvent_setBond_true {e : Bond d} {ω : Configuration d} {v : Vertex d}
    (h : setBond e false ω ∈ infiniteComponentEvent v) (b : Bool) :
    setBond e b ω ∈ infiniteComponentEvent v := by
  cases b
  · exact h
  · exact Set.Infinite.mono (supp_setBond_false_subset e ω v) h

/-- The heat average of a gradient does not see additive constants. -/
theorem heatComp_add_const (u : Vertex d → ℝ) (c r : ℝ) (x : Vertex d) (j : Fin d) :
    heatComp (fun z => u z + c) r x j = heatComp u r x j := by
  unfold heatComp
  exact tsum_congr fun y => by ring

/-- **The split (3.15), abstractly**: for functions `u₀, u₁` and anchor maps `A₀, A₁`,
`Φ * ∇_j(u₁ ∘ A₁) - Φ * ∇_j(u₀ ∘ A₀)` is the heat average of the change of anchors for `u₁`
plus `Φ * ∇_j((u₁ - u₀) ∘ A₀)`, when the three series converge. -/
theorem heatComp_sub_eq_split (A₀ A₁ : Vertex d → Vertex d) (u₀ u₁ : Vertex d → ℝ) (r : ℝ)
    (x : Vertex d) (j : Fin d)
    (hS₁ : Summable fun y => zdHeat d (r ^ 2) x y *
      (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y)))
    (hS₂ : Summable fun y => zdHeat d (r ^ 2) x y *
      (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y)))
    (hS₃ : Summable fun y => zdHeat d (r ^ 2) x y *
      (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))) :
    heatComp (fun z => u₁ (A₁ z)) r x j - heatComp (fun z => u₀ (A₀ z)) r x j =
      (∑' y, zdHeat d (r ^ 2) x y *
        ((u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y)) -
          (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y)))) +
        heatComp (fun z => u₁ (A₀ z) - u₀ (A₀ z)) r x j := by
  unfold heatComp
  calc (∑' y, zdHeat d (r ^ 2) x y * (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y))) -
        ∑' y, zdHeat d (r ^ 2) x y * (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))
      = ((∑' y, zdHeat d (r ^ 2) x y * (u₁ (A₁ (y + LatticeProb.unit j)) - u₁ (A₁ y))) -
          ∑' y, zdHeat d (r ^ 2) x y * (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y))) +
        ((∑' y, zdHeat d (r ^ 2) x y * (u₁ (A₀ (y + LatticeProb.unit j)) - u₁ (A₀ y))) -
          ∑' y, zdHeat d (r ^ 2) x y * (u₀ (A₀ (y + LatticeProb.unit j)) - u₀ (A₀ y))) := by
        ring
    _ = _ := by
        rw [← hS₁.tsum_sub hS₂, ← hS₂.tsum_sub hS₃]
        congr 1
        · exact tsum_congr fun y => by ring
        · exact tsum_congr fun y => by ring

section Terms

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The variable `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` of Dario's Lemma 3.3. -/
noncomputable def heatCoarseComp (i j : Fin d) (r : ℝ) (x : Vertex d) (ω : Configuration d) : ℝ :=
  heatComp (fun z => coarseField hG hGv i 0 z ω) r x j

/-- The flip sum `Σ_e (X(ω^{e,1}) - X(ω^{e,0}))²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)`. -/
noncomputable def heatFlipSum (i j : Fin d) (r : ℝ) (x : Vertex d) (ω : Configuration d) :
    ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω ^ 2)

theorem measurable_heatCoarseComp (i j : Fin d) (r : ℝ) (x : Vertex d) :
    Measurable (heatCoarseComp hG hGv i j r x) :=
  measurable_heatComp (fun z => measurable_coarseField hG hGv i 0 z) r x j

theorem measurable_heatFlipSum (i j : Fin d) (r : ℝ) (x : Vertex d) :
    Measurable (heatFlipSum hG hGv i j r x) :=
  Measurable.tsum fun e => ENNReal.measurable_ofReal.comp
    ((measurable_bondFlipDiff (measurable_heatCoarseComp hG hGv i j r x) e).pow_const 2)

theorem measurable_correctorDiff_comp_config (q : Fin d → ℝ)
    {f : Configuration d → Configuration d} (hf : Measurable f)
    {a b : Configuration d → Vertex d} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => correctorDiff hG hGv q (f ω) (a ω) (b ω) := by
  have h : Measurable fun x : Configuration d × (Vertex d × Vertex d) =>
      correctorDiff hG hGv q x.1 x.2.1 x.2.2 :=
    measurable_from_prod_countable_left fun ab => measurable_correctorDiff hG hGv q ab.1 ab.2
  exact h.comp (hf.prodMk (ha.prodMk hb))

/-- The corrector `χ_b` of the flip `ω^{e,b}`, rooted at the anchor `z̄⁰(0)` of the origin for the
partition of `ω^{e,0}`. -/
noncomputable def flipCorrector (i : Fin d) (b : Bool) (e : Bond d) (ω : Configuration d)
    (v : Vertex d) : ℝ :=
  correctorDiff hG hGv (Pi.single i 1) (setBond e b ω) v (guardAnchor (setBond e false ω) 0)

theorem measurable_guardAnchor_setBond (e : Bond d) (b : Bool) (z : Vertex d) :
    Measurable fun ω => guardAnchor (setBond e b ω) z :=
  (measurable_guardAnchor z).comp (measurable_setBond e b)

theorem measurable_flipCorrector_comp (i : Fin d) (b : Bool) (e : Bond d)
    {a : Configuration d → Vertex d} (ha : Measurable a) :
    Measurable fun ω => flipCorrector hG hGv i b e ω (a ω) :=
  measurable_correctorDiff_comp_config hG hGv _ (measurable_setBond e b) ha
    (measurable_guardAnchor_setBond e false 0)

/-- The term (3.15)-(i) in flip form: the heat average of the change of the coarse gradient of
`χ₁` from the partition of `ω^{e,1}` to that of `ω^{e,0}`. -/
noncomputable def flipTermOne (i j : Fin d) (r : ℝ) (x : Vertex d) (e : Bond d)
    (ω : Configuration d) : ℝ :=
  ∑' y, zdHeat d (r ^ 2) x y *
    ((flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) y)) -
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y)))

/-- The convergence of the heat series of the term (3.15)-(i). -/
def FlipTermOneSummable (i j : Fin d) (r : ℝ) (x : Vertex d) (e : Bond d) (ω : Configuration d) :
    Prop :=
  Summable fun y => zdHeat d (r ^ 2) x y *
    ((flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) y)) -
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y)))

/-- The term (3.15)-(ii) in flip form: `Φ_{r²} * ∇_j[χ₁ - χ₀]_{𝒫⁰}(x)`. -/
noncomputable def flipTermTwo (i j : Fin d) (r : ℝ) (x : Vertex d) (e : Bond d)
    (ω : Configuration d) : ℝ :=
  heatComp (fun z => flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) z) -
    flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) z)) r x j

/-- `Σ_e T₁(e)²`. -/
noncomputable def flipSumOne (i j : Fin d) (r : ℝ) (x : Vertex d) (ω : Configuration d) :
    ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2)

/-- `Σ_e T₂(e)²`. -/
noncomputable def flipSumTwo (i j : Fin d) (r : ℝ) (x : Vertex d) (ω : Configuration d) :
    ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2)

theorem measurable_flipTermOne (i j : Fin d) (r : ℝ) (x : Vertex d) (e : Bond d) :
    Measurable (flipTermOne hG hGv i j r x e) := by
  unfold flipTermOne
  refine Measurable.tsum fun y => Measurable.const_mul ?_ _
  have m := fun (b : Bool) (z : Vertex d) =>
    measurable_flipCorrector_comp hG hGv i true e (measurable_guardAnchor_setBond e b z)
  exact ((m true _).sub (m true _)).sub ((m false _).sub (m false _))

theorem measurable_flipTermTwo (i j : Fin d) (r : ℝ) (x : Vertex d) (e : Bond d) :
    Measurable (flipTermTwo hG hGv i j r x e) := by
  unfold flipTermTwo
  exact measurable_heatComp (fun z =>
    (measurable_flipCorrector_comp hG hGv i true e (measurable_guardAnchor_setBond e false z)).sub
      (measurable_flipCorrector_comp hG hGv i false e (measurable_guardAnchor_setBond e false z)))
    r x j

theorem measurable_flipSumOne (i j : Fin d) (r : ℝ) (x : Vertex d) :
    Measurable (flipSumOne hG hGv i j r x) :=
  Measurable.tsum fun e =>
    ENNReal.measurable_ofReal.comp ((measurable_flipTermOne hG hGv i j r x e).pow_const 2)

theorem measurable_flipSumTwo (i j : Fin d) (r : ℝ) (x : Vertex d) :
    Measurable (flipSumTwo hG hGv i j r x) :=
  Measurable.tsum fun e =>
    ENNReal.measurable_ofReal.comp ((measurable_flipTermTwo hG hGv i j r x e).pow_const 2)

variable [NeZero d]

/-- The root `z̄⁰(0)` of the flip correctors is in the infinite cluster of both flips. -/
theorem setBond_mem_infiniteComponentEvent_guardAnchor {e : Bond d} {ω : Configuration d}
    (hP₀ : PartitionEvent (setBond e false ω)) (b : Bool) (z : Vertex d) :
    setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e false ω) z) := by
  refine infiniteComponentEvent_setBond_true ?_ b
  rw [guardAnchor_of_event hP₀]
  exact infinite_partitionAnchor (Nat.pos_of_neZero d) hP₀ z

/-- On a flip in `G` and in the partition event, the variable of Lemma 3.3 is the heat average of
the coarse gradient of `χ_b`. -/
theorem heatCoarseComp_setBond_eq {e : Bond d} {ω : Configuration d} {b : Bool}
    (hω : setBond e b ω ∈ G) (hP : PartitionEvent (setBond e b ω))
    (hP₀ : PartitionEvent (setBond e false ω)) (i j : Fin d) (r : ℝ) (x : Vertex d) :
    heatCoarseComp hG hGv i j r x (setBond e b ω) =
      heatComp (fun z => flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) z)) r x j := by
  unfold heatCoarseComp
  have ho := setBond_mem_infiniteComponentEvent_guardAnchor hP₀ b 0
  have hA : ∀ z, setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e b ω) z) :=
    fun z => by
      rw [guardAnchor_of_event hP]
      exact infinite_partitionAnchor (Nat.pos_of_neZero d) hP z
  have e' : (fun z => coarseField hG hGv i 0 z (setBond e b ω)) = fun z =>
      flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) z) +
        -flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) 0) := by
    funext z
    unfold coarseField flipCorrector
    rw [shiftedAnchor_zero, shiftedAnchor_zero]
    have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA z) (hA 0) ho
    linarith
  rw [e', heatComp_add_const]

/-- The coarse gradient of `χ_b` for the partition of `ω^{e,b}` is that of the coarsened corrector
of `ω^{e,b}`. -/
theorem flipCorrector_sub_eq_coarseField_sub {e : Bond d} {ω : Configuration d} {b : Bool}
    (hω : setBond e b ω ∈ G) (hP : PartitionEvent (setBond e b ω))
    (hP₀ : PartitionEvent (setBond e false ω)) (i j : Fin d) (y : Vertex d) :
    flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) y) =
      coarseField hG hGv i 0 (y + LatticeProb.unit j) (setBond e b ω) -
        coarseField hG hGv i 0 y (setBond e b ω) := by
  have ho := setBond_mem_infiniteComponentEvent_guardAnchor hP₀ b 0
  have hA : ∀ z, setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e b ω) z) :=
    fun z => by
      rw [guardAnchor_of_event hP]
      exact infinite_partitionAnchor (Nat.pos_of_neZero d) hP z
  unfold flipCorrector coarseField
  simp only [shiftedAnchor_zero]
  have h1 := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA (y + LatticeProb.unit j))
    (hA y) ho
  have h2 := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA (y + LatticeProb.unit j))
    (hA y) (hA 0)
  linarith

/-- **The heat series of the flips converge**: almost surely, for every bond, flip, point,
direction and radius `r > 0`, the heat series of the coarse gradient of `χ_b` for the partition of
`ω^{e,b}` converges. -/
theorem ae_flipSeries_summable (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (e : Bond d) (b : Bool) (x : Vertex d) (j : Fin d) (r : ℝ),
      0 < r → Summable fun y => zdHeat d (r ^ 2) x y *
        (flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) (y + LatticeProb.unit j)) -
          flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) y)) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have h := ae_summable_heat_coarseField hG hGv hd hpc hp1 hGae i
  filter_upwards [ae_setBond hp0 hp1 h, ae_setBond hp0 hp1 hGae,
    ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)] with ω hS hG' hP' e b x j r hr
  refine (hS e b x j r hr).congr fun y => ?_
  rw [flipCorrector_sub_eq_coarseField_sub hG hGv (hG' e b) (hP' e b) (hP' e false) i j y]

/-- **The split (3.15) in flip form**: `D_e X = T₁(e) + T₂(e)`, when the heat series of `T₁` and of
`∇[χ_b]_{𝒫^b}` for both flips converge. -/
theorem bondFlipDiff_eq_flipTermOne_add_flipTermTwo {e : Bond d} {ω : Configuration d}
    (hω₁ : setBond e true ω ∈ G) (hω₀ : setBond e false ω ∈ G)
    (hP₁ : PartitionEvent (setBond e true ω)) (hP₀ : PartitionEvent (setBond e false ω))
    (i j : Fin d) (r : ℝ) (x : Vertex d)
    (hS : ∀ b : Bool, Summable fun y => zdHeat d (r ^ 2) x y *
      (flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) y)))
    (hT : FlipTermOneSummable hG hGv i j r x e ω) :
    bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω =
      flipTermOne hG hGv i j r x e ω + flipTermTwo hG hGv i j r x e ω := by
  have hS₂ : Summable fun y => zdHeat d (r ^ 2) x y *
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y)) :=
    ((hS true).sub hT).congr fun y => by ring
  unfold bondFlipDiff
  rw [heatCoarseComp_setBond_eq hG hGv hω₁ hP₁ hP₀ i j r x,
    heatCoarseComp_setBond_eq hG hGv hω₀ hP₀ hP₀ i j r x,
    heatComp_sub_eq_split _ _ _ _ r x j (hS true) hS₂ (hS false)]
  rfl

end Terms

end Rigidity.Corrector.GeneralDim
