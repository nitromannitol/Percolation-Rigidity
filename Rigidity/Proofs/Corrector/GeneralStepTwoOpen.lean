import Rigidity.Proofs.Corrector.GeneralStepTwoCases
import Rigidity.Proofs.Corrector.GeneralStepOneLocal

/-!
# Step 2 of Lemma 3.3 of Dario on `ℤᵈ`: the term `T₂(e)` for an open bond, and the dipole

As in the planar files `DarioFlipTermTwoSummable`, `DarioStepTwoOpen` and `DarioStepTwoElectric`:

* `exists_edgeBond_eq`: every bond is the bond of an oriented lattice edge;
* `summable_heat_coarse_of_le`: the heat series of a coarse gradient with an `ℓ²` gradient
  converges;
* `edgeOpen_setBond_true_of_false`: an edge open in `ω^{e,0}` is open in `ω^{e,1}`;
* `ae_flipTermTwo_eq_open`: for a bond open in `ω`, `T₂(e)` through the potential of the Green
  projection of the field of the anchor paths;
* `ae_dipoleCoeff_eq`: the coefficient of the dipole in terms of the corrector of the
  configuration itself.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

/-- Every bond is the bond of an oriented lattice edge. -/
theorem exists_edgeBond_eq (e : Bond d) : ∃ a : LatticeEdge d, edgeBond a = e := by
  obtain ⟨_, x, y, rfl, h⟩ := e
  have hadj : (nearestNeighborGraph d).Adj x y := lattice_adj_iff_l1Dist.mpr h
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 hadj
  · exact ⟨(x, i), Subtype.ext (by simp [edgeBond, bondOfAdjacent, edgeHead, hi])⟩
  · exact ⟨(y, i), Subtype.ext (by simp [edgeBond, bondOfAdjacent, edgeHead, hi, Sym2.eq_swap])⟩

/-- **Convergence of the heat series of a coarse gradient with an `ℓ²` gradient**: on the
partition event, if `|∇u| ≤ |c| |g|` on the edges for a field `g ∈ ℓ²` and
`Σ_z Φ_{r²}(x, z) |stepRegion(z)| < ∞`, then `Σ_z Φ_{r²}(x, z) ∇_j[u]_𝒫(z)` converges. -/
theorem summable_heat_coarse_of_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) {r : ℝ}
    {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card)
    {u : Vertex d → ℝ} {c : ℝ} {g : EdgeField d} (hle : ∀ b, |edgeGrad ω u b| ≤ |c| * |g b|) :
    Summable fun z => zdHeat d (r ^ 2) x z *
      (u (partitionAnchor ω (z + LatticeProb.unit j)) - u (partitionAnchor ω z)) := by
  have hmem : Memℓp (edgeGrad ω u) 2 := by
    refine memℓp_gen' (C := c ^ 2 * ‖g‖ ^ 2) fun s => ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    calc ∑ b ∈ s, edgeGrad ω u b ^ 2 ≤ ∑ b ∈ s, c ^ 2 * g b ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h := hle b
          rw [← sq_abs (edgeGrad ω u b), ← sq_abs c, ← sq_abs (g b), ← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = c ^ 2 * ∑ b ∈ s, g b ^ 2 := by rw [Finset.mul_sum]
      _ ≤ c ^ 2 * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_sq_le_norm_sq g s) (sq_nonneg c)
  set G' : EdgeField d := ⟨edgeGrad ω u, hmem⟩ with hG'
  refine ((summable_heat_smul_pathField hP hS).mapL (innerSL ℝ G')).congr fun z => ?_
  simp only [innerSL_apply_apply]
  rw [real_inner_smul_right, inner_pathField]
  have hw := walkSum_eq_of_isGradOf ω (isGradOf_edgeGrad ω u) (coarseStepWalk hP z j)
  rw [show ((G' : LatticeEdge d → ℝ)) = edgeGrad ω u from rfl, hw]

theorem edgeOpen_setBond_true_of_false {a b : LatticeEdge d} {ω : Configuration d}
    (h : EdgeOpen (setBond (edgeBond a) false ω) b) :
    EdgeOpen (setBond (edgeBond a) true ω) b := by
  by_cases hba : b = a
  · subst hba
    exact absurd ((edgeOpen_setBond_self b false ω).1 h) (by simp)
  · exact (edgeOpen_setBond_iff_of_ne hba true ω).2 ((edgeOpen_setBond_iff_of_ne hba false ω).1 h)

section Planes

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The term (3.15)-(ii) per bond in Case 3, through `ω^{e,1}`.** -/
theorem ae_flipTermTwo_eq_open [NeZero d] (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (a : LatticeEdge d) (hP₁ : PartitionEvent (setBond (edgeBond a) true ω)),
      PartitionEvent (setBond (edgeBond a) false ω) →
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) →
      flipTermTwo hG hGv i j r x (edgeBond a) ω =
        (flipCorrector hG hGv i false (edgeBond a) ω a.1 -
            flipCorrector hG hGv i false (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) *
          (greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a +
            ∑' y, zdHeat d (r ^ 2) x y *
              partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
                (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) j y) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_correctedPlane_sub_eq_smul_greenProj hd hpc hp1,
    ae_summable_heat_stepRegion hd hpc hp1] with ω hG' hpl hS i j r hr x a hP₁ hP₀ hinf hreach
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).2 hinf
  have hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have hmem₀ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₀).supp :=
    fun v hv => (mem_uniqueInfiniteComponent_iff h₀ v).2 hv
  have hmem₁ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₁).supp := fun v hv =>
    (mem_uniqueInfiniteComponent_iff h₁ v).2 (infiniteComponentEvent_setBond_true hv true)
  have hA : ∀ z, (setBond (edgeBond a) false ω) ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) z) := fun z => by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor (Nat.pos_of_ne_zero (NeZero.ne d)) hP₀ z
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩ := ⟨_, rfl⟩
  -- `ℓ₁ - ℓ₀ - c' g` has no increment on the open edges of the cluster of `ω¹`
  have hFedge : ∀ b : LatticeEdge d, EdgeOpen (setBond (edgeBond a) true ω) b →
      b.1 ∈ (uniqueInfiniteComponent h₁).supp →
      (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₀ (edgeHead b)) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) (edgeHead b) =
        (extendComp _ ℓ₁ b.1 - extendComp _ ℓ₀ b.1) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) b.1 := by
    intro b hb hb1
    have key := hpl a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ b hb hb1
    rw [← hc'] at key
    have hgb := edgeGrad_clusterPot (ω := setBond (edgeBond a) true ω) (lp.single 2 a 1) hb
    rw [if_pos ((mem_uniqueInfiniteComponent_iff h₁ b.1).1 hb1)] at hgb
    simp only [edgeGrad, if_pos hb] at hgb
    linear_combination key - c' * hgb
  have ha₁ : a.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
  have hconst : ∀ v ∈ (uniqueInfiniteComponent h₁).supp,
      (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) v =
        (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₀ a.1) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) a.1 := by
    intro v hv
    have hreach' : (openGraph (setBond (edgeBond a) true ω)).Reachable a.1 v :=
      SimpleGraph.ConnectedComponent.exact
        (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ha₁).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hv).symm)
    exact (eq_of_walk_of_edge (S := (uniqueInfiniteComponent h₁).supp)
      (F := fun v => (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
        c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) v)
      (fun z w hz hzw => (uniqueInfiniteComponent h₁).mem_supp_of_adj_mem_supp hz hzw)
      hFedge hreach'.some ha₁).symm
  have hdiff : ∀ z,
      flipCorrector hG hGv i true (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) -
        flipCorrector hG hGv i false (edgeBond a) ω (guardAnchor (setBond (edgeBond a) false ω) z) =
      (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) z) -
          extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) z)) -
        (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) 0) -
          extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) 0)) := fun z => by
    rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ (hmem₁ _ (hA z))
        (hmem₁ _ (hA 0)),
      flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ (hmem₀ _ (hA z))
        (hmem₀ _ (hA 0))]
    ring
  have hconstA : ∀ z, (extendComp _ ℓ₁ (guardAnchor (setBond (edgeBond a) false ω) z) -
        extendComp _ ℓ₀ (guardAnchor (setBond (edgeBond a) false ω) z)) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)
            (guardAnchor (setBond (edgeBond a) false ω) z) =
        (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₀ a.1) -
          c' * clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1) a.1 :=
    fun z => hconst _ (hmem₁ _ (hA z))
  -- `T₂(e) = c' Φ * ∇_j[g]_{𝒫⁰}(x)`
  have hT : flipTermTwo hG hGv i j r x (edgeBond a) ω =
      c' * heatComp (fun z => clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)
        (partitionAnchor (setBond (edgeBond a) false ω) z)) r x j := by
    unfold flipTermTwo heatComp
    rw [← tsum_mul_left]
    refine tsum_congr fun y => ?_
    beta_reduce
    have e1 := hdiff (y + LatticeProb.unit j)
    have e2 := hdiff y
    have e3 := hconstA (y + LatticeProb.unit j)
    have e4 := hconstA y
    simp only [guardAnchor_of_event hP₀] at e1 e2 e3 e4 ⊢
    linear_combination zdHeat d (r ^ 2) x y * (e1 - e2 + e3 - e4)
  -- the change of partition for `g`
  have hle₁ : ∀ b, |edgeGrad (setBond (edgeBond a) true ω)
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) b| ≤
        |(1 : ℝ)| * |greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b| := fun b => by
    rw [abs_one, one_mul]
    exact abs_edgeGrad_clusterPot_le _ (lp.single 2 a 1) b
  have hle₀ : ∀ b, |edgeGrad (setBond (edgeBond a) false ω)
      (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) b| ≤
        |(1 : ℝ)| * |greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b| := fun b => by
    by_cases hb : EdgeOpen (setBond (edgeBond a) false ω) b
    · have e : edgeGrad (setBond (edgeBond a) false ω)
          (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) b =
          edgeGrad (setBond (edgeBond a) true ω)
            (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) b := by
        unfold edgeGrad
        rw [if_pos hb, if_pos (edgeOpen_setBond_true_of_false hb)]
      rw [e]
      exact hle₁ b
    · simp only [edgeGrad, if_neg hb, abs_zero]
      positivity
  have hs₁ := summable_heat_coarse_of_le hP₁ (hS (edgeBond a) true x j r hr) hle₁
  have hs₀ := summable_heat_coarse_of_le hP₀ (hS (edgeBond a) false x j r hr) hle₀
  have hsc : Summable fun y => zdHeat d (r ^ 2) x y *
      partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
        (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) j y := by
    refine (hs₀.sub hs₁).congr fun y => ?_
    simp only [partitionChange, guardAnchor_of_event hP₀, guardAnchor_of_event hP₁]
    ring
  have hpair : heatComp (fun z => clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)
      (partitionAnchor (setBond (edgeBond a) true ω) z)) r x j =
      greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a := by
    have h := heatComp_coarse_eq_smul_greenProj hP₁ (hS (edgeBond a) true x j r hr)
      (v := clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) (c := 1) (a := a)
      (fun b hb hinf => by
        rw [edgeGrad_clusterPot (lp.single 2 a 1) hb,
          if_pos (show setBond (edgeBond a) true ω ∈ infiniteComponentEvent b.1 from hinf),
          one_mul])
      (fun b hb hinf => by
        rw [edgeGrad_clusterPot (lp.single 2 a 1) hb,
          if_neg (show setBond (edgeBond a) true ω ∉ infiniteComponentEvent b.1 from hinf)])
    rwa [one_mul] at h
  have hsplit : heatComp (fun z => clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)
      (partitionAnchor (setBond (edgeBond a) false ω) z)) r x j =
      greenProj (setBond (edgeBond a) true ω) (coarseHeatField hP₁ r x j) a +
        ∑' y, zdHeat d (r ^ 2) x y *
          partitionChange (setBond (edgeBond a) true ω) (setBond (edgeBond a) false ω)
            (clusterPot (setBond (edgeBond a) true ω) (lp.single 2 a 1)) j y := by
    rw [← hpair]
    unfold heatComp
    rw [← hs₁.tsum_add hsc]
    refine tsum_congr fun y => ?_
    simp only [partitionChange, guardAnchor_of_event hP₀, guardAnchor_of_event hP₁]
    ring
  rw [hT, hsplit]
  congr 1
  rw [hc', flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hx (hmem₀ _ (hA 0)),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hy (hmem₀ _ (hA 0)),
    extendComp_of_mem _ _ hx, extendComp_of_mem _ _ hy]
  simp only [sum_single_mul_coord]
  ring

/-- **The two dipole coefficients of Case 3**: `ℓ₀(x) - ℓ₀(y) = (1 + R) (ℓ₁(x) - ℓ₁(y))` with
`0 ≤ R ≤ (4d (|B⁰(x)| + |B⁰(y)|))²`, `B⁰` the boxes `anchorBox` of the partition of `ω^{e,0}`. -/
theorem ae_dipoleCoeff_eq [NeZero d] (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i : Fin d) (a : LatticeEdge d),
      PartitionEvent (setBond (edgeBond a) false ω) →
      setBond (edgeBond a) false ω ∈ infiniteComponentEvent a.1 →
      (openGraph (setBond (edgeBond a) false ω)).Reachable a.1 (edgeHead a) →
      ∃ R : ℝ, 0 ≤ R ∧
        R ≤ (4 * d * (((anchorBox (setBond (edgeBond a) false ω) a.1).card : ℝ) +
          (anchorBox (setBond (edgeBond a) false ω) (edgeHead a)).card)) ^ 2 ∧
        flipCorrector hG hGv i false (edgeBond a) ω a.1 -
            flipCorrector hG hGv i false (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ)) =
          (1 + R) * (flipCorrector hG hGv i true (edgeBond a) ω a.1 -
            flipCorrector hG hGv i true (edgeBond a) ω (edgeHead a) +
            ((a.1 i : ℝ) - ((edgeHead a) i : ℝ))) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae,
    ae_correctedPlane_sub_eq_smul_greenProj_closed hd hpc hp1] with ω hG' hcl i a hP₀ hinf hreach
  obtain ⟨h₁, -⟩ := hGv (hG' (edgeBond a) true)
  obtain ⟨h₀, -⟩ := hGv (hG' (edgeBond a) false)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) true) h₁ (Pi.single i 1)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isCorrectedPlane hGv (hG' (edgeBond a) false) h₀ (Pi.single i 1)
  have hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp :=
    (mem_uniqueInfiniteComponent_iff h₀ a.1).2 hinf
  have hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hC := mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have hmem₀ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₀).supp :=
    fun v hv => (mem_uniqueInfiniteComponent_iff h₀ v).2 hv
  have hmem₁ : ∀ v, (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent v →
      v ∈ (uniqueInfiniteComponent h₁).supp := fun v hv =>
    (mem_uniqueInfiniteComponent_iff h₁ v).2 (infiniteComponentEvent_setBond_true hv true)
  have hA : (setBond (edgeBond a) false ω) ∈
      infiniteComponentEvent (guardAnchor (setBond (edgeBond a) false ω) 0) := by
    rw [guardAnchor_of_event hP₀]
    exact infinite_partitionAnchor (Nat.pos_of_ne_zero (NeZero.ne d)) hP₀ 0
  obtain ⟨pw⟩ := hreach
  have hspec := (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
    (pathField (setBond (edgeBond a) false ω) pw)).choose_spec
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a) := ⟨_, rfl⟩
  -- `ℓ₁ - ℓ₀ - c w₀` has no increment on the open edges of the cluster of `ω⁰`
  have hFedge : ∀ b : LatticeEdge d, EdgeOpen (setBond (edgeBond a) false ω) b →
      b.1 ∈ (uniqueInfiniteComponent h₀).supp →
      (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₀ (edgeHead b)) -
          c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
            (pathField (setBond (edgeBond a) false ω) pw)).choose (edgeHead b) =
        (extendComp _ ℓ₁ b.1 - extendComp _ ℓ₀ b.1) -
          c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
            (pathField (setBond (edgeBond a) false ω) pw)).choose b.1 := by
    intro b hb hb1
    have key := hcl a h₁ h₀ hx hy (Pi.single i 1) ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw b hb hb1
    rw [← hc, hspec b hb] at key
    linear_combination key
  have hFxy := eq_of_walk_of_edge (S := (uniqueInfiniteComponent h₀).supp)
    (F := fun v => (extendComp _ ℓ₁ v - extendComp _ ℓ₀ v) -
      c * (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose v)
    (fun z w hz hzw => (uniqueInfiniteComponent h₀).mem_supp_of_adj_mem_supp hz hzw) hFedge pw hx
  have hW := walkSum_eq_of_isGradOf _ hspec pw
  rw [← inner_pathField, inner_greenProj_self] at hW
  -- the bound on the effective resistance
  set ηn := ‖greenProj (setBond (edgeBond a) false ω)
    (pathField (setBond (edgeBond a) false ω) pw)‖ with hηn
  have hηn0 : 0 ≤ ηn := norm_nonneg _
  have hpot : ∀ b, |edgeGrad (setBond (edgeBond a) false ω)
      (clusterPot (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)) b| ≤ ηn := fun b => by
    refine (abs_edgeGrad_clusterPot_le _ _ b).trans ?_
    have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (greenProj (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw)) b
    rwa [Real.norm_eq_abs] at this
  have hreach' : ((openGraph (setBond (edgeBond a) false ω)).connectedComponentMk
      (edgeHead a)).supp.Infinite := by
    have : (openGraph (setBond (edgeBond a) false ω)).connectedComponentMk (edgeHead a) =
        (openGraph (setBond (edgeBond a) false ω)).connectedComponentMk a.1 :=
      (SimpleGraph.ConnectedComponent.sound pw.reachable).symm
    rw [this]
    exact hinf
  have hev := abs_sub_le_two_mul_edgeVariation hP₀ (lattice_adj_edgeHead a) hinf hreach'
    (clusterPot (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw))
  have hv1 := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) false ω)
    (anchorBox (setBond (edgeBond a) false ω) a.1) hηn0
    (fun u w huw => abs_sub_le_of_abs_edgeGrad_le hpot huw)
  have hv2 := edgeVariationIn_le_card_mul (ω := setBond (edgeBond a) false ω)
    (anchorBox (setBond (edgeBond a) false ω) (edgeHead a)) hηn0
    (fun u w huw => abs_sub_le_of_abs_edgeGrad_le hpot huw)
  have hcx : clusterPot (setBond (edgeBond a) false ω)
      (pathField (setBond (edgeBond a) false ω) pw) a.1 =
      (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose a.1 := if_pos hinf
  have hcy : clusterPot (setBond (edgeBond a) false ω)
      (pathField (setBond (edgeBond a) false ω) pw) (edgeHead a) =
      (exists_isGradOf_greenProj (setBond (edgeBond a) false ω)
        (pathField (setBond (edgeBond a) false ω) pw)).choose (edgeHead a) := if_pos hreach'
  rw [hcx, hcy, abs_sub_comm, ← hW, abs_of_nonneg (sq_nonneg _)] at hev
  set N : ℝ := ((anchorBox (setBond (edgeBond a) false ω) a.1).card : ℝ) +
    (anchorBox (setBond (edgeBond a) false ω) (edgeHead a)).card with hN
  have hN0 : 0 ≤ N := by positivity
  have hsq : ηn ^ 2 ≤ 4 * d * N * ηn := by
    have e : 4 * d * N * ηn = 4 * d * ((anchorBox (setBond (edgeBond a) false ω) a.1).card : ℝ) * ηn +
        4 * d * ((anchorBox (setBond (edgeBond a) false ω) (edgeHead a)).card : ℝ) * ηn := by
      rw [hN]; ring
    rw [e]
    linarith
  have hle : ηn ≤ 4 * d * N := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [mul_pos (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 4 * d * N) hlt) (sub_pos.2 hlt)]
  refine ⟨ηn ^ 2, sq_nonneg _, pow_le_pow_left₀ hηn0 hle 2, ?_⟩
  -- the identity
  have hx₁ : a.1 ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hx
  have hy₁ : edgeHead a ∈ (uniqueInfiniteComponent h₁).supp := (hC _).2 hy
  rw [flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hx (hmem₀ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) false) h₀ i hℓ₀ hy (hmem₀ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ hx₁ (hmem₁ _ hA),
    flipCorrector_eq_plane hG hGv (hG' (edgeBond a) true) h₁ i hℓ₁ hy₁ (hmem₁ _ hA)]
  simp only [sum_single_mul_coord]
  linear_combination -hFxy - c * hW + ηn ^ 2 * hc

end Planes

end Rigidity.Corrector.GeneralDim
