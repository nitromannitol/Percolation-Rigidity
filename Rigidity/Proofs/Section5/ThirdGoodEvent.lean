import Rigidity.Steps.Section5.GoodEventLowerBound
import Rigidity.Steps.Section5.PrintedGoodEvents
import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Lemma 5.25: the printed third good event (L2370)

**The printed event, changed by [C32] in the corrected draft.** The draft `G_3(x, C_χ)` is
direction-free, and `ThirdGoodEventStep` is proved from Proposition 3.2 as printed in
`Rigidity/Proofs/Section5/ThirdGoodEventDirectionFree.lean`. This file treats the printed event
`eventG3Edge 0 C_χ` (the edge `(0, e₁)` of `𝒞_∞` across which `ℓ_{e₁}` increases by at least
`C_χ`), which needs the signed variant `HorizontalIncrementStep` of Proposition 3.2; it implies the
direction-free event (`eventG3Edge_subset`), so `thirdGoodEventStep_of_horizontalIncrement` still
gives `ThirdGoodEventStep`.

**Gap (L2370, "Theorem 3.1 and symmetry arguments").** Proposition 3.2 bounds from below the
probability of `|∇ℓ_{e₁}(0)| > L`, the sum of `|ℓ_{e₁}(e₁) - ℓ_{e₁}(0)|` and
`|ℓ_{e₁}(e₂) - ℓ_{e₁}(0)|`. The lattice symmetries `g` that map the slope `e₁` to `±e₁` are
the compositions of the translations and the reflections `x₁ ↦ -x₁`, `x₂ ↦ -x₂`; they carry `ℓ_{e₁}` to
`ℓ_{e₁} ∘ g` or `-ℓ_{e₁} ∘ g`, and in both cases the increment `ℓ(a + e₁) - ℓ(a)` along a
horizontal edge goes to an increment `ℓ(b + e₁) - ℓ(b)` of the same sign. So the symmetries
transfer neither a large gradient along `(0, e₂)` nor a large negative increment along `(0, e₁)`
to `G_3`. The printed proof of Proposition 3.2 does not give the signed bound either: its count
of the centre plane is one-sided, but Lemma 3.3 needs `|∇ℓ_{e₁}| ≤ L` on the removed edges.

The needed variant of Proposition 3.2 is carved as `HorizontalIncrementStep`: for every `L ≥ 1`,
with positive probability `(0, e₁)` is an edge of `𝒞_∞` with `ℓ_{e₁}(e₁) - ℓ_{e₁}(0) > L`.
`thirdGoodEventStep_of_horizontalIncrement` proves the rest: the uniqueness of the corrected
plane up to additive constants (`SupercriticalBondCorrectorInput`) turns "some corrected plane"
into "every corrected plane", and the measurable rooted plane field of Lattice-Probability makes
the event measurable. Proposition 3.2 itself (the hypothesis `NotLipschitzStmt` of the step) is
not used.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation LatticeProb.External

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5 Classical

/-- **Carved variant of Proposition 3.2** (L2370, see the module docstring): for every `L ≥ 1`,
with positive (outer) probability `(0, e₁)` is an edge of the infinite cluster across which a
corrected plane `ℓ_{e₁}` increases by more than `L`. -/
def HorizontalIncrementStep (p : unitInterval) : Prop :=
  ∀ L : ℝ, 1 ≤ L →
    latticeBondLaw 2 p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
      ∃ he : e1 ∈ (uniqueInfiniteComponent h).supp,
        (componentGraph _).Adj ⟨0, ho⟩ ⟨e1, he⟩ ∧
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u ∧
          L < u ⟨e1, he⟩ - u ⟨0, ho⟩} ≠ 0

variable {ω : Configuration 2}

/-- A corrected plane minus a constant, extended by zero off its component, is a corrected plane
of any equal component. -/
theorem isCorrectedPlane_extend_sub {C D : OpenComponent ω} (hDC : D = C) {q : Fin 2 → ℝ}
    {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (c : ℝ) :
    IsCorrectedPlane D q
      (fun x => if hx : x.val ∈ C.supp then ℓ ⟨x.val, hx⟩ - c else 0) := by
  subst hDC
  have heq : (fun x : D => if hx : x.val ∈ D.supp then ℓ ⟨x.val, hx⟩ - c else 0) =
      ℓ - fun _ => c := by
    funext x
    rw [dif_pos (show x.val ∈ D.supp from x.2)]
    rfl
  rw [heq]
  simpa only [sub_zero] using isCorrectedPlane_sub D hℓ (isCorrectedPlane_const D c)

/-- The measurable rooted plane field at the root `0` is a corrected plane of the unique infinite
cluster minus its value at the origin. -/
theorem rootedPlane_eq {G : Set (Configuration 2)}
    {F : (↥(G ∩ infiniteComponentEvent 0) × (Fin 2 → ℝ)) → (Vertex 2 → ℝ)}
    (hF : ∀ z U, (U 0 = 0 ∧
        IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk 0) z.2
          (fun x => U x.val) ∧
        ∀ x, ¬ (openGraph z.1.val).Reachable 0 x → U x = 0) ↔ F z = U)
    (z : ↥(G ∩ infiniteComponentEvent 0)) (h : HasUniqueInfiniteOpenComponent z.val)
    (ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp) {q : Fin 2 → ℝ}
    {ℓ : uniqueInfiniteComponent h → ℝ} (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ)
    {x : Vertex 2} (hx : x ∈ (uniqueInfiniteComponent h).supp) :
    F (z, q) x = ℓ ⟨x, hx⟩ - ℓ ⟨0, ho⟩ := by
  have hC0 : (openGraph z.val).connectedComponentMk 0 = uniqueInfiniteComponent h :=
    (eq_uniqueInfiniteComponent_iff h _).mpr z.2.2
  have hval := (hF (z, q) fun y =>
    if hy : y ∈ (uniqueInfiniteComponent h).supp then ℓ ⟨y, hy⟩ - ℓ ⟨0, ho⟩ else 0).mp
    ⟨by simp only [dif_pos ho, sub_self],
      isCorrectedPlane_extend_sub hC0 hℓ _,
      fun y hy => by
        refine dif_neg fun hy' => hy ?_
        exact SimpleGraph.ConnectedComponent.exact
          (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ho).trans
            ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy').symm)⟩
  rw [hval]
  exact dif_pos hx

/-- `ThirdGoodEventStep` of Lemma 5.25 through the printed event, from the carved signed
variant of Proposition 3.2:
a measurable event of positive probability inside the printed `eventG3Edge 0 C_χ`, which lies in the
direction-free `G_3(0, C_χ)`. -/
theorem thirdGoodEventStep_of_horizontalIncrement
    (hH : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      HorizontalIncrementStep p) : ThirdGoodEventStep := by
  intro hU p hpc hp1 _ Cχ hCχ
  set μ := latticeBondLaw 2 p
  set q : Fin 2 → ℝ := Pi.single 0 1
  have hbad := ae_iff.mp (hU 2 le_rfl p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  set G := Nᶜ ∩ uniqueInfiniteComponentEvent 2
  have hGm : MeasurableSet G :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : G ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  set T : Set ↥(G ∩ infiniteComponentEvent 0) :=
    {z | (openGraph z.val).Adj 0 e1 ∧ Cχ ≤ F (z, q) e1}
  have hT : MeasurableSet T := by
    refine (measurable_subtype_coe (measurableSet_openGraph_adj 0 e1)).inter ?_
    exact measurableSet_le measurable_const
      ((measurable_pi_apply e1).comp (hFm.comp (measurable_id.prodMk measurable_const)))
  refine ⟨Subtype.val '' T, Set.Subset.trans ?_ (eventG3Edge_subset 0 Cχ), hB.subtype_image hT, ?_⟩
  · rintro _ ⟨z, ⟨hadj, hval⟩, rfl⟩
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    have he : e1 ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have he' : (0 : Vertex 2) + e1 ∈ (uniqueInfiniteComponent h).supp := by
      rw [zero_add]; exact he
    refine ⟨h, ho, he', ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he').2
      (by rw [zero_add]; exact hadj), fun ℓ hℓ => ?_⟩
    rw [rootedPlane_eq hF z h ho hℓ he] at hval
    have h0e : ℓ ⟨(0 : Vertex 2) + e1, he'⟩ = ℓ ⟨e1, he⟩ :=
      congrArg ℓ (Subtype.ext (zero_add e1))
    rw [h0e]
    exact hval
  · have hS := hH p hpc hp1 Cχ hCχ
    refine pos_iff_ne_zero.mpr fun hA => hS (measure_mono_null ?_ (measure_union_null hA hN0))
    rintro ω ⟨h, ho, he, hadj, u, hu, hlt⟩
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨⟨ω, ⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩, ⟨?_, ?_⟩, rfl⟩
      · exact ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he).1 hadj
      · rw [rootedPlane_eq hF _ h ho hu he]
        exact hlt.le

end Rigidity.Proofs.Section5
