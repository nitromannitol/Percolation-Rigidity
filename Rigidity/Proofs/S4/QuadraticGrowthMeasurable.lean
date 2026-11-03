import Rigidity.Proofs.S4.TranslateDifference
import LatticeProb.Prob.Percolation.MeasurableRootedPlane

/-!
# The event `E` of Proposition 4.10 is null-measurable

Proof of `Rigidity.Steps.S4.QuadraticGrowthEventMeasurableStep` (paper L1463-1496 of the corrected
draft, where the measurability of `E` is left implicit). The event `E` asks for the existence of a
function on the cluster, so it is a projection. Encode a function `u` on the cluster of a root `o`
by its extension `U` by zero to `ℤ^d`, normalized by `U(o) = m ∈ ℤ`. The resulting relation
`rootedQuadraticGrowthRelation M b c o m` between configurations and functions `ℤ^d → ℝ` is Borel:
harmonicity, integrality and nonconstancy are countably many coordinate conditions, and
`|u(x) - p̄(x)| / |x| → 0` along the cofinite filter of the countable set `ℤ^d` is the convergence
of a countable family of measurable functions.

On the conull measurable set `G` where the cited corrector input holds (Armstrong-Dario,
`LatticeProb.External.SupercriticalBondCorrectorInput`), the normalized `U` is unique: the
difference of two solutions is harmonic and sublinear, hence a corrected plane of slope `0`
vanishing at `o`, hence zero. By the Lusin-Souslin theorem
(`MeasurableSet.image_of_measurable_injOn`) the projection of the relation over `G` is
measurable, so `E ∩ G` is measurable and `E` is null-measurable.
-/

namespace Rigidity.Proofs.S4

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4

/-- The cofinite filter of a countable type is countably generated. -/
theorem isCountablyGenerated_cofinite {α : Type*} [Countable α] :
    (cofinite : Filter α).IsCountablyGenerated :=
  (show (cofinite : Filter α).HasCountableBasis (fun s : Set α => s.Finite) compl from
    ⟨hasBasis_cofinite, Set.Countable.mono (s₁ := {s : Set α | s.Finite})
      (fun t (ht : t.Finite) => (⟨ht, Set.subset_univ t⟩ : t.Finite ∧ t ⊆ Set.univ))
      (Set.countable_setOf_finite_subset Set.countable_univ)⟩).isCountablyGenerated

/-- Convergence to `0` along the cofinite filter of a subset is convergence of the extension by
zero along the cofinite filter of the ambient type. -/
theorem tendsto_subtype_cofinite_iff_indicator {α : Type*} (s : Set α) (g : α → ℝ) :
    Tendsto (fun x : s => g x) cofinite (𝓝 0) ↔ Tendsto (s.indicator g) cofinite (𝓝 0) := by
  constructor
  · intro h
    rw [tendsto_def] at h ⊢
    intro V hV
    have h0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
    have hfin : ((fun x : s => g x) ⁻¹' V)ᶜ.Finite := mem_cofinite.mp (h V hV)
    refine mem_cofinite.mpr ((hfin.image Subtype.val).subset fun x hx => ?_)
    by_cases hxs : x ∈ s
    · refine ⟨⟨x, hxs⟩, ?_, rfl⟩
      simpa [Set.indicator_of_mem hxs] using hx
    · exact absurd (by simp [Set.indicator_of_notMem hxs, h0]) hx
  · intro h
    exact (h.comp Subtype.val_injective.tendsto_cofinite).congr fun x =>
      Set.indicator_of_mem x.property g

variable {d : ℕ}

/-- The Laplacian of a component is additive: it maps differences to differences. -/
theorem componentLaplacian_sub_apply {ω : Configuration d} (C : OpenComponent ω) (u v : C → ℝ)
    (x : C) :
    componentLaplacian C (fun y => u y - v y) x = componentLaplacian C u x - componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- With `o` in the support of a component, membership in the support is reachability from `o`. -/
theorem mem_supp_iff_reachable {ω : Configuration d} {C : OpenComponent ω} {o : Vertex d}
    (ho : o ∈ C.supp) (x : Vertex d) : x ∈ C.supp ↔ (openGraph ω).Reachable o x := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ho ⊢
  rw [← ho, SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The rooted encoding of the event `E` of Proposition 4.10: the function `U : ℤ^d → ℝ` takes the
value `m` at the root `o`, whose cluster is infinite, vanishes off that cluster, is integer-valued,
harmonic on the cluster, within `o(|x|)` of `p̄` on it, and not constant on it. -/
def rootedQuadraticGrowthRelation [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (c : ℝ) (o : Vertex d) (m : ℤ) : Set (Configuration d × (Vertex d → ℝ)) :=
  {z | z.1 ∈ infiniteComponentEvent o ∧ z.2 o = m ∧
    (∀ x, (openGraph z.1).Reachable o x → LatticeProb.Graph.laplacian (openGraph z.1) z.2 x = 0) ∧
    (∀ x, ¬ (openGraph z.1).Reachable o x → z.2 x = 0) ∧
    (∀ x, ∃ k : ℤ, z.2 x = k) ∧
    Tendsto ({x | (openGraph z.1).Reachable o x}.indicator
      fun x => |z.2 x - quadratic M b c x| / ∑ i, |(x i : ℝ)|) cofinite (𝓝 0) ∧
    ∃ x, (openGraph z.1).Reachable o x ∧ z.2 x ≠ m}

/-- The rooted encoding of `E` is a Borel relation. -/
theorem measurableSet_rootedQuadraticGrowthRelation [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (c : ℝ) (o : Vertex d) (m : ℤ) :
    MeasurableSet (rootedQuadraticGrowthRelation M b c o m) := by
  have hreach : ∀ x, MeasurableSet
      {z : Configuration d × (Vertex d → ℝ) | (openGraph z.1).Reachable o x} :=
    fun x => (measurableSet_openGraph_reachable o x).preimage measurable_fst
  have hcoord : ∀ x, Measurable fun z : Configuration d × (Vertex d → ℝ) => z.2 x :=
    fun x => (measurable_pi_apply x).comp measurable_snd
  simp only [rootedQuadraticGrowthRelation, Set.setOf_and]
  refine ((measurableSet_infiniteComponentEvent o).preimage measurable_fst).inter
    ((measurableSet_eq_fun (hcoord o) measurable_const).inter
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
      (MeasurableSet.inter ?_ ?_)))))
  · simp only [Set.setOf_forall, imp_iff_not_or, Set.setOf_or]
    exact MeasurableSet.iInter fun x => (hreach x).compl.union
      (measurableSet_eq_fun (measurable_laplacian_openGraph x) measurable_const)
  · simp only [Set.setOf_forall, imp_iff_not_or, not_not, Set.setOf_or]
    exact MeasurableSet.iInter fun x => (hreach x).union
      (measurableSet_eq_fun (hcoord x) measurable_const)
  · simp only [Set.setOf_forall, Set.setOf_exists]
    exact MeasurableSet.iInter fun x => MeasurableSet.iUnion fun k =>
      measurableSet_eq_fun (hcoord x) measurable_const
  · haveI : (cofinite : Filter (Vertex d)).IsCountablyGenerated := isCountablyGenerated_cofinite
    refine measurableSet_tendsto (𝓝 0) fun x => ?_
    classical
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    exact Measurable.ite (hreach x)
      ((continuous_abs.measurable.comp ((hcoord x).sub_const _)).div_const _) measurable_const
  · simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun x => (hreach x).inter
      (measurableSet_eq_fun (hcoord x) measurable_const).compl

/-- A point of `E` lies in the projection of the rooted relation, for the root `o = x` at any
vertex `x` of the cluster and the value `m = u(x)`. -/
theorem exists_mem_rootedQuadraticGrowthRelation [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    {b : Fin d → ℝ} {c : ℝ} {ω : Configuration d} (hE : ω ∈ quadraticGrowthEvent d M b c) :
    ∃ (o : Vertex d) (m : ℤ) (U : Vertex d → ℝ),
      (ω, U) ∈ rootedQuadraticGrowthRelation M b c o m := by
  obtain ⟨h, u, hu, hi, ht, x, y, hxy⟩ := hE
  obtain ⟨m, hm⟩ := hi x
  have hsupp := mem_supp_iff_reachable (C := uniqueInfiniteComponent h) x.property
  set U : Vertex d → ℝ := Function.extend Subtype.val u 0
  have hU : ∀ z : uniqueInfiniteComponent h, U z.val = u z := fun z => Subtype.val_injective.extend_apply u 0 z
  have hU0 : ∀ z, z ∉ (uniqueInfiniteComponent h).supp → U z = 0 := fun z hz =>
    Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => hz (ha ▸ a.property)
  refine ⟨x.val, m, U, ?_⟩
  simp only [rootedQuadraticGrowthRelation, Set.mem_setOf_eq]
  refine ⟨(mem_uniqueInfiniteComponent_iff h x.val).mp x.property, (hU x).trans hm,
    fun z hz => ?_, fun z hz => hU0 z fun hzC => hz ((hsupp z).mp hzC), fun z => ?_, ?_,
    y.val, (hsupp _).mp y.property, ?_⟩
  · rw [← componentLaplacian_restrict_eq (uniqueInfiniteComponent h) U ⟨z, (hsupp z).mpr hz⟩]
    have hUu : (fun y : uniqueInfiniteComponent h => U y.val) = u := funext hU
    rw [hUu]
    exact hu _
  · by_cases hzC : z ∈ (uniqueInfiniteComponent h).supp
    · obtain ⟨k, hk⟩ := hi ⟨z, hzC⟩
      exact ⟨k, (hU ⟨z, hzC⟩).trans hk⟩
    · exact ⟨0, by rw [hU0 z hzC, Int.cast_zero]⟩
  · have hset : {z | (openGraph ω).Reachable x.val z} = (uniqueInfiniteComponent h).supp :=
      Set.ext fun z => (hsupp z).symm
    rw [hset, ← tendsto_subtype_cofinite_iff_indicator]
    exact ht.congr fun z => by rw [hU]
  · rw [hU y, ← hm]
    exact fun h => hxy h.symm

/-- On a configuration with a unique infinite cluster, a point of the rooted relation gives a
point of `E`. -/
theorem mem_quadraticGrowthEvent_of_mem [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    {b : Fin d → ℝ} {c : ℝ} {ω : Configuration d} (h : HasUniqueInfiniteOpenComponent ω)
    {o : Vertex d} {m : ℤ} {U : Vertex d → ℝ}
    (hU : (ω, U) ∈ rootedQuadraticGrowthRelation M b c o m) :
    ω ∈ quadraticGrowthEvent d M b c := by
  simp only [rootedQuadraticGrowthRelation, Set.mem_setOf_eq] at hU
  obtain ⟨hinf, hUo, hharm, -, hint, ht, x, hx, hxm⟩ := hU
  set C := uniqueInfiniteComponent h
  have ho : o ∈ C.supp := (mem_uniqueInfiniteComponent_iff h o).mpr hinf
  have hsupp := mem_supp_iff_reachable ho
  have hset : {z | (openGraph ω).Reachable o z} = C.supp := Set.ext fun z => (hsupp z).symm
  rw [hset, ← tendsto_subtype_cofinite_iff_indicator] at ht
  refine ⟨h, fun z : C => U z.val, fun z => ?_, fun z => hint z.val, ht, ⟨o, ho⟩,
    ⟨x, (hsupp x).mpr hx⟩, ?_⟩
  · rw [componentLaplacian_restrict_eq]
    exact hharm _ ((hsupp _).mp z.property)
  · change U o ≠ U x
    rw [hUo]
    exact fun h => hxm h.symm

/-- Where the cited corrector clauses hold, the rooted relation has at most one point over each
configuration: the difference of two solutions is a sublinear harmonic function, hence a corrected
plane of slope `0` vanishing at the root, hence zero. -/
theorem eq_of_mem_rootedQuadraticGrowthRelation [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    {b : Fin d → ℝ} {c : ℝ} {ω : Configuration d} (hv : ω ∈ correctorValidEvent d)
    {o : Vertex d} {m : ℤ} {U U' : Vertex d → ℝ}
    (hU : (ω, U) ∈ rootedQuadraticGrowthRelation M b c o m)
    (hU' : (ω, U') ∈ rootedQuadraticGrowthRelation M b c o m) : U = U' := by
  simp only [rootedQuadraticGrowthRelation, Set.mem_setOf_eq] at hU hU'
  obtain ⟨hinf, hUo, hharm, hout, -, ht, -⟩ := hU
  obtain ⟨-, hUo', hharm', hout', -, ht', -⟩ := hU'
  set C := uniqueInfiniteComponent hv.1
  have ho : o ∈ C.supp := (mem_uniqueInfiniteComponent_iff hv.1 o).mpr hinf
  have hsupp := mem_supp_iff_reachable ho
  have hset : {z | (openGraph ω).Reachable o z} = C.supp := Set.ext fun z => (hsupp z).symm
  rw [hset, ← tendsto_subtype_cofinite_iff_indicator] at ht ht'
  have hw : ∀ z, componentLaplacian C (fun y : C => U y.val - U' y.val) z = 0 := by
    intro z
    rw [componentLaplacian_sub_apply, componentLaplacian_restrict_eq,
      componentLaplacian_restrict_eq, hharm _ ((hsupp _).mp z.property),
      hharm' _ ((hsupp _).mp z.property), sub_zero]
  have hwt : Tendsto (fun z : C => |(U z.val - U' z.val) - quadratic 0 0 0 z.val| /
      ∑ i, |(z.val i : ℝ)|) cofinite (𝓝 0) := by
    have hsum := ht.add ht'
    rw [add_zero] at hsum
    refine squeeze_zero (fun z => by positivity) (fun z => ?_) hsum
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hq : quadratic 0 0 0 z.val = 0 := by simp [quadratic]
    rw [hq, sub_zero]
    calc |U z.val - U' z.val|
        = |(U z.val - quadratic M b c z.val) - (U' z.val - quadratic M b c z.val)| := by ring_nf
      _ ≤ |U z.val - quadratic M b c z.val| + |U' z.val - quadratic M b c z.val| := abs_sub _ _
  have hplane := isCorrectedPlane_of_tendsto C 0 0 _ hw hwt
  obtain ⟨_, -, hunique⟩ := (hv.2 hv.1).1 0 ⟨o, ho⟩
  have hw0 : (fun y : C => U y.val - U' y.val) = fun _ => 0 :=
    (hunique _ ⟨hplane, by simp [hUo, hUo']⟩).trans
      (hunique _ ⟨isCorrectedPlane_const C 0, rfl⟩).symm
  funext z
  by_cases hz : (openGraph ω).Reachable o z
  · have hz0 := congrFun hw0 ⟨z, (hsupp z).mpr hz⟩
    simp only at hz0
    linarith
  · rw [hout z hz, hout' z hz]

/-- **The event `E` of Proposition 4.10 is null-measurable.** Over the conull measurable set
where the cited inputs hold, `E` is the countable union over roots `o` and values `m` of injective
projections of the Borel relations `rootedQuadraticGrowthRelation M b c o m`, measurable by the
Lusin-Souslin theorem. -/
theorem quadraticGrowthEventMeasurable [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    QuadraticGrowthEventMeasurableStep d p := by
  intro M b c
  obtain ⟨G, hG, hG1, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  set E := quadraticGrowthEvent d M b c
  have hEG : E ∩ G = ⋃ o : Vertex d, ⋃ m : ℤ,
      Prod.fst '' (rootedQuadraticGrowthRelation M b c o m ∩ G ×ˢ Set.univ) := by
    apply Set.Subset.antisymm
    · rintro ω ⟨hE, hωG⟩
      obtain ⟨o, m, U, hU⟩ := exists_mem_rootedQuadraticGrowthRelation hE
      exact Set.mem_iUnion.mpr ⟨o, Set.mem_iUnion.mpr
        ⟨m, ⟨(ω, U), ⟨hU, hωG, Set.mem_univ _⟩, rfl⟩⟩⟩
    · intro ω hω
      obtain ⟨o, hω⟩ := Set.mem_iUnion.mp hω
      obtain ⟨m, ⟨⟨ω', U⟩, ⟨hU, hωG, -⟩, rfl⟩⟩ := Set.mem_iUnion.mp hω
      exact ⟨mem_quadraticGrowthEvent_of_mem (hvalid hωG).1 hU, hωG⟩
  have hmeas : MeasurableSet (E ∩ G) := by
    rw [hEG]
    refine MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun m => ?_
    refine ((measurableSet_rootedQuadraticGrowthRelation M b c o m).inter
      (hG.prod MeasurableSet.univ)).image_of_measurable_injOn measurable_fst ?_
    rintro ⟨ω, U⟩ ⟨hU, hωG, -⟩ ⟨ω', U'⟩ ⟨hU', -, -⟩ hωω'
    change ω = ω' at hωω'
    subst hωω'
    rw [eq_of_mem_rootedQuadraticGrowthRelation (hvalid hωG) hU hU']
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G := (mem_ae_iff_prob_eq_one hG).mpr hG1
  refine hmeas.nullMeasurableSet.congr ?_
  filter_upwards [hGae] with ω hω
  exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩

/-- **Proposition 4.10** by Poincaré recurrence (`rationalMatrix_of_recurrence`), from the
cited inputs: almost surely the cluster carries no nonconstant integer-valued harmonic function
within `o(|x|)` of a given harmonic quadratic `p̄`. -/
theorem rationalMatrix [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Section4.RationalMatrixStmt d p :=
  rationalMatrix_of_recurrence hd p hpc hp1 hclassical hcorrector
    (quadraticGrowthEventMeasurable hd p hpc hp1 hclassical hcorrector)
    (translateDifference hd p hpc hp1 hcorrector)

end Rigidity.Proofs.S4
