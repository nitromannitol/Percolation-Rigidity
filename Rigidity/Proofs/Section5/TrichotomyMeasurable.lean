import Rigidity.Proofs.Section5.FlipSteps
import LatticeProb.Prob.Percolation.RootedCorrectedPlaneBorel
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Proposition 5.7: the event `E` is null-measurable

Proof of `Rigidity.Steps.Section5.TrichotomyEventMeasurableStep` (the measurability of the event
`E` of L1741 of the corrected draft, used by Step 1 of the proof of Proposition 5.7 and left
implicit in the paper), for `f` finitely supported, from the Liouville theorem at order zero
(`SublinearLiouville p`).

The event `E` asks for the existence of a Green family `G`, a corrected plane `ℓ` and a limit
`L` on the unique infinite cluster, so it is a projection. Fix a root `o` and encode `G` and `ℓ`
by their extensions by zero to `ℤ²`, normalized by `ℓ(o) = 0`; this normalization is harmless
since `Σ f = 0`. The resulting relation `rootedFailureRelation f q o` between configurations and
witnesses `(G, ℓ, L)` is Borel: the Green equation, the normalization and the sublinear growth of
the columns are countably many coordinate conditions, the corrected-plane conditions are Borel
(`measurableSet_rooted_encoded_correctedPlane`), the sums against `f` are finite sums, the
convergence of `u_f` to `L` is the convergence of a countable family of measurable functions, and
the infinitude of the support of `u_f - L` is a countable condition.

On the measurable conull set where Liouville at order zero holds, the witnesses are unique:
two Green columns at `y` differ by a sublinear harmonic function vanishing at `y`, two
normalized corrected planes of slope `q` by one vanishing at `o`, and `L` is a limit along the
cofinite filter of an infinite set. By the Lusin-Souslin theorem
(`MeasurableSet.image_of_measurable_injOn`, as in
`Rigidity.Proofs.S4.quadraticGrowthEventMeasurable`) the projection of the relation over that set
is measurable, so `E` is null-measurable.

* `trichotomyEventMeasurable q hLiou hf : TrichotomyEventMeasurableStep p f q`;
* `trichotomyEventMeasurable_of_inputs`: the same for `p_c < p < 1` from the cited input
  `LatticeProb.External.ArmstrongDarioOrderZero`.

No hypothesis on `q` is used. The assumption `f` finitely supported is the one of Proposition 5.7
(`GradientTrichotomyStmt p f` assumes it before fixing `q`).
-/

namespace Rigidity.Proofs.Section5

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section5
  Rigidity.Steps.Section5 Classical

section Deterministic

variable {ω : Configuration 2}

/-- The witnesses of the event `E` of L1741 on an arbitrary open component `C`: `Σ f = 0`, a
Green family `G`, a corrected plane `ℓ` of slope `q` with `Σ f ℓ = 0`, and a limit `L` of `u_f`
at infinity such that `u_f - L` has infinite support. -/
def IsFailureOn (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) (C : OpenComponent ω) (G : C → C → ℝ)
    (ℓ : C → ℝ) (L : ℝ) : Prop :=
  mass C f = 0 ∧ IsGreenFamily C G ∧ IsCorrectedPlane C q ℓ ∧ pairing C f ℓ = 0 ∧
    Tendsto (potential C G f) cofinite (𝓝 L) ∧
    (Function.support fun x => potential C G f x - L).Infinite

theorem exists_isFailureOn_congr {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} {C C' : OpenComponent ω}
    (hC : C = C') :
    (∃ G ℓ L, IsFailureOn f q C G ℓ L) ↔ ∃ G ℓ L, IsFailureOn f q C' G ℓ L := by
  subst hC
  rfl

/-- Membership in the component of `o` is reachability from `o`. -/
theorem mem_connectedComponentMk_iff (o x : Vertex 2) :
    x ∈ (openGraph ω).connectedComponentMk o ↔ (openGraph ω).Reachable o x := by
  change x ∈ ((openGraph ω).connectedComponentMk o).supp ↔ _
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- A sum over the component of `o` of a function supported in a finite set `S` is a finite sum
over `S`. -/
theorem finsum_rooted_eq {M : Type*} [AddCommMonoid M] (o : Vertex 2) (S : Finset (Vertex 2))
    (F : Vertex 2 → M) (hF : ∀ y, F y ≠ 0 → y ∈ S) :
    ∑ᶠ y : (openGraph ω).connectedComponentMk o, F y.val =
      ∑ y ∈ S, if (openGraph ω).Reachable o y then F y else 0 := by
  classical
  rw [finsum_subtype_eq_finsum_cond (fun y => y ∈ (openGraph ω).connectedComponentMk o),
    finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun y _ => by
      rw [finsum_eq_if]
      exact if_congr (mem_connectedComponentMk_iff o y) rfl rfl
  · intro y hy
    refine hF y fun h0 => hy ?_
    simp [h0]

/-- The Laplacian of a component maps differences to differences. -/
theorem componentLaplacian_sub_apply' (C : OpenComponent ω) (u v : C → ℝ) (x : C) :
    componentLaplacian C (fun y => u y - v y) x =
      componentLaplacian C u x - componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Under Liouville at order zero, a Green column is unique. -/
theorem eq_of_isGreenColumn {C : OpenComponent ω} (hL : HasSublinearLiouville C) {y : C}
    {g g' : C → ℝ} (hg : IsGreenColumn 2 le_rfl C y g) (hg' : IsGreenColumn 2 le_rfl C y g') :
    g = g' := by
  obtain ⟨c, hc⟩ := hL (fun x => g x - g' x)
    (fun x => by
      rw [componentLaplacian_sub_apply']
      have h1 := hg.1 x
      have h2 := hg'.1 x
      linarith)
    ((isSublinearOn_column hg).sub (isSublinearOn_column hg'))
  have hy := hc y
  rw [(hg.2.1 rfl).1, (hg'.2.1 rfl).1, sub_zero] at hy
  funext x
  have hx := hc x
  linarith

/-- Under Liouville at order zero, two corrected planes of the same slope agreeing at one point
are equal. -/
theorem eq_of_isCorrectedPlane {C : OpenComponent ω} (hL : HasSublinearLiouville C)
    {q : Fin 2 → ℝ} {u u' : C → ℝ} (hu : IsCorrectedPlane C q u) (hu' : IsCorrectedPlane C q u')
    (o : C) (ho : u o = u' o) : u = u' := by
  obtain ⟨c, hc⟩ := hL (fun x => u x - u' x)
    (fun x => by rw [componentLaplacian_sub_apply', hu.1.1 x, hu'.1.1 x, sub_zero])
    (((isSublinearOn_of_slope hu.2).sub (isSublinearOn_of_slope hu'.2)).congr fun x => by ring)
  have h0 := hc o
  rw [ho, sub_self] at h0
  funext x
  have hx := hc x
  linarith

end Deterministic

/-- The witnesses `(G, ℓ, L)`, with `G` and `ℓ` extended by zero to `ℤ²`. -/
abbrev FailureWitness : Type := (Vertex 2 → Vertex 2 → ℝ) × ((Vertex 2 → ℝ) × ℝ)

instance standardBorelSpace_kernel : StandardBorelSpace (Vertex 2 → Vertex 2 → ℝ) :=
  inferInstance

instance standardBorelSpace_planeLimit : StandardBorelSpace ((Vertex 2 → ℝ) × ℝ) :=
  inferInstance

instance standardBorelSpace_failureWitness : StandardBorelSpace FailureWitness :=
  StandardBorelSpace.prod

instance standardBorelSpace_configuration_failureWitness :
    StandardBorelSpace (Configuration 2 × FailureWitness) :=
  StandardBorelSpace.prod

/-- The rooted encoding of the event `E`: the cluster is unique and contains the root `o`, the
encoded `G` and `ℓ` vanish off the cluster, `ℓ(o) = 0`, and the restrictions are witnesses of
`E` on the cluster. -/
def rootedFailureRelation (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) (o : Vertex 2) :
    Set (Configuration 2 × FailureWitness) :=
  {z | z.1 ∈ uniqueInfiniteComponentEvent 2 ∧ z.1 ∈ infiniteComponentEvent o ∧
    (∀ x y, ¬ ((openGraph z.1).Reachable o x ∧ (openGraph z.1).Reachable o y) →
      z.2.1 x y = 0) ∧
    (z.2.2.1 o = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk o) q
      (fun x => z.2.2.1 x.val) ∧ ∀ x, ¬ (openGraph z.1).Reachable o x → z.2.2.1 x = 0) ∧
    IsFailureOn f q ((openGraph z.1).connectedComponentMk o) (fun x y => z.2.1 x.val y.val)
      (fun x => z.2.2.1 x.val) z.2.2.2}

section Measurability

variable {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} {o : Vertex 2}

/-- The finite sum `Σ_{y ∈ S, y ∈ 𝒞(o)} f(y) G(x, y)`, the encoded potential `u_f(x)`. -/
noncomputable def rootedPotential (S : Finset (Vertex 2)) (f : Vertex 2 → ℤ) (o : Vertex 2)
    (z : Configuration 2 × FailureWitness) (x : Vertex 2) : ℝ :=
  ∑ y ∈ S, if (openGraph z.1).Reachable o y then (f y : ℝ) * z.2.1 x y else 0

theorem measurable_reachable (o x : Vertex 2) :
    Measurable fun z : Configuration 2 × FailureWitness => (openGraph z.1).Reachable o x :=
  measurableSet_setOf.1 ((measurableSet_openGraph_reachable o x).preimage measurable_fst)

theorem measurable_kernel (x y : Vertex 2) :
    Measurable fun z : Configuration 2 × FailureWitness => z.2.1 x y :=
  (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd))

theorem measurable_plane (x : Vertex 2) :
    Measurable fun z : Configuration 2 × FailureWitness => z.2.2.1 x :=
  (measurable_pi_apply x).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))

theorem measurable_rootedPotential (S : Finset (Vertex 2)) (x : Vertex 2) :
    Measurable fun z => rootedPotential S f o z x :=
  Finset.measurable_sum _ fun y _ =>
    Measurable.ite (measurableSet_setOf.2 (measurable_reachable o y))
      ((measurable_kernel x y).const_mul _) measurable_const

/-- The cofinite filter of a countable type is countably generated. -/
theorem isCountablyGenerated_cofinite' {α : Type*} [Countable α] :
    (cofinite : Filter α).IsCountablyGenerated :=
  (show (cofinite : Filter α).HasCountableBasis (fun s : Set α => s.Finite) compl from
    ⟨hasBasis_cofinite, Set.Countable.mono (s₁ := {s : Set α | s.Finite})
      (fun t (ht : t.Finite) => (⟨ht, Set.subset_univ t⟩ : t.Finite ∧ t ⊆ Set.univ))
      (Set.countable_setOf_finite_subset Set.countable_univ)⟩).isCountablyGenerated

/-- Countable characterization of infinitude. -/
theorem measurable_setOf_infinite {α : Type*} [MeasurableSpace α] {Q : α → Vertex 2 → Prop}
    (hQ : ∀ x, Measurable fun a => Q a x) : Measurable fun a => {x | Q a x}.Infinite := by
  have h : (fun a => {x | Q a x}.Infinite) =
      fun a => ∀ s : Finset (Vertex 2), ∃ x, x ∉ s ∧ Q a x := by
    funext a
    apply propext
    constructor
    · intro h s
      obtain ⟨x, hx, hxs⟩ := h.exists_notMem_finset s
      exact ⟨x, hxs, hx⟩
    · intro h hfin
      obtain ⟨x, hxs, hx⟩ := h hfin.toFinset
      exact hxs (hfin.mem_toFinset.2 hx)
  rw [h]
  exact Measurable.forall fun s => Measurable.exists fun x => measurable_const.and (hQ x)

/-- Convergence along the cofinite filter of a subtype is convergence of the extension by zero. -/
theorem tendsto_subtype_cofinite_iff_indicator' {α : Type*} (P : α → Prop) (g : α → ℝ) :
    Tendsto (fun x : Subtype P => g x) cofinite (𝓝 0) ↔
      Tendsto ({x | P x}.indicator g) cofinite (𝓝 0) := by
  constructor
  · intro h
    rw [tendsto_def] at h ⊢
    intro V hV
    have h0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
    have hfin : ((fun x : Subtype P => g x) ⁻¹' V)ᶜ.Finite := mem_cofinite.mp (h V hV)
    refine mem_cofinite.mpr ((hfin.image Subtype.val).subset fun x hx => ?_)
    by_cases hxs : P x
    · refine ⟨⟨x, hxs⟩, ?_, rfl⟩
      simpa [Set.indicator_of_mem (show x ∈ {x | P x} from hxs)] using hx
    · exact absurd (by simp [Set.indicator_of_notMem (show x ∉ {x | P x} from hxs), h0]) hx
  · intro h
    exact (h.comp Subtype.val_injective.tendsto_cofinite).congr fun x =>
      Set.indicator_of_mem (show x.val ∈ {x | P x} from x.property) g

variable (hf : (Function.support f).Finite)
include hf

theorem potential_rooted_eq (z : Configuration 2 × FailureWitness)
    (x : (openGraph z.1).connectedComponentMk o) :
    potential _ (fun x y => z.2.1 x.val y.val) f x = rootedPotential hf.toFinset f o z x.val := by
  refine finsum_rooted_eq o hf.toFinset (fun y => (f y : ℝ) * z.2.1 x.val y) fun y hy => ?_
  exact hf.mem_toFinset.2 fun h0 => hy (by simp [h0])

theorem mass_rooted_eq_zero_iff (ω : Configuration 2) :
    mass ((openGraph ω).connectedComponentMk o) f = 0 ↔
      ∑ y ∈ hf.toFinset, (if (openGraph ω).Reachable o y then (f y : ℝ) else 0) = 0 := by
  rw [mass, finsum_rooted_eq o hf.toFinset (fun y => f y) fun y hy => hf.mem_toFinset.2 hy,
    ← Int.cast_eq_zero (α := ℝ)]
  push_cast
  rfl

theorem pairing_rooted_eq (ω : Configuration 2) (U : Vertex 2 → ℝ) :
    pairing ((openGraph ω).connectedComponentMk o) f (fun x => U x.val) =
      ∑ y ∈ hf.toFinset, if (openGraph ω).Reachable o y then (f y : ℝ) * U y else 0 :=
  finsum_rooted_eq o hf.toFinset (fun y => (f y : ℝ) * U y) fun y hy =>
    hf.mem_toFinset.2 fun h0 => hy (by simp [h0])

omit hf in
/-- The Green-family condition on the encoded kernel, in coordinates. -/
theorem isGreenFamily_rooted_iff (ω : Configuration 2) (Γ : Vertex 2 → Vertex 2 → ℝ) :
    IsGreenFamily ((openGraph ω).connectedComponentMk o) (fun x y => Γ x.val y.val) ↔
      ∀ y, (openGraph ω).Reachable o y →
        (∀ x, (openGraph ω).Reachable o x →
          -LatticeProb.Graph.laplacian (openGraph ω) (fun w => Γ w y) x =
            if x = y then 1 else 0) ∧
        Γ y y = 0 ∧
        ∀ k : ℕ, ∃ N : ℕ, ∀ x, (openGraph ω).Reachable o x → (N : ℝ) ≤ eucl x →
          |Γ x y| ≤ 1 / (k + 1 : ℝ) * eucl x := by
  set K := (openGraph ω).connectedComponentMk o
  constructor
  · intro hG y hy
    obtain ⟨h1, h2, -⟩ := hG ⟨y, (mem_connectedComponentMk_iff o y).2 hy⟩
    obtain ⟨h2a, h2b⟩ := h2 rfl
    refine ⟨fun x hx => ?_, h2a, fun k => ?_⟩
    · have h := h1 ⟨x, (mem_connectedComponentMk_iff o x).2 hx⟩
      rw [componentLaplacian_restrict_eq K (fun w => Γ w y)] at h
      rw [h]
      exact if_congr Subtype.ext_iff rfl rfl
    · obtain ⟨R, -, hR⟩ := h2b (1 / (k + 1 : ℝ)) (by positivity)
      refine ⟨⌈R⌉₊, fun x hx hN => ?_⟩
      exact hR ⟨x, (mem_connectedComponentMk_iff o x).2 hx⟩ ((Nat.le_ceil R).trans hN)
  · intro h y
    obtain ⟨h1, h2, h3⟩ := h y.val ((mem_connectedComponentMk_iff o y.val).1 y.property)
    refine ⟨fun x => ?_, fun _ => ⟨h2, fun ε hε => ?_⟩, fun h3 => absurd h3 (by norm_num)⟩
    · rw [componentLaplacian_restrict_eq K (fun w => Γ w y.val),
        h1 x.val ((mem_connectedComponentMk_iff o x.val).1 x.property)]
      exact if_congr Subtype.ext_iff.symm rfl rfl
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h3 k
      refine ⟨max (N : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
      have hb := hN x.val ((mem_connectedComponentMk_iff o x.val).1 x.property)
        ((le_max_left _ _).trans hx)
      exact hb.trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

theorem tendsto_potential_rooted_iff (z : Configuration 2 × FailureWitness) :
    Tendsto (potential ((openGraph z.1).connectedComponentMk o)
        (fun x y => z.2.1 x.val y.val) f) cofinite (𝓝 z.2.2.2) ↔
      Tendsto ({x | (openGraph z.1).Reachable o x}.indicator
        fun x => rootedPotential hf.toFinset f o z x - z.2.2.2) cofinite (𝓝 0) := by
  have hpot : potential ((openGraph z.1).connectedComponentMk o)
      (fun x y => z.2.1 x.val y.val) f = fun x => rootedPotential hf.toFinset f o z x.val :=
    funext (potential_rooted_eq hf z)
  have hset : {x | x ∈ (openGraph z.1).connectedComponentMk o} =
      {x | (openGraph z.1).Reachable o x} := Set.ext fun x => mem_connectedComponentMk_iff o x
  rw [hpot, ← tendsto_sub_nhds_zero_iff, ← hset]
  exact tendsto_subtype_cofinite_iff_indicator' _
    (fun x => rootedPotential hf.toFinset f o z x - z.2.2.2)

theorem support_potential_rooted_infinite_iff (z : Configuration 2 × FailureWitness) :
    (Function.support fun x => potential ((openGraph z.1).connectedComponentMk o)
        (fun x y => z.2.1 x.val y.val) f x - z.2.2.2).Infinite ↔
      {x | (openGraph z.1).Reachable o x ∧
        rootedPotential hf.toFinset f o z x - z.2.2.2 ≠ 0}.Infinite := by
  have himg : Subtype.val '' (Function.support fun x => potential
      ((openGraph z.1).connectedComponentMk o) (fun x y => z.2.1 x.val y.val) f x - z.2.2.2) =
      {x | (openGraph z.1).Reachable o x ∧
        rootedPotential hf.toFinset f o z x - z.2.2.2 ≠ 0} := by
    ext x
    simp only [Set.mem_image, Function.mem_support, Set.mem_setOf_eq, potential_rooted_eq hf z]
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨(mem_connectedComponentMk_iff o _).1 x'.property, hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, (mem_connectedComponentMk_iff o x).2 hx⟩, hx', rfl⟩
  rw [← himg, Set.infinite_image_iff Subtype.val_injective.injOn]

/-- The rooted encoding of `E` is a Borel relation. -/
theorem measurableSet_rootedFailureRelation : MeasurableSet (rootedFailureRelation f q o) := by
  have hR := measurable_reachable o
  have hΓ := measurable_kernel
  have hU := measurable_plane
  have hLm : Measurable fun z : Configuration 2 × FailureWitness => z.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hP := measurable_rootedPotential (f := f) (o := o) hf.toFinset
  have hset : rootedFailureRelation f q o =
      {z : Configuration 2 × FailureWitness | z.1 ∈ uniqueInfiniteComponentEvent 2} ∩
      {z | z.1 ∈ infiniteComponentEvent o} ∩
      {z | ∀ x y, ¬ ((openGraph z.1).Reachable o x ∧ (openGraph z.1).Reachable o y) →
        z.2.1 x y = 0} ∩
      {z | z.2.2.1 o = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk o) q
        (fun x => z.2.2.1 x.val) ∧ ∀ x, ¬ (openGraph z.1).Reachable o x → z.2.2.1 x = 0} ∩
      {z | ∑ y ∈ hf.toFinset, (if (openGraph z.1).Reachable o y then (f y : ℝ) else 0) = 0} ∩
      {z | ∀ y, (openGraph z.1).Reachable o y →
        (∀ x, (openGraph z.1).Reachable o x →
          -LatticeProb.Graph.laplacian (openGraph z.1) (fun w => z.2.1 w y) x =
            if x = y then 1 else 0) ∧
        z.2.1 y y = 0 ∧
        ∀ k : ℕ, ∃ N : ℕ, ∀ x, (openGraph z.1).Reachable o x → (N : ℝ) ≤ eucl x →
          |z.2.1 x y| ≤ 1 / (k + 1 : ℝ) * eucl x} ∩
      {z | ∑ y ∈ hf.toFinset,
        (if (openGraph z.1).Reachable o y then (f y : ℝ) * z.2.2.1 y else 0) = 0} ∩
      {z | Tendsto ({x | (openGraph z.1).Reachable o x}.indicator
        fun x => rootedPotential hf.toFinset f o z x - z.2.2.2) cofinite (𝓝 0)} ∩
      {z | {x | (openGraph z.1).Reachable o x ∧
        rootedPotential hf.toFinset f o z x - z.2.2.2 ≠ 0}.Infinite} := by
    ext z
    simp only [rootedFailureRelation, IsFailureOn, Set.mem_setOf_eq, Set.mem_inter_iff,
      mass_rooted_eq_zero_iff hf, isGreenFamily_rooted_iff, pairing_rooted_eq hf,
      tendsto_potential_rooted_iff hf, support_potential_rooted_infinite_iff hf]
    tauto
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter
    (MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter
    ((measurableSet_uniqueInfiniteComponentEvent 2).preimage measurable_fst)
    ((measurableSet_infiniteComponentEvent o).preimage measurable_fst)) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact measurableSet_setOf.2 (Measurable.forall fun x => Measurable.forall fun y =>
      ((hR x).and (hR y)).not.imp
        (measurableSet_setOf.1 (measurableSet_eq_fun (hΓ x y) measurable_const)))
  · exact (measurableSet_rooted_encoded_correctedPlane o).preimage
      (measurable_fst.prodMk (measurable_const.prodMk (measurable_fst.comp
        (measurable_snd.comp measurable_snd))))
  · exact measurableSet_eq_fun (Finset.measurable_sum _ fun y _ =>
      Measurable.ite (measurableSet_setOf.2 (hR y)) measurable_const measurable_const)
      measurable_const
  · refine measurableSet_setOf.2 (Measurable.forall fun y => (hR y).imp
      (Measurable.and (Measurable.forall fun x => (hR x).imp ?_)
        (Measurable.and ?_ (Measurable.forall fun k => Measurable.exists fun N =>
          Measurable.forall fun x => (hR x).imp (measurable_const.imp ?_)))))
    · refine measurableSet_setOf.1 (measurableSet_eq_fun ?_ measurable_const)
      exact ((measurable_laplacian_openGraph x).comp
        (measurable_fst.prodMk (measurable_pi_lambda _ fun w => hΓ w y))).neg
    · exact measurableSet_setOf.1 (measurableSet_eq_fun (hΓ y y) measurable_const)
    · exact measurableSet_setOf.1 (measurableSet_le (hΓ x y).abs measurable_const)
  · exact measurableSet_eq_fun (Finset.measurable_sum _ fun y _ =>
      Measurable.ite (measurableSet_setOf.2 (hR y)) ((hU y).const_mul _) measurable_const)
      measurable_const
  · haveI : (cofinite : Filter (Vertex 2)).IsCountablyGenerated :=
      isCountablyGenerated_cofinite'
    refine measurableSet_tendsto (𝓝 0) fun x => ?_
    classical
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    exact Measurable.ite (measurableSet_setOf.2 (hR x)) ((hP x).sub hLm) measurable_const
  · exact measurableSet_setOf.2 (measurable_setOf_infinite fun x =>
      (hR x).and (measurableSet_setOf.1 (measurableSet_eq_fun ((hP x).sub hLm)
        measurable_const)).not)

end Measurability

section Projection

variable {ω : Configuration 2} {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} {o : Vertex 2}

/-- Witnesses of `E` on the cluster of a root `o` give a point of the rooted relation: normalize
the corrected plane by `ℓ(o) = 0` (harmless since `Σ f = 0`) and extend by zero. -/
theorem exists_mem_rootedFailureRelation (hf : (Function.support f).Finite)
    (huniq : HasUniqueInfiniteOpenComponent ω) (hinf : ω ∈ infiniteComponentEvent o)
    {G : (openGraph ω).connectedComponentMk o → (openGraph ω).connectedComponentMk o → ℝ}
    {ℓ : (openGraph ω).connectedComponentMk o → ℝ} {L : ℝ}
    (hfail : IsFailureOn f q ((openGraph ω).connectedComponentMk o) G ℓ L) :
    ∃ w : FailureWitness, (ω, w) ∈ rootedFailureRelation f q o := by
  obtain ⟨hm, hG, hℓ, hp, hL, hs⟩ := hfail
  let o' : (openGraph ω).connectedComponentMk o :=
    ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  let ℓ₀ : (openGraph ω).connectedComponentMk o → ℝ := fun x => ℓ x - ℓ o'
  have hℓ₀ : IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q ℓ₀ := by
    have h := isCorrectedPlane_sub _ hℓ (isCorrectedPlane_const _ (ℓ o'))
    rw [sub_zero] at h
    exact h
  have hfin : (Function.support fun y : (openGraph ω).connectedComponentMk o =>
      (f y.val : ℝ)).Finite :=
    (hf.preimage Subtype.val_injective.injOn).subset fun y hy => by simpa using hy
  have hmR : ∑ᶠ y : (openGraph ω).connectedComponentMk o, (f y.val : ℝ) = 0 := by
    rw [finsum_rooted_eq o hf.toFinset (fun y => (f y : ℝ))
      fun y hy => hf.mem_toFinset.2 (by simpa using hy)]
    exact (mass_rooted_eq_zero_iff hf ω).1 hm
  have hp0 : pairing ((openGraph ω).connectedComponentMk o) f ℓ₀ = 0 := by
    have h : pairing ((openGraph ω).connectedComponentMk o) f ℓ₀ =
        pairing ((openGraph ω).connectedComponentMk o) f ℓ -
          ℓ o' * ∑ᶠ y : (openGraph ω).connectedComponentMk o, (f y.val : ℝ) := by
      rw [pairing, pairing, mul_finsum, ← finsum_sub_distrib
        (hfin.subset fun y hy => left_ne_zero_of_mul hy)
        (hfin.subset fun y hy => right_ne_zero_of_mul hy)]
      exact finsum_congr fun y => by simp only [ℓ₀]; ring
    rw [h, hp, hmR, mul_zero, sub_zero]
  let Γ : Vertex 2 → Vertex 2 → ℝ := fun x y =>
    if hx : x ∈ (openGraph ω).connectedComponentMk o then
      (if hy : y ∈ (openGraph ω).connectedComponentMk o then G ⟨x, hx⟩ ⟨y, hy⟩ else 0)
    else 0
  let U : Vertex 2 → ℝ := fun x =>
    if hx : x ∈ (openGraph ω).connectedComponentMk o then ℓ₀ ⟨x, hx⟩ else 0
  have hΓ : (fun x y : (openGraph ω).connectedComponentMk o => Γ x.val y.val) = G :=
    funext fun x => funext fun y => by simp only [Γ, dif_pos x.property, dif_pos y.property]
  have hU : (fun x : (openGraph ω).connectedComponentMk o => U x.val) = ℓ₀ :=
    funext fun x => by simp only [U, dif_pos x.property]
  refine ⟨(Γ, (U, L)), huniq, hinf, fun x y hxy => ?_, ⟨?_, ?_, fun x hx => ?_⟩, ?_⟩
  · simp only [Γ]
    split_ifs with hx hy
    · exact absurd ⟨(mem_connectedComponentMk_iff o x).1 hx,
        (mem_connectedComponentMk_iff o y).1 hy⟩ hxy
    · rfl
    · rfl
  · change U o = 0
    simp only [U]
    rw [dif_pos SimpleGraph.ConnectedComponent.connectedComponentMk_mem]
    exact sub_self _
  · change IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => U x.val)
    rw [hU]
    exact hℓ₀
  · change U x = 0
    simp only [U]
    rw [dif_neg fun h => hx ((mem_connectedComponentMk_iff o x).1 h)]
  · change IsFailureOn f q ((openGraph ω).connectedComponentMk o)
      (fun x y => Γ x.val y.val) (fun x => U x.val) L
    rw [hΓ, hU]
    exact ⟨hm, hG, hℓ₀, hp0, hL, hs⟩

/-- A point of the rooted relation lies in `E`: the cluster of the root is the unique infinite
cluster. -/
theorem mem_trichotomyFailure_of_mem {z : Configuration 2 × FailureWitness}
    (hz : z ∈ rootedFailureRelation f q o) : z.1 ∈ trichotomyFailure f q := by
  obtain ⟨huniq, hinf, -, -, hfail⟩ := hz
  have hK : (openGraph z.1).connectedComponentMk o = uniqueInfiniteComponent huniq :=
    (eq_uniqueInfiniteComponent_iff huniq _).2 hinf
  obtain ⟨G, ℓ, L, h⟩ := (exists_isFailureOn_congr hK).1 ⟨_, _, _, hfail⟩
  exact ⟨huniq, G, ℓ, L, h⟩

/-- Under Liouville at order zero, the rooted witnesses are unique. -/
theorem eq_of_mem_rootedFailureRelation {w w' : FailureWitness}
    (hLiou : ∀ h : HasUniqueInfiniteOpenComponent ω,
      HasSublinearLiouville (uniqueInfiniteComponent h))
    (hz : (ω, w) ∈ rootedFailureRelation f q o) (hz' : (ω, w') ∈ rootedFailureRelation f q o) :
    w = w' := by
  obtain ⟨Γ, U, L⟩ := w
  obtain ⟨Γ', U', L'⟩ := w'
  obtain ⟨huniq, hinf, hΓ0, ⟨hU0, hUc, hUoff⟩, -, hG, -, -, hLt, -⟩ := hz
  obtain ⟨-, -, hΓ0', ⟨hU0', hUc', hUoff'⟩, -, hG', -, -, hLt', -⟩ := hz'
  set K := (openGraph ω).connectedComponentMk o
  have hK : K = uniqueInfiniteComponent huniq := (eq_uniqueInfiniteComponent_iff huniq _).2 hinf
  have hLK : HasSublinearLiouville K := by
    rw [hK]
    exact hLiou huniq
  have hΓ : Γ = Γ' := by
    funext x y
    by_cases hxy : (openGraph ω).Reachable o x ∧ (openGraph ω).Reachable o y
    · exact congrFun (eq_of_isGreenColumn hLK (hG ⟨y, (mem_connectedComponentMk_iff o y).2 hxy.2⟩)
        (hG' ⟨y, (mem_connectedComponentMk_iff o y).2 hxy.2⟩))
        ⟨x, (mem_connectedComponentMk_iff o x).2 hxy.1⟩
    · exact (hΓ0 x y hxy).trans (hΓ0' x y hxy).symm
  have hU : U = U' := by
    funext x
    by_cases hx : (openGraph ω).Reachable o x
    · exact congrFun (eq_of_isCorrectedPlane hLK hUc hUc'
        ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ (hU0.trans hU0'.symm))
        ⟨x, (mem_connectedComponentMk_iff o x).2 hx⟩
    · exact (hUoff x hx).trans (hUoff' x hx).symm
  subst hΓ hU
  haveI : Infinite K := hinf.to_subtype
  have hLL : L = L' := tendsto_nhds_unique hLt hLt'
  rw [hLL]

end Projection

/-- **The event `E` of Proposition 5.7 is null-measurable** (`TrichotomyEventMeasurableStep`),
for `f` finitely supported, from the Liouville theorem at order zero. Over the measurable conull
set where Liouville holds, `E` is the countable union over roots `o` of the injective projections
of the Borel relations `rootedFailureRelation f q o`, measurable by the Lusin-Souslin theorem. -/
theorem trichotomyEventMeasurable {p : unitInterval} {f : Vertex 2 → ℤ} (q : Fin 2 → ℝ)
    (hLiou : SublinearLiouville p) (hf : (Function.support f).Finite) :
    TrichotomyEventMeasurableStep p f q := by
  obtain ⟨G, hGae, hG, hGL⟩ := hLiou.exists_measurable_mem
  set E := trichotomyFailure f q
  have hEG : E ∩ G =
      ⋃ o : Vertex 2, Prod.fst '' (rootedFailureRelation f q o ∩ G ×ˢ Set.univ) := by
    apply Set.Subset.antisymm
    · rintro ω ⟨⟨h, Gk, ℓ, L, hfail⟩, hωG⟩
      obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
      have hK : (openGraph ω).connectedComponentMk o = uniqueInfiniteComponent h :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ho
      obtain ⟨G', ℓ', L', hfail'⟩ := (exists_isFailureOn_congr hK).2 ⟨Gk, ℓ, L, hfail⟩
      have hinf : ω ∈ infiniteComponentEvent o := by
        change ((openGraph ω).connectedComponentMk o).supp.Infinite
        rw [hK]
        exact uniqueInfiniteComponent_infinite h
      obtain ⟨w, hw⟩ := exists_mem_rootedFailureRelation hf h hinf hfail'
      exact Set.mem_iUnion.2 ⟨o, ⟨(ω, w), ⟨hw, hωG, Set.mem_univ _⟩, rfl⟩⟩
    · intro ω hω
      obtain ⟨o, ⟨⟨ω', w⟩, ⟨hw, hωG, -⟩, rfl⟩⟩ := Set.mem_iUnion.1 hω
      exact ⟨mem_trichotomyFailure_of_mem hw, hωG⟩
  have hmeas : MeasurableSet (E ∩ G) := by
    rw [hEG]
    refine MeasurableSet.iUnion fun o => ?_
    refine ((measurableSet_rootedFailureRelation hf).inter
      (hG.prod MeasurableSet.univ)).image_of_measurable_injOn measurable_fst ?_
    rintro ⟨ω, w⟩ ⟨hw, hωG, -⟩ ⟨ω', w'⟩ ⟨hw', -, -⟩ hωω'
    change ω = ω' at hωω'
    subst hωω'
    rw [eq_of_mem_rootedFailureRelation (hGL ω hωG) hw hw']
  refine hmeas.nullMeasurableSet.congr ?_
  filter_upwards [hGae] with ω hω
  exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩

/-- `TrichotomyEventMeasurableStep` from the cited input (Armstrong-Dario, order zero) for
`p_c < p < 1`, via `sublinearLiouville`. -/
theorem trichotomyEventMeasurable_of_inputs {p : unitInterval} {f : Vertex 2 → ℤ}
    (q : Fin 2 → ℝ) (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (input : LatticeProb.External.ArmstrongDarioOrderZero) (hf : (Function.support f).Finite) :
    TrichotomyEventMeasurableStep p f q :=
  trichotomyEventMeasurable q (sublinearLiouville p hpc hp1 input) hf

end Rigidity.Proofs.Section5
