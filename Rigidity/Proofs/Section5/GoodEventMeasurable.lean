import Rigidity.Proofs.Section5.TriangleDensity
import Rigidity.Proofs.Section5.MengerRays
import Rigidity.Proofs.Section5.RenormField
import Rigidity.Proofs.Section5.ThirdGoodEventDirectionFree

/-!
# The good event of Lemma 5.26 is null-measurable

Lemma 5.26 (`lemma:density-bound-good-event`, corrected draft L2392-2406) uses the measurability
of the good event `G(0, C_χ, K) = G_1(0, K) ∩ G_2(0, K) ∩ G_3(0, C_χ)` (eq. `def-good-event`),
which the paper leaves implicit (`GoodEventMeasurableStep` of
`Rigidity/Steps/Section5/GoodEventDensity.lean`). This file proves:

* `measurableSet_eventE`, `measurableSet_eventG1`: the events `E_R(x)` (eq. `def.eventE`) and
  `G_1(x, K)` (eq. `defG1`) are measurable. The only infinite quantifier of `E_R(x)` is the
  existence of `C_f + 1` disjoint infinite paths of `𝒞_∞` from a finite set `S`; by König's lemma
  (`Menger.exists_forall_levelPaths`, the compactness step of Menger's theorem for rays) it holds
  if and only if for every `t` there are `C_f + 1` disjoint open paths with `t` steps from `S`,
  a countable union of cylinder events. The other quantifiers range over the finite subsets of
  `ℤ²` and the finite lattice paths.
* `nullMeasurableSet_eventG`: under `SupercriticalBondCorrectorInput` and `p_c(2) < p < 1`, the
  good event `G(0, C_χ, K)` (universal `G_1` [C31], direction-free `G_3` [C32]) is null-measurable.
  The events `G_2` and `G_3` quantify over every corrected plane; off a null set the corrected
  plane is unique up to additive constants, and the measurable rooted plane field of
  Lattice-Probability (`exists_measurable_rooted_plane_on_valid_set`) turns `G_2 ∩ G_3` into
  measurable conditions on the configuration (`rootedPlane_eq_sub`). `nullMeasurableSet_eventGPrinted`
  does the same for the printed good event (changed by [C31], [C32]).
* `goodEventMeasurableStep`, `goodEventDensity`: Lemma 5.26 (`GoodEventDensityStmt`, null-measurable
  form, all parameters), from the translation and triangle-density steps
  (`goodEventTranslationStep`, `triangleDensityStep`).

On the measurability in the product σ-algebra (not asked by the draft statement): `G_1` is
measurable, but `G_2` and `G_3` assert a bound for every corrected plane, including on the null
event where the corrected planes are not unique up to additive constants. There the event is the
complement of the projection of a Borel subset of `Ω × ℝ^{ℤ²}` (the encoded corrected planes
violating the bound, `measurableSet_rooted_encoded_correctedPlane`), whose sections are affine
spaces of harmonic functions of sublinear deviation; no section structure making this projection
Borel (countable or `σ`-compact sections) is available. The argument of the paper uses only
null-measurability.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation LatticeProb.External

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5 Rigidity.Steps.S3 Classical

/-! ### Finite connected sets and disjoint infinite paths in ambient form -/

section Ambient

variable {ω : Configuration 2}

/-- A finite set `T` of vertices of a component `C` is connected in `C` if and only if its points
are joined by the open edges inside `T`. -/
theorem isConnectedSet_iff_reachable_openIn {C : OpenComponent ω} {T : Finset (Vertex 2)}
    (hTC : ∀ v ∈ T, v ∈ C.supp) :
    IsConnectedSet C {v | v.val ∈ T} ↔
      ∀ a ∈ T, ∀ b ∈ T, (openIn ω (T : Set (Vertex 2))).Reachable a b := by
  constructor
  · intro h a ha b hb
    obtain ⟨_, _, hr⟩ := h ⟨a, hTC a ha⟩ ha ⟨b, hTC b hb⟩ hb
    let φ : (componentGraph C).induce {v : C | v.val ∈ T} →g openIn ω (T : Set (Vertex 2)) :=
      { toFun := fun v => v.val.val
        map_rel' := fun {v w} hvw => ⟨hvw, v.2, w.2⟩ }
    exact hr.map φ
  · intro h a ha b hb
    refine ⟨ha, hb, ?_⟩
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (h a.val ha b.val hb)
    let g : Vertex 2 → {v : C | v.val ∈ T} := fun v =>
      if hv : v ∈ T then ⟨⟨v, hTC v hv⟩, hv⟩ else ⟨a, ha⟩
    have hg : ∀ v (hv : v ∈ T), g v = ⟨⟨v, hTC v hv⟩, hv⟩ := fun v hv => dif_pos hv
    have hlift := hr.lift (p := ((componentGraph C).induce {v : C | v.val ∈ T}).Adj) g
      fun u w huw => by
        dsimp only [Function.onFun]
        rw [hg u huw.2.1, hg w huw.2.2]
        exact huw.1
    dsimp only [Function.onFun] at hlift
    rw [hg a.val ha, hg b.val hb] at hlift
    exact (SimpleGraph.reachable_iff_reflTransGen _ _).2 hlift

/-- `k` disjoint infinite paths of a component `C` from a finite set `T` of its vertices exist if
and only if for every `t` there are `k` disjoint open paths with `t` steps from `T` (König's
lemma). -/
theorem hasDisjointPathsToInfinity_iff_levelPathsFin {C : OpenComponent ω}
    {T : Finset (Vertex 2)} (hTC : ∀ v ∈ T, v ∈ C.supp) (k : ℕ) :
    HasDisjointPathsToInfinity C {v | v.val ∈ T} k ↔
      ∀ t, ∃ f : Fin k → Fin (t + 1) → Vertex 2,
        Menger.LevelPathsFin (openGraph ω) (T : Set (Vertex 2)) k t f := by
  constructor
  · rintro ⟨γ, hγ, hdisj⟩ t
    refine ⟨fun j i => (γ j i).val, fun j a b hab => Fin.ext ((hγ j).1.1 (Subtype.ext hab)),
      fun j i => ?_, fun j => (hγ j).2, fun j j' hjj' i i' hii' => ?_⟩
    · have h := (hγ j).1.2.1 i
      exact (C.toSimpleGraph_adj (γ j i).2 (γ j (i + 1)).2).1 h
    · exact Set.disjoint_left.1 (hdisj j j' hjj') ⟨i, rfl⟩ ⟨i', (Subtype.ext hii').symm⟩
  · intro h
    have hlev : ∀ t, ∃ g : Fin k → ℕ → Vertex 2,
        Menger.LevelPaths (openGraph ω) (T : Set (Vertex 2)) k t g := by
      intro t
      obtain ⟨f, hf⟩ := h t
      refine ⟨fun j i => if hi : i ≤ t then f j ⟨i, Nat.lt_succ_of_le hi⟩ else f j 0, ?_⟩
      have hr : Menger.restrictSteps t
          (fun j i => if hi : i ≤ t then f j ⟨i, Nat.lt_succ_of_le hi⟩ else f j 0) = f := by
        funext j i
        simp [Menger.restrictSteps, Fin.is_le i]
      rw [Menger.LevelPaths, hr]
      exact hf
    obtain ⟨g, hg⟩ := Menger.exists_forall_levelPaths (fun v => Set.toFinite _) T.finite_toSet hlev
    obtain ⟨hray, hdisj⟩ := Menger.rays_of_forall_levelPaths hg
    have hmem : ∀ j n, g j n ∈ C.supp := fun j n => by
      induction n with
      | zero => exact hTC _ (hray j).2.2
      | succ n ih => exact C.mem_supp_of_adj_mem_supp ih ((hray j).2.1 n)
    refine ⟨fun j n => ⟨g j n, hmem j n⟩, fun j => ⟨⟨fun a b hab => (hray j).1
      (congrArg Subtype.val hab), fun n => (C.toSimpleGraph_adj (hmem j n) (hmem j (n + 1))).2
        ((hray j).2.1 n), fun _ => Set.mem_univ _⟩, (hray j).2.2⟩,
      fun j j' hjj' => Set.disjoint_left.2 ?_⟩
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Set.disjoint_left.1 (hdisj j j' hjj') ⟨a, rfl⟩ ⟨b, congrArg Subtype.val hb⟩

end Ambient

/-! ### The event `E_R(x)` -/

/-- The requirement of `E_R(x)` on a finite vertex set `T`, in ambient form: if `T` is a connected
subset of `𝒞_∞` containing `x` with `diam T ≥ R`, then for every `t` there are `C_f + 1` disjoint
open paths with `t` steps from `T`. -/
def EventEClause (Cf : ℕ) (R : ℝ) (x : Vertex 2) (ω : Configuration 2) (T : Finset (Vertex 2)) :
    Prop :=
  (∀ v ∈ T, ω ∈ infiniteComponentEvent v) →
    (∀ a ∈ T, ∀ b ∈ T, (openIn ω (T : Set (Vertex 2))).Reachable a b) → x ∈ T →
      (∃ a ∈ T, ∃ b ∈ T, R ≤ l1 (a - b)) →
        ∀ t, ∃ f : Fin (Cf + 1) → Fin (t + 1) → Vertex 2,
          Menger.LevelPathsFin (openGraph ω) (T : Set (Vertex 2)) (Cf + 1) t f

/-- `E_R(x)` in ambient form: the clause holds for every finite vertex set. -/
theorem eventE_eq (Cf : ℕ) (R : ℝ) (x : Vertex 2) :
    eventE Cf R x =
      {ω | HasUniqueInfiniteOpenComponent ω → ∀ T, EventEClause Cf R x ω T} := by
  ext ω
  constructor
  · intro hE h T hTi hconn hx hdiam
    have hTC : ∀ v ∈ T, v ∈ (uniqueInfiniteComponent h).supp :=
      fun v hv => (mem_uniqueInfiniteComponent_iff h v).2 (hTi v hv)
    refine (hasDisjointPathsToInfinity_iff_levelPathsFin hTC (Cf + 1)).1
      (hE h _ (T.finite_toSet.preimage Subtype.val_injective.injOn)
        ((isConnectedSet_iff_reachable_openIn hTC).2 hconn) ⟨⟨x, hTC x hx⟩, hx, rfl⟩ ?_)
    obtain ⟨a, ha, b, hb, hab⟩ := hdiam
    exact ⟨⟨a, hTC a ha⟩, ha, ⟨b, hTC b hb⟩, hb, hab⟩
  · intro hE h S hS hconn hx hdiam
    obtain ⟨T, hST, hTC⟩ : ∃ T : Finset (Vertex 2), S = {v | v.val ∈ T} ∧
        ∀ v ∈ T, v ∈ (uniqueInfiniteComponent h).supp := by
      refine ⟨hS.toFinset.image Subtype.val, ?_, fun v hv => ?_⟩
      · ext v
        simp
      · obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hv
        exact w.2
    subst hST
    refine (hasDisjointPathsToInfinity_iff_levelPathsFin hTC (Cf + 1)).2
      (hE h T (fun v hv => (mem_uniqueInfiniteComponent_iff h v).1 (hTC v hv))
        ((isConnectedSet_iff_reachable_openIn hTC).1 hconn) ?_ ?_)
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hy
    · obtain ⟨a, ha, b, hb, hab⟩ := hdiam
      exact ⟨a.val, ha, b.val, hb, hab⟩

/-- Reachability by the open edges inside a finite set is a measurable event. -/
theorem measurableSet_reachable_openIn (T : Finset (Vertex 2)) (a b : Vertex 2) :
    MeasurableSet {ω : Configuration 2 | (openIn ω (T : Set (Vertex 2))).Reachable a b} :=
  measurableSet_of_eqOn (finite_bondsIn T.finite_toSet) fun ω ω' h hω => by
    show (openIn ω' _).Reachable a b
    rwa [← openIn_eq_of_eqOn subset_rfl h]

/-- That `k` given vertex sequences are disjoint open paths is a measurable event. -/
theorem measurable_levelPathsFin {k t : ℕ} (T : Set (Vertex 2))
    (f : Fin k → Fin (t + 1) → Vertex 2) :
    Measurable fun ω : Configuration 2 => Menger.LevelPathsFin (openGraph ω) T k t f :=
  measurable_const.and ((Measurable.forall fun _ => Measurable.forall fun _ =>
    measurableSet_setOf.1 (measurableSet_openGraph_adj _ _)).and
      (measurable_const.and measurable_const))

theorem measurable_hasUniqueInfiniteOpenComponent :
    Measurable fun ω : Configuration 2 => HasUniqueInfiniteOpenComponent ω :=
  measurableSet_setOf.1 (measurableSet_uniqueInfiniteComponentEvent 2)

/-- The event `E_R(x)` (eq. `def.eventE`) is measurable. -/
theorem measurableSet_eventE (Cf : ℕ) (R : ℝ) (x : Vertex 2) : MeasurableSet (eventE Cf R x) := by
  rw [eventE_eq]
  refine measurableSet_setOf.2 (measurable_hasUniqueInfiniteOpenComponent.imp
    (Measurable.forall fun T => ?_))
  exact (Measurable.forall fun v => measurable_const.imp
    (measurable_mem.2 (measurableSet_infiniteComponentEvent v))).imp
    ((Measurable.forall fun a => measurable_const.imp (Measurable.forall fun b =>
      measurable_const.imp (measurableSet_setOf.1 (measurableSet_reachable_openIn T a b)))).imp
      (measurable_const.imp (measurable_const.imp (Measurable.forall fun t =>
        Measurable.exists fun f => measurable_levelPathsFin _ f))))

/-! ### The first good event `G_1(x, K)` -/

/-- The number of steps `1 ≤ i ≤ n` of the vertex sequence `f` with `ω ∈ E_R(f(i))`. -/
noncomputable def goodSteps (ω : Configuration 2) (Cf : ℕ) (R : ℝ) {n : ℕ}
    (f : Fin (n + 1) → Vertex 2) : ℕ :=
  (Finset.univ.filter fun i : Fin (n + 1) => i ≠ 0 ∧ ω ∈ eventE Cf R (f i)).card

/-- `G_1(x, K)` in ambient form: an intersection over the lattice paths from `x`. -/
theorem eventG1_eq (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) :
    eventG1 Cf R c₁ x K = {ω | HasUniqueInfiniteOpenComponent ω ∧ ∀ n : ℕ,
      ∀ f : Fin (n + 1) → Vertex 2, (∀ i, ω ∈ infiniteComponentEvent (f i)) →
        Function.Injective f → (∀ i : Fin n, (openGraph ω).Adj (f i.castSucc) (f i.succ)) →
        f 0 = x → K ≤ l1 (f (Fin.last n) - x) →
        c₁ * l1 (f (Fin.last n) - x) ≤ (goodSteps ω Cf R f : ℝ)} := by
  ext ω
  constructor
  · rintro ⟨h, hG⟩
    refine ⟨h, fun n f hf hinj hadj h0 hK => ?_⟩
    have hfC : ∀ i, f i ∈ (uniqueInfiniteComponent h).supp :=
      fun i => (mem_uniqueInfiniteComponent_iff h _).2 (hf i)
    exact hG n (fun i => ⟨f i, hfC i⟩) ⟨fun a b hab => hinj (congrArg Subtype.val hab),
      fun i => ((uniqueInfiniteComponent h).toSimpleGraph_adj (hfC _) (hfC _)).2 (hadj i)⟩ h0 hK
  · rintro ⟨h, hG⟩
    refine ⟨h, fun n γ hγ h0 hK => ?_⟩
    exact hG n (fun i => (γ i).val) (fun i => (mem_uniqueInfiniteComponent_iff h _).1 (γ i).2)
      (Subtype.val_injective.comp hγ.1)
      (fun i => ((uniqueInfiniteComponent h).toSimpleGraph_adj (γ _).2 (γ _).2).1 (hγ.2 i)) h0 hK

/-- The printed `G_1(x, K)` (changed by [C31]) in ambient form: a countable
union over the lattice paths from `x`. -/
theorem eventG1Exists_eq (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) :
    eventG1Exists Cf R c₁ x K = {ω | HasUniqueInfiniteOpenComponent ω ∧ ∃ n : ℕ,
      ∃ f : Fin (n + 1) → Vertex 2, (∀ i, ω ∈ infiniteComponentEvent (f i)) ∧
        Function.Injective f ∧ (∀ i : Fin n, (openGraph ω).Adj (f i.castSucc) (f i.succ)) ∧
        f 0 = x ∧ K ≤ l1 (f (Fin.last n) - x) ∧
        c₁ * l1 (f (Fin.last n) - x) ≤ (goodSteps ω Cf R f : ℝ)} := by
  ext ω
  constructor
  · rintro ⟨h, n, γ, ⟨hinj, hadj⟩, h0, hK, hc⟩
    exact ⟨h, n, fun i => (γ i).val, fun i => (mem_uniqueInfiniteComponent_iff h _).1 (γ i).2,
      Subtype.val_injective.comp hinj,
      fun i => ((uniqueInfiniteComponent h).toSimpleGraph_adj (γ _).2 (γ _).2).1 (hadj i),
      h0, hK, hc⟩
  · rintro ⟨h, n, f, hf, hinj, hadj, h0, hK, hc⟩
    have hfC : ∀ i, f i ∈ (uniqueInfiniteComponent h).supp :=
      fun i => (mem_uniqueInfiniteComponent_iff h _).2 (hf i)
    exact ⟨h, n, fun i => ⟨f i, hfC i⟩, ⟨fun a b hab => hinj (congrArg Subtype.val hab),
      fun i => ((uniqueInfiniteComponent h).toSimpleGraph_adj (hfC _) (hfC _)).2 (hadj i)⟩,
      h0, hK, hc⟩

theorem measurable_goodSteps (Cf : ℕ) (R : ℝ) {n : ℕ} (f : Fin (n + 1) → Vertex 2) :
    Measurable fun ω => (goodSteps ω Cf R f : ℝ) := by
  have heq : (fun ω => (goodSteps ω Cf R f : ℝ)) = fun ω =>
      ∑ i : Fin (n + 1), (if i ≠ 0 ∧ ω ∈ eventE Cf R (f i) then 1 else 0 : ℝ) := by
    funext ω
    simp only [goodSteps, Finset.card_filter]
    push_cast
    rfl
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (measurableSet_setOf.2
    (measurable_const.and (measurable_mem.2 (measurableSet_eventE Cf R (f i)))))
    measurable_const measurable_const

/-- The first good event `G_1(x, K)` (eq. `defG1`, [C31]) is measurable. -/
theorem measurableSet_eventG1 (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) :
    MeasurableSet (eventG1 Cf R c₁ x K) := by
  rw [eventG1_eq]
  refine measurableSet_setOf.2 (measurable_hasUniqueInfiniteOpenComponent.and
    (Measurable.forall fun n => Measurable.forall fun f => ?_))
  exact (Measurable.forall fun i => measurable_mem.2 (measurableSet_infiniteComponentEvent _)).imp
    (measurable_const.imp ((Measurable.forall fun i =>
      measurableSet_setOf.1 (measurableSet_openGraph_adj _ _)).imp (measurable_const.imp
        (measurable_const.imp (measurableSet_setOf.1
          (measurableSet_le measurable_const (measurable_goodSteps Cf R f)))))))

/-- The printed first good event (changed by [C31]) is measurable. -/
theorem measurableSet_eventG1Exists (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) :
    MeasurableSet (eventG1Exists Cf R c₁ x K) := by
  rw [eventG1Exists_eq]
  refine measurableSet_setOf.2 (measurable_hasUniqueInfiniteOpenComponent.and
    (Measurable.exists fun n => Measurable.exists fun f => ?_))
  exact (Measurable.forall fun i => measurable_mem.2 (measurableSet_infiniteComponentEvent _)).and
    (measurable_const.and ((Measurable.forall fun i =>
      measurableSet_setOf.1 (measurableSet_openGraph_adj _ _)).and (measurable_const.and
        (measurable_const.and (measurableSet_setOf.1
          (measurableSet_le measurable_const (measurable_goodSteps Cf R f)))))))

/-! ### The second and third good events on the valid set -/

/-- Off a measurable null event `N` the corrector clauses hold on the unique infinite cluster, and
the normalized corrected plane rooted at `0` is a measurable field on
`(Nᶜ ∩ {unique 𝒞_∞}) ∩ {0 ∈ 𝒞_∞}` (`exists_measurable_rooted_plane_on_valid_set`). -/
theorem exists_rootedPlane_field (hU : SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ N : Set (Configuration 2), MeasurableSet N ∧ latticeBondLaw 2 p N = 0 ∧
      Nᶜ ∩ uniqueInfiniteComponentEvent 2 ⊆ correctorValidEvent 2 ∧
      ∃ F : (↥((Nᶜ ∩ uniqueInfiniteComponentEvent 2) ∩ infiniteComponentEvent 0) ×
          (Fin 2 → ℝ)) → (Vertex 2 → ℝ), Measurable F ∧ ∀ z U,
        (U 0 = 0 ∧ IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk 0) z.2
            (fun x => U x.val) ∧ ∀ x, ¬ (openGraph z.1.val).Reachable 0 x → U x = 0) ↔
          F z = U := by
  set μ := latticeBondLaw 2 p
  have hbad := ae_iff.mp (hU 2 le_rfl p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  have hGm : MeasurableSet (Nᶜ ∩ uniqueInfiniteComponentEvent 2) :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : Nᶜ ∩ uniqueInfiniteComponentEvent 2 ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  exact ⟨N, measurableSet_toMeasurable _ _, hN0, hvalid,
    exists_measurable_rooted_plane_on_valid_set _ hGm hvalid 0⟩

/-- On the valid event every slope has a corrected plane. -/
theorem exists_correctedPlane_of_valid {ω : Configuration 2} (hω : ω ∈ correctorValidEvent 2)
    (h : HasUniqueInfiniteOpenComponent ω) (o : uniqueInfiniteComponent h) (q : Fin 2 → ℝ) :
    ∃ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ :=
  let ⟨u, ⟨hu, _⟩, _⟩ := (hω.2 h).1 q o
  ⟨u, hu⟩

section Plane

variable {G : Set (Configuration 2)}
  {F : (↥(G ∩ infiniteComponentEvent 0) × (Fin 2 → ℝ)) → (Vertex 2 → ℝ)}

/-- The increments of every corrected plane are those of the rooted plane field. -/
theorem sub_eq_rootedPlane_sub
    (hF : ∀ z U, (U 0 = 0 ∧
        IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk 0) z.2
          (fun x => U x.val) ∧
        ∀ x, ¬ (openGraph z.1.val).Reachable 0 x → U x = 0) ↔ F z = U)
    (z : ↥(G ∩ infiniteComponentEvent 0)) (h : HasUniqueInfiniteOpenComponent z.val)
    (ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp) {q : Fin 2 → ℝ}
    {ℓ : uniqueInfiniteComponent h → ℝ} (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ)
    (a b : uniqueInfiniteComponent h) : ℓ a - ℓ b = F (z, q) a.val - F (z, q) b.val := by
  rw [rootedPlane_eq_sub hF z h ho hℓ a.2, rootedPlane_eq_sub hF z h ho hℓ b.2,
    sub_sub_sub_cancel_right]

variable (hvalid : G ⊆ correctorValidEvent 2)
  (hF : ∀ z U, (U 0 = 0 ∧
        IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk 0) z.2
          (fun x => U x.val) ∧
        ∀ x, ¬ (openGraph z.1.val).Reachable 0 x → U x = 0) ↔ F z = U)
include hvalid hF

/-- `G_2(0, K)` through the rooted plane field. -/
theorem mem_eventG2_iff_rootedPlane (z : ↥(G ∩ infiniteComponentEvent 0)) (K : ℝ) :
    z.val ∈ eventG2 0 K ↔ ∀ R' : ℕ, K ≤ R' → ∀ a ∈ cubeAt 0 R', ∀ b ∈ cubeAt 0 R',
      z.val ∈ infiniteComponentEvent a → z.val ∈ infiniteComponentEvent b →
        F (z, Pi.single 0 1) a - F (z, Pi.single 0 1) b ≤ 4 * R' := by
  have h := (hvalid z.2.1).1
  have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
    (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_correctedPlane_of_valid (hvalid z.2.1) h ⟨0, ho⟩ (Pi.single 0 1)
  constructor
  · rintro ⟨h', hall⟩ R' hR a ha b hb hai hbi
    have := hall ℓ₀ hℓ₀ R' hR ⟨a, (mem_uniqueInfiniteComponent_iff h' a).2 hai⟩
      ⟨b, (mem_uniqueInfiniteComponent_iff h' b).2 hbi⟩ ha hb
    rwa [sub_eq_rootedPlane_sub hF z h ho hℓ₀] at this
  · intro hP
    refine ⟨h, fun ℓ hℓ R' hR y w hy hw => ?_⟩
    rw [sub_eq_rootedPlane_sub hF z h ho hℓ]
    exact hP R' hR _ hy _ hw ((mem_uniqueInfiniteComponent_iff h _).1 y.2)
      ((mem_uniqueInfiniteComponent_iff h _).1 w.2)

/-- The printed `G_3(0, C_χ)` (changed by [C32]) through the rooted plane
field. -/
theorem mem_eventG3Edge_iff_rootedPlane (z : ↥(G ∩ infiniteComponentEvent 0)) (Cχ : ℝ) :
    z.val ∈ eventG3Edge 0 Cχ ↔ (openGraph z.val).Adj 0 e1 ∧ Cχ ≤ F (z, Pi.single 0 1) e1 := by
  have h := (hvalid z.2.1).1
  have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
    (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
  have hF0 : F (z, Pi.single 0 1) 0 = 0 := ((hF (z, _) _).2 rfl).1
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_correctedPlane_of_valid (hvalid z.2.1) h ⟨0, ho⟩ (Pi.single 0 1)
  constructor
  · rintro ⟨h', ho', he', hadj, hall⟩
    have hadj' := ((uniqueInfiniteComponent h').toSimpleGraph_adj ho' he').1 hadj
    rw [zero_add] at hadj'
    refine ⟨hadj', ?_⟩
    have := hall ℓ₀ hℓ₀
    rw [sub_eq_rootedPlane_sub hF z h ho hℓ₀] at this
    simpa [hF0] using this
  · rintro ⟨hadj, hval⟩
    have he : e1 ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have he' : (0 : Vertex 2) + e1 ∈ (uniqueInfiniteComponent h).supp := by
      rw [zero_add]; exact he
    refine ⟨h, ho, he', ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he').2
      (by rw [zero_add]; exact hadj), fun ℓ hℓ => ?_⟩
    rw [sub_eq_rootedPlane_sub hF z h ho hℓ]
    simpa [hF0] using hval

/-- The third good event `G_3(0, C_χ)` ([C32]) through the rooted plane field. -/
theorem mem_eventG3_iff_rootedPlane (z : ↥(G ∩ infiniteComponentEvent 0)) (Cχ : ℝ) :
    z.val ∈ eventG3 0 Cχ ↔
      ∃ y, (openGraph z.val).Adj 0 y ∧ Cχ ≤ F (z, Pi.single 0 1) y := by
  have h := (hvalid z.2.1).1
  have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
    (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
  have hF0 : F (z, Pi.single 0 1) 0 = 0 := ((hF (z, _) _).2 rfl).1
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_correctedPlane_of_valid (hvalid z.2.1) h ⟨0, ho⟩ (Pi.single 0 1)
  constructor
  · rintro ⟨h', ho', y, hadj, hall⟩
    refine ⟨y.val, ((uniqueInfiniteComponent h').toSimpleGraph_adj ho' y.2).1 hadj, ?_⟩
    have := hall ℓ₀ hℓ₀
    rw [sub_eq_rootedPlane_sub hF z h ho hℓ₀] at this
    simpa [hF0] using this
  · rintro ⟨y, hadj, hval⟩
    have hy : y ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    refine ⟨h, ho, ⟨y, hy⟩, ((uniqueInfiniteComponent h).toSimpleGraph_adj ho hy).2 hadj,
      fun ℓ hℓ => ?_⟩
    rw [sub_eq_rootedPlane_sub hF z h ho hℓ]
    simpa [hF0] using hval

end Plane

/-- If off a null event `N` the set `A` lies in a measurable set `B ⊆ Nᶜ`, on which it is a
measurable subset, then `A` is null-measurable. -/
theorem nullMeasurableSet_of_subtype {μ : Measure (Configuration 2)}
    {N B A : Set (Configuration 2)} (hN : μ N = 0) (hB : MeasurableSet B) (hAB : A ∩ Nᶜ ⊆ B)
    (hBN : B ⊆ Nᶜ) {T : Set B} (hT : MeasurableSet T) (hAT : ∀ z : B, z.val ∈ A ↔ z ∈ T) :
    NullMeasurableSet A μ := by
  have heq : A ∩ Nᶜ = Subtype.val '' T := by
    ext ω
    constructor
    · rintro ⟨hA, hN'⟩
      exact ⟨⟨ω, hAB ⟨hA, hN'⟩⟩, (hAT _).1 hA, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hAT z).2 hz, hBN z.2⟩
  have hm : MeasurableSet (A ∩ Nᶜ) := by
    rw [heq]
    exact hB.subtype_image hT
  exact hm.nullMeasurableSet.congr
    (inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.2 (by rwa [compl_compl])))

/-- The printed good event (changed by [C31], [C32]) is null-measurable for
`p_c(2) < p < 1`. -/
theorem nullMeasurableSet_eventGPrinted (hU : SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (Cf : ℕ) (R c₁ Cχ K : ℝ) :
    NullMeasurableSet (eventGPrinted Cf R c₁ 0 Cχ K) (latticeBondLaw 2 p) := by
  obtain ⟨N, hNm, hN0, hvalid, F, hFm, hF⟩ := exists_rootedPlane_field hU hpc hp1
  have hB : MeasurableSet ((Nᶜ ∩ uniqueInfiniteComponentEvent 2) ∩ infiniteComponentEvent 0) :=
    (hNm.compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)).inter
      (measurableSet_infiniteComponentEvent 0)
  have hΦ : ∀ a, Measurable fun z : ↥((Nᶜ ∩ uniqueInfiniteComponentEvent 2) ∩
      infiniteComponentEvent 0) => F (z, Pi.single 0 1) a := fun a =>
    (measurable_pi_apply a).comp (hFm.comp (measurable_id.prodMk measurable_const))
  refine nullMeasurableSet_of_subtype hN0 hB ?_ (fun ω hω => hω.1.1)
    (T := {z | z.val ∈ eventG1Exists Cf R c₁ 0 K ∧ (∀ R' : ℕ, K ≤ R' → ∀ a ∈ cubeAt 0 R',
      ∀ b ∈ cubeAt 0 R', z.val ∈ infiniteComponentEvent a → z.val ∈ infiniteComponentEvent b →
        F (z, Pi.single 0 1) a - F (z, Pi.single 0 1) b ≤ 4 * R') ∧
      (openGraph z.val).Adj 0 e1 ∧ Cχ ≤ F (z, Pi.single 0 1) e1}) ?_ ?_
  · rintro ω ⟨⟨-, ⟨h, ho, -⟩⟩, hωN⟩
    exact ⟨⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).1 ho⟩
  · refine measurableSet_setOf.2 ((measurable_mem.2 (measurable_subtype_coe
      (measurableSet_eventG1Exists Cf R c₁ 0 K))).and ((Measurable.forall fun R' =>
        measurable_const.imp (Measurable.forall fun a => measurable_const.imp
          (Measurable.forall fun b => measurable_const.imp ((measurable_mem.2
            (measurable_subtype_coe (measurableSet_infiniteComponentEvent a))).imp
            ((measurable_mem.2 (measurable_subtype_coe
              (measurableSet_infiniteComponentEvent b))).imp (measurableSet_setOf.1
                (measurableSet_le ((hΦ a).sub (hΦ b)) measurable_const))))))).and
        ((measurable_mem.2 (measurable_subtype_coe (measurableSet_openGraph_adj 0 e1))).and
          (measurableSet_setOf.1 (measurableSet_le measurable_const (hΦ e1))))))
  · intro z
    rw [eventGPrinted, Set.mem_inter_iff, Set.mem_inter_iff, mem_eventG2_iff_rootedPlane hvalid hF,
      mem_eventG3Edge_iff_rootedPlane hvalid hF]
    simp only [Set.mem_setOf_eq, and_assoc]

/-- **The good event `G(0, C_χ, K)` is null-measurable** (step `GoodEventMeasurableStep` of
Lemma 5.26), for `p_c(2) < p < 1`. -/
theorem nullMeasurableSet_eventG (hU : SupercriticalBondCorrectorInput)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (Cf : ℕ)
    (R c₁ Cχ K : ℝ) :
    NullMeasurableSet (eventG Cf R c₁ 0 Cχ K) (latticeBondLaw 2 p) := by
  obtain ⟨N, hNm, hN0, hvalid, F, hFm, hF⟩ := exists_rootedPlane_field hU hpc hp1
  have hB : MeasurableSet ((Nᶜ ∩ uniqueInfiniteComponentEvent 2) ∩ infiniteComponentEvent 0) :=
    (hNm.compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)).inter
      (measurableSet_infiniteComponentEvent 0)
  have hΦ : ∀ a, Measurable fun z : ↥((Nᶜ ∩ uniqueInfiniteComponentEvent 2) ∩
      infiniteComponentEvent 0) => F (z, Pi.single 0 1) a := fun a =>
    (measurable_pi_apply a).comp (hFm.comp (measurable_id.prodMk measurable_const))
  refine nullMeasurableSet_of_subtype hN0 hB ?_ (fun ω hω => hω.1.1)
    (T := {z | z.val ∈ eventG1 Cf R c₁ 0 K ∧ (∀ R' : ℕ, K ≤ R' → ∀ a ∈ cubeAt 0 R',
      ∀ b ∈ cubeAt 0 R', z.val ∈ infiniteComponentEvent a → z.val ∈ infiniteComponentEvent b →
        F (z, Pi.single 0 1) a - F (z, Pi.single 0 1) b ≤ 4 * R') ∧
      ∃ y, (openGraph z.val).Adj 0 y ∧ Cχ ≤ F (z, Pi.single 0 1) y}) ?_ ?_
  · rintro ω ⟨⟨-, ⟨h, ho, -⟩⟩, hωN⟩
    exact ⟨⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).1 ho⟩
  · refine measurableSet_setOf.2 ((measurable_mem.2 (measurable_subtype_coe
      (measurableSet_eventG1 Cf R c₁ 0 K))).and ((Measurable.forall fun R' =>
        measurable_const.imp (Measurable.forall fun a => measurable_const.imp
          (Measurable.forall fun b => measurable_const.imp ((measurable_mem.2
            (measurable_subtype_coe (measurableSet_infiniteComponentEvent a))).imp
            ((measurable_mem.2 (measurable_subtype_coe
              (measurableSet_infiniteComponentEvent b))).imp (measurableSet_setOf.1
                (measurableSet_le ((hΦ a).sub (hΦ b)) measurable_const))))))).and
        (Measurable.exists fun y => (measurable_mem.2 (measurable_subtype_coe
          (measurableSet_openGraph_adj 0 y))).and
          (measurableSet_setOf.1 (measurableSet_le measurable_const (hΦ y))))))
  · intro z
    rw [eventG, Set.mem_inter_iff, Set.mem_inter_iff, mem_eventG2_iff_rootedPlane hvalid hF,
      mem_eventG3_iff_rootedPlane hvalid hF]
    simp only [Set.mem_setOf_eq, and_assoc]

/-! ### Lemma 5.26 -/

/-- **Step `GoodEventMeasurableStep`** of Lemma 5.26 for `p_c(2) < p < 1`, from
`SupercriticalBondCorrectorInput`. -/
theorem goodEventMeasurableStep (hU : SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GoodEventMeasurableStep p :=
  nullMeasurableSet_eventG hU hpc hp1

/-- **Lemma 5.26** (`GoodEventDensityStmt`, null-measurable form, all parameters) for
`p_c(2) < p < 1`, from `SupercriticalBondCorrectorInput`. -/
theorem goodEventDensity (hU : SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : GoodEventDensityStmt p :=
  goodEventDensity_of_measurableStep p (goodEventMeasurableStep hU hpc hp1)

end Rigidity.Proofs.Section5
