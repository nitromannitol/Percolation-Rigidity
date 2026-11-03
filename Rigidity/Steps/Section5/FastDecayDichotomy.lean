import Rigidity.Steps.Section5.Common

/-!
# Theorem 5.1: the steps of the fast-decay dichotomy

Theorem 5.1 (paper L1503-1520 of the corrected draft, proof L1549-1557) is carved into
Proposition 5.3 (`FastDecayPotentialStmt`), Proposition 5.5 (`LogGrowthStmt`), the countability
step `step:5.1-countable` and the identification step `step:5.1-liouville`.

* `step:5.1-countable`: the finitely supported `f : ℤ² → ℤ` form a countable family, so the
  almost-sure events of Propositions 5.3 and 5.5 hold simultaneously for all of them.
* `step:5.1-liouville` (correction C15): for `u → 0` with integer Laplacian, `f := -Δu` is
  finitely supported, and `w := u - u_f` is harmonic (`PotentialLaplacian`). If `Σ f ≠ 0`, then
  `u_f = Θ(log |x|)` (Proposition 5.5), so `w` grows sublinearly and is constant
  (`SublinearLiouville`), and the bounded function `u - w = u_f` contradicts the lower bound
  `|u_f| ≥ c log |x|`. If `Σ f = 0`, Proposition 5.3 gives the limit `L` of `u_f` at infinity, so
  `w → -L` is bounded, hence constant, hence `w = -L` and `u = u_f - L`; Proposition 5.3 then
  applies to `u`.

The limit at infinity of `u_f` is supplied by Proposition 5.3 itself, so `PotentialLimit` is not
used. The Green family of the cluster is supplied by `GreenFamilyExists`.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

variable {ω : Configuration 2}

/-! ### The `ℓ¹` and Euclidean norms on `ℤ²` -/

/-- Each coordinate of a lattice point is bounded by its Euclidean norm. -/
theorem abs_coord_le_eucl (x : Vertex 2) (i : Fin 2) : |(x i : ℝ)| ≤ eucl x := by
  have hi := PiLp.norm_apply_le (latticeEuclideanEmbedding x) i
  change |(x i : ℝ)| ≤ ‖latticeEuclideanEmbedding x‖ at hi
  exact hi

theorem l1_nonneg (x : Vertex 2) : 0 ≤ l1 x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The Euclidean norm is at most the `ℓ¹` norm. -/
theorem eucl_le_l1 (x : Vertex 2) : eucl x ≤ l1 x := by
  calc eucl x = Real.sqrt (∑ i, ‖(latticeEuclideanEmbedding x) i‖ ^ 2) :=
        EuclideanSpace.norm_eq _
    _ ≤ Real.sqrt (l1 x ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        change ∑ i, |(x i : ℝ)| ^ 2 ≤ (∑ i, |(x i : ℝ)|) ^ 2
        simp only [Fin.sum_univ_two]
        nlinarith [abs_nonneg (x 0 : ℝ), abs_nonneg (x 1 : ℝ)]
    _ = l1 x := Real.sqrt_sq (l1_nonneg x)

/-- The `ℓ¹` norm is at most twice the Euclidean norm. -/
theorem l1_le_two_mul_eucl (x : Vertex 2) : l1 x ≤ 2 * eucl x := by
  simp only [l1, Fin.sum_univ_two]
  linarith [abs_coord_le_eucl x 0, abs_coord_le_eucl x 1]

/-! ### Large Euclidean norm and the cofinite filter of a component -/

/-- A component has only finitely many vertices in a Euclidean ball around the origin. -/
theorem finite_eucl_lt (C : OpenComponent ω) (R : ℝ) : {x : C | eucl x.val < R}.Finite := by
  have h0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i; simp [latticeEuclideanEmbedding]
  refine ((finite_latticeEuclideanBall (0 : Vertex 2) R).preimage
    Subtype.val_injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, h0, dist_zero_right]
  exact hx

/-- A property holding at every vertex of large Euclidean norm holds cofinitely. -/
theorem eventually_cofinite_of_forall_eucl_ge {C : OpenComponent ω} {P : C → Prop} {R : ℝ}
    (h : ∀ x : C, R ≤ eucl x.val → P x) : ∀ᶠ x in cofinite, P x :=
  eventually_cofinite.2 ((finite_eucl_lt C R).subset fun x hx => not_le.1 fun hR => hx (h x hR))

/-- A property holding cofinitely holds at every vertex of large Euclidean norm. -/
theorem exists_forall_eucl_ge_of_eventually {C : OpenComponent ω} {P : C → Prop}
    (h : ∀ᶠ x in cofinite, P x) : ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → P x := by
  obtain ⟨M, hM⟩ := ((eventually_cofinite.1 h).image fun x : C => eucl x.val).bddAbove
  refine ⟨M + 1, fun x hx => by_contra fun hPx => ?_⟩
  have := hM ⟨x, hPx, rfl⟩
  linarith

/-- An infinite component has vertices of arbitrarily large Euclidean norm. -/
theorem exists_le_eucl (C : OpenComponent ω) (hC : (Set.univ : Set C).Infinite) (R : ℝ) :
    ∃ x : C, R ≤ eucl x.val := by
  obtain ⟨x, -, hx⟩ := (hC.sdiff (finite_eucl_lt C R)).nonempty
  exact ⟨x, not_lt.1 hx⟩

/-- A function with a limit at infinity is bounded at large Euclidean norm. -/
theorem exists_abs_le_of_tendsto {C : OpenComponent ω} {v : C → ℝ} {L : ℝ}
    (hv : Tendsto v cofinite (𝓝 L)) : ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → |v x| ≤ |L| + 1 := by
  refine exists_forall_eucl_ge_of_eventually
    ((hv.eventually (Metric.closedBall_mem_nhds L one_pos)).mono fun x hx => ?_)
  rw [Real.dist_eq] at hx
  have := abs_sub_abs_le_abs_sub (v x) L
  linarith

/-- A function bounded at large Euclidean norm grows sublinearly. -/
theorem sublinear_of_abs_le {C : OpenComponent ω} {v : C → ℝ} {R B : ℝ}
    (h : ∀ x : C, R ≤ eucl x.val → |v x| ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, ∀ x : C, R' ≤ eucl x.val → |v x| ≤ ε * eucl x.val := by
  intro ε hε
  refine ⟨max R (B / ε), fun x hx => ?_⟩
  have h1 := h x ((le_max_left _ _).trans hx)
  have h2 : B / ε ≤ eucl x.val := (le_max_right _ _).trans hx
  rw [div_le_iff₀ hε] at h2
  linarith

/-- `A + B log (2t) ≤ ε t` for large `t`. -/
theorem exists_add_mul_log_le (A B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → A + B * Real.log (2 * t) ≤ ε * t := by
  have ho := (Asymptotics.isLittleO_const_id_atTop (A + B * Real.log 2)).add
    (Real.isLittleO_log_id_atTop.const_mul_left B)
  obtain ⟨T, hT⟩ := eventually_atTop.1 (ho.bound hε)
  refine ⟨max T 1, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have h := hT t ((le_max_left _ _).trans ht)
  simp only [id, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)] at h
  rw [Real.log_mul two_ne_zero (by linarith)]
  linarith [le_abs_self (A + B * Real.log 2 + B * Real.log t)]

/-! ### The pole function `f = -Δu` -/

/-- The component Laplacian of a difference. -/
theorem componentLaplacian_sub (C : OpenComponent ω) (u v : C → ℝ) (x : C) :
    componentLaplacian C (fun y => u y - v y) x =
      componentLaplacian C u x - componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A function tending to zero at infinity with integer-valued Laplacian has finitely supported
Laplacian: off the finite set where `|u| ≥ 1/10` and its neighbours, `|Δu| ≤ 4/5`. -/
theorem finite_laplacian_ne_zero (C : OpenComponent ω) (u : C → ℝ)
    (hu : Tendsto u cofinite (𝓝 0)) (hz : ∀ x, ∃ z : ℤ, componentLaplacian C u x = z) :
    {x | componentLaplacian C u x ≠ 0}.Finite := by
  have hev : ∀ᶠ y in cofinite, |u y| < 1 / 10 := by
    refine (hu.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10))).mono fun y hy => ?_
    rwa [Real.dist_eq, sub_zero] at hy
  set T : Set C := {y | ¬|u y| < 1 / 10}
  have hT : T.Finite := eventually_cofinite.1 hev
  refine (hT.union (hT.biUnion fun y _ => Set.toFinite ((componentGraph C).neighborSet y))).subset
    fun x hx => by_contra fun hxS => hx ?_
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxS
  obtain ⟨hxT, hxN⟩ := hxS
  have hux : |u x| < 1 / 10 := not_not.1 hxT
  have hy : ∀ y ∈ (componentGraph C).neighborFinset x, |u y - u x| ≤ 1 / 5 := by
    intro y hy
    have hyT : y ∉ T := fun hyT =>
      hxN y hyT ((SimpleGraph.mem_neighborFinset _ _ _).1 hy).symm
    have huy : |u y| < 1 / 10 := not_not.1 hyT
    linarith [abs_sub (u y) (u x)]
  have hdeg : (componentGraph C).degree x ≤ 4 := componentGraph_degree_le C x
  have hdeg' : ((componentGraph C).degree x : ℝ) ≤ 4 := by exact_mod_cast hdeg
  have hbound : |componentLaplacian C u x| < 1 :=
    calc |componentLaplacian C u x|
        ≤ ∑ y ∈ (componentGraph C).neighborFinset x, |u y - u x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ (componentGraph C).neighborFinset x, (1 / 5 : ℝ) := Finset.sum_le_sum hy
      _ = ((componentGraph C).degree x : ℝ) * (1 / 5) := by
          rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      _ < 1 := by linarith
  obtain ⟨z, hz'⟩ := hz x
  rw [hz'] at hbound ⊢
  have hz0 : z = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hbound)
  simp [hz0]

/-- The pole function `f = -Δu` of a function `u → 0` with integer Laplacian, extended by zero
off the component: it is finitely supported. -/
theorem exists_pole_of_tendsto_zero (C : OpenComponent ω) (u : C → ℝ)
    (hu : Tendsto u cofinite (𝓝 0)) (hz : ∀ x, ∃ z : ℤ, componentLaplacian C u x = z) :
    ∃ f : Vertex 2 → ℤ, (Function.support f).Finite ∧
      ∀ x : C, -componentLaplacian C u x = f x.val := by
  choose z hz' using hz
  let f : Vertex 2 → ℤ := fun v => if h : ∃ x : C, x.val = v then -z h.choose else 0
  have hf : ∀ x : C, f x.val = -z x := by
    intro x
    have hex : ∃ x' : C, x'.val = x.val := ⟨x, rfl⟩
    simp only [f, dif_pos hex, Subtype.val_injective hex.choose_spec]
  refine ⟨f, ?_, fun x => by rw [hf, hz']; push_cast; ring⟩
  refine ((finite_laplacian_ne_zero C u hu fun x => ⟨z x, hz' x⟩).image Subtype.val).subset
    fun v hv => ?_
  by_cases hex : ∃ x : C, x.val = v
  · obtain ⟨x, rfl⟩ := hex
    refine ⟨x, fun hx => hv ?_, rfl⟩
    rw [hf, neg_eq_zero]
    exact_mod_cast (hz' x).symm.trans hx
  · exact absurd (by simp only [f, dif_neg hex]) hv

/-! ### The deterministic core of Theorem 5.1 -/

/-- Theorem 5.1 on one infinite component carrying a Green family, from Propositions 5.3 and 5.5
for this family, sublinear Liouville and `PotentialLaplacian` (step `step:5.1-liouville`). -/
theorem linearDecay_or_eventuallyZero_of_component (C : OpenComponent ω)
    (hC : (Set.univ : Set C).Infinite) (hLap : PotentialLaplacian) (G : C → C → ℝ)
    (hG : IsGreenFamily C G)
    (h53 : ∀ f : Vertex 2 → ℤ, (Function.support f).Finite → mass C f ≠ 0 ∨
      ∃ L : ℝ, Tendsto (potential C G f) cofinite (𝓝 L) ∧
        (LinearDecay C (fun x => potential C G f x - L) ∨
          EventuallyZero C (fun x => potential C G f x - L)))
    (h55 : ∀ f : Vertex 2 → ℤ, (Function.support f).Finite → mass C f ≠ 0 →
      ∃ c K R₀ : ℝ, 0 < c ∧ 0 < K ∧ ∀ x : C, R₀ ≤ l1 x.val →
        c * Real.log (l1 x.val) ≤ |potential C G f x| ∧
          |potential C G f x| ≤ K * Real.log (l1 x.val))
    (hLiou : ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → |v x| ≤ ε * eucl x.val) →
      ∃ c : ℝ, ∀ x, v x = c)
    (u : C → ℝ) (hu : Tendsto u cofinite (𝓝 0))
    (hz : ∀ x, ∃ z : ℤ, componentLaplacian C u x = z) :
    LinearDecay C u ∨ EventuallyZero C u := by
  haveI : Infinite C := Set.infinite_univ_iff.1 hC
  obtain ⟨f, hf, hfu⟩ := exists_pole_of_tendsto_zero C u hu hz
  have hw : ∀ x, componentLaplacian C (fun y => u y - potential C G f y) x = 0 := by
    intro x
    rw [componentLaplacian_sub]
    linarith [hLap ω C G hG f hf x, hfu x]
  obtain ⟨R₁, hR₁⟩ := exists_abs_le_of_tendsto hu
  rw [abs_zero, zero_add] at hR₁
  by_cases hm : mass C f = 0
  · rcases h53 f hf with hm' | ⟨L, hL, hdich⟩
    · exact absurd hm hm'
    have hwL : Tendsto (fun y => u y - potential C G f y) cofinite (𝓝 (-L)) := by
      simpa using hu.sub hL
    obtain ⟨R₂, hR₂⟩ := exists_abs_le_of_tendsto hwL
    obtain ⟨c₀, hc₀⟩ := hLiou _ hw (sublinear_of_abs_le hR₂)
    have hc₀L : c₀ = -L := by
      have hconst : (fun y => u y - potential C G f y) = fun _ => c₀ := funext hc₀
      rw [hconst] at hwL
      exact tendsto_nhds_unique tendsto_const_nhds hwL
    have hu_eq : (fun x => potential C G f x - L) = u :=
      funext fun x => by linarith [hc₀ x]
    rwa [hu_eq] at hdich
  · obtain ⟨c, K, R₀, hc, hK, hlog⟩ := h55 f hf hm
    have hsub : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val →
        |u x - potential C G f x| ≤ ε * eucl x.val := by
      intro ε hε
      obtain ⟨T, hT⟩ := exists_add_mul_log_le 1 K hε
      refine ⟨max (max R₁ R₀) (max T 1), fun x hx => ?_⟩
      have hxR₁ : R₁ ≤ eucl x.val := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
      have hxR₀ : R₀ ≤ eucl x.val := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
      have hxT : T ≤ eucl x.val := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
      have hx1 : 1 ≤ eucl x.val := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
      have hl := eucl_le_l1 x.val
      have hfx := (hlog x (hxR₀.trans hl)).2
      have hlog2 : Real.log (l1 x.val) ≤ Real.log (2 * eucl x.val) :=
        Real.log_le_log (by linarith) (l1_le_two_mul_eucl x.val)
      have hKlog := mul_le_mul_of_nonneg_left hlog2 hK.le
      linarith [abs_sub (u x) (potential C G f x), hR₁ x hxR₁, hT _ hxT]
    obtain ⟨c₀, hc₀⟩ := hLiou _ hw hsub
    exfalso
    set E := Real.exp ((1 + |c₀|) / c + 1)
    obtain ⟨x, hx⟩ := exists_le_eucl C hC (max (max R₁ R₀) E)
    have hxR₁ : R₁ ≤ eucl x.val := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
    have hxR₀ : R₀ ≤ eucl x.val := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    have hxE : E ≤ eucl x.val := (le_max_right _ _).trans hx
    have hl := eucl_le_l1 x.val
    have hfx := (hlog x (hxR₀.trans hl)).1
    have hlogE : (1 + |c₀|) / c + 1 ≤ Real.log (l1 x.val) := by
      rw [← Real.log_exp ((1 + |c₀|) / c + 1)]
      exact Real.log_le_log (Real.exp_pos _) (hxE.trans hl)
    have hcl := mul_le_mul_of_nonneg_left hlogE hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at hcl
    have hufx : potential C G f x = u x - c₀ := by linarith [hc₀ x]
    rw [hufx] at hfx
    linarith [abs_sub (u x) c₀, hR₁ x hxR₁]

/-! ### Theorem 5.1 -/

/-- The finitely supported pole functions `f : ℤ² → ℤ`. -/
abbrev FinitePole : Type := {f : Vertex 2 → ℤ // (Function.support f).Finite}

/-- Step `step:5.1-countable`: the finitely supported pole functions form a countable family. -/
instance : Countable FinitePole :=
  Function.Injective.countable (f := fun F : FinitePole => Finsupp.ofSupportFinite F.1 F.2)
    fun _ _ h => Subtype.ext (funext fun v => DFunLike.congr_fun h v)

/-- Theorem 5.1 from Propositions 5.3 and 5.5 (for every finitely supported `f`), the existence
of a Green family, sublinear Liouville and `PotentialLaplacian`. -/
theorem fastDecayDichotomy_of_steps {p : unitInterval}
    (h53 : ∀ f, FastDecayPotentialStmt p f) (h55 : ∀ f, LogGrowthStmt p f)
    (hGreen : GreenFamilyExists p) (hLiou : SublinearLiouville p) (hLap : PotentialLaplacian) :
    FastDecayDichotomyStmt p := by
  filter_upwards [ae_all_iff.2 fun F : FinitePole => h53 F.1 F.2,
    ae_all_iff.2 fun F : FinitePole => h55 F.1 F.2, hGreen, hLiou] with ω H53 H55 HG HL
  obtain ⟨h, -⟩ := H53 ⟨0, by simp⟩
  refine ⟨h, fun u hu hz => ?_⟩
  obtain ⟨G, hG⟩ := HG h
  exact linearDecay_or_eventuallyZero_of_component _
    (Set.infinite_univ_iff.mpr (Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)))
    hLap G hG (fun f hf => (H53 ⟨f, hf⟩).choose_spec G hG)
    (fun f hf => (H55 ⟨f, hf⟩).choose_spec G hG) (HL h) u hu hz

end Rigidity.Steps.Section5
