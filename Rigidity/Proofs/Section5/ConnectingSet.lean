import Rigidity.Steps.Section5.MeanZeroRepresentation
import Rigidity.Proofs.S3.ChemicalDistance

/-! # Lemma 5.6, step `ConnectingSetStep`: a connected set around `supp f ∩ 𝒞_∞` of size `O_s(1)`

The proof of Lemma 5.6 (corrected draft L1582-1592, eq. `bound-on-size`) uses the cluster
`𝒞_*(□_f)` of the smallest well-connected box `□_f` containing `supp f ∩ 𝒞_∞`, whose size is
`O_s(C_f)` by Proposition 2.3. We prove the step `Steps.Section5.ConnectingSetStep` (d = 2) from
`Rigidity.External.WellConnectedInput` alone, reusing the chaining of good subcubes of the
chemical-distance bound (`Rigidity.Proofs.S3.exists_walk_of_isWellConnected`):

* deterministic part: if `supp f ⊆ Q_N` and `Q_N` is well-connected, the vertices of the open
  walks of length at most `(2d + 1) 4^d N^{3/2}` joining a point of `supp f ∩ 𝒞_∞` to the others
  form a set `V ⊆ 𝒞_∞`, connected through its own edges, with `|V| ≤ |supp f| (80 N^{3/2} + 1)`;
* the scale: `X(ω)` is the first `N ≥ N_f` outside a measurable hull `A_N ⊇ {Q_N not
  well-connected}` (`toMeasurable`, so no measurability of well-connectedness is needed), with
  `P[X = m + 1] ≤ P[A_m] ≤ C exp(-c m^s)`; by Borel–Cantelli `X` is almost surely a
  well-connected scale;
* stochastic integrability: `exp((K X²)^{s/4})` is integrable (an AM–GM bound against the
  stretched-exponential tail), hence by dominated convergence `K X² ≤ O_{s/4}(θ)` for `θ` large.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Proofs.Section5

open Rigidity.Section2 Rigidity.Proofs.S3

variable {d : ℕ}

/-! ### The connecting set in a well-connected cube -/

/-- The union of the supports of walks from a common base point is connected through its own
edges. -/
theorem preconnected_induce_biUnion_support {α ι : Type*} [DecidableEq α] {G : SimpleGraph α}
    {a : α} {b : ι → α} (S : Finset ι) (w : ∀ i, G.Walk a (b i)) :
    (G.induce (↑(S.biUnion fun i => (w i).support.toFinset) : Set α)).Preconnected := by
  set V := S.biUnion fun i => (w i).support.toFinset
  have hmem : ∀ k ∈ S, ∀ x ∈ (w k).support, x ∈ (V : Set α) := fun k hk x hx =>
    Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, hk, List.mem_toFinset.2 hx⟩)
  have reach : ∀ k (hk : k ∈ S) x (hx : x ∈ (w k).support),
      (G.induce (V : Set α)).Reachable ⟨a, hmem k hk a (w k).start_mem_support⟩
        ⟨x, hmem k hk x hx⟩ := fun k hk x hx =>
    (((w k).takeUntil x hx).induce (V : Set α) fun y hy =>
      hmem k hk y ((w k).support_takeUntil_subset_support hx hy)).reachable
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hu)
  obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hv)
  exact (reach i hi u (List.mem_toFinset.1 hui)).symm.trans (reach j hj v (List.mem_toFinset.1 hvj))

/-- An open walk between two vertices of a component is a walk of the component graph of the
same length. -/
theorem exists_componentGraph_walk {ω : Configuration d} (C : OpenComponent ω) (x y : C)
    (q : (openGraph ω).Walk x y) : ∃ w : (componentGraph C).Walk x y, w.length = q.length := by
  have hq : ∀ v ∈ q.support, v ∈ C.supp := fun v hv =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      ((SimpleGraph.ConnectedComponent.eq.mpr (q.takeUntil v hv).reachable.symm).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp x.2))
  exact ⟨q.induce C.supp hq, (SimpleGraph.Walk.length_map _ _).symm.trans
    (congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce q hq))⟩

/-- **Connecting set in a well-connected cube.** If `Q_N` is well-connected, a finite set `S` of
vertices of an infinite open cluster `C` lying in `Q_N` is contained in a set `V ⊆ C` connected
through the edges of `C` inside `V`, with `|V| ≤ |S| ((2d + 1) 4^d N^{3/2} + 1)`: the vertices of
open walks of chemical length at most `(2d + 1) 4^d N^{3/2}` from one point of `S` to the
others. -/
theorem exists_connectingSet_of_isWellConnected [NeZero d] {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) {N : ℕ} (hN : 1 ≤ N)
    (hwc : IsWellConnected ω 0 N) (S : Finset C) (hS : ∀ y ∈ S, y.val ∈ cubeAt 0 N) :
    ∃ V : Finset C, ((componentGraph C).induce (V : Set C)).Preconnected ∧ S ⊆ V ∧
      (V.card : ℝ) ≤ S.card * ((2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ) + 1) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · refine ⟨∅, ?_, Finset.Subset.refl _, by simp⟩
    rintro ⟨u, hu⟩
    simp at hu
  have hinf : ∀ y : C, ((openGraph ω).connectedComponentMk y.val).supp.Infinite := fun y => by
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp y.2]
    exact hC
  have hw : ∀ y : S, ∃ w : (componentGraph C).Walk y₀ y.1,
      (w.length : ℝ) ≤ (2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ) := by
    intro y
    obtain ⟨q, hq⟩ := exists_walk_of_isWellConnected hN hwc (hS y₀ hy₀) (hS y.1 y.2)
      (hinf y₀) (hinf y.1)
    obtain ⟨w, hwq⟩ := exists_componentGraph_walk C y₀ y.1 q
    exact ⟨w, by rw [hwq]; exact (Nat.cast_le.mpr hq).trans (chainBound_le hN)⟩
  choose w hwlen using hw
  refine ⟨S.attach.biUnion fun y => (w y).support.toFinset,
    preconnected_induce_biUnion_support (b := Subtype.val) S.attach w, fun y hy => ?_, ?_⟩
  · exact Finset.mem_biUnion.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _,
      List.mem_toFinset.2 (w _).end_mem_support⟩
  · calc ((S.attach.biUnion fun y => (w y).support.toFinset).card : ℝ)
        ≤ ∑ y ∈ S.attach, ((w y).support.toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ S.attach, ((2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ) + 1) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have h1 := List.toFinset_card_le (w y).support
          rw [SimpleGraph.Walk.length_support] at h1
          have h2 : ((w y).support.toFinset.card : ℝ) ≤ (w y).length + 1 := by exact_mod_cast h1
          linarith [hwlen y]
      _ = _ := by rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]

/-- A finitely supported function on `ℤ^d` is supported in a cube `Q_N` with `N ≥ 1`. -/
theorem exists_cube_superset_support {f : Vertex d → ℤ} (hf : (Function.support f).Finite) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x, f x ≠ 0 → x ∈ cubeAt 0 N := by
  set T := ∑ x ∈ hf.toFinset, ∑ i, (x i).natAbs
  refine ⟨T + 1, by omega, fun x hx i => ?_⟩
  have h1 : (x i).natAbs ≤ ∑ i, (x i).natAbs :=
    Finset.single_le_sum (f := fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : ∑ i, (x i).natAbs ≤ T :=
    Finset.single_le_sum (f := fun x : Vertex d => ∑ i, (x i).natAbs) (fun _ _ => Nat.zero_le _)
      (hf.mem_toFinset.mpr hx)
  simp only [Pi.zero_apply, sub_zero]
  rw [abs_le]
  constructor <;> omega

/-! ### A well-connected scale with stretched-exponential tails -/

/-- **A random well-connected scale.** For `n₀ ≥ 1` there is a measurable `X ≥ n₀` such that
`Q_X` is almost surely well-connected and `P[X = m] ≤ C exp(-c m^s)` for `m > n₀`: `X` is the
first `N ≥ n₀` outside a measurable hull `A_N` of the event that `Q_N` is not well-connected. -/
theorem exists_wellConnectedScale [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) :
    ∃ c C s : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 < s ∧ ∃ X : Configuration d → ℕ, Measurable X ∧
      (∀ ω, n₀ ≤ X ω) ∧
      (∀ m : ℕ, n₀ < m → latticeBondLaw d p {ω | X ω = m} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (m : ℝ) ^ s)))) ∧
      ∀ᵐ ω ∂latticeBondLaw d p, IsWellConnected ω 0 (X ω) := by
  classical
  obtain ⟨c, C, s, hc, hC, hs, hbound⟩ := hwc d hd p hpc hp1
  set μ := latticeBondLaw d p
  set A : ℕ → Set (Configuration d) := fun N => toMeasurable μ {ω | ¬ IsWellConnected ω 0 N}
  have hAm : ∀ N, MeasurableSet (A N) := fun N => measurableSet_toMeasurable _ _
  have hAμ : ∀ N : ℕ, μ (A N) ≤ ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s))) := fun N =>
    (measure_toMeasurable _).trans_le (hbound 0 N)
  set B : Set (Configuration d) := {ω | ∀ N, n₀ ≤ N → ω ∈ A N}
  have hBm : MeasurableSet B := by
    have : B = ⋂ N, ⋂ (_ : n₀ ≤ N), A N := by ext ω; simp [B]
    rw [this]
    exact MeasurableSet.iInter fun N => MeasurableSet.iInter fun _ => hAm N
  have hP : ∀ ω, ∃ N, n₀ ≤ N ∧ (ω ∉ A N ∨ ω ∈ B) := by
    intro ω
    by_cases hω : ω ∈ B
    · exact ⟨n₀, le_rfl, Or.inr hω⟩
    · simp only [B, Set.mem_setOf_eq, not_forall] at hω
      obtain ⟨N, hN, hωN⟩ := hω
      exact ⟨N, hN, Or.inl hωN⟩
  refine ⟨c / 2 ^ s, C, s, by positivity, hC.le, hs, fun ω => Nat.find (hP ω),
    measurable_find hP fun k => (MeasurableSet.const _).inter ((hAm k).compl.union hBm),
    fun ω => (Nat.find_spec (hP ω)).1, ?_, ?_⟩
  · intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n₀ ≤ m' := by omega
    refine (measure_mono fun ω (hω : Nat.find (hP ω) = m' + 1) => ?_).trans
      ((hAμ m').trans (ENNReal.ofReal_le_ofReal ?_))
    · have := Nat.find_min (hP ω) (show m' < Nat.find (hP ω) by omega)
      simp only [not_and, not_or, not_not] at this
      exact (this hm').1
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) hC.le
      have hm1 : (1 : ℝ) ≤ m' := by exact_mod_cast hn₀.trans hm'
      have h1 : ((m' + 1 : ℕ) : ℝ) ^ s ≤ 2 ^ s * (m' : ℝ) ^ s := by
        rw [← Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) hs.le
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  · have hsum : ∑' N, μ (A N) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAμ)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
        ((summable_exp_neg_mul_rpow hc hs).mul_left C)]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    have hωB : ω ∉ B := by
      obtain ⟨N, hωN, hN⟩ := (hω.and (eventually_ge_atTop n₀)).exists
      exact fun h => hωN (h N hN)
    have hnot : ω ∉ A (Nat.find (hP ω)) := (Nat.find_spec (hP ω)).2.resolve_right hωB
    by_contra hbad
    exact hnot (subset_toMeasurable μ _ hbad)

/-! ### Stochastic integrability -/

/-- AM–GM against the tail: `(K m²)^{s/4} - c m^s ≤ (K^{s/2} + 1)/c - (c/2) m^s`. -/
theorem rpow_sub_le_of_amgm {K c s : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (m : ℕ) :
    (K * (m : ℝ) ^ 2) ^ (s / 4) - c * (m : ℝ) ^ s ≤ (K ^ (s / 2) + 1) / c - c / 2 * (m : ℝ) ^ s := by
  have hKm : 0 ≤ K * (m : ℝ) ^ 2 := by positivity
  set z := (K * (m : ℝ) ^ 2) ^ (s / 4)
  set y := (m : ℝ) ^ s
  set D := K ^ (s / 2) + 1
  have hz : 0 ≤ z := Real.rpow_nonneg hKm _
  have hy : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hD : 0 < D := by positivity
  have hz2 : z ^ 2 ≤ D * y := by
    have : z ^ 2 = K ^ (s / 2) * y := by
      rw [← Real.rpow_natCast z 2, ← Real.rpow_mul hKm, Real.mul_rpow hK (by positivity),
        ← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 2 <;> push_cast <;> ring
    rw [this]
    nlinarith
  have hamgm : z ≤ c * z ^ 2 / (4 * D) + D / c := by
    rw [div_add_div _ _ (by positivity) hc.ne', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c * z - 2 * D)]
  have h2 : c * z ^ 2 / (4 * D) ≤ c / 4 * y := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcy : 0 ≤ c * y := mul_nonneg hc.le hy
  linarith

/-- If `P[X = m] ≤ C exp(-c m^s)` for `m ≥ n₀`, then `exp((K X²)^{s/4})` is integrable. -/
theorem integrable_exp_rpow_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℕ} (hX : Measurable X) {K C c s : ℝ} (n₀ : ℕ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : 0 < c) (hs : 0 < s)
    (htail : ∀ m : ℕ, n₀ ≤ m → μ {ω | X ω = m} ≤
      ENNReal.ofReal (C * Real.exp (-(c * (m : ℝ) ^ s)))) :
    Integrable (fun ω => Real.exp (Real.rpow (K * (X ω : ℝ) ^ 2) (s / 4))) μ := by
  obtain ⟨C', hC', htail'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ m : ℕ, μ {ω | X ω = m} ≤
      ENNReal.ofReal (C' * Real.exp (-(c * (m : ℝ) ^ s))) := by
    refine ⟨C + Real.exp (c * (n₀ : ℝ) ^ s), by positivity, fun m => ?_⟩
    rcases le_or_gt n₀ m with hm | hm
    · refine (htail m hm).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (c * (n₀ : ℝ) ^ s)])
        (Real.exp_pos _).le
    · refine prob_le_one.trans ?_
      rw [ENNReal.one_le_ofReal]
      have h1 : (m : ℝ) ^ s ≤ (n₀ : ℝ) ^ s :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm.le) hs.le
      calc (1 : ℝ) = Real.exp (c * (n₀ : ℝ) ^ s) * Real.exp (-(c * (n₀ : ℝ) ^ s)) := by
            rw [← Real.exp_add]; simp
        _ ≤ (C + Real.exp (c * (n₀ : ℝ) ^ s)) * Real.exp (-(c * (m : ℝ) ^ s)) := by
            refine mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
              (by positivity)
            nlinarith
  set g : ℕ → ℝ := fun n => Real.exp (Real.rpow (K * (n : ℝ) ^ 2) (s / 4))
  set B := (K ^ (s / 2) + 1) / c
  have hterm : ∀ m : ℕ, ENNReal.ofReal (g m) * μ {ω | X ω = m} ≤
      ENNReal.ofReal (C' * Real.exp B * Real.exp (-(c / 2 * (m : ℝ) ^ s))) := by
    intro m
    refine (mul_le_mul_right (htail' m) _).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc g m * (C' * Real.exp (-(c * (m : ℝ) ^ s)))
        = C' * Real.exp ((K * (m : ℝ) ^ 2) ^ (s / 4) - c * (m : ℝ) ^ s) := by
          simp only [g, Real.rpow_eq_pow]
          rw [sub_eq_add_neg, Real.exp_add]
          ring
      _ ≤ C' * Real.exp (B - c / 2 * (m : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (rpow_sub_le_of_amgm hK hc m)) hC'
      _ = C' * Real.exp B * Real.exp (-(c / 2 * (m : ℝ) ^ s)) := by
          rw [sub_eq_add_neg, Real.exp_add]
          ring
  refine ⟨((measurable_from_nat (f := g)).comp hX).aestronglyMeasurable, ?_⟩
  show ∫⁻ ω, ‖g (X ω)‖ₑ ∂μ < ⊤
  rw [← lintegral_map (f := fun n => ‖g n‖ₑ) measurable_from_nat hX, lintegral_countable']
  calc ∑' n, ‖g n‖ₑ * μ.map X {n} = ∑' n, ENNReal.ofReal (g n) * μ {ω | X ω = n} := by
        congr 1
        ext n
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le,
          Measure.map_apply hX (measurableSet_singleton n)]
        rfl
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * Real.exp B * Real.exp (-(c / 2 * (n : ℝ) ^ s))) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℕ, C' * Real.exp B * Real.exp (-(c / 2 * (n : ℝ) ^ s))) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => mul_nonneg (mul_nonneg hC' (Real.exp_pos _).le) (Real.exp_pos _).le)
          ((summable_exp_neg_mul_rpow (half_pos hc) hs).mul_left _)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- If `Y ≥ 0` and `exp(Y^s)` is integrable then `Y ≤ O_s(θ)` for some `θ > 0`: by dominated
convergence `E[exp((Y/θ)^s)] → 1` as `θ → ∞`. -/
theorem exists_isOs_of_integrable {p : unitInterval} {Y : Configuration d → ℝ} {s : ℝ}
    (hs : 0 < s) (hY0 : ∀ ω, 0 ≤ Y ω) (hYm : Measurable Y)
    (hint : Integrable (fun ω => Real.exp (Real.rpow (Y ω) s)) (latticeBondLaw d p)) :
    ∃ θ : ℝ, 0 < θ ∧ IsOs d p Y s θ := by
  set μ := latticeBondLaw d p
  set F : ℝ → Configuration d → ℝ := fun θ ω => Real.exp (Real.rpow (max (Y ω / θ) 0) s)
  have hFm : ∀ θ, AEStronglyMeasurable (F θ) μ := fun θ =>
    (((hYm.div_const θ).max measurable_const).pow_const s).exp.aestronglyMeasurable
  have hbound : ∀ θ : ℝ, 1 ≤ θ → ∀ ω, ‖F θ ω‖ ≤ Real.exp (Real.rpow (Y ω) s) := by
    intro θ hθ ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow (le_max_right _ _)
      (max_le (div_le_self (hY0 ω) hθ) (hY0 ω)) hs.le)
  have hlim : ∀ ω, Tendsto (fun θ => F θ ω) atTop (𝓝 1) := by
    intro ω
    have h1 : Tendsto (fun θ : ℝ => max (Y ω / θ) 0) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_id).max
        (tendsto_const_nhds (x := (0 : ℝ)))
    have h2 := (Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto.comp h1
    rw [Real.zero_rpow hs.ne'] at h2
    simpa [F, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h2
  have hT : Tendsto (fun θ => ∫ ω, F θ ω ∂μ) atTop (𝓝 (∫ _ω, (1 : ℝ) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hFm)
      ((eventually_ge_atTop 1).mono fun θ hθ => Eventually.of_forall (hbound θ hθ)) hint
      (Eventually.of_forall hlim)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hT
  obtain ⟨θ, hθ1, hθ2⟩ :=
    ((eventually_ge_atTop 1).and ((tendsto_order.1 hT).2 2 (by norm_num))).exists
  exact ⟨θ, by linarith, hint.mono' (hFm θ) (Eventually.of_forall (hbound θ hθ1)), hθ2.le⟩

/-! ### The step -/

/-- **Step `ConnectingSetStep`** (Lemma 5.6, eq. `bound-on-size`; d = 2): for `p_c < p < 1` and
finitely supported `f`, almost surely `supp f ∩ 𝒞_∞` lies in a finite set `V ⊆ 𝒞_∞` connected
through the edges of `𝒞_∞` inside `V`, with `|V| ≤ 81 |supp f| X²` for the well-connected scale
`X` of `exists_wellConnectedScale`, and `81 |supp f| X² ≤ O_{s/4}(θ)`. -/
theorem connectingSetStep : Rigidity.Steps.Section5.ConnectingSetStep := by
  intro hwc p hpc hp1 f hf
  obtain ⟨Nf, hNf1, hNf⟩ := exists_cube_superset_support hf
  obtain ⟨c, C, s, hc, hC, hs, X, hXm, hXge, hXtail, hXae⟩ :=
    exists_wellConnectedScale (d := 2) le_rfl hpc hp1 hwc Nf hNf1
  have hint := integrable_exp_rpow_of_tail (μ := latticeBondLaw 2 p) hXm
    (K := 81 * (hf.toFinset.card : ℝ)) (Nf + 1) (by positivity) hC hc hs
    fun m hm => hXtail m hm
  have hYm : Measurable fun ω => 81 * (hf.toFinset.card : ℝ) * (X ω : ℝ) ^ 2 :=
    (measurable_from_nat (f := fun n : ℕ => 81 * (hf.toFinset.card : ℝ) * (n : ℝ) ^ 2)).comp hXm
  obtain ⟨θ, hθ, hOs⟩ := exists_isOs_of_integrable (p := p) (by positivity : 0 < s / 4)
    (fun ω => by positivity) hYm hint
  refine ⟨θ, s / 4, hθ, by positivity, _, hYm, hOs, ?_⟩
  filter_upwards [hXae] with ω hω h
  have hfin : ({y : uniqueInfiniteComponent h | f y.val ≠ 0} : Set _).Finite :=
    hf.preimage Subtype.val_injective.injOn
  have hN1 : 1 ≤ X ω := hNf1.trans (hXge ω)
  obtain ⟨V, hVc, hSV, hV⟩ := exists_connectingSet_of_isWellConnected
    (uniqueInfiniteComponent h) (uniqueInfiniteComponent_infinite h) hN1 hω hfin.toFinset
    fun y hy i => (hNf _ (hfin.mem_toFinset.mp hy) i).trans (by exact_mod_cast hXge ω)
  refine ⟨V, hVc, fun y hy => hSV (hfin.mem_toFinset.mpr hy), hV.trans ?_⟩
  have hScard : (hfin.toFinset.card : ℝ) ≤ hf.toFinset.card := by
    exact_mod_cast Finset.card_le_card_of_injOn Subtype.val
      (by intro y hy; exact hf.mem_toFinset.mpr (hfin.mem_toFinset.mp hy))
      Subtype.val_injective.injOn
  have hN1' : (1 : ℝ) ≤ X ω := by exact_mod_cast hN1
  have h32 : (X ω : ℝ) ^ (3 / 2 : ℝ) ≤ (X ω : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have hsq : (1 : ℝ) ≤ (X ω : ℝ) ^ 2 := one_le_pow₀ hN1'
  calc (hfin.toFinset.card : ℝ) * ((2 * ((2 : ℕ) : ℝ) + 1) * 4 ^ 2 * (X ω : ℝ) ^ (3 / 2 : ℝ) + 1)
      ≤ hf.toFinset.card * (81 * (X ω : ℝ) ^ 2) := by
        refine mul_le_mul hScard ?_ (by positivity) (Nat.cast_nonneg _)
        norm_num
        linarith
    _ = 81 * (hf.toFinset.card : ℝ) * (X ω : ℝ) ^ 2 := by ring

end Rigidity.Proofs.Section5
