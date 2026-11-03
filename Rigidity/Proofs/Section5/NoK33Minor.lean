import Rigidity.Proofs.Section5.Separation
import Rigidity.Steps.Section5.FiniteBranches

/-!
# Lemma 5.28: no `K_{3,3}` minor in the planar lattice

This file proves `NoK33MinorStep` (corrected draft L2711-2715, Lemma 5.28) from the
Jordan curve theorem on `S²` (`External.JordanCurveTheoremSphere`).

Let `X₀, X₁, X₂` be disjoint connected subsets of `𝒞_∞` and `z₀, z₁, z₂` distinct points outside
them, each adjacent to each `Xⱼ`. Join a neighbour of `z₀` to a neighbour of `z₁` inside `Xⱼ` by a
simple chain: the arcs `Kⱼ = z₀, Xⱼ ⋯, z₁` form a theta graph (they meet only at `z₀, z₁`).
The point `w = z₂` is joined to the interior of each `Kᵢ` (through `Xᵢ`) off the two other arcs,
so the interior of each arc lies on the side of `w` of the Jordan curve formed by the two others.
This contradicts the theta graph lemma.

The theta graph lemma `false_of_theta` (Lemma 5.19) is stated for `w` outside the three curves.
Here `w` may lie inside some of them, so the lemma is reproved (`false_of_theta_sides`) for the
two sides of the curves treated symmetrically (`CurveSides`): both sides of a Jordan curve of the
plane are preconnected with the curve in their closure (`exists_curveSides`; for the side through
`∞` this is `isPreconnected_preimage_toSphere`).
-/

open Set Topology Function LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5
  Rigidity.External

namespace Rigidity.Proofs.Section5

/-! ### The two sides of a Jordan curve, treated symmetrically -/

/-- `P` and `Q` are the two sides of the closed set `J` of the plane: open, disjoint and covering
`ℝ² \ J`, the side `P` preconnected with `J` in its closure. -/
structure CurveSides (J P Q : Set Plane) : Prop where
  isOpen_far : IsOpen P
  isOpen_near : IsOpen Q
  isPreconnected_far : IsPreconnected P
  disjoint : Disjoint P Q
  union_eq : P ∪ Q = Jᶜ
  subset_closure : J ⊆ closure P

namespace CurveSides

variable {J P Q : Set Plane}

theorem disjoint_far (h : CurveSides J P Q) : Disjoint P J :=
  Set.disjoint_left.2 fun _ hvP hvJ => (show _ ∈ Jᶜ from h.union_eq ▸ Or.inl hvP) hvJ

theorem disjoint_near (h : CurveSides J P Q) : Disjoint Q J :=
  Set.disjoint_left.2 fun _ hvQ hvJ => (show _ ∈ Jᶜ from h.union_eq ▸ Or.inr hvQ) hvJ

/-- A preconnected set off `J` meeting `P` lies in `P`. -/
theorem subset_far (h : CurveSides J P Q) {H : Set Plane} (hH : IsPreconnected H)
    (hHJ : Disjoint H J) (hne : (H ∩ P).Nonempty) : H ⊆ P := by
  refine hH.subset_left_of_subset_union h.isOpen_far h.isOpen_near h.disjoint ?_ hne
  rw [h.union_eq]
  exact fun x hx hxJ => hHJ.ne_of_mem hx hxJ rfl

/-- A preconnected set off `J` meeting `Q` lies in `Q`. -/
theorem subset_near (h : CurveSides J P Q) {H : Set Plane} (hH : IsPreconnected H)
    (hHJ : Disjoint H J) (hne : (H ∩ Q).Nonempty) : H ⊆ Q := by
  refine hH.subset_left_of_subset_union h.isOpen_near h.isOpen_far h.disjoint.symm ?_ hne
  rw [union_comm, h.union_eq]
  exact fun x hx hxJ => hHJ.ne_of_mem hx hxJ rfl

/-- The far side of the curve formed by two arcs misses the third arc when its interior lies on
the near side. -/
theorem disjoint_arc (h : CurveSides J P Q) {K A : Set Plane} (hK : K ⊆ A ∪ J) (hA : A ⊆ Q) :
    Disjoint P (K ∪ J) := by
  refine Set.disjoint_union_right.2 ⟨Set.disjoint_left.2 fun x hxP hx => ?_, h.disjoint_far⟩
  rcases hK hx with hxA | hxJ
  · exact h.disjoint.ne_of_mem hxP (hA hxA) rfl
  · exact h.disjoint_far.ne_of_mem hxP hxJ rfl

/-- Two far sides are disjoint when a point on the near side of the second lies on the first
curve. -/
theorem disjoint_fars {J' P' Q' : Set Plane} {y : Plane} (h : CurveSides J P Q)
    (h' : CurveSides J' P' Q') (hPJ' : Disjoint P J') (hyJ : y ∈ J) (hyQ' : y ∈ Q') :
    Disjoint P P' := by
  refine Set.disjoint_left.2 fun x hxP hxP' => ?_
  have hsub : P ⊆ P' := h'.subset_far h.isPreconnected_far hPJ' ⟨x, hxP, hxP'⟩
  have hy : y ∈ closure P' := closure_mono hsub (h.subset_closure hyJ)
  exact (h'.disjoint.symm.closure_right h'.isOpen_near).ne_of_mem hyQ' hy rfl

end CurveSides

/-! ### Both sides of a Jordan curve of the plane -/

/-- The exterior of a ball of the plane is preconnected. -/
theorem isPreconnected_norm_gt {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected {x : Plane | R < ‖x‖} := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  have heq : {x : Plane | R < ‖x‖} =
      (fun p : ℝ × Plane => p.1 • p.2) '' (Ioi R ×ˢ Metric.sphere (0 : Plane) 1) := by
    ext x
    constructor
    · intro hx
      have hx0 : ‖x‖ ≠ 0 := (hR.trans_lt hx).ne'
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0]
      · simp only [smul_smul, mul_inv_cancel₀ hx0, one_smul]
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hv
      show R < ‖t • v‖
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (hR.trans_lt ht)]
      exact ht
  rw [heq]
  exact (isPreconnected_Ioi.prod (isPreconnected_sphere hrank 0 1)).image _
    (continuous_fst.smul continuous_snd).continuousOn

/-- A preconnected open subset of `S²` is preconnected in the plane, also through `∞`. -/
theorem isPreconnected_preimage_toSphere {U : Set S2} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsPreconnected (toSphere ⁻¹' U) := by
  by_cases hN : sphereInfty ∈ U
  swap
  · have hUr : U ⊆ range toSphere := by
      rw [range_toSphere]
      intro w hw hw'
      rw [mem_singleton_iff] at hw'
      exact hN (hw' ▸ hw)
    rw [← isOpenEmbedding_toSphere.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset hUr]
    exact hUc
  set O := toSphere ⁻¹' U with hOdef
  have hcob : O ∈ Bornology.cobounded Plane := tendsto_toSphere_cobounded (hU.mem_nhds hN)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).1
    (Bornology.isBounded_def.2 (by rwa [compl_compl]))
  set R' := max R 0 with hR'
  set E := {x : Plane | R' < ‖x‖} with hEdef
  have hEc : IsPreconnected E := isPreconnected_norm_gt (le_max_right _ _)
  have hEO : E ⊆ O := fun x hx => by
    by_contra hxO
    have := hR hxO
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd (lt_of_le_of_lt (le_max_left R 0) hx) (not_lt.2 this)
  -- a neighbourhood of `∞` in `S²` whose points other than `∞` come from `E`
  set N := (toSphere '' Metric.closedBall (0 : Plane) R')ᶜ with hNdef
  have hNo : IsOpen N :=
    ((isCompact_closedBall _ _).image continuous_toSphere).isClosed.isOpen_compl
  have hNi : sphereInfty ∈ N := fun ⟨x, _, hx⟩ => toSphere_ne_infty x hx
  have hNE : ∀ x, toSphere x ∈ N → x ∈ E := fun x hx => by
    by_contra hxE
    exact hx ⟨x, by simpa [hEdef] using hxE, rfl⟩
  have key : ∀ u v : Set Plane, IsOpen u → IsOpen v → O ⊆ u ∪ v → (O ∩ v).Nonempty →
      O ∩ (u ∩ v) = ∅ → E ⊆ u → False := by
    intro u v hu hv hsub hOv huv hEu
    have ho₁ : IsOpen (toSphere '' (O ∩ u) ∪ N) :=
      (isOpenEmbedding_toSphere.isOpenMap _ ((hU.preimage continuous_toSphere).inter hu)).union
        hNo
    have ho₂ : IsOpen (toSphere '' (O ∩ v)) :=
      isOpenEmbedding_toSphere.isOpenMap _ ((hU.preimage continuous_toSphere).inter hv)
    have hcov : U ⊆ (toSphere '' (O ∩ u) ∪ N) ∪ toSphere '' (O ∩ v) := by
      intro p hp
      by_cases hpN : p = sphereInfty
      · exact Or.inl (Or.inr (hpN ▸ hNi))
      · have : p ∈ range toSphere := by rw [range_toSphere]; exact hpN
        obtain ⟨x, rfl⟩ := this
        rcases hsub (show x ∈ O from hp) with hxu | hxv
        · exact Or.inl (Or.inl ⟨x, ⟨hp, hxu⟩, rfl⟩)
        · exact Or.inr ⟨x, ⟨hp, hxv⟩, rfl⟩
    obtain ⟨x, hxO, hxv⟩ := hOv
    obtain ⟨p, -, hp₁, ⟨y, ⟨hyO, hyv⟩, rfl⟩⟩ := hUc _ _ ho₁ ho₂ hcov ⟨sphereInfty, hN, Or.inr hNi⟩
      ⟨toSphere x, hxO, ⟨x, ⟨hxO, hxv⟩, rfl⟩⟩
    have hyu : y ∈ u := by
      rcases hp₁ with ⟨y', ⟨-, hy'u⟩, e⟩ | hpN
      · exact toSphere_injective e ▸ hy'u
      · exact hEu (hNE y hpN)
    exact (Set.eq_empty_iff_forall_notMem.1 huv) y ⟨hyO, hyu, hyv⟩
  intro u v hu hv hsub hOu hOv
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hd : Disjoint (u ∩ O) (v ∩ O) := Set.disjoint_left.2 fun x hx hx' =>
    (Set.eq_empty_iff_forall_notMem.1 hne) x ⟨hx.2, hx.1, hx'.1⟩
  rcases hEc.subset_or_subset (hu.inter (hU.preimage continuous_toSphere))
      (hv.inter (hU.preimage continuous_toSphere)) hd
      (fun x hx => (hsub (hEO hx)).imp (fun h => ⟨h, hEO hx⟩) (fun h => ⟨h, hEO hx⟩)) with h | h
  · exact key u v hu hv hsub hOv hne fun x hx => (h hx).1
  · refine key v u hv hu (by rwa [union_comm]) hOu (by rwa [inter_comm u v] at hne)
      fun x hx => (h hx).1

/-- The curve lies in the closure of each side. -/
theorem subset_closure_preimage_toSphere {K : Set Plane} {U : Set S2}
    (hU : frontier U = toSphere '' K) : K ⊆ closure (toSphere ⁻¹' U) := by
  intro x hx
  rw [mem_closure_iff]
  intro o ho hxo
  have h1 : toSphere x ∈ closure U := frontier_subset_closure (hU ▸ mem_image_of_mem _ hx)
  obtain ⟨p, ⟨y, hyo, rfl⟩, hpU⟩ := mem_closure_iff.1 h1 _
    (isOpenEmbedding_toSphere.isOpenMap _ ho) (mem_image_of_mem _ hxo)
  exact ⟨y, hyo, hpU⟩

theorem curveSides_of_sphere {K : Set Plane} {U V : Set S2} (hU : IsOpen U) (hV : IsOpen V)
    (hVc : IsPreconnected V) (hUV : Disjoint U V) (hunion : U ∪ V = (toSphere '' K)ᶜ)
    (hfV : frontier V = toSphere '' K) :
    CurveSides K (toSphere ⁻¹' V) (toSphere ⁻¹' U) where
  isOpen_far := hV.preimage continuous_toSphere
  isOpen_near := hU.preimage continuous_toSphere
  isPreconnected_far := isPreconnected_preimage_toSphere hV hVc
  disjoint := hUV.symm.preimage _
  union_eq := by
    rw [← preimage_union, union_comm, hunion, preimage_compl,
      preimage_image_eq _ toSphere_injective]
  subset_closure := subset_closure_preimage_toSphere hfV

/-- The Jordan curve theorem on `S²` for a simple closed curve of the plane, both sides. -/
theorem exists_curveSides (hJ : JordanCurveTheoremSphere) {K : Set Plane} {q : S2}
    (β : Path q q) (hβ : InjOn β (Ico 0 1)) (hr : range β = toSphere '' K) :
    ∃ P Q, CurveSides K P Q ∧ CurveSides K Q P := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hunion, hfU, hfV⟩ := hJ q β hβ
  rw [hr] at hunion hfU hfV
  exact ⟨_, _, curveSides_of_sphere hU hV hVc.isPreconnected hUV hunion hfV,
    curveSides_of_sphere hV hU hUc.isPreconnected hUV.symm (by rw [union_comm]; exact hunion)
      hfU⟩

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- Two arcs from `X 0 = Y 0` to `X L = Y M` meeting only at their endpoints form a Jordan
curve; both sides. -/
theorem exists_curveSides_of_arcs (hJ : JordanCurveTheoremSphere) {X Y : ℤ → C} {L M : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) (hY : IsSimpleChain (componentGraph C) Y M)
    (h0 : X 0 = Y 0) (hLM : X L = Y M) (h3 : 3 ≤ L + M)
    (hth : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M)) :
    ∃ P Q, CurveSides (arcTrace X L ∪ arcTrace Y M) P Q ∧
      CurveSides (arcTrace X L ∪ arcTrace Y M) Q P := by
  have hcj : X L = chainRev Y M 0 := by simp [chainRev, hLM]
  have hYr := hY.rev
  set c := chainAppend X L (chainRev Y M) with hc
  have hval : ∀ k : ℤ, (L : ℤ) ≤ k → c k = Y (M - (k - L)) := fun k hk => by
    rw [hc, chainAppend_of_ge hcj hk]
    rfl
  have hcm : (Subtype.val ∘ c) ((L + M : ℕ) : ℤ) = (Subtype.val ∘ c) 0 := by
    show (c _).val = (c 0).val
    rw [hval _ (by push_cast; omega), hc, chainAppend_of_le (by omega),
      show (M : ℤ) - (((L + M : ℕ) : ℤ) - L) = 0 by push_cast; ring, h0]
  have hadj : ∀ k : ℤ, 0 ≤ k → k < ((L + M : ℕ) : ℤ) →
      (nearestNeighborGraph 2).Adj ((Subtype.val ∘ c) k) ((Subtype.val ∘ c) (k + 1)) := by
    intro k hk0 hk1
    push_cast at hk1
    by_cases hk : k < L
    · simp only [Function.comp, hc]
      rw [chainAppend_of_le hk.le, chainAppend_of_le (by omega)]
      exact Rigidity.Proofs.Section5.adj_val (hX.adj k hk0 hk)
    · simp only [Function.comp]
      rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_ge hcj (by omega),
        show k + 1 - L = k - L + 1 by ring]
      exact Rigidity.Proofs.Section5.adj_val (hYr.adj _ (by omega) (by omega))
  have hinj : ∀ k k' : ℤ, 0 ≤ k → k < ((L + M : ℕ) : ℤ) → 0 ≤ k' → k' < ((L + M : ℕ) : ℤ) →
      (Subtype.val ∘ c) k = (Subtype.val ∘ c) k' → k = k' := by
    intro k k' hk0 hk1 hk0' hk1' e
    push_cast at hk1 hk1'
    have e' : c k = c k' := Subtype.ext e
    by_cases hk : k ≤ L <;> by_cases hk' : k' ≤ L
    · rw [hc, chainAppend_of_le hk, chainAppend_of_le hk'] at e'
      exact hX.inj _ _ hk0 hk hk0' hk' e'
    · rw [hc, chainAppend_of_le hk, chainAppend_of_ge hcj (by omega)] at e'
      have := hth _ _ hk0 hk (by omega) (by omega) e'
      omega
    · rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_le hk'] at e'
      have := hth _ _ hk0' hk' (by omega) (by omega) e'.symm
      omega
    · rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_ge hcj (by omega)] at e'
      have := hYr.inj _ _ (by omega) (by omega) (by omega) (by omega) e'
      omega
  obtain ⟨q, β, hβ, hr⟩ := exists_path_cycle h3 hcm hadj hinj
  refine exists_curveSides hJ β hβ ?_
  rw [hr]
  congr 1
  rw [arcTrace, arcTrace, ← chainTrace_chainRev Subtype.val Y M]
  exact chainTrace_chainAppend Subtype.val hcj

/-- **Theta graph**, both sides. Three unions of lattice segments `K₁, K₂, K₃`, with interiors
`Aᵢ` off the other two, cannot all have their interior on the side of `w` of the Jordan curve
formed by the other two, for a point `w` off the three arcs (the proof of `false_of_theta`). -/
theorem false_of_theta_sides {K₁ K₂ K₃ P₁ P₂ P₃ Q₁ Q₂ Q₃ A₁ A₂ A₃ : Set Plane} {w : Plane}
    (hΘ : IsClosed (K₁ ∪ K₂ ∪ K₃))
    (hloc : ∀ v ∈ K₁ ∪ K₂ ∪ K₃, v ∉ range latticePoint → ∃ δ > 0, ∃ H₁ H₂ : Set Plane,
      IsPreconnected H₁ ∧ IsPreconnected H₂ ∧ H₁.Nonempty ∧ H₂.Nonempty ∧
      Disjoint H₁ (K₁ ∪ K₂ ∪ K₃) ∧ Disjoint H₂ (K₁ ∪ K₂ ∪ K₃) ∧
      Metric.ball v δ ⊆ H₁ ∪ H₂ ∪ (K₁ ∪ K₂ ∪ K₃))
    (h₁ : CurveSides (K₂ ∪ K₃) P₁ Q₁) (h₂ : CurveSides (K₁ ∪ K₃) P₂ Q₂)
    (h₃ : CurveSides (K₁ ∪ K₂) P₃ Q₃)
    (hK₁ : K₁ ⊆ A₁ ∪ (K₂ ∪ K₃)) (hA₁Q : A₁ ⊆ Q₁)
    (hA₂ : A₂ ⊆ K₂) (hK₂ : K₂ ⊆ A₂ ∪ (K₁ ∪ K₃)) (hA₂Q : A₂ ⊆ Q₂) (hA₂n : A₂.Nonempty)
    (hA₃ : A₃ ⊆ K₃) (hK₃ : K₃ ⊆ A₃ ∪ (K₁ ∪ K₂)) (hA₃Q : A₃ ⊆ Q₃) (hA₃n : A₃.Nonempty)
    (hw : w ∉ K₁ ∪ K₂ ∪ K₃) (hw₁ : w ∈ Q₁) (hw₂ : w ∈ Q₂) (hw₃ : w ∈ Q₃)
    (hy : ∃ y ∈ K₁ ∪ K₂ ∪ K₃, y ∉ range latticePoint) : False := by
  set Θ := K₁ ∪ K₂ ∪ K₃ with hΘdef
  -- the insides miss `Θ`
  have hP₁ : Disjoint P₁ Θ := by
    have := h₁.disjoint_arc hK₁ hA₁Q
    rwa [show K₁ ∪ (K₂ ∪ K₃) = Θ by rw [hΘdef, union_assoc]] at this
  have hP₂ : Disjoint P₂ Θ := by
    have := h₂.disjoint_arc hK₂ hA₂Q
    rwa [show K₂ ∪ (K₁ ∪ K₃) = Θ by rw [hΘdef]; ac_rfl] at this
  have hP₃ : Disjoint P₃ Θ := by
    have := h₃.disjoint_arc hK₃ hA₃Q
    rwa [show K₃ ∪ (K₁ ∪ K₂) = Θ by rw [hΘdef]; ac_rfl] at this
  have hJ₁ : K₂ ∪ K₃ ⊆ Θ := by rw [hΘdef, union_assoc]; exact subset_union_right
  have hJ₂ : K₁ ∪ K₃ ⊆ Θ := union_subset (subset_union_left.trans subset_union_left)
    subset_union_right
  have hJ₃ : K₁ ∪ K₂ ⊆ Θ := subset_union_left
  -- the insides are pairwise disjoint
  obtain ⟨a₂, ha₂⟩ := hA₂n
  obtain ⟨a₃, ha₃⟩ := hA₃n
  have hP₁₂ : Disjoint P₁ P₂ := h₁.disjoint_fars h₂ (hP₁.mono_right hJ₂)
    (Or.inl (hA₂ ha₂)) (hA₂Q ha₂)
  have hP₁₃ : Disjoint P₁ P₃ := h₁.disjoint_fars h₃ (hP₁.mono_right hJ₃)
    (Or.inr (hA₃ ha₃)) (hA₃Q ha₃)
  have hP₂₃ : Disjoint P₂ P₃ := h₂.disjoint_fars h₃ (hP₂.mono_right hJ₃)
    (Or.inr (hA₃ ha₃)) (hA₃Q ha₃)
  -- the component `W` of `w`
  set W := connectedComponentIn Θᶜ w with hWdef
  have hWo : IsOpen W := hΘ.isOpen_compl.connectedComponentIn
  have hWΘ : Disjoint W Θ :=
    Set.disjoint_left.2 fun x hx hxΘ => connectedComponentIn_subset _ _ hx hxΘ
  have hwW : w ∈ W := mem_connectedComponentIn hw
  have hWI : ∀ {J I O : Set Plane}, CurveSides J I O → J ⊆ Θ → w ∈ O → Disjoint W I := by
    intro J I O h hJ hwO
    have : W ⊆ O := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union h.isOpen_near
        h.isOpen_far h.disjoint.symm ?_ ⟨w, hwW, hwO⟩
      rw [union_comm, h.union_eq]
      exact fun x hx hxJ => hWΘ.ne_of_mem hx (hJ hxJ) rfl
    exact h.disjoint.symm.mono_left this
  have hW₁ := hWI h₁ hJ₁ hw₁
  have hW₂ := hWI h₂ hJ₂ hw₂
  have hW₃ := hWI h₃ hJ₃ hw₃
  -- absorption of the half-balls
  have habsW : ∀ H : Set Plane, IsPreconnected H → Disjoint H Θ → (H ∩ W).Nonempty → H ⊆ W := by
    rintro H hH hHΘ ⟨x, hxH, hxW⟩
    rw [hWdef, connectedComponentIn_eq (F := Θᶜ) (x := w) hxW]
    exact hH.subset_connectedComponentIn hxH fun z hz hzΘ => hHΘ.ne_of_mem hz hzΘ rfl
  have habsI : ∀ {J I O : Set Plane}, CurveSides J I O → J ⊆ Θ → ∀ H : Set Plane,
      IsPreconnected H → Disjoint H Θ → (H ∩ I).Nonempty → H ⊆ I :=
    fun h hJ H hH hHΘ hne => h.subset_far hH (hHΘ.mono_right hJ) hne
  -- the closure of `W` misses the non-lattice points of `Θ`
  have hcl : closure W ∩ (range latticePoint)ᶜ ⊆ W := by
    rintro v ⟨hvW, hvl⟩
    by_cases hvΘ : v ∈ Θ
    · exfalso
      obtain ⟨δ, hδ, H₁, H₂, hH₁, hH₂, hn₁, hn₂, hd₁, hd₂, hball⟩ := hloc v hvΘ hvl
      have hpick : ∀ X : Set Plane, v ∈ closure X → Disjoint X Θ →
          (∀ H : Set Plane, IsPreconnected H → Disjoint H Θ → (H ∩ X).Nonempty → H ⊆ X) →
          H₁ ⊆ X ∨ H₂ ⊆ X := by
        intro X hvX hXΘ habs
        obtain ⟨x, hxX, hxb⟩ := Metric.mem_closure_iff.1 hvX δ hδ
        have hxb' : x ∈ Metric.ball v δ := by rw [Metric.mem_ball, dist_comm]; exact hxb
        rcases hball hxb' with (hx₁ | hx₂) | hxΘ
        · exact Or.inl (habs H₁ hH₁ hd₁ ⟨x, hx₁, hxX⟩)
        · exact Or.inr (habs H₂ hH₂ hd₂ ⟨x, hx₂, hxX⟩)
        · exact absurd hxΘ (hXΘ.ne_of_mem hxX · rfl)
      have hW := hpick W hvW hWΘ habsW
      rcases hvΘ with (hv₁ | hv₂) | hv₃
      · exact false_of_three_disjoint hW₂ hW₃ hP₂₃ hn₁ hn₂ hW
          (hpick P₂ (h₂.subset_closure (Or.inl hv₁)) hP₂ (habsI h₂ hJ₂))
          (hpick P₃ (h₃.subset_closure (Or.inl hv₁)) hP₃ (habsI h₃ hJ₃))
      · exact false_of_three_disjoint hW₁ hW₃ hP₁₃ hn₁ hn₂ hW
          (hpick P₁ (h₁.subset_closure (Or.inl hv₂)) hP₁ (habsI h₁ hJ₁))
          (hpick P₃ (h₃.subset_closure (Or.inr hv₂)) hP₃ (habsI h₃ hJ₃))
      · exact false_of_three_disjoint hW₁ hW₂ hP₁₂ hn₁ hn₂ hW
          (hpick P₁ (h₁.subset_closure (Or.inr hv₃)) hP₁ (habsI h₁ hJ₁))
          (hpick P₂ (h₂.subset_closure (Or.inr hv₃)) hP₂ (habsI h₂ hJ₂))
    · obtain ⟨x, hxV, hxW⟩ := mem_closure_iff.1 hvW _
        (hΘ.isOpen_compl.connectedComponentIn (x := v)) (mem_connectedComponentIn hvΘ)
      rw [hWdef, connectedComponentIn_eq (F := Θᶜ) (x := w) hxW, ← connectedComponentIn_eq hxV]
      exact mem_connectedComponentIn hvΘ
  -- hence `W` contains every non-lattice point
  have hS := isConnected_compl_range_latticePoint.isPreconnected
  have hSW : ((range latticePoint)ᶜ ∩ W).Nonempty := by
    rw [inter_comm]
    exact dense_compl_range_latticePoint.inter_open_nonempty W hWo ⟨w, hwW⟩
  have hsub := hS.subset_of_closure_inter_subset hWo hSW hcl
  obtain ⟨y, hyΘ, hyl⟩ := hy
  exact hWΘ.ne_of_mem (hsub hyl) hyΘ rfl

/-! ### No `K_{3,3}` minor -/

/-- The values of the arc `x, f, y` with `f` in `S`. -/
theorem chainBracket_mem {x y : C} {f : ℤ → C} {ℓ : ℕ} {S : Set C} (hf : ∀ k, f k ∈ S) (k : ℤ) :
    chainBracket x f ℓ y k = x ∨ chainBracket x f ℓ y k = y ∨ chainBracket x f ℓ y k ∈ S := by
  unfold chainBracket
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (hf _))
  · exact Or.inr (Or.inl rfl)

/-- L2711-2715: three disjoint connected sets of `𝒞_∞`, each adjacent to three distinct points
outside them, would be a `K_{3,3}` minor of the planar lattice. -/
theorem noK33MinorStep : NoK33MinorStep := by
  intro hJ ω C X z hXc hXd hz hzX hadj
  -- the arcs `z 0, X j ⋯, z 1`
  have hf : ∀ j, ∃ (f : ℤ → C) (ℓ : ℕ), (componentGraph C).Adj (z 0) (f 0) ∧
      (componentGraph C).Adj (f ℓ) (z 1) ∧ IsSimpleChain (componentGraph C) f ℓ ∧
      ∀ k, f k ∈ X j := by
    intro j
    obtain ⟨a, haX, ha⟩ := hadj 0 j
    obtain ⟨b, hbX, hb⟩ := hadj 1 j
    obtain ⟨f, ℓ, hf0, hfℓ, hfs, hfX⟩ := exists_isSimpleChain_of_joinedIn (hXc j a haX b hbX)
    exact ⟨f, ℓ, hf0 ▸ ha, hfℓ ▸ hb.symm, hfs, hfX⟩
  choose f ℓ hfa0 hfa1 hfs hfX using hf
  have hz01 : z 0 ≠ z 1 := hz.ne (by decide)
  obtain ⟨A, hAdef⟩ : ∃ A : Fin 3 → ℤ → C, A = fun j => chainBracket (z 0) (f j) (ℓ j) (z 1) :=
    ⟨_, rfl⟩
  have hAs : ∀ j, IsSimpleChain (componentGraph C) (A j) (ℓ j + 2) := fun j => by
    subst hAdef
    exact (hfs j).bracket (hfa0 j) (hfa1 j) hz01 (fun k _ _ e => hzX 0 j (e ▸ hfX j k))
      (fun k _ _ e => hzX 1 j (e ▸ hfX j k))
  have hA0 : ∀ j, A j 0 = z 0 := fun j => by subst hAdef; exact chainBracket_zero _ _ _ _
  have hAL : ∀ j, A j ((ℓ j + 2 : ℕ) : ℤ) = z 1 := fun j => by
    subst hAdef; exact chainBracket_last _ _ _ _
  have hAv : ∀ j k, A j k = z 0 ∨ A j k = z 1 ∨ A j k ∈ X j := fun j k => by
    subst hAdef; exact chainBracket_mem (hfX j) k
  have hA1 : ∀ j, A j 1 = f j 0 := fun j => by
    subst hAdef
    exact (chainBracket_mid _ _ _ _ one_pos (by omega)).trans (by rw [sub_self])
  -- points of `X i` are off the arcs through the other `X j`
  have hXA : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ k, x ≠ A j k := by
    intro i j hij x hx k e
    rcases hAv j k with h | h | h
    · exact hzX 0 i (h ▸ e ▸ hx)
    · exact hzX 1 i (h ▸ e ▸ hx)
    · exact (hXd i j hij).ne_of_mem hx (e ▸ h) rfl
  have hA2 : ∀ j k, A j k ≠ z 2 := fun j k e => by
    rcases hAv j k with h | h | h
    · exact hz.ne (show (0 : Fin 3) ≠ 2 by decide) (h.symm.trans e)
    · exact hz.ne (show (1 : Fin 3) ≠ 2 by decide) (h.symm.trans e)
    · exact hzX 2 j (e ▸ h)
  -- the theta condition
  have hth : ∀ j j', j ≠ j' → ∀ k k' : ℤ, 0 ≤ k → k ≤ ((ℓ j + 2 : ℕ) : ℤ) → 0 ≤ k' →
      k' ≤ ((ℓ j' + 2 : ℕ) : ℤ) → A j k = A j' k' →
      (k = 0 ∧ k' = 0) ∨ (k = ((ℓ j + 2 : ℕ) : ℤ) ∧ k' = ((ℓ j' + 2 : ℕ) : ℤ)) := by
    intro j j' hjj'
    have := theta_of_bracket (x := z 0) (y := z 1) (f := f j) (ℓ := ℓ j) (hAs j') (hA0 j')
      (hAL j') fun i k' _ _ _ _ => hXA j j' hjj' _ (hfX j i) k'
    subst hAdef
    exact this
  set w : Plane := latticePoint (z 2).val with hw
  have hwK : ∀ j, w ∉ arcTrace (A j) (ℓ j + 2) := fun j =>
    latticePoint_not_mem_arcTrace (hAs j) fun k' _ _ e => hA2 j k' e.symm
  have hAin : ∀ i, latticePoint (f i 0).val ∈ arcInterior (A i) (ℓ i + 2) := fun i => by
    have := latticePoint_mem_arcInterior (A i) (L := ℓ i + 2) (k := 1) one_pos (by push_cast; omega)
    rwa [hA1] at this
  -- the interior of each arc is on the side of `w` of the curve formed by the two others
  have hnear : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∃ P Q,
      CurveSides (arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2)) P Q ∧ w ∈ Q ∧
      arcInterior (A i) (ℓ i + 2) ⊆ Q := by
    intro i j k hij hik hjk
    obtain ⟨P, Q, hPQ, hQP⟩ := exists_curveSides_of_arcs hJ (hAs j) (hAs k)
      ((hA0 j).trans (hA0 k).symm) ((hAL j).trans (hAL k).symm) (by omega) (hth j k hjk)
    have hwJ : w ∉ arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2) := fun h =>
      h.elim (hwK j) (hwK k)
    obtain ⟨P', Q', h', hwQ'⟩ : ∃ P' Q', CurveSides
        (arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2)) P' Q' ∧ w ∈ Q' := by
      have : w ∈ P ∪ Q := hPQ.union_eq ▸ hwJ
      rcases this with h | h
      · exact ⟨Q, P, hQP, h⟩
      · exact ⟨P, Q, hPQ, h⟩
    refine ⟨P', Q', h', hwQ', ?_⟩
    -- the link from `z 2` to `f i 0` through `X i`
    obtain ⟨y, hyX, hy⟩ := hadj 2 i
    have hlink : JoinedIn C (insert (z 2) (X i)) (z 2) (f i 0) := by
      obtain ⟨hy', hf', hr⟩ := hXc i y hyX (f i 0) (hfX i 0)
      refine ⟨mem_insert _ _, mem_insert_of_mem _ hf', ?_⟩
      have hr' := hr.map (SimpleGraph.induceHomOfLE (componentGraph C)
        (subset_insert (z 2) (X i))).toHom
      have hadj' : ((componentGraph C).induce (insert (z 2) (X i))).Adj ⟨z 2, mem_insert _ _⟩
          ⟨y, mem_insert_of_mem _ hyX⟩ := by simpa using hy
      exact hadj'.reachable.trans hr'
    obtain ⟨g, m, hg0, hgm, hgs, hgX⟩ := exists_isSimpleChain_of_joinedIn hlink
    have hgK : ∀ j', j' ≠ i → Disjoint (arcTrace g m) (arcTrace (A j') (ℓ j' + 2)) :=
      fun j' hj' => disjoint_arcTrace hgs (hAs j') fun k k' _ _ _ _ e => by
        rcases hgX k with h | h
        · exact hA2 j' k' (e.symm.trans h)
        · exact hXA i j' (Ne.symm hj') _ h k' e
    have hfK : ∀ j', j' ≠ i → latticePoint (f i 0).val ∉ arcTrace (A j') (ℓ j' + 2) :=
      fun j' hj' => latticePoint_not_mem_arcTrace (hAs j') fun k' _ _ =>
        hXA i j' (Ne.symm hj') _ (hfX i 0) k'
    set D := polyline (latticePoint ∘ (Subtype.val ∘ g)) '' Icc 0 (m : ℝ) with hDdef
    have hDsub : D ⊆ arcTrace g m ∪ {latticePoint (f i 0).val} := by
      have := polyline_image_Icc_subset (Subtype.val ∘ g) m
      rwa [Function.comp_apply, hgm] at this
    have hDJ : Disjoint D (arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2)) :=
      Set.disjoint_of_subset_left hDsub (Set.disjoint_union_left.2
        ⟨Set.disjoint_union_right.2 ⟨hgK j (Ne.symm hij), hgK k (Ne.symm hik)⟩,
          Set.disjoint_singleton_left.2 fun h => h.elim (hfK j (Ne.symm hij))
            (hfK k (Ne.symm hik))⟩)
    have hDc : IsPreconnected D :=
      isPreconnected_Icc.image _ (continuous_polyline _).continuousOn
    have hwD : w ∈ D := by
      refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
      have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) 0
      push_cast at this
      rw [this]
      simp [hg0, hw]
    have hfD : latticePoint (f i 0).val ∈ D := by
      refine ⟨m, ⟨by positivity, le_rfl⟩, ?_⟩
      have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) m
      push_cast at this
      rw [this]
      simp [hgm]
    have hDQ := h'.subset_near hDc hDJ ⟨w, hwD, hwQ'⟩
    have hAJ : Disjoint (arcInterior (A i) (ℓ i + 2))
        (arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2)) :=
      disjoint_arcInterior (hAs i) (by
        rw [Set.inter_union_distrib_left]
        exact union_subset (arcTrace_inter_subset (hAs i) (hAs j) (by omega) (hth i j hij))
          (arcTrace_inter_subset (hAs i) (hAs k) (by omega) (hth i k hik)))
    exact h'.subset_near (isPreconnected_arcInterior _ _) hAJ ⟨_, hAin i, hDQ hfD⟩
  have hKsub : ∀ i j k : Fin 3, arcTrace (A i) (ℓ i + 2) ⊆
      arcInterior (A i) (ℓ i + 2) ∪ (arcTrace (A j) (ℓ j + 2) ∪ arcTrace (A k) (ℓ k + 2)) := by
    intro i j k v hv
    rcases arcTrace_subset (A i) (by omega) hv with h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rcases h with rfl | rfl
      · rw [hA0 i, ← hA0 j]
        exact (endpoints_mem_arcTrace (A j) (by omega)).1
      · rw [hAL i, ← hAL j]
        exact (endpoints_mem_arcTrace (A j) (by omega)).2
  obtain ⟨P₁, Q₁, h₁, hw₁, hA₁⟩ := hnear 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨P₂, Q₂, h₂, hw₂, hA₂⟩ := hnear 1 0 2 (by decide) (by decide) (by decide)
  obtain ⟨P₃, Q₃, h₃, hw₃, hA₃⟩ := hnear 2 0 1 (by decide) (by decide) (by decide)
  -- a point of the theta graph off the lattice: the middle of the first edge of `A 0`
  have hfl : ⌊(1 / 2 : ℝ)⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
  have hxA : polyline (latticePoint ∘ (Subtype.val ∘ A 0)) (1 / 2) ∈ arcInterior (A 0) (ℓ 0 + 2) :=
    ⟨1 / 2, ⟨by norm_num, by push_cast; linarith [(Nat.cast_nonneg (ℓ 0) : (0 : ℝ) ≤ ℓ 0)]⟩, rfl⟩
  have hxl : polyline (latticePoint ∘ (Subtype.val ∘ A 0)) (1 / 2) ∉ range latticePoint := by
    rintro ⟨z', hz'⟩
    have hadj' := (hAs 0).adj_val ⌊(1 / 2 : ℝ)⌋ (by rw [hfl]; exact ⟨le_rfl, by push_cast; omega⟩)
    obtain ⟨-, hfr⟩ := polyline_eq_latticePoint hadj' hz'.symm
    rw [Int.fract, hfl] at hfr
    norm_num at hfr
  have hΘs : arcTrace (A 0) (ℓ 0 + 2) ∪ arcTrace (A 1) (ℓ 1 + 2) ∪ arcTrace (A 2) (ℓ 2 + 2) ⊆
      latticeSkeleton :=
    union_subset (union_subset (chainTrace_subset_latticeSkeleton (hAs 0).adj_val)
      (chainTrace_subset_latticeSkeleton (hAs 1).adj_val))
      (chainTrace_subset_latticeSkeleton (hAs 2).adj_val)
  have hΘc : IsClosed
      (arcTrace (A 0) (ℓ 0 + 2) ∪ arcTrace (A 1) (ℓ 1 + 2) ∪ arcTrace (A 2) (ℓ 2 + 2)) :=
    ((isClosed_chainTrace _ (finite_Ico _ _)).union (isClosed_chainTrace _ (finite_Ico _ _))).union
      (isClosed_chainTrace _ (finite_Ico _ _))
  refine false_of_theta_sides hΘc ?_ h₁ h₂ h₃ (hKsub 0 1 2) hA₁ (arcInterior_subset _ _)
    (hKsub 1 0 2) hA₂ ⟨_, hAin 1⟩ (arcInterior_subset _ _) (hKsub 2 0 1) hA₃ ⟨_, hAin 2⟩
    (by rintro ((h | h) | h) <;> [exact hwK 0 h; exact hwK 1 h; exact hwK 2 h]) hw₁ hw₂ hw₃
    ⟨_, Or.inl (Or.inl (arcInterior_subset _ _ hxA)), hxl⟩
  rintro v ((hv | hv) | hv) hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 0) (subset_union_left.trans subset_union_left) hv
      hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 1) (subset_union_right.trans subset_union_left) hv
      hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 2) subset_union_right hv hvl

end Rigidity.Proofs.Section5
