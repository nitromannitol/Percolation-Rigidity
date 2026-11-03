import Rigidity.Proofs.Section5.Separation.Lattice
import Rigidity.External.JordanCurve
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Lemma 5.19: Jordan curves of lattice paths on `S²`

The plane is seen in `S²` through the inverse stereographic projection
`toSphere : ℝ² → S² \ {∞}` (`onePointEquivSphereOfFinrankEq`). The Jordan curve theorem on `S²`
(`External.JordanCurveTheoremSphere`) is applied to two kinds of simple closed curves:

* a lattice cycle (`exists_path_cycle`): the trace of the cycle has an inside `I` and an outside
  `O` in the plane (`JordanSides`), the outside containing every preconnected set which
  accumulates at `∞` in `S²` (`exists_jordanSides`);
* a bi-infinite lattice path closed up by `∞` (`exists_path_line`): every point of the path lies
  in the closure of each complementary component, which accumulates at `∞`
  (`closure_connectedComponentIn_of_sphere`).
-/

open Set Filter Topology Function LatticeProb.Percolation Rigidity.External
open scoped Real

namespace Rigidity.Proofs.Section5

/-- The homeomorphism of the one-point compactification of the plane onto `S²`. -/
noncomputable def planeSphereEquiv : OnePoint Plane ≃ₜ S2 :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- The plane in `S²` (inverse stereographic projection). -/
noncomputable def toSphere (v : Plane) : S2 := planeSphereEquiv v

/-- The point at infinity of `S²`. -/
noncomputable def sphereInfty : S2 := planeSphereEquiv OnePoint.infty

theorem isOpenEmbedding_toSphere : IsOpenEmbedding toSphere :=
  planeSphereEquiv.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

theorem continuous_toSphere : Continuous toSphere := isOpenEmbedding_toSphere.continuous

theorem toSphere_injective : Injective toSphere := isOpenEmbedding_toSphere.injective

theorem toSphere_ne_infty (v : Plane) : toSphere v ≠ sphereInfty := fun h =>
  OnePoint.coe_ne_infty v (planeSphereEquiv.injective h)

theorem range_toSphere : range toSphere = {sphereInfty}ᶜ := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact toSphere_ne_infty v
  · intro hw
    obtain ⟨x, rfl⟩ := planeSphereEquiv.surjective w
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hw
    | coe v => exact ⟨v, rfl⟩

theorem tendsto_toSphere_cobounded :
    Tendsto toSphere (Bornology.cobounded Plane) (𝓝 sphereInfty) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
  exact (planeSphereEquiv.continuous.tendsto _).comp OnePoint.tendsto_coe_infty

/-- An unbounded set of the plane accumulates at `∞` in `S²`. -/
theorem infty_mem_closure_image {S : Set Plane} (hS : ¬ Bornology.IsBounded S) :
    sphereInfty ∈ closure (toSphere '' S) := by
  by_contra h
  have himg : toSphere '' S = planeSphereEquiv '' (((↑) : Plane → OnePoint Plane) '' S) := by
    rw [image_image]; rfl
  rw [himg, ← planeSphereEquiv.image_closure] at h
  have h' : (OnePoint.infty : OnePoint Plane) ∉ closure (((↑) : Plane → OnePoint Plane) '' S) :=
    fun hm => h ⟨_, hm, rfl⟩
  set F := closure (((↑) : Plane → OnePoint Plane) '' S)
  have hF : ((↑) : Plane → OnePoint Plane) '' ((↑) ⁻¹' F) = F := by
    refine image_preimage_eq_of_subset ?_
    rw [← OnePoint.compl_infty]
    intro x hx hx'
    rw [mem_singleton_iff] at hx'
    rw [hx'] at hx
    exact h' hx
  have hc : IsCompact (((↑) : Plane → OnePoint Plane) ⁻¹' F) := by
    have hcl : IsClosed F := isClosed_closure
    rw [← hF] at hcl
    exact (OnePoint.isClosed_image_coe.1 hcl).2
  exact hS (hc.isBounded.subset fun x hx => subset_closure (mem_image_of_mem _ hx))

/-! ### The two sides of a Jordan curve in the plane -/

/-- `I` and `O` are the two sides of the closed set `J` of the plane given by the Jordan curve
theorem: open, disjoint and covering `ℝ² \ J`, the inside `I` preconnected with `J` in its
closure, and the outside `O` containing every preconnected subset of `ℝ² \ J` which accumulates
at `∞` in `S²`. -/
structure JordanSides (J I O : Set Plane) : Prop where
  isOpen_inside : IsOpen I
  isOpen_outside : IsOpen O
  isPreconnected_inside : IsPreconnected I
  disjoint : Disjoint I O
  union_eq : I ∪ O = Jᶜ
  subset_closure : J ⊆ closure I
  subset_outside : ∀ S ⊆ Jᶜ, IsPreconnected S → sphereInfty ∈ closure (toSphere '' S) → S ⊆ O

theorem jordanSides_of_sphere {K : Set Plane} {U V : Set S2} (hU : IsOpen U) (hV : IsOpen V)
    (hVc : IsPreconnected V) (hUV : Disjoint U V) (hunion : U ∪ V = (toSphere '' K)ᶜ)
    (hfV : frontier V = toSphere '' K) (hN : sphereInfty ∈ U) :
    JordanSides K (toSphere ⁻¹' V) (toSphere ⁻¹' U) := by
  have hVr : V ⊆ range toSphere := by
    rw [range_toSphere]
    intro w hw hw'
    rw [mem_singleton_iff] at hw'
    subst hw'
    exact hUV.ne_of_mem hN hw rfl
  have hcl : closure (toSphere ⁻¹' V) = toSphere ⁻¹' closure V := by
    rw [isOpenEmbedding_toSphere.isInducing.closure_eq_preimage_closure_image,
      image_preimage_eq_of_subset hVr]
  refine ⟨hV.preimage continuous_toSphere, hU.preimage continuous_toSphere, ?_,
    hUV.symm.preimage _, ?_, ?_, ?_⟩
  · rw [← isOpenEmbedding_toSphere.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset hVr]
    exact hVc
  · rw [← preimage_union, union_comm, hunion, preimage_compl,
      preimage_image_eq _ toSphere_injective]
  · intro x hx
    rw [hcl]
    exact frontier_subset_closure (hfV ▸ mem_image_of_mem _ hx)
  · intro S hS hSc hSN
    have hsub : toSphere '' S ⊆ U ∪ V := by
      rw [hunion]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      exact hS hx (toSphere_injective hxy ▸ hy)
    rcases (hSc.image _ continuous_toSphere.continuousOn).subset_or_subset hU hV hUV hsub with
      h | h
    · exact fun x hx => h (mem_image_of_mem _ hx)
    · exact absurd (closure_mono h hSN) ((hUV.closure_right hU).ne_of_mem hN · rfl)

/-- The Jordan curve theorem on `S²` for a simple closed curve of the plane. -/
theorem exists_jordanSides (hJ : JordanCurveTheoremSphere) {K : Set Plane} {q : S2}
    (β : Path q q) (hβ : InjOn β (Ico 0 1)) (hr : range β = toSphere '' K) :
    ∃ I O, JordanSides K I O := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hunion, hfU, hfV⟩ := hJ q β hβ
  rw [hr] at hunion hfU hfV
  have hN : sphereInfty ∈ U ∪ V := by
    rw [hunion]
    rintro ⟨x, -, hx⟩
    exact toSphere_ne_infty x hx
  rcases hN with hN | hN
  · exact ⟨_, _, jordanSides_of_sphere hU hV hVc.isPreconnected hUV hunion hfV hN⟩
  · exact ⟨_, _, jordanSides_of_sphere hV hU hUc.isPreconnected hUV.symm
      (by rw [union_comm]; exact hunion) hfU hN⟩

/-- The Jordan curve theorem on `S²` for a curve of the plane closed up by `∞`: each point of the
curve lies in the closure of each complementary component, which accumulates at `∞`. -/
theorem closure_connectedComponentIn_of_sphere (hJ : JordanCurveTheoremSphere) {T : Set Plane}
    {q : S2} (β : Path q q) (hβ : InjOn β (Ico 0 1))
    (hr : range β = insert sphereInfty (toSphere '' T)) {z : Plane} (hz : z ∉ T) :
    T ⊆ closure (connectedComponentIn Tᶜ z) ∧
      sphereInfty ∈ closure (toSphere '' connectedComponentIn Tᶜ z) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hunion, hfU, hfV⟩ := hJ q β hβ
  rw [hr] at hunion hfU hfV
  have key : ∀ U : Set S2, IsPreconnected U → U ⊆ (insert sphereInfty (toSphere '' T))ᶜ →
      toSphere z ∈ U → frontier U = insert sphereInfty (toSphere '' T) →
      T ⊆ closure (connectedComponentIn Tᶜ z) ∧
        sphereInfty ∈ closure (toSphere '' connectedComponentIn Tᶜ z) := by
    intro U hUc hUs hzU hfr
    have hUr : U ⊆ range toSphere := by
      rw [range_toSphere]
      intro w hw hw'
      exact hUs hw (Or.inl hw')
    have hD' : IsPreconnected (toSphere ⁻¹' U) := by
      rw [← isOpenEmbedding_toSphere.isInducing.isPreconnected_image,
        image_preimage_eq_of_subset hUr]
      exact hUc
    have hD'T : toSphere ⁻¹' U ⊆ Tᶜ := fun x hx hxT => hUs hx (Or.inr ⟨x, hxT, rfl⟩)
    have hsub := hD'.subset_connectedComponentIn (show z ∈ toSphere ⁻¹' U from hzU) hD'T
    have hcl : closure (toSphere ⁻¹' U) = toSphere ⁻¹' closure U := by
      rw [isOpenEmbedding_toSphere.isInducing.closure_eq_preimage_closure_image,
        image_preimage_eq_of_subset hUr]
    refine ⟨fun x hx => closure_mono hsub ?_, ?_⟩
    · rw [hcl]
      exact frontier_subset_closure (hfr ▸ Or.inr ⟨x, hx, rfl⟩)
    · refine closure_mono (image_mono hsub) ?_
      rw [image_preimage_eq_of_subset hUr]
      exact frontier_subset_closure (hfr ▸ Or.inl rfl)
  have hz' : toSphere z ∈ U ∪ V := by
    rw [hunion]
    rintro (h | ⟨x, hx, hxz⟩)
    · exact toSphere_ne_infty z h
    · exact hz (toSphere_injective hxz ▸ hx)
  rcases hz' with h | h
  · exact key U hUc.isPreconnected (hunion ▸ subset_union_left) h hfU
  · exact key V hVc.isPreconnected (hunion ▸ subset_union_right) h hfV

/-! ### Lattice cycles -/

/-- A lattice cycle of length `m ≥ 3` without repeated vertices is a simple closed curve. -/
theorem exists_path_cycle {c : ℤ → Vertex 2} {m : ℕ} (hm : 3 ≤ m) (hcm : c m = c 0)
    (hadj : ∀ n : ℤ, 0 ≤ n → n < m → (nearestNeighborGraph 2).Adj (c n) (c (n + 1)))
    (hinj : ∀ n n' : ℤ, 0 ≤ n → n < m → 0 ≤ n' → n' < m → c n = c n' → n = n') :
    ∃ (q : S2) (β : Path q q), InjOn β (Ico 0 1) ∧
      range β = toSphere '' chainTrace c (Ico 0 m) := by
  set f : ℝ → Plane := fun t => polyline (latticePoint ∘ c) (m * t) with hf
  have hfc : Continuous f := (continuous_polyline _).comp (continuous_const.mul continuous_id)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hf0 : f 0 = latticePoint (c 0) := by
    simp only [hf, mul_zero]
    exact_mod_cast polyline_intCast (latticePoint ∘ c) 0
  have hf1 : f 1 = latticePoint (c 0) := by
    simp only [hf, mul_one]
    rw [show ((m : ℕ) : ℝ) = ((m : ℤ) : ℝ) by norm_cast, polyline_intCast]
    simp [hcm]
  let β : Path (toSphere (latticePoint (c 0))) (toSphere (latticePoint (c 0))) :=
    { toFun := fun t => toSphere (f t)
      continuous_toFun := continuous_toSphere.comp (hfc.comp continuous_subtype_val)
      source' := by simp only [Set.Icc.coe_zero, hf0]
      target' := by simp only [Set.Icc.coe_one, hf1] }
  have hcyc : ∀ n n' : ℤ, 0 ≤ n → n < m → 0 ≤ n' → n' < m → c n = c (n' + 1) →
      n = n' + 1 ∨ (n' + 1 = m ∧ n = 0) := by
    intro n n' h0 h1 h0' h1' h
    by_cases hlt : n' + 1 < m
    · exact Or.inl (hinj _ _ h0 h1 (by omega) hlt h)
    · have he : n' + 1 = m := by omega
      rw [he, hcm] at h
      exact Or.inr ⟨he, hinj _ _ h0 h1 le_rfl (by omega) h⟩
  have hfl : ∀ s ∈ Ico (0 : ℝ) m, 0 ≤ ⌊s⌋ ∧ ⌊s⌋ < m := fun s hs =>
    ⟨Int.floor_nonneg.2 hs.1, Int.floor_lt.2 (by exact_mod_cast hs.2)⟩
  have hinjf : InjOn (polyline (latticePoint ∘ c)) (Ico 0 (m : ℝ)) := by
    apply polyline_injOn
    · intro s hs
      exact hadj _ (hfl s hs).1 (hfl s hs).2
    · intro s hs s' hs' h
      exact hinj _ _ (hfl s hs).1 (hfl s hs).2 (hfl s' hs').1 (hfl s' hs').2 h
    · intro s hs s' hs' hne h1 h2
      have e1 := hcyc _ _ (hfl s hs).1 (hfl s hs).2 (hfl s' hs').1 (hfl s' hs').2 h1
      have e2 := hcyc _ _ (hfl s' hs').1 (hfl s' hs').2 (hfl s hs).1 (hfl s hs).2 h2.symm
      have := (hfl s hs).2
      have := (hfl s' hs').2
      omega
  refine ⟨_, β, ?_, ?_⟩
  · intro t ht t' ht' h
    have h' : f t = f t' := toSphere_injective h
    have hmt : ∀ t : unitInterval, t ∈ Ico 0 1 → (m : ℝ) * t ∈ Ico 0 (m : ℝ) := by
      intro t ht
      have h1 : (t : ℝ) < 1 := ht.2
      exact ⟨mul_nonneg hm0.le t.2.1, by nlinarith⟩
    have := hinjf (hmt t ht) (hmt t' ht') h'
    exact Subtype.ext (mul_left_cancel₀ hm0.ne' this)
  · have himg := polyline_image_Icc c (a := 0) (b := m) (by omega)
    push_cast at himg
    have hrange : range (fun t : unitInterval => f t) =
        polyline (latticePoint ∘ c) '' Icc 0 (m : ℝ) := by
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨m * t, ⟨mul_nonneg hm0.le t.2.1, by nlinarith [t.2.2]⟩, rfl⟩
      · rintro ⟨s, ⟨h0, h1⟩, rfl⟩
        refine ⟨⟨s / m, div_nonneg h0 hm0.le, (div_le_one hm0).2 h1⟩, ?_⟩
        simp only [hf]
        congr 1
        field_simp
    rw [← himg, ← hrange, ← range_comp]
    rfl

/-! ### Bi-infinite lattice paths closed up by `∞` -/

/-- A homeomorphism of `(0, 1)` onto `ℝ`. -/
noncomputable def unitTan (t : ℝ) : ℝ := Real.tan (π * t - π / 2)

theorem unitTan_arg_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    π * t - π / 2 ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

theorem injOn_unitTan : InjOn unitTan (Ioo 0 1) := by
  intro t ht t' ht' h
  have := Real.injOn_tan (unitTan_arg_mem ht.1 ht.2) (unitTan_arg_mem ht'.1 ht'.2) h
  have hpi := Real.pi_pos
  nlinarith

theorem exists_unitTan_eq (s : ℝ) : ∃ t ∈ Ioo (0 : ℝ) 1, unitTan t = s := by
  have hpi := Real.pi_pos
  have h1 := Real.arctan_lt_pi_div_two s
  have h2 := Real.neg_pi_div_two_lt_arctan s
  refine ⟨(Real.arctan s + π / 2) / π, ⟨div_pos (by linarith) hpi, ?_⟩, ?_⟩
  · rw [div_lt_one hpi]; linarith
  · rw [unitTan, mul_div_cancel₀ _ hpi.ne', add_sub_cancel_right, Real.tan_arctan]

theorem continuousAt_unitTan {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : ContinuousAt unitTan t := by
  have h := unitTan_arg_mem h0 h1
  have hc : Continuous (fun t : ℝ => π * t - π / 2) := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => π * t - π / 2)
    (Real.continuousOn_tan_Ioo.continuousAt (Ioo_mem_nhds h.1 h.2)) hc.continuousAt

theorem tendsto_unitTan_zero : Tendsto unitTan (𝓝[>] 0) atBot := by
  refine Real.tendsto_tan_neg_pi_div_two.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have hc : Continuous (fun t : ℝ => π * t - π / 2) := by fun_prop
    have : Tendsto (fun t : ℝ => π * t - π / 2) (𝓝 0) (𝓝 (-(π / 2))) :=
      hc.tendsto' 0 _ (by show π * 0 - π / 2 = -(π / 2); ring)
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    show -(π / 2) < π * t - π / 2
    nlinarith [Real.pi_pos]

theorem tendsto_unitTan_one : Tendsto unitTan (𝓝[<] 1) atTop := by
  refine Real.tendsto_tan_pi_div_two.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have hc : Continuous (fun t : ℝ => π * t - π / 2) := by fun_prop
    have : Tendsto (fun t : ℝ => π * t - π / 2) (𝓝 1) (𝓝 (π / 2)) :=
      hc.tendsto' 1 _ (by show π * 1 - π / 2 = π / 2; ring)
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 1)
    show π * t - π / 2 < π / 2
    nlinarith [Real.pi_pos]

theorem norm_sub_latticePoint_le_one {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y) :
    ‖latticePoint y - latticePoint x‖ ≤ 1 := by
  have key : ∀ (a : Vertex 2) (i : Fin 2),
      latticePoint (a + LatticeProb.unit i) - latticePoint a = EuclideanSpace.single i 1 := by
    intro a i
    ext k
    simp only [PiLp.sub_apply, latticePoint_apply, Pi.add_apply, unit_apply, PiLp.single_apply]
    split_ifs <;> push_cast <;> ring
  obtain ⟨i, rfl | rfl⟩ := h
  · rw [key, PiLp.norm_single, norm_one]
  · rw [← norm_neg, neg_sub, key, PiLp.norm_single, norm_one]

theorem tendsto_norm_latticePoint {g : ℤ → Vertex 2} (hg : Injective g) :
    Tendsto (fun n => ‖latticePoint (g n)‖) (atBot ⊔ atTop) atTop := by
  refine Tendsto.mono_left ?_ (sup_le atBot_le_cofinite atTop_le_cofinite)
  refine tendsto_atTop.2 fun r => ?_
  have hfin : (g ⁻¹' {x | ‖latticePoint x‖ < r}).Finite := by
    refine Set.Finite.preimage hg.injOn ((finite_latticeEuclideanBall (0 : Vertex 2) r).subset ?_)
    intro x hx
    have h0 : latticePoint (0 : Vertex 2) = 0 := by ext k; simp [latticePoint_apply]
    simpa [h0] using hx
  filter_upwards [hfin.compl_mem_cofinite] with n hn
  simpa using hn

theorem tendsto_polyline_cobounded {g : ℤ → Vertex 2} (hg : Injective g)
    (hadj : ∀ n, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) :
    Tendsto (polyline (latticePoint ∘ g)) (atBot ⊔ atTop) (Bornology.cobounded Plane) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hfl : Tendsto (fun s : ℝ => ⌊s⌋) (atBot ⊔ atTop) (atBot ⊔ atTop) :=
    tendsto_sup.2 ⟨tendsto_floor_atBot.mono_right le_sup_left,
      tendsto_floor_atTop.mono_right le_sup_right⟩
  have h1 := tendsto_atTop_add_const_right _ (-1) ((tendsto_norm_latticePoint hg).comp hfl)
  refine tendsto_atTop_mono (fun s => ?_) h1
  show ‖latticePoint (g ⌊s⌋)‖ + -1 ≤ ‖polyline (latticePoint ∘ g) s‖
  simp only [polyline, Function.comp, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  set A := latticePoint (g ⌊s⌋)
  set d := latticePoint (g (⌊s⌋ + 1)) - A
  have hf : ‖Int.fract s • d‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg s)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one s).le).trans
      (norm_sub_latticePoint_le_one (hadj ⌊s⌋))
  have := norm_sub_le (Int.fract s • d + A) (Int.fract s • d)
  rw [add_sub_cancel_left] at this
  linarith

/-- A bi-infinite lattice path without repeated vertices, closed up by `∞`, is a simple closed
curve of `S²`. -/
theorem exists_path_line {g : ℤ → Vertex 2} (hg : Injective g)
    (hadj : ∀ n, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) :
    ∃ β : Path sphereInfty sphereInfty, InjOn β (Ico 0 1) ∧
      range β = insert sphereInfty (toSphere '' chainTrace g univ) := by
  classical
  set F : ℝ → S2 := fun t => toSphere (polyline (latticePoint ∘ g) (unitTan t)) with hF
  have hF0 : Tendsto F (𝓝[>] 0) (𝓝 sphereInfty) :=
    tendsto_toSphere_cobounded.comp ((tendsto_polyline_cobounded hg hadj).comp
      (tendsto_unitTan_zero.mono_right le_sup_left))
  have hF1 : Tendsto F (𝓝[<] 1) (𝓝 sphereInfty) :=
    tendsto_toSphere_cobounded.comp ((tendsto_polyline_cobounded hg hadj).comp
      (tendsto_unitTan_one.mono_right le_sup_right))
  set b : unitInterval → S2 := fun t => if 0 < (t : ℝ) ∧ (t : ℝ) < 1 then F t else sphereInfty
    with hb
  have hbc : Continuous b := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    by_cases ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1
    · have hev : (fun t' : unitInterval => F t') =ᶠ[𝓝 t] b := by
        have : IsOpen {t' : unitInterval | 0 < (t' : ℝ) ∧ (t' : ℝ) < 1} :=
          (isOpen_lt continuous_const continuous_subtype_val).inter
            (isOpen_lt continuous_subtype_val continuous_const)
        filter_upwards [this.mem_nhds ht] with t' ht'
        simp only [hb, if_pos ht']
      refine ContinuousAt.congr ?_ hev
      exact (continuous_toSphere.comp (continuous_polyline _)).continuousAt.comp
        ((continuousAt_unitTan ht.1 ht.2).comp continuous_subtype_val.continuousAt)
    · have hbt : b t = sphereInfty := by simp only [hb, if_neg ht]
      rw [ContinuousAt, hbt, tendsto_def]
      intro U hU
      have t0 := t.2.1
      have t1 := t.2.2
      rcases (not_and_or.1 ht) with h | h
      · have htz : (t : ℝ) = 0 := by linarith [not_lt.1 h]
        obtain ⟨ε, hε, hεU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hF0 hU)
        have hopen : IsOpen {t' : unitInterval | (t' : ℝ) < min ε 1} :=
          isOpen_lt continuous_subtype_val continuous_const
        refine mem_of_superset (hopen.mem_nhds (show (t : ℝ) < min ε 1 by
          rw [htz]; exact lt_min hε one_pos)) fun t' ht' => ?_
        simp only [mem_setOf_eq, lt_min_iff] at ht'
        simp only [mem_preimage, hb]
        split_ifs with h'
        · exact hεU ⟨h'.1, ht'.1⟩
        · exact mem_of_mem_nhds hU
      · have hto : (t : ℝ) = 1 := by linarith [not_lt.1 h]
        obtain ⟨ε, hε, hεU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hF1 hU)
        have hopen : IsOpen {t' : unitInterval | max ε 0 < (t' : ℝ)} :=
          isOpen_lt continuous_const continuous_subtype_val
        refine mem_of_superset (hopen.mem_nhds (show max ε 0 < (t : ℝ) by
          rw [hto]; exact max_lt hε one_pos)) fun t' ht' => ?_
        simp only [mem_setOf_eq, max_lt_iff] at ht'
        simp only [mem_preimage, hb]
        split_ifs with h'
        · exact hεU ⟨ht'.1, h'.2⟩
        · exact mem_of_mem_nhds hU
  let β : Path sphereInfty sphereInfty :=
    { toFun := b
      continuous_toFun := hbc
      source' := by simp [hb]
      target' := by simp [hb] }
  have hpinj : Injective (polyline (latticePoint ∘ g)) := by
    rw [← injOn_univ]
    apply polyline_injOn
    · exact fun s _ => hadj _
    · exact fun s _ s' _ h => hg h
    · intro s _ s' _ hne h1 h2
      have e1 := hg h1
      have e2 := hg h2
      omega
  refine ⟨β, ?_, ?_⟩
  · intro t ht t' ht' h
    have h1 : (t : ℝ) < 1 := ht.2
    have h1' : (t' : ℝ) < 1 := ht'.2
    change b t = b t' at h
    by_cases h0 : 0 < (t : ℝ) <;> by_cases h0' : 0 < (t' : ℝ)
    · simp only [hb, if_pos (And.intro h0 h1), if_pos (And.intro h0' h1')] at h
      exact Subtype.ext (injOn_unitTan ⟨h0, h1⟩ ⟨h0', h1'⟩ (hpinj (toSphere_injective h)))
    · simp only [hb, if_pos (And.intro h0 h1), if_neg (fun h : _ ∧ _ => h0' h.1)] at h
      exact absurd h (toSphere_ne_infty _)
    · simp only [hb, if_neg (fun h : _ ∧ _ => h0 h.1), if_pos (And.intro h0' h1')] at h
      exact absurd h.symm (toSphere_ne_infty _)
    · exact Subtype.ext (by linarith [t.2.1, t'.2.1, not_lt.1 h0, not_lt.1 h0'])
  · ext w
    constructor
    · rintro ⟨t, rfl⟩
      change b t ∈ _
      simp only [hb]
      split_ifs
      · exact Or.inr ⟨_, by rw [← range_polyline]; exact mem_range_self _, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨0, β.source⟩
      · rw [← range_polyline] at hv
        obtain ⟨s, rfl⟩ := hv
        obtain ⟨t, ht, rfl⟩ := exists_unitTan_eq s
        refine ⟨⟨t, ht.1.le, ht.2.le⟩, ?_⟩
        exact if_pos (show 0 < t ∧ t < 1 from ht)

end Rigidity.Proofs.Section5
