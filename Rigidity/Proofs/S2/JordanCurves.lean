import Rigidity.Steps.S2.JordanCurves

/-!
# Lemma 2.16: proofs of the steps

The three steps of `Rigidity.Steps.S2.jordanCurves_of_steps`.

* `parametrizeStep`: lift each point `x_i` to a parameter `t_i ∈ [0, 1)` and sort them.
* `loopsStep`: the arc `α_k` of the Jordan curve is simple since it is shorter than one turn, and
  `β_k = α_k * (γ_{k+1} * γ_k⁻¹)` is a concatenation of simple arcs meeting only at their
  endpoints.
* `componentsStep`: by the Jordan curve theorem, one of the two components of `S² \ β_k` avoids
  the connected set `D_k ⊇ Γ \ β_k` made of the complementary arc `α \ α_k` and of the paths
  `γ_j` with `j ∉ {k, k + 1}` (deprived of the north pole); it is a component of `S² \ Γ` with
  frontier `β_k`. The midpoint of `α_k` lies on no other `β_l`, so these components are distinct.
-/

namespace Rigidity.Proofs.S2

open Set Function unitInterval Rigidity.Section2 Rigidity.Steps.S2

section Paths

variable {X : Type*} [TopologicalSpace X]

/-- Two simple arcs meeting only at their common endpoint concatenate to a simple arc. -/
theorem injective_trans {a b c : X} (p : Path a b) (r : Path b c) (hp : Injective p)
    (hr : Injective r) (hpr : range p ∩ range r ⊆ {b}) : Injective (p.trans r) := by
  intro t t' h
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Subtype.ext (by linarith [Subtype.mk.inj (hp h)])
  · have hb : r _ ∈ ({b} : Set X) := hpr ⟨⟨_, h⟩, mem_range_self _⟩
    have := congrArg Subtype.val (hr ((mem_singleton_iff.1 hb).trans r.source.symm))
    simp only [Icc.coe_zero] at this
    linarith [not_le.1 h2]
  · have hb : r _ ∈ ({b} : Set X) := hpr ⟨⟨_, h.symm⟩, mem_range_self _⟩
    have := congrArg Subtype.val (hr ((mem_singleton_iff.1 hb).trans r.source.symm))
    simp only [Icc.coe_zero] at this
    linarith [not_le.1 h1]
  · exact Subtype.ext (by linarith [Subtype.mk.inj (hr h)])

/-- Two simple arcs from `a` to `b` and back, meeting only at `a` and `b`, concatenate to a
simple loop. -/
theorem injOn_trans_Ico {a b : X} (p : Path a b) (r : Path b a) (hp : Injective p)
    (hr : Injective r) (hpr : range p ∩ range r ⊆ {a, b}) :
    InjOn (p.trans r) (Ico 0 1) := by
  intro t ht t' ht' h
  have ht1 : (t : ℝ) < 1 := ht.2
  have ht1' : (t' : ℝ) < 1 := ht'.2
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Subtype.ext (by linarith [Subtype.mk.inj (hp h)])
  · have hb : r _ ∈ ({a, b} : Set X) := hpr ⟨⟨_, h⟩, mem_range_self _⟩
    rcases hb with hb | hb
    · have := congrArg Subtype.val (hr (hb.trans r.target.symm))
      simp only [Icc.coe_one] at this
      linarith
    · have := congrArg Subtype.val (hr ((mem_singleton_iff.1 hb).trans r.source.symm))
      simp only [Icc.coe_zero] at this
      linarith [not_le.1 h2]
  · have hb : r _ ∈ ({a, b} : Set X) := hpr ⟨⟨_, h.symm⟩, mem_range_self _⟩
    rcases hb with hb | hb
    · have := congrArg Subtype.val (hr (hb.trans r.target.symm))
      simp only [Icc.coe_one] at this
      linarith
    · have := congrArg Subtype.val (hr ((mem_singleton_iff.1 hb).trans r.source.symm))
      simp only [Icc.coe_zero] at this
      linarith [not_le.1 h1]
  · exact Subtype.ext (by linarith [Subtype.mk.inj (hr h)])

/-- The reverse of a simple arc is a simple arc. -/
theorem injective_symm {a b : X} {p : Path a b} (hp : Injective p) : Injective p.symm := by
  intro t t' h
  have h' : p (σ t) = p (σ t') := h
  simpa using congrArg σ (hp h')

end Paths

section LoopLift

variable {X : Type*} [TopologicalSpace X] {q : X}

theorem continuous_loopLift (α : Path q q) : Continuous (loopLift α) :=
  ContinuousOn.comp_fract'' α.continuous_extend.continuousOn (by simp)

theorem loopLift_add_intCast (α : Path q q) (u : ℝ) (m : ℤ) :
    loopLift α (u + m) = loopLift α u := by
  simp only [loopLift, Int.fract_add_intCast]

theorem loopLift_add_one (α : Path q q) (u : ℝ) : loopLift α (u + 1) = loopLift α u := by
  simp only [loopLift, Int.fract_add_one]

theorem loopLift_coe (α : Path q q) (t : I) : loopLift α t = α t := by
  rcases eq_or_lt_of_le t.2.2 with h | h
  · have : t = 1 := Subtype.ext h
    subst this
    simp [loopLift]
  · simp only [loopLift, Int.fract_eq_self.2 ⟨t.2.1, h⟩, Path.extend_extends']

theorem loopLift_mem_range (α : Path q q) (u : ℝ) : loopLift α u ∈ range α := by
  rw [← Path.extend_range]
  exact mem_range_self _

/-- A simple loop is injective on `[0, 1)`, as a function of a real parameter. -/
theorem extend_injOn_Ico (α : Path q q) (hα : InjOn α (Ico 0 1)) :
    InjOn α.extend (Ico (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hu' : u ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hu
  have hv' : v ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hv
  have e1 : α.extend u = α ⟨u, hu'⟩ := α.extend_extends' ⟨u, hu'⟩
  have e2 : α.extend v = α ⟨v, hv'⟩ := α.extend_extends' ⟨v, hv'⟩
  rw [e1, e2] at huv
  have hmu : (⟨u, hu'⟩ : I) ∈ Ico (0 : I) 1 := ⟨hu.1, hu.2⟩
  have hmv : (⟨v, hv'⟩ : I) ∈ Ico (0 : I) 1 := ⟨hv.1, hv.2⟩
  exact Subtype.mk.inj (hα hmu hmv huv)

/-- The periodic lift of a simple loop is injective on every turn `[a, a + 1)`. -/
theorem loopLift_injOn (α : Path q q) (hα : InjOn α (Ico 0 1)) (a : ℝ) :
    InjOn (loopLift α) (Ico a (a + 1)) := by
  intro u hu v hv huv
  have h := extend_injOn_Ico α hα ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩
    ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩ huv
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h
  have h1 : (z : ℝ) < 1 := by rw [← hz]; linarith [hu.2, hv.1]
  have h2 : (-1 : ℝ) < z := by rw [← hz]; linarith [hu.1, hv.2]
  have h1' : z < 1 := by exact_mod_cast h1
  have h2' : -1 < z := by exact_mod_cast h2
  have hz0 : z = 0 := by omega
  rw [hz0, Int.cast_zero] at hz
  linarith

/-- Every point of the loop is the lift of a parameter in any given turn `[a, a + 1)`. -/
theorem exists_loopLift_eq (α : Path q q) {y : X} (hy : y ∈ range α) (a : ℝ) :
    ∃ u ∈ Ico a (a + 1), loopLift α u = y := by
  obtain ⟨t, rfl⟩ := hy
  refine ⟨t - ⌊(t : ℝ) - a⌋, ⟨?_, ?_⟩, ?_⟩
  · linarith [Int.floor_le ((t : ℝ) - a)]
  · linarith [Int.lt_floor_add_one ((t : ℝ) - a)]
  · rw [sub_eq_add_neg, ← Int.cast_neg, loopLift_add_intCast, loopLift_coe]

theorem affine_mem_Icc {a b : ℝ} (hab : a ≤ b) (t : I) : a + t * (b - a) ∈ Icc a b := by
  have h1 := mul_nonneg t.2.1 (sub_nonneg.2 hab)
  have h2 := mul_le_of_le_one_left (sub_nonneg.2 hab) t.2.2
  constructor <;> linarith

/-- The arc of a loop between the parameters `a` and `b`, as a path. -/
noncomputable def loopArc (α : Path q q) (a b : ℝ) : Path (loopLift α a) (loopLift α b) where
  toFun t := loopLift α (a + t * (b - a))
  continuous_toFun := (continuous_loopLift α).comp (by fun_prop)
  source' := by simp
  target' := by simp

theorem range_loopArc (α : Path q q) {a b : ℝ} (hab : a < b) :
    range (loopArc α a b) = loopLift α '' Icc a b := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a + t * (b - a), affine_mem_Icc hab.le t, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨(u - a) / (b - a), div_nonneg (by linarith [hu.1]) (by linarith), ?_⟩, ?_⟩
    · rw [div_le_one (by linarith)]
      linarith [hu.2]
    · show loopLift α (a + (u - a) / (b - a) * (b - a)) = loopLift α u
      rw [div_mul_cancel₀ _ (by linarith : b - a ≠ 0), add_sub_cancel]

/-- An arc of a simple loop shorter than one turn is simple. -/
theorem injective_loopArc (α : Path q q) (hα : InjOn α (Ico 0 1)) {a b : ℝ} (hab : a < b)
    (hba : b < a + 1) : Injective (loopArc α a b) := by
  intro t t' h
  have ht := affine_mem_Icc hab.le t
  have ht' := affine_mem_Icc hab.le t'
  have := loopLift_injOn α hα a ⟨ht.1, by linarith [ht.2]⟩ ⟨ht'.1, by linarith [ht'.2]⟩ h
  exact Subtype.ext (mul_right_cancel₀ (sub_ne_zero.2 hab.ne') (by linarith))

end LoopLift

section Cyclic

variable {n : ℕ} {s : Fin (n + 2) → ℝ}

theorem lt_arcEnd (hs : StrictMono s) (hl : s (Fin.last (n + 1)) < s 0 + 1) (k : Fin (n + 2)) :
    s k < arcEnd s k := by
  rw [arcEnd]
  split_ifs with hk
  · subst hk
    exact hl
  · exact hs (Fin.lt_add_one_iff.2 (Fin.lt_last_iff_ne_last.2 hk))

theorem arcEnd_lt (hs : StrictMono s) (hl : s (Fin.last (n + 1)) < s 0 + 1) (k : Fin (n + 2)) :
    arcEnd s k < s k + 1 := by
  rw [arcEnd]
  split_ifs with hk
  · subst hk
    linarith [hs (Fin.last_pos' : (0 : Fin (n + 2)) < Fin.last (n + 1))]
  · linarith [hs.monotone (Fin.le_last (k + 1)), hs.monotone (Fin.zero_le k)]

/-- The cyclic order: for `k ≠ l`, a translate of the arc `[s k, arcEnd s k]` by an integer lies
in the complementary turn `[arcEnd s l, s l + 1]` of the arc `l`. -/
theorem exists_shift (hs : StrictMono s) (hl : s (Fin.last (n + 1)) < s 0 + 1) {k l : Fin (n + 2)}
    (hkl : k ≠ l) : ∃ z : ℤ, arcEnd s l ≤ s k + z ∧ arcEnd s k + z ≤ s l + 1 := by
  have h0 : ∀ j, s 0 ≤ s j := fun j => hs.monotone (Fin.zero_le j)
  have hL : ∀ j, s j ≤ s (Fin.last (n + 1)) := fun j => hs.monotone (Fin.le_last j)
  by_cases hk : k = Fin.last (n + 1)
  · have hl' : l ≠ Fin.last (n + 1) := fun h => hkl (hk.trans h.symm)
    refine ⟨0, ?_, ?_⟩ <;> simp only [arcEnd, if_pos hk, if_neg hl', Int.cast_zero, add_zero] <;>
      subst hk <;> linarith [hL (l + 1), h0 l]
  · by_cases hl' : l = Fin.last (n + 1)
    · refine ⟨1, ?_, ?_⟩ <;> simp only [arcEnd, if_neg hk, if_pos hl', Int.cast_one] <;>
        subst hl' <;> linarith [hL (k + 1), h0 k]
    · rcases lt_or_gt_of_ne hkl with h | h
      · have := hs.monotone (Fin.add_one_le_of_lt h)
        refine ⟨1, ?_, ?_⟩ <;> simp only [arcEnd, if_neg hk, if_neg hl', Int.cast_one] <;>
          linarith [hL (l + 1), h0 k]
      · have := hs.monotone (Fin.add_one_le_of_lt h)
        refine ⟨0, ?_, ?_⟩ <;>
          simp only [arcEnd, if_neg hk, if_neg hl', Int.cast_zero, add_zero] <;>
          linarith [hL (k + 1), h0 l]

end Cyclic

section Configuration

variable {n : ℕ} {q : S2} {α : Path q q} {x : Fin (n + 2) → S2}
  {γ : ∀ i, Path (x i) northPole} {s : Fin (n + 2) → ℝ}

/-- The Jordan curve `β_k = α_k ∪ γ_k ∪ γ_{k+1}`, as a set. -/
def jordanLoop (α : Path q q) (γ : ∀ i, Path (x i) northPole) (s : Fin (n + 2) → ℝ)
    (k : Fin (n + 2)) : Set S2 :=
  loopLift α '' Icc (s k) (arcEnd s k) ∪ range (γ k) ∪ range (γ (k + 1))

theorem loopLift_arcEnd (hS : IsCyclicParametrization α x s) (k : Fin (n + 2)) :
    loopLift α (arcEnd s k) = x (k + 1) := by
  rw [arcEnd]
  split_ifs with hk
  · subst hk
    rw [loopLift_add_one, hS.loopLift_eq, Fin.last_add_one]
  · exact hS.loopLift_eq _

/-- The points of the complementary arc `α \ α_k` are not on the Jordan curve `β_k`. -/
theorem loopLift_not_mem_jordanLoop (hD : IsJordanCurvesData x γ α)
    (hS : IsCyclicParametrization α x s) (k : Fin (n + 2)) {u : ℝ}
    (hu : u ∈ Ioo (arcEnd s k) (s k + 1)) : loopLift α u ∉ jordanLoop α γ s k := by
  have hk := lt_arcEnd hS.strictMono hS.last_lt k
  have hk' := arcEnd_lt hS.strictMono hS.last_lt k
  have hinj := loopLift_injOn α hD.injOn_curve (s k)
  have huI : u ∈ Ico (s k) (s k + 1) := ⟨hk.le.trans hu.1.le, hu.2⟩
  intro h
  simp only [jordanLoop, mem_union] at h
  rcases h with (⟨v, hv, hvu⟩ | hy) | hy
  · have := hinj ⟨hv.1, hv.2.trans_lt hk'⟩ huI hvu
    linarith [hv.2, hu.1]
  · have h1 : loopLift α u ∈ range α ∩ range (γ k) := ⟨loopLift_mem_range α u, hy⟩
    rw [hD.curve_inter_path k, mem_singleton_iff, ← hS.loopLift_eq k] at h1
    have := hinj huI ⟨le_rfl, by linarith⟩ h1
    linarith [hu.1]
  · have h1 : loopLift α u ∈ range α ∩ range (γ (k + 1)) := ⟨loopLift_mem_range α u, hy⟩
    rw [hD.curve_inter_path (k + 1), mem_singleton_iff, ← loopLift_arcEnd hS k] at h1
    have := hinj huI ⟨hk.le, hk'⟩ h1
    linarith [hu.1]

/-- The points `x_j` with `j ∉ {k, k + 1}` lie on the complementary arc `α \ α_k`. -/
theorem exists_lift_point (hD : IsJordanCurvesData x γ α) (hS : IsCyclicParametrization α x s)
    {j k : Fin (n + 2)} (hjk : j ≠ k) (hjk' : j ≠ k + 1) :
    ∃ u ∈ Ioo (arcEnd s k) (s k + 1), loopLift α u = x j := by
  obtain ⟨z, h1, h2⟩ := exists_shift hS.strictMono hS.last_lt hjk
  have hlift : loopLift α (s j + z) = x j := by rw [loopLift_add_intCast, hS.loopLift_eq]
  refine ⟨s j + z, ⟨lt_of_le_of_ne h1 fun h => hjk' (hD.injective_points ?_), ?_⟩, hlift⟩
  · rw [← hlift, ← h, loopLift_arcEnd hS]
  · linarith [lt_arcEnd hS.strictMono hS.last_lt j]

/-- The midpoint of the arc `α_k` lies on the complementary arc `α \ α_l` for `l ≠ k`. -/
theorem exists_lift_midpoint (hS : IsCyclicParametrization α x s) {k l : Fin (n + 2)}
    (hkl : k ≠ l) : ∃ u ∈ Ioo (arcEnd s l) (s l + 1),
      loopLift α u = loopLift α ((s k + arcEnd s k) / 2) := by
  obtain ⟨z, h1, h2⟩ := exists_shift hS.strictMono hS.last_lt hkl
  have hk := lt_arcEnd hS.strictMono hS.last_lt k
  exact ⟨(s k + arcEnd s k) / 2 + z, ⟨by linarith, by linarith⟩, loopLift_add_intCast _ _ _⟩

/-- The paths `γ_j` with `j ∉ {k, k + 1}`, deprived of the north pole, avoid `β_k`. -/
theorem extend_not_mem_jordanLoop (hD : IsJordanCurvesData x γ α)
    (hS : IsCyclicParametrization α x s) {j k : Fin (n + 2)} (hjk : j ≠ k) (hjk' : j ≠ k + 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : (γ j).extend t ∉ jordanLoop α γ s k := by
  have htI : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
  have hy : (γ j).extend t = γ j ⟨t, htI⟩ := (γ j).extend_extends' ⟨t, htI⟩
  have hN : (γ j).extend t ≠ northPole := by
    rw [hy]
    intro h
    have := congrArg Subtype.val (hD.injective_path j (h.trans (γ j).target.symm))
    simp only [Icc.coe_one] at this
    linarith [ht.2]
  have hmem : (γ j).extend t ∈ range (γ j) := by
    rw [hy]
    exact mem_range_self _
  intro h
  simp only [jordanLoop, mem_union] at h
  rcases h with (h | h) | h
  · have hα : (γ j).extend t ∈ range α := by
      obtain ⟨v, -, hv⟩ := h
      rw [← hv]
      exact loopLift_mem_range α v
    have h1 : (γ j).extend t ∈ range α ∩ range (γ j) := ⟨hα, hmem⟩
    rw [hD.curve_inter_path j, mem_singleton_iff] at h1
    obtain ⟨u, hu, hux⟩ := exists_lift_point hD hS hjk hjk'
    apply loopLift_not_mem_jordanLoop hD hS k hu
    rw [hux, ← h1]
    simp only [jordanLoop, mem_union]
    exact Or.inl (Or.inl h)
  · have h1 : (γ j).extend t ∈ range (γ j) ∩ range (γ k) := ⟨hmem, h⟩
    rw [hD.path_inter_path j k hjk] at h1
    exact hN h1
  · have h1 : (γ j).extend t ∈ range (γ j) ∩ range (γ (k + 1)) := ⟨hmem, h⟩
    rw [hD.path_inter_path j (k + 1) hjk'] at h1
    exact hN h1

/-- The connected set `D_k = (α \ α_k) ∪ ⋃_{j ∉ {k, k+1}} (γ_j \ {N})` contains `Γ \ β_k` and
avoids `β_k`. -/
theorem exists_preconnected (hD : IsJordanCurvesData x γ α) (hS : IsCyclicParametrization α x s)
    (k : Fin (n + 2)) : ∃ D : Set S2, IsPreconnected D ∧
      (range α ∪ ⋃ i, range (γ i)) \ jordanLoop α γ s k ⊆ D ∧
      Disjoint D (jordanLoop α γ s k) := by
  have hk' := arcEnd_lt hS.strictMono hS.last_lt k
  set A := loopLift α '' Ioo (arcEnd s k) (s k + 1) with hA
  set B := jordanLoop α γ s k with hB
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    rintro _ ⟨u, hu, rfl⟩
    exact loopLift_not_mem_jordanLoop hD hS k hu
  have hAc : IsPreconnected A :=
    isPreconnected_Ioo.image _ (continuous_loopLift α).continuousOn
  obtain ⟨c, hc⟩ : A.Nonempty := (nonempty_Ioo.2 hk').image _
  refine ⟨⋃ j, (A ∪ ((γ j).extend '' Ico 0 1 \ B)),
    isPreconnected_iUnion ⟨c, mem_iInter.2 fun j => Or.inl hc⟩ fun j => ?_, ?_, ?_⟩
  · by_cases hj : j = k ∨ j = k + 1
    · have : (γ j).extend '' Ico 0 1 \ B = ∅ := by
        rw [Set.sdiff_eq_empty]
        rintro _ ⟨t, -, rfl⟩
        have : (γ j).extend t ∈ range (γ j) := by
          rw [← Path.extend_range]
          exact mem_range_self t
        simp only [hB, jordanLoop, mem_union]
        rcases hj with rfl | rfl
        · exact Or.inl (Or.inr this)
        · exact Or.inr this
      rw [this, union_empty]
      exact hAc
    · replace hj := not_or.1 hj
      have : (γ j).extend '' Ico 0 1 \ B = (γ j).extend '' Ico 0 1 := by
        rw [sdiff_eq_left, disjoint_left]
        rintro _ ⟨t, ht, rfl⟩
        exact extend_not_mem_jordanLoop hD hS hj.1 hj.2 ht
      rw [this]
      obtain ⟨u, hu, hux⟩ := exists_lift_point hD hS hj.1 hj.2
      exact IsPreconnected.union' ⟨x j, ⟨u, hu, hux⟩, ⟨0, ⟨le_rfl, zero_lt_one⟩, (γ j).extend_zero⟩⟩
        hAc (isPreconnected_Ico.image _ (γ j).continuous_extend.continuousOn)
  · rintro y ⟨hy | hy, hyB⟩
    · obtain ⟨u, hu, rfl⟩ := exists_loopLift_eq α hy (s k)
      refine mem_iUnion.2 ⟨k, Or.inl ⟨u, ⟨not_le.1 fun h => hyB ?_, hu.2⟩, rfl⟩⟩
      simp only [hB, jordanLoop, mem_union]
      exact Or.inl (Or.inl ⟨u, ⟨hu.1, h⟩, rfl⟩)
    · obtain ⟨j, t, rfl⟩ := mem_iUnion.1 hy
      have ht : (t : ℝ) < 1 := by
        refine lt_of_le_of_ne t.2.2 fun h => hyB ?_
        have : t = 1 := Subtype.ext h
        subst this
        rw [(γ j).target]
        simp only [hB, jordanLoop, mem_union]
        exact Or.inl (Or.inr ⟨1, (γ k).target⟩)
      exact mem_iUnion.2 ⟨j, Or.inr ⟨⟨t, ⟨t.2.1, ht⟩, (γ j).extend_extends' t⟩, hyB⟩⟩
  · rw [disjoint_iUnion_left]
    exact fun j => disjoint_union_left.2 ⟨hAB, disjoint_sdiff_left⟩

/-- The Jordan curves `β_k` are pairwise distinct: the midpoint of `α_k` is on no other `β_l`. -/
theorem jordanLoop_ne (hD : IsJordanCurvesData x γ α) (hS : IsCyclicParametrization α x s)
    {k l : Fin (n + 2)} (hkl : k ≠ l) : jordanLoop α γ s k ≠ jordanLoop α γ s l := by
  intro h
  obtain ⟨u, hu, hum⟩ := exists_lift_midpoint hS hkl
  have hk := lt_arcEnd hS.strictMono hS.last_lt k
  apply loopLift_not_mem_jordanLoop hD hS l hu
  rw [hum, ← h]
  simp only [jordanLoop, mem_union]
  exact Or.inl (Or.inl ⟨_, ⟨by linarith, by linarith⟩, rfl⟩)

end Configuration

section Components

/-- One Jordan curve `β ⊆ Γ`: if `Γ \ β` lies in a connected set avoiding `β`, one of the two
components of `S² \ β` is a component of `S² \ Γ`, with frontier `β`. -/
theorem exists_component_of_loop (hJ : External.JordanCurveTheoremSphere) (Γ : Set S2) {p : S2}
    (β : Path p p) (hβ : InjOn β (Ico 0 1)) (hβΓ : range β ⊆ Γ) {D : Set S2}
    (hDc : IsPreconnected D) (hΓD : Γ \ range β ⊆ D) (hDβ : Disjoint D (range β)) :
    ∃ W : Set S2, W.Nonempty ∧ frontier W = range β ∧
      ∀ z ∈ W, z ∉ Γ ∧ connectedComponentIn Γᶜ z = W := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hUVβ, hfU, hfV⟩ := hJ p β hβ
  have key : ∀ W W' : Set S2, IsOpen W → IsOpen W' → IsConnected W → Disjoint W W' →
      W ∪ W' = (range β)ᶜ → frontier W = range β → D ⊆ W' →
      ∃ W : Set S2, W.Nonempty ∧ frontier W = range β ∧
        ∀ z ∈ W, z ∉ Γ ∧ connectedComponentIn Γᶜ z = W := by
    intro W W' hW hW' hWc hWW' hWWβ hfW hDW'
    have hWΓ : W ⊆ Γᶜ := by
      intro y hy hyΓ
      by_cases hyβ : y ∈ range β
      · have : y ∈ (range β)ᶜ := by
          rw [← hWWβ]
          exact Or.inl hy
        exact this hyβ
      · exact hWW'.ne_of_mem hy (hDW' (hΓD ⟨hyΓ, hyβ⟩)) rfl
    refine ⟨W, hWc.nonempty, hfW, fun z hz => ⟨hWΓ hz, subset_antisymm ?_
      (hWc.isPreconnected.subset_connectedComponentIn hz hWΓ)⟩⟩
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hW hW' hWW' ?_
      ⟨z, mem_connectedComponentIn (hWΓ hz), hz⟩
    rw [hWWβ]
    exact (connectedComponentIn_subset _ _).trans (compl_subset_compl.2 hβΓ)
  have hDUV : D ⊆ U ∪ V := by
    rw [hUVβ]
    exact hDβ.subset_compl_right
  rcases hDc.subset_or_subset hU hV hUV hDUV with h | h
  · exact key V U hV hU hVc hUV.symm (by rw [union_comm, hUVβ]) hfV h
  · exact key U V hU hV hUc hUV hUVβ hfU h

/-- A family of Jordan curves `β_k ⊆ Γ` through the north pole, with distinct ranges, each with
`Γ \ β_k` in a connected set avoiding `β_k`, gives distinct components of `S² \ Γ` whose closure
contains the north pole. -/
theorem exists_components_of_loops (hJ : External.JordanCurveTheoremSphere) {ι : Type*}
    (Γ : Set S2) (p : ι → S2) (β : ∀ k, Path (p k) (p k)) (hβ : ∀ k, InjOn (β k) (Ico 0 1))
    (hβΓ : ∀ k, range (β k) ⊆ Γ) (hN : ∀ k, northPole ∈ range (β k))
    (hD : ∀ k, ∃ D : Set S2, IsPreconnected D ∧ Γ \ range (β k) ⊆ D ∧
      Disjoint D (range (β k)))
    (hdist : ∀ k l, k ≠ l → range (β k) ≠ range (β l)) :
    ∃ z : ι → S2, (∀ k, z k ∉ Γ) ∧
      (∀ k l, k ≠ l → connectedComponentIn Γᶜ (z k) ≠ connectedComponentIn Γᶜ (z l)) ∧
      ∀ k, northPole ∈ closure (connectedComponentIn Γᶜ (z k)) := by
  have h : ∀ k, ∃ W : Set S2, W.Nonempty ∧ frontier W = range (β k) ∧
      ∀ z ∈ W, z ∉ Γ ∧ connectedComponentIn Γᶜ z = W := by
    intro k
    obtain ⟨D, h1, h2, h3⟩ := hD k
    exact exists_component_of_loop hJ Γ (β k) (hβ k) (hβΓ k) h1 h2 h3
  choose W hWne hfW hW using h
  choose z hz using hWne
  refine ⟨z, fun k => (hW k _ (hz k)).1, fun k l hkl heq => hdist k l hkl ?_, fun k => ?_⟩
  · have e1 := (hW k _ (hz k)).2
    have e2 := (hW l _ (hz l)).2
    rw [← hfW k, ← hfW l, ← e1, ← e2, heq]
  · rw [(hW k _ (hz k)).2]
    apply frontier_subset_closure
    rw [hfW k]
    exact hN k

end Components

/-- Step `step:2.16-parametrize`. -/
theorem parametrizeStep : ParametrizeStep := by
  intro K q α x hα hx hxα
  choose t ht htx using fun i => exists_loopLift_eq α (hxα i) 0
  have htinj : Injective t := fun i j h => hx (by rw [← htx i, ← htx j, h])
  refine ⟨Tuple.sort t, t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective
    (htinj.comp (Tuple.sort t).injective), fun k => ?_, fun k => htx _⟩
  simpa using ht (Tuple.sort t k)

/-- Step `step:2.16-loops`. -/
theorem loopsStep : LoopsStep := by
  intro n q α x γ s hD hS k
  have hk : s k < arcEnd s k := lt_arcEnd hS.strictMono hS.last_lt k
  have hk' : arcEnd s k < s k + 1 := arcEnd_lt hS.strictMono hS.last_lt k
  let p : Path (x k) (x (k + 1)) :=
    (loopArc α (s k) (arcEnd s k)).cast (hS.loopLift_eq k).symm (loopLift_arcEnd hS k).symm
  let r : Path (x (k + 1)) (x k) := (γ (k + 1)).trans (γ k).symm
  have hp : Injective p := injective_loopArc α hD.injOn_curve hk hk'
  have hkk : k + 1 ≠ k := by simp
  have hr : Injective r := injective_trans _ _ (hD.injective_path _)
    (injective_symm (hD.injective_path k))
    (by rw [Path.symm_range, hD.path_inter_path _ _ hkk])
  have hpr : range p = loopLift α '' Icc (s k) (arcEnd s k) := range_loopArc α hk
  refine ⟨p.trans r, injOn_trans_Ico p r hp hr ?_, ?_⟩
  · rw [hpr, Path.trans_range, Path.symm_range]
    rintro y ⟨⟨u, -, rfl⟩, hy | hy⟩
    · have h1 : loopLift α u ∈ range α ∩ range (γ (k + 1)) := ⟨loopLift_mem_range α u, hy⟩
      rw [hD.curve_inter_path] at h1
      exact Or.inr h1
    · have h1 : loopLift α u ∈ range α ∩ range (γ k) := ⟨loopLift_mem_range α u, hy⟩
      rw [hD.curve_inter_path] at h1
      exact Or.inl h1
  · rw [Path.trans_range, Path.trans_range, Path.symm_range, hpr]
    ext y
    simp only [mem_union]
    tauto

/-- Step `step:2.16-components`. -/
theorem componentsStep : ComponentsStep := by
  intro hJ n q α x γ s hD hS hL
  choose β hβ hβr using hL
  refine exists_components_of_loops hJ (range α ∪ ⋃ i, range (γ i)) x β hβ (fun k => ?_)
    (fun k => ?_) (fun k => ?_) (fun k l hkl => ?_)
  · rw [hβr k]
    rintro y ((⟨u, -, rfl⟩ | hy) | hy)
    · exact Or.inl (loopLift_mem_range α u)
    · exact Or.inr (mem_iUnion.2 ⟨k, hy⟩)
    · exact Or.inr (mem_iUnion.2 ⟨k + 1, hy⟩)
  · rw [hβr k]
    exact Or.inl (Or.inr ⟨1, (γ k).target⟩)
  · rw [hβr k]
    exact exists_preconnected hD hS k
  · rw [hβr k, hβr l]
    exact jordanLoop_ne hD hS hkl

/-- **Lemma 2.16** (corrected statement), from the Jordan curve theorem on `S²`. -/
theorem jordanCurves (hJ : External.JordanCurveTheoremSphere) : Section2.JordanCurvesStmt :=
  jordanCurves_of_steps hJ parametrizeStep loopsStep componentsStep

end Rigidity.Proofs.S2
