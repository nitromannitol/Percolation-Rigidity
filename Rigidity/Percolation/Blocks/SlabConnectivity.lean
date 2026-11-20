import Rigidity.Percolation.Blocks.SlabTwoPoint
import Rigidity.Percolation.SlabFiniteEnergy

/-!
# Uniform slab connectivity above criticality

In dimension `d ≥ 3`, above the critical point, a single slab width gives a uniform positive
lower bound for two-point connections inside every complete slab of every integer cube. Two
vertices of a slab are joined through the `d` intermediate vertices obtained by changing one
coordinate at a time; consecutive intermediate vertices lie in a common slab box inside the slab,
whose two long directions contain the changed coordinate, and Harris' inequality combines the `d`
connections. Small cubes are handled by finite energy. This is the Grimmett–Marstrand theorem in
the form used by the coarse graining.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- In dimension at least three, two directions leave a third one. -/
theorem exists_ne_ne (hd : 3 ≤ d) (a l : Fin d) : ∃ l' : Fin d, l' ≠ a ∧ l' ≠ l := by
  by_contra h
  push Not at h
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  have := Fin.ext_iff.not.mp (show (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ by simp)
  rcases a with ⟨a, ha⟩
  rcases l with ⟨l, hl⟩
  by_cases e0 : (⟨0, by omega⟩ : Fin d) = ⟨a, ha⟩ <;>
    by_cases e1 : (⟨1, by omega⟩ : Fin d) = ⟨a, ha⟩ <;>
      by_cases e2 : (⟨2, by omega⟩ : Fin d) = ⟨a, ha⟩ <;>
        simp_all [Fin.ext_iff] <;> omega

/-- A partner direction: different from `a` and from `l`. -/
def partner (hd : 3 ≤ d) (a l : Fin d) : Fin d := (exists_ne_ne hd a l).choose

theorem partner_ne_left (hd : 3 ≤ d) (a l : Fin d) : partner hd a l ≠ a :=
  (exists_ne_ne hd a l).choose_spec.1

theorem partner_ne_right (hd : 3 ≤ d) (a l : Fin d) : partner hd a l ≠ l :=
  (exists_ne_ne hd a l).choose_spec.2

/-- The vertex with the first `t` coordinates of `y` and the others of `x`. -/
def interPoint (x y : Vertex d) (t : ℕ) : Vertex d := fun l => if l.val < t then y l else x l

theorem interPoint_zero (x y : Vertex d) : interPoint x y 0 = x := by
  funext l
  simp [interPoint]

theorem interPoint_last (x y : Vertex d) : interPoint x y d = y := by
  funext l
  simp [interPoint, l.isLt]

theorem interPoint_succ_of_ne (x y : Vertex d) {t : ℕ} {l : Fin d} (h : l.val ≠ t) :
    interPoint x y (t + 1) l = interPoint x y t l := by
  simp only [interPoint]
  by_cases h1 : l.val < t
  · simp [h1, show l.val < t + 1 by omega]
  · simp [h1, show ¬ l.val < t + 1 by omega]

/-- Each coordinate of an intermediate vertex is a coordinate of one of the two ends. -/
theorem interPoint_apply (x y : Vertex d) (t : ℕ) (l : Fin d) :
    interPoint x y t l = x l ∨ interPoint x y t l = y l := by
  simp only [interPoint]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The long directions of the move changing the coordinate `l`. -/
def moveDirs (hd : 3 ≤ d) (a l : Fin d) : Fin d × Fin d :=
  if l = a then (partner hd a a, partner hd a (partner hd a a)) else (l, partner hd a l)

theorem moveDirs_ne (hd : 3 ≤ d) (a l : Fin d) :
    (moveDirs hd a l).1 ≠ (moveDirs hd a l).2 ∧ (moveDirs hd a l).1 ≠ a ∧
      (moveDirs hd a l).2 ≠ a := by
  unfold moveDirs
  split_ifs with h
  · exact ⟨(partner_ne_right hd a _).symm, partner_ne_left hd a a, partner_ne_left hd a _⟩
  · exact ⟨(partner_ne_right hd a l).symm, h, partner_ne_left hd a l⟩

/-- A changed coordinate is long or is the slab direction. -/
theorem moveDirs_cover (hd : 3 ≤ d) (a l : Fin d) :
    l = (moveDirs hd a l).1 ∨ l = a := by
  unfold moveDirs
  split_ifs with h
  · exact Or.inr h
  · exact Or.inl rfl

/-- The corner of the slab box of the move changing the coordinate `l` at the vertex `z`. -/
def moveCorner (Q : IntegerCube d) (a : Fin d) (w k : ℕ) (D : Fin d × Fin d) (z : Vertex d) :
    Vertex d := fun l =>
  if l = D.1 ∨ l = D.2 then Q.corner l else
    if l = a then Q.corner a + ((k * w : ℕ) : ℤ) else
      min (z l) (Q.corner l + Q.size - w)

/-- The slab boxes of the moves lie in the slab. -/
theorem slabBox_moveCorner_subset (Q : IntegerCube d) {a : Fin d} {w k : ℕ}
    (hfull : (k + 1) * w ≤ Q.size) {D : Fin d × Fin d} (hDa : D.1 ≠ a ∧ D.2 ≠ a) (z : Vertex d)
    (hz : z ∈ Q.vertices) :
    slabBox (moveCorner Q a w k D z) D.1 D.2 Q.size w ⊆ Q.slab a w k := by
  intro v hv
  rw [IntegerCube.mem_vertices] at hz
  have hw : w ≤ Q.size := le_trans (by nlinarith) hfull
  have hkw : ((k * w : ℕ) : ℤ) + w ≤ Q.size := by
    have : k * w + w ≤ Q.size := by nlinarith
    exact_mod_cast this
  have hcoord : ∀ l, Q.corner l ≤ v l ∧ v l < Q.corner l + (Q.size : ℤ) := by
    intro l
    have h := hv l
    have hz' := hz l
    unfold moveCorner at h
    by_cases hl : l = D.1 ∨ l = D.2
    · simp only [hl, ↓reduceIte] at h
      exact h
    · simp only [hl, ↓reduceIte] at h
      by_cases hla : l = a
      · subst hla
        simp only [↓reduceIte] at h
        constructor <;> omega
      · simp only [hla, ↓reduceIte] at h
        constructor <;> omega
  refine ⟨(IntegerCube.mem_vertices Q v).2 hcoord, ?_⟩
  have h := hv a
  have hna : ¬ (a = D.1 ∨ a = D.2) := by
    rintro (h1 | h1)
    · exact hDa.1 h1.symm
    · exact hDa.2 h1.symm
  unfold moveCorner at h
  simp only [hna, ↓reduceIte] at h
  push_cast at h ⊢
  constructor <;> nlinarith [h.1, h.2]

/-- Consecutive intermediate vertices lie in the slab box of their move. -/
theorem interPoint_mem_moveBox (hd : 3 ≤ d) (Q : IntegerCube d) {a : Fin d} {w k : ℕ}
    (hw : 0 < w) {x y : Vertex d} (hx : x ∈ Q.slab a w k) (hy : y ∈ Q.slab a w k) {t : ℕ} (ht : t < d)
    {s : ℕ} (hs : s = t ∨ s = t + 1) :
    interPoint x y s ∈ slabBox (moveCorner Q a w k (moveDirs hd a ⟨t, ht⟩) (interPoint x y t))
      (moveDirs hd a ⟨t, ht⟩).1 (moveDirs hd a ⟨t, ht⟩).2 Q.size w := by
  set D := moveDirs hd a ⟨t, ht⟩ with hD
  obtain ⟨hxv, hxa1, hxa2⟩ := hx
  obtain ⟨hyv, hya1, hya2⟩ := hy
  rw [IntegerCube.mem_vertices] at hxv hyv
  intro l
  unfold moveCorner
  by_cases hl : l = D.1 ∨ l = D.2
  · simp only [hl, ↓reduceIte]
    rcases interPoint_apply x y s l with h | h <;> rw [h]
    · exact hxv l
    · exact hyv l
  · simp only [hl, ↓reduceIte]
    by_cases hla : l = a
    · subst hla
      simp only [↓reduceIte]
      rcases interPoint_apply x y s l with h | h <;> rw [h] <;> push_cast at * <;>
        constructor <;> nlinarith
    · simp only [hla, ↓reduceIte]
      have hlt : l.val ≠ t := by
        intro h
        have hlt' : l = ⟨t, ht⟩ := Fin.ext h
        rcases moveDirs_cover hd a ⟨t, ht⟩ with h1 | h1
        · exact hl (Or.inl (hlt' ▸ h1))
        · exact hla (hlt' ▸ h1)
      have hst : interPoint x y s l = interPoint x y t l := by
        rcases hs with rfl | rfl
        · rfl
        · exact interPoint_succ_of_ne x y hlt
      rw [hst]
      have hc : Q.corner l ≤ interPoint x y t l ∧ interPoint x y t l < Q.corner l + Q.size := by
        rcases interPoint_apply x y t l with h | h <;> rw [h]
        · exact hxv l
        · exact hyv l
      refine ⟨min_le_left _ _, ?_⟩
      rcases min_cases (interPoint x y t l) (Q.corner l + Q.size - w) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        rw [h1] <;> omega

/-- **Grimmett–Marstrand.** In dimension at least three, above the critical point, a single slab
width gives a uniform positive lower bound for two-point connections inside every complete slab
of every integer cube. -/
theorem uniformCubeSlabConnectivity_of_criticalProbability_lt {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) : UniformCubeSlabConnectivity d p := by
  classical
  obtain ⟨m, hm, ρ, hρ, hbox⟩ := exists_slabBox_two_point (by omega) hp
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hp
  refine UniformCubeSlabConnectivity.of_large_cubes p hp0 (12 * m + 1) (22 * m + 1) (by omega)
    (ρ ^ d) (pow_pos hρ d) ?_
  intro Q hQ a k hfull x hx y hy
  set w := 12 * m + 1 with hw
  set A : ℕ → Set (Configuration d) := fun t => if ht : t < d then
    {ω | (openIn ω (slabBox (moveCorner Q a w k (moveDirs hd a ⟨t, ht⟩) (interPoint x y t))
      (moveDirs hd a ⟨t, ht⟩).1 (moveDirs hd a ⟨t, ht⟩).2 Q.size w)).Reachable
        (interPoint x y t) (interPoint x y (t + 1))} else Set.univ with hA
  have hA_prob : ∀ t ∈ Finset.range d, ρ ≤ (latticeBondLaw d p).real (A t) := by
    intro t htd
    have ht : t < d := Finset.mem_range.1 htd
    simp only [hA, ht, ↓reduceDIte]
    exact hbox _ _ _ (moveDirs_ne hd a ⟨t, ht⟩).1 Q.size hQ _
      (interPoint_mem_moveBox hd Q (by omega) hx hy ht (Or.inl rfl)) _
      (interPoint_mem_moveBox hd Q (by omega) hx hy ht (Or.inr rfl))
  have hAu : ∀ t, IsUpperSet (A t) := by
    intro t
    simp only [hA]
    split_ifs
    · exact isUpperSet_reachable_openIn _ _ _
    · exact isUpperSet_univ
  have hAm : ∀ t, MeasurableSet (A t) := by
    intro t
    simp only [hA]
    split_ifs
    · exact measurableSet_openIn_reachable _ _ _
    · exact MeasurableSet.univ
  have hharris := prod_le_latticeBondLaw_real_biInter p A hAu hAm (Finset.range d)
  have hprod : ρ ^ d ≤ ∏ t ∈ Finset.range d, (latticeBondLaw d p).real (A t) := by
    have hpow : ρ ^ d = ∏ _t ∈ Finset.range d, ρ := by rw [Finset.prod_const, Finset.card_range]
    rw [hpow]
    exact Finset.prod_le_prod (fun _ _ => hρ.le) hA_prob
  have hsub : (⋂ t ∈ Finset.range d, A t) ⊆
      {ω | (openIn ω (Q.slab a w k)).Reachable x y} := by
    intro ω hω
    have hstep : ∀ t ≤ d, (openIn ω (Q.slab a w k)).Reachable x (interPoint x y t) := by
      intro t
      induction t with
      | zero => intro _; rw [interPoint_zero]
      | succ t ih =>
        intro ht
        have ht' : t < d := by omega
        have hmem := Set.mem_iInter₂.1 hω t (Finset.mem_range.2 ht')
        simp only [hA, ht', ↓reduceDIte, Set.mem_setOf_eq] at hmem
        have hzv : interPoint x y t ∈ Q.vertices := by
          rw [IntegerCube.mem_vertices]
          intro l
          rcases interPoint_apply x y t l with h | h <;> rw [h]
          · exact (IntegerCube.mem_vertices Q x).1 hx.1 l
          · exact (IntegerCube.mem_vertices Q y).1 hy.1 l
        have hboxsub := slabBox_moveCorner_subset Q hfull
          ⟨(moveDirs_ne hd a ⟨t, ht'⟩).2.1, (moveDirs_ne hd a ⟨t, ht'⟩).2.2⟩
          (interPoint x y t) hzv
        exact (ih (by omega)).trans (openIn_reachable_mono_region hboxsub hmem)
    have := hstep d le_rfl
    rwa [interPoint_last] at this
  calc ρ ^ d ≤ _ := hprod
    _ ≤ _ := hharris
    _ ≤ _ := measureReal_mono hsub

end Rigidity.Percolation
