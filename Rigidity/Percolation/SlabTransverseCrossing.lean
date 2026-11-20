import Rigidity.Percolation.SlabRootSurvival
import Rigidity.Percolation.SlabLongRangeCrossing

/-!
# Transverse crossings of cube slabs

Every nonempty slab meets the two cube faces in each transverse direction.
Uniform slab two-point connectivity therefore implies a rooted transverse
crossing probability through positive association.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A nonempty slab meets both faces of the cube in every transverse direction. -/
theorem IntegerCube.exists_slab_face_points {d : ℕ} (Q : IntegerCube d)
    (j i : Fin d) (hij : i ≠ j) (width k : ℕ) {x : Vertex d}
    (hx : x ∈ Q.slab j width k) :
    (∃ y ∈ Q.slab j width k, y ∈ Q.lowerFace i) ∧
      ∃ y ∈ Q.slab j width k, y ∈ Q.upperFace i := by
  classical
  let a : Vertex d := Function.update x i (Q.corner i)
  let b : Vertex d := Function.update x i (Q.corner i + (Q.size : ℤ) - 1)
  have hsize : (0 : ℤ) < Q.size := by
    have hj := (Q.mem_vertices x).mp hx.1 j
    omega
  have haQ : a ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro t
    by_cases ht : t = i
    · subst t
      simp only [a, Function.update_self]
      omega
    · simpa only [a, Function.update_of_ne ht] using (Q.mem_vertices x).mp hx.1 t
  have hbQ : b ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro t
    by_cases ht : t = i
    · subst t
      simp only [b, Function.update_self]
      omega
    · simpa only [b, Function.update_of_ne ht] using (Q.mem_vertices x).mp hx.1 t
  have haj : a j = x j := Function.update_of_ne (Ne.symm hij) _ _
  have hbj : b j = x j := Function.update_of_ne (Ne.symm hij) _ _
  have ha : a ∈ Q.slab j width k := ⟨haQ, by simpa only [haj] using hx.2⟩
  have hb : b ∈ Q.slab j width k := ⟨hbQ, by simpa only [hbj] using hx.2⟩
  refine ⟨⟨a, ha, (Q.mem_lowerFace i a).mpr ⟨haQ, ?_⟩⟩,
    ⟨b, hb, (Q.mem_upperFace i b).mpr ⟨hbQ, ?_⟩⟩⟩
  · simp only [a, Function.update_self]
  · simp only [b, Function.update_self]
    omega

/-- The cube faces transverse to `j`, with unrestricted marks in direction `j`. -/
def IntegerCube.transverseLower {d : ℕ} (Q : IntegerCube d) (j : Fin d) :
    Fin d → Set (Vertex d) := fun i => if i = j then Set.univ else Q.lowerFace i

/-- The upper cube faces transverse to `j`, with unrestricted marks in direction `j`. -/
def IntegerCube.transverseUpper {d : ℕ} (Q : IntegerCube d) (j : Fin d) :
    Fin d → Set (Vertex d) := fun i => if i = j then Set.univ else Q.upperFace i

/-- Uniform two-point connectivity in a slab gives a rooted transverse
crossing probability of at least `ρ ^ (2 * d)`. -/
theorem IntegerCube.pow_le_slab_transverse_crossing {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k : ℕ) (p : unitInterval)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x : Vertex d) (hx : x ∈ Q.slab j width k)
    (hprob : ∀ y ∈ Q.slab j width k, ρ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω (Q.slab j width k)).Reachable x y}) :
    ρ ^ (2 * d) ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω (Q.slab j width k) (Q.transverseLower j)
        (Q.transverseUpper j) x} := by
  classical
  have hex : ∀ face : Fin d × Bool, ∃ y ∈ Q.slab j width k,
      y ∈ (if face.2 then Q.transverseUpper j face.1 else Q.transverseLower j face.1) := by
    intro ⟨i, b⟩
    by_cases hij : i = j
    · exact ⟨x, hx, by simp [IntegerCube.transverseUpper, IntegerCube.transverseLower, hij]⟩
    · obtain ⟨⟨a, ha, hal⟩, ⟨b', hb, hbu⟩⟩ := Q.exists_slab_face_points j i hij width k hx
      cases b with
      | false => exact ⟨a, ha, by simpa [IntegerCube.transverseLower, hij] using hal⟩
      | true => exact ⟨b', hb, by simpa [IntegerCube.transverseUpper, hij] using hbu⟩
  choose point hpointB hpointFace using hex
  exact pow_le_measureReal_crossingRoot_of_twoPoint p (Q.slab j width k)
    (Q.transverseLower j) (Q.transverseUpper j) x hx point hpointB hpointFace ρ hρ
    (fun face => hprob (point face) (hpointB face))

/-- Transverse crossing, together with connection to both faces in the slab
direction, gives a crossing component of the cube. -/
theorem IntegerCube.crossingRoot_of_transverse {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {ω : Configuration d} {z : Vertex d}
    (htrans : IsCrossingRoot ω Q.vertices (Q.transverseLower j) (Q.transverseUpper j) z)
    (hj : targetConnection Q.vertices (Q.lowerFace j) z ω ∧
      targetConnection Q.vertices (Q.upperFace j) z ω) :
    IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
      (fun i => ↑(Q.upperFace i)) z := by
  refine ⟨htrans.1, fun i => ?_⟩
  by_cases hij : i = j
  · subst i
    exact hj
  · simpa only [IntegerCube.transverseLower, IntegerCube.transverseUpper, if_neg hij] using
      htrans.2 i

/-- If a root connects both faces in the slab direction, failure of full
cube crossing implies that the root does not cross the transverse faces. -/
theorem IntegerCube.not_transverse_of_not_crossing {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {ω : Configuration d} {z : Vertex d}
    (hj : targetConnection Q.vertices (Q.lowerFace j) z ω ∧
      targetConnection Q.vertices (Q.upperFace j) z ω)
    (hfail : ¬ ∃ w, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
      (fun i => ↑(Q.upperFace i)) w) :
    ¬ IsCrossingRoot ω Q.vertices (Q.transverseLower j) (Q.transverseUpper j) z := by
  intro htrans
  exact hfail ⟨z, Q.crossingRoot_of_transverse j htrans hj⟩

/-- A connection between the two faces in the slab direction, without a full
crossing component, has geometrically small probability under a uniform slab
two-point bound. -/
theorem IntegerCube.measureReal_face_connection_without_crossing_le {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (A : Finset (Vertex d)) (hA : (↑A : Set (Vertex d)) ⊆ Q.slabPrefix j width k₀)
    (hL : (↑(Q.lowerFace j) : Set (Vertex d)) ⊆ A)
    (hR : (↑(Q.upperFace j) : Set (Vertex d)) ⊆
      Q.vertices \ Q.slabPrefix j width (k₀ + N))
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hprob : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ConnectsRegions ω Q.vertices
      (Q.lowerFace j) (Q.upperFace j) ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) z} ≤
      (A.card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N := by
  classical
  let E : Vertex d → Set (Configuration d) := fun z => {ω |
    targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
    ¬ IsCrossingRoot ω Q.vertices (Q.transverseLower j) (Q.transverseUpper j) z}
  have hcover : {ω | ConnectsRegions ω Q.vertices (Q.lowerFace j) (Q.upperFace j) ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) z} ⊆ ⋃ z ∈ A, E z := by
    rintro ω ⟨⟨z, hzQ, hzL, w, hwQ, hwR, hzw⟩, hfail⟩
    have hj : targetConnection Q.vertices (Q.lowerFace j) z ω ∧
        targetConnection Q.vertices (Q.upperFace j) z ω :=
      ⟨⟨z, hzQ, hzL, SimpleGraph.Reachable.refl z⟩, ⟨w, hwQ, hwR, hzw⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨z, hL hzL, ⟨w, hwQ, hR hwR, hzw⟩,
      Q.not_transverse_of_not_crossing j hj hfail⟩
  have hcross : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n),
      ρ ^ (2 * d) ≤ (latticeBondLaw d p).real {ω |
        IsCrossingRoot ω (Q.slab j width (k₀ + n))
          (Q.transverseLower j) (Q.transverseUpper j) y} := by
    intro n hn y hy
    exact Q.pow_le_slab_transverse_crossing j width (k₀ + n) p ρ hρ y hy
      (hprob n hn y hy)
  calc
    _ ≤ (latticeBondLaw d p).real (⋃ z ∈ A, E z) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ z ∈ A, (latticeBondLaw d p).real (E z) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ A, (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N := by
      apply Finset.sum_le_sum
      intro z hz
      exact Q.measureReal_escape_without_crossing_le j width k₀ N hwidth hsize
        z (hA hz) (Q.transverseLower j) (Q.transverseUpper j) p (ρ ^ (2 * d))
        (pow_le_one₀ hρ hρ₁) hcross
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The lower face lies in a nonempty initial prefix and the upper face lies
beyond any prefix ending inside the cube. -/
theorem IntegerCube.faces_separated_by_prefixes {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k₀ N : ℕ} (hstart : 0 < k₀ * width)
    (hend : (k₀ + N) * width < Q.size) :
    (↑(Q.lowerFace j) : Set (Vertex d)) ⊆ Q.slabPrefix j width k₀ ∧
    (↑(Q.upperFace j) : Set (Vertex d)) ⊆
      Q.vertices \ Q.slabPrefix j width (k₀ + N) := by
  constructor
  · intro x hx
    obtain ⟨hxQ, hface⟩ := (Q.mem_lowerFace j x).mp hx
    have hp : (0 : ℤ) < ((k₀ * width : ℕ) : ℤ) := by exact_mod_cast hstart
    exact ⟨hxQ, by omega⟩
  · intro x hx
    obtain ⟨hxQ, hface⟩ := (Q.mem_upperFace j x).mp hx
    have he : ((k₀ + N) * width : ℕ) < Q.size := hend
    have he' : (((k₀ + N) * width : ℕ) : ℤ) < Q.size := by exact_mod_cast he
    refine ⟨hxQ, ?_⟩
    intro hp
    have hp' := hp.2
    omega

/-- A face-crossing path fails to belong to a full cube-crossing component
with geometric probability under uniform slab two-point bounds. -/
theorem IntegerCube.measureReal_face_connection_without_crossing_le_of_slab {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hstart : 0 < k₀ * width) (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hprob : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ConnectsRegions ω Q.vertices
      (Q.lowerFace j) (Q.upperFace j) ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) z} ≤
      ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N := by
  obtain ⟨hL, hR⟩ := Q.faces_separated_by_prefixes j hstart (hsize N le_rfl)
  exact Q.measureReal_face_connection_without_crossing_le j width k₀ N hwidth hsize
    (Q.lowerFace j) hL (Set.Subset.refl _) hR p ρ hρ hρ₁ hprob

/-- Every slab whose first coordinate slice lies in the cube is nonempty. -/
theorem IntegerCube.exists_mem_slab {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size) :
    ∃ x, x ∈ Q.slab j width k := by
  classical
  let x : Vertex d := Function.update Q.corner j (Q.corner j + ((k * width : ℕ) : ℤ))
  have hsize' : ((k * width : ℕ) : ℤ) < (Q.size : ℤ) := by exact_mod_cast hsize
  have hwidth' : (0 : ℤ) < (width : ℤ) := by exact_mod_cast hwidth
  have hxj : x j = Q.corner j + ((k * width : ℕ) : ℤ) := by
    simp only [x, Function.update_self]
  have hxQ : x ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro i
    by_cases hij : i = j
    · subst i
      rw [hxj]
      have hk : (0 : ℤ) ≤ ((k * width : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      omega
    · have hi : x i = Q.corner i := Function.update_of_ne hij _ _
      rw [hi]
      constructor
      · exact le_rfl
      · have hk : (0 : ℤ) ≤ ((k * width : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
        omega
  refine ⟨x, hxQ, by rw [hxj], ?_⟩
  rw [hxj]
  push_cast
  nlinarith

/-- A uniform two-point bound in each perpendicular slab controls failure of
a cube face connection. -/
theorem IntegerCube.measureReal_no_face_connection_le_of_twoPoint {d : ℕ}
    (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j) (width : ℕ)
    (hwidth : 0 < width) (p : unitInterval) (ρ : ℝ)
    (hprob : ∀ k : Fin (Q.size / width), ∀ x ∈ Q.slab j width k,
      ∀ y ∈ Q.slab j width k, ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ ConnectsRegions ω Q.vertices
      (Q.lowerFace i) (Q.upperFace i)} ≤ (1 - ρ) ^ (Q.size / width) := by
  apply Q.measureReal_no_face_connection_le j i width p ρ
  intro k
  have hk : (k.val + 1) * width ≤ Q.size := by
    apply (Nat.le_div_iff_mul_le hwidth).mp
    exact k.isLt
  have hksize : k.val * width < Q.size := by nlinarith
  obtain ⟨x, hx⟩ := Q.exists_mem_slab j hwidth hksize
  obtain ⟨⟨a, ha, hal⟩, ⟨b, hb, hbu⟩⟩ := Q.exists_slab_face_points j i hij width k hx
  apply (hprob k a ha b hb).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  exact ⟨a, ha, hal, b, hb, hbu, hω⟩

/-- Uniform two-point bounds in perpendicular slab families give an explicit
upper bound for failure of a full crossing component in the cube. -/
theorem IntegerCube.measureReal_no_crossing_le_of_twoPoint_slabs {d : ℕ}
    (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j)
    (width width' k₀ N : ℕ) (hwidth : 0 < width) (hwidth' : 0 < width')
    (hstart : 0 < k₀ * width) (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hparallel : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y})
    (hperp : ∀ k : Fin (Q.size / width'), ∀ x ∈ Q.slab i width' k,
      ∀ y ∈ Q.slab i width' k, ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab i width' k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ ∃ z,
      IsCrossingRoot ω Q.vertices (fun t => ↑(Q.lowerFace t))
        (fun t => ↑(Q.upperFace t)) z} ≤
      (1 - ρ) ^ (Q.size / width') +
        ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N := by
  let F : Set (Configuration d) := {ω | ¬ ConnectsRegions ω Q.vertices
    (Q.lowerFace j) (Q.upperFace j)}
  let G : Set (Configuration d) := {ω | ConnectsRegions ω Q.vertices
    (Q.lowerFace j) (Q.upperFace j) ∧
      ¬ ∃ z, IsCrossingRoot ω Q.vertices (fun t => ↑(Q.lowerFace t))
        (fun t => ↑(Q.upperFace t)) z}
  have hcover : {ω | ¬ ∃ z, IsCrossingRoot ω Q.vertices (fun t => ↑(Q.lowerFace t))
      (fun t => ↑(Q.upperFace t)) z} ⊆ F ∪ G := by
    intro ω hω
    by_cases h : ConnectsRegions ω Q.vertices (Q.lowerFace j) (Q.upperFace j)
    · exact Or.inr ⟨h, hω⟩
    · exact Or.inl h
  calc
    _ ≤ (latticeBondLaw d p).real (F ∪ G) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ (latticeBondLaw d p).real F + (latticeBondLaw d p).real G := measureReal_union_le _ _
    _ ≤ _ := add_le_add
      (Q.measureReal_no_face_connection_le_of_twoPoint i j (Ne.symm hij) width' hwidth' p ρ hperp)
      (Q.measureReal_face_connection_without_crossing_le_of_slab j width k₀ N hwidth
        hstart hsize p ρ hρ hρ₁ hparallel)

end Rigidity.Percolation
