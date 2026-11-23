import Rigidity.Proofs.S3.Reflection
import Rigidity.Percolation.TriadicStopping
import Rigidity.Percolation.TriadicGoodCubes

/-!
# Signed permutations of the triadic cubes

A signed permutation `φ(x)ᵢ = sᵢ x_{π i}` of `ℤ^d` maps the triadic cube of scale `n` and index `j`
onto the triadic cube of scale `n` and index `φ(j)`, since the triadic cubes are centred at
`3ⁿ j` and symmetric about their centres. It commutes with the parent map (the parent index is
the nearest integer to `j/3`, which is odd in `j`), carries the children to the children (with the
digits reversed in the coordinates with a negative sign), and so preserves the influence relation,
the stable cubes, the good cubes of a well-connected family and the maximal stopping cubes. These
are the combinatorial steps of the invariance of the partition of Armstrong and Dario
(Proposition 2.1) under the symmetries of the lattice.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.Proofs.S3

variable {d : ℕ} (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)

theorem signedPermVertex_apply (x : Vertex d) (i : Fin d) :
    signedPermVertex π s x i = (s i : ℤ) * x (π i) := rfl

theorem units_int_eq_one_or (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

omit π s in
/-- A statement for all coordinates, reindexed by a permutation. -/
theorem forall_perm_iff (σ : Equiv.Perm (Fin d)) (P : Fin d → Prop) :
    (∀ i, P (σ i)) ↔ ∀ i, P i :=
  ⟨fun h i => by simpa only [Equiv.apply_symm_apply] using h (σ.symm i), fun h i => h (σ i)⟩

/-- The image of a triadic cube under a signed permutation. -/
def TriadicCube.signedPerm (Q : TriadicCube d) : TriadicCube d :=
  ⟨Q.scale, signedPermVertex π s Q.index⟩

@[simp] theorem TriadicCube.scale_signedPerm (Q : TriadicCube d) :
    (Q.signedPerm π s).scale = Q.scale := rfl

@[simp] theorem TriadicCube.side_signedPerm (Q : TriadicCube d) :
    (Q.signedPerm π s).side = Q.side := rfl

/-- The signed permutation of triadic cubes as an equivalence. -/
def TriadicCube.signedPermEquiv : TriadicCube d ≃ TriadicCube d where
  toFun Q := Q.signedPerm π s
  invFun R := ⟨R.scale, (signedPermVertex π s).symm R.index⟩
  left_inv Q := by
    apply TriadicCube.ext
    · rfl
    · exact (signedPermVertex π s).symm_apply_apply Q.index
  right_inv R := by
    apply TriadicCube.ext
    · rfl
    · exact (signedPermVertex π s).apply_symm_apply R.index

theorem TriadicCube.signedPermEquiv_apply (Q : TriadicCube d) :
    TriadicCube.signedPermEquiv π s Q = Q.signedPerm π s := rfl

theorem TriadicCube.signedPerm_surjective (R : TriadicCube d) :
    ∃ Q : TriadicCube d, Q.signedPerm π s = R :=
  ⟨(TriadicCube.signedPermEquiv π s).symm R, (TriadicCube.signedPermEquiv π s).apply_symm_apply R⟩

theorem TriadicCube.signedPerm_injective {Q R : TriadicCube d}
    (h : Q.signedPerm π s = R.signedPerm π s) : Q = R :=
  (TriadicCube.signedPermEquiv π s).injective h

/-- **Vertices of the image cube.** -/
theorem TriadicCube.signedPermVertex_mem_vertices_iff (Q : TriadicCube d) (x : Vertex d) :
    signedPermVertex π s x ∈ (Q.signedPerm π s).vertices ↔ x ∈ Q.vertices := by
  simp only [TriadicCube.vertices, Set.mem_setOf_eq, side_signedPerm]
  have h : ∀ i, |2 * (signedPermVertex π s x i - Q.side * (Q.signedPerm π s).index i)| =
      |2 * (x (π i) - Q.side * Q.index (π i))| := by
    intro i
    change |2 * ((s i : ℤ) * x (π i) - Q.side * ((s i : ℤ) * Q.index (π i)))| = _
    rw [show 2 * ((s i : ℤ) * x (π i) - Q.side * ((s i : ℤ) * Q.index (π i))) =
      (s i : ℤ) * (2 * (x (π i) - Q.side * Q.index (π i))) by ring, abs_mul, abs_units_int,
      one_mul]
  simp only [h]
  exact forall_perm_iff π (fun i => |2 * (x i - Q.side * Q.index i)| < Q.side)

theorem TriadicCube.mem_signedPerm_vertices_iff (Q : TriadicCube d) (y : Vertex d) :
    y ∈ (Q.signedPerm π s).vertices ↔ (signedPermVertex π s).symm y ∈ Q.vertices := by
  rw [← Q.signedPermVertex_mem_vertices_iff π s, Equiv.apply_symm_apply]

theorem TriadicCube.signedPerm_vertices_subset_iff (Q R : TriadicCube d) :
    (Q.signedPerm π s).vertices ⊆ (R.signedPerm π s).vertices ↔ Q.vertices ⊆ R.vertices := by
  constructor
  · intro h x hx
    rw [← R.signedPermVertex_mem_vertices_iff π s]
    exact h ((Q.signedPermVertex_mem_vertices_iff π s x).2 hx)
  · intro h y hy
    rw [Q.mem_signedPerm_vertices_iff] at hy
    rw [R.mem_signedPerm_vertices_iff]
    exact h hy

/-- The nearest integer to `j / 3` is odd in `j`. -/
theorem int_neg_add_one_ediv_three (j : ℤ) : (-j + 1) / 3 = -((j + 1) / 3) := by
  omega

/-- **Parents of image cubes.** -/
theorem TriadicCube.parent_signedPerm (Q : TriadicCube d) :
    (Q.signedPerm π s).parent = Q.parent.signedPerm π s := by
  apply TriadicCube.ext
  · rfl
  · funext i
    change ((s i : ℤ) * Q.index (π i) + 1) / 3 = (s i : ℤ) * ((Q.index (π i) + 1) / 3)
    rcases units_int_eq_one_or (s i) with h | h <;> rw [h]
    · simp
    · rw [neg_one_mul, neg_one_mul, int_neg_add_one_ediv_three]

/-- The digits of the image child: reversed in the coordinates with a negative sign. -/
def signedPermDigits : (Fin d → Fin 3) ≃ (Fin d → Fin 3) where
  toFun g i := if (s i : ℤ) = 1 then g (π i) else (g (π i)).rev
  invFun h j := if (s (π.symm j) : ℤ) = 1 then h (π.symm j) else (h (π.symm j)).rev
  left_inv g := by
    funext j
    simp only [Equiv.apply_symm_apply]
    split_ifs <;> simp
  right_inv h := by
    funext i
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> simp

/-- **Children of image cubes.** -/
theorem TriadicCube.child_signedPerm (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    (Q.signedPerm π s).child (signedPermDigits π s digits) = (Q.child digits).signedPerm π s := by
  apply TriadicCube.ext
  · rfl
  · funext i
    change 3 * ((s i : ℤ) * Q.index (π i)) +
        ((if (s i : ℤ) = 1 then digits (π i) else (digits (π i)).rev : Fin 3) : ℤ) - 1 =
      (s i : ℤ) * (3 * Q.index (π i) + (digits (π i) : ℤ) - 1)
    have h3 : ((digits (π i)).rev : ℤ) = 2 - (digits (π i) : ℤ) := by
      rw [Fin.val_rev]
      have := (digits (π i)).isLt
      omega
    rcases units_int_eq_one_or (s i) with h | h
    · rw [if_pos h, h]
      ring
    · rw [if_neg (by rw [h]; norm_num), h, h3]
      ring

/-- **Influence steps between image cubes.** -/
theorem TriadicCube.influenceStep_signedPerm_iff (Q R : TriadicCube d) :
    (Q.signedPerm π s).InfluenceStep (R.signedPerm π s) ↔ Q.InfluenceStep R := by
  unfold TriadicCube.InfluenceStep
  simp only [scale_signedPerm, parent_signedPerm]
  refine and_congr_right fun _ => ?_
  have hd : ∀ a b : Vertex d, (∀ i, |signedPermVertex π s a i - signedPermVertex π s b i| ≤ 1) ↔
      ∀ i, |a i - b i| ≤ 1 := by
    intro a b
    have h : ∀ i, |signedPermVertex π s a i - signedPermVertex π s b i| = |a (π i) - b (π i)| := by
      intro i
      rw [signedPermVertex_apply, signedPermVertex_apply, ← mul_sub, abs_mul, abs_units_int,
        one_mul]
    simp only [h]
    exact forall_perm_iff π (fun i => |a i - b i| ≤ 1)
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Q.mem_signedPerm_vertices_iff] at ha
    rw [R.parent.mem_signedPerm_vertices_iff] at hb
    refine ⟨_, ha, _, hb, ?_⟩
    rw [← hd]
    simpa only [Equiv.apply_symm_apply] using hab
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨_, (Q.signedPermVertex_mem_vertices_iff π s a).2 ha, _,
      (R.parent.signedPermVertex_mem_vertices_iff π s b).2 hb, (hd a b).2 hab⟩

/-- **Influence sets of image cubes.** -/
theorem TriadicCube.signedPerm_mem_influence_iff (Q R : TriadicCube d) :
    R.signedPerm π s ∈ (Q.signedPerm π s).influence ↔ R ∈ Q.influence := by
  unfold TriadicCube.influence
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have h' := Relation.ReflTransGen.lift (TriadicCube.signedPermEquiv π s).symm
      (fun a b (hab : a.InfluenceStep b) => by
        obtain ⟨a', rfl⟩ := TriadicCube.signedPerm_surjective π s a
        obtain ⟨b', rfl⟩ := TriadicCube.signedPerm_surjective π s b
        rw [influenceStep_signedPerm_iff] at hab
        change (TriadicCube.signedPermEquiv π s).symm (TriadicCube.signedPermEquiv π s a') |>.InfluenceStep
          ((TriadicCube.signedPermEquiv π s).symm (TriadicCube.signedPermEquiv π s b'))
        simpa only [Equiv.symm_apply_apply] using hab) _ _ h
    change Relation.ReflTransGen TriadicCube.InfluenceStep
      ((TriadicCube.signedPermEquiv π s).symm (TriadicCube.signedPermEquiv π s Q))
      ((TriadicCube.signedPermEquiv π s).symm (TriadicCube.signedPermEquiv π s R)) at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    exact Relation.ReflTransGen.lift (fun Q => Q.signedPerm π s)
      (fun a b hab => (influenceStep_signedPerm_iff π s a b).2 hab) _ _ h

variable {π s}

/-- **Stable cubes of image families.** -/
theorem TriadicCube.signedPerm_mem_stableGood_iff {G G' : Set (TriadicCube d)}
    (hG : ∀ Q : TriadicCube d, Q.signedPerm π s ∈ G' ↔ Q ∈ G) (Q : TriadicCube d) :
    Q.signedPerm π s ∈ stableGood G' ↔ Q ∈ stableGood G := by
  unfold TriadicCube.stableGood
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h R hR
    rw [← hG]
    exact h ((signedPerm_mem_influence_iff π s Q R).2 hR)
  · intro h R' hR'
    obtain ⟨R, rfl⟩ := TriadicCube.signedPerm_surjective π s R'
    rw [hG]
    exact h ((signedPerm_mem_influence_iff π s Q R).1 hR')

/-- **Good cubes of image families.** -/
theorem TriadicCube.signedPerm_mem_goodOfWellConnected_iff {W W' : Set (TriadicCube d)}
    (hW : ∀ Q : TriadicCube d, Q.signedPerm π s ∈ W' ↔ Q ∈ W) (Q : TriadicCube d) :
    Q.signedPerm π s ∈ goodOfWellConnected W' ↔ Q ∈ goodOfWellConnected W := by
  unfold TriadicCube.goodOfWellConnected
  simp only [Set.mem_setOf_eq, scale_signedPerm, hW]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h digits
    have := h (signedPermDigits π s digits)
    rwa [child_signedPerm, hW] at this
  · intro h digits'
    obtain ⟨digits, rfl⟩ := (signedPermDigits π s).surjective digits'
    rw [child_signedPerm, hW]
    exact h digits

/-- **Stopping cubes of image families.** -/
theorem TriadicCube.signedPerm_isStopping_iff {G G' : Set (TriadicCube d)}
    (hG : ∀ Q : TriadicCube d, Q.signedPerm π s ∈ G' ↔ Q ∈ G) (Q : TriadicCube d) :
    (Q.signedPerm π s).IsStopping G' ↔ Q.IsStopping G := by
  unfold TriadicCube.IsStopping
  rw [signedPerm_mem_stableGood_iff hG, scale_signedPerm]
  refine and_congr_right fun _ => or_congr_right ?_
  constructor
  · rintro ⟨digits', hd⟩
    obtain ⟨digits, rfl⟩ := (signedPermDigits π s).surjective digits'
    rw [child_signedPerm, signedPerm_mem_stableGood_iff hG] at hd
    exact ⟨digits, hd⟩
  · rintro ⟨digits, hd⟩
    refine ⟨signedPermDigits π s digits, ?_⟩
    rwa [child_signedPerm, signedPerm_mem_stableGood_iff hG]

/-- **Maximal stopping cubes of image families.** -/
theorem TriadicCube.signedPerm_isMaximalStopping_iff {G G' : Set (TriadicCube d)}
    (hG : ∀ Q : TriadicCube d, Q.signedPerm π s ∈ G' ↔ Q ∈ G) (Q : TriadicCube d) :
    (Q.signedPerm π s).IsMaximalStopping G' ↔ Q.IsMaximalStopping G := by
  unfold TriadicCube.IsMaximalStopping
  rw [signedPerm_isStopping_iff hG]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h R hR hQR
    have := h (R.signedPerm π s) ((signedPerm_isStopping_iff hG R).2 hR)
      ((signedPerm_vertices_subset_iff π s Q R).2 hQR)
    simpa only [scale_signedPerm] using this
  · intro h R' hR' hQR'
    obtain ⟨R, rfl⟩ := TriadicCube.signedPerm_surjective π s R'
    rw [signedPerm_isStopping_iff hG] at hR'
    rw [signedPerm_vertices_subset_iff] at hQR'
    simpa only [scale_signedPerm] using h R hR' hQR'

end Rigidity.Percolation
