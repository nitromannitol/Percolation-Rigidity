import Rigidity.Percolation.ConditionalFaceSeedSource

/-!
# Steering an outward pad toward a neighboring block

Choosing transverse directions opposite to the displacement of a seed keeps
its next outward pad inside the neighboring block.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- The outward pad whose transverse signs point toward the coordinate axes. -/
def steeredFacePad {d : ℕ} (M n : ℕ) (i : Fin d) (b : Vertex d) : Set (Vertex d) :=
  {x | (n : ℤ) + 1 ≤ x i ∧ x i ≤ (n : ℤ) + (2 * M + 1 : ℕ) ∧
    ∀ j, j ≠ i → if 0 ≤ b j then -(n : ℤ) ≤ x j ∧ x j ≤ 0
      else 0 ≤ x j ∧ x j ≤ n}

/-- Steering opposite each transverse displacement keeps the translated pad
inside the block centered two block radii along the chosen coordinate. -/
theorem steeredFacePad_subset_neighborBlock {d : ℕ} (M n : ℕ) (i : Fin d)
    (b : Vertex d) (hb : ∀ j, |b j| ≤ ((M + n + 1 : ℕ) : ℤ))
    (hbi : (M : ℤ) ≤ b i) :
    ∀ x ∈ steeredFacePad M n i b, ∀ j,
      |b j + x j - (if j = i then (2 * (M + n + 1 : ℕ) : ℤ) else 0)| ≤
        ((M + n + 1 : ℕ) : ℤ) := by
  intro x hx j
  have hb' := abs_le.mp (hb j)
  rw [abs_le]
  by_cases hji : j = i
  · subst j
    have hlower := hx.1
    have hupper := hx.2.1
    simp only [↓reduceIte] 
    push_cast at hlower hupper hb' ⊢
    constructor <;> omega
  · have htrans := hx.2.2 j hji
    simp only [if_neg hji, sub_zero]
    by_cases hbj : 0 ≤ b j
    · simp only [hbj, ↓reduceIte] at htrans
      constructor <;> push_cast at * <;> omega
    · simp only [hbj, ↓reduceIte] at htrans
      constructor <;> push_cast at * <;> omega

/-- The coordinate signs that reverse positive transverse displacements. -/
def steeringSigns {d : ℕ} (i : Fin d) (b : Vertex d) : Fin d → Bool :=
  fun j => decide (j ≠ i ∧ 0 ≤ b j)

/-- Steering preserves the normal coordinate. -/
theorem coordinateSignFlip_steeringSigns_normal {d : ℕ} (i : Fin d)
    (b x : Vertex d) : coordinateSignFlip (steeringSigns i b) x i = x i := by
  change (if steeringSigns i b i then -(x i) else x i) = x i
  have hs : steeringSigns i b i = false := by simp [steeringSigns]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]

/-- Flipping the appropriate transverse coordinates maps the positive
outward pad to the pad steered toward the coordinate axes. -/
theorem mem_steeredFacePad_coordinateSignFlip_iff {d : ℕ} (M n : ℕ)
    (i : Fin d) (b x : Vertex d) :
    coordinateSignFlip (steeringSigns i b) x ∈ steeredFacePad M n i b ↔
      x ∈ orthantFaceSeedPad n (2 * M + 1) i := by
  change ((n : ℤ) + 1 ≤ coordinateSignFlip (steeringSigns i b) x i ∧
    coordinateSignFlip (steeringSigns i b) x i ≤ (n : ℤ) + (2 * M + 1 : ℕ) ∧
    ∀ j, j ≠ i → if 0 ≤ b j then -(n : ℤ) ≤ coordinateSignFlip (steeringSigns i b) x j ∧
      coordinateSignFlip (steeringSigns i b) x j ≤ 0 else
        0 ≤ coordinateSignFlip (steeringSigns i b) x j ∧
          coordinateSignFlip (steeringSigns i b) x j ≤ n) ↔ _
  rw [coordinateSignFlip_steeringSigns_normal]
  have hnorm : x i < (n : ℤ) + 1 + ((2 * M + 1 : ℕ) : ℤ) ↔
      x i ≤ (n : ℤ) + ((2 * M + 1 : ℕ) : ℤ) := by omega
  have htrans (j : Fin d) (hj : j ≠ i) :
      (if 0 ≤ b j then -(n : ℤ) ≤ coordinateSignFlip (steeringSigns i b) x j ∧
        coordinateSignFlip (steeringSigns i b) x j ≤ 0 else
          0 ≤ coordinateSignFlip (steeringSigns i b) x j ∧
            coordinateSignFlip (steeringSigns i b) x j ≤ n) ↔
        0 ≤ x j ∧ x j ≤ n := by
    change (if 0 ≤ b j then -(n : ℤ) ≤ (if steeringSigns i b j then -(x j) else x j) ∧
      (if steeringSigns i b j then -(x j) else x j) ≤ 0 else
        0 ≤ (if steeringSigns i b j then -(x j) else x j) ∧
          (if steeringSigns i b j then -(x j) else x j) ≤ n) ↔ _
    by_cases hb : 0 ≤ b j
    · have hs : steeringSigns i b j = true := by simp [steeringSigns, hj, hb]
      simp only [hb, ↓reduceIte, hs]
      omega
    · have hs : steeringSigns i b j = false := by simp [steeringSigns, hb]
      simp only [hb, ↓reduceIte, hs, Bool.false_eq_true]
  change ((n : ℤ) + 1 ≤ x i ∧ x i ≤ (n : ℤ) + ((2 * M + 1 : ℕ) : ℤ) ∧ _) ↔
    ((n : ℤ) + 1 ≤ x i ∧ x i < (n : ℤ) + 1 + ((2 * M + 1 : ℕ) : ℤ) ∧ _)
  constructor
  · rintro ⟨hl, hu, hh⟩
    exact ⟨hl, hnorm.mpr hu, fun j hj => (htrans j hj).mp (hh j hj)⟩
  · rintro ⟨hl, hu, hh⟩
    exact ⟨hl, hnorm.mp hu, fun j hj => (htrans j hj).mpr (hh j hj)⟩

/-- The steered pad is the image of the positive pad under coordinate sign
reversal. -/
theorem image_orthantFaceSeedPad_coordinateSignFlip {d : ℕ} (M n : ℕ)
    (i : Fin d) (b : Vertex d) :
    coordinateSignFlip (steeringSigns i b) '' orthantFaceSeedPad n (2 * M + 1) i =
      steeredFacePad M n i b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_steeredFacePad_coordinateSignFlip_iff M n i b y).mpr hy
  · intro hx
    refine ⟨(coordinateSignFlip (steeringSigns i b)).symm x, ?_, Equiv.apply_symm_apply _ _⟩
    apply (mem_steeredFacePad_coordinateSignFlip_iff M n i b _).mp
    rwa [Equiv.apply_symm_apply]

/-- A centered seed inside a positive outward pad has its center exactly one
block radius along the normal direction and at most that radius transversely. -/
theorem center_of_seed_subset_orthantFaceSeedPad {d : ℕ} (M n : ℕ) (i : Fin d)
    (b : Vertex d)
    (hsub : (fun z : Vertex d => z + b) '' centeredBondCube M ⊆
      orthantFaceSeedPad n (2 * M + 1) i) :
    b i = ((M + n + 1 : ℕ) : ℤ) ∧
      ∀ j, j ≠ i → (M : ℤ) ≤ b j ∧ b j ≤ (n : ℤ) - M := by
  let v : Fin d → ℤ := fun j => if j = i then (M : ℤ) else 0
  have hv : v ∈ centeredBondCube M := by
    apply (mem_centeredBondCube M v).mpr
    intro j
    dsimp only [v]
    split_ifs <;> simp only [abs_of_nonneg (Int.natCast_nonneg _), abs_zero] <;> omega
  have hnv : -v ∈ centeredBondCube M := by
    apply (mem_centeredBondCube M _).mpr
    intro j
    simpa only [Pi.neg_apply, abs_neg] using (mem_centeredBondCube M v).mp hv j
  have hplus := hsub ⟨v, hv, rfl⟩
  have hminus := hsub ⟨-v, hnv, rfl⟩
  have hi₁ := hplus.1
  have hi₂ := hminus.1
  have hi₃ := hplus.2.1
  have hi₄ := hminus.2.1
  simp only [Pi.add_apply, Pi.neg_apply, v, ↓reduceIte, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] at hi₁ hi₂ hi₃ hi₄ ⊢
  constructor
  · omega
  · intro j hj
    let w : Vertex d := fun k => if k = j then (M : ℤ) else 0
    have hw : w ∈ centeredBondCube M := by
      apply (mem_centeredBondCube M w).mpr
      intro k
      dsimp only [w]
      split_ifs <;> simp only [abs_of_nonneg (Int.natCast_nonneg _), abs_zero] <;> omega
    have hnw : -w ∈ centeredBondCube M := by
      apply (mem_centeredBondCube M _).mpr
      intro k
      simpa only [Pi.neg_apply, abs_neg] using (mem_centeredBondCube M w).mp hw k
    have hwplus := (hsub ⟨w, hw, rfl⟩).2.2 j hj
    have hwminus := (hsub ⟨-w, hnw, rfl⟩).2.2 j hj
    simp only [Pi.add_apply, Pi.neg_apply, w, ↓reduceIte] at hwplus hwminus
    omega

end Rigidity.Percolation
