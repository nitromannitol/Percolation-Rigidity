import Rigidity.Percolation.BondFaceSeeds

/-!
# Face seed trials

A trial region consists of a face contact and its outward seed. Distinct
transverse cells give disjoint trial regions and independent bond tests.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- The trial region includes the face contact and the seed beyond it. -/
def faceSeedTrial {d : ℕ} (k : ℕ) (j : Fin d) (n : ℤ) (x : Vertex d) :
    Set (Vertex d) := insert x (faceSeedCell k j n (seedGridIndex k x))

/-- A face seed is exactly its side-`k` lattice rectangle. -/
theorem faceSeedCell_eq_rectangle {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (a : Vertex d) :
    faceSeedCell k j n a =
      latticeRectangle (fun i => if i = j then n + 1 else (k : ℤ) * a i)
        (fun i => (if i = j then n + 1 else (k : ℤ) * a i) + k) := by
  apply Set.Subset.antisymm (faceSeedCell_subset_rectangle hk j n a)
  intro x hx
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_, ?_⟩
  · simpa only [↓reduceIte] using (hx j).1
  · simpa only [↓reduceIte] using (hx j).2
  · intro i hi
    have h := hx i
    simp only [if_neg hi] at h
    change x i / (k : ℤ) = a i
    apply (Int.ediv_eq_iff_of_pos hk').2
    simpa only [mul_comm] using h

/-- A fully open trial contains a fully open seed beyond the face. -/
theorem fullyOpenRegion_faceSeed_of_trial {d k : ℕ} (j : Fin d) (n : ℤ)
    (x : Vertex d) {ω : Configuration d}
    (hopen : ω ∈ fullyOpenRegion (faceSeedTrial k j n x)) :
    ω ∈ fullyOpenRegion (faceSeedCell k j n (seedGridIndex k x)) := by
  intro e he
  apply hopen e
  intro y hy
  exact Set.mem_insert_of_mem x (he y hy)

/-- A fully open trial connects its face contact to the seed immediately
beyond the face. -/
theorem faceSeedTrial_reachable_step {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (x : Vertex d) (hx : x j = n) {ω : Configuration d}
    (hopen : ω ∈ fullyOpenRegion (faceSeedTrial k j n x)) :
    (openIn ω (faceSeedTrial k j n x)).Reachable x
      (fun i => if i = j then x i + 1 else x i) := by
  apply reachable_openIn_of_fullyOpenRegion hopen
  apply SimpleGraph.Adj.reachable
  refine ⟨?_, Set.mem_insert x _, Set.mem_insert_of_mem _ ?_⟩
  · simpa only [openGraph_allOpen] using face_contact_step_adj j x
  · exact face_contact_step_mem_seed hk j n x hx

/-- Trial regions at contacts in different grid cells are disjoint. -/
theorem disjoint_faceSeedTrial {d k : ℕ} (j : Fin d) (n : ℤ)
    {x y : Vertex d} (hx : x j = n) (hy : y j = n)
    (hxy : seedGridIndex k x ≠ seedGridIndex k y) :
    Disjoint (faceSeedTrial k j n x) (faceSeedTrial k j n y) := by
  have hnormal : seedGridIndex k x j = seedGridIndex k y j := by
    simp only [seedGridIndex, hx, hy]
  have hseed := disjoint_faceSeedCell_of_same_normal (k := k) j n hnormal hxy
  apply Set.disjoint_left.mpr
  intro z hz hw
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · rcases Set.mem_insert_iff.mp hw with heq | hw
    · subst y
      exact hxy rfl
    · have := hw.1
      omega
  · rcases Set.mem_insert_iff.mp hw with rfl | hw
    · have := hz.1
      omega
    · exact Set.disjoint_left.mp hseed hz hw

/-- Every trial region at positive width is finite. -/
theorem finite_faceSeedTrial {d k : ℕ} (hk : 0 < k) (j : Fin d) (n : ℤ)
    (x : Vertex d) : (faceSeedTrial k j n x).Finite :=
  (finite_faceSeedCell hk j n (seedGridIndex k x)).insert x

/-- Each trial region contains at most `k ^ d + 1` vertices. -/
theorem card_faceSeedTrial_le {d k : ℕ} (hk : 0 < k) (j : Fin d) (n : ℤ)
    (x : Vertex d) : (finite_faceSeedTrial hk j n x).toFinset.card ≤ k ^ d + 1 := by
  let a := seedGridIndex k x
  let lo : Vertex d := fun i => if i = j then n + 1 else (k : ℤ) * a i
  have hcard := card_latticeRectangle_le lo (fun i => lo i + k) k (by
    intro i
    simp only [add_sub_cancel_left, Int.toNat_natCast, le_refl])
  have hseed : (finite_faceSeedCell hk j n a).toFinset.card ≤ k ^ d := by
    apply le_trans (Finset.card_le_card ?_) hcard
    intro y hy
    simpa only [Set.Finite.mem_toFinset] using
      (faceSeedCell_subset_rectangle hk j n a (by simpa only [Set.Finite.mem_toFinset] using hy))
  calc
    (finite_faceSeedTrial hk j n x).toFinset.card ≤
        (finite_faceSeedCell hk j n a).toFinset.card + 1 := by
      simpa only [faceSeedTrial, Set.Finite.toFinset_insert] using
        (Finset.card_insert_le x (finite_faceSeedCell hk j n a).toFinset)
    _ ≤ k ^ d + 1 := Nat.add_le_add_right hseed 1

/-- The internal bond count of a trial region is uniformly bounded. -/
theorem card_localBonds_faceSeedTrial_le {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (x : Vertex d) :
    (finite_localBonds (finite_faceSeedTrial hk j n x)).toFinset.card ≤ (k ^ d + 1) ^ 2 :=
  card_localBonds_le_of_card_le (finite_faceSeedTrial hk j n x)
    (card_faceSeedTrial_le hk j n x)

/-- The chance that all fixed disjoint face seed trials fail decays geometrically. -/
theorem measureReal_no_faceSeedTrial_le {d k : ℕ} {ι : Type*} (hk : 0 < k)
    (p : unitInterval) (j : Fin d) (n : ℤ) (x : ι → Vertex d)
    (hface : ∀ i, x i j = n) (hinj : Function.Injective (fun i => seedGridIndex k (x i)))
    (s : Finset ι) :
    (latticeBondLaw d p).real
      (⋂ i ∈ s, (fullyOpenRegion (faceSeedTrial k j n (x i)))ᶜ) ≤
        (1 - (p : ℝ) ^ ((k ^ d + 1) ^ 2)) ^ s.card := by
  apply measureReal_no_fullyOpenRegion_le p (fun i => faceSeedTrial k j n (x i))
    (fun i l hil => disjoint_faceSeedTrial j n (hface i) (hface l) (fun h => hil (hinj h)))
    ((p : ℝ) ^ ((k ^ d + 1) ^ 2))
  intro i
  exact latticeBondLaw_real_fullyOpenRegion_lower p _ (finite_faceSeedTrial hk j n (x i)) _
    (card_localBonds_faceSeedTrial_le hk j n (x i))

end Rigidity.Percolation
