import Rigidity.Percolation.BondSeedGrid

/-!
# Seeds beyond a lattice face

Each contact on a coordinate face determines a finite seed region immediately
beyond the face. Contacts in distinct grid cells determine disjoint regions.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A seed region beyond the face `x j = n`, indexed by its transverse cell. -/
def faceSeedCell {d : ℕ} (k : ℕ) (j : Fin d) (n : ℤ) (a : Vertex d) :
    Set (Vertex d) :=
  {y | n + 1 ≤ y j ∧ y j < n + 1 + k ∧
    ∀ i, i ≠ j → seedGridIndex k y i = a i}

/-- Moving one step outward from a face contact enters its seed region. -/
theorem face_contact_step_mem_seed {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (x : Vertex d) (hx : x j = n) :
    (fun i => if i = j then x i + 1 else x i) ∈
      faceSeedCell k j n (seedGridIndex k x) := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  change n + 1 ≤ (if j = j then x j + 1 else x j) ∧
    (if j = j then x j + 1 else x j) < n + 1 + k ∧
    ∀ i, i ≠ j → (if i = j then x i + 1 else x i) / (k : ℤ) = x i / k
  simp only [↓reduceIte, hx]
  refine ⟨le_rfl, ?_, ?_⟩
  · omega
  · intro i hi
    simp only [if_neg hi]

/-- The outward step from a face contact is a nearest-neighbor step. -/
theorem face_contact_step_adj {d : ℕ} (j : Fin d) (x : Vertex d) :
    (nearestNeighborGraph d).Adj x (fun i => if i = j then x i + 1 else x i) := by
  refine ⟨j, Or.inl ?_⟩
  funext i
  by_cases hi : i = j
  · subst i
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same, ↓reduceIte]
  · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hi, add_zero, if_neg hi]

/-- Seed regions with distinct transverse indices are disjoint. -/
theorem disjoint_faceSeedCell {d k : ℕ} (j : Fin d) (n : ℤ)
    {a b : Vertex d} (h : ∃ i, i ≠ j ∧ a i ≠ b i) :
    Disjoint (faceSeedCell k j n a) (faceSeedCell k j n b) := by
  obtain ⟨i, hij, hab⟩ := h
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab ((hx.2.2 i hij).symm.trans (hy.2.2 i hij))

/-- For indices with the same normal coordinate, distinct cells produce
 disjoint face seed regions. -/
theorem disjoint_faceSeedCell_of_same_normal {d k : ℕ} (j : Fin d) (n : ℤ)
    {a b : Vertex d} (hj : a j = b j) (hab : a ≠ b) :
    Disjoint (faceSeedCell k j n a) (faceSeedCell k j n b) := by
  apply disjoint_faceSeedCell j n
  by_contra h
  apply hab
  funext i
  by_cases hi : i = j
  · simpa only [hi] using hj
  · by_contra hne
    exact h ⟨i, hi, hne⟩

/-- Each face seed lies inside a side-`k` lattice rectangle. -/
theorem faceSeedCell_subset_rectangle {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (a : Vertex d) :
    faceSeedCell k j n a ⊆
      latticeRectangle (fun i => if i = j then n + 1 else (k : ℤ) * a i)
        (fun i => (if i = j then n + 1 else (k : ℤ) * a i) + k) := by
  intro x hx i
  by_cases hij : i = j
  · subst i
    simpa only [if_pos rfl] using ⟨hx.1, hx.2.1⟩
  · have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    have heq : x i / (k : ℤ) = a i := hx.2.2 i hij
    simp only [if_neg hij]
    exact ⟨by simpa only [heq] using (Int.mul_ediv_self_le (x := x i) (ne_of_gt hk')),
      by simpa only [heq] using (Int.lt_mul_ediv_self_add (x := x i) hk')⟩

/-- Every positive-width face seed is finite. -/
theorem finite_faceSeedCell {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (a : Vertex d) : (faceSeedCell k j n a).Finite :=
  (finite_latticeRectangle _ _).subset (faceSeedCell_subset_rectangle hk j n a)

/-- The number of internal bonds of a face seed is uniformly bounded. -/
theorem card_localBonds_faceSeedCell_le {d k : ℕ} (hk : 0 < k) (j : Fin d)
    (n : ℤ) (a : Vertex d) :
    (finite_localBonds (finite_faceSeedCell hk j n a)).toFinset.card ≤ (k ^ d) ^ 2 := by
  have hcard := card_latticeRectangle_le
    (fun i => if i = j then n + 1 else (k : ℤ) * a i)
    (fun i => (if i = j then n + 1 else (k : ℤ) * a i) + k) k (by
      intro i
      simp only [add_sub_cancel_left, Int.toNat_natCast, le_refl])
  apply card_localBonds_le_of_card_le (finite_faceSeedCell hk j n a)
  apply le_trans (Finset.card_le_card ?_) hcard
  intro x hx
  simpa only [Set.Finite.mem_toFinset] using
    (faceSeedCell_subset_rectangle hk j n a (by simpa only [Set.Finite.mem_toFinset] using hx))

end Rigidity.Percolation
