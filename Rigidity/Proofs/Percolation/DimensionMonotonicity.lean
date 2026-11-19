import Rigidity.Proofs.Percolation.ClusterComparison

/-!
# Percolation in sublattices

A lower-dimensional coordinate lattice embeds as an induced subgraph of a higher-dimensional
lattice, so its percolation probability is no larger.
-/

open MeasureTheory

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation _root_.Percolation.Literature

/-- Extend an integer vector by zeros in the additional coordinates. -/
def extendCoordinates {m n : ℕ} (x : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then x ⟨i.val, h⟩ else 0

/-- Restriction to the original coordinates recovers the vector. -/
theorem extendCoordinates_cast {m n : ℕ} (h : m ≤ n) (x : Fin m → ℤ) (i : Fin m) :
    extendCoordinates (n := n) x (Fin.castLE h i) = x i := by
  simp [extendCoordinates]

/-- Extension by zeros is injective. -/
theorem extendCoordinates_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (extendCoordinates (m := m) (n := n)) := by
  intro x y hxy
  funext i
  have := congrFun hxy (Fin.castLE h i)
  simpa only [extendCoordinates_cast] using this

/-- Extension by zeros preserves sums. -/
theorem extendCoordinates_add {m n : ℕ} (x y : Fin m → ℤ) :
    extendCoordinates (n := n) (x + y) = extendCoordinates x + extendCoordinates y := by
  funext i
  simp only [extendCoordinates, Pi.add_apply]
  split_ifs <;> simp

/-- Extension by zeros preserves the zero vector. -/
theorem extendCoordinates_zero {m n : ℕ} :
    extendCoordinates (n := n) (0 : Fin m → ℤ) = 0 := by
  funext i
  simp [extendCoordinates]

/-- Extension by zeros sends coordinate vectors to their corresponding coordinate vectors. -/
theorem extendCoordinates_single {m n : ℕ} (h : m ≤ n) (i : Fin m) :
    extendCoordinates (n := n) (Pi.single i (1 : ℤ)) = Pi.single (Fin.castLE h i) 1 := by
  classical
  funext j
  by_cases hj : j.val < m
  · have hj' : (⟨j.val, hj⟩ : Fin m) = i ↔ j = Fin.castLE h i := by
      constructor
      · intro heq
        apply Fin.ext
        have hv := congrArg (fun a : Fin m => a.val) heq
        exact hv
      · intro heq
        apply Fin.ext
        have hv := congrArg (fun a : Fin n => a.val) heq
        exact hv
    simp only [extendCoordinates, dif_pos hj, Pi.single_apply]
    split_ifs <;> simp_all
  · have hne : j ≠ Fin.castLE h i := by
      intro heq
      apply hj
      rw [heq]
      exact i.isLt
    simp [extendCoordinates, hj, hne]

/-- The coordinate embedding identifies the lower lattice with an induced subgraph. -/
theorem zdGraph_comap_extendCoordinates {m n : ℕ} (h : m ≤ n) :
    (LatticeModels.zdGraph n).comap (extendCoordinates (m := m) (n := n)) =
      LatticeModels.zdGraph m := by
  ext x y
  rw [SimpleGraph.comap_adj, LatticeModels.zdGraph_adj_iff, LatticeModels.zdGraph_adj_iff]
  constructor
  · rintro ⟨j, hj | hj⟩
    · have hjm : j.val < m := by
        by_contra hjm
        have he := congrFun hj j
        simp [extendCoordinates, hjm] at he
      let i : Fin m := ⟨j.val, hjm⟩
      have hij : Fin.castLE h i = j := Fin.ext rfl
      refine ⟨i, Or.inl ?_⟩
      apply extendCoordinates_injective h
      rw [extendCoordinates_add, extendCoordinates_single h i, hij]
      exact hj
    · have hjm : j.val < m := by
        by_contra hjm
        have he := congrFun hj j
        simp [extendCoordinates, hjm] at he
      let i : Fin m := ⟨j.val, hjm⟩
      have hij : Fin.castLE h i = j := Fin.ext rfl
      refine ⟨i, Or.inr ?_⟩
      apply extendCoordinates_injective h
      rw [extendCoordinates_add, extendCoordinates_single h i, hij]
      exact hj
  · rintro ⟨i, hi | hi⟩
    · refine ⟨Fin.castLE h i, Or.inl ?_⟩
      rw [hi, extendCoordinates_add, extendCoordinates_single]
    · refine ⟨Fin.castLE h i, Or.inr ?_⟩
      rw [hi, extendCoordinates_add, extendCoordinates_single]

/-- The percolation probability increases when coordinates are added. -/
theorem theta_le_of_le_dimension {m n : ℕ} (h : m ≤ n) (p : unitInterval) :
    LatticeProb.Percolation.theta m p ≤ LatticeProb.Percolation.theta n p := by
  have ht := theta_comap_le (LatticeModels.zdGraph n) (extendCoordinates_injective h)
    (0 : Fin m → ℤ) p
  rw [zdGraph_comap_extendCoordinates h, extendCoordinates_zero, ← theta_eq, ← theta_eq] at ht
  exact ht

/-- Critical probabilities decrease when coordinates are added. -/
theorem criticalProbability_antitone {m n : ℕ} [NeZero m] [NeZero n] (h : m ≤ n) :
    criticalProbability n ≤ criticalProbability m := by
  apply (le_criticalProbability_iff (d := m) (criticalProbability n)).mpr
  intro p hp
  exact criticalProbability_le p (hp.trans_le (theta_le_of_le_dimension h p))

end Rigidity.Percolation
