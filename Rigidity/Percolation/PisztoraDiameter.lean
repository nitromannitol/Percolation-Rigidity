import Rigidity.Percolation.CrossingRadiusAdapter

/-!
# Coordinate diameter and lattice radius

An ℓ¹-radius threshold implies a coordinate-diameter threshold, with the
dimension-dependent factor needed to compare lattice box estimates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- If a path reaches ℓ¹-distance greater than `N / 10` from every center,
then its coordinate diameter exceeds `N / (10 * d)`. -/
theorem exists_coordinate_diameter_of_l1_radius {d n : ℕ} (hd : 0 < d)
    (N : ℕ) (γ : Fin (n + 1) → Vertex d)
    (h : ∀ z : Vertex d, ∃ i : Fin (n + 1),
      (N : ℤ) < 10 * ∑ k, |γ i k - z k|) :
    ∃ (i j : Fin (n + 1)) (k : Fin d),
      (N : ℤ) < 10 * (d : ℤ) * |γ i k - γ j k| := by
  obtain ⟨i, hi⟩ := h (γ 0)
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hsum : ∑ k : Fin d, (N : ℤ) <
      ∑ k : Fin d, (10 * (d : ℤ) * |γ i k - γ 0 k|) := by
    have hm := mul_lt_mul_of_pos_left hi hd'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    nlinarith
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_of_sum_lt hsum
  exact ⟨i, 0, k, hk⟩

/-- A coordinate-diameter crossing estimate at scale `r + 1` controls the
event defined by ℓ¹ radius whenever `10 * d * r ≤ N`. -/
theorem HasCrossingComponentConnectingPaths.of_coordinate_diameter {d : ℕ}
    (hd : 0 < d) {ω : Configuration d} {B : Set (Vertex d)}
    {lower upper : Fin d → Set (Vertex d)} (N r : ℕ)
    (hr : 10 * d * r ≤ N)
    (h : HasCrossingComponentConnectingPaths ω B lower upper
      (pathDiameterAtLeast ((r : ℤ) + 1))) :
    HasCrossingComponentConnectingPaths ω B lower upper
      (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
        (N : ℤ) < 10 * ∑ k, |γ i k - z k|) := by
  obtain ⟨root, hroot, hpaths⟩ := h
  refine ⟨root, hroot, ?_⟩
  intro n γ hlarge hstart hadj
  apply hpaths n γ ?_ hstart hadj
  obtain ⟨i, j, k, hk⟩ := exists_coordinate_diameter_of_l1_radius hd N γ hlarge
  refine ⟨i, j, k, ?_⟩
  have hr' : (10 : ℤ) * d * r ≤ N := by exact_mod_cast hr
  have hd' : (0 : ℤ) < 10 * d := by exact_mod_cast (show 0 < 10 * d by omega)
  nlinarith

end Rigidity.Percolation
