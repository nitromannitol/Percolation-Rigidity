import Rigidity.Percolation.SelectedPathSegment
import LatticeProb.Lattice.PathBoundingRectangle

/-!
# Geometry of path segments

A nearest-neighbor path reaching a prescribed distance has an initial segment
contained in the corresponding coordinate box and reaching its boundary.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- The first segment reaching a positive coordinate distance stays within
that distance of its initial vertex. -/
theorem exists_bounded_segment_of_coordinate_step {d n : ℕ}
    (γ : Fin (n + 1) → Vertex d) (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n)
    (R : ℤ) (hR : 0 < R)
    (hstep : ∀ (j : Fin n) (k : Fin d),
      |γ j.succ k - γ j.castSucc k| ≤ 1)
    (hfar : ∃ k : Fin d, R ≤ |γ ⟨b, by omega⟩ k - γ ⟨a, by omega⟩ k|) :
    ∃ m, ∃ hm : a + m ≤ n,
      pathDiameterAtLeast R m (pathSegment γ a m hm) ∧
      ∀ j k, |pathSegment γ a m hm j k - γ ⟨a, by omega⟩ k| ≤ R := by
  classical
  let P : ℕ → Prop := fun m => ∃ hm : a + m ≤ n, ∃ k : Fin d,
    R ≤ |γ ⟨a + m, by omega⟩ k - γ ⟨a, by omega⟩ k|
  have hex : ∃ m, P m := by
    refine ⟨b - a, ?_, ?_⟩
    · omega
    · obtain ⟨k, hk⟩ := hfar
      refine ⟨k, ?_⟩
      simpa only [Nat.add_sub_of_le hab] using hk
  let m := Nat.find hex
  obtain ⟨hm, k, hk⟩ := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    have hzero : P 0 := by simpa only [← hz] using (Nat.find_spec hex)
    obtain ⟨_, k₀, hk₀⟩ := hzero
    simp only [Nat.add_zero, sub_self, abs_zero] at hk₀
    omega
  have hbefore : ∀ (t : ℕ) (ht : t < m) (htn : a + t ≤ n) (k : Fin d),
      |γ ⟨a + t, by omega⟩ k - γ ⟨a, by omega⟩ k| < R := by
    intro t ht htn k
    have hn := Nat.find_min hex ht
    by_contra hh
    exact hn ⟨htn, k, by omega⟩
  have hlast : ∀ k : Fin d,
      |γ ⟨a + m, by omega⟩ k - γ ⟨a, by omega⟩ k| ≤ R := by
    intro k
    have hp := hbefore (m - 1) (by omega) (by omega) k
    have hs := hstep ⟨a + (m - 1), by omega⟩ k
    have ht := abs_sub_le (γ ⟨a + m, by omega⟩ k)
      (γ ⟨a + (m - 1), by omega⟩ k) (γ ⟨a, by omega⟩ k)
    have hs' : |γ ⟨a + m, by omega⟩ k -
        γ ⟨a + (m - 1), by omega⟩ k| ≤ 1 := by
      have heq : a + (m - 1) + 1 = a + m := by omega
      change |γ ⟨a + (m - 1) + 1, by omega⟩ k -
        γ ⟨a + (m - 1), by omega⟩ k| ≤ 1 at hs
      simpa only [heq] using hs
    omega
  refine ⟨m, hm, ?_, ?_⟩
  · refine ⟨Fin.last m, 0, k, ?_⟩
    simpa only [pathSegment, Fin.val_last, Fin.val_zero, Nat.add_zero] using hk
  · intro j k
    by_cases h : j.val = m
    · simpa only [pathSegment, h] using hlast k
    · have hj := hbefore j.val (by omega) (by omega) k
      exact le_of_lt hj

/-- A selected path of sufficient diameter contains a segment of that
    diameter in one region of a cover with coordinate boxes around its points. -/
theorem IsSelectedOpenPath.exists_segment_of_buffered_cover {d n : ℕ} {ι : Type*}
    {ω : Configuration d} {D : Set (Vertex d)} (B : ι → Set (Vertex d))
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω D large n γ)
    (R : ℤ) (hR : 0 < R) (hdiam : pathDiameterAtLeast R n γ)
    (hcover : ∀ x ∈ D, ∃ i, ∀ y ∈ D, (∀ k, |y k - x k| ≤ R) → y ∈ B i) :
    ∃ i a m, ∃ h : a + m ≤ n,
      pathDiameterAtLeast R m (pathSegment γ a m h) ∧
      ∀ j, pathSegment γ a m h j ∈ B i := by
  obtain ⟨u, v, k, hfar⟩ := hdiam
  have hordered : ∃ a b : ℕ, ∃ hab : a ≤ b, ∃ hbn : b ≤ n,
      ∃ k : Fin d, R ≤ |γ ⟨b, by omega⟩ k - γ ⟨a, by omega⟩ k| := by
    by_cases huv : u.val ≤ v.val
    · refine ⟨u.val, v.val, huv, by omega, k, ?_⟩
      rw [abs_sub_comm]
      exact hfar
    · exact ⟨v.val, u.val, by omega, by omega, k, hfar⟩
  obtain ⟨a, b, hab, hbn, k, hfar⟩ := hordered
  have hstep : ∀ (j : Fin n) (k : Fin d), |γ j.succ k - γ j.castSucc k| ≤ 1 := by
    intro j k
    exact LatticeProb.abs_sub_coord_le_one_of_adj
      ((openGraph_le ω) (hγ.2.2 j).1).symm k
  obtain ⟨m, hm, hlarge, hbounded⟩ :=
    exists_bounded_segment_of_coordinate_step γ a b hab hbn R hR hstep ⟨k, hfar⟩
  obtain ⟨i, hi⟩ := hcover (γ ⟨a, by omega⟩) (hγ.mem_region ⟨a, by omega⟩)
  refine ⟨i, a, m, hm, hlarge, ?_⟩
  intro j
  exact hi _ (hγ.mem_region ⟨a + j.val, by omega⟩) (hbounded j)

/-- Buffered connected crossing covers transfer coalescence to long paths. -/
theorem largePathsCoalesce_of_buffered_crossing_cover {d : ℕ} {ι : Type*}
    (hd : 0 < d) {ω : Configuration d} (G : SimpleGraph ι)
    (B : ι → Set (Vertex d)) (D : Set (Vertex d)) (R : ℤ) (hR : 0 < R)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hBD : ∀ i, B i ⊆ D)
    (hcoal : ∀ i, LargePathsCoalesce ω (B i) (pathDiameterAtLeast R))
    (hpath : ∀ i, HasSelectedOpenPath ω (B i) (pathDiameterAtLeast R))
    (hoverlap : ∀ i j, G.Adj i j → ∃ T : IntegerCube d,
      R ≤ (T.size : ℤ) - 1 ∧
      (↑T.vertices : Set (Vertex d)) ⊆ B i ∩ B j ∧
      HasCrossingComponent ω (↑T.vertices)
        (fun k => ↑(T.lowerFace k)) (fun k => ↑(T.upperFace k)))
    (hconnected : ∀ i j, G.Reachable i j)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast R n γ)
    (hcover : ∀ x ∈ D, ∃ i, ∀ y ∈ D, (∀ k, |y k - x k| ≤ R) → y ∈ B i) :
    LargePathsCoalesce ω D large := by
  apply largePathsCoalesce_of_crossing_cover_segments hd G B D R large
    hBD hcoal hpath hoverlap hconnected
  intro n γ hγ
  exact hγ.exists_segment_of_buffered_cover B R hR (hdiam n γ hγ.1) hcover

end Rigidity.Percolation
