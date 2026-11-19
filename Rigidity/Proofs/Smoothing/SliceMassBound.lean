import Rigidity.Proofs.Smoothing.SliceCover
import Rigidity.Proofs.Smoothing.MassBound

/-!
# Mass bounds from coordinate slices

A finite cover by slices whose total relative mass is at most `ε / (1 + ε)` controls the mass away
from a point of unit weight. This is the final summation in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Classical

namespace Rigidity.Smoothing

/-- Slice bounds imply the mass bound away from a point of unit weight. -/
theorem tsum_off_point_le_of_slice_fraction {α ι : Type*} [Fintype ι] (f : α → ℝ)
    (hf : Summable f) (hnonneg : ∀ y, 0 ≤ f y) (o : α) (ho : f o = 1)
    (P : ι → α → Prop) (hcover : ∀ y, y ≠ o → ∃ i, P i y) (p : ι → ℝ)
    (hslice : ∀ i, Summable (fun y => if P i y then f y else 0) ∧
      (∑' y, if P i y then f y else 0) ≤ p i * ∑' y, f y)
    {ε : ℝ} (hε : 0 < ε) (hp : (∑ i, p i) ≤ ε / (1 + ε)) :
    Summable (fun y => if y = o then 0 else f y) ∧
      (∑' y, if y = o then 0 else f y) ≤ ε := by
  obtain ⟨hoff, hcoverbound⟩ := tsum_off_point_le_of_cover f hf hnonneg o P hcover p hslice
  have htotal : (∑' y, f y) = 1 + ∑' y, if y = o then 0 else f y := by
    simpa only [ho] using hf.tsum_eq_add_tsum_ite o
  refine ⟨hoff, le_of_le_fraction_mul_one_add hε hp ?_⟩
  simpa only [htotal] using hcoverbound

end Rigidity.Smoothing
