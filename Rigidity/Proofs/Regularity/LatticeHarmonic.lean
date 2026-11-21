import LatticeProb.Graph.Zd
import LatticeProb.Network.LocalCaccioppoli
import Rigidity.Proofs.Regularity.MixedDifferenceSobolev

/-!
# Discrete harmonic functions on the lattice

The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))` (`latticeLaplacian`) is the
network Laplacian of `ℤ^d` with unit conductances (`netLaplacian_lattice`). It commutes with
translations, so the forward differences, and more generally the mixed differences, of a function
harmonic on a region are harmonic on the region shrunk by the directions of the differences
(`latticeLaplacian_mixedDiff`). These are the first ingredients of the interior regularity of
discrete harmonic functions (Caccioppoli inequalities for their differences of all orders).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))`. -/
noncomputable def latticeLaplacian (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ i, (f (x + unit i) + f (x - unit i) - 2 * f x)

theorem unit_add_ne_sub (x : Fin d → ℤ) (i : Fin d) : x + unit i ≠ x - unit i := by
  intro h
  have := congrFun h i
  simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
  omega

/-- The lattice Laplacian is the network Laplacian of `ℤ^d` with unit conductances. -/
theorem netLaplacian_lattice (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x = latticeLaplacian f x := by
  classical
  rw [Network.netLaplacian_unitCond, Graph.laplacian, Graph.Zd.neighborFinset_eq, nbrFinset,
    sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair (unit_add_ne_sub x i)]
    ring
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The lattice Laplacian commutes with translations. -/
theorem latticeLaplacian_comp_add (f : (Fin d → ℤ) → ℝ) (v x : Fin d → ℤ) :
    latticeLaplacian (fun y => f (y + v)) x = latticeLaplacian f (x + v) := by
  simp only [latticeLaplacian]
  refine sum_congr rfl fun i _ => ?_
  rw [add_right_comm x (unit i) v, sub_add_eq_add_sub, add_sub_right_comm]

theorem latticeLaplacian_sub (f g : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => f y - g y) x = latticeLaplacian f x - latticeLaplacian g x := by
  simp only [latticeLaplacian, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The mixed difference `D_S f` is harmonic wherever `f` is harmonic at all the points
`x + ∑_{j ∈ U} e_j`, `U ⊆ S`. -/
theorem latticeLaplacian_mixedDiff (S : Finset (Fin d)) (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ)
    (hf : ∀ U ∈ S.powerset, latticeLaplacian f (x + shiftSum U) = 0) :
    latticeLaplacian (mixedDiff S f) x = 0 := by
  have hi : ∀ i, mixedDiff S f (x + unit i) + mixedDiff S f (x - unit i) - 2 * mixedDiff S f x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) *
        (f (x + shiftSum U + unit i) + f (x + shiftSum U - unit i) - 2 * f (x + shiftSum U)) := by
    intro i
    simp only [mixedDiff, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun U _ => ?_
    rw [add_right_comm x (unit i), sub_add_eq_add_sub]
    ring
  have h : latticeLaplacian (mixedDiff S f) x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * latticeLaplacian f (x + shiftSum U) := by
    rw [latticeLaplacian, sum_congr rfl fun i _ => hi i, sum_comm]
    refine sum_congr rfl fun U _ => ?_
    rw [latticeLaplacian, mul_sum]
  rw [h]
  exact sum_eq_zero fun U hU => by rw [hf U hU, mul_zero]

/-- The `ℓ^∞` box `{x : |xᵢ - zᵢ| ≤ m for all i}`. -/
noncomputable def supBox (z : Fin d → ℤ) (m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Icc (z i - m) (z i + m)

/-- The `ℓ^∞` distance `maxᵢ |xᵢ - zᵢ|`. -/
def supDist (x z : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i - z i).natAbs

theorem mem_supBox_iff_supDist_le {z x : Fin d → ℤ} {m : ℕ} :
    x ∈ supBox z m ↔ supDist x z ≤ m := by
  simp only [supBox, Fintype.mem_piFinset, mem_Icc, supDist, Finset.sup_le_iff, mem_univ,
    true_implies]
  refine forall_congr' fun i => ?_
  omega

theorem supDist_add_unit_le (x z : Fin d → ℤ) (i : Fin d) (s : ℤ) (hs : |s| ≤ 1) :
    supDist (x + s • unit i) z ≤ supDist x z + 1 := by
  simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
  intro j
  have hj : (x j - z j).natAbs ≤ Finset.univ.sup fun i => (x i - z i).natAbs :=
    Finset.le_sup (f := fun i => (x i - z i).natAbs) (mem_univ j)
  have hu : |(s • unit i) j| ≤ 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
    split_ifs <;> simp [hs]
  have : (x + s • unit i) j - z j = (x j - z j) + (s • unit i) j := by
    simp only [Pi.add_apply]; ring
  rw [this]
  have h1 := Int.natAbs_add_le (x j - z j) ((s • unit i) j)
  have h2 : ((s • unit i) j).natAbs ≤ 1 := by
    have h : (((s • unit i) j).natAbs : ℤ) ≤ 1 := by rw [← Int.abs_eq_natAbs]; exact hu
    exact_mod_cast h
  omega

/-- Neighbours differ by at most one in `ℓ^∞` distance. -/
theorem abs_supDist_sub_le_one {x y : Fin d → ℤ} (hy : y ∈ nbrFinset x) (z : Fin d → ℤ) :
    |(supDist y z : ℝ) - supDist x z| ≤ 1 := by
  obtain ⟨i, rfl | rfl⟩ := Graph.Zd.mem_nbrFinset.1 hy
  · have h1 := supDist_add_unit_le x z i 1 (by norm_num)
    have h2 := supDist_add_unit_le (x + unit i) z i (-1) (by norm_num)
    rw [one_smul] at h1
    rw [neg_one_smul, add_neg_cancel_right] at h2
    have h1' : (supDist (x + unit i) z : ℝ) ≤ supDist x z + 1 := by exact_mod_cast h1
    have h2' : (supDist x z : ℝ) ≤ supDist (x + unit i) z + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith
  · have h1 := supDist_add_unit_le x z i (-1) (by norm_num)
    have h2 := supDist_add_unit_le (x - unit i) z i 1 (by norm_num)
    rw [neg_one_smul, ← sub_eq_add_neg] at h1
    rw [one_smul, sub_add_cancel] at h2
    have h1' : (supDist (x - unit i) z : ℝ) ≤ supDist x z + 1 := by exact_mod_cast h1
    have h2' : (supDist x z : ℝ) ≤ supDist (x - unit i) z + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith

/-- Sums over the neighbours of `x`, direction by direction. -/
theorem sum_nbrFinset (F : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    ∑ y ∈ nbrFinset x, F y = ∑ i, (F (x + unit i) + F (x - unit i)) := by
  classical
  rw [nbrFinset, sum_biUnion]
  · exact sum_congr rfl fun i _ => sum_pair (unit_add_ne_sub x i)
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- Translating a sum of a nonnegative function into a larger finset. -/
theorem sum_comp_add_le {S T : Finset (Fin d → ℤ)} (F : (Fin d → ℤ) → ℝ) (hF : ∀ y, 0 ≤ F y)
    (v : Fin d → ℤ) (hST : ∀ x ∈ S, x + v ∈ T) : ∑ x ∈ S, F (x + v) ≤ ∑ y ∈ T, F y := by
  classical
  rw [← sum_image (f := F) (g := fun x => x + v) fun x _ y _ h => add_right_cancel h]
  exact sum_le_sum_of_subset_of_nonneg (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hST x hx) fun y _ _ => hF y

theorem supDist_le_of_mem_nbrFinset {x y z : Fin d → ℤ} (hy : y ∈ nbrFinset x) :
    supDist y z ≤ supDist x z + 1 := by
  have h := abs_supDist_sub_le_one hy z
  have : (supDist y z : ℝ) ≤ supDist x z + 1 := by linarith [(abs_le.1 h).2]
  exact_mod_cast this

/-- The cutoff `η = min 1 (max 0 ((2m - |x - z|_∞) / m))`. -/
noncomputable def boxCutoff (z : Fin d → ℤ) (m : ℕ) (x : Fin d → ℤ) : ℝ :=
  min 1 (max 0 ((2 * (m : ℝ) - supDist x z) / m))

theorem boxCutoff_eq_one {z x : Fin d → ℤ} {m : ℕ} (hm : 0 < m) (hx : supDist x z ≤ m) :
    boxCutoff z m x = 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : (supDist x z : ℝ) ≤ m := by exact_mod_cast hx
  have : 1 ≤ (2 * (m : ℝ) - supDist x z) / m := by rw [le_div_iff₀ hm']; linarith
  rw [boxCutoff, min_eq_left (this.trans (le_max_right _ _))]

theorem boxCutoff_eq_zero {z x : Fin d → ℤ} {m : ℕ} (hm : 0 < m) (hx : 2 * m ≤ supDist x z) :
    boxCutoff z m x = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : 2 * (m : ℝ) ≤ supDist x z := by exact_mod_cast hx
  have : (2 * (m : ℝ) - supDist x z) / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm'.le
  rw [boxCutoff, max_eq_left this, min_eq_right zero_le_one]

theorem abs_boxCutoff_sub_le {z x y : Fin d → ℤ} {m : ℕ} (hm : 0 < m) (hy : y ∈ nbrFinset x) :
    |boxCutoff z m y - boxCutoff z m x| ≤ 1 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((2 * (m : ℝ) - supDist y z) / m)) 1
    (max 0 ((2 * (m : ℝ) - supDist x z) / m))
  rw [sub_self, abs_zero] at h1
  have h2 := abs_max_sub_max_le_abs ((2 * (m : ℝ) - supDist y z) / m)
    ((2 * (m : ℝ) - supDist x z) / m) 0
  rw [max_comm _ (0 : ℝ), max_comm ((2 * (m : ℝ) - supDist x z) / m) 0] at h2
  have h3 : |(2 * (m : ℝ) - supDist y z) / m - (2 * (m : ℝ) - supDist x z) / m| ≤ 1 / m := by
    rw [← sub_div, abs_div, abs_of_pos hm', div_le_div_iff_of_pos_right hm']
    have := abs_supDist_sub_le_one hy z
    rw [abs_sub_comm] at this
    calc |2 * (m : ℝ) - supDist y z - (2 * m - supDist x z)| = |(supDist x z : ℝ) - supDist y z| :=
          by ring_nf
      _ ≤ 1 := this
  unfold boxCutoff
  calc |min 1 (max 0 ((2 * (m : ℝ) - supDist y z) / m)) -
        min 1 (max 0 ((2 * (m : ℝ) - supDist x z) / m))|
      ≤ max 0 |max 0 ((2 * (m : ℝ) - supDist y z) / m) -
          max 0 ((2 * (m : ℝ) - supDist x z) / m)| := h1
    _ ≤ 1 / m := max_le (by positivity) (h2.trans h3)

theorem boxCutoff_nonneg (z x : Fin d → ℤ) (m : ℕ) : 0 ≤ boxCutoff z m x :=
  le_min zero_le_one (le_max_left _ _)

/-- **Caccioppoli inequality** for lattice harmonic functions on sup-norm boxes:
`∑_{x ∈ Q_m} ∑ᵢ (D_i f(x))² ≤ 16 d / m² ∑_{x ∈ Q_{2m+2}} f(x)²` if `Δ f = 0` on `Q_{2m}`. -/
theorem caccioppoli_supBox (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {m : ℕ} (hm : 0 < m)
    (hharm : ∀ x ∈ supBox z (2 * m), latticeLaplacian f x = 0) :
    ∑ x ∈ supBox z m, ∑ i, (f (x + unit i) - f x) ^ 2 ≤
      16 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set η := boxCutoff z m with hη
  set S := supBox z (2 * m + 1)
  set B := supBox z (2 * m)
  have hBS : B ⊆ S := fun x hx => by
    rw [mem_supBox_iff_supDist_le] at hx ⊢; omega
  have hnb : ∀ x ∈ B, ∀ y, (lattice d).Adj x y → y ∈ S := by
    intro x hx y hy
    have hy' : y ∈ nbrFinset x := Graph.Zd.mem_nbrFinset.2 (Graph.Zd.adj_iff.1 hy)
    rw [mem_supBox_iff_supDist_le] at hx ⊢
    have := supDist_le_of_mem_nbrFinset (z := z) hy'
    omega
  have htest : ∀ x, x ∉ B → f x * η x ^ 2 = 0 := by
    intro x hx
    rw [mem_supBox_iff_supDist_le, not_le] at hx
    rw [hη, boxCutoff_eq_zero hm (by omega)]; ring
  have hf : ∀ x ∈ B, Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x = 0 :=
    fun x hx => by rw [netLaplacian_lattice]; exact hharm x hx
  have key := Network.caccioppoli_of_support Network.isCond_unitCond S B f η hf htest hBS hnb
  have hc : ∀ x, ∀ y ∈ (lattice d).neighborFinset x, Network.unitCond (lattice d) x y = 1 := by
    intro x y hy
    rw [Network.unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)]
  -- the left side
  have hlow : ∑ x ∈ supBox z m, ∑ i, (f (x + unit i) - f x) ^ 2 ≤
      ∑ x ∈ S, ∑ y ∈ (lattice d).neighborFinset x,
        Network.unitCond (lattice d) x y * (f x - f y) ^ 2 * η x ^ 2 := by
    have hsub : supBox z m ⊆ S := fun x hx => by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => sum_nonneg fun y hy =>
      by rw [hc x y hy]; positivity)
    refine sum_le_sum fun x hx => ?_
    rw [mem_supBox_iff_supDist_le] at hx
    have hη1 : η x = 1 := boxCutoff_eq_one hm hx
    have e : ∑ y ∈ (lattice d).neighborFinset x,
        Network.unitCond (lattice d) x y * (f x - f y) ^ 2 * η x ^ 2 =
          ∑ y ∈ (lattice d).neighborFinset x, (f x - f y) ^ 2 :=
      sum_congr rfl fun y hy => by rw [hc x y hy, hη1]; ring
    rw [e, Graph.Zd.neighborFinset_eq, sum_nbrFinset]
    refine sum_le_sum fun i _ => ?_
    have := sq_nonneg (f x - f (x - unit i))
    nlinarith [sq_nonneg (f x - f (x + unit i))]
  -- the right side
  have hup : ∑ x ∈ S, ∑ y ∈ (lattice d).neighborFinset x,
        Network.unitCond (lattice d) x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 ≤
      4 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 := by
    have hpt : ∀ x ∈ S, ∑ y ∈ (lattice d).neighborFinset x,
        Network.unitCond (lattice d) x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 ≤
          1 / (m : ℝ) ^ 2 * ∑ i, (2 * f x ^ 2 + f (x + unit i) ^ 2 + f (x - unit i) ^ 2) := by
      intro x _
      rw [Graph.Zd.neighborFinset_eq]
      have hb : ∀ y ∈ nbrFinset x, Network.unitCond (lattice d) x y * (f x ^ 2 + f y ^ 2) *
          (η x - η y) ^ 2 ≤ 1 / (m : ℝ) ^ 2 * (f x ^ 2 + f y ^ 2) := by
        intro y hy
        rw [hc x y (by rw [Graph.Zd.neighborFinset_eq]; exact hy), one_mul]
        have h1 := abs_boxCutoff_sub_le (z := z) hm hy
        have h2 : (η x - η y) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 := by
          rw [← sq_abs, abs_sub_comm]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [div_pow, one_pow] at h2
        rw [mul_comm (1 / (m : ℝ) ^ 2)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      refine (sum_le_sum hb).trans (le_of_eq ?_)
      rw [← mul_sum, sum_nbrFinset]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, sum_comm]
    have hS2 : ∀ x ∈ S, x ∈ supBox z (2 * m + 2) := fun x hx => by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega
    have hshift : ∀ (v : Fin d → ℤ), v ∈ nbrFinset 0 → ∀ x ∈ S, x + v ∈ supBox z (2 * m + 2) := by
      intro v hv x hx
      rw [mem_supBox_iff_supDist_le] at hx ⊢
      have hv' : x + v ∈ nbrFinset x := by
        obtain ⟨i, h | h⟩ := Graph.Zd.mem_nbrFinset.1 hv
        · exact Graph.Zd.mem_nbrFinset.2 ⟨i, Or.inl (by rw [h, zero_add])⟩
        · exact Graph.Zd.mem_nbrFinset.2 ⟨i, Or.inr (by rw [h, zero_sub, ← sub_eq_add_neg])⟩
      have := supDist_le_of_mem_nbrFinset (z := z) hv'
      omega
    have hT := sum_le_sum_of_subset_of_nonneg (f := fun x => f x ^ 2) (fun x hx => hS2 x hx)
      fun x _ _ => sq_nonneg (f x)
    have hplus : ∀ i, ∑ x ∈ S, f (x + unit i) ^ 2 ≤ ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 :=
      fun i => sum_comp_add_le (fun y => f y ^ 2) (fun y => sq_nonneg _) _
        (hshift _ (Graph.Zd.mem_nbrFinset.2 ⟨i, Or.inl (zero_add _).symm⟩))
    have hminus : ∀ i, ∑ x ∈ S, f (x - unit i) ^ 2 ≤ ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 := by
      intro i
      have := sum_comp_add_le (S := S) (fun y => f y ^ 2) (fun y => sq_nonneg _) (-unit i)
        (hshift _ (Graph.Zd.mem_nbrFinset.2 ⟨i, Or.inr (by rw [zero_sub])⟩))
      simpa only [← sub_eq_add_neg] using this
    have htot : ∑ i : Fin d, ∑ x ∈ S, (2 * f x ^ 2 + f (x + unit i) ^ 2 + f (x - unit i) ^ 2) ≤
        ∑ _i : Fin d, 4 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 :=
      sum_le_sum fun i _ => by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
        linarith [hplus i, hminus i]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
    have hm2 : 0 ≤ 1 / (m : ℝ) ^ 2 := by positivity
    calc 1 / (m : ℝ) ^ 2 * ∑ i : Fin d, ∑ x ∈ S,
          (2 * f x ^ 2 + f (x + unit i) ^ 2 + f (x - unit i) ^ 2)
        ≤ 1 / (m : ℝ) ^ 2 * (d * (4 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2)) :=
          mul_le_mul_of_nonneg_left htot hm2
      _ = 4 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 := by ring
  have := key.trans (mul_le_mul_of_nonneg_left hup (by norm_num : (0 : ℝ) ≤ 4))
  calc ∑ x ∈ supBox z m, ∑ i, (f (x + unit i) - f x) ^ 2 ≤ _ := hlow
    _ ≤ 4 * (4 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2) := this
    _ = 16 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), f x ^ 2 := by ring

theorem shiftSum_apply (U : Finset (Fin d)) (j : Fin d) :
    shiftSum U j = if j ∈ U then 1 else 0 := by
  classical
  simp only [shiftSum, Finset.sum_apply, unit, Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem supDist_add_shiftSum_le (x z : Fin d → ℤ) (U : Finset (Fin d)) :
    supDist (x + shiftSum U) z ≤ supDist x z + 1 := by
  simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
  intro j
  have hj : (x j - z j).natAbs ≤ Finset.univ.sup fun i => (x i - z i).natAbs :=
    Finset.le_sup (f := fun i => (x i - z i).natAbs) (mem_univ j)
  have : (x + shiftSum U) j - z j = (x j - z j) + shiftSum U j := by
    simp only [Pi.add_apply]; ring
  rw [this, shiftSum_apply]
  split_ifs <;> omega

/-- **Iterated Caccioppoli inequality**: the mixed differences of order `k = |S|` of a function
harmonic on `Q_{4^k m}` satisfy `∑_{Q_m} (D_S f)² ≤ (64 d)^k m^{-2k} ∑_{Q_{4^k m}} f²`. -/
theorem sum_sq_mixedDiff_le (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) (S : Finset (Fin d)) :
    ∀ m : ℕ, 0 < m → (∀ x ∈ supBox z (4 ^ S.card * m), latticeLaplacian f x = 0) →
      ∑ x ∈ supBox z m, (mixedDiff S f x) ^ 2 ≤
        (64 * d) ^ S.card / (m : ℝ) ^ (2 * S.card) *
          ∑ x ∈ supBox z (4 ^ S.card * m), f x ^ 2 := by
  induction S using Finset.induction_on with
  | empty =>
    intro m _ _
    simp [mixedDiff_empty]
  | insert i S hi ih =>
    intro m hm hf
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    set k := S.card with hk
    have hcard : (insert i S).card = k + 1 := card_insert_of_notMem hi
    rw [hcard] at hf ⊢
    set g := mixedDiff S f with hg
    -- `g` is harmonic on `Q_{2m}`
    have hgh : ∀ x ∈ supBox z (2 * m), latticeLaplacian g x = 0 := by
      intro x hx
      apply latticeLaplacian_mixedDiff
      intro U _
      apply hf
      rw [mem_supBox_iff_supDist_le] at hx ⊢
      have h1 := supDist_add_shiftSum_le x z U
      have h2 : 2 * m + 1 ≤ 4 ^ (k + 1) * m := by
        have : 4 ≤ 4 ^ (k + 1) := by
          calc 4 = 4 ^ 1 := (pow_one 4).symm
            _ ≤ 4 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      omega
    have hcac := caccioppoli_supBox g z hm hgh
    have hDi : ∑ x ∈ supBox z m, (mixedDiff (insert i S) f x) ^ 2 ≤
        ∑ x ∈ supBox z m, ∑ j, (g (x + unit j) - g x) ^ 2 := by
      refine sum_le_sum fun x _ => ?_
      rw [mixedDiff_insert hi]
      exact single_le_sum (f := fun j => (g (x + unit j) - g x) ^ 2)
        (fun j _ => sq_nonneg _) (mem_univ i)
    have hbox : 4 ^ k * (4 * m) = 4 ^ (k + 1) * m := by ring
    have hih := ih (4 * m) (by omega) (by rw [hbox]; exact hf)
    have hsub : ∑ x ∈ supBox z (2 * m + 2), g x ^ 2 ≤ ∑ x ∈ supBox z (4 * m), g x ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (fun x hx => by
        rw [mem_supBox_iff_supDist_le] at hx ⊢; omega) fun x _ _ => sq_nonneg _
    rw [hbox] at hih
    have hA : 0 ≤ ∑ x ∈ supBox z (4 ^ (k + 1) * m), f x ^ 2 :=
      sum_nonneg fun x _ => sq_nonneg _
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc ∑ x ∈ supBox z m, (mixedDiff (insert i S) f x) ^ 2
        ≤ 16 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * m + 2), g x ^ 2 := hDi.trans hcac
      _ ≤ 16 * d / (m : ℝ) ^ 2 * ∑ x ∈ supBox z (4 * m), g x ^ 2 :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ ≤ 16 * d / (m : ℝ) ^ 2 * ((64 * d) ^ k / ((4 * m : ℕ) : ℝ) ^ (2 * k) *
            ∑ x ∈ supBox z (4 ^ (k + 1) * m), f x ^ 2) :=
          mul_le_mul_of_nonneg_left hih (by positivity)
      _ ≤ (64 * d) ^ (k + 1) / (m : ℝ) ^ (2 * (k + 1)) *
            ∑ x ∈ supBox z (4 ^ (k + 1) * m), f x ^ 2 := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hA
          have e1 : ((4 * m : ℕ) : ℝ) ^ (2 * k) = 16 ^ k * (m : ℝ) ^ (2 * k) := by
            push_cast; rw [mul_pow, pow_mul]; norm_num
          have e2 : (m : ℝ) ^ (2 * (k + 1)) = (m : ℝ) ^ 2 * (m : ℝ) ^ (2 * k) := by ring
          have e3 : (64 * (d : ℝ)) ^ (k + 1) = 64 * d * (64 * d) ^ k := by ring
          rw [e1, e2, e3, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have h16 : (16 : ℝ) ≤ 64 * 16 ^ k := by
            have : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
            linarith
          have hP : 0 ≤ (d : ℝ) * (64 * d) ^ k * ((m : ℝ) ^ 2 * (m : ℝ) ^ (2 * k)) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_left h16 hP]

end Rigidity.Proofs.Regularity
