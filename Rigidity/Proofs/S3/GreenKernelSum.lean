import Rigidity.Steps.S3.NotLipschitz
import LatticeProb.Euclidean.Series

/-!
# The lattice sum of Proposition 3.2

`GreenKernelSumStep` (`step:3.2-contradiction`, eqs. (altered-grad-left-bound) and
(altered-grad-top-and-bottom-bound)): summing the decay `|e - e'|^{-(d - 1/4)}` of the mixed
derivative of the Green function over the centre points `z` of `Q_{N - N^{1/d}}` and the outward
edges `(x, y)` of `L(Q_N)` through the left face and the sides gives `O(N^{d - 2 + 1/4})`.

Deterministic, with no literature input. The dyadic decomposition of the printed proof is replaced
by a product bound. On a face `{x_k = c}` of `Q_N` the endpoint `x` of the outward edge is the one
closer to `z`, and with `a = |c - z_k| ≥ 1`, `ε = 1/(4d)` and `r = d - 1/4 - (1 + ε)(d - 1) ≥ 0`,
`|x - z|_1^{-(d - 1/4)} ≤ a^{-r} ∏_{i ≠ k} (a + |x_i - z_i|)^{-(1 + ε)}`,
since `|x - z|_1 ≥ a + |x_i - z_i|` for every `i ≠ k`. Summing coordinate by coordinate with
`∑_{t ∈ ℤ} (a + |t|)^{-(1 + ε)} ≤ C a^{-ε}` bounds the sum over the face by `C a^{-3/4}`
(`sum_one_div_rpow_le`). On the left face `a = N`, which gives `C N^{d - 1} N^{-3/4}`
(`leftSum_pairKernel_le`); on a side `a = |±N - z_j|`, and `∑_{|z_j| < N} |±N - z_j|^{-3/4} ≤ C N^{1/4}`
gives `C N^{d - 2} N^{1/4}` (`sum_side_pairKernel_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LatticeProb LatticeProb.Percolation Rigidity.Steps.S3
open scoped BigOperators

namespace Rigidity.Proofs.S3

variable {d : ℕ}

/-! ### One-dimensional sums -/

/-- Split at `z`, the map `t ↦ k + |t - z|` is at most two-to-one: a sum of a function of
`k + |t - z|` over `t ∈ T` is at most twice the sum over the values. -/
theorem sum_comp_natAbs_sub_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (T : Finset ℤ) (z : ℤ) (k : ℕ) :
    ∑ t ∈ T, f (k + (t - z).natAbs) ≤
      2 * ∑ n ∈ T.image (fun t => k + (t - z).natAbs), f n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => z ≤ t), two_mul]
  have key : ∀ T' ⊆ T, Set.InjOn (fun t => k + (t - z).natAbs) T' →
      ∑ t ∈ T', f (k + (t - z).natAbs) ≤ ∑ n ∈ T.image (fun t => k + (t - z).natAbs), f n := by
    intro T' hT' hinj
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hT') fun n _ _ => hf n
  refine add_le_add (key _ (Finset.filter_subset _ _) ?_) (key _ (Finset.filter_subset _ _) ?_)
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    simp only at hab
    omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    simp only at hab
    omega

/-- The tail sum `∑_{|t| ≤ N} (a + |t - z|)^{-(1 + ε)} ≤ 2 (1 + 1/ε) 4^ε a^{-ε}`, for `a ≥ 1`. -/
theorem sum_Icc_add_natAbs_rpow_le {ε : ℝ} (hε : 0 < ε) {a : ℕ} (ha : 1 ≤ a) (z : ℤ) (N : ℕ) :
    ∑ t ∈ Finset.Icc (-(N : ℤ)) N, ((a + (t - z).natAbs : ℕ) : ℝ) ^ (-ε - 1) ≤
      2 * ((1 + 1 / ε) * 4 ^ ε) * (a : ℝ) ^ (-ε) := by
  refine (sum_comp_natAbs_sub_le (fun n => (n : ℝ) ^ (-ε - 1))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) _ z a).trans ?_
  have h := LatticeProb.Euclidean.Series.tail_finset_bound hε (R := (a : ℝ))
    (by exact_mod_cast ha) ((Finset.Icc (-(N : ℤ)) N).image fun t => a + (t - z).natAbs) (by
      intro n hn
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hn
      rw [Nat.floor_natCast]
      omega)
  calc _ ≤ 2 * ((1 + 1 / ε) * ((4 : ℝ) ^ ε * (a : ℝ) ^ (-ε))) := by linarith
    _ = _ := by ring

/-- `∑_{|t| ≤ N} |t - c|^{-3/4} ≤ 16 N^{1/4}` for `|c| ≤ N`. -/
theorem sum_Icc_natAbs_rpow_le {c : ℤ} {N : ℕ} (hc : |c| ≤ N) :
    ∑ t ∈ Finset.Icc (-(N : ℤ)) N, ((t - c).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) ≤
      16 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have h := sum_comp_natAbs_sub_le (fun n => (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) (Finset.Icc (-(N : ℤ)) N) c 0
  simp only [zero_add] at h
  have hsub : (Finset.Icc (-(N : ℤ)) N).image (fun t => (t - c).natAbs) ⊆
      insert 0 (Finset.Icc 1 (2 * N)) := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hn
    rw [Finset.mem_Icc] at ht
    rw [Finset.mem_insert, Finset.mem_Icc]
    rw [abs_le] at hc
    omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-(3 / 4 : ℝ)))
  rw [Finset.sum_insert (by simp), Nat.cast_zero, Real.zero_rpow (by norm_num), zero_add] at h1
  have h2 := LatticeProb.Euclidean.Series.sum_rpow_Icc_le_of_gt_neg_one
    (β := -(3 / 4 : ℝ)) (by norm_num) (by norm_num) (2 * N)
  rw [show -(3 / 4 : ℝ) + 1 = 1 / 4 by norm_num] at h2
  have h3 : ((2 * N : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    gcongr
    calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  linarith

/-! ### Sums over a face of the cube -/

/-- `#([-N, N] ∩ ℤ) = 2N + 1`. -/
theorem sum_Icc_one (N : ℕ) : ∑ _t ∈ Finset.Icc (-(N : ℤ)) N, (1 : ℝ) = 2 * N + 1 := by
  rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one,
    show ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 by omega]
  push_cast
  ring

/-- A product over `s ∋ j` of a function equal to `B` off `j`. -/
theorem prod_eq_mul_pow_of_ne {s : Finset (Fin d)} {j : Fin d} (hj : j ∈ s) (f : Fin d → ℝ)
    {B : ℝ} (hf : ∀ i ∈ s, i ≠ j → f i = B) : ∏ i ∈ s, f i = f j * B ^ (s.card - 1) := by
  rw [← Finset.mul_prod_erase s f hj,
    Finset.prod_congr rfl fun i hi => hf i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi),
    Finset.prod_const, Finset.card_erase_of_mem hj]

/-- A sum over a face `{x_k = c}` of `Q_N` of a function bounded by a product of functions of the
other coordinates is at most the product of the one-dimensional sums over `[-N, N]`. -/
theorem sum_le_mul_prod_sum {N : ℕ} {S : Finset (Vertex d)} (hS : S ⊆ latticeCube d N)
    (k : Fin d) (c : ℤ) (hc : ∀ x ∈ S, x k = c) (F : Vertex d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (g : Fin d → ℤ → ℝ) (hg : ∀ i t, 0 ≤ g i t)
    (hF : ∀ x ∈ S, F x ≤ A * ∏ i ∈ Finset.univ.erase k, g i (x i)) :
    ∑ x ∈ S, F x ≤ A * ∏ i ∈ Finset.univ.erase k, ∑ t ∈ Finset.Icc (-(N : ℤ)) N, g i t := by
  classical
  let T : Fin d → Finset ℤ := fun i => if i = k then {c} else Finset.Icc (-(N : ℤ)) N
  let G : Fin d → ℤ → ℝ := fun i t => if i = k then 1 else g i t
  have hsub : S ⊆ Fintype.piFinset T := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = k
    · subst hi
      simp [T, hc x hx]
    · simp only [T, if_neg hi]
      exact Fintype.mem_piFinset.1 (hS hx) i
  have hprod : ∀ x : Vertex d, ∏ i, G i (x i) = ∏ i ∈ Finset.univ.erase k, g i (x i) := by
    intro x
    rw [← Finset.prod_erase Finset.univ (f := fun i => G i (x i)) (a := k) (by simp [G])]
    exact Finset.prod_congr rfl fun i hi => by simp [G, Finset.ne_of_mem_erase hi]
  have hsum : ∏ i, ∑ t ∈ T i, G i t =
      ∏ i ∈ Finset.univ.erase k, ∑ t ∈ Finset.Icc (-(N : ℤ)) N, g i t := by
    rw [← Finset.prod_erase Finset.univ (f := fun i => ∑ t ∈ T i, G i t) (a := k)
      (by simp [T, G])]
    exact Finset.prod_congr rfl fun i hi => by simp [T, G, Finset.ne_of_mem_erase hi]
  have hG : ∀ i t, 0 ≤ G i t := fun i t => by
    by_cases hi : i = k
    · simp [G, hi]
    · simp only [G, if_neg hi]
      exact hg i t
  calc ∑ x ∈ S, F x ≤ ∑ x ∈ S, A * ∏ i, G i (x i) :=
        Finset.sum_le_sum fun x hx => by rw [hprod x]; exact hF x hx
    _ ≤ ∑ x ∈ Fintype.piFinset T, A * ∏ i, G i (x i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          mul_nonneg hA (Finset.prod_nonneg fun i _ => hG i (x i))
    _ = A * ∏ i, ∑ t ∈ T i, G i t := by rw [← Finset.mul_sum, Finset.prod_univ_sum]
    _ = _ := by rw [hsum]

/-! ### The kernel on a face -/

/-- The `ℓ¹` distance as a sum of coordinate distances in `ℕ`. -/
theorem latticeL1Dist_eq_sum_natAbs (x z : Vertex d) :
    (latticeL1Dist x z : ℝ) = ((∑ i, (x i - z i).natAbs : ℕ) : ℝ) := by
  unfold latticeL1Dist
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

/-- If `y` differs from `x` only in the coordinate `k`, and is farther from `z` there, the kernel
of the edge `(x, y)` is the decay `|x - z|_1^{-(d - 1/4)}` at `x`. -/
theorem pairKernel_le_of_coord {x y z : Vertex d} (k : Fin d) (hy : ∀ i, i ≠ k → y i = x i)
    (hk : (x k - z k).natAbs ≤ (y k - z k).natAbs) :
    pairKernel x y z ≤ 1 / (latticeL1Dist x z : ℝ) ^ ((d : ℝ) - 1 / 4) := by
  have hle : (latticeL1Dist x z : ℝ) ≤ (latticeL1Dist y z : ℝ) := by
    rw [latticeL1Dist_eq_sum_natAbs, latticeL1Dist_eq_sum_natAbs]
    exact_mod_cast Finset.sum_le_sum fun i _ => by
      by_cases hi : i = k
      · subst hi
        exact hk
      · rw [hy i hi]
  rw [pairKernel, min_eq_left hle, Real.rpow_eq_pow]

section Face

variable [NeZero d]

/-- The exponent `ε = 1/(4d)` spent on each free coordinate of a face. -/
noncomputable def slabExponent (d : ℕ) : ℝ := 1 / (4 * d)

theorem slabExponent_pos : 0 < slabExponent d := by
  have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  unfold slabExponent
  positivity

/-- The constant `C` of `∑_{x_k = c} |x - z|_1^{-(d - 1/4)} ≤ C |c - z_k|^{-3/4}`. -/
noncomputable def slabConst (d : ℕ) : ℝ :=
  (2 * ((1 + 1 / slabExponent d) * 4 ^ slabExponent d)) ^ (d - 1)

theorem slabConst_nonneg : 0 ≤ slabConst d := by
  have := slabExponent_pos (d := d)
  unfold slabConst
  exact pow_nonneg (mul_nonneg zero_le_two (mul_nonneg
    (add_nonneg zero_le_one (one_div_nonneg.2 this.le)) (Real.rpow_nonneg (by norm_num) _))) _

/-- The product bound: with `a = |x_k - z_k| ≥ 1` and `r = d - 1/4 - (1 + ε)(d - 1) ≥ 0`,
`|x - z|_1^{-(d - 1/4)} ≤ a^{-r} ∏_{i ≠ k} (a + |x_i - z_i|)^{-(1 + ε)}`. -/
theorem one_div_rpow_le_mul_prod {ε : ℝ} (hr : 0 ≤ (d : ℝ) - 1 / 4 - (ε + 1) * ((d : ℝ) - 1))
    (hε : 0 < ε) (k : Fin d) {x z : Vertex d} (ha : 1 ≤ (x k - z k).natAbs) :
    1 / (latticeL1Dist x z : ℝ) ^ ((d : ℝ) - 1 / 4) ≤
      ((x k - z k).natAbs : ℝ) ^ (-((d : ℝ) - 1 / 4 - (ε + 1) * ((d : ℝ) - 1))) *
        ∏ i ∈ Finset.univ.erase k,
          (((x k - z k).natAbs + (x i - z i).natAbs : ℕ) : ℝ) ^ (-ε - 1) := by
  have hD : ∀ i ∈ Finset.univ.erase k,
      (x k - z k).natAbs + (x i - z i).natAbs ≤ ∑ i, (x i - z i).natAbs := by
    intro i hi
    have h := Finset.sum_le_sum_of_subset (f := fun i => (x i - z i).natAbs)
      (Finset.subset_univ {k, i})
    rwa [Finset.sum_pair (Finset.ne_of_mem_erase hi).symm] at h
  have haD : (x k - z k).natAbs ≤ ∑ i, (x i - z i).natAbs :=
    Finset.single_le_sum (f := fun i => (x i - z i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  rw [latticeL1Dist_eq_sum_natAbs]
  set r := (d : ℝ) - 1 / 4 - (ε + 1) * ((d : ℝ) - 1) with hr_def
  set a : ℕ := (x k - z k).natAbs
  set D : ℕ := ∑ i, (x i - z i).natAbs
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  rw [show (-ε - 1) = -(ε + 1) by ring]
  simp only [Real.rpow_neg, Nat.cast_nonneg]
  rw [Finset.prod_inv_distrib, ← mul_inv, one_div]
  refine inv_anti₀ (mul_pos (Real.rpow_pos_of_pos ha0 _) (Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < a + (x i - z i).natAbs by omega)) _)) ?_
  calc (a : ℝ) ^ r * ∏ i ∈ Finset.univ.erase k, ((a + (x i - z i).natAbs : ℕ) : ℝ) ^ (ε + 1)
      ≤ (D : ℝ) ^ r * ∏ _i ∈ Finset.univ.erase k, (D : ℝ) ^ (ε + 1) :=
        mul_le_mul (Real.rpow_le_rpow ha0.le (by exact_mod_cast haD) hr)
          (Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
            fun i hi => Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hD i hi)
              (by linarith))
          (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg hD0.le _)
    _ = (D : ℝ) ^ ((d : ℝ) - 1 / 4) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, ← Real.rpow_add hD0,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)), hr_def]
        congr 1
        push_cast
        ring

/-- The sum over a face `{x_k = c}` of `Q_N`: `∑_x |x - z|_1^{-(d - 1/4)} ≤ C |c - z_k|^{-3/4}`
when `|c - z_k| ≥ 1`. -/
theorem sum_one_div_rpow_le {N : ℕ} {S : Finset (Vertex d)} (hS : S ⊆ latticeCube d N)
    (k : Fin d) (c : ℤ) (hc : ∀ x ∈ S, x k = c) (z : Vertex d) (ha : 1 ≤ (c - z k).natAbs) :
    ∑ x ∈ S, 1 / (latticeL1Dist x z : ℝ) ^ ((d : ℝ) - 1 / 4) ≤
      slabConst d * ((c - z k).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hε := slabExponent_pos (d := d)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hεd : slabExponent d * ((d : ℝ) - 1) ≤ 1 / 4 := by
    rw [slabExponent, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hr : 0 ≤ (d : ℝ) - 1 / 4 - (slabExponent d + 1) * ((d : ℝ) - 1) := by linarith
  have ha0 : (0 : ℝ) < (c - z k).natAbs := by exact_mod_cast ha
  calc ∑ x ∈ S, 1 / (latticeL1Dist x z : ℝ) ^ ((d : ℝ) - 1 / 4)
      ≤ ((c - z k).natAbs : ℝ) ^ (-((d : ℝ) - 1 / 4 - (slabExponent d + 1) * ((d : ℝ) - 1))) *
          ∏ i ∈ Finset.univ.erase k, ∑ t ∈ Finset.Icc (-(N : ℤ)) N,
            (((c - z k).natAbs + (t - z i).natAbs : ℕ) : ℝ) ^ (-slabExponent d - 1) := by
        refine sum_le_mul_prod_sum hS k c hc _ (Real.rpow_nonneg ha0.le _) _
          (fun i t => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun x hx => ?_
        have h := one_div_rpow_le_mul_prod hr hε k (x := x) (z := z) (by rw [hc x hx]; exact ha)
        rwa [hc x hx] at h
    _ ≤ ((c - z k).natAbs : ℝ) ^ (-((d : ℝ) - 1 / 4 - (slabExponent d + 1) * ((d : ℝ) - 1))) *
          ∏ _i ∈ Finset.univ.erase k, (2 * ((1 + 1 / slabExponent d) * 4 ^ slabExponent d) *
            ((c - z k).natAbs : ℝ) ^ (-slabExponent d)) := by
        gcongr with i hi
        exact sum_Icc_add_natAbs_rpow_le hε ha (z i) N
    _ = slabConst d * ((c - z k).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, mul_pow, ← Real.rpow_natCast (((c - z k).natAbs : ℝ) ^ _),
          ← Real.rpow_mul ha0.le, mul_left_comm, ← Real.rpow_add ha0, slabConst]
        congr 2
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne d))]
        push_cast
        ring

theorem centerInner_subset {N : ℕ} : centerInner d N ⊆ latticeCube d N :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

/-- A centre point of `Q_{N - N^{1/d}}` lies on the centre plane, at distance at least `1` from
the sides. -/
theorem centerInner_spec {N : ℕ} (hN : 1 ≤ N) {z : Vertex d} (hz : z ∈ centerInner d N) :
    z 0 = 0 ∧ ∀ i, i ≠ 0 → |z i| + 1 ≤ N := by
  have hz' := Finset.mem_filter.1 hz
  refine ⟨(Finset.mem_filter.1 hz'.1).2, fun i hi => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have h2 := hz'.2 i hi
  have : ((|z i| : ℤ) : ℝ) + 1 ≤ (N : ℝ) := by linarith
  exact_mod_cast this

/-- The sum of the kernel over the outward edges `(x, y x)` of a face `{x_k = c}` of `Q_N`, for one
centre point `z`. -/
theorem sum_face_pairKernel_le {N : ℕ} {S : Finset (Vertex d)} (hS : S ⊆ latticeCube d N)
    (k : Fin d) (c : ℤ) (hc : ∀ x ∈ S, x k = c) (y : Vertex d → Vertex d) (z : Vertex d)
    (hy : ∀ x ∈ S, ∀ i, i ≠ k → y x i = x i)
    (hyk : ∀ x ∈ S, (x k - z k).natAbs ≤ (y x k - z k).natAbs) (ha : 1 ≤ (c - z k).natAbs) :
    ∑ x ∈ S, pairKernel x (y x) z ≤ slabConst d * ((c - z k).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) :=
  (Finset.sum_le_sum fun x hx => pairKernel_le_of_coord k (hy x hx) (hyk x hx)).trans
    (sum_one_div_rpow_le hS k c hc z ha)

/-- Eq. (altered-grad-left-bound): the left face, where `|x - z|_1 ≥ N`. -/
theorem leftSum_pairKernel_le {N : ℕ} (hN : 1 ≤ N) :
    leftSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N ≤
      3 ^ (d - 1) * slabConst d * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) := by
  unfold leftSum
  rw [Finset.sum_comm]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hface : ∀ z ∈ centerInner d N, ∑ x ∈ leftFace d N, pairKernel x (x - unit 0) z ≤
      slabConst d * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
    intro z hz
    have hz0 := (centerInner_spec hN hz).1
    have h := sum_face_pairKernel_le (S := leftFace d N) (Finset.filter_subset _ _) 0 (-(N : ℤ))
      (fun x hx => (Finset.mem_filter.1 hx).2) (fun x => x - unit 0) z
      (fun x _ i hi => by simp [unit, hi])
      (fun (x : Vertex d) hx => by
        rw [show (x - unit 0 : Vertex d) 0 = x 0 - 1 by simp [unit],
          (Finset.mem_filter.1 hx).2, hz0]
        omega)
      (by rw [hz0]; omega)
    have hzN : (-(N : ℤ) - z 0).natAbs = N := by rw [hz0]; omega
    rwa [hzN] at h
  calc ∑ z ∈ centerInner d N, ∑ x ∈ leftFace d N, pairKernel x (x - unit 0) z
      ≤ slabConst d * (N : ℝ) ^ (-(3 / 4 : ℝ)) *
          ∏ _i ∈ Finset.univ.erase (0 : Fin d), ∑ _t ∈ Finset.Icc (-(N : ℤ)) N, (1 : ℝ) := by
        refine sum_le_mul_prod_sum centerInner_subset 0 0 (fun z hz => (centerInner_spec hN hz).1)
          _ (mul_nonneg slabConst_nonneg (Real.rpow_nonneg hN0.le _)) (fun _ _ => 1)
          (fun _ _ => zero_le_one) fun z hz => ?_
        rw [Finset.prod_const_one, mul_one]
        exact hface z hz
    _ = slabConst d * (N : ℝ) ^ (-(3 / 4 : ℝ)) * (2 * N + 1) ^ (d - 1) := by
        rw [sum_Icc_one, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
    _ ≤ slabConst d * (N : ℝ) ^ (-(3 / 4 : ℝ)) * (3 * N) ^ (d - 1) := by
        gcongr
        · exact mul_nonneg slabConst_nonneg (Real.rpow_nonneg hN0.le _)
        · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
          linarith
    _ = 3 ^ (d - 1) * slabConst d * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) := by
        rw [mul_pow, ← Real.rpow_natCast (N : ℝ) (d - 1)]
        rw [show (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) =
            (N : ℝ) ^ (-(3 / 4 : ℝ)) * (N : ℝ) ^ (((d - 1 : ℕ) : ℝ)) by
          rw [← Real.rpow_add hN0, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne d))]
          congr 1
          push_cast
          ring]
        ring

/-- Eq. (altered-grad-top-and-bottom-bound), for one side `{x_j = c}`, `|c| = N`, `j ≠ 1`:
`∑_z |c - z_j|^{-3/4}` over the centre points is `O(N^{d - 2} N^{1/4})`. -/
theorem sum_side_pairKernel_le {N : ℕ} (hN : 1 ≤ N) (hd : 2 ≤ d) {j : Fin d} (hj : j ≠ 0)
    {S : Finset (Vertex d)} (hS : S ⊆ latticeCube d N) (c : ℤ) (hcN : |c| = N)
    (hc : ∀ x ∈ S, x j = c) (y : Vertex d → Vertex d) (hy : ∀ x ∈ S, ∀ i, i ≠ j → y x i = x i)
    (hyk : ∀ x ∈ S, ∀ z ∈ centerInner d N, (x j - z j).natAbs ≤ (y x j - z j).natAbs) :
    ∑ x ∈ S, ∑ z ∈ centerInner d N, pairKernel x (y x) z ≤
      16 * 3 ^ (d - 2) * slabConst d * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) := by
  rw [Finset.sum_comm]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hface : ∀ z ∈ centerInner d N, ∑ x ∈ S, pairKernel x (y x) z ≤
      slabConst d * ((z j - c).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) := by
    intro z hz
    have hzj := (centerInner_spec hN hz).2 j hj
    have h1 : (1 : ℤ) ≤ |c - z j| := by
      have := abs_sub_abs_le_abs_sub c (z j)
      omega
    have h2 : (1 : ℤ) ≤ ((c - z j).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact h1
    have h := sum_face_pairKernel_le hS j c hc y z hy (fun x hx => hyk x hx z hz) (by omega)
    rwa [← Int.natAbs_neg, neg_sub] at h
  let g : Fin d → ℤ → ℝ := fun i =>
    if i = j then fun t => ((t - c).natAbs : ℝ) ^ (-(3 / 4 : ℝ)) else fun _ => 1
  have hj' : j ∈ Finset.univ.erase (0 : Fin d) := Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩
  have hcard : (Finset.univ.erase (0 : Fin d)).card - 1 = d - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  calc ∑ z ∈ centerInner d N, ∑ x ∈ S, pairKernel x (y x) z
      ≤ slabConst d * ∏ i ∈ Finset.univ.erase (0 : Fin d),
          ∑ t ∈ Finset.Icc (-(N : ℤ)) N, g i t := by
        refine sum_le_mul_prod_sum centerInner_subset 0 0 (fun z hz => (centerInner_spec hN hz).1)
          _ slabConst_nonneg g (fun i t => ?_) fun z hz => ?_
        · by_cases hi : i = j
          · simp only [g, if_pos hi]
            exact Real.rpow_nonneg (Nat.cast_nonneg _) _
          · simp only [g, if_neg hi]
            exact zero_le_one
        · rw [prod_eq_mul_pow_of_ne hj' _ (B := 1) fun i _ hi => by simp only [g, if_neg hi],
            one_pow, mul_one]
          simp only [g, if_pos rfl]
          exact hface z hz
    _ = slabConst d * ((∑ t ∈ Finset.Icc (-(N : ℤ)) N, ((t - c).natAbs : ℝ) ^ (-(3 / 4 : ℝ))) *
          (2 * N + 1) ^ (d - 2)) := by
        rw [prod_eq_mul_pow_of_ne hj' _ (B := 2 * N + 1) fun i _ hi => by
          simp only [g, if_neg hi]; exact sum_Icc_one N, hcard]
        simp only [g, if_pos rfl]
    _ ≤ slabConst d * (16 * (N : ℝ) ^ (1 / 4 : ℝ) * (3 * N) ^ (d - 2)) := by
        have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        gcongr
        · exact slabConst_nonneg
        · exact sum_Icc_natAbs_rpow_le hcN.le
        · linarith
    _ = 16 * 3 ^ (d - 2) * slabConst d * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) := by
        rw [mul_pow, ← Real.rpow_natCast (N : ℝ) (d - 2)]
        rw [show (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) =
            (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (((d - 2 : ℕ) : ℝ)) by
          rw [← Real.rpow_add hN0, Nat.cast_sub hd]
          congr 1
          push_cast
          ring]
        ring

end Face

/-- `GreenKernelSumStep` (`step:3.2-contradiction`, eqs. (altered-grad-left-bound) and
(altered-grad-top-and-bottom-bound)): the lattice sum of the decay of the mixed derivative of the
Green function over the centre points of `Q_{N - N^{1/d}}` and the outward edges of `L(Q_N)`
through the left face and the sides is `O(N^{d - 2 + 1/4})`. -/
theorem greenKernelSumStep (d : ℕ) [NeZero d] : GreenKernelSumStep d := by
  intro hd
  refine ⟨3 ^ (d - 1) * slabConst d + ((Finset.univ.erase (0 : Fin d)).card : ℝ) *
      (2 * (16 * 3 ^ (d - 2) * slabConst d)), Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩⟩
  have hL := leftSum_pairKernel_le (d := d) hN
  have hS : sidesSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N ≤
      ((Finset.univ.erase (0 : Fin d)).card : ℝ) * (2 * (16 * 3 ^ (d - 2) * slabConst d)) *
        (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) := by
    unfold sidesSum
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj0 := Finset.ne_of_mem_erase hj
    rw [two_mul, add_mul]
    refine add_le_add ?_ ?_
    · refine sum_side_pairKernel_le hN hd hj0 ((Finset.filter_subset _ _).trans
        (Finset.filter_subset _ _)) N (by simp) (fun x hx => (Finset.mem_filter.1 hx).2)
        (fun x => x + unit j) (fun x _ i hi => by simp [unit, hi])
        fun x hx z hz => ?_
      have hzj := (centerInner_spec hN hz).2 j hj0
      have := abs_le.1 (show |z j| ≤ (N : ℤ) - 1 by omega)
      rw [show (x + unit j) j = x j + 1 by simp [unit], (Finset.mem_filter.1 hx).2]
      omega
    · refine sum_side_pairKernel_le hN hd hj0 ((Finset.filter_subset _ _).trans
        (Finset.filter_subset _ _)) (-(N : ℤ)) (by simp) (fun x hx => (Finset.mem_filter.1 hx).2)
        (fun x => x - unit j) (fun x _ i hi => by simp [unit, hi])
        fun x hx z hz => ?_
      have hzj := (centerInner_spec hN hz).2 j hj0
      have := abs_le.1 (show |z j| ≤ (N : ℤ) - 1 by omega)
      rw [show (x - unit j) j = x j - 1 by simp [unit], (Finset.mem_filter.1 hx).2]
      omega
  linarith

end Rigidity.Proofs.S3
