import Rigidity.Proofs.Cluster.CoarseInequalities

/-!
# The Sobolev inequality on a cluster from a lattice Sobolev inequality

Armstrong and Dario (Proposition 3.4) deduce the Sobolev inequality on the cluster from the
Sobolev inequality on the lattice applied to the coarsening `[w]_𝒫`, Lemma 3.2 for `w - [w]_𝒫` and
Lemma 3.3 for `∇[w]_𝒫`. This file proves the deduction for coarse-graining data in the cases
`∑_{C_*(U)} w = 0` and `∑_{cl_𝒫(U)} [w]_𝒫 = 0` of Armstrong and Dario. If the lattice
Sobolev–Poincaré inequality `∑_{x ∈ D} |f(x) - (f)_D|^s ≤ S (∑_{x ∈ D} |∇f|^t(x))^{s/t}` holds
on the domain `D`, Lemma 3.2 holds for `w` with exponent `s`, constant `A` and weights `a`, and
Lemma 3.3 holds for `w` with exponent `t ≤ s`, constant `B` and weights `b`, then
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ c (A + S B^{s/t}) (∑_z (a(z)^{t/s} + b(z)) |∇w 1_{a≠0}|^t(z))^{s/t}`
with `c = 2^{s-1}(1 + 2^{s-1} + 4^{s-1})`, and `c = 2^{s-1}` in the second case. The last step of
Armstrong and Dario, `∑ a_i^{s/t} ≤ (∑ a_i)^{s/t}`, turns the weights `a` of Lemma 3.2 into
`a^{t/s}`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The lattice Sobolev–Poincaré inequality on a finite domain `D` with exponents `s`, `t` and
constant `S`: `∑_{x ∈ D} |f(x) - (f)_D|^s ≤ S (∑_{x ∈ D} |∇f|^t(x))^{s/t}` for every `f`, with
`|∇f|(x)` the magnitude of the lattice gradient on `D`. -/
def LatticeSobolevOn (D : Finset (Vertex d)) (s t S : ℝ) : Prop :=
  ∀ f : Vertex d → ℝ, ∑ x ∈ D, |f x - (∑ y ∈ D, f y) / D.card| ^ s ≤
    S * (∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ t) ^ (s / t)

/-- For `p ≥ 1`, the sum of the `p`-th powers of nonnegative numbers is at most the `p`-th power
of their sum. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hx : ∀ i ∈ s, 0 ≤ x i) : ∑ i ∈ s, x i ^ p ≤ (∑ i ∈ s, x i) ^ p := by
  have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  have hp' : 1 + (p - 1) ≠ 0 := by linarith
  calc ∑ i ∈ s, x i ^ p = ∑ i ∈ s, x i * x i ^ (p - 1) := Finset.sum_congr rfl fun i hi => by
          rw [← Real.rpow_one_add' (hx i hi) hp']
          congr 1
          ring
    _ ≤ ∑ i ∈ s, x i * (∑ j ∈ s, x j) ^ (p - 1) := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hx i hi) (Finset.single_le_sum hx hi)
            (by linarith)) (hx i hi)
    _ = (∑ i ∈ s, x i) * (∑ i ∈ s, x i) ^ (p - 1) := by rw [Finset.sum_mul]
    _ = (∑ i ∈ s, x i) ^ p := by
          rw [← Real.rpow_one_add' hS hp']
          congr 1
          ring

/-- For `s ≥ 1` and `u, v ≥ 0`, `(u + v)^s ≤ 2^{s-1} (u^s + v^s)`. -/
theorem add_rpow_le_two_rpow_mul {u v s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 1 ≤ s) :
    (u + v) ^ s ≤ 2 ^ (s - 1) * (u ^ s + v ^ s) := by
  have h := NNReal.coe_le_coe.2 (NNReal.rpow_add_le_mul_rpow_add_rpow ⟨u, hu⟩ ⟨v, hv⟩ hs)
  push_cast at h
  exact h

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- **Armstrong and Dario, Proposition 3.4, from the lattice Sobolev inequality** (case
`∑_{C_*(U)} w = 0`). -/
theorem sum_rpow_le_of_latticeSobolevOn {s t A B S : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hts : t ≤ s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) {a b : Vertex d → ℝ} (ha : ∀ z, 0 ≤ a z)
    (hb : ∀ z, 0 ≤ b z) (hLS : LatticeSobolevOn P.domain s t S) (w : Vertex d → ℝ)
    (h32 : ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      A * ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s)
    (h33 : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t ≤
      B * ∑ z ∈ P.cluster, b z * gradNormIn (openGraph ω) P.cluster w z ^ t)
    (hw : ∑ x ∈ P.cluster, w x = 0) :
    ∑ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) * (A + S * B ^ (s / t)) *
        (∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
          gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  have htne : t ≠ 0 := ht0.ne'
  have hst : 1 ≤ s / t := by rw [le_div_iff₀ ht0]; linarith
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) P.cluster w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
      gradNormIn (openGraph ω) P.cluster w z ^ t := ⟨_, rfl⟩
  rw [← hW]
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (add_nonneg (Real.rpow_nonneg (ha z) _) (hb z))
      (Real.rpow_nonneg (hg0 z) _)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∑ y ∈ P.domain, P.coarsen w y) / P.domain.card := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ x ∈ P.cluster, |P.coarsen w x - m| ^ s := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hV0 : 0 ≤ V := by
    rw [hV]
    exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hc0 : (0 : ℝ) ≤ 2 ^ (s - 1) := by positivity
  -- Lemma 3.2 and superadditivity
  have hUW : U ≤ A * W ^ (s / t) := by
    rw [hU]
    refine h32.trans (mul_le_mul_of_nonneg_left ?_ hA)
    calc ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s
        = ∑ z ∈ P.cluster, (a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          Finset.sum_congr rfl fun z _ => by
            have e1 : (a z ^ (t / s)) ^ (s / t) = a z := by
              rw [← Real.rpow_mul (ha z), show t / s * (s / t) = 1 by field_simp, Real.rpow_one]
            have e2 : (gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) =
                gradNormIn (openGraph ω) P.cluster w z ^ s := by
              rw [← Real.rpow_mul (hg0 z), show t * (s / t) = s by field_simp]
            rw [Real.mul_rpow (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _), e1, e2]
      _ ≤ (∑ z ∈ P.cluster, a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          sum_rpow_le_rpow_sum _ _ hst fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _)
      _ ≤ W ^ (s / t) := by
          rw [hW]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _))
            (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (hb z)) (Real.rpow_nonneg (hg0 z) _)) (by linarith)
  -- the lattice Sobolev inequality and Lemma 3.3
  have hVW : V ≤ S * B ^ (s / t) * W ^ (s / t) := by
    have h1 : V ≤ ∑ x ∈ P.domain, |P.coarsen w x - m| ^ s := by
      rw [hV]
      exact Finset.sum_le_sum_of_subset_of_nonneg P.cluster_subset fun _ _ _ =>
        Real.rpow_nonneg (abs_nonneg _) _
    have h2 := hLS (P.coarsen w)
    rw [← hm] at h2
    have h3 : (∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^
        (s / t) ≤ (B * W) ^ (s / t) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (h33.trans ?_) (by linarith)
      rw [hW]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Real.rpow_nonneg (ha z) _)) (Real.rpow_nonneg (hg0 z) _)) hB
    rw [Real.mul_rpow hB hW0] at h3
    calc V ≤ ∑ x ∈ P.domain, |P.coarsen w x - m| ^ s := h1
      _ ≤ S * (∑ x ∈ P.domain,
            gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^ (s / t) := h2
      _ ≤ S * (B ^ (s / t) * W ^ (s / t)) := mul_le_mul_of_nonneg_left h3 hS
      _ = S * B ^ (s / t) * W ^ (s / t) := by ring
  -- the empty cluster
  by_cases hCe : P.cluster = ∅
  · have h0 : ∑ x ∈ P.cluster, |w x| ^ s = 0 := by rw [hCe, Finset.sum_empty]
    have : 0 ≤ A + S * B ^ (s / t) := add_nonneg hA (mul_nonneg hS (Real.rpow_nonneg hB _))
    rw [h0]
    positivity
  have hn0 : (0 : ℝ) < P.cluster.card :=
    by exact_mod_cast (Finset.nonempty_iff_ne_empty.2 hCe).card_pos
  -- the mean of the coarsening
  have hnm : (P.cluster.card : ℝ) * |m| ≤
      ∑ x ∈ P.cluster, |P.coarsen w x - m| + ∑ x ∈ P.cluster, |w x - P.coarsen w x| := by
    have e : (P.cluster.card : ℝ) * m = ∑ x ∈ P.cluster, (m - w x) := by
      rw [Finset.sum_sub_distrib, hw, Finset.sum_const, nsmul_eq_mul, sub_zero]
    calc (P.cluster.card : ℝ) * |m| = |(P.cluster.card : ℝ) * m| := by
          rw [abs_mul, abs_of_pos hn0]
      _ = |∑ x ∈ P.cluster, (m - w x)| := by rw [e]
      _ ≤ ∑ x ∈ P.cluster, |m - w x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ P.cluster, (|P.coarsen w x - m| + |w x - P.coarsen w x|) :=
          Finset.sum_le_sum fun x _ => by
            calc |m - w x| = |(m - P.coarsen w x) + (P.coarsen w x - w x)| := by
                  congr 1
                  ring
              _ ≤ |m - P.coarsen w x| + |P.coarsen w x - w x| := abs_add_le _ _
              _ = |P.coarsen w x - m| + |w x - P.coarsen w x| := by
                  rw [abs_sub_comm m (P.coarsen w x), abs_sub_comm (P.coarsen w x) (w x)]
      _ = _ := Finset.sum_add_distrib
  have hmV : (P.cluster.card : ℝ) * |m| ^ s ≤ 2 ^ (s - 1) * (V + U) := by
    have hX := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := P.cluster)
      (f := fun x => |P.coarsen w x - m|) hs (fun _ _ => abs_nonneg _)
    have hY := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := P.cluster)
      (f := fun x => |w x - P.coarsen w x|) hs (fun _ _ => abs_nonneg _)
    rw [← hV] at hX
    rw [← hU] at hY
    have hXY := add_rpow_le_two_rpow_mul
      (Finset.sum_nonneg (s := P.cluster) fun x _ => abs_nonneg (P.coarsen w x - m))
      (Finset.sum_nonneg (s := P.cluster) fun x _ => abs_nonneg (w x - P.coarsen w x)) hs
    have h1 : ((P.cluster.card : ℝ) * |m|) ^ s ≤
        (∑ x ∈ P.cluster, |P.coarsen w x - m| + ∑ x ∈ P.cluster, |w x - P.coarsen w x|) ^ s :=
      Real.rpow_le_rpow (by positivity) hnm (by linarith)
    have hsplit : (P.cluster.card : ℝ) ^ s = (P.cluster.card : ℝ) ^ (s - 1) * P.cluster.card := by
      conv_lhs => rw [show s = s - 1 + 1 by ring]
      rw [Real.rpow_add hn0, Real.rpow_one]
    have hns : ((P.cluster.card : ℝ) * |m|) ^ s =
        (P.cluster.card : ℝ) ^ (s - 1) * ((P.cluster.card : ℝ) * |m| ^ s) := by
      rw [Real.mul_rpow hn0.le (abs_nonneg _), hsplit]
      ring
    have hpos : 0 < (P.cluster.card : ℝ) ^ (s - 1) := Real.rpow_pos_of_pos hn0 _
    refine le_of_mul_le_mul_left ?_ hpos
    calc (P.cluster.card : ℝ) ^ (s - 1) * ((P.cluster.card : ℝ) * |m| ^ s)
        = ((P.cluster.card : ℝ) * |m|) ^ s := hns.symm
      _ ≤ _ := h1
      _ ≤ 2 ^ (s - 1) * ((∑ x ∈ P.cluster, |P.coarsen w x - m|) ^ s +
            (∑ x ∈ P.cluster, |w x - P.coarsen w x|) ^ s) := hXY
      _ ≤ 2 ^ (s - 1) * ((P.cluster.card : ℝ) ^ (s - 1) * V +
            (P.cluster.card : ℝ) ^ (s - 1) * U) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) hc0
      _ = (P.cluster.card : ℝ) ^ (s - 1) * (2 ^ (s - 1) * (V + U)) := by ring
  -- splitting `w = (w - [w]) + ([w] - m) + m`
  have hpt : ∀ x ∈ P.cluster, |w x| ^ s ≤ 2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s +
      2 ^ (s - 1) * (|P.coarsen w x - m| ^ s + |m| ^ s)) := by
    intro x _
    have e : w x = (w x - P.coarsen w x) + ((P.coarsen w x - m) + m) := by ring
    calc |w x| ^ s = |(w x - P.coarsen w x) + ((P.coarsen w x - m) + m)| ^ s := by rw [← e]
      _ ≤ (|w x - P.coarsen w x| + (|P.coarsen w x - m| + |m|)) ^ s :=
          Real.rpow_le_rpow (abs_nonneg _) ((abs_add_le _ _).trans
            (add_le_add le_rfl (abs_add_le _ _))) (by linarith)
      _ ≤ 2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s + (|P.coarsen w x - m| + |m|) ^ s) :=
          add_rpow_le_two_rpow_mul (abs_nonneg _) (by positivity) hs
      _ ≤ 2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s +
            2 ^ (s - 1) * (|P.coarsen w x - m| ^ s + |m| ^ s)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl
            (add_rpow_le_two_rpow_mul (abs_nonneg _) (abs_nonneg _) hs)) hc0
  have hsum : ∑ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (U + 2 ^ (s - 1) * (V + (P.cluster.card : ℝ) * |m| ^ s)) := by
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [hU, hV, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc2 : 0 ≤ (2 : ℝ) ^ (s - 1) * 2 ^ (s - 1) := mul_nonneg hc0 hc0
  calc ∑ x ∈ P.cluster, |w x| ^ s
      ≤ 2 ^ (s - 1) * (U + 2 ^ (s - 1) * (V + (P.cluster.card : ℝ) * |m| ^ s)) := hsum
    _ ≤ 2 ^ (s - 1) * (U + 2 ^ (s - 1) * (V + 2 ^ (s - 1) * (V + U))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl hmV) hc0)) hc0
    _ ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) * (U + V) := by
        nlinarith [mul_nonneg hc2 hU0, mul_nonneg hc0 hV0, mul_nonneg hc0 (mul_nonneg hc2 hU0),
          mul_nonneg hc0 (mul_nonneg hc0 hV0)]
    _ ≤ 2 ^ (s - 1) * (1 + 2 ^ (s - 1) + 2 ^ (s - 1) * 2 ^ (s - 1)) *
          ((A + S * B ^ (s / t)) * W ^ (s / t)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hUW, hVW]) (by positivity)
    _ = _ := by ring

/-- **Armstrong and Dario, Proposition 3.4, from the lattice Sobolev inequality** (case
`∑_{cl_𝒫(U)} [w]_𝒫 = 0`). -/
theorem sum_rpow_le_of_latticeSobolevOn_of_sum_coarsen {s t A B S : ℝ} (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hts : t ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) {a b : Vertex d → ℝ}
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hLS : LatticeSobolevOn P.domain s t S)
    (w : Vertex d → ℝ)
    (h32 : ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      A * ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s)
    (h33 : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t ≤
      B * ∑ z ∈ P.cluster, b z * gradNormIn (openGraph ω) P.cluster w z ^ t)
    (hw : ∑ x ∈ P.domain, P.coarsen w x = 0) :
    ∑ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (A + S * B ^ (s / t)) *
        (∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
          gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  have htne : t ≠ 0 := ht0.ne'
  have hst : 1 ≤ s / t := by rw [le_div_iff₀ ht0]; linarith
  have hg0 : ∀ z, 0 ≤ gradNormIn (openGraph ω) P.cluster w z := fun z =>
    gradNormIn_nonneg _ _ _ _
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ z ∈ P.cluster, (a z ^ (t / s) + b z) *
      gradNormIn (openGraph ω) P.cluster w z ^ t := ⟨_, rfl⟩
  rw [← hW]
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (add_nonneg (Real.rpow_nonneg (ha z) _) (hb z))
      (Real.rpow_nonneg (hg0 z) _)
  have hc0 : (0 : ℝ) ≤ 2 ^ (s - 1) := by positivity
  have hUW : ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤ A * W ^ (s / t) := by
    refine h32.trans (mul_le_mul_of_nonneg_left ?_ hA)
    calc ∑ z ∈ P.cluster, a z * gradNormIn (openGraph ω) P.cluster w z ^ s
        = ∑ z ∈ P.cluster, (a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          Finset.sum_congr rfl fun z _ => by
            have e1 : (a z ^ (t / s)) ^ (s / t) = a z := by
              rw [← Real.rpow_mul (ha z), show t / s * (s / t) = 1 by field_simp, Real.rpow_one]
            have e2 : (gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) =
                gradNormIn (openGraph ω) P.cluster w z ^ s := by
              rw [← Real.rpow_mul (hg0 z), show t * (s / t) = s by field_simp]
            rw [Real.mul_rpow (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _), e1, e2]
      _ ≤ (∑ z ∈ P.cluster, a z ^ (t / s) * gradNormIn (openGraph ω) P.cluster w z ^ t) ^ (s / t) :=
          sum_rpow_le_rpow_sum _ _ hst fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _)
      _ ≤ W ^ (s / t) := by
          rw [hW]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun z _ =>
            mul_nonneg (Real.rpow_nonneg (ha z) _) (Real.rpow_nonneg (hg0 z) _))
            (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (hb z)) (Real.rpow_nonneg (hg0 z) _)) (by linarith)
  have hVW : ∑ x ∈ P.cluster, |P.coarsen w x| ^ s ≤ S * B ^ (s / t) * W ^ (s / t) := by
    have h1 : ∑ x ∈ P.cluster, |P.coarsen w x| ^ s ≤
        ∑ x ∈ P.domain, |P.coarsen w x - (∑ y ∈ P.domain, P.coarsen w y) / P.domain.card| ^ s := by
      rw [hw, zero_div]
      simp only [sub_zero]
      exact Finset.sum_le_sum_of_subset_of_nonneg P.cluster_subset fun _ _ _ =>
        Real.rpow_nonneg (abs_nonneg _) _
    have h3 : (∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^
        (s / t) ≤ (B * W) ^ (s / t) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (h33.trans ?_) (by linarith)
      rw [hW]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Real.rpow_nonneg (ha z) _)) (Real.rpow_nonneg (hg0 z) _)) hB
    rw [Real.mul_rpow hB hW0] at h3
    calc ∑ x ∈ P.cluster, |P.coarsen w x| ^ s
        ≤ ∑ x ∈ P.domain, |P.coarsen w x - (∑ y ∈ P.domain, P.coarsen w y) / P.domain.card| ^ s :=
          h1
      _ ≤ S * (∑ x ∈ P.domain,
            gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ t) ^ (s / t) :=
          hLS (P.coarsen w)
      _ ≤ S * (B ^ (s / t) * W ^ (s / t)) := mul_le_mul_of_nonneg_left h3 hS
      _ = S * B ^ (s / t) * W ^ (s / t) := by ring
  have hpt : ∀ x ∈ P.cluster, |w x| ^ s ≤
      2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s + |P.coarsen w x| ^ s) := by
    intro x _
    have e : w x = (w x - P.coarsen w x) + P.coarsen w x := by ring
    calc |w x| ^ s = |(w x - P.coarsen w x) + P.coarsen w x| ^ s := by rw [← e]
      _ ≤ (|w x - P.coarsen w x| + |P.coarsen w x|) ^ s :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by linarith)
      _ ≤ _ := add_rpow_le_two_rpow_mul (abs_nonneg _) (abs_nonneg _) hs
  calc ∑ x ∈ P.cluster, |w x| ^ s
      ≤ ∑ x ∈ P.cluster, 2 ^ (s - 1) * (|w x - P.coarsen w x| ^ s + |P.coarsen w x| ^ s) :=
        Finset.sum_le_sum hpt
    _ = 2 ^ (s - 1) * (∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s +
          ∑ x ∈ P.cluster, |P.coarsen w x| ^ s) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ (s - 1) * (A * W ^ (s / t) + S * B ^ (s / t) * W ^ (s / t)) :=
        mul_le_mul_of_nonneg_left (add_le_add hUW hVW) hc0
    _ = 2 ^ (s - 1) * (A + S * B ^ (s / t)) * W ^ (s / t) := by ring

end CoarseData

end Rigidity.Percolation
