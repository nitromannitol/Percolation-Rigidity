import Rigidity.Proofs.Cluster.CoarseSobolev
import Rigidity.Vendor.LHCH.Support.Analysis.WeightedSobolev

/-!
# The lattice Sobolev inequality with zero boundary values

For `d ≥ 2`, `s ≥ d/(d-1)` and `s_* = sd/(s+d)`, there is a constant `S(d, s)` such that for every
finite set `D ⊆ ℤ^d` and every `f` vanishing on the lattice boundary of `D` (the vertices of `D`
with a lattice neighbour outside `D`),
`∑_{x ∈ D} |f(x)|^s ≤ S (∑_{x ∈ D} |∇f|^{s_*}(x))^{s/s_*}`,
with `|∇f|(x)` the magnitude of the lattice gradient on `D`. This is the usual Sobolev inequality
on `ℤ^d` used by Armstrong and Dario in the proof of Proposition 3.4. The proof applies the
lattice `ℓ¹` Sobolev inequality (Gagliardo–Nirenberg) to the zero extension of `|f|^γ`,
`γ = s(d-1)/d`, whose increments vanish off the edges of `D`; bounds the increments of `|f|^γ` by
`γ (|f(x)|^{γ-1} + |f(y)|^{γ-1}) |f(y) - f(x)|`; and uses Hölder's inequality with the exponents
`s_*/(s_* - 1)` and `s_*`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The increment of a function along an edge into a finite set is at most `√2` times the
magnitude of its gradient on the set. -/
theorem abs_sub_le_sqrt_two_mul_gradNormIn (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) {x y : Vertex d} (hy : y ∈ S) (hxy : G.Adj x y) :
    |f x - f y| ≤ √2 * gradNormIn G S f x := by
  have h : (f x - f y) ^ 2 ≤ ∑ z ∈ S, if G.Adj x z then (f x - f z) ^ 2 else 0 := by
    have := Finset.single_le_sum (f := fun z => if G.Adj x z then (f x - f z) ^ 2 else 0)
      (fun z _ => by split_ifs <;> positivity) hy
    simpa [hxy] using this
  rw [gradNormIn, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The lattice Sobolev inequality with zero boundary values for `d ≥ 2`, `s > d/(d-1)` and
`t = sd/(s+d)`: there is `S ≥ 0` such that for every finite `D ⊆ ℤ^d` and every `f` vanishing at
the vertices of `D` having a lattice neighbour outside `D`,
`∑_{x ∈ D} |f(x)|^s ≤ S (∑_{x ∈ D} |∇f|^t(x))^{s/t}`. -/
theorem exists_sum_rpow_le_of_eq_zero_on_boundary_of_lt (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) < s) (ht : t = s * d / (s + d)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (D : Finset (Vertex d)) (f : Vertex d → ℝ),
      (∀ x ∈ D, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ D → f x = 0) →
      ∑ x ∈ D, |f x| ^ s ≤
        S * (∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ t) ^ (s / t) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hsd : (d : ℝ) < s * (d - 1) := by rwa [div_lt_iff₀ hdm] at hs
  have hs0 : 0 < s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have hk : 0 < s * d - s - d := by nlinarith
  have hsd1 : 0 < s * d := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  -- the exponents
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = s * (d - 1) / d := ⟨_, rfl⟩
  have hγ1 : 1 < γ := by rw [hγ, one_lt_div hd0]; linarith
  have hγ0 : 0 < γ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = s * d / (s * d - s - d) := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq, one_lt_div hk]; linarith
  have hq0 : 0 < q := by linarith
  have hconj : q.HolderConjugate t := by
    rw [Real.holderConjugate_iff]
    refine ⟨hq1, ?_⟩
    rw [hq, ht, inv_div, inv_div, ← add_div, div_eq_one_iff_eq hsd1.ne']
    ring
  have hγp : γ * ((d : ℝ) / (d - 1)) = s := by
    rw [hγ]
    field_simp
  have hγq : (γ - 1) * q = s := by
    have e : γ - 1 = (s * d - s - d) / d := by
      rw [hγ]
      field_simp
    rw [e, hq, div_mul_div_comm, div_eq_iff (mul_ne_zero hd0.ne' hk.ne')]
    ring
  have hexp : ((d : ℝ) - 1) / d = 1 / s + 1 / q := by
    rw [hq, one_div_div]
    field_simp
    ring
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 2 ^ (q - 1) * (2 * d) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = d * √2 ^ t := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  have hK0 : 0 ≤ γ * c₁ ^ (1 / q) := mul_nonneg hγ0.le (Real.rpow_nonneg hc₁0 _)
  refine ⟨(γ * c₁ ^ (1 / q)) ^ s * c₂ ^ (s / t),
    mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hc₂0 _), ?_⟩
  intro D f hf
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ x ∈ D, |f x| ^ s := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ t :=
    ⟨_, rfl⟩
  rw [← hM, ← hG]
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact Finset.sum_nonneg fun x _ => Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _
  have hadj : ∀ (x : Vertex d) (j : Fin d),
      (nearestNeighborGraph d).Adj x (x + LatticeProb.unit j) := fun x j => ⟨j, Or.inl rfl⟩
  -- the zero extension of `|f|^γ`
  obtain ⟨v, hv⟩ : ∃ v : Vertex d → ℝ, v = fun x => if x ∈ D then |f x| ^ γ else 0 := ⟨_, rfl⟩
  have hv0 : ∀ x, x ∉ D → v x = 0 := fun x hx => by simp [hv, hx]
  have hvS : ∀ x (j : Fin d), v (x + LatticeProb.unit j) ≠ v x → x ∈ D := by
    intro x j hne
    by_contra hx
    apply hne
    rw [hv0 x hx]
    by_cases hxj : x + LatticeProb.unit j ∈ D
    · have h0 := hf _ hxj x (hadj x j).symm hx
      simp [hv, hxj, h0, Real.zero_rpow hγ0.ne']
    · exact hv0 _ hxj
  have hGN := LatticeHC.sum_rpow_le_sum_abs_grad hd D D v hv0 hvS
  have hleft : ∑ x ∈ D, |v x| ^ ((d : ℝ) / (d - 1)) = M := by
    rw [hM]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hv, hx, if_true]
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _), hγp]
  -- the increments of `|f|^γ`
  obtain ⟨A, hA⟩ : ∃ A : Vertex d → Fin d → ℝ, A = fun x j =>
      if x + LatticeProb.unit j ∈ D then
        |f x| ^ (γ - 1) + |f (x + LatticeProb.unit j)| ^ (γ - 1) else 0 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Vertex d → Fin d → ℝ, E = fun x j =>
      if x + LatticeProb.unit j ∈ D then |f (x + LatticeProb.unit j) - f x| else 0 := ⟨_, rfl⟩
  have hA0 : ∀ x j, 0 ≤ A x j := fun x j => by
    simp only [hA]
    split_ifs <;> positivity
  have hE0 : ∀ x j, 0 ≤ E x j := fun x j => by
    simp only [hE]
    split_ifs <;> positivity
  have hpt : ∀ x ∈ D, ∀ j : Fin d, |v (x + LatticeProb.unit j) - v x| ≤ γ * (A x j * E x j) := by
    intro x hx j
    by_cases hxj : x + LatticeProb.unit j ∈ D
    · simp only [hv, hA, hE, hx, hxj, if_true]
      exact (LatticeHC.abs_abs_rpow_sub_le (f x) (f (x + LatticeProb.unit j)) hγ1.le).trans
        (le_of_eq (by ring))
    · have h0 := hf x hx _ (hadj x j) hxj
      simp [hv, hA, hE, hx, hxj, h0, Real.zero_rpow hγ0.ne']
  have hsumR : ∑ x ∈ D, ∑ j : Fin d, |v (x + LatticeProb.unit j) - v x| ≤
      γ * ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), A p.1 p.2 * E p.1 p.2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx => by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hpt x hx j
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := D ×ˢ (Finset.univ : Finset (Fin d)))
    (f := fun p => A p.1 p.2) (g := fun p => E p.1 p.2) hconj (fun p _ => hA0 _ _)
    (fun p _ => hE0 _ _)
  -- the sum of `A^q`
  have hshift : ∀ j : Fin d, ∑ x ∈ D, (if x + LatticeProb.unit j ∈ D then
      |f (x + LatticeProb.unit j)| ^ s else 0) ≤ M := by
    intro j
    rw [← Finset.sum_filter, hM]
    rw [← Finset.sum_image (s := D.filter (fun x => x + LatticeProb.unit j ∈ D))
      (g := fun x => x + LatticeProb.unit j) (f := fun y => |f y| ^ s)
      (fun a _ b _ h => add_right_cancel h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
      Real.rpow_nonneg (abs_nonneg _) _
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact (Finset.mem_filter.1 hx).2
  have hAq : ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), A p.1 p.2 ^ q ≤ c₁ * M := by
    have hpt2 : ∀ x ∈ D, ∀ j : Fin d, A x j ^ q ≤ 2 ^ (q - 1) * (|f x| ^ s +
        (if x + LatticeProb.unit j ∈ D then |f (x + LatticeProb.unit j)| ^ s else 0)) := by
      intro x _ j
      by_cases hxj : x + LatticeProb.unit j ∈ D
      · simp only [hA, hxj, if_true]
        have h := add_rpow_le_two_rpow_mul (Real.rpow_nonneg (abs_nonneg (f x)) (γ - 1))
          (Real.rpow_nonneg (abs_nonneg (f (x + LatticeProb.unit j))) (γ - 1)) hq1.le
        rwa [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _), hγq] at h
      · simp only [hA, hxj, if_false, Real.zero_rpow hq0.ne', add_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)
    have h1 : ∑ x ∈ D, ∑ _j : Fin d, |f x| ^ s = d * M := by
      rw [hM, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∑ x ∈ D, ∑ j : Fin d, (if x + LatticeProb.unit j ∈ D then
        |f (x + LatticeProb.unit j)| ^ s else 0) ≤ d * M := by
      rw [Finset.sum_comm]
      calc _ ≤ ∑ _j : Fin d, M := Finset.sum_le_sum fun j _ => hshift j
        _ = d * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), A p.1 p.2 ^ q
        = ∑ x ∈ D, ∑ j : Fin d, A x j ^ q := Finset.sum_product _ _ _
      _ ≤ ∑ x ∈ D, ∑ j : Fin d, 2 ^ (q - 1) * (|f x| ^ s +
            (if x + LatticeProb.unit j ∈ D then |f (x + LatticeProb.unit j)| ^ s else 0)) :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => hpt2 x hx j
      _ = 2 ^ (q - 1) * (∑ x ∈ D, ∑ _j : Fin d, |f x| ^ s + ∑ x ∈ D, ∑ j : Fin d,
            (if x + LatticeProb.unit j ∈ D then |f (x + LatticeProb.unit j)| ^ s else 0)) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2 ^ (q - 1) * (d * M + d * M) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) (by positivity)
      _ = c₁ * M := by
          rw [hc₁]
          ring
  -- the sum of `E^t`
  have hEt : ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), E p.1 p.2 ^ t ≤ c₂ * G := by
    have hpt3 : ∀ x ∈ D, ∀ j : Fin d, E x j ^ t ≤
        √2 ^ t * gradNormIn (nearestNeighborGraph d) D f x ^ t := by
      intro x _ j
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _)]
      refine Real.rpow_le_rpow (hE0 x j) ?_ ht0.le
      simp only [hE]
      split_ifs with hxj
      · rw [abs_sub_comm]
        exact abs_sub_le_sqrt_two_mul_gradNormIn _ _ _ hxj (hadj x j)
      · exact mul_nonneg (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _)
    calc ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), E p.1 p.2 ^ t
        = ∑ x ∈ D, ∑ j : Fin d, E x j ^ t := Finset.sum_product _ _ _
      _ ≤ ∑ x ∈ D, ∑ _j : Fin d, √2 ^ t * gradNormIn (nearestNeighborGraph d) D f x ^ t :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => hpt3 x hx j
      _ = c₂ * G := by
          rw [hc₂, hG, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the Sobolev inequality for `|f|^γ` and Hölder
  have hAq0 : 0 ≤ ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), A p.1 p.2 ^ q :=
    Finset.sum_nonneg fun p _ => Real.rpow_nonneg (hA0 _ _) _
  have hEt0 : 0 ≤ ∑ p ∈ D ×ˢ (Finset.univ : Finset (Fin d)), E p.1 p.2 ^ t :=
    Finset.sum_nonneg fun p _ => Real.rpow_nonneg (hE0 _ _) _
  have hmain : M ^ (((d : ℝ) - 1) / d) ≤
      γ * ((c₁ * M) ^ (1 / q) * (c₂ * G) ^ (1 / t)) := by
    rw [hleft] at hGN
    refine hGN.trans (hsumR.trans (mul_le_mul_of_nonneg_left (hHolder.trans ?_) hγ0.le))
    exact mul_le_mul (Real.rpow_le_rpow hAq0 hAq (by positivity))
      (Real.rpow_le_rpow hEt0 hEt (by positivity)) (Real.rpow_nonneg hEt0 _)
      (Real.rpow_nonneg (mul_nonneg hc₁0 hM0) _)
  -- dividing by `M^{1/q}`
  rcases hM0.eq_or_lt with hMz | hMpos
  · rw [← hMz]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hc₂0 _))
      (Real.rpow_nonneg hG0 _)
  rw [hexp, Real.rpow_add hMpos, Real.mul_rpow hc₁0 hM0] at hmain
  have hMq : 0 < M ^ (1 / q) := Real.rpow_pos_of_pos hMpos _
  have h1s : M ^ (1 / s) ≤ γ * c₁ ^ (1 / q) * (c₂ * G) ^ (1 / t) := by
    refine le_of_mul_le_mul_right ?_ hMq
    calc M ^ (1 / s) * M ^ (1 / q) ≤ _ := hmain
      _ = γ * c₁ ^ (1 / q) * (c₂ * G) ^ (1 / t) * M ^ (1 / q) := by ring
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) h1s hs0.le
  rw [← Real.rpow_mul hM0, one_div_mul_cancel hs0.ne', Real.rpow_one] at hpow
  calc M ≤ (γ * c₁ ^ (1 / q) * (c₂ * G) ^ (1 / t)) ^ s := hpow
    _ = (γ * c₁ ^ (1 / q)) ^ s * c₂ ^ (s / t) * G ^ (s / t) := by
        rw [Real.mul_rpow hK0 (Real.rpow_nonneg (mul_nonneg hc₂0 hG0) _),
          ← Real.rpow_mul (mul_nonneg hc₂0 hG0), Real.mul_rpow hc₂0 hG0,
          show 1 / t * s = s / t by ring]
        ring

/-- **The lattice Sobolev inequality with zero boundary values at the endpoint** `s = d/(d-1)`,
`t = 1`: for every finite `D ⊆ ℤ^d`, `d ≥ 2`, and every `f` vanishing at the vertices of `D`
having a lattice neighbour outside `D`,
`∑_{x ∈ D} |f(x)|^{d/(d-1)} ≤ (√2 d)^{d/(d-1)} (∑_{x ∈ D} |∇f|(x))^{d/(d-1)}`. -/
theorem sum_rpow_le_of_eq_zero_on_boundary_endpoint (hd : 2 ≤ d) (D : Finset (Vertex d))
    (f : Vertex d → ℝ)
    (hf : ∀ x ∈ D, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ D → f x = 0) :
    ∑ x ∈ D, |f x| ^ ((d : ℝ) / (d - 1)) ≤
      (√2 * d) ^ ((d : ℝ) / (d - 1)) *
        (∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x) ^ ((d : ℝ) / (d - 1)) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hp0 : (0 : ℝ) < d / (d - 1) := div_pos hd0 hdm
  have hadj : ∀ (x : Vertex d) (j : Fin d),
      (nearestNeighborGraph d).Adj x (x + LatticeProb.unit j) := fun x j => ⟨j, Or.inl rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Vertex d → ℝ, v = fun x => if x ∈ D then f x else 0 := ⟨_, rfl⟩
  have hv0 : ∀ x, x ∉ D → v x = 0 := fun x hx => by simp [hv, hx]
  have hvS : ∀ x (j : Fin d), v (x + LatticeProb.unit j) ≠ v x → x ∈ D := by
    intro x j hne
    by_contra hx
    apply hne
    rw [hv0 x hx]
    by_cases hxj : x + LatticeProb.unit j ∈ D
    · have h0 := hf _ hxj x (hadj x j).symm hx
      simp [hv, hxj, h0]
    · exact hv0 _ hxj
  have hGN := LatticeHC.sum_rpow_le_sum_abs_grad hd D D v hv0 hvS
  have hleft : ∑ x ∈ D, |v x| ^ ((d : ℝ) / (d - 1)) = ∑ x ∈ D, |f x| ^ ((d : ℝ) / (d - 1)) :=
    Finset.sum_congr rfl fun x hx => by simp only [hv, hx, if_true]
  have hpt : ∀ x ∈ D, ∑ j : Fin d, |v (x + LatticeProb.unit j) - v x| ≤
      √2 * d * gradNormIn (nearestNeighborGraph d) D f x := by
    intro x hx
    have hterm : ∀ j : Fin d, |v (x + LatticeProb.unit j) - v x| ≤
        √2 * gradNormIn (nearestNeighborGraph d) D f x := by
      intro j
      by_cases hxj : x + LatticeProb.unit j ∈ D
      · simp only [hv, hx, hxj, if_true]
        rw [abs_sub_comm]
        exact abs_sub_le_sqrt_two_mul_gradNormIn _ _ _ hxj (hadj x j)
      · have h0 := hf x hx _ (hadj x j) hxj
        simp only [hv, hx, hxj, if_true, if_false, h0, sub_zero, abs_zero]
        exact mul_nonneg (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _)
    calc ∑ j : Fin d, |v (x + LatticeProb.unit j) - v x|
        ≤ ∑ _j : Fin d, √2 * gradNormIn (nearestNeighborGraph d) D f x :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = √2 * d * gradNormIn (nearestNeighborGraph d) D f x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hR : ∑ x ∈ D, ∑ j : Fin d, |v (x + LatticeProb.unit j) - v x| ≤
      √2 * d * ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  rw [hleft] at hGN
  have hM0 : 0 ≤ ∑ x ∈ D, |f x| ^ ((d : ℝ) / (d - 1)) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) (hGN.trans hR) hp0.le
  rw [← Real.rpow_mul hM0, show ((d : ℝ) - 1) / d * (d / (d - 1)) = 1 by field_simp,
    Real.rpow_one, Real.mul_rpow (by positivity)
      (Finset.sum_nonneg fun x _ => gradNormIn_nonneg _ _ _ _)] at h1
  exact h1

/-- **The lattice Sobolev inequality with zero boundary values.** For `d ≥ 2`, `s ≥ d/(d-1)` and
`t = sd/(s+d)`, there is `S ≥ 0` such that for every finite `D ⊆ ℤ^d` and every `f` vanishing at
the vertices of `D` having a lattice neighbour outside `D`,
`∑_{x ∈ D} |f(x)|^s ≤ S (∑_{x ∈ D} |∇f|^t(x))^{s/t}`. -/
theorem exists_sum_rpow_le_of_eq_zero_on_boundary (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) ≤ s) (ht : t = s * d / (s + d)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (D : Finset (Vertex d)) (f : Vertex d → ℝ),
      (∀ x ∈ D, ∀ y, (nearestNeighborGraph d).Adj x y → y ∉ D → f x = 0) →
      ∑ x ∈ D, |f x| ^ s ≤
        S * (∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ t) ^ (s / t) := by
  rcases hs.lt_or_eq with hs | hs
  · exact exists_sum_rpow_le_of_eq_zero_on_boundary_of_lt hd hs ht
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  subst hs
  have ht1 : t = 1 := by
    have hne : (d : ℝ) / (d - 1) + d ≠ 0 := by positivity
    rw [ht, div_eq_one_iff_eq hne]
    field_simp
    ring
  subst ht1
  refine ⟨(√2 * d) ^ ((d : ℝ) / (d - 1)), by positivity, fun D f hf => ?_⟩
  simp only [Real.rpow_one, div_one]
  exact sum_rpow_le_of_eq_zero_on_boundary_endpoint hd D f hf

end Rigidity.Percolation
