import Rigidity.Proofs.Regularity.PlanarCorrectorScale

/-!
# The uniform sublinearity of the planar correctors

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19): the bound (1.18) in `L̲²` upgrades
to the uniform norm, (1.22). At the triadic scale `N = 9 · 3^m`, with the minimal scales of the
Lipschitz estimate at the vertices of `{|z_i| ≤ 3N}` and the sides of the partition cubes of
`{|z_i| ≤ 2N}` at most `y` and `3y`, and `‖χ‖_{L̲²(𝒞_∞ ∩ B_{6N})} ≤ K |q| N y^{-28}`,
`abs_corrector_le_at_scale` gives `|χ(x)| ≤ c₃ y⁷ |q| + c₄ |q| N y^{-7}` for `x ∈ 𝒞_∞`,
`|x_i| ≤ N`: the comparison with the coarsening and the interpolation inequality on the box
`x + [0, t]²`, `t = ⌊N y^{-14}⌋`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
open Rigidity.External
open scoped Classical

variable {ω : Configuration 2}

/-- The algebra of the two terms of `abs_le_of_scale_bounds` at one scale. -/
theorem scale_terms_le {N y t K CL q L B : ℝ} (hN : 0 < N) (hy : 1 ≤ y) (ht0 : 0 ≤ t)
    (ht : t ≤ N / y ^ 14) (ht1 : N / y ^ 14 ≤ t + 1) (hq : 0 ≤ q)
    (hL : L = CL * y ^ 3 * q) (hB : B = K * q * N / y ^ 28) :
    (81 * (3 * y) ^ 2) ^ 2 * L +
        √(2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * B ^ 2)) +
          8 * t ^ 2 * ((81 * (3 * y) ^ 2) ^ 2 * L) ^ 2) ≤
      729 ^ 2 * CL * y ^ 7 * q + √(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N / y ^ 7 := by
  have hy0 : 0 < y := by linarith
  have hyp : ∀ n : ℕ, 0 < y ^ n := fun n => pow_pos hy0 n
  have hy14 : 1 ≤ y ^ 12 := one_le_pow₀ hy
  have hA : (81 * (3 * y) ^ 2) ^ 2 * L = 729 ^ 2 * CL * y ^ 7 * q := by rw [hL]; ring
  rw [hA]
  gcongr
  have htp : 0 < t + 1 := by linarith
  have h1 : 2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * B ^ 2)) ≤
      4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
    have hinv : 1 / (t + 1) ^ 2 ≤ y ^ 28 / N ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have := pow_le_pow_left₀ (by positivity) ht1 2
      rw [div_pow, div_le_iff₀ (by positivity), ← pow_mul] at this
      norm_num at this
      linarith
    rw [hB]
    calc 2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2))
        = 2 * (1 / (t + 1) ^ 2) * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2)) := by
          ring
      _ ≤ 2 * (y ^ 28 / N ^ 2) * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2)) := by
          gcongr
      _ = 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 26 := by
          field_simp
          ring
      _ ≤ 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
          apply div_le_div_of_nonneg_left (by positivity) (hyp 14)
          calc y ^ 14 = y ^ 14 * 1 := (mul_one _).symm
            _ ≤ y ^ 14 * y ^ 12 := mul_le_mul_of_nonneg_left hy14 (hyp 14).le
            _ = y ^ 26 := by ring
  have h2 : 8 * t ^ 2 * (729 ^ 2 * CL * y ^ 7 * q) ^ 2 ≤
      8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
    have ht2 : t ^ 2 ≤ N ^ 2 / y ^ 28 := by
      have := pow_le_pow_left₀ ht0 ht 2
      rw [div_pow, ← pow_mul] at this
      exact this
    calc 8 * t ^ 2 * (729 ^ 2 * CL * y ^ 7 * q) ^ 2
        ≤ 8 * (N ^ 2 / y ^ 28) * (729 ^ 2 * CL * y ^ 7 * q) ^ 2 := by gcongr
      _ = 8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
          field_simp
  have h3 : 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 + 8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 =
      (√(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N / y ^ 7) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    field_simp
    ring
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ √(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N /
    y ^ 7), ← h3]
  exact Real.sqrt_le_sqrt (add_le_add h1 h2)

/-- **The uniform bound of the corrector at one scale** `N = 9 · 3^m`. -/
theorem abs_corrector_le_at_scale (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) (q : Fin 2 → ℝ) (u : C → ℝ) (hu : u ∈ harmonicGrowthSpace C 1)
    {m : ℕ} {y K C₀ κ ℓ : ℝ} (hy : 1 ≤ y) (hy14 : 2 ≤ y ^ 14) (hyN : 30 * y ≤ 9 * 3 ^ m)
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 54 ℓ κ)
    (hℓ : ℓ ≤ 3 ^ m) (Yv : Vertex 2 → ℝ)
    (hR3 : ∀ a : Vertex 2, (∀ i, |a i| ≤ 3 * (9 * 3 ^ m)) → ∀ (R : ℝ), 2 * Yv a ≤ R →
      ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C a R,
        (∀ z : C, (componentGraph C).Adj x z → z ∈ componentEuclideanBall C a R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Yv a ≤ r → r ≤ R / 2 →
        componentBallL2 C a r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C a R v)
    (hYle : ∀ a : Vertex 2, (∀ i, |a i| ≤ 3 * (9 * 3 ^ m)) → Yv a ≤ y)
    (hsize : ∀ z : Vertex 2, (∀ i, |z i| ≤ 2 * (9 * 3 ^ m)) →
      (3 : ℝ) ^ (planarPartCube ω z).scale ≤ 3 * y)
    (hL2 : componentBallL2 C 0 (6 * (9 * 3 ^ m)) (componentCorrector C q u) ≤
      K * (|q 0| + |q 1|) * (9 * 3 ^ m) / y ^ 28)
    (x : C) (hx : ∀ i, |x.val i| ≤ 9 * 3 ^ m) :
    |componentCorrector C q u x| ≤
      729 ^ 2 * (196 * C₀ * (Real.sqrt (18225 / κ) * K + 1) + 1) * y ^ 7 * (|q 0| + |q 1|) +
        √(4050 * K ^ 2 + 8 * 729 ^ 4 * (196 * C₀ * (Real.sqrt (18225 / κ) * K + 1) + 1) ^ 2) *
          (|q 0| + |q 1|) * (9 * 3 ^ m) / y ^ 7 := by
  set Nn : ℕ := 9 * 3 ^ m with hNn
  have hNr : ((Nn : ℕ) : ℝ) = 9 * 3 ^ m := by rw [hNn]; push_cast; ring
  have hNz : ((Nn : ℕ) : ℤ) = 9 * 3 ^ m := by rw [hNn]; push_cast; ring
  have hN0 : (0 : ℝ) < 9 * 3 ^ m := by positivity
  have hy0 : 0 < y := by linarith
  have hq : 0 ≤ |q 0| + |q 1| := by positivity
  set χ := componentCorrector C q u with hχ
  set w := Rigidity.Section3.extend C χ with hw
  set B : ℝ := K * (|q 0| + |q 1|) * (9 * 3 ^ m) / y ^ 28 with hBdef
  set CB : ℝ := Real.sqrt (18225 / κ) * K with hCBdef
  have hCB : 0 ≤ CB := by positivity
  set CL : ℝ := 196 * C₀ * (CB + 1) + 1 with hCLdef
  have hCL : 0 ≤ CL := by positivity
  -- the norms on the balls `B_N(a)`
  have hB' : ∀ a : C, (∀ i, |a.val i| ≤ 3 * (9 * 3 ^ m)) →
      componentBallL2 C a.val (9 * 3 ^ m) χ ≤ CB * (|q 0| + |q 1|) * (9 * 3 ^ m) := by
    intro a ha
    refine (componentBallL2_corrector_le C hκ hcube hℓ χ hL2 ha).trans ?_
    rw [hCBdef]
    have hy28 : 1 ≤ y ^ 28 := one_le_pow₀ hy
    have : K * (|q 0| + |q 1|) * (9 * 3 ^ m) / y ^ 28 ≤ K * (|q 0| + |q 1|) * (9 * 3 ^ m) :=
      div_le_self (by positivity) hy28
    calc Real.sqrt (18225 / κ) * (K * (|q 0| + |q 1|) * (9 * 3 ^ m) / y ^ 28)
        ≤ Real.sqrt (18225 / κ) * (K * (|q 0| + |q 1|) * (9 * 3 ^ m)) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = _ := by ring
  -- the increments
  have hgrad : ∀ a b : Vertex 2, (∀ i, |a i| ≤ 3 * Nn) → (∀ i, |b i| ≤ 3 * Nn) →
      (openGraph ω).Adj a b → |w a - w b| ≤ CL * y ^ 3 * (|q 0| + |q 1|) := by
    intro a b ha _ hab
    have ha' : ∀ i, |a i| ≤ 3 * (9 * 3 ^ m) := fun i => by have := ha i; rw [hNz] at this; exact this
    exact abs_extend_sub_le_of_adj C q u hu hN0 hC₀ hCB hy (by linarith) Yv hR3 hYle hB' a b ha' hab
  -- the sum of squares
  have hM := sum_sq_extend_le C χ (N := Nn) (B := B)
    (by rw [hNn]; have := Nat.one_le_pow m 3 (by norm_num); omega)
    (by rw [hNr]; exact hL2)
  -- the box of the interpolation
  set t : ℕ := ⌊(9 * 3 ^ m : ℝ) / y ^ 14⌋₊ with htdef
  have ht : (t : ℝ) ≤ (9 * 3 ^ m : ℝ) / y ^ 14 := Nat.floor_le (by positivity)
  have ht1 : (9 * 3 ^ m : ℝ) / y ^ 14 ≤ t + 1 := (Nat.lt_floor_add_one _).le
  have htN : t + 1 ≤ Nn := by
    have h1 : (9 * 3 ^ m : ℝ) / y ^ 14 ≤ (9 * 3 ^ m) / 2 :=
      div_le_div_of_nonneg_left hN0.le (by norm_num) hy14
    have h2 : (30 : ℝ) ≤ 9 * 3 ^ m := by
      have : (1 : ℝ) ≤ y := hy
      linarith
    have h3 : ((t + 1 : ℕ) : ℝ) ≤ (Nn : ℝ) := by
      push_cast; rw [hNr]; linarith
    exact_mod_cast h3
  have hsize' : ∀ z : Vertex 2, (∀ i, |z i| ≤ 2 * Nn) →
      (3 : ℝ) ^ (planarPartCube ω z).scale ≤ 3 * y := fun z hz =>
    hsize z fun i => by have := hz i; rw [hNz] at this; exact this
  have hδN : 10 * (3 * y) ≤ (Nn : ℝ) := by rw [hNr]; linarith
  have hx' : ∀ i, |x.val i| ≤ Nn := fun i => by have := hx i; rw [hNz]; exact this
  have hinfx : ((openGraph ω).connectedComponentMk x.val).supp.Infinite := by
    have hC : (openGraph ω).connectedComponentMk x.val = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 x.2
    rw [hC]; exact hinf
  have hmain := abs_le_of_scale_bounds hP w htN (by positivity) hsize' hδN hgrad hM hx' hinfx
  have hwx : w x.val = χ x := extend_val C χ x
  rw [hwx, hNr] at hmain
  refine hmain.trans ?_
  have := scale_terms_le (N := 9 * 3 ^ m) (y := y) (t := t) (K := K) (CL := CL)
    (q := |q 0| + |q 1|) (L := CL * y ^ 3 * (|q 0| + |q 1|)) (B := B) hN0 hy (Nat.cast_nonneg _)
    ht ht1 hq rfl (by rw [hBdef])
  convert this using 2

end Rigidity.Proofs.Regularity
