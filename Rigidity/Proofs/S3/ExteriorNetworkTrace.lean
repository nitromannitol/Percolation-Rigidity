import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import LatticeProb.Network.Dirichlet

/-!
# The trace of a network on a finite set of terminals

For a connected locally finite graph `G` with a finite set of terminals `T`, and a linear space `W`
of functions on the vertices (the admissible potentials: harmonic off `T`, with a uniqueness
property, the Green reciprocity and the minimum principle), the response of `W` at the terminals is
a finite network: there are conductances `c t s = c s t ≥ 0` on `T × T` with `∑_s c t s ≤ deg t`
such that every `w ∈ W` satisfies Kirchhoff's law `Δw(t) = ∑_s c t s (w(s) - w(t))` at each
terminal (`exists_traceNetwork`).

Two instances, used for the exterior of the surgery region in `ExteriorNetwork.lean`:
* a finite graph (`exists_traceNetwork_of_finite`): `W` is the space of all functions harmonic
  off `T`, solved by the Dirichlet problem of `LatticeProb.Network`;
* an infinite graph with Green columns `g_r` (`-Δ g_r = δ_r`) at the terminals whose zero-sum
  combinations decay along a profile `φ` with a vanishing boundary sum, and with the Liouville
  property for a class `Sub` containing the Green columns (`exists_traceNetwork_of_green`): `W` is
  the span of the constants and the zero-sum combinations of the Green columns, and every function
  of `Sub` harmonic off `T` with zero total flux belongs to `W`.

The uniqueness is the energy identity `∑_B f Δf = -½ ∑_B ∑_{y∼x} (∇f)² + ½ ∑_{∂B} (f(y)² - f(x)²)`
(`sum_mul_lap_eq`), the reciprocity is Green's identity (`sum_green_eq_boundary`), and the minimum
principle is the sign of the flux out of a finite set (`sum_lap_neg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Rigidity.Proofs.S3.NetworkTrace

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- The neighbour-sum Laplacian of a locally finite graph (unit conductances). -/
noncomputable def lap (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, (f y - f x)

/-! ### Summation by parts on a finite set -/

/-- The interior part of the double sum of an antisymmetric function vanishes. -/
theorem sum_sum_inside_eq_zero (B : Finset V) (F : V → V → ℝ)
    (hF : ∀ x y, G.Adj x y → F y x = -F x y) :
    ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∈ B), F x y = 0 := by
  classical
  have h1 : ∀ x, ∑ y ∈ (G.neighborFinset x).filter (· ∈ B), F x y =
      ∑ y ∈ B, if G.Adj x y then F x y else 0 := by
    intro x
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_comm]
  simp_rw [h1]
  have h2 : ∀ S : ℝ, S = -S → S = 0 := fun S h => by linarith
  apply h2
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : G.Adj a b
  · rw [if_pos h.symm, if_pos h, hF a b h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h, neg_zero]

/-- The double sum of an antisymmetric function over a finite set reduces to its boundary. -/
theorem sum_sum_neighbor_eq_boundary (B : Finset V) (F : V → V → ℝ)
    (hF : ∀ x y, G.Adj x y → F y x = -F x y) :
    ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, F x y =
      ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), F x y := by
  have h := sum_sum_inside_eq_zero G B F hF
  rw [← add_zero (∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), F x y), ← h,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The total Laplacian of a finite set is the flux through its boundary. -/
theorem sum_lap_eq_boundary (B : Finset V) (f : V → ℝ) :
    ∑ x ∈ B, lap G f x = ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (f y - f x) :=
  sum_sum_neighbor_eq_boundary G B (fun x y => f y - f x) (fun _ _ _ => by ring)

/-- The energy identity on a finite set. -/
theorem sum_mul_lap_eq (B : Finset V) (f : V → ℝ) :
    ∑ x ∈ B, f x * lap G f x =
      -(1 / 2) * ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, (f y - f x) ^ 2 +
        (1 / 2) * ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (f y ^ 2 - f x ^ 2) := by
  have h := sum_sum_neighbor_eq_boundary G B (fun x y => f y ^ 2 - f x ^ 2)
    (fun _ _ _ => by ring)
  rw [← h, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lap, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- Green's identity on a finite set. -/
theorem sum_green_eq_boundary (B : Finset V) (u v : V → ℝ) :
    ∑ x ∈ B, (u x * lap G v x - v x * lap G u x) =
      ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (u x * v y - v x * u y) := by
  rw [← sum_sum_neighbor_eq_boundary G B (fun x y => u x * v y - v x * u y)
    (fun _ _ _ => by ring)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lap, lap, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq V] in
/-- The Laplacian of a finite combination. -/
theorem lap_sum_smul {ι : Type*} (S : Finset ι) (a : ι → ℝ) (f : ι → V → ℝ) (x : V) :
    lap G (∑ i ∈ S, a i • f i) x = ∑ i ∈ S, a i * lap G (f i) x := by
  simp only [lap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq V] in
theorem lap_add (f g : V → ℝ) (x : V) : lap G (f + g) x = lap G f x + lap G g x := by
  simp only [lap, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq V] in
theorem lap_smul (a : ℝ) (f : V → ℝ) (x : V) : lap G (a • f) x = a * lap G f x := by
  simp only [lap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq V] in
theorem lap_const (κ : ℝ) (x : V) : lap G (fun _ => κ) x = 0 := by
  simp only [lap, sub_self, Finset.sum_const_zero]

omit [DecidableEq V] in
theorem lap_sub_const (f : V → ℝ) (κ : ℝ) (x : V) :
    lap G (fun z => f z - κ) x = lap G f x := by
  simp only [lap]
  exact Finset.sum_congr rfl fun y _ => by ring

/-! ### Connectivity -/

omit [DecidableEq V] [G.LocallyFinite] in
theorem eq_of_reachable {f : V → ℝ} (hf : ∀ x y, G.Adj x y → f x = f y) {x y : V}
    (h : G.Reachable x y) : f x = f y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

omit [DecidableEq V] [G.LocallyFinite] in
theorem exists_boundary_adj (hG : G.Connected) (A : Finset V) {a z : V} (ha : a ∈ A)
    (hz : z ∉ A) : ∃ x ∈ A, ∃ y, G.Adj x y ∧ y ∉ A := by
  obtain ⟨p⟩ := hG.preconnected a z
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (A : Set V) ha hz
  exact ⟨d.fst, hd1, d.snd, d.adj, hd2⟩

/-- **The sign of the flux**: if every boundary value of a finite proper nonempty set is below
the adjacent interior value, the total Laplacian of the set is negative. -/
theorem sum_lap_neg (hG : G.Connected) (A : Finset V) {a z : V} (ha : a ∈ A) (hz : z ∉ A)
    (f : V → ℝ) (hf : ∀ x ∈ A, ∀ y, G.Adj x y → y ∉ A → f y < f x) :
    ∑ x ∈ A, lap G f x < 0 := by
  rw [sum_lap_eq_boundary]
  obtain ⟨x0, hx0, y0, hadj, hy0⟩ := exists_boundary_adj G hG A ha hz
  have hle : ∀ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (· ∉ A), (f y - f x) ≤ 0 := by
    intro x hx
    refine Finset.sum_nonpos fun y hy => ?_
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    linarith [hf x hx y hy.1 hy.2]
  have hlt : ∑ y ∈ (G.neighborFinset x0).filter (· ∉ A), (f y - f x0) < 0 := by
    have hne : ((G.neighborFinset x0).filter (· ∉ A)).Nonempty :=
      ⟨y0, Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hadj, hy0⟩⟩
    calc _ < ∑ y ∈ (G.neighborFinset x0).filter (· ∉ A), (0 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne fun y hy => by
            rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
            linarith [hf x0 hx0 y hy.1 hy.2]
      _ = 0 := Finset.sum_const_zero
  calc _ < ∑ x ∈ A, (0 : ℝ) := Finset.sum_lt_sum hle ⟨x0, hx0, hlt⟩
    _ = 0 := Finset.sum_const_zero

/-! ### Uniqueness, reciprocity and the minimum principle -/

/-- **Uniqueness by energy**: a function harmonic off `T`, with zero total flux, vanishing on `T`
and whose deviation from a constant has vanishing boundary energy terms, vanishes. -/
theorem eq_zero_of_energy (hG : G.Connected) (T : Finset V) (hT : T.Nonempty) (w : V → ℝ)
    (κ : ℝ) (hharm : ∀ x, x ∉ T → lap G w x = 0) (hflux : ∑ t ∈ T, lap G w t = 0)
    (hzero : ∀ t ∈ T, w t = 0)
    (hdecay : ∀ ε > 0, ∀ S : Finset V, ∃ B : Finset V, S ⊆ B ∧
      ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B),
        |(w y - κ) ^ 2 - (w x - κ) ^ 2| ≤ ε) :
    w = 0 := by
  set w' : V → ℝ := fun z => w z - κ with hw'
  have hedge : ∀ x0 y0, G.Adj x0 y0 → w x0 = w y0 := by
    intro x0 y0 hadj
    by_contra hne
    have hpos : 0 < (w y0 - w x0) ^ 2 := by
      have : w y0 - w x0 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      positivity
    obtain ⟨B, hSB, hB⟩ := hdecay ((w y0 - w x0) ^ 2 / 2) (by positivity) (insert x0 T)
    have hTB : T ⊆ B := (Finset.subset_insert _ _).trans hSB
    have hx0B : x0 ∈ B := hSB (Finset.mem_insert_self _ _)
    have hid := sum_mul_lap_eq G B w'
    have hlhs : ∑ x ∈ B, w' x * lap G w' x = 0 := by
      have hs : ∀ x, w' x * lap G w' x = (w x - κ) * lap G w x := fun x => by
        rw [hw', lap_sub_const]
      simp_rw [hs]
      rw [← Finset.sum_subset hTB (fun x _ hx => by rw [hharm x hx, mul_zero])]
      have : ∀ t ∈ T, (w t - κ) * lap G w t = -κ * lap G w t := fun t ht => by
        rw [hzero t ht]; ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hflux, mul_zero]
    have hE : (w y0 - w x0) ^ 2 ≤ ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, (w' y - w' x) ^ 2 := by
      have h1 : (w' y0 - w' x0) ^ 2 ≤ ∑ y ∈ G.neighborFinset x0, (w' y - w' x0) ^ 2 :=
        Finset.single_le_sum (f := fun y => (w' y - w' x0) ^ 2) (fun _ _ => sq_nonneg _)
          ((SimpleGraph.mem_neighborFinset _ _ _).2 hadj)
      have h2 : ∑ y ∈ G.neighborFinset x0, (w' y - w' x0) ^ 2 ≤
          ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, (w' y - w' x) ^ 2 :=
        Finset.single_le_sum (f := fun x => ∑ y ∈ G.neighborFinset x, (w' y - w' x) ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hx0B
      have h3 : w' y0 - w' x0 = w y0 - w x0 := by rw [hw']; ring
      rw [h3] at h1
      exact h1.trans h2
    have hbd : ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (w' y ^ 2 - w' x ^ 2) ≤
        (w y0 - w x0) ^ 2 / 2 :=
      le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => le_abs_self _) hB
    linarith
  have hT0 := hT
  obtain ⟨t0, ht0⟩ := hT0
  funext x
  rw [Pi.zero_apply, eq_of_reachable G hedge (hG.preconnected x t0), hzero t0 ht0]

/-- **Reciprocity**: Green's identity on the terminals for two functions harmonic off `T` with
zero total flux whose deviations from constants have vanishing boundary terms. -/
theorem green_symm_of_decay (T : Finset V) (u w : V → ℝ) (κu κw : ℝ)
    (hu : ∀ x, x ∉ T → lap G u x = 0) (hw : ∀ x, x ∉ T → lap G w x = 0)
    (hfu : ∑ t ∈ T, lap G u t = 0) (hfw : ∑ t ∈ T, lap G w t = 0)
    (hdecay : ∀ ε > 0, ∃ B : Finset V, T ⊆ B ∧
      ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B),
        |(u x - κu) * (w y - κw) - (w x - κw) * (u y - κu)| ≤ ε) :
    ∑ t ∈ T, (u t * lap G w t - w t * lap G u t) = 0 := by
  have hle : ∀ ε > 0, |∑ t ∈ T, (u t * lap G w t - w t * lap G u t)| ≤ ε := by
    intro ε hε
    obtain ⟨B, hTB, hB⟩ := hdecay ε hε
    have hid := sum_green_eq_boundary G B (fun z => u z - κu) (fun z => w z - κw)
    simp only [lap_sub_const] at hid
    rw [← Finset.sum_subset hTB (fun x _ hx => by rw [hu x hx, hw x hx]; ring)] at hid
    have hT : ∑ t ∈ T, ((u t - κu) * lap G w t - (w t - κw) * lap G u t) =
        ∑ t ∈ T, (u t * lap G w t - w t * lap G u t) := by
      have : ∀ t ∈ T, (u t - κu) * lap G w t - (w t - κw) * lap G u t =
          (u t * lap G w t - w t * lap G u t) - κu * lap G w t + κw * lap G u t :=
        fun t _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hfu, hfw]
      ring
    rw [hT] at hid
    rw [hid]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _).trans hB)
  by_contra hne
  have hpos : 0 < |∑ t ∈ T, (u t * lap G w t - w t * lap G u t)| := abs_pos.2 hne
  linarith [hle _ (half_pos hpos)]

/-- **The minimum principle**: a function harmonic off `T`, with zero total flux, nonnegative on
`T` and tending to a constant at infinity, is nonnegative. -/
theorem nonneg_of_flux (hG : G.Connected) (T : Finset V) (hT : T.Nonempty) (w : V → ℝ) (κ : ℝ)
    (hharm : ∀ x, x ∉ T → lap G w x = 0) (hflux : ∑ t ∈ T, lap G w t = 0)
    (hnn : ∀ t ∈ T, 0 ≤ w t) (hfin : ∀ ε > 0, {x | ε ≤ |w x - κ|}.Finite) (x0 : V) :
    0 ≤ w x0 := by
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨t0, ht0⟩ := hT
  set m := w x0 with hm
  rcases lt_or_ge m κ with hκ | hκ
  · -- the sublevel set `{w ≤ m}` is finite, avoids `T` and has outward flux
    have hAfin : {x | w x ≤ m}.Finite := (hfin (κ - m) (by linarith)).subset fun x hx => by
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    set A := hAfin.toFinset
    have hmemA : ∀ x, x ∈ A ↔ w x ≤ m := fun x => by simp [A]
    have hlt := sum_lap_neg G hG A ((hmemA x0).2 le_rfl)
      (z := t0) (fun h => by linarith [(hmemA t0).1 h, hnn t0 ht0]) (fun z => -w z)
      (fun x hx y _ hy => by
        rw [hmemA] at hx hy
        push Not at hy
        linarith)
    have h0 : ∑ x ∈ A, lap G (fun z => -w z) x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxT : x ∉ T := fun h => by linarith [(hmemA x).1 hx, hnn x h]
      have : lap G (fun z => -w z) x = -lap G w x := by
        rw [lap, lap, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [this, hharm x hxT, neg_zero]
    linarith
  · -- the superlevel set `{w > m / 2}` is finite, contains `T`, and has inward flux
    have hAfin : {x | m / 2 < w x}.Finite := (hfin (-m / 2) (by linarith)).subset fun x hx => by
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_trans (by linarith) (le_abs_self _)
    set A := hAfin.toFinset
    have hmemA : ∀ x, x ∈ A ↔ m / 2 < w x := fun x => by simp [A]
    have hTA : T ⊆ A := fun t ht => (hmemA t).2 (by linarith [hnn t ht])
    have hlt := sum_lap_neg G hG A (hTA ht0) (z := x0) (fun h => by linarith [(hmemA x0).1 h])
      w (fun x hx y _ hy => by
        rw [hmemA] at hx hy
        push Not at hy
        linarith)
    rw [← Finset.sum_subset hTA (fun x _ hx => hharm x hx), hflux] at hlt
    exact lt_irrefl _ hlt

/-! ### The trace network -/

/-- A network on the terminals `T`: symmetric nonnegative conductances, supported on `T × T`,
whose total at each vertex is at most its degree. -/
def IsTraceNetwork (T : Finset V) (c : V → V → ℝ) : Prop :=
  (∀ t s, c t s = c s t) ∧ (∀ t s, 0 ≤ c t s) ∧ (∀ t, ∑ s ∈ T, c t s ≤ G.degree t) ∧
    (∀ t s, t ∉ T → c t s = 0)

omit [DecidableEq V] in
/-- The zero network. -/
theorem isTraceNetwork_zero (T : Finset V) : IsTraceNetwork G T (fun _ _ => 0) :=
  ⟨fun _ _ => rfl, fun _ _ => le_rfl,
    fun t => by simp only [Finset.sum_const_zero]; exact Nat.cast_nonneg _, fun _ _ _ => rfl⟩

/-- **The trace network of an admissible space**: the response at the terminals of a space of
potentials with uniqueness, reciprocity, existence and the minimum principle is a network. -/
theorem exists_traceNetwork (T : Finset V) (W : Submodule ℝ (V → ℝ))
    (hconst : ∀ κ : ℝ, (fun _ => κ) ∈ W)
    (huniq : ∀ w ∈ W, (∀ t ∈ T, w t = 0) → w = 0)
    (hsymm : ∀ u ∈ W, ∀ w ∈ W, ∑ t ∈ T, (u t * lap G w t - w t * lap G u t) = 0)
    (hsurj : ∀ f : V → ℝ, ∃ w ∈ W, ∀ t ∈ T, w t = f t)
    (hpos : ∀ w ∈ W, (∀ t ∈ T, 0 ≤ w t) → ∀ x, 0 ≤ w x) :
    ∃ c : V → V → ℝ, IsTraceNetwork G T c ∧
      ∀ w ∈ W, ∀ t ∈ T, lap G w t = ∑ s ∈ T, c t s * (w s - w t) := by
  classical
  choose h hW hval using fun s : V => hsurj (fun x => if x = s then 1 else 0)
  have hnn : ∀ s x, 0 ≤ h s x := fun s => hpos _ (hW s) fun t ht => by
    rw [hval s t ht]; split_ifs <;> norm_num
  have hsum : ∀ x, ∑ s ∈ T, h s x = 1 := by
    have hmem : (∑ s ∈ T, h s) - (fun _ => (1 : ℝ)) ∈ W :=
      W.sub_mem (W.sum_mem fun s _ => hW s) (hconst 1)
    have h0 := huniq _ hmem fun t ht => by
      simp only [Pi.sub_apply, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun s _ => hval s t ht, Finset.sum_ite_eq, if_pos ht, sub_self]
    intro x
    have := congrFun h0 x
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at this
    linarith
  -- the response at `t ≠ s` to the unit potential at `s`
  have hlap : ∀ s t, t ∈ T → t ≠ s → lap G (h s) t = ∑ y ∈ G.neighborFinset t, h s y := by
    intro s t ht hts
    rw [lap]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hval s t ht, if_neg hts, sub_zero]
  let c : V → V → ℝ := fun t s =>
    if t ∈ T ∧ s ∈ T ∧ t ≠ s then ∑ y ∈ G.neighborFinset t, h s y else 0
  have hrecip : ∀ s t, s ∈ T → t ∈ T → lap G (h t) s = lap G (h s) t := by
    intro s t hs ht
    have key := hsymm _ (hW s) _ (hW t)
    rw [Finset.sum_sub_distrib] at key
    have e1 : ∑ r ∈ T, h s r * lap G (h t) r = lap G (h t) s := by
      rw [Finset.sum_congr rfl fun r hr => by rw [hval s r hr]]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos hs]
    have e2 : ∑ r ∈ T, h t r * lap G (h s) r = lap G (h s) t := by
      rw [Finset.sum_congr rfl fun r hr => by rw [hval t r hr]]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos ht]
    linarith
  refine ⟨c, ⟨fun t s => ?_, fun t s => ?_, fun t => ?_, fun t s ht => ?_⟩, ?_⟩
  · simp only [c]
    by_cases hc : t ∈ T ∧ s ∈ T ∧ t ≠ s
    · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2.symm⟩, ← hlap s t hc.1 hc.2.2,
        ← hlap t s hc.2.1 hc.2.2.symm, hrecip s t hc.2.1 hc.1]
    · rw [if_neg hc, if_neg fun h' => hc ⟨h'.2.1, h'.1, h'.2.2.symm⟩]
  · simp only [c]
    split_ifs
    · exact Finset.sum_nonneg fun y _ => hnn s y
    · exact le_rfl
  · by_cases ht : t ∈ T
    · have e1 : ∑ s ∈ T, c t s = ∑ s ∈ T.erase t, ∑ y ∈ G.neighborFinset t, h s y := by
        rw [← Finset.sum_erase_add T _ ht]
        simp only [c, ne_eq, not_true_eq_false, and_false, if_false, add_zero]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [if_pos ⟨ht, Finset.mem_of_mem_erase hs, Ne.symm (Finset.ne_of_mem_erase hs)⟩]
      rw [e1, Finset.sum_comm, ← SimpleGraph.card_neighborFinset_eq_degree]
      calc ∑ y ∈ G.neighborFinset t, ∑ s ∈ T.erase t, h s y
          ≤ ∑ y ∈ G.neighborFinset t, (1 : ℝ) := Finset.sum_le_sum fun y _ => by
            rw [Finset.sum_erase_eq_sub ht, hsum y]
            linarith [hnn t y]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · simp only [c, ht, false_and, if_false, Finset.sum_const_zero]
      exact Nat.cast_nonneg _
  · simp only [c, ht, false_and, if_false]
  · intro w hw t ht
    have hrep : w = ∑ s ∈ T, w s • h s := by
      have hmem : w - ∑ s ∈ T, w s • h s ∈ W :=
        W.sub_mem hw (W.sum_mem fun s _ => W.smul_mem _ (hW s))
      have := huniq _ hmem fun r hr => by
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl fun s _ => by rw [hval s r hr]]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hr, sub_self]
      exact sub_eq_zero.1 this
    have hone : ∑ s ∈ T, lap G (h s) t = 0 := by
      have h1 := lap_sum_smul G T (fun _ => (1 : ℝ)) h t
      have h2 : (∑ s ∈ T, (fun _ => (1 : ℝ)) s • h s) = fun _ => (1 : ℝ) := by
        funext x
        simp only [one_smul, Finset.sum_apply, hsum x]
      rw [h2, lap_const] at h1
      simpa only [one_mul] using h1.symm
    have hw' : lap G w t = ∑ s ∈ T, w s * lap G (h s) t := by
      conv_lhs => rw [hrep]
      exact lap_sum_smul G T w h t
    have hw'' : lap G w t = ∑ s ∈ T, (w s - w t) * lap G (h s) t := by
      rw [hw', ← sub_zero (∑ s ∈ T, w s * lap G (h s) t), ← mul_zero (w t), ← hone,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hw'']
    refine Finset.sum_congr rfl fun s hs => ?_
    by_cases hts : t = s
    · rw [hts, sub_self, zero_mul, mul_zero]
    · simp only [c]
      rw [if_pos ⟨ht, hs, hts⟩, ← hlap s t ht hts, mul_comm]

/-! ### The finite instance -/

/-- The total Laplacian of a finite graph vanishes. -/
theorem sum_univ_lap [Fintype V] (f : V → ℝ) : ∑ x, lap G f x = 0 := by
  rw [sum_lap_eq_boundary]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.filter_false_of_mem fun y _ h => h (Finset.mem_univ y), Finset.sum_empty]

/-- The functions harmonic off `T`. -/
def harmonicOff (T : Finset V) : Submodule ℝ (V → ℝ) where
  carrier := {w | ∀ x, x ∉ T → lap G w x = 0}
  add_mem' {f g} hf hg x hx := by rw [lap_add, hf x hx, hg x hx, add_zero]
  zero_mem' x _ := by
    simpa only [Pi.zero_def] using lap_const G (0 : ℝ) x
  smul_mem' a f hf x hx := by rw [lap_smul, hf x hx, mul_zero]

/-- **The trace network of a finite connected graph** on any set of terminals. -/
theorem exists_traceNetwork_of_finite [Fintype V] (hG : G.Connected) (T : Finset V) :
    ∃ c : V → V → ℝ, IsTraceNetwork G T c ∧ ∀ w : V → ℝ, (∀ x, x ∉ T → lap G w x = 0) →
      ∀ t ∈ T, lap G w t = ∑ s ∈ T, c t s * (w s - w t) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨fun _ _ => 0, isTraceNetwork_zero G T, fun _ _ t ht => by simp [hT] at ht⟩
  have hflux : ∀ w ∈ harmonicOff G T, ∑ t ∈ T, lap G w t = 0 := fun w hw => by
    rw [Finset.sum_subset (Finset.subset_univ T) (fun x _ hx => hw x hx)]
    exact sum_univ_lap G w
  have hnob : ∀ (P : V → V → ℝ) (ε : ℝ), 0 < ε →
      ∑ x ∈ Finset.univ, ∑ y ∈ (G.neighborFinset x).filter (· ∉ Finset.univ), |P x y| ≤ ε :=
    fun P ε hε => by
      rw [Finset.sum_eq_zero fun x _ => by
        rw [Finset.filter_false_of_mem fun y _ h => h (Finset.mem_univ y), Finset.sum_empty]]
      exact hε.le
  obtain ⟨c, hc, hK⟩ := exists_traceNetwork G T (harmonicOff G T)
    (fun κ x _ => lap_const G κ x)
    (fun w hw hz => eq_zero_of_energy G hG T hT w 0 hw (hflux w hw) hz
      fun ε hε _ => ⟨Finset.univ, Finset.subset_univ _, hnob _ ε hε⟩)
    (fun u hu w hw => green_symm_of_decay G T u w 0 0 hu hw (hflux u hu) (hflux w hw)
      fun ε hε => ⟨Finset.univ, Finset.subset_univ _, hnob _ ε hε⟩)
    (fun f => by
      obtain ⟨t0, ht0⟩ := hT
      have hacc : LatticeProb.Network.BoundaryAccessible G (Finset.univ.filter (· ∉ T)) :=
        LatticeProb.Network.boundaryAccessible_of_connected hG _
          ⟨t0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, ht0]⟩
      obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := LatticeProb.Network.existsUnique_dirichlet
        LatticeProb.Network.isCond_unitCond _ hacc f
      refine ⟨w, fun x hx => ?_, fun t ht => hw2 t (by simp [ht])⟩
      have := hw1 x (by simp [hx])
      rwa [LatticeProb.Network.netLaplacian_unitCond] at this)
    (fun w hw hT' x => nonneg_of_flux G hG T hT w 0 hw (hflux w hw) hT'
      (fun _ _ => Set.toFinite _) x)
  exact ⟨c, hc, fun w hw => hK w hw⟩

/-! ### The instance with Green columns -/

theorem abs_sq_sub_sq_le {a b C p q : ℝ} (_hC : 0 ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : |a| ≤ C * p) (hb : |b| ≤ C * q) : |a ^ 2 - b ^ 2| ≤ C ^ 2 * (q + p) ^ 2 := by
  have ha2 : a ^ 2 ≤ (C * p) ^ 2 := sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
  have hb2 : b ^ 2 ≤ (C * q) ^ 2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have hcross : 0 ≤ C ^ 2 * (p * q) := mul_nonneg (sq_nonneg C) (mul_nonneg hp hq)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem abs_cross_le {a b c d Cu Cw p q : ℝ} (hCu : 0 ≤ Cu) (hCw : 0 ≤ Cw) (hp : 0 ≤ p)
    (_hq : 0 ≤ q) (ha : |a| ≤ Cu * p) (hb : |b| ≤ Cw * q) (hc : |c| ≤ Cw * p)
    (hd : |d| ≤ Cu * q) : |a * b - c * d| ≤ Cu * Cw * (p + q) ^ 2 := by
  have h1 : |a * b| ≤ Cu * p * (Cw * q) := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
  have h2 : |c * d| ≤ Cw * p * (Cu * q) := by
    rw [abs_mul]; exact mul_le_mul hc hd (abs_nonneg _) (by positivity)
  have h3 : 0 ≤ Cu * Cw * (p ^ 2 + q ^ 2) :=
    mul_nonneg (mul_nonneg hCu hCw) (add_nonneg (sq_nonneg p) (sq_nonneg q))
  calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
    _ ≤ Cu * p * (Cw * q) + Cw * p * (Cu * q) := add_le_add h1 h2
    _ ≤ Cu * Cw * (p + q) ^ 2 := by nlinarith

section Green

variable (T : Finset V) (g : V → V → ℝ)

omit [DecidableEq V] in
/-- The span of the constants and of the zero-sum combinations of the Green columns `g r` at the
terminals `r ∈ T`. -/
def greenSpan : Submodule ℝ (V → ℝ) where
  carrier := {w | ∃ (κ : ℝ) (b : T → ℝ), ∑ r, b r = 0 ∧ ∀ x, w x = κ + ∑ r, b r * g r x}
  add_mem' := by
    rintro f f' ⟨κ, b, hb, hf⟩ ⟨κ', b', hb', hf'⟩
    refine ⟨κ + κ', b + b', ?_, fun x => ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hb, hb', add_zero]
    · simp only [Pi.add_apply, hf, hf', add_mul, Finset.sum_add_distrib]
      ring
  zero_mem' := ⟨0, 0, by simp, fun x => by simp⟩
  smul_mem' := by
    rintro a f ⟨κ, b, hb, hf⟩
    refine ⟨a * κ, a • b, ?_, fun x => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hb, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, hf, mul_add, Finset.mul_sum, mul_assoc]

variable {T g}

theorem sum_coe_mul_ite (b : T → ℝ) {t : V} (ht : t ∈ T) :
    ∑ r : T, b r * (if t = r then 1 else 0) = b ⟨t, ht⟩ := by
  classical
  rw [Fintype.sum_eq_single ⟨t, ht⟩ fun r hr => by
    rw [if_neg (fun h => hr (Subtype.ext h.symm)), mul_zero]]
  simp

theorem sum_coe_mul_ite_of_not_mem (b : T → ℝ) {x : V} (hx : x ∉ T) :
    ∑ r : T, b r * (if x = r then 1 else 0) = 0 :=
  Finset.sum_eq_zero fun r _ => by rw [if_neg (fun h => hx (by rw [h]; exact r.2)), mul_zero]

theorem lap_of_greenSpan (hg : ∀ r ∈ T, ∀ x, lap G (g r) x = -(if x = r then 1 else 0))
    {w : V → ℝ} {κ : ℝ} {b : T → ℝ} (hw : ∀ x, w x = κ + ∑ r, b r * g r x) (x : V) :
    lap G w x = -∑ r : T, b r * (if x = r then 1 else 0) := by
  have e : w = (fun _ => κ) + ∑ r : T, b r • g r := by
    funext z
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw z]
  rw [e, lap_add, lap_const, zero_add, lap_sum_smul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hg r r.2 x]
  ring

omit [DecidableEq V] [G.LocallyFinite] in
theorem greenSpan_decay (Kc φ : V → ℝ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hdecay : ∀ b : T → ℝ, ∑ r, b r = 0 →
      ∃ C, ∀ x, |∑ r, b r * (g r x - Kc r)| ≤ C * φ x)
    {w : V → ℝ} (hw : w ∈ greenSpan T g) :
    ∃ κ C : ℝ, 0 ≤ C ∧ ∀ x, |w x - κ| ≤ C * φ x := by
  obtain ⟨κ, b, hb, hw⟩ := hw
  obtain ⟨C, hC⟩ := hdecay b hb
  refine ⟨κ + ∑ r, b r * Kc r, max C 0, le_max_right _ _, fun x => ?_⟩
  have e : w x - (κ + ∑ r, b r * Kc r) = ∑ r, b r * (g r x - Kc r) := by
    rw [hw x]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e]
  exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ0 x))

/-- **The trace network of an infinite graph with Green columns**: Green columns `g r` at the
terminals whose zero-sum combinations decay along a profile `φ` (finite superlevel sets, vanishing
boundary sums on an exhaustion), and the Liouville property for a class `Sub` containing them.
Every function of `Sub` harmonic off `T` with zero total flux satisfies Kirchhoff's law at the
terminals for a network on `T`. -/
theorem exists_traceNetwork_of_green (hG : G.Connected)
    (hg : ∀ r ∈ T, ∀ x, lap G (g r) x = -(if x = r then 1 else 0))
    (Kc φ : V → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφfin : ∀ ε > 0, {x | ε ≤ φ x}.Finite)
    (hφbd : ∀ ε > 0, ∀ S : Finset V, ∃ B : Finset V, S ⊆ B ∧
      ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (φ x + φ y) ^ 2 ≤ ε)
    (hdecay : ∀ b : T → ℝ, ∑ r, b r = 0 →
      ∃ C, ∀ x, |∑ r, b r * (g r x - Kc r)| ≤ C * φ x)
    (Sub : Submodule ℝ (V → ℝ)) (hgS : ∀ r ∈ T, g r ∈ Sub)
    (hLiou : ∀ v ∈ Sub, (∀ x, lap G v x = 0) → ∃ κ, ∀ x, v x = κ) :
    ∃ c : V → V → ℝ, IsTraceNetwork G T c ∧ ∀ v ∈ Sub, (∀ x, x ∉ T → lap G v x = 0) →
      ∑ t ∈ T, lap G v t = 0 → ∀ t ∈ T, lap G v t = ∑ s ∈ T, c t s * (v s - v t) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨fun _ _ => 0, isTraceNetwork_zero G T, fun _ _ _ _ t ht => by simp [hT] at ht⟩
  have hoff : ∀ w ∈ greenSpan T g, ∀ x, x ∉ T → lap G w x = 0 := by
    rintro w ⟨κ, b, -, hw⟩ x hx
    rw [lap_of_greenSpan G hg hw, sum_coe_mul_ite_of_not_mem b hx, neg_zero]
  have hflux : ∀ w ∈ greenSpan T g, ∑ t ∈ T, lap G w t = 0 := by
    rintro w ⟨κ, b, hb, hw⟩
    rw [← Finset.sum_coe_sort T]
    have e : ∀ t : T, lap G w t = -b t := fun t => by
      rw [lap_of_greenSpan G hg hw, sum_coe_mul_ite b t.2]
    simp only [e, Finset.sum_neg_distrib, hb, neg_zero]
  have hdec := fun w (hw : w ∈ greenSpan T g) => greenSpan_decay Kc φ hφ0 hdecay hw
  have huniq : ∀ w ∈ greenSpan T g, (∀ t ∈ T, w t = 0) → w = 0 := by
    intro w hw hz
    obtain ⟨κ, C, hC, hwC⟩ := hdec w hw
    refine eq_zero_of_energy G hG T hT w κ (hoff w hw) (hflux w hw) hz fun ε hε S => ?_
    obtain ⟨B, hSB, hB⟩ := hφbd (ε / (C ^ 2 + 1)) (by positivity) S
    refine ⟨B, hSB, ?_⟩
    calc _ ≤ ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), C ^ 2 * (φ x + φ y) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            abs_sq_sub_sq_le hC (hφ0 y) (hφ0 x) (hwC y) (hwC x)
      _ = C ^ 2 * ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (φ x + φ y) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
      _ ≤ C ^ 2 * (ε / (C ^ 2 + 1)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg C]
  have hsymm : ∀ u ∈ greenSpan T g, ∀ w ∈ greenSpan T g,
      ∑ t ∈ T, (u t * lap G w t - w t * lap G u t) = 0 := by
    intro u hu w hw
    obtain ⟨κu, Cu, hCu, huC⟩ := hdec u hu
    obtain ⟨κw, Cw, hCw, hwC⟩ := hdec w hw
    refine green_symm_of_decay G T u w κu κw (hoff u hu) (hoff w hw) (hflux u hu) (hflux w hw)
      fun ε hε => ?_
    obtain ⟨B, hSB, hB⟩ := hφbd (ε / (Cu * Cw + 1)) (by positivity) T
    refine ⟨B, hSB, ?_⟩
    calc _ ≤ ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), Cu * Cw * (φ x + φ y) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            abs_cross_le hCu hCw (hφ0 x) (hφ0 y) (huC x) (hwC y) (hwC x) (huC y)
      _ = Cu * Cw * ∑ x ∈ B, ∑ y ∈ (G.neighborFinset x).filter (· ∉ B), (φ x + φ y) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
      _ ≤ Cu * Cw * (ε / (Cu * Cw + 1)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hCu hCw]
  have hpos : ∀ w ∈ greenSpan T g, (∀ t ∈ T, 0 ≤ w t) → ∀ x, 0 ≤ w x := by
    intro w hw hnn x
    obtain ⟨κ, C, hC, hwC⟩ := hdec w hw
    refine nonneg_of_flux G hG T hT w κ (hoff w hw) (hflux w hw) hnn (fun ε hε => ?_) x
    refine (hφfin (ε / (C + 1)) (by positivity)).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hwC z, hφ0 z]
  have hsurj : ∀ f : V → ℝ, ∃ w ∈ greenSpan T g, ∀ t ∈ T, w t = f t := by
    let Q : ((T → ℝ) × ℝ) →ₗ[ℝ] ((T → ℝ) × ℝ) :=
      { toFun := fun p => (fun t => p.2 + ∑ r, p.1 r * g r t, ∑ r, p.1 r)
        map_add' := fun p q => Prod.ext (funext fun t => by
            simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
              Finset.sum_add_distrib]
            ring)
          (by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib])
        map_smul' := fun a p => Prod.ext (funext fun t => by
            simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
              RingHom.id_apply, Finset.mul_sum, mul_add, mul_assoc])
          (by simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply, Finset.mul_sum]) }
    have hinj : Function.Injective Q := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨b, κ⟩ hQ
      have h1 : ∀ t : T, κ + ∑ r, b r * g r t = 0 := fun t =>
        congrFun (congrArg Prod.fst hQ) t
      have h2 : ∑ r, b r = 0 := congrArg Prod.snd hQ
      have hw : (fun x => κ + ∑ r, b r * g r x) ∈ greenSpan T g := ⟨κ, b, h2, fun _ => rfl⟩
      have h0 := huniq _ hw fun t ht => h1 ⟨t, ht⟩
      have hb : b = 0 := by
        funext r
        have := lap_of_greenSpan G hg (w := fun x => κ + ∑ r, b r * g r x) (fun _ => rfl) r
        rw [h0, sum_coe_mul_ite b r.2] at this
        have hl : lap G (0 : V → ℝ) r = 0 := by
          simpa only [Pi.zero_def] using lap_const G (0 : ℝ) (r : V)
        rw [hl] at this
        simp only [Pi.zero_apply]
        linarith
      obtain ⟨t0, ht0⟩ := hT
      have hκ : κ = 0 := by
        have := h1 ⟨t0, ht0⟩
        simpa only [hb, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using this
      rw [hb, hκ]
      rfl
    have hsQ := LinearMap.injective_iff_surjective.mp hinj
    intro f
    obtain ⟨⟨b, κ⟩, hQ⟩ := hsQ (fun t => f t, 0)
    refine ⟨fun x => κ + ∑ r, b r * g r x, ⟨κ, b, congrArg Prod.snd hQ, fun _ => rfl⟩,
      fun t ht => congrFun (congrArg Prod.fst hQ) ⟨t, ht⟩⟩
  have hmem : ∀ v ∈ Sub, (∀ x, x ∉ T → lap G v x = 0) → ∑ t ∈ T, lap G v t = 0 →
      v ∈ greenSpan T g := by
    intro v hv hoffv hfv
    obtain ⟨b, hbv⟩ : ∃ b : T → ℝ, ∀ r, b r = lap G v r := ⟨_, fun _ => rfl⟩
    have hu : v + ∑ r : T, b r • g r ∈ Sub :=
      Sub.add_mem hv (Sub.sum_mem fun r _ => Sub.smul_mem _ (hgS r r.2))
    obtain ⟨κ, hκ⟩ := hLiou _ hu fun x => by
      have e : ∑ r : T, b r * lap G (g r) x = -∑ r : T, b r * (if x = r then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun r _ => by rw [hg r r.2 x]; ring
      rw [lap_add, lap_sum_smul, e]
      by_cases hx : x ∈ T
      · rw [sum_coe_mul_ite b hx, hbv, Subtype.coe_mk]; ring
      · rw [sum_coe_mul_ite_of_not_mem b hx, hoffv x hx]; ring
    refine ⟨κ, fun r => -b r, ?_, fun x => ?_⟩
    · have e : ∑ r : T, b r = ∑ t ∈ T, lap G v t := by
        rw [← Finset.sum_coe_sort T]; exact Finset.sum_congr rfl fun r _ => hbv r
      simp only [Finset.sum_neg_distrib, e, hfv, neg_zero]
    · have := hκ x
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
  obtain ⟨c, hc, hK⟩ := exists_traceNetwork G T (greenSpan T g)
    (fun κ => ⟨κ, 0, by simp, fun _ => by simp⟩) huniq hsymm hsurj hpos
  exact ⟨c, hc, fun v hv hoffv hfv => hK v (hmem v hv hoffv hfv)⟩

end Green

end Rigidity.Proofs.S3.NetworkTrace
