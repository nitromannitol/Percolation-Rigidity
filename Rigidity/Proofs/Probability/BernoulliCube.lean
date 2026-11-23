import Rigidity.Proofs.Probability.BregmanConvex
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Function.DependsOn

/-!
# The product Bernoulli law on a finite cube and the tensorization of `φ`-entropies

For a finite index type `ι` and `p ∈ [0, 1]`, the product of Bernoulli laws of parameter `p` on
`ι → Bool` gives the configuration `x` the weight `∏ i, w(x i)` with `w(true) = p`,
`w(false) = 1 - p`. Expectations are finite sums, so no integrability question arises.

* `cubeExp p F`: the expectation of `F`; `coordAvg p i F`: the average of `F` over the
  coordinate `i`, `p F(x^{i,1}) + (1 - p) F(x^{i,0})`, with `cubeExp_coordAvg`:
  `E[coordAvg p i F] = E[F]`;
* `rpowEntropy r p W = E[W^r] - E[W]^r` and `coordEntropy r p i W`, its analogue in the
  coordinate `i` (the two-point Jensen gap of `W(x^{i,1})`, `W(x^{i,0})`);
* `rpowEntropy_le_sum_coordEntropy`: **the tensorization inequality**
  `E[W^r] - E[W]^r ≤ Σ_i E[coordEntropy r p i W]` for `W ≥ 0` and `1 ≤ r ≤ 2` (Boucheron,
  Bousquet, Lugosi and Massart, Ann. Probab. 33 (2005), §3.1, after Latała and Oleszkiewicz),
  by induction on the coordinates read by `W`: averaging out one coordinate splits off its
  entropy, and the entropy in another coordinate of the average is at most the average of the
  entropies by the convexity of the two-point Jensen gap (`jensenGap_convex`).
-/

namespace Rigidity.Probability

open Finset

variable {ι : Type*}

section Weights

variable [Fintype ι]


/-- The weight of a state of one coordinate under the Bernoulli law of parameter `p`. -/
def bernWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem bernWeight_true (p : ℝ) : bernWeight p true = p := rfl

@[simp] theorem bernWeight_false (p : ℝ) : bernWeight p false = 1 - p := rfl

theorem bernWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bernWeight p b := by
  cases b
  · simp only [bernWeight_false]; linarith
  · simpa using hp0

/-- The weight `∏ i, w(x i)` of a configuration under the product Bernoulli law. -/
def cubeWeight (p : ℝ) (x : ι → Bool) : ℝ := ∏ i, bernWeight p (x i)

theorem cubeWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ cubeWeight p x :=
  prod_nonneg fun _ _ => bernWeight_nonneg hp0 hp1 _

variable [DecidableEq ι]

theorem sum_cubeWeight (p : ℝ) : ∑ x : ι → Bool, cubeWeight p x = 1 := by
  have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool)) (fun _ b => bernWeight p b)
  simp only [Fintype.piFinset_univ] at h
  unfold cubeWeight
  rw [← h]
  simp

/-- The expectation of `F` under the product Bernoulli law. -/
def cubeExp (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ := ∑ x, cubeWeight p x * F x

theorem cubeExp_const (p c : ℝ) : cubeExp p (fun _ : ι → Bool => c) = c := by
  simp only [cubeExp, ← Finset.sum_mul, sum_cubeWeight, one_mul]

theorem cubeExp_add (p : ℝ) (F G : (ι → Bool) → ℝ) :
    cubeExp p (fun x => F x + G x) = cubeExp p F + cubeExp p G := by
  simp only [cubeExp, mul_add, Finset.sum_add_distrib]

theorem cubeExp_sub (p : ℝ) (F G : (ι → Bool) → ℝ) :
    cubeExp p (fun x => F x - G x) = cubeExp p F - cubeExp p G := by
  simp only [cubeExp, mul_sub, Finset.sum_sub_distrib]

theorem cubeExp_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    cubeExp p (fun x => c * F x) = c * cubeExp p F := by
  simp only [cubeExp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem cubeExp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {F G : (ι → Bool) → ℝ}
    (h : ∀ x, F x ≤ G x) : cubeExp p F ≤ cubeExp p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (cubeWeight_nonneg hp0 hp1 x)

theorem cubeExp_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {F : (ι → Bool) → ℝ}
    (h : ∀ x, 0 ≤ F x) : 0 ≤ cubeExp p F := by
  simpa [cubeExp_const] using cubeExp_mono hp0 hp1 (F := fun _ => (0 : ℝ)) h

end Weights

section Coordinate

variable [DecidableEq ι]

/-- The average of `F` over the coordinate `i`: `p F(x^{i,1}) + (1 - p) F(x^{i,0})`. -/
def coordAvg (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  p * F (Function.update x i true) + (1 - p) * F (Function.update x i false)

theorem coordAvg_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) {F : (ι → Bool) → ℝ}
    (h : ∀ x, 0 ≤ F x) (x : ι → Bool) : 0 ≤ coordAvg p i F x := by
  unfold coordAvg
  have : 0 ≤ 1 - p := by linarith
  have := h (Function.update x i true)
  have := h (Function.update x i false)
  positivity

theorem coordAvg_update (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) (b : Bool) :
    coordAvg p i F (Function.update x i b) = coordAvg p i F x := by
  simp only [coordAvg, Function.update_idem]



/-- The configuration equal to `b` at `i` and to `y` elsewhere. -/
def joinAt (i : ι) (b : Bool) (y : {j // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, y)

theorem joinAt_self (i : ι) (b : Bool) (y : {j // j ≠ i} → Bool) : joinAt i b y i = b := by
  simp [joinAt, Equiv.funSplitAt_symm_apply]

theorem joinAt_of_ne {i j : ι} (h : j ≠ i) (b : Bool) (y : {j // j ≠ i} → Bool) :
    joinAt i b y j = y ⟨j, h⟩ := by
  simp [joinAt, Equiv.funSplitAt_symm_apply, h]

theorem update_joinAt (i : ι) (b c : Bool) (y : {j // j ≠ i} → Bool) :
    Function.update (joinAt i b y) i c = joinAt i c y := by
  funext j
  by_cases h : j = i
  · subst h
    rw [Function.update_self, joinAt_self]
  · rw [Function.update_of_ne h, joinAt_of_ne h, joinAt_of_ne h]

/-- The `φ`-entropy of `W` in the coordinate `i` at `x`: the two-point Jensen gap of
`W(x^{i,1})` and `W(x^{i,0})`. -/
noncomputable def coordEntropy (r p : ℝ) (i : ι) (W : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  jensenGap r p (W (Function.update x i true)) (W (Function.update x i false))

theorem coordEntropy_eq (r p : ℝ) (i : ι) (W : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordEntropy r p i W x = coordAvg p i (fun y => W y ^ r) x - coordAvg p i W x ^ r := rfl

/-- **The Jensen property**: for `i ≠ e`, the entropy in `i` of the average over `e` is at most
the average over `e` of the entropy in `i`. -/
theorem coordEntropy_coordAvg_le {r p : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) {i e : ι} (hie : i ≠ e) {W : (ι → Bool) → ℝ} (hW : ∀ x, 0 ≤ W x)
    (x : ι → Bool) :
    coordEntropy r p i (coordAvg p e W) x ≤ coordAvg p e (coordEntropy r p i W) x := by
  simp only [coordEntropy, coordAvg, Function.update_comm hie]
  exact jensenGap_convex hr1 hr2 hp0 hp1 (hW _) (hW _) (hW _) (hW _) hp0 hp1

end Coordinate

section Tensorization

variable [Fintype ι] [DecidableEq ι]

theorem sum_eq_sum_joinAt (i : ι) (H : (ι → Bool) → ℝ) :
    ∑ x, H x = ∑ b, ∑ y : {j // j ≠ i} → Bool, H (joinAt i b y) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem cubeWeight_joinAt (p : ℝ) (i : ι) (b : Bool) (y : {j // j ≠ i} → Bool) :
    cubeWeight p (joinAt i b y) = bernWeight p b * ∏ j, bernWeight p (y j) := by
  unfold cubeWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, joinAt_self]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [joinAt_of_ne j.2]

/-- The expectation as a sum over the coordinates other than `i` of the average over `i`. -/
theorem cubeExp_eq_sum_joinAt (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    cubeExp p F = ∑ y : {j // j ≠ i} → Bool, (∏ j, bernWeight p (y j)) *
      (p * F (joinAt i true y) + (1 - p) * F (joinAt i false y)) := by
  unfold cubeExp
  rw [sum_eq_sum_joinAt i, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cubeWeight_joinAt, cubeWeight_joinAt, bernWeight_true, bernWeight_false]
  ring

/-- **Averaging out a coordinate does not change the expectation.** -/
theorem cubeExp_coordAvg (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    cubeExp p (coordAvg p i F) = cubeExp p F := by
  rw [cubeExp_eq_sum_joinAt p i, cubeExp_eq_sum_joinAt p i]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [coordAvg, update_joinAt]
  ring


/-- The `φ`-entropy `E[W^r] - E[W]^r` of `W` for `φ(x) = x^r`. -/
noncomputable def rpowEntropy (r p : ℝ) (W : (ι → Bool) → ℝ) : ℝ :=
  cubeExp p (fun x => W x ^ r) - cubeExp p W ^ r

/-- Averaging out the coordinate `e` splits off the entropy in `e`. -/
theorem rpowEntropy_eq_add_coordAvg (r p : ℝ) (e : ι) (W : (ι → Bool) → ℝ) :
    rpowEntropy r p W = cubeExp p (coordEntropy r p e W) + rpowEntropy r p (coordAvg p e W) := by
  have h1 : cubeExp p (coordEntropy r p e W) =
      cubeExp p (fun x => W x ^ r) - cubeExp p (fun x => coordAvg p e W x ^ r) := by
    rw [← cubeExp_coordAvg p e (fun x => W x ^ r), ← cubeExp_sub]
    rfl
  rw [h1]
  unfold rpowEntropy
  rw [cubeExp_coordAvg]
  ring

/-- The tensorization inequality for a function reading only the coordinates in `T`. -/
theorem rpowEntropy_le_of_dependsOn {r p : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (T : Finset ι) :
    ∀ W : (ι → Bool) → ℝ, (∀ x, 0 ≤ W x) → DependsOn W (T : Set ι) →
      rpowEntropy r p W ≤ ∑ i ∈ T, cubeExp p (coordEntropy r p i W) := by
  induction T using Finset.induction_on with
  | empty =>
    intro W hW hdep
    have hc : W = fun _ => W (fun _ => false) := by
      funext x
      exact hdep (by simp)
    rw [hc]
    simp [rpowEntropy, cubeExp_const]
  | insert e T he ih =>
    intro W hW hdep
    rw [rpowEntropy_eq_add_coordAvg r p e W, Finset.sum_insert he]
    have hupd : ∀ (x y : ι → Bool), (∀ j ∈ (T : Set ι), x j = y j) → ∀ b : Bool,
        W (Function.update x e b) = W (Function.update y e b) := by
      intro x y hxy b
      apply hdep
      intro j hj
      by_cases hje : j = e
      · subst hje
        simp
      · rw [Function.update_of_ne hje, Function.update_of_ne hje]
        have : j ∈ (T : Set ι) := by
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hj
          tauto
        exact hxy j this
    have hdep' : DependsOn (coordAvg p e W) (T : Set ι) := by
      intro x y hxy
      simp only [coordAvg]
      rw [hupd x y hxy true, hupd x y hxy false]
    have hrec := ih (coordAvg p e W) (coordAvg_nonneg hp0 hp1 e hW) hdep'
    have hsum : ∑ i ∈ T, cubeExp p (coordEntropy r p i (coordAvg p e W)) ≤
        ∑ i ∈ T, cubeExp p (coordEntropy r p i W) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hie : i ≠ e := fun h => he (h ▸ hi)
      calc cubeExp p (coordEntropy r p i (coordAvg p e W))
          ≤ cubeExp p (coordAvg p e (coordEntropy r p i W)) :=
            cubeExp_mono hp0 hp1 fun x => coordEntropy_coordAvg_le hr1 hr2 hp0 hp1 hie hW x
        _ = cubeExp p (coordEntropy r p i W) := cubeExp_coordAvg p e _
    linarith

/-- **Tensorization of the `φ`-entropy for `φ(x) = x^r`, `1 ≤ r ≤ 2`**, under the product
Bernoulli law: `E[W^r] - E[W]^r ≤ Σ_i E[coordEntropy r p i W]` for `W ≥ 0`. -/
theorem rpowEntropy_le_sum_coordEntropy {r p : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) {W : (ι → Bool) → ℝ} (hW : ∀ x, 0 ≤ W x) :
    rpowEntropy r p W ≤ ∑ i, cubeExp p (coordEntropy r p i W) := by
  refine rpowEntropy_le_of_dependsOn hr1 hr2 hp0 hp1 univ W hW ?_
  intro x y hxy
  exact congrArg W (funext fun i => hxy i (by simp))

end Tensorization

end Rigidity.Probability
