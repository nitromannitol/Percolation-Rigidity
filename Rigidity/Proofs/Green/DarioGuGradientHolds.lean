import Rigidity.Proofs.Green.DarioGuGradientDirect
import Rigidity.Proofs.Barlow.UpperBoundHolds

/-!
# Theorem 3 of Dario and Gu in dimension two with no hypothesis

The gradient bound of Dario and Gu, Theorem 3 in the form of Remark 1.3
(`DarioGuGradientBoundTwo`), follows from the Gaussian upper bound of Barlow
(`darioGuGradientBoundTwo_of_barlow`), which is proved
(`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`).
-/

namespace Rigidity.Green

/-- **Dario–Gu, Theorem 3 (Remark 1.3), in dimension two**, with no hypothesis. -/
theorem darioGuGradientBoundTwo_holds : DarioGuGradientBoundTwo :=
  darioGuGradientBoundTwo_of_barlow Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

end Rigidity.Green
