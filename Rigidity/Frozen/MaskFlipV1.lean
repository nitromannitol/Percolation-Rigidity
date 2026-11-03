import Mathlib.Data.Bool.Basic

namespace RigidityFullProduct

def maskFlip {ι : Type*} (f ω : ι → Bool) : ι → Bool :=
  fun e => if f e = true then !(ω e) else ω e

end RigidityFullProduct
