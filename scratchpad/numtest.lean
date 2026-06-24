import GoodsteinPA.InternalONote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
example : (0:V) ≠ 2 := by simp
example : (0:V) ≠ 1 := by simp
example : (2:V) ≠ 1 := by simp
example : (1:V) ≠ 2 := by simp
