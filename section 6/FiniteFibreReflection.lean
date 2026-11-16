import «section 6».RVScalarArithmeticMaps

/-! A new actual map has finite fibres whenever equality of its values
forces equality of the values of a known finite-to-one map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M]

theorem finiteFibres_of_value_reflection
    {P Q R : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}
    (f : Map A B) (g : Map A C) (hf : f.FiniteFibres)
    (hReflect : ∀ a b : A, g a = g b → f a = f b) : g.FiniteFibres := by
  intro c
  by_cases hne : {a : A | g a = c}.Nonempty
  · obtain ⟨a₀,ha₀⟩ := hne
    apply (hf (f a₀)).subset
    intro a ha
    exact hReflect a a₀ (ha.trans ha₀.symm)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

end DiamondIntegral.Section6
