import «section 6».FiniteFibreReflection
import Section4.FiniteGluing

/-! Replacing a map on a definable piece. The graph and both finite
fibre bounds stay over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section6
variable {L : Language} {M : Type} [L.Structure M] {P Q : Space L M} {S : Set M}
variable {A D : DefSet P S} {B : DefSet Q S}

def replaceMapOn (f : Map D B) (g : Map A B) : Map A B :=
  (f.union g).comp (Map.inclusion (fun _ h => Or.inr h))

theorem replaceMapOn_of_mem (f : Map D B) (g : Map A B) (a : A) (h : a.val ∈ D.carrier) :
    replaceMapOn f g a = f ⟨a.val,h⟩ := by
  change (if h' : a.val ∈ D.carrier then f ⟨a.val,h'⟩ else _) = _
  rw [dif_pos h]

theorem replaceMapOn_of_not_mem (f : Map D B) (g : Map A B) (a : A) (h : a.val ∉ D.carrier) :
    replaceMapOn f g a = g a := by
  change (if h' : a.val ∈ D.carrier then _ else _) = _
  rw [dif_neg h]
  rfl

theorem replaceMapOn_finiteFibres (f : Map D B) (g : Map A B)
    (hf : f.FiniteFibres) (hg : g.FiniteFibres) : (replaceMapOn f g).FiniteFibres := by
  apply (hf.union hg).comp
  apply Map.finiteFibres_of_injective
  intro a b he
  exact Subtype.ext (congrArg (fun x : D.union A => x.val) he)

end DiamondIntegral.Section6
