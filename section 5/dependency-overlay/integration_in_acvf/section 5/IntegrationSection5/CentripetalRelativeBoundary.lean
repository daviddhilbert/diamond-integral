import IntegrationSection5.FibreFocusBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

theorem centripetal_specialRelativeBoundary (D : Focus A i k) (previous : Option Bool)
    (hp : previous ≠ some true) :
    SpecialRelativeBoundary (SpecialBijection.centripetal D).toMap i previous (some true) := by
  apply specialRelativeBoundary_of_fibre_focus D.etaMap (centripetal_unaryRelative D)
    (fun u => fibreFocus D u) (fun u p => ?_) previous hp
  exact fibreFocusGeometry_eta_insert D u p

end IntegrationInACVF.Section5
