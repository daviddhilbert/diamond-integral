import IntegrationSection6.VFParameterFibreIsomorphisms
import IntegrationSection6.GammaSortedParameterPreservation

/-! The existing VF-parameter fibre isomorphism restricts a VF-fixed
Gamma bijection to its literal finite RV rows, with the same output map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {U : Set (Point (M := M) p a)} {V : Set (Point (M := M) p b)}

theorem gammaZeroVFParameterFibre_eq (U : Set (Point (M := M) p a)) (x : Fin p → VF (M := M)) :
    vfParameterFibre (p := p) (n := 0) U x = {q : Point (M := M) 0 a | (x,q.2) ∈ U} := by
  ext q
  have he : vfParameterInsert x q = (x,q.2) :=
    Prod.ext (funext (fun j => Fin.append_left x q.1 j)) rfl
  exact Iff.of_eq (congrArg (fun z => z ∈ U) he)

def gammaFixedVFRowIso (e : GammaIso B U V) (hp : ∀ u, (e.equiv u).val.1 = u.val.1)
    (x : Fin p → VF (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      {q : Point (M := M) 0 a | (x,q.2) ∈ U} {q : Point (M := M) 0 b | (x,q.2) ∈ V} :=
  (gammaVFParameterFibreIso (p := p) (n := 0) (m := 0) e (fun u j => congrFun (hp u) j) x).congr
    (gammaZeroVFParameterFibre_eq U x) (gammaZeroVFParameterFibre_eq V x)

theorem gammaFixedVFRowIso_value (e : GammaIso B U V) (hp : ∀ u, (e.equiv u).val.1 = u.val.1)
    (x : Fin p → VF (M := M)) (u : {q : Point (M := M) 0 a | (x,q.2) ∈ U}) :
    ((gammaFixedVFRowIso e hp x).equiv u).val.2 = (e.equiv ⟨(x,u.val.2),u.property⟩).val.2 := by
  unfold gammaFixedVFRowIso
  rw [gammaIsoCongr_value]
  let u0 := (Equiv.subtypeEquivRight (fun q : Point (M := M) 0 a =>
    Iff.of_eq (congrArg (fun D : Set (Point (M := M) 0 a) => q ∈ D)
      (gammaZeroVFParameterFibre_eq U x)))).symm u
  have hi : (⟨vfParameterInsert x u0.val,u0.property⟩ : U) = ⟨(x,u.val.2),u.property⟩ := by
    apply Subtype.ext
    exact Prod.ext (funext (fun j => Fin.append_left x u0.val.1 j)) rfl
  have h := congrArg Prod.snd (vfParameterRowEquiv_packed (p := p) (n := 0) (m := 0)
    e (fun q j => congrFun (hp q) j) x u0)
  exact h.trans (congrArg (fun q : U => (e.equiv q).val.2) hi)

end DiamondIntegral.Section3
