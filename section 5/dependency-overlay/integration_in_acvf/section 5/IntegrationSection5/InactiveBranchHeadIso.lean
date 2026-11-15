import IntegrationSection5.RVProductBranchCompletion
import IntegrationSection5.FixedVFHeadDescent
import IntegrationSection5.GammaSpecialRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H N : DefSet (M := M) S 2 m} {u : SpecialBijection A B}
variable {E : Set (Fin m → RV (M := M))}
namespace RVProductBranchCompletion

def inactiveSourceSubset (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) : carrier N ⊆ carrier H :=
  fun p hp => ((Set.ext_iff.mp hN p).mp hp).1

def inactiveImage (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) :=
  restrictPointImage C.preparation.map N (C.inactiveSourceSubset hN)

def inactiveMap (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) : Map N (C.inactiveImage hN) :=
  restrictPointMap C.preparation.map N (C.inactiveSourceSubset hN)

theorem inactiveMap_vf (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) (p : N) (i : Fin 2) :
    vfAt (C.inactiveMap hN p).val i = vfAt p.val i := by
  let q : H := ⟨p.val,C.inactiveSourceSubset hN p.property⟩
  have hFlag : q.val.2 ∉ E := ((Set.ext_iff.mp hN p.val).mp p.property).2
  fin_cases i
  · exact C.preparation_inactive_vf q hFlag
  · exact specialRelative_unaryRelative C.preparation.special q 1 (by decide)

theorem inactiveMap_sameRV (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E})
    (p q : N) (he : SameRV p.val q.val) :
    SameRV (C.inactiveMap hN p).val (C.inactiveMap hN q).val :=
  C.preparation_inactive_sameRV ⟨p.val,C.inactiveSourceSubset hN p.property⟩
    ⟨q.val,C.inactiveSourceSubset hN q.property⟩
    ((Set.ext_iff.mp hN p.val).mp p.property).2 ((Set.ext_iff.mp hN q.val).mp q.property).2 he

theorem inactiveMap_oldLabels (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) (p : N) :
    (C.inactiveMap hN p).val.2 ∘ suffixIndex (specialRelative_rvArity_le C.preparation.special) = p.val.2 := by
  funext j
  exact specialRelative_oldLabels C.preparation.special ⟨p.val,C.inactiveSourceSubset hN p.property⟩ j

def inactiveHeadIso (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) (hNΓ : GammaSetDefinable G (carrier N)) :
    GammaIso G (carrier (headImage N)) (carrier (headImage (C.inactiveImage hN))) :=
  fixedVFHeadIso (C.inactiveMap hN)
    (restrictPointMap_surjective C.preparation.map N (C.inactiveSourceSubset hN)) hNΓ
    (gamma_restrictPointImage C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (gamma_restrictPointMap C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (C.inactiveMap_vf hN) (suffixIndex (specialRelative_rvArity_le C.preparation.special))
    (C.inactiveMap_oldLabels hN) (C.inactiveMap_sameRV hN)

theorem inactiveHeadIso_square (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) (hNΓ : GammaSetDefinable G (carrier N)) (p : N) :
    (C.inactiveHeadIso hN hNΓ).equiv (Map.toImage (headKeyMap N) p) =
      Map.toImage (headKeyMap (C.inactiveImage hN)) (C.inactiveMap hN p) :=
  fixedVFHeadIso_square (C.inactiveMap hN)
    (restrictPointMap_surjective C.preparation.map N (C.inactiveSourceSubset hN)) hNΓ
    (gamma_restrictPointImage C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (gamma_restrictPointMap C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (C.inactiveMap_vf hN) (suffixIndex (specialRelative_rvArity_le C.preparation.special))
    (C.inactiveMap_oldLabels hN) (C.inactiveMap_sameRV hN) p

end RVProductBranchCompletion
end IntegrationInACVF.Section5
