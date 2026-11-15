import IntegrationSection5.CommonProductHeadPair
import IntegrationSection5.HeadProjectionPadding
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
namespace IntegrationInACVF.Section5.CanonicalProductBranchCompletion
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H : DefSet (M := M) S (n+1) (1+m)} {u : SpecialBijection A B}
variable {E : Set (Fin m → RV (M := M))}

theorem inactive_vf (C : CanonicalProductBranchCompletion (G := G) u H E)
    (p : H) (hp : p.val.2 ∘ Fin.natAdd 1 ∉ E) : vfAt (C.preparation.map p).val 0 = vfAt p.val 0 := by
  have hFlag : (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) ∉ E := by
    rw [C.prefix_formula]
    have he : (coordinateCanonical 0 p.val).2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) = p.val.2 ∘ Fin.natAdd 1 :=
      congrArg (fun s => s ∘ Fin.natAdd 1) (coordinateCanonical_oldRV 0 p.val)
    rwa [he]
  exact (C.head.inactive_vf (C.preMap p) hFlag).trans
    (congrArg (fun q : Point (M := M) (n+1) (1+(1+m)) => vfAt q 0) (C.prefix_formula p))

theorem inactive_sameRV (C : CanonicalProductBranchCompletion (G := G) u H E)
    (p q : H) (hp : p.val.2 ∘ Fin.natAdd 1 ∉ E) (hq : q.val.2 ∘ Fin.natAdd 1 ∉ E)
    (he : SameRV p.val q.val) : SameRV (C.preparation.map p).val (C.preparation.map q).val := by
  apply C.head.inactive_sameRV (C.preMap p) (C.preMap q)
  · rw [C.prefix_formula]
    have hOld : (coordinateCanonical 0 p.val).2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) = p.val.2 ∘ Fin.natAdd 1 :=
      congrArg (fun s => s ∘ Fin.natAdd 1) (coordinateCanonical_oldRV 0 p.val)
    rwa [hOld]
  · rw [C.prefix_formula]
    have hOld : (coordinateCanonical 0 q.val).2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) = q.val.2 ∘ Fin.natAdd 1 :=
      congrArg (fun s => s ∘ Fin.natAdd 1) (coordinateCanonical_oldRV 0 q.val)
    rwa [hOld]
  · rw [C.prefix_formula,C.prefix_formula]
    exact coordinateCanonical_sameRV 0 he
end IntegrationInACVF.Section5.CanonicalProductBranchCompletion

namespace IntegrationInACVF.Section5.CanonicalProductBranchCompletion
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H N : DefSet (M := M) S 2 (1+m)} {u : SpecialBijection A B}
variable {E : Set (Fin m → RV (M := M))}

def inactiveSubset (C : CanonicalProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∉ E}) : carrier N ⊆ carrier H :=
  fun p hp => ((Set.ext_iff.mp hN p).mp hp).1

def inactiveImage (C : CanonicalProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∉ E}) :=
  restrictPointImage C.preparation.map N (C.inactiveSubset hN)

def inactivePadding (C : CanonicalProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∉ E}) (hNΓ : GammaSetDefinable G (carrier N)) :
    RVProjectionPadding (G := G) (headImage (C.inactiveImage hN)) (headImage N)
      (headPaddingProjection (suffixIndex (specialRelative_rvArity_le C.preparation.special))) := by
  let f := restrictPointMap C.preparation.map N (C.inactiveSubset hN)
  have hVF (p : N) (i : Fin 2) : vfAt (f p).val i = vfAt p.val i := by
    fin_cases i
    · exact C.inactive_vf ⟨p.val,C.inactiveSubset hN p.property⟩ ((Set.ext_iff.mp hN p.val).mp p.property).2
    · exact specialRelative_unaryRelative C.preparation.special ⟨p.val,C.inactiveSubset hN p.property⟩ 1 (by decide)
  have hRV (p q : N) (he : SameRV p.val q.val) : SameRV (f p).val (f q).val :=
    C.inactive_sameRV ⟨p.val,C.inactiveSubset hN p.property⟩ ⟨q.val,C.inactiveSubset hN q.property⟩
      ((Set.ext_iff.mp hN p.val).mp p.property).2 ((Set.ext_iff.mp hN q.val).mp q.property).2 he
  have hLabels (p : N) : (f p).val.2 ∘ suffixIndex (specialRelative_rvArity_le C.preparation.special) = p.val.2 := by
    funext j
    exact specialRelative_oldLabels C.preparation.special ⟨p.val,C.inactiveSubset hN p.property⟩ j
  exact fixedVFHeadProjectionPadding f
    (restrictPointMap_surjective C.preparation.map N (C.inactiveSubset hN)) hNΓ
    (gamma_restrictPointImage C.preparation.map N (C.inactiveSubset hN) hNΓ C.graph)
    (gamma_restrictPointMap C.preparation.map N (C.inactiveSubset hN) hNΓ C.graph)
    hVF _ hLabels hRV

end IntegrationInACVF.Section5.CanonicalProductBranchCompletion
