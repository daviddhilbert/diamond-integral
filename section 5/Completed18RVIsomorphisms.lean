import «section 5».Completed18RVGraphs
import IntegrationSection6.GammaNativeRawIsomorphisms

/-! Both object conversions preserve all actual original-Gamma domain
bijections. No labels are required to be preserved by such a bijection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def groundRVAtDomainEquiv (U : GammaGroundRVObject hc B k) :
    U.domain ≃ rvObjectDomain (groundRVAt U).object.obj where
  toFun u := ⟨u.val,(groundRVAt_domain U).symm ▸ u.property⟩
  invFun u := ⟨u.val,(groundRVAt_domain U) ▸ u.property⟩
  left_inv u := rfl
  right_inv u := rfl

def groundRVAtIso {U V : GammaGroundRVObject hc B k}
    (f : GammaGroundBijection U.domain V.domain) : GammaIsoAt (groundRVAt U) (groundRVAt V) := by
  let P := groundRVAtDomainEquiv U
  let Q := groundRVAtDomainEquiv V
  let e := P.symm.trans ((Equiv.ofBijective f.map f.bijective).trans Q)
  apply fullWeightIsoAtOfEquiv _ _ (groundRVAt_full U) (groundRVAt_full V) e
  apply GammaGraphDefinable.congr (groundRV_gamma_map f.map)
  intro p q
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨P u,hu,?_⟩
    change (Q (f.map (P.symm (P u)))).val=q.2
    rw [P.symm_apply_apply]
    exact hv
  · rintro ⟨u,hu,hv⟩
    exact ⟨P.symm u,hu,hv⟩

theorem nativeRVGroundDomain_carrier (U : GammaObjectAt B Set.univ k) :
    (nativeRVGroundDomain (hc := hc) U).carrier =
      (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)) := by
  ext x
  change (∃ u : rvObjectDomain U.object.obj,(fun j => (u.val j).val)=SpecialTransformations.Section4.rvValues x) ↔ _
  constructor
  · rintro ⟨u,hu⟩
    have he : u.val=x := by
      funext j
      exact Subtype.ext (congrFun hu j)
    exact he ▸ u.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

def nativeRVGroundDomainEquiv (U : GammaObjectAt B Set.univ k) :
    nativeRVGroundDomain (hc := hc) U ≃ rvObjectDomain U.object.obj where
  toFun u := ⟨u.val,(nativeRVGroundDomain_carrier U) ▸ u.property⟩
  invFun u := ⟨u.val,(nativeRVGroundDomain_carrier U).symm ▸ u.property⟩
  left_inv u := rfl
  right_inv u := rfl

def nativeRVGroundIso {U V : GammaObjectAt B Set.univ k} (e : GammaIsoAt U V) :
    GammaGroundBijection (nativeRVGroundDomain (hc := hc) U) (nativeRVGroundDomain V) := by
  let P := nativeRVGroundDomainEquiv (hc := hc) U
  let Q := nativeRVGroundDomainEquiv (hc := hc) V
  let f := P.trans (e.toGamma.equiv.trans Q.symm)
  have he : groundRVMapRawGraph f = gammaRawIsoGraph e.toGamma := by
    ext w
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨P u,hu⟩
    · rintro ⟨u,hu⟩
      refine ⟨P.symm u,?_⟩
      change Fin.append (SpecialTransformations.Section4.rvValues (P.symm u).val)
        (SpecialTransformations.Section4.rvValues (Q.symm (e.toGamma.equiv (P (P.symm u)))).val)=w
      rw [P.apply_symm_apply]
      exact hu
  refine ⟨groundRVMapOfRawGraph f ?_,f.bijective⟩
  rw [he]
  have hs : Fin.append (fun _ : Fin (rvObjectArity U.object.obj) => SortTag.rv)
      (fun _ : Fin (rvObjectArity V.object.obj) => SortTag.rv) = (fun _ => SortTag.rv) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left,Fin.append_right]
  exact (congrArg (fun sn : Fin (rvObjectArity U.object.obj + rvObjectArity V.object.obj) → SortTag =>
    DefinableOverBase B sn (gammaRawIsoGraph e.toGamma)) hs).mpr (gammaRawIsoGraph_definable e.toGamma)

def groundRVAtToNativeIso (U : GammaGroundRVObject hc B k)
    (V : GammaObjectAt B Set.univ k) (hV : GammaFullWeightAt V)
    (f : GammaGroundBijection U.domain (nativeRVGroundDomain (hc := hc) V)) :
    GammaIsoAt (groundRVAt U) V := by
  let P := groundRVAtDomainEquiv U
  let Q := nativeRVGroundDomainEquiv (hc := hc) V
  let e := P.symm.trans ((Equiv.ofBijective f.map f.bijective).trans Q)
  apply fullWeightIsoAtOfEquiv _ _ (groundRVAt_full U) hV e
  apply GammaGraphDefinable.congr (groundRV_gamma_map f.map)
  intro p q
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨P u,hu,?_⟩
    change (Q (f.map (P.symm (P u)))).val=q.2
    rw [P.symm_apply_apply]
    exact hv
  · rintro ⟨u,hu,hv⟩
    exact ⟨P.symm u,hu,hv⟩

def groundRVObjectRoundTrip (U : GammaGroundRVObject hc B k) :
    GammaGroundBijection
      (nativeRVGroundObject (groundRVAt U) (groundRVAt_full U)).domain U.domain :=
  GammaGroundBijection.ofCarrierEq ((nativeRVGroundDomain_carrier (groundRVAt U)).trans (groundRVAt_domain U))

def nativeRVObjectRoundTrip (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U) :
    GammaIsoAt (groundRVAt (nativeRVGroundObject (hc := hc) U hU)) U :=
  groundRVAtToNativeIso _ U hU (GammaGroundBijection.id _)


end DiamondIntegral.Section5
