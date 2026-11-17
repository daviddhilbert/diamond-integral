import «section 3».GammaMeasuredLiteralNormalizationRows
import «section 3».GammaSelectedRetainedData
import IntegrationSection6.GammaSelectedRVPresentations

/-! The literal pure-RV selected presentation has exactly the final
complete Gamma schema rows. Its density is the retained original form,
without a choice of representatives or a change of base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable (U : GammaSelectedRetainedData hc B 0 (k+1))
variable (P : GammaSelectedRVPresentation B U.set U.select)

theorem gammaPureSelected_mem
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (Fin.elim0,u.val) ∈ carrier U.set := by
  let v := Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma) u
  exact P.domain_eq.le v.property

def gammaPureSelectedLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) U.labels :=
  GammaGroundMap.inclusion (fun r hr => U.labels_mem ⟨(Fin.elim0,r),gammaPureSelected_mem U P ⟨r,hr⟩⟩)

def gammaPureSelectedForm := U.form.comp (gammaPureSelectedLabels U P)

def gammaPureSelectedObject : GammaGroundMeasuredRVObject hc B (k+1) :=
  gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma) (gammaPureSelectedForm U P)

theorem gammaPureSelected_volume (N : ℕ) (r : Fin U.arity → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    (U.schema N).object.rowVolume (vfValues (Fin.elim0 : Fin 0 → VF (M := M))) r y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = r ∧ (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val = y := by
  have hS := gammaSelectedLabelSchema_volume U.set U.gamma U.select
    (Fin.elim0 : Fin 0 → VF (M := M)) r y
  apply hS.trans
  constructor
  · intro h
    obtain ⟨v,hv,hV⟩ := (P.graph_iff r y).mpr ⟨h.1,h⟩
    let u := (Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma)).symm v
    refine ⟨u,hv,?_⟩
    exact (gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) u).trans hV
  · rintro ⟨u,hu,hV⟩
    let v := Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma) u
    exact ((P.graph_iff r y).mp ⟨v,hu,
      (gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) u).symm.trans hV⟩).2

theorem gammaPureSelected_density (N : ℕ) (r : Fin U.arity → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    (U.schema N).rowDensity (vfValues (Fin.elim0 : Fin 0 → VF (M := M))) r c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = r ∧ (gammaPureSelectedForm U P u).val = (volumeGammaSpace hc).decode c := by
  have hS := gammaMeasuredSelectedSchema_density U.set U.gamma U.select U.pointForm
    (Fin.elim0 : Fin 0 → VF (M := M)) r c
  apply hS.trans
  constructor
  · rintro ⟨q,hq,hω⟩
    have hr : r ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)).carrier := by
      apply (Section5.nativeRVGroundDomain_carrier _).ge
      apply P.domain_eq.ge
      change (Fin.elim0,r) ∈ carrier U.set
      exact hq ▸ q.property
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) := ⟨r,hr⟩
    have he : gammaPureSelectedForm U P u = U.pointForm q := by
      apply congrArg U.form
      apply Subtype.ext
      exact (congrArg Prod.snd hq).symm
    exact ⟨u,rfl,(congrArg Subtype.val he).trans hω⟩
  · rintro ⟨u,hu,hω⟩
    let q : Section5.nativeGammaPointDomain (hc := hc) (carrier U.set) U.gamma :=
      ⟨(Fin.elim0,u.val),gammaPureSelected_mem U P u⟩
    refine ⟨q,Prod.ext rfl hu,?_⟩
    exact hω

theorem gammaPureSelected_normalized_row (N : ℕ) :
    GammaMeasuredLiteralObjectRow (Fin.elim0 : Fin 0 → M) (gammaPureSelectedObject U P) (U.schema N).essential := by
  have h := gammaMeasured_normalization_literal_row
    (vfValues (Fin.elim0 : Fin 0 → VF (M := M))) (gammaUniversalObject P.toGamma)
    (gammaPureSelectedForm U P) (U.schema N) (gammaPureSelected_volume U P N) (gammaPureSelected_density U P N)
  have he : vfValues (Fin.elim0 : Fin 0 → VF (M := M)) = Fin.elim0 := Subsingleton.elim _ _
  exact he ▸ h

end DiamondIntegral.Section3
