import «section 3».GammaMeasuredIndexedGeometry
import IntegrationSection6.GammaIdentityIndexPresentation

/-! At the end of contraction there are no VF parameters. Realize the
remaining complete Gamma row over the zero-degree RV index and apply
the already proved indexed soundness theorem in the principal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b k : ℕ}
variable {sp sq : Fin p → SortTag}

def GammaMeasuredRVSchema.changeParameterSort (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (h : sp = sq) : GammaMeasuredRVSchema hc B p a (k+1) sq := h ▸ F

theorem GammaMeasuredRVSchema.changeParameterSort_valid
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (h : sp = sq) (z : Fin p → M) :
    (F.changeParameterSort h).valid z ↔ F.valid z := by
  cases h
  rfl

def GammaMeasuredRelationSchema.changeParameterSort
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {E : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F E) (h : sp = sq) :
    GammaMeasuredRelationSchema (F.changeParameterSort h) (E.changeParameterSort h) := by
  cases h
  exact H

theorem GammaMeasuredRelationSchema.changeParameterSort_valid
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {E : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F E) (h : sp = sq) (z : Fin p → M) :
    (H.changeParameterSort h).valid z ↔ H.valid z := by
  cases h
  rfl

def gammaEmptyParameterSortEq (sp : Fin 0 → SortTag) : sp = (fun _ => .rv) :=
  funext (fun i => Fin.elim0 i)

def gammaEmptyParameterIndex (B : Base (M := M)) : IdentityIndexPresentation B 0 :=
  Classical.choice (gamma_identity_index_presentation_exists B 0)

variable {sp0 : Fin 0 → SortTag}

def GammaMeasuredRVSchema.emptyRV (F : GammaMeasuredRVSchema hc B 0 a (k+1) sp0) :=
  F.changeParameterSort (gammaEmptyParameterSortEq sp0)

theorem GammaMeasuredRVSchema.emptyRV_valid
    (F : GammaMeasuredRVSchema hc B 0 a (k+1) sp0) (hF : F.valid Fin.elim0)
    (t : Fin 0 → RV (M := M)) : F.emptyRV.valid (rvValues t) := by
  apply (F.changeParameterSort_valid _ _).mpr
  exact Eq.mpr (congrArg F.valid (Subsingleton.elim (rvValues t) Fin.elim0)) hF

def GammaMeasuredRVSchema.emptyParameterObject
    (F : GammaMeasuredRVSchema hc B 0 a (k+1) sp0) (hF : F.valid Fin.elim0) :
    GammaGroundMeasuredRVObject hc B ((0+k)+1) :=
  F.emptyRV.indexedObject (gammaEmptyParameterIndex B)
    (fun t _ => F.emptyRV_valid hF t)
    (F.emptyRV.object.indexedPresentation (gammaEmptyParameterIndex B) (fun t _ => (F.emptyRV_valid hF t).1))

def GammaMeasuredRVSchema.emptyParameterValue
    (F : GammaMeasuredRVSchema hc B 0 a (k+1) sp0) (hF : F.valid Fin.elim0) :=
  gammaMeasuredPrincipalValue (F.emptyParameterObject hF)

theorem GammaMeasuredRelationSchema.emptyParameter_sound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {F : GammaMeasuredRVSchema hc B 0 a (k+1) sp0} {E : GammaMeasuredRVSchema hc B 0 b (k+1) sp0}
    (H : GammaMeasuredRelationSchema F E) (hF : F.valid Fin.elim0) (hE : E.valid Fin.elim0)
    (hH : H.valid Fin.elim0) : F.emptyParameterValue hF = E.emptyParameterValue hE := by
  let K := H.changeParameterSort (gammaEmptyParameterSortEq sp0)
  have hK (t : Fin 0 → RV (M := M)) (_ : t ∈ (Set.univ : Set (Fin 0 → RV (M := M)))) :
      K.valid (rvValues t) := by
    apply (H.changeParameterSort_valid _ _).mpr
    exact Eq.mpr (congrArg H.valid (Subsingleton.elim (rvValues t) Fin.elim0)) hH
  exact K.indexed_sound hκ hs h00 hr hg (gammaEmptyParameterIndex B)
    (fun t _ => F.emptyRV_valid hF t) (fun t _ => E.emptyRV_valid hE t) hK _ _

end DiamondIntegral.Section3
