import «section 5».Completed18CellBaseTransfer
import IntegrationSection6.FiniteGammaObjects

/-! Actual finite RV presentations and their isomorphisms descend from
definable parameter extensions. Their domains and volume maps are unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def nativeFiniteRVBaseTransfer {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {n : ℕ} (U : GammaRVFiniteObject G n) (hHU : H.real ⊆ U.codes) : GammaRVFiniteObject H n where
  codes := U.codes
  real_contains := hHU
  object := U.object
  domain_graph := h.transfer U.domain_graph
  volume_graph := h.transfer U.volume_graph
  finite_volume := U.finite_volume

def nativeFiniteRVIsoBaseTransfer {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {n : ℕ} {U V : GammaRVFiniteObject G n} (hHU : H.real ⊆ U.codes) (hHV : H.real ⊆ V.codes)
    (e : SpecialTransformations.Section7.GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    SpecialTransformations.Section7.GammaRVIso
      (nativeFiniteRVBaseTransfer h U hHU).toGammaRVObject
      (nativeFiniteRVBaseTransfer h V hHV).toGammaRVObject where
  equiv := e.equiv
  graph := h.transfer e.graph
  weight := e.weight
  leftFinite := e.leftFinite
  rightFinite := e.rightFinite

def gammaIsoMapUniv {B : Base (M := M)} {n m u w : ℕ}
    (U : DefSet (M := M) Set.univ n m) (V : DefSet (M := M) Set.univ u w)
    (e : GammaIso B (carrier U) (carrier V)) : Map U V := by
  refine Map.mk e.equiv ?_
  obtain ⟨d,t,hr⟩ := GammaGraphDefinable.real_specialize e.graph
  exact RelationDefinable.mono _ _ hr (Set.subset_univ _)

end DiamondIntegral.Section5
