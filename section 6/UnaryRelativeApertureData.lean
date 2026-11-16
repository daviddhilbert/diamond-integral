import «section 6».UnaryCentripetalExistence
import «section 6».UnaryApertureTransport

/-! Auxiliary, unapplied variable-aperture unary primitive. The endpoint
is an actual original-base definable VF map, constant on retained-label
fibres. It need not be one globally named scalar times the focus.
The source invariance radius on each retained-label fibre is dominated
by that fibre's endpoint value.
This does not alter the paper's existing CentripetalData or chain type. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

structure UnaryRelativeApertureData (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  focusData : UnaryFocusData A
  endpoint : (Fin r → RVInfinity M) → VF M
  endpointMap : Map (focusActive A focusData.activeTags) (DefSet.univ (rawVFSpace 1) S)
  endpointMap_eq : ∀ p : focusActive A focusData.activeTags,
    (endpointMap p).val 0=endpoint p.val.2
  endpoint_nonzero : ∀ p : focusActive A focusData.activeTags,endpoint p.val.2≠0
  endpoint_nonnegative : ∀ p : focusActive A focusData.activeTags,
    vfValue (focusData.focus p.val.2) ≤ vfValue (endpoint p.val.2)
  radius : (Fin r → RVInfinity M) → Gamma M
  radius_definable : ∀ u,(S ∪ Set.range (rvValues u)).Definable LRV
    {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {radius u}}
  invariant : ∀ u,AlphaInvariant (fun _ => radius u) (vfFibre A.carrier u)
  radius_le_endpoint : ∀ p : focusActive A focusData.activeTags,
    (radius p.val.2).val ≤ vfValue (endpoint p.val.2)

namespace UnaryRelativeApertureData
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def coordinate (_D : UnaryRelativeApertureData A) : Fin 1 := 0

def focusMap (D : UnaryRelativeApertureData A) := D.focusData.focusMap

def extendedFocus (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) : VF M :=
  ⟨scalarCodeExtension D.focusMap (mixedValues p),scalarCodeExtension_isVF D.focusMap _⟩

def extendedEndpoint (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) : VF M :=
  ⟨scalarCodeExtension D.endpointMap (mixedValues p),scalarCodeExtension_isVF D.endpointMap _⟩

theorem extendedFocus_active (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) : D.extendedFocus p.val=D.focusData.focus p.val.2 :=
  (Subtype.ext (scalarCodeExtension_at D.focusMap p)).trans (D.focusData.focusMap_eq p)

theorem extendedEndpoint_active (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) : D.extendedEndpoint p.val=D.endpoint p.val.2 :=
  (Subtype.ext (scalarCodeExtension_at D.endpointMap p)).trans (D.endpointMap_eq p)

theorem scalarExtension_inactive
    {D : UnaryRelativeApertureData A}
    (F : Map (focusActive A D.focusData.activeTags) (DefSet.univ (rawVFSpace 1) S))
    {p : Mixed M 1 r}
    (hu : p.2 ∉ D.focusData.activeTags.carrier) :
    scalarCodeExtension F (mixedValues p)=iVFZero := by
  have hno : mixedValues p ∉ (rawMixedSpace 1 r).preimage (focusActive A D.focusData.activeTags).carrier := by
    rintro ⟨hz,hp⟩
    have hp' : p ∈ (focusActive A D.focusData.activeTags).carrier := by
      simpa only [decode_mixedValues] using hp
    exact hu hp'.2
  rw [scalarCodeExtension,dite_eq_right hno]

theorem extendedFocus_same_tags (D : UnaryRelativeApertureData A)
    {p q : Mixed M 1 r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (hu : p.2=q.2) :
    D.extendedFocus p=D.extendedFocus q := by
  by_cases ha : p.2 ∈ D.focusData.activeTags.carrier
  · exact (D.extendedFocus_active ⟨p,hp,ha⟩).trans
      ((congrArg D.focusData.focus hu).trans (D.extendedFocus_active ⟨q,hq,hu ▸ ha⟩).symm)
  · apply Subtype.ext
    exact (scalarExtension_inactive D.focusMap ha).trans
      (scalarExtension_inactive D.focusMap (hu ▸ ha)).symm

theorem extendedEndpoint_same_tags (D : UnaryRelativeApertureData A)
    {p q : Mixed M 1 r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (hu : p.2=q.2) :
    D.extendedEndpoint p=D.extendedEndpoint q := by
  by_cases ha : p.2 ∈ D.focusData.activeTags.carrier
  · exact (D.extendedEndpoint_active ⟨p,hp,ha⟩).trans
      ((congrArg D.endpoint hu).trans (D.extendedEndpoint_active ⟨q,hq,hu ▸ ha⟩).symm)
  · apply Subtype.ext
    exact (scalarExtension_inactive D.endpointMap ha).trans
      (scalarExtension_inactive D.endpointMap (hu ▸ ha)).symm

def core (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) : Bool :=
  decide (vfValue (D.extendedEndpoint p) < vfValue (p.1 D.coordinate-D.extendedFocus p))

def point (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) : Mixed M 1 (1+r) :=
  (Function.update p.1 D.coordinate (p.1 D.coordinate-D.extendedFocus p+
    if D.core p then D.extendedEndpoint p else 0),
    Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core p)) p.2)

theorem point_injective_on (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00) :
    Set.InjOn D.point A.carrier := by
  intro p hp q hq he
  have hOld : p.2=q.2 := funext fun i => by
    simpa only [point,Fin.append_right] using
      congrArg (fun z : Mixed M 1 (1+r) => z.2 (Fin.natAdd 1 i)) he
  have hTag : branchTag (M := M) (D.core p)=branchTag (M := M) (D.core q) := by
    simpa only [point,Fin.append_left] using
      congrArg (fun z : Mixed M 1 (1+r) => z.2 (Fin.castAdd r 0)) he
  have hCore := branchTag_injective h00 hTag
  have hFocus := D.extendedFocus_same_tags hp hq hOld
  have hEnd := D.extendedEndpoint_same_tags hp hq hOld
  have hJ := congrArg (fun z : Mixed M 1 (1+r) => z.1 D.coordinate) he
  simp only [point,Function.update_self] at hJ
  rw [hFocus,hEnd,hCore] at hJ
  have hField : p.1 D.coordinate=q.1 D.coordinate := by
    have hsub := add_right_cancel hJ
    calc
      p.1 D.coordinate = (p.1 D.coordinate-D.extendedFocus q)+D.extendedFocus q := (sub_add_cancel _ _).symm
      _ = (q.1 D.coordinate-D.extendedFocus q)+D.extendedFocus q := congrArg (fun x => x+D.extendedFocus q) hsub
      _ = q.1 D.coordinate := sub_add_cancel _ _
  apply Prod.ext _ hOld
  funext i
  have hi : i=D.coordinate := Subsingleton.elim _ _
  exact hi ▸ hField

theorem endpointImage_finite (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : (scalarFocusImage D.endpointMap).Finite :=
  scalarFocusImage_finite hc hs hsmall D.endpointMap (fun p q he => by
    rw [D.endpointMap_eq,D.endpointMap_eq,he])

end UnaryRelativeApertureData
end DiamondIntegral.Section6
