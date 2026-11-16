import «section 6».CentripetalData

/-! Auxiliary bounded variable apertures in arbitrary VF arity. The
endpoint is an actual continuous original-base VF graph independent of
the changed coordinate. Its RV value depends only on retained labels;
a named relative-value bound replaces the old scalar coefficient.
Original scalar data and the main manuscript remain unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure RelativeApertureData (A : DefSet (rawMixedSpace (M := M) n r) S) where
  coordinate : Fin n
  activeTags : DefSet (rawRVSpace (M := M) r) S
  focus : (Fin n → VF M) → (Fin r → RVInfinity M) → VF M
  focusMap : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace 1) S)
  focusMap_eq : ∀ p : focusActive A activeTags,
    (focusMap p).val 0 = focus (Function.update p.val.1 coordinate 0) p.val.2
  sourceProper : ProperInvariant S A.carrier
  sourceDoublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  continuous : ∀ u ∈ activeTags.carrier,
    ContinuousOn (fun x => focus (Function.update x coordinate 0) u) (vfFibre A.carrier u)
  focusRV : ∀ p ∈ A.carrier, p.2 ∈ activeTags.carrier →
    rv M (focus (Function.update p.1 coordinate 0) p.2) = rv M (p.1 coordinate)
  endpoint : (Fin n → VF M) → (Fin r → RVInfinity M) → VF M
  endpointMap : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace 1) S)
  endpointMap_eq : ∀ p : focusActive A activeTags,
    (endpointMap p).val 0=endpoint (Function.update p.val.1 coordinate 0) p.val.2
  endpoint_continuous : ∀ u ∈ activeTags.carrier,
    ContinuousOn (fun x => endpoint (Function.update x coordinate 0) u) (vfFibre A.carrier u)
  endpoint_nonzero : ∀ p : focusActive A activeTags,
    endpoint (Function.update p.val.1 coordinate 0) p.val.2 ≠ 0
  endpoint_nonnegative : ∀ p : focusActive A activeTags,
    vfValue (focus (Function.update p.val.1 coordinate 0) p.val.2) ≤
      vfValue (endpoint (Function.update p.val.1 coordinate 0) p.val.2)
  endpoint_RV_constant : ∀ p q : focusActive A activeTags,p.val.2=q.val.2 →
    rv M ((endpointMap p).val 0)=rv M ((endpointMap q).val 0)
  apertureBound : Gamma M
  apertureBound_nonnegative : 1 ≤ apertureBound
  apertureBound_named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {apertureBound}}
  endpoint_upper_bound : ∀ p : focusActive A activeTags,
    vfValue ((endpointMap p).val 0) ≤ apertureBound.val*vfValue (p.val.1 coordinate)
  covariance : ∀ u ∈ activeTags.carrier, ∃ α : Gamma M, ∃ β : Fin n → Gamma M,
    (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}} ∧
    NamedGammaTuple (S ∪ Set.range (rvValues u)) β ∧
    AlphaInvariant (fun i => if i = coordinate then α else β i) (vfFibre A.carrier u) ∧
    (∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent β (Function.update a coordinate 0) (Function.update b coordinate 0) →
      α.val < vfValue (focus (Function.update a coordinate 0) u - focus (Function.update b coordinate 0) u)) ∧
    (∀ a ∈ vfFibre A.carrier u,
      α.val ≤ vfValue (endpoint (Function.update a coordinate 0) u))

namespace RelativeApertureData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def extendedFocus (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : VF M :=
  ⟨scalarCodeExtension D.focusMap (mixedValues p),scalarCodeExtension_isVF D.focusMap _⟩

theorem extendedFocus_active (D : RelativeApertureData (G := G) A)
    {p : Mixed M n r} (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    D.extendedFocus p = D.focus (Function.update p.1 D.coordinate 0) p.2 := by
  have hpa : p ∈ (focusActive A D.activeTags).carrier := ⟨hp,hu⟩
  have he : D.extendedFocus p = (D.focusMap ⟨p,hpa⟩).val 0 :=
    Subtype.ext (scalarCodeExtension_at D.focusMap ⟨p,hpa⟩)
  exact he.trans (D.focusMap_eq ⟨p,hpa⟩)

theorem extendedFocus_inactive (D : RelativeApertureData (G := G) A)
    {p : Mixed M n r} (hu : p.2 ∉ D.activeTags.carrier) : D.extendedFocus p = 0 := by
  have hno : mixedValues p ∉ (rawMixedSpace n r).preimage (focusActive A D.activeTags).carrier := by
    rintro ⟨hz,hp⟩
    have hp' : p ∈ (focusActive A D.activeTags).carrier := by simpa only [decode_mixedValues] using hp
    exact hu hp'.2
  apply Subtype.ext
  change scalarCodeExtension D.focusMap (mixedValues p) = iVFZero
  rw [scalarCodeExtension,dite_eq_right hno]

theorem extendedFocus_same_other (D : RelativeApertureData (G := G) A)
    {p q : Mixed M n r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (hu : p.2 = q.2)
    (hother : ∀ i ≠ D.coordinate, p.1 i = q.1 i) : D.extendedFocus p = D.extendedFocus q := by
  classical
  by_cases hact : p.2 ∈ D.activeTags.carrier
  · have hactq : q.2 ∈ D.activeTags.carrier := hu ▸ hact
    rw [D.extendedFocus_active hp hact,D.extendedFocus_active hq hactq]
    have he : Function.update p.1 D.coordinate 0 = Function.update q.1 D.coordinate 0 := by
      funext i
      by_cases hi : i = D.coordinate
      · subst i
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hi]
        exact hother i hi
    rw [he,hu]
  · rw [D.extendedFocus_inactive hact,D.extendedFocus_inactive (hu ▸ hact)]

def extendedEndpoint (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : VF M :=
  ⟨scalarCodeExtension D.endpointMap (mixedValues p),scalarCodeExtension_isVF D.endpointMap _⟩

theorem extendedEndpoint_active (D : RelativeApertureData (G := G) A)
    {p : Mixed M n r} (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    D.extendedEndpoint p = D.endpoint (Function.update p.1 D.coordinate 0) p.2 := by
  have hpa : p ∈ (focusActive A D.activeTags).carrier := ⟨hp,hu⟩
  have he : D.extendedEndpoint p = (D.endpointMap ⟨p,hpa⟩).val 0 :=
    Subtype.ext (scalarCodeExtension_at D.endpointMap ⟨p,hpa⟩)
  exact he.trans (D.endpointMap_eq ⟨p,hpa⟩)

theorem extendedEndpoint_inactive (D : RelativeApertureData (G := G) A)
    {p : Mixed M n r} (hu : p.2 ∉ D.activeTags.carrier) : D.extendedEndpoint p = 0 := by
  have hno : mixedValues p ∉ (rawMixedSpace n r).preimage (focusActive A D.activeTags).carrier := by
    rintro ⟨hz,hp⟩
    have hp' : p ∈ (focusActive A D.activeTags).carrier := by simpa only [decode_mixedValues] using hp
    exact hu hp'.2
  apply Subtype.ext
  change scalarCodeExtension D.endpointMap (mixedValues p) = iVFZero
  rw [scalarCodeExtension,dite_eq_right hno]

theorem extendedEndpoint_same_other (D : RelativeApertureData (G := G) A)
    {p q : Mixed M n r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (hu : p.2 = q.2)
    (hother : ∀ i ≠ D.coordinate, p.1 i = q.1 i) : D.extendedEndpoint p = D.extendedEndpoint q := by
  classical
  by_cases hact : p.2 ∈ D.activeTags.carrier
  · have hactq : q.2 ∈ D.activeTags.carrier := hu ▸ hact
    rw [D.extendedEndpoint_active hp hact,D.extendedEndpoint_active hq hactq]
    have he : Function.update p.1 D.coordinate 0 = Function.update q.1 D.coordinate 0 := by
      funext i
      by_cases hi : i = D.coordinate
      · subst i
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hi]
        exact hother i hi
    rw [he,hu]
  · rw [D.extendedEndpoint_inactive hact,D.extendedEndpoint_inactive (hu ▸ hact)]

def core (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : Bool :=
  decide (vfValue (D.extendedEndpoint p) < vfValue (p.1 D.coordinate - D.extendedFocus p))

def point (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : Mixed M n (1+r) :=
  (Function.update p.1 D.coordinate (p.1 D.coordinate - D.extendedFocus p +
    if D.core p then D.extendedEndpoint p else 0),
    Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core p)) p.2)

theorem point_injective_on (D : RelativeApertureData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) :
    Set.InjOn D.point A.carrier := by
  classical
  intro p hp q hq he
  have hOld : p.2 = q.2 := funext (fun i => by
    simpa only [point,Fin.append_right] using
      congrArg (fun z : Mixed M n (1+r) => z.2 (Fin.natAdd 1 i)) he)
  have hTag : branchTag (M := M) (D.core p) = branchTag (M := M) (D.core q) := by
    simpa only [point,Fin.append_left] using
      congrArg (fun z : Mixed M n (1+r) => z.2 (Fin.castAdd r 0)) he
  have hCore : D.core p = D.core q := branchTag_injective h00 hTag
  have hOther (i : Fin n) (hi : i ≠ D.coordinate) : p.1 i = q.1 i := by
    simpa only [point,Function.update_of_ne hi] using congrArg (fun z : Mixed M n (1+r) => z.1 i) he
  have hFocus := D.extendedFocus_same_other hp hq hOld hOther
  have hEnd := D.extendedEndpoint_same_other hp hq hOld hOther
  have hJ := congrArg (fun z : Mixed M n (1+r) => z.1 D.coordinate) he
  simp only [point,Function.update_self] at hJ
  rw [hFocus,hEnd,hCore] at hJ
  have hJ' : p.1 D.coordinate = q.1 D.coordinate := by
    have hsub := add_right_cancel hJ
    calc
      p.1 D.coordinate = (p.1 D.coordinate - D.extendedFocus q) + D.extendedFocus q := (sub_add_cancel _ _).symm
      _ = (q.1 D.coordinate - D.extendedFocus q) + D.extendedFocus q := congrArg (fun x => x + D.extendedFocus q) hsub
      _ = q.1 D.coordinate := sub_add_cancel _ _
  apply Prod.ext _ hOld
  funext i
  by_cases hi : i = D.coordinate
  · exact hi ▸ hJ'
  · exact hOther i hi

end RelativeApertureData

end DiamondIntegral.Section6
