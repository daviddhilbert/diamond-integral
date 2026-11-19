import «section 6».RelativeApertureChains

/-! Relative aperture data restricted to its active labels.

The active part `focusActive A U` of a set is its restriction to the labels in
`U`. It is proper invariant when `A` is, because each fibre is either a fibre
of `A` or empty. Section 6's relative aperture data restrict to the active part,
with every label active, and the restricted point map agrees with the original
one there (`restrictActive_point`). On the inactive part the point map only
adds the tag `rv(1)` (`point_inactive`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.RelativeRestrict
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

omit hM in
theorem vfFibre_focusActive (A : DefSet (rawMixedSpace (M := M) n r) S) (U : DefSet (rawRVSpace (M := M) r) S)
    {u : Fin r → RVInfinity M} (hu : u ∈ U.carrier) :
    vfFibre (focusActive A U).carrier u = vfFibre A.carrier u := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, hu⟩⟩

/-- The active part of a proper invariant set is proper invariant. -/
theorem properInvariant_focusActive (A : DefSet (rawMixedSpace (M := M) n r) S) (U : DefSet (rawRVSpace (M := M) r) S)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S (focusActive A U).carrier where
  definable := (focusActive A U).definable
  vfBounded := hA.vfBounded.mono (fun _ h => h.1)
  rvBounded := hA.rvBounded.mono (fun _ h => h.1)
  radii := by
    intro t
    obtain ⟨α, hα, hinv⟩ := hA.radii t
    refine ⟨α, hα, ?_⟩
    by_cases ht : t ∈ U.carrier
    · rw [vfFibre_focusActive A U ht]
      exact hinv
    · have he : vfFibre (focusActive A U).carrier t = ∅ :=
        Set.eq_empty_of_forall_notMem (fun x hx => ht hx.2)
      rw [he]
      intro a b _
      simp only [Set.mem_empty_iff_false]

namespace RelativeApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S} (R : DiamondIntegral.Section6.RelativeApertureData (G := G) A)

theorem focusActive_sub :
    (focusActive (focusActive A R.activeTags) R.activeTags).carrier ⊆ (focusActive A R.activeTags).carrier :=
  fun _ h => h.1

/-- The data restricted to the active labels; every label is active. -/
def restrictActive : DiamondIntegral.Section6.RelativeApertureData (G := G) (focusActive A R.activeTags) where
  coordinate := R.coordinate
  activeTags := R.activeTags
  focus := R.focus
  focusMap := R.focusMap.comp (Map.inclusion (focusActive_sub R))
  focusMap_eq := fun p => R.focusMap_eq ⟨p.val, p.property.1⟩
  sourceProper := properInvariant_focusActive A R.activeTags R.sourceProper
  sourceDoublyBounded := by
    obtain ⟨γ, hγ⟩ := R.sourceDoublyBounded
    exact ⟨γ, fun p hp => hγ p hp.1⟩
  tagged := fun p hp q hq => R.tagged p hp.1 q hq.1
  continuous := fun u hu => (R.continuous u hu).mono (fun _ h => h.1)
  focusRV := fun p hp hu => R.focusRV p hp.1 hu
  endpoint := R.endpoint
  endpointMap := R.endpointMap.comp (Map.inclusion (focusActive_sub R))
  endpointMap_eq := fun p => R.endpointMap_eq ⟨p.val, p.property.1⟩
  endpoint_continuous := fun u hu => (R.endpoint_continuous u hu).mono (fun _ h => h.1)
  endpoint_nonzero := fun p => R.endpoint_nonzero ⟨p.val, p.property.1⟩
  endpoint_nonnegative := fun p => R.endpoint_nonnegative ⟨p.val, p.property.1⟩
  endpoint_RV_constant := fun p q he => R.endpoint_RV_constant ⟨p.val, p.property.1⟩ ⟨q.val, q.property.1⟩ he
  apertureBound := R.apertureBound
  apertureBound_nonnegative := R.apertureBound_nonnegative
  apertureBound_named := R.apertureBound_named
  endpoint_upper_bound := fun p => R.endpoint_upper_bound ⟨p.val, p.property.1⟩
  covariance := fun u hu => by
    rw [vfFibre_focusActive A R.activeTags hu]
    exact R.covariance u hu

theorem restrictActive_all : ∀ p ∈ (focusActive A R.activeTags).carrier, p.2 ∈ (restrictActive R).activeTags.carrier :=
  fun _ hp => hp.2

theorem restrictActive_extendedFocus {p : Mixed M n r} (hp : p ∈ (focusActive A R.activeTags).carrier) :
    (restrictActive R).extendedFocus p = R.extendedFocus p := by
  rw [(restrictActive R).extendedFocus_active hp hp.2, R.extendedFocus_active hp.1 hp.2]
  rfl

theorem restrictActive_extendedEndpoint {p : Mixed M n r} (hp : p ∈ (focusActive A R.activeTags).carrier) :
    (restrictActive R).extendedEndpoint p = R.extendedEndpoint p := by
  rw [(restrictActive R).extendedEndpoint_active hp hp.2, R.extendedEndpoint_active hp.1 hp.2]
  rfl

theorem restrictActive_point {p : Mixed M n r} (hp : p ∈ (focusActive A R.activeTags).carrier) :
    (restrictActive R).point p = R.point p := by
  have h1 := restrictActive_extendedFocus R hp
  have h2 := restrictActive_extendedEndpoint R hp
  have hc : (restrictActive R).core p = R.core p := by
    unfold DiamondIntegral.Section6.RelativeApertureData.core
    rw [h1, h2]
    rfl
  unfold DiamondIntegral.Section6.RelativeApertureData.point
  rw [h1, h2, hc]
  rfl

/-- On an inactive label the point map only adds the tag `rv(1)`. -/
theorem point_inactive {p : Mixed M n r} (hu : p.2 ∉ R.activeTags.carrier) :
    R.point p = (p.1, Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2) := by
  have h1 := R.extendedFocus_inactive hu
  have h2 := R.extendedEndpoint_inactive hu
  have hc : R.core p = false := by
    unfold DiamondIntegral.Section6.RelativeApertureData.core
    rw [h1, h2]
    apply decide_eq_false
    intro hlt
    rw [(vfValue_eq_infinity_iff (0 : VF M)).mpr rfl] at hlt
    exact absurd (Values.le_infinity _) (not_le.mpr hlt)
  unfold DiamondIntegral.Section6.RelativeApertureData.point
  rw [h1, h2, hc]
  simp

end RelativeApertureData

end DiamondIntegral.Section7.RelativeRestrict
