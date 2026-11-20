import «section 6».CarriedCentripetalData
import «section 6».RelativeApertureHomeomorphism
import «section 6».RVHeadStartGeometry

/-! Lemma 7.14, part 13: relative aperture data on head-start bundles.

For the head-start form of Lemma 7.13 (used in the comparison step of Lemma
7.14), a relative aperture step on a set `A` is carried to the RV-coordinate
bundle `rvCoordinateBundle A k`, whose last VF coordinate lifts the label `k`.
The carried data act on the same coordinate with the same focus and endpoint,
and leave the lifted coordinate unchanged (`carryBundle`). Its image is the
bundle of the image over the shifted label (`carryBundle_image`).
Iterating gives the head-start bundles (`carryHeadStart`,
`carryHeadStart_image`).

This follows Section 6's `CentripetalData.carryCoordinate`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.RelativeApertureData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

/-- **Relative aperture data carried to an RV-coordinate bundle.** -/
def carryBundle (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier) :
    RelativeApertureData (G := G) (rvCoordinateBundle A k) where
  coordinate := D.coordinate.castSucc
  activeTags := D.activeTags
  focus x u := D.focus (Fin.init x) u
  focusMap := D.focusMap.comp (bundleFocusProjection A k D.activeTags)
  focusMap_eq := by
    intro p
    change (D.focusMap (bundleFocusProjection A k D.activeTags p)).val 0 =
      D.focus (Fin.init (Function.update p.val.1 D.coordinate.castSucc 0)) p.val.2
    rw [init_update_castSucc]
    exact D.focusMap_eq (bundleFocusProjection A k D.activeTags p)
  sourceProper := hW
  sourceDoublyBounded := rvCoordinateBundle_doublyBounded A k D.sourceDoublyBounded D.sourceProper.rvBounded
  tagged := rvCoordinateBundle_tagged A k D.tagged
  continuous := by
    intro u hu
    have hinit : Continuous (Fin.init : (Fin (n+1) → VF M) → Fin n → VF M) :=
      continuous_pi (fun i => continuous_apply i.castSucc)
    have h := (D.continuous u hu).comp hinit.continuousOn
      (show Set.MapsTo Fin.init (vfFibre (rvCoordinateBundle A k).carrier u) (vfFibre A.carrier u) from
        fun _ hp => hp.1)
    convert h using 1
    funext x
    exact congrArg (fun a => D.focus a u) (init_update_castSucc x D.coordinate 0)
  focusRV := by
    intro p hp hu
    change rv M (D.focus (Fin.init (Function.update p.1 D.coordinate.castSucc 0)) p.2) =
      rv M (p.1 D.coordinate.castSucc)
    rw [init_update_castSucc]
    exact D.focusRV (Fin.init p.1,p.2) hp.1 hu
  endpoint x u := D.endpoint (Fin.init x) u
  endpointMap := D.endpointMap.comp (bundleFocusProjection A k D.activeTags)
  endpointMap_eq := by
    intro p
    change (D.endpointMap (bundleFocusProjection A k D.activeTags p)).val 0 =
      D.endpoint (Fin.init (Function.update p.val.1 D.coordinate.castSucc 0)) p.val.2
    rw [init_update_castSucc]
    exact D.endpointMap_eq (bundleFocusProjection A k D.activeTags p)
  endpoint_continuous := by
    intro u hu
    have hinit : Continuous (Fin.init : (Fin (n+1) → VF M) → Fin n → VF M) :=
      continuous_pi (fun i => continuous_apply i.castSucc)
    have h := (D.endpoint_continuous u hu).comp hinit.continuousOn
      (show Set.MapsTo Fin.init (vfFibre (rvCoordinateBundle A k).carrier u) (vfFibre A.carrier u) from
        fun _ hp => hp.1)
    convert h using 1
    funext x
    exact congrArg (fun a => D.endpoint a u) (init_update_castSucc x D.coordinate 0)
  endpoint_nonzero := by
    intro p
    change D.endpoint (Fin.init (Function.update p.val.1 D.coordinate.castSucc 0)) p.val.2 ≠ 0
    rw [init_update_castSucc]
    exact D.endpoint_nonzero (bundleFocusProjection A k D.activeTags p)
  endpoint_nonnegative := by
    intro p
    change vfValue (D.focus (Fin.init (Function.update p.val.1 D.coordinate.castSucc 0)) p.val.2) ≤
      vfValue (D.endpoint (Fin.init (Function.update p.val.1 D.coordinate.castSucc 0)) p.val.2)
    rw [init_update_castSucc]
    exact D.endpoint_nonnegative (bundleFocusProjection A k D.activeTags p)
  endpoint_RV_constant := by
    intro p q he
    exact D.endpoint_RV_constant (bundleFocusProjection A k D.activeTags p)
      (bundleFocusProjection A k D.activeTags q) he
  apertureBound := D.apertureBound
  apertureBound_nonnegative := D.apertureBound_nonnegative
  apertureBound_named := D.apertureBound_named
  endpoint_upper_bound := by
    intro p
    exact D.endpoint_upper_bound (bundleFocusProjection A k D.activeTags p)
  covariance := by
    intro u hu
    obtain ⟨α,β,hα,hβ,hInv,hCov,hDom⟩ := D.covariance u hu
    obtain ⟨ε,hε,hεInv⟩ := hW.radii u
    let β' : Fin (n+1) → Gamma M := Fin.snoc β (ε (Fin.last n))
    refine ⟨α,β',hα,?_,?_,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [β',Fin.snoc_last] using hε (Fin.last n)
      · simpa only [β',Fin.snoc_castSucc] using hβ j
    · have h := rvCoordinateBundle_invariant_preserving_old_radii A k u
        (fun i => if i = D.coordinate then α else β i) hInv ε hεInv
      simpa only [snoc_coordinate_radii,β'] using h
    · intro a ha b hb hab
      have hOld : Congruent β (Function.update (Fin.init a) D.coordinate 0)
          (Function.update (Fin.init b) D.coordinate 0) := by
        intro i
        have h := hab i.castSucc
        simpa only [β',Fin.snoc_castSucc,← init_update_castSucc,Fin.init] using h
      have h := hCov (Fin.init a) ha.1 (Fin.init b) hb.1 hOld
      simpa only [init_update_castSucc] using h
    · intro a ha
      have h := hDom (Fin.init a) ha.1
      simpa only [init_update_castSucc] using h

theorem carryBundle_extendedFocus (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryBundle k hW).extendedFocus p = D.extendedFocus (Fin.init p.1,p.2) := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · rw [(D.carryBundle k hW).extendedFocus_active hp hu,D.extendedFocus_active hp.1 hu]
    change D.focus (Fin.init (Function.update p.1 D.coordinate.castSucc 0)) p.2 =
      D.focus (Function.update (Fin.init p.1) D.coordinate 0) p.2
    rw [init_update_castSucc]
  · rw [(D.carryBundle k hW).extendedFocus_inactive hu,D.extendedFocus_inactive hu]

theorem carryBundle_extendedEndpoint (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryBundle k hW).extendedEndpoint p = D.extendedEndpoint (Fin.init p.1,p.2) := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · rw [(D.carryBundle k hW).extendedEndpoint_active hp hu,D.extendedEndpoint_active hp.1 hu]
    change D.endpoint (Fin.init (Function.update p.1 D.coordinate.castSucc 0)) p.2 =
      D.endpoint (Function.update (Fin.init p.1) D.coordinate 0) p.2
    rw [init_update_castSucc]
  · rw [(D.carryBundle k hW).extendedEndpoint_inactive hu,D.extendedEndpoint_inactive hu]

theorem carryBundle_core (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryBundle k hW).core p = D.core (Fin.init p.1,p.2) := by
  change decide (vfValue ((D.carryBundle k hW).extendedEndpoint p) <
      vfValue (p.1 D.coordinate.castSucc - (D.carryBundle k hW).extendedFocus p)) = _
  rw [D.carryBundle_extendedFocus k hW p hp,D.carryBundle_extendedEndpoint k hW p hp]
  rfl

theorem carryBundle_point (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryBundle k hW).point p =
      (Fin.snoc (D.point (Fin.init p.1,p.2)).1 (p.1 (Fin.last n)),(D.point (Fin.init p.1,p.2)).2) := by
  let E := D.carryBundle k hW
  have hFocus := D.carryBundle_extendedFocus k hW p hp
  have hEnd := D.carryBundle_extendedEndpoint k hW p hp
  have hCore := D.carryBundle_core k hW p hp
  have hInit : Fin.init (E.point p).1 = (D.point (Fin.init p.1,p.2)).1 := by
    change Fin.init (Function.update p.1 D.coordinate.castSucc
      (p.1 D.coordinate.castSucc - E.extendedFocus p +
        if E.core p then E.extendedEndpoint p else 0)) = _
    rw [init_update_castSucc,hFocus,hCore,hEnd]
    rfl
  have hLast : (E.point p).1 (Fin.last n) = p.1 (Fin.last n) := by
    change Function.update p.1 D.coordinate.castSucc _ (Fin.last n) = p.1 (Fin.last n)
    exact Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last D.coordinate)) _ _
  apply Prod.ext
  · calc
      (E.point p).1 = Fin.snoc (Fin.init (E.point p).1) ((E.point p).1 (Fin.last n)) :=
        (Fin.snoc_init_self _).symm
      _ = _ := by rw [hInit,hLast]
  · change Fin.append (fun _ : Fin 1 => branchTag (M := M) (E.core p)) p.2 =
      Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core (Fin.init p.1,p.2))) p.2
    rw [hCore]

/-- **The image of carried data** is the bundle of the image over the shifted
label. -/
theorem carryBundle_image (D : RelativeApertureData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier) :
    (D.carryBundle k hW).map.image.carrier =
      (rvCoordinateBundle D.map.image (Fin.natAdd 1 k)).carrier := by
  rw [(D.carryBundle k hW).image_carrier]
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [D.carryBundle_point k hW p hp]
    refine ⟨?_,?_⟩
    · change ((Fin.init (Fin.snoc (D.point (Fin.init p.1,p.2)).1 (p.1 (Fin.last n)) :
          Fin (n+1) → VF M), (D.point (Fin.init p.1,p.2)).2) : Mixed M n (1+r)) ∈ D.map.image.carrier
      rw [Fin.init_snoc,D.image_carrier]
      exact ⟨(Fin.init p.1,p.2),hp.1,rfl⟩
    · simpa only [Fin.snoc_last,point,Fin.append_right] using hp.2
  · intro hq
    obtain ⟨a,ha,hDa⟩ := (show (Fin.init q.1,q.2) ∈ D.point '' A.carrier by
      rw [← D.image_carrier]
      exact hq.1)
    let p : Mixed M (n+1) r := (Fin.snoc a.1 (q.1 (Fin.last n)),a.2)
    have hbase : ((Fin.init p.1,p.2) : Mixed M n r) = a := by
      apply Prod.ext
      · show Fin.init (Fin.snoc a.1 (q.1 (Fin.last n)) : Fin (n+1) → VF M) = a.1
        exact Fin.init_snoc _ _
      · rfl
    have htag : a.2 k = q.2 (Fin.natAdd 1 k) := by
      have h := congrArg (fun z : Mixed M n (1+r) => z.2 (Fin.natAdd 1 k)) hDa
      simpa only [point,Fin.append_right] using h
    have hp : p ∈ (rvCoordinateBundle A k).carrier := by
      refine ⟨?_,?_⟩
      · change (Fin.init p.1,p.2) ∈ A.carrier
        rw [hbase]
        exact ha
      · change rv M ((Fin.snoc a.1 (q.1 (Fin.last n)) : Fin (n+1) → VF M) (Fin.last n)) = a.2 k
        rw [Fin.snoc_last,htag]
        exact hq.2
    refine ⟨p,hp,?_⟩
    rw [D.carryBundle_point k hW p hp,hbase,hDa]
    apply Prod.ext
    · show Fin.snoc (Fin.init q.1) ((Fin.snoc a.1 (q.1 (Fin.last n)) : Fin (n+1) → VF M) (Fin.last n)) = q.1
      rw [Fin.snoc_last]
      exact Fin.snoc_init_self q.1
    · rfl

end DiamondIntegral.Section6.RelativeApertureData
