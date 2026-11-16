import «section 6».CarriedCoordinateRadii

/-! A permitted lower-dimensional centripetal component lifts to an
actual RV-coordinate bundle. It carries the released coordinate along,
retaining the old focus, coefficient and aperture-dominated radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def bundleFocusProjection
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (U : DefSet (rawRVSpace (M := M) r) S) :
    Map (focusActive (rvCoordinateBundle A k) U) (focusActive A U) :=
  (vfDropLast (focusActive (rvCoordinateBundle A k) U)).corestrict
    (fun p => ⟨p.property.1.1,p.property.2⟩)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def carryCoordinate (D : CentripetalData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier) :
    CentripetalData (G := G) (rvCoordinateBundle A k) where
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
  coefficient := D.coefficient
  coefficient_nonzero := D.coefficient_nonzero
  coefficient_nonnegative := D.coefficient_nonnegative
  coefficient_definable := D.coefficient_definable
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

theorem exists_carried_centripetal_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A) (k : Fin r) :
    Nonempty (CentripetalData (G := G) (rvCoordinateBundle A k)) :=
  ⟨D.carryCoordinate k (rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k D.sourceProper)⟩

end CentripetalData
end DiamondIntegral.Section6
