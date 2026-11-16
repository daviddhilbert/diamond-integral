import «section 6».RVGoodCoordinatePivots

/-! Constructed measured forms on actual good coordinate pivots. Their
Gamma quotient exactly retains the original total RV weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def measuredGoodReplacementObject (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (n+1)} (F : RVHom U.object V.object) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    MeasuredRVObject (M := M) S (n+1) where
  object := rvGoodReplacementObject F j E
  finiteVolume := rvGoodReplacementMap_finite F j E U.finiteVolume hObs
  nonzero := rvGoodReplacementObject_nonzero F j E U.nonzero V.nonzero
  form := gammaMapDiv hc
    (gammaMapMul hc (U.form.restrict (rvGoodReplacementDomain_subset F j E))
      (rvVolumeGammaMap hc (U.object.restrict (rvGoodReplacementDomain F j E) (rvGoodReplacementDomain_subset F j E))))
    (rvVolumeGammaMap hc (rvGoodReplacementObject F j E))

theorem measuredGoodReplacementObject_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (n+1)} (F : RVHom U.object V.object) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite)
    (u : (rvGoodReplacementDomain F j E)) :
    (measuredGoodReplacementObject hc F j E hObs).totalWeight u =
      (U.restrict (rvGoodReplacementDomain F j E) (rvGoodReplacementDomain_subset F j E)).totalWeight u := by
  let A := U.restrict (rvGoodReplacementDomain F j E) (rvGoodReplacementDomain_subset F j E)
  let W := measuredGoodReplacementObject hc F j E hObs
  change ((gammaMapValue A.form u * gammaMapValue (rvVolumeGammaMap hc A.object) u) /
    gammaMapValue (rvVolumeGammaMap hc W.object) u) * W.volumeGamma u = A.totalWeight u
  rw [rvVolumeGammaMap_value hc A.object A.nonzero,rvVolumeGammaMap_value hc W.object W.nonzero]
  change (A.totalWeight u / W.volumeGamma u) * W.volumeGamma u = A.totalWeight u
  exact div_mul_cancel _ _

def measuredGoodPivotIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (n+1)} (F : RVHom U.object V.object) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    MeasuredRVIso (U.restrict (rvGoodReplacementDomain F j E) (rvGoodReplacementDomain_subset F j E))
      (measuredGoodReplacementObject hc F j E hObs) where
  iso := rvGoodPivotIso F j E U.finiteVolume U.nonzero V.nonzero hObs
  balance u := (measuredGoodReplacementObject_totalWeight hc F j E hObs u).symm

theorem measuredGoodPivotIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (n+1)} (F : RVHom U.object V.object) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    RVUnaryRelativeAt (measuredGoodPivotIso hc F j E hObs).iso.hom.map (Fin.last n) :=
  rvGoodPivotIso_unary F j E U.finiteVolume U.nonzero V.nonzero hObs

end DiamondIntegral.Section6
