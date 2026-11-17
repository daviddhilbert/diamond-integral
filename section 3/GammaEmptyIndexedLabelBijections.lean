import «section 3».GammaEmptyParameterMeasuredValues
import «section 3».GammaMeasuredIndexedWeights

/-! The zero-degree index adds no actual RV labels. Projection to the
row labels is an original-ground definable bijection, supplying the
literal object comparison at the end of contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}
variable (F : GammaMeasuredRVSchema hc B 0 a (k+1) (fun _ => .rv))
variable (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hD : ∀ r, r ∈ F.object.rowDomain Fin.elim0 ↔ r ∈ D.carrier)
variable (P : F.object.IndexedPresentation (gammaEmptyParameterIndex B))

def gammaEmptyIndexedLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) D :=
  (gammaGroundRVSelectCoordinates (Fin.natAdd 0)
    (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))).corestrict (by
      intro u
      have h := (F.indexed_mem (gammaEmptyParameterIndex B) P u).2
      change indexedRight u.val ∈ F.object.rowDomain (rvValues (indexedLeft u.val)) at h
      have he : rvValues (indexedLeft u.val) = Fin.elim0 := Subsingleton.elim _ _
      rw [he] at h
      exact (hD (indexedRight u.val)).mp h)

theorem gammaEmptyIndexedLabels_bijective : Function.Bijective (gammaEmptyIndexedLabels F D hD P) := by
  constructor
  · intro u v he
    have hr := congrArg Subtype.val he
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin a => ?_) i
    exact congrFun hr j
  · intro d
    let x := Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) d.val
    have hx : x ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)).carrier := by
      rw [F.indexed_domain_eq (gammaEmptyParameterIndex B) P]
      have hr : indexedRight x = d.val := by
        funext j
        exact Fin.append_right (Fin.elim0 : Fin 0 → RV (M := M)) d.val j
      have he : rvValues (indexedLeft x) = Fin.elim0 := Subsingleton.elim _ _
      refine ⟨Set.mem_univ _,?_⟩
      change indexedRight x ∈ F.object.rowDomain (rvValues (indexedLeft x))
      rw [he,hr]
      exact (hD d.val).mpr d.property
    refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
    funext j
    exact Fin.append_right (Fin.elim0 : Fin 0 → RV (M := M)) d.val j

def gammaEmptyIndexedLabelBijection :
    GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) D :=
  ⟨gammaEmptyIndexedLabels F D hD P,gammaEmptyIndexedLabels_bijective F D hD P⟩

end DiamondIntegral.Section3
