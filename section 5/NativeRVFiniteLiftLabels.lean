import «section 3».GammaGroundLifting
import «section 3».GammaGroundFiniteFibreInvariance
import «section 3».GammaGroundFiniteVFObjects

/-! Finiteness of a total RV label map follows from finite RV fibres of
its actual VF lift. Surjective RV lifting is used only in the proof;
no representatives are added as parameters or as new VF coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}

def nativeRVLabelLift (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k))) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) k a) where
  carrier := {q | ∃ u : D, u.val = q.2 ∧ (p u).val = Section2.tupleRV M q.1}
  definable := p.graph_definable.preimage (universalLiftGraphMap B.real k a)

theorem nativeRVLabelLift_finite_fibres
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)))
    (hf : p.FiniteFibres) (x : Fin k → Section2.VF M) :
    {r | (x,r) ∈ (nativeRVLabelLift D p).carrier}.Finite := by
  let y : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k) := ⟨Section2.tupleRV M x,Set.mem_univ _⟩
  apply ((hf y).image (fun u : D => u.val)).subset
  rintro r ⟨u,hu,hp⟩
  exact ⟨u,Subtype.ext hp,hu⟩

theorem finite_native_RV_labels_of_finite_lift
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)))
    (hf : ∀ x : Fin k → Section2.VF M, {r | (x,r) ∈ (nativeRVLabelLift D p).carrier}.Finite) :
    p.FiniteFibres := by
  intro y
  obtain ⟨x,hx⟩ := Section2.tupleRV_surjective y.val
  apply (hf x).of_injOn (f := fun u : D => u.val)
  · intro u hu
    exact ⟨u,rfl,(congrArg Subtype.val hu).trans hx.symm⟩
  · intro u hu v hv he
    exact Subtype.ext he

theorem native_RV_finite_labels_iff_finite_lift
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k))) :
    p.FiniteFibres ↔ ∀ x : Fin k → Section2.VF M, {r | (x,r) ∈ (nativeRVLabelLift D p).carrier}.Finite :=
  ⟨nativeRVLabelLift_finite_fibres D p,finite_native_RV_labels_of_finite_lift D p⟩

def nativeRVObjectOfFiniteLift
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)))
    (hf : ∀ x : Fin k → Section2.VF M, {r | (x,r) ∈ (nativeRVLabelLift D p).carrier}.Finite)
    (hnz : ∀ u : D, ∀ i, ((p u).val i).val ≠ iRVZero) : GammaGroundRVObject hc B k :=
  ⟨a,D,p,finite_native_RV_labels_of_finite_lift D p hf,hnz⟩

theorem nativeRVObjectOfFiniteLift_lift
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)))
    (hf : ∀ x : Fin k → Section2.VF M, {r | (x,r) ∈ (nativeRVLabelLift D p).carrier}.Finite)
    (hnz : ∀ u : D, ∀ i, ((p u).val i).val ≠ iRVZero) :
    gammaGroundObjectLift (nativeRVObjectOfFiniteLift D p hf hnz) = nativeRVLabelLift D p := rfl

def nativeRVObjectOfLiftBijection
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (p : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)))
    (A : GammaGroundFiniteVFObject hc B) (e : GammaGroundBijection A.domain (nativeRVLabelLift D p))
    (hnz : ∀ u : D, ∀ i, ((p u).val i).val ≠ iRVZero) : GammaGroundRVObject hc B k :=
  nativeRVObjectOfFiniteLift D p ((gammaGroundFiniteRVFibres_iff e hκ hs h00 hr).mp A.finite) hnz

end DiamondIntegral.Section5
