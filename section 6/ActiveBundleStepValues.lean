import «section 6».UnaryApertureFocusTransport
import «section 6».CarriedUnaryHomeLifts
import «section 6».CorePullbacks

/-! Scalar clauses of an active-coordinate step on a full RV-disc
bundle, including its actual polydisc-dependent focus and boundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def rvCoordinateBundlePoint (B : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (b : Fin n → VF M) (u : Fin r → RVInfinity M) (x : VF M)
    (hb : (b,u) ∈ B.carrier) (hx : rv M x=u k) : rvCoordinateBundle B k :=
  ⟨(Fin.snoc b x,u),by
    change (Fin.init (Fin.snoc b x : Fin (n+1) → VF M),u) ∈ B.carrier ∧
      rv M ((Fin.snoc b x : Fin (n+1) → VF M) (Fin.last n))=u k
    simpa only [Fin.init_snoc,Fin.snoc_last] using And.intro hb hx⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n r) S} {k : Fin r}

theorem activeBundle_focus_rv (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle B k) (hu : p.val.2 ∈ D.activeTags.carrier) :
    rv M (D.extendedFocus p.val)=p.val.2 k := by
  rw [D.extendedFocus_active p.property hu]
  have h := D.focusRV p.val p.property hu
  rw [hCoord] at h
  simpa only [hCoord] using h.trans p.property.2

theorem activeBundle_core (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle B k) :
    D.core p.val=unaryApertureCore (D.extendedFocus p.val) (D.coefficient*D.extendedFocus p.val) (p.val.1 (Fin.last n)) := by
  unfold CentripetalData.core unaryApertureCore
  rw [hCoord]

theorem activeBundle_point_last (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle B k) :
    (D.point p.val).1 (Fin.last n)=
      unaryApertureValue (D.extendedFocus p.val) (D.coefficient*D.extendedFocus p.val) (p.val.1 (Fin.last n)) := by
  simp only [CentripetalData.point,hCoord,Function.update_self,unaryApertureValue,activeBundle_core D hCoord p]

theorem activeBundle_point_base (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle B k) :
    Fin.init (D.point p.val).1=Fin.init p.val.1 := by
  funext i
  simp only [CentripetalData.point,hCoord,Fin.init,Function.update_of_ne (Fin.castSucc_ne_last i)]

theorem activeBundle_boundary_ge (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (p : rvCoordinateBundle B k) : vfValue (D.extendedFocus p.val) ≤ vfValue (D.coefficient*D.extendedFocus p.val) := by
  change Values.vfValueHom (D.extendedFocus p.val) ≤ Values.vfValueHom (D.coefficient*D.extendedFocus p.val)
  simp only [map_mul,valueHom_eq_value]
  simpa only [one_mul] using mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue (D.extendedFocus p.val)))

theorem activeBundle_step_value (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (p : rvCoordinateBundle B k) : (centripetalStepMap D p).val=regularize (D.point p.val) := rfl

end DiamondIntegral.Section6
