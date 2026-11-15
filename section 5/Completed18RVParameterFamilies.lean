import «section 5».NativeMixedCodeRealization
import IntegrationSection6.GammaTuplePromotion
import IntegrationSection5.GammaGraphOperations
import IntegrationSection4.RVLabelSlices

/-! Finite RV parameters become free old RV label coordinates over the
original generated base, before cell preparation is applied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_point_code_preimage {B : Base (M := M)} {n m : ℕ}
    (D : Set (Fin (n+m) → M)) (hD : DefinableOverBase B (gammaPointSort n m) D) :
    GammaSetDefinable B {p : Point (M := M) n m | gammaPointCode p ∈ D} := by
  change DefinableOverBase B (gammaPointSort n m) _
  convert hD using 1
  ext w
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hw
    let p : Point (M := M) n m := nativeMixedPointOfCode w (hD.proper w hw)
    have hc : gammaPointCode p = w := nativeMixedPointOfCode_code w (hD.proper w hw)
    refine ⟨p,?_,hc⟩
    change gammaPointCode p ∈ D
    rw [hc]
    exact hw

def rvParameterFamilyIndex (n m r : ℕ) : Fin (r+(n+m)) → Fin (n+(r+m)) :=
  Fin.addCases (fun i => Fin.natAdd n (Fin.castAdd m i))
    (Fin.addCases (fun i => Fin.castAdd (r+m) i) (fun i => Fin.natAdd n (Fin.natAdd r i)))

theorem rv_parameter_family {B : Base (M := M)} {n m r : ℕ}
    (z : Fin r → RV (M := M)) (U : Set (Point (M := M) n m))
    (hU : GammaSetDefinable (RVLabelSlices.labelBase B z) U) :
    ∃ A : Set (Point (M := M) n (r+m)),GammaSetDefinable B A ∧
      ∀ p : Point (M := M) n m,(p.1,Fin.append z p.2) ∈ A ↔ p ∈ U := by
  let z' : Fin r → M := fun i => (z i).val
  obtain ⟨P,hP,hPz⟩ := gamma_tuple_parameter_promotion B (fun _ : Fin r => .rv)
    (gammaPointSort n m) z' (fun i => (z i).property) (gammaPointCode '' U) hU
  let D := {w : Fin (r+(n+m)) → M |
    ((fun i => w (Fin.castAdd (n+m) i)),fun j => w (Fin.natAdd r j)) ∈ P}
  let E : Set (Fin (n+(r+m)) → M) :=
    {w | w ∘ rvParameterFamilyIndex n m r ∈ D ∧ w ∈ sortedUniverse (gammaPointSort n (r+m))}
  have hE : DefinableOverBase B (gammaPointSort n (r+m)) E :=
    hP.preimage_real _ (rvParameterFamilyIndex n m r)
  let A : Set (Point (M := M) n (r+m)) := {p | gammaPointCode p ∈ E}
  refine ⟨A,gamma_point_code_preimage E hE,?_⟩
  intro p
  have hcode : gammaPointCode (p.1,Fin.append z p.2) ∘ rvParameterFamilyIndex n m r =
      Fin.append z' (gammaPointCode p) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,rvParameterFamilyIndex,Fin.addCases_left,
        gammaPointCode,Fin.append_right,Fin.append_left,z']
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp only [Function.comp_apply,rvParameterFamilyIndex,Fin.addCases_right,Fin.addCases_left,
          gammaPointCode,Fin.append_right,Fin.append_left,vfAt]
  have hsorted : gammaPointCode (p.1,Fin.append z p.2) ∈ sortedUniverse (gammaPointSort n (r+m)) :=
    nativeMixedCode_proper (p.1,Fin.append z p.2)
  change (_ ∈ D ∧ _) ↔ _
  rw [hcode,and_iff_left hsorted]
  simp only [D,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]
  have hh := Set.ext_iff.mp hPz (gammaPointCode p)
  exact hh.trans ⟨by rintro ⟨q,hq,hqp⟩; exact gammaPointCode_injective hqp ▸ hq,
    fun hp => ⟨p,hp,rfl⟩⟩

end DiamondIntegral.Section5
