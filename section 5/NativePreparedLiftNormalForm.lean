import «section 5».NativeVFLiftFamilies
import «section 5».NativeVFBaseTransport

/-! Exact domains of actual prepared VF lift totals. The original VF base
is recovered by the actual inverse preparation map; old RV parameters,
fibre RV labels and fibre VF coordinates remain literal coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q a k l : ℕ}

theorem nativePreparedLiftNormalForm
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ x : nativeVFLiftFamily Z F,
      ((nativeMixedCoordinateMap (nativeVFLiftFamily Z F) (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin (q+a))) x).val ∈ P.carrier)
    (c : C) (v : Fin q → CanonicalRV.RVSort M) (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) :
    (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) ∈
      (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier ↔
      ((T.symm.map c).val.1,v) ∈ Z.carrier ∧
        Fin.append (Fin.append (nativeMixedCode ((T.symm.map c).val.1,v)) (rvValues u))
          (rvValues (Section2.tupleRV M y)) ∈ F.volume := by
  constructor
  · rintro ⟨x,hx⟩
    let b := (nativeVFBaseParameterMap (nativeVFLiftFamily Z F) P hP) x
    let d := T.map b
    have hx' : ((nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP) x).val =
        (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) := hx
    have hpack : (Fin.append d.val.1 (x.val.1 ∘ Fin.natAdd p),Fin.append d.val.2 x.val.2) =
        (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) :=
      (nativeVFPrepareBaseMap_value (nativeVFLiftFamily Z F) T hP x).symm.trans hx'
    have hdVF : d.val.1 = c.val.1 := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+(q+a)) => z.1 (Fin.castAdd k i)) hpack
      simpa only [Fin.append_left] using hi)
    have hdRV : d.val.2 = c.val.2 := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+(q+a)) => z.2 (Fin.castAdd (q+a) i)) hpack
      simpa only [Fin.append_left] using hi)
    have hd : d = c := Subtype.ext (Prod.ext hdVF hdRV)
    have hb : b = T.symm.map c := by
      apply T.bijective.1
      exact hd.trans (T.map.apply_inverse T.bijective c).symm
    have hprefix : x.val.1 ∘ Fin.castAdd k = (T.symm.map c).val.1 :=
      congrArg (fun z : P => z.val.1) hb
    have hfibre : x.val.1 ∘ Fin.natAdd p = y := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+(q+a)) => z.1 (Fin.natAdd p i)) hpack
      simpa only [Fin.append_right] using hi)
    have hRV : x.val.2 = Fin.append v u := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+(q+a)) => z.2 (Fin.natAdd l i)) hpack
      simpa only [Fin.append_right] using hi)
    have hxpack : x.val = (Fin.append (T.symm.map c).val.1 y,Fin.append v u) := by
      apply Prod.ext ?_ hRV
      exact Fin.append_castAdd_natAdd.symm.trans (congrArg₂ Fin.append hprefix hfibre)
    have hsource : x.val ∈ (nativeVFLiftFamily Z F).carrier := x.property
    rw [hxpack] at hsource
    exact (nativeVFLiftFamily_mem Z F (T.symm.map c).val.1 v y u).mp hsource
  · intro h
    let x : nativeVFLiftFamily Z F :=
      ⟨(Fin.append (T.symm.map c).val.1 y,Fin.append v u),
        (nativeVFLiftFamily_mem Z F (T.symm.map c).val.1 v y u).mpr h⟩
    have hb : (nativeVFBaseParameterMap (nativeVFLiftFamily Z F) P hP) x = T.symm.map c := by
      apply Subtype.ext
      apply Prod.ext ?_ (Subsingleton.elim _ _)
      exact funext (fun i => Fin.append_left _ _ i)
    refine ⟨x,?_⟩
    change ((nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP) x).val = _
    have hc' : T.map (T.symm.map c) = c := T.map.apply_inverse T.bijective c
    rw [nativeVFPrepareBaseMap_value,hb,hc']
    have hfibre : x.val.1 ∘ Fin.natAdd p = y := funext (fun i => Fin.append_right _ _ i)
    rw [hfibre]

end DiamondIntegral.Section5
