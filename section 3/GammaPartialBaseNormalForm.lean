import «section 5».NativeVFBaseTransport

/-! Exact full domains of partial VF-base preparation, with the original
inverse base point and all complementary VF and RV coordinates retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a k l : ℕ}
variable (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) a))
variable {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
variable (hP : ∀ x : A,
  ((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin a)) x).val ∈ P.carrier)

theorem gammaPartialBase_normalForm (c : C) (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) :
    (Fin.append c.val.1 y,Fin.append c.val.2 u) ∈ (nativeVFPrepareBaseMap A T hP).image.carrier ↔
      (Fin.append (T.symm.map c).val.1 y,u) ∈ A.carrier := by
  constructor
  · rintro ⟨x,hx⟩
    let b := (nativeVFBaseParameterMap A P hP) x
    let d := T.map b
    have hx' : ((nativeVFPrepareBaseMap A T hP) x).val =
        (Fin.append c.val.1 y,Fin.append c.val.2 (u)) := hx
    have hpack : (Fin.append d.val.1 (x.val.1 ∘ Fin.natAdd p),Fin.append d.val.2 x.val.2) =
        (Fin.append c.val.1 y,Fin.append c.val.2 (u)) :=
      (nativeVFPrepareBaseMap_value A T hP x).symm.trans hx'
    have hdVF : d.val.1 = c.val.1 := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.1 (Fin.castAdd k i)) hpack
      simpa only [Fin.append_left] using hi)
    have hdRV : d.val.2 = c.val.2 := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.2 (Fin.castAdd a i)) hpack
      simpa only [Fin.append_left] using hi)
    have hd : d = c := Subtype.ext (Prod.ext hdVF hdRV)
    have hb : b = T.symm.map c := by
      apply T.bijective.1
      exact hd.trans (T.map.apply_inverse T.bijective c).symm
    have hprefix : x.val.1 ∘ Fin.castAdd k = (T.symm.map c).val.1 :=
      congrArg (fun z : P => z.val.1) hb
    have hfibre : x.val.1 ∘ Fin.natAdd p = y := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.1 (Fin.natAdd p i)) hpack
      simpa only [Fin.append_right] using hi)
    have hRV : x.val.2 = u := funext (fun i => by
      have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.2 (Fin.natAdd l i)) hpack
      simpa only [Fin.append_right] using hi)
    have hxpack : x.val = (Fin.append (T.symm.map c).val.1 y,u) := by
      apply Prod.ext ?_ hRV
      exact Fin.append_castAdd_natAdd.symm.trans (congrArg₂ Fin.append hprefix hfibre)
    have hsource : x.val ∈ A.carrier := x.property
    rw [hxpack] at hsource
    exact hsource
  · intro h
    let x : A :=
      ⟨(Fin.append (T.symm.map c).val.1 y,u),
        h⟩
    have hb : (nativeVFBaseParameterMap A P hP) x = T.symm.map c := by
      apply Subtype.ext
      apply Prod.ext ?_ (Subsingleton.elim _ _)
      exact funext (fun i => Fin.append_left _ _ i)
    refine ⟨x,?_⟩
    change ((nativeVFPrepareBaseMap A T hP) x).val = _
    have hc' : T.map (T.symm.map c) = c := T.map.apply_inverse T.bijective c
    rw [nativeVFPrepareBaseMap_value,hb,hc']
    have hfibre : x.val.1 ∘ Fin.natAdd p = y := funext (fun i => Fin.append_right _ _ i)
    rw [hfibre]


theorem gammaPartialBase_base_mem
    (w : (nativeVFPrepareBaseMap A T hP).image) :
    (w.val.1 ∘ Fin.castAdd k,w.val.2 ∘ Fin.castAdd a) ∈ C.carrier := by
  obtain ⟨q,hq⟩ := w.property
  let d := T.map ((nativeVFBaseParameterMap A P hP) q)
  have he : (Fin.append d.val.1 (q.val.1 ∘ Fin.natAdd p),Fin.append d.val.2 q.val.2) = w.val :=
    (nativeVFPrepareBaseMap_value A T hP q).symm.trans hq
  have hh : (w.val.1 ∘ Fin.castAdd k,w.val.2 ∘ Fin.castAdd a) = d.val := by
    refine Prod.ext (funext (fun i => ?_)) (funext (fun i => ?_))
    · have h := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.1 (Fin.castAdd k i)) he
      simpa only [Function.comp_apply,Fin.append_left] using h.symm
    · have h := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.2 (Fin.castAdd a i)) he
      simpa only [Function.comp_apply,Fin.append_left] using h.symm
  exact hh.symm ▸ d.property

theorem gammaPartialBase_inverse_labels
    (q : (nativeVFPrepareBaseMap A T hP).image) :
    ((nativeVFPrepareBaseBijection A T hP).symm.map q).val.2 = q.val.2 ∘ Fin.natAdd l := by
  let E := nativeVFPrepareBaseBijection A T hP
  let u := E.symm.map q
  have h := congrArg Subtype.val (E.map.apply_inverse E.bijective q)
  have he : (Fin.append (T.map ((nativeVFBaseParameterMap A P hP) u)).val.1 (u.val.1 ∘ Fin.natAdd p),
      Fin.append (T.map ((nativeVFBaseParameterMap A P hP) u)).val.2 u.val.2) = q.val :=
    (nativeVFPrepareBaseMap_value A T hP u).symm.trans h
  funext i
  have hi := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.2 (Fin.natAdd l i)) he
  simpa only [Function.comp_apply,Fin.append_right] using hi


theorem gammaPartialBase_inverse_basepoint
    (q : (nativeVFPrepareBaseMap A T hP).image) :
    (T.symm.map ⟨(q.val.1 ∘ Fin.castAdd k,q.val.2 ∘ Fin.castAdd a),gammaPartialBase_base_mem A T hP q⟩).val.1 =
      ((nativeVFPrepareBaseBijection A T hP).symm.map q).val.1 ∘ Fin.castAdd k := by
  let E := nativeVFPrepareBaseBijection A T hP
  let u := E.symm.map q
  let b := (nativeVFBaseParameterMap A P hP) u
  let c : C := ⟨(q.val.1 ∘ Fin.castAdd k,q.val.2 ∘ Fin.castAdd a),gammaPartialBase_base_mem A T hP q⟩
  have h := congrArg Subtype.val (E.map.apply_inverse E.bijective q)
  have he : (Fin.append (T.map b).val.1 (u.val.1 ∘ Fin.natAdd p),Fin.append (T.map b).val.2 u.val.2) = q.val :=
    (nativeVFPrepareBaseMap_value A T hP u).symm.trans h
  have hc : T.map b = c := by
    apply Subtype.ext
    refine Prod.ext (funext (fun i => ?_)) (funext (fun i => ?_))
    · have h := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.1 (Fin.castAdd k i)) he
      simpa only [c,Function.comp_apply,Fin.append_left] using h
    · have h := congrArg (fun z : Section2.Mixed M (p+k) (l+a) => z.2 (Fin.castAdd a i)) he
      simpa only [c,Function.comp_apply,Fin.append_left] using h
  have hb : T.symm.map c = b := by
    rw [← hc]
    exact T.map.inverse_apply T.bijective b
  exact congrArg (fun z : P => z.val.1) hb

end DiamondIntegral.Section3
