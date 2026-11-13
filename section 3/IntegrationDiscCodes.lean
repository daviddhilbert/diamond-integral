import «section 3».IntegrationBallShapes
import IntegrationSection3ACVF.BallKindGeometry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Definable full ball codes for finite-radius disc presentations. The code is auxiliary and is never added to the ground parameter base. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationDiscCode (closed : Bool) (z : Fin 2 → M) : Fin 5 → M :=
  ![z 0,z 1,if closed then iVFOne else iVFZero,
    if closed then iVFZero else iVFOne,iVFZero]

theorem integrationDiscCode_compatible (closed : Bool) (a r : Section2.VF M) (hr : r ≠ 0) :
    ∃ h : integrationDiscCode closed ![a.val,r.val] ∈ ParameterPresentation.codeDomain,
      ParameterPresentation.decode ⟨integrationDiscCode closed ![a.val,r.val],h⟩ =
        Sum.inl (if closed then Section2.closedDiscCode a (Section2.vfValue r)
          else Section2.openDiscCode a (Section2.finiteValue r hr)) := by
  have hone : iVFOne (M := M) ≠ iVFZero :=
    fun he => (one_ne_zero : (1 : Section2.VF M) ≠ 0) (Subtype.ext he)
  cases closed with
  | false =>
    let q : OpenBallCodes.Code M := ⟨![a.val,r.val],⟨by
      intro j; fin_cases j; exact a.property; exact r.property,
      fun he => hr (Subtype.ext he)⟩⟩
    let c := ParameterPresentation.encodeBall (BallPresentation.encodeOpen q)
    have hc : c.val = integrationDiscCode false ![a.val,r.val] := rfl
    have hb : BallImaginaries.ofOpen (Quotient.mk _ q) =
        Section2.openDiscCode a (Section2.finiteValue r hr) := by
      apply BallImaginaries.underlying_injective
      exact (BallKindGeometry.open_raw_gammaBall q (Section2.finiteValue r hr) rfl).trans
        (integrationOpenDisc_gammaBall a (Section2.finiteValue r hr)).symm
    refine ⟨hc ▸ c.property,?_⟩
    change ParameterPresentation.decode ⟨_,_⟩ = Sum.inl _
    have hd := (ParameterPresentation.decode_encodeBall (BallPresentation.encodeOpen q)).trans
      (congrArg Sum.inl (BallPresentation.decode_encodeOpen q))
    exact hd.trans (congrArg Sum.inl hb)
  | true =>
    let q : ClosedBallCodes.Code M := ⟨![a.val,r.val,iVFOne],by
      intro j; fin_cases j; exact a.property; exact r.property; exact (1 : Section2.VF M).property⟩
    let c := ParameterPresentation.encodeBall (BallPresentation.encodeClosed q)
    have hc : c.val = integrationDiscCode true ![a.val,r.val] := rfl
    have hb : BallImaginaries.ofClosed (Quotient.mk _ q) =
        Section2.closedDiscCode a (Section2.vfValue r) := by
      apply BallImaginaries.underlying_injective
      exact (BallKindGeometry.closed_raw_gammaBall q hone (Section2.finiteValue r hr) rfl).trans
        (integrationClosedDisc_gammaBall a (Section2.finiteValue r hr)).symm
    refine ⟨hc ▸ c.property,?_⟩
    have hd := (ParameterPresentation.decode_encodeBall (BallPresentation.encodeClosed q)).trans
      (congrArg Sum.inl (BallPresentation.decode_encodeClosed q))
    exact hd.trans (congrArg Sum.inl hb)

theorem integrationDiscCode_definable (S : Set M) (closed : Bool) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin 2) (Fin 5) S
      (integrationDiscCode closed) := by
  have he := AdjoinGamma.embedCode_definable (M := M) S
  let E := integrationDiscCode (M := M) closed
  letI := CanonicalStructure.normalize (M := M)
  have hzero : S.DefinableFun LRV (fun _ : Fin 2 → M => @iVFZero M sM) :=
    (he 1).comp (g := fun z : Fin 2 → M => fun _ : Fin 1 => z 0) (fun _ => Set.DefinableFun.proj LRV (i := (0 : Fin 2)))
  have hone : S.DefinableFun LRV (fun _ : Fin 2 → M => @iVFOne M sM) :=
    (he 4).comp (g := fun z : Fin 2 → M => fun _ : Fin 1 => z 0) (fun _ => Set.DefinableFun.proj LRV (i := (0 : Fin 2)))
  intro j
  fin_cases j
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · cases closed
    · exact hzero
    · exact hone
  · cases closed
    · exact hone
    · exact hzero
  · exact hzero
end DiamondIntegral.Section3
