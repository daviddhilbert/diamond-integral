import «section 3».GammaEmptyParameterMeasuredValues
import «section 3».GammaSelectedMeasuredOrderedTraces

/-! Finite generic Gamma row proofs have actual principal-quotient
values at the end of contraction. The empty parameter tuple is generic,
so the saved ordered induction now gives equality of these RV values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)

def GammaSelectedRetainedData.finalObject (U : GammaSelectedRetainedData hc B 0 (k+1)) :
    GammaGroundMeasuredRVObject hc B ((0+k)+1) := by
  let N := (U.uniform_bound hκ hs hr hg).choose
  have hN := (U.uniform_bound hκ hs hr hg).choose_spec
  exact (U.schema N).essential.emptyParameterObject (by
    have he : vfValues (Fin.elim0 : Fin 0 → VF (M := M)) = Fin.elim0 := Subsingleton.elim _ _
    exact he ▸ (U.schema N).essential_valid _ (hN Fin.elim0))

def GammaSelectedRetainedData.finalValue (U : GammaSelectedRetainedData hc B 0 (k+1)) :=
  gammaMeasuredPrincipalValue (U.finalObject hκ hs hr hg)

theorem GammaGenericSelectedRelated.finalValue_eq
    (h00 : M ⊨ Axioms.ACVF00)
    {U V : GammaSelectedRetainedData hc B 0 (k+1)} (h : GammaGenericSelectedRelated U V) :
    U.finalValue hκ hs hr hg = V.finalValue hκ hs hr hg := by
  obtain ⟨N,L,hN,hL,hH⟩ := h
  let NU := (U.uniform_bound hκ hs hr hg).choose
  let NV := (V.uniform_bound hκ hs hr hg).choose
  have hU := (U.uniform_bound hκ hs hr hg).choose_spec
  have hV := (V.uniform_bound hκ hs hr hg).choose_spec
  obtain ⟨H,hValid⟩ := hH Fin.elim0 algebraicIndependent_empty_type
  let K := GammaMeasuredRelationSchema.trans (U.schema N).essential
    (.agreement (U.schema NU).essential (U.schema N).essential)
    (.trans (V.schema L).essential H (.agreement (V.schema L).essential (V.schema NV).essential))
  have hK : K.valid (vfValues (Fin.elim0 : Fin 0 → VF (M := M))) :=
    ⟨⟨(U.schema NU).essential_valid _ (hU Fin.elim0),(U.schema N).essential_valid _ (hN Fin.elim0),
      U.schema_sameRow NU N Fin.elim0⟩,
      hValid,⟨(V.schema L).essential_valid _ (hL Fin.elim0),(V.schema NV).essential_valid _ (hV Fin.elim0),
        V.schema_sameRow L NV Fin.elim0⟩⟩
  have he : vfValues (Fin.elim0 : Fin 0 → VF (M := M)) = Fin.elim0 := Subsingleton.elim _ _
  have hKU := (U.schema NU).essential_valid _ (hU Fin.elim0)
  have hKV := (V.schema NV).essential_valid _ (hV Fin.elim0)
  have result := K.emptyParameter_sound hκ hs h00 hr hg (he ▸ hKU) (he ▸ hKV) (he ▸ hK)
  exact result

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem GammaSelectedMeasuredOrderedTrace.finalValue_eq
    (hunc : Cardinal.aleph0 < κ) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n j l : ℕ} {U V : GammaSelectedRetainedData hc B n (j+1)}
    {A D : GammaSelectedRetainedData hc B 0 (l+1)}
    (T : GammaSelectedMeasuredOrderedTrace hκ hs hr U A)
    (E : GammaSelectedMeasuredOrderedTrace hκ hs hr V D) (h : GammaGenericSelectedRelated U V) :
    A.finalValue hκ hs hr hg = D.finalValue hκ hs hr hg :=
  (T.preserves_generic_geometry hunc h00 hg hv C₀ hBC₀ δ hδ hδ1 E h).finalValue_eq hκ hs hr hg h00

end DiamondIntegral.Section3
