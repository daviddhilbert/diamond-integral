import «section 3».GammaEmptyParameterObjectIdentification
import «section 3».GammaPureSelectedMeasuredRows
import «section 3».GammaRelativeOrderedMeasuredValues

/-! The end values of the contraction induction are the literal
selected RV presentation classes. This connects the saved formula
induction and the actual original-ground principal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
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

theorem GammaSelectedRetainedData.finalValue_actual {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : GammaSelectedRetainedData hc B 0 (k+1)) (P : GammaSelectedRVPresentation B U.set U.select) :
    U.finalValue hκ hs hr hg = gammaMeasuredPrincipalValue (gammaPureSelectedObject U P) := by
  let N := (U.uniform_bound hκ hs hr hg).choose
  have hN := (U.uniform_bound hκ hs hr hg).choose_spec
  have hrow := gammaPureSelected_normalized_row U P N
  have he : vfValues (Fin.elim0 : Fin 0 → VF (M := M)) = Fin.elim0 := Subsingleton.elim _ _
  have hF : (U.schema N).essential.valid Fin.elim0 := he ▸ (U.schema N).essential_valid _ (hN Fin.elim0)
  exact gammaEmptyParameterValue_actual (gammaPureSelectedObject U P) (U.schema N).essential hF
    (fun r => Set.ext_iff.mp hrow.domain r) hrow.volume hrow.density

theorem GammaGenericSelectedRelated.literalEndpointValue_eq {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {U V : GammaSelectedRetainedData hc B 0 (k+1)} (h : GammaGenericSelectedRelated U V)
    (P : GammaSelectedRVPresentation B U.set U.select) (Q : GammaSelectedRVPresentation B V.set V.select) :
    gammaMeasuredPrincipalValue (gammaPureSelectedObject U P) =
      gammaMeasuredPrincipalValue (gammaPureSelectedObject V Q) :=
  (U.finalValue_actual hκ hs hr hg P).symm.trans
    ((h.finalValue_eq hκ hs hr hg h00).trans (V.finalValue_actual hκ hs hr hg Q))

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRelative_ordered_literalValue_eq
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n l : ℕ} {U V : GammaSelectedRetainedData hc B (n+1) 0}
    (F : GammaFullMeasuredBijection U.zeroSelectedMeasured V.zeroSelectedMeasured)
    (hi : ∀ p, ∀ j, j ≠ 0 → (F.map.map p).val.1 j = p.val.1 j)
    (T : GammaSelectedMeasuredHead U) (E : GammaSelectedMeasuredHead V)
    {A D : GammaSelectedRetainedData hc B 0 (l+1)}
    (tail : GammaSelectedMeasuredOrderedTrace hκ.le hs hr (n := n) (k := 0) (l := l) (T.next hκ.le hs hr) A)
    (etail : GammaSelectedMeasuredOrderedTrace hκ.le hs hr (n := n) (k := 0) (l := l) (E.next hκ.le hs hr) D)
    (P : GammaSelectedRVPresentation B A.set A.select) (Q : GammaSelectedRVPresentation B D.set D.select) :
    gammaMeasuredPrincipalValue (gammaPureSelectedObject A P) = gammaMeasuredPrincipalValue (gammaPureSelectedObject D Q) :=
  (A.finalValue_actual hκ.le hs hr hg P).symm.trans
    ((gammaRelative_ordered_finalValue_eq hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1 F hi T E tail etail).trans
      (D.finalValue_actual hκ.le hs hr hg Q))

end DiamondIntegral.Section3
