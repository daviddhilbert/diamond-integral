import «section 3».GammaNativeFullProgramValues

/-! Native program values in the identity coordinate order are
independent of the specified Gamma preparations. This is the full
measured comparison, with arbitrary retained Gamma density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeFullProgramValue_same_source
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n a b c : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    {E : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 c}
    (P : OrderedContractionProgram (C.base : Set M) A D) (R : OrderedContractionProgram (C.base : Set M) A E)
    (hP : GammaProgramDefinable B P) (hR : GammaProgramDefinable B R)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    gammaNativeFullProgramValue C hBC hv hg P hP hA hfin Q hQ ω =
      gammaNativeFullProgramValue C hBC hv hg R hR hA hfin Q hQ ω := by
  let U := gammaPointMeasuredData A hA hfin (gammaPointRetainedForm A hA Q id hQ ω)
  let F : GammaFullMeasuredBijection U U := gammaFullMeasuredFixedVF C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv (GammaGroundBijection.id U.domain)
    (fun _ => rfl) (fun _ => rfl)
  exact gammaNativeFullProgramValue_relative C hBC hv hg δ hδ hδ1 P R hP hR hA hA hfin hfin
    Q Q hQ hQ ω ω F (fun _ _ _ => rfl)

end DiamondIntegral.Section3
