import «section 3».GammaNativeOrderedMeasuredEndpoints

/-! Native ordered endpoint forms retain the original Gamma density
on every actual contraction fibre. The recursive head construction
therefore gives the same form as the paper's old-label convention. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeOrderedEndpoint_form
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (P : OrderedContractionProgram (C.base : Set M) A D) :
    ∀ (hP : GammaProgramDefinable B P) (hA : GammaSetDefinable B (carrier A))
    {k : ℕ} (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q),
      let E := gammaNativeOrderedEndpoint C hBC hv P hP hA ρ hfin Q hQ ω
      ∀ a : A, ∀ q : Section5.nativeGammaPointDomain (hc := hc) (carrier E.set) E.gamma,
        HEq q.val (P.toMap a).val → E.pointForm q = ω ⟨a.val.2,hQ a⟩ := by
  induction P with
  | zero A =>
    intro hP hA k ρ hfin Q hQ ω E a q hq
    have he : q.val = a.val := eq_of_heq hq
    apply congrArg ω
    apply Subtype.ext
    exact congrArg Prod.snd he
  | step T tail ih =>
    intro hP hA k ρ hfin Q hQ ω E a q hq
    let H := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 ρ hfin Q hQ ω
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let N := H.next C.uncountable.le C.saturated hr
    have hTail := ih hP.2.2 (gamma_headImage T.target hP.2.1) N.select N.finite N.labels
      (fun p => N.labels_mem ⟨p.val,p.property⟩) N.form (T.contractionMap a) q hq
    let p : Section5.nativeGammaPointDomain (hc := hc) (carrier N.set) N.gamma :=
      ⟨(H.head.contractionMap ⟨a.val,a.property⟩).val,(H.head.contractionMap ⟨a.val,a.property⟩).property⟩
    have hNext := congrArg (fun f => f p) (H.next_pointForm C.uncountable.le C.saturated hr)
    have hHead := gammaHeadContractedForm_apply H.head H.targetGamma Q hQ ω ⟨a.val,a.property⟩
    exact hTail.trans (hNext.trans hHead)

end DiamondIntegral.Section3
