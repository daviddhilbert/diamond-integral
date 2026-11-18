import «section 3».GammaNativePositiveProgramTraces
import «section 3».GammaFullMeasuredFixedMaps

/-! A native full measured family starts with no selected labels. Its
first specified head supplies the positive selected tail, so the proved
relative unary comparison now applies to complete native programs. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ) {n a b : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}

theorem gammaNative_finite_zero_selected
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (x : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
    {r | (x,r) ∈ carrier A ∧ r ∘ (Fin.elim0 : Fin 0 → Fin a) = t}.Finite :=
  (hfin x).subset (fun _ h => h.1)

def gammaNativeFullProgramValue
    (P : OrderedContractionProgram (C.base : Set M) A D) (hP : GammaProgramDefinable B P)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) := by
  cases P with
  | step T tail =>
    let H := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 Fin.elim0
      (gammaNative_finite_zero_selected C hfin) Q hQ ω
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let N := H.next C.uncountable.le C.saturated hr
    let E := gammaNativePositiveProgramTrace C hBC hv tail hP.2.2 (gamma_headImage T.target hP.2.1)
      (k := 0) N.select N.finite N.labels (fun p => N.labels_mem ⟨p.val,p.property⟩) N.form
    exact E.value hg

theorem gammaNativeFullProgramValue_relative
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {a' b' : ℕ}
    {A' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a'}
    {D' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b'}
    (P : OrderedContractionProgram (C.base : Set M) A D) (R : OrderedContractionProgram (C.base : Set M) A' D')
    (hP : GammaProgramDefinable B P) (hR : GammaProgramDefinable B R)
    (hA : GammaSetDefinable B (carrier A)) (hA' : GammaSetDefinable B (carrier A'))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfin' : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A'}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (Q' : GammaGroundDefSet hc B (rawRVSpace (M := M) a'))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (hQ' : ∀ p : A', p.val.2 ∈ Q'.carrier)
    (ω : GammaGroundVolumeForm hc B Q) (η : GammaGroundVolumeForm hc B Q')
    (F : GammaFullMeasuredBijection
      (gammaPointMeasuredData A hA hfin (gammaPointRetainedForm A hA Q id hQ ω))
      (gammaPointMeasuredData A' hA' hfin' (gammaPointRetainedForm A' hA' Q' id hQ' η)))
    (hi : ∀ p, ∀ j, j ≠ 0 → (F.map.map p).val.1 j = p.val.1 j) :
    gammaNativeFullProgramValue C hBC hv hg P hP hA hfin Q hQ ω =
      gammaNativeFullProgramValue C hBC hv hg R hR hA' hfin' Q' hQ' η := by
  cases P with
  | step T tail =>
    cases R with
    | step E etail =>
      let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
      let HT := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 Fin.elim0
        (gammaNative_finite_zero_selected C hfin) Q hQ ω
      let HE := gammaNativeSelectedMeasuredHead C hBC hv hA' E hR.2.1 hR.1 Fin.elim0
        (gammaNative_finite_zero_selected C hfin') Q' hQ' η
      let NT := HT.next C.uncountable.le C.saturated hr
      let NE := HE.next C.uncountable.le C.saturated hr
      let PT := gammaNativePositiveProgramTrace C hBC hv tail hP.2.2 (gamma_headImage T.target hP.2.1)
        (k := 0) NT.select NT.finite NT.labels (fun p => NT.labels_mem ⟨p.val,p.property⟩) NT.form
      let PE := gammaNativePositiveProgramTrace C hBC hv etail hR.2.2 (gamma_headImage E.target hR.2.1)
        (k := 0) NE.select NE.finite NE.labels (fun p => NE.labels_mem ⟨p.val,p.property⟩) NE.form
      change PT.value hg = PE.value hg
      rcases PT with ⟨l,V,TT,hTT⟩
      rcases PE with ⟨j,W,EE,hEE⟩
      have hdeg : l = j := by
        have hTdeg := TT.degree
        have hEdeg := EE.degree
        omega
      subst j
      exact gammaRelative_ordered_finalValue_eq C.uncountable C.saturated C.model00 hr hg hv C hBC
        δ hδ hδ1
        (U := gammaNativeSelectedRetainedData A hA Fin.elim0 (gammaNative_finite_zero_selected C hfin) Q hQ ω)
        (V := gammaNativeSelectedRetainedData A' hA' Fin.elim0 (gammaNative_finite_zero_selected C hfin') Q' hQ' η)
        F hi HT HE TT EE

end DiamondIntegral.Section3
