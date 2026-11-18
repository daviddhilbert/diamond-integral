import «section 3».GammaNativeOrderedMeasuredTraces
import «section 3».GammaNativeOrderedEndpointForms

/-! A specified native program has a constructed measured trace and
an actual RV endpoint value. The saved induction compares any two such
programs whose initial selected rows have finite generic Gamma proofs. -/
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
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {n a b k : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
variable {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}

structure GammaNativePositiveProgramTrace
    (P : OrderedContractionProgram (C.base : Set M) A D) (hP : GammaProgramDefinable B P)
    (hA : GammaSetDefinable B (carrier A))
    (ρ : Fin (k+1) → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) where
  degree : ℕ
  target : GammaSelectedRetainedData hc B 0 (degree+1)
  trace : GammaSelectedMeasuredOrderedTrace C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small)
    (gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω) target
  endpoint : HEq target (gammaNativeOrderedEndpoint C hBC hv P hP hA ρ hfin Q hQ ω)

def gammaNativePositiveProgramTrace
    (P : OrderedContractionProgram (C.base : Set M) A D) (hP : GammaProgramDefinable B P)
    (hA : GammaSetDefinable B (carrier A))
    (ρ : Fin (k+1) → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaNativePositiveProgramTrace C hBC hv P hP hA ρ hfin Q hQ ω := by
  let H := gammaNativeOrdered_measured_trace_exists C hBC hv P hP hA ρ hfin Q hQ ω
  let l := H.choose
  let V := H.choose_spec.choose
  have hV := H.choose_spec.choose_spec
  exact ⟨l,V,hV.1.some,hV.2⟩

variable {C hBC hv}

def GammaNativePositiveProgramTrace.value
    {P : OrderedContractionProgram (C.base : Set M) A D} {hP : GammaProgramDefinable B P}
    {hA : GammaSetDefinable B (carrier A)}
    {ρ : Fin (k+1) → Fin a} {hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite}
    {Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}
    {hQ : ∀ p : A, p.val.2 ∈ Q.carrier} {ω : GammaGroundVolumeForm hc B Q}
    (T : GammaNativePositiveProgramTrace C hBC hv P hP hA ρ hfin Q hQ ω)
    (hg : Cardinal.mk B.gamma < C.κ) :=
  T.target.finalValue C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hg

theorem gammaNativePositiveProgramTrace_value_eq
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {a' b' : ℕ}
    {A' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a'}
    {D' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b'}
    {P : OrderedContractionProgram (C.base : Set M) A D} {hP : GammaProgramDefinable B P}
    {R : OrderedContractionProgram (C.base : Set M) A' D'} {hR : GammaProgramDefinable B R}
    {hA : GammaSetDefinable B (carrier A)} {hA' : GammaSetDefinable B (carrier A')}
    {ρ : Fin (k+1) → Fin a} {τ : Fin (k+1) → Fin a'}
    {hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite}
    {hfin' : ∀ x t, {r | (x,r) ∈ carrier A' ∧ r ∘ τ = t}.Finite}
    {Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}
    {Q' : GammaGroundDefSet hc B (rawRVSpace (M := M) a')}
    {hQ : ∀ p : A, p.val.2 ∈ Q.carrier} {hQ' : ∀ p : A', p.val.2 ∈ Q'.carrier}
    {ω : GammaGroundVolumeForm hc B Q} {η : GammaGroundVolumeForm hc B Q'}
    (T : GammaNativePositiveProgramTrace C hBC hv P hP hA ρ hfin Q hQ ω)
    (E : GammaNativePositiveProgramTrace C hBC hv R hR hA' τ hfin' Q' hQ' η)
    (h : GammaGenericSelectedRelated (gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω)
      (gammaNativeSelectedRetainedData A' hA' τ hfin' Q' hQ' η)) :
    T.value hg = E.value hg := by
  rcases T with ⟨l,V,T,hT⟩
  rcases E with ⟨j,W,E,hE⟩
  have hdeg : l = j := by
    have hTdeg := T.degree
    have hEdeg := E.degree
    omega
  subst j
  exact T.finalValue_eq C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hg C.uncountable C.model00 hv C hBC δ hδ hδ1 E h

end DiamondIntegral.Section3
