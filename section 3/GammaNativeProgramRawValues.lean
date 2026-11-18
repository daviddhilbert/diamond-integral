import «section 3».GammaNativeEndpointRawClasses
import «section 3».GammaNativeSameOrderMeasuredValues

/-! The full native program value is the literal raw contraction
class. Thus its proved relatively unary and same-order comparisons
apply directly to the actual geometric RV presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ) {n a : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable {σ : Equiv.Perm (Fin (n+1))}

theorem gammaNativeFullProgramValue_raw
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaNativeFullProgramValue C hBC hv hg T.program hT
      (gamma_vfPermutationImage A hA σ) (vfPermutation_finite_rv_fibres A σ hfin)
      (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) := by
  rcases T with ⟨b,D,P⟩
  cases P with
  | step R tail =>
    let hAP := gamma_vfPermutationImage A hA σ
    let hfinP := vfPermutation_finite_rv_fibres A σ hfin
    let H := gammaNativeSelectedMeasuredHead C hBC hv hAP R hT.2.1 hT.1 Fin.elim0
      (gammaNative_finite_zero_selected C hfinP)
      (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let N := H.next C.uncountable.le C.saturated hr
    let E := gammaNativePositiveProgramTrace C hBC hv tail hT.2.2 (gamma_headImage R.target hT.2.1)
      (k := 0) N.select N.finite N.labels (fun p => N.labels_mem ⟨p.val,p.property⟩) N.form
    change E.value hg = _
    rcases E with ⟨l,V,tr,hV⟩
    have hl : l = n := by have h := tr.degree; omega
    subst l
    exact gammaNative_endpoint_raw_class C hBC hv hg hA hfin ⟨b,D,.step R tail⟩ hT ω V hV

include hv hg in
theorem gammaNativeRawMeasuredContraction_same_order
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (T W : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (hW : GammaProgramDefinable B W.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin W hW ω) := by
  rw [← gammaNativeFullProgramValue_raw C hBC hv hg hA hfin T hT ω,
    ← gammaNativeFullProgramValue_raw C hBC hv hg hA hfin W hW ω]
  exact gammaNativeFullProgramValue_same_source C hBC hv hg δ hδ hδ1 T.program W.program hT hW
    (gamma_vfPermutationImage A hA σ) (vfPermutation_finite_rv_fibres A σ hfin)
    (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω

end DiamondIntegral.Section3
