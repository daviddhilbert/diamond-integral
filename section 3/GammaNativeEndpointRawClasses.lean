import «section 3».GammaNativeFullProgramValues
import «section 3».GammaNativeEndpointHeterogeneousSpecs
import «section 3».GammaSelectedNativeFinalComparison
import IntegrationSection6.RawFiniteContractions
import IntegrationSection6.FiniteContractionLabels

/-! The native ordered endpoint has the principal class of the literal
raw standard contraction, with its original retained Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ) {n a : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable {σ : Equiv.Perm (Fin (n+1))}

def gammaNativeRawMeasuredContraction
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :=
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let V := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
  gammaNativeMeasuredNormalization V (gammaNativeTotalRVForm V (suffixIndex T.program.rvArity_le) ω)

theorem gammaNative_endpoint_raw_class
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (U : GammaSelectedRetainedData hc B 0 (n+1))
    (hU : HEq U (gammaNativeOrderedEndpoint C hBC hv T.program hT
      (gamma_vfPermutationImage A hA σ) Fin.elim0
      (gammaNative_finite_zero_selected C (vfPermutation_finite_rv_fibres A σ hfin))
      (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω)) :
    U.finalValue C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hg =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) := by
  let E := gammaNativeOrderedEndpoint C hBC hv T.program hT
    (gamma_vfPermutationImage A hA σ) Fin.elim0
    (gammaNative_finite_zero_selected C (vfPermutation_finite_rv_fibres A σ hfin))
    (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω
  have hd : n+1 = orderedVolumeDegree (n+1) 0 := by rw [orderedVolumeDegree_eq,Nat.add_zero]
  have hspec := gammaNativeOrderedEndpoint_spec C hBC hv T.program hT
    (gamma_vfPermutationImage A hA σ) Fin.elim0
    (gammaNative_finite_zero_selected C (vfPermutation_finite_rv_fibres A σ hfin))
    (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω
  have ha : U.arity = T.arity := (gammaSelectedData_heq_arity hd hU).trans hspec.1
  have hset : HEq U.set (extendBase T.target (Set.subset_univ _)) :=
    (gammaSelectedData_heq_set hd hU).trans hspec.2.1
  have hsel : HEq U.select (orderedSelectedIndex T.program (Fin.elim0 : Fin 0 → Fin a)) :=
    (gammaSelectedData_heq_select hd hU).trans hspec.2.2
  rcases U with ⟨b,X,hX,ρ,hfinite,Q,hQ,η⟩
  dsimp only at ha hset hsel
  subst b
  have hXeq : X = extendBase T.target (Set.subset_univ _) := eq_of_heq hset
  subst X
  let U : GammaSelectedRetainedData hc B 0 (n+1) :=
    ⟨T.arity,extendBase T.target (Set.subset_univ _),hX,ρ,hfinite,Q,hQ,η⟩
  obtain ⟨P⟩ := gammaSelectedRVPresentation_exists U.set U.gamma U.select (U.finite Fin.elim0)
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let V := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
  let ζ := gammaNativeTotalRVForm V (suffixIndex T.program.rvArity_le) ω
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) V).carrier := by
    rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier]
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
      (@CanonicalStructure.normalize M _) _ _ P.domain) = carrier (Map.image (rawLabelMap T.target))
    rw [P.domain_eq]
    ext r
    constructor
    · intro hr
      exact ⟨⟨(Fin.elim0,r),hr⟩,rfl⟩
    · rintro ⟨p,hp⟩
      have hp' : p.val = (Fin.elim0,r) := Prod.ext (Subsingleton.elim _ _) hp
      change (Fin.elim0,r) ∈ carrier T.target
      exact hp' ▸ p.property
  let f := GammaGroundBijection.ofCarrierEq hDom
  apply gammaSelected_native_final_comparison C.uncountable.le C.saturated hr hg U P V ζ f
  · intro u
    have hvP := (P.graph_iff u.val (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val).mp
      ⟨Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma) u,rfl,
        (gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) u).symm⟩
    have hvp : (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val = u.val ∘ ρ := hvP.2.2.symm
    rw [hvp,gammaNativeRVGroundVolume_value]
    change (∏ i, Values.vrv (u.val (ρ i))) = ∏ i, Values.vrv (u.val (T.volumeIndex i))
    have hp := gammaProduct_heq hd hsel (fun j => Values.vrv (u.val j))
    exact hp.trans ((gammaOrderedSelectedIndex_empty_product T.program (fun j => Values.vrv (u.val j))).trans
      (Equiv.prod_comp σ.symm (fun i => Values.vrv (u.val (T.program.volumeIndex i)))).symm)
  · intro u
    let q : Section5.nativeGammaPointDomain (hc := hc) (carrier U.set) U.gamma :=
      ⟨(Fin.elim0,u.val),gammaPureSelected_mem U P u⟩
    obtain ⟨p,hp⟩ := T.program.surjective ⟨q.val,q.property⟩
    have hEarity : E.arity = T.arity := hspec.1
    have hForm : U.pointForm q = ω ⟨p.val.2,Set.mem_univ _⟩ := by
      apply gammaSelectedData_heq_form_fibre hd hU (T.program.toMap p).val
        (ω ⟨p.val.2,Set.mem_univ _⟩)
        (gammaNativeOrderedEndpoint_form C hBC hv T.program hT
          (gamma_vfPermutationImage A hA σ) Fin.elim0
          (gammaNative_finite_zero_selected C (vfPermutation_finite_rv_fibres A σ hfin))
          (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω p) q
      exact heq_of_eq (congrArg Subtype.val hp.symm)
    change U.pointForm q = ω ⟨(f.map u).val ∘ suffixIndex T.program.rvArity_le,Set.mem_univ _⟩
    rw [hForm]
    apply congrArg ω
    apply Subtype.ext
    funext i
    have hi := T.program.oldLabels p i
    have he := congrArg (fun z => z.val.2 (suffixIndex T.program.rvArity_le i)) hp
    exact hi.symm.trans he

end DiamondIntegral.Section3
