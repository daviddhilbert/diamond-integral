import «section 3».GammaRawSelectedMeasuredContractions
import Integration7.SelectedVFTailVolumeCharts

/-! The existing canonical selected-tail projection preserves every
old label and every structural coordinate, hence any complete retained
Gamma density. It gives an actual measured arrow on normalized objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a d b : ℕ}

theorem gammaSelected_tail_completion_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (E : OrderedContractionProgram (C.base : Set M)
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hFull : GammaProgramDefinable B (selectedRVVFTailFullProgram hc T.program ρ E))
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (hCon : Contractible E.toMap)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    let A' := nativeProgramSelectedRVVFTailLift hc A ρ
    let hA' := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
    let hfin' := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
    let R := selectedRVVFTailStandardContraction hc T ρ E
    let hR := gamma_selected_rv_vf_tail_standard_contraction hc T ρ E hFull
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA' hfin' R hR ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω) := by
  intro A' hA' hfin' R hR
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA' hfin' R hR)
  let W := gammaNativeRawSelectedAt C hBC hA ρ hfin T hT
  let f := canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E
  have hf := canonical_selected_tail_rv_projection_bijective hc T.target _ E hCon
  have hUmem := gammaNative_raw_contraction_mem (hc := hc) C hBC hA' hfin' R hR
  have hWmem := gammaNativeRawSelected_mem (hc := hc) C hBC hA ρ hfin T hT
  let point (u : Section5.nativeRVGroundDomain (hc := hc) U) : V :=
    ⟨(Fin.elim0,u.val),(hUmem u.val).mp u.property⟩
  let g : GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) U)
      (Section5.nativeRVGroundDomain (hc := hc) W) :=
    (gammaGroundRVSelectCoordinates (suffixIndex E.rvArity_le) (Section5.nativeRVGroundDomain U)).corestrict
      (fun u => (hWmem _).mpr (f (point u)).property)
  have hg : Function.Bijective g := by
    constructor
    · intro u v huv
      apply Subtype.ext
      have he : f (point u) = f (point v) := by
        apply Subtype.ext
        exact Prod.ext (Subsingleton.elim _ _) (congrArg Subtype.val huv)
      exact congrArg (fun p => p.val.2) (hf.1 he)
    · intro w
      obtain ⟨p,hp⟩ := hf.2 ⟨(Fin.elim0,w.val),(hWmem w.val).mp w.property⟩
      let u : Section5.nativeRVGroundDomain (hc := hc) U := ⟨p.val.2,(hUmem p.val.2).mpr (by
        have he : (Fin.elim0,p.val.2) = p.val := Prod.ext (Subsingleton.elim _ _) rfl
        exact he ▸ p.property)⟩
      refine ⟨u,Subtype.ext ?_⟩
      have he : point u = p := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
      exact (congrArg (fun p => (f p).val.2) he).trans (congrArg (fun p => p.val.2) hp)
  apply gammaMeasuredPrincipalValue_iso
  apply gammaNativeGroundCoordinateHom
    (gammaNativeTotalRVForm U (suffixIndex R.program.rvArity_le) ω)
    (gammaNativeTotalRVForm W (suffixIndex T.program.rvArity_le) ω) ⟨g,hg⟩
  · intro u
    rw [gammaNativeRawSelected_volume,gammaNativeRVGroundVolume_value]
    exact selected_rv_vf_tail_standard_volume hc T ρ E hVF (point u)
  · intro u
    apply congrArg ω
    apply Subtype.ext
    funext i
    exact selected_rv_vf_tail_standard_density hc T ρ E (point u) i

end DiamondIntegral.Section3
