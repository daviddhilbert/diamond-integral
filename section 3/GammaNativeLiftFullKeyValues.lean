import «section 3».GammaRetainedNativeLiftData
import «section 3».GammaCanonicalPullbackMeasuredValues
import «section 3».GammaStandardRawLabelCutComparisons

/-! The full key of a literal native lift contains no additional
information beyond its original RV label. Projecting that label is
an actual Gamma bijection preserving all structural coordinates and
the complete original density, including zero strata. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeLift_full_key_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hNames : commonRealNames B ⊆ (C.base : Set M))
    (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres
      (rvObjectVolume (pullbackObject ((gammaRetainedNativeLiftData U ω).nativeSet C hNames)))) :
    gammaMeasuredPrincipalValue (gammaNativePullbackTotalMeasuredObject C hBC
      ((gammaRetainedNativeLiftData U ω).nativeSet C hNames)
      (gammaRetainedNativeLiftData U ω).point_definable hAF ω.extendByOne) =
        gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization U ω) := by
  let P := gammaRetainedNativeLiftData U ω
  let A := P.nativeSet C hNames
  let K := gammaNativeFiniteAt (gammaPullbackAt hBC A P.point_definable hAF).toGamma
  have hKey (k : Section5.nativeRVGroundDomain (hc := hc) K) :
      ∃ p : A, Fin.append (Section2.tupleRV M p.val.1) p.val.2 = k.val := by
    obtain ⟨p,hp⟩ := (Section5.nativeRVGroundDomain_carrier K).le k.property
    exact ⟨p,hp⟩
  let old (k : Section5.nativeRVGroundDomain (hc := hc) K) :
      Section5.nativeRVGroundDomain (hc := hc) U := by
    refine ⟨k.val ∘ Fin.natAdd (n+1),?_⟩
    obtain ⟨p,hp⟩ := hKey k
    have he : k.val ∘ Fin.natAdd (n+1) = p.val.2 := by
      rw [← hp]
      funext i
      exact Fin.append_right _ _ i
    exact he ▸ (gammaNativeLiftLabel U ⟨p.val,p.property⟩).property
  let g : GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) K)
      (Section5.nativeRVGroundDomain (hc := hc) U) :=
    (gammaGroundRVSelectCoordinates (Fin.natAdd (n+1)) (Section5.nativeRVGroundDomain K)).corestrict
      (fun k => (old k).property)
  have hVolume (k : Section5.nativeRVGroundDomain (hc := hc) K) :
      (Section5.nativeRVGroundVolume U (g k)).val =
        (Section5.nativeRVGroundVolume K k).val := by
    obtain ⟨p,hp⟩ := hKey k
    obtain ⟨u,hu,hv⟩ := (gammaNativeLift_membership (hc := hc) U p.val).mp p.property
    have he : g k = u := by
      apply Subtype.ext
      change k.val ∘ Fin.natAdd (n+1) = u.val
      rw [← hp,hu]
      funext i
      exact Fin.append_right _ _ i
    rw [he,gammaNativeRVGroundVolume_value K]
    change _ = k.val ∘ Fin.castAdd P.arity
    rw [hv,← hp]
    funext i
    exact (Fin.append_left _ _ i).symm
  have hg : Function.Bijective g := by
    constructor
    · intro k l hkl
      apply Subtype.ext
      obtain ⟨p,hp⟩ := hKey k
      obtain ⟨q,hq⟩ := hKey l
      have hOld : p.val.2 = q.val.2 := by
        have he := congrArg (fun z : Section5.nativeRVGroundDomain (hc := hc) U => z.val) hkl
        change k.val ∘ Fin.natAdd (n+1) = l.val ∘ Fin.natAdd (n+1) at he
        simpa only [← hp,← hq,Function.comp_def,Fin.append_right] using he
      obtain ⟨u,hu,hvu⟩ := (gammaNativeLift_membership (hc := hc) U p.val).mp p.property
      obtain ⟨v,hv,hvv⟩ := (gammaNativeLift_membership (hc := hc) U q.val).mp q.property
      have huv : u = v := by
        apply Subtype.ext
        exact hu.trans (hOld.trans hv.symm)
      rw [← hp,← hq,← hvu,← hvv,huv,hOld]
    · intro u
      obtain ⟨x,hx⟩ := @Section2.tupleRV_surjective M _ _ (n+1) (Section5.nativeRVGroundVolume U u).val
      have hxmem : (x,u.val) ∈ carrier A :=
        (gammaNativeLift_membership (hc := hc) U (x,u.val)).mpr ⟨u,rfl,hx.symm⟩
      let p : A := ⟨(x,u.val),hxmem⟩
      let k : Section5.nativeRVGroundDomain (hc := hc) K :=
        ⟨Fin.append (Section2.tupleRV M x) u.val,
          (Section5.nativeRVGroundDomain_carrier K).ge ⟨p,rfl⟩⟩
      refine ⟨k,Subtype.ext ?_⟩
      funext i
      exact Fin.append_right _ _ i
  apply gammaMeasuredPrincipalValue_iso
  apply gammaNativeGroundCoordinateHom (gammaNativeTotalRVForm K (Fin.natAdd (n+1)) ω.extendByOne) ω ⟨g,hg⟩ hVolume
  intro k
  exact (ω.extendByOne_apply (g k)).symm

end DiamondIntegral.Section3
