import «section 6».MeasuredRVLabelReplacements
import «section 6».MeasuredVFUnaryChainExtensions

/-! One actual VF global assembly step. Extend a local chain only on labels not
processed earlier; then identify its endpoint with the canonical volume
replacement on the enlarged processed set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_vf_cover_extension_step (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (P Q R : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hP : P.carrier ⊆ U.object.domain.carrier) (hQ : Q.carrier ⊆ U.object.domain.carrier)
    (hR : R.carrier ⊆ U.object.domain.carrier)
    (hUnion : ∀ u : U.object.domain, u.val ∈ R.carrier ↔ u.val ∈ P.carrier ∨ u.val ∈ Q.carrier)
    (T : MeasuredVFUnaryLiftChain S n (U.restrict Q hQ)
      (V.restrict (e.iso.hom.map.restrict hQ).image (rvLabelImage_subset e.iso Q hQ)))
    (hT : T.iso.iso.hom.map = (e.restrict Q hQ).iso.hom.map) :
    ∃ H : MeasuredVFUnaryLiftChain S n (measuredRVLabelReplacement hc e P hP) (measuredRVLabelReplacement hc e R hR),
      (∀ u, H.iso.iso.hom.map u = u) ∧
        ((U.doublyBounded ∧ V.doublyBounded ∧ T.doublyBounded) → H.doublyBounded) := by
  let A := measuredRVLabelReplacement hc e P hP
  let B := V.restrict (e.iso.hom.map.restrict hQ).image (rvLabelImage_subset e.iso Q hQ)
  let D := Q.sdiff P
  have hD : D.carrier ⊆ A.object.domain.carrier := fun _ hu => hQ hu.1
  let χ : Map D (U.restrict Q hQ).object.domain := Map.inclusion (fun _ hu => hu.1)
  have hχ : Function.Injective χ := by
    intro u v he
    exact Subtype.ext (congrArg (fun x : Q => x.val) he)
  have hVol (u : D) : (U.restrict Q hQ).object.value (χ u) = A.object.value ⟨u.val,hD u.property⟩ := by
    exact (measuredRVLabelReplacement_of_not_mem hc e P hP
      ⟨u.val,hQ u.property.1⟩ u.property.2).symm
  obtain ⟨L,hL,hLB⟩ := exists_measured_vfChain_extension_from_source hc hn A T D hD χ hχ hVol
  let ι := T.iso.iso.hom.map.comp χ
  have hι : Function.Injective ι := (rvIso_map_bijective T.iso.iso).1.comp hχ
  let G := measuredRVVolumeExtension hc A B D ι hι
  have hNew (u : U.object.domain) (hu : u.val ∈ D.carrier) :
      G.object.value u = V.object.value (e.iso.hom.map u) := by
    rw [measuredRVVolumeExtension_of_mem hc A B D ι hι u hu]
    change B.object.value (T.iso.iso.hom.map (χ ⟨u.val,hu⟩)) = _
    rw [hT]
    rfl
  have hValue (u : U.object.domain) : (measuredRVLabelReplacement hc e R hR).object.value u = G.object.value u := by
    by_cases huP : u.val ∈ P.carrier
    · have huD : u.val ∉ D.carrier := fun h => h.2 huP
      rw [measuredRVLabelReplacement_of_mem hc e R hR u ((hUnion u).mpr (Or.inl huP)),
        measuredRVVolumeExtension_of_not_mem hc A B D ι hι u huD,
        measuredRVLabelReplacement_of_mem hc e P hP u huP]
    · by_cases huQ : u.val ∈ Q.carrier
      · have huD : u.val ∈ D.carrier := ⟨huQ,huP⟩
        rw [measuredRVLabelReplacement_of_mem hc e R hR u ((hUnion u).mpr (Or.inr huQ)),hNew u huD]
      · have huD : u.val ∉ D.carrier := fun h => huQ h.1
        have huR : u.val ∉ R.carrier := by
          intro h
          rcases (hUnion u).mp h with h | h
          · exact huP h
          · exact huQ h
        rw [measuredRVLabelReplacement_of_not_mem hc e R hR u huR,
          measuredRVVolumeExtension_of_not_mem hc A B D ι hι u huD,
          measuredRVLabelReplacement_of_not_mem hc e P hP u huP]
  let d : MeasuredRVIso G (measuredRVLabelReplacement hc e R hR) := {
    iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id hValue
    balance u := (measuredRVVolumeExtension_totalWeight hc A B D ι hι u).trans
      ((measuredRVLabelReplacement_totalWeight hc e P hP u).trans
        (measuredRVLabelReplacement_totalWeight hc e R hR u).symm) }
  let i : Fin n := ⟨0,hn⟩
  let F := volumePreservingMeasuredRVLift d hValue
  let K : MeasuredVFUnaryLiftChain S n G (measuredRVLabelReplacement hc e R hR) :=
    .step i F (volumePreservingMeasuredRVLift_unary d hValue i) (.identity _)
  refine ⟨L.comp K,fun u => ?_,fun hB => ?_⟩
  · rw [MeasuredVFUnaryLiftChain.comp_map,hL]
    rfl
  · have hA := measuredRVLabelReplacement_doublyBounded hc e P hP hB.1 hB.2.1
    have hB' : B.doublyBounded := V.restrict_doublyBounded _ _ hB.2.1
    exact L.comp_doublyBounded K (hLB ⟨hA,hB.2.2⟩)
      ⟨measuredRVVolumeExtension_doublyBounded hc A B D ι hι hA hB',
        measuredRVLabelReplacement_doublyBounded hc e R hR hB.1 hB.2.1⟩

end DiamondIntegral.Section6
