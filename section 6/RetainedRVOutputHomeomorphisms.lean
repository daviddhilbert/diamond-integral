import «section 6».RefinementPortHomeomorphisms
import «section 6».RefinementPortDerivatives

/-! Retaining the source RV labels of any actual proper covariant
homeomorphism preserves its proper homeomorphism geometry. No retention
selector for the original map is needed. Its new fibres are the actual
fixed-label graph ranges, rather than whole old target fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem retainedRVOutput_target_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (v : Fin (s+r) → RVInfinity M) :
    vfFibre (retainedRVOutputMap hc f).image.carrier v=
      graphFibreRange f (v ∘ Fin.natAdd s) (v ∘ Fin.castAdd r) := by
  ext b
  constructor
  · rintro ⟨p,hp⟩
    change (retainedRVOutput hc f p).val=(b,v) at hp
    have hInput : p.val.2=v ∘ Fin.natAdd s := by
      funext i
      exact (retainedRVOutput_retained hc f p i).symm.trans
        (congrArg (fun q : Mixed M m (s+r) => q.2 (Fin.natAdd s i)) hp)
    have hOutput : (f p).val=(b,v ∘ Fin.castAdd r) := by
      have h := retainedRVOutput_selected hc f p
      rw [hp] at h
      exact h.symm
    exact ⟨p.val.1,p,Prod.ext rfl hInput,hOutput⟩
  · rintro ⟨a,p,hp,hfp⟩
    have hInput := congrArg Prod.snd hp
    have hOutput := congrArg Prod.snd hfp
    refine ⟨p,?_⟩
    change (retainedRVOutput hc f p).val=(b,v)
    apply Prod.ext
    · have hVF := congrArg Prod.fst hfp
      exact hVF
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [retainedRVOutput_value,Fin.append_left,Function.comp_apply] using congrFun hOutput j
      · simpa only [retainedRVOutput_value,Fin.append_right,Function.comp_apply] using congrFun hInput j

theorem retainedRVOutput_target_doublyBounded
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (hB : VFDoublyBounded B.carrier) :
    VFDoublyBounded (retainedRVOutputMap hc f).image.carrier := by
  obtain ⟨α,hα⟩ := hB
  exact ⟨α,by rintro q ⟨p,rfl⟩ i; exact hα (f p).val (f p).property i⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem retainedRVOutput_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hF : ProperCovariantHomeomorphism f)
    (hAD : VFDoublyBounded A.carrier) (hBD : VFDoublyBounded B.carrier) :
    ProperCovariantHomeomorphism (retainedRVOutput hc f) := by
  have hA := hF.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  let X := RVRefinementFrame.identity A hA hAD
  have hD := retainedRVOutput_target_doublyBounded hc f hBD
  have hR : RVSupportDoublyBounded (retainedRVOutputMap hc f).image.carrier :=
    X.port_target_rvBounded hc f hB.rvBounded
  have hProper : ProperInvariant S (retainedRVOutputMap hc f).image.carrier := by
    obtain ⟨α,hα⟩ := hD
    apply (lemma_6_5 h00 hc hκ hs hv _ (retainedRVOutputMap hc f).image.definable
      ⟨α⁻¹,fun p hp i => (hα p hp i).1⟩ hR).mpr
    intro v
    rw [retainedRVOutput_target_fibre hc f v]
    obtain ⟨α,β,hα,hβ,hInv,hRange,hCov⟩ := hF.covariant.radii (v ∘ Fin.natAdd s) (v ∘ Fin.castAdd r)
    exact hRange.isClopen hv
  have hSource (u v) : IsClopen (graphFibreSource (retainedRVOutput hc f) u v) := by
    change IsClopen (graphFibreSource (X.portMap hc f) u v)
    rw [X.port_graph_source hc f u v]
    split_ifs
    · obtain ⟨α,β,hα,hβ,hInv,hRange,hCov⟩ := hF.covariant.radii (u ∘ X.labels) (v ∘ Fin.castAdd X.arity)
      exact (hA.clopen_fibres hv u).inter (hInv.isClopen hv)
    · exact isClopen_empty
  have hRange (u v) : IsClopen (graphFibreRange (retainedRVOutput hc f) u v) := by
    change IsClopen (graphFibreRange (X.portMap hc f) u v)
    rw [X.port_graph_range hc f u v]
    split_ifs
    · exact hProper.clopen_fibres hv v
    · exact isClopen_empty
  have hCont : ContinuousOnGraphFibres (retainedRVOutput hc f) := X.port_continuous hc f hF.continuous
  have hBij : Function.Bijective (retainedRVOutput hc f) := X.port_bijective hc f hF.bijective.injective
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv _ hA hProper hCont
      (fun u v => (hSource u v).isOpen) hRange) hBij hCont

end DiamondIntegral.Section6
