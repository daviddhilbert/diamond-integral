import «section 6».RefinementPortTargets

/-! An actual proper covariant base homeomorphism ports through full
RV refinements. The full target and graph ranges retain their clopen
geometry, and the VF graph maps are the original graph maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem RVRefinementFrame.port_graph_range (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B)
    (u : Fin X.arity → RVInfinity M) (v : Fin (s+X.arity) → RVInfinity M) :
    graphFibreRange (X.portMap hc f) u v=if u=v ∘ Fin.natAdd s then
      vfFibre (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier v else ∅ := by
  ext b
  constructor
  · rintro ⟨a,p,hp,hfp⟩
    have hLabels : u=v ∘ Fin.natAdd s := by
      funext i
      have hInput := congrArg (fun q : Mixed M n X.arity => q.2 i) hp
      have hOutput := congrArg (fun q : Mixed M m (s+X.arity) => q.2 (Fin.natAdd s i)) hfp
      exact hInput.symm.trans ((X.port_retained hc f p i).symm.trans hOutput)
    rw [if_pos hLabels]
    exact ⟨p,hfp⟩
  · intro hb
    split_ifs at hb with hLabels
    · obtain ⟨p,hp⟩ := hb
      have hInput : p.val.2=u := by
        funext i
        have hOutput := congrArg (fun q : Mixed M m (s+X.arity) => q.2 (Fin.natAdd s i)) hp
        exact (X.port_retained hc f p i).symm.trans (hOutput.trans (congrFun hLabels i).symm)
      exact ⟨p.val.1,p,Prod.ext rfl hInput,hp⟩
    · exact False.elim hb

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem RVRefinementFrame.port_continuous (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (hCont : ContinuousOnGraphFibres f) :
    ContinuousOnGraphFibres (X.portMap hc f) := by
  intro u v
  have hSub : graphFibreSource (X.portMap hc f) u v ⊆ graphFibreSource f (u ∘ X.labels) (v ∘ Fin.castAdd X.arity) :=
    fun a ha => ((X.port_source_iff hc f u v a).mp ha).2.2
  exact ((hCont _ _).mono hSub).congr (X.port_graphMap_agrees hc f u v)

theorem RVRefinementFrame.port_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (X : RVRefinementFrame A) (f : Map A B) (hF : ProperCovariantHomeomorphism f)
    (π : Fin r → Fin s) (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (hBD : VFDoublyBounded B.carrier) : ProperCovariantHomeomorphism (X.portMap hc f) := by
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  let Y := X.portTarget h00 hc hκ hs hv f hF.bijective π hRetain hB hBD
  have hSource (u v) : IsClopen (graphFibreSource (X.portMap hc f) u v) := by
    rw [X.port_graph_source hc f u v]
    split_ifs
    · obtain ⟨α,β,hα,hβ,hInv,hRange,hCov⟩ := hF.covariant.radii (u ∘ X.labels) (v ∘ Fin.castAdd X.arity)
      exact (X.proper.clopen_fibres hv u).inter (hInv.isClopen hv)
    · exact isClopen_empty
  have hRange (u v) : IsClopen (graphFibreRange (X.portMap hc f) u v) := by
    rw [X.port_graph_range hc f u v]
    split_ifs
    · exact Y.proper.clopen_fibres hv v
    · exact isClopen_empty
  have hCont := X.port_continuous hc f hF.continuous
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv _ X.proper Y.proper hCont
      (fun u v => (hSource u v).isOpen) hRange) (X.port_bijective hc f hF.bijective.injective) hCont

end DiamondIntegral.Section6
