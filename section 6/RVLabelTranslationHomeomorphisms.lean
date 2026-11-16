import «section 6».RVLabelTranslations

/-! A labelwise translation on a proper source is a proper covariant
homeomorphism whenever its actual image is VF bounded. The proof uses
the full clopen graph fibres and retains every original RV label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S))
variable (hδ : ∀ p z : A,p.val.2=z.val.2 → δ p=δ z)

include hδ in
theorem rvLabelTranslation_image_clopen
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hA : ProperInvariant S A.carrier) (u : Fin r → RVInfinity M) :
    IsClopen (vfFibre (rvLabelTranslationMap δ).image.carrier u) := by
  by_cases hu : (vfFibre A.carrier u).Nonempty
  · obtain ⟨a,ha⟩ := hu
    let p : A := ⟨(a,u),ha⟩
    change IsClopen (vfFibre (rvLabelTranslationMap δ).image.carrier p.val.2)
    rw [rvLabelTranslation_image_fibre δ hδ p]
    exact (hA.clopen_fibres hv u).preimage (continuous_id.sub continuous_const)
  · have he : vfFibre (rvLabelTranslationMap δ).image.carrier u=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨p,hp⟩
      change (rvTranslationHead p+rvTranslationVector δ p,p.val.2)=(x,u) at hp
      have hTags := congrArg (fun w : (Fin n → VF M) × (Fin r → RVInfinity M) => w.2) hp
      change p.val.2=u at hTags
      exact hu ⟨p.val.1,hTags ▸ p.property⟩
    rw [he]
    exact isClopen_empty

include hδ in
theorem rvLabelTranslation_continuous : ContinuousOnGraphFibres (rvLabelTranslation δ) := by
  intro u v
  by_cases hu : (graphFibreSource (rvLabelTranslation δ) u v).Nonempty
  · obtain ⟨a,ha⟩ := hu
    obtain ⟨p,hp,_⟩ := graphFibreMap_graph (rvLabelTranslation δ) u v ha
    apply (continuous_id.add (continuous_const (y := rvTranslationVector δ p))).continuousOn.congr
    intro x hx
    obtain ⟨z,hz,hfz⟩ := graphFibreMap_graph (rvLabelTranslation δ) u v hx
    have hTags : z.val.2=p.val.2 := (congrArg Prod.snd hz).trans (congrArg Prod.snd hp).symm
    have hValue : rvTranslationHead z+rvTranslationVector δ z=graphFibreMap (rvLabelTranslation δ) u v x := congrArg Prod.fst hfz
    have hShift : rvTranslationVector δ z=rvTranslationVector δ p := congrArg Subtype.val (hδ z p hTags)
    rw [hShift] at hValue
    exact hValue.symm.trans (congrArg (fun b => b+rvTranslationVector δ p) (congrArg Prod.fst hz))
  · rw [Set.not_nonempty_iff_eq_empty.mp hu]
    exact continuousOn_empty (graphFibreMap (rvLabelTranslation δ) u v)

theorem rvLabelTranslation_image_rvBounded (hA : RVSupportDoublyBounded A.carrier) :
    RVSupportDoublyBounded (rvLabelTranslationMap δ).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hγ p.val p.property i

include hδ in
theorem rvLabelTranslation_image_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hA : ProperInvariant S A.carrier) (hBound : VFBounded (rvLabelTranslationMap δ).image.carrier) :
    ProperInvariant S (rvLabelTranslationMap δ).image.carrier :=
  (lemma_6_5 h00 hc hκ hs hv _ (rvLabelTranslationMap δ).image.definable hBound
    (rvLabelTranslation_image_rvBounded δ hA.rvBounded)).mpr (rvLabelTranslation_image_clopen δ hδ hv hA)

include hδ in
theorem rvLabelTranslation_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier) (hBound : VFBounded (rvLabelTranslationMap δ).image.carrier) :
    ProperCovariantHomeomorphism (rvLabelTranslation δ) := by
  have hB := rvLabelTranslation_image_proper δ hδ h00 hc hκ hs hv hA hBound
  have hSource (u v : Fin r → RVInfinity M) : IsOpen (graphFibreSource (rvLabelTranslation δ) u v) := by
    rw [rvLabelTranslation_graph_source]
    split_ifs
    · exact (hA.clopen_fibres hv u).isOpen
    · exact isOpen_empty
  have hRange (u v : Fin r → RVInfinity M) : IsClopen (graphFibreRange (rvLabelTranslation δ) u v) := by
    rw [rvLabelTranslation_graph_range]
    split_ifs
    · exact hB.clopen_fibres hv v
    · exact isClopen_empty
  have hCov := properCovariant_of_clopen_ranges h00 hc hκ hs hv (rvLabelTranslation δ) hA hB
    (rvLabelTranslation_continuous δ hδ) hSource hRange
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (rvLabelTranslation δ) hCov (rvLabelTranslation_bijective δ hδ) (rvLabelTranslation_continuous δ hδ)

end DiamondIntegral.Section6
