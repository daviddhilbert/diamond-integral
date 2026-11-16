import «section 6».OpenRVLabelBounds
import «section 6».RVGraftingHomeomorphism
import «section 6».RVLabelCovariance
import «section 6».RVTagProjection

/-! Open nonzero labels construct their own proper covariance and
bounded target support. A retained input selector identifies every
actual target fibre with one fixed-label graph range. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem open_nonzero_rv_labels_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {D : DefSet (rawMixedSpace (M := M) 0 q) S}
    (τ : Map A D) (hA : ProperInvariant S A.carrier)
    (hOpen : ∀ u v,IsOpen (graphFibreSource τ u v))
    (hNZ : ∀ p : A,∀ i,((τ p).val.2 i).val ≠ iRVZero) : ProperCovariant τ :=
  properCovariant_RV_labels_of_open h00 hc hκ hs hv τ hA
    (open_rv_labels_doublyBounded h00 hc linear hκ hs hv hsmall hΓ τ hA hOpen hNZ) hOpen

theorem target_rvBounded_of_open_nonzero_labels
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hSurj : Function.Surjective f) (hA : ProperInvariant S A.carrier)
    (hOpen : ∀ u v,IsOpen (graphFibreSource f u v))
    (hNZ : ∀ p : A,∀ i,((f p).val.2 i).val ≠ iRVZero) : RVSupportDoublyBounded B.carrier := by
  have hO (u v) : IsOpen (graphFibreSource (rvProjection f) u v) := by
    rw [rvProjection_source]
    exact hOpen u v
  have hN (p : A) (i : Fin s) : ((rvProjection f p).val.2 i).val ≠ iRVZero := by
    simpa only [rvProjection_apply] using hNZ p i
  obtain ⟨γ,hγ⟩ := open_rv_labels_doublyBounded h00 hc linear hκ hs hv hsmall hΓ (rvProjection f) hA hO hN
  refine ⟨γ,?_⟩
  intro b hb i
  obtain ⟨p,hp⟩ := hSurj ⟨b,hb⟩
  have h := hγ (rvProjection f p).val ⟨p,rfl⟩ i
  simpa only [rvProjection_apply,hp] using h

theorem retained_target_fibre_eq_graphRange
    (f : Map A B) (hSurj : Function.Surjective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (v : Fin s → RVInfinity M) :
    vfFibre B.carrier v=graphFibreRange f (v ∘ π) v := by
  ext b
  constructor
  · intro hb
    obtain ⟨p,hp⟩ := hSurj ⟨(b,v),hb⟩
    have hInput : p.val.2=v ∘ π := by
      funext i
      exact (hRetain p i).symm.trans (congrArg (fun q : B => q.val.2 (π i)) hp)
    exact ⟨p.val.1,p,Prod.ext rfl hInput,congrArg Subtype.val hp⟩
  · rintro ⟨a,p,hp,hfp⟩
    change (b,v) ∈ B.carrier
    exact hfp ▸ (f p).property

end DiamondIntegral.Section6
