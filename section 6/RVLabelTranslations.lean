import «section 6».VFTupleArithmeticMaps
import «section 6».MixedVFProjectionMaps
import «section 6».SurjectiveMapDescent

/-! Actual translations whose displacement depends only on retained
RV labels. These are available for standard-contraction lifts, which
are allowed to be proper covariant homeomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def rvTranslationHead (p : A) : Fin n → VF M := fun i => p.val.1 i

def rvTranslationVector (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S)) (p : A) : Fin n → VF M :=
  (δ p).val

def rvLabelTranslationMap (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S)) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let H := (mixedVFHeadMap A).pair δ
  let D := (vfTupleBinaryMap S .add).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp H)
  exact (Map.inclusion (fun _ _ => Set.mem_univ _)).comp (D.pair (rvTailMap A))

def rvLabelTranslation (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S)) :=
  (rvLabelTranslationMap δ).toImage

theorem rvLabelTranslation_value (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S)) (p : A) :
    (rvLabelTranslation δ p).val=(rvTranslationHead p+rvTranslationVector δ p,p.val.2) := rfl

variable (δ : Map A (DefSet.univ (rawVFSpace (M := M) n) S))
variable (hδ : ∀ p z : A,p.val.2=z.val.2 → δ p=δ z)

include hδ in
theorem rvLabelTranslation_bijective : Function.Bijective (rvLabelTranslation δ) := by
  refine ⟨?_,map_toImage_surjective _⟩
  intro p z he
  have hTags : p.val.2=z.val.2 := congrArg (fun q => q.val.2) he
  have hValues := congrArg (fun q => q.val.1) he
  change rvTranslationHead p+rvTranslationVector δ p=rvTranslationHead z+rvTranslationVector δ z at hValues
  have hShift : rvTranslationVector δ p=rvTranslationVector δ z := congrArg Subtype.val (hδ p z hTags)
  rw [hShift] at hValues
  have hHead : rvTranslationHead p=rvTranslationHead z := add_right_cancel hValues
  exact Subtype.ext (Prod.ext hHead hTags)

include hδ in
theorem rvLabelTranslation_image_fibre (p : A) :
    vfFibre (rvLabelTranslationMap δ).image.carrier p.val.2=
      {x | (x-rvTranslationVector δ p,p.val.2) ∈ A.carrier} := by
  ext x
  constructor
  · rintro ⟨z,hz⟩
    change (rvTranslationHead z+rvTranslationVector δ z,z.val.2)=(x,p.val.2) at hz
    have hTags := congrArg (fun w : (Fin n → VF M) × (Fin r → RVInfinity M) => w.2) hz
    change z.val.2=p.val.2 at hTags
    have hValues : rvTranslationHead z+rvTranslationVector δ z=x :=
      congrArg (fun w : (Fin n → VF M) × (Fin r → RVInfinity M) => w.1) hz
    have hShift : rvTranslationVector δ z=rvTranslationVector δ p := congrArg Subtype.val (hδ z p hTags)
    rw [hShift] at hValues
    have hSource : z.val.1=x-rvTranslationVector δ p := (eq_sub_iff_add_eq).mpr hValues
    have hPoint : z.val=(x-rvTranslationVector δ p,p.val.2) := Prod.ext hSource hTags
    change (x-rvTranslationVector δ p,p.val.2) ∈ A.carrier
    exact hPoint ▸ z.property
  · intro hx
    let z : A := ⟨(x-rvTranslationVector δ p,p.val.2),hx⟩
    refine ⟨z,?_⟩
    change (rvTranslationHead z+rvTranslationVector δ z,z.val.2)=(x,p.val.2)
    have hShift : rvTranslationVector δ z=rvTranslationVector δ p := congrArg Subtype.val (hδ z p rfl)
    rw [hShift]
    change (x-rvTranslationVector δ p+rvTranslationVector δ p,p.val.2)=(x,p.val.2)
    rw [sub_add_cancel]

theorem rvLabelTranslation_graph_source (u v : Fin r → RVInfinity M) :
    graphFibreSource (rvLabelTranslation δ) u v=if u=v then vfFibre A.carrier u else ∅ := by
  ext x
  constructor
  · rintro ⟨y,p,hp,hfp⟩
    have hTags : u=v := (congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)
    rw [if_pos hTags]
    change (x,u) ∈ A.carrier
    exact hp ▸ p.property
  · intro hx
    split_ifs at hx with hTags
    · let p : A := ⟨(x,u),hx⟩
      exact ⟨x+rvTranslationVector δ p,p,rfl,Prod.ext rfl hTags⟩
    · exact False.elim hx

theorem rvLabelTranslation_graph_range (u v : Fin r → RVInfinity M) :
    graphFibreRange (rvLabelTranslation δ) u v=
      if u=v then vfFibre (rvLabelTranslationMap δ).image.carrier v else ∅ := by
  ext y
  constructor
  · rintro ⟨x,p,hp,hfp⟩
    have hTags : u=v := (congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)
    rw [if_pos hTags]
    change (y,v) ∈ (rvLabelTranslationMap δ).image.carrier
    exact hfp ▸ (rvLabelTranslation δ p).property
  · intro hy
    split_ifs at hy with hTags
    · obtain ⟨p,hp⟩ := hy
      have hpTags : p.val.2=u := (congrArg Prod.snd hp).trans hTags.symm
      exact ⟨p.val.1,p,Prod.ext rfl hpTags,hp⟩
    · exact False.elim hy

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

include hδ in
theorem rvLabelTranslation_chart (hA : ProperInvariant S A.carrier)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    IsVFChartAt (rvLabelTranslation δ) p (fun x => x+rvTranslationVector δ p) := by
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hA.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨ρ,fun x hx => ⟨hρ hx,?_⟩⟩
  change (rvLabelTranslation δ ⟨(x,p.val.2),hρ hx⟩).val=_
  rw [rvLabelTranslation_value,rvLabelTranslation_value]
  have hShift : rvTranslationVector δ ⟨(x,p.val.2),hρ hx⟩=rvTranslationVector δ p :=
    congrArg Subtype.val (hδ _ p rfl)
  rw [hShift]
  rfl

include hδ in
theorem rvLabelTranslation_unit_derivative (hA : ProperInvariant S A.carrier)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    HasMixedUnitDerivativeAt (rvLabelTranslation δ) p := by
  obtain ⟨L,hL,hDet⟩ := hasUnitJacobianAt_translation (rvTranslationVector δ p) p.val.1
  exact ⟨L,⟨_,rvLabelTranslation_chart δ hδ hA hv p,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hDet⟩

end DiamondIntegral.Section6
