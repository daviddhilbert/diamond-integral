import «section 6».RVCoordinateDisplacements
import «section 6».RetainedUnaryHomeChains

/-! A full map whose VF displacement is fixed by its final RV labels
is a translation on each actual graph fibre. Proper covariance then
gives an identity total derivative on every point of that fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def mapVFDisplacement (f : Map A B) (p : A) : Fin n → VF M :=
  fun i => (f p).val.1 i-p.val.1 i

theorem graphFibreMap_eq_translation_of_rv_displacements
    (f : Map A B) (hD : ∀ i,RVCoordinateDisplacement f i)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (p : A) (hpv : (f p).val.2=v) :
    Set.EqOn (graphFibreMap f u v) (fun x => x+mapVFDisplacement f p) (graphFibreSource f u v) := by
  intro x hx
  obtain ⟨a,ha,hfa⟩ := graphFibreMap_graph f u v hx
  have hTags : (f a).val.2=(f p).val.2 := (congrArg Prod.snd hfa).trans hpv.symm
  funext i
  have hInput : a.val.1 i=x i := congrArg (fun w : Mixed M n r => w.1 i) ha
  have hOutput : (f a).val.1 i=graphFibreMap f u v x i := congrArg (fun w : Mixed M n s => w.1 i) hfa
  change graphFibreMap f u v x i=x i+mapVFDisplacement f p i
  rw [← hOutput]
  calc
    (f a).val.1 i=((f a).val.1 i-a.val.1 i)+a.val.1 i := (sub_add_cancel _ _).symm
    _=x i+mapVFDisplacement f p i := by rw [hD i a p hTags,hInput]; exact add_comm _ _

theorem graphFibreRange_translation_of_rv_displacements
    (f : Map A B) (hD : ∀ i,RVCoordinateDisplacement f i)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (p : A) (hpv : (f p).val.2=v) :
    graphFibreRange f u v=(fun x => x+mapVFDisplacement f p) '' graphFibreSource f u v := by
  rw [graphFibreRange_eq_image]
  exact (graphFibreMap_eq_translation_of_rv_displacements f hD u v p hpv).image_eq

theorem injective_of_rv_displacements
    (f : Map A B) (π : Fin r → Fin s) (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (hD : ∀ i,RVCoordinateDisplacement f i) : Function.Injective f := by
  intro p z he
  have hTags : (f p).val.2=(f z).val.2 := congrArg (fun q => q.val.2) he
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have h := hD i p z hTags
    have hOut : (f p).val.1 i=(f z).val.1 i := congrArg (fun q => q.val.1 i) he
    rw [hOut] at h
    exact sub_right_inj.mp h
  · funext i
    exact (hRetain p i).symm.trans ((congrFun hTags (π i)).trans (hRetain z i))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_of_rv_displacements
    (f : Map A B) (hD : ∀ i,RVCoordinateDisplacement f i) : ContinuousOnGraphFibres f := by
  intro u v
  by_cases hNE : (graphFibreSource f u v).Nonempty
  · obtain ⟨x,hx⟩ := hNE
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v hx
    exact (continuous_id.add_const (mapVFDisplacement f p)).continuousOn.congr
      (graphFibreMap_eq_translation_of_rv_displacements f hD u v p (congrArg Prod.snd hfp))
  · rw [Set.not_nonempty_iff_eq_empty.mp hNE]
    exact continuousOn_empty _

theorem graphFibreRange_clopen_of_rv_displacements
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hD : ∀ i,RVCoordinateDisplacement f i)
    (hSource : ∀ u v,IsClopen (graphFibreSource f u v)) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsClopen (graphFibreRange f u v) := by
  by_cases hNE : (graphFibreSource f u v).Nonempty
  · obtain ⟨x,hx⟩ := hNE
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v hx
    rw [graphFibreRange_translation_of_rv_displacements f hD u v p (congrArg Prod.snd hfp)]
    exact ⟨(Homeomorph.addRight (mapVFDisplacement f p)).isClosedMap _ (hSource u v).isClosed,
      (Homeomorph.addRight (mapVFDisplacement f p)).isOpenMap _ (hSource u v).isOpen⟩
  · rw [graphFibreRange_eq_image,Set.not_nonempty_iff_eq_empty.mp hNE,Set.image_empty]
    exact isClopen_empty

theorem unit_derivative_of_rv_displacements
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hCov : ProperCovariant f) (hD : ∀ i,RVCoordinateDisplacement f i) (p : A) :
    HasMixedUnitDerivativeAt f p := by
  obtain ⟨α,β,hα,hβ,hSource,hRange,hCovar⟩ := hCov.radii p.val.2 (f p).val.2
  have hp : p.val.1 ∈ graphFibreSource f p.val.2 (f p).val.2 := ⟨(f p).val.1,p,rfl,rfl⟩
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1 ((hSource.isClopen hv).isOpen.mem_nhds hp)
  have hChart : IsVFChartAt f p (fun x => x+mapVFDisplacement f p) := by
    refine ⟨ρ,fun x hx => ?_⟩
    obtain ⟨y,a,ha,hfa⟩ := hρ hx
    have hxA : (x,p.val.2) ∈ A.carrier := ha ▸ a.property
    have hA : (⟨(x,p.val.2),hxA⟩ : A)=a := Subtype.ext ha.symm
    refine ⟨hxA,?_⟩
    rw [hA]
    apply Prod.ext
    · have hGraph := graphFibreMap_eq_translation_of_rv_displacements f hD p.val.2 (f p).val.2 p rfl (hρ hx)
      have hFunction : graphFibreMap f p.val.2 (f p).val.2 x=y :=
        graphFibre_functional f p.val.2 (f p).val.2 (graphFibreMap_graph f _ _ (hρ hx)) ⟨a,ha,hfa⟩
      exact (congrArg Prod.fst hfa).trans (hFunction.symm.trans hGraph)
    · have hTags := congrArg Prod.snd hfa
      exact hTags
  obtain ⟨L,hL,hDet⟩ := hasUnitJacobianAt_translation (mapVFDisplacement f p) p.val.1
  exact ⟨L,⟨_,hChart,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hDet⟩

end DiamondIntegral.Section6
