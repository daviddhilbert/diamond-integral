import «section 6».ProperGraphChartContinuity
import «section 6».RVGraftingHomeomorphism
import «section 6».RVTagProjection
import «section 6».MixedVFProjectionMaps
import «section 6».TupleCoordinateMaps

/-! Actual original-base scalar charts for every source and target
RV label of a mixed map. Grafting the output labels supplies a definable
chart domain; zero extension is the actual fixed-label graph map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

def graphChartDomain (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :=
  (graftMap hc (rvProjection f)).image

theorem graphChartDomain_fibre (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (w : Fin (r+s) → RVInfinity M) :
    vfFibre (graphChartDomain hc f).carrier w=
      graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) := by
  ext x
  rw [graphChartDomain,graft_image_fibre,graft_range_eq_source,graft_source_iff,rvProjection_source]
  exact and_iff_right rfl

def graphChartScalarMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) (j : Fin m) :
    Map (graphChartDomain hc f) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleSelectMap S (fun _ : Fin 1 => j)).comp
    ((mixedVFHeadMap B).comp (f.comp ((graft hc (rvProjection f)).inverse (graft_bijective hc (rvProjection f)))))

theorem graphChartScalarMap_graft (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (j : Fin m) (p : A) :
    (graphChartScalarMap hc f j (graft hc (rvProjection f) p)).val=fun _ => (f p).val.1 j := by
  funext i
  change (f ((graft hc (rvProjection f)).inverse (graft_bijective hc (rvProjection f))
    (graft hc (rvProjection f) p))).val.1 j=(f p).val.1 j
  rw [Map.inverse_apply]

theorem totalGraphChartScalar_value (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (j : Fin m) (w : Fin (r+s) → RVInfinity M) (x : Fin n → VF M) :
    totalFocusFibre (graphChartScalarMap hc f j) w x=
      fun _ => graphFibreMap f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) x j := by
  let u := w ∘ Fin.castAdd s
  let v := w ∘ Fin.natAdd r
  by_cases hx : x ∈ graphFibreSource f u v
  · have hxD : (x,w) ∈ (graphChartDomain hc f).carrier :=
      (Set.ext_iff.mp (graphChartDomain_fibre hc f w) x).mpr hx
    obtain ⟨y,p,hp,hfp⟩ := hx
    have hPoint : (graft hc (rvProjection f) p).val=(x,w) := by
      have hInput := congrArg Prod.snd hp
      have hOutput := congrArg Prod.snd hfp
      rw [graft_apply]
      change (p.val.1,Fin.append p.val.2 (f p).val.2)=(x,w)
      rw [hInput,hOutput]
      have hVF := congrArg Prod.fst hp
      exact Prod.ext hVF Fin.append_castAdd_natAdd
    have hTyped : (⟨(x,w),hxD⟩ : graphChartDomain hc f)=graft hc (rvProjection f) p :=
      Subtype.ext hPoint.symm
    rw [totalFocusFibre_at _ w x hxD,hTyped,graphChartScalarMap_graft]
    have hTarget : (f p).val.2=v := congrArg Prod.snd hfp
    have hGraph : graphFibre f u v x (f p).val.1 := ⟨p,hp,Prod.ext rfl hTarget⟩
    have hMap : graphFibreMap f u v x=(f p).val.1 :=
      graphFibre_functional f u v (graphFibreMap_graph f u v ⟨y,p,hp,hfp⟩) hGraph
    exact congrArg (fun b : Fin m → VF M => fun _ : Fin 1 => b j) hMap.symm
  · have hxD : (x,w) ∉ (graphChartDomain hc f).carrier := fun h =>
      hx ((Set.ext_iff.mp (graphChartDomain_fibre hc f w) x).mp h)
    rw [totalFocusFibre_off _ w x hxD]
    change (0 : Fin 1 → VF M)=(fun _ => graphFibreMap f u v x j)
    simp only [graphFibreMap,dite_eq_right hx,Pi.zero_apply]
    rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem totalGraphChartScalar_continuous
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hF : ProperCovariantHomeomorphism f) (j : Fin m)
    (w : Fin (r+s) → RVInfinity M) :
    Continuous (totalFocusFibre (graphChartScalarMap hc f j) w) := by
  have he : totalFocusFibre (graphChartScalarMap hc f j) w=
      fun x => fun _ : Fin 1 => graphFibreMap f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) x j :=
    funext (totalGraphChartScalar_value hc f j w)
  rw [he]
  exact continuous_pi (fun _ => (continuous_apply j).comp (hF.graphFibreMap_continuous hv _ _))

end DiamondIntegral.Section6
