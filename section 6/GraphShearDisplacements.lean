import «section 6».DefinableGraphChartFamilies
import «section 6».ShearDisplacementCalculus
import «section 6».SurjectiveMapDescent
import «section 6».VFTupleArithmeticMaps
import «section 6».VFProjection

/-! The active displacement of an actual stable shear descends to
its inactive VF coordinates and the two full RV label tuples. This
is an original-base definable map, constructed from the actual graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}

def graphChartOriginal (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :
    Map (graphChartDomain hc f) A :=
  (graft hc (rvProjection f)).inverse (graft_bijective hc (rvProjection f))

theorem graphChartOriginal_recovery (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (q : graphChartDomain hc f) : graft hc (rvProjection f) (graphChartOriginal hc f q)=q :=
  Map.apply_inverse _ _ q

theorem graphChartOriginal_vf (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (q : graphChartDomain hc f) : (graphChartOriginal hc f q).val.1=q.val.1 :=
  congrArg (fun z : graphChartDomain hc f => z.val.1) (graphChartOriginal_recovery hc f q)

theorem graphChartOriginal_input_tag (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (q : graphChartDomain hc f) (i : Fin r) :
    (graphChartOriginal hc f q).val.2 i=q.val.2 (Fin.castAdd s i) := by
  have h := congrArg (fun z : graphChartDomain hc f => z.val.2 (Fin.castAdd s i)) (graphChartOriginal_recovery hc f q)
  simpa only [graft_apply,Fin.append_left] using h

theorem graphChartOriginal_output_tag (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (q : graphChartDomain hc f) (i : Fin s) :
    (f (graphChartOriginal hc f q)).val.2 i=q.val.2 (Fin.natAdd r i) := by
  have h := congrArg (fun z : graphChartDomain hc f => z.val.2 (Fin.natAdd r i)) (graphChartOriginal_recovery hc f q)
  simpa only [graft_apply,Fin.append_right,rvProjection_apply] using h

def graphShearDisplacementMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :
    Map (graphChartDomain hc f) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let F := graphChartScalarMap hc f (Fin.last n)
  let X := (vfTupleSelectMap S (fun _ : Fin 1 => Fin.last n)).comp (mixedVFHeadMap (graphChartDomain hc f))
  exact (vfTupleBinaryMap S .sub).comp (F.pair X).toUniv

theorem graphShearDisplacementMap_graft (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (p : A) :
    (graphShearDisplacementMap hc f (graft hc (rvProjection f) p)).val 0=
      (f p).val.1 (Fin.last n)-p.val.1 (Fin.last n) := by
  change (graphChartScalarMap hc f (Fin.last n) (graft hc (rvProjection f) p)).val 0-
    (graft hc (rvProjection f) p).val.1 (Fin.last n)=_
  rw [graphChartScalarMap_graft,graft_apply]

theorem graphShearDisplacementMap_original (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (q : graphChartDomain hc f) :
    (graphShearDisplacementMap hc f q).val 0=
      (f (graphChartOriginal hc f q)).val.1 (Fin.last n)-(graphChartOriginal hc f q).val.1 (Fin.last n) := by
  have h := graphShearDisplacementMap_graft hc f (graphChartOriginal hc f q)
  rw [graphChartOriginal_recovery] at h
  exact h

theorem graphShearDisplacementMap_factors (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (hStable : SameLabelShearDisplacement f (Fin.last n))
    (p q : graphChartDomain hc f)
    (hEq : (vfDropLast (graphChartDomain hc f)).toImage p=(vfDropLast (graphChartDomain hc f)).toImage q) :
    graphShearDisplacementMap hc f p=graphShearDisplacementMap hc f q := by
  have hBase : Fin.init p.val.1=Fin.init q.val.1 :=
    congrArg (fun z : (vfDropLast (graphChartDomain hc f)).image => z.val.1) hEq
  have hTags : p.val.2=q.val.2 :=
    congrArg (fun z : (vfDropLast (graphChartDomain hc f)).image => z.val.2) hEq
  have hInput : (graphChartOriginal hc f p).val.2=(graphChartOriginal hc f q).val.2 := by
    funext i
    rw [graphChartOriginal_input_tag,graphChartOriginal_input_tag,hTags]
  have hOutput : (f (graphChartOriginal hc f p)).val.2=(f (graphChartOriginal hc f q)).val.2 := by
    funext i
    rw [graphChartOriginal_output_tag,graphChartOriginal_output_tag,hTags]
  have hInactive (i : Fin (n+1)) : i ≠ Fin.last n →
      (graphChartOriginal hc f p).val.1 i=(graphChartOriginal hc f q).val.1 i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact (hi rfl).elim
    · intro _
      rw [graphChartOriginal_vf,graphChartOriginal_vf]
      exact congrFun hBase j
  apply Subtype.ext
  funext i
  have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rw [graphShearDisplacementMap_original,graphShearDisplacementMap_original]
  exact hStable _ _ hInput hOutput hInactive

def graphShearBaseDisplacement (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (hStable : SameLabelShearDisplacement f (Fin.last n)) :
    Map (vfDropLast (graphChartDomain hc f)).image (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  descendSurjectiveMap (vfDropLast (graphChartDomain hc f)).toImage (map_toImage_surjective _)
    (graphShearDisplacementMap hc f) (graphShearDisplacementMap_factors hc f hStable)

theorem graphShearBaseDisplacement_factor (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (hStable : SameLabelShearDisplacement f (Fin.last n)) (q : graphChartDomain hc f) :
    graphShearBaseDisplacement hc f hStable ((vfDropLast (graphChartDomain hc f)).toImage q)=
      graphShearDisplacementMap hc f q :=
  descendSurjectiveMap_factor _ _ _ _ q

end DiamondIntegral.Section6
