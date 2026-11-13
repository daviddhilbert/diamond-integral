import «section 3».MeasuredTensorRankLayerTwoSidedCovers
import «section 3».MeasuredSourceGridMatching
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}
variable {L R : GammaGroundMeasuredTensorRankLayer hc B k m}
variable {F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain}
namespace GammaGroundMeasuredTensorRankLayerTwoSidedCover

abbrev Seed (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount) :=
  Σ j : Fin R.topCount, {e // e ∈ C.patches i j}

def seed (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount)
    (a : Fin (Fintype.card (C.Seed i))) : C.Seed i := (Fintype.equivFin (C.Seed i)).symm a

def seedTarget (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount)
    (a : Fin (Fintype.card (C.Seed i))) : Fin R.topCount := (C.seed i a).1

def seedMatch (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount)
    (a : Fin (Fintype.card (C.Seed i))) :
    GammaGroundMeasuredTensorLocalMatch F (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.weight i) (L.weight_definable i)
      (R.residue (C.seedTarget i a)) (R.gamma (C.seedTarget i a)) (R.unmeasured.topMap (C.seedTarget i a)) (R.weight (C.seedTarget i a)) (R.weight_definable (C.seedTarget i a)) :=
  (C.seed i a).2.val

def gridMatching (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount) :=
  gammaGroundMeasuredTensorSourceGridMatching F (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.weight i) (L.weight_definable i)
    (fun a => R.residue (C.seedTarget i a)) (fun a => R.gamma (C.seedTarget i a))
      (fun a => R.unmeasured.topMap (C.seedTarget i a))
        (fun a => R.weight (C.seedTarget i a)) (fun a => R.weight_definable (C.seedTarget i a)) (C.seedMatch i)

abbrev Cell (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (i : Fin L.topCount) :=
  GammaGroundMeasuredTensorSourceGridMatching.Cell (E := C.seedMatch i)

abbrev MatchedIndex (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) := Σ i : Fin L.topCount, C.Cell i

def sourceBox (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) :=
  gammaGroundTensorGridBox (L.residue c.1) (L.gamma c.1)
    (fun a => (C.seedMatch c.1 a).source.residue) (fun a => (C.seedMatch c.1 a).source.gamma) c.2.val

def targetParent (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) : Fin R.topCount :=
  C.seedTarget c.1 ((C.gridMatching c.1).targetIndex c.2)

def targetBox (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) :
    GammaGroundTensorBox (R.residue (C.targetParent c)) (R.gamma (C.targetParent c)) :=
  (C.gridMatching c.1).target c.2

def data (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) :
    GammaGroundMeasuredTensorBoxMatch F (L.residue c.1) (L.gamma c.1) (L.unmeasured.topMap c.1) (L.weight c.1) (L.weight_definable c.1)
      (R.residue (C.targetParent c)) (R.gamma (C.targetParent c)) (R.unmeasured.topMap (C.targetParent c)) (R.weight (C.targetParent c)) (R.weight_definable (C.targetParent c))
        (C.sourceBox c) (C.targetBox c) :=
  (C.gridMatching c.1).data c.2

def sourceMap (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) :=
  (L.unmeasured.topMap c.1).comp (C.sourceBox c).inclusion

def targetMap (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) (c : C.MatchedIndex) :=
  (R.unmeasured.topMap (C.targetParent c)).comp (C.targetBox c).inclusion

theorem matched_congruence (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :
    gammaGroundMeasuredCoefficientCongruence (∑ c : C.MatchedIndex, (C.sourceBox c).measuredValue (L.weight c.1) (L.weight_definable c.1))
      (∑ c : C.MatchedIndex, (C.targetBox c).measuredValue (R.weight (C.targetParent c)) (R.weight_definable (C.targetParent c))) :=
  gammaGroundMeasuredCoefficientCongruence.finsetSum Finset.univ (fun c _ => (C.data c).congruence)

theorem sourceMap_disjoint (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (c d : C.MatchedIndex) (hcd : c ≠ d) :
    Disjoint (C.sourceMap c).image.carrier (C.sourceMap d).image.carrier := by
  rcases c with ⟨i,c⟩
  rcases d with ⟨j,d⟩
  by_cases hij : i = j
  · subst j
    exact (C.gridMatching i).forget.sourceMap_disjoint (L.unmeasured.topMap_injective i) c d
      (fun he => hcd (congrArg (Sigma.mk i) he))
  · apply (L.unmeasured.topMap_disjoint i j hij).mono
    · rintro z ⟨v,hv⟩
      exact ⟨(C.sourceBox ⟨i,c⟩).inclusion v,hv⟩
    · rintro z ⟨v,hv⟩
      exact ⟨(C.sourceBox ⟨j,d⟩).inclusion v,hv⟩

theorem targetMap_disjoint (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (c d : C.MatchedIndex) (hcd : c ≠ d) :
    Disjoint (C.targetMap c).image.carrier (C.targetMap d).image.carrier :=
  gammaGroundMatchedImages_disjoint F (fun c => (C.data c).data.bijection) C.sourceMap C.targetMap
    (fun c u => (C.data c).data.agrees u) c d (C.sourceMap_disjoint c d hcd)

theorem source_seed_cover (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (i : Fin L.topCount) (u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i)) :
    (∃ a, u.val ∈ (C.seedMatch i a).source.source.carrier) ∨
      ∃ h ∈ C.sourceHyperplanes i, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  rcases C.source_cover i u with ⟨j,e,he,hu⟩ | hu
  · let s : C.Seed i := ⟨j,e,he⟩
    let a := Fintype.equivFin (C.Seed i) s
    have ha : C.seed i a = s := (Fintype.equivFin (C.Seed i)).symm_apply_apply s
    refine Or.inl ⟨a,?_⟩
    change u.val ∈ (C.seed i a).2.val.source.source.carrier
    have hh := congrArg (fun v : C.Seed i => v.2.val.source.source.carrier) ha
    rw [hh]
    exact hu
  · exact Or.inr hu
end GammaGroundMeasuredTensorRankLayerTwoSidedCover
end DiamondIntegral.Section3
