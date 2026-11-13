import «section 3».GammaGroundFamilyValueMaps
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {A : GammaGroundFiniteFamily hc B P} {D : GammaGroundFiniteFamily hc B Q}

def GammaGroundFamilyMap.branchGraph (F : GammaGroundFamilyMap A D) (i : Fin A.tags) (j : Fin D.tags) :
    GammaGroundDefSet hc B (P.prod Q) :=
  ⟨{z | gammaGroundFamilyGraph A D F.toFun i j z.1 z.2},F.definable i j⟩

def GammaGroundFamilyMap.branchSource (F : GammaGroundFamilyMap A D) (i : Fin A.tags) (j : Fin D.tags) :
    GammaGroundDefSet hc B P :=
  (GammaGroundMap.ofGlobal (F.branchGraph i j) (GammaGroundDefSet.univ hc B P)
    (universalProductFst P Q B.real) (fun _ => Set.mem_univ _)).image

theorem GammaGroundFamilyMap.mem_branchSource (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) (x : P.Carrier) :
    x ∈ (F.branchSource i j).carrier ↔
      ∃ a : A.piece i, a.val = x ∧ ∃ b : D.piece j, F.toFun ⟨i,a⟩ = ⟨j,b⟩ := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨a,b,ha,_,hf⟩ := z.property
    exact ⟨a,ha.trans hz,b,hf⟩
  · rintro ⟨a,ha,b,hf⟩
    exact ⟨⟨(a.val,b.val),a,b,rfl,rfl,hf⟩,ha⟩

theorem GammaGroundFamilyMap.branchSource_subset (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) : (F.branchSource i j).carrier ⊆ (A.piece i).carrier := by
  intro x hx
  obtain ⟨a,ha,_⟩ := (F.mem_branchSource i j x).mp hx
  exact ha ▸ a.property

theorem GammaGroundFamilyMap.mem_branchSource_iff_tag (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) (a : A.piece i) :
    a.val ∈ (F.branchSource i j).carrier ↔ (F.toFun ⟨i,a⟩).1 = j := by
  rw [F.mem_branchSource]
  constructor
  · rintro ⟨a',ha',b,hf⟩
    have he : a' = a := Subtype.ext ha'
    subst a'
    exact congrArg Sigma.fst hf
  · intro hj
    cases hf : F.toFun ⟨i,a⟩ with
    | mk j' b =>
      rw [hf] at hj
      change j' = j at hj
      subst j'
      exact ⟨a,rfl,b,hf⟩

/-- Actual target tags give a finite disjoint partition of each source
piece; no encoding parameters or extra points are chosen. -/
theorem GammaGroundFamilyMap.branchSource_partition (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (a : A.piece i) : ∃! j, a.val ∈ (F.branchSource i j).carrier := by
  refine ⟨(F.toFun ⟨i,a⟩).1,(F.mem_branchSource_iff_tag i _ a).mpr rfl,?_⟩
  intro j hj
  exact ((F.mem_branchSource_iff_tag i j a).mp hj).symm

end DiamondIntegral.Section3
