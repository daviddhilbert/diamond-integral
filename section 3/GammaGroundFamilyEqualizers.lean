import «section 3».GammaGroundFamilyBranchSources
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

def GammaGroundFamilyMap.branchEqualizer (F G : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) : GammaGroundDefSet hc B P :=
  (GammaGroundMap.ofGlobal ((F.branchGraph i j).inter (G.branchGraph i j))
    (GammaGroundDefSet.univ hc B P) (universalProductFst P Q B.real) (fun _ => Set.mem_univ _)).image

/-- Equalizers of actual finite-family maps compare their entire tagged
outputs, not just the underlying value tuples. -/
def GammaGroundFamilyMap.equalizerPiece (F G : GammaGroundFamilyMap A D) (i : Fin A.tags) :
    GammaGroundDefSet hc B P :=
  ⟨⋃ j, (F.branchEqualizer G i j).carrier,
    GammaGroundDefinable.iUnion (fun j => (F.branchEqualizer G i j).definable)⟩

theorem GammaGroundFamilyMap.mem_equalizerPiece (F G : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (x : P.Carrier) :
    x ∈ (F.equalizerPiece G i).carrier ↔
      ∃ a : A.piece i, a.val = x ∧ F.toFun ⟨i,a⟩ = G.toFun ⟨i,a⟩ := by
  constructor
  · intro hx
    obtain ⟨j,z,hz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a,b,ha,hb,hF⟩ := z.property.1
    obtain ⟨c,d,hc,hd,hG⟩ := z.property.2
    have hca : c = a := Subtype.ext (hc.trans ha.symm)
    have hdb : d = b := Subtype.ext (hd.trans hb.symm)
    subst c
    subst d
    exact ⟨a,ha.trans hz,hF.trans hG.symm⟩
  · rintro ⟨a,ha,he⟩
    let v := F.toFun ⟨i,a⟩
    apply Set.mem_iUnion.mpr
    refine ⟨v.1,⟨(a.val,v.2.val),?_,?_⟩,ha⟩
    · exact ⟨a,v.2,rfl,rfl,rfl⟩
    · exact ⟨a,v.2,rfl,rfl,he.symm⟩

theorem GammaGroundFamilyMap.equalizerPiece_subset (F G : GammaGroundFamilyMap A D)
    (i : Fin A.tags) : (F.equalizerPiece G i).carrier ⊆ (A.piece i).carrier := by
  intro x hx
  obtain ⟨a,ha,_⟩ := (F.mem_equalizerPiece G i x).mp hx
  exact ha ▸ a.property

theorem GammaGroundFamilyMap.mem_equalizerPiece_at (F G : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (a : A.piece i) :
    a.val ∈ (F.equalizerPiece G i).carrier ↔ F.toFun ⟨i,a⟩ = G.toFun ⟨i,a⟩ := by
  rw [F.mem_equalizerPiece]
  constructor
  · rintro ⟨b,hb,he⟩
    have hba : b = a := Subtype.ext hb
    exact hba ▸ he
  · exact fun he => ⟨a,rfl,he⟩

end DiamondIntegral.Section3
