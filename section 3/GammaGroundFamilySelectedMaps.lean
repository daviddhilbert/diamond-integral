import «section 3».GammaGroundFamilyMaps
import «section 3».GammaGroundFamilyPartitions
import «section 3».GammaGroundMapRelations
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

/-- Definable finite tag selection and actual value maps assemble into
a complete same-ground family map, including all its branch graphs. -/
theorem gammaGroundFamilyMap_of_selected_values
    (A : GammaGroundFiniteFamily hc B P) (D : GammaGroundFiniteFamily hc B Q)
    (T : Fin A.tags → Fin D.tags → GammaGroundDefSet hc B P)
    (hcover : ∀ i (a : A.piece i), ∃! j, a.val ∈ (T i j).carrier)
    (h : ∀ i, GammaGroundMap (A.piece i) (GammaGroundDefSet.univ hc B Q))
    (hrange : ∀ i j (a : A.piece i), a.val ∈ (T i j).carrier → (h i a).val ∈ (D.piece j).carrier) :
    ∃ F : GammaGroundFamilyMap A D,
      (∀ i (a : A.piece i) j, (F.toFun ⟨i,a⟩).1 = j ↔ a.val ∈ (T i j).carrier) ∧
      ∀ i (a : A.piece i), (F.toFun ⟨i,a⟩).2.val = (h i a).val := by
  choose tag htag using fun i (a : A.piece i) => ExistsUnique.exists (hcover i a)
  let f : A.Carrier → D.Carrier := fun a =>
    ⟨tag a.1 a.2,⟨(h a.1 a.2).val,hrange a.1 (tag a.1 a.2) a.2 (htag a.1 a.2)⟩⟩
  have htagiff (i : Fin A.tags) (a : A.piece i) (j : Fin D.tags) :
      (f ⟨i,a⟩).1 = j ↔ a.val ∈ (T i j).carrier := by
    constructor
    · intro he
      exact he ▸ htag i a
    · intro hj
      exact (hcover i a).unique (htag i a) hj
  have hd : GammaGroundFamilyDefinable A D f := by
    intro i j
    have hh := (h i).graph_definable.inter ((T i j).definable.preimage (universalProductFst P Q B.real))
    apply GammaGroundDefinable.congr hh
    intro z
    constructor
    · rintro ⟨⟨a,ha,hv⟩,ht⟩
      have hat : a.val ∈ (T i j).carrier := ha.symm ▸ ht
      let b : D.piece j := ⟨(h i a).val,hrange i j a hat⟩
      refine ⟨a,b,ha,hv,?_⟩
      exact gammaGroundFamilyCarrier_ext D ((htagiff i a j).mpr hat) rfl
    · rintro ⟨a,b,ha,hb,hf⟩
      have htagj : (f ⟨i,a⟩).1 = j := congrArg Sigma.fst hf
      have hat := (htagiff i a j).mp htagj
      have hv : (h i a).val = b.val := congrArg (fun t : D.Carrier => t.2.val) hf
      refine ⟨⟨a,ha,hv.trans hb⟩,?_⟩
      change z.1 ∈ (T i j).carrier
      exact ha ▸ hat
  exact ⟨⟨f,hd⟩,htagiff,fun _ _ => rfl⟩

end DiamondIntegral.Section3
