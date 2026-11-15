import «section 5».MonomialEndpointSupports
import «section 5».FiniteGammaParameterControl
import «section 3».GammaGroundMapPreimages

/-! Literal full-RV lifts of cylindrical Gamma families given by actual
endpoint maps. Definability retains their full original-ground graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

def endpointFamilyTupleMap (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    GammaGroundMap (X.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin (shape.endpoints+1)))) :=
  GammaGroundMap.tuple (fun i => Fin.lastCases
    (GammaGroundMap.prodSnd X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (fun j => (f j).comp (GammaGroundMap.prodFst X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))) i)

theorem endpointFamilyTupleMap_value (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (a : X.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    (endpointFamilyTupleMap shape f a).val =
      Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M))
        (fun j => (f j ⟨a.val.1,a.property.1⟩).val) a.val.2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [endpointFamilyTupleMap, GammaGroundMap.tuple_value, Fin.lastCases_last,
      Fin.lastCases_castSucc, Fin.snoc_last, Fin.snoc_castSucc] <;> rfl

def endpointConditionSet (shape : CylinderFibreKind) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (shape.endpoints+1))) :=
  ⟨{z | shape.condition (Γ := Values.Gamma (M := M)) (z ∘ Fin.castSucc) (z (Fin.last shape.endpoints))},
    gammaGroundGammaPower_predicate_definable _
      (shape.condition_fullDefinable (B := B) Fin.castSucc (Fin.last shape.endpoints))⟩

def endpointGammaFamily (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :=
  (endpointFamilyTupleMap shape f).preimage (endpointConditionSet shape)

theorem endpointGammaFamily_mem (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (p : (Fin n → (CanonicalRV.RVSort M)ˣ) × Values.Gamma (M := M)) :
    p ∈ (endpointGammaFamily shape f).carrier ↔
      ∃ x : X, x.val = p.1 ∧ shape.condition (Γ := Values.Gamma (M := M)) (fun j => (f j x).val) p.2 := by
  constructor
  · rintro ⟨a, ha, he⟩
    subst p
    rw [endpointFamilyTupleMap_value] at he
    change shape.condition (Γ := Values.Gamma (M := M)) _ _ at he
    have hi : (Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M))
      (fun j => (f j ⟨a.val.1,a.property.1⟩).val) a.val.2) ∘ Fin.castSucc =
        (fun j => (f j ⟨a.val.1,a.property.1⟩).val) := by funext j; simp only [Function.comp_def, Fin.snoc_castSucc]
    rw [hi, Fin.snoc_last] at he
    exact ⟨⟨a.val.1,a.property.1⟩,rfl,he⟩
  · rintro ⟨x, hx, he⟩
    let a : X.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) := ⟨p,hx ▸ x.property,Set.mem_univ _⟩
    refine ⟨a,rfl,?_⟩
    rw [endpointFamilyTupleMap_value]
    change shape.condition (Γ := Values.Gamma (M := M)) _ _
    have hi : (Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M))
      (fun j => (f j ⟨a.val.1,a.property.1⟩).val) a.val.2) ∘ Fin.castSucc =
        (fun j => (f j ⟨a.val.1,a.property.1⟩).val) := by funext j; simp only [Function.comp_def, Fin.snoc_castSucc]
    rw [hi, Fin.snoc_last]
    have heq : (⟨a.val.1,a.property.1⟩ : X) = x := Subtype.ext hx.symm
    simpa only [heq] using he

def groundGammaCylinderLift (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1)) where
  carrier := {u | ∃ x : X, x.val = Fin.init u ∧
    shape.condition (Γ := Values.Gamma (M := M)) (fun j => (f j x).val) (rvUnitValueHom (u (Fin.last n)))}
  definable := by
    have h := (endpointGammaFamily shape f).definable.preimage (unitGraphInputValueMap hc B.real n)
    apply h.congr
    intro u
    exact endpointGammaFamily_mem shape f (Fin.init u, rvUnitValueHom (u (Fin.last n)))

theorem groundGammaCylinderLift_finite_partition (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    {ι : Type} [Fintype ι] (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint
      (groundGammaCylinderLift shape (fun k => (f k).restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩))).carrier
      (groundGammaCylinderLift shape (fun k => (f k).restrict (fun x hx => (hcov x).mpr ⟨j,hx⟩))).carrier) ∧
    ∀ u, u ∈ (groundGammaCylinderLift shape f).carrier ↔ ∃ i,
      u ∈ (groundGammaCylinderLift shape (fun k => (f k).restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩))).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro u ⟨x, hx, _⟩ ⟨y, hy, _⟩
    exact Set.disjoint_left.mp (hd i j hij) (hx ▸ x.property) (hy ▸ y.property)
  · intro u
    constructor
    · rintro ⟨x, hx, hc⟩
      obtain ⟨i, hi⟩ := (hcov x.val).mp x.property
      exact ⟨i, ⟨x.val,hi⟩, hx, hc⟩
    · rintro ⟨i, x, hx, hc⟩
      exact ⟨⟨x.val,(hcov x.val).mpr ⟨i,x.property⟩⟩,hx,hc⟩

end DiamondIntegral.Section5
