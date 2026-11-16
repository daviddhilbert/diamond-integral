import «section 6».UnaryFiniteFieldImages

/-! The complete original-base graph of paired source and target VF
coordinates of an actual unary map, retaining all old RV parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def unaryFieldPairMap (f : Map A B) : Map A (DefSet.univ (rawVFSpace (M := M) 2) S) := by
  let P := (rawMixedSpace (M := M) 1 r).prod (rawMixedSpace (M := M) 1 s)
  let F (z : ((Fin 1 ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin s)) → M) : Fin 2 → M :=
    ![z (.inl (.inl 0)),z (.inr (.inl 0))]
  have hCode (c : P.domain) : vfValues (![(P.decode c).1.1 0,(P.decode c).2.1 0])=F c.val := by
    have hLeft := mixedValues_decode
      (⟨c.val ∘ Sum.inl,c.property.1⟩ : (rawMixedSpace (M := M) 1 r).domain)
    have hRight := mixedValues_decode
      (⟨c.val ∘ Sum.inr,c.property.2⟩ : (rawMixedSpace (M := M) 1 s).domain)
    funext i
    fin_cases i
    · exact congrFun hLeft (.inl 0)
    · exact congrFun hRight (.inl 0)
  let H : Map (A.prod B) (DefSet.univ (rawVFSpace (M := M) 2) S) := Map.ofCodes (A.prod B)
    (fun p => ![p.1.1 0,p.2.1 0]) F
    (by
      change S.DefinableMap LRV F
      intro i
      fin_cases i <;> exact Set.DefinableFun.proj LRV)
    (fun c => ⟨![(P.decode c).1.1 0,(P.decode c).2.1 0],hCode c⟩)
    (by
      intro c
      apply vfValues_injective
      exact (vfValues_decode _).trans (hCode c).symm)
  exact H.comp ((Map.id A).pair f)

theorem unaryFieldPairMap_value (f : Map A B) (p : A) :
    (unaryFieldPairMap f p).val=![p.val.1 0,(f p).val.1 0] := rfl

theorem unaryFieldPairMap_image_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hE : (Prod.fst '' E.carrier).Finite) : ((unaryFieldPairMap f).restrict hEA).image.carrier.Finite := by
  have hImage := unaryFieldImage_finite hc hκ hs hsmall f E.carrier hE
  apply ((hE.prod hImage).image (fun p => ![p.1 0,p.2 0])).subset
  rintro y ⟨p,rfl⟩
  exact ⟨(p.val.1,(f ⟨p.val,hEA p.property⟩).val.1),
    ⟨⟨p.val,p.property,rfl⟩,⟨⟨p.val,hEA p.property⟩,p.property,rfl⟩⟩,rfl⟩

end DiamondIntegral.Section6
