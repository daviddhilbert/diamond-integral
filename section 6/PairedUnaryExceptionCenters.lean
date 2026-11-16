import «section 6».UnaryFieldPairMaps

/-! Pair the finite ordinary exceptional projections under the actual
bijection, including both images and inverse images. The whole paired
center set and its full graph remain over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def pairedUnaryExceptionDomain (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S) :
    DefSet (rawMixedSpace (M := M) 1 r) S :=
  ⟨E.carrier ∪ {q | ∃ p : A,p.val=q ∧ (f p).val ∈ F.carrier},
    E.definable.union _ (f.definable_preimage F.definable)⟩

theorem pairedUnaryExceptionDomain_subset (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier) : (pairedUnaryExceptionDomain f E F).carrier ⊆ A.carrier := by
  rintro q (hq | ⟨p,rfl,_⟩)
  · exact hEA hq
  · exact p.property

theorem mem_pairedUnaryExceptionDomain (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S) (p : A) :
    p.val ∈ (pairedUnaryExceptionDomain f E F).carrier ↔ p.val ∈ E.carrier ∨ (f p).val ∈ F.carrier := by
  constructor
  · rintro (h | ⟨a,ha,hF⟩)
    · exact Or.inl h
    · have he : a=p := Subtype.ext ha
      exact Or.inr (he ▸ hF)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨p,rfl,h⟩

def pairedUnaryExceptionCenters (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier) : DefSet (rawVFSpace (M := M) 2) S :=
  ((unaryFieldPairMap f).restrict (pairedUnaryExceptionDomain_subset f E F hEA)).image

theorem mem_pairedUnaryExceptionCenters (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier) (q : Fin 2 → VF M) :
    q ∈ (pairedUnaryExceptionCenters f E F hEA).carrier ↔
      ∃ p : A,(p.val ∈ E.carrier ∨ (f p).val ∈ F.carrier) ∧ ![p.val.1 0,(f p).val.1 0]=q := by
  constructor
  · rintro ⟨a,ha⟩
    let p : A := ⟨a.val,pairedUnaryExceptionDomain_subset f E F hEA a.property⟩
    exact ⟨p,(mem_pairedUnaryExceptionDomain f E F p).mp a.property,ha⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨⟨p.val,(mem_pairedUnaryExceptionDomain f E F p).mpr hp⟩,he⟩

theorem pairedUnaryExceptionCenters_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier) (hFB : F.carrier ⊆ B.carrier)
    (hE : (Prod.fst '' E.carrier).Finite) (hF : (Prod.fst '' F.carrier).Finite) :
    (pairedUnaryExceptionCenters f E F hEA).carrier.Finite := by
  have hLeft := unaryFieldPairMap_image_finite hc hκ hs hsmall f E hEA hE
  have hRight := unaryFieldPairMap_image_finite hc hκ hs hsmall (f.inverse hf) F hFB hF
  apply (hLeft.union (hRight.image (fun q => ![q 1,q 0]))).subset
  intro q hq
  obtain ⟨p,hp,rfl⟩ := (mem_pairedUnaryExceptionCenters f E F hEA q).mp hq
  rcases hp with hE | hF
  · exact Or.inl ⟨⟨p.val,hE⟩,rfl⟩
  · apply Or.inr
    refine ⟨![(f p).val.1 0,p.val.1 0],?_,rfl⟩
    refine ⟨⟨(f p).val,hF⟩,?_⟩
    change ![(f p).val.1 0,(f.inverse hf (f p)).val.1 0]=_
    rw [Map.inverse_apply]

end DiamondIntegral.Section6
