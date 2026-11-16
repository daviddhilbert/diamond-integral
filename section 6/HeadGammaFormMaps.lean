import «section 6».GammaFormFreezing
import «section 6».FibrePreparationBases

/-! Actual Gamma forms on the head-coordinate fibres, over exactly the
original base with that VF head adjoined. Complete graphs and open level
sets are inherited without adjoining any Gamma or RV representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}

variable {P : SpecialTransformations.DefinableGeometry.Space LRV M}

def gammaFormExtendParameters {A : DefSet P S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hST : S ⊆ T) :
    Map (⟨A.carrier,Space.Definable.mono P A.definable hST⟩ : DefSet P T) (DefSet.univ (rawGammaPresentation (M := M)) T) :=
  ⟨fun p => ⟨(ω ⟨p.val,p.property⟩).val,Set.mem_univ _⟩,Space.RelationDefinable.mono P rawGammaPresentation ω.graph_definable hST⟩

def headFibreEmbedding
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (a : VF M) :
    Map ((headFibreTemplate A).fibre (fun _ => a.val))
      (⟨A.carrier,Space.Definable.mono (rawMixedSpace (n+1) r) A.definable Set.subset_union_left⟩ :
        DefSet (rawMixedSpace (M := M) (n+1) r) (S ∪ Set.range (fun _ : Fin 1 => a.val))) := by
  let C := (headFibreTemplate A).fibre (fun _ => a.val)
  let U := S ∪ Set.range (fun _ : Fin 1 => a.val)
  let e (p : Mixed M n r) : Mixed M (n+1) r := (Fin.cons a p.1,p.2)
  let F (z : Fin n ⊕ Fin r → M) : Fin (n+1) ⊕ Fin r → M :=
    Sum.elim (Fin.cons a.val (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hF : U.DefinableMap LRV F := by
    rintro (i | i)
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self (0 : Fin 1)))
      · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have he (p : Mixed M n r) : mixedValues (e p)=F (mixedValues p) := by
    funext i
    cases i with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr i => rfl
  have hcode (z : (rawMixedSpace (M := M) n r).domain) :
      mixedValues (e ((rawMixedSpace n r).decode z))=F z.val :=
    (he _).trans (congrArg F (mixedValues_decode z))
  have hdom (z : (rawMixedSpace (M := M) n r).domain) :
      F z.val ∈ (rawMixedSpace (M := M) (n+1) r).domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  let g := Map.ofCodes (Q := rawMixedSpace (M := M) (n+1) r) C e F hF hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))
  exact g.corestrict (fun p => (mem_headFibreTemplate_iff A a p.val).mp p.property)

theorem headFibreEmbedding_value
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (a : VF M)
    (p : (headFibreTemplate A).fibre (fun _ => a.val)) :
    (headFibreEmbedding A a p).val=(Fin.cons a p.val.1,p.val.2) := rfl

def headGammaFormMap {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : VF M) :
    Map ((headFibreTemplate A).fibre (fun _ => a.val))
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range (fun _ : Fin 1 => a.val))) :=
  (gammaFormExtendParameters ω Set.subset_union_left).comp (headFibreEmbedding A a)

theorem headGammaFormMap_value {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : VF M)
    (p : (headFibreTemplate A).fibre (fun _ => a.val)) :
    (headGammaFormMap ω a p).val=(ω ⟨(Fin.cons a p.val.1,p.val.2),
      (mem_headFibreTemplate_iff A a p.val).mp p.property⟩).val := rfl

theorem headGammaFormMap_levels_open
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : VF M)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier ∧
      gammaFormExtension (headGammaFormMap ω a) (x,u)=γ} := by
  intro u γ
  have he : {x : Fin n → VF M | (x,u) ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier ∧
      gammaFormExtension (headGammaFormMap ω a) (x,u)=γ}=
      (fun x : Fin n → VF M => Fin.cons a x) ⁻¹'
        {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      have hAx := (mem_headFibreTemplate_iff A a (x,u)).mp hx
      refine ⟨hAx,?_⟩
      rw [gammaFormExtension_at _ ⟨_,hx⟩,headGammaFormMap_value] at hγ
      rw [gammaFormExtension_at _ ⟨_,hAx⟩]
      exact hγ
    · rintro ⟨hx,hγ⟩
      have hCx := (mem_headFibreTemplate_iff A a (x,u)).mpr hx
      refine ⟨hCx,?_⟩
      rw [gammaFormExtension_at _ ⟨_,hCx⟩,headGammaFormMap_value]
      rw [gammaFormExtension_at _ ⟨_,hx⟩] at hγ
      exact hγ
  rw [he]
  exact (hLevels u γ).preimage (by fun_prop)

end DiamondIntegral.Section6
