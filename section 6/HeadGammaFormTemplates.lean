import «section 6».HeadGammaFormMaps

/-! One original-base full Gamma template specializes to the actual
form on every head fibre, including empty fibres. The actual head is the
only additional parameter of a specialization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def headGammaFormCodeIndex : ((Fin (n+1) ⊕ Fin r) ⊕ Fin 1) → Fin 1 ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) :=
  Sum.elim (fun i => Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) (headFibreCodeIndex i)) (Sum.inr ∘ Sum.inr)

def headGammaFormTemplate {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    GammaFormParameterTemplate (M := M) S 1 n r :=
  ⟨{z | z ∘ headGammaFormCodeIndex ∈ sumMixedGammaGraph A.carrier (gammaFormExtension ω)},
    (sumMixedGammaGraph_definable A.carrier (gammaFormExtension ω)
      (gammaFormExtension_graph_definable ω)).preimage_comp headGammaFormCodeIndex⟩

theorem headGammaFormExtension_at {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : VF M)
    (x : (headFibreTemplate A).fibre (fun _ => a.val)) :
    gammaFormExtension (headGammaFormMap ω a) x.val=gammaFormExtension ω (Fin.cons a x.val.1,x.val.2) := by
  rw [gammaFormExtension_at,headGammaFormMap_value,
    gammaFormExtension_at ω ⟨_,(mem_headFibreTemplate_iff A a x.val).mp x.property⟩]

theorem headGammaFormTemplate_section {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : VF M) :
    {z | Sum.elim (fun _ : Fin 1 => a.val) z ∈ (headGammaFormTemplate ω).graph}=
      (rawMixedSpace n r).relation rawGammaPresentation (headGammaFormMap ω a).graph := by
  have he : (rawMixedSpace n r).relation rawGammaPresentation (headGammaFormMap ω a).graph=
      sumMixedGammaGraph ((headFibreTemplate A).fibre (fun _ => a.val)).carrier
        (gammaFormExtension (headGammaFormMap ω a)) :=
    sumMixedGammaGraph_eq_relation _ (headGammaFormMap ω a).toFun _
      (fun x => (gammaFormExtension_at (headGammaFormMap ω a) x).symm)
  rw [he]
  ext z
  constructor
  · rintro ⟨hγ,p,hp,hpc,hVal⟩
    have hHead : p.1 0=a := by
      apply Subtype.ext
      exact congrFun hpc (.inl 0)
    let x : Mixed M n r := (Fin.tail p.1,p.2)
    have hxFull : (Fin.cons a x.1,x.2)=p := by
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        exact hHead.symm
      · rfl
    have hx : x ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
      apply (mem_headFibreTemplate_iff A a x).mpr
      exact hxFull.symm ▸ hp
    refine ⟨hγ,x,hx,?_,?_⟩
    · funext i
      cases i with
      | inl i => exact congrFun hpc (.inl i.succ)
      | inr i => exact congrFun hpc (.inr i)
    · have hValue := headGammaFormExtension_at ω a ⟨x,hx⟩
      rw [hxFull] at hValue
      exact hVal.trans hValue.symm
  · rintro ⟨hγ,x,hx,hxc,hVal⟩
    let p : Mixed M (n+1) r := (Fin.cons a x.1,x.2)
    have hp : p ∈ A.carrier := (mem_headFibreTemplate_iff A a x).mp hx
    refine ⟨hγ,p,hp,?_,?_⟩
    · funext i
      cases i with
      | inl i =>
        refine Fin.cases rfl (fun j => ?_) i
        exact congrFun hxc (.inl j)
      | inr i => exact congrFun hxc (.inr i)
    · exact hVal.trans (headGammaFormExtension_at ω a ⟨x,hx⟩)

end DiamondIntegral.Section6
