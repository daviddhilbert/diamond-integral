import «section 6».TransportedGammaLevels

/-! Exact inverse graph fibres and Gamma-level transport for arbitrary
retained-label selectors, including prefix membership grafts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem selected_inverse_tags (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (π i) = p.val.2 i) (q : B) :
    (f.inverse hf q).val.2 = fun i => q.val.2 (π i) := by
  funext i
  have he := congrArg (fun z : B => z.val.2 (π i)) (Map.apply_inverse f hf q)
  exact (hRetain (f.inverse hf q) i).symm.trans he

theorem selected_inverse_fiber_source (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (π i) = p.val.2 i)
    (v : Fin s → RVInfinity M) :
    graphFibreSource (f.inverse hf) v (fun i => v (π i)) = vfFibre B.carrier v := by
  ext x
  constructor
  · rintro ⟨a,q,hqx,_⟩
    change (x,v) ∈ B.carrier
    rw [← hqx]
    exact q.property
  · intro hx
    let q : B := ⟨(x,v),hx⟩
    exact ⟨(f.inverse hf q).val.1,q,rfl,Prod.ext rfl (selected_inverse_tags f hf π hRetain q)⟩

theorem selected_inverse_point (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (π i) = p.val.2 i)
    (v : Fin s → RVInfinity M) (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) :
    (f.inverse hf ⟨(x,v),hx⟩).val =
      (graphFibreMap (f.inverse hf) v (fun i => v (π i)) x,fun i => v (π i)) := by
  let q : B := ⟨(x,v),hx⟩
  have hTags := selected_inverse_tags f hf π hRetain q
  have hSource : x ∈ graphFibreSource (f.inverse hf) v (fun i => v (π i)) := by
    rw [selected_inverse_fiber_source f hf π hRetain]
    exact hx
  have hGraph : graphFibre (f.inverse hf) v (fun i => v (π i)) x (f.inverse hf q).val.1 :=
    ⟨q,rfl,Prod.ext rfl hTags⟩
  exact Prod.ext (graphFibre_functional (f.inverse hf) v _ hGraph
    (graphFibreMap_graph (f.inverse hf) v _ hSource)) hTags

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem transported_gamma_levels_open_selected (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (π i) = p.val.2 i)
    (hCont : ContinuousOnGraphFibres (f.inverse hf))
    (hBOpen : ∀ v, IsOpen (vfFibre B.carrier v))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    ∀ v γ, IsOpen {b : Fin m → VF M | (b,v) ∈ B.carrier ∧
      gammaFormExtension (ω.comp (f.inverse hf)) (b,v) = γ} := by
  intro v γ
  let u : Fin r → RVInfinity M := fun i => v (π i)
  let g := graphFibreMap (f.inverse hf) v u
  have hg : ContinuousOn g (vfFibre B.carrier v) := by
    have hc := hCont v u
    rw [selected_inverse_fiber_source f hf π hRetain v] at hc
    exact hc
  have hInput (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) : (g x,u) ∈ A.carrier := by
    have hp := (f.inverse hf ⟨(x,v),hx⟩).property
    rwa [selected_inverse_point f hf π hRetain v x hx] at hp
  have hValue (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) :
      gammaFormExtension (ω.comp (f.inverse hf)) (x,v) = gammaFormExtension ω (g x,u) := by
    have hc := gammaFormExtension_comp_at ω (f.inverse hf) (⟨(x,v),hx⟩ : B)
    rw [selected_inverse_point f hf π hRetain v x hx] at hc
    exact hc
  have hEq : {x : Fin m → VF M | (x,v) ∈ B.carrier ∧
      gammaFormExtension (ω.comp (f.inverse hf)) (x,v) = γ} =
      vfFibre B.carrier v ∩ g ⁻¹' {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      exact ⟨hx,hInput x hx,(hValue x hx).symm.trans hγ⟩
    · rintro ⟨hx,_,hγ⟩
      exact ⟨hx,(hValue x hx).trans hγ⟩
  rw [hEq]
  exact hg.isOpen_inter_preimage (hBOpen v) (hLevels u γ)

end DiamondIntegral.Section6
