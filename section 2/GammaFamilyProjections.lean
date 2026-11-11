import «section 2».UniformGammaSuprema

/-! Existential source projections of a Gamma-valued family retain the
remaining real coordinates and the complete output Gamma-code fibre. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def projectedGammaFamily (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (π : Fin m → Fin n) (y : Fin m → M) : Set (Gamma M) :=
  {γ | ∃ x ∈ D, x ∘ π = y ∧ γ ∈ P x}

theorem rawGammaFamilyGraph_source_projection_definable (S : Set M)
    (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P)) (π : Fin m → Fin n) :
    S.Definable LRV (rawGammaFamilyGraph ((fun x => x ∘ π) '' D) (projectedGammaFamily D P π)) := by
  let idx : Fin m ⊕ Fin 1 → Fin n ⊕ Fin 1 := Sum.map π id
  convert hP.image_comp idx using 1
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,x,hx,hxz,hγ⟩
    let w : Fin n ⊕ Fin 1 → M := Sum.elim x (fun _ => z (.inr 0))
    refine ⟨w,⟨hx,hzNZ,hγ⟩,?_⟩
    funext j
    cases j with
    | inl j => exact congrFun hxz j
    | inr j => fin_cases j; rfl
  · rintro ⟨w,⟨hwD,hwNZ,hwγ⟩,hwz⟩
    have hxz : (w ∘ Sum.inl) ∘ π = z ∘ Sum.inl := by
      funext j
      exact congrFun hwz (.inl j)
    have hout : w (.inr 0) = z (.inr 0) := congrFun hwz (.inr 0)
    exact ⟨⟨w ∘ Sum.inl,hwD,hxz⟩,hout ▸ hwNZ,w ∘ Sum.inl,hwD,hxz,hout ▸ hwγ⟩

end DiamondIntegral.Section2
