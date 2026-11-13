import «section 3».RVAngularQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

theorem coordinate_full_fibre (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ A)
    (u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ)
    (hu : rvUnitTupleValues u = rvUnitTupleValues (E.coordinateEquiv K x).2) :
    (E.coordinateEquiv K).symm ((E.coordinateEquiv K x).1,u) ∈ A := by
  have hh := E.coordinateImage_fibre_invariant K (E.coordinateEquiv K x).1 (E.coordinateEquiv K x).2 u
    ⟨x,hx,rfl⟩ hu.symm
  obtain ⟨y,hy,he⟩ := hh
  exact (((E.coordinateEquiv K).symm_apply_apply y).symm.trans
    (congrArg (E.coordinateEquiv K).symm he)) ▸ hy
end RVAngularCell
end DiamondIntegral.Section3
