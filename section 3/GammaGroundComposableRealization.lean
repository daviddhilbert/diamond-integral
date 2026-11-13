import «section 3».GammaGroundMapRealization

/-! Two composable same-ground maps have a common small real
interpretation, with their original VF coefficient field preserved. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q R U : Space LRV M}
variable {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
variable {C : GammaGroundDefSet hc ground U}

structure GammaGroundComposableRealization (f : GammaGroundMap A B) (g : GammaGroundMap B C) (T : Set M) where
  source : Q.Definable T A.carrier
  middle : R.Definable T B.carrier
  target : U.Definable T C.carrier
  firstGraph : (Q.prod R).Definable T {z | ∃ a : A, a.val = z.1 ∧ (f a).val = z.2}
  secondGraph : (R.prod U).Definable T {z | ∃ b : B, b.val = z.1 ∧ (g b).val = z.2}

def GammaGroundComposableRealization.first {f : GammaGroundMap A B} {g : GammaGroundMap B C}
    {T : Set M} (H : GammaGroundComposableRealization f g T) : Map ⟨A.carrier, H.source⟩ ⟨B.carrier, H.middle⟩ :=
  ⟨f.toFun, (relationDefinable_iff_product _).mpr H.firstGraph⟩

def GammaGroundComposableRealization.second {f : GammaGroundMap A B} {g : GammaGroundMap B C}
    {T : Set M} (H : GammaGroundComposableRealization f g T) : Map ⟨B.carrier, H.middle⟩ ⟨C.carrier, H.target⟩ :=
  ⟨g.toFun, (relationDefinable_iff_product _).mpr H.secondGraph⟩

theorem gammaGround_composable_realization (f : GammaGroundMap A B) (g : GammaGroundMap B C)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ) :
    ∃ T : Set M, ground.real ⊆ T ∧ Cardinal.mk T < κ ∧
      vfParameterField T = vfParameterField ground.real ∧ Nonempty (GammaGroundComposableRealization f g T) := by
  let P : Fin 5 → Space LRV M := ![Q, R, U, Q.prod R, R.prod U]
  let D : ∀ i, Set (P i).Carrier := Fin.cases A.carrier (Fin.cases B.carrier (Fin.cases C.carrier
    (Fin.cases {z | ∃ a : A, a.val = z.1 ∧ (f a).val = z.2}
      (Fin.cases {z | ∃ b : B, b.val = z.1 ∧ (g b).val = z.2} (fun i => i.elim0)))))
  have hD : ∀ i, GammaGroundDefinable hc ground (P i) (D i) := by
    intro i
    fin_cases i
    · exact A.definable
    · exact B.definable
    · exact C.definable
    · exact f.graph_definable
    · exact g.graph_definable
  obtain ⟨T, hT, hs, hf, hd⟩ := GammaGroundDefinable.realizeFinite P D hD hκ hS
  exact ⟨T, hT, hs, hf, ⟨⟨hd 0, hd 1, hd 2, hd 3, hd 4⟩⟩⟩

end DiamondIntegral.Section3
