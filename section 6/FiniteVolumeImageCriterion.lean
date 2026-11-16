import «section 6».RVLastCoordinateReplacement

/-! A finite-volume criterion for actual coordinate pivots. A fixed
prefix and finitely many last coordinates give finitely many volume
values; a finite-to-one original volume then gives a finite fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem finite_rv_tuples_of_fixed_prefix
    (T : Set (Fin (n+1) → RVInfinity M)) (a : Fin n → RVInfinity M)
    (hPrefix : ∀ t ∈ T, Fin.init t = a)
    (hLast : ((fun t : Fin (n+1) → RVInfinity M => (t (Fin.last n)).val) '' T).Finite) : T.Finite := by
  apply Set.Finite.of_finite_image hLast
  intro t ht s hs he
  have hpre : Fin.init t = Fin.init s := (hPrefix t ht).trans (hPrefix s hs).symm
  funext i
  refine Fin.lastCases (Subtype.ext he) (fun j => congrFun hpre j) i

theorem finite_fibres_of_finite_volume_images
    {P Q R : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}
    (f : Map A B) (g : Map A C) (hf : f.FiniteFibres)
    (hImage : ∀ c : C, (f '' {a : A | g a = c}).Finite) : g.FiniteFibres := by
  intro c
  apply ((hImage c).biUnion (fun b _ => hf b)).subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨f a,Set.mem_iUnion.mpr ⟨⟨a,ha,rfl⟩,rfl⟩⟩

end DiamondIntegral.Section6
