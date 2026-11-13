import «section 3».RVVariableRelabel
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {I R V W M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvDNFRelabel (f : V ≃ W) (D : LiteralDNF I R V) : LiteralDNF I R W :=
  D.map (fun C => C.map (rvLiteralRelabel f))

theorem rvDNFRelabel_comparison (f : V ≃ W) (D : LiteralDNF I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    PolarityDNF.holds (RVLiteral.comparison a r y) (rvDNFRelabel f D) ↔
      PolarityDNF.holds (RVLiteral.comparison a r (y ∘ f)) D := by
  constructor
  · rintro ⟨Cout,hCout,hcomp⟩
    change Cout ∈ D.map (fun C => C.map (rvLiteralRelabel f)) at hCout
    obtain ⟨C,hC,hCC⟩ := List.mem_map.mp hCout
    subst Cout
    refine ⟨C,hC,?_⟩
    intro L hL
    exact (rvLiteralRelabel_comparison f L a r y).mp
      (hcomp _ (List.mem_map.mpr ⟨L,hL,rfl⟩))
  · rintro ⟨C,hC,hcomp⟩
    refine ⟨C.map (rvLiteralRelabel f),List.mem_map.mpr ⟨C,hC,rfl⟩,?_⟩
    intro Lout hLout
    obtain ⟨L,hL,hLL⟩ := List.mem_map.mp hLout
    subst Lout
    exact (rvLiteralRelabel_comparison f L a r y).mpr (hcomp L hL)

theorem rvDNFRelabel_certified (f : V ≃ W) (D : LiteralDNF I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M)
    (hD : LiteralDNF.Certified a r (y ∘ f) D) : LiteralDNF.Certified a r y (rvDNFRelabel f D) := by
  intro Cout hCout hcomp Lout hLout
  change Cout ∈ D.map (fun C => C.map (rvLiteralRelabel f)) at hCout
  obtain ⟨C,hC,hCC⟩ := List.mem_map.mp hCout
  subst Cout
  obtain ⟨L,hL,hLL⟩ := List.mem_map.mp hLout
  subst Lout
  apply (rvLiteralRelabel_domain f L a r y).mpr
  apply hD C hC ?_ L hL
  intro T hT
  exact (rvLiteralRelabel_comparison f T a r y).mp
    (hcomp _ (List.mem_map.mpr ⟨T,hT,rfl⟩))
end DiamondIntegral.Section3
