import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSyntaxBridge
import Section4.RelationFibres
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
variable {P Q : Space LRV M}
theorem GammaGroundDefinable.monoReal {T : Set M} {A : Set P.Carrier}
    (hA : GammaGroundDefinable hc ground P A) (hT : ground.real ⊆ T) :
    GammaGroundDefinable hc ⟨T, ground.gamma⟩ P A := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.mono hT⟩

def realPointInsertMap (P Q : Space LRV M) (S : Set M) (c : Q.domain) :
    Map (DefSet.univ P (S ∪ Set.range c.val))
      (DefSet.univ (P.prod Q) (S ∪ Set.range c.val)) := by
  let T := S ∪ Set.range c.val
  let F (z : P.Index → M) : P.Index ⊕ Q.Index → M := Sum.elim z c.val
  have hF : T.DefinableMap LRV F := by
    intro i
    cases i with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i => exact LRV.definableFun_const P.Index (Or.inr (Set.mem_range_self i))
  exact Map.ofCodes _ (fun x => (x, Q.decode c)) F hF
    (fun d => ⟨d.property, c.property⟩) (fun _ => rfl)

theorem GammaGroundDefinable.fibreRealPoint {A : Set (P.prod Q).Carrier}
    (hA : GammaGroundDefinable hc ground (P.prod Q) A) (c : Q.domain) :
    GammaGroundDefinable hc ⟨ground.real ∪ Set.range c.val, ground.gamma⟩ P
      {x | (x, Q.decode c) ∈ A} :=
  (hA.monoReal Set.subset_union_left).preimage (realPointInsertMap P Q ground.real c)

def GammaGroundMap.fibre {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
    (f : GammaGroundMap A B) (b : B) (c : Q.domain) (hcb : Q.decode c = b.val) :
    GammaGroundDefSet hc ⟨ground.real ∪ Set.range c.val, ground.gamma⟩ P where
  carrier := {x | ∃ a : A, a.val = x ∧ f a = b}
  definable := by
    apply (f.graph_definable.fibreRealPoint c).congr
    intro x
    constructor
    · rintro ⟨a, ha, he⟩
      exact ⟨a, ha, Subtype.ext (he.trans hcb)⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨a, ha, (congrArg Subtype.val he).trans hcb.symm⟩

theorem GammaGroundMap.fibre_finite {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
    (f : GammaGroundMap A B) (hf : f.FiniteFibres) (b : B) (c : Q.domain) (hcb : Q.decode c = b.val) :
    (f.fibre b c hcb).carrier.Finite := by
  apply ((hf b).image (fun a : A => a.val)).subset
  rintro x ⟨a, ha, he⟩
  exact ⟨a, he, ha⟩
end DiamondIntegral.Section3
