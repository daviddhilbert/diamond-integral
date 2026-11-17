import «section 3».GammaGroundRealFibres
import «section 3».GammaGroundRawLogic

/-! Specialize raw formula relations at a real parameter tuple while
keeping all original Gamma names. This applies to complete imaginary
code graphs as well as ordinary finite-row graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

def gammaRawParameterRelationMap (z : Fin p → M) :
    Map (DefSet.univ (rawTupleSpace LRV M (Fin a ⊕ Fin b)) (B.real ∪ Set.range z))
      (DefSet.univ (rawTupleSpace LRV M (Fin ((p+a)+b))) (B.real ∪ Set.range z)) := by
  let f := fun w : Fin a ⊕ Fin b → M => Fin.append (Fin.append z (w ∘ Sum.inl)) (w ∘ Sum.inr)
  have h : (B.real ∪ Set.range z).DefinableMap LRV f := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [f,Fin.append_left] using (show (B.real ∪ Set.range z).DefinableFun LRV (fun _ : Fin a ⊕ Fin b → M => z i) from
          LRV.definableFun_const _ (Or.inr (Set.mem_range_self i)))
      · simpa only [f,Fin.append_left,Fin.append_right,Function.comp_def] using
          (Set.DefinableFun.proj LRV : (B.real ∪ Set.range z).DefinableFun LRV (fun w : Fin a ⊕ Fin b → M => w (Sum.inl i)))
    · simpa only [f,Fin.append_right,Function.comp_def] using
        (Set.DefinableFun.proj LRV : (B.real ∪ Set.range z).DefinableFun LRV (fun w : Fin a ⊕ Fin b → M => w (Sum.inr i)))
  exact Map.ofCodes _ f f h (fun _ => Set.mem_univ _) (fun _ => rfl)

theorem gammaGroundRaw_relation_specialize
    {D : Set (Fin ((p+a)+b) → M)} (hD : GammaGroundRawDefinable hc B D) (z : Fin p → M) :
    GammaGroundRawDefinable hc ⟨B.real ∪ Set.range z,B.gamma⟩
      {w : Fin a ⊕ Fin b → M | Fin.append (Fin.append z (w ∘ Sum.inl)) (w ∘ Sum.inr) ∈ D} :=
  (hD.monoReal Set.subset_union_left).preimage (gammaRawParameterRelationMap (B := B) (a := a) (b := b) z)

end DiamondIntegral.Section3
