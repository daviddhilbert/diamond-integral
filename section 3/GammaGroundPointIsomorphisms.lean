import «section 5».NativeGammaPointBridge
import IntegrationSection5.GammaMapPresentation

/-! Actual native Gamma-ground mixed bijections retain the complete
inherited-point Gamma graph and retain the same map in the universal real
presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaGroundPointIso
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)} (f : GammaGroundBijection A C) :
    GammaIso B A.carrier C.carrier where
  equiv := Equiv.ofBijective f.map f.bijective
  graph := by
    have h := Section5.nativeMixedGraph_definable f
    have he : Section5.nativeMixedGraph f = {w | ∃ p q,
        (∃ a : A, a.val = p ∧ (f.map a).val = q) ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = w} := by
      ext w
      constructor
      · rintro ⟨a,ha⟩
        exact ⟨a.val,(f.map a).val,⟨a,rfl,rfl⟩,ha.symm⟩
      · rintro ⟨p,q,⟨a,ha,hb⟩,hw⟩
        exact ⟨a,((congrArg₂ Fin.append (congrArg Section5.nativeMixedCode ha)
          (congrArg Section5.nativeMixedCode hb)).trans hw).symm⟩
    change DefinableOverBase B _ _
    exact Eq.mp (congrArg (fun D => DefinableOverBase B (Fin.append (gammaPointSort n r) (gammaPointSort m s)) D) he) h

def gammaGroundPointMap
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n r}
    {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ m s}
    (hA : GammaSetDefinable B (carrier A)) (hC : GammaSetDefinable B (carrier C))
    (f : GammaGroundBijection (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)
      (Section5.nativeGammaPointDomain (carrier C) hC)) : Map A C :=
  @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ Set.univ A C f.map (by
    obtain ⟨d,t,ht⟩ := (gammaGroundPointIso f).graph.real_specialize
    exact @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
      (pointSpace n r) (pointSpace m s) (B.real ∪ Set.range (rawTuple t)) Set.univ _ ht (Set.subset_univ _))

end DiamondIntegral.Section3
