import «section 5».NativeRVLabelGraphs
import «section 5».NativeMixedCodeRealization
import IntegrationSection6.GammaTupleCodes

/-! The local full imaginary-name predicates give precisely the original
Gamma domain and volume graphs used by the completed [18] RV categories. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem groundPointCode_sorted {n m : ℕ} (p : Point (M := M) n m) :
    gammaPointCode p ∈ sortedUniverse (gammaPointSort n m) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [gammaPointSort,gammaPointCode,Fin.append_left,sortEval,iVF,vfAt] using (p.1 j).property
  · simpa only [gammaPointSort,gammaPointCode,Fin.append_right,sortEval,iRV] using (p.2 j).property

theorem groundDefinable_univ {Q : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) : Q.Definable Set.univ A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  obtain ⟨c,hcγ⟩ := ((volumeGammaSpace hc).power (Fin k)).onto γ
  exact (hA.over_real_code c hcγ).mono _ (Set.subset_univ _)

theorem groundRV_gamma_set {a : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) :
    GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D.carrier} := by
  have hW := (rawDomain_definable D).preimage_real (gammaPointSort 0 a) (Fin.natAdd 0)
  have h := gamma_set_of_sorted_formula hW
  convert h using 1
  ext p
  have he : gammaPointCode p ∘ Fin.natAdd 0 = rvValues p.2 := by
    funext i
    simp only [Function.comp_apply,gammaPointCode,Fin.append_right,rvValues]
  change (p.2 ∈ D.carrier) ↔ (_ ∈ rawDomain D ∧ _)
  rw [he]
  constructor
  · intro hp
    exact ⟨⟨p.2,hp,rfl⟩,groundPointCode_sorted p⟩
  · rintro ⟨⟨t,ht,he⟩,_⟩
    exact rvValues_injective he ▸ ht

def groundRVPairIndex (a k : ℕ) : Fin (a+k) → Fin ((0+a)+(0+k)) :=
  Fin.addCases (fun i => Fin.castAdd (0+k) (Fin.natAdd 0 i))
    (fun i => Fin.natAdd (0+a) (Fin.natAdd 0 i))

theorem groundRV_gamma_volume {k : ℕ} (U : GammaGroundRVObject hc B k) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 U.arity) (q : Point (M := M) 0 k) =>
      ∃ u : U.domain,u.val=p.2 ∧ (U.volume u).val=q.2) := by
  let st := Fin.append (gammaPointSort 0 U.arity) (gammaPointSort 0 k)
  have hW := (nativeRVLabelGraph_definable U).preimage_real st (groundRVPairIndex U.arity k)
  have h := gamma_graph_of_sorted_formula hW
  apply GammaGraphDefinable.congr h
  intro p q
  have he : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ groundRVPairIndex U.arity k =
      Fin.append (rvValues p.2) (rvValues q.2) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply,groundRVPairIndex,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointCode,rvValues]
  change (_ ∈ nativeRVLabelGraph U ∧ _) ↔ _
  rw [he,nativeRVLabelGraph_append_iff]
  constructor
  · rintro ⟨⟨u,hu,hv⟩,_⟩
    exact ⟨u,rvValues_injective hu,rvValues_injective hv⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨⟨u,congrArg rvValues hu,congrArg rvValues hv⟩,?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [st,Fin.append_left] using groundPointCode_sorted p j
    · simpa only [st,Fin.append_right] using groundPointCode_sorted q j

end DiamondIntegral.Section5
