import «section 5».OriginalRVTotalFamilies
import «section 5».OriginalDomainProducts
import «section 5».RawParameterProjectionRecoding
import «section 5».RawTupleReindexBijections

/-! The total domain of an original block product is the Gamma family
over the full first-factor total domain, up to literal block association. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem rvValues_append (x : Fin p → CanonicalRV.RVSort M) (y : Fin a → CanonicalRV.RVSort M) :
    rvValues (Fin.append x y) = Fin.append (rvValues x) (rvValues y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvValues,Fin.append_left,Fin.append_right]

theorem originalRVTotalFamily_append_mem
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (x : Fin p → CanonicalRV.RVSort M) (y : Fin a → CanonicalRV.RVSort M) :
    Fin.append x y ∈ (originalRVTotalFamily X D).carrier ↔
      x ∈ X.carrier ∧ Fin.append (rvValues x) (rvValues y) ∈ D.val := by
  rw [originalRVTotalFamily_mem,rvValues_append]
  have he : Fin.append x y ∘ Fin.castAdd a = x := by
    funext j
    exact Fin.append_left _ _ j
  rw [he]

theorem originalProductTotal_reindex
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaDomainFormula B p a (fun _ => .rv))
    (G : GammaDomainFormula B p b (fun _ => .rv))
    (u : Fin (p+(a+b)) → CanonicalRV.RVSort M) :
    u ∈ (originalRVTotalFamily X (originalDomainProduct F G)).carrier ↔
      u ∘ finCongr (Nat.add_assoc p a b) ∈
        (originalRVTotalFamily (originalRVTotalFamily X F)
          ((rawParameterProjectionRecode B (Fin.castAdd a)).domain G)).carrier := by
  let x := u ∘ Fin.castAdd (a+b)
  let y := (u ∘ Fin.natAdd p) ∘ Fin.castAdd b
  let z := (u ∘ Fin.natAdd p) ∘ Fin.natAdd a
  have he : Fin.append x (Fin.append y z) = u := by
    dsimp only [x,y,z]
    have ht : Fin.append ((u ∘ Fin.natAdd p) ∘ Fin.castAdd b)
        ((u ∘ Fin.natAdd p) ∘ Fin.natAdd a) = u ∘ Fin.natAdd p := Fin.append_castAdd_natAdd
    rw [ht]
    exact Fin.append_castAdd_natAdd
  rw [← he]
  have hassoc : Fin.append x (Fin.append y z) ∘ finCongr (Nat.add_assoc p a b) =
      Fin.append (Fin.append x y) z := Fin.append_assoc x y z |>.symm
  rw [hassoc,originalRVTotalFamily_append_mem,originalRVTotalFamily_append_mem,
    originalRVTotalFamily_append_mem,originalDomainProduct_row]
  have hy : Fin.append (rvValues y) (rvValues z) ∘ Fin.castAdd b = rvValues y := by
    funext j
    exact Fin.append_left _ _ j
  have hz : Fin.append (rvValues y) (rvValues z) ∘ Fin.natAdd a = rvValues z := by
    funext j
    exact Fin.append_right _ _ j
  have hp : rvValues (Fin.append x y) ∘ Fin.castAdd a = rvValues x := by
    rw [rvValues_append]
    funext j
    exact Fin.append_left _ _ j
  rw [rvValues_append,hy,hz]
  have hg := rawParameterProjectionRecode_domain_agreement (Fin.castAdd a) G
    (rvValues (Fin.append x y)) (fun j => (Fin.append x y j).property) (rvValues z)
  rw [hp] at hg
  rw [← hg]
  exact and_assoc.symm

def originalProductTotalBijection
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaDomainFormula B p a (fun _ => .rv))
    (G : GammaDomainFormula B p b (fun _ => .rv)) :
    GammaGroundBijection (originalRVTotalFamily X (originalDomainProduct F G))
      (originalRVTotalFamily (originalRVTotalFamily X F)
        ((rawParameterProjectionRecode B (Fin.castAdd a)).domain G)) :=
  rawTupleReindexBijection _ _ (finCongr (Nat.add_assoc p a b)) (originalProductTotal_reindex X F G)

end DiamondIntegral.Section5
