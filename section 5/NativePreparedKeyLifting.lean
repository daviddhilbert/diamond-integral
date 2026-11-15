import «section 5».NativePreparedKeyDomains
import «section 5».OriginalProductTotalBijections

/-! Every VF realization of a prepared key lies in the prepared base.
This uses the actual RV-pullback identity and retains the full key tuple;
no definable section of RV is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p l : ℕ}

theorem rawPreparedKey_first (x : Point (M := M) p l) (i : Fin p) :
    rawPreparedKey x (Fin.castAdd l i) = rvValues (Section2.tupleRV M x.1) i := by
  simp only [rawPreparedKey,flatKey,key,Fin.append_left,rvValues,Section2.tupleRV]
  rfl

theorem rawPreparedKey_last (x : Point (M := M) p l) (i : Fin l) :
    rawPreparedKey x (Fin.natAdd p i) = rvValues x.2 i := by
  simp only [rawPreparedKey,flatKey,key,Fin.append_right,rvValues]

theorem nativePreparedKey_realization {S : Set M} (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C)) (hpull : IsRVPullback (carrier C))
    (t : Fin (p+l) → CanonicalRV.RVSort M)
    (ht : rvValues t ∈ rawDomain (nativePreparedKeyDomain (hc := hc) C hC))
    (x : Fin p → Section2.VF M)
    (hx : rvValues t ∘ Fin.castAdd l = rvValues (Section2.tupleRV M x)) :
    (x,t ∘ Fin.natAdd p) ∈ carrier C := by
  rw [nativePreparedKeyDomain_raw] at ht
  obtain ⟨c,hc⟩ := ht
  let y : Point (M := M) p l := (x,t ∘ Fin.natAdd p)
  have he : flatKey c.val = flatKey y := by
    apply Prod.ext (Subsingleton.elim _ _)
    apply rvValues_injective
    funext i
    change rawPreparedKey c.val i = rawPreparedKey y i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (congrFun hc (Fin.castAdd l j)).trans
        ((congrFun hx j).trans (rawPreparedKey_first y j).symm)
    · exact (congrFun hc (Fin.natAdd p j)).trans (rawPreparedKey_last y j).symm
  exact (mem_iff_sameRV hpull ((flatKey_eq_iff c.val y).mp he)).mp c.property

end DiamondIntegral.Section5
