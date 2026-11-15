import «section 5».NativeMixedSortedRealization
import «section 5».OriginalRVTotalFamilies
import «section 5».GammaMixedPreparedRows
import IntegrationSection6.GammaPreparedDescent
import IntegrationSection6.GammaPreparedRowAgreements

/-! The full prepared RV key domain is definable over the original Gamma
ground. Its old RV parameter block is retained as RV coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l q : ℕ}

theorem rawPreparedKey_definable (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C)) :
    DefinableOverBase B (fun _ : Fin (p+l) => .rv) {w | ∃ c : C, rawPreparedKey c.val = w} := by
  have h := (gammaLogicInput B).image_real (fullRVKeyMap B.real p l) hC
  change DefinableOverBase B (gammaPointSort 0 (p+l)) (gammaPointCode '' _) at h
  have h' := h.image_real (Fin.natAdd 0 : Fin (p+l) → Fin (0+(p+l)))
  have hsort : gammaPointSort 0 (p+l) ∘ Fin.natAdd 0 = (fun _ : Fin (p+l) => SortTag.rv) := by
    funext i
    simp only [gammaPointSort,Function.comp_apply,Fin.append_right]
  rw [hsort] at h'
  convert h' using 1
  ext w
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨gammaPointCode (flatKey c.val),⟨flatKey c.val,⟨⟨c.val,Set.mem_univ _⟩,c.property,rfl⟩,rfl⟩,?_⟩
    funext i
    simp only [Function.comp_apply,gammaPointCode,rawPreparedKey,Fin.append_right]
  · rintro ⟨_,⟨v,⟨a,ha,hav⟩,rfl⟩,hw⟩
    refine ⟨⟨a.val,ha⟩,?_⟩
    have he : gammaPointCode (flatKey a.val) ∘ Fin.natAdd 0 = rawPreparedKey a.val :=
      funext (fun i => by simp only [Function.comp_apply,gammaPointCode,rawPreparedKey,Fin.append_right])
    exact he.symm.trans ((congrArg (fun t => gammaPointCode t ∘ Fin.natAdd 0) hav).trans hw)

def nativePreparedKeyDomain (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C)) : GammaGroundDefSet hc B (rawRVSpace (M := M) (p+l)) :=
  ofRaw {w | ∃ c : C,rawPreparedKey c.val = w} (rawPreparedKey_definable C hC)

theorem nativePreparedKeyDomain_raw (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C)) :
    rawDomain (nativePreparedKeyDomain (hc := hc) C hC) = {w | ∃ c : C,rawPreparedKey c.val = w} :=
  rawDomain_ofRaw _ _

def nativePreparedParameterBase (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C))
    (Z : GammaDomainFormula B ((p+l)+q) 0 (fun _ => .rv)) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) ((p+l)+q)) :=
  ofRaw {w | Fin.append w (Fin.elim0 : Fin 0 → M) ∈ Z.val ∧
    w ∘ Fin.castAdd q ∈ rawDomain (nativePreparedKeyDomain (hc := hc) C hC)} (by
    let π : Fin (((p+l)+q)+0) → Fin ((p+l)+q) := Fin.addCases id Fin.elim0
    have hπ (w : Fin ((p+l)+q) → M) : w ∘ π = Fin.append w (Fin.elim0 : Fin 0 → M) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
      simp only [π,Function.comp_apply,Fin.addCases_left,id_eq,Fin.append_left]
    have hZ : DefinableOverBase B (fun _ : Fin ((p+l)+q) => .rv)
        {w | Fin.append w (Fin.elim0 : Fin 0 → M) ∈ Z.val} := by
      have h := Z.property.preimage_real (fun _ : Fin ((p+l)+q) => .rv) π
      convert h using 1
      ext w
      change (Fin.append w (Fin.elim0 : Fin 0 → M) ∈ Z.val) ↔ (w ∘ π ∈ Z.val ∧ _)
      rw [hπ]
      change _ ↔ (_ ∧ _)
      refine ⟨fun hw => ⟨hw,?_⟩,And.left⟩
      intro i
      simpa only [Fin.append_left] using Z.property.proper _ hw (Fin.castAdd 0 i)
    have hK := (rawDomain_definable (nativePreparedKeyDomain (hc := hc) C hC)).preimage_real
      (fun _ : Fin ((p+l)+q) => .rv) (Fin.castAdd q)
    convert hZ.inter hK using 1
    ext w
    change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    exact ⟨fun h => ⟨h.1,h.2,hZ.proper _ h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩)

theorem nativePreparedParameterBase_raw (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C))
    (Z : GammaDomainFormula B ((p+l)+q) 0 (fun _ => .rv)) :
    rawDomain (nativePreparedParameterBase (hc := hc) C hC Z) =
      {w | Fin.append w (Fin.elim0 : Fin 0 → M) ∈ Z.val ∧
        ∃ c : C,rawPreparedKey c.val = w ∘ Fin.castAdd q} := by
  rw [nativePreparedParameterBase,rawDomain_ofRaw,nativePreparedKeyDomain_raw]
  rfl

end DiamondIntegral.Section5
