import «section 5».NativeMixedFamilyTotals
import «section 5».NativeFiniteRVLiftDomains
import «section 5».NativeFiniteRVSchemaValidity
import «section 5».NativeMixedKeyMaps

/-! Literal total families of finite RV fibre lifts retain their mixed
base coordinates. Their full domains and nonzero fibre VF coordinates
are computed from the actual finite label graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q a k : ℕ}

theorem nativeMixedCode_mem_domain_iff {n r : ℕ}
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (x : Section2.Mixed M n r) :
    nativeMixedCode x ∈ nativeMixedDomain A ↔ x ∈ A.carrier := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact nativeMixedCode_injective he ▸ hy
  · exact fun hx => ⟨x,hx,rfl⟩

def nativeVFLiftFamily (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (q+a)) :=
  nativeMixedFamilyTotal (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
    (finiteRVSchemaLiftDomain hc F).val (finiteRVSchemaLiftDomain hc F).property

theorem nativeVFLiftFamily_mem (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (b : Fin p → Section2.VF M) (v : Fin q → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) :
    (Fin.append b y,Fin.append v u) ∈ (nativeVFLiftFamily Z F).carrier ↔
      (b,v) ∈ Z.carrier ∧ Fin.append (Fin.append (nativeMixedCode (b,v)) (rvValues u))
        (rvValues (Section2.tupleRV M y)) ∈ F.volume := by
  have ht := nativeMixedFamilyTotal_mem (hc := hc) (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
    (finiteRVSchemaLiftDomain hc F).val (finiteRVSchemaLiftDomain hc F).property b v y u
  refine ht.trans (and_congr (nativeMixedCode_mem_domain_iff Z (b,v)) ?_)
  exact finiteRVSchemaLiftDomain_row hc F (nativeMixedCode (b,v)) (vfValues y) (rvValues u)
    (nativeMixedCode_proper (b,v)) (fun i => (y i).property) (fun i => (u i).property)

theorem nativeVFLiftFamily_fibre_nonzero
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hv : ∀ z ∈ nativeMixedDomain Z,nativeFiniteRVSchemaValid F z)
    (b : Fin p → Section2.VF M) (v : Fin q → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M)
    (h : (Fin.append b y,Fin.append v u) ∈ (nativeVFLiftFamily Z F).carrier) (i : Fin k) : y i ≠ 0 := by
  have hm := (nativeVFLiftFamily_mem Z F b v y u).mp h
  have hn := (hv _ ⟨(b,v),hm.1,rfl⟩).2 _ _ hm.2 i
  exact fun hi => hn ((rvValues_tupleRV_zero_iff y i).mpr hi)

end DiamondIntegral.Section5
