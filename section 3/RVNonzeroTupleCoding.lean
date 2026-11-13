import «section 3».RVUnitDomains
import «section 3».GammaGroundMapImages
import «section 2».FiniteSets
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rvNonzeroTupleCode (t : Fin n → CanonicalRV.RVSort M) : Fin (n*2) → (CanonicalRV.RVSort M)ˣ := fun j =>
  let p := finProdFinEquiv.symm j
  let h := Section2.nonzeroRVCode_proper (t p.1).val (t p.1).property p.2
  Units.mk0 ⟨Section2.nonzeroRVCode (t p.1).val p.2,h.1⟩
    (fun he => h.2 ((congrArg Subtype.val he).trans RVOperations.zero_val))

theorem rvNonzeroTupleCode_injective (h00 : M ⊨ Axioms.ACVF00) :
    Function.Injective (rvNonzeroTupleCode (M := M) (n := n)) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hne := Section2.r023_distinct_tags h00 v hv
  intro a b he
  funext i
  apply Subtype.ext
  apply Section2.nonzeroRVCode_injective hne
  funext j
  have hh := congrArg (fun u : (CanonicalRV.RVSort M)ˣ => u.val.val) (congrFun he (finProdFinEquiv (i,j)))
  simpa only [rvNonzeroTupleCode,Equiv.symm_apply_apply,Units.val_mk0] using hh

def rvNonzeroTupleCodeMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (rawRVUnitSpace (n*2)) S) := by
  let F (z : Fin n → M) (j : Fin (n*2)) := Section2.nonzeroRVCode (z (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2
  have hcode (c : (rawRVSpace (M := M) n).domain) :
      rvUnitValues (rvNonzeroTupleCode ((rawRVSpace n).decode c)) = F c.val := by
    funext j
    exact congrArg (fun t => Section2.nonzeroRVCode t (finProdFinEquiv.symm j).2)
      (congrFun (rvValues_decode c) (finProdFinEquiv.symm j).1)
  have hdom (c : (rawRVSpace (M := M) n).domain) : F c.val ∈ (rawRVUnitSpace (M := M) (n*2)).domain :=
    ⟨rvNonzeroTupleCode ((rawRVSpace n).decode c),hcode c⟩
  refine Map.ofCodes _ rvNonzeroTupleCode F
    (fun j => Section2.nonzeroRVCode_definable S (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) hdom ?_
  intro c
  exact rvUnitValues_injective ((rvUnitValues_decode _).trans (hcode c).symm)

def gammaGroundRVNonzeroTupleCodeMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)} (X : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B (rawRVUnitSpace (n*2))) :=
  GammaGroundMap.ofGlobal _ _ (rvNonzeroTupleCodeMap B.real n) (fun _ => Set.mem_univ _)

def gammaGroundRVNonzeroTupleCodeBijection (h00 : M ⊨ Axioms.ACVF00)
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundBijection X (gammaGroundRVNonzeroTupleCodeMap X).image := by
  refine ⟨(gammaGroundRVNonzeroTupleCodeMap X).toImage,
    (gammaGroundRVNonzeroTupleCodeMap X).toImage_bijective ?_⟩
  intro a b he
  apply Subtype.ext
  apply rvNonzeroTupleCode_injective h00
  exact congrArg (fun z : GammaGroundDefSet.univ hc B (rawRVUnitSpace (n*2)) => z.val) he
end DiamondIntegral.Section3
