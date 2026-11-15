import «section 5».ElementaryNativeRVDomains
import «section 5».NativeRESClasses
import «section 3».GammaGroundRVProductScissors

/-! Literal elementary restriction commutes with cuts and cartesian RV
products; these statements concern the full native domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M) {n m : ℕ}

local notation "R" => elementaryNativeRVRestriction hcM hcN e c
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)

theorem rv_product_mem_projections {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF]
    {hc : CanonicalStructure.IsCanonical (M := Q)} {B : GammaParameters.Base (M := Q)}
    (D : GammaGroundDefSet hc B (rawRVSpace (M := Q) n))
    (E : GammaGroundDefSet hc B (rawRVSpace (M := Q) m)) (x : Fin (n+m) → CanonicalRV.RVSort Q) :
    x ∈ (gammaGroundRVProductDomain D E).carrier ↔
      x ∘ Fin.castAdd m ∈ D.carrier ∧ x ∘ Fin.natAdd n ∈ E.carrier := by
  rw [mem_gammaGroundRVProductDomain]
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simpa only [rvAppend,Function.comp_def,Fin.append_left,Fin.append_right] using And.intro ha hb
  · rintro ⟨ha,hb⟩
    exact ⟨_,ha,_,hb,Fin.append_castAdd_natAdd (f := x)⟩

theorem elementaryNativeRVRestriction_product
    (D : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n))
    (E : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) m)) :
    (R (gammaGroundRVProductDomain D E)).carrier =
      (gammaGroundRVProductDomain (R D) (R E)).carrier := by
  ext x
  rw [elementaryNativeRVRestriction_mem,rv_product_mem_projections,rv_product_mem_projections,
    elementaryNativeRVRestriction_mem,elementaryNativeRVRestriction_mem]
  rfl

theorem elementaryNativeRVRestriction_sdiff
    (D E : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n)) :
    (R (D.sdiff E)).carrier = ((R D).sdiff (R E)).carrier := by
  ext x
  rw [elementaryNativeRVRestriction_mem]
  change (_ ∈ D.carrier ∧ _ ∉ E.carrier) ↔ (x ∈ (R D).carrier ∧ x ∉ (R E).carrier)
  exact and_congr (elementaryNativeRVRestriction_mem hcM hcN e c D x).symm
    (not_congr (elementaryNativeRVRestriction_mem hcM hcN e c E x)).symm

theorem elementaryNativeRVRestriction_empty (k : ℕ) :
    (elementaryNativeRESRestriction hcM hcN e c (GammaGroundRESObject.empty hcN Bₙ k)).obj.domain.carrier = ∅ := by
  ext x
  rw [Set.mem_empty_iff_false]
  change x ∈ (R (GammaGroundRESObject.empty hcN Bₙ k).obj.domain).carrier ↔ False
  rw [elementaryNativeRVRestriction_mem]
  exact Iff.rfl

end DiamondIntegral.Section5
