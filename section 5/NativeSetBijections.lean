import «section 5».NativeTaggedDomains
import «section 5».RESSetSumSchemata

/-! Exact raw-domain agreement produces actual Gamma-ground bijections.
Literal schema sums agree with the actual native tagged coproduct domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaGroundBijectionOfCarrierEq {Q : Space LRV M}
    (A C : GammaGroundDefSet hc B Q) (h : A.carrier = C.carrier) : GammaGroundBijection A C where
  map := GammaGroundMap.inclusion h.subset
  bijective := ⟨(fun _ _ he => Subtype.ext (congrArg (fun c : C => c.val) he)),
    fun c => ⟨⟨c.val, h.symm ▸ c.property⟩, rfl⟩⟩

theorem rawDomain_carrier_eq
    (A C : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) (h : rawDomain A = rawDomain C) :
    A.carrier = C.carrier := rvValues_injective.image_injective h

def gammaGroundBijectionOfRawDomainEq
    (A C : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) (h : rawDomain A = rawDomain C) :
    GammaGroundBijection A C := gammaGroundBijectionOfCarrierEq A C (rawDomain_carrier_eq A C h)

def nativeSchemaSumBijection {p a b : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    GammaGroundBijection ((F.sum G).object hc z (F.sum_valid hc G z hF hG)).obj.domain
      (gammaGroundRVTaggedUnion (F.object hc z hF).obj.domain (G.object hc z hG).obj.domain) := by
  let A := (F.object hc z hF).obj.domain
  let C := (G.object hc z hG).obj.domain
  let U := ((F.sum G).object hc z (F.sum_valid hc G z hF hG)).obj.domain
  apply gammaGroundBijectionOfRawDomainEq U (gammaGroundRVTaggedUnion A C)
  have ha : rawDomain A = F.rowDomain z := rawDomain_ofRaw (F.rowDomain z) (F.row_domain_definable z)
  have hc' : rawDomain C = G.rowDomain z := rawDomain_ofRaw (G.rowDomain z) (G.row_domain_definable z)
  have hu : rawDomain U = (F.sum G).rowDomain z := rawDomain_ofRaw ((F.sum G).rowDomain z) ((F.sum G).row_domain_definable z)
  ext w
  rw [hu, rawDomain_native_tagged_union A C w, ha, hc']
  exact F.sum_row G z w

end DiamondIntegral.Section5
