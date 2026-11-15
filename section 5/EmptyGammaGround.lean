import «section 3».GammaGroundBijections
import «section 3».GammaGroundMapRestrictions

/-! Exact conversion between the native ground presentation with no
additional Gamma names and original real-parameter definability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EmptyGammaGround
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def base (S : Set M) : GammaParameters.Base (M := M) := ⟨S, ∅⟩

theorem definable_iff (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M)
    (P : Space LRV M) (A : Set P.Carrier) :
    GammaGroundDefinable hc (base S) P A ↔ P.Definable S A := by
  constructor
  · rintro ⟨k, γ, hγ, hA⟩
    cases k with
    | succ k => exact (hγ 0).elim
    | zero =>
      let V := (volumeGammaSpace hc).power (Fin 0)
      letI : IsEmpty V.Index := by
        change IsEmpty (Fin 0 × (volumeGammaSpace hc).Index)
        infer_instance
      obtain ⟨c, hcγ⟩ := V.onto γ
      have h := hA.over_real_code c hcγ
      have he : Set.range c.val = ∅ := Set.range_eq_empty _
      simpa only [realCodeParameters, he, Set.union_empty, base] using h
  · intro h
    exact GammaGroundDefinable.of_real (hc := hc) (B := base S) h

def toReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P : Space LRV M}
    (A : GammaGroundDefSet hc (base S) P) : DefSet P S :=
  ⟨A.carrier, (definable_iff hc S P A.carrier).mp A.definable⟩

def fromReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P : Space LRV M}
    (A : DefSet P S) : GammaGroundDefSet hc (base S) P := GammaGroundDefSet.ofReal A

theorem toReal_fromReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P : Space LRV M}
    (A : DefSet P S) : toReal hc (fromReal hc A) = A := rfl

theorem fromReal_toReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P : Space LRV M}
    (A : GammaGroundDefSet hc (base S) P) : fromReal hc (toReal hc A) = A := rfl

def mapToReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P Q : Space LRV M}
    {A : GammaGroundDefSet hc (base S) P} {B : GammaGroundDefSet hc (base S) Q}
    (f : GammaGroundMap A B) : Map (toReal hc A) (toReal hc B) where
  toFun := f.toFun
  graph_definable := (relationDefinable_iff_product _).mpr
    ((definable_iff hc S (P.prod Q) _).mp f.graph_definable)

def mapFromReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P Q : Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (f : Map A B) :
    GammaGroundMap (fromReal hc A) (fromReal hc B) := GammaGroundMap.ofReal f

def bijectionToReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P Q : Space LRV M}
    {A : GammaGroundDefSet hc (base S) P} {B : GammaGroundDefSet hc (base S) Q}
    (f : GammaGroundBijection A B) : DefinableBijection (toReal hc A) (toReal hc B) :=
  ⟨mapToReal hc f.map, f.bijective⟩

def bijectionFromReal (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {P Q : Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (f : DefinableBijection A B) :
    GammaGroundBijection (fromReal hc A) (fromReal hc B) := ⟨mapFromReal hc f.map, f.bijective⟩

end DiamondIntegral.Section5.EmptyGammaGround
