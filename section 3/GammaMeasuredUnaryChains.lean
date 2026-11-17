import «section 3».GammaGroundMeasuredFormTransport
import «section 3».GammaFullMeasuredFixedMaps
import «section 3».GammaGroundPointIsomorphisms
import IntegrationSection5.GammaUnaryChain
import IntegrationSection6.GammaFiniteMixedBijections

/-! Finite relatively unary chains with actual transported Gamma forms
on every mixed intermediate domain. This adds measure data to the given
chain without replacing its map or enlarging its ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

inductive GammaMeasuredUnaryChain :
    GammaGroundMeasuredVFData hc B (n+1) → GammaGroundMeasuredVFData hc B (n+1) → Type
  | nil (U) : GammaMeasuredUnaryChain U U
  | cons {U V W} (i : Fin (n+1)) (f : GammaFullMeasuredBijection U V)
      (unary : ∀ p, ∀ j, j ≠ i → (f.map.map p).val.1 j = p.val.1 j)
      (tail : GammaMeasuredUnaryChain V W) : GammaMeasuredUnaryChain U W

namespace GammaMeasuredUnaryChain
def append {U V W : GammaGroundMeasuredVFData hc B (n+1)} :
    GammaMeasuredUnaryChain U V → GammaMeasuredUnaryChain V W → GammaMeasuredUnaryChain U W
  | .nil _, R => R
  | .cons i f hi tail, R => .cons i f hi (tail.append R)

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def fullMap {U V : GammaGroundMeasuredVFData hc B (n+1)} :
    GammaMeasuredUnaryChain U V → GammaFullMeasuredBijection U V
  | .nil U => gammaFullMeasuredFixedVF hκ hs hr hv (GammaGroundBijection.id U.domain) (fun _ => rfl) (fun _ => rfl)
  | .cons _ f _ tail => f.comp hκ hs hr hv (fullMap tail)

theorem append_fullMap_value {U V W : GammaGroundMeasuredVFData hc B (n+1)}
    (H : GammaMeasuredUnaryChain U V) (K : GammaMeasuredUnaryChain V W) (p : U.domain) :
    (((H.append K).fullMap hκ hs hr hv).map.map p).val =
      ((K.fullMap hκ hs hr hv).map.map ((H.fullMap hκ hs hr hv).map.map p)).val := by
  induction H with
  | nil U => rfl
  | cons i f hi tail ih => exact ih K (f.map.map p)

end GammaMeasuredUnaryChain

def gammaRawPointMeasuredData {a : ℕ} (A : Set (Point (M := M) (n+1) a))
    (hA : GammaSetDefinable B A) (hfin : ∀ x, {r | (x,r) ∈ A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain A hA)) :
    GammaGroundMeasuredVFData hc B (n+1) := ⟨a,Section5.nativeGammaPointDomain A hA,hfin,ω⟩

theorem gammaUnaryChain_measured_transport
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {a b : ℕ} {A : Set (Point (M := M) (n+1) a)} {D : Set (Point (M := M) (n+1) b)}
    (T : GammaUnaryChain B (n+1) A D) :
    ∀ (hA : GammaSetDefinable B A) (hD : GammaSetDefinable B D)
      (hfin : ∀ x, {r | (x,r) ∈ A}.Finite)
      (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain A hA)),
    ∃ hfinD : ∀ x, {r | (x,r) ∈ D}.Finite,
    ∃ η : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain D hD),
    ∃ H : GammaMeasuredUnaryChain (gammaRawPointMeasuredData A hA hfin ω) (gammaRawPointMeasuredData D hD hfinD η),
      ∀ p, ((H.fullMap hκ hs hr hv).map.map p).val = (T.toIso.equiv ⟨p.val,p.property⟩).val := by
  induction T with
  | nil A hA₀ =>
    intro hA hD hfin ω
    exact ⟨hfin,ω,.nil _,fun _ => rfl⟩
  | @cons a b c A D E i e hu tail ih =>
    intro hA hE hfin ω
    have hD := e.target_definable (gammaLogicInput B)
    have hfinD := finiteRVFibres_of_gammaIso hκ hs B hr e
      (fun p _ => @vfTupleTrdeg_le_arity M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) B.real (n+1) p.1) hfin
    let f := Section5.nativeGammaPointBijection (hc := hc) hA hD e
    let U := gammaRawPointMeasuredData A hA hfin ω
    let F := gammaGroundTransportFullMeasured hκ hs hr hv (Nat.zero_lt_succ n) U
      (Section5.nativeGammaPointDomain D hD) hfinD f
    obtain ⟨hfinE,η,H,hH⟩ := ih hD hE hfinD (gammaGroundTransportedForm (Nat.zero_lt_succ n) f ω)
    have hUnary : ∀ p, ∀ j, j ≠ i → (F.map.map p).val.1 j = p.val.1 j := by
      intro p j hj
      exact (congrArg (fun z : Point (M := M) (n+1) b => z.1 j)
        (Section5.nativeGammaPointBijection_apply hA hD e p)).trans (hu ⟨p.val,p.property⟩ j hj)
    refine ⟨hfinE,η,.cons i F hUnary H,?_⟩
    intro p
    have hStep := Section5.nativeGammaPointBijection_apply hA hD e p
    have hEq : (⟨(F.map.map p).val,(F.map.map p).property⟩ : D) = e.equiv ⟨p.val,p.property⟩ :=
      Subtype.ext hStep
    exact (hH (F.map.map p)).trans (congrArg (fun z : D => (tail.toIso.equiv z).val) hEq)

end DiamondIntegral.Section3
