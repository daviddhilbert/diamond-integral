import «section 3».GammaMeasuredIndexedElementarySchemata
import «section 3».GammaMeasuredIndexedIsomorphisms
import «section 3».GammaMeasuredIndexedCoproducts
import «section 3».GammaMeasuredGeometricRecoding

/-! Uniform finite Gamma-measured geometric proofs are sound after
indexed assembly in the original principal semiring quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def gammaMeasuredPrincipalValue {n : ℕ} (U : GammaGroundMeasuredRVObject hc B n) :=
  (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass U)

theorem gammaMeasuredPrincipalValue_iso {n : ℕ} {U V : GammaGroundMeasuredRVObject hc B n}
    (e : GammaGroundMeasuredRVHom U V) : gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V :=
  congrArg (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass_iso (asIso e))

theorem gammaMeasuredPrincipalValue_add {n : ℕ} {U V W : GammaGroundMeasuredRVObject hc B n}
    (h : gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass V + gammaGroundMeasuredRVClass W) :
    gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V + gammaMeasuredPrincipalValue W := by
  let φ := gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := B) (k := n)
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  have hSemiring : φ (gammaGroundMeasuredRVClass U) =
      φ (gammaGroundMeasuredRVClass V) + φ (gammaGroundMeasuredRVClass W) :=
    (congrArg φ h).trans (φ.map_add _ _)
  change gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U) =
    gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass V) +
      gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass W) at hSemiring
  rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaGroundMeasuredRVKPlusToSemiring_class,
    gammaGroundMeasuredRVKPlusToSemiring_class] at hSemiring
  exact (congrArg q hSemiring).trans (q.map_add _ _)

set_option maxHeartbeats 600000 in
theorem GammaMeasuredRelationSchema.indexed_sound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)}
    {G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv)}
    (H : GammaMeasuredRelationSchema F G) (BP : GammaFiniteGraphPresentation B p d T R) :
    ∀ (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
      (hH : ∀ t ∈ T, H.valid (rvValues t))
      (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP),
      gammaMeasuredPrincipalValue (F.indexedObject BP hF P) = gammaMeasuredPrincipalValue (G.indexedObject BP hG Q) := by
  induction H with
  | iso I =>
    intro hF hG hH P Q
    let hFS := fun t ht => I.source.essential_valid (rvValues t) (hF t ht)
    let hGS := fun t ht => I.target.essential_valid (rvValues t) (hG t ht)
    let PS := I.source.essential.object.indexedPresentation BP (fun t ht => (hFS t ht).1)
    let QS := I.target.essential.object.indexedPresentation BP (fun t ht => (hGS t ht).1)
    obtain ⟨eF⟩ := I.source.indexedEssential BP hF P PS
    obtain ⟨eG⟩ := I.target.indexedEssential BP hG Q QS
    obtain ⟨eI⟩ := I.indexedRealize BP hH PS QS
    exact gammaMeasuredPrincipalValue_iso (eG.symm.comp (eI.comp eF))
  | agreement F G =>
    intro hF hG hH P Q
    obtain ⟨e⟩ := F.indexedAgreement G BP hF hG (fun t ht => (hH t ht).2.2) P Q
    exact gammaMeasuredPrincipalValue_iso e
  | elementary F N A =>
    intro hF hG hH P Q
    exact (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
      (F.indexedElementary_relation hκ hs h00 hr hg A N BP hH P Q)
  | symm H ih =>
    intro hF hG hH P Q
    exact (ih hG hF hH Q P).symm
  | trans E H K ihH ihK =>
    intro hF hG hHK P Q
    let hE := fun t ht => (H.valid_endpoints (hHK t ht).1).2
    let EP := E.object.indexedPresentation BP (fun t ht => (hE t ht).1)
    exact (ihH hF hE (fun t ht => (hHK t ht).1) P EP).trans
      (ihK hE hG (fun t ht => (hHK t ht).2) EP Q)
  | @coprod a b c e F G E D H K N L ihH ihK =>
    intro hSource hTarget hHK P Q
    let hH := fun t ht => (hHK t ht).1
    let hK := fun t ht => (hHK t ht).2.1
    let hF := fun t ht => (H.valid_endpoints (hH t ht)).1
    let hG := fun t ht => (H.valid_endpoints (hH t ht)).2
    let hE := fun t ht => (K.valid_endpoints (hK t ht)).1
    let hD := fun t ht => (K.valid_endpoints (hK t ht)).2
    let FP := F.object.indexedPresentation BP (fun t ht => (hF t ht).1)
    let GP := G.object.indexedPresentation BP (fun t ht => (hG t ht).1)
    let EP := E.object.indexedPresentation BP (fun t ht => (hE t ht).1)
    let DP := D.object.indexedPresentation BP (fun t ht => (hD t ht).1)
    have hLeft := gammaMeasuredPrincipalValue_add (F.indexedCoprod_class E N BP hF hE hSource FP EP P)
    have hRight := gammaMeasuredPrincipalValue_add (G.indexedCoprod_class D L BP hG hD hTarget GP DP Q)
    exact hLeft.trans ((congrArg₂ (· + ·) (ihH hF hG hH FP GP) (ihK hE hD hK EP DP)).trans hRight.symm)

end DiamondIntegral.Section3
