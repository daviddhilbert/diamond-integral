import «section 6».OrdinaryZeroFocus
import «section 6».OrdinaryChainNearZero

/-! On a sufficiently small whole zero disc, an ordinary unary chain
is the identity on VF and its full endpoint RV tuple is an explicit
function of the original leading term and the old labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

def ordinaryChainZeroDiscTags : {r s : ℕ} →
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} →
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} →
    SpecialTransformations.Section5.Chain R 1 A B →
    (Fin 1 → RVInfinity M) → (Fin r → RVInfinity M) → (Fin s → RVInfinity M)
  | _,_,_,_,.nil _,_,u => u
  | _,_,_,_,.cons (.canonical _) tail,t,u => ordinaryChainZeroDiscTags tail t (Fin.append t u)
  | _,_,_,_,.cons (.centripetal _) tail,t,u => ordinaryChainZeroDiscTags tail t u

theorem ordinary_chain_whole_zero_disc_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ p : A,η.val < vfValue (p.val.1 0) →
      (T.toMap p).val.1=p.val.1 ∧
      (T.toMap p).val.2=ordinaryChainZeroDiscTags T (tupleRV M p.val.1) p.val.2 := by
  induction T with
  | nil A => exact ⟨1,le_rfl,fun _ _ => ⟨rfl,rfl⟩⟩
  | @cons a b c A B C step tail ih =>
    obtain ⟨ηTail,hηTail1,hTail⟩ := ih hT.2
    cases step with
    | canonical A =>
      refine ⟨ηTail,hηTail1,fun p hpSmall => ?_⟩
      exact hTail ((SpecialTransformations.Section5.Primitive.canonical A).toMap p) hpSmall
    | @centripetal a i j D =>
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      obtain ⟨ηFocus,hηFocus1,hFocus⟩ := OriginalBaseOrdinaryFocus.eta_identity_near_zero D hc hs hsmall hT.1.1 hT.1.2
      refine ⟨max ηTail ηFocus,hηTail1.trans (le_max_left _ _),fun p hpSmall => ?_⟩
      have hStep := hFocus p ((show ηFocus.val ≤ (max ηTail ηFocus).val from le_max_right _ _).trans_lt hpSmall)
      have hSmall : ηTail.val < vfValue (((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val.1 0) := by
        rw [hStep]
        exact (show ηTail.val ≤ (max ηTail ηFocus).val from le_max_left _ _).trans_lt hpSmall
      obtain ⟨hVF,hTags⟩ := hTail ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p) hSmall
      refine ⟨hVF.trans (congrArg Prod.fst hStep),hTags.trans ?_⟩
      rw [hStep]
      rfl

end DiamondIntegral.Section6
