import IntegrationSection3ACVF.AtomicBallFamilyChoice
import IntegrationSection3ACVF.BetaSubballFamilies
import IntegrationSection3ACVF.NamedBallSetup
import IntegrationSection3ACVF.RVLinearity

/-! An RV-linear ball at any strictly smaller ordinary radius.
The ball is obtained from genuine saturation and Lemma 3.2. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace DiamondIntegral.Section6.RVLocalLinearity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem at_named_radius {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hB : B.imaginary = ∅) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α < β)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ gammaBall a α true})
    (hβ : FullGammaSyntax.Scalar B {β}) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) :
    ∃ c : VFType (M := M), c.val ∈ gammaBall a α true ∧
      ∃ hsub : gammaBall c β true ⊆ gammaBall a α true,
      ∃ t : CanonicalRV.RVSort M, t.val ≠ iRVZero ∧
        RVLinearity.RVLinear (gammaBall c β true) f (fun x hx => hfVF x (hsub hx)) t := by
  obtain ⟨H,hH,hcosets⟩ := FullGammaRadius.gamma_subgroup B β hβ true
  let T := BetaSubballFamilies.family H (gammaBall a α true)
  have hT := BetaSubballFamilies.definable B H hH hA
  have hInf := BetaSubballFamilies.infinite h00 H β hcosets a α hαβ
  have hdis := BetaSubballFamilies.disjoint H (gammaBall a α true)
  have hne (i : BallImaginaries.Ball M) (_ : i ∈ T) : (BallImaginaries.underlying i).Nonempty :=
    CanonicalBallSupport.encodedBall_nonempty (BallCodeGeometry.underlying_isBall i)
  obtain ⟨i,hi,hat⟩ := AtomicBallFamilyChoice.exists_atomic hs B hB hsmall T hT hInf hne hdis
  obtain ⟨c,hc⟩ := BetaSubballFamilies.member_presentation H β hcosets hi
  let C := B.adjoin (Sum.inl i)
  have hsub : gammaBall c β true ⊆ gammaBall a α true := by
    have h := hi.2
    change BallImaginaries.underlying i ⊆ gammaBall a α true at h
    rwa [hc] at h
  have hat' : AdjoinBall.AtomicOver C (gammaBall c β true) := hc ▸ hat
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  have hfC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (gammaBall a α true) f) :=
    FullBaseAtomicity.OverBase.mono hf Set.Subset.rfl (Set.subset_insert _ _)
  have hm := FullBaseAtomicity.OverBase.preimage_comp hat'.1 (fun _ : Fin 1 => (0 : Fin 2))
  have hgraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (gammaBall c β true) f) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hfC)
    intro z
    change (z 0 ∈ gammaBall c β true ∧ z 0 ∈ gammaBall a α true ∧ z 1 = f (z 0)) ↔
      (z 0 ∈ gammaBall c β true ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
  have hVF : ∀ x ∈ gammaBall c β true, iVF (f x) := fun x hx => hfVF x (hsub hx)
  have hInj : Set.InjOn f (gammaBall c β true) := fun _ hx _ hy he => hinj (hsub hx) (hsub hy) he
  have ho : PaperBalls.IsOpenBall (gammaBall c β true) := Or.inr ⟨c,β,rfl⟩
  obtain ⟨t,ht,hLin⟩ := RVLinearity.lemma_3_18 hκ hs C hsmall h00 δ hδC hδ1 ho hat' f hgraph hVF hInj
  exact ⟨c,hsub (BallEnlargementGeometry.gammaBall_centre_mem c β true),hsub,t,ht,hLin⟩

end DiamondIntegral.Section6.RVLocalLinearity
