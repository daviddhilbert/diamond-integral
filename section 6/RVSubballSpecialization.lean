import «section 6».RVLocalLinearity
import Section3.SmallFiniteParameters

/-! Only finitely many real codes are named inside the proof. The original
map may be defined over any genuine real/Gamma/ball base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace DiamondIntegral.Section6.RVSubballSpecialization

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem inside_open_ball {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    {A : Set M} (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (a : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α < β)
    (hPsub : gammaBall a α true ⊆ A) :
    ∃ c : VFType (M := M), c.val ∈ gammaBall a α true ∧
      ∃ hsub : gammaBall c β true ⊆ A, ∃ t : CanonicalRV.RVSort M, t.val ≠ iRVZero ∧
        RVLinearity.RVLinear (gammaBall c β true) f (fun x hx => hfVF x (hsub hx)) t := by
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
        (ImaginaryBaseImages.graphOn A f) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hf
  obtain ⟨F,hF,hd⟩ := hex
  obtain ⟨δ,hδ1⟩ := exists_gt (1 : Values.Gamma (M := M))
  obtain ⟨tα,htα0,htα⟩ := Values.gamma_has_nonzero_representative α
  obtain ⟨tβ,htβ0,htβ⟩ := Values.gamma_has_nonzero_representative β
  obtain ⟨tδ,htδ0,htδ⟩ := Values.gamma_has_nonzero_representative δ
  let S := B.real ∪ F
  let codes : Fin 4 → M := ![a.val,tα.val,tβ.val,tδ.val]
  let Q := S ∪ Set.range codes
  let C : FullBaseAtomicity.Base (M := M) := ⟨Q,∅⟩
  have hsmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall F hF
  have hsmallQ : Cardinal.mk Q < κ := small_union_range hκ S hsmallS codes
  have haQ : a.val ∈ C.real := Or.inr ⟨0,rfl⟩
  have hα : FullGammaSyntax.Scalar C {α} :=
    NamedBallSetup.gamma_scalar_of_code h00 C α tα htα0 htα (Or.inr ⟨1,rfl⟩)
  have hβ : FullGammaSyntax.Scalar C {β} :=
    NamedBallSetup.gamma_scalar_of_code h00 C β tβ htβ0 htβ (Or.inr ⟨2,rfl⟩)
  have hδ : FullGammaSyntax.Scalar C {δ} :=
    NamedBallSetup.gamma_scalar_of_code h00 C δ tδ htδ0 htδ (Or.inr ⟨3,rfl⟩)
  have hP := NamedBallSetup.gammaBall_definable C a haQ α hα
  have hfC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn A f) := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := CanonicalStructure.normalize (M := M)
    exact hd.mono Set.subset_union_left
  have hm := FullBaseAtomicity.OverBase.preimage_comp hP (fun _ : Fin 1 => (0 : Fin 2))
  have hgraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (gammaBall a α true) f) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hfC)
    intro z
    change (z 0 ∈ gammaBall a α true ∧ z 0 ∈ A ∧ z 1 = f (z 0)) ↔
      (z 0 ∈ gammaBall a α true ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hPsub h.1,h.2⟩⟩
  obtain ⟨c,hc,hsub,t,ht,hLin⟩ := RVLocalLinearity.at_named_radius hκ hs C rfl hsmallQ
    h00 δ hδ hδ1 a α β hαβ hP hβ f hgraph
    (fun x hx => hfVF x (hPsub hx)) (fun _ hx _ hy he => hinj (hPsub hx) (hPsub hy) he)
  exact ⟨c,hc,hsub.trans hPsub,t,ht,hLin⟩

end DiamondIntegral.Section6.RVSubballSpecialization
