import IntegrationSection5.GammaHeadCertifiedTrace
import IntegrationSection5.GammaTraceLift
import IntegrationSection5.GammaProgramTraceHelper

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M}

def GammaProgramHasUniformTraces {a b c : ℕ} {A : DefSet (M := M) S a b} {U : DefSet (M := M) S 0 c} :
    OrderedContractionProgram S A U → Prop
  | .zero A => GammaSetDefinable G (carrier A)
  | .step T tail => (∃ W : UniformRelativeTrace S _ _ T.target, GammaUniformTrace (G := G) W ∧ ∀ a, W.toMap a = T.map a) ∧
      GammaProgramHasUniformTraces tail

theorem gamma_ordered_contraction_program_gamma_traced {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (hGS : G.real ⊆ S) (n : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S n m), GammaSetDefinable G (carrier A) →
      ∃ l, ∃ U : DefSet (M := M) S 0 l, ∃ T : OrderedContractionProgram S A U,
        GammaProgramDefinable G T ∧ GammaProgramHasUniformTraces (G := G) T := by
  induction n with
  | zero =>
    intro m A hA
    exact ⟨m,A,.zero A,hA,hA⟩
  | succ n ih =>
    intro m A hA
    obtain ⟨T,_,_,hB,hT,W,hWG,hW⟩ := gamma_head_preparation_certified_trace hs h00 G hsmall F hGS A hA
    obtain ⟨l,U,R,hR,hTrace⟩ := ih T.contractedSet (gamma_headImage T.target hB)
    exact ⟨l,U,.step T R,⟨hT,hB,hR⟩,⟨⟨W,hWG,hW⟩,hTrace⟩⟩

theorem program_natural_gamma_trace {n m l : ℕ} {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) (hT : GammaProgramHasUniformTraces (G := G) T) : ∃ R : ProgramNaturalTrace T, GammaUniformTrace (G := G) R.trace := by
  induction T with
  | zero A => exact ⟨⟨_,A,.nil A,id,fun _ => rfl⟩,hT⟩
  | @step n m l A U T tail ih =>
    obtain ⟨V,hVG,hV⟩ := hT.1
    obtain ⟨R,hRG⟩ := ih hT.2
    let H := coordinateCanonicalImage T.target 0
    let can := coordinateCanonicalBijection T.target 0
    have hSub : ∀ p ∈ carrier H, vfRVProjection Fin.succ id p ∈ carrier T.contractedSet := by
      rintro p ⟨a,rfl⟩
      exact ⟨a,headKeyMap_apply T.target a⟩
    have hTargetG := (gammaUniformTraceIso V hVG).target_definable (gammaLogicInput G)
    have hHG := gamma_coordinateCanonicalImage T.target hTargetG 0
    obtain ⟨b,K,σ,W,hWG,hW,hOther⟩ := R.trace.gamma_lift_projection hRG H Fin.succ (Fin.succ_injective n) id hSub hHG
    let Q : UniformRelativeTrace S (n+1) T.target K := .canonical 0 W
    let L := V.append Q
    let ρ : Fin l → Fin b := σ ∘ R.projection
    have hLG := gamma_uniform_trace_append V Q hVG ⟨hTargetG,hWG⟩
    refine ⟨⟨b,K,L,ρ,?_⟩,hLG⟩
    intro a
    have hVa : V.toMap a = T.map a := hV a
    have hVal : (L.toMap a).val = (W.toMap (can (T.map a))).val := by
      rw [UniformRelativeTrace.append_apply,hVa]
      rfl
    have hTail : vfRVProjection Fin.succ ρ (W.toMap (can (T.map a))).val =
        (tail.naturalMap (T.contractionMap a)).val := by
      have hw := congrArg (fullRVProjection R.projection) (hW (can (T.map a)))
      have he : (⟨vfRVProjection Fin.succ id (can (T.map a)).val,hSub _ (can (T.map a)).property⟩ : T.contractedSet) =
          T.contractionMap a := by
        apply Subtype.ext
        exact (headKeyMap_apply T.target (T.map a)).symm
      rw [he] at hw
      exact hw.trans (R.square (T.contractionMap a))
    rw [hVal]
    change fullRVProjection ρ (W.toMap (can (T.map a))).val =
      insertHead (vfAt (T.map a).val 0) (tail.naturalMap (T.contractionMap a)).val
    apply Prod.ext
    · funext j
      cases j using Fin.cases with
      | zero => exact hOther (can (T.map a)) 0 (fun i => Fin.succ_ne_zero i)
      | succ j => exact congrFun (congrArg (fun z : Point (M := M) n l => z.1) hTail) j
    · exact congrArg (fun z : Point (M := M) n l => z.2) hTail

end IntegrationInACVF.Section5
