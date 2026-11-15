import IntegrationSection5.RelativeGammaTrace
import IntegrationSection5.GammaTraceExtension
import IntegrationSection5.GammaTraceRestriction

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
theorem gamma_head_preparation_certified_trace {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real)
    {S : Set M} (hPS : P.real ⊆ S) {n m : ℕ} (A : DefSet (M := M) S (n+1) m)
    (hA : GammaSetDefinable P (carrier A)) :
    ∃ T : HeadPreparation A, SpecialRelativeBoundary T.map 0 none (some false) ∧
      (∃ j, Tagged (carrier T.target) 0 j) ∧ GammaSetDefinable P (carrier T.target) ∧
        GammaGraphDefinable P (pointMapGraph T.map) ∧
        ∃ W : UniformRelativeTrace S (n+1) A T.target, GammaUniformTrace (G := P) W ∧ ∀ a, W.toMap a = T.map a := by
  let X := PresentedSet.univ (pointSpace (M := M) (n+1) m) P.real
  let L := gammaLogicInput P
  let r : Point (M := M) (n+1) m → Point (M := M) 0 0 → Prop := fun p _ => p ∈ carrier A
  have hr : GammaGraphDefinable P r := by
    apply GammaGraphDefinable.congr (L.restrict_graph hA (L.real_map_graph (constantRVMap X 0)))
    intro p q
    exact ⟨fun h => h.1,fun hp => ⟨hp,⟨p,Set.mem_univ _⟩,rfl,Subsingleton.elim _ _⟩⟩
  obtain ⟨V,hVb,hTag,hUniform,U,hTraceValues⟩ := relative_prepare_gamma_relation_trace hs h00 P hsmall F r hr
  let f := extendPointMap V.map hPS
  let hAX : carrier A ⊆ carrier (extendBase X hPS) := Set.subset_univ _
  let B := restrictPointImage f A hAX
  let g := restrictPointMap f A hAX
  have hf : Function.Bijective f := V.bijective
  have hgb : SpecialRelativeBoundary g 0 none (some false) :=
    specialRelativeBoundary_restrict f A hAX (specialRelativeBoundary_extendBase V.map hPS hVb)
  have hU : ∀ b c : extendBase V.target hPS, SameRV b.val c.val → TailEq b.val c.val →
      ((Map.inverse f hf b).val ∈ carrier A ↔ (Map.inverse f hf c).val ∈ carrier A) := by
    intro b c he ht
    exact hUniform ⟨b.val,b.property⟩ ⟨c.val,c.property⟩ he ht (Fin.elim0,Fin.elim0)
  have hB : HeadSaturated (carrier B) := restrictPointImage_headSaturated f hf V.saturated A hAX hU
  let T : HeadPreparation A := ⟨V.arity,B,g,specialRelativeBoundary_forget hgb,hB⟩
  have hgDef : GammaGraphDefinable P (pointMapGraph g) := by
    apply GammaGraphDefinable.congr (L.restrict_graph hA (L.real_map_graph V.map))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hv⟩
      have ha' : a = ⟨p,Set.mem_univ _⟩ := Subtype.ext ha
      rw [ha'] at hv
      exact ⟨⟨p,hp⟩,rfl,hv⟩
    · rintro ⟨a,rfl,hg⟩
      exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,hg⟩
  have hBDef : GammaSetDefinable P (carrier B) := by
    have h := L.image_graph hgDef
    convert h using 1
    ext q
    constructor
    · intro hq
      obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget hgb)).2 ⟨q,hq⟩
      exact ⟨a.val,a,rfl,congrArg (fun z : B => z.val) ha⟩
    · rintro ⟨p,a,rfl,he⟩
      exact he ▸ (g a).property
  let UE := U.extendBase hPS
  have hUE := GammaUniformTrace.extendBase U (gamma_uniform_trace_of_real U) hPS
  obtain ⟨K,W,hWG,hW⟩ := UE.gamma_restrict_source hUE A hAX hA
  have hVal (a : A) : (W.toMap a).val = (g a).val :=
    (hW a).trans ((U.extendBase_val hPS ⟨a.val,hAX a.property⟩).trans
      (congrArg (fun z : V.target => z.val) (hTraceValues ⟨a.val,Set.mem_univ _⟩)))
  have hEq : K = B := by
    apply PresentedSet.eq_of_carrier_eq
    ext p
    constructor
    · intro hp
      obtain ⟨a,ha⟩ := W.bijective.2 ⟨p,hp⟩
      have he : (g a).val = p := (hVal a).symm.trans (congrArg (fun z : K => z.val) ha)
      exact he ▸ (g a).property
    · intro hp
      obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget hgb)).2 ⟨p,hp⟩
      have he : (W.toMap a).val = p := (hVal a).trans (congrArg (fun z : B => z.val) ha)
      exact he ▸ (W.toMap a).property
  refine ⟨T,hgb,?_,hBDef,hgDef,W.castTarget hEq,GammaUniformTrace.castTarget W hWG hEq,?_⟩
  · obtain ⟨j,hj⟩ := hTag
    refine ⟨j,?_⟩
    rintro _ ⟨a,rfl⟩
    exact hj (f ⟨a.val,hAX a.property⟩).val (f ⟨a.val,hAX a.property⟩).property
  · intro a
    exact Subtype.ext ((W.castTarget_val hEq a).trans (hVal a))

end IntegrationInACVF.Section5
