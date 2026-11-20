import «section 7».Lemma714ProdTop
import «section 7».Lemma714Comps
import «section 6».MeasuredFrozenUnaryRVDataPreparation

/-! Lemma 7.14, part 23: freezing with two protected measured ambients.

Step 2 of the proof. Section 6's `exists_measured_protected_unary_data_freezing`
freezes a unary data value on finitely many discs around its obstacles, with
the discs small enough that given proper invariant sets and the levels of one
Γ-form are products over them. Lemma 7.14 needs two ambients with their own
forms (`A'`, `A''` transported to the prepared projection), so this is the same
construction with two measured ambients (`freezing_two`): the freezing radius is
the maximum of the uniform invariance radii of the base and of both ambients
and their form levels. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r t₁ t₂ : ℕ} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem freezing_two
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier)
    (B₁ : DefSet (rawMixedSpace (M := M) 1 t₁) S) (hB₁ : ProperInvariant S B₁.carrier)
    (θ₁ : Map B₁ (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hL₁ : ∀ u γ,IsOpen {x : Fin 1 → VF M | (x,u) ∈ B₁.carrier ∧ gammaFormExtension θ₁ (x,u)=γ})
    (B₂ : DefSet (rawMixedSpace (M := M) 1 t₂) S) (hB₂ : ProperInvariant S B₂.carrier)
    (θ₂ : Map B₂ (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hL₂ : ∀ u γ,IsOpen {x : Fin 1 → VF M | (x,u) ∈ B₂.carrier ∧ gammaFormExtension θ₂ (x,u)=γ})
    (Q : Finset (VF M)) (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
    (ω : Mixed M 1 r → T)
    (hControl : ∀ a ρ,(∀ z ∈ Q,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,ω ((fun _ : Fin 1 => x),u)=ω ((fun _ : Fin 1 => y),u)) :
    ∃ F : FMT.FocusFreezingData A,∃ ρ : Gamma M,
      S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}} ∧
      (∀ D : F.balls,FMT.CoordinateProductDomain B₁.carrier (FMT.vfOpenBall D.val) (F.centers D) 0) ∧
      (∀ γ,∀ D : F.balls,FMT.CoordinateProductDomain
        {p | p ∈ B₁.carrier ∧ gammaFormExtension θ₁ p=γ} (FMT.vfOpenBall D.val) (F.centers D) 0) ∧
      (∀ D : F.balls,FMT.CoordinateProductDomain B₂.carrier (FMT.vfOpenBall D.val) (F.centers D) 0) ∧
      (∀ γ,∀ D : F.balls,FMT.CoordinateProductDomain
        {p | p ∈ B₂.carrier ∧ gammaFormExtension θ₂ p=γ} (FMT.vfOpenBall D.val) (F.centers D) 0) ∧
      (∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => ρ) a b → FMT.frozenUnaryValue F.balls F.centers ω (a,u)=
          FMT.frozenUnaryValue F.balls F.centers ω (b,u)) ∧
      UnaryValueRootControl (G := G) (UnaryRootFamily.fromObstacles A Q hQ)
        (FMT.frozenUnaryValue F.balls F.centers ω) := by
  obtain ⟨α,hα,hα1,hLA⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    (fun _ : Fin 1 => A.carrier) (fun _ => hA)
  obtain ⟨ε₁,hε₁,hε₁1,hInvB₁,hInvL₁⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hB₁ (gammaFormExtension θ₁) (gammaFormExtension_graph_definable θ₁) hL₁
  obtain ⟨ε₂,hε₂,hε₂1,hInvB₂,hInvL₂⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hB₂ (gammaFormExtension θ₂) (gammaFormExtension_graph_definable θ₂) hL₂
  let δ := max (max α ε₁) ε₂
  have hδ := gamma_max_named (max α ε₁) ε₂ (gamma_max_named α ε₁ hα hε₁) hε₂
  have hαδ : α ≤ δ := (le_max_left α ε₁).trans (le_max_left _ ε₂)
  have hε₁δ : ε₁ ≤ δ := (le_max_right α ε₁).trans (le_max_left _ ε₂)
  have hε₂δ : ε₂ ≤ δ := le_max_right _ ε₂
  have hInvA (u) : AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) := (hLA 0 u).larger_radius (fun _ => hαδ)
  have hIB₁ (u) : AlphaInvariant (fun _ => δ) (vfFibre B₁.carrier u) := (hInvB₁ u).larger_radius (fun _ => hε₁δ)
  have hIB₂ (u) : AlphaInvariant (fun _ => δ) (vfFibre B₂.carrier u) := (hInvB₂ u).larger_radius (fun _ => hε₂δ)
  have hIL₁ (γ) (u) : AlphaInvariant (fun _ => δ)
      (vfFibre {p | p ∈ B₁.carrier ∧ gammaFormExtension θ₁ p=γ} u) :=
    (hInvL₁ γ u).larger_radius (fun _ => hε₁δ)
  have hIL₂ (γ) (u) : AlphaInvariant (fun _ => δ)
      (vfFibre {p | p ∈ B₂.carrier ∧ gammaFormExtension θ₂ p=γ} u) :=
    (hInvL₂ γ u).larger_radius (fun _ => hε₂δ)
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ
    (hα1.trans hαδ) hδ
  let E : Set (Fin 1 → VF M) := {a | a 0 ∈ Q}
  have hEeq : E=(fun x : VF M => fun _ : Fin 1 => x) '' (Q : Set (VF M)) := by
    ext a
    constructor
    · intro ha
      exact ⟨a 0,ha,by funext i; fin_cases i; rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact hx
  have hEF : E.Finite := by rw [hEeq]; exact Q.finite_toSet.image _
  have hEdef : S.Definable LRV (vfValues '' E) := by
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q : Set (VF M))} at hQ
    convert hQ using 1
    ext z
    constructor
    · rintro ⟨a,ha,he⟩
      exact ⟨a 0,ha,congrFun he 0⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨fun _ => x,hx,by funext i; fin_cases i; exact he⟩
  let balls := FMT.exceptionalOpenBalls E s hs0
  have hBF := FMT.exceptionalOpenBalls_finite E hEF s hs0
  have hBdef := FMT.exceptionalOpenBalls_definable E hEdef s hs0 hsdef
  have hRadius := FMT.exceptionalOpenBalls_sameRadius hv E s hs0
  have hSep := FMT.sameOpenRadius_separated balls s hRadius
  obtain ⟨c,hcMem,hcDef⟩ := FMT.exceptionalOpenBalls_centers hc h00 hv E hEF hEdef s hs0 hsdef
  have hProdA := FMT.exceptionalOpenBalls_product_domain hv A.carrier δ hInvA E s hs0 hδs.le c hcMem 0
  let F : FMT.FocusFreezingData A := ⟨balls,hBF,c,hcMem,hSep,hBdef,hcDef,hProdA⟩
  have hCover (z : VF M) (hz : z ∈ Q) : ∃ D : balls,z ∈ FMT.vfOpenBall D.val :=
    FMT.exceptionalOpenBalls_cover E s hs0 (fun _ => z) hz
  have hHit (D : balls) : ∃ z ∈ Q,z ∈ FMT.vfOpenBall D.val := by
    obtain ⟨a,ha,he⟩ := D.property
    refine ⟨a 0,ha,?_⟩
    change (a 0).val ∈ OpenBallCodes.underlying D.val
    rw [← he]
    exact OpenBallCodes.raw_center_mem _ (FMT.pointedOpenBallCode (a 0) s hs0).property
  have hFrozen := FMT.frozenUnaryValue_obstacle_control balls c hSep s hs0 hRadius Q hCover hHit ω hControl
  refine ⟨F,finiteValue s hs0,finiteValue_named s hs0 hsdef,
    FMT.exceptionalOpenBalls_product_domain hv B₁.carrier δ hIB₁ E s hs0 hδs.le c hcMem 0,
    (fun γ => FMT.exceptionalOpenBalls_product_domain hv _ δ (hIL₁ γ) E s hs0 hδs.le c hcMem 0),
    FMT.exceptionalOpenBalls_product_domain hv B₂.carrier δ hIB₂ E s hs0 hδs.le c hcMem 0,
    (fun γ => FMT.exceptionalOpenBalls_product_domain hv _ δ (hIL₂ γ) E s hs0 hδs.le c hcMem 0),?_,?_⟩
  · intro u a ha b hb hab
    have hClose : Valued.v (a 0-b 0)<Valued.v s := by
      apply lt_of_not_ge
      intro hn
      have hPred := (hv s (a 0-b 0)).mpr hn
      exact (not_le_of_gt (hab 0)) ((Values.vf_pred_iff_gamma_le s (a 0-b 0)).mp hPred)
    have h := FMT.frozenUnaryValue_uniform_constancy balls c hSep s hs0 hRadius Q hCover ω hControl
      (a 0) (b 0) ((Valued.v.map_sub_swap _ _).trans_lt hClose) u
    have hAeta : (fun _ : Fin 1 => a 0)=a := by funext i; fin_cases i; rfl
    have hBeta : (fun _ : Fin 1 => b 0)=b := by funext i; fin_cases i; rfl
    simpa only [hAeta,hBeta] using h
  · intro u a ρ hAmbient hAvoid x hx y hy
    apply hFrozen a ρ ?_ x hx y hy u
    intro z hz hzd
    exact hAvoid z ((UnaryRootFamily.mem_fibre _ u z).mpr ⟨hAmbient z hzd,hz⟩) hzd

end DiamondIntegral.Section6
