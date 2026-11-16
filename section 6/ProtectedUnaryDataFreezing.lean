import «section 6».NamedVFValues

/-! Construct finite original-base freezing for a complete unary data
value, with product conditions on both the unary pieces and arbitrary
higher-dimensional protected pieces. The output row is not assumed bounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m t k l : ℕ} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_protected_unary_data_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m t) S) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (j : Fin m) (Q : Finset (VF M)) (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
    (ω : Mixed M 1 r → T)
    (hControl : ∀ a ρ,(∀ z ∈ Q,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,ω ((fun _ : Fin 1 => x),u)=ω ((fun _ : Fin 1 => y),u)) :
    ∃ F : FMT.FocusFreezingData A,∃ ρ : Gamma M,
      S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}} ∧
      (∀ i,∀ D : F.balls,FMT.CoordinateProductDomain (C i).carrier (FMT.vfOpenBall D.val) (F.centers D) 0) ∧
      (∀ i,∀ D : F.balls,FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall D.val) (F.centers D) j) ∧
      (∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => ρ) a b → FMT.frozenUnaryValue F.balls F.centers ω (a,u)=
          FMT.frozenUnaryValue F.balls F.centers ω (b,u)) ∧
      UnaryValueRootControl (G := G) (UnaryRootFamily.fromObstacles A Q hQ)
        (FMT.frozenUnaryValue F.balls F.centers ω) := by
  let L : Fin (k+1) → Set (Mixed M 1 r) := Fin.cons A.carrier (fun i => (C i).carrier)
  obtain ⟨α,hα,hα1,hLA⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ L
    (Fin.cases hA hC)
  obtain ⟨β,hβ,hβ1,hPB⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    (fun i => (P i).carrier) hP
  let δ := max α β
  have hδ := gamma_max_named α β hα hβ
  have hInvA (u) : AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) :=
    (hLA 0 u).larger_radius (fun _ => le_max_left _ _)
  have hInvC (i) (u) : AlphaInvariant (fun _ => δ) (vfFibre (C i).carrier u) :=
    (hLA i.succ u).larger_radius (fun _ => le_max_left _ _)
  have hInvP (i) (u) : AlphaInvariant (fun _ => δ) (vfFibre (P i).carrier u) :=
    (hPB i u).larger_radius (fun _ => le_max_right _ _)
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ
    (hα1.trans (le_max_left _ _)) hδ
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
    (fun i => FMT.exceptionalOpenBalls_product_domain hv (C i).carrier δ (hInvC i) E s hs0 hδs.le c hcMem 0),
    (fun i => FMT.exceptionalOpenBalls_product_domain hv (P i).carrier δ (hInvP i) E s hs0 hδs.le c hcMem j),?_,?_⟩
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
