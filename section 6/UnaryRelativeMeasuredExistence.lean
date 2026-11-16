import «section 6».UnaryRelativeMatchingPrecomposition
import «section 6».UnaryUnitConjugateJacobian
import «section 6».MeasuredProperPreparation
import «section 6».FiniteRVFiberTransport

/-! The complete auxiliary variable-aperture measured unary matching
construction starts with the original proper objects and actual Gamma
forms. Initial measured preparation is constructed and attached to the
finite first-zero executions. No prepared-input or disc witness remains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_relative_measured_matching_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    Nonempty (UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) (S : Set M) := Fin.elim0
  let D : Fin 0 → DefSet (rawMixedSpace (M := M) 1 s) (S : Set M) := Fin.elim0
  obtain ⟨P⟩ := measured_proper_preparation h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' A hA C (fun i => i.elim0) (fun i => i.elim0) ω hωLevels
  obtain ⟨Q⟩ := measured_proper_preparation h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' B hB D (fun i => i.elim0) (fun i => i.elim0) σ hσLevels
  have hPHome := P.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hQHome := Q.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  let inv := P.map.inverse (P.special.bijective h00)
  let g := Q.map.comp (f.comp inv)
  have hInvHome : ProperCovariantHomeomorphism inv :=
    inverse_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ P.map hPHome
  have hg : ProperCovariantHomeomorphism g :=
    lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hInvHome hf) hQHome
  have hPFinite := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall P.map (P.special.bijective h00) hFinite
  have hPConst (p q : P.target) (hTags : p.val.2=q.val.2) : P.form p=P.form q := by
    apply Subtype.ext
    have h := P.constant p.val p.property q.val q.property hTags
    simpa only [gammaFormExtension_at] using h
  have hQConst (p q : Q.target) (hTags : p.val.2=q.val.2) : Q.form p=Q.form q := by
    apply Subtype.ext
    have h := Q.constant p.val p.property q.val q.property hTags
    simpa only [gammaFormExtension_at] using h
  have hGCommutes (p : A) : g (P.map p)=Q.map (f p) := by
    change Q.map (f (P.map.inverse _ (P.map p)))=Q.map (f p)
    rw [Map.inverse_apply]
  have hGGeneric (p : P.target) (hp : AlgebraicIndependent (vfParameterField (S : Set M)) p.val.1) :
      ∃ J : VF M,HasMixedVFJacobianAt g p J ∧
        vfValue J=(gammaMapValue P.form p/gammaMapValue Q.form (g p)).val := by
    let a := inv p
    have hInvInj : Function.Injective inv := by
      intro x y he
      have h := congrArg P.map he
      simpa only [inv,Map.apply_inverse] using h
    have ha := independent_map_of_finiteFibres hc inv (Map.finiteFibres_of_injective hInvInj) p hp
    obtain ⟨J,hJ,hVal⟩ := hGeneric a ha
    have hGJ := unary_unit_preparation_conjugate_jacobian h00 hc hκ.le hs hsmall hv
      P.map Q.map (.original P.special) (.original Q.special) f hf.bijective p hp J hJ
    have hPAt : P.form p=ω a := by
      have hp' : P.map a=p := Map.apply_inverse P.map (P.special.bijective h00) p
      rw [← hp']
      exact Subtype.ext (P.transport a)
    have hQAt : Q.form (g p)=σ (f a) := Subtype.ext (Q.transport (f a))
    have hRatio : gammaMapValue P.form p/gammaMapValue Q.form (g p)=
        gammaMapValue ω a/gammaMapValue σ (f a) := by
      unfold gammaMapValue
      rw [hPAt,hQAt]
    refine ⟨J,hGJ,?_⟩
    rw [hRatio]
    exact hVal
  obtain ⟨R⟩ := unary_relative_measured_prepared_matching_exists h00 hc hκ hs hv S B₀ hsmall hnt
    P.target Q.target g hg P.proper P.doublyBounded P.prepared P.tagged
    Q.proper Q.doublyBounded Q.prepared Q.tagged hPFinite P.form Q.form hPConst hQConst hGGeneric
  exact ⟨R.precompose P.map Q.map (.original P.special) (.original Q.special) hGCommutes
    h00 ω σ P.form Q.form (fun p => Subtype.ext (P.transport p)) (fun p => Subtype.ext (Q.transport p))⟩

end DiamondIntegral.Section6
