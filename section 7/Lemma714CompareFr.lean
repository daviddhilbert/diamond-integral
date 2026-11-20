import «section 7».Lemma714IdentFr

/-! Lemma 7.14, part 30: comparison of the frozen set with the standard
contraction.

For a unary normalized measured contraction `F'` of `(A, ω)` and a guarded `A`,
the map `(Φ ⋉ A) ∘ F'⁻¹` from the target of `F'` to the frozen set `Φ ⋉ A` is a
label-preserving proper covariant homeomorphism with generic unit Jacobian
(`prodMap_unit_derivative`, `inverse_generic_unit_derivative`), and the forms
agree along it. The head-start Lemma 7.13 (`muIsp_head`) gives `μIsp` of the two
head-start classes (`muIsp_compare`). Level sets of label-constant forms on
proper invariant sets are open (`levels_open_of_proper`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section6
open DiamondIntegral.Section7.Lemma714Prod DiamondIntegral.Section7.Lemma714Schema DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Level sets of a label-constant form on a proper invariant set are open.** -/
theorem levels_open_of_proper (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) n r) S} (hX : ProperInvariant S X.carrier)
    (σ : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hσ : ∀ p q : X, p.val.2 = q.val.2 → σ p = σ q)
    (u : Fin r → RVInfinity M) (γ : rawGammaPresentation.Carrier) :
    IsOpen {a : Fin n → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension σ (a, u) = γ} := by
  by_cases h : ∃ a, (a, u) ∈ X.carrier ∧ gammaFormExtension σ (a, u) = γ
  · obtain ⟨a₀, h₀, hγ⟩ := h
    have he : {a : Fin n → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension σ (a, u) = γ} = vfFibre X.carrier u := by
      ext a
      constructor
      · exact And.left
      · intro ha
        refine ⟨ha, ?_⟩
        have e1 : gammaFormExtension σ (a, u) = (σ ⟨_, ha⟩).val := gammaFormExtension_at σ ⟨_, ha⟩
        have e2 : gammaFormExtension σ (a₀, u) = (σ ⟨_, h₀⟩).val := gammaFormExtension_at σ ⟨_, h₀⟩
        rw [e1, hσ ⟨_, ha⟩ ⟨_, h₀⟩ rfl, ← e2]
        exact hγ
    rw [he]
    exact (hX.clopen_fibres hv u).isOpen
  · have he : {a : Fin n → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension σ (a, u) = γ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun a ha => h ⟨a, ha⟩
    rw [he]
    exact isOpen_empty

/-- **The product map has the derivative of the base map.** -/
theorem prodMap_unit_derivative (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {r s : ℕ} {P : DefSet (rawMixedSpace (M := M) 1 0) S} {Q : DefSet (rawMixedSpace (M := M) 1 s) S}
    (g : Map P Q) {A : DefSet (rawMixedSpace (M := M) 1 r) S} (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)
    (hA : ProperInvariant S A.carrier) (p : A) (hg : HasMixedUnitDerivativeAt g (baseMap hAP p)) :
    HasMixedUnitDerivativeAt (prodMap g hAP).toImage p := by
  obtain ⟨L, ⟨F, ⟨ρ, hρ⟩, hF⟩, hdet⟩ := hg
  obtain ⟨σ, hσ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hA.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨L, ⟨F, ⟨max σ ρ, fun z hz => ?_⟩, hF⟩, hdet⟩
  have hzA : (z, p.val.2) ∈ A.carrier := hσ (vfBall_anti (le_max_left σ ρ) hz)
  obtain ⟨hzP, hval⟩ := hρ z (vfBall_anti (le_max_right σ ρ) hz)
  refine ⟨hzA, ?_⟩
  have hb : baseMap hAP ⟨(z, p.val.2), hzA⟩ = ⟨(z, (baseMap hAP p).val.2), hzP⟩ :=
    Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
  change (prodMap g hAP ⟨(z, p.val.2), hzA⟩).val = (F z, (prodMap g hAP p).val.2)
  rw [prodMap_apply, prodMap_apply, hb, hval]

section Compare
variable {T : LRV.Substructure M} {P : DefSet (rawMixedSpace (M := M) 1 0) (T : Set M)} (Z : Frozen (G := G) P)
  (hc : CanonicalStructure.IsCanonical (M := M)) {r k : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r) (N : ℕ)
  (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)
  {κ : Cardinal} (h00 : M ⊨ Axioms.ACVF00) (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hA : ProperInvariant (T : Set M) A.carrier)
  (hFin : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
  (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include hV hVT hTV hnt in
/-- **The standard contraction and the frozen set have `μIsp`-related head-start
classes.** -/
theorem muIsp_compare (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) {e : Equiv.Perm (Fin (0 + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A ω e) :
    MuIsp (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F' π hFin))
      (clsH hc (frHGood Z hc ω π N hAP h00 hκ hs hv hsmall hA hFin hG hRC)) := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let gfr := frHGood Z hc ω π N hAP h00 hκ hs hv hsmall hA hFin hG hRC
  have hF := F'.homeomorphism h00 hc lin hκ hs hv hsmall hΓ
  let Finv := F'.map.inverse hF.bijective
  have hFinv : ProperCovariantHomeomorphism (G := G) Finv := DiamondGroupoid.homeo_inverse hF
  have hPΦ := prodMap_properHomeomorphism Z.Φ hAP hv h00 hc hκ hs lin hsmall hΓ Z.homeo hA
  have hPY := prodMap_image_properInvariant Z.Φ hAP hv h00 hc hκ hs Z.homeo hA
  have hPX : ProperInvariant (T : Set M) F'.target.carrier := F'.preparedContraction.lift.originalTarget_proper
  refine muIsp_head hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ (targetHGood hc h00 hκ hs hv hsmall hΓ F' π hFin) gfr
    hPX hPY ((prodMap Z.Φ hAP).toImage.comp Finv)
    (lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ hFinv hPΦ) ?_
    (levels_open_of_proper hv hPX F'.form F'.form_same_tags)
    (levels_open_of_proper hv hPY gfr.form gfr.form_labels) ?_
  · intro p i
    change (prodMap Z.Φ hAP (Finv p)).val.2 (Fin.natAdd (1 + Z.sk) (π i)) = p.val.2 (F'.oldIndex (π i))
    rw [prodMap_labels]
    have h := F'.retained (Finv p) (π i)
    rw [Map.apply_inverse] at h
    exact h.symm
  · intro a hInd
    have hU1 : HasMixedUnitDerivativeAt Finv a :=
      inverse_generic_unit_derivative h00 hc hκ.le hs hsmall hv F'.map hF.bijective
        (fun p hp => F'.normalization.normalizedOrderedMap_generic_unit h00 hc hκ hs hv F'.preparedContraction.lift p hp)
        a hInd
    have hInj : Function.Injective Finv := (DiamondGroupoid.homeo_inverse hF).bijective.1
    have hInd' := independent_map_of_finiteFibres hc Finv (Map.finiteFibres_of_injective hInj) a hInd
    have hU2 : HasMixedUnitDerivativeAt (prodMap Z.Φ hAP).toImage (Finv a) :=
      prodMap_unit_derivative hv Z.Φ hAP hA (Finv a)
        (Z.chain.unit_derivative_of_independent h00 hc hκ.le hs hsmall hv (baseMap hAP (Finv a)) hInd')
    refine ⟨1, (hU2.comp hU1).partialJacobian, ?_⟩
    have hform : gammaMapValue gfr.form ((prodMap Z.Φ hAP).toImage.comp Finv a) = gammaMapValue F'.form a := by
      change gammaMapValue (prodForm Z.Φ Z.bij hAP ω) ((prodMap Z.Φ hAP).toImage (Finv a)) = _
      unfold gammaMapValue
      rw [prodForm_apply]
      have h := F'.form_transport (Finv a)
      rw [Map.apply_inverse] at h
      exact h.symm
    have h2 : gammaMapValue (targetHGood hc h00 hκ hs hv hsmall hΓ F' π hFin).form a /
        gammaMapValue gfr.form ((prodMap Z.Φ hAP).toImage.comp Finv a) = 1 := by
      rw [hform]
      exact div_self' _
    rw [h2]
    exact (valueHom_eq_value (1 : VF M)).symm.trans
      ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)

end Compare

end DiamondIntegral.Section7.Lemma714Frozen
