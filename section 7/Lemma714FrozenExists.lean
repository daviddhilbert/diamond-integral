import «section 7».Lemma714CompareFr
import «section 6».SelectedInverseGammaTransport

/-! Lemma 7.14, part 31: existence of the freezing.

* Level sets of a form transported from a label-constant form along a proper
  covariant map are open (`levels_open_of_transport`); for a normalized
  measured contraction this gives open level sets of the original form.
* Product forms have open level sets (`prodForm_levels_open`).
* **Existence of the freezing** (`exists_frozen`): for the proper invariant VF
  projection `P` of `A'`, `A''` and a finite list of witness sets, there is a
  frozen preparation guarding `(A', ω')` and `(A'', ω'')` on whose key classes all
  listed sets have constant rows. -/

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

/-- **Level sets of a form transported from a label-constant form are open.** -/
theorem levels_open_of_transport (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {n m r s : ℕ} {X : DefSet (rawMixedSpace (M := M) n r) S} {Y : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map X Y) (hf : ProperCovariant f)
    (σ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)) (hσ : ∀ p q : Y, p.val.2 = q.val.2 → σ p = σ q)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hω : ∀ p : X, ω p = σ (f p))
    (u : Fin r → RVInfinity M) (γ : rawGammaPresentation.Carrier) :
    IsOpen {a : Fin n → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension ω (a, u) = γ} := by
  have he : {a : Fin n → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension ω (a, u) = γ} =
      ⋃ v ∈ {v : Fin s → RVInfinity M | ∃ q : Y, q.val.2 = v ∧ (σ q).val = γ}, graphFibreSource f u v := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ha, hγ⟩
      let p : X := ⟨(a, u), ha⟩
      refine ⟨(f p).val.2, ⟨f p, rfl, ?_⟩, (f p).val.1, p, rfl, rfl⟩
      rw [← hω p, ← hγ]
      exact (gammaFormExtension_at ω p).symm
    · rintro ⟨v, ⟨q, hqv, hqγ⟩, b, p, hp, hfp⟩
      have ha : (a, u) ∈ X.carrier := by
        rw [← hp]
        exact p.property
      refine ⟨ha, ?_⟩
      have e1 : gammaFormExtension ω (a, u) = (ω p).val := by
        rw [← hp]
        exact gammaFormExtension_at ω p
      have hl : (f p).val.2 = q.val.2 := by
        rw [hfp, hqv]
      rw [e1, hω p, hσ (f p) q hl]
      exact hqγ
  rw [he]
  exact isOpen_biUnion fun v _ => (source_isOpen_of_covariant hv hf u v).isOpen

section Prod
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv hsmall hΓ in
/-- **Product forms have open level sets.** -/
theorem prodForm_levels_open {r s : ℕ} {P : DefSet (rawMixedSpace (M := M) 1 0) S}
    {Q : DefSet (rawMixedSpace (M := M) 1 s) S} (g : Map P Q) (hg : ProperCovariantHomeomorphism (G := G) g)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)
    (hA : ProperInvariant S A.carrier) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a, u) ∈ A.carrier ∧ gammaFormExtension ω (a, u) = γ}) :
    ∀ v γ, IsOpen {b : Fin 1 → VF M | (b, v) ∈ (prodMap g hAP).image.carrier ∧
      gammaFormExtension (prodForm g hg.bijective hAP ω) (b, v) = γ} := by
  have hPH := prodMap_properHomeomorphism g hAP hv h00 hc hκ hs lin hsmall hΓ hg hA
  have hB := prodMap_image_properInvariant g hAP hv h00 hc hκ hs hg hA
  exact transported_gamma_levels_open_selected (prodMap g hAP).toImage (prodMap_toImage_bijective g hg.bijective hAP)
    (Fin.natAdd s) (fun p i => prodMap_labels g hAP p i) hPH.inverseContinuous
    (fun v => (hB.clopen_fibres hv v).isOpen) ω hω

end Prod

/-! ### Existence of the freezing -/

section Exists
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  {T : LRV.Substructure M} (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
  (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
  (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hκ hs hv hV hVT hTV hnt hsmall hΓ in
/-- **Existence of the freezing.** -/
theorem exists_frozen {P : DefSet (rawMixedSpace (M := M) 1 0) (T : Set M)} (hP : ProperInvariant (T : Set M) P.carrier)
    {r' r'' : ℕ} {A' : DefSet (rawMixedSpace (M := M) 1 r') (T : Set M)}
    {A'' : DefSet (rawMixedSpace (M := M) 1 r'') (T : Set M)}
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hAP' : ∀ p ∈ A'.carrier, basePoint p ∈ P.carrier) (hAP'' : ∀ p ∈ A''.carrier, basePoint p ∈ P.carrier)
    (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
    (hω' : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a, u) ∈ A'.carrier ∧ gammaFormExtension ω' (a, u) = γ})
    (hω'' : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a, u) ∈ A''.carrier ∧ gammaFormExtension ω'' (a, u) = γ})
    (L : List (Comp (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfs 1))) :
    ∃ Z : Frozen (G := G) P, Guards Z ω' hAP' ∧ Guards Z ω'' hAP'' ∧ ∀ x, AllRowConst (Z.K hc) L x := by
  obtain ⟨BP⟩ := exists_basePrep (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt P hP
  have hΦ₀ := BP.chain.properHomeomorphism h00 hc lin hκ hs hv hsmall hΓ
  have bij₀ := BP.chain.bijective h00
  have hB₁ := prodMap_image_properInvariant BP.map hAP' hv h00 hc hκ hs hΦ₀ hA'
  have hB₂ := prodMap_image_properInvariant BP.map hAP'' hv h00 hc hκ hs hΦ₀ hA''
  have hL₁ := prodForm_levels_open h00 hc hκ hs hv hsmall hΓ BP.map hΦ₀ hAP' hA' ω' hω'
  have hL₂ := prodForm_levels_open h00 hc hκ hs hv hsmall hΓ BP.map hΦ₀ hAP'' hA'' ω'' hω''
  obtain ⟨F, sk, Bk, f, hf, hBk, hBkD, hBkRV, -, hP1, hP1l, hP2, hP2l, hrows⟩ :=
    frozen_prep_two (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt BP.B BP.proper BP.doublyBounded
      BP.pullback BP.tagged (prodMap BP.map hAP').image hB₁ (prodForm BP.map hΦ₀.bijective hAP' ω') hL₁
      (prodMap BP.map hAP'').image hB₂ (prodForm BP.map hΦ₀.bijective hAP'' ω'') hL₂
      (fun i : Fin L.length => (L.get i).n)
      (fun i => pullSet (BP.map.inverse hΦ₀.bijective) (L.get i).D (compDef hc (L.get i)))
  have hreg := regularization_properHomeomorphism h00 hc lin hκ hs hv hsmall hΓ Bk hBk hBkD
  have hRP : ProperInvariant (T : Set M) (regularizeMap Bk).image.carrier :=
    hreg.covariant.target_properInvariant h00 hc lin hκ hs hv hsmall hΓ hreg.bijective.2
  have hch : SpecialCovariantChain (G := G) P (regT Bk) ((fReg f).comp BP.map) :=
    .comp BP.chain (.comp hf (.regularize Bk hBk hBkD))
  have hbij := hch.bijective h00
  have hfin : ∀ y : Fin 1 → VF M, {u : Fin (1 + sk) → RVInfinity M | (y, u) ∈ (regT Bk).carrier}.Finite :=
    finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall _ hbij
      (fun a => Set.Subsingleton.finite fun u _ v _ => Subsingleton.elim u v)
  let Z : Frozen (G := G) P :=
    { s := 1 + BP.s, B₀ := BP.B, Φ₀ := BP.map, bij₀ := hΦ₀.bijective, F := F, sk := sk, Bk := Bk, f := f,
      bijk := hf.bijective h00, rvBounded := hRP.rvBounded, pullback := SpecialChains.regularize_pullback Bk hBkRV,
      finite := hfin, vfBounded := SpecialChains.regularize_vfDoublyBounded Bk hBkD,
      homeo := hch.properHomeomorphism h00 hc lin hκ hs hv hsmall hΓ, chain := hch }
  refine ⟨Z, ⟨hP1, hP1l⟩, ⟨hP2, hP2l⟩, fun x => keyRel_rowConst Z.f (Z.Φ₀.inverse Z.bij₀) Z.F hc L ?_ x⟩
  intro p z h c hcL
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hcL
  rw [frz_val, frz_val]
  exact hrows p z h i

end Exists

end DiamondIntegral.Section7.Lemma714Frozen
