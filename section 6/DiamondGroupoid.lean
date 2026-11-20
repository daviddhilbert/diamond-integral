import «section 6».DiamondCategory
import «section 6».MixedGammaJacobianException
import «section 6».CarriedExceptionalSets
import «section 6».GammaMapArithmetic
import «section 6».SpecialCovariant
import «section 6».EverywhereMeasuredRVLiftData
import Section9.MixedInverseJacobian
import Section9.MixedGenericDifferentiation

/-! Remark 6.35 (`dia:cat:well`): `μVF^◇[n]` is a groupoid.

Every morphism is an honest bijection. Its inverse is again a morphism: the
inverse of a relatively unary proper covariant homeomorphism is one in the same
coordinate, so factorizations invert, and the measure identity of the inverse
holds at VF-generic points by the generic derivative of the inverse and the
inverse Jacobian identity; the exceptional set is then produced definably.
Composites are morphisms by the chain rule at generic points. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

omit [M ⊨ Axioms.ACVF] in
theorem inverse_bijective (f : Map A B) (hf : Function.Bijective f) :
    Function.Bijective (f.inverse hf) :=
  ⟨fun p z he => by simpa only [Map.apply_inverse] using congrArg f he,
    fun p => ⟨f p, Map.inverse_apply f hf p⟩⟩

omit [M ⊨ Axioms.ACVF] in
theorem inverse_inverse (f : Map A B) (hf : Function.Bijective f)
    (hb : Function.Bijective (f.inverse hf)) : (f.inverse hf).inverse hb = f := by
  ext p
  have h := Map.inverse_apply (f.inverse hf) hb (f p)
  rw [Map.inverse_apply f hf p] at h
  exact congrArg Subtype.val h

theorem homeo_inverse {f : Map A B} (h : ProperCovariantHomeomorphism (G := G) f) :
    ProperCovariantHomeomorphism (G := G) (f.inverse h.bijective) := by
  have hb := inverse_bijective f h.bijective
  have he := inverse_inverse f h.bijective hb
  refine ⟨hb, h.inverseCovariant, h.inverseContinuous, ?_, ?_⟩
  · rw [he]
    exact h.covariant
  · rw [he]
    exact h.continuous

omit [M ⊨ Axioms.ACVF] in
/-- The inverse of a bijection relatively unary in the `i`-th coordinate is
relatively unary in the `i`-th coordinate. -/
theorem unary_inverse {f : Map A B} (hf : Function.Bijective f)
    (h : n = 0 ∨ ∃ i : Fin n, VFUnaryRelativeAt f i) :
    n = 0 ∨ ∃ i : Fin n, VFUnaryRelativeAt (f.inverse hf) i := by
  refine h.imp id (fun ⟨i, hi⟩ => ⟨i, fun q k hk => ?_⟩)
  have hq := hi (f.inverse hf q) k hk
  rw [Map.apply_inverse] at hq
  exact hq.symm

omit [M ⊨ Axioms.ACVF] in
theorem inverse_id (A : DefSet (rawMixedSpace (M := M) n r) S) (h : Function.Bijective (Map.id A)) :
    (Map.id A).inverse h = Map.id A := by
  ext p
  exact congrArg Subtype.val (Map.inverse_apply (Map.id A) h p)

omit [M ⊨ Axioms.ACVF] in
theorem inverse_comp {t : ℕ} {C : DefSet (rawMixedSpace (M := M) n t) S} (f : Map A B) (g : Map B C)
    (hf : Function.Bijective f) (hg : Function.Bijective g) (h : Function.Bijective (g.comp f)) :
    (g.comp f).inverse h = (f.inverse hf).comp (g.inverse hg) := by
  ext q
  have h1 : (g.comp f) ((f.inverse hf).comp (g.inverse hg) q) = q := by
    simp only [Map.comp_apply, Map.apply_inverse]
  have h2 := Map.inverse_apply (g.comp f) h ((f.inverse hf).comp (g.inverse hg) q)
  rw [h1] at h2
  exact congrArg Subtype.val h2

theorem factor_bijective {f : Map A B} (hF : UnaryFactorization G A B f) : Function.Bijective f := by
  induction hF with
  | id A => exact ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  | step homeo _ => exact homeo.bijective
  | comp _ _ ihf ihg => exact ihg.comp ihf

/-- The inverse of a factorization is a factorization. -/
theorem factor_inverse {f : Map A B} (hF : UnaryFactorization G A B f) :
    ∀ hf : Function.Bijective f, UnaryFactorization G B A (f.inverse hf) := by
  induction hF with
  | id A =>
    intro hf
    rw [inverse_id A hf]
    exact UnaryFactorization.id A
  | step homeo unary =>
    intro hf
    exact UnaryFactorization.step (homeo_inverse homeo) (unary_inverse hf unary)
  | comp hF hG ihf ihg =>
    intro hfg
    rw [inverse_comp _ _ (factor_bijective hF) (factor_bijective hG) hfg]
    exact UnaryFactorization.comp (ihg (factor_bijective hG)) (ihf (factor_bijective hF))

/-- A step satisfies the measure identity at every VF-generic point. -/
theorem step_generic (hc : CanonicalStructure.IsCanonical (M := M))
    {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier} (h : IsStep G A B f) (p : A.carrier)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    ∃ L, HasMixedVFDerivativeAt f p L ∧
      vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (f p)).val := by
  obtain ⟨bad, -, hsmall, hmeas⟩ := h.measure
  apply hmeas p
  rcases hsmall with h | h
  · exact not_mem_small_set_of_independent hc bad h p.val hp
  · rw [h]
    exact Set.notMem_empty _

/-- A relatively unary proper covariant homeomorphism between objects with the
measure identity at VF-generic points is a step: the exceptional set is
produced definably (empty in degree zero). -/
theorem isStep_of_generic (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A B : VFObject (M := M) S n} (f : Map A.carrier B.carrier)
    (homeo : ProperCovariantHomeomorphism (G := G) f) (unary : n = 0 ∨ ∃ i : Fin n, VFUnaryRelativeAt f i)
    (hgen : ∀ p : A.carrier, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (f p)).val) :
    IsStep G A B f := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  refine ⟨homeo, unary, ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact ⟨DefSet.empty _ S, Set.empty_subset _, Or.inr rfl,
      fun p _ => hgen p algebraicIndependent_empty_type⟩
  · obtain ⟨E, hEsub, hEdim, hE⟩ := exists_mixedGammaJacobian_exception hc hs hsmall
      (Nat.pos_of_ne_zero hn) f (gammaMapDiv hc A.form (B.form.comp f)) hgen
    exact ⟨E, hEsub, Or.inl hEdim, fun p hp => hE p hp⟩

theorem chain_bijective {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier}
    (h : ObjectFactorization G A B f) : Function.Bijective f :=
  factor_bijective h.toUnary

/-- The inverse of a step is a step. -/
theorem step_inverse (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier} (h : IsStep G A B f) :
    IsStep G B A (f.inverse h.homeo.bijective) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  let g := f.inverse h.homeo.bijective
  have hg : Function.Bijective g := inverse_bijective f h.homeo.bijective
  refine isStep_of_generic h00 hc hs hsmall g (homeo_inverse h.homeo)
    (unary_inverse h.homeo.bijective h.unary) (fun q hq => ?_)
  have hp := independent_map_of_finiteFibres hc g (Map.finiteFibres_of_injective hg.1) q hq
  obtain ⟨L, hL, hdet⟩ := step_generic hc h (g q) hp
  obtain ⟨D, hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g q hq
  have hfq : f (g q) = q := Map.apply_inverse f h.homeo.bijective q
  have hD' : HasMixedVFDerivativeAt g (f (g q)) D := by
    rw [hfq]
    exact hD
  have hprod := mixedVFJacobian_inverse_product f g (Map.inverse_apply f h.homeo.bijective) (g q) L D hL hD'
  refine ⟨D, hD, ?_⟩
  have h1 : vfValue (LinearMap.toMatrix' D).det * vfValue (LinearMap.toMatrix' L).det = 1 := by
    have h := congrArg Values.vfValueHom hprod
    rw [map_mul, map_one] at h
    exact h
  rw [hdet, hfq] at h1
  rw [eq_inv_of_mul_eq_one_left h1, ← Values.gamma_val_inv]
  change ((gammaMapValue A.form (g q) / gammaMapValue B.form q)⁻¹).val =
    (gammaMapValue B.form q / gammaMapValue A.form (g q)).val
  rw [inv_div]

/-- The inverse of a factorization inside `μVF^◇[n]` is one. -/
theorem chain_inverse (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier} (h : ObjectFactorization G A B f) :
    ∀ hf : Function.Bijective f, ObjectFactorization G B A (f.inverse hf) := by
  induction h with
  | id A =>
    intro hf
    rw [inverse_id A.carrier hf]
    exact ObjectFactorization.id A
  | step h =>
    intro hf
    exact ObjectFactorization.step (step_inverse h00 hc hκ hs hsmall hv h)
  | comp hF hG ihf ihg =>
    intro hfg
    rw [inverse_comp _ _ (chain_bijective hF) (chain_bijective hG) hfg]
    exact ObjectFactorization.comp (ihg (chain_bijective hG)) (ihf (chain_bijective hF))

/-- A morphism satisfies the measure identity at every VF-generic point. -/
theorem Morphism.generic (hc : CanonicalStructure.IsCanonical (M := M))
    {A B : VFObject (M := M) S n} (F : Morphism G A B) (p : A.carrier)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    ∃ L, HasMixedVFDerivativeAt F.map p L ∧
      vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (F.map p)).val := by
  apply F.measure p
  rcases F.bad_small with h | h
  · exact not_mem_small_set_of_independent hc F.bad h p.val hp
  · rw [h]
    exact Set.notMem_empty _

/-- A factored bijection with the measure identity at VF-generic points is a
morphism: the exceptional set is produced definably (empty in degree zero). -/
theorem morphism_of_generic (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A B : VFObject (M := M) S n} (f : Map A.carrier B.carrier) (hb : Function.Bijective f)
    (hF : ObjectFactorization G A B f)
    (hgen : ∀ p : A.carrier, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (f p)).val) :
    Nonempty (Morphism G A B) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  by_cases hn : n = 0
  · subst hn
    let st : Morphism G A B :=
      { map := f
        bijective := hb
        chain := hF
        bad := DefSet.empty _ S
        bad_subset := Set.empty_subset _
        bad_small := Or.inr rfl
        measure := fun p _ => hgen p algebraicIndependent_empty_type }
    exact ⟨st⟩
  · obtain ⟨E, hEsub, hEdim, hE⟩ := exists_mixedGammaJacobian_exception hc hs hsmall
      (Nat.pos_of_ne_zero hn) f (gammaMapDiv hc A.form (B.form.comp f)) hgen
    let st : Morphism G A B :=
      { map := f
        bijective := hb
        chain := hF
        bad := E
        bad_subset := hEsub
        bad_small := Or.inl hEdim
        measure := fun p hp => hE p hp }
    exact ⟨st⟩

/-- Remark 6.35: the inverse of a morphism is a morphism. -/
theorem Morphism.inverse_nonempty (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : VFObject (M := M) S n} (F : Morphism G A B) : Nonempty (Morphism G B A) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  let g := F.map.inverse F.bijective
  have hg : Function.Bijective g := inverse_bijective F.map F.bijective
  refine morphism_of_generic h00 hc hs hsmall g hg (chain_inverse h00 hc hκ hs hsmall hv F.chain F.bijective)
    (fun q hq => ?_)
  have hp := independent_map_of_finiteFibres hc g (Map.finiteFibres_of_injective hg.1) q hq
  obtain ⟨L, hL, hdet⟩ := Morphism.generic hc F (g q) hp
  obtain ⟨D, hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g q hq
  have hfq : F.map (g q) = q := Map.apply_inverse F.map F.bijective q
  have hD' : HasMixedVFDerivativeAt g (F.map (g q)) D := by
    rw [hfq]
    exact hD
  have hprod := mixedVFJacobian_inverse_product F.map g (Map.inverse_apply F.map F.bijective)
    (g q) L D hL hD'
  refine ⟨D, hD, ?_⟩
  have h1 : vfValue (LinearMap.toMatrix' D).det * vfValue (LinearMap.toMatrix' L).det = 1 := by
    have h := congrArg Values.vfValueHom hprod
    rw [map_mul, map_one] at h
    exact h
  rw [hdet, hfq] at h1
  rw [eq_inv_of_mul_eq_one_left h1, ← Values.gamma_val_inv]
  change ((gammaMapValue A.form (g q) / gammaMapValue B.form q)⁻¹).val =
    (gammaMapValue B.form q / gammaMapValue A.form (g q)).val
  rw [inv_div]

/-- Remark 6.35: the composite of two morphisms is a morphism. -/
theorem Morphism.comp_nonempty (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A B C : VFObject (M := M) S n} (F : Morphism G A B) (H : Morphism G B C) :
    Nonempty (Morphism G A C) := by
  refine morphism_of_generic h00 hc hs hsmall (H.map.comp F.map) (H.bijective.comp F.bijective)
    (ObjectFactorization.comp F.chain H.chain) (fun p hp => ?_)
  obtain ⟨L, hL, hJ⟩ := Morphism.generic hc F p hp
  have hq := independent_map_of_finiteFibres hc F.map (Map.finiteFibres_of_injective F.bijective.1) p hp
  obtain ⟨D, hD, hK⟩ := Morphism.generic hc H (F.map p) hq
  refine ⟨D.comp L, mixedDerivative_comp F.map H.map p hL hD, ?_⟩
  rw [LinearMap.toMatrix'_comp, Matrix.det_mul]
  change Values.vfValueHom (_ * _) = _
  rw [map_mul]
  change vfValue (LinearMap.toMatrix' D).det * vfValue (LinearMap.toMatrix' L).det = _
  rw [hK, hJ, ← Values.gamma_val_mul]
  apply congrArg (fun z : Gamma M => z.val)
  change (gammaMapValue B.form (F.map p) / gammaMapValue C.form (H.map (F.map p))) *
      (gammaMapValue A.form p / gammaMapValue B.form (F.map p)) =
    gammaMapValue A.form p / gammaMapValue C.form (H.map (F.map p))
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Remark 6.35: isomorphism in `μVF^◇[n]` is an equivalence relation
(`μVF^◇[n]` is a groupoid; every morphism is an honest bijection). -/
theorem isomorphic_equivalence (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Equivalence (Isomorphic (M := M) (S := S) (n := n) G) :=
  ⟨Isomorphic.refl, fun ⟨F⟩ => Morphism.inverse_nonempty h00 hc hκ hs hsmall hv F,
    fun ⟨F⟩ ⟨H⟩ => Morphism.comp_nonempty h00 hc hs hsmall F H⟩

end DiamondIntegral.Section6.DiamondGroupoid
