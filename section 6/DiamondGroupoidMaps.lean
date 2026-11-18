import «section 6».DiamondGroupoid

/-! Remark 6.35 (`dia:cat:well`) with the maps named. In `DiamondGroupoid`
the composite and inverse are shown only to exist (`Nonempty`). Here the
composite morphism has map `H.map.comp F.map` and the inverse morphism has
map `F.map.inverse F.bijective`. The morphism maps therefore form a
groupoid: they contain identities and are closed under composition and
inverses, and these operations satisfy the groupoid laws. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `morphism_of_generic`, keeping the given map. -/
theorem morphism_of_generic_map (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A B : VFObject (M := M) S n} (f : Map A.carrier B.carrier) (hb : Function.Bijective f)
    (hF : UnaryFactorization G A.carrier B.carrier f)
    (hgen : ∀ p : A.carrier, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (f p)).val) :
    ∃ K : Morphism G A B, K.map = f := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  by_cases hn : n = 0
  · subst hn
    exact ⟨{ map := f
             bijective := hb
             factor := hF
             bad := DefSet.empty _ S
             bad_subset := Set.empty_subset _
             bad_small := Or.inr rfl
             measure := fun p _ => hgen p algebraicIndependent_empty_type }, rfl⟩
  · obtain ⟨E, hEsub, hEdim, hE⟩ := exists_mixedGammaJacobian_exception hc hs hsmall
      (Nat.pos_of_ne_zero hn) f (gammaMapDiv hc A.form (B.form.comp f)) hgen
    exact ⟨{ map := f
             bijective := hb
             factor := hF
             bad := E
             bad_subset := hEsub
             bad_small := Or.inl hEdim
             measure := fun p hp => hE p hp }, rfl⟩

/-- Remark 6.35: the inverse map of a morphism underlies a morphism. -/
theorem Morphism.inverse_exists (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : VFObject (M := M) S n} (F : Morphism G A B) :
    ∃ K : Morphism G B A, K.map = F.map.inverse F.bijective := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  let g := F.map.inverse F.bijective
  have hg : Function.Bijective g := inverse_bijective F.map F.bijective
  refine morphism_of_generic_map h00 hc hs hsmall g hg (factor_inverse F.factor F.bijective) (fun q hq => ?_)
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

/-- Remark 6.35: the composite map of two morphisms underlies a morphism. -/
theorem Morphism.comp_exists (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A B C : VFObject (M := M) S n} (F : Morphism G A B) (H : Morphism G B C) :
    ∃ K : Morphism G A C, K.map = H.map.comp F.map := by
  refine morphism_of_generic_map h00 hc hs hsmall (H.map.comp F.map) (H.bijective.comp F.bijective)
    (UnaryFactorization.comp F.factor H.factor) (fun p hp => ?_)
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

variable (G) in
/-- The maps underlying `μVF^◇[n]`-morphisms `A → B`. -/
def IsMorphismMap (A B : VFObject (M := M) S n) (f : Map A.carrier B.carrier) : Prop :=
  ∃ K : Morphism G A B, K.map = f

/-- The standing context of Section 6 in which `μVF^◇[n]` is a groupoid. -/
structure DiamondContext (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : Set M) where
  h00 : M ⊨ Axioms.ACVF00
  hc : CanonicalStructure.IsCanonical (M := M)
  κ : Cardinal
  hκ : Cardinal.aleph0 ≤ κ
  hs : Saturated M κ
  hsmall : Cardinal.mk S < κ

variable (G) in
/-- Objects of `μVF^◇[n]` in a fixed context (the valuation `G` is the one in
`hv`). -/
structure DiamondObj (X : DiamondContext M S) (n : ℕ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) where
  obj : VFObject (M := M) S n

theorem IsMorphismMap.bijective {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier}
    (hf : IsMorphismMap G A B f) : Function.Bijective f := by
  obtain ⟨F, rfl⟩ := hf
  exact F.bijective

theorem IsMorphismMap.inverse (X : DiamondContext M S)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : VFObject (M := M) S n} {f : Map A.carrier B.carrier}
    (hf : IsMorphismMap G A B f) (hb : Function.Bijective f) :
    IsMorphismMap G B A (f.inverse hb) := by
  obtain ⟨F, rfl⟩ := hf
  exact Morphism.inverse_exists X.h00 X.hc X.hκ X.hs X.hsmall hv F

theorem IsMorphismMap.comp (X : DiamondContext M S)
    {A B C : VFObject (M := M) S n} {f : Map A.carrier B.carrier} {g : Map B.carrier C.carrier}
    (hf : IsMorphismMap G A B f) (hg : IsMorphismMap G B C g) :
    IsMorphismMap G A C (g.comp f) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨H, rfl⟩ := hg
  exact Morphism.comp_exists X.h00 X.hc X.hs X.hsmall F H

/-- `μVF^◇[n]` as a groupoid: morphisms are the maps underlying Definition 6.34
morphisms (Remark 6.35). -/
instance (X : DiamondContext M S) (n : ℕ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Groupoid (DiamondObj G X n hv) where
  Hom A B := {f : Map A.obj.carrier B.obj.carrier // IsMorphismMap G A.obj B.obj f}
  id A := ⟨Map.id A.obj.carrier, ⟨Morphism.id A.obj, rfl⟩⟩
  comp f g := ⟨g.val.comp f.val, IsMorphismMap.comp X f.property g.property⟩
  id_comp f := Subtype.ext (Map.ext (fun _ => rfl))
  comp_id f := Subtype.ext (Map.ext (fun _ => rfl))
  assoc f g h := Subtype.ext (Map.ext (fun _ => rfl))
  inv f := ⟨f.val.inverse f.property.bijective,
    IsMorphismMap.inverse X hv f.property f.property.bijective⟩
  inv_comp f := by
    apply Subtype.ext
    apply Map.ext
    intro p
    exact Map.apply_inverse _ _ p
  comp_inv f := by
    apply Subtype.ext
    apply Map.ext
    intro p
    exact Map.inverse_apply _ _ p

end DiamondIntegral.Section6.DiamondGroupoid
