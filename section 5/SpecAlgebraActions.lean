import «section 5».AffineSchemeActions

/-! Every actual scheme action on an affine complex spectrum over the
complex base comes from an actual action on its complex coordinate algebra. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ D]

def specOverAlgHom (f : Spec (.of B) ⟶ Spec (.of A))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) : A →ₐ[ℂ] B :=
  Spec.homEquivAlgHom ⟨f, hf⟩

theorem specOverAlgHom_map (f : Spec (.of B) ⟶ Spec (.of A))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) :
    Spec.map (CommRingCat.ofHom (specOverAlgHom f hf).toRingHom) = f := by
  change Spec.map (Spec.preimage f) = f
  exact Spec.map_preimage f

theorem specMapAlgHom_injective : Function.Injective
    (fun f : A →ₐ[ℂ] B => Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  intro f g h
  apply AlgHom.toRingHom_injective
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem specMapAlgHom_comp (f : B →ₐ[ℂ] D) (g : A →ₐ[ℂ] B) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [← Spec.map_comp]
  rfl

theorem specMapAlgHom_id : Spec.map (CommRingCat.ofHom (AlgHom.id ℂ A).toRingHom) = 𝟙 (Spec (.of A)) :=
  Spec.map_id _

def specOverAutomorphism (e : Aut (Spec (.of A)))
    (he : e.asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) : A ≃ₐ[ℂ] A := by
  have hi : e.asIso.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) := by
    calc
      _ = e.asIso.inv ≫ (e.asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :=
        congrArg (fun m => e.asIso.inv ≫ m) he.symm
      _ = _ := by rw [← Category.assoc, e.asIso.inv_hom_id, Category.id_comp]
  refine AlgEquiv.ofAlgHom (specOverAlgHom e.asIso.inv hi) (specOverAlgHom e.asIso.hom he) ?_ ?_
  · apply specMapAlgHom_injective
    dsimp only
    rw [specMapAlgHom_comp, specOverAlgHom_map, specOverAlgHom_map, specMapAlgHom_id]
    exact e.asIso.inv_hom_id
  · apply specMapAlgHom_injective
    dsimp only
    rw [specMapAlgHom_comp, specOverAlgHom_map, specOverAlgHom_map, specMapAlgHom_id]
    exact e.asIso.hom_inv_id

theorem specOverAutomorphism_map (e : Aut (Spec (.of A)))
    (he : e.asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    Spec.map (CommRingCat.ofHom (specOverAutomorphism e he).toRingHom) = e.asIso.inv :=
  specOverAlgHom_map _ _

theorem specOverAutomorphism_algHom_map (e : Aut (Spec (.of A)))
    (he : e.asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    Spec.map (CommRingCat.ofHom (specOverAutomorphism e he).toAlgHom.toRingHom) = e.asIso.inv :=
  specOverAutomorphism_map e he

def specActionAlgebraAction {G : Type} [Group G] (σ : G →* Aut (Spec (.of A)))
    (hσ : ∀ g, (σ g).asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) : G →* (A ≃ₐ[ℂ] A) where
  toFun g := specOverAutomorphism (σ g) (hσ g)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply specMapAlgHom_injective
    change Spec.map (CommRingCat.ofHom (specOverAutomorphism (σ 1) (hσ 1)).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgHom.id ℂ A).toRingHom)
    rw [specOverAutomorphism_map, specMapAlgHom_id, map_one]
    rfl
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply specMapAlgHom_injective
    change Spec.map (CommRingCat.ofHom (specOverAutomorphism (σ (g * h)) (hσ (g * h))).toRingHom) =
      Spec.map (CommRingCat.ofHom ((specOverAutomorphism (σ g) (hσ g)).toAlgHom.comp
        (specOverAutomorphism (σ h) (hσ h)).toAlgHom).toRingHom)
    rw [specMapAlgHom_comp, specOverAutomorphism_algHom_map, specOverAutomorphism_algHom_map,
      specOverAutomorphism_map, map_mul]
    rfl

theorem algebraSpecAction_specActionAlgebraAction {G : Type} [Group G]
    (σ : G →* Aut (Spec (.of A)))
    (hσ : ∀ g, (σ g).asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    algebraSpecAction (specActionAlgebraAction σ hσ) = σ := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  apply CategoryTheory.Iso.ext
  change Spec.map (CommRingCat.ofHom (specOverAutomorphism (σ g⁻¹) (hσ g⁻¹)).toRingHom) = (σ g).asIso.hom
  rw [specOverAutomorphism_map, map_inv]
  rfl

end DiamondIntegral.Section5
