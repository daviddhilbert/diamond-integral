import «section 3».RVProductFibreArity
import «section 3».GammaGenericFiniteCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m k p : ℕ}

/-- A branch landing in fewer free Gamma coordinates has no generic
source fibre. Compactness puts all its source values in finitely many
proper original-ground character hyperplanes. -/
theorem gammaGroundRVProduct_lower_arity_hyperplane_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (hTR : ∀ t : T, t.val.2 ∈ R.carrier)
    (D : GammaGroundDefSet hc B (rawRVUnitSpace k))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (hkm : k < m) :
    ∃ F : Finset (GammaGroundCharacterHyperplane B m),
      ∀ t : T, ∃ H ∈ F, rvUnitTupleValues t.val.1 ∈ H.carrier := by
  let values : GammaGroundMap T (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))) :=
    GammaGroundMap.ofGlobal T _ ((rvUnitGammaMap hc B.real m).comp
      (universalProductFst (rawRVUnitSpace m) (rawRVUnitSpace n) B.real)) (fun _ => Set.mem_univ _)
  have hnogeneric : ∀ t : T, ¬ GammaTupleIndependentOver B (values t).val := by
    intro t ht
    let r : R := ⟨t.val.2,hTR t⟩
    let cr : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
    have hxt : (t.val.1,(rawRVUnitSpace n).decode cr) ∈ T.carrier := by
      rw [decode_rvUnitValues r.val]
      exact t.property
    let x : gammaGroundRealPointFibre T cr := ⟨t.val.1,hxt⟩
    have hle := gammaGroundRVProduct_generic_fibre_arity_le hκ hs h00 hsmall hγsmall hΓ
      R hR T D S hS f g hjoint r x ht
    exact (Nat.not_le_of_gt hkm) hle
  obtain ⟨E,hE,hcover⟩ := gammaGround_generic_finite_cover hκ hs hsmall hγsmall T values ∅
    (by intro U hU; exact False.elim hU)
    (by intro t ht; exact False.elim (hnogeneric t ht))
  have hH : ∀ U ∈ E, ∃ H : GammaGroundCharacterHyperplane B m,
      U = (values.preimage H.defSet).carrier := by
    intro U hU
    exact (hE U hU).resolve_left (fun h => h)
  let pick : E → GammaGroundCharacterHyperplane B m := fun U => Classical.choose (hH U.val U.property)
  refine ⟨E.attach.image pick,?_⟩
  intro t
  obtain ⟨U,hU,htU⟩ := hcover t
  let a : E := ⟨U,hU⟩
  refine ⟨pick a,Finset.mem_image.mpr ⟨a,Finset.mem_attach _ a,rfl⟩,?_⟩
  have he : U = (values.preimage (pick a).defSet).carrier := Classical.choose_spec (hH U hU)
  rw [he] at htU
  obtain ⟨t',htt',htH⟩ := htU
  have hteq : t' = t := Subtype.ext htt'
  subst t'
  exact htH
end DiamondIntegral.Section3
