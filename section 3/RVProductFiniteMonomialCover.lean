import «section 3».RVProductMonomialImages
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m p : ℕ}

/-- Swap actual product coordinates over the same ground. -/
def gammaGroundProductSwap {Q V : Space LRV M}
    (A : GammaGroundDefSet hc B Q) (E : GammaGroundDefSet hc B V) :
    GammaGroundBijection (A.prod E) (E.prod A) where
  map := (GammaGroundMap.prodSnd A E).pair (GammaGroundMap.prodFst A E)
  bijective := by
    constructor
    · intro a b h
      apply Subtype.ext
      have he := congrArg Subtype.val h
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro z
      exact ⟨⟨(z.val.2,z.val.1),z.property.2,z.property.1⟩,Subtype.ext (Prod.eta z.val)⟩

/-- One original-ground monomial rectangle, including its actual map
formula and the constant values of its RES-dependent coefficients. -/
structure GammaGroundRVProductMonomialPatch
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (f : GammaGroundMap T D) (g : GammaGroundMap T S) where
  matrix : Matrix (Fin m) (Fin m) ℤ
  unimodular : IsUnit matrix.det
  residue : GammaGroundDefSet hc B (rawRVUnitSpace n)
  residue_subset : residue.carrier ⊆ R.carrier
  residue_nonempty : residue.carrier.Nonempty
  gamma : GammaGroundGammaPiece hc B m
  gamma_nonempty : gamma.carrier.Nonempty
  coefficient : GammaGroundMap residue (GammaGroundDefSet.univ hc B (rawRVUnitSpace m))
  residueMap : GammaGroundMap residue (GammaGroundDefSet.univ hc B (rawRVUnitSpace p))
  value : Fin m → Values.Gamma (M := M)
  value_definable : ∀ i, GammaDefinableClosureAtBase B (value i)
  coefficient_values : ∀ a : residue, rvUnitTupleValues (coefficient a).val = value
  formula : ∀ a : residue, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
    rvUnitTupleValues u ∈ gamma.carrier → ∃ t : T, t.val = (u,a.val) ∧
      (f t).val = (fun i => (coefficient a).val i * integerMonomialMap matrix u i) ∧
      (g t).val = (residueMap a).val

namespace GammaGroundRVProductMonomialPatch
variable {R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n))}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace m)} {S : GammaGroundDefSet hc B (rawRVUnitSpace p)}
variable {f : GammaGroundMap T D} {g : GammaGroundMap T S}

def source (P : GammaGroundRVProductMonomialPatch R T D S f g) :=
  (gammaGroundRVUnitGammaPreimage P.gamma).prod P.residue

theorem source_subset (P : GammaGroundRVProductMonomialPatch R T D S f g) :
    P.source.carrier ⊆ T.carrier := by
  intro z hz
  obtain ⟨t,ht,_,_⟩ := P.formula ⟨z.2,hz.2⟩ z.1 hz.1
  exact ht.trans (Prod.eta z) ▸ t.property

theorem residueMap_injective (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) : Function.Injective P.residueMap :=
  gammaGroundRVProduct_residue_output_injective P.residue P.gamma P.gamma_nonempty T D S f g hjoint
    P.matrix P.unimodular P.coefficient P.residueMap P.value P.coefficient_values P.formula

def targetGamma (P : GammaGroundRVProductMonomialPatch R T D S f g) :=
  gammaGroundGammaTranslate (gammaGroundMonomialValueImage P.gamma P.matrix) P.value P.value_definable

def target (P : GammaGroundRVProductMonomialPatch R T D S f g) :=
  (gammaGroundRVUnitGammaPreimage P.targetGamma).prod P.residueMap.image

/-- The original map on a monomial patch is an actual product bijection
onto its entire native target rectangle. -/
def bijection (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) :
    GammaGroundBijection P.source P.target :=
  (gammaGroundProductSwap P.residueMap.image (gammaGroundRVUnitGammaPreimage P.targetGamma)).comp
    ((gammaGroundRVUnitAffineProductBijection P.residue P.gamma P.matrix P.unimodular
      P.coefficient P.residueMap (P.residueMap_injective hjoint) P.value P.value_definable P.coefficient_values).comp
        (gammaGroundProductSwap (gammaGroundRVUnitGammaPreimage P.gamma) P.residue))

@[simp] theorem bijection_value (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (z : P.source) :
    ((P.bijection hjoint).map z).val =
      ((fun i => (P.coefficient ⟨z.val.2,z.property.2⟩).val i * integerMonomialMap P.matrix z.val.1 i),
        (P.residueMap ⟨z.val.2,z.property.2⟩).val) := rfl

theorem bijection_agrees (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (z : P.source) :
    ((P.bijection hjoint).map z).val =
      ((f ⟨z.val,P.source_subset z.property⟩).val,(g ⟨z.val,P.source_subset z.property⟩).val) := by
  obtain ⟨t,ht,hf,hg⟩ := P.formula ⟨z.val.2,z.property.2⟩ z.val.1 z.property.1
  have he : t = (⟨z.val,P.source_subset z.property⟩ : T) := Subtype.ext (ht.trans (Prod.eta z.val))
  rw [he] at hf hg
  rw [bijection_value]
  exact Prod.ext hf.symm hg.symm

theorem target_subset (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) :
    P.target.carrier ⊆ (D.prod S).carrier := by
  intro z hz
  obtain ⟨a,ha⟩ := (P.bijection hjoint).bijective.2 ⟨z,hz⟩
  have he := (P.bijection_agrees hjoint a).symm.trans (congrArg Subtype.val ha)
  change ((f ⟨a.val,P.source_subset a.property⟩).val,(g ⟨a.val,P.source_subset a.property⟩).val) = z at he
  rw [← he]
  exact ⟨(f ⟨a.val,P.source_subset a.property⟩).property,(g ⟨a.val,P.source_subset a.property⟩).property⟩

theorem gamma_subset (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (G : GammaGroundGammaPiece hc B m) (hTG : ∀ t : T, rvUnitTupleValues t.val.1 ∈ G.carrier) :
    P.gamma.carrier ⊆ G.carrier := by
  intro γ hγ
  change Fin m → Values.Gamma (M := M) at γ
  obtain ⟨a,ha⟩ := P.residue_nonempty
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huG : rvUnitTupleValues u ∈ P.gamma.carrier := hu.symm ▸ hγ
  obtain ⟨t,ht,_,_⟩ := P.formula ⟨a,ha⟩ u huG
  have h := hTG t
  rw [ht] at h
  exact hu ▸ h

theorem targetGamma_subset (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (G : GammaGroundGammaPiece hc B m) (hDG : ∀ u : D, rvUnitTupleValues u.val ∈ G.carrier) :
    P.targetGamma.carrier ⊆ G.carrier := by
  intro γ hγ
  change Fin m → Values.Gamma (M := M) at γ
  obtain ⟨a,ha⟩ := P.residue_nonempty
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huG : u ∈ (gammaGroundRVUnitGammaPreimage P.targetGamma).carrier := by
    change rvUnitTupleValues u ∈ P.targetGamma.carrier
    exact hu.symm ▸ hγ
  have hb : (P.residueMap ⟨a,ha⟩).val ∈ P.residueMap.image.carrier := ⟨⟨a,ha⟩,rfl⟩
  have h := P.target_subset hjoint (show (u,(P.residueMap ⟨a,ha⟩).val) ∈ P.target.carrier from ⟨huG,hb⟩)
  exact hu ▸ hDG ⟨u,h.1⟩
end GammaGroundRVProductMonomialPatch

/-- A jointly injective square product map has a finite positive cover
by original-ground monomial rectangles and proper character hyperplanes.
The assertion concerns actual domains and retains every coefficient map. -/
theorem gammaGroundRVProduct_finite_monomial_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (hTR : ∀ t : T, t.val.2 ∈ R.carrier)
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) :
    ∃ F : Finset (GammaGroundRVProductMonomialPatch R T D S f g),
      ∃ H : Finset (GammaGroundCharacterHyperplane B m),
      ∀ t : T, (∃ P ∈ F, t.val ∈ P.source.carrier) ∨
        ∃ h ∈ H, rvUnitTupleValues t.val.1 ∈ h.carrier := by
  let values : GammaGroundMap T (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))) :=
    GammaGroundMap.ofGlobal T _ ((rvUnitGammaMap hc B.real m).comp
      (universalProductFst (rawRVUnitSpace m) (rawRVUnitSpace n) B.real)) (fun _ => Set.mem_univ _)
  let C : Set (Set ((rawRVUnitSpace (M := M) m).prod (rawRVUnitSpace n)).Carrier) :=
    Set.range (fun P : GammaGroundRVProductMonomialPatch R T D S f g => P.source.carrier)
  have hC : ∀ U ∈ C, GammaGroundDefinable hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)) U := by
    rintro U ⟨P,rfl⟩
    exact P.source.definable
  have hcovers : ∀ t : T, GammaTupleIndependentOver B (values t).val → ∃ U ∈ C, t.val ∈ U := by
    intro t ht
    let r : R := ⟨t.val.2,hTR t⟩
    let cr : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
    have hxt : (t.val.1,(rawRVUnitSpace n).decode cr) ∈ T.carrier := by
      rw [decode_rvUnitValues r.val]
      exact t.property
    let x : gammaGroundRealPointFibre T cr := ⟨t.val.1,hxt⟩
    obtain ⟨A,hA,U,G,hU,c,s,δ,hr,hx,hδ,hcval,hformula⟩ := gammaGroundRVProduct_monomial_neighborhood
      hκ hs h00 hsmall hγsmall hΓ R hR T D S hS f g hjoint r x ht
    let P : GammaGroundRVProductMonomialPatch R T D S f g :=
      ⟨A,hA,U,hU,⟨r.val,hr⟩,G,⟨rvUnitTupleValues x.val,hx⟩,c,s,δ,hδ,hcval,hformula⟩
    exact ⟨P.source.carrier,⟨P,rfl⟩,hx,hr⟩
  obtain ⟨E,hE,hcover⟩ := gammaGround_generic_finite_cover hκ hs hsmall hγsmall T values C hC hcovers
  let good := E.filter (fun U => U ∈ C)
  let bad := E.filter (fun U => U ∉ C)
  have hgood : ∀ U : good, ∃ P : GammaGroundRVProductMonomialPatch R T D S f g, P.source.carrier = U.val := by
    intro U
    exact (Finset.mem_filter.mp U.property).2
  have hbad : ∀ U : bad, ∃ h : GammaGroundCharacterHyperplane B m,
      U.val = (values.preimage h.defSet).carrier := by
    intro U
    obtain ⟨hUE,hUC⟩ := Finset.mem_filter.mp U.property
    exact (hE U.val hUE).resolve_left hUC
  let pickGood : good → GammaGroundRVProductMonomialPatch R T D S f g := fun U => Classical.choose (hgood U)
  let pickBad : bad → GammaGroundCharacterHyperplane B m := fun U => Classical.choose (hbad U)
  refine ⟨good.attach.image pickGood,bad.attach.image pickBad,?_⟩
  intro t
  obtain ⟨U,hU,htU⟩ := hcover t
  by_cases hUC : U ∈ C
  · let a : good := ⟨U,Finset.mem_filter.mpr ⟨hU,hUC⟩⟩
    refine Or.inl ⟨pickGood a,Finset.mem_image.mpr ⟨a,Finset.mem_attach _ a,rfl⟩,?_⟩
    exact (Classical.choose_spec (hgood a)).symm ▸ htU
  · let a : bad := ⟨U,Finset.mem_filter.mpr ⟨hU,hUC⟩⟩
    refine Or.inr ⟨pickBad a,Finset.mem_image.mpr ⟨a,Finset.mem_attach _ a,rfl⟩,?_⟩
    have he : U = (values.preimage (pickBad a).defSet).carrier := Classical.choose_spec (hbad a)
    rw [he] at htU
    obtain ⟨t',htt',htH⟩ := htU
    have hteq : t' = t := Subtype.ext htt'
    subst t'
    exact htH
end DiamondIntegral.Section3
