import «section 5».GlobalAngularPartition
import Mathlib.Data.Fintype.Sigma

/-! Global original-ground monomial charts in unimodular-basis form.
Each coordinate map is an integer monomial basis equivalence followed by
the recorded coordinate split. Empty charts are removed, and the source
pieces are induced by a disjoint partition of the original value image. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

structure GroundMonomialPiece (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) where
  angularSource : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)
  cell : RVAngularCell angularSource.carrier
  split : Section2.ZeroFaceChart (Set.range cell.active)
  arity_eq : split.zeroArity + split.freeArity = n
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) split.zeroArity)
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin split.freeArity))
  beta : Fin split.zeroArity → Values.Gamma (M := M)
  beta_definable : ∀ i, GammaDefinableClosureAtBase B (beta i)
  residue_values : rvUnitTupleValues '' residue.carrier = {beta}
  residue_nonempty : residue.carrier.Nonempty
  gamma_nonempty : gamma.carrier.Nonempty
  source : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)
  values : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))
  source_nonempty : source.carrier.Nonempty
  source_cut : source.carrier = X.carrier ∩ rvUnitTupleValues ⁻¹' values.carrier
  coordinate_image : cell.coordinateEquiv split '' source.carrier =
    (residue.prod (gammaGroundRVUnitGammaPreimage gamma)).carrier
  bijection : GammaGroundBijection source (residue.prod (gammaGroundRVUnitGammaPreimage gamma))

/-- Global finite nonempty monomial product pieces, over the original
real/Gamma ground, with a partition of the original value image. -/
theorem ground_global_monomial_decomposition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    ∃ N : ℕ, ∃ C : Fin N → GroundMonomialPiece X,
      (∀ i j, i ≠ j → Disjoint (C i).values.carrier (C j).values.carrier) ∧
      (∀ γ, γ ∈ rvUnitTupleValues '' X.carrier ↔ ∃ j, γ ∈ (C j).values.carrier) := by
  obtain ⟨N, A, F, hE, hA, hFd, hFc⟩ := ground_global_angular_value_partition hκ hs h00 hsmall X
  let E := fun i => Classical.choice (hE i)
  let K := fun i => Section2.zeroFaceChart (Set.range (E i).active)
  choose L β R G Y D hβ hR hbij himg hcut hdis hcov using
    fun i => ground_angular_value_partition hκ hs h00 hsmall hγsmall hΓ (A i) (E i) (K i)
  have hDsub : ∀ i j, (D i j).carrier ⊆ rvUnitTupleValues '' (A i).carrier := by
    intro i j γ hγ
    exact (hcov i γ).mpr ⟨j, hγ⟩
  have hDF : ∀ i j, (D i j).carrier ⊆ (F i).carrier := by
    intro i j γ hγ
    obtain ⟨x, hx, hv⟩ := hDsub i j hγ
    rw [hA i] at hx
    exact hv ▸ hx.2
  have hglobalcut : ∀ i j, (Y i j).carrier = X.carrier ∩ rvUnitTupleValues ⁻¹' (D i j).carrier := by
    intro i j
    rw [hcut i j, hA i]
    ext x
    constructor
    · rintro ⟨⟨hx, _⟩, hd⟩
      exact ⟨hx, hd⟩
    · rintro ⟨hx, hd⟩
      exact ⟨⟨hx, hDF i j hd⟩, hd⟩
  let J := (i : Fin N) × Fin (L i)
  let Z : J → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun j => Y j.1 j.2
  let V : J → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) := fun j => D j.1 j.2
  have hVd : ∀ j k : J, j ≠ k → Disjoint (V j).carrier (V k).carrier := by
    rintro ⟨i,j⟩ ⟨k,l⟩ hne
    by_cases hik : i = k
    · subst k
      exact hdis i j l (fun h => hne (by cases h; rfl))
    · exact (hFd i k hik).mono (hDF i j) (hDF k l)
  let J' := {j : J // (Z j).carrier.Nonempty}
  letI : Fintype J' := Fintype.ofFinite J'
  let e : Fin (Fintype.card J') ≃ J' := (Fintype.equivFin J').symm
  have hnonempty : ∀ j : J', (R j.val.1 j.val.2).carrier.Nonempty ∧
      (G j.val.1 j.val.2).carrier.Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := j.property
    have hz := (Set.ext_iff.mp (himg j.val.1 j.val.2)
      ((E j.val.1).coordinateEquiv (K j.val.1) x)).mp ⟨x, hx, rfl⟩
    exact ⟨⟨_, hz.1⟩, ⟨_, hz.2⟩⟩
  let C : J' → GroundMonomialPiece X := fun j => {
    angularSource := A j.val.1
    cell := E j.val.1
    split := K j.val.1
    arity_eq := by simpa only [Fintype.card_fin] using Fintype.card_congr (K j.val.1).coordinates
    residue := R j.val.1 j.val.2
    gamma := G j.val.1 j.val.2
    beta := β j.val.1 j.val.2
    beta_definable := hβ j.val.1 j.val.2
    residue_values := by
      apply Set.Subset.antisymm (hR j.val.1 j.val.2)
      rintro γ rfl
      obtain ⟨r, hr⟩ := (hnonempty j).1
      have hv : rvUnitTupleValues r = β j.val.1 j.val.2 := hR j.val.1 j.val.2 ⟨r, hr, rfl⟩
      exact ⟨r, hr, hv⟩
    residue_nonempty := (hnonempty j).1
    gamma_nonempty := (hnonempty j).2
    source := Z j.val
    values := V j.val
    source_nonempty := j.property
    source_cut := hglobalcut j.val.1 j.val.2
    coordinate_image := himg j.val.1 j.val.2
    bijection := Classical.choice (hbij j.val.1 j.val.2)
  }
  refine ⟨Fintype.card J', fun j => C (e j), ?_, ?_⟩
  · intro j k hjk
    exact hVd (e j).val (e k).val (fun h => hjk (e.injective (Subtype.ext h)))
  · intro γ
    constructor
    · intro hγ
      obtain ⟨i, hi⟩ := (hFc γ).mp hγ
      obtain ⟨x, hx, hv⟩ := hγ
      have hxi : x ∈ (A i).carrier := by
        rw [hA i]
        refine ⟨hx, ?_⟩
        change rvUnitTupleValues x ∈ (F i).carrier
        rwa [hv]
      obtain ⟨j, hj⟩ := (hcov i γ).mp ⟨x, hxi, hv⟩
      have hxy : x ∈ (Y i j).carrier := by
        rw [hcut i j]
        refine ⟨hxi, ?_⟩
        change rvUnitTupleValues x ∈ (D i j).carrier
        rwa [hv]
      obtain ⟨k, hk⟩ := e.surjective ⟨⟨i,j⟩, x, hxy⟩
      refine ⟨k, ?_⟩
      change γ ∈ (V (e k).val).carrier
      rw [hk]
      exact hj
    · rintro ⟨j, hj⟩
      change γ ∈ (V (e j).val).carrier at hj
      obtain ⟨x, hx, hv⟩ := hDsub (e j).val.1 (e j).val.2 hj
      rw [hA (e j).val.1] at hx
      exact ⟨x, hx.1, hv⟩

end DiamondIntegral.Section5
