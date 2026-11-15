import «section 5».MonomialPieceScalarGraphs
import «section 3».GammaGroundFiniteValuePoints

/-! Pulling an original Gamma graph back through a monomial chart uses
only its fixed definable value tuple and free Gamma coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

def GroundMonomialPiece.freeValueReconstruction (P : GroundMonomialPiece X)
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) : Fin n → Values.Gamma (M := M) :=
  P.cell.valueReconstruction P.split (Sum.elim P.beta η)

theorem GroundMonomialPiece.freeValueReconstruction_definable (P : GroundMonomialPiece X) (i : Fin n) :
    FullGammaFunction (integrationGammaBase B) (fun η => P.freeValueReconstruction η i) := by
  change FullGammaFunction (integrationGammaBase B) (fun η =>
    ∏ j, Sum.elim P.beta η (coordinateValueIndex P.split j) ^ integerBasisInverseMatrix P.cell.basis i j)
  apply FullGammaFunction.prod Finset.univ
  intro j _
  apply FullGammaFunction.zpow
  cases h : coordinateValueIndex P.split j with
  | inl k =>
    simpa only [h, Sum.elim_inl] using
      FullGammaFunction.constant (α := Fin P.split.freeArity) (P.beta k)
        (integrationGammaDefinable (P.beta_definable k))
  | inr k =>
    simpa only [h, Sum.elim_inr] using FullGammaFunction.proj (integrationGammaBase B) k

theorem GroundMonomialPiece.freeValueReconstruction_coordinate (P : GroundMonomialPiece X)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ P.source.carrier) :
    P.freeValueReconstruction (rvUnitTupleValues (P.cell.coordinateEquiv P.split x).2) = rvUnitTupleValues x := by
  have h := P.cell.valueReconstruction_coordinate P.split x
  rw [P.active_values x hx] at h
  exact h

def GroundMonomialPiece.reconstructedGammaGraph (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))) := by
  let f (i : Fin (n+1)) (z : Fin (P.split.freeArity+1) → Values.Gamma (M := M)) :=
    Fin.snoc (α := fun _ : Fin (n+1) => Values.Gamma (M := M))
      (P.freeValueReconstruction ((z ∘ Fin.castSucc))) (z (Fin.last P.split.freeArity)) i
  have hf : ∀ i, FullGammaFunction (integrationGammaBase B) (f i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f, Fin.snoc_last] using
        FullGammaFunction.proj (integrationGammaBase B) (Fin.last P.split.freeArity)
    · simpa only [f, Fin.snoc_castSucc, Fin.init] using
        (P.freeValueReconstruction_definable j).reindex (Fin.castSucc : Fin P.split.freeArity → Fin (P.split.freeArity+1))
  have hI := ((gammaGroundGammaPower_definable_iff P.gamma.carrier).mp P.gamma.definable).reindex
    (Fin.castSucc : Fin P.split.freeArity → Fin (P.split.freeArity+1))
  have hD := (gammaGroundGammaPower_definable_iff D.carrier).mp D.definable
  exact ⟨{z | (z ∘ Fin.castSucc) ∈ P.gamma.carrier ∧
      Fin.snoc (α := fun _ : Fin (n+1) => Values.Gamma (M := M)) (P.freeValueReconstruction (z ∘ Fin.castSucc)) (z (Fin.last P.split.freeArity)) ∈ D.carrier},
    gammaGroundGammaPower_predicate_definable _ (hI.and (FullGammaFunction.substitute hD f hf))⟩

theorem GroundMonomialPiece.reconstructedGammaGraph_row (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (γ : Values.Gamma (M := M)) :
    Fin.snoc η γ ∈ (P.reconstructedGammaGraph D).carrier ↔
      η ∈ P.gamma.carrier ∧ Fin.snoc (P.freeValueReconstruction η) γ ∈ D.carrier := by
  have hi : (Fin.snoc (α := fun _ : Fin (P.split.freeArity+1) => Values.Gamma (M := M)) η γ) ∘ Fin.castSucc = η := by
    funext j
    simp only [Function.comp_def, Fin.snoc_castSucc]
  change (_ ∧ _) ↔ _
  rw [hi, Fin.snoc_last]

theorem GroundMonomialPiece.reconstructedGammaGraph_exists (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hcomplete : ∀ x ∈ P.source.carrier, ∃ γ, Fin.snoc (rvUnitTupleValues x) γ ∈ D.carrier)
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (hη : η ∈ P.gamma.carrier) :
    ∃ γ, Fin.snoc η γ ∈ (P.reconstructedGammaGraph D).carrier := by
  obtain ⟨r, hr⟩ := P.residue_nonempty
  obtain ⟨z, hz⟩ := rvUnitTupleValues_surjective P.split.freeArity η
  let e := P.cell.coordinateEquiv P.split
  let u := e.symm (r,z)
  have heu : e u = (r,z) := e.apply_symm_apply _
  have hu : u ∈ P.source.carrier := by
    apply (P.coordinate_mem_iff u).mp
    change e u ∈ _
    rw [heu]
    refine ⟨hr, ?_⟩
    change rvUnitTupleValues z ∈ P.gamma.carrier
    rwa [hz]
  have hfree : rvUnitTupleValues (e u).2 = η := by rw [heu]; exact hz
  have huvalue : rvUnitTupleValues u = P.freeValueReconstruction η := by
    have hv := P.freeValueReconstruction_coordinate u hu
    change P.freeValueReconstruction (rvUnitTupleValues (e u).2) = _ at hv
    rw [hfree] at hv
    exact hv.symm
  obtain ⟨γ, hγ⟩ := hcomplete u hu
  refine ⟨γ, (P.reconstructedGammaGraph_row D η γ).mpr ⟨hη, ?_⟩⟩
  rwa [← huvalue]


theorem GroundMonomialPiece.reconstructedGammaGraph_unique (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hD : ∀ α ∈ D.carrier, ∀ β ∈ D.carrier, Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (γ δ : Values.Gamma (M := M))
    (hγ : Fin.snoc η γ ∈ (P.reconstructedGammaGraph D).carrier)
    (hδ : Fin.snoc η δ ∈ (P.reconstructedGammaGraph D).carrier) : γ = δ := by
  have hg := ((P.reconstructedGammaGraph_row D η γ).mp hγ).2
  have hd := ((P.reconstructedGammaGraph_row D η δ).mp hδ).2
  have he := hD _ hg _ hd (by
    funext j
    simp only [Fin.init, Fin.snoc_castSucc])
  simpa only [Fin.snoc_last] using he

theorem GroundMonomialPiece.reconstructedGammaGraph_existsUnique (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hD : ∀ α ∈ D.carrier, ∀ β ∈ D.carrier, Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hcomplete : ∀ x ∈ P.source.carrier, ∃ γ, Fin.snoc (rvUnitTupleValues x) γ ∈ D.carrier)
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (hη : η ∈ P.gamma.carrier) :
    ∃! γ, Fin.snoc η γ ∈ (P.reconstructedGammaGraph D).carrier := by
  obtain ⟨γ, hγ⟩ := P.reconstructedGammaGraph_exists D hcomplete η hη
  exact ⟨γ, hγ, fun δ hδ => P.reconstructedGammaGraph_unique D hD η δ γ hδ hγ⟩

end DiamondIntegral.Section5
