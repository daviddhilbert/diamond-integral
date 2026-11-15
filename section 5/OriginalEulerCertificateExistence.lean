import «section 5».OriginalGammaCellTrees
import «section 5».NativeGammaRelationSyntax

/-! Actual original-base Euler packages exist for every native Gamma set
over a displayed parameter tuple. Both the source and every cell predicate
are promoted before compactness, and the computed integers are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure OriginalEulerCertificate (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag) (n : ℕ) where
  size : ℕ
  cells : Fin size → OriginalGammaCellTree B sp n

def OriginalEulerCertificate.syntax (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}
    (C : OriginalEulerCertificate B sp n) : EulerFormulaCertificate LRV (commonRealNames B ⊕ Fin p) n :=
  ⟨C.size, fun i => (C.cells i).syntax hc⟩

theorem finitePartitionValidity_of_gamma_presentations {P : Type*} {n : ℕ} {ι : Type} [Finite ι]
    (D : LRV.Formula (P ⊕ Fin n)) (C : ι → LRV.Formula (P ⊕ Fin n)) (v : P → M)
    (X : Set (Fin n → Values.Gamma (M := M))) (R : ι → Set (Fin n → Values.Gamma (M := M)))
    (hD : gammaFormulaRepresents D v X) (hC : ∀ i, gammaFormulaRepresents (C i) v (R i))
    (hcover : X = ⋃ i, R i) (hdisj : Pairwise (fun i j => Disjoint (R i) (R j))) :
    (finitePartitionValidityFormula D C).Realize v := by
  apply (finitePartitionValidityFormula_realize D C v).mpr
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨hp, hm⟩ := (hD x).mp hx
      rw [hcover] at hm
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
      exact ⟨i, (hC i x).mpr ⟨hp, hi⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨hp, hm⟩ := (hC i x).mp hi
      apply (hD x).mpr
      exact ⟨hp, hcover.symm ▸ Set.mem_iUnion.mpr ⟨i, hm⟩⟩
  · intro i j hij x hx
    exact Set.disjoint_left.mp (hdisj hij) ((hC i x).mp hx.1).2 ((hC j x).mp hx.2).2

theorem original_euler_certificate_exists (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {p n : ℕ} (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (X : Set (Fin n → Values.Gamma (M := M)))
    (hX : GammaDefinable ⟨B.real ∪ Set.range z, B.gamma⟩ X) :
    ∃ D : GammaDomainFormula B p n sp, ∃ C : OriginalEulerCertificate B sp n,
      gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z) X ∧
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
        (nativeGammaRelationSyntax hc).less (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z) ∧
      ∀ k : EulerKind, GammaIteratedIntegral.integrateAll h00 hκ hs
        ⟨B.real ∪ Set.range z, B.gamma⟩ (small_union_range_carrier hκ B.real hr z) hγ k n
        (GammaIndicators.indicatorFamily _ X hX) = (C.syntax hc).eulerValue k := by
  let G := nativeGammaRelationSyntax hc
  obtain ⟨D, hD⟩ := promote_original_gamma_predicate hc B sp z hz
    {x : Fin n → M | Proper x ∧ (fun i => codeValue (M := M) (x i)) ∈ X} hX
  have hrep : gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z) X := hD
  obtain ⟨A, shape, hshape, hEuler⟩ := finite_cylindrical_euler_certificate h00 hκ hs
    ⟨B.real ∪ Set.range z, B.gamma⟩ (small_union_range_carrier hκ B.real hr z) hγ n X hX
  have hex (i : Fin A.size) := shaped_gamma_cell_has_original_formula_tree hc B sp z hz
    G.proper G.equal G.less G.proper_realize G.equal_realize G.less_realize (hshape i)
  choose cell hcellShape hcellValid hcellRep using hex
  let C : OriginalEulerCertificate B sp n := ⟨A.size, cell⟩
  refine ⟨D, C, hrep, ?_, ?_⟩
  · change (finiteWitnessValidityFormula (fun i => ((cell i).syntax hc).validity G.proper G.equal G.less) ⊓
      finitePartitionValidityFormula (gammaDomainSyntax hc B D) (fun i => ((cell i).syntax hc).domain)).Realize _
    rw [Formula.realize_inf, finiteWitnessValidityFormula_realize]
    exact ⟨hcellValid, finitePartitionValidity_of_gamma_presentations _ _ _ X A.pieces hrep hcellRep A.cover A.disjoint⟩
  · intro k
    exact (hEuler k).trans (Finset.sum_congr rfl (fun i _ =>
      (congrArg (fun s => s.eulerValue k) (hcellShape i)).symm))

end DiamondIntegral.Section5
