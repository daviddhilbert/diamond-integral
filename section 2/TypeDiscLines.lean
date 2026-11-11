import «section 2».CitedDiscRVImages
import «section 2».NamedPolydiscAtomicity
import «section 2».RectangleImages

/-! Coordinate lines in a polydisc contained in a complete type locus.
Only the other actual VF coordinates are added to the real ground base.
The varying disc is kept as a DC name. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem type_polydisc_line_atomic (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    {n : ℕ} (a : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M)
    (A : Set (Fin (n+1) → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc (fun _ => false) a δ ⊆ A)
    (b : Fin (n+1) → M) (hb : b ∈ namedPolydisc (fun _ => false) a δ) (i : Fin (n+1)) :
    IsAtomicOverFiniteDiscNames (tupleBase B (Fin.removeNth i b)) (![false]) (![a i]) (![δ i])
      (fun _ : Fin 1 => .vf) {z | z 0 ∈ BallImaginaries.underlying (openDiscCode (a i) (δ i))} := by
  let E := tupleBase B (Fin.removeNth i b)
  let T : Set (Fin 1 → M) := {z | Fin.insertNth i (z 0) (Fin.removeNth i b) ∈ A}
  have hT : GeneratesCompleteType E (fun _ => .vf) T := hA.coordinate_fibre b (hsub hb) i
  have hΓE : NontrivialDefinableGamma E :=
    hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  apply lemma_2_25_unary h00 E (unary E) hΓE T hT false (a i) (δ i)
  intro z hz
  have hw : Function.update b i (z 0) ∈ namedPolydisc (fun _ => false) a δ := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Set.mem_ofPred_eq,Function.update_self,finitePolydiscNames,Bool.false_eq_true,ite_false] using hz
    · simpa only [Function.update_of_ne hj] using hb j
  change Fin.insertNth i (z 0) (Fin.removeNth i b) ∈ A
  simpa only [Fin.insertNth_removeNth] using hsub hw

theorem coordinate_relation_definable (B : ParameterBase M) {n : ℕ}
    (F : Set ((Fin (n+1) → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+2) => .vf)
      {z | (Fin.init z,z (Fin.last (n+1))) ∈ F})
    (b : Fin (n+1) → M) (i : Fin (n+1)) :
    GammaParameters.DefinableOverBase (tupleBase B (Fin.removeNth i b))
      (fun _ : Fin 2 => .vf)
      {z | (Function.update b i (z 0),z 1) ∈ F} := by
  let E := tupleBase B (Fin.removeNth i b)
  let W (z : Fin 2 → M) : Fin (n+2) → M :=
    Fin.snoc (Fin.insertNth i (z 0) (Fin.removeNth i b)) (z 1)
  have hnames (q : Fin n) : Fin.removeNth i b q ∈ E.real := Or.inr (Set.mem_range_self q)
  have hW : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ E.real W := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    intro j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simpa only [W,Fin.snoc_last] using (Set.DefinableFun.proj LRV (i := (1 : Fin 2)))
    · refine i.succAboveCases ?_ (fun q => ?_) q
      · simpa only [W,Fin.snoc_castSucc,Fin.insertNth_apply_same] using
          (Set.DefinableFun.proj LRV (i := (0 : Fin 2)))
      · simpa only [W,Fin.snoc_castSucc,Fin.insertNth_apply_succAbove] using
          (LRV.definableFun_const (Fin 2)
            (hnames q))
  have hF' := hF.mono (show B.real ⊆ E.real from Set.subset_union_left) (Set.Subset.refl _)
  have h := hF'.preimage_real_map (fun _ : Fin 2 => .vf) W hW
  convert h using 1
  ext z
  have hw : (Fin.init (W z),(W z) (Fin.last (n+1))) = (Function.update b i (z 0),z 1) := by
    simp only [W,Fin.init_snoc,Fin.snoc_last,Fin.insertNth_removeNth]
  change _ ↔ ((Fin.init (W z),(W z) (Fin.last (n+1))) ∈ F ∧
    z ∈ GammaParameters.sortedUniverse (fun _ => .vf))
  rw [hw]
  constructor
  · intro hz
    have hs := hF'.proper (W z) (by change _ ∈ F; rwa [hw])
    refine ⟨hz,?_⟩
    intro j
    fin_cases j
    · change sortEval SortTag.vf (z 0)
      have hx := hs i.castSucc
      simpa only [W,Fin.snoc_castSucc,Fin.insertNth_apply_same] using hx
    · change sortEval SortTag.vf (z 1)
      have hy := hs (Fin.last (n+1))
      simpa only [W,Fin.snoc_last] using hy
  · exact And.left

end DiamondIntegral.Section2
