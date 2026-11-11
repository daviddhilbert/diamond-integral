import «section 2».TypeDiscLines
import «section 2».RVBranches

/-! RV constancy on a polydisc inside a complete type locus. The cited
input remains unary. A finite coordinate chain proves the product result,
including zero source coordinates and empty or zero-tag rows. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem type_polydisc_rv_rows_constant (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {n : ℕ} (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc (fun _ => false) a δ ⊆ A)
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) :
    ∀ p ∈ namedPolydisc (fun _ => false) a δ,
      ∀ q ∈ namedPolydisc (fun _ => false) a δ,
      iRv '' {y | (p,y) ∈ F} = iRv '' {y | (q,y) ∈ F} := by
  let D (i : Fin n) := BallImaginaries.underlying (openDiscCode (a i) (δ i))
  have hD : namedPolydisc (fun _ => false) a δ = {x | ∀ i, x i ∈ D i} := rfl
  intro p hp q hq
  have hstep (b : Fin n → M) (hb : ∀ j, b j ∈ D j)
      (he : iRv '' {y | (p,y) ∈ F} = iRv '' {y | (b,y) ∈ F})
      (i : Fin n) (x : M) (hx : x ∈ D i) :
      iRv '' {y | (p,y) ∈ F} = iRv '' {y | (Function.update b i x,y) ∈ F} := by
    apply he.trans
    cases n with
    | zero => exact i.elim0
    | succ k =>
      let E := tupleBase B (Fin.removeNth i b)
      have hΓE : NontrivialDefinableGamma E :=
        hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have hline := type_polydisc_line_atomic h00 B hΓ unary a δ A hA hsub b hb i
      let L : Set ((Fin 1 → M) × M) := {z | (Function.update b i (z.1 0),z.2) ∈ F}
      have hL : GammaParameters.DefinableOverBase E (fun _ : Fin 2 => .vf)
          {z | (Fin.init z,z (Fin.last 1)) ∈ L} := by
        convert coordinate_relation_definable B F hF b i using 1
        ext z
        rfl
      have hR := vfRVImage_definable E L hL
      have hrows := named_open_disc_rv_rows_constant h00 E hΓE (rvbase E)
        (![false]) (![a i]) (![δ i]) (D i) hline ⟨a i,δ i,rfl⟩ (vfRVImage L) hR
      ext t
      have hh := hrows (fun _ => b i) (hb i) (fun _ => x) hx t
      simpa only [vfRVImage,L,Set.mem_ofPred_eq,Function.update_eq_self,Set.mem_image] using hh
  exact rectangle_induction D (fun b =>
    iRv '' {y | (p,y) ∈ F} = iRv '' {y | (b,y) ∈ F}) p hp rfl hstep q hq

end DiamondIntegral.Section2
