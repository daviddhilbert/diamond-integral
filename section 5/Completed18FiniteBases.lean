import «section 5».Completed18CellBaseTransfer
import IntegrationSection6.VFParameterCoefficientBases
import TypedModelMap

/-! Each original-Gamma formula uses a finite VF base and finitely many
RV parameters. Taking definable closure of just the VF and Gamma names
gives a small generated base; the RV names remain explicit labels. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem finite_generated_rv_parameter_base {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (B : Base (M := M)) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma)
    {n m : ℕ} (U : Set (Point (M := M) n m)) (hU : GammaSetDefinable B U) :
    ∃ (G : Base (M := M)) (F : VFFieldBase G.real), VFGammaGeneratedBase G ∧
      Cardinal.mk G.real < κ ∧ δ ∈ G.gamma ∧ BaseDefinableIn G B ∧
      ∃ (r : ℕ) (z : Fin r → RV (M := M)),
        (∀ i,(z i).val ∈ B.real) ∧ GammaSetDefinable (RVLabelSlices.labelBase G z) U := by
  obtain ⟨k,γ,hγ,Q,hQU⟩ := hU
  obtain ⟨D,hDB,R,hRQ⟩ := Q.finite_real_support
  let A := D.filter (fun x => iVF x)
  let E := D.filter (fun x => iRV x)
  let e := E.equivFin
  let z : Fin E.card → RV (M := M) := fun i =>
    ⟨(e.symm i).val,(Finset.mem_filter.mp (e.symm i).property).2⟩
  let C : Base (M := M) := ⟨(A : Set M),insert δ (Set.range γ)⟩
  let G := closureBase C
  have hCBreal : C.real ⊆ B.real := fun x hx => hDB (Finset.mem_filter.mp hx).1
  have hCBgamma : C.gamma ⊆ B.gamma := by
    rintro x (hx | ⟨i,rfl⟩)
    · exact hx ▸ hδ
    · exact hγ i
  have hsmallA : Cardinal.mk C.real < κ := by
    letI : Finite C.real := inferInstanceAs (Finite (A : Set M))
    exact Cardinal.mk_lt_aleph0.trans hκ
  have hsmallG : Cardinal.mk C.gamma < κ := by
    have hf : C.gamma.Finite := (Set.finite_range γ).insert δ
    letI := hf.to_subtype
    exact Cardinal.mk_lt_aleph0.trans hκ
  have hGsmall := closureBase_real_small hκ C hsmallA hsmallG
  have hgen : VFGammaGeneratedBase G :=
    ⟨C.real,C.gamma,(subset_closureBase C).1,(subset_closureBase C).2,
      fun x hx => (Finset.mem_filter.mp hx).2,rfl⟩
  have hGb : BaseDefinableIn G B := closureBase_mono hCBreal hCBgamma
  have hzB (i : Fin E.card) : (z i).val ∈ B.real :=
    hDB (Finset.mem_filter.mp (e.symm i).property).1
  have hDsub : (D : Set M) ⊆ (RVLabelSlices.labelBase G z).real := by
    intro x hx
    rcases TypedModelMap.sort_cover x with hv | hr
    · exact Or.inl ((subset_closureBase C).1 (Finset.mem_filter.mpr ⟨hx,hv⟩))
    · let u : E := ⟨x,Finset.mem_filter.mpr ⟨hx,hr⟩⟩
      exact Or.inr ⟨e u,congrArg Subtype.val (e.symm_apply_apply u)⟩
  have hΓ (i : Fin k) : γ i ∈ G.gamma :=
    (subset_closureBase C).2 (Set.mem_insert_of_mem _ ⟨i,rfl⟩)
  refine ⟨G,closureBase_field C,hgen,hGsmall,(subset_closureBase C).2 (Set.mem_insert _ _),hGb,
    E.card,z,hzB,k,γ,hΓ,R.monoReal hDsub,?_⟩
  change (R.monoReal hDsub).fibre γ = gammaPointCode '' U
  change R.fibre γ = gammaPointCode '' U
  have hf : R.fibre γ = Q.fibre γ := by
    ext x
    exact Set.ext_iff.mp hRQ (rawTuple (representatives γ),x)
  exact hf.trans hQU

end DiamondIntegral.Section5
