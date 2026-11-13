import «section 3».IntegrationDiscAtomicity
import «section 3».IntegrationUnaryImages
import IntegrationSection3ACVF.RealParameterPromotion
import «section 2».CitedDiscRVImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Checked [18] 3.9 and 3.13 over every retained finite tuple of actual
disc names. Real-parameter promotion keeps full code invariance and covers
the zero RV label as well. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationDiscUnaryAtomic {B : GammaParameters.Base (M := M)} {k : ℕ}
    {closed : Fin k → Bool} {a : Fin k → Section2.VF M} {δ : Fin k → Section2.Gamma M} {D : Set M}
    (hD : Section2.IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D}) :
    AdjoinBall.AtomicOver (integrationDiscBase B closed a δ) D := by
  have ht := integrationDiscAtomic hD
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.unary_tuple_atomic_iff.mp ht

theorem integrationRVCoordinate_definable (B : FullBaseAtomicity.Base (M := M))
    {α : Type} [Finite α] (i : α) : FullBaseAtomicity.OverBase B {z : α → M | iRV (z i)} := by
  have hu := ((definableOver_iff_normalized_raw B.real (fun _ : Fin 1 => .rv)
    {z | iRV (z 0)}).mp (definableAt_sort B.real .rv).1).1
  exact FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hu)
    (fun _ : Fin 1 => i)

def integrationRVCutRows (R : Set (Fin 1 ⊕ Fin 1 → M)) (x : Section2.VF M) : Set (Fin 1 → M) :=
  {ys | iRV (ys 0) ∧ Sum.elim ys ![x.val] ∈ R}

theorem integrationRVCutRows_graph (B : FullBaseAtomicity.Base (M := M))
    (R : Set (Fin 1 ⊕ Fin 1 → M)) (hR : FullBaseAtomicity.OverBase B R)
    (D : Set M) (hD : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ D}) :
    FullBaseAtomicity.OverBase B (OpenBallConstancy.graphOn D (integrationRVCutRows R)) := by
  let π : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 1) (fun _ => 0)
  have hr := FullBaseAtomicity.OverBase.preimage_comp hR π
  have hd := FullBaseAtomicity.OverBase.preimage_comp hD (fun _ : Fin 1 => (0 : Fin 2))
  have hv := integrationVFCoordinate_definable B (0 : Fin 2)
  have ht := integrationRVCoordinate_definable B (1 : Fin 2)
  convert FullBaseAtomicity.OverBase.inter hv (FullBaseAtomicity.OverBase.inter ht
    (FullBaseAtomicity.OverBase.inter hr hd)) using 1
  ext z
  constructor
  · rintro ⟨⟨x,hx,hf⟩,hz⟩
    refine ⟨(show iVF (z 0) from hx ▸ x.property),hf.1,?_,hz⟩
    have he : Sum.elim (Fin.tail z) ![x.val] = z ∘ π := by
      funext j
      cases j with
      | inl i => fin_cases i; rfl
      | inr i => fin_cases i; exact hx
    change z ∘ π ∈ R
    exact he ▸ hf.2
  · rintro ⟨hv,ht,hr,hd⟩
    refine ⟨⟨⟨z 0,hv⟩,rfl,ht,?_⟩,hd⟩
    have he : Sum.elim (Fin.tail z) ![z 0] = z ∘ π := by
      funext j
      cases j with
      | inl i => fin_cases i; rfl
      | inr i => fin_cases i; rfl
    exact he.symm ▸ hr

theorem integrationFullOpenRVAtomic (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) (ρ : Values.Gamma (M := M))
    (hρ : FullGammaSyntax.Scalar B {ρ}) (hρ1 : 1 < ρ)
    (D : Set M) (ho : PaperBalls.IsOpenBall D)
    (hD : FullGammaAtomicity.AtomicTuple B {z : Fin 1 → M | z 0 ∈ D})
    (hne : D.Nonempty) (hp : D ⊆ {x | iVF x}) (t : Section2.RVInfinity M) :
    FullGammaAtomicity.AtomicTuple (RealParameterTuples.extend B ![t.val]) {z : Fin 1 → M | z 0 ∈ D} := by
  have ha : AdjoinBall.AtomicOver B D := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.unary_tuple_atomic_iff.mp hD
  refine ⟨RealParameterTuples.mono B ![t.val] hD.1,?_⟩
  intro T hT
  obtain ⟨R,hR,hRT⟩ := RealParameterPromotion.promote B ![t.val] hT
  let f := integrationRVCutRows R
  have hf : ∀ x : Section2.VF M, x.val ∈ D → ∀ ys ∈ f x, ∀ i, iRV (ys i) := by
    intro x hx ys hys i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
    exact hys.1
  have hc := OpenBallConstancy.lemma_3_9_open h00 B ρ hρ hρ1 ho ha f hf
    (integrationRVCutRows_graph B R hR D hD.1)
  have hrow (x : Section2.VF M) : ![t.val] ∈ f x ↔ ![x.val] ∈ T := by
    change (iRV t.val ∧ Sum.elim ![t.val] ![x.val] ∈ R) ↔ _
    rw [and_iff_right t.property]
    exact Set.ext_iff.mp hRT ![x.val]
  obtain ⟨w,hw⟩ := hne
  let y : Section2.VF M := ⟨w,hp hw⟩
  have hdec (z : Fin 1 → M) (hz : z 0 ∈ D) : z ∈ T ↔ ![y.val] ∈ T := by
    let x : Section2.VF M := ⟨z 0,hp hz⟩
    have he := hc x hz y hw
    have h := (hrow x).symm.trans ((Set.ext_iff.mp he ![t.val]).trans (hrow y))
    have hzeta : ![x.val] = z := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi]
      rfl
    rwa [hzeta] at h
  by_cases hy : ![y.val] ∈ T
  · exact Or.inl (fun z hz => (hdec z hz).mpr hy)
  · exact Or.inr (Set.disjoint_left.mpr fun z hz ht => hy ((hdec z hz).mp ht))

theorem integrationDiscBase_adjoinRV (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (t : Section2.RVInfinity M) :
    integrationDiscBase (Section2.adjoinRV B t) closed a δ =
      RealParameterTuples.extend (integrationDiscBase B closed a δ) ![t.val] := by
  have hr : Set.range (![t.val] : Fin 1 → M) = {t.val} := by
    ext x
    simp only [Set.mem_range,Set.mem_singleton_iff,Fin.exists_fin_one,Matrix.cons_val_zero]
    exact eq_comm
  simp only [integrationDiscBase,Section2.adjoinRV,RealParameterTuples.extend,hr,Set.union_singleton]

theorem integrationUnaryOpenDiscRVBaseChangeInput (B : GammaParameters.Base (M := M)) :
    Section2.UnaryOpenDiscRVBaseChangeInput B := by
  intro h00 hΓ k closed a δ D hD ho t
  obtain ⟨ρ,hρ,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let C := integrationDiscBase B closed a δ
  have hd : FullGammaSyntax.Scalar C {ρ} :=
    FullBaseAtomicity.OverBase.mono hρ Set.Subset.rfl (integrationDiscBase_mono B closed a δ)
  have hp : D ⊆ {x | iVF x} := by
    intro x hx
    have h := hD.2.2.1 (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ D} from hx) 0
    simpa only [sortEval,iVF,Matrix.cons_val_zero,Set.mem_ofPred_eq] using h
  have hn : D.Nonempty := by
    obtain ⟨z,hz⟩ := hD.2.1
    exact ⟨z 0,hz⟩
  have hu := integrationFullOpenRVAtomic h00 C ρ hd hρ1 D
    ((integrationIsOpenBall_iff D).mpr (Or.inr ho)) (integrationDiscAtomic hD) hn hp t
  rw [← integrationDiscBase_adjoinRV] at hu
  exact integrationDiscAtomic_to_native hu hD.2.1 hD.2.2.1

theorem integrationOpenDiscNamesImageInput (B : GammaParameters.Base (M := M)) :
    Section2.OpenDiscNamesImageInput B := by
  intro h00 hΓ k closed a δ D f hD ho hG hnonconstant
  obtain ⟨ρ,hρ,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let C := integrationDiscBase B closed a δ
  have hd : FullGammaSyntax.Scalar C {ρ} :=
    FullBaseAtomicity.OverBase.mono hρ Set.Subset.rfl (integrationDiscBase_mono B closed a δ)
  have hf : ∀ x ∈ D, iVF (f x) := by
    intro x hx
    have h := hG.proper (show ![x,f x] ∈ Section2.scalarVFGraph D f from ⟨hx,rfl⟩) 1
    simpa only [sortEval,iVF,Matrix.cons_val_one,Matrix.cons_val_zero] using h
  have hg := integrationFiniteDiscDefinable_to_full B closed a δ (fun _ : Fin 2 => .vf)
    (Section2.scalarVFGraph D f) hG
  rcases OpenImages.lemma_3_13 C h00 ρ hd hρ1
      ((integrationIsOpenBall_iff D).mpr (Or.inr ho)) (integrationDiscUnaryAtomic hD) f hg hf with hc | hi
  · exact (hnonconstant ⟨hc.choose.val,hc.choose_spec⟩).elim
  · apply ((integrationIsOpenBall_iff (f '' D)).mp hi.2).resolve_left
    intro he
    exact OpenBallConstancy.atomic_not_contains_vf C hi.1 (he.symm ▸ Set.Subset.rfl)
end DiamondIntegral.Section3
