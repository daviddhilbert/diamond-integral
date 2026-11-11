import «section 2».NamedRVImageGraphs

/-! Lemma 2.26 over previously named disc parameters. Constancy of each
RV membership cut follows from the proved product base-change theorem. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_relation_constant_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (R : Set ((Fin n → M) × M))
    (hR : DefinableOverFiniteDiscNames B ground d τ (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z,z (Fin.last n)) ∈ R}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ b ∈ {z | ∀ j, z j ∈ D j}, {t | (a,t) ∈ R} = {t | (b,t) ∈ R} := by
  have hmem (a b : Fin n → M) (ha : ∀ j, a j ∈ D j) (hb : ∀ j, b j ∈ D j)
      (x : M) (hx : (a,x) ∈ R) : (b,x) ∈ R := by
    have hRa : (Fin.snoc a x : Fin (n+1) → M) ∈ {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ R} := by
      simpa only [Fin.init_snoc,Fin.snoc_last,Set.mem_ofPred_eq] using hx
    have hxsort := hR.proper hRa (Fin.last n)
    have hxRV : iRV x := by
      simpa only [Fin.lastCases_last,Fin.snoc_last,sortEval,iRV] using hxsort
    let t : RVInfinity M := ⟨x,hxRV⟩
    have hAt := lemma_2_24_disc_names hc h00 B hΓ cited ground d τ D hopen hA t
    have hCut := rv_row_definable_disc_names B ground d τ R hR t
    rcases hAt.2.2.2 _ hCut with hsub | hdis
    · exact hsub hb
    · exact (Set.disjoint_left.mp hdis ha hx).elim
  intro a ha b hb
  ext x
  exact ⟨hmem a b ha hb x,hmem b a hb ha x⟩

theorem rv_image_constant_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ b ∈ {z | ∀ j, z j ∈ D j},
      iRv '' {y | (a,y) ∈ F} = iRv '' {y | (b,y) ∈ F} :=
  rv_relation_constant_disc_names hc h00 B hΓ cited ground d τ D hopen hA (vfRVImage F)
    (vfRVImage_definable_disc_names B ground d τ F hF)

/-- The paper's finitary and RV-injectivity hypotheses are retained for
the branch construction; image constancy itself proves a stronger assertion. -/
theorem lemma_2_26_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (_hfinite : ∀ a ∈ {z | ∀ j, z j ∈ D j}, {y | (a,y) ∈ F}.Finite)
    (_hrv : ∀ a ∈ {z | ∀ j, z j ∈ D j}, Set.InjOn iRv {y | (a,y) ∈ F}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ b ∈ {z | ∀ j, z j ∈ D j},
      iRv '' {y | (a,y) ∈ F} = iRv '' {y | (b,y) ∈ F} :=
  rv_image_constant_disc_names hc h00 B hΓ cited ground d τ D hopen hA F hF

end DiamondIntegral.Section2
