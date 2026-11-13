import IntegrationSection3ACVF.FullGammaPoint
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : FullBaseAtomicity.Base (M := M)}
/-- Iterating projection and fibres supplies an original-base definable
point in every nonempty definable finite-dimensional Gamma set. -/
theorem fullGammaTuple_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {n : ℕ} (A : Set (Fin n → Values.Gamma (M := M)))
    (hA : FullGammaSyntax.Definable B (fun a => a ∈ A)) (hne : A.Nonempty) :
    ∃ γ ∈ A, ∀ i, FullGammaSyntax.Scalar B {γ i} := by
  induction n with
  | zero =>
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, fun i => i.elim0⟩
  | succ n ih =>
    let idx : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.lastCases (.inr 0) Sum.inl
    have hidx (a : Fin n → Values.Gamma (M := M)) (b : Fin 1 → Values.Gamma (M := M)) :
        Sum.elim a b ∘ idx = Fin.snoc a (b 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, idx, Fin.lastCases_last, Sum.elim_inr, Fin.snoc_last]
      · simp only [Function.comp_apply, idx, Fin.lastCases_castSucc, Sum.elim_inl, Fin.snoc_castSucc]
    let P : Set (Fin n → Values.Gamma (M := M)) := {a | ∃ b, Fin.snoc a b ∈ A}
    have hP : FullGammaSyntax.Definable B (fun a => a ∈ P) := by
      have h := (hA.reindex idx).exists_block
      exact h.congr (fun a => by
        constructor
        · rintro ⟨b, hb⟩
          exact ⟨b 0, by rwa [hidx] at hb⟩
        · rintro ⟨b, hb⟩
          exact ⟨fun _ => b, by rwa [hidx]⟩)
    have hPne : P.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨Fin.init a, a (Fin.last n), by simpa only [Fin.snoc_init_self] using ha⟩
    obtain ⟨a, ⟨b, hab⟩, had⟩ := ih P hP hPne
    let T : Set (Values.Gamma (M := M)) := {b | Fin.snoc a b ∈ A}
    let ι := Fin 1 ⊕ Fin n
    let idx' : Fin (n + 1) → ι := Fin.lastCases (.inl 0) Sum.inr
    have hidx' (z : Fin 1 → Values.Gamma (M := M)) (t : Fin n → Values.Gamma (M := M)) :
        Sum.elim z t ∘ idx' = Fin.snoc t (z 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, idx', Fin.lastCases_last, Sum.elim_inl, Fin.snoc_last]
      · simp only [Function.comp_apply, idx', Fin.lastCases_castSucc, Sum.elim_inr, Fin.snoc_castSucc]
    have hnames : FullGammaSyntax.Definable B
        (fun z : ι → Values.Gamma (M := M) => ∀ i, z (.inr i) = a i) :=
      FullGammaSyntax.Definable.forall_finite (fun i => FullGammaSyntax.unary_at (had i) (Sum.inr i))
    have hT : FullGammaSyntax.Scalar B T := by
      have h := ((hA.reindex idx').and hnames).exists_block
      apply (FullGammaSyntax.scalar_definable_iff T).mp
      exact h.congr (fun z => by
        simp only [hidx', Sum.elim_inr]
        change (∃ t : Fin n → Values.Gamma (M := M),
          Fin.snoc t (z 0) ∈ A ∧ ∀ i, t i = a i) ↔ Fin.snoc a (z 0) ∈ A
        constructor
        · rintro ⟨t, ht, he⟩
          have hta : t = a := funext he
          rwa [hta] at ht
        · intro hz
          exact ⟨a, hz, fun _ => rfl⟩)
    obtain ⟨c, hc, hcd⟩ := FullGammaPoint.gamma_definable_point h00 δ hδ hδ1 T hT ⟨b, hab⟩
    refine ⟨Fin.snoc a c, hc, ?_⟩
    exact Fin.lastCases (by simpa only [Fin.snoc_last] using hcd)
      (fun i => by simpa only [Fin.snoc_castSucc] using had i)

end DiamondIntegral.Section3
