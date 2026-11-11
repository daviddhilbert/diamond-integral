import «section 2».CorrespondenceSets
import «section 2».Atomic

/-! Full VF correspondence graphs under a definable source map. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem scalar_correspondence_pullback_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {n r : ℕ}
    (D : Set (Fin n → M)) (E : Set (Fin r → M)) (hE : DefinableOver S (fun _ => .vf) E)
    (Φ : (Fin r → M) → Fin n → M) (hΦ : S.DefinableMap LRV Φ) (hmap : Set.MapsTo Φ E D)
    (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ : Fin (n+1) => .vf)
      {z | Fin.init z ∈ D ∧ z (Fin.last n) ∈ F (Fin.init z)}) :
    DefinableOver S (fun _ : Fin (r+1) => .vf)
      {z | Fin.init z ∈ E ∧ z (Fin.last r) ∈ F (Φ (Fin.init z))} := by
  have hEsort : E ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hE
    exact fun _ hz => hz.1
  have hFsort : {z : Fin (n+1) → M | Fin.init z ∈ D ∧ z (Fin.last n) ∈ F (Fin.init z)} ⊆
      GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,hEq⟩ := hF
    intro w hw
    rw [hEq] at hw
    exact hw.1
  let W (z : Fin (r+1) → M) : Fin (n+1) → M := Fin.snoc (Φ (Fin.init z)) (z (Fin.last r))
  have hprefix : S.DefinableMap LRV (fun z : Fin (r+1) → M => Fin.init z) :=
    fun j => Set.DefinableFun.proj LRV (i := j.castSucc)
  have hW : S.DefinableMap LRV W := by
    intro j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simpa only [W,Fin.snoc_last] using (Set.DefinableFun.proj LRV (i := Fin.last r))
    · simpa only [W,Fin.snoc_castSucc] using (hΦ q).comp hprefix
  apply raw_definableOver_sorted hc
  · convert (hE.raw_definable.preimage_comp Fin.castSucc).inter (hF.raw_definable.preimage_map hW) using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,W,Fin.init_snoc,Fin.snoc_last]
    change (_ ∧ _) ↔ (_ ∧ (_ ∧ _))
    constructor
    · rintro ⟨he,hy⟩
      exact ⟨he,hmap he,hy⟩
    · rintro ⟨he,_,hy⟩
      exact ⟨he,hy⟩
  · rintro z ⟨he,hy⟩ j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · have hw : W z ∈ {w : Fin (n+1) → M | Fin.init w ∈ D ∧ w (Fin.last n) ∈ F (Fin.init w)} := by
        simpa only [W,Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last] using And.intro (hmap he) hy
      simpa only [W,Fin.snoc_last] using hFsort hw (Fin.last n)
    · exact hEsort he q

end DiamondIntegral.Section2
