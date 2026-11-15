import «section 5».OriginalRVTotalFamilies
import IntegrationSection6.GammaSortedBijectionRealization

/-! A full family of original bijective RV rows gives an equivalence of
the total raw domains, with every base coordinate retained literally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

def originalRawTotalEquiv (A : Set (Fin p → M))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ z ∈ A, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z) : rawRowTotal A D.val ≃ rawRowTotal A E.val :=
  (rawRowTotalEquiv A D.val).trans
    ((Equiv.sigmaCongrRight (fun z : A => (hv z.val z.property).equiv
      (fun y hy j => by
        simpa only [Fin.append_right] using E.property.proper _ hy (Fin.natAdd p j)))).trans
      (rawRowTotalEquiv A E.val).symm)

theorem originalRawTotalEquiv_value (A : Set (Fin p → M))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ z ∈ A, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z) (u : rawRowTotal A D.val) :
    (originalRawTotalEquiv A D E H hv u).val =
      Fin.append (u.val ∘ Fin.castAdd a)
        ((hv _ u.property.1).map ⟨u.val ∘ Fin.natAdd p,by
          change Fin.append (u.val ∘ Fin.castAdd a) (u.val ∘ Fin.natAdd p) ∈ D.val
          simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using u.property.2⟩).val := rfl

theorem originalRawTotalEquiv_graph (A : Set (Fin p → M))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ z ∈ A, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z) (u : Fin (p+a) → M) (v : Fin (p+b) → M) :
    (∃ t : rawRowTotal A D.val, t.val = u ∧
      (originalRawTotalEquiv A D E H hv t).val = v) ↔
      u ∘ Fin.castAdd a ∈ A ∧ v ∘ Fin.castAdd b = u ∘ Fin.castAdd a ∧
        Fin.append u (v ∘ Fin.natAdd p) ∈ H.val := by
  constructor
  · rintro ⟨t,rfl,rfl⟩
    rw [originalRawTotalEquiv_value]
    refine ⟨t.property.1,?_,?_⟩
    · funext j
      exact Fin.append_left _ _ j
    · have hg := (hv _ t.property.1).map_graph
        ⟨t.val ∘ Fin.natAdd p,by
          change Fin.append (t.val ∘ Fin.castAdd a) (t.val ∘ Fin.natAdd p) ∈ D.val
          simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using t.property.2⟩
      simpa only [Function.comp_def,Fin.append_right,Fin.append_castAdd_natAdd] using hg
  · rintro ⟨hz,he,hg⟩
    have hsplit : Fin.append (u ∘ Fin.castAdd a) (u ∘ Fin.natAdd p) = u := Fin.append_castAdd_natAdd
    have hh := (hv _ hz).equiv_graph
      (fun y hy j => by
        simpa only [Fin.append_right] using E.property.proper _ hy (Fin.natAdd p j))
      (u ∘ Fin.natAdd p) (v ∘ Fin.natAdd p)
    rw [hsplit] at hh
    obtain ⟨t,ht,hv'⟩ := hh.mp hg
    have hu : u ∈ D.val := by
      have h : Fin.append (u ∘ Fin.castAdd a) t.val ∈ D.val := t.property
      rw [ht,hsplit] at h
      exact h
    refine ⟨⟨u,hz,hu⟩,rfl,?_⟩
    rw [originalRawTotalEquiv_value]
    have htail : ((hv _ hz).map ⟨u ∘ Fin.natAdd p,by
        change Fin.append (u ∘ Fin.castAdd a) (u ∘ Fin.natAdd p) ∈ D.val
        rw [hsplit]; exact hu⟩).val =
        v ∘ Fin.natAdd p := by
      have hte : t = ⟨u ∘ Fin.natAdd p,by
        change Fin.append (u ∘ Fin.castAdd a) (u ∘ Fin.natAdd p) ∈ D.val
        rw [hsplit]; exact hu⟩ := Subtype.ext ht
      exact hte ▸ hv'
    rw [htail,← he]
    exact Fin.append_castAdd_natAdd

end DiamondIntegral.Section5
