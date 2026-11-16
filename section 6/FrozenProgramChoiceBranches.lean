import «section 6».FrozenProgramParameterMaps

/-! The finite program choices become actual disjoint whole-label
branches of the prepared unary domain, with their full original-base
geometry and their actual old frozen parameter map retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}

def vfParameterSet (X : Set (Fin n → M)) (hX : S.Definable LRV X) :
    DefSet (rawVFSpace (M := M) n) S := by
  let Q := rawVFSpace (M := M) n
  refine ⟨{x | vfValues x ∈ X},?_⟩
  change S.Definable LRV (Q.preimage {x | vfValues x ∈ X})
  convert (Q.definable_domain S).inter hX using 1
  ext z
  constructor
  · rintro ⟨hz,hMem⟩
    change vfValues (Q.decode ⟨z,hz⟩) ∈ X at hMem
    have he : vfValues (Q.decode ⟨z,hz⟩)=z := vfValues_decode _
    rw [he] at hMem
    exact ⟨hz,hMem⟩
  · rintro ⟨hz,hMem⟩
    refine ⟨hz,?_⟩
    change vfValues (Q.decode ⟨z,hz⟩) ∈ X
    have he : vfValues (Q.decode ⟨z,hz⟩)=z := vfValues_decode _
    rw [he]
    exact hMem

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

def choiceDomain (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :
    DefSet (rawMixedSpace (M := M) 1 F.unary.arity) S :=
  ⟨{p | ∃ b : F.unary.target,b.val=p ∧
    (F.oldParameterMap h00 b).val ∈ (vfParameterSet (F.programs.choices i) (F.programs.choices_definable i)).carrier},
    Map.definable_preimage (F.oldParameterMap h00)
      (vfParameterSet (F.programs.choices i) (F.programs.choices_definable i)).definable⟩

theorem mem_choiceDomain (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) (b : F.unary.target) :
    b.val ∈ (F.choiceDomain h00 i).carrier ↔
      unaryFamilyParameter (F.oldParameterMap h00) b ∈ F.programs.choices i := by
  have he : vfValues (F.oldParameterMap h00 b).val=unaryFamilyParameter (F.oldParameterMap h00) b := by
    funext j
    fin_cases j
    rfl
  constructor
  · rintro ⟨c,hc,hChoice⟩
    have hcEq : c=b := Subtype.ext hc
    subst c
    change vfValues (F.oldParameterMap h00 b).val ∈ F.programs.choices i at hChoice
    exact he ▸ hChoice
  · intro hChoice
    refine ⟨b,rfl,?_⟩
    change vfValues (F.oldParameterMap h00 b).val ∈ F.programs.choices i
    rw [he]
    exact hChoice

theorem choiceDomain_subset (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :
    (F.choiceDomain h00 i).carrier ⊆ F.unary.target.carrier := by
  rintro p ⟨b,hb,hChoice⟩
  exact hb ▸ b.property

theorem choiceDomain_rvPullback (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :
    IsRVPullback (F.choiceDomain h00 i).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  let b : F.unary.target := ⟨p,F.choiceDomain_subset h00 i hp⟩
  have hqB : q ∈ F.unary.target.carrier :=
    rvPullback_mem_of_sameRV F.unary.pullback b.property hVF hRV
  let c : F.unary.target := ⟨q,hqB⟩
  apply (F.mem_choiceDomain h00 i c).mpr
  exact (F.choices_on_target_labels h00 b c hRV i).mp ((F.mem_choiceDomain h00 i b).mp hp)

theorem choiceDomain_eq_focusActive (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :
    F.choiceDomain h00 i=focusActive F.unary.target (pureRVTagDomain (F.choiceDomain h00 i)) :=
  rvPullback_subdomain_eq_focusActive (F.choiceDomain_subset h00 i)
    (F.choiceDomain_rvPullback h00 i) F.unary.tagged

theorem choiceDomain_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (i : Fin F.programs.count) : ProperInvariant S (F.choiceDomain h00 i).carrier := by
  rw [F.choiceDomain_eq_focusActive h00 i]
  exact focusActive_properInvariant F.unary.target F.unary.proper _

theorem choiceDomain_cover (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (b : F.unary.target) :
    ∃ i,b.val ∈ (F.choiceDomain h00 i).carrier := by
  obtain ⟨i,hi⟩ := F.programs.cover ((F.oldParameterMap h00 b).val 0)
  exact ⟨i,(F.mem_choiceDomain h00 i b).mpr hi⟩

theorem choiceDomain_disjoint (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (i j : Fin F.programs.count) (b : F.unary.target)
    (hi : b.val ∈ (F.choiceDomain h00 i).carrier) (hj : b.val ∈ (F.choiceDomain h00 j).carrier) : i=j :=
  F.programs.disjoint i j _ ((F.mem_choiceDomain h00 i b).mp hi) ((F.mem_choiceDomain h00 j b).mp hj)

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
