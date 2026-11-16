import «section 6».NamedFiniteVFBounds

/-! One original-base named radius separates all points of a finite
definable center family. Its complete nonzero difference set is used,
so no enumeration or individual center name enters the construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def finiteCenterDifferences (E : Set (VF M)) : Set (VF M) :=
  {d | ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ a-b = d}

theorem finiteCenterDifferences_finite (E : Set (VF M)) (hE : E.Finite) :
    (finiteCenterDifferences E).Finite := by
  apply ((hE.prod hE).image (fun p => p.1-p.2)).subset
  rintro d ⟨a,ha,b,hb,hn,rfl⟩
  exact ⟨(a,b),⟨ha,hb⟩,rfl⟩

theorem finiteCenterDifferences_nonzero (E : Set (VF M)) :
    ∀ d ∈ finiteCenterDifferences E, d ≠ 0 := by
  rintro d ⟨a,ha,b,hb,hn,he⟩ h0
  exact hn (sub_eq_zero.mp (he.trans h0))

theorem finiteCenterDifferences_definable (E : Set (VF M))
    (hE : S.Definable₁ LRV (Subtype.val '' E)) :
    S.Definable₁ LRV (Subtype.val '' finiteCenterDifferences E) := by
  let J := Fin 1 ⊕ Fin 2
  have hA := hE.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : J))
  have hB := hE.preimage_comp (fun _ : Fin 1 => (Sum.inr 1 : J))
  have hNe := ((Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 0 : J))).ofPred_eq
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 1 : J)))).compl
  have hSub := (scalarSubCode_definable
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 0 : J)))
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 1 : J)))).ofPred_eq
      (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inl 0 : J)))
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' finiteCenterDifferences E}
  convert ((hA.inter hB).inter (hNe.inter hSub)).exists_of_finite using 1
  ext z
  constructor
  · rintro ⟨d,⟨a,ha,b,hb,hn,he⟩,hd⟩
    refine ⟨![a.val,b.val],⟨⟨a,ha,rfl⟩,b,hb,rfl⟩,?_,?_⟩
    · change a.val ≠ b.val
      exact fun h => hn (Subtype.ext h)
    · change iVFAdd a.val (iVFNeg b.val) = z 0
      exact (congrArg Subtype.val he).trans hd
  · rintro ⟨q,⟨⟨a,ha,hqa⟩,b,hb,hqb⟩,hne,hsub⟩
    change a.val = q 0 at hqa
    change b.val = q 1 at hqb
    change q 0 ≠ q 1 at hne
    change iVFAdd (q 0) (iVFNeg (q 1)) = z 0 at hsub
    have hab : a ≠ b := fun he => hne (hqa.symm.trans ((congrArg Subtype.val he).trans hqb))
    let a' : VF M := a
    let b' : VF M := b
    refine ⟨a'-b',⟨a',ha,b',hb,hab,rfl⟩,?_⟩
    change iVFAdd a.val (iVFNeg b.val) = z 0
    rw [hqa,hqb]
    exact hsub

theorem centered_discs_disjoint_of_value_bound (a b r : VF M) (hr : r ≠ 0)
    (hBound : vfValue (a-b) < vfValue r) :
    Disjoint (centeredGammaDisc a (finiteValue r hr)) (centeredGammaDisc b (finiteValue r hr)) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have hA := (mem_centeredGammaDisc a x (finiteValue r hr)).mp hxa
  have hB := (mem_centeredGammaDisc b x (finiteValue r hr)).mp hxb
  have hmin := vfValue_min_le_sub (x-a) (x-b)
  change min (vfValue (x-a)) (vfValue (x-b)) ≤ vfValue ((x-a)-(x-b)) at hmin
  have hComm : vfValue (b-a) = vfValue (a-b) := by
    simpa only [valueHom_eq_value] using vfValue_sub_comm b a
  rw [show (x-a)-(x-b) = b-a by abel,hComm] at hmin
  exact lt_asymm hBound ((lt_min hA hB).trans_le hmin)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_named_separating_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (E : Set (VF M)) (hE : S.Definable₁ LRV (Subtype.val '' E)) (hFin : E.Finite) :
    ∃ r : VF M, ∃ hr : r ≠ 0, S.Definable₁ LRV {r.val} ∧
      (1 : GammaInfinity M) < vfValue r ∧
      ∀ a ∈ E, ∀ b ∈ E, a ≠ b →
        Disjoint (centeredGammaDisc a (finiteValue r hr)) (centeredGammaDisc b (finiteValue r hr)) := by
  obtain ⟨r,hr,hDef,hPos,hBound⟩ := exists_named_vf_above_finite_family h00 hc hv V hV hVS hSV hnt
    (finiteCenterDifferences E) (finiteCenterDifferences_definable E hE)
    (finiteCenterDifferences_finite E hFin) (finiteCenterDifferences_nonzero E)
  exact ⟨r,hr,hDef,hPos,fun a ha b hb hn => centered_discs_disjoint_of_value_bound a b r hr
    (hBound (a-b) ⟨a,ha,b,hb,hn,rfl⟩)⟩

end DiamondIntegral.Section6
