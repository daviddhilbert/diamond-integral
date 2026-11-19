# Section 7 gap and convention record

Independently checked against the revised main text before the referee notes.
None of these is a mathematical error; each is an omitted justification or a
formalization convention. No manuscript edit has been made for them.

1. **Grothendieck semigroups and isomorphism.** Definition 3.1 presents
   K₊ by scissor relations. 7.8, 7.10, 7.24 and 7.25 use that equal classes
   come from isomorphic objects. For μRV^db[k] the Lean class monoid
   `BoundedClasses.Cls` *is* the set of isomorphism classes under ⊎. The
   scissor relation holds there (`cls_partition`), so the two presentations
   agree. The same fact for K₊ μVF^◇[k] is still to be proved (needed in 7.24).
2. **Blowups on classes.** The paper remarks after Corollary 7.8 that the blowup
   relations may be regarded on isomorphism classes. The Lean definitions
   (`ElementaryStep`, `Step`, `BlowupSteps`, `MuIsp`) are stated on classes. A
   length-one blowup replaces summands `[U_i]` by `[U_i^♭]`, which is the class
   form of `(V ∖ C) ⊎ ⊎ U_i^♭` via `F_i : U_i ≅ C_i`. Still to do: the
   object-level converse, that a class-level blowup is realised by literal
   disjoint subobjects of a given `V`.
3. **∞ as a tag.** As in Section 4, objects are bounded charts whose label
   coordinates may equal ∞, and the coproduct tags with ∞. Section 4's
   `RVStrictBoundedComparison` shows this presentation and the paper's ∞-free
   one give isomorphic rings. The lift to μVF^◇ (milestone M3) needs ∞-free
   labels and will convert there.
4. **Named aperture bound.** Section 4's `Aperture.bound` is a Γ value without a
   definability requirement. For doubly bounded objects a named bound exists by
   Remark 7.4 (`Remark74.remark_7_4_named`).
5. **Lemma 7.23.** "By compactness" is not needed: restricting the first two
   stages of a standard contraction to the fibres over `A_E` already gives the
   fibrewise standard contractions.
6. **Lemma 7.5.** The proof splits by the pointwise order of the depths and
   uses the ratio aperture. As formalized, its comparison maps are explicit
   definable bijections, and its multipliers are coordinates or values of
   definable functions. Equal depths with different endpoints are covered:
   the second blowup has depth zero and an endpoint of valuation zero.
