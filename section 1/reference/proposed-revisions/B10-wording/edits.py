"""Author-directed wording changes of November 23 (applied without a review round).

1. "original" in the sense of the parameter base was introduced by the formalization work; the
   author never uses it and says "ground structure S", never "ground S". Base-related uses are
   removed: "definable" already means definable over the ground structure S, and "t-definable"
   means definable over S together with t. Where the word marked a real contrast (after an
   enlargement of the base, or with a named parameter), the contrast is kept in other words.
   Uses of "original" that mean "the given object before a construction changes it" are kept.
2. "Gamma" written as a word becomes the letter $\\Gamma$.
3. Section 5 is renumbered: the counter jumps that kept the old numbers 5.12, 5.14, 5.15 are
   removed, so the three items are Lemma 5.1, Notation 5.2, Notation 5.3.
"""

PAIRS = [
    (r"For a real/$\Gamma$ ground base the following argument also applies.",
     r"Without disc parameters, the following argument applies."),
    (r"it would contain a point algebraic over the fixed ground base. This point belongs to a finite ground-definable set.",
     r"it would contain a point algebraic over $\mathbb S$. This point belongs to a finite definable set."),
    (r"over the ground base together with this disc parameter",
     r"over $\mathbb S$ together with this disc parameter"),
    (r"Thus there is a ground-definable set $A_a\sub A$",
     r"Thus there is a definable set $A_a\sub A$"),
    (r"No choice over the original parameter base is asserted.",
     r"No choice over $\mathbb S$ itself is asserted."),
    (r"make these functions definable over the original parameter base.",
     r"make these functions definable."),
    (r"proves the asserted continuity. This spells out the relative-closure step in the original implication.",
     r"proves the asserted continuity."),
    ("every Gamma value,\nand every old-ground RV point.",
     "every $\\Gamma$ value,\nand every definable RV point."),
    (r"All definitions below use the original ground $\mathbb S$.",
     r"All definitions below use the ground structure $\mathbb S$."),
    (r"The finite product normal form over the original ground partitions",
     r"The finite product normal form over the ground structure $\mathbb S$ partitions"),
    ("has finite original-ground\nGamma image.",
     "has finite\n$\\Gamma$-image."),
    (r"original-ground definable bijection between the two product lifts;",
     r"definable bijection between the two product lifts;"),
    (r"and their values are definable over the original ground.",
     r"and their values are definable."),
    (r"original-ground RV representative of $\boldsymbol\delta$ is chosen.",
     r"definable RV representative of $\boldsymbol\delta$ is chosen."),
    (r"exceptions in finitely many proper original-ground integral-character",
     r"exceptions in finitely many proper definable integral-character"),
    (r"fixed original-ground value. Finite-Gamma balancing transfers that",
     r"fixed definable value. Finite-$\Gamma$ balancing transfers that"),
    (r"of native charts, the forms glue to an original-ground definable form;",
     r"of native charts, the forms glue to a definable form;"),
    (r"A definable Gamma value need not have a definable RV lift, as already noted after Definition~\ref{def:Ga:cat}. All choices are made over the original parameter base.",
     r"A definable $\Gamma$ value need not have a definable RV lift, as already noted after Definition~\ref{def:Ga:cat}. All choices are made over the ground structure $\mathbb S$."),
    ("$I=(\\bm P_\\Gamma)$ of Notation~\\ref{pgammabis}, with exactly its\noriginal RV-liftable radius indexing.",
     "$I=(\\bm P_\\Gamma)$ of Notation~\\ref{pgammabis}, with the same set\n$D_{\\RV}$ of radii."),
    (r"factor through $B/J_{\mathrm{var}}$, with their original restrictions",
     r"factor through $B/J_{\mathrm{var}}$, with the same restrictions"),
    (r"is definable over the original base, is nonzero, and has",
     r"is definable, is nonzero, and has"),
    (r"Their supremum is definable over the original base together with $t$, and",
     r"Their supremum is $t$-definable, and"),
    ("with the radius tuple definable\nover the original base together with $\\rv(\\gp)$.",
     "with the radius tuple\n$\\rv(\\gp)$-definable."),
    (r"All these maps and bounds are over the original base.",
     r"All these maps and bounds are definable."),
    (r"the original scalar ones. The existing bounds",
     r"the scalar ones. The existing bounds"),
    (r"RV labels remain variables over the original VF-generated base.",
     r"RV labels remain variables over $\mathbb S$."),
    (r"choose original-base definable offsets",
     r"choose definable offsets"),
    ("gives one original-base\nnamed coefficient beyond every bad row.",
     "gives one\ndefinable coefficient beyond every bad row."),
    (r"one may take $b_1 = c b_0$, which recovers the original translation.",
     r"one may take $b_1 = c b_0$."),
    (r"no bound uniform in the original parameter $a$ is assumed.",
     r"no bound uniform in the parameter $a$ is assumed."),
    ("\\setcounter{thm}{11}\n\\begin{lem}[Monomial decomposition",
     "\\begin{lem}[Monomial decomposition"),
    ("\\setcounter{thm}{13}\n\\begin{nota}[Equivariant residue realization]",
     "\\begin{nota}[Equivariant residue realization]"),
]
