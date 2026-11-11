import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Cup
import NumberFieldKB.MilneCFT.Ch2Lemma33

/-!
# Milne, *Class Field Theory*, Chapter II: Remarks 1.35, 3.5 and 3.13

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

All three are stated without proof in the book (Milne cites Dekimpe–Hartl–Wauters, Serre's *Local Fields* and
Weiss), and are recorded here as named statements. Cup products are those of any family satisfying the
conditions of Proposition 1.38 (`CupProductFamily`); cup products on Tate groups in degrees $\le 0$ are not
defined in the library, so Remarks 3.5 and 3.13 are stated in degrees $r \ge 1$, where $H^r_T = H^r$.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits MonoidalCategory

/-! ## Remark 1.35 -/

section Remark1_35

variable {G : Type} [Group G]

/-- The subgroup $H^1(H, M)^{G/H}$ of classes fixed by the conjugation action of Remark 1.28 (b)
(`conjAction`, which is trivial on $H$ by Example 1.27 (d), so this is the fixed part for $G/H$). -/
noncomputable def H1Fixed (H : Subgroup G) [H.Normal] (M : Rep ℤ G) :
    AddSubgroup (groupCohomology (res H.subtype M) 1) where
  carrier := {x | ∀ g : G, conjAction H M 1 g x = x}
  add_mem' {x y} hx hy g := by simp [map_add, hx g, hy g]
  zero_mem' g := by simp
  neg_mem' {x} hx g := by simp [map_neg, hx g]

/-- **Remark 1.35 (a)** (p. 72), the five-term part, as a named statement. For a normal subgroup $H$ of $G$ and a
$G$-module $M$, the inflation–restriction sequence extends to an exact sequence
$$0 \to H^1(G/H, M^H) \xrightarrow{\mathrm{Inf}} H^1(G, M) \xrightarrow{\mathrm{Res}} H^1(H, M)^{G/H}
\xrightarrow{\mathrm{tg}} H^2(G/H, M^H) \xrightarrow{\mathrm{Inf}} H^2(G, M).$$
Exactness at the first two terms is Mathlib's (`prop_1_34_one`); the statement records that restriction lands in
the fixed part and that there is a map $\mathrm{tg}$ (the transgression) making the sequence exact at the last
three terms.

Deviations: the transgression is asserted to exist rather than given by a formula, and the continuation
$\to H^2(G, M)_1 \to H^1(G/H, H^1(H, M)) \to H^3(G/H, M^H)$ of the book's sequence (which needs $H^1(H, M)$ as a
$G/H$-module) and part (b) (the Hochschild–Serre spectral sequence) are not formalized. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.35 (a), p. 72"]
structure Remark1_35 : Prop where
  exact : ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (M : Rep ℤ G),
    (∀ x : groupCohomology M 1, (HInfRes M H 1).g x ∈ H1Fixed H M) ∧
    ∃ tg : H1Fixed H M →+ groupCohomology (M.quotientToInvariants H) 2,
      (∀ y : H1Fixed H M, tg y = 0 ↔ ∃ x : groupCohomology M 1, (HInfRes M H 1).g x = (y : groupCohomology (res H.subtype M) 1)) ∧
      (∀ z : groupCohomology (M.quotientToInvariants H) 2, (HInfRes M H 2).f z = 0 ↔ ∃ y, tg y = z)

end Remark1_35

/-! ## Remarks 3.5 and 3.13 -/

section Tate

variable {G : Type} [Group G] [Fintype G]

/-- The isomorphism $H^n_T(G, M) \simeq H^n(G, M)$ for $n \ge 1$, with the degree written as an integer
$m = n$ (Mathlib's `TateCohomology.isoGroupCohomology`). -/
noncomputable def tateIsoOfEq (M : Rep ℤ G) (m : ℤ) (n : ℕ) [NeZero n] (h : m = n) :
    tateCohomology M m ≅ groupCohomology M n :=
  eqToIso (by rw [h]) ≪≫ (TateCohomology.isoGroupCohomology n).app M

/-- **Remark 3.5** (p. 81), as a named statement. Let $G$ be cyclic of order $m$ with generator $\sigma$, and
let $\gamma \in H^2(G, \mathbb Z)$ correspond, under $H^2(G, \mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q /
\mathbb Z)$ (Lemma 3.3 (c): the connecting map of $0 \to \mathbb Z \to \mathbb Q \to \mathbb Q/\mathbb Z \to 0$
composed with `H1IsoOfIsTrivial`), to the homomorphism $f$ with $f(\sigma) = 1/m$. Then the periodicity
isomorphism of Proposition 3.4 (`periodicity`) is $x \mapsto x \cup \gamma$ (followed by $M \otimes \mathbb Z
\simeq M$). Milne states this without proof ("In a future version, I'll prove this"; Serre, *Local Fields*
VIII §4; Weiss 4-5-10).

Deviation: stated for $r \ge 1$ only (ordinary cohomology, `tateIsoOfEq`); the sign is as in the book. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.5, p. 81"]
structure Remark3_5 : Prop where
  periodicity_eq_cup : ∀ (G : Type) [Group G] [Fintype G] (σ : G) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    (f : Additive G →+ QZ),
    f (Additive.ofMul σ) = QuotientAddGroup.mk ((1 : ℚ) / Fintype.card G) →
    ∀ (c : CupProductFamily G) (M : Rep ℤ G) (r : ℕ) [NeZero r] (x : tateCohomology M r),
      (tateIsoOfEq M ((r : ℤ) + 2) (r + 2) (by push_cast; rfl)).hom ((periodicity σ hσ M r).hom x) =
        (functor ℤ G (r + 2)).map (ρ_ M).hom
          (c.cup M (trivial ℤ G ℤ) r 2 (r + 2) rfl ((tateIsoOfEq M r r rfl).hom x)
            (δ (seqZQ_shortExact G) 1 2 rfl ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv f)))

/-- **Remark 3.13** (p. 85), as a named statement. Under the hypotheses of Tate's theorem (Theorem 3.11): for
every subgroup $H$ of $G$, $H^1(H, C) = 0$ and $H^2(H, C)$ is cyclic of order $(H : 1)$, and $\gamma$ generates
$H^2(G, C)$, the isomorphism $H^r_T(G, \mathbb Z) \to H^{r+2}_T(G, C)$ of Tate's theorem is cup product with
$\gamma$. Recorded as: $x \mapsto x \cup \gamma$ (followed by $\mathbb Z \otimes C \simeq C$) is a bijection
$H^r(G, \mathbb Z) \to H^{r+2}(G, C)$.

Deviations: stated for $r \ge 1$ only (cup products on Tate groups in degrees $\le 0$ are not defined), and as
bijectivity of the cup-product map rather than its equality with the double connecting map of the sequence (24)
built from the splitting module (`splittingModule`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.13, p. 85"]
structure Remark3_13 : Prop where
  cup_bijective : ∀ (G : Type) [Group G] [Fintype G] (C : Rep ℤ G),
    (∀ H : Subgroup G, IsZero (groupCohomology (res H.subtype C) 1) ∧
      IsAddCyclic (groupCohomology (res H.subtype C) 2) ∧
      Nat.card (groupCohomology (res H.subtype C) 2) = Nat.card H) →
    ∀ γ : groupCohomology C 2, (∀ x : groupCohomology C 2, x ∈ AddSubgroup.zmultiples γ) →
    ∀ (c : CupProductFamily G) (r : ℕ), 1 ≤ r →
      Function.Bijective fun x : groupCohomology (trivial ℤ G ℤ) r =>
        (functor ℤ G (r + 2)).map (λ_ C).hom (c.cup (trivial ℤ G ℤ) C r 2 (r + 2) rfl x γ)

end Tate

end NumberFieldKB.MilneCFT
