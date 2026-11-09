import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Corestriction

/-!
# Milne, *Class Field Theory*, Chapter II §1: cup products

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Neither Mathlib nor the knowledge base defines cup products in group cohomology. Milne's Proposition 1.38
characterizes them axiomatically (existence and uniqueness of a family of pairings with properties (a)–(d)), and
Proposition 1.39 lists their formal properties. We define the structure `CupProductFamily G` of such a family
(the conditions (a)–(d)), record Proposition 1.38 as a named statement (existence and uniqueness), and
Proposition 1.39 as a named statement about any such family.

Degrees: to avoid casts between `groupCohomology X (r + s + 1)` and `groupCohomology X (r + 1 + s)`, the pairing
is indexed by `r s n` with a proof of `r + s = n`.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits MonoidalCategory

/-- A family of **cup-product pairings** for a group $G$ (Milne, Proposition 1.38, p. 73): bi-additive maps
$H^r(G, M) \times H^s(G, N) \to H^{r+s}(G, M \otimes N)$ for all $G$-modules $M$, $N$ (diagonal action on
$M \otimes_{\mathbb Z} N$) and all $r, s \ge 0$, such that
(a) they are natural in $(M, N)$;
(b) for $r = s = 0$ the pairing is $(m, n) \mapsto m \otimes n : M^G \times N^G \to (M \otimes N)^G$;
(c) if $0 \to M' \to M \to M'' \to 0$ is exact and stays exact after $- \otimes N$, then
$(\delta m'') \cup n = \delta(m'' \cup n)$;
(d) if $0 \to N' \to N \to N'' \to 0$ is exact and stays exact after $M \otimes -$, then
$m \cup \delta n'' = (-1)^r \delta(m \cup n'')$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.38, the conditions on cup products, p. 73"]
structure CupProductFamily (G : Type) [Group G] where
  /-- The pairing $H^r(G, M) \times H^s(G, N) \to H^n(G, M \otimes N)$, $n = r + s$. -/
  cup : ∀ (M N : Rep ℤ G) (r s n : ℕ), r + s = n →
    groupCohomology M r →+ groupCohomology N s →+ groupCohomology (M ⊗ N) n
  natural : ∀ {M M' N N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N') (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology M r) (y : groupCohomology N s),
    cup M' N' r s n h ((functor ℤ G r).map f x) ((functor ℤ G s).map g y) =
      (functor ℤ G n).map (f ⊗ₘ g) (cup M N r s n h x y)
  zero : ∀ (M N : Rep ℤ G) (m : M.ρ.invariants) (n : N.ρ.invariants),
    (H0Iso (M ⊗ N)).hom (cup M N 0 0 0 rfl ((H0Iso M).inv m) ((H0Iso N).inv n)) =
      ⟨TensorProduct.tmul ℤ (m : M) (n : N), fun g => by
        change TensorProduct.map (M.ρ g) (N.ρ g) (TensorProduct.tmul ℤ (m : M) (n : N)) = _
        rw [TensorProduct.map_tmul, m.2 g, n.2 g]⟩
  delta_left : ∀ (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact) (N : Rep ℤ G)
    (hSN : (S.map (tensorRight N)).ShortExact) (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology S.X₃ r) (y : groupCohomology N s),
    cup S.X₁ N (r + 1) s (n + 1) (by omega) (δ hS r (r + 1) rfl x) y =
      δ hSN n (n + 1) rfl (cup S.X₃ N r s n h x y)
  delta_right : ∀ (M : Rep ℤ G) (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (hMS : (S.map (tensorLeft M)).ShortExact) (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology M r) (y : groupCohomology S.X₃ s),
    cup M S.X₁ r (s + 1) (n + 1) (by omega) x (δ hS s (s + 1) rfl y) =
      (-1 : ℤ) ^ r • δ hMS n (n + 1) rfl (cup M S.X₃ r s n h x y)

/-- **Proposition 1.38** (p. 73), as a named statement: for every group $G$ there exists one and only one family
of cup-product pairings with the properties (a)–(d) (`CupProductFamily`). Milne proves uniqueness by dimension
shifting (using Lemma 1.37) and existence by the cochain formula
$(\varphi \cup \psi)(g_1, \dots, g_{r+s}) = \varphi(g_1, \dots, g_r) \otimes g_1 \cdots g_r\,\psi(g_{r+1}, \dots,
g_{r+s})$, "several pages" of details. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.38, p. 73"]
structure Prop1_38 : Prop where
  exists_unique : ∀ (G : Type) [Group G],
    Nonempty (CupProductFamily G) ∧ ∀ c₁ c₂ : CupProductFamily G, c₁.cup = c₂.cup

/-- **Proposition 1.39** (p. 73–74), as a named statement, for the cup products of Proposition 1.38 (any family
satisfying (a)–(d); by Proposition 1.38 there is exactly one):
(a) $(x \cup y) \cup z = x \cup (y \cup z)$ in $H^{r+s+t}(G, M \otimes N \otimes P)$ (via the associator);
(b) $x \cup y = (-1)^{rs}\, y \cup x$ (identifying $M \otimes N$ and $N \otimes M$ by the braiding);
(c) $\mathrm{Res}(x \cup y) = \mathrm{Res}(x) \cup \mathrm{Res}(y)$ (restriction to a subgroup $H$, Mathlib's
`groupCohomology.map H.subtype (𝟙 _)`; the restriction of $M \otimes N$ is $\operatorname{Res} M \otimes
\operatorname{Res} N$);
(d) $\mathrm{Cor}(x \cup \mathrm{Res}\, y) = \mathrm{Cor}(x) \cup y$ for $H$ of finite index (`cor`);
(e) $\mathrm{Inf}(x \cup y) = \mathrm{Inf}(x) \cup \mathrm{Inf}(y)$ (inflation from $G/H$, $H$ normal, for
$G/H$-modules regarded as $G$-modules; Mathlib's `groupCohomology.map (QuotientGroup.mk' H)`).
Milne proves each by checking degree $0$ and dimension shifting (Atiyah–Wall, Prop. 9; Weiss 4-3-9). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.39, p. 73–74"]
structure Prop1_39 : Prop where
  assoc_cup : ∀ (G : Type) [Group G] (c : CupProductFamily G) (M N P : Rep ℤ G) (r s t : ℕ)
    (x : groupCohomology M r) (y : groupCohomology N s) (z : groupCohomology P t),
    (functor ℤ G (r + s + t)).map (α_ M N P).hom
        (c.cup (M ⊗ N) P (r + s) t (r + s + t) rfl (c.cup M N r s (r + s) rfl x y) z) =
      c.cup M (N ⊗ P) r (s + t) (r + s + t) (by omega) x (c.cup N P s t (s + t) rfl y z)
  comm_cup : ∀ (G : Type) [Group G] (c : CupProductFamily G) (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology M r) (y : groupCohomology N s),
    (functor ℤ G (r + s)).map (β_ M N).hom (c.cup M N r s (r + s) rfl x y) =
      (-1 : ℤ) ^ (r * s) • c.cup N M s r (r + s) (by omega) y x
  res_cup : ∀ (G : Type) [Group G] (H : Subgroup G) (cG : CupProductFamily G) (cH : CupProductFamily H)
    (M N : Rep ℤ G) (r s : ℕ) (x : groupCohomology M r) (y : groupCohomology N s),
    map H.subtype (𝟙 (res H.subtype (M ⊗ N))) (r + s) (cG.cup M N r s (r + s) rfl x y) =
      cH.cup (res H.subtype M) (res H.subtype N) r s (r + s) rfl
        (map H.subtype (𝟙 _) r x) (map H.subtype (𝟙 _) s y)
  cor_cup : ∀ (G : Type) [Group G] (H : Subgroup G) [Fintype (G ⧸ H)] (cG : CupProductFamily G)
    (cH : CupProductFamily H) (M N : Rep ℤ G) (r s : ℕ) (x : groupCohomology (res H.subtype M) r)
    (y : groupCohomology N s),
    cor H (M ⊗ N) (r + s)
        (cH.cup (res H.subtype M) (res H.subtype N) r s (r + s) rfl x (map H.subtype (𝟙 _) s y)) =
      cG.cup M N r s (r + s) rfl (cor H M r x) y
  inf_cup : ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (cG : CupProductFamily G)
    (cQ : CupProductFamily (G ⧸ H)) (M N : Rep ℤ (G ⧸ H)) (r s : ℕ) (x : groupCohomology M r)
    (y : groupCohomology N s),
    map (QuotientGroup.mk' H) (𝟙 (res (QuotientGroup.mk' H) (M ⊗ N))) (r + s)
        (cQ.cup M N r s (r + s) rfl x y) =
      cG.cup (res (QuotientGroup.mk' H) M) (res (QuotientGroup.mk' H) N) r s (r + s) rfl
        (map (QuotientGroup.mk' H) (𝟙 _) r x) (map (QuotientGroup.mk' H) (𝟙 _) s y)

end NumberFieldKB.MilneCFT
