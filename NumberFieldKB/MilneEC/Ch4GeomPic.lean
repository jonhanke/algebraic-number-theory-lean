import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV, Example 1.10: divisor classes over a non-closed field

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Example 1.10 (pdf p. 116), and
Chapter I, Remark 4.14 (pdf p. 46).  Locators give the pdf page of the text `ectext6`.

Let $k$ be a perfect field, $\Gamma = \operatorname{Gal}(\bar k/k)$, $C$ a curve over $k$ and $\bar C$ the curve over
$\bar k$.  Milne defines $\operatorname{Pic}(C) = \operatorname{Pic}(\bar C)^\Gamma$ and asks whether it is the group of
divisor classes of $C$.  From the exact sequences of $\Gamma$-modules
$$0 \to \bar k^\times \to \bar k(\bar C)^\times \to \bar k(\bar C)^\times/\bar k^\times \to 0, \qquad
  0 \to \bar k(\bar C)^\times/\bar k^\times \to \operatorname{Div}(\bar C) \to \operatorname{Pic}(\bar C) \to 0,$$
Hilbert's Theorem 90 ($H^1(\Gamma, \bar k^\times) = 0 = H^1(\Gamma, \bar k(\bar C)^\times)$, Milne IV 1.8) and
$\operatorname{Div}(\bar C)^\Gamma = \operatorname{Div}(C)$ (Milne p. 38), he obtains the exact sequence
$$k(C)^\times \to \operatorname{Div}(C) \to \operatorname{Pic}(C) \to H^2(\Gamma, \bar k^\times) = \operatorname{Br}(k).$$

## What is formalized
The homological algebra of the example, for an arbitrary group $G$ and arbitrary $\mathbb Z[G]$-modules in the roles of
$\bar k^\times$ (`A`), $\bar k(\bar C)^\times$ (`B`), the principal divisors $\bar k(\bar C)^\times/\bar k^\times$
(`C`), $\operatorname{Div}(\bar C)$ (`D`) and $\operatorname{Pic}(\bar C)$ (`P`), written additively; $H^0$ is the
module of invariants (Mathlib's `groupCohomology _ 0`).  The two hypotheses are exactly Milne's two uses of
Hilbert 90.  The same theorem with `D` the divisors of degree $0$ and `P` the classes of degree $0$ gives the
$\operatorname{Pic}^0$ version used in Remark 4.14.

* `example_1_10_exact_div`: exactness of $H^0(B) \to H^0(D) \to H^0(P)$, i.e. a $\Gamma$-invariant divisor has
  invariant class $0$ exactly when it is the divisor of a function defined over $k$.
* `example_1_10_exact_pic`: exactness of $H^0(D) \to H^0(P) \to H^2(A)$, with the connecting map `obstruction`
  (the composite of the two connecting homomorphisms).
* `example_1_10_epi_of_isZero`: if $H^2(G, A) = 0$ (the Brauer group vanishes, for example for a finite field), every
  invariant class is the class of an invariant divisor; with the first exactness, $\operatorname{Pic}(C)$ is then the
  group of divisors on $C$ modulo principal divisors.
* `remark_4_14_obstruction`: Remark 4.14 in the form Milne proves it by referring to 1.10: an invariant class is the
  class of an invariant divisor exactly when its obstruction in $H^2$ vanishes.

**Deviation recorded.** Milne's $\Gamma$ is a profinite group and his $H^i$ is continuous cohomology with discrete
coefficients.  Mathlib's `groupCohomology` is the cohomology of the abstract group.  The theorem below holds for every
group, so it is exactly Milne's statement for a finite Galois group $\operatorname{Gal}(L/k)$ (a curve split over a
finite Galois extension $L$); for the profinite group the same proof applies verbatim to continuous cochains, whose
long exact sequence is not in Mathlib.  The identification of the modules with $\bar k^\times$,
$\bar k(\bar C)^\times$, $\operatorname{Div}(\bar C)$ for an actual curve, and the existence of a curve with nonzero
obstruction (the "not every class" of Remark 4.14), are not formalized.
-/

open CategoryTheory groupCohomology

namespace NumberFieldKB.MilneEC.Example110

variable {G : Type} [Group G] {A B C D P : Rep ℤ G}
  {i : A ⟶ B} {p : B ⟶ C} {j : C ⟶ D} {q : D ⟶ P} {w₁ : i ≫ p = 0} {w₂ : j ≫ q = 0}

/-- The map $H^n(G, X) \to H^n(G, Y)$ induced by a morphism of representations. -/
noncomputable abbrev hmap {X Y : Rep ℤ G} (f : X ⟶ Y) (n : ℕ) :
    groupCohomology X n ⟶ groupCohomology Y n :=
  map (MonoidHom.id G) f n

/-- The obstruction map $\operatorname{Pic}(\bar C)^\Gamma \to H^2(\Gamma, \bar k^\times)$ of Example 1.10: the
connecting map of the divisor sequence followed by the connecting map of the function sequence. -/
@[kb "milne2006ec" "Ch. IV, Example 1.10, the map Pic(C) → H²(Γ, k̄×), pdf p. 116"]
noncomputable def obstruction (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) : groupCohomology P 0 ⟶ groupCohomology A 2 :=
  δ h₂ 0 1 rfl ≫ δ h₁ 1 2 rfl

lemma hmap_comp {X Y Z : Rep ℤ G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    hmap (f ≫ g) n = hmap f n ≫ hmap g n :=
  (functor ℤ G n).map_comp f g

lemma hmap_comp_zero (w₂ : j ≫ q = 0) :
    hmap (p ≫ j) 0 ≫ hmap q 0 = 0 := by
  rw [← hmap_comp, Category.assoc, w₂, Limits.comp_zero]
  exact (functor ℤ G 0).map_zero _ _

lemma hmap_comp_obstruction (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) :
    hmap q 0 ≫ obstruction h₁ h₂ = 0 := by
  have := (mapShortComplex₃ h₂ (i := 0) rfl).zero
  simp only [obstruction, ← Category.assoc]
  rw [show hmap q 0 ≫ δ h₂ 0 1 rfl = 0 from this, Limits.zero_comp]

/-- **Example 1.10, exactness at $\operatorname{Div}(C)$.**  If $H^1(G, A) = 0$ (Hilbert 90 for $\bar k^\times$), then
$H^0(B) \to H^0(D) \to H^0(P)$ is exact: $k(C)^\times \to \operatorname{Div}(C) \to \operatorname{Pic}(C)$. -/
@[kb "milne2006ec" "Ch. IV, Example 1.10, exactness of k(C)× → Div(C) → Pic(C), pdf p. 116"]
theorem example_1_10_exact_div (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) (hA : Limits.IsZero (groupCohomology A 1)) :
    (ShortComplex.mk (hmap (p ≫ j) 0) (hmap q 0) (hmap_comp_zero (p := p) w₂)).Exact := by
  -- `H⁰(C) → H⁰(D) → H⁰(P)` is exact, and `H⁰(B) → H⁰(C)` is onto because `H¹(A) = 0`.
  have hS₂ := mapShortComplex₂_exact h₂ 0
  have hT := mapShortComplex₃_exact h₁ (i := 0) (j := 1) rfl
  have hepi : Epi (hmap p 0) := hT.epi_f (hA.eq_of_tgt _ _)
  let φ : ShortComplex.mk (hmap (p ≫ j) 0) (hmap q 0) (hmap_comp_zero (p := p) w₂) ⟶
      (ShortComplex.mk j q w₂).map (functor ℤ G 0) :=
    { τ₁ := hmap p 0
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        show hmap p 0 ≫ hmap j 0 = hmap (p ≫ j) 0 ≫ 𝟙 _
        rw [Category.comp_id, hmap_comp]
      comm₂₃ := by
        show 𝟙 _ ≫ hmap q 0 = hmap q 0 ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id] }
  have h1 : Epi φ.τ₁ := hepi
  have h2 : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have h3 : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS₂

/-- **Example 1.10, exactness at $\operatorname{Pic}(C)$.**  If $H^1(G, B) = 0$ (Hilbert 90 for
$\bar k(\bar C)^\times$), then $H^0(D) \to H^0(P) \to H^2(A)$ is exact:
$\operatorname{Div}(C) \to \operatorname{Pic}(C) \to H^2(\Gamma, \bar k^\times)$. -/
@[kb "milne2006ec" "Ch. IV, Example 1.10, exactness of Div(C) → Pic(C) → H²(Γ, k̄×), pdf p. 116"]
theorem example_1_10_exact_pic (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) (hB : Limits.IsZero (groupCohomology B 1)) :
    (ShortComplex.mk (hmap q 0) (obstruction h₁ h₂) (hmap_comp_obstruction h₁ h₂)).Exact := by
  have hT := mapShortComplex₃_exact h₂ (i := 0) (j := 1) rfl
  have hmono : Mono (δ h₁ 1 2 rfl) := mono_δ_of_isZero h₁ 1 hB
  let φ : mapShortComplex₃ h₂ (i := 0) (j := 1) rfl ⟶
      ShortComplex.mk (hmap q 0) (obstruction h₁ h₂) (hmap_comp_obstruction h₁ h₂) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := δ h₁ 1 2 rfl
      comm₁₂ := by
        show 𝟙 _ ≫ hmap q 0 = hmap q 0 ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        show 𝟙 _ ≫ obstruction h₁ h₂ = δ h₂ 0 1 rfl ≫ δ h₁ 1 2 rfl
        rw [Category.id_comp]; rfl }
  have h1 : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have h2 : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have h3 : Mono φ.τ₃ := hmono
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hT

/-- **Example 1.10, the case of vanishing Brauer group.**  If moreover $H^2(G, A) = 0$, every invariant class is the
class of an invariant divisor; with `example_1_10_exact_div`, $\operatorname{Pic}(C)$ is the group of divisors on $C$
modulo principal divisors (Milne: "for example, if $k$ is finite"). -/
@[kb "milne2006ec" "Ch. IV, Example 1.10, Pic(C) = Div(C)/principal divisors when Br(k) = 0, pdf p. 116"]
theorem example_1_10_epi_of_isZero (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) (hB : Limits.IsZero (groupCohomology B 1))
    (hA2 : Limits.IsZero (groupCohomology A 2)) : Epi (hmap q 0) :=
  (example_1_10_exact_pic h₁ h₂ hB).epi_f (hA2.eq_of_tgt _ _)

/-- **Remark 4.14 (via Example 1.10).**  An invariant class $c \in \operatorname{Pic}(\bar C)^\Gamma$ is the class of
an invariant divisor if and only if its obstruction in $H^2(\Gamma, \bar k^\times)$ vanishes.  So the classes not
represented by divisors on $C$ are measured by the Brauer group, which is zero for a finite field. -/
@[kb "milne2006ec" "Ch. I, Remark 4.14 (with Ch. IV, Example 1.10), pdf p. 46"]
theorem remark_4_14_obstruction (h₁ : (ShortComplex.mk i p w₁).ShortExact)
    (h₂ : (ShortComplex.mk j q w₂).ShortExact) (hB : Limits.IsZero (groupCohomology B 1))
    (c : groupCohomology P 0) :
    (∃ d : groupCohomology D 0, hmap q 0 d = c) ↔ obstruction h₁ h₂ c = 0 := by
  have hex := example_1_10_exact_pic h₁ h₂ hB
  rw [ShortComplex.moduleCat_exact_iff] at hex
  constructor
  · rintro ⟨d, rfl⟩
    have := congrArg (fun f => f.hom d) (hmap_comp_obstruction h₁ h₂)
    simpa using this
  · intro hc
    obtain ⟨d, hd⟩ := hex c hc
    exact ⟨d, hd⟩

end NumberFieldKB.MilneEC.Example110
