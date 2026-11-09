import NumberFieldKB.MilneCFT.Ch5Complements

/-!
# Characters of ideals, the conductor-discriminant formula, power residue symbols
(Milne, *Class Field Theory*, Chapter V, §3, pp. 165–166)

* Dirichlet (Weber) characters of ideals (p. 155, p. 165): `IsDirichletCharOn`; cotrained characters
  (`CharCotrained`, an equivalence relation `charCotrained_equivalence`), primitive characters (`IsPrimitiveChar`), the
  named statement `PrimitiveCharacters` (each class has a unique primitive member), the conductor of a character
  (`IsCharConductor`);
* **Theorem 3.27** (the conductor-discriminant formula, named `Theorem3_27`), **Remark 3.28** (named),
  **Example 3.29** (`example_3_29`, from 3.27 and 3.11), **Example 3.30** (`example_3_30`: Mathlib's discriminant of
  $\mathbb Q(\zeta_p)$);
* the power residue symbol $(a/\mathfrak p)_n$ (`powerResidueSymbol`, p. 166) and its criterion (named
  `PowerResidueCriterion`);
* Remark 3.26(d) (Chebotarev with natural density): the named statement `MilneANT.Theorem8_31` of this library,
  proved (`MilneANT.theorem8_31`); the hypothesis-free form is `remark_3_26d'` (`Ch5Remark326d.lean`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- **Remark 3.26(d)** (Milne, *CFT*, V, p. 165): "Chebotarev proved his theorem using Dirichlet densities. Artin noted
that it should hold for natural densities, and in fact it does": the natural-density form is the library's named
statement `MilneANT.Theorem8_31` (Milne, *ANT*, Theorem 8.31); the Dirichlet form is proved (`theorem_3_23`). -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(d)"]
theorem remark_3_26d (h : MilneANT.Theorem8_31) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses Gal(L/K)) :
    MilneANT.HasNaturalDensity (frobSet K L C) (Nat.card C.carrier / Nat.card Gal(L/K)) :=
  h.natural_density K L C

/-! ## Characters of ideals -/

/-- **A Dirichlet (Weber) character on $I^S$** (Milne, *CFT*, V, §2, p. 155): $\chi : I^S \to \mathbb C^\times$ trivial on
$i(K_{\mathfrak m,1})$ for some modulus $\mathfrak m$ with $S(\mathfrak m) = S$ (equivalently, a character of
$C_\mathfrak m$). -/
@[kb "milne2020cft" "Ch. V, §2, p. 155 (Dirichlet or Weber character)"]
def IsDirichletCharOn (S : Set (HeightOneSpectrum (𝓞 K))) (χ : sIdeals S →* ℂˣ) : Prop :=
  ∃ m : Modulus K, m.finiteSupport = S ∧
    ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S, χ ⟨_, h⟩ = 1

/-- **Cotrained characters** (Milne, *CFT*, V, p. 165): $\chi$ on $I^S$ and $\chi'$ on $I^{S'}$ agree on $I^{S''}$ for some
finite $S'' \supseteq S \cup S'$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (cotrained characters)"]
def CharCotrained {S S' : Set (HeightOneSpectrum (𝓞 K))} (χ : sIdeals S →* ℂˣ) (χ' : sIdeals S' →* ℂˣ) : Prop :=
  ∃ S'' : Set (HeightOneSpectrum (𝓞 K)), S''.Finite ∧ S ∪ S' ⊆ S'' ∧
    ∀ a ∈ sIdeals S'', ∀ (h : a ∈ sIdeals S) (h' : a ∈ sIdeals S'), χ ⟨a, h⟩ = χ' ⟨a, h'⟩

/-- Characters on finite sets of primes, as pairs. -/
structure IdealChar (K : Type) [Field K] [NumberField K] where
  /-- The finite set $S$. -/
  S : Set (HeightOneSpectrum (𝓞 K))
  finite : S.Finite
  /-- The character of $I^S$. -/
  χ : sIdeals S →* ℂˣ

/-- "Cotrained is an equivalence relation" (Milne, *CFT*, V, p. 165). -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (cotrained is an equivalence relation)"]
theorem charCotrained_equivalence :
    Equivalence (fun χ χ' : IdealChar K => CharCotrained χ.χ χ'.χ) := by
  have anti : ∀ {S T : Set (HeightOneSpectrum (𝓞 K))}, S ⊆ T → ∀ a ∈ sIdeals T, a ∈ sIdeals S :=
    fun hST _ ha v hv => ha v (hST hv)
  refine ⟨fun χ => ⟨χ.S, χ.finite, by simp, fun a _ h h' => rfl⟩, ?_, ?_⟩
  · rintro χ χ' ⟨S'', hfin, hsub, h⟩
    exact ⟨S'', hfin, by rwa [Set.union_comm], fun a ha h1 h2 => (h a ha h2 h1).symm⟩
  · rintro χ χ' χ'' ⟨S₁, hf₁, hs₁, h₁⟩ ⟨S₂, hf₂, hs₂, h₂⟩
    refine ⟨S₁ ∪ S₂, hf₁.union hf₂, ?_, fun a ha h h'' => ?_⟩
    · exact Set.union_subset (Set.subset_union_left.trans (hs₁.trans Set.subset_union_left))
        (Set.subset_union_right.trans (hs₂.trans Set.subset_union_right))
    · have ha₁ : a ∈ sIdeals S₁ := anti Set.subset_union_left a ha
      have ha₂ : a ∈ sIdeals S₂ := anti Set.subset_union_right a ha
      have h' : a ∈ sIdeals χ'.S := anti (Set.subset_union_right.trans hs₁) a ha₁
      exact (h₁ a ha₁ h h').trans (h₂ a ha₂ h' h'')

/-- **A primitive character** (Milne, *CFT*, V, p. 165): a Dirichlet character whose $S$ is contained in the $S'$ of every
cotrained Dirichlet character. -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (primitive character)"]
def IsPrimitiveChar (χ : IdealChar K) : Prop :=
  IsDirichletCharOn χ.S χ.χ ∧
    ∀ χ' : IdealChar K, IsDirichletCharOn χ'.S χ'.χ → CharCotrained χ.χ χ'.χ → χ.S ⊆ χ'.S

variable (K) in
/-- **Primitive characters** (named statement; Milne, *CFT*, V, p. 165): every class of cotrained Dirichlet characters
contains a unique primitive character. -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (each class has a unique primitive character; input)"]
structure PrimitiveCharacters : Prop where
  exists_primitive : ∀ χ : IdealChar K, IsDirichletCharOn χ.S χ.χ →
    ∃ χ₁ : IdealChar K, IsPrimitiveChar χ₁ ∧ CharCotrained χ.χ χ₁.χ
  unique : ∀ χ₁ χ₂ : IdealChar K, IsPrimitiveChar χ₁ → IsPrimitiveChar χ₂ → CharCotrained χ₁.χ χ₂.χ →
    ∃ h : χ₁.S = χ₂.S, ∀ a : sIdeals χ₁.S, χ₁.χ a = χ₂.χ ⟨a, h ▸ a.2⟩

/-- **The conductor of a character** (Milne, *CFT*, V, p. 165): $\mathfrak f(\chi)$ is the smallest modulus
$\mathfrak m$ such that the primitive character $\chi_1$ cotrained with $\chi$ is trivial on $i(K_{\mathfrak m,1})$;
$\mathfrak f = \mathfrak f_\infty\mathfrak f_0$ with $\mathfrak f_0$ = `f.finite`. -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (conductor of a character)"]
def IsCharConductor (χ : IdealChar K) (f : Modulus K) : Prop :=
  ∃ χ₁ : IdealChar K, IsPrimitiveChar χ₁ ∧ CharCotrained χ.χ χ₁.χ ∧
    (f.finiteSupport ⊆ χ₁.S ∧ ∀ a : Kˣ, a ∈ congruenceSubgroup f →
      ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals χ₁.S, χ₁.χ ⟨_, h⟩ = 1) ∧
    ∀ m : Modulus K, m.finiteSupport ⊆ χ₁.S → (∀ a : Kˣ, a ∈ congruenceSubgroup m →
      ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals χ₁.S, χ₁.χ ⟨_, h⟩ = 1) → f.Dvd m

/-! ## The conductor-discriminant formula -/

/-- The relative discriminant ideal $\mathfrak d_{L/K}$, as the norm of the different (Neukirch, III, 2.9
[unverified locator]; Mathlib's `differentIdeal` and `Ideal.relNorm`). -/
def relDiscr (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Ideal (𝓞 K) :=
  Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L))

/-- The character $\chi\circ\psi_{L/K}$ of $I^S$, $S$ the finite primes ramified in $L$. -/
def charOfGal (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (χ : Gal(L/K) →* ℂˣ) : IdealChar K where
  S := (unramifiedPrimes K L)ᶜ
  finite := finite_compl_unramifiedPrimes K L
  χ := χ.comp (artinMap L (unramifiedPrimes K L)ᶜ)

variable (K) in
/-- **Theorem 3.27, the conductor-discriminant formula** (named statement; Milne, *CFT*, V, Theorem 3.27, p. 165,
"really a statement about local fields"): for a finite abelian $L/K$ with group $G$,
$\mathfrak d_{L/K} = \prod_{\chi\in\hat G}\mathfrak f_0(\chi\circ\psi_{L/K})$ and
$\mathfrak f(L/K) = \mathrm{lcm}_\chi\,\mathfrak f(\chi\circ\psi_{L/K})$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.27 (input)"]
structure Theorem3_27 : Prop where
  disc : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (f : (Gal(L/K) →* ℂˣ) → Modulus K), (∀ χ, IsCharConductor (charOfGal L χ) (f χ)) →
      relDiscr K L = ∏ᶠ χ : Gal(L/K) →* ℂˣ, (f χ).finite
  lcm : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (f : (Gal(L/K) →* ℂˣ) → Modulus K), (∀ χ, IsCharConductor (charOfGal L χ) (f χ)) →
      ∀ g : Modulus K, IsArtinConductor L g ↔ ∀ m : Modulus K, g.Dvd m ↔ ∀ χ, (f χ).Dvd m

variable (K) in
/-- **Remark 3.28** (named statement; Milne, *CFT*, V, Remark 3.28, p. 165): for a character $\chi$ of $G$ with kernel
$H$, $\mathfrak f(\chi\circ\psi_{L/K}) = \mathfrak f(L^H/K)$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.28 (input)"]
structure Remark3_28 : Prop where
  conductor_eq : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (χ : Gal(L/K) →* ℂˣ) (f g : Modulus K), IsCharConductor (charOfGal L χ) f →
      IsArtinConductor (IntermediateField.fixedField χ.ker) g → f = g

/-- **Example 3.30** (Milne, *CFT*, V, p. 165): the discriminant of $\mathbb Q(\zeta_p)$, $p$ an odd prime, is
$\pm p^{p-2}$ (Mathlib's `IsCyclotomicExtension.Rat.discr_prime`; Milne recovers it from the conductor-discriminant
formula: the $p-2$ nontrivial characters have conductor $(p)$ or $\infty(p)$). -/
@[kb "milne2020cft" "Ch. V, Example 3.30"]
theorem example_3_30 (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {p} ℚ L] :
    discr L = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) :=
  IsCyclotomicExtension.Rat.discr_prime p L

/-! ## The power residue symbol (p. 166) -/

/-- **The power residue symbol** $(a/\mathfrak p)_n$ (Milne, *CFT*, V, §3, p. 166): $K$ contains a primitive $n$-th root
of $1$, $L = K(\alpha)$ with $\alpha^n = a \in K$ (an abelian extension), and $\mathfrak p$ is prime to $n$ and $a$ (so
unramified in $L$); $(a/\mathfrak p)_n$ is the $n$-th root of $1$ with $(\mathfrak p, L/K)\alpha =
(a/\mathfrak p)_n\,\alpha$. Here it is the element $(\mathfrak p, L/K)\alpha/\alpha$ of $L$; it is an $n$-th root of $1$
(`powerResidueSymbol_pow`), so it lies in $K$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 166 (power residue symbol)"]
def powerResidueSymbol (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (v : HeightOneSpectrum (𝓞 K)) : L :=
  artinFrob L v α / α

/-- The power residue symbol is an $n$-th root of $1$ when $\alpha^n \in K$, $\alpha \ne 0$. -/
theorem powerResidueSymbol_pow (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (n : ℕ) (α : L) (hα : α ≠ 0) (a : K) (ha : α ^ n = algebraMap K L a) (v : HeightOneSpectrum (𝓞 K)) :
    powerResidueSymbol L α v ^ n = 1 := by
  have ha0 : algebraMap K L a ≠ 0 := by
    rw [← ha]; exact pow_ne_zero n hα
  rw [powerResidueSymbol, div_pow, ← map_pow, ha, AlgEquiv.commutes, div_self ha0]

variable (K) in
/-- **The power residue criterion** (named statement; Milne, *CFT*, V, §3, p. 166, "one can show"): with $K \ni \zeta_n$,
$L = K(\alpha)$, $\alpha^n = a \in \mathcal O_K$, and $\mathfrak p$ a prime not dividing $n a$:
$(a/\mathfrak p)_n = 1$ iff $a$ is an $n$-th power modulo $\mathfrak p$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 166 ((a/p)_n = 1 iff a is an n-th power mod p; input)"]
structure PowerResidueCriterion : Prop where
  criterion : ∀ (n : ℕ) (ζ : K), IsPrimitiveRoot ζ n → ∀ (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (α : L) (a : 𝓞 K), α ^ n = algebraMap K L (a : K) → IntermediateField.adjoin K {α} = ⊤ →
    ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ v.asIdeal → a ∉ v.asIdeal →
      (powerResidueSymbol L α v = 1 ↔ ∃ x : 𝓞 K, x ^ n - a ∈ v.asIdeal)

end NumberFieldKB.MilneCFT
