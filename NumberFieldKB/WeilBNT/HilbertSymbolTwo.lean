import QuadFormsKB.Tamagawa.SquareClassDuality

/-!
# Weil, *Basic Number Theory*, Chapter XIII, §5: the Hilbert symbol for $n=2$ over a number field

Weil (XIII.§5, p. 260–262) defines, for a local field $K$ containing the $n$-th roots of unity, the symbol
$(x,y)_{n,K}=(\chi_{n,x},y)_K$ through local class field theory, and for an A-field $k$ containing them the global symbol
$(z,z')_n=\prod_v(z_v,z'_v)_{n,k_v}$ on ideles. For $n=2$ (every field contains $\pm1$) Weil's local symbol is the
classical quadratic Hilbert symbol: $(x,y)_{2,K}=1$ exactly when $y$ is a norm from $K(\sqrt x)$, i.e. when
$z^2=xX^2+yY^2$ has a nonzero solution. Here the symbol is QuadFormsKB's `hilbertSymbol` (that classical definition);
the identification with Weil's class-field-theoretic definition is not formalized (it is Weil XII.§3, Prop. 9 and IX.§5).

This file packages, for a number field $k$ and $n=2$, the parts of Weil's Prop. 6, Prop. 7 and the text of p. 262 that
QuadFormsKB proves **without class field theory** (Weil derives them from Artin–Hasse reciprocity, XIII.§3):

* **`weil_XIII_5_prop6_symm`** (Prop. 6, first assertion): $(y,x)_2=(x,y)_2^{-1}=(x,y)_2$, over any field;
* **`weil_XIII_5_prop6_squares_finite`**, **`weil_XIII_5_prop6_squares_infinite`** (Prop. 6, second assertion): at
  every place $v$ of $k$, $y\in k_v^\times$ is a square if and only if $(x,y)_{2,k_v}=1$ for all $x\in k_v^\times$
  (QuadFormsKB `SqDual.hilbCl_nondeg_fin`, `SqDual.hilbCl_nondeg_inf`, by norm groups of quadratic extensions);
* **`weil_XIII_5_prop6_units_nondyadic`** (Prop. 6, third assertion, the direction "units are orthogonal to units"
  for elements of $k$): if $\lvert 2\rvert_v=1$ and $\xi,\eta\in k$ are units at $v$, then $(\xi,\eta)_{2,v}=1$;
* **`weil_XIII_5_prop7_finite`** (Prop. 7, first assertion, for $\xi,\eta\in k^\times$): almost all factors
  $(\xi,\eta)_{2,v}$ are $1$;
* **`weil_XIII_5_reciprocity`** (text p. 262: $(\xi,\eta)_n=1$ for $\xi,\eta\in k^\times$; Hilbert's product formula):
  $\prod_v(\xi,\eta)_{2,v}=1$, the product over all places of $k$ (QuadFormsKB `HN.hilbert_product_formula_nf`, proved by
  Weil's other route, the Weil index and adelic Poisson summation, Acta Math. 111, 1964).
-/

open IsDedekindDomain NumberField QuadFormsKB

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- **Weil, XIII.§5, Prop. 6, first assertion ($n=2$)**: $(y,x)_2=(x,y)_2^{-1}$; for $n=2$ the symbol is $\pm1$, so this
is the symmetry $(y,x)_2=(x,y)_2$, and it holds over every field. -/
@[kb "weil1973bnt" "Ch. XIII, §5, Prop. 6 (p. 260), first assertion, n = 2"]
theorem weil_XIII_5_prop6_symm (K : Type*) [Field K] (x y : K) :
    hilbertSymbol K y x = hilbertSymbol K x y :=
  hilbertSymbol_comm K y x

/-- The Hilbert symbol takes only the values $\pm1$, so it is its own inverse. -/
theorem hilbertSymbol_mul_self (K : Type*) [Field K] (x y : K) :
    hilbertSymbol K x y * hilbertSymbol K x y = 1 := by
  rcases HN.hilbertSymbol_eq_one_or K x y with h | h <;> rw [h] <;> norm_num

variable {F : Type} [Field F] [NumberField F]

/-- On square classes: a class $y$ is trivial iff it pairs to $1$ with every class. -/
private theorem sqCl_eq_one_iff {K : Type*} [Field K]
    (hnd : ∀ y : SqDual.SqCl K, y ≠ 1 → ∃ x, SqDual.hilbCl K x y = -1) (y : Kˣ) :
    IsSquare (y : K) ↔ ∀ x : Kˣ, hilbertSymbol K (x : K) (y : K) = 1 := by
  constructor
  · rintro ⟨d, hd⟩ x
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    rw [hd, ← one_mul (d * d), ← sq, SqDual.hilbertSymbol_mul_sq_right K _ _ _ hd0, hilbertSymbol_one_right]
  · intro h
    by_contra hns
    have hy : (QuotientGroup.mk y : SqDual.SqCl K) ≠ 1 := fun h1 =>
      hns ((SqDual.mk_eq_one_iff_isSquare K y).mp h1)
    obtain ⟨x, hx⟩ := hnd _ hy
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [SqDual.hilbCl_mk, h x] at hx
      norm_num at hx

/-- **Weil, XIII.§5, Prop. 6, second assertion ($n=2$), finite places**: for a finite place $v$ of a number field $k$
(dyadic places included), $y\in k_v^\times$ is a square if and only if $(x,y)_{2,k_v}=1$ for every $x\in k_v^\times$;
i.e. $(k_v^\times)^2$ is the orthogonal of $k_v^\times$ under the Hilbert symbol. -/
@[kb "weil1973bnt" "Ch. XIII, §5, Prop. 6 (p. 260), second assertion, n = 2, finite places of a number field"]
theorem weil_XIII_5_prop6_squares_finite (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    IsSquare (y : v.adicCompletion F) ↔
      ∀ x : (v.adicCompletion F)ˣ, hilbertSymbol (v.adicCompletion F) (x : v.adicCompletion F) y = 1 :=
  sqCl_eq_one_iff (SqDual.hilbCl_nondeg_fin v) y

/-- **Weil, XIII.§5, Prop. 6, second assertion ($n=2$), infinite places**: at an infinite place $w$ of a number field,
$y\in k_w^\times$ is a square if and only if $(x,y)_{2,k_w}=1$ for every $x\in k_w^\times$. -/
@[kb "weil1973bnt" "Ch. XIII, §5, Prop. 6 (p. 260), second assertion, n = 2, infinite places of a number field"]
theorem weil_XIII_5_prop6_squares_infinite (w : InfinitePlace F) (y : (w.Completion)ˣ) :
    IsSquare (y : w.Completion) ↔ ∀ x : (w.Completion)ˣ, hilbertSymbol w.Completion (x : w.Completion) y = 1 :=
  sqCl_eq_one_iff (SqDual.hilbCl_nondeg_inf w) y

/-- **Weil, XIII.§5, Prop. 6, third assertion ($n=2$), one direction, for elements of $k$**: at a finite place $v$
with $\lvert 2\rvert_v=1$, if $\xi,\eta\in k$ are units at $v$ then $(\xi,\eta)_{2,v}=1$ (so the units of $k$ at $v$ lie
in the orthogonal of $r_v^\times$). Weil's full assertion (the orthogonal of $r_v^\times$ in $k_v^\times$ is
$(k_v^\times)^2r_v^\times$) is not formalized here. -/
@[kb "weil1973bnt" "Ch. XIII, §5, Prop. 6 (p. 260), third assertion, direction 'units pair trivially', n = 2, elements of a number field"]
theorem weil_XIII_5_prop6_units_nondyadic (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (ξ η : F)
    (hξ : v.valuation F ξ = 1) (hη : v.valuation F η = 1) : (NFPlace.finite v).hilbert ξ η = 1 :=
  SqDual.hilbert_units_nondyadic v h2 ξ η hξ hη

theorem hilbert_eq_one_or (v : NFPlace F) (ξ η : F) : v.hilbert ξ η = 1 ∨ v.hilbert ξ η = -1 := by
  cases v <;> exact HN.hilbertSymbol_eq_one_or _ _ _

/-- **Weil, XIII.§5, Prop. 7, first assertion ($n=2$), for $\xi,\eta\in k^\times$**: $(\xi,\eta)_{2,v}=1$ for all but
finitely many places $v$ of the number field $k$. -/
@[kb "weil1973bnt" "Ch. XIII, §5, Prop. 7 (p. 261), first assertion, n = 2, principal ideles of a number field"]
theorem weil_XIII_5_prop7_finite {ξ η : F} (hξ : ξ ≠ 0) (hη : η ≠ 0) :
    {v : NFPlace F | v.hilbert ξ η ≠ 1}.Finite := by
  refine (HN.hilbert_product_formula_nf ξ η hξ hη).1.subset fun v hv => ?_
  exact (hilbert_eq_one_or v ξ η).resolve_left hv

/-- **Weil, XIII.§5, text p. 262 ($n=2$): Hilbert's reciprocity law.** For $\xi,\eta\in k^\times$ ($k$ a number field),
$$\prod_v(\xi,\eta)_{2,v}=1,$$
the product over all places of $k$ (a finite product by `weil_XIII_5_prop7_finite`). Weil deduces it from Artin–Hasse
reciprocity (XIII.§3, Cor. of Thm. 2); here it is QuadFormsKB's `HN.hilbert_product_formula_nf` (the number of places
with $(\xi,\eta)_{2,v}=-1$ is finite and even), proved through the Weil index without class field theory. -/
@[kb "weil1973bnt" "Ch. XIII, §5, text p. 262 (Hilbert reciprocity), n = 2, number field case"]
theorem weil_XIII_5_reciprocity {ξ η : F} (hξ : ξ ≠ 0) (hη : η ≠ 0) :
    ∏ᶠ v : NFPlace F, v.hilbert ξ η = 1 := by
  obtain ⟨hfin, heven⟩ := HN.hilbert_product_formula_nf ξ η hξ hη
  have hpm := fun v => hilbert_eq_one_or (F := F) v ξ η
  have hsupp : Function.mulSupport (fun v : NFPlace F => v.hilbert ξ η) = {v | v.hilbert ξ η = -1} := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_ofPred_eq]
    rcases hpm v with h | h <;> simp [h]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [hsupp, Set.Finite.coe_toFinset])]
  rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℤ)) (fun v hv => by simpa using hv),
    Finset.prod_const, ← Set.ncard_eq_toFinset_card _ hfin]
  exact heven.neg_one_pow

end NumberFieldKB.WeilBNT
